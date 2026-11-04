"""Finite, pinned MSC screening and a resumable queue. No model or Lean calls.

Text matches are inferred navigation links, never classifications or evidence of
mathematical applicability. A complete screening is not exhaustive mathematics.
"""
from __future__ import annotations

from collections import Counter, defaultdict, deque
from contextlib import closing
import copy
import hashlib
import heapq
import json
from pathlib import Path
import re
import sqlite3
import time

ROOT = Path(__file__).resolve().parent
ATLAS_PATH = ROOT / 'data/msc2020.json'
DEFAULTS = dict(max_deep_routes=8, pool_limit=24, coarse_limit=6, local_timeout_seconds=180)
BOUNDS = dict(max_deep_routes=(1,128), pool_limit=(1,48), coarse_limit=(1,24), local_timeout_seconds=(1,600))
STOP = set('the and for with from that this are not other general theory theories mathematical '
           'mathematics including related applications aspects special particular methods of in '
           'to by or as on at an a see also problems structures study type types function functions '
           'theorem lemma def abbrev forall prop sort true false import'.split())
TOKEN_ALIASES = (('product','prod'),('injective','injectivity','inj'),
                 ('homomorphism','hom'),('polynomial','mvpolynomial'),
                 ('equivalence','equiv'),('embedding','isembedding'))
SCREENING_METHOD = 'local_token_inverted_v2'
_MSC_CODE = r'[0-9]{2}(?:-(?:[0-9]{2}|XX)|[A-Z](?:[0-9]{2}|xx))'
MSC_REFERENCE = re.compile(
    r'\[\s*(?:Consider also classification numbers from Section\s*' + _MSC_CODE +
    r'|Should also be assigned at least one other classification number in Section\s*' + _MSC_CODE +
    r'|See also\s+' + _MSC_CODE + r'(?:\s*(?:,|;|and)\s*' + _MSC_CODE + r')*)\s*\]', re.I)
LIMITATIONS = [
    'Покрытие всех кодов относится к сохранённому классификатору MSC и указанной локальной процедуре поиска.',
    'Совпадения текста и предполагаемые метки MSC не подтверждают классификацию, применимость или математическую близость.',
    'Корпус и размер выборки ограничены: подходящий источник может быть пропущен. Отсутствие связи этим не доказано.',
    'Смысловая оценка и доказательство учитываются отдельно; этот этап не доказывает кандидатов.',
]


def digest(value):
    return hashlib.sha256(json.dumps(value, sort_keys=True, ensure_ascii=False,
                                   separators=(',', ':'), allow_nan=False).encode('utf-8')).hexdigest()


def normalize_options(value=None):
    value = {} if value is None else value
    if not isinstance(value, dict) or set(value) - set(DEFAULTS):
        raise ValueError('Неизвестные параметры atlas_search.')
    result = dict(DEFAULTS, **value)
    for key, (low, high) in BOUNDS.items():
        if type(result[key]) is not int or not low <= result[key] <= high:
            raise ValueError(f'Параметр atlas_search.{key} должен быть целым от {low} до {high}.')
    return result


def tokens(text):
    text = re.sub(r'([a-z])([A-Z])', r'\1 \2', str(text))
    result = set()
    for word in re.findall(r'[^\W\d_]+', text.casefold(), re.UNICODE):
        if len(word) < 3 or word in STOP:
            continue
        # Deterministic morphology only, not semantic embeddings.
        if len(word) > 5 and word.endswith('ies'):
            word = word[:-3] + 'y'
        elif len(word) > 4 and word.endswith('s') and not word.endswith('ss'):
            word = word[:-1]
        result.add(word)
    for group in TOKEN_ALIASES:
        if result.intersection(group):
            result.update(group)
    return result


def _topic_text(text):
    """Remove MSC navigation clauses, retaining the mathematical topic itself."""
    return MSC_REFERENCE.sub(' ', str(text))


def _atlas(atlas):
    nodes = atlas.get('nodes', [])
    known = {n['id']: n for n in nodes}
    if not nodes or len(known) != len(nodes):
        raise ValueError('MSC inventory is empty or contains duplicate codes.')
    roots = {}
    for code in known:
        seen, current = set(), code
        while known[current].get('parent_id') is not None:
            if current in seen or known[current]['parent_id'] not in known:
                raise ValueError('Invalid MSC hierarchy.')
            seen.add(current)
            current = known[current]['parent_id']
        roots[code] = current
    return known, roots


def _mapping(record, known):
    """Explicit mappings need an exact source pin; legacy labels stay inferred."""
    result = []
    for item in record.get('msc_mappings', []):
        if not isinstance(item, dict) or item.get('code') not in known:
            continue
        kind = item.get('provenance_kind')
        if kind not in ('source_reported', 'curated', 'inferred'):
            continue
        if (not item.get('evidence') or not record.get('source_sha256') or
                item.get('source_sha256') != record['source_sha256']):
            continue
        result.append(dict(code=item['code'], provenance_kind=kind,
                           evidence=copy.deepcopy(item['evidence']), source_sha256=item['source_sha256']))
    bound = {x['code'] for x in result}
    for code in record.get('msc_codes', []):
        if code in known and code not in bound:
            result.append(dict(code=code, provenance_kind='inferred',
                               evidence='unattested_corpus_msc_label', source_sha256=record.get('source_sha256')))
    return result


def _push(heap, limit, score, record, link):
    key = (score, record['id'])
    item = (score, record['id'], record, link)
    if len(heap) < limit:
        heapq.heappush(heap, item)
    elif key > heap[0][:2]:
        heapq.heapreplace(heap, item)


def screen(atlas, records, source, profile, *, options=None, corpus_manifest=None,
           atlas_sha256=None, check=None, clock=time.monotonic):
    """One corpus scan, then bounded inverted-index queries for EVERY code.

    Corpus records must be unique. source_reported/curated labels are accepted
    only with explicit evidence bound to the record's source hash. Empty labels
    are never promoted. Cancellation/timeout returns an honest partial snapshot.
    """
    options = normalize_options(options)
    known, roots = _atlas(atlas)
    node_terms = {code: tokens(_topic_text(n.get('title', '')) + ' ' + _topic_text(n.get('description', '')))
                  for code, n in known.items()}
    postings = defaultdict(set)
    for code, terms in node_terms.items():
        for term in terms:
            postings[term].add(code)
    mechanism = tokens(' '.join(str(profile.get(k, '')) for k in
                               ('summary','objects','operations','assumptions','conclusion_shape','mechanism')))
    mechanism |= tokens(source.get('selected_declaration', {}).get('type', ''))
    heaps, counts, mappings = defaultdict(list), Counter(), defaultdict(Counter)
    global_heap, seen, processed, global_matches = [], set(), 0, 0
    module_tokens={}
    started, interruption = clock(), None
    manifest = copy.deepcopy(corpus_manifest or dict(status='ready', scope='provided_records'))
    if manifest.get('status') != 'ready':
        interruption = 'corpus_unavailable'
    else:
        try:
            for record in records:
                if processed % 128 == 0:
                    if check:
                        check()
                    if clock() - started >= options['local_timeout_seconds']:
                        interruption = 'local_budget_exhausted'
                        break
                if not isinstance(record, dict) or not isinstance(record.get('id'), str):
                    raise ValueError('Invalid corpus record.')
                if record['id'] in seen:
                    raise ValueError('Duplicate corpus id: ' + record['id'])
                seen.add(record['id']); processed += 1
                module=str(record.get('module',''))
                if module not in module_tokens:
                    module_tokens[module]=tokens(module)
                name=str(record.get('name',''))
                words = tokens(' '.join((name, str(record.get('title','')) if record.get('title')!=name else '',
                    str(record.get('statement','')),str(record.get('doc_comment',''))))) | module_tokens[module]
                overlap = len(words & mechanism)
                links = {item['code']: item for item in _mapping(record, known)}
                matched = Counter()
                for word in words & postings.keys():
                    for code in postings[word]:
                        matched[code] += 1
                for code in links:
                    matched.setdefault(code, 0)
                for code, count in matched.items():
                    kind=links.get(code,{}).get('provenance_kind','inferred')
                    counts[code] += 1
                    mappings[code][kind] += 1
                    score = overlap * 4 + count + (2 if kind != 'inferred' else 0)
                    heap=heaps[code]
                    if len(heap)<options['coarse_limit'] or (score,record['id'])>heap[0][:2]:
                        link=links.get(code) or dict(code=code,provenance_kind='inferred',
                            evidence=dict(method='atlas_title_token_match',tokens=sorted(words & node_terms[code])),
                            source_sha256=record.get('source_sha256'))
                        _push(heap, options['coarse_limit'], score, record, link)
                # All unclassified documents remain eligible by mechanism text;
                # it is not necessary to invent a subject label for them.
                if overlap:
                    global_matches += 1
                    _push(global_heap, options['pool_limit'], overlap, record,
                          dict(code=None, provenance_kind='inferred', evidence='global_mechanism_token_match',
                               source_sha256=record.get('source_sha256')))
        except (OSError, sqlite3.Error) as error:
            interruption = 'corpus_unavailable: ' + str(error)
        except Exception as error:
            # Persist cancellation before the controller re-raises on its next
            # budget check. Contract/data errors are not negative searches.
            if type(error).__name__ == 'StopRun':
                interruption = 'controller_stopped: ' + str(error)
            else:
                raise
    ready = interruption is None
    sources, source_links, nodes = {}, [], []
    def retain(heap):
        ids = []
        for score, identity, record, link in sorted(heap, key=lambda x: (-x[0], x[1])):
            if identity not in sources:
                sources[identity] = copy.deepcopy(record)
            source_links.append(dict(source_id=identity,title=record.get('title') or record.get('name') or identity,
                                     name=record.get('name'),url=record.get('source_url',''),**copy.deepcopy(link)))
            ids.append(identity)
        return ids
    for code, n in sorted(known.items()):
        ids = retain(heaps[code])
        attested = mappings[code]['source_reported'] + mappings[code]['curated']
        corpus_status = ('mapped' if attested else 'inferred_only' if counts[code] else 'unknown') if ready else 'unavailable'
        nodes.append(dict(code=code, parent_code=n.get('parent_id'), root_code=roots[code], level=n['level'],
            title=n['title'], screen_status='considered', query_status='executed' if ready else 'partial' if processed else 'unavailable',
            query=dict(method='msc_mapping_or_local_title_tokens',code=code,tokens=sorted(node_terms[code])),
            corpus_status=corpus_status, source_count=counts[code], mapping_counts=dict(mappings[code]),
            pool_ids=ids, pool_truncated=max(0, counts[code]-len(ids)),
            priority=len(node_terms[code] & mechanism), reason=interruption or
                ('No matching indexed text; not evidence of no mathematical connection.' if not ids else
                 'Local textual shortlist; applicability not assessed.')))
    global_ids = retain(global_heap)
    value = dict(schema_version=1, atlas_sha256=atlas_sha256 or digest(atlas),
        screening_method=SCREENING_METHOD,policy_sha256=digest(dict(stop=sorted(STOP),aliases=TOKEN_ALIASES,
            msc_reference_pattern=MSC_REFERENCE.pattern,msc_reference_flags=MSC_REFERENCE.flags)),
        input_sha256=digest(source), source_sha256=source.get('source_sha256'), profile=copy.deepcopy(profile),
        options=options, corpus_manifest=manifest, corpus_sha256=digest(manifest), corpus_records_processed=processed,
        screening_complete=True, local_queries_complete=ready, interruption=interruption,
        nodes=nodes, sources=sources, source_links=source_links,
        global_channel=dict(id='global_unclassified', status='queried' if ready else 'partial',
                            source_count=global_matches,retained_count=len(global_ids),
                            pool_truncated=max(0,global_matches-len(global_ids)),pool_ids=global_ids,
                            scope='mechanism text over entire corpus, including unclassified records'),
        limitations=LIMITATIONS)
    return dict(value, snapshot_sha256=digest(value))


def mechanism_records(entries):
    return [dict(id='mechanism:'+entry['id'],mechanism_id=entry['id'],title=entry['title'],
        name=entry['formal_contract']['target'],statement=entry['formal_contract']['statement'],
        assumptions=entry['provenance']['assumptions'],mechanism_contract=entry['formal_contract'],provenance=entry['provenance'],
        source_sha256=entry['proof_sha256'],extraction='independently_checked_stored_contract',
        type_status='verified_stored_contract',evidence_type='verified_mechanism_reuse',
        verification_scope='stored_contract_only',reuse=True,requires_new_proof=True,
        source_application_status=entry['source_application_status'],applicability_status='not_verified_for_current_task')
        for entry in entries if entry.get('status')=='verified_stored_contract']


def corpus_manifest(extra_records=(), index_path=None):
    import research_retrieval as retrieval
    library=retrieval.library_manifest(index_path)
    return dict(status=library.get('status'),library=library,mechanisms_sha256=digest(list(extra_records)),
                mechanisms_count=len(extra_records))


def local_screen(source, profile, *, options=None, index_path=None, atlas_path=None, check=None, extra_records=()):
    import research_retrieval as retrieval
    atlas_path = Path(atlas_path or ATLAS_PATH)
    raw = atlas_path.read_bytes(); atlas = json.loads(raw)
    path = Path(index_path or retrieval.INDEX_PATH)
    extra_records=list(extra_records)
    manifest = corpus_manifest(extra_records,path)
    def records():
        with closing(sqlite3.connect('file:' + path.as_posix() + '?mode=ro', uri=True, timeout=2)) as connection:
            # A read transaction pins rows to the same SQLite snapshot.
            connection.execute('BEGIN')
            row = connection.execute("SELECT value FROM metadata WHERE key='manifest'").fetchone()
            if not row or json.loads(row[0]) != manifest['library']:
                raise ValueError('Corpus manifest changed before screening.')
            # Physical row order avoids random page reads through hashed IDs.
            # Heap tie-breaks and final ordering are independent of scan order.
            for (payload,) in connection.execute('SELECT payload FROM declarations ORDER BY rowid'):
                yield json.loads(payload)
            yield from extra_records
    return screen(atlas, records() if manifest.get('status') == 'ready' else [], source, profile,
                  options=options, corpus_manifest=manifest, atlas_sha256=hashlib.sha256(raw).hexdigest(), check=check)


def verify_snapshot(snapshot):
    if not isinstance(snapshot, dict) or snapshot.get('schema_version') != 1:
        raise ValueError('Unsupported atlas snapshot.')
    body = {k:v for k,v in snapshot.items() if k != 'snapshot_sha256'}
    if digest(body) != snapshot.get('snapshot_sha256'):
        raise ValueError('Atlas snapshot checksum mismatch.')
    return snapshot


def new_progress(snapshot, previous=None):
    verify_snapshot(snapshot)
    buckets = defaultdict(list)
    for node in snapshot['nodes']:
        if node['pool_ids'] and node['query_status'] == 'executed':
            buckets[node['root_code']].append(node)
    # Rotate across roots before returning to another leaf of one root.
    for root in buckets:
        buckets[root].sort(key=lambda n: (-n['priority'], -n['level'], n['code']))
    ordered = []
    if snapshot['local_queries_complete'] and snapshot['global_channel']['pool_ids']:
        ordered.append(dict(id='global_unclassified', code=None, status='pending'))
    queues = [deque(buckets[root]) for root in sorted(buckets, key=lambda r: (-max(n['priority'] for n in buckets[r]), r))]
    while any(queues):
        for queue in queues:
            if queue:
                node = queue.popleft()
                ordered.append(dict(id='msc_' + node['code'], code=node['code'], status='pending'))
    for row in ordered:
        row.update(reason='', candidate_count=0, semantic_status='not_assessed', route_id=None)
    result = dict(schema_version=1, snapshot_sha256=snapshot['snapshot_sha256'], queue=ordered,
                  stop_reason=None, continuation=None)
    if previous:
        verify_progress(previous, snapshot)
        saved = {x['id']:x for x in previous['queue']}
        for row in result['queue']:
            old = saved[row['id']]
            if old['status'] in ('complete', 'failed'):
                row.update(copy.deepcopy(old))
            else:
                # A new run may retry interrupted tasks, never inherit an active
                # worker or silently turn a failure into a negative result.
                row['reason'] = 'Continued from an unfinished prior queue item.'
    return result


def verify_progress(progress, snapshot):
    if progress.get('snapshot_sha256') != snapshot['snapshot_sha256']:
        raise ValueError('Atlas progress belongs to another snapshot.')
    ids = [x['id'] for x in progress.get('queue', [])]
    expected = [x['id'] for x in new_progress(snapshot)['queue']]
    if ids != expected or any(x.get('status') not in ('pending','active','complete','failed') for x in progress['queue']):
        raise ValueError('Atlas queue inventory or state is invalid.')
    if any(type(x.get('candidate_count')) is not int or x['candidate_count']<0 for x in progress['queue']):
        raise ValueError('Invalid atlas candidate count.')
    return progress


def overview(snapshot, progress, run_id=None):
    verify_snapshot(snapshot); verify_progress(progress, snapshot)
    states = {x['code']:x for x in progress['queue'] if x['code'] is not None}
    nodes = []
    for raw in snapshot['nodes']:
        state = states.get(raw['code'], {})
        nodes.append({**{k:raw[k] for k in ('code','parent_code','root_code','level','title','screen_status',
                                         'query_status','corpus_status','source_count','reason')},
            'retained_count':len(raw['pool_ids']), 'pool_truncated':raw['pool_truncated'],
            'deep_status':state.get('status', 'not_scheduled'), 'candidate_count':state.get('candidate_count',0),
            'route_ids':[state['route_id']] if state.get('route_id') else [],
            'semantic_status':state.get('semantic_status','not_assessed'), 'proof_status':'not_checked'})
    counts = Counter(x['status'] for x in progress['queue'])
    deep_complete = snapshot['local_queries_complete'] and all(x['status']=='complete' for x in progress['queue'])
    levels = Counter(n['level'] for n in nodes)
    summary = dict(total_codes=len(nodes), considered_codes=sum(n['screen_status']=='considered' for n in nodes),
        queried_codes=sum(n['query_status']=='executed' for n in nodes),
        query_count=sum(n['query_status']=='executed' for n in nodes) + int(snapshot['local_queries_complete']),
        corpus_gaps=sum(n['corpus_status'] in ('unknown','unavailable','inferred_only') for n in nodes),
        deep_completed=counts['complete'], deep_pending=counts['pending']+counts['active'], deep_failed=counts['failed'],
        queue_total=len(progress['queue']), candidates_found=sum(x.get('candidate_count',0) for x in progress['queue']),
        status='complete' if deep_complete else 'partial', screening_complete=snapshot['screening_complete'],
        local_queries_complete=snapshot['local_queries_complete'], deep_complete=deep_complete, proof_verified=0,
        level_counts=dict(roots=levels[0],groups=levels[1],leaves=levels[2]),
        snapshot_sha256=snapshot['snapshot_sha256'], progress_sha256=digest(progress), stop_reason=progress.get('stop_reason'))
    examples={}
    for link in snapshot['source_links']:
        examples.setdefault(link['code'],link)
    return dict(schema_version=1,run_id=run_id,snapshot_sha256=snapshot['snapshot_sha256'],
        progress_sha256=digest(progress),summary=summary,nodes=nodes,queue=copy.deepcopy(progress['queue']),
        source_links=[{k:link[k] for k in ('source_id','title','name','url','code','provenance_kind') if k in link}
                      for link in examples.values()],source_links_total=len(snapshot['source_links']),
        source_links_scope='Показан один сохранённый пример источника для каждого кода. Все отобранные привязки сохранены в неизменяемом снимке.',
        global_channel=copy.deepcopy(snapshot['global_channel']),
        limitations=LIMITATIONS)


def load(folder, expected_progress_sha256=None):
    run_folder=Path(folder)
    if expected_progress_sha256 is None and (run_folder/'run.json').is_file():
        run=json.loads((run_folder/'run.json').read_text(encoding='utf-8'))
        expected_progress_sha256=run.get('atlas_summary',{}).get('progress_sha256')
    folder = run_folder / 'atlas'
    snapshot = verify_snapshot(json.loads((folder/'snapshot.json').read_text(encoding='utf-8')))
    if expected_progress_sha256 is not None:
        if not re.fullmatch(r'[a-f0-9]{64}',expected_progress_sha256):
            raise ValueError('Invalid progress pointer.')
        version=folder/('progress-'+expected_progress_sha256+'.json')
        # Legacy flat snapshots may be read only when they match the pin exactly.
        path=version if version.is_file() else folder/'progress.json'
    else:
        path=folder/'progress.json'
    progress = json.loads(path.read_text(encoding='utf-8'))
    if expected_progress_sha256 is not None and digest(progress)!=expected_progress_sha256:
        raise ValueError('Atlas progress checksum mismatch.')
    return snapshot, verify_progress(progress, snapshot)


def validate_atlas_integrity(service, run):
    """Called by the shared controller; performs no writes or model dispatch."""
    if run.get('contract', {}).get('search_scope', 'focused') != 'atlas':
        return
    for key in ('search_scope', 'atlas_options', 'atlas_seed'):
        if run.get(key) != run['contract'].get(key):
            raise ValueError('Frozen atlas contract changed: ' + key)
    if run.get('atlas_snapshot_sha256'):
        snapshot, progress = load(service.folder(run['id']),run.get('atlas_summary',{}).get('progress_sha256'))
        if snapshot['snapshot_sha256'] != run['atlas_snapshot_sha256']:
            raise ValueError('Pinned atlas snapshot changed.')
        if run.get('atlas_summary',{}).get('progress_sha256')!=digest(progress):
            raise ValueError('Pinned atlas progress changed.')
        source = service._structure_input(run)
        if snapshot['input_sha256'] != digest(source):
            raise ValueError('Atlas input changed.')
        if run.get('structure_profile')!=snapshot['profile']:
            raise ValueError('Pinned atlas mechanism profile changed.')
        nodes={n['code']:n for n in snapshot['nodes']}
        queue={x['id']:x for x in progress['queue']}
        for route in run.get('structure_routes',[]):
            item=queue.get(route.get('atlas_queue_id'))
            if item is None:
                raise ValueError('Atlas route is outside the pinned queue.')
            node=nodes.get(item['code'])
            pool_ids=node['pool_ids'] if node else snapshot['global_channel']['pool_ids']
            expected=digest(dict(snapshot=snapshot['snapshot_sha256'],scope=item['id'],pool_ids=pool_ids,
                                 input_sha256=snapshot['input_sha256'],corpus_sha256=snapshot['corpus_sha256']))
            if (route.get('id')!='atlas_'+item['id'] or route.get('msc_code')!=item['code'] or
                    route.get('atlas_pool_ids')!=pool_ids or route.get('atlas_cache_key')!=expected):
                raise ValueError('Pinned atlas route scope or pool changed.')
            for hit in route.get('hits',[]):
                original=snapshot['sources'].get(hit.get('id'))
                if original is None or hit['id'] not in pool_ids:
                    raise ValueError('Atlas hit is outside the pinned pool.')
                for key in ('source_sha256','name','module','statement','doc_comment','mechanism_id','mechanism_contract','provenance'):
                    if key in original and hit.get(key)!=original[key]:
                        raise ValueError('Pinned atlas source evidence changed: '+key)
