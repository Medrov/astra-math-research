"""Read-only validation and explicit snapshots of stopped structure searches.

These graphs contain proposals, never proof certificates. The parent run and its
ordinary graph_ref are deliberately untouched, including on historical recovery.
"""
from __future__ import annotations

import copy
import hashlib
import json
import re


STOPPED = {'cancelled', 'budget_exhausted', 'failed', 'interrupted'}
MAX_JSON_BYTES = 12_000_000
ROUTE_ID = re.compile(r'route_[1-6]')
ATLAS_ROUTE_ID = re.compile(r'atlas_(?:global_unclassified|msc_[0-9]{2}(?:-[0-9]{2}|[A-Z](?:[0-9]{2})?)?)')
DIGEST = re.compile(r'[a-f0-9]{64}')


def _issue(code, message, route_id=None):
    return dict(code=code, message=str(message)[:1000], route_id=route_id)


def _read(base, relative):
    path = (base / relative).resolve()
    if not path.is_relative_to(base.resolve()):
        raise ValueError('Артефакт частичного поиска находится вне каталога запуска.')
    with path.open('rb') as stream:
        data = stream.read(MAX_JSON_BYTES + 1)
    if len(data) > MAX_JSON_BYTES:
        raise ValueError('Артефакт частичного поиска слишком велик.')
    value = json.loads(data.decode('utf-8'))
    if not isinstance(value, dict):
        raise ValueError('Артефакт частичного поиска должен быть JSON-объектом.')
    return value, hashlib.sha256(data).hexdigest()


def _busy(service, run):
    from research_service import ACTIVE, _LOCAL_FUTURES
    key = str(service.folder(run['id']).resolve())
    futures = (service.futures.get(run['id']), _LOCAL_FUTURES.get(key))
    return (run.get('status') in ACTIVE | {'cancelling'} or run['id'] in service._started or
            any(f is not None and not f.done() for f in futures))


def _source(service, run):
    """Check immutable input without cancellation/time/model checks in _check."""
    from research_service import sha
    contract = run['contract']
    if not isinstance(contract, dict):
        raise ValueError('Некорректный контракт исходного поиска.')
    if sha(contract) != run.get('contract_sha256'):
        raise ValueError('Контракт исходного поиска изменён.')
    if run.get('claim') != contract.get('question'):
        raise ValueError('Цель исходного поиска изменена.')
    for key in ('proof_backend', 'source_lineage', 'paper_ids', 'section_ids', 'paper_manifest',
                'source_graph_ref', 'source_transition_id'):
        default = [] if key in ('paper_ids', 'section_ids', 'paper_manifest') else None
        if run.get(key, default) != contract.get(key, default):
            raise ValueError('Привязка исходного поиска изменена: ' + key)
    source = service._structure_input(run)
    if contract.get('source_transition'):
        if run.get('structure_input_kind') != 'literature_transition' or run.get('source_application_status') != 'not_verified':
            raise ValueError('Статус литературного источника изменён.')
        service._check_source_transition(source)
    else:
        current = service.structure_store().select(source['source_id'], source['selected_declaration']['name'])
        if (current['source_sha256'] != source['source_sha256'] or
                current['selected_declaration'] != source['selected_declaration']):
            raise ValueError('Закреплённая Lean-теорема отличается от исходного поиска.')
    return source


def _route(service, run, route, source):
    from research_service import parse_json, sha
    from research_structure import is_literature, normalize_candidates
    folder = service.folder(run['id'])
    prefix = 'structure/' + route['id'] + '/'
    saved, graph_hash = _read(folder, prefix + 'candidates.json')
    resolution, resolution_hash = _read(folder, prefix + 'source-reference-resolution.json')
    if (resolution.get('status') != 'validated' or resolution.get('proof_checked') is not False or
            resolution.get('input_source_sha256') != source['source_sha256']):
        raise ValueError('Происхождение кандидатов не прошло сохранённую проверку.')
    suffix = '-transition-candidates-v1' if is_literature(source) else '-candidates-v1'
    attempt = route['id'] + suffix
    response, response_hash = _read(folder, 'attempts/' + attempt + '/result.json')
    if response.get('status') != 'completed' or not isinstance(response.get('text'), str):
        raise ValueError('Ответ модели с кандидатами не завершён.')
    bindings = []
    graph, candidates = normalize_candidates(parse_json(response['text']), route, source, resolution_log=bindings)
    saved_cards = route.get('candidates')
    # Canonical ids added by merge are presentation metadata. Recovery rebuilds
    # the graph from the original response and does not trust those extra fields.
    def base_cards(cards):
        return [{k: v for k, v in c.items() if k not in
                 {'canonical_key', 'canonical_transition_id', 'canonical_run_id', 'duplicate_of'}}
                for c in cards] if isinstance(cards, list) else cards
    saved_cards, candidates = base_cards(saved_cards), base_cards(candidates)
    if graph != saved or candidates != saved_cards or bindings != resolution.get('bindings'):
        raise ValueError('Сохранённые кандидаты отличаются от ответа, источников или привязок.')
    graph = service._validate_graph_contracts(graph)
    return graph, dict(route_id=route['id'], route_sha256=sha(route),
                       candidates_sha256=graph_hash, resolution_sha256=resolution_hash,
                       response_sha256=response_hash, attempt_key=attempt)


def _merge(run, source, accepted):
    from research_structure import input_references, source_object
    graph = dict(title=run['title'], question=run['claim'], msc_codes=[],
                 objects=[source_object(source)], transitions=[], sources=input_references(source))
    seen = {key: {row['id']: row for row in graph[key]} for key in ('objects', 'transitions', 'sources')}
    for route, candidate_graph, _ in accepted:
        if route['msc_code'] and route['msc_code'] not in graph['msc_codes']:
            graph['msc_codes'].append(route['msc_code'])
        for key in seen:
            for row in candidate_graph[key]:
                prior = seen[key].get(row['id'])
                if prior is not None:
                    if prior != row:
                        raise ValueError('Противоречивые общие данные кандидатов: ' + row['id'])
                else:
                    seen[key][row['id']] = row
                    graph[key].append(row)
    return graph


def _receipt_path(snapshot):
    return 'partial-candidates/' + snapshot + '/snapshot.json'


def _collect(service, run):
    """Return public metadata plus private validated graph/manifest; no writes."""
    from research_objects import validate_graph
    from research_service import sha
    from research_structure import MAX_ROUTES
    view = dict(status='unavailable', snapshot_sha256=None, candidate_count=0,
                completed_route_ids=[], pending_route_ids=[], issues=[],
                kind='partial_structure_candidates', search_complete=False, proof_checked=False)
    if run.get('purpose') != 'structure' or run.get('graph_ref'):
        return view, None, None
    if run.get('status') not in STOPPED or _busy(service, run):
        view['issues'].append(_issue('active_run', 'Частичные кандидаты доступны после остановки процесса поиска.'))
        return view, None, None
    try:
        source = _source(service, run)
        routes = run.get('structure_routes', [])
        atlas_mode = run['contract'].get('search_scope') == 'atlas'
        limit = MAX_ROUTES
        if atlas_mode:
            import research_atlas
            research_atlas.validate_atlas_integrity(service, run)
            limit = research_atlas.normalize_options(run['contract'].get('atlas_options'))['max_deep_routes']
        if not isinstance(routes, list) or len(routes) > limit:
            raise ValueError('Некорректный сохранённый список направлений.')
        identifiers = [r.get('id') for r in routes if isinstance(r, dict)]
        if (len(identifiers) != len(routes) or len(set(identifiers)) != len(routes) or
                any(not isinstance(i, str) or not (ATLAS_ROUTE_ID if atlas_mode else ROUTE_ID).fullmatch(i) for i in identifiers)):
            raise ValueError('Некорректные или повторные ID направлений.')
    except (ValueError, KeyError, TypeError, OSError) as error:
        view['issues'].append(_issue('invalid_source', error))
        return view, None, None
    accepted = []
    for route in routes:
        identifier = route['id']
        if route.get('status') != 'complete':
            view['pending_route_ids'].append(identifier)
            if route.get('status') == 'failed':
                view['issues'].append(_issue('failed_route', route.get('reason') or 'Направление завершилось ошибкой.', identifier))
            continue
        # A complete empty retrieval has no model candidate artifact by design.
        if route.get('candidates') == [] and not route.get('hits'):
            view['completed_route_ids'].append(identifier)
            continue
        try:
            candidate_graph, receipt = _route(service, run, route, source)
            accepted.append((route, candidate_graph, receipt))
            view['completed_route_ids'].append(identifier)
        except (ValueError, KeyError, TypeError, AttributeError, OSError) as error:
            view['pending_route_ids'].append(identifier)
            view['issues'].append(_issue('invalid_route', error, identifier))
    if not accepted or not any(g['transitions'] for _, g, _ in accepted):
        return view, None, None
    try:
        graph = service._validate_graph_contracts(_merge(run, source, accepted))
        manifest = dict(schema_version=1, run_id=run['id'], contract_sha256=run['contract_sha256'],
                        input_source_sha256=source['source_sha256'],
                        routes=[receipt for _, _, receipt in accepted], graph_sha256=sha(graph))
        digest = sha(manifest)
        view.update(status='available', snapshot_sha256=digest, candidate_count=len(graph['transitions']))
        path = service.folder(run['id']) / _receipt_path(digest)
        if path.exists():
            receipt, _ = _read(service.folder(run['id']), _receipt_path(digest))
            if (receipt.get('manifest') != manifest or receipt.get('snapshot_sha256') != digest or
                    receipt.get('proof_checked') is not False or receipt.get('schema_version') != 1):
                raise ValueError('Сохранённый частичный снимок изменён.')
            ref = receipt['graph_ref']
            if set(ref) != {'id', 'revision'} or ref['revision'] != 1:
                raise ValueError('Некорректная версия частичного графа.')
            stored = service.registry.get(ref['id'], ref['revision'])
            if validate_graph(stored) != graph:
                raise ValueError('Частичный граф отличается от закреплённого снимка.')
            view.update(status='materialized', graph_ref=ref)
        return view, graph, manifest
    except (ValueError, KeyError, TypeError, OSError) as error:
        view.update(status='unavailable', snapshot_sha256=None, candidate_count=0)
        view.pop('graph_ref', None)
        view['issues'].append(_issue('invalid_snapshot', error))
        return view, None, None


def preview(service, run_id):
    return _collect(service, service.get(run_id))[0]


def enrich(service, run):
    result = copy.deepcopy(run)
    if run.get('purpose') != 'structure' or run.get('graph_ref'):
        return result
    result.pop('object_graph', None)
    result.pop('partial_graph_ref', None)
    view, _, _ = _collect(service, run)
    result['partial_search'] = view
    if view['status'] == 'materialized':
        ref = view['graph_ref']
        result['partial_graph_ref'] = ref
        result['object_graph'] = service.registry.get(ref['id'], ref['revision'])
    return result


def materialize(service, run_id, expected_snapshot_sha256):
    from research_service import atomic
    if not isinstance(expected_snapshot_sha256, str) or not DIGEST.fullmatch(expected_snapshot_sha256):
        raise ValueError('Укажите точный SHA-256 частичного снимка.')
    # Existence/read before _guard prevents creating a directory for an invalid ID.
    service.get(run_id)
    with service._guard(run_id):
        view, graph, manifest = _collect(service, service.get(run_id))
        if view['status'] == 'unavailable':
            raise ValueError('Частичные кандидаты недоступны: ' + '; '.join(i['message'] for i in view['issues']))
        if view['snapshot_sha256'] != expected_snapshot_sha256:
            raise ValueError('Частичные кандидаты изменились; обновите результат поиска.')
        if view['status'] == 'materialized':
            return view
        stored = service.registry.create(graph, idempotency_key=run_id + '-partial-' + expected_snapshot_sha256)
        ref = dict(id=stored['id'], revision=stored['revision'])
        receipt = dict(schema_version=1, snapshot_sha256=expected_snapshot_sha256, manifest=manifest,
                       graph_ref=ref, proof_checked=False, search_complete=False)
        atomic(service.folder(run_id) / _receipt_path(expected_snapshot_sha256), receipt)
        return dict(view, status='materialized', graph_ref=ref)
