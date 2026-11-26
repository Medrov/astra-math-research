"""Ground a pattern search in a snapshot of compiler-checked Lean declarations."""
from __future__ import annotations

from functools import lru_cache
import json
from pathlib import Path
import re

import lean_service
import research_registry as registry
from research_lean_files import LeanFiles


MAX_SOURCES = 12


def _tokens(statement):
    # Preserve quoted literals and identifier boundaries across formatting changes.
    return tuple(re.findall(r'"(?:[^"\\]|\\.)*"|[\w\']+|[^\s]', statement))


@lru_cache(maxsize=1)
def _taxonomy():
    nodes = json.loads((Path(__file__).parent / 'data/msc2020.json').read_text())['nodes']
    return {node['id']: node['parent_id'] for node in nodes}


def scope_codes(codes):
    if not isinstance(codes, list) or len(codes) > 12 or any(not isinstance(c, str) or c not in _taxonomy() for c in codes):
        raise ValueError('Нужны до 12 существующих кодов MSC.')
    return list(dict.fromkeys(codes))


def _descendants(codes):
    if not codes:
        return None
    parents = _taxonomy()
    result = set(codes)
    for code, parent in parents.items():
        while parent:
            if parent in result:
                result.add(code)
                break
            parent = parents.get(parent)
    return result


def _attached(root, sources):
    store = LeanFiles(Path(root) / 'lean-files')
    groups = []
    for source in sources:
        if source.get('bundle_format'):
            continue
        report = store.get(source['id'])
        meta, modules = store._load(source['id'])
        if (report.get('status') not in ('verified','compiled') or report['audit']['status'] != 'passed'
                or report['sha256'] != source['sha256'] or meta['sha256'] != source['sha256']):
            raise ValueError('Не удалось подтвердить происхождение исходного Lean-файла.')
        # Only declarations authored in the submitted source qualify. Lean generates
        # additional equation lemmas/recursors for a single user definition.
        authored = {m['module']: {d['name'] for d in lean_service.lexical_declarations(m['content'])} for m in modules}
        items = []
        for d in report['declarations']:
            name = d['name']
            if d['kind'] not in ('theorem','def','opaque','inductive'):
                continue
            if not any(name == n or name.endswith('.'+n) for n in authored.get(d['module'], ())):
                continue
            statement = meta['expected_statement'] if meta.get('target') == name and meta.get('expected_statement') else d['type']
            if not statement or len(statement) > 20000:
                continue
            items.append(dict(name=name, statement=statement, kind='attachment', declaration_kind=d['kind'],
                              module=d['module'], sha256=meta['sha256'], attachment_id=source['id'],
                              title=source['name'], url='/api/research/lean-files/'+source['id']+'/download'))
        groups.append(items)
    # Round-robin keeps multiple selected attachments represented.
    return [group[i] for i in range(max(map(len,groups), default=0)) for group in groups if i < len(group)]


def snapshot(research, question, codes, case, sources):
    items = _attached(research.root, sources)
    env = case.get('agent_task')
    # Files explicitly supplied for comparison define the search corpus; a
    # selected topic/MSC/fixture can additionally bring in certified archive data.
    if not sources or case or codes:
        registry.refresh(research.root)
        cards = registry.search(research.root, question, scope_codes=_descendants(codes),
                                scope_context=registry.context_hash(env) if env else None, limit=60)
        for card in cards:
            try:
                registry.load_source(research.root, card)
            except (OSError, ValueError):
                continue
            items.append(dict(name=card['name'], statement=card['statement'], kind='archive',
                              declaration_kind='theorem', title=card['title'], source_run_id=card['source_run_id'],
                              context_sha256=card['context_sha256'], url=card['url'], sha256=card['source_sha256']))
    unique, names, propositions = [], set(), set()
    for item in items:
        name, statement = item['name'], _tokens(item['statement'])
        if name in names or (item['declaration_kind'] == 'theorem' and statement in propositions):
            continue
        names.add(name)
        if item['declaration_kind'] == 'theorem':
            propositions.add(statement)
        unique.append(dict(item,id='S'+str(len(unique)+1)))
        if len(unique) == MAX_SOURCES:
            break
    if len(unique) < 2:
        if not sources and not case:
            from research_pattern_catalog import find_theorems
            catalog = find_theorems(question, codes, MAX_SOURCES)
            if len(catalog) >= 2:
                modules = list(dict.fromkeys(s['module'] for s in catalog))
                return [dict(s, id='S'+str(i)) for i, s in enumerate(catalog, 1)], {'imports':modules, 'prelude':''}
        raise ValueError('Для поиска нужны минимум две разные проверенные декларации. Выберите другую область MSC или приложите .lean/ZIP с двумя объектами.')
    # Topic-only searches can use the same immutable environment as their archive
    # without asking the model to reconstruct definitions from theorem names.
    if not env and not sources and len({s['context_sha256'] for s in unique}) == 1:
        seed = unique[0]
        env = archive_environment(research.root,seed)
    return unique, env


def archive_environment(root,source):
    plan = json.loads((Path(root) / source['source_run_id'] / 'plan.json').read_text())
    if registry.context_hash(plan) != source['context_sha256']:
        raise ValueError('Изменились определения, в которых проверялся архивный результат.')
    return {k:plan[k] for k in ('imports','prelude')}


def validate_proposal(state, task, proposal):
    ids, connection = proposal.get('source_ids'), proposal.get('pattern')
    seeds = {s['id']:s for s in state['pattern_sources']}
    if (not isinstance(ids,list) or not 2 <= len(ids) <= len(seeds)
            or any(not isinstance(i,str) or i not in seeds for i in ids) or len(set(ids))!=len(ids)):
        raise ValueError('Укажите как минимум два разных ID из исходных проверенных объектов.')
    # Some Astra turns put their full observation in reason. Preserve its actual
    # text only when it describes the named inputs; never synthesize a relation
    # by concatenating a generic scheduling reason and the IDs from the array.
    reason = proposal.get('reason','')
    if isinstance(connection,str) and not connection.strip() and isinstance(reason,str):
        cited = [i for i in ids if re.search(r'(?<!\w)'+re.escape(i)+r'(?!\w)',reason)
                 or seeds[i]['name'] in reason]
        content = re.sub(r'\bS\d+\b','',reason)
        description = re.search(r'монотон|равенств|неравенств|формул|сумм|зависимост|оценк|инвариант|'
                                r'услови|отображени|операц|структур|функци|величин|границ|разложени|'
                                r'композици|симметр|связыва|переход|обобщ|квадрат|эквивален|[=≤≥∀↔→]',
                                content,re.IGNORECASE)
        if len(cited)>=2 and len(content.strip())>=60 and description:
            connection = reason
    if not isinstance(connection,str) or not 5 <= len(connection.strip()) <= 4000:
        raise ValueError('Опишите общую математическую структуру выбранных объектов.')
    statement = _tokens(task['statement'])
    if any(s['name']==task['target'] or _tokens(s['statement'])==statement for s in seeds.values()):
        raise ValueError('Нужна новая проверяемая гипотеза. Предложена исходная декларация.')
    for previous in checked_tasks(state):
        if (previous['imports']==task['imports'] and previous['prelude']==task['prelude']
                and _tokens(previous['statement'])==statement):
            raise ValueError('Эта гипотеза уже проверена в той же среде.')
    task.update(source_ids=ids, pattern=connection.strip())


def checked_tasks(state):
    return [t for t in state['tasks'] if t.get('source_ids') and t['outcome'] in ('proved','refuted')
            and (not state['attachment_ids'] or (t.get('source_check') or {}).get('status')=='verified')]


def handoff(state, task):
    return dict(mode='patterns', pattern=task['pattern'], source_ids=task['source_ids'],
                pattern_sources=[s for s in state['pattern_sources'] if s['id'] in task['source_ids']])
