"""Inspectable source cards; citations are evidence, never proof certificates."""
from __future__ import annotations

import copy


def complete_grounding(transition):
    """Missing support is explicitly an inference, never an invented citation."""
    items = copy.deepcopy(transition.get('grounding', []))
    required = ['construction', 'claim'] + ['assumption:' + str(i) for i in range(len(transition['assumptions']))]
    required += ['object:' + identifier for identifier in dict.fromkeys(transition['source_ids'] + transition['target_ids'])]
    present = {item['component'] for item in items}
    for component in required:
        if component not in present:
            items.append(dict(component=component, source_ref='', quote='', origin='proposed_abstraction'))
    return items


def validate_grounding(items, references, evidence=None):
    if not isinstance(items, list) or len(items) > 48:
        raise ValueError('Разметка источника должна содержать не более 48 элементов.')
    result = []
    for item in items:
        if not isinstance(item, dict) or set(item) != {'component', 'source_ref', 'quote', 'origin'}:
            raise ValueError('Неверный формат привязки к источнику.')
        if item['origin'] not in ('source_excerpt', 'proposed_abstraction', 'user_revision'):
            raise ValueError('Неизвестное происхождение утверждения.')
        if any(not isinstance(item[k], str) or len(item[k]) > limit for k, limit in
               [('component', 500), ('source_ref', 80), ('quote', 4000)]):
            raise ValueError('Слишком длинная или некорректная разметка источника.')
        if not item['component'].strip():
            raise ValueError('Укажите элемент математической карточки.')
        ref = item['source_ref']
        if ref and ref not in references:
            raise ValueError('Разметка ссылается на неизвестный источник.')
        if item['origin'] == 'source_excerpt':
            if not ref or not item['quote'].strip():
                raise ValueError('Утверждению из источника нужна точная цитата.')
            if evidence is not None:
                row = evidence.get(ref, {})
                text = str(row.get('content') or row.get('text') or row.get('statement') or '')
                if ' '.join(item['quote'].split()) not in ' '.join(text.split()):
                    raise ValueError('Цитата отсутствует в предоставленном фрагменте источника: ' + ref)
        elif item['quote']:
            raise ValueError('Предложенное обобщение нельзя представлять как цитату.')
        result.append(copy.deepcopy(item))
    return result


def source_card(run):
    graph = run.get('object_graph') or (run.get('object_contract') or {}).get('graph') or {}
    transition = next((t for t in graph.get('transitions', [])
                       if t['id'] == run.get('selected_transition_id')), None)
    library = run.get('contract', {}).get('source_library')
    if transition is None and library:
        selected = library['selected_declaration']
        profile = run.get('structure_profile') or {}
        return dict(version=1, title=library.get('title') or selected['name'], kind='lean',
                    source_status='verified_formal_source', graph_ref=run.get('graph_ref'), transition_id=None,
                    input_objects=[dict(id=selected['name'], title=selected['name'], definition=selected['type'],
                                        parameters=[], assumptions=[])], output_objects=[],
                    operations=profile.get('operations', []), assumptions=profile.get('assumptions', []),
                    conclusion=profile.get('conclusion_shape') or selected['type'], formal_statement=selected['type'],
                    sources=[dict(id=library['source_id'], title=library.get('title') or selected['name'], url='',
                                  locator=selected['name'], snapshot_sha256=library['source_sha256'])], grounding=[],
                    scope='Lean подтверждает указанную теорему; структурное описание предложено моделью.', editable=False)
    if transition is None:
        return None
    fields = ('id', 'title', 'definition', 'parameters', 'assumptions')
    def objects(ids):
        return [{key: copy.deepcopy(obj.get(key)) for key in fields}
                for obj in graph.get('objects', []) if obj['id'] in ids]
    refs = set(transition.get('source_refs', []))
    sources = [copy.deepcopy(s) for s in graph.get('sources', []) if s['id'] in refs]
    # Only retained source excerpts may be displayed as quotations.
    evidence = {}
    for row in run.get('evidence', []):
        source_ref = row.get('source')
        url = source_ref.get('url', row.get('url')) if isinstance(source_ref, dict) else row.get('url')
        if url:
            evidence[url] = row
    for source in sources:
        match = evidence.get(source.get('url'))
        if match and source.get('url'):
            source['excerpt'] = str(match.get('content') or match.get('text') or '')[:6000]
    task = transition.get('agent_task') or {}
    literary = bool(run.get('paper_ids') or run.get('contract', {}).get('source_transition'))
    return dict(version=1, title=transition['title'], kind='literature' if literary else 'transition',
                source_status='literature_not_compiler_verified' if literary else 'proposed_transition',
                graph_ref=run.get('graph_ref'), transition_id=transition['id'],
                input_objects=objects(transition['source_ids']), output_objects=objects(transition['target_ids']),
                operations=[transition['construction']], assumptions=copy.deepcopy(transition['assumptions']),
                conclusion=transition['claim'], formal_statement=task.get('statement'), sources=sources,
                grounding=copy.deepcopy(transition.get('grounding', [])),
                scope=('Применение к исходной статье требует отдельной проверки.' if literary else
                       'Статус доказательства и смысловая рецензия показаны отдельно.'), editable=True)
