"""Create an explicit, unstarted correction version; never mutate old results."""
from __future__ import annotations

import copy
import hashlib
import json
from pathlib import Path
import re


def _same_task(formalization, transition):
    return (isinstance(formalization, dict) and formalization.get('status') == 'ready' and
            formalization.get('agent_task') == transition.get('agent_task') and
            formalization.get('obligations') == transition.get('obligations'))


def _accepted_seed(service, run):
    """Select retained formal data, never a parent's proof or acceptance result."""
    from research_service import sha
    from research_objects import validate_graph
    if sha(run['contract']) != run['contract_sha256']:
        raise ValueError('Контракт предыдущей попытки изменён.')
    if run.get('object_contract') and sha(run['object_contract']) != run.get('object_contract_sha256'):
        raise ValueError('Зафиксированная постановка предыдущей попытки изменена.')
    if (run.get('revision_draft') is not None or 'revision_draft_sha256' in run['contract']) and \
            sha(run.get('revision_draft')) != run['contract'].get('revision_draft_sha256'):
        raise ValueError('Исходный черновик предыдущей версии изменён.')
    if not run.get('object_graph') or not run.get('selected_transition_id'):
        return None, None
    graph = validate_graph(run['object_graph'])
    transition = service._transition(graph, run['selected_transition_id'])
    origin = dict(parent_run_id=run['id'], parent_contract_sha256=run['contract_sha256'],
                  parent_graph_ref=copy.deepcopy(run.get('graph_ref')),
                  parent_transition_id=run['selected_transition_id'])
    if run.get('library_context'):
        from research_library_context import _read_receipt
        receipt = _read_receipt(service, run, required=True)
        seed = copy.deepcopy(receipt['formalization'])
        if transition.get('agent_task') and not _same_task(seed, transition):
            raise ValueError('Библиотечный черновик не совпадает с принятой постановкой.')
        return seed, dict(origin, source='library_context', library_context=copy.deepcopy(run['library_context']),
                          parent_object_contract_sha256=run.get('object_contract_sha256'), seed_sha256=sha(seed))
    if transition.get('agent_task'):
        obj = run.get('object_contract')
        if obj:
            fixed = service._transition(obj['graph'], obj['transition_id'])
            if fixed['agent_task'] != transition['agent_task'] or fixed['obligations'] != transition['obligations']:
                raise ValueError('Отображаемый переход отличается от закреплённой постановки.')
        review = run.get('formalization_review')
        if isinstance(review, dict) and review.get('status') == 'ready':
            if not _same_task(review, transition):
                raise ValueError('Принятая формализация не совпадает с закреплённой постановкой.')
            seed = copy.deepcopy(review)
        else:
            # Compatibility for prepared fixtures/legacy graphs without a full
            # formalizer record. The exact task and all obligations remain intact.
            seed = dict(status='ready', reason='Исходный черновик предыдущей попытки', limitations=[],
                        agent_task=copy.deepcopy(transition['agent_task']), obligations=copy.deepcopy(transition['obligations']))
        return seed, dict(origin, source='bound_graph_task',
                          parent_object_contract_sha256=run.get('object_contract_sha256'), seed_sha256=sha(seed))

    # A run may stop after a successful type preflight but before binding a graph
    # (e.g. a later library-context failure). Preserve its last accepted repair,
    # not the earlier raw formalizer response or an unchecked in-progress draft.
    previous, accepted = None, (None, None)
    folder = service.folder(run['id'])
    drafts = sorted((p for p in (folder / 'drafts').glob('v*/draft.json')
                     if re.fullmatch(r'v[0-2]', p.parent.name)), key=lambda p: p.parent.name)
    for version, path in enumerate(drafts):
        record = json.loads(path.read_text(encoding='utf-8'))
        if path.parent.name != 'v' + str(version) or record.get('version') != version or \
                record.get('intent_sha256') != sha(graph) or record.get('parent_sha256') != previous or \
                record.get('draft_sha256') != sha(record.get('formalization')):
            raise ValueError('Цепочка сохранённых черновиков предыдущей попытки изменена.')
        previous = record['draft_sha256']
        report_path = path.parent / 'verification.json'
        if not report_path.exists():
            continue
        report = json.loads(report_path.read_text(encoding='utf-8'))
        if report.get('well_typed') is not True:
            continue
        seed = record['formalization']
        task = dict(seed['agent_task'], required_obligations=seed['obligations'])
        harness = (Path(report.get('workspace', '')) / 'ContractTypes.lean').resolve()
        if report.get('status') != 'complete' or report.get('proof_checked') is not False or \
                report.get('audit', {}).get('status') != 'passed' or report.get('contract_sha256') != sha(task) or \
                not harness.is_relative_to(folder.resolve()) or not harness.is_file() or \
                hashlib.sha256(harness.read_bytes()).hexdigest() != report.get('source_sha256'):
            raise ValueError('Проверка типов сохранённого черновика не подтверждена артефактами.')
        accepted = copy.deepcopy(seed), dict(origin, source='typed_draft', version=version,
            draft_path=path.relative_to(folder).as_posix(), draft_record_sha256=sha(record),
            preflight_path=report_path.relative_to(folder).as_posix(), preflight_sha256=sha(report),
            preflight_source_sha256=report['source_sha256'], seed_sha256=sha(seed))
    return accepted


class ResearchVersionsMixin:
    def revision_options(self, run):
        if run.get('status') in ('running', 'queued', 'cancelling'):
            return dict(can_preserve_formalization=False, default_preserve_formalization=False,
                        source=None, reason='Сначала завершите или остановите текущую попытку.')
        try:
            seed, provenance = _accepted_seed(self, run)
        except (ValueError, OSError, KeyError, TypeError) as error:
            return dict(can_preserve_formalization=False, default_preserve_formalization=False,
                        source=None, reason=str(error))
        return dict(can_preserve_formalization=seed is not None, default_preserve_formalization=seed is not None,
                    source=(provenance or {}).get('source'),
                    reason=('Сохранить точные определения, импорты и все обязательства; проверки будут выполнены заново.'
                            if seed is not None else 'Принятая постановка отсутствует; требуется новая формализация.'))

    def revise_run(self, run_id, payload):
        from research_service import atomic, sha
        from research_objects import validate_graph
        old = self.detail(run_id)
        if old['status'] in ('running', 'queued', 'cancelling'):
            raise ValueError('Сначала остановите текущую попытку, чтобы создать исправленную версию.')
        reason = payload.get('reason')
        if not isinstance(reason, str) or not 3 <= len(reason.strip()) <= 2000:
            raise ValueError('Укажите причину новой версии (3–2000 символов).')
        changes = payload.get('corrections', {})
        preserve = payload.get('preserve_formalization', True)
        if not isinstance(preserve, bool):
            raise ValueError('preserve_formalization должен быть логическим значением.')
        allowed = {'title', 'claim', 'construction', 'assumptions'}
        if not isinstance(changes, dict) or set(changes) - allowed:
            raise ValueError('Разрешено исправить название, вывод, конструкцию и предпосылки карточки.')
        if not old.get('object_graph') or not old.get('selected_transition_id'):
            raise ValueError('Для исправления сначала выберите конкретный математический переход.')
        graph = validate_graph(old['object_graph'])
        transition = self._transition(graph, old['selected_transition_id'])
        mathematical_changes = set(changes) - {'title'}
        seed, seed_provenance = _accepted_seed(self, old) if preserve and not mathematical_changes else (None, None)
        for key, value in changes.items():
            if key == 'assumptions':
                if not isinstance(value, list) or len(value) > 32 or any(not isinstance(v, str) or not v.strip() or len(v) > 3000 for v in value):
                    raise ValueError('Предпосылки должны быть списком непустых строк.')
            elif not isinstance(value, str) or not value.strip() or len(value) > (300 if key == 'title' else 12000):
                raise ValueError('Некорректное поле карточки: ' + key)
            transition[key] = copy.deepcopy(value)
        transition.update(formulation_status='literature_only', agent_task=None, obligations=[], case_id=None)
        if changes:
            aliases = {'claim': {'claim', 'conclusion'}, 'construction': {'construction', 'operation', 'operations'},
                       'assumptions': {'assumptions'}, 'title': {'title'}}
            replaced = set().union(*(aliases[k] for k in changes))
            retained = [g for g in transition.get('grounding', []) if g['component'] not in replaced
                        and not ('assumptions' in changes and g['component'].startswith('assumption:'))]
            components = [key for key in changes if key != 'assumptions']
            if 'assumptions' in changes:
                components += ['assumption:' + str(i) for i in range(len(transition['assumptions']))]
            transition['grounding'] = retained + [dict(component=k, source_ref='', quote='', origin='user_revision') for k in components]
        # This version contains only the chosen transition, with unchanged objects and source snapshots.
        graph['transitions'] = [transition]
        graph['question'] = transition['claim']
        graph['title'] = transition['title']
        graph = self._validate_graph_contracts(graph)
        stored = self.registry.create(graph)
        lineage = dict(parent_run_id=old['id'], root_run_id=(old.get('source_lineage') or {}).get('root_run_id') or old['id'],
                       kind='correction', reason=reason.strip())
        new = self.create(dict(graph_id=stored['id'], graph_revision=stored['revision'], transition_id=transition['id'],
                               purpose='prove', mode=old['mode'] if old['mode'] != 'pilot' else 'multi',
                               proof_backend=payload.get('proof_backend', old.get('proof_backend', 'native')),
                               question=transition['claim'], title=transition['title'],
                               budget=dict(max_calls=old['budget']['max_calls'] or 8,
                                           timeout_seconds=old['budget']['timeout_seconds'])),
                          start=False)
        contract = new['contract']
        contract['source_lineage'] = lineage
        contract['preserve_formalization'] = seed is not None
        contract['revision_seed_policy'] = ('preserved' if seed is not None else 'mathematical_changes' if mathematical_changes
                                           else 'reformalize_requested' if not preserve else 'no_accepted_formalization')
        if seed:
            contract['revision_draft_sha256'] = sha(seed)
            contract['revision_seed_provenance'] = seed_provenance
        atomic(self.folder(new['id']) / 'contract-v1.json', contract)
        self.update(new['id'], contract=contract, contract_sha256=sha(contract), source_lineage=lineage,
                    revision_draft=seed, status='draft', phase='draft', ready_to_start=True)
        self.event(new['id'], 'draft', 'Создана новая версия. Исходная попытка сохранена. Запуск выполняется отдельно.',
                   preserve_formalization=seed is not None, revision_seed_policy=contract['revision_seed_policy'])
        return self.detail(new['id'])
