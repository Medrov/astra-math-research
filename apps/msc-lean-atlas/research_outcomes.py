"""Read-only presentation of search, formalization and proof evidence.

No status here creates a certificate or changes a saved research result. Empty
searches, incomplete proofs and infrastructure failures are different outcomes.
"""
from __future__ import annotations

import hashlib


ACTIVE = {'queued', 'running'}
PROOF_STAGES = {'prove', 'verify', 'compose', 'certify_transition', 'retrieve_obligation'}
TECHNICAL_CODES = {'infrastructure', 'internal_error', 'model_response_invalid',
                   'library_context_failed', 'proof_audit_rejected', 'proof_audit_failed'}


def obligations(run):
    contract = run.get('object_contract') or {}
    graph = contract.get('graph') or run.get('object_graph') or {}
    selected = contract.get('transition_id') or run.get('selected_transition_id')
    transition = next((t for t in graph.get('transitions', []) if t.get('id') == selected), {})
    return transition.get('obligations') or (run.get('formal_contract') or {}).get('required_obligations') or []


def _verified(report):
    return (isinstance(report, dict) and report.get('success') is True and
            report.get('target_preserved') is True and (report.get('audit') or {}).get('status') == 'passed')


def _final_matches(run, report):
    if not _verified(report) or report.get('obligations_passed') is not True:
        return False
    graph = (run.get('object_contract') or {}).get('graph') or run.get('object_graph') or {}
    selected = (run.get('object_contract') or {}).get('transition_id') or run.get('selected_transition_id')
    transition = next((t for t in graph.get('transitions', []) if t.get('id') == selected), {})
    task = transition.get('agent_task') or run.get('formal_contract') or (run.get('contract') or {}).get('agent_task') or {}
    if (not task.get('target') or not task.get('statement') or report.get('target') != task['target'] or
            report.get('expected_statement') != task['statement']):
        return False
    checked = report.get('obligations') or []
    goals = obligations(run)
    if len(checked) != len(goals):
        return False
    for goal in goals:
        matched = [item for item in checked if item.get('id') == goal['id']]
        if len(matched) != 1:
            return False
        item = matched[0]
        if (item.get('ok') is not True or item.get('target') != goal['target'] or
                item.get('statement_sha256') != hashlib.sha256(goal['statement'].encode('utf-8')).hexdigest()):
            return False
    return True


def proof_progress(run):
    goals = obligations(run)
    nodes = {n.get('id'): n for n in run.get('nodes', []) if isinstance(n, dict)}
    verified = {name for name, node in nodes.items() if _verified(node.get('verification'))}
    # Only exact required targets count; an auxiliary lemma is still useful but
    # must not inflate the number of completed obligations.
    def matches(goal):
        node = nodes.get(goal.get('target'), {})
        report = node.get('verification') or {}
        return (goal.get('target') in verified and node.get('statement') == goal.get('statement') and
                report.get('target') == goal.get('target') and
                report.get('expected_statement') == goal.get('statement'))
    proved = sum(matches(o) for o in goals)
    failed = sum(nodes.get(o.get('target'), {}).get('status') in ('failed', 'unproved')
                 and o.get('target') not in verified for o in goals)
    final = (run.get('result') or {}).get('verification') or run.get('verification') or {}
    full_verified = _final_matches(run, final)
    if full_verified:
        proved = len(goals)
    events = run.get('events') or []
    started = (bool(verified) or any(a.get('role') == 'prove' for a in run.get('attempts', [])) or
               any(e.get('phase') in PROOF_STAGES for e in events) or
               run.get('phase') in PROOF_STAGES)
    termination = run.get('termination') or (run.get('result') or {}).get('termination') or {}
    return dict(started=started, obligations_total=len(goals), proved=proved,
                failed=failed, pending=max(0, len(goals)-proved-failed),
                verified_lemmas=len(verified), active_stage=run.get('active_stage') or run.get('phase'),
                stop_kind=termination.get('code'), full_contract_verified=full_verified)


def outcome_summary(run):
    result = run.get('result') or {}
    stop = run.get('termination') or result.get('termination') or {}
    code, stage = stop.get('code'), stop.get('stage') or run.get('active_stage') or run.get('phase')
    reason = str(stop.get('message') or result.get('reason') or run.get('error') or '')[:4000]
    progress = proof_progress(run)
    finding = dict(category='pending', title='Проверка ещё не начата', stage=stage,
                   technical_failure=False, reason=reason, search_status='not_applicable',
                   proof_status='not_started')
    active = run.get('status') in ACTIVE and not run.get('ready_to_start')
    search = run.get('purpose') in ('discover', 'structure')
    if search:
        finding['proof_status'] = 'not_applicable'
        routes = run.get('structure_routes') or []
        graph = run.get('object_graph') or {}
        count = (len(graph.get('transitions') or []) if 'transitions' in graph else
                 sum(not c.get('duplicate_of') for r in routes for c in r.get('candidates', [])))
        summary = run.get('atlas_summary') or {}
        incomplete = (run.get('status') != 'complete' or summary.get('status') == 'partial' or
                      any(r.get('status') == 'failed' for r in routes))
        if active:
            finding.update(category='searching', title='Поиск выполняется', search_status='running')
        elif code in ('cancelled', 'budget_exhausted') or run.get('status') in ('cancelled', 'budget_exhausted', 'interrupted'):
            finding.update(category='search_partial', title='Поиск остановлен · результаты сохранены', search_status='partial')
        elif run.get('status') == 'failed':
            finding.update(category='search_error', title='Поиск остановлен из-за ошибки',
                           search_status='partial', technical_failure=True)
        elif count:
            finding.update(category='candidates_found', title=f'Найдены кандидаты: {count}',
                           search_status='partial' if incomplete else 'complete')
        elif run.get('status') == 'complete':
            finding.update(category='search_partial' if incomplete else 'no_supported_candidates',
                           title='Поиск выполнен частично' if incomplete else 'В рассмотренных источниках кандидаты не найдены',
                           search_status='partial' if incomplete else 'complete')
        else:
            finding.update(search_status='not_started', title='Поиск ещё не начат')
        return finding
    verification = result.get('verification') or run.get('verification') or {}
    semantic = run.get('final_semantic_review') or result.get('semantic_review') or {}
    if _final_matches(run, verification):
        formal = run.get('formal_outcome') or verification.get('outcome') or run.get('outcome')
        if formal == 'refuted':
            finding.update(category='refuted', title='Проверено формальное опровержение', proof_status='refuted')
        elif semantic.get('status') in ('aligned', 'reviewed_fixture'):
            finding.update(category='proved', title='Формальный контракт проверен', proof_status='proved')
        else:
            finding.update(category='semantic_review_needed', title='Lean проверен · нужна смысловая рецензия',
                           proof_status='formal_only')
        return finding
    if active:
        finding.update(category='proving' if progress['started'] else 'preparing',
                       title='Доказательство выполняется' if progress['started'] else 'Готовим и проверяем постановку',
                       proof_status='running' if progress['started'] else 'not_started')
    elif code in ('cancelled', 'budget_exhausted') or run.get('status') in ('cancelled', 'budget_exhausted', 'interrupted'):
        finding.update(category='proof_incomplete' if progress['started'] else 'preparation_incomplete',
                       title='Проверка остановлена · результат неполный', proof_status='incomplete')
    elif code in TECHNICAL_CODES or code == 'lean_timeout':
        finding.update(category='infrastructure_error', title='Проверке помешала техническая ошибка',
                       technical_failure=True, proof_status='incomplete' if progress['started'] else 'not_started')
    elif progress['started'] or code in ('lean_unproved', 'proof_not_produced'):
        # In particular, legacy Goedel ValueErrors after a typed preflight must
        # never be presented as a rejection of that accepted formalization.
        finding.update(category='proof_incomplete', title='Доказательство не завершено', proof_status='incomplete')
    elif (run.get('contract_verification') or {}).get('well_typed') is False or \
            code == 'invalid_contract' and stage in ('formalize_transition', 'lean_contract_preflight', 'validate_contract'):
        finding.update(category='formalization_failed', title='Lean отклонил формальную постановку', proof_status='not_started')
    elif code == 'needs_review' or run.get('requires_review'):
        finding.update(category='semantic_review_needed', title='Постановка требует уточнения', proof_status='not_started')
    elif run.get('status') == 'failed':
        finding.update(category='infrastructure_error', title='Подготовка проверки остановлена',
                       technical_failure=True, proof_status='not_started')
    return finding
