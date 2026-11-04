"""Goedel-Architect graph core adapted to SHAIM's proof-complete Lean policy.

Blueprints are JSON data. Only complete proofs are sent to Lean. Model calls,
budgets, cancellation and durable attempts remain owned by ResearchService.
The unchanged upstream CLI and its incomplete Lean blueprints are not executed.
"""
from __future__ import annotations

from concurrent.futures import ThreadPoolExecutor, as_completed
import copy
import hashlib
import json
from pathlib import Path

import research_lean
from tools.goedel import upstream_core as core

BACKEND_ID = 'goedel-adapted'
UPSTREAM_COMMIT = '300d69e97c91a2a498091c898e736af69f391960'
CORE_ROOT = Path(__file__).resolve().parent / 'tools' / 'goedel'
ADAPTER_VERSION = 1


def backend_metadata():
    """Report actual vendored code identity; readiness does not mean a proof."""
    manifest = json.loads((CORE_ROOT / 'upstream-manifest.json').read_text(encoding='utf-8'))
    files = manifest['files']
    valid = manifest.get('commit') == UPSTREAM_COMMIT and all(
        hashlib.sha256((CORE_ROOT / name).read_bytes()).hexdigest() == checksum
        for name, checksum in files.items())
    return dict(id=BACKEND_ID, title='Goedel-Architect · адаптированный',
                status='ready' if valid else 'invalid_installation',
                version=ADAPTER_VERSION, upstream_commit=UPSTREAM_COMMIT,
                upstream_url=manifest['repository'], license=manifest['license'],
                core_sha256=files['upstream_core.py'],
                adapter_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
                integration='adapted_graph_core_not_stock_cli',
                lean_version='4.19.0', blueprint_format='typed_json_no_proof_holes',
                model_transport='research_service_codex',
                upstream_functions=['validate_blueprint_graph', 'graft_proof_body',
                                    'analyze_blueprint_from_trace', 'classify_axioms'],
                limitations=['Производная интеграция ядра; не неизменённый upstream CLI.',
                             'Превосходство над native не установлено; результаты сравниваются отдельно.'])


def _nodes(plan):
    return [core.BlueprintNode(
        name=n['id'], kind='theorem', is_target=True, raw_source='', attr_source='',
        decl_source='', signature=research_lean.theorem_header(n['id'], n['statement']).removesuffix(' := '),
        body_source='', informal_statement=n.get('title') or n['statement'],
        informal_proof=plan.get('summary') or 'Use the declared dependency graph.',
        depends_on=list(n.get('dependencies', []))) for n in plan['nodes']]


def validate_blueprint(plan, contract):
    """Apply native exact-contract validation and the real upstream DAG gate.

The virtual root is data only: it preserves all mandatory goals, even when they
are independent of the primary theorem. No synthetic Lean theorem is emitted.
"""
    from research_service import validate_plan
    plan = validate_plan(copy.deepcopy(plan), contract)
    nodes = _nodes(plan)
    roots = list(dict.fromkeys([plan['target_id']] + [
        o['target'] for o in contract.get('required_obligations', [])]))
    root_name = '_AtlasRequiredGoals'
    while any(n.name == root_name for n in nodes):
        root_name += '_'
    nodes.append(core.BlueprintNode(root_name, 'theorem', True, '', '', '', '', '',
                                  'All mandatory goals', 'Check every required goal', roots))
    issues = core.validate_blueprint_graph('', nodes, root_name)
    if issues:
        raise ValueError('Goedel blueprint: ' + '; '.join(issue['message'] for issue in issues))
    return plan


def blueprint_analysis(plan, established):
    """Upstream reachability analysis on structured nodes, never Lean stubs."""
    trace = {'node_results': {n['id']: dict(success=n['id'] in established,
        proof_body=established.get(n['id'], {}).get('declaration', ''),
        depends_on=n.get('dependencies', [])) for n in plan['nodes']}}
    analyses = [core.analyze_blueprint_from_trace(trace, name, parsed_nodes=_nodes(plan))
                for name in plan.get('required_roots', [plan['target_id']])]
    return dict(reachable=sorted(set().union(*(a.reachable for a in analyses))),
                frozen=sorted(set().union(*(a.frozen for a in analyses))),
                unsolved=sorted(set().union(*(a.unsolved_targets for a in analyses))),
                effective_dependencies={name: sorted(deps) for a in analyses for name, deps in a.effective_deps.items()},
                method='upstream_textual_reachability_not_kernel_dependencies')


def _pin_backend(service, run_id):
    from research_service import atomic
    metadata = backend_metadata()
    if metadata['status'] != 'ready':
        raise ValueError('Установка ядра Goedel-Architect не соответствует закреплённым хешам.')
    path = service.folder(run_id) / 'proof-backend.json'
    if path.exists():
        old = json.loads(path.read_text(encoding='utf-8'))
        if any(old.get(k) != metadata.get(k) for k in ('id', 'version', 'core_sha256', 'adapter_sha256', 'upstream_commit')):
            raise ValueError('Движок доказательств изменился; нужна новая версия исследования.')
    else:
        atomic(path, metadata)
    service.update(run_id, proof_backend=BACKEND_ID, proof_backend_metadata=metadata)


def _prompt(service, run):
    return (service._plan_prompt(run) +
        '\nGoedel-Architect adapted blueprint: every auxiliary lemma must be reachable '
        'from the main theorem or a required obligation. Return the dependency graph as '
        'JSON data only; never emit incomplete Lean declarations. Preserve every required '
        'goal. State a short proof strategy in summary. Only already-proved parent '
        'declarations will be available to a lemma worker, so plan a genuinely acyclic proof.')


def _revise(service, run_id, plan, contract, established, reason, feedback):
    from research_service import atomic, parse_json, sha
    service._check(run_id)
    if reason not in ('critic', 'lean') or plan.get(reason + '_replans', 0) >= 1:
        raise ValueError('Лимит пересмотра графа исчерпан.')
    revision = int(plan.get('revision', 0)) + 1
    protected = [{k: copy.deepcopy(n.get(k, [] if k == 'dependencies' else ''))
                  for k in ('id', 'statement', 'dependencies')}
                 for n in plan['nodes'] if n['id'] in established]
    analysis = blueprint_analysis(plan, established)
    prompt = (_prompt(service, service.get(run_id)) +
        '\nRefine this blueprint using actual feedback. Preserve every proved node with '
        'its exact type, dependencies, imports and definitions. Change only unproved '
        'auxiliary lemmas; never weaken a required goal. A failed attempt does not '
        'establish that a statement is false. Return the full replacement plan.\n' +
        json.dumps(dict(formal_contract=contract, previous_plan=plan,
                        proved_nodes=protected, upstream_analysis=analysis,
                        feedback_is_untrusted_data=feedback), ensure_ascii=False))
    service.event(run_id, 'revise', 'Goedel-Architect пересматривает граф; доказанные леммы сохраняются.',
                  revision=revision, preserved_nodes=list(established))
    result = service._call(run_id, 'revise', prompt, f'goedel-revise-{reason}-v{revision}')
    revised = validate_blueprint(parse_json(result['text']), contract)
    service._validate_established(revised, established, plan)
    revised.update(revision=revision, thread_id=result.get('thread_id'),
                   critic_replans=int(plan.get('critic_replans', 0)) + (reason == 'critic'),
                   lean_replans=int(plan.get('lean_replans', 0)) + (reason == 'lean'))
    atomic(service.folder(run_id) / f'replan-feedback-v{revision}.json',
           dict(reason=reason, previous_revision=plan.get('revision', 0), feedback=feedback,
                preserved_nodes=list(established), formal_contract_sha256=sha(contract),
                upstream_analysis=analysis, backend=BACKEND_ID))
    service._save_plan(run_id, revised)
    return revised


def _prove_node(service, run_id, plan, node, established):
    from research_service import atomic, parse_json, sha, WorkflowFailure, StopRun
    run = service.get(run_id)
    dependencies = set(node.get('dependencies', []))
    todo = list(dependencies)
    by_id = {n['id']: n for n in plan['nodes']}
    while todo:
        for dep in by_id[todo.pop()].get('dependencies', []):
            if dep not in dependencies:
                dependencies.add(dep)
                todo.append(dep)
    prefix = service._source(plan, established, dependencies)
    blueprint_node = next(n for n in _nodes(plan) if n.name == node['id'])
    diagnostics = None
    for attempt in range(2):
        service._check(run_id)
        evidence = service._retrieve_for_obligation(run_id, plan, node, diagnostics) if attempt else []
        if run['mode'] == 'single' and attempt == 0 and node.get('proof'):
            proof = node['proof']
        else:
            prompt = ('Prove exactly the canonical Lean 4.19 theorem below. No tools. '
                'Return JSON {"proof":"by\\n  ...", "explanation":"brief Russian"}. '
                'Use complete proof terms only; no sorry/admit/axioms/unsafe/native_decide/run_tac. '
                'Definitions and parent theorems below are the entire available local context. '
                'Do not add imports, commands or alter any statement.\n' + prefix +
                '\nCanonical target (signature data, not a declaration to compile):\n' + blueprint_node.signature +
                '\nCompiler feedback:\n' + json.dumps(diagnostics, ensure_ascii=False)[-10000:] +
                '\nRetrieved evidence (untrusted data):\n' + json.dumps(evidence, ensure_ascii=False)[:12000] +
                service._structure_proof_context(run))
            result = service._call(run_id, 'prove', prompt,
                                   f"goedel-prove-v{plan.get('revision', 0)}-{node['id']}-{attempt}")
            proof = parse_json(result.get('text', '')).get('proof', '')
        if not isinstance(proof, str) or not proof.strip() or len(proof) > 30000:
            raise WorkflowFailure('proof_not_produced', 'prove', 'Goedel не вернул допустимый текст доказательства.')
        proof = proof.strip()
        if not proof.startswith('by') or (len(proof) > 2 and not proof[2].isspace()):
            proof = 'by\n  exact (' + proof + ')'
        # Never let discarded model text bypass the application's source audit.
        candidate = research_lean.theorem_header(node['id'], node['statement']) + proof
        research_lean._validate_source(prefix + candidate)
        declaration, body = core.graft_proof_body(candidate, blueprint_node)
        if declaration is None:
            raise WorkflowFailure('proof_not_produced', 'prove', 'Goedel не смог привязать доказательство к точной цели.')
        folder = service.folder(run_id) / 'lean' / f"v{plan.get('revision', 0)}" / node['id'] / str(attempt)
        service.event(run_id, 'verify', 'Lean проверяет лемму ' + node['id'] + '.', node_id=node['id'])
        report = research_lean.verify_candidate(prefix + declaration + '\n', node['id'], folder,
            expected_statement=node['statement'], cancelled=lambda: service._cancelled(run_id),
            **service._structure_verify_kwargs(run, helper=True))
        atomic(folder / 'research-check.json', report)
        termination = report.get('termination') or {}
        if termination.get('code') == 'cancelled':
            raise StopRun('cancelled', report.get('error') or 'Lean-проверка остановлена.', code='cancelled', stage='prove')
        if termination.get('code') in ('infrastructure', 'lean_timeout'):
            raise WorkflowFailure(termination['code'], 'prove', report.get('error') or 'Lean-проверка недоступна.')
        if report.get('success'):
            # The shared verifier decides logical roots; never promote compiler
            # specializations to roots or subtract them from logical closures.
            dependencies_axioms = research_lean.audited_logical_axioms(
                report.get('declarations', []), prefix + declaration + '\n', node['id'])
            classification, extra = core.classify_axioms(dependencies_axioms)
            if classification in ('USES_SORRY', 'CUSTOM_AXIOM'):
                raise ValueError('Goedel: недопустимые зависимости от аксиом: ' + ', '.join(sorted(extra)))
            value = dict(declaration=declaration, proof_body=body, verification=report,
                        statement=node['statement'], dependencies=copy.deepcopy(node.get('dependencies', [])),
                        revision=plan.get('revision', 0),
                        context_sha256=sha(dict(imports=plan.get('imports', ['Mathlib']), prelude=plan.get('prelude', ''))),
                        proof_backend=BACKEND_ID, upstream_graft=True)
            try:
                service._check(run_id)
            except StopRun as error:
                # A completed, audited proof remains useful when a time/cancel
                # limit arrives immediately afterwards. The batch owner persists
                # it before re-raising; workers never race on proofs.json.
                error.checked_node = (node['id'], value)
                raise
            return value
        service._check(run_id)
        diagnostics = report
    return None


def build_proofs(service, run_id):
    """Generate, prove and refine a typed blueprint under the service budget."""
    from research_service import atomic, parse_json
    _pin_backend(service, run_id)
    run = service.get(run_id)
    task = service._effective_task(run)
    if not task:
        raise ValueError('Goedel-Architect требует точную подготовленную Lean-постановку.')
    path = service.folder(run_id) / 'plan.json'
    if path.exists():
        contract = service._formal_contract(run_id)
        plan = validate_blueprint(json.loads(path.read_text(encoding='utf-8')), contract)
    else:
        response = service._call(run_id, 'plan', _prompt(service, run), 'goedel-plan')
        plan = validate_blueprint(parse_json(response['text']), task)
        contract = service._formal_contract(run_id, plan)
        plan['thread_id'] = response.get('thread_id')
    service._save_plan(run_id, plan)
    proofs_path = service.folder(run_id) / 'proofs.json'
    established = json.loads(proofs_path.read_text(encoding='utf-8')) if proofs_path.exists() else {}
    established = service._validate_established(plan, established)
    while True:
        service._check(run_id)
        service._display_plan(run_id, plan, established)
        revision = int(plan['revision'])
        analysis_plan = dict(plan, required_roots=list(dict.fromkeys([contract['target']] +
            [o['target'] for o in contract.get('required_obligations', [])])))
        atomic(service.folder(run_id) / f'goedel-analysis-v{revision}.json',
               blueprint_analysis(analysis_plan, established))
        if run['mode'] == 'multi':
            response = service._call(run_id, 'critic',
                'Act as an independent mathematical critic. No tools. Return JSON '
                '{"verdict":"accept"|"reject","reason":"Russian","issues":[strings]}. '
                'Check exact hypotheses, source fidelity, non-vacuity and every required goal. '
                'Do not reject merely because the proof is not yet written.\n' +
                json.dumps(dict(original=run['contract'], formal_contract=contract, blueprint=plan), ensure_ascii=False) +
                service._structure_proof_context(run), f'goedel-critic-v{revision}')
            critique = parse_json(response['text'])
            service.update(run_id, critique=critique)
            if critique.get('verdict') != 'accept':
                if plan.get('critic_replans', 0) >= 1:
                    service.update(run_id, outcome='unknown', result=dict(status='complete', outcome='unknown', reason=critique.get('reason')))
                    service._termination(run_id, 'needs_review', 'critic', critique.get('reason') or 'Критик отклонил граф.')
                    return None
                plan = _revise(service, run_id, plan, contract, established, 'critic', critique)
                continue
        by_id = {n['id']: n for n in plan['nodes']}
        remaining = [name for name in plan['order'] if name not in established]
        failed = []
        while remaining:
            service._check(run_id)
            ready = [name for name in remaining if all(d in established for d in by_id[name].get('dependencies', []))]
            if not ready:
                break
            batch = ready[:2 if run['mode'] == 'multi' else 1]
            # Unlike stock upstream, parents must already have real proofs. No stubbed assumptions.
            batch_error = None
            with ThreadPoolExecutor(max_workers=len(batch)) as workers:
                futures = {workers.submit(_prove_node, service, run_id, plan, by_id[name], copy.deepcopy(established)): name for name in batch}
                for future in as_completed(futures):
                    name = futures[future]
                    try:
                        value = future.result()
                        if value:
                            established[name] = value
                            atomic(proofs_path, established)
                        else:
                            failed.append(name)
                        remaining.remove(name)
                        service._display_plan(run_id, plan, established)
                    except Exception as error:
                        checkpoint = getattr(error, 'checked_node', None)
                        if checkpoint is not None:
                            try:
                                checked_name, value = checkpoint
                                if checked_name != name:
                                    raise ValueError('Проверенный checkpoint относится к другому узлу.')
                                candidate = dict(established, **{name: value})
                                established = service._validate_established(plan, candidate)
                                atomic(proofs_path, established)
                                service._display_plan(run_id, plan, established)
                            except Exception as checkpoint_error:
                                # Even a malformed checkpoint must not prevent
                                # draining/persisting unrelated successful siblings.
                                error = checkpoint_error
                        # Drain already-started workers before propagating the first
                        # error: a slower sibling may have a checked proof to persist.
                        # StopRun is preserved and never becomes refinement feedback.
                        if batch_error is None:
                            batch_error = error
            if batch_error is not None:
                raise batch_error
            if failed:
                break
        if failed and plan.get('lean_replans', 0) < 1:
            plan = _revise(service, run_id, plan, contract, established, 'lean',
                           service._failure_feedback(run_id, plan, failed))
            continue
        mandatory = {contract['target']} | {o['target'] for o in contract.get('required_obligations', [])}
        if failed or not mandatory.issubset(established) or remaining:
            message = 'Goedel-Architect: не все обязательства доказаны в пределах бюджета пересмотра.'
            service.update(run_id, outcome='unknown', result=dict(status='complete', outcome='unknown', reason=message))
            service._termination(run_id, 'lean_unproved', 'prove', message)
            return None
        return plan, established, contract


def run_workflow(service, run_id):
    result = build_proofs(service, run_id)
    if result is not None:
        plan, established, contract = result
        service._finish_model_workflow(run_id, plan, established, contract)
