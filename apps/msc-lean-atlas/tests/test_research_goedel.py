"""Adapted upstream core + durable real controller; model/Lean doubles are explicit."""
import copy
import json
import os
from pathlib import Path
import sys
import tempfile
import threading
import time
import unittest
from unittest.mock import patch, Mock

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
import research_goedel as goedel
import research_service as service_module
from tools.goedel import evaluate_backends


def node(name, dependencies=()):
    return dict(id=name, title=name, statement='True', dependencies=list(dependencies), proof='')


def plan(nodes):
    return dict(imports=['Mathlib'], prelude='', summary='Dependency proof plan', assumptions=[],
                relation_kind='test', target_id='finish', nodes=nodes)


def task():
    return dict(imports=['Mathlib'], prelude='', target='finish', statement='True')


class GoedelCoreTests(unittest.TestCase):
    def test_manifest_matches_actual_vendored_files(self):
        metadata = goedel.backend_metadata()
        self.assertEqual(metadata['status'], 'ready')
        self.assertEqual(metadata['upstream_commit'], goedel.UPSTREAM_COMMIT)
        self.assertIn('graft_proof_body', metadata['upstream_functions'])
        self.assertEqual(metadata['integration'], 'adapted_graph_core_not_stock_cli')

    def test_upstream_gate_rejects_unreachable_optional_node(self):
        with self.assertRaisesRegex(ValueError, 'not reachable'):
            goedel.validate_blueprint(plan([node('unused'), node('finish')]), task())

    def test_independent_required_obligation_is_not_pruned(self):
        fixed = dict(task(), required_obligations=[dict(id='side', target='side', statement='True', expected_outcome='proved')])
        value = goedel.validate_blueprint(plan([node('side'), node('finish')]), fixed)
        self.assertEqual(set(value['order']), {'side', 'finish'})
        with self.assertRaises(ValueError):
            goedel.validate_blueprint(plan([node('finish')]), fixed)

    def test_goal_and_context_cannot_change(self):
        for change in ('statement', 'imports', 'prelude'):
            with self.subTest(change=change):
                candidate = plan([node('finish')])
                if change == 'statement':
                    candidate['nodes'][0]['statement'] = 'False'
                else:
                    candidate[change] = ['Init'] if change == 'imports' else 'def extra : Nat := 0'
                with self.assertRaises(ValueError):
                    goedel.validate_blueprint(candidate, task())

    def test_policy_never_accepts_native_decide_environment_override(self):
        with patch.dict(os.environ, {'ALLOW_NATIVE_DECIDE': '1'}):
            classification, extra = goedel.core.classify_axioms({'Lean.ofReduceBool'})
        self.assertEqual(classification, 'CUSTOM_AXIOM')
        self.assertEqual(extra, {'Lean.ofReduceBool'})

    def test_upstream_grafting_uses_canonical_signature(self):
        original = goedel._nodes(plan([node('finish')]))[0]
        declaration, body = goedel.core.graft_proof_body('theorem finish : False := by\n  exact True.intro', original)
        self.assertTrue(declaration.startswith(original.signature + ' := by'))
        self.assertNotIn('False', declaration)
        self.assertIn('exact True.intro', body)

    def test_upstream_reachability_sees_proven_dependencies(self):
        value = plan([node('parent'), node('finish', ['parent'])])
        established = {'parent': dict(declaration='theorem parent : True := by trivial'),
                       'finish': dict(declaration='theorem finish : True := by exact parent')}
        analysis = goedel.blueprint_analysis(value, established)
        self.assertEqual(analysis['reachable'], ['finish', 'parent'])
        self.assertEqual(analysis['frozen'], ['finish', 'parent'])
        self.assertEqual(analysis['unsolved'], [])


class GoedelWorkflowTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.service = service_module.ResearchService(root=self.temp.name)
        self.fixed = task()
        self.initial = plan([node('kept'), node('hard', ['kept']), node('finish', ['hard'])])
        self.revised = plan([node('kept'), node('bridge', ['kept']), node('finish', ['bridge'])])
        self.calls = []
        self.lean_calls = []
        self.fail_names = {'hard'}
        self.reject_first = False
        self.proof = 'by\n  exact True.intro'
        self.patches = [patch.object(self.service, '_effective_task', side_effect=lambda run: copy.deepcopy(self.fixed)),
                        patch('research_codex.run_task', side_effect=self.model),
                        patch('research_lean.verify_candidate', side_effect=self.lean),
                        patch.object(self.service, '_retrieve_for_obligation', return_value=[])]
        for p in self.patches:
            p.start()

    def tearDown(self):
        for p in reversed(self.patches):
            p.stop()
        self.service.pool.shutdown(wait=True)
        self.temp.cleanup()

    def create(self, max_calls=24, mode='multi'):
        run = self.service.create(dict(mode=mode, question='Test exact frozen contract.',
            proof_backend=goedel.BACKEND_ID, budget=dict(max_calls=max_calls, timeout_seconds=600)), start=False)
        rid = run['id']
        self.service._started[rid] = time.monotonic()
        self.service.cancel_flags[rid] = threading.Event()
        return rid

    def model(self, prompt, work_dir, **kwargs):
        key = Path(work_dir).name
        self.calls.append(key)
        if key == 'goedel-plan':
            value = copy.deepcopy(self.initial)
        elif key.startswith('goedel-critic'):
            value = dict(verdict='reject' if self.reject_first and key.endswith('v0') else 'accept', reason='Controlled review', issues=[])
        elif key.startswith('goedel-revise-critic'):
            value = copy.deepcopy(self.initial)
        elif key.startswith('goedel-revise-lean'):
            value = copy.deepcopy(self.revised)
        elif key.startswith('goedel-prove'):
            value = dict(proof=self.proof, explanation='Controlled proof')
        else:
            raise AssertionError(key)
        return dict(status='completed', text=json.dumps(value), thread_id='thread-' + key,
                    turn_id='turn-' + key, usage={'last': {'totalTokens': 100}}, error=None, model='gpt-6-astra')

    def lean(self, source, target, work_dir, **kwargs):
        self.lean_calls.append((target, source, kwargs))
        success = target not in self.fail_names
        return dict(success=success, status='complete' if success else 'failed',
                    target_preserved=success, declarations=[dict(name=target, kind='theorem', unsafe=False, axioms=[])],
                    diagnostics=[{'stdout': '' if success else 'unknown helper constant'}],
                    error=None if success else 'Controlled compiler error')

    def test_failed_node_refines_graph_and_keeps_proved_parents(self):
        rid = self.create()
        result = goedel.build_proofs(self.service, rid)
        self.assertIsNotNone(result)
        final_plan, established, contract = result
        self.assertEqual(final_plan['revision'], 1)
        self.assertEqual(set(established), {'kept', 'bridge', 'finish'})
        self.assertEqual(established['kept']['revision'], 0)
        self.assertEqual(established['bridge']['revision'], 1)
        self.assertTrue(all(p['upstream_graft'] for p in established.values()))
        self.assertEqual(self.calls.count('goedel-prove-v0-kept-0'), 1)
        self.assertNotIn('goedel-prove-v1-kept-0', self.calls)
        self.assertEqual(contract['statement'], 'True')
        self.assertEqual(self.service.get(rid)['usage']['calls'], len(self.calls))
        self.assertEqual(self.service.get(rid)['usage']['total_tokens'], len(self.calls) * 100)
        feedback = json.loads((self.service.folder(rid) / 'replan-feedback-v1.json').read_text())
        self.assertIn('unknown helper constant', json.dumps(feedback))

    def test_resume_reuses_saved_attempts_without_new_generation(self):
        rid = self.create()
        first = goedel.build_proofs(self.service, rid)
        count = len(self.calls)
        again = goedel.build_proofs(self.service, rid)
        self.assertEqual(len(self.calls), count)
        self.assertEqual(first[0], again[0])
        self.assertEqual(self.service.get(rid)['usage']['total_tokens'], count * 100)

    def test_parallel_error_drains_slow_success_and_resume_reuses_it(self):
        self.initial = plan([node('fast'), node('slow'), node('finish', ['fast', 'slow'])])
        self.fail_names.clear()
        errors = [RuntimeError('fast worker infrastructure failure'),
                  service_module.StopRun('budget_exhausted', 'controlled budget stop'),
                  service_module.StopRun('cancelled', 'controlled cancellation')]
        real_completed = goedel.as_completed
        for error in errors:
            with self.subTest(error=type(error).__name__, reason=str(error)):
                self.calls.clear()
                self.lean_calls.clear()
                rid = self.create()
                slow_started, release_slow = threading.Event(), threading.Event()

                def checked(source, target, work_dir, **kwargs):
                    if target == 'fast':
                        self.assertTrue(slow_started.wait(5), 'The sibling did not start')
                        raise error
                    if target == 'slow':
                        slow_started.set()
                        release_slow.wait(5)
                    return self.lean(source, target, work_dir, **kwargs)

                def deterministic_completion(futures):
                    fast = next(future for future, name in futures.items() if name == 'fast')
                    fast.exception(timeout=5)
                    try:
                        yield fast
                    finally:
                        # The successful worker completes only after the failing
                        # result has been consumed; no scheduling sleeps required.
                        release_slow.set()
                    yield from real_completed(future for future in futures if future is not fast)

                with patch('research_lean.verify_candidate', side_effect=checked), \
                        patch.object(goedel, 'as_completed', side_effect=deterministic_completion):
                    with self.assertRaises(type(error)) as caught:
                        goedel.build_proofs(self.service, rid)
                self.assertIs(caught.exception, error)
                saved = json.loads((self.service.folder(rid) / 'proofs.json').read_text())
                self.assertEqual(set(saved), {'slow'})
                self.assertEqual(saved['slow']['dependencies'], [])
                self.assertTrue(saved['slow']['verification']['success'])
                self.assertFalse(any(key.startswith('goedel-revise') for key in self.calls))

                # Resume uses the persisted checked declaration and cached model
                # attempts. In particular it never asks to prove the sibling again.
                result = goedel.build_proofs(self.service, rid)
                self.assertEqual(set(result[1]), {'fast', 'slow', 'finish'})
                self.assertEqual(self.calls.count('goedel-prove-v0-slow-0'), 1)
                self.assertEqual(sum(target == 'slow' for target, _, _ in self.lean_calls), 1)
                self.assertEqual(result[1]['slow'], saved['slow'])

    def test_second_failure_stops_unknown(self):
        self.fail_names.add('bridge')
        rid = self.create()
        self.assertIsNone(goedel.build_proofs(self.service, rid))
        run = self.service.get(rid)
        self.assertEqual(run['outcome'], 'unknown')
        self.assertEqual(run['termination']['code'], 'lean_unproved')
        self.assertEqual(sum(k.startswith('goedel-revise-lean') for k in self.calls), 1)

    def test_cancel_after_successful_audit_persists_node_and_resume_reuses_it(self):
        self.initial = plan([node('kept'), node('finish', ['kept'])])
        self.fail_names.clear()
        rid = self.create(mode='single')

        def checked(source, target, work_dir, **kwargs):
            report = self.lean(source, target, work_dir, **kwargs)
            if target == 'kept':
                self.service.cancel_flags[rid].set()
            return report

        with patch('research_lean.verify_candidate', side_effect=checked):
            with self.assertRaises(service_module.StopRun) as caught:
                goedel.build_proofs(self.service, rid)
        self.assertEqual(caught.exception.status, 'cancelled')
        saved = json.loads((self.service.folder(rid) / 'proofs.json').read_text())
        self.assertEqual(set(saved), {'kept'})
        self.assertTrue(saved['kept']['verification']['success'])
        self.assertNotIn('goedel-prove-v0-finish-0', self.calls)
        self.service.cancel_flags[rid].clear()
        result = goedel.build_proofs(self.service, rid)
        self.assertEqual(result[1]['kept'], saved['kept'])
        self.assertEqual(self.calls.count('goedel-prove-v0-kept-0'), 1)
        self.assertEqual(sum(target == 'kept' for target, _, _ in self.lean_calls), 1)

    def test_success_without_target_or_with_actual_custom_axiom_is_never_checkpointed(self):
        self.initial = plan([node('finish')])
        for declarations in ([], [dict(name='finish', kind='theorem', unsafe=False, axioms=['bad'])]):
            with self.subTest(declarations=declarations):
                rid = self.create(mode='single')
                with patch('research_lean.verify_candidate', return_value=dict(success=True, declarations=declarations)):
                    with self.assertRaises(ValueError):
                        goedel.build_proofs(self.service, rid)
                self.assertFalse((self.service.folder(rid) / 'proofs.json').exists())

    def test_success_with_unreferenced_compiler_specialization_reaches_checkpoint(self):
        self.initial = plan([node('finish')])
        rid = self.create(mode='single')

        def checked(source, target, work_dir, **kwargs):
            report = self.lean(source, target, work_dir, **kwargs)
            name = 'Finset.sum._at.localDef._spec_1'
            report['declarations'].append(dict(name=name, kind='axiom', unsafe=True, axioms=[name]))
            return report

        with patch('research_lean.verify_candidate', side_effect=checked):
            result = goedel.build_proofs(self.service, rid)
        self.assertEqual(set(result[1]), {'finish'})
        saved = json.loads((self.service.folder(rid) / 'proofs.json').read_text())
        self.assertTrue(saved['finish']['verification']['success'])

    def test_total_call_budget_includes_plan_critic_proofs_and_refinement(self):
        rid = self.create(max_calls=5)
        with self.assertRaises(service_module.StopRun) as caught:
            goedel.build_proofs(self.service, rid)
        self.assertEqual(caught.exception.status, 'budget_exhausted')
        self.assertEqual(len(self.calls), 5)
        self.assertEqual(self.service.get(rid)['usage']['calls'], 5)

    def test_cancel_stops_before_new_generation(self):
        rid = self.create()
        self.service.cancel_flags[rid].set()
        with self.assertRaises(service_module.StopRun) as caught:
            goedel.build_proofs(self.service, rid)
        self.assertEqual(caught.exception.status, 'cancelled')
        self.assertEqual(self.calls, [])

    def test_proved_type_cannot_be_changed_by_refinement(self):
        self.revised['nodes'][0]['statement'] = 'False'
        rid = self.create()
        with self.assertRaises(ValueError):
            goedel.build_proofs(self.service, rid)
        self.assertFalse((self.service.folder(rid) / 'plan-v1.json').exists())

    def test_unfinished_proof_rejected_before_lean(self):
        self.proof = 'by\n  sorry'
        rid = self.create()
        with self.assertRaises(ValueError):
            goedel.build_proofs(self.service, rid)
        self.assertEqual(self.lean_calls, [])

    def test_infrastructure_failure_is_not_sent_back_to_model_as_math_feedback(self):
        rid = self.create()
        failure = dict(success=False, status='failed', error='Lean unavailable',
                       termination=dict(code='infrastructure'), diagnostics=[])
        with patch('research_lean.verify_candidate', return_value=failure):
            with self.assertRaises(service_module.WorkflowFailure) as caught:
                goedel.build_proofs(self.service, rid)
        self.assertEqual(caught.exception.code, 'infrastructure')
        self.assertEqual(sum(k.startswith('goedel-prove') for k in self.calls), 1)
        self.assertFalse(any(k.startswith('goedel-revise') for k in self.calls))

    def test_backend_change_invalidates_resume(self):
        rid = self.create()
        goedel.build_proofs(self.service, rid)
        path = self.service.folder(rid) / 'proof-backend.json'
        value = json.loads(path.read_text())
        value['upstream_commit'] = 'other'
        path.write_text(json.dumps(value))
        with self.assertRaisesRegex(ValueError, 'Движок'):
            goedel.build_proofs(self.service, rid)

    def test_complete_graph_delegates_independent_final_acceptance(self):
        rid = self.create()
        final = Mock()
        with patch.object(self.service, '_finish_model_workflow', final, create=True):
            goedel.run_workflow(self.service, rid)
        final.assert_called_once()
        self.assertEqual(final.call_args.args[0], rid)
        self.assertEqual(final.call_args.args[3]['statement'], 'True')


class BackendComparisonTests(unittest.TestCase):
    def entry(self, backend):
        return dict(case_id='graph_energy', backend=backend, formal_input_sha256='same-goal',
                    budget=dict(max_calls=8, timeout_seconds=600), mode='multi',
                    environment_fingerprint='same-pinned-environment', fully_accepted=True,
                    all_required_goals_lean_checked=True, usage=dict(calls=5, total_tokens=1000, elapsed_seconds=30))

    def test_comparison_checks_caps_and_environment_and_counts_all_cost(self):
        report = dict(selected_cases=['graph_energy'], runs=[self.entry('native'), self.entry(goedel.BACKEND_ID)])
        summary = evaluate_backends.summarize(report)
        self.assertTrue(summary['pairs'][0]['comparable'])
        self.assertEqual(summary['totals'][goedel.BACKEND_ID]['actual_tokens'], 1000)
        report['runs'][1]['budget']['max_calls'] = 16
        self.assertFalse(evaluate_backends.summarize(report)['pairs'][0]['comparable'])
        report['runs'][1]['budget']['max_calls'] = 8
        report['runs'][1]['environment_fingerprint'] = None
        self.assertFalse(evaluate_backends.summarize(report)['pairs'][0]['comparable'])

    def test_lean_success_without_semantic_review_is_not_full_acceptance(self):
        run = dict(id='x', case_id='graph_energy', mode='multi', status='complete', phase='result',
                   outcome='unknown', budget={}, usage={}, contract=dict(agent_task=task(), question='q'),
                   result=dict(verification=dict(success=True, target_preserved=True, obligations_passed=True)),
                   final_semantic_review=dict(status='not_performed'))
        measured = evaluate_backends.measured_run(run)
        self.assertTrue(measured['all_required_goals_lean_checked'])
        self.assertFalse(measured['fully_accepted'])

    def test_backend_identity_does_not_mask_formal_input_change(self):
        first = dict(contract=dict(agent_task=task(), proof_backend='native', question='q'))
        other = copy.deepcopy(first)
        other['contract']['proof_backend'] = goedel.BACKEND_ID
        self.assertEqual(evaluate_backends.formal_input(first), evaluate_backends.formal_input(other))
        other['contract']['agent_task']['statement'] = 'False'
        self.assertNotEqual(evaluate_backends.formal_input(first), evaluate_backends.formal_input(other))


if __name__ == '__main__':
    unittest.main()
