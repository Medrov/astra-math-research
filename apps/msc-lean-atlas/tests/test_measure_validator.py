"""Type-boundary and terminal-evidence regressions; no model calls."""
import copy
import hashlib
import json
import os
from pathlib import Path
import sys
import tempfile
import threading
import time
import unittest
from unittest.mock import patch

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))
import research_lean as lean
import research_service as service


def plan(statement='True'):
    return dict(imports=['Init'], prelude='', summary='test', assumptions=[], relation_kind='test',
                target_id='finish', nodes=[dict(id='finish', statement=statement, dependencies=[], proof='')])


VALID_TYPES = [
    'let n : Nat := 1; n = n',
    'letI : Inhabited Nat := ⟨0⟩; True',
    '(id (α := Nat) 1) = 1',
    '({ fst := 1, snd := 2 } : Nat × Nat).1 = 1',
    'let n := (let m := 1; m); n = n -- theorem fake := by sorry',
    'True /- outer /- theorem fake : False := by sorry -/ comment -/',
    '"theorem := #" = "theorem := #"',
    "'(' = '('",
]


class TypeBoundaryTests(unittest.TestCase):
    def test_legitimate_types_keep_frozen_bytes_and_accept_local_assignment(self):
        for statement in VALID_TYPES:
            with self.subTest(statement=statement):
                result = service.validate_plan(plan(statement))
                self.assertEqual(result['nodes'][0]['statement'], statement)
                self.assertEqual(lean.type_expression(statement), '(\n' + statement + '\n)')

    def test_command_and_proof_boundary_injections_remain_rejected(self):
        invalid = ['True := by trivial', 'True) := by trivial\ntheorem evil : True := by trivial\n(',
                   'True\n  import Mathlib', 'True\ttheorem evil : True := by trivial',
                   'True\nnamespace Evil', 'True\nend', 'True\n#eval 1', 'True\nattribute [simp] f',
                   'True\ninstance : Inhabited Nat := ⟨0⟩', 'True\nset_option maxRecDepth 1000',
                   'True\naxiom evil : False', '(by sorry)', '(by admit)', '(by native_decide)',
                   '(by run_tac pure ())', 'unsafe True', 'True /- unfinished', '"unfinished',
                   '(True', 'True)', 'let n := 1; True := by trivial', 'True -/']
        # A stray comment terminator is invalid Lean syntax even when it cannot
        # escape the enclosing term; reject it at the lexical boundary too.
        for statement in invalid:
            with self.subTest(statement=statement):
                with self.assertRaises(ValueError):
                    lean._validate_type_contract(statement)
                with self.assertRaises(service.WorkflowFailure) as failure:
                    service.validate_plan(plan(statement))
                self.assertEqual(failure.exception.code, 'invalid_plan')

    def test_contract_graph_uses_the_same_type_validator(self):
        from research_object_examples import graph_for_case
        graph = graph_for_case('graph_energy')
        transition = graph['transitions'][0]
        transition['agent_task']['statement'] = VALID_TYPES[0]
        transition['obligations'][0]['statement'] = VALID_TYPES[0]
        result = service.ResearchService._validate_graph_contracts(graph)
        self.assertEqual(result['transitions'][0]['agent_task']['statement'], VALID_TYPES[0])
        transition['agent_task']['statement'] = 'True := by trivial'
        transition['obligations'][0]['statement'] = 'True := by trivial'
        with self.assertRaises(service.WorkflowFailure) as failure:
            service.ResearchService._validate_graph_contracts(graph)
        self.assertEqual(failure.exception.code, 'invalid_contract')

    def test_actual_failed_measure_plan_is_validated_without_changing_history(self):
        folder = ROOT / 'research_data/1021913905104fea9267d81d3e3dbff6'
        if not folder.exists():
            self.skipTest('Local historical attempt is not distributed with the repository')
        files = [folder / 'run.json', folder / 'attempts/plan/result.json']
        before = [p.read_bytes() for p in files]
        run, response = [json.loads(content) for content in before]
        original = service.parse_json(response['text'])
        transition = next(t for t in run['object_contract']['graph']['transitions'] if t['id'] == run['selected_transition_id'])
        task = {**transition['agent_task'], 'required_obligations': transition['obligations']}
        validated = service.validate_plan(copy.deepcopy(original), task)
        self.assertEqual(validated['target_id'], task['target'])
        self.assertTrue(any('let μ :=' in n['statement'] for n in original['nodes']))
        self.assertEqual([n['statement'] for n in validated['nodes']], [n['statement'] for n in original['nodes']])
        service.ResearchService._validate_graph_contracts(run['object_contract']['graph'])
        self.assertEqual(before, [p.read_bytes() for p in files])


class TerminationTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.service = service.ResearchService(self.temp.name, recover=False)
        self.run = self.service.create(dict(question='Controlled terminal metadata test', mode='single',
                                            budget=dict(max_calls=8, timeout_seconds=600)), start=False)
        self.rid = self.run['id']
        self.service._started[self.rid] = time.monotonic()
        self.service.cancel_flags[self.rid] = threading.Event()

    def tearDown(self):
        self.service.pool.shutdown(wait=True)
        self.temp.cleanup()

    def work_with(self, action):
        with patch.object(self.service, '_retrieve', side_effect=action), patch('research_codex.run_task') as model:
            self.service._work(self.rid)
            model.assert_not_called()
        return self.service.get(self.rid)

    def test_invalid_plan_ends_with_precise_stage_and_preserves_contract_review(self):
        prior = dict(status='aligned', reason='Before-proof review', limitations=['Not a proof'])
        self.service.update(self.rid, contract_review=prior)
        saved = self.work_with(lambda state: service.validate_plan(plan('True := by trivial')))
        self.assertEqual(saved['termination']['code'], 'invalid_plan')
        self.assertEqual(saved['termination']['stage'], 'plan')
        self.assertEqual(saved['final_semantic_review']['status'], 'not_performed')
        self.assertEqual(saved['result']['semantic_review']['status'], 'not_performed')
        self.assertEqual(saved['contract_review'], prior)
        self.assertEqual(saved['result']['termination'], saved['termination'])

    def test_empty_model_proof_is_not_invalid_json_or_a_lean_failure(self):
        for text in ['', '   ', '{}', '{"proof":""}', '{"proof":null}']:
            with self.subTest(text=text), patch.object(self.service, '_call', return_value={'text':text}), \
                    patch('research_lean.verify_candidate') as verifier:
                with self.assertRaises(service.WorkflowFailure) as failure:
                    self.service._prove_node(self.rid, {**plan(), 'order':['finish']}, plan()['nodes'][0], {})
                self.assertEqual(failure.exception.code, 'proof_not_produced')
                self.assertEqual(failure.exception.stage, 'prove')
                self.assertIn('Доказательство не построено', str(failure.exception))
                verifier.assert_not_called()

    def test_malformed_nonempty_response_is_distinct_from_empty_proof(self):
        with self.assertRaises(service.WorkflowFailure) as failure:
            service.parse_json('not json')
        self.assertEqual(failure.exception.code, 'model_response_invalid')

    def test_valid_final_lean_and_real_semantic_review_are_never_erased(self):
        verification = dict(success=True, target_preserved=True, obligations_passed=True, axioms=[])
        semantic = dict(status='aligned', reason='Actual final review')
        self.service.update(self.rid, formal_outcome='proved', semantic_review=semantic,
                            final_semantic_review=semantic,
                            result=dict(status='complete', outcome='proved', formal_outcome='proved',
                                        verification=verification, semantic_review=semantic))
        self.service._termination(self.rid, 'infrastructure', 'publish', 'Write failed', status='failed')
        saved = self.service.get(self.rid)
        self.assertEqual(saved['result']['verification'], verification)
        self.assertEqual(saved['final_semantic_review'], semantic)
        self.assertEqual(saved['semantic_review'], semantic)
        self.assertEqual(saved['formal_outcome'], 'proved')

    def test_verified_formal_result_survives_review_budget_stop(self):
        verification = dict(success=True, target_preserved=True)
        self.service.update(self.rid, formal_outcome='proved', result=dict(verification=verification, outcome='unknown',
                            formal_outcome='proved', semantic_review=dict(status='pending')))
        self.service._termination(self.rid, 'budget_exhausted', 'semantic_review', 'Budget used', status='budget_exhausted')
        saved = self.service.get(self.rid)
        self.assertEqual(saved['result']['verification'], verification)
        self.assertEqual(saved['final_semantic_review']['status'], 'not_performed')
        self.assertEqual(saved['formal_outcome'], 'proved')

    def test_infrastructure_error_and_nonproof_review_status(self):
        def failing(_): raise OSError('Compiler missing')
        self.service.update(self.rid, purpose='discover')
        saved = self.work_with(failing)
        self.assertEqual(saved['termination']['code'], 'infrastructure')
        self.assertEqual(saved['termination']['stage'], 'retrieve')
        self.assertEqual(saved['final_semantic_review']['status'], 'not_applicable')

    def test_legacy_history_exposes_diagnostics_read_only(self):
        run = dict(self.run, error='Тип леммы не должен содержать команды Lean.', requires_review=False,
                   contract_review=dict(status='aligned', reason='Before proof'))
        original = copy.deepcopy(run)
        summary = service.history_summary(run)
        self.assertEqual(summary['error'], run['error'])
        self.assertEqual(summary['contract_review']['status'], 'aligned')
        self.assertEqual(run, original)
        self.assertIsNone(summary['termination'])


@unittest.skipUnless(Path(lean.lean_service.default_context()['lean']).is_file(), 'Prepared Lean unavailable')
class RealTypeBoundaryTests(unittest.TestCase):
    def test_real_lean_accepts_terms_and_checks_exact_types_and_axioms(self):
        with tempfile.TemporaryDirectory(prefix='measure-type-boundary-') as folder:
            source = 'import Init\n' + '\n'.join(lean.theorem_header('Boundary.t' + str(i), statement) + 'by rfl' if i not in (1, 5)
                          else lean.theorem_header('Boundary.t' + str(i), statement) + 'by trivial'
                          for i, statement in enumerate(VALID_TYPES))
            obligations = [dict(id='t'+str(i), target='Boundary.t'+str(i), statement=statement, expected_outcome='proved')
                           for i, statement in enumerate(VALID_TYPES)]
            captured = {}
            prepare = lean.lean_service._prepare
            def capture(*args, **kwargs):
                context, env = prepare(*args, **kwargs)
                captured.update(context=context, env=env)
                return context, env
            with patch.object(lean.lean_service, '_prepare', side_effect=capture):
                report = lean.verify_candidate(source, 'Boundary.t0', folder, VALID_TYPES[0], required_obligations=obligations)
            self.assertTrue(report['success'], json.dumps(report, ensure_ascii=False))
            self.assertTrue(report['obligations_passed'])
            self.assertEqual(report['audit']['status'], 'passed')
            work = Path(report['workspace'])
            (work/'PrintAxioms.lean').write_text('import Candidate\n' + '\n'.join('#print axioms Boundary.t'+str(i) for i in range(len(VALID_TYPES))), encoding='utf8')
            diagnostics = []
            lean._run(captured['context'], captured['env'], work, 'PrintAxioms.lean', diagnostics, output=False)
            self.assertEqual(diagnostics[0]['exit_code'], 0)
            self.assertNotIn('sorryAx', diagnostics[0]['stdout'])
            bad = lean.verify_candidate(source, 'Boundary.t0', folder, 'let n : Nat := 1; n = 2')
            self.assertFalse(bad['success'])
            self.assertFalse(bad['target_preserved'])
            self.assertEqual(bad['termination']['code'], 'invalid_contract')
            self.assertEqual(bad['termination']['stage'], 'lean_contract')
            # Keep this test's actual command/audit evidence separate from user runs.
            retained = ROOT/'verification/measure-validator-smoke.json'
            service.atomic(retained, dict(kind='validator_smoke_not_measure_proof', source_sha256=hashlib.sha256(source.encode()).hexdigest(),
                                          success=report['success'], obligations=report['obligations'], audit=report['audit'],
                                          diagnostics=report['diagnostics'], print_axioms=diagnostics,
                                          changed_type_rejected=not bad['success'], changed_type_diagnostics=bad['diagnostics']))


if __name__ == '__main__':
    unittest.main()
