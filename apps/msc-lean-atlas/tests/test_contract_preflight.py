"""Frozen proposition elaboration is neither a proof nor a mathematical verdict."""
import copy
import json
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


def task():
    return dict(imports=['Init'], prelude='def frozenNumber : Nat := 2', target='goal',
                statement='let n := frozenNumber; n = 2', required_obligations=[
                    dict(id='unproved', target='unproved', statement='False', expected_outcome='proved')])


class PreflightControllerTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.service = service.ResearchService(self.temp.name, recover=False)
        self.run = self.service.create(dict(mode='single', case_id='graph_energy',
                                            budget=dict(max_calls=8, timeout_seconds=600)), start=False)
        self.rid = self.run['id']
        self.service._started[self.rid] = time.monotonic()
        self.service.cancel_flags[self.rid] = threading.Event()

    def tearDown(self):
        self.service.pool.shutdown(wait=True)
        self.temp.cleanup()

    @staticmethod
    def mocked_preflight(value, folder, **kwargs):
        work = Path(folder) / 'contract-mocked'; work.mkdir(parents=True, exist_ok=True)
        harness = work/'ContractTypes.lean'; harness.write_text(json.dumps(value), encoding='utf8')
        return dict(kind='lean_contract_preflight', status='complete', well_typed=True, proof_checked=False,
                    outcome='unknown', target=value['target'], workspace=str(work),
                    source_sha256=lean._sha(harness.read_bytes()), contract_sha256=service.sha(value),
                    audit=dict(status='passed'), diagnostics=[], declarations=[])

    def test_cache_reuses_only_exact_task_environment_and_unchanged_harness(self):
        value = task()
        with patch('research_lean.verify_contract', side_effect=self.mocked_preflight) as check:
            first = self.service._preflight_contract(self.rid, value)
            self.service._preflight_contract(self.rid, value)
            self.assertEqual(check.call_count, 1)
            (Path(first['workspace'])/'ContractTypes.lean').write_text('changed', encoding='utf8')
            self.service._preflight_contract(self.rid, value)
            self.assertEqual(check.call_count, 2)
            changed = {**value, 'statement':'False'}
            self.service._preflight_contract(self.rid, changed)
            self.assertEqual(check.call_count, 3)
            self.service.environment_fingerprint = 'different-environment'
            self.service._preflight_contract(self.rid, changed)
            self.assertEqual(check.call_count, 4)
        saved = self.service.get(self.rid)
        self.assertEqual(saved['contract_verification']['outcome'], 'unknown')
        self.assertNotEqual(saved.get('outcome'), 'proved')
        self.assertNotIn('verification', saved.get('result') or {})

    def test_failed_elaboration_stops_before_contract_review_or_prover(self):
        failed = dict(kind='lean_contract_preflight', status='rejected', well_typed=False,
                      proof_checked=False, outcome='unknown', error='Unknown identifier in frozen type',
                      diagnostics=[dict(file='ContractTypes.lean', exit_code=1, stdout='unknown identifier')],
                      termination=dict(code='invalid_contract', stage='lean_contract_preflight', message='Unknown identifier'))
        with patch('research_lean.verify_contract', return_value=failed), patch.object(self.service, '_call') as model:
            with self.assertRaises(service.WorkflowFailure) as failure:
                self.service._validate_transition({'run_id':self.rid})
            model.assert_not_called()
        self.assertEqual(failure.exception.code, 'invalid_contract')
        self.assertEqual(failure.exception.stage, 'lean_contract_preflight')
        self.service._termination(self.rid, failure.exception.code, failure.exception.stage, str(failure.exception), status='failed')
        saved = self.service.get(self.rid)
        self.assertFalse(saved['contract_verification']['well_typed'])
        self.assertEqual(saved['final_semantic_review']['status'], 'not_performed')
        self.assertEqual(saved['usage']['calls'], 0)
        self.assertNotEqual(saved.get('outcome'), 'proved')

    def test_preflight_pass_does_not_start_or_replace_proof_on_its_own(self):
        before = copy.deepcopy(self.service.get(self.rid)['object_contract'])
        with patch('research_lean.verify_contract', side_effect=self.mocked_preflight), patch.object(self.service, '_call') as model:
            self.service._validate_transition({'run_id':self.rid})
            model.assert_not_called()  # exact prepared fixture has an existing contract review
        saved = self.service.get(self.rid)
        self.assertTrue(saved['contract_verification']['well_typed'])
        self.assertEqual(saved['object_contract'], before)
        self.assertEqual(saved['usage']['calls'], 0)
        self.assertNotEqual(saved.get('outcome'), 'proved')
        self.assertNotIn('verification', saved.get('result') or {})

    def test_resume_before_investigation_rechecks_cached_contract(self):
        with patch.object(self.service, '_preflight_contract') as preflight, patch.object(self.service, '_model_workflow') as prove:
            self.service._investigate({'run_id':self.rid})
        preflight.assert_called_once_with(self.rid, self.service._effective_task(self.service.get(self.rid)))
        prove.assert_called_once_with(self.rid)


@unittest.skipUnless(Path(lean.lean_service.default_context()['lean']).is_file(), 'Prepared Lean unavailable')
class RealContractPreflightTests(unittest.TestCase):
    def test_real_proposition_elaboration_and_failures_without_any_proof(self):
        reports = []
        with tempfile.TemporaryDirectory(prefix='contract-preflight-test-') as folder:
            fixed = task(); before = copy.deepcopy(fixed)
            valid = lean.verify_contract(fixed, folder); reports.append(valid)
            self.assertTrue(valid['well_typed'], json.dumps(valid, ensure_ascii=False))
            self.assertFalse(valid['proof_checked'])
            self.assertNotIn('success', valid)
            self.assertNotIn('target_preserved', valid)
            self.assertEqual(valid['outcome'], 'unknown')
            self.assertEqual(valid['audit']['status'], 'passed')
            self.assertEqual(len(valid['checked_obligations']), 2)
            self.assertTrue(all(d['kind'] == 'def' for d in valid['declarations']))
            self.assertEqual(fixed, before)
            source = (Path(valid['workspace'])/'ContractTypes.lean').read_text(encoding='utf8')
            self.assertIn(fixed['prelude'], source)
            self.assertIn(lean.type_expression(fixed['statement']), source)
            self.assertIn(': Prop := (\nFalse\n)', source)
            self.assertNotIn('theorem ', source)
            for change in [dict(prelude='def frozenNumber : Nat := "not a Nat"'),
                           dict(statement='unknownFrozenConstant = 2'), dict(statement='Nat'),
                           dict(required_obligations=[dict(id='bad', target='bad', statement='UnknownProp', expected_outcome='proved')])]:
                with self.subTest(change=change):
                    invalid = lean.verify_contract({**fixed, **change}, folder); reports.append(invalid)
                    self.assertFalse(invalid['well_typed'])
                    self.assertFalse(invalid['proof_checked'])
                    self.assertEqual(invalid['outcome'], 'unknown')
                    self.assertEqual(invalid['termination']['code'], 'invalid_contract')
                    self.assertEqual(invalid['termination']['stage'], 'lean_contract_preflight')
                    self.assertTrue(any(d['file']=='ContractTypes.lean' and d['exit_code']!=0 for d in invalid['diagnostics']))
            service.atomic(ROOT/'verification/contract-preflight-smoke.json',
                           dict(kind='preflight_smoke_not_measure_proof', reports=reports))


if __name__ == '__main__':
    unittest.main()
