"""Repairs may fix compiler names, but cannot silently change a theorem."""
import copy
import json
from pathlib import Path
import sys
import tempfile
import time
import unittest
from unittest.mock import patch

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))
import research_drafts as drafts
import research_service as service
import research_lean as lean
from research_objects import validate_graph
from test_draft_imports import module_fixture, missing_report, draft as import_draft, WRONG, RIGHT


def formalization():
    statement = '∀ (f : Nat → Nat) (n : Nat), Function.iterate f n 0 = Function.iterate f n 0'
    return dict(status='ready', reason='test', limitations=[], agent_task=dict(
        imports=['Mathlib.Logic.Function.Iterate'], prelude='', target='iteration_identity', statement=statement),
        obligations=[dict(id='identity', title='Iteration identity', target='iteration_identity', statement=statement,
                          expected_outcome='proved')])


def failure(code='invalid_contract'):
    return dict(well_typed=False, status='rejected', proof_checked=False, error='Lean failed',
                diagnostics=[dict(stdout="ContractTypes.lean:1:1: error: unknown identifier 'Function.iterate'", stderr='')],
                termination=dict(code=code))


REPAIR = dict(reason='Correct pinned library namespace', imports_additions=[],
              replacements=[dict(old='Function.iterate', new='Nat.iterate')])


class RepairBoundaryTests(unittest.TestCase):
    def test_patch_preserves_all_obligation_names_and_directions(self):
        before = formalization()
        changed = drafts.apply_repair(before, REPAIR, failure())
        self.assertEqual(before, formalization())
        self.assertEqual(changed['obligations'][0]['target'], before['obligations'][0]['target'])
        self.assertEqual(changed['obligations'][0]['expected_outcome'], 'proved')
        self.assertEqual(changed['agent_task']['statement'], before['agent_task']['statement'].replace('Function.iterate', 'Nat.iterate'))
        self.assertEqual(changed['obligations'][0]['statement'], changed['agent_task']['statement'])

    def test_cannot_rewrite_predicate_or_inject_proof(self):
        for item in [dict(old='Nat', new='Int'), dict(old='Function.iterate', new='fun x => True'),
                     dict(old='Function.iterate', new='Nat.iterate; axiom bad : False')]:
            with self.subTest(item=item), self.assertRaises(ValueError):
                drafts.apply_repair(formalization(), dict(REPAIR, replacements=[item]), failure())
        with self.assertRaises(ValueError):
            drafts.apply_repair(formalization(), dict(REPAIR, statement='True'), failure())


class DraftLifecycleTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.svc = service.ResearchService(self.temp.name, recover=False)
        self.run = self.svc.create(dict(mode='single', case_id='graph_energy'), start=False)
        self.rid = self.run['id']
        self.svc._started[self.rid] = time.monotonic()
        self.graph = validate_graph(self.run['object_graph'])
        self.tid = self.graph['transitions'][0]['id']
        self.graph['transitions'][0].update(formulation_status='literature_only', agent_task=None,
                                           obligations=[], case_id=None)

    def tearDown(self):
        self.svc.pool.shutdown(wait=True)
        self.temp.cleanup()

    def test_compiler_failure_repairs_before_any_graph_is_frozen(self):
        prior = copy.deepcopy(self.svc.get(self.rid)['object_contract'])
        with patch.object(self.svc, '_preflight_contract', side_effect=[failure(), dict(well_typed=True)]), \
             patch.object(self.svc, '_call', return_value={'text':json.dumps(REPAIR)}) as calls, \
             patch('research_retrieval.search_library', return_value=[]):
            graph, fixed = self.svc._prepare_draft_contract(self.rid, self.graph, self.tid, formalization())
        self.assertEqual(calls.call_count, 1)
        self.assertEqual(self.svc.get(self.rid)['object_contract'], prior)
        self.assertIn('Nat.iterate', fixed['agent_task']['statement'])
        self.assertEqual(graph['transitions'][0]['claim'], self.graph['transitions'][0]['claim'])
        self.assertTrue((self.svc.folder(self.rid)/'drafts/v0/repair.json').exists())
        self.assertTrue((self.svc.folder(self.rid)/'drafts/v1/verification.json').exists())

    def test_infrastructure_failure_never_calls_repair_model(self):
        with patch.object(self.svc, '_preflight_contract', return_value=failure('infrastructure')), \
             patch.object(self.svc, '_call') as calls:
            with self.assertRaises(service.WorkflowFailure) as error:
                self.svc._prepare_draft_contract(self.rid, self.graph, self.tid, formalization())
        self.assertEqual(error.exception.code, 'infrastructure')
        calls.assert_not_called()

    def test_explicitly_preserved_contract_is_not_automatically_rewritten(self):
        seed = formalization()
        run = self.svc.get(self.rid)
        contract = dict(run['contract'], preserve_formalization=True, revision_draft_sha256=service.sha(seed))
        self.svc.update(self.rid, contract=contract, contract_sha256=service.sha(contract), revision_draft=seed)
        with patch.object(self.svc, '_preflight_contract', return_value=failure()), \
                patch.object(self.svc, '_call') as calls:
            with self.assertRaisesRegex(service.WorkflowFailure, 'Точная сохранённая постановка'):
                self.svc._prepare_draft_contract(self.rid, self.graph, self.tid, seed)
        calls.assert_not_called()
        self.assertEqual(self.svc.get(self.rid)['revision_draft'], seed)
        self.assertFalse((self.svc.folder(self.rid)/'drafts/v0/repair.json').exists())

    def test_exhausted_repairs_never_publish_a_contract(self):
        sequence = [failure(), failure(), failure()]
        repairs = [REPAIR, dict(REPAIR, replacements=[], imports_additions=['Mathlib.Data.Nat.Basic'])]
        with patch.object(self.svc, '_preflight_contract', side_effect=sequence), \
             patch.object(self.svc, '_call', side_effect=[{'text':json.dumps(p)} for p in repairs]) as calls, \
             patch('research_retrieval.search_library', return_value=[]):
            with self.assertRaises(service.WorkflowFailure):
                self.svc._prepare_draft_contract(self.rid, self.graph, self.tid, formalization())
        self.assertEqual(calls.call_count, 2)
        self.assertEqual(self.svc.get(self.rid)['draft_repair']['status'], 'stopped')

    def test_missing_module_repair_persists_versions_and_rechecks_without_model(self):
        root = Path(self.temp.name) / 'module-fixture'
        module_fixture(root, RIGHT)
        original = import_draft()
        before = copy.deepcopy(self.svc.get(self.rid)['object_contract'])
        reports = [missing_report(root), dict(well_typed=True)]
        with patch.object(self.svc, '_preflight_contract', side_effect=reports) as checks, \
             patch.object(self.svc, '_call') as calls:
            _, fixed = self.svc._prepare_draft_contract(self.rid, self.graph, self.tid, original)
        self.assertEqual(checks.call_count, 2)
        calls.assert_not_called()
        expected = copy.deepcopy(original); expected['agent_task']['imports'] = [RIGHT]
        self.assertEqual(fixed, expected)
        self.assertEqual(self.svc.get(self.rid)['object_contract'], before)
        folder = self.svc.folder(self.rid) / 'drafts'
        first = json.loads((folder/'v0/draft.json').read_text(encoding='utf-8'))
        second = json.loads((folder/'v1/draft.json').read_text(encoding='utf-8'))
        self.assertEqual(first['formalization']['agent_task']['imports'], [WRONG])
        self.assertEqual(second['parent_sha256'], first['draft_sha256'])
        self.assertEqual(second['formalization']['obligations'], first['formalization']['obligations'])
        self.assertEqual(json.loads((folder/'v0/import-check.json').read_text())['status'], 'repairable')
        self.assertEqual(json.loads((folder/'v0/repair.json').read_text(encoding='utf-8'))['kind'], 'local_import_path_repair')
        self.assertFalse(json.loads((folder/'v0/verification.json').read_text())['well_typed'])
        self.assertTrue(json.loads((folder/'v1/verification.json').read_text())['well_typed'])
        self.assertEqual(self.svc.get(self.rid)['usage']['calls'], 0)
        self.assertEqual(self.svc.get(self.rid)['draft_repair']['repairs'], 1)

    def test_import_replacement_is_not_assumed_to_make_contract_well_typed(self):
        root = Path(self.temp.name) / 'module-fixture'; module_fixture(root, RIGHT)
        still_bad = dict(failure(), diagnostics=[dict(stdout='type mismatch')])
        with patch.object(self.svc, '_preflight_contract', side_effect=[missing_report(root), still_bad]), \
             patch.object(self.svc, '_call') as calls:
            with self.assertRaises(service.WorkflowFailure):
                self.svc._prepare_draft_contract(self.rid, self.graph, self.tid, import_draft())
        calls.assert_not_called()
        self.assertEqual(self.svc.get(self.rid)['draft_repair']['status'], 'stopped')
        self.assertFalse((self.svc.folder(self.rid)/'formal-contract.json').exists())

    def test_missing_cache_is_infrastructure_and_does_not_trigger_repair(self):
        root = Path(self.temp.name) / 'module-fixture'
        module_fixture(root, RIGHT); module_fixture(root, WRONG, compiled=False)
        with patch.object(self.svc, '_preflight_contract', return_value=missing_report(root)), \
             patch.object(self.svc, '_call') as calls:
            with self.assertRaises(service.WorkflowFailure) as error:
                self.svc._prepare_draft_contract(self.rid, self.graph, self.tid, import_draft())
        self.assertEqual(error.exception.code, 'infrastructure')
        calls.assert_not_called()
        self.assertFalse((self.svc.folder(self.rid)/'drafts/v1').exists())

    def test_module_moves_share_the_same_two_repair_limit(self):
        root = Path(self.temp.name) / 'module-fixture'
        wrong = ['Mathlib.Wrong.' + name for name in ['First', 'Second', 'Third']]
        for name in ['First', 'Second', 'Third']:
            module_fixture(root, 'Mathlib.Correct.' + name)
        value = import_draft(); value['agent_task']['imports'] = wrong
        with patch.object(self.svc, '_preflight_contract', side_effect=[missing_report(root, name) for name in wrong]) as checks, \
             patch.object(self.svc, '_call') as calls:
            with self.assertRaises(service.WorkflowFailure):
                self.svc._prepare_draft_contract(self.rid, self.graph, self.tid, value)
        calls.assert_not_called()
        self.assertEqual(checks.call_count, 3)
        saved = self.svc.get(self.rid)['draft_repair']
        self.assertEqual(saved['repairs'], 2)
        self.assertEqual(saved['max_repairs'], 2)
        self.assertEqual(saved['import_status'], 'repair_limit')
        self.assertFalse((self.svc.folder(self.rid)/'drafts/v3').exists())

    def test_resumed_import_repair_does_not_silently_change_saved_evidence(self):
        root = Path(self.temp.name) / 'module-fixture'; module_fixture(root, RIGHT)
        with patch.object(self.svc, '_preflight_contract', side_effect=[missing_report(root), dict(well_typed=True)]):
            self.svc._prepare_draft_contract(self.rid, self.graph, self.tid, import_draft())
        candidate = root.joinpath(*RIGHT.split('.')).with_suffix('.lean')
        candidate.write_text('-- Changed local source after the saved repair\n', encoding='utf-8')
        with patch.object(self.svc, '_preflight_contract', return_value=missing_report(root)), \
             patch.object(self.svc, '_call') as calls:
            with self.assertRaisesRegex(ValueError, 'Сохранённое исправление импорта'):
                self.svc._prepare_draft_contract(self.rid, self.graph, self.tid, import_draft())
        calls.assert_not_called()


@unittest.skipUnless(Path(lean.lean_service.default_context()['lean']).is_file(), 'Prepared Lean unavailable')
class RealIterationDraftTest(unittest.TestCase):
    def test_real_pinned_iteration_api_elaborates_without_proof(self):
        fixed = drafts.apply_repair(formalization(), REPAIR, failure())
        with tempfile.TemporaryDirectory() as folder:
            report = lean.verify_contract(dict(fixed['agent_task'], required_obligations=fixed['obligations']), folder)
            self.assertTrue(report['well_typed'], json.dumps(report, ensure_ascii=False))
            self.assertFalse(report['proof_checked'])
            self.assertEqual(report['audit']['status'], 'passed')


if __name__ == '__main__':
    unittest.main()
