"""Local module inventory checks. Cache fixtures are bytes, never Lean proofs."""
import copy
import json
from pathlib import Path
import sys
import tempfile
import time
import unittest
from unittest.mock import patch

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
import research_drafts as drafts
import research_lean as lean

WRONG = 'Mathlib.LinearAlgebra.Matrix.ConjTranspose'
RIGHT = 'Mathlib.Data.Matrix.ConjTranspose'


def module_fixture(root, module, *, compiled=True):
    source = root.joinpath(*module.split('.')).with_suffix('.lean')
    source.parent.mkdir(parents=True, exist_ok=True)
    source.write_text('-- Inventory fixture only; no theorem or compiler run.\n', encoding='utf-8')
    if compiled:
        cache = root / '.lake' / 'build' / 'lib' / 'lean'
        artifact = cache.joinpath(*module.split('.')).with_suffix('.olean')
        artifact.parent.mkdir(parents=True, exist_ok=True)
        artifact.write_bytes(b'NOT A COMPILED PROOF: inventory fixture')


def missing_report(root, module=WRONG):
    cache = root / '.lake' / 'build' / 'lib' / 'lean'
    return dict(well_typed=False, status='rejected', proof_checked=False,
        error='Lean rejected ContractTypes.lean', termination=dict(code='invalid_contract'),
        diagnostics=[dict(stdout=f"ContractTypes.lean:1:0: error: object file 'not-a-trusted-path' of module {module} does not exist\n")],
        context=dict(mathlib=str(root), lean_search_paths=[str(cache)], mathlib_revision='test-fixture',
                     mathlib_manifest_sha256='test-fixture'))


def draft(module=WRONG):
    statement = '∀ (n : Nat), n = n'
    return dict(status='ready', reason='Inventory test', limitations=['No Lean invocation'],
        agent_task=dict(imports=[module], prelude='', target='unchanged', statement=statement),
        obligations=[dict(id='original', title='Original obligation', target='unchanged',
                          statement=statement, expected_outcome='proved')])


class ImportInventoryTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.root = Path(self.temp.name) / 'mathlib'
        module_fixture(self.root, RIGHT)

    def tearDown(self):
        self.temp.cleanup()

    def test_unique_conjtranspose_move_changes_only_imports(self):
        original = draft()
        decision = drafts.inspect_missing_imports(original, missing_report(self.root))
        self.assertEqual(decision['status'], 'repairable')
        self.assertEqual([(x['old'], x['new']) for x in decision['replacements']], [(WRONG, RIGHT)])
        self.assertFalse(decision['proof_checked'])
        fixed = drafts.apply_import_repair(original, decision)
        expected = copy.deepcopy(original); expected['agent_task']['imports'] = [RIGHT]
        self.assertEqual(fixed, expected)
        self.assertEqual(original, draft())

    def test_move_is_general_not_a_conjtranspose_allowlist(self):
        module_fixture(self.root, 'Mathlib.Other.ExactUniqueName')
        original = draft('Mathlib.Wrong.ExactUniqueName')
        result = drafts.inspect_missing_imports(original, missing_report(self.root, original['agent_task']['imports'][0]))
        self.assertEqual(result['status'], 'repairable')
        self.assertEqual(result['replacements'][0]['new'], 'Mathlib.Other.ExactUniqueName')

    def test_ambiguous_terminal_name_is_never_ranked_or_guessed(self):
        module_fixture(self.root, 'Mathlib.Other.ConjTranspose')
        result = drafts.inspect_missing_imports(draft(), missing_report(self.root))
        self.assertEqual(result['status'], 'ambiguous')
        with self.assertRaises(ValueError):
            drafts.apply_import_repair(draft(), result)

    def test_existing_source_with_missing_cache_is_not_an_import_move(self):
        module_fixture(self.root, WRONG, compiled=False)
        result = drafts.inspect_missing_imports(draft(), missing_report(self.root))
        self.assertEqual(result['status'], 'cache_missing')
        self.assertEqual(result['replacements'], [])

    def test_existing_cache_but_compiler_cannot_resolve_it_is_not_rewritten(self):
        module_fixture(self.root, WRONG)
        result = drafts.inspect_missing_imports(draft(), missing_report(self.root))
        self.assertEqual(result['status'], 'cache_resolution_conflict')

    def test_unique_candidate_requires_its_prepared_olean(self):
        cache = self.root / '.lake' / 'build' / 'lib' / 'lean'
        cache.joinpath(*RIGHT.split('.')).with_suffix('.olean').unlink()
        result = drafts.inspect_missing_imports(draft(), missing_report(self.root))
        self.assertEqual(result['status'], 'candidate_cache_missing')

    def test_transitive_missing_module_cannot_replace_direct_import(self):
        result = drafts.inspect_missing_imports(draft(RIGHT), missing_report(self.root))
        self.assertEqual(result['status'], 'indirect_missing_module')

    def test_no_same_terminal_source_is_not_a_candidate(self):
        value = 'Mathlib.Wrong.NoSuchModule'
        result = drafts.inspect_missing_imports(draft(value), missing_report(self.root, value))
        self.assertEqual(result['status'], 'no_candidate')

    def test_traversal_is_rejected_before_resolving_any_path(self):
        for value in ['Mathlib..ConjTranspose', '../Mathlib/ConjTranspose',
                      'Mathlib.Data/Matrix.ConjTranspose', 'Mathlib.C:ConjTranspose']:
            with self.subTest(module=value), patch.object(Path, 'resolve', side_effect=AssertionError('No filesystem lookup allowed')):
                result = drafts.inspect_missing_imports(draft(value), missing_report(self.root, value))
                self.assertEqual(result['status'], 'invalid_module_name')

    def test_unpinned_cache_root_is_not_used(self):
        report = missing_report(self.root)
        report['context']['lean_search_paths'] = [str(self.root / 'other-cache')]
        self.assertEqual(drafts.inspect_missing_imports(draft(), report)['status'], 'unavailable_environment')

    def test_inventory_respects_cancellation_callback(self):
        def stop():
            raise RuntimeError('controlled cancellation')
        with self.assertRaisesRegex(RuntimeError, 'controlled cancellation'):
            drafts.inspect_missing_imports(draft(), missing_report(self.root), check=stop)


_LEAN_CONTEXT = lean.lean_service.default_context()
_REAL_MODULES_READY = (Path(_LEAN_CONTEXT['lean']).is_file() and
    (Path(_LEAN_CONTEXT['mathlib']) / 'Mathlib/Data/Matrix/ConjTranspose.lean').is_file() and
    (Path(_LEAN_CONTEXT['mathlib']) / '.lake/build/lib/lean/Mathlib/Data/Matrix/ConjTranspose.olean').is_file())


@unittest.skipUnless(_REAL_MODULES_READY, 'Prepared pinned Lean/Mathlib source and cache unavailable')
class RealMissingModuleDraftTest(unittest.TestCase):
    def test_real_missing_import_moves_then_fresh_contract_elaborates(self):
        """Integration of the repair boundary, not a proof of the exterior task."""
        import research_service as service
        from research_objects import validate_graph

        value = draft()
        statement = ('∀ (n : ℕ) (A : Matrix (Fin n) (Fin n) ℂ), '
                     'Matrix.conjTranspose (Matrix.conjTranspose A) = A')
        value['agent_task'].update(imports=[WRONG, 'Mathlib.Analysis.Complex.Basic'],
                                  target='module_repair_double_adjoint', statement=statement)
        value['obligations'][0].update(target='module_repair_double_adjoint', statement=statement)
        with tempfile.TemporaryDirectory() as folder:
            svc = service.ResearchService(folder, recover=False)
            try:
                run = svc.create(dict(mode='single', case_id='graph_energy'), start=False)
                rid = run['id']; svc._started[rid] = time.monotonic()
                graph = validate_graph(run['object_graph']); tid = graph['transitions'][0]['id']
                graph['transitions'][0].update(formulation_status='literature_only',
                                               agent_task=None, obligations=[], case_id=None)
                # Both the service model boundary and its underlying transport
                # are guarded; the compiler itself is deliberately not mocked.
                with patch.object(svc, '_call', side_effect=AssertionError('No model call in compiler regression')), \
                     patch('research_codex.run_task', side_effect=AssertionError('No external model transport')):
                    _, fixed = svc._prepare_draft_contract(rid, graph, tid, value)
                drafts_root = svc.folder(rid) / 'drafts'
                before = json.loads((drafts_root/'v0/verification.json').read_text(encoding='utf-8'))
                after = json.loads((drafts_root/'v1/verification.json').read_text(encoding='utf-8'))
                self.assertFalse(before['well_typed'])
                self.assertIn(WRONG, drafts.missing_modules(before))
                self.assertTrue(any(d.get('exit_code') == 1 for d in before['diagnostics']))
                self.assertTrue(after['well_typed'], json.dumps(after, ensure_ascii=False))
                self.assertFalse(after['proof_checked'])
                self.assertNotEqual(before['workspace'], after['workspace'])
                self.assertTrue(all(d['exit_code'] == 0 for d in after['diagnostics']))
                self.assertEqual(fixed['agent_task']['imports'], [RIGHT, 'Mathlib.Analysis.Complex.Basic'])
                expected = copy.deepcopy(value); expected['agent_task']['imports'] = fixed['agent_task']['imports']
                self.assertEqual(fixed, expected)
                self.assertEqual(svc.get(rid)['usage']['calls'], 0)
                self.assertEqual(svc.get(rid)['draft_repair']['repairs'], 1)
            finally:
                svc.pool.shutdown(wait=True)


if __name__ == '__main__':
    unittest.main()
