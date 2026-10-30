import json
from pathlib import Path
import sys
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))
import research_lean as service


class FixtureContractTests(unittest.TestCase):
    def test_agent_tasks_exclude_reference_solutions(self):
        for fixture in service.fixtures():
            task = fixture["agent_task"]
            self.assertNotIn("theorem ", service.lean_service._mask(task["prelude"]))
            self.assertEqual(task["prelude_sha256"], service._sha(task["prelude"]))
            self.assertTrue(task["lemmas"])
            self.assertEqual(task["statement"], fixture["expected_statement"])

    def test_generated_code_subset_rejects_compile_time_commands(self):
        for source in ["#eval IO.println 1", "run_elab pure ()", "axiom x : False", "theorem x : False := by sorry",
                       "set_option debug.skipKernelTC true\ntheorem x : True := by trivial"]:
            with self.subTest(source=source), self.assertRaises(ValueError):
                service._validate_source(source)
        service._validate_source("-- sorry\ntheorem okay : True := by trivial")

    def test_unknown_case_is_not_silently_replaced(self):
        with self.assertRaises(ValueError):
            service.run_pilot("missing_case", Path("/tmp/unused"))

    def test_runtime_helper_in_logical_axiom_closure_is_still_rejected(self):
        helper = 'Finset.sum._at.edgeEnergy._spec_1'
        declarations = [dict(name=helper, kind='axiom', unsafe=True, axioms=[helper]),
                        dict(name='target', kind='theorem', unsafe=False, axioms=[helper])]
        result = service._audit_declarations(declarations, 'theorem target : True := by trivial', 'target')
        self.assertEqual(result['status'], 'rejected')
        self.assertIn(helper, result['unexpected_axioms'])
        self.assertEqual(len(result['ignored_implementation_helpers']), 1)

    def test_explicit_helper_shaped_declaration_is_not_ignored(self):
        helper = 'Finset.sum._at.edgeEnergy._spec_1'
        result = service._audit_declarations([dict(name=helper, kind='axiom', unsafe=True, axioms=[helper])],
                                             'def ' + helper + ' : Nat := 0', 'target')
        self.assertEqual(result['status'], 'rejected')
        self.assertFalse(result['ignored_implementation_helpers'])


@unittest.skipUnless(Path(service.lean_service.default_context()["lean"]).is_file(), "Prepared Lean unavailable")
class RealLeanContractTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.temp = tempfile.TemporaryDirectory(prefix="research-lean-contract-")
        cls.work = Path(cls.temp.name)

    @classmethod
    def tearDownClass(cls):
        cls.temp.cleanup()

    def test_checked_target_matches_independent_type(self):
        result = service.verify_candidate("theorem identity (n : Nat) : n = n := by rfl", "identity", self.work,
                                          "∀ n : Nat, n = n")
        self.assertTrue(result["success"], json.dumps(result, ensure_ascii=False))
        self.assertTrue(result["target_preserved"])
        self.assertEqual(result["audit"]["status"], "passed")

    def test_compiled_wrong_target_is_not_accepted(self):
        result = service.verify_candidate("theorem weak : True := by trivial", "weak", self.work,
                                          "∀ n : Nat, n = n")
        self.assertTrue(result["compilation_success"])
        self.assertFalse(result["success"])
        self.assertFalse(result["target_preserved"])
        self.assertEqual(result["outcome"], "unknown")

    def test_cancel_is_neither_refutation_nor_proof(self):
        result = service.verify_candidate("theorem okay : True := by trivial", "okay", self.work,
                                          "True", cancelled=lambda: True)
        self.assertEqual(result["status"], "cancelled")
        self.assertEqual(result["outcome"], "unknown")

    def test_graph_bridge_has_actual_proof_dependency(self):
        result = service.run_pilot("graph_energy", self.work)
        self.assertEqual(result["outcome"], "proved", json.dumps(result, ensure_ascii=False))
        self.assertTrue(all(c["passed"] for c in result["checks"]))
        self.assertTrue(any(e["source"] == "TriangleEnergy.graph_energy_eq" and
                            e["target"] == "TriangleEnergy.laplacian_nonnegative" and
                            e["type"] == "proof_dependency" for e in result["edges"]))

    def test_false_claim_has_checked_counterexample(self):
        result = service.run_pilot("strict_inequality", self.work)
        self.assertEqual(result["outcome"], "refuted", json.dumps(result, ensure_ascii=False))
        self.assertTrue(result["verification"]["success"])
        self.assertEqual(result["semantic_review"]["counterexample"]["a"], 0)

    def test_pure_finite_sum_runtime_specializations_are_not_logical_axioms(self):
        source = '''import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.BigOperators
open scoped BigOperators
universe u v
def edgeDifference {V : Type u} {E : Type v}
    (s t : E → V) (f : V → ℝ) : E → ℝ := fun e => f (s e) - f (t e)
def edgeEnergy {V : Type u} {E : Type v} [Fintype E]
    (s t : E → V) (w : E → ℝ) (f : V → ℝ) : ℝ :=
  ∑ e, w e * (edgeDifference s t f e) ^ 2
theorem energy_self {V : Type u} {E : Type v} [Fintype E]
    (s t : E → V) (w : E → ℝ) (f : V → ℝ) :
    edgeEnergy s t w f = edgeEnergy s t w f := by rfl
'''
        statement = '''∀ {V : Type u} {E : Type v} [Fintype E]
            (s t : E → V) (w : E → ℝ) (f : V → ℝ), edgeEnergy s t w f = edgeEnergy s t w f'''
        result = service.verify_candidate(source, 'energy_self', self.work, statement)
        self.assertTrue(result['success'], json.dumps(result, ensure_ascii=False))
        self.assertTrue(result['target_preserved'])
        self.assertTrue(result['audit']['ignored_implementation_helpers'])
        self.assertFalse(result['audit']['unexpected_axioms'])
        self.assertIn('edgeEnergy', result['audit']['audited_roots'])


if __name__ == "__main__":
    unittest.main()
