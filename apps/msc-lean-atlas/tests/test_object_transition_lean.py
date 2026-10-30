import json
from pathlib import Path
import sys
import tempfile
import unittest
from unittest.mock import patch

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))

import research_lean as lean
from research_object_examples import graph_for_case
from research_objects import validate_graph


class PreparedObjectGraphTests(unittest.TestCase):
    def test_each_transition_has_a_pinned_primary_goal_and_real_endpoints(self):
        for fixture in lean.fixtures():
            with self.subTest(case=fixture["id"]):
                graph = graph_for_case(fixture)
                objects = {item["id"] for item in graph["objects"]}
                self.assertTrue(graph["sources"])
                for transition in graph["transitions"]:
                    self.assertTrue(set(transition["source_ids"]) <= objects)
                    self.assertTrue(set(transition["target_ids"]) <= objects)
                    self.assertIn(transition["relation_type"], {"construction", "representation", "property_transfer", "equivalence", "reduction"})
                    task = transition["agent_task"]
                    self.assertEqual(set(task), {"imports", "prelude", "target", "statement"})
                    self.assertNotIn("theorem ", lean.lean_service._mask(task["prelude"]))
                    self.assertTrue(any(o["target"] == task["target"] and o["statement"] == task["statement"]
                                        for o in transition["obligations"]))
                    lean._validate_obligations(transition["obligations"])

    def test_nonnegative_transfer_requires_both_representation_and_property(self):
        graph = graph_for_case("graph_energy")
        identity, transfer = graph["transitions"]
        self.assertFalse(identity["assumptions"])
        self.assertEqual(identity["agent_task"]["statement"], lean.ENERGY_STATEMENT)
        self.assertEqual(transfer["assumptions"], ["0 ≤ w01", "0 ≤ w12", "0 ≤ w02"])
        self.assertEqual({o["target"] for o in transfer["obligations"]},
                         {"TriangleEnergy.graph_energy_eq", "TriangleEnergy.laplacian_nonnegative"})

    def test_negative_control_preserves_identity_without_claiming_positivity(self):
        identity, transfer = graph_for_case("graph_energy_negative")["transitions"]
        self.assertFalse(identity["assumptions"])
        self.assertFalse(transfer["assumptions"])
        self.assertEqual(identity["obligations"][0]["expected_outcome"], "proved")
        self.assertEqual(transfer["obligations"][-1]["expected_outcome"], "refuted")
        self.assertEqual(transfer["agent_task"]["statement"], lean.NEGATIVE_ENERGY_STATEMENT)
        self.assertEqual(len(transfer["obligations"]), 3)

    def test_graphs_are_canonical_and_do_not_share_mutable_contracts(self):
        graph = graph_for_case({"id": "graph_energy", "claim": "changed"})
        graph["transitions"][0]["obligations"][0]["statement"] = "True"
        fresh = graph_for_case("graph_energy")
        self.assertEqual(fresh["transitions"][0]["obligations"][0]["statement"], lean.ENERGY_STATEMENT)
        self.assertNotEqual(fresh["question"], "changed")
        with self.assertRaises(ValueError):
            graph_for_case("unknown")

    def test_malformed_or_duplicate_obligations_rejected_before_compilation(self):
        valid = dict(id="identity", target="identity", statement="∀ n : Nat, n = n", expected_outcome="proved")
        invalid = [[valid, valid], [{**valid, "expected_outcome": "unknown"}],
                   [{**valid, "statement": "True\ntheorem injected : True := by trivial"}],
                   [{**valid, "target": "identity\nimport Mathlib"}], "not a list"]
        with tempfile.TemporaryDirectory() as folder, patch.object(lean.lean_service, "_prepare") as prepare:
            for obligations in invalid:
                with self.subTest(obligations=obligations):
                    result = lean.verify_candidate("theorem identity (n : Nat) : n = n := by rfl", "identity", folder,
                                                   "∀ n : Nat, n = n", required_obligations=obligations)
                    self.assertEqual(result["status"], "rejected")
                    self.assertFalse(result["obligations_passed"])
            prepare.assert_not_called()

    def test_selected_pilot_cannot_replace_canonical_definitions(self):
        transition = graph_for_case("graph_energy")["transitions"][0]
        task = {**transition["agent_task"], "required_obligations": transition["obligations"]}
        task["prelude"] += "\ndef altered : Nat := 0\n"
        with tempfile.TemporaryDirectory() as folder, patch.object(lean, "verify_candidate") as verify:
            with self.assertRaises(ValueError):
                lean.run_pilot("graph_energy", folder, transition_task=task)
            verify.assert_not_called()


@unittest.skipUnless(Path(lean.lean_service.default_context()["lean"]).is_file(), "Prepared Lean unavailable")
class RealObjectTransitionLeanTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.temp = tempfile.TemporaryDirectory(prefix="object-transition-lean-")
        cls.work = Path(cls.temp.name)

    @classmethod
    def tearDownClass(cls):
        cls.temp.cleanup()

    def _sample(self, second_statement="True", second_target="Sample.truth"):
        source = "theorem Sample.identity (n : Nat) : n = n := by rfl\ntheorem Sample.truth : True := by trivial\n"
        obligations = [dict(id="identity", target="Sample.identity", statement="∀ n : Nat, n = n", expected_outcome="proved"),
                       dict(id="second", target=second_target, statement=second_statement, expected_outcome="proved")]
        return source, obligations

    def test_one_final_contract_checks_every_exact_obligation(self):
        source, obligations = self._sample()
        with patch.object(lean, "_run", wraps=lean._run) as run:
            result = lean.verify_candidate(source, "Sample.identity", self.work, "∀ n : Nat, n = n",
                                           required_obligations=obligations)
        self.assertTrue(result["success"], json.dumps(result, ensure_ascii=False))
        self.assertTrue(result["target_preserved"])
        self.assertTrue(result["obligations_passed"])
        self.assertTrue(all(item["ok"] for item in result["obligations"]))
        self.assertEqual([call.args[3] for call in run.call_args_list].count("Contract.lean"), 1)
        self.assertEqual(result["obligations"][1]["statement_sha256"], lean._sha("True"))
        self.assertEqual(result["audit"]["status"], "passed")
        self.assertIn("Sample.truth", result["audit"]["audited_roots"])

    def test_valid_primary_cannot_hide_a_weakened_second_goal(self):
        source, obligations = self._sample("∀ n : Nat, n = n")
        result = lean.verify_candidate(source, "Sample.identity", self.work, "∀ n : Nat, n = n",
                                       required_obligations=obligations)
        self.assertTrue(result["compilation_success"])
        self.assertFalse(result["success"])
        self.assertFalse(result["target_preserved"])
        self.assertFalse(result["obligations_passed"])
        self.assertTrue(all(not item["ok"] for item in result["obligations"]))
        self.assertEqual([d["file"] for d in result["diagnostics"]].count("Contract.lean"), 1)

    def test_missing_obligation_is_not_replaced_by_a_matching_primary(self):
        source, obligations = self._sample(second_target="Sample.missing")
        result = lean.verify_candidate(source, "Sample.identity", self.work, "∀ n : Nat, n = n",
                                       required_obligations=obligations)
        self.assertTrue(result["compilation_success"])
        self.assertEqual(result["status"], "rejected")
        self.assertFalse(result["obligations_passed"])

    def test_definition_cannot_stand_in_for_an_obligation_theorem(self):
        source, obligations = self._sample("Nat", "Sample.value")
        source += "def Sample.value : Nat := 0\n"
        result = lean.verify_candidate(source, "Sample.identity", self.work, "∀ n : Nat, n = n",
                                       required_obligations=obligations)
        self.assertTrue(result["compilation_success"])
        self.assertEqual(result["status"], "rejected")

    def test_existing_call_without_extra_contracts_remains_supported(self):
        result = lean.verify_candidate("theorem identity (n : Nat) : n = n := by rfl", "identity", self.work,
                                       "∀ n : Nat, n = n")
        self.assertTrue(result["success"], json.dumps(result, ensure_ascii=False))
        self.assertTrue(result["target_preserved"])
        self.assertEqual(result["obligations"], [])
        self.assertTrue(result["obligations_passed"])

    def test_positive_pilot_checks_the_representation_and_transfer_together(self):
        result = lean.run_pilot("graph_energy", self.work)
        self.assertEqual(result["outcome"], "proved", json.dumps(result, ensure_ascii=False))
        self.assertTrue(result["verification"]["obligations_passed"])
        self.assertEqual(len(result["verification"]["obligations"]), 2)
        self.assertTrue(all(check["passed"] for check in result["checks"]))

    def test_negative_weight_is_real_refutation_while_identity_stays_proved(self):
        result = lean.run_pilot("graph_energy_negative", self.work)
        self.assertEqual(result["outcome"], "refuted", json.dumps(result, ensure_ascii=False))
        checked = result["verification"]
        self.assertTrue(checked["success"])
        self.assertTrue(checked["obligations_passed"])
        self.assertEqual(len(checked["obligations"]), 3)
        self.assertEqual(result["semantic_review"]["counterexample"]["form_value"], -1)
        self.assertTrue(any(edge["source"] == "TriangleEnergy.graph_energy_eq" and
                            edge["target"] == "TriangleEnergyNegative.negative_weight_witness" and
                            edge["type"] == "proof_dependency" for edge in result["edges"]))

    def test_selected_identity_in_negative_case_is_proved_not_refuted(self):
        transition = validate_graph(graph_for_case("graph_energy_negative"))["transitions"][0]
        task = {**transition["agent_task"], "required_obligations": transition["obligations"]}
        result = lean.run_pilot("graph_energy_negative", self.work, transition_task=task)
        self.assertEqual(result["outcome"], "proved", json.dumps(result, ensure_ascii=False))
        self.assertEqual(result["fixture"]["expected_outcome"], "refuted")
        self.assertEqual(result["verification"]["target"], "TriangleEnergy.graph_energy_eq")
        self.assertEqual(len(result["verification"]["obligations"]), 1)
        self.assertEqual(result["selected_target"]["expected_outcome"], "proved")
        self.assertEqual(result["semantic_review"]["assumptions"], [])


if __name__ == "__main__":
    unittest.main()
