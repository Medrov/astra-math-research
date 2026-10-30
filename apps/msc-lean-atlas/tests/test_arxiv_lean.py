import json
from pathlib import Path
import sys
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))

import research_arxiv_example as example
import research_lean as lean
from research_objects import GraphRegistry


class ArxivExampleContractTests(unittest.TestCase):
    def test_source_scope_and_polynomial_contract_are_explicit(self):
        fixture = example.fixture()
        graph = example.graph_for_article()
        transition = graph["transitions"][0]
        self.assertEqual(fixture["id"], example.CASE_ID)
        self.assertEqual(fixture["required_obligations"], transition["obligations"])
        self.assertEqual(len(transition["obligations"]), 3)
        self.assertIn("MvPolynomial.X", transition["obligations"][0]["statement"])
        self.assertIn("MvPolynomial.X", transition["obligations"][1]["statement"])
        self.assertIn("Polynomial.X", transition["obligations"][2]["statement"])
        self.assertIn("9.1", graph["sources"][0]["locator"])
        self.assertIn("9.2", graph["sources"][0]["locator"])
        self.assertIn("не весь", transition["claim"])
        self.assertTrue(any("не проверены" in note for note in example.example()["limitations"]))
        self.assertEqual(set(transition["agent_task"]), {"imports", "prelude", "target", "statement"})
        self.assertNotIn("theorem ", lean.lean_service._mask(transition["agent_task"]["prelude"]))
        lean._validate_source(example.source())
        lean._validate_obligations(transition["obligations"])

    def test_metadata_returns_independent_contracts(self):
        first = example.graph_for_article()
        first["transitions"][0]["obligations"][0]["statement"] = "True"
        self.assertEqual(example.graph_for_article()["transitions"][0]["obligations"][0]["statement"],
                         example.SUBTRACT_RESTORE)

    def test_registry_preserves_all_three_exact_obligations_and_prelude(self):
        with tempfile.TemporaryDirectory() as directory:
            registry = GraphRegistry(Path(directory) / "objects.sqlite")
            created = registry.create(example.graph_for_article())
            restored = registry.get(created["id"])
            transition = restored["transitions"][0]
            self.assertEqual(transition["obligations"], example.obligations())
            self.assertEqual(transition["agent_task"]["prelude"], example.fixture()["agent_task"]["prelude"])


@unittest.skipUnless(Path(lean.lean_service.default_context()["lean"]).is_file(), "Prepared Lean unavailable")
class RealArxivLeanTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.temp = tempfile.TemporaryDirectory(prefix="arxiv-polynomial-lean-")
        cls.fixture = example.fixture()
        cls.result = lean.verify_candidate(example.source(), cls.fixture["target"], cls.temp.name,
                                           cls.fixture["expected_statement"],
                                           required_obligations=example.obligations())

    @classmethod
    def tearDownClass(cls):
        cls.temp.cleanup()

    def test_three_polynomial_equalities_have_one_contract_and_clean_axiom_audit(self):
        result = self.result
        self.assertTrue(result["success"], json.dumps(result, ensure_ascii=False, indent=2))
        self.assertTrue(result["target_preserved"])
        self.assertTrue(result["obligations_passed"])
        self.assertEqual(len(result["obligations"]), 3)
        self.assertTrue(all(item["ok"] for item in result["obligations"]))
        self.assertEqual(sum(item["file"] == "Contract.lean" for item in result["diagnostics"]), 1)
        self.assertEqual(result["audit"]["unexpected_axioms"], [])
        self.assertEqual(result["audit"]["unsafe_declarations"], [])
        theorems = [item for item in result["declarations"] if item["kind"] == "theorem"]
        self.assertTrue({"Arxiv261038474.eval_univariate", *[item["target"] for item in example.obligations()]}
                        <= {item["name"] for item in theorems})
        self.assertTrue(all(set(item["axioms"]) <= lean.lean_service.ALLOWED_AXIOMS for item in theorems))

    def test_graph_image_alone_cannot_certify_an_incorrect_inverse_obligation(self):
        goals = example.obligations()
        goals[0]["statement"] = example.PREFIX + "Arxiv261038474.compose (Arxiv261038474.graphSubtract b w) (Arxiv261038474.graphRestore b w) = 0"
        result = lean.verify_candidate(example.source(), self.fixture["target"], self.temp.name,
                                       self.fixture["expected_statement"], required_obligations=goals)
        self.assertTrue(result["compilation_success"])
        self.assertFalse(result["success"])
        self.assertFalse(result["obligations_passed"])
        self.assertTrue(all(not item["ok"] for item in result["obligations"]))
        self.assertEqual(result["diagnostics"][-1]["file"], "Contract.lean")
        self.assertNotEqual(result["diagnostics"][-1]["exit_code"], 0)


if __name__ == "__main__":
    unittest.main()
