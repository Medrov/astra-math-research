"""Audit the published example against its saved proof and exact arithmetic.

These checks inspect the certificate already produced by Lean. They do not
invoke Lean or infer a proof from a numerical example.
"""

from fractions import Fraction
import hashlib
import json
from pathlib import Path
import unittest


ROOT = Path(__file__).resolve().parents[1]
EXAMPLE = ROOT / "examples" / "astra_energy"


class WorkedStoryTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.story = json.loads((EXAMPLE / "story.json").read_text())
        cls.analysis = json.loads(
            (ROOT / cls.story["provenance"]["analysis_report"]).read_text()
        )
        # The story cites a historical certificate, not the mutable latest attempt.
        cls.verification = json.loads(
            (ROOT / cls.story["provenance"]["verification_report"]).read_text()
        )
        cls.graph = json.loads((ROOT / "data" / "msc2020.json").read_text())
        cls.nodes = {node["id"]: node for node in cls.graph["nodes"]}

    def test_saved_proof_is_bound_to_current_input_and_bridge_sources(self):
        bridge = self.story["bridge"]
        verification = self.verification
        self.assertEqual(bridge["status"], "verified")
        self.assertEqual(verification["status"], "verified")
        self.assertTrue(verification["success"])
        self.assertTrue(verification["lean_compilation_success"])
        self.assertEqual(bridge["verification_origin"], "saved_run")
        for key in ("analysis_id", "verification_id", "checked_at"):
            self.assertEqual(bridge[key], verification[key])
        self.assertEqual(bridge["analysis_id"], self.analysis["id"])

        self.assertEqual(bridge["input_sha256"], verification["input_sha256"])
        self.assertEqual(
            set(bridge["input_sha256"]),
            {obj["file"] for obj in self.story["objects"]},
        )
        for filename, expected_hash in bridge["input_sha256"].items():
            with self.subTest(filename=filename):
                actual_hash = hashlib.sha256((EXAMPLE / filename).read_bytes()).hexdigest()
                self.assertEqual(actual_hash, expected_hash)

        bridge_hash = hashlib.sha256((EXAMPLE / "Bridge.lean").read_bytes()).hexdigest()
        self.assertEqual(bridge_hash, bridge["source_sha256"])
        self.assertEqual(bridge_hash, verification["source_sha256"])

    def test_certificate_covers_the_exact_statement_and_both_selected_objects(self):
        bridge = self.story["bridge"]
        target = next(
            result for result in self.verification["target_results"]
            if result["name"] == bridge["declaration"]
        )
        self.assertIn(bridge["declaration"], self.verification["targets"])
        self.assertEqual(bridge["statement"], target["type"])
        self.assertTrue(bridge["both_inputs_participate"])
        self.assertTrue(target["both_inputs_participate"])

        for obj in self.story["objects"]:
            with self.subTest(declaration=obj["declaration"]):
                self.assertIs(target["selected_target_coverage"][obj["declaration"]], True)
                self.assertIn(obj["declaration"], target["input_coverage"][obj["file"]])
                self.assertIn(obj["declaration"], target["type_dependencies"])

        revision = self.story["provenance"]["project_revision"]
        self.assertEqual(revision, self.verification["context"]["project_revision"])
        self.assertIn("/" + revision + "/", bridge["source_url"])
        self.assertIn(
            bridge["source_theorem"], (EXAMPLE / "Bridge.lean").read_text()
        )

    def test_type_and_direct_dependency_overlap_match_lean_inspection(self):
        selected = []
        for obj in self.story["objects"]:
            file_report = next(
                report for report in self.analysis["files"]
                if report["name"] == obj["file"]
            )
            declaration = next(
                decl for decl in file_report["selected_declarations"]
                if decl["name"] == obj["declaration"]
            )
            self.assertEqual(declaration["extraction"], "lean_environment")
            self.assertIn(obj["direct_mathematical_dependency"], declaration["dependencies"])
            selected.append(declaration)

        shared_type = next(item for item in self.story["shared"] if item["id"] == "type")
        self.assertEqual({decl["type"] for decl in selected}, {shared_type["value"]})
        common_dependencies = set.intersection(*(set(decl["dependencies"]) for decl in selected))
        overlap = self.story["dependency_overlap"]
        self.assertEqual(set(overlap["direct_common_declarations"]), common_dependencies)
        self.assertEqual(overlap["meaningful_direct_matches"], [])
        self.assertEqual(self.analysis["structural_matches"], [])

    def test_numerical_illustration_obeys_weight_laplacian_and_energy_formulas(self):
        example = self.story["numeric_example"]
        d = [Fraction(value) for value in example["d"]]
        f = [Fraction(value) for value in example["f"]]
        self.assertEqual(len(d), 3)
        self.assertEqual(len(f), 3)
        edges = {tuple(edge["vertices"]): edge for edge in example["edge_weights"]}
        expected_pairs = {(0, 1), (0, 2), (1, 2)}
        self.assertEqual(set(edges), expected_pairs)
        self.assertEqual(len(example["edge_weights"]), len(expected_pairs))

        weights = {(i, j): (d[i] - d[j]) ** 2 / 4 for i, j in expected_pairs}
        for (i, j), weight in weights.items():
            with self.subTest(edge=(i, j)):
                edge = edges[i, j]
                squared_difference = (f[i] - f[j]) ** 2
                self.assertEqual(Fraction(edge["weight"]), weight)
                self.assertEqual(Fraction(edge["squared_difference"]), squared_difference)
                self.assertEqual(Fraction(edge["contribution"]), weight * squared_difference)

        laplacian = [
            sum(weights[tuple(sorted((i, j)))] * (f[i] - f[j])
                for j in range(3) if i != j)
            for i in range(3)
        ]
        self.assertEqual([Fraction(value) for value in example["laplacian"]], laplacian)
        edge_energy = sum(weights[i, j] * (f[i] - f[j]) ** 2 for i, j in expected_pairs)
        graph_energy = sum(f[i] * laplacian[i] for i in range(3))
        self.assertEqual(edge_energy, graph_energy)
        self.assertEqual(Fraction(example["energy"]), edge_energy)

    def test_topic_labels_and_ancestor_claims_match_official_msc_graph(self):
        paths = []
        assigned_codes = []
        for obj in self.story["objects"]:
            with self.subTest(code=obj["msc_code"]):
                node = self.nodes[obj["msc_code"]]
                self.assertEqual(obj["msc_title_original"], node["title"])
                ancestors = []
                while node is not None:
                    ancestors.append(node["id"])
                    node = self.nodes.get(node["parent_id"])
                path = list(reversed(ancestors))
                self.assertEqual(obj["msc_path"], path)
                paths.append(set(path))

                report = next(item for item in self.analysis["files"] if item["name"] == obj["file"])
                codes = {match["code"] for match in report["msc_matches"]}
                self.assertIn(obj["msc_code"], codes)
                assigned_codes.append(codes)

        classification = self.story["classification"]
        self.assertEqual(set(classification["shared_codes"]), set.intersection(*assigned_codes))
        self.assertEqual(set(classification["shared_ancestor_codes"]), set.intersection(*paths))


if __name__ == "__main__":
    unittest.main()
