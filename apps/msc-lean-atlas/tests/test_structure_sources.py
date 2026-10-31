import copy
import hashlib
import json
from pathlib import Path
import shutil
import sys
import tempfile
import unittest
from unittest.mock import patch

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))

import lean_service
import research_lean as lean
import research_structure_sources as sources


INPUT = """import Init
namespace Imported
def advance (n : Nat) : Nat := n + 1
def distractor (n : Nat) : Nat := n + 2
theorem advances (n : Nat) : advance n = n + 1 := by rfl
end Imported
"""


def _candidate(payload, body):
    return "import StructureInput\n" + sources.PIN_PREFIX + payload["source_sha256"] + "\n" + body


class StructureSourceValidationTests(unittest.TestCase):
    def test_input_is_only_one_content_source_with_mathlib_or_standard_imports(self):
        for content in ["import StructureInput", "import Candidate", "import MathResearch.AlbertSpectralGeometry",
                        "import ../Other", "axiom fake : False", "theorem fake : False := by sorry"]:
            with self.subTest(content=content), self.assertRaises(ValueError):
                sources.validate_input(content)
        self.assertEqual(sources.validate_input("\ufeff" + INPUT), INPUT)
        with tempfile.TemporaryDirectory() as directory:
            store = sources.StructureSourceStore(directory, "environment-a")
            for payload in [dict(path="D:/not-authorized.lean"), dict(content=INPUT, name="../input.lean")]:
                with self.subTest(payload=payload), self.assertRaises(ValueError):
                    store.create(payload)

    def test_missing_payload_wrong_pin_and_changed_content_rejected_before_compilation(self):
        payload = dict(source_id="1" * 32, content=INPUT, source_sha256=hashlib.sha256(INPUT.encode()).hexdigest(),
                       environment_fingerprint="environment-a", selected_declaration=dict(name="Imported.advances", kind="theorem", type="not trusted"))
        candidate = _candidate(payload, "theorem result : True := by trivial\n")
        variations = [(candidate, None), (candidate.replace(payload["source_sha256"], "0" * 64), payload),
                      (candidate, {**payload, "content": INPUT + "\n"}),
                      (candidate, {**payload, "selected_declaration": dict(name="Imported.advance", kind="def", type="Nat → Nat")}),
                      ("theorem result : True := by trivial", payload)]
        with tempfile.TemporaryDirectory() as directory, patch.object(lean_service, "_prepare") as prepare:
            for source, supplied in variations:
                with self.subTest(source=source[:50], supplied=supplied is not None):
                    result = lean.verify_candidate(source, "result", directory, "True", source_library=supplied,
                                                   require_source_usage=False)
                    self.assertFalse(result["success"])
                    self.assertEqual(result["status"], "rejected")
            prepare.assert_not_called()

    def test_input_ids_and_pin_are_not_paths_or_ambiguous_comments(self):
        with tempfile.TemporaryDirectory() as directory:
            store = sources.StructureSourceStore(directory, "env")
            for identifier in ["../x", "a/b", "a" * 31, "g" * 32]:
                with self.subTest(identifier=identifier), self.assertRaises(ValueError):
                    store.get(identifier)
        for source in ["", sources.PIN_PREFIX + "bad", (sources.PIN_PREFIX + "1" * 64 + "\n") * 2]:
            with self.subTest(source=source), self.assertRaises(ValueError):
                sources.pinned_fingerprint(source, required=True)


@unittest.skipUnless(Path(lean_service.default_context()["lean"]).is_file(), "Prepared Lean unavailable")
class RealStructureSourceTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.temp = tempfile.TemporaryDirectory(prefix="structure-source-real-")
        cls.folder = Path(cls.temp.name)
        cls.store = sources.StructureSourceStore(cls.folder / "sources", "environment-a")
        cls.created = cls.store.create(dict(content=INPUT, name="Original.lean", title="A controlled source", provenance={"kind": "test_input"}))
        if not cls.created["inspection"]["success"]:
            raise AssertionError(json.dumps(cls.created, ensure_ascii=False, indent=2))
        cls.payload = cls.store.select(cls.created["source_id"], "Imported.advances")

    @classmethod
    def tearDownClass(cls):
        cls.temp.cleanup()

    def test_real_inspection_and_read_guards(self):
        created = self.created
        self.assertEqual(created["status"], "ready")
        self.assertEqual(created["module"], "StructureInput")
        self.assertEqual(created["inspection"]["audit"]["status"], "passed")
        self.assertEqual(created["inspection"]["print_axioms"]["exit_code"], 0)
        self.assertIn("Imported.advances", created["inspection"]["print_axioms"]["stdout"])
        self.assertEqual({item["name"] for item in created["definitions"]}, {"Imported.advance", "Imported.distractor"})
        self.assertTrue(any(item["source_id"] == created["source_id"] for item in self.store.list_sources()))
        with self.assertRaises(ValueError):
            self.store.select(created["source_id"], "Imported.advance")
        with self.assertRaises(ValueError):
            sources.StructureSourceStore(self.folder / "sources", "environment-b").get(created["source_id"])
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            copy_folder = root / created["source_id"]
            copy_folder.mkdir()
            for name in ["StructureInput.lean", "snapshot.json"]:
                shutil.copyfile(self.folder / "sources" / created["source_id"] / name, copy_folder / name)
            copy_store = sources.StructureSourceStore(root, "environment-a")
            self.assertEqual(copy_store.get(created["source_id"])["source_sha256"], created["source_sha256"])
            (copy_folder / "StructureInput.lean").write_text(INPUT + "\n-- changed\n", encoding="utf-8")
            with self.assertRaisesRegex(ValueError, "Содержимое"):
                copy_store.get(created["source_id"])
            (copy_folder / "StructureInput.lean").write_text(INPUT, encoding="utf-8")
            metadata = json.loads((copy_folder / "snapshot.json").read_text(encoding="utf-8"))
            metadata["title"] = "tampered"
            (copy_folder / "snapshot.json").write_text(json.dumps(metadata), encoding="utf-8")
            with self.assertRaisesRegex(ValueError, "Метаданные"):
                copy_store.get(created["source_id"])

    def test_real_definition_anchor_and_separate_proof_only_signal(self):
        candidate = _candidate(self.payload, """theorem Bridge.definition (n : Nat) : Imported.advance n = n + 1 := by rfl
theorem Bridge.reused (n : Nat) : n + 1 = n + 1 := by exact Imported.advances n
""")
        result = lean.verify_candidate(candidate, "Bridge.definition", self.folder / "checks",
                                       "∀ n : Nat, Imported.advance n = n + 1", source_library=self.payload)
        self.assertTrue(result["success"], json.dumps(result, ensure_ascii=False, indent=2))
        self.assertTrue(result["source_library"]["fresh_compilation"])
        self.assertEqual(result["print_axioms"]["exit_code"], 0)
        self.assertIn("Bridge.definition", result["print_axioms"]["stdout"])
        self.assertIn("Bridge.reused", result["print_axioms"]["stdout"])
        self.assertEqual(result["source_library"]["audit"]["status"], "passed")
        self.assertIn("Imported.advance", result["source_usage"]["type_participation"])
        self.assertFalse(result["source_usage"]["selected_theorem_used"])
        self.assertNotIn("Imported.distractor", result["source_usage"]["relevant_definitions"])
        proof_only = sources.source_usage("Bridge.reused", result["declarations"], result["source_library"]["declarations"],
                                          "Imported.advances", INPUT)
        self.assertTrue(proof_only["selected_theorem_used"])
        self.assertFalse(proof_only["type_participation"])
        self.assertIn("Imported.advances", proof_only["proof_only_participation"])

    def test_unrelated_input_definition_rejected_but_helper_can_defer_usage(self):
        candidate = _candidate(self.payload, "theorem Bridge.unrelated (n : Nat) : Imported.distractor n = n + 2 := by rfl\n")
        statement = "∀ n : Nat, Imported.distractor n = n + 2"
        rejected = lean.verify_candidate(candidate, "Bridge.unrelated", self.folder / "checks", statement, source_library=self.payload)
        self.assertTrue(rejected["compilation_success"])
        self.assertFalse(rejected["success"])
        self.assertEqual(rejected["outcome"], "unrelated")
        self.assertEqual(rejected["source_usage"]["status"], "unrelated")
        helper = lean.verify_candidate(candidate, "Bridge.unrelated", self.folder / "checks", statement,
                                       source_library=self.payload, require_source_usage=False)
        self.assertTrue(helper["success"], json.dumps(helper, ensure_ascii=False, indent=2))
        self.assertFalse(helper["source_usage"]["required"])
        self.assertEqual(helper["source_library"]["audit"]["status"], "passed")

    def test_selected_type_is_checked_against_fresh_export(self):
        changed = copy.deepcopy(self.payload)
        changed["selected_declaration"]["type"] = "True"
        candidate = _candidate(changed, "theorem Bridge.result (n : Nat) : Imported.advance n = n + 1 := by rfl\n")
        result = lean.verify_candidate(candidate, "Bridge.result", self.folder / "checks",
                                       "∀ n : Nat, Imported.advance n = n + 1", source_library=changed)
        self.assertFalse(result["success"])
        self.assertIn("свежим экспортом", result["error"])

    def test_failed_real_input_cannot_be_selected(self):
        failed = self.store.create(dict(content="import Init\ntheorem Broken : (0 : Nat) = 1 := by rfl\n"))
        self.assertEqual(failed["status"], "failed")
        self.assertFalse(failed["inspection"]["success"])
        with self.assertRaises(ValueError):
            self.store.select(failed["source_id"], "Broken")


if __name__ == "__main__":
    unittest.main()
