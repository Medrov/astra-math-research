import hashlib
import json
import os
from pathlib import Path
import shutil
import sys
import tempfile
import unittest
from unittest.mock import Mock

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))

import lean_service
import research_lean
import research_project_library as library
import research_published_example as published
from research_objects import GraphRegistry


EXPECTED_MODULES = ["MathResearch.MinimalAInfinity", "MathResearch.AlbertObstruction",
                    "MathResearch.AlbertMatrix", "MathResearch.AlbertSpectralGeometry"]


class PublishedExampleTests(unittest.TestCase):
    def test_published_adapters_keep_the_real_associator_and_exact_model(self):
        fixture = published.fixture()
        self.assertEqual(fixture["target"], "Bridge.energy_correspondence")
        self.assertEqual(fixture["agent_task"]["imports"], [library.ENTRY_POINT])
        self.assertEqual(library.pinned_fingerprint(published.source(), required=True), library.fingerprint())
        self.assertEqual(library.pinned_fingerprint(fixture["agent_task"]["prelude"], required=True), library.fingerprint())
        self.assertIn("associatorDirichlet d f", fixture["agent_task"]["prelude"])
        self.assertIn("graphLaplacian d f", fixture["agent_task"]["prelude"])
        self.assertNotIn("theorem ", lean_service._mask(fixture["agent_task"]["prelude"]))
        self.assertIn("exact MathResearch.AlbertSpectralGeometry.associatorDirichlet_graphLaplacian d f", published.source())
        self.assertEqual(fixture["semantic_review"]["novelty"], "published_proof_reuse")
        self.assertTrue(all(published.PUBLICATION_COMMIT in item["url"] for item in fixture["evidence"]))
        research_lean._validate_source(published.source())
        with self.assertRaises(ValueError):
            research_lean._validate_source("import MathResearch.MinimalAInfinity\n")

    def test_four_source_dependencies_and_one_public_entry_point(self):
        manifest = library.source_manifest()
        self.assertEqual([item["module"] for item in manifest["sources"]], EXPECTED_MODULES)
        self.assertEqual(library.allowed_imports(), frozenset({library.ENTRY_POINT}))
        self.assertEqual(manifest["fingerprint"], library.fingerprint())
        self.assertTrue(all(len(item["sha256"]) == 64 for item in manifest["sources"]))

    def test_source_pin_cannot_be_omitted_malformed_or_duplicated(self):
        self.assertIsNone(library.pinned_fingerprint("import Mathlib"))
        for source in ["import Mathlib", library.PIN_PREFIX + "bad", published.source() + library.PIN_PREFIX + "0" * 64]:
            with self.subTest(source=source[:60]), self.assertRaises(ValueError):
                library.pinned_fingerprint(source, required=True)

    def test_graph_registry_preserves_exact_published_task(self):
        with tempfile.TemporaryDirectory() as directory:
            registry = GraphRegistry(Path(directory) / "objects.sqlite")
            graph = registry.create(published.graph_for_published_example())
            transition = registry.get(graph["id"])["transitions"][0]
            fixture = published.fixture()
            self.assertEqual(transition["obligations"], published.obligations())
            self.assertEqual(transition["agent_task"]["prelude"], fixture["agent_task"]["prelude"])
            self.assertEqual(transition["relation_type"], "representation")


class LibrarySourcePinTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory(prefix="published-library-unit-")
        self.root = Path(self.temp.name) / "project"
        self.work = Path(self.temp.name) / "work"
        self.work.mkdir()
        for source in library.source_manifest()["sources"]:
            relative = source["path"]
            target = self.root / relative
            target.parent.mkdir(parents=True, exist_ok=True)
            shutil.copyfile(Path(lean_service.PROJECT_DEFAULT) / relative, target)
        self.context = dict(project_root=str(self.root), lean="not-invoked-by-stub", lean_search_paths=[
            str(self.work), str(self.root), str(self.root / ".lake/build/lib/lean"), str(self.root / ".lake/packages/mathlib/.lake/build/lib/lean")])
        self.env = {}

    def tearDown(self):
        self.temp.cleanup()

    def _stub_compile(self, relative):
        (self.work / relative).with_suffix(".olean").write_bytes(b"unit-test-output-not-a-real-olean")

    def test_changed_source_invalidates_expected_fingerprint_before_compilation(self):
        previous = library.fingerprint(self.root)
        changed = self.root / "MathResearch/MinimalAInfinity.lean"
        changed.write_bytes(changed.read_bytes() + b"\n-- changed source pin\n")
        self.assertNotEqual(previous, library.fingerprint(self.root))
        runner = Mock()
        with self.assertRaisesRegex(ValueError, "fingerprint changed"):
            library.prepare_library(self.context, self.env, self.work, runner, expected_fingerprint=previous)
        runner.assert_not_called()

    def test_source_edit_during_build_is_rejected(self):
        def runner(relative):
            self._stub_compile(relative)
            if relative.endswith("AlbertSpectralGeometry.lean"):
                changed = self.root / relative
                changed.write_bytes(changed.read_bytes() + b"\n-- changed during build\n")
        with self.assertRaisesRegex(ValueError, "changed during compilation"):
            library.prepare_library(self.context, self.env, self.work, runner)
        manifest = json.loads((self.work / "project-library.json").read_text(encoding="utf-8"))
        self.assertEqual(manifest["status"], "failed")

    def test_shared_project_caches_are_removed_and_preexisting_run_cache_rejected(self):
        target = self.work / "MathResearch/MinimalAInfinity.olean"
        target.parent.mkdir()
        target.write_bytes(b"stale output")
        runner = Mock()
        with self.assertRaisesRegex(ValueError, "pre-existing"):
            library.prepare_library(self.context, self.env, self.work, runner)
        runner.assert_not_called()
        paths = self.env["LEAN_PATH"].split(os.pathsep)
        self.assertNotIn(str(self.root.resolve()), paths)
        self.assertNotIn(str((self.root / ".lake/build/lib/lean").resolve()), paths)
        self.assertEqual(paths[0], str(self.work.resolve()))


@unittest.skipUnless(Path(lean_service.default_context()["lean"]).is_file(), "Prepared Lean unavailable")
class RealPublishedLeanTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.temp = tempfile.TemporaryDirectory(prefix="published-library-lean-")
        cls.work = Path(cls.temp.name)
        cls.context, cls.env = lean_service._prepare({}, cls.work)
        cls.diagnostics = []
        cls.runner = lambda relative: research_lean._run(cls.context, cls.env, cls.work, relative, cls.diagnostics)
        cls.manifest = library.prepare_library(cls.context, cls.env, cls.work, cls.runner,
                                               expected_fingerprint=library.pinned_fingerprint(published.source(), required=True))
        (cls.work / "Candidate.lean").write_text(published.source(), encoding="utf-8")
        cls.runner("Candidate.lean")
        cls.exported = research_lean._export(cls.context, cls.env, cls.work, cls.diagnostics, None)
        cls.audit = research_lean._audit_declarations(cls.exported["declarations"], published.source(), published.TARGET)
        (cls.work / "Contract.lean").write_text("import Candidate\nset_option autoImplicit false\nexample : (" +
                                               published.STATEMENT + ") := @" + published.TARGET + "\n", encoding="utf-8")
        cls.runner("Contract.lean")
        (cls.work / "PrintAxioms.lean").write_text("import Candidate\n#print axioms Bridge.energy_correspondence\n", encoding="utf-8")
        cls.runner("PrintAxioms.lean")

    @classmethod
    def tearDownClass(cls):
        cls.temp.cleanup()

    def test_fresh_closure_candidate_contract_and_axioms(self):
        self.assertEqual(self.manifest["status"], "complete")
        self.assertEqual([source["module"] for source in self.manifest["sources"]], EXPECTED_MODULES)
        self.assertTrue(all(item["exit_code"] == 0 for item in self.diagnostics))
        self.assertEqual(self.audit["unexpected_axioms"], [])
        self.assertEqual(self.audit["unsafe_declarations"], [])
        declaration = next(d for d in self.exported["declarations"] if d["name"] == published.TARGET)
        self.assertTrue(set(declaration["axioms"]) <= lean_service.ALLOWED_AXIOMS)
        self.assertIn("MathResearch.AlbertSpectralGeometry.associatorDirichlet_graphLaplacian", declaration["dependencies"])
        self.assertIn("AlgebraObject.energy", declaration["type_dependencies"])
        self.assertIn("GraphObject.energy", declaration["type_dependencies"])
        for item in self.manifest["sources"]:
            source = self.work / item["path"]
            self.assertEqual(hashlib.sha256(source.read_bytes()).hexdigest(), item["sha256"])
            self.assertEqual(hashlib.sha256(source.with_suffix(".olean").read_bytes()).hexdigest(), item["olean_sha256"])
        self.assertIn("Bridge.energy_correspondence", self.diagnostics[-1]["stdout"])


if __name__ == "__main__":
    unittest.main()
