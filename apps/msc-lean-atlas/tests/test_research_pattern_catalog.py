import hashlib
import json
from pathlib import Path
import sqlite3
import sys
import tempfile
import unittest
from unittest.mock import patch

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))
import lean_service
import research_pattern_catalog as catalog
import research_patterns
import research_retrieval


class CatalogTests(unittest.TestCase):
    def test_source_link_rejects_replaced_content_and_nonlibrary_paths(self):
        with tempfile.TemporaryDirectory() as folder:
            root = Path(folder)
            file = root / 'Mathlib' / 'Example.lean'
            file.parent.mkdir()
            file.write_text('theorem sample : True := trivial')
            digest = hashlib.sha256(file.read_bytes()).hexdigest()
            card = dict(file=str(file), module='Mathlib.Example', source_sha256=digest)
            index = root / 'library-index.sqlite'
            with sqlite3.connect(index) as db:
                db.execute('CREATE TABLE declarations(id,payload)')
                db.execute('INSERT INTO declarations VALUES(?,?)', ('lean:example',json.dumps(card)))
            with patch.object(research_retrieval,'INDEX_PATH',index), patch.object(lean_service,'default_context',return_value={'mathlib':str(root)}):
                self.assertEqual(catalog.read_source('example',digest),file.read_bytes())
                file.write_text('-- different source')
                with self.assertRaises(ValueError):
                    catalog.read_source('example',digest)
                with self.assertRaises(FileNotFoundError):
                    catalog.read_source('unknown',digest)
            self.assertIsNone(catalog._source_path(dict(card,file=str(root/'elsewhere.lean')),root))

    @unittest.skipUnless(research_retrieval.INDEX_PATH.is_file() and Path(lean_service.default_context()['lean']).is_file(),
                         'Requires the prepared Lean toolchain and local declaration index')
    def test_mathlib_fallback_uses_actual_types_and_rejects_missing_names(self):
        candidates = research_retrieval.search_library('convex', 12)
        self.assertTrue(candidates)
        missing = dict(candidates[0],name='AMRUnregisteredPatternClaim')
        with patch.object(research_retrieval,'search_library',return_value=[missing, *candidates]):
            found = catalog.find_theorems('convex',[],6)
        self.assertGreaterEqual(len(found),2)
        self.assertNotIn(missing['name'],[s['name'] for s in found])
        for source in found:
            self.assertEqual(source['kind'],'mathlib')
            self.assertFalse(source['statement'].startswith(('theorem ', 'lemma ')))
            self.assertFalse(set(source['axioms']) - lean_service.ALLOWED_AXIOMS)

    @unittest.skipUnless(research_retrieval.INDEX_PATH.is_file() and Path(lean_service.default_context()['lean']).is_file(),
                         'Requires the prepared Lean toolchain and local declaration index')
    def test_empty_archive_uses_msc_title_and_pins_resolved_modules(self):
        from types import SimpleNamespace
        with tempfile.TemporaryDirectory() as root:
            sources, env = research_patterns.snapshot(SimpleNamespace(root=root), '', ['90C25'], {}, [])
        self.assertGreaterEqual(len(sources), 2)
        self.assertTrue(all(s['kind']=='mathlib' and s['match']=='msc_title' for s in sources))
        self.assertEqual(set(env['imports']), {s['module'] for s in sources})
        self.assertEqual(len(set(s['id'] for s in sources)), len(sources))
