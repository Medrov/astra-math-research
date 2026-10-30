from pathlib import Path
import sys
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))
import research_retrieval as retrieval


class DeclarationExtractionTests(unittest.TestCase):
    def test_noncomputable_section_and_attribute_assignment(self):
        source = '''namespace F
noncomputable section
/-- Useful doc. -/
@[simp]
theorem one : True := by trivial
end
@[to_additive (attr := simp)] theorem two : True := by trivial
end F
'''
        rows = list(retrieval.extract_declarations(source, 'D', '/tmp/D.lean', 'x'))
        self.assertEqual([r['name'] for r in rows], ['F.one', 'F.two'])
        self.assertIn('Useful doc.', rows[0]['doc_comment'])
        self.assertEqual(rows[1]['statement'], 'theorem two : True')

    def test_headers_namespaces_and_docs_without_proofs(self):
        source = '''namespace Finset
section Basic
/-- The sum is zero when each summand is zero. -/
@[simp] theorem sum_eq_zero (x : Nat) : x = x := by
  -- HIDDEN_PROOF_SECRET
  exact rfl
end Basic
def identity (x : Nat) : Nat := x + 1234567
end Finset
theorem outside : True := by trivial
'''
        rows = list(retrieval.extract_declarations(source, 'Demo', '/tmp/Demo.lean', 'hash'))
        self.assertEqual([r['name'] for r in rows], ['Finset.sum_eq_zero', 'Finset.identity', 'outside'])
        self.assertIn('summand', rows[0]['doc_comment'])
        self.assertNotIn('exact rfl', str(rows))
        self.assertNotIn('1234567', str(rows))
        self.assertNotIn('HIDDEN_PROOF_SECRET', str(rows))
        self.assertTrue(all(r['extraction'] == 'textual_unverified' for r in rows))
        self.assertEqual(rows[0]['line'], 4)

    def test_equation_body_and_comment_declarations_are_excluded(self):
        source = '''/- theorem bogus : False := by sorry -/
def ident | n => n
structure Item where
  value : Nat
'''
        rows = list(retrieval.extract_declarations(source, 'D', '/tmp/D.lean', 'x'))
        self.assertEqual([r['name'] for r in rows], ['ident', 'Item'])
        self.assertNotIn('=>', rows[0]['statement'])
        self.assertNotIn('value', rows[1]['statement'])


class IncrementalIndexTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory(prefix='research-source-index-')
        self.folder = Path(self.temp.name)
        self.sources = self.folder / 'Mathlib'
        self.sources.mkdir()
        self.index = self.folder / 'index.sqlite'
        self.roots = [dict(path=str(self.sources), repository=str(self.folder), module_prefix='Mathlib', name='test')]
        (self.folder / 'lean-toolchain').write_text('leanprover/lean4:v4.19.0\n')
        self.source = self.sources / 'Demo.lean'
        self.source.write_text('namespace Finset\n/-- A sum theorem. -/\ntheorem sum_eq_zero : True := by trivial\nend Finset\n'
                               '/-- Graph energy and laplacian. -/\ndef graphEnergy : Nat := 3\n')

    def tearDown(self):
        self.temp.cleanup()

    def test_incremental_hash_and_removal(self):
        first = retrieval.build_index(self.index, self.roots)
        self.assertEqual(first['declarations'], 2)
        self.assertEqual(first['changed_files'], 1)
        second = retrieval.build_index(self.index, self.roots)
        self.assertEqual(second['changed_files'], 0)
        self.assertEqual(second['unchanged_files'], 1)
        self.assertEqual(first['source_sha256'], second['source_sha256'])
        self.source.write_text('theorem replacement : True := by trivial\n')
        third = retrieval.build_index(self.index, self.roots)
        self.assertEqual(third['declarations'], 1)
        self.assertNotEqual(first['source_sha256'], third['source_sha256'])
        self.assertFalse(retrieval.search_library('sum_eq_zero', index_path=self.index))
        self.source.unlink()
        fourth = retrieval.build_index(self.index, self.roots)
        self.assertEqual(fourth['declarations'], 0)
        self.assertEqual(fourth['files'], 0)

    def test_symbol_tokens_and_russian_alias(self):
        retrieval.build_index(self.index, self.roots)
        rows = retrieval.search_library('Finset sum_eq_zero', index_path=self.index)
        self.assertEqual(rows[0]['name'], 'Finset.sum_eq_zero')
        self.assertIn('Mathlib.Demo', rows[0]['module'])
        self.assertEqual(rows[0]['proof_status'], 'not_checked')
        graph = retrieval.search_library('граф энергия', index_path=self.index)
        self.assertEqual(graph[0]['name'], 'graphEnergy')
        self.assertEqual(retrieval.library_manifest(self.index)['sources'][0]['lean_toolchain'], 'leanprover/lean4:v4.19.0')

    def test_search_never_builds_missing_index(self):
        self.assertEqual(retrieval.search_library('x', index_path=self.index), [])
        self.assertFalse(self.index.exists())


if __name__ == '__main__':
    unittest.main()
