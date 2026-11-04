"""An exact Lean name must survive highly ranked lexical distractors."""
from pathlib import Path
import sys
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))
import research_retrieval as retrieval


class ExactLibraryNames(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.root = Path(self.temp.name)
        self.sources = self.root / 'Mathlib'
        self.sources.mkdir()
        self.index = self.root / 'index.sqlite'
        source = 'theorem add_pow (n : Nat) : n = n := by rfl\n'
        source += '\n'.join(f'theorem add_pow_add_pow_variant{i} (n : Nat) : n = n := by rfl' for i in range(30))
        source += '\nnamespace Commute\ntheorem add_pow : True := by trivial\nend Commute\n'
        source += "\nnamespace MvPolynomial\ntheorem eval₂Hom_C : True := by trivial\ntheorem eval₂Hom_X' : True := by trivial\nend MvPolynomial\n"
        (self.sources / 'Primary.lean').write_text(source, encoding='utf-8')
        (self.sources / 'Duplicate.lean').write_text('theorem ambiguous_name : True := by trivial\n')
        (self.sources / 'Other.lean').write_text('theorem ambiguous_name : True := by trivial\n')
        retrieval.build_index(self.index, [dict(path=str(self.sources), repository=str(self.root), module_prefix='Mathlib')])

    def tearDown(self):
        self.temp.cleanup()

    def test_exact_name_is_not_lost_beyond_fts_window(self):
        rows = retrieval.lookup_library_name('add_pow', limit=16, index_path=self.index)
        self.assertEqual([row['name'] for row in rows], ['add_pow'])
        ranked = retrieval.search_library('add_pow', limit=16, index_path=self.index)
        self.assertEqual([row['name'] for row in ranked], ['add_pow'])
        self.assertEqual(ranked[0]['retrieval_backend'], 'library_exact_name')

    def test_namespace_case_and_ambiguity_are_preserved(self):
        self.assertEqual([row['name'] for row in retrieval.lookup_library_name('Commute.add_pow', index_path=self.index)], ['Commute.add_pow'])
        self.assertEqual(retrieval.lookup_library_name('Add_pow', index_path=self.index), [])
        rows = retrieval.lookup_library_name('ambiguous_name', index_path=self.index)
        self.assertEqual({row['module'] for row in rows}, {'Mathlib.Duplicate', 'Mathlib.Other'})
        self.assertEqual(retrieval.lookup_library_name("add_pow' OR 1=1 --", index_path=self.index), [])

    def test_missing_name_does_not_return_similar_names(self):
        self.assertEqual(retrieval.lookup_library_name('missing_add_pow', index_path=self.index), [])
        self.assertTrue(retrieval.search_library('binomial add power', index_path=self.index))

    def test_unicode_exact_names_keep_primes_and_reject_injection(self):
        for name in ('MvPolynomial.eval₂Hom_C', "MvPolynomial.eval₂Hom_X'"):
            rows = retrieval.lookup_library_name(name, index_path=self.index)
            self.assertEqual([row['name'] for row in rows], [name])
            ranked = retrieval.search_library(name, index_path=self.index)
            self.assertEqual([row['name'] for row in ranked], [name])
            self.assertEqual(ranked[0]['retrieval_backend'], 'library_exact_name')
        for missing in ('MvPolynomial.eval₂Hom_X', 'MvPolynomial.eval2Hom_C'):
            self.assertEqual(retrieval.lookup_library_name(missing, index_path=self.index), [])
        for malicious in ('MvPolynomial.eval₂Hom_C\n#eval IO.println "bad"',
                          "MvPolynomial.eval₂Hom_C' OR 1=1 --", 'MvPolynomial..eval₂Hom_C'):
            self.assertEqual(retrieval.lookup_library_name(malicious, index_path=self.index), [])


if __name__ == '__main__':
    unittest.main()
