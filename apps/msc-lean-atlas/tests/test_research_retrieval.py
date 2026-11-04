from pathlib import Path
import sys
import tempfile
import unittest
from unittest.mock import patch
import hashlib

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))
import research_retrieval as retrieval


class DeclarationExtractionTests(unittest.TestCase):
    def test_compound_end_closes_all_named_scopes_without_fabricating_namespace(self):
        source='namespace Topology\nsection Q\nnamespace Q\ntheorem first : True := by trivial\nend Q\nend Topology.Q\nnamespace Topology\ntheorem second : True := by trivial\nend Topology\n'
        rows=list(retrieval.extract_declarations(source,'Demo','demo','hash'))
        self.assertEqual([r['name'] for r in rows],['Topology.Q.first','Topology.second'])

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

    def test_type_channel_is_not_claimed_as_compiler_verified(self):
        self.source.write_text('namespace F\ntheorem transfer (f : Function.Semiconj a b c) : True := by trivial\nend F\n')
        retrieval.build_index(self.index,self.roots)
        results=retrieval.search_library_types('Function.Semiconj f g h',index_path=self.index)
        self.assertEqual(results[0]['name'],'F.transfer')
        self.assertEqual(results[0]['type_status'],'textual_unverified')
        self.assertNotIn('elaborated_type',results[0])
        pool=retrieval.hybrid_pool(['unmatchedword'],{'objects':[]},'Function.Semiconj f g h',index_path=self.index)
        self.assertEqual(pool[0]['retrieval_channels'],['textual_type_signature'])
        self.assertEqual(pool[0]['type_status'],'textual_unverified')

    def test_vocabulary_expansion_is_transparent_and_deduplicated(self):
        self.source.write_text('namespace Function\ntheorem semiconj : True := by trivial\nend Function\n')
        retrieval.build_index(self.index,self.roots)
        pool=retrieval.hybrid_pool(['conjugacy','conjugacy'],{'objects':[]},'',index_path=self.index)
        self.assertEqual(len(pool),1)
        self.assertIn('vocabulary_expansion',pool[0]['retrieval_channels'])
        self.assertNotIn('semantic_assessment',pool[0])

    def test_type_resolution_requires_current_source_and_compiler_evidence(self):
        retrieval.build_index(self.index,self.roots)
        hit=retrieval.search_library('sum_eq_zero',index_path=self.index)[0]
        with patch('research_lean._export',side_effect=AssertionError('stale source must not reach compiler')):
            bad=dict(hit,source_sha256='0'*64)
            result=retrieval.resolve_library_types([bad],self.folder/'resolution')
        self.assertEqual(result[0]['type_status'],'stale')
        self.assertNotIn('elaborated_type',result[0])
        with patch('lean_service._prepare',side_effect=ValueError('compiler unavailable')):
            result=retrieval.resolve_library_types([hit],self.folder/'missing-compiler')
        self.assertEqual(result[0]['type_status'],'not_resolved')
        self.assertNotIn('elaborated_type',result[0])


@unittest.skipUnless(Path(retrieval.lean_service.default_context()['lean']).is_file(),'Prepared Lean unavailable')
class RealTypeResolution(unittest.TestCase):
    def test_selected_mathlib_name_is_resolved_with_complete_type(self):
        context=retrieval.lean_service.default_context()
        source=Path(context['mathlib'])/'Mathlib/Logic/Function/Iterate.lean'
        raw=source.read_bytes()
        rows=list(retrieval.extract_declarations(raw.decode('utf-8'),'Mathlib.Logic.Function.Iterate',str(source),hashlib.sha256(raw).hexdigest()))
        hit=next(row for row in rows if row['name']=='Function.Semiconj.iterate_right')
        with tempfile.TemporaryDirectory(prefix='retrieval-real-type-') as directory:
            resolved=retrieval.resolve_library_types([hit],directory,timeout_seconds=60)[0]
        self.assertEqual(resolved['type_status'],'compiler_resolved',resolved.get('type_resolution_reason'))
        self.assertIn('Semiconj',resolved['elaborated_type'])
        self.assertEqual(resolved['resolved_imports'],['Mathlib.Logic.Function.Iterate'])
        self.assertEqual(resolved['verification_scope'],'existing_library_type_only')
        self.assertTrue(resolved['requires_new_proof'])


if __name__ == '__main__':
    unittest.main()
