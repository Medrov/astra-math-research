"""Selected library names must be resolved by Lean, not guessed from headers."""
import hashlib
import json
from pathlib import Path
import sys
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))
import lean_service
import research_lean
import research_retrieval as retrieval


@unittest.skipUnless(Path(lean_service.default_context()['lean']).is_file(), 'Prepared Lean unavailable')
class TargetedLibraryExport(unittest.TestCase):
    def test_real_unicode_names_and_prime_resolve_without_aliases(self):
        context = lean_service.default_context()
        module = 'Mathlib.Algebra.MvPolynomial.Eval'
        source = Path(context['mathlib']) / 'Mathlib/Algebra/MvPolynomial/Eval.lean'
        raw = source.read_bytes()
        records = list(retrieval.extract_declarations(raw.decode('utf-8'), module,
            str(source), hashlib.sha256(raw).hexdigest()))
        names = ['MvPolynomial.eval₂Hom_C', "MvPolynomial.eval₂Hom_X'"]
        hits = [next(row for row in records if row['name'] == name) for name in names]
        with tempfile.TemporaryDirectory(prefix='atlas-unicode-retrieval-') as directory:
            rows = retrieval.resolve_library_types(hits + [
                dict(hits[1], name='MvPolynomial.eval₂Hom_X'),
                dict(hits[0], name='MvPolynomial.eval₂Hom_C\n#eval IO.println "bad"'),
            ], directory, timeout_seconds=60)
            report = json.loads((Path(directory) / 'type-resolution.json').read_text(encoding='utf-8'))
        for name, row in zip(names, rows):
            self.assertEqual(row['name'], name)
            self.assertEqual(row['type_status'], 'compiler_resolved', row)
            self.assertEqual(row['resolved_imports'], [module])
            self.assertFalse(set(row['axioms']) - lean_service.ALLOWED_AXIOMS)
            self.assertEqual(row['verification_scope'], 'existing_library_type_only')
            self.assertTrue(row['requires_new_proof'])
        self.assertEqual(rows[2]['type_status'], 'not_found')
        self.assertEqual(rows[3]['type_status'], 'not_resolved')
        self.assertEqual(report['model_calls'], 0)
        self.assertEqual(report['status'], 'complete')

    def test_requested_names_only_with_missing_name_and_full_type_audit(self):
        with tempfile.TemporaryDirectory(prefix='atlas-targeted-export-') as directory:
            work = Path(directory)
            context, env = lean_service._prepare({}, work)
            diagnostics = []
            result = research_lean._export(context, env, work, diagnostics, None,
                modules=['Mathlib.Data.Nat.Choose.Sum'],
                names=['add_pow', 'Commute.add_pow', 'AtlasMissingLibraryConstant', 'add_pow'])
            self.assertEqual({d['name'] for d in result['declarations']}, {'add_pow', 'Commute.add_pow'})
            self.assertEqual(len(result['declarations']), 2)
            self.assertEqual(result['missing_names'], ['AtlasMissingLibraryConstant'])
            self.assertIn('Mathlib.Data.Nat.Choose.Sum', result['imported_modules'])
            for declaration in result['declarations']:
                self.assertEqual(declaration['module'], 'Mathlib.Data.Nat.Choose.Sum')
                self.assertIn('choose', declaration['type'])
                self.assertFalse(declaration['unsafe'])
                self.assertFalse(set(declaration['axioms']) - lean_service.ALLOWED_AXIOMS)
                self.assertFalse(declaration['dependency_walk_truncated'])
            self.assertTrue(diagnostics)
            self.assertTrue(all(row['exit_code'] == 0 for row in diagnostics))

    def test_retrieval_checks_exact_module_and_does_not_promote_missing_symbol(self):
        context = lean_service.default_context()
        source = Path(context['mathlib']) / 'Mathlib/Data/Nat/Choose/Sum.lean'
        raw = source.read_bytes()
        records = list(retrieval.extract_declarations(raw.decode('utf-8'),
            'Mathlib.Data.Nat.Choose.Sum', str(source), hashlib.sha256(raw).hexdigest()))
        hit = next(row for row in records if row['name'] == 'add_pow')
        with tempfile.TemporaryDirectory(prefix='atlas-targeted-retrieval-') as directory:
            rows = retrieval.resolve_library_types([
                hit, dict(hit, name='AtlasMissingLibraryConstant'),
                dict(hit, name='add_pow\n#eval IO.println "bad"'),
                dict(hit, module='Mathlib.Data.Nat.Choose.Basic'),
            ], directory, timeout_seconds=60)
            report = json.loads((Path(directory) / 'type-resolution.json').read_text(encoding='utf-8'))
        self.assertEqual(rows[0]['type_status'], 'compiler_resolved', rows[0])
        self.assertEqual(rows[0]['resolved_imports'], ['Mathlib.Data.Nat.Choose.Sum'])
        self.assertTrue(rows[0]['requires_new_proof'])
        self.assertEqual(rows[1]['type_status'], 'not_found')
        self.assertEqual(rows[2]['type_status'], 'not_resolved')
        self.assertEqual(rows[3]['type_status'], 'not_found')
        self.assertNotIn('elaborated_type', rows[1])
        self.assertEqual(report['model_calls'], 0)
        self.assertEqual(report['status'], 'complete')


if __name__ == '__main__':
    unittest.main()
