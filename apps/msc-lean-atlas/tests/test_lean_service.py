import importlib.util
import json
from pathlib import Path
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[1]
spec = importlib.util.spec_from_file_location('lean_service', ROOT / 'lean_service.py')
service = importlib.util.module_from_spec(spec)
spec.loader.exec_module(service)


class SyntaxTests(unittest.TestCase):
    def test_comments_strings_and_nested_comments_are_not_proofs(self):
        source = '/- sorry /- axiom nested -/ still comment -/\n-- admit\ndef value := "sorry"\ntheorem actual : True := by trivial\n'
        clean = service._mask(source)
        self.assertNotIn('sorry', clean)
        self.assertNotIn('axiom', clean)
        self.assertEqual(clean.count('\n'), source.count('\n'))
        self.assertEqual([d['name'] for d in service.lexical_declarations(source)], ['value', 'actual'])

    def test_filename_traversal_is_rejected(self):
        with self.assertRaises(ValueError):
            service._validate_files([{'name':'../Escape.lean','content':''},{'name':'B.lean','content':''}])

    def test_internal_imports_are_topologically_ordered(self):
        files = service._validate_files([{'name':'A.lean','content':'import B\ndef a := b'}, {'name':'B.lean','content':'def b := 1'}])
        self.assertEqual([f['name'] for f in service._order(files)], ['B.lean', 'A.lean'])


@unittest.skipUnless(Path(service.default_context()['lean']).is_file(), 'Prepared Lean unavailable')
class LiveLeanTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.temp = tempfile.TemporaryDirectory(prefix='atlas-lean-test-')
        cls.directory = Path(cls.temp.name)
        cls.context = {**service.default_context(), 'mathlib':'', 'project_root':'', 'timeout_seconds':120}
        cls.files = [
            {'name':'FirstObject.lean','content':'namespace FirstObject\ndef value : Nat := 2\nend FirstObject\n'},
            {'name':'SecondObject.lean','content':'namespace SecondObject\ndef value : Nat := 3\nend SecondObject\n'},
        ]
        cls.inspection = service.inspect_files(cls.files, cls.context, cls.directory)
        if not cls.inspection['semantic_extraction']:
            raise AssertionError(json.dumps(cls.inspection, ensure_ascii=False))

    @classmethod
    def tearDownClass(cls):
        cls.temp.cleanup()

    def test_compiler_extraction_has_resolved_names_types_and_dependencies(self):
        self.assertEqual(self.inspection['status'], 'complete')
        names = [d['name'] for f in self.inspection['files'] for d in f['declarations']]
        self.assertIn('FirstObject.value', names)
        self.assertIn('SecondObject.value', names)
        d = self.inspection['files'][0]['declarations'][0]
        self.assertEqual(d['type'], 'Nat')
        self.assertIn('Nat', d['dependencies'])
        self.assertEqual(d['extraction'], 'lean_environment')

    def test_bridge_is_fresh_and_false_replacement_is_not_stale_success(self):
        source = 'import FirstObject\nimport SecondObject\nnamespace Bridge\ntheorem sum : FirstObject.value + SecondObject.value = 5 := by rfl\nend Bridge\n'
        good = service.verify_bridge(source, ['Bridge.sum'], self.context, self.directory, self.inspection)
        self.assertTrue(good['success'], good)
        self.assertEqual(good['status'], 'verified')
        self.assertTrue(good['target_results'][0]['both_inputs_participate'])
        bad = service.verify_bridge(source.replace('= 5', '= 6'), ['Bridge.sum'], self.context, self.directory, self.inspection)
        self.assertFalse(bad['success'])
        self.assertNotEqual(good['workspace'], bad['workspace'])
        self.assertNotEqual(good['source_sha256'], bad['source_sha256'])

    def test_imports_alone_are_not_a_bridge(self):
        source = 'import FirstObject\nimport SecondObject\nnamespace Bridge\ntheorem unrelated : (1 : Nat) = 1 := by rfl\nend Bridge\n'
        result = service.verify_bridge(source, ['Bridge.unrelated'], self.context, self.directory, self.inspection)
        self.assertFalse(result['success'])
        self.assertTrue(result['lean_compilation_success'])
        self.assertEqual(result['status'], 'unrelated')

    def test_selected_object_is_required_not_another_helper_in_same_file(self):
        files = [dict(f) for f in self.files]
        files[0]['content'] = 'namespace FirstObject\ndef value : Nat := 2\ndef other : Nat := 7\nend FirstObject\n'
        inspection = service.inspect_files(files, self.context, self.directory)
        inspection['selected_targets'] = ['FirstObject.value', 'SecondObject.value']
        source = 'import FirstObject\nimport SecondObject\nnamespace Bridge\ntheorem wrong_pair : FirstObject.other + SecondObject.value = 10 := by rfl\nend Bridge\n'
        result = service.verify_bridge(source, ['Bridge.wrong_pair'], self.context, self.directory, inspection)
        self.assertTrue(result['lean_compilation_success'])
        self.assertFalse(result['success'])
        self.assertEqual(result['status'], 'unrelated')
        coverage = result['target_results'][0]['selected_target_coverage']
        self.assertFalse(coverage['FirstObject.value'])
        self.assertTrue(coverage['SecondObject.value'])

    def test_sorry_is_rejected_before_success(self):
        source = 'import FirstObject\nimport SecondObject\ntheorem bad : FirstObject.value = SecondObject.value := by sorry\n'
        result = service.verify_bridge(source, ['bad'], self.context, self.directory, self.inspection)
        self.assertFalse(result['success'])
        self.assertEqual(result['status'], 'rejected')

    def test_imported_extra_axiom_is_rejected(self):
        files = [dict(f) for f in self.files]
        files[0]['content'] = 'namespace FirstObject\naxiom bogus : False\ndef value : Nat := 2\nend FirstObject\n'
        inspection = service.inspect_files(files, self.context, self.directory)
        self.assertEqual(inspection['status'], 'compiled_untrusted')
        source = 'import FirstObject\nimport SecondObject\ntheorem bad : FirstObject.value = SecondObject.value := False.elim FirstObject.bogus\n'
        result = service.verify_bridge(source, ['bad'], self.context, self.directory, inspection)
        self.assertFalse(result['success'])
        self.assertEqual(result['status'], 'rejected')
        self.assertIn('FirstObject.bogus', result['error'])

    def test_modified_input_invalidates_verification(self):
        inspection = service.inspect_files(self.files, self.context, self.directory)
        path = Path(inspection['files'][0]['source_path'])
        path.write_text(path.read_text() + '\n-- changed\n')
        result = service.verify_bridge('theorem harmless : True := by trivial', ['harmless'], self.context, self.directory, inspection)
        self.assertFalse(result['success'])
        self.assertIn('изменился после анализа', result['error'])


if __name__ == '__main__':
    unittest.main()
