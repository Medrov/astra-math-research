"""Portable demo boundaries: no research/corpus seed, no model calls."""
import copy
import hashlib
import json
from pathlib import Path
import sys
import tempfile
import unittest
from unittest.mock import Mock, patch

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))
import lean_service
import research_fibonacci_example as demo
import research_lean
import research_retrieval
import research_structure
from research_structure_sources import StructureSourceStore


def report_for(content, contract):
    return dict(status='complete', success=True, compilation_success=True,
        target_preserved=True, obligations_passed=True, audit={'status':'passed'},
        source_sha256=demo._sha(content), target=contract['target'], expected_statement=contract['statement'],
        obligations=[dict(id=goal['id'], target=goal['target'], ok=True,
                          statement_sha256=demo._sha(goal['statement']))
                     for goal in contract['required_obligations']])


class FibonacciDemoBoundaries(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.content, self.contract, self.provenance = demo.load()
        self.store = Mock(root=Path(self.temp.name))
        self.source = dict(source_id='d'*32, status='ready', source_sha256=demo._sha(self.content),
                           inspection=dict(status='complete', success=True))
        self.store.create.side_effect = lambda payload: dict(self.source, provenance=payload['provenance'])
        self.service = research_structure.StructureResearchMixin()
        self.service.structure_store = lambda: self.store

    def test_catalog_is_metadata_only_and_demo_stays_outside_all_cases_and_default_index_roots(self):
        self.store.list_sources.return_value = []
        with patch.object(research_lean, 'verify_candidate', side_effect=AssertionError('metadata must not compile')):
            examples = self.service.structure_sources()['examples']
        entry = next(row for row in examples if row['id'] == demo.EXAMPLE_ID)
        self.assertEqual(entry['recommended_target'], demo.TARGET)
        self.assertEqual(entry['required_obligation_count'], 4)
        self.assertEqual(entry['verification_kind'], 'exact_demo_contract')
        self.assertNotIn('content', entry)
        self.assertNotIn('inspection', entry)
        self.assertNotIn(demo.EXAMPLE_ID, [case['id'] for case in research_lean.fixtures()])
        documents = json.dumps(research_retrieval.documents(research_lean.fixtures()), ensure_ascii=False)
        self.assertNotIn(demo.TARGET, documents)
        self.assertNotIn(demo.EXAMPLE_ID, documents)
        self.assertTrue(all(not demo.PACKAGE.resolve().is_relative_to(Path(root['path']).resolve())
                            for root in research_retrieval._default_roots()))

    def test_import_ignores_browser_proof_and_uses_every_exact_obligation_without_model(self):
        expected = report_for(self.content, self.contract)
        with patch('research_codex.run_task', side_effect=AssertionError('No models')), \
             patch.object(research_lean, 'verify_candidate', return_value=expected) as verify:
            result = self.service.import_structure_source(dict(example_id=demo.EXAMPLE_ID,
                content='import Evil', contract={'target':'Other.fake'}, prepared_example_id='forged'))
        args, kwargs = verify.call_args
        self.assertEqual(args, (self.content, demo.TARGET,
            self.store.root / self.source['source_id'] / 'demo-verification', self.contract['statement']))
        self.assertEqual(kwargs, {'required_obligations':self.contract['required_obligations']})
        self.assertEqual(self.store.create.call_args.args[0]['content'], self.content)
        self.store.create_prepared.assert_not_called()
        check = result['demo_verification']
        self.assertTrue(check['verified'])
        self.assertTrue(check['fresh_local_check'])
        self.assertEqual(check['model_calls'], 0)
        self.assertEqual(check['source_application_status'], 'not_verified')
        self.assertEqual(check['msc'], [dict(code='15A63', origin='reviewer_inferred', source_verified=False)])
        self.assertNotIn('demo_verification', self.source)

    def test_inspection_alone_never_confirms_four_obligations(self):
        clean = report_for(self.content, self.contract)
        variants = [dict(clean, success=False), dict(clean, obligations=clean['obligations'][:3]),
                    dict(clean, target='Other.target'), dict(clean, source_sha256='0'*64),
                    dict(clean, expected_statement='True'), dict(clean, audit={'status':'failed'})]
        wrong = copy.deepcopy(clean)
        wrong['obligations'][0]['statement_sha256'] = '0'*64
        variants.append(wrong)
        duplicate = copy.deepcopy(clean)
        duplicate['obligations'][0] = duplicate['obligations'][1]
        variants.append(duplicate)
        for report in variants:
            with self.subTest(report=report), patch.object(research_lean, 'verify_candidate', return_value=report):
                result = demo.import_source(self.store)
                self.assertFalse(result['demo_verification']['verified'])
                self.assertEqual(result['status'], 'ready')  # separately inspected Lean source

    def test_bad_source_inspection_stops_before_independent_check(self):
        self.source.update(status='failed', inspection={'success':False})
        with patch.object(research_lean, 'verify_candidate') as verify:
            result = demo.import_source(self.store)
        verify.assert_not_called()
        self.assertNotIn('demo_verification', result)

    def test_changed_canonical_bytes_fail_before_source_creation(self):
        package = Path(self.temp.name) / 'package'
        package.mkdir()
        for name in ('Candidate.lean', 'contract.json', 'provenance.json'):
            (package / name).write_bytes((demo.PACKAGE / name).read_bytes())
        for filename in ('Candidate.lean', 'contract.json'):
            original = (package / filename).read_bytes()
            (package / filename).write_bytes(original + b'\n')
            with patch.object(demo, 'PACKAGE', package), self.assertRaisesRegex(ValueError, 'изменилось'):
                demo.import_source(self.store)
            (package / filename).write_bytes(original)
        self.store.create.assert_not_called()


@unittest.skipUnless(Path(lean_service.default_context()['lean']).is_file(), 'Prepared Lean unavailable')
class FibonacciDemoRealLean(unittest.TestCase):
    def test_fresh_empty_store_checks_the_exact_four_obligations_without_research_data_or_model(self):
        with tempfile.TemporaryDirectory(prefix='fibonacci-demo-') as directory, \
             patch('research_codex.run_task', side_effect=AssertionError('No model calls')):
            store = StructureSourceStore(directory, 'demo-test-environment')
            result = demo.import_source(store)
            self.assertEqual(result['status'], 'ready', json.dumps(result, ensure_ascii=False))
            self.assertEqual(result['source_sha256'], demo.metadata()['source_sha256'])
            self.assertEqual(result['source_sha256'], demo._sha(result['content']))
            view = result['demo_verification']
            self.assertTrue(view['verified'], json.dumps(view, ensure_ascii=False))
            self.assertEqual(len(view['verification']['obligations']), 4)
            self.assertTrue(all(row['ok'] for row in view['verification']['obligations']))
            self.assertEqual(view['verification']['audit']['status'], 'passed')
            self.assertEqual(view['source_application_status'], 'not_verified')
            self.assertEqual(view['model_calls'], 0)
            # A normal source GET retains its immutable snapshot and does not turn
            # a historical inspection into a fresh independent contract check.
            self.assertNotIn('demo_verification', store.get(result['source_id']))
            self.assertEqual(len(list(Path(directory).glob('*/demo-verification/lean-*/verification.json'))), 1)


if __name__ == '__main__':
    unittest.main()
