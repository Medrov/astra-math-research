import copy
from pathlib import Path
import sys
import tempfile
import time
import unittest
from unittest.mock import patch, Mock

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))
from research_cards import validate_grounding, source_card
from research_service import ResearchService


class GroundingTests(unittest.TestCase):
    def test_quote_must_actually_be_in_retained_source(self):
        row = dict(component='conclusion', source_ref='s1', quote='the preserved invariant', origin='source_excerpt')
        self.assertEqual(validate_grounding([row], {'s1'}, {'s1':dict(content='Here is the preserved invariant.')}), [row])
        with self.assertRaises(ValueError):
            validate_grounding([row], {'s1'}, {'s1':dict(content='An unrelated statement')} )

    def test_model_inference_cannot_be_labeled_a_quote(self):
        with self.assertRaises(ValueError):
            validate_grounding([dict(component='conclusion', source_ref='s1', quote='fiction', origin='proposed_abstraction')], {'s1'})


class VersionTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.svc = ResearchService(self.temp.name, recover=False)
        self.run = self.svc.create(dict(mode='single', case_id='graph_energy', budget={'max_calls':16,'timeout_seconds':900}), start=False)
        self.svc.update(self.run['id'], status='failed')

    def tearDown(self):
        self.svc.pool.shutdown(wait=True)
        self.temp.cleanup()

    def test_correction_is_unstarted_and_does_not_change_parent(self):
        before = self.svc.detail(self.run['id'])
        child = self.svc.revise_run(self.run['id'], {'reason':'Correct the API name'})
        self.assertEqual(self.svc.detail(self.run['id']), before)
        self.assertEqual(child['status'], 'draft')
        self.assertTrue(child['ready_to_start'])
        self.assertEqual(child['source_lineage']['parent_run_id'], before['id'])
        self.assertEqual(child['budget']['max_calls'], 16)
        self.assertEqual(child['usage']['calls'], 0)
        self.assertNotIn('object_contract', child)
        self.assertIsNotNone(child['revision_draft'])
        self.assertEqual(child['source_card']['conclusion'], before['source_card']['conclusion'])
        self.assertEqual(self.svc.list_runs()[0]['source_lineage']['root_run_id'], before['id'])

    def test_legacy_library_evidence_string_source_is_supported(self):
        self.svc.update(self.run['id'], evidence=[dict(source='Mathlib', statement='A library declaration')])
        card = self.svc.detail(self.run['id'])['source_card']
        self.assertTrue(card['conclusion'])

    def test_small_budget_is_preserved_and_title_does_not_discard_seed(self):
        budget = dict(self.run['budget'], max_calls=2)
        self.svc.update(self.run['id'], budget=budget)
        child = self.svc.revise_run(self.run['id'], dict(reason='Improve readable title', corrections={'title':'Clearer title'}))
        self.assertEqual(child['budget']['max_calls'], 2)
        self.assertIsNotNone(child['revision_draft'])
        self.svc._started[child['id']] = time.monotonic()
        self.svc.update(child['id'], revision_draft=None)
        with self.assertRaisesRegex(ValueError, 'черновик'):
            self.svc._check(child['id'])

    def test_user_change_is_explicit_new_unverified_statement(self):
        original = copy.deepcopy(self.svc.detail(self.run['id'])['source_card'])
        child = self.svc.revise_run(self.run['id'], dict(reason='Clarify the intended claim',
            corrections={'claim':'A different claim requiring new proof'}))
        self.assertEqual(child['source_card']['conclusion'], 'A different claim requiring new proof')
        self.assertEqual(child['source_card']['grounding'][0]['origin'], 'user_revision')
        self.assertIsNone(child['revision_draft'])
        self.assertEqual(child['outcome'], 'unknown')
        self.assertEqual(self.svc.detail(self.run['id'])['source_card'], original)

    def test_cannot_change_hidden_contract_fields_or_revise_running_job(self):
        with self.assertRaises(ValueError):
            self.svc.revise_run(self.run['id'], dict(reason='Change goal', corrections={'agent_task':{}}))
        self.svc.update(self.run['id'], status='running')
        with self.assertRaises(ValueError):
            self.svc.revise_run(self.run['id'], {'reason':'Change API name'})

    def test_optional_catalogue_error_preserves_existing_result(self):
        result = dict(status='complete', outcome='proved', verification={'source_sha256':'a' * 64})
        self.svc.update(self.run['id'], result=result)
        store = Mock()
        store.register.side_effect = RuntimeError('Lean rejected catalogue audit subprocess')
        with patch.object(self.svc, '_check', return_value=60), patch.object(self.svc, 'mechanism_store', return_value=store):
            self.svc._register_verified_mechanism(self.run['id'], 'unused', {}, {'status':'aligned'})
        saved = self.svc.get(self.run['id'])
        self.assertEqual(saved['result'], result)
        self.assertEqual(saved['mechanism_registration']['status'], 'not_registered')
        self.assertEqual(saved['mechanism_registration']['error_type'], 'RuntimeError')


if __name__ == '__main__':
    unittest.main()
