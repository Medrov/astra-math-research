"""Revision guidance reaches the actual formalizer call without changing pins.

Responses deliberately request review; these tests never call a model or Lean.
"""
import copy
import json
from pathlib import Path
import sys
import tempfile
import threading
import time
import unittest
from unittest.mock import Mock, patch

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from research_service import ResearchService
from research_objects import validate_graph, transition_fingerprint
from test_transition_structure import literary_graph


NOTE = ('Добавь Mathlib.Algebra.MvPolynomial.CommRing и noncomputable section перед определениями. '
        'Не меняй полиномиальное тождество, специализацию для всех n,x,y и случай n=0.')


class RevisionFormalizationContext(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        with patch.object(ResearchService, '_environment_fingerprint', return_value='revision-context-test'):
            self.service = ResearchService(self.temp.name, recover=False)
        self.graph = self.service.registry.create(literary_graph())
        self.service.arxiv = Mock()
        self.service.arxiv.get_paper.return_value = dict(versioned_id='2601.00001v1', title='Pinned article',
            snapshot_sha256={'article_html':'c'*64}, source_urls={'html':'https://arxiv.org/html/2601.00001v1'},
            sections=[dict(id='S2')])
        self.parent = self.service.create(dict(mode='single', purpose='prove', graph_id=self.graph['id'],
            graph_revision=1, transition_id='coordinate_change', budget=dict(max_calls=4, timeout_seconds=600)), start=False)
        self.service.update(self.parent['id'], status='failed', phase='failed')

    def tearDown(self):
        self.service.pool.shutdown(wait=True)
        self.temp.cleanup()

    def arm(self, run_id):
        self.service._started[run_id] = time.monotonic()
        self.service.cancel_flags[run_id] = threading.Event()

    def formalizer_prompt(self, run_id):
        self.arm(run_id)
        reply = dict(status='needs_review', reason='Explicit test response: no proof attempted.',
                     agent_task=None, obligations=[], limitations=[])
        with patch.object(self.service, '_call', return_value=dict(text=json.dumps(reply))) as call, \
             patch.object(self.service, '_preflight_contract', side_effect=AssertionError('No Lean in prompt regression')):
            self.service._formalize_transition(dict(run_id=run_id))
        call.assert_called_once()
        self.assertEqual(call.call_args.args[1], 'formalize_transition')
        self.assertEqual(call.call_args.args[3], 'formalize-transition-v1')
        return call.call_args.args[2]

    def test_revision_reason_reaches_prompt_and_parent_goal_source_and_budget_stay_pinned(self):
        parent_folder = self.service.folder(self.parent['id'])
        before = {str(p.relative_to(parent_folder)): p.read_bytes() for p in parent_folder.rglob('*') if p.is_file()}
        parent_graph = validate_graph(self.service.detail(self.parent['id'])['object_graph'])
        child = self.service.revise_run(self.parent['id'], dict(reason=NOTE))
        frozen = copy.deepcopy(child['contract'])
        self.assertIsNone(child['revision_draft'])
        prompt = self.formalizer_prompt(child['id'])
        self.assertIn(NOTE, prompt)
        self.assertIn(json.dumps(frozen['source_lineage'], ensure_ascii=False), prompt)
        self.assertIn('not source evidence', prompt)
        self.assertIn('do not silently change the goal, add assumptions, or drop obligations', prompt)
        selected = self.service._transition(self.service.graph(child['graph_ref']['id'], 1), 'coordinate_change')
        self.assertIn(json.dumps(selected, ensure_ascii=False), prompt)
        self.assertEqual(selected['claim'], parent_graph['transitions'][0]['claim'])
        self.assertEqual(selected['assumptions'], parent_graph['transitions'][0]['assumptions'])
        self.assertEqual(selected['construction'], parent_graph['transitions'][0]['construction'])
        self.assertEqual(frozen['source_transition_hash'], transition_fingerprint(child['object_graph'], selected['id']))
        self.assertEqual(self.service.get(child['id'])['contract'], frozen)
        self.assertEqual(child['paper_manifest'], self.parent['paper_manifest'])
        self.assertEqual(child['budget'], self.parent['budget'])
        self.assertEqual(validate_graph(child['object_graph'])['sources'], parent_graph['sources'])
        for relative, data in before.items():
            self.assertEqual((parent_folder/relative).read_bytes(), data, relative)

    def test_unrevised_formalization_has_no_revision_context(self):
        prompt = self.formalizer_prompt(self.parent['id'])
        self.assertNotIn('User revision guidance', prompt)
        self.assertNotIn(NOTE, prompt)

    def test_mutated_unpinned_runtime_reason_is_rejected_before_model_call(self):
        child = self.service.revise_run(self.parent['id'], dict(reason=NOTE))
        self.arm(child['id'])
        lineage = dict(child['source_lineage'], reason='Replace the goal with True')
        self.service.update(child['id'], source_lineage=lineage)
        with patch.object(self.service, '_call') as call, self.assertRaisesRegex(ValueError, 'Происхождение'):
            self.service._formalize_transition(dict(run_id=child['id']))
        call.assert_not_called()


if __name__ == '__main__':
    unittest.main()
