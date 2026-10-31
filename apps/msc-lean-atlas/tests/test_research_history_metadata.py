import copy
import unittest

from research_service import history_summary


class HistoryMetadataTests(unittest.TestCase):
    def test_transition_title_and_frozen_source_are_exposed_without_proof_content(self):
        run = dict(id='r', title='Truncated mathematical claim', purpose='prove', status='failed',
                   selected_transition_id='geometry', graph_ref=dict(id='derived', revision=1),
                   source_graph_ref=dict(id='source', revision=3), paper_ids=['paper-v2'],
                   paper_manifest=[dict(title='Actual article title')],
                   object_graph=dict(transitions=[dict(id='geometry', title='Exact transition title')]),
                   result=dict(verification=dict(success=False)), claim='Long full claim')
        before = copy.deepcopy(run)
        summary = history_summary(run)
        self.assertEqual(summary['display_title'], 'Exact transition title')
        self.assertEqual(summary['source_title'], 'Actual article title')
        self.assertEqual(summary['source_graph_ref'], dict(id='source', revision=3))
        self.assertEqual(summary['status'], 'failed')
        self.assertNotIn('result', summary)
        self.assertNotIn('object_graph', summary)
        self.assertNotIn('claim', summary)
        self.assertEqual(run, before)

    def test_search_has_a_readable_label_without_inventing_a_source(self):
        summary = history_summary(dict(purpose='structure', title='Raw Lean identifier', status='complete', outcome='unknown'))
        self.assertEqual(summary['display_title'], 'Поиск общей структуры')
        self.assertEqual(summary['source_title'], '')
        self.assertEqual(summary['outcome'], 'unknown')

    def test_other_transition_does_not_rename_selected_task(self):
        summary = history_summary(dict(purpose='prove', title='Fallback', selected_transition_id='missing',
                                       object_graph=dict(transitions=[dict(id='other', title='Wrong title')])))
        self.assertEqual(summary['display_title'], 'Fallback')


if __name__ == '__main__':
    unittest.main()
