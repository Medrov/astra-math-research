import json
from pathlib import Path
import unittest
import analysis_engine as engine

ROOT=Path(__file__).resolve().parents[1]

class CandidateGenerationTests(unittest.TestCase):
    def pair(self,kind='def',type_='Nat → Nat'):
        return [dict(module=m,selected_declarations=[dict(name=m+'.transform',kind=kind,type=type_)]) for m in ['InputA','InputB']]

    def test_generated_attempt_has_both_targets_and_no_placeholder_axiom(self):
        source=engine.definition_equality_attempt(self.pair())
        self.assertIn('@InputA.transform = @InputB.transform',source)
        self.assertIn('  rfl',source)
        self.assertNotIn('sorry',source)
        self.assertNotIn('axiom',source)

    def test_proof_objects_are_not_compared_by_proof_irrelevance(self):
        self.assertIsNone(engine.definition_equality_attempt(self.pair('theorem','∀ n : Nat, n = n')))

    def test_different_types_do_not_get_equality_attempt(self):
        pair=self.pair();pair[1]['selected_declarations'][0]['type']='Nat → Bool'
        self.assertIsNone(engine.definition_equality_attempt(pair))

    def test_subject_route_does_not_use_history_or_publication_hubs(self):
        data=json.loads((ROOT/'data/msc2020.json').read_text())
        route=engine.navigation_path('17C40','05C50',data)
        self.assertEqual(route['status'],'navigation_only')
        self.assertEqual(route['search_policy'],'subject_navigation_v2')
        self.assertTrue(route['nodes'])
        self.assertFalse(any('-' in code or code[:2] in {'00','01'} for code in route['nodes']))

if __name__=='__main__':unittest.main()
