"""Evidence presentation: no proof/search promotion from labels or errors."""
import copy
import hashlib
from pathlib import Path
import sys
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from research_outcomes import outcome_summary, proof_progress


def proof_run():
    goals = [dict(id='one', target='one', statement='∀ n : Nat, n = n'),
             dict(id='two', target='two', statement='True')]
    return dict(purpose='prove', status='failed', phase='failed', active_stage='investigate',
        contract_verification=dict(well_typed=True),
        object_contract=dict(transition_id='bridge', graph=dict(transitions=[dict(id='bridge', obligations=goals,
                             agent_task=dict(target=goals[0]['target'], statement=goals[0]['statement']))])),
        nodes=[dict(id=g['target'], statement=g['statement'], status='pending') for g in goals],
        events=[dict(phase='prove'), dict(phase='verify')],
        termination=dict(code='invalid_contract', stage='verify', message='Legacy Goedel audit failure'))


class OutcomeTests(unittest.TestCase):
    def test_late_proof_error_does_not_reject_accepted_formalization(self):
        run = proof_run()
        self.assertEqual(outcome_summary(run)['category'], 'proof_incomplete')
        self.assertTrue(proof_progress(run)['started'])

    def test_preserves_exact_verified_partial_obligation_not_arbitrary_lemma(self):
        run = proof_run()
        good = dict(success=True, target_preserved=True, audit=dict(status='passed'),
                    target='one', expected_statement=run['nodes'][0]['statement'])
        run['nodes'][0].update(status='proved', verification=good)
        run['nodes'].append(dict(id='helper', statement='True', status='proved', verification=good))
        self.assertEqual(proof_progress(run)['proved'], 1)
        self.assertEqual(proof_progress(run)['obligations_total'], 2)
        for mutation in ('target', 'expected_statement'):
            invalid = copy.deepcopy(run)
            invalid['nodes'][0]['verification'][mutation] = 'different'
            self.assertEqual(proof_progress(invalid)['proved'], 0)
        run['nodes'][0]['verification']['audit']['status'] = 'rejected'
        self.assertEqual(proof_progress(run)['proved'], 0)

    def test_type_failure_has_its_own_stage(self):
        run = proof_run()
        run.update(events=[], active_stage='formalize_transition', contract_verification=dict(well_typed=False),
                   termination=dict(code='invalid_contract', stage='lean_contract_preflight'))
        self.assertEqual(outcome_summary(run)['category'], 'formalization_failed')
        self.assertFalse(proof_progress(run)['started'])

    def test_technical_failure_is_not_a_refutation(self):
        for code in ('infrastructure', 'proof_audit_rejected', 'model_response_invalid', 'lean_timeout'):
            run = proof_run(); run['termination']['code'] = code
            with self.subTest(code=code):
                result = outcome_summary(run)
                self.assertEqual(result['category'], 'infrastructure_error')
                self.assertTrue(result['technical_failure'])
                self.assertNotEqual(result['proof_status'], 'refuted')

    def test_empty_search_is_distinct_from_unfinished_search(self):
        run = dict(purpose='structure', status='complete', structure_routes=[dict(status='complete', candidates=[])])
        self.assertEqual(outcome_summary(run)['category'], 'no_supported_candidates')
        for state in ('cancelled', 'budget_exhausted', 'failed'):
            interrupted = dict(run, status=state)
            self.assertEqual(outcome_summary(interrupted)['search_status'], 'partial')
            self.assertNotEqual(outcome_summary(interrupted)['category'], 'no_supported_candidates')
        run['structure_routes'][0]['status'] = 'failed'
        self.assertEqual(outcome_summary(run)['category'], 'search_partial')

    def test_candidate_search_can_be_complete_without_any_proof(self):
        run = dict(purpose='structure', status='complete', object_graph=dict(transitions=[dict(id='candidate')]))
        self.assertEqual(outcome_summary(run)['category'], 'candidates_found')
        self.assertEqual(outcome_summary(run)['proof_status'], 'not_applicable')
        self.assertEqual(outcome_summary(run)['search_status'], 'complete')

    def test_continuation_duplicates_are_not_new_candidates(self):
        run = dict(purpose='structure', status='complete', object_graph=dict(transitions=[]),
                   structure_routes=[dict(status='complete', candidates=[dict(duplicate_of='previous')])])
        self.assertEqual(outcome_summary(run)['category'], 'no_supported_candidates')
        run.pop('object_graph')
        self.assertEqual(outcome_summary(run)['category'], 'no_supported_candidates')

    def test_budget_keeps_partial_evidence_and_does_not_claim_impossibility(self):
        run = proof_run(); run.update(status='budget_exhausted', termination=dict(code='budget_exhausted'))
        result = outcome_summary(run)
        self.assertEqual(result['category'], 'proof_incomplete')
        self.assertFalse(result['technical_failure'])

    def test_green_labels_without_full_verification_are_insufficient(self):
        run = proof_run(); run.update(status='complete', outcome='proved', final_semantic_review=dict(status='aligned'))
        self.assertNotEqual(outcome_summary(run)['category'], 'proved')
        run['verification'] = dict(success=True, target_preserved=True, audit=dict(status='passed'), obligations_passed=True)
        self.assertNotEqual(outcome_summary(run)['category'], 'proved')
        goals = run['object_contract']['graph']['transitions'][0]['obligations']
        run['verification'].update(target=goals[0]['target'], expected_statement=goals[0]['statement'],
            obligations=[dict(id=g['id'], target=g['target'], ok=True,
                statement_sha256=hashlib.sha256(g['statement'].encode('utf-8')).hexdigest()) for g in goals])
        self.assertEqual(outcome_summary(run)['category'], 'proved')
        self.assertEqual(proof_progress(run)['proved'], 2)
        changed = copy.deepcopy(run)
        changed['verification']['obligations'][1]['statement_sha256'] = '0'*64
        self.assertFalse(proof_progress(changed)['full_contract_verified'])
        self.assertNotEqual(outcome_summary(changed)['category'], 'proved')
        changed = copy.deepcopy(run); changed['verification']['target'] = 'different'
        self.assertFalse(proof_progress(changed)['full_contract_verified'])
        run['final_semantic_review']['status'] = 'not_performed'
        self.assertEqual(outcome_summary(run)['category'], 'semantic_review_needed')


if __name__ == '__main__':
    unittest.main()
