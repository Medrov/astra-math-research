"""Controller/registry boundaries; model and proof results are explicit test doubles."""
import copy
import hashlib
import json
from pathlib import Path
import sys
import tempfile
import threading
import time
import unittest
from unittest.mock import patch

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
import research_service as rs
from research_object_examples import graph_for_case


def verified(transition):
    """Synthetic verifier report for publication tests, not a real Lean result."""
    return dict(success=True, compilation_success=True, target_preserved=True, obligations_passed=True,
                target=transition['agent_task']['target'], expected_statement=transition['agent_task']['statement'],
                audit={'status':'passed','unexpected_axioms':[],'unsafe_declarations':[]}, axioms=[],
                obligations=[dict(id=o['id'],target=o['target'],ok=True,
                                  statement_sha256=hashlib.sha256(o['statement'].encode()).hexdigest())
                             for o in transition['obligations']])


class TransitionWorkflowTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.service = rs.ResearchService(self.temp.name)

    def tearDown(self):
        self.service.pool.shutdown(wait=True)
        self.temp.cleanup()

    def create(self, **payload):
        run = self.service.create(dict(case_id='graph_energy',mode='pilot',**payload), start=False)
        self.service._started[run['id']] = time.monotonic()
        self.service.cancel_flags[run['id']] = threading.Event()
        return run

    def report(self, transition):
        return dict(verified(transition), environment_fingerprint=self.service.environment_fingerprint)

    def test_prepared_example_pins_all_obligations_before_execution(self):
        run = self.create()
        task = self.service._effective_task(run)
        self.assertEqual(run['selected_transition_id'], 'nonnegative_transfer')
        self.assertEqual(len(task['required_obligations']), 2)
        self.assertEqual(run['object_graph']['revision'], 1)
        self.assertTrue(run['object_contract_sha256'])
        self.assertTrue(all(t['status']=='proposed' for t in run['object_graph']['transitions']))
        again = self.create()
        self.assertEqual(again['graph_ref'], run['graph_ref'])

    def test_preview_selection_verifies_identity_not_default_transfer(self):
        run = self.create(transition_id='energy_identity')
        task = self.service._effective_task(run)
        self.assertEqual(task['target'], 'TriangleEnergy.graph_energy_eq')
        self.assertEqual(len(task['required_obligations']), 1)
        self.assertEqual(run['claim'], self.service._transition(run['object_graph'],'energy_identity')['claim'])

    def test_changed_semantics_cannot_reuse_a_prepared_proof(self):
        run = self.create()
        graph = copy.deepcopy(run['object_graph'])
        graph['objects'][0]['definition'] += ' Изменённое определение.'
        revised = self.service.revise_graph(graph['id'], {'graph':graph,'expected_revision':1})
        with self.assertRaisesRegex(ValueError, 'Изменённая постановка'):
            self.service.create(dict(mode='pilot',graph_id=revised['id'],graph_revision=2,
                                     transition_id=run['selected_transition_id']), start=False)

    def test_mutated_object_contract_is_rejected(self):
        run = self.create()
        changed = copy.deepcopy(run['object_contract'])
        changed['graph']['objects'][0]['definition'] = 'Другой объект'
        self.service.update(run['id'], object_contract=changed)
        with self.assertRaisesRegex(ValueError, 'Объекты'):
            self.service._check(run['id'])

    def test_plan_cannot_drop_a_secondary_obligation(self):
        run = self.create()
        task = self.service._effective_task(run)
        plan = dict(imports=task['imports'],prelude=task['prelude'],target_id=task['target'],
                    nodes=[dict(id=task['target'],statement=task['statement'],dependencies=[])])
        with self.assertRaisesRegex(ValueError, 'обязательную цель'):
            rs.validate_plan(plan,task)

    def test_discovery_is_one_bounded_model_call_and_no_proof(self):
        proposal = graph_for_case('graph_energy')
        proposal['sources'] = []
        run = self.service.create(dict(purpose='discover',mode='single',question='Предложить связи энергии графа и формы.',
                                       msc_codes=['05C50'],budget={'max_calls':1,'timeout_seconds':600}),start=False)
        response = dict(status='completed',text=json.dumps(proposal),usage={'last':{'totalTokens':50}})
        with patch('research_codex.run_task',return_value=response) as model, \
             patch('research_lean.verify_candidate',side_effect=AssertionError('discovery must not prove')):
            self.service.start(run['id'])
            self.service.futures[run['id']].result()
        saved = self.service.detail(run['id'])
        self.assertEqual(saved['status'],'complete',saved.get('error'))
        self.assertEqual(saved['result']['kind'],'transition_candidates')
        self.assertEqual(saved['usage']['calls'],1)
        self.assertEqual(model.call_count,1)
        self.assertTrue(all(t['status']=='proposed' and t['certificate'] is None for t in saved['object_graph']['transitions']))
        self.assertTrue(all(t['case_id'] is None for t in saved['object_graph']['transitions']))
        self.assertEqual(saved['object_graph']['question'], run['claim'])

    def test_publication_requires_every_exact_obligation(self):
        run = self.create()
        transition = self.service._transition(run['object_graph'],run['selected_transition_id'])
        report = self.report(transition)
        report['obligations'].pop()
        self.service.update(run['id'],result={'status':'complete','outcome':'proved','verification':report})
        self.service._record_transition_result(run['id'])
        graph = self.service.detail(run['id'])['object_graph']
        transition = self.service._transition(graph,run['selected_transition_id'])
        self.assertEqual(transition['status'],'unknown')
        self.assertIsNone(transition['certificate'])

    def test_late_result_stays_bound_to_its_historical_revision(self):
        run = self.create()
        transition = self.service._transition(run['object_graph'],run['selected_transition_id'])
        graph = copy.deepcopy(run['object_graph'])
        graph['objects'][0]['definition'] += ' Другая версия.'
        self.service.revise_graph(graph['id'],{'graph':graph,'expected_revision':1})
        self.service.update(run['id'],result={'status':'complete','outcome':'proved','verification':self.report(transition)})
        self.service._record_transition_result(run['id'])
        old = self.service.graph(graph['id'],1)
        current = self.service.graph(graph['id'])
        self.assertEqual(self.service._transition(old,transition['id'])['status'],'proved')
        self.assertIsNone(self.service._transition(current,transition['id'])['certificate'])

    def test_cancelled_publication_does_not_prevent_resume_certificate(self):
        run = self.create()
        rid = run['id']
        transition = self.service._transition(run['object_graph'],run['selected_transition_id'])
        self.service.update(rid,status='cancelled',error='User stopped')
        self.service._record_transition_result(rid)
        with patch.object(self.service,'_work'):
            self.service.start(rid)
            self.service.futures[rid].result()
        self.service.update(rid,result={'status':'complete','outcome':'proved','verification':self.report(transition)})
        self.service._record_transition_result(rid)
        saved = self.service._transition(self.service.detail(rid)['object_graph'],transition['id'])
        self.assertEqual(saved['status'],'proved')
        self.assertEqual(len(saved['results']),2)

    def test_pending_partial_publication_is_replayed_then_superseded(self):
        run = self.create()
        rid = run['id']
        transition = self.service._transition(run['object_graph'],run['selected_transition_id'])
        self.service.update(rid,status='cancelled',error='Interrupted before publication acknowledgement')
        self.service._record_transition_result(rid)
        self.service.update(rid,transition_result_recorded=False)
        with patch.object(self.service,'_work'):
            self.service.start(rid)
            self.service.futures[rid].result()
        self.service.update(rid,result={'status':'complete','outcome':'proved','verification':self.report(transition)})
        self.service._record_transition_result(rid)
        saved = self.service._transition(self.service.detail(rid)['object_graph'],transition['id'])
        self.assertEqual(saved['status'],'proved')
        self.assertEqual(len(saved['results']),2)

    def test_cached_model_reply_can_resume_at_call_budget(self):
        proposal = graph_for_case('graph_energy'); proposal['sources'] = []
        run = self.service.create(dict(purpose='discover',mode='single',question='Предложить связи энергии графа.',
                                       budget={'max_calls':1,'timeout_seconds':600}),start=False)
        rid = run['id']; key = 'object-proposal-v1'
        response = dict(status='completed',text=json.dumps(proposal),usage={'last':{'totalTokens':50}})
        rs.atomic(self.service.folder(rid)/'attempts'/key/'result.json',response)
        self.service.update(rid,status='interrupted',usage={'calls':1,'total_tokens':0,'elapsed_seconds':0},
                            attempts=[{'id':key,'role':'propose_transitions','status':'running'}])
        with patch('research_codex.run_task',side_effect=AssertionError('must use cached model result')):
            self.service.start(rid);self.service.futures[rid].result()
        saved = self.service.detail(rid)
        self.assertEqual(saved['status'],'complete',saved.get('error'))
        self.assertEqual(saved['usage']['calls'],1)

    def test_cached_proof_is_not_relabelled_as_a_new_environment(self):
        run = self.create(); rid = run['id']
        transition = self.service._transition(run['object_graph'],run['selected_transition_id'])
        old_report = self.report(transition)
        previous_environment = self.service.environment_fingerprint
        self.service.environment_fingerprint = 'different-environment'
        self.service.registry.environment_fingerprint = 'different-environment'
        self.service.update(rid,result={'status':'complete','outcome':'proved','verification':old_report})
        self.service._record_transition_result(rid)
        saved = self.service._transition(self.service.detail(rid)['object_graph'],transition['id'])
        self.assertEqual(saved['status'],'needs_recheck')
        self.assertEqual(saved['last_result']['environment_fingerprint'],previous_environment)

    def test_immediate_resume_waits_for_terminal_worker_cleanup(self):
        run = self.create(); rid = run['id']
        entered = threading.Event()
        def first_work(_):
            self.service.update(rid,status='cancelled',cancel_requested=True)
            entered.set()
            time.sleep(.15)
            self.service._record_transition_result(rid)
        with patch.object(self.service,'_work',side_effect=first_work):
            self.service.start(rid)
            self.assertTrue(entered.wait(3))
        with patch.object(self.service,'_work') as resumed:
            response = self.service.start(rid)
            self.service.futures[rid].result()
        self.assertIn(response['status'],('queued','running'))
        resumed.assert_called_once_with(rid)
        self.assertFalse(self.service.get(rid)['cancel_requested'])

    def test_obligation_search_is_cached_per_plan_version_without_mutating_goal(self):
        run = self.create(); rid = run['id']
        node = dict(id='energy_lemma',statement='∀ x : ℝ, x ^ 2 ≥ 0')
        diagnostics = {'error':'unknown constant helper_nonneg'}
        with patch('research_retrieval.search',return_value=[{'id':'known_lemma'}]) as search:
            first = self.service._retrieve_for_obligation(rid,{'revision':0},node,diagnostics)
            second = self.service._retrieve_for_obligation(rid,{'revision':0},node,diagnostics)
            self.assertEqual(first,second)
            self.assertEqual(search.call_count,1)
            self.assertIn(node['statement'],search.call_args.args[0])
            self.assertIn('helper_nonneg',search.call_args.args[0])
            self.service._retrieve_for_obligation(rid,{'revision':1},node,diagnostics)
            self.assertEqual(search.call_count,2)
        self.assertEqual(self.service.get(rid)['object_contract_sha256'],run['object_contract_sha256'])


if __name__ == '__main__':
    unittest.main()
