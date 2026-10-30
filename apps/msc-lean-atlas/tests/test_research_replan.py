"""Compiler-driven replan scenarios: real controller, deterministic model/tool doubles."""
import copy
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


def node(name, dependencies=None):
    return dict(id=name, title=name, statement='True', dependencies=dependencies or [], proof='')


def plan(nodes):
    return dict(imports=['Mathlib'], prelude='', summary='Controlled test plan', assumptions=[],
                relation_kind='test', target_id='finish', nodes=nodes)


class ReplanTests(unittest.TestCase):
    def setUp(self):
        self.temp=tempfile.TemporaryDirectory()
        self.service=rs.ResearchService(root=self.temp.name)
        self.initial=plan([node('kept'),node('hard',['kept']),node('finish',['hard'])])
        self.revised=plan([node('kept'),node('bridge',['kept']),node('finish',['bridge'])])
        self.calls=[]
        self.lean_calls=[]
        self.fail_names={'hard'}
        self.reject_first=False
        self.model_patch=patch('research_codex.run_task',side_effect=self.model)
        self.lean_patch=patch('research_lean.verify_candidate',side_effect=self.lean)
        self.model_patch.start();self.lean_patch.start()
    def tearDown(self):
        self.model_patch.stop();self.lean_patch.stop()
        self.service.pool.shutdown(wait=True)
        self.temp.cleanup()
    def create(self, mode='multi', max_calls=24):
        run=self.service.create({'mode':mode,'question':'Проверить неизменность целевой постановки.',
                                 'budget':{'max_calls':max_calls,'timeout_seconds':600}},start=False)
        rid=run['id']
        self.service._started[rid]=time.monotonic()
        self.service.cancel_flags[rid]=threading.Event()
        return rid
    def model(self,prompt,work_dir,**kwargs):
        key=Path(work_dir).name
        self.calls.append((key,prompt,kwargs))
        if key=='plan':
            value=copy.deepcopy(self.initial)
        elif key.startswith('critic-'):
            value={'verdict':'reject' if self.reject_first and key=='critic-v0' else 'accept',
                   'reason':'controlled critique','issues':[]}
        elif key.startswith('revise-critic'):
            value=copy.deepcopy(self.initial)
        elif key.startswith('revise-lean'):
            value=copy.deepcopy(self.revised)
        elif key.startswith('prove-'):
            value={'proof':'by\n  exact True.intro','explanation':'fixture response'}
        elif key.startswith('semantic-'):
            value={'status':'aligned','reason':'controlled semantic review','limitations':[]}
        else:
            raise AssertionError('Unexpected call '+key)
        return {'status':'completed','text':json.dumps(value),'thread_id':'t-'+key,'turn_id':'turn-'+key,
                'usage':{'last':{'totalTokens':100}},'error':None,'model':'gpt-6-astra'}
    def lean(self, source,target,work_dir,expected_statement=None,**kwargs):
        self.lean_calls.append((target,str(work_dir),source,expected_statement))
        failed=target in self.fail_names
        return {'success':not failed,'status':'failed' if failed else 'complete','declarations':[],
                'target_preserved':not failed,'diagnostics':[{'stdout':'unknown helper constant' if failed else ''}],
                'error':'compiler rejected candidate' if failed else None}
    def test_replan_reuses_proved_nodes_and_persists_diagnostics(self):
        rid=self.create()
        self.service._model_workflow(rid)
        folder=self.service.folder(rid)
        saved=self.service.get(rid)
        self.assertEqual(saved['outcome'],'proved')
        self.assertEqual(saved['plan_revision'],1)
        self.assertEqual(saved['replan_counts'],{'critic':0,'lean':1})
        keys=[key for key,_,_ in self.calls]
        self.assertEqual(keys.count('prove-v0-kept-0'),1)
        self.assertFalse(any(key.startswith('prove-v1-kept') for key in keys))
        self.assertIn('prove-v0-hard-0',keys)
        self.assertIn('prove-v0-hard-1',keys)
        self.assertIn('prove-v1-bridge-0',keys)
        self.assertIn('critic-v0',keys);self.assertIn('critic-v1',keys)
        self.assertIn('semantic-review-v1',keys)
        self.assertTrue((folder/'plan-v0.json').exists())
        self.assertTrue((folder/'plan-v1.json').exists())
        feedback=json.loads((folder/'replan-feedback-v1.json').read_text())
        self.assertEqual(feedback['preserved_nodes'],['kept'])
        self.assertEqual(len(feedback['feedback'][0]['reports']),2)
        self.assertIn('unknown helper',json.dumps(feedback))
        proofs=json.loads((folder/'proofs.json').read_text())
        self.assertEqual(proofs['kept']['revision'],0)
        self.assertEqual(proofs['finish']['revision'],1)
        self.assertEqual(proofs['finish']['dependencies'],['bridge'])
        self.assertEqual(saved['usage']['calls'],len(keys))
        self.assertEqual(saved['usage']['total_tokens'],100*len(keys))
        self.assertTrue(any(e['phase']=='verify' and e['message'].startswith('Lean проверяет') for e in saved['events']))
    def test_recovery_reuses_revision_calls_without_new_inference(self):
        rid=self.create()
        self.service._model_workflow(rid)
        count=len(self.calls)
        tokens=self.service.get(rid)['usage']['total_tokens']
        self.service._model_workflow(rid)
        self.assertEqual(len(self.calls),count)
        self.assertEqual(self.service.get(rid)['usage']['total_tokens'],tokens)
        self.assertEqual(self.service.get(rid)['plan_revision'],1)
    def test_second_compiler_failure_stops_without_unbounded_replan(self):
        self.fail_names.add('bridge')
        rid=self.create();self.service._model_workflow(rid)
        saved=self.service.get(rid)
        self.assertEqual(saved['outcome'],'unknown')
        self.assertEqual(sum(key.startswith('revise-lean') for key,_,_ in self.calls),1)
        self.assertFalse(any(key.startswith('semantic') for key,_,_ in self.calls))
        self.assertFalse((self.service.folder(rid)/'plan-v2.json').exists())
    def test_replan_cannot_change_proved_type(self):
        self.revised['nodes'][0]['statement']='False'
        rid=self.create()
        with self.assertRaisesRegex(ValueError,'доказанную лемму'):
            self.service._model_workflow(rid)
        self.assertEqual(self.service.get(rid)['outcome'],'unknown')
        self.assertFalse((self.service.folder(rid)/'plan-v1.json').exists())
    def test_replan_cannot_change_proved_dependencies(self):
        self.revised=plan([node('new'),node('kept',['new']),node('bridge',['kept']),node('finish',['bridge'])])
        rid=self.create()
        with self.assertRaisesRegex(ValueError,'зависимости доказанной'):
            self.service._model_workflow(rid)
    def test_custom_target_and_definitions_are_frozen(self):
        for change in ('target','imports','prelude'):
            with self.subTest(change=change):
                revised=copy.deepcopy(self.revised)
                if change=='target': self.revised['nodes'][-1]['statement']='False'
                if change=='imports': self.revised['imports']=['Mathlib.Data.Nat.Basic']
                if change=='prelude': self.revised['prelude']='def surprise : Nat := 1'
                rid=self.create()
                with self.assertRaises(ValueError): self.service._model_workflow(rid)
                contract=json.loads((self.service.folder(rid)/'formal-contract.json').read_text())
                self.assertEqual(contract['target'],'finish')
                self.assertEqual(contract['statement'],'True')
                self.assertEqual(contract['imports'],['Mathlib'])
                self.assertEqual(contract['prelude'],'')
                self.revised=revised
    def test_resume_rejects_changed_custom_formal_target(self):
        rid=self.create();self.service._model_workflow(rid)
        folder=self.service.folder(rid)
        current=json.loads((folder/'plan.json').read_text())
        current['nodes'][-1]['statement']='False'
        rs.atomic(folder/'plan.json',current)
        count=len(self.calls)
        with self.assertRaises(ValueError): self.service._model_workflow(rid)
        self.assertEqual(len(self.calls),count)
    def test_one_critic_and_one_lean_replan_use_separate_revisions(self):
        self.reject_first=True
        rid=self.create();self.service._model_workflow(rid)
        saved=self.service.get(rid)
        self.assertEqual(saved['plan_revision'],2)
        self.assertEqual(saved['replan_counts'],{'critic':1,'lean':1})
        keys=[key for key,_,_ in self.calls]
        self.assertIn('revise-critic-v1',keys)
        self.assertIn('revise-lean-v2',keys)
        self.assertIn('critic-v2',keys)
        self.assertTrue((self.service.folder(rid)/'plan-v2.json').exists())
    def test_failure_artifacts_available_without_publish(self):
        rid=self.create()
        marker=self.service.folder(rid)/'diagnostic.log';marker.write_text('saved failure evidence')
        with patch.object(self.service,'_retrieve',side_effect=ValueError('controlled failure')):
            self.service._work(rid)
        saved=self.service.get(rid)
        self.assertEqual(saved['status'],'failed')
        self.assertTrue(any(a['path']=='diagnostic.log' for a in saved['artifacts']))
    def test_replan_respects_existing_call_budget(self):
        rid=self.create(max_calls=5)
        with self.assertRaises(rs.StopRun) as caught:
            self.service._model_workflow(rid)
        self.assertEqual(caught.exception.status,'budget_exhausted')
        self.assertEqual(len(self.calls),5)
        self.assertFalse(any(key.startswith('revise-lean') for key,_,_ in self.calls))
        self.assertEqual(self.service.get(rid)['usage']['calls'],5)


if __name__=='__main__':unittest.main()
