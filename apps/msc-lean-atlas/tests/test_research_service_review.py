"""Regression scenarios from independent controller review (no model inference)."""
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
import research_retrieval as rr
import research_lean


class ResearchReviewTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.service = rs.ResearchService(root=self.temp.name)
    def tearDown(self):
        self.service.pool.shutdown(wait=True)
        self.temp.cleanup()
    def make_run(self, **extra):
        payload = dict(case_id='graph_energy', mode='single', budget={'max_calls':8,'timeout_seconds':600})
        payload.update(extra)
        run = self.service.create(payload, start=False)
        self.service._started[run['id']] = time.monotonic()
        self.service.cancel_flags[run['id']] = threading.Event()
        return run
    def test_real_catalog_relations_are_indexed_with_sources(self):
        expected=json.loads((rr.ROOT/'catalog/bridges.json').read_text())['edges']
        docs=[d for d in rr.documents([]) if d['id'].startswith('catalog:')]
        self.assertEqual(len(docs),len(expected))
        self.assertTrue(all(d['statement'] for d in docs))
        self.assertTrue(any('https://' in str(d['source']) for d in docs))
    def test_case_claim_cannot_be_silently_replaced(self):
        with self.assertRaises(ValueError):
            self.make_run(mode='pilot', question='Все действительные числа равны нулю.')
    def test_cached_call_reconciles_accounting_after_crash(self):
        run=self.make_run();key='plan';rid=run['id']
        self.service.update(rid, attempts=[{'id':key,'role':'plan','status':'running'}],
                            usage={'calls':1,'total_tokens':0,'elapsed_seconds':0})
        folder=self.service.folder(rid)/'attempts'/key
        result={'status':'completed','text':'{}','thread_id':'thread','turn_id':'turn',
                'usage':{'total':{'totalTokens':1000},'last':{'totalTokens':42}}}
        rs.atomic(folder/'result.json',result)
        with patch('research_codex.run_task',side_effect=AssertionError('must not regenerate')):
            self.service._call(rid,'plan','prompt',key)
        saved=self.service.get(rid)
        self.assertEqual(saved['usage']['calls'],1)
        self.assertEqual(saved['usage']['total_tokens'],42)
        self.assertEqual(saved['attempts'][0]['status'],'completed')
        self.service._call(rid,'plan','prompt',key)
        self.assertEqual(self.service.get(rid)['usage']['total_tokens'],42)
    def test_resume_revalidates_target_against_immutable_contract(self):
        run=self.make_run();rid=run['id'];folder=self.service.folder(rid)
        bad={'imports':['Mathlib'],'prelude':'','target_id':'intruder','order':['intruder'],
             'nodes':[{'id':'intruder','statement':'True','dependencies':[],'proof':'by trivial'}]}
        rs.atomic(folder/'plan.json',bad)
        rs.atomic(folder/'proofs.json',{'intruder':{'declaration':'theorem intruder : True := by trivial'}})
        with patch.object(self.service,'_call',return_value={'text':'{"status":"aligned"}'}), \
             patch('research_lean.verify_candidate',return_value={'success':True,'declarations':[]}):
            with self.assertRaises(ValueError):
                self.service._model_workflow(rid)

    def test_lean_work_observes_overall_deadline(self):
        run=self.make_run(mode='pilot');rid=run['id']
        def slow_pilot(*args, **kwargs):
            self.service._started[rid] = time.monotonic()-601
            stopped=kwargs['cancelled']()
            return {'status':'cancelled' if stopped else 'complete','outcome':'unknown'}
        with patch('research_lean.run_pilot',side_effect=slow_pilot):
            with self.assertRaises(rs.StopRun):
                self.service._investigate({'run_id':rid})
    def test_cancel_before_publish_does_not_mark_complete(self):
        run=self.make_run(mode='pilot');rid=run['id']
        self.service.update(rid,result={'status':'complete','outcome':'proved'})
        self.service.cancel_flags[rid].set()
        with self.assertRaises(rs.StopRun):
            self.service._publish({'run_id':rid})


if __name__=='__main__':unittest.main()
