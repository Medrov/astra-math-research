"""Cross-process ownership/cancellation without model calls or real foreign PIDs."""
from concurrent.futures import Future
import json
import os
from pathlib import Path
import sys
import subprocess
import tempfile
import threading
import time
import unittest
from unittest.mock import patch

sys.path.insert(0,str(Path(__file__).resolve().parents[1]))
import research_service as rs


class OwnershipTests(unittest.TestCase):
    def setUp(self):
        self.temp=tempfile.TemporaryDirectory()
        self.services=[]
        self.service=self.new_service()
        self.run=self.service.create({'mode':'single','question':'Controlled ownership research task',
                                      'budget':{'max_calls':8,'timeout_seconds':600}},start=False)
        self.rid=self.run['id']
    def new_service(self, recover=True):
        service=rs.ResearchService(self.temp.name,recover=recover)
        self.services.append(service)
        return service
    def tearDown(self):
        for service in self.services: service.pool.shutdown(wait=True)
        rs._LOCAL_FUTURES.pop(str(self.service.folder(self.rid).resolve()),None)
        self.temp.cleanup()
    def test_create_records_owner(self):
        self.assertEqual(self.run['owner_pid'],os.getpid())
        self.assertFalse(self.run['cancel_requested'])
    def test_initializing_second_service_preserves_live_foreign_run(self):
        self.service.update(self.rid,status='running',owner_pid=424242)
        with patch.object(rs,'owner_alive',return_value=True):
            observer=self.new_service()
        self.assertEqual(observer.get(self.rid)['status'],'running')
    def test_dead_owner_recovered_but_unknown_legacy_owner_left_alone(self):
        self.service.update(self.rid,status='running',owner_pid=424242)
        with patch('research_service.process_exists',side_effect=ProcessLookupError):
            observer=self.new_service()
        self.assertEqual(observer.get(self.rid)['status'],'interrupted')
        self.service.update(self.rid,status='running',owner_pid=None)
        observer=self.new_service()
        self.assertEqual(observer.get(self.rid)['status'],'running')
    def test_permission_denied_is_not_evidence_owner_died(self):
        with patch('research_service.process_exists',side_effect=PermissionError):
            self.assertTrue(rs.owner_alive(424242))
        with patch('research_service.process_exists',side_effect=OSError):
            self.assertTrue(rs.owner_alive(424242))
    def test_start_does_not_dispatch_foreign_live_owner(self):
        self.service.update(self.rid,status='running',owner_pid=424242)
        with patch.object(rs,'owner_alive',return_value=True),patch.object(self.service.pool,'submit') as submit:
            result=self.service.start(self.rid)
        submit.assert_not_called()
        self.assertEqual(result['owner_pid'],424242)
    def test_same_process_service_instances_share_active_future(self):
        observer=self.new_service()
        active=Future()
        with patch.object(self.service.pool,'submit',return_value=active):
            self.service.start(self.rid)
        with patch.object(observer.pool,'submit') as submit:
            observer.start(self.rid)
        submit.assert_not_called()
        # A stale completed local future must not shadow another instance's active one.
        completed=Future();completed.set_result(None)
        observer.futures[self.rid]=completed
        with patch.object(observer.pool,'submit') as submit:
            observer.start(self.rid)
        submit.assert_not_called()
        active.set_result(None)
    def test_cancel_is_durable_and_observed_by_other_instance(self):
        observer=self.new_service()
        self.service._started[self.rid]=time.monotonic()
        self.service.cancel_flags[self.rid]=threading.Event()
        observer.cancel(self.rid)
        self.assertFalse(self.service.cancel_flags[self.rid].is_set())
        self.assertTrue(self.service.get(self.rid)['cancel_requested'])
        with self.assertRaises(rs.StopRun) as caught:
            self.service._check(self.rid)
        self.assertEqual(caught.exception.status,'cancelled')
        self.service.event(self.rid,'verify','late worker event')
        self.service.update(self.rid,usage={'calls':1,'total_tokens':17,'elapsed_seconds':1})
        self.assertTrue(observer.get(self.rid)['cancel_requested'])
    def test_valid_resume_claims_owner_and_clears_cancellation(self):
        self.service.update(self.rid,status='cancelled',owner_pid=424242,cancel_requested=True)
        future=Future()
        with patch.object(self.service.pool,'submit',return_value=future):
            result=self.service.start(self.rid)
        self.assertEqual(result['owner_pid'],os.getpid())
        self.assertFalse(result['cancel_requested'])
        self.assertFalse(self.service.cancel_flags[self.rid].is_set())
        future.set_result(None)
    def test_mutating_events_and_cancel_across_instances_preserve_each_other(self):
        observer=self.new_service()
        barrier=threading.Barrier(3)
        def worker(service,label):
            barrier.wait()
            for i in range(15): service.event(self.rid,'test',label+str(i))
        a=threading.Thread(target=worker,args=(self.service,'a'))
        b=threading.Thread(target=worker,args=(observer,'b'))
        a.start();b.start();barrier.wait()
        observer.cancel(self.rid)
        a.join(timeout=5);b.join(timeout=5)
        self.assertFalse(a.is_alive());self.assertFalse(b.is_alive())
        result=self.service.get(self.rid)
        expected={label+str(i) for label in ('a','b') for i in range(15)}
        self.assertEqual({event['message'] for event in result['events'] if event['message'] in expected},expected)
        self.assertTrue(result['cancel_requested'])

    def test_real_second_process_can_cancel_without_stealing_owner(self):
        self.service._started[self.rid]=time.monotonic()
        self.service.cancel_flags[self.rid]=threading.Event()
        script = """import json,sys
sys.path.insert(0,sys.argv[1])
import research_service
service=research_service.ResearchService(sys.argv[2])
def forbid_dispatch(*args,**kwargs):
    raise AssertionError('foreign run must not dispatch')
service.pool.submit=forbid_dispatch
before=service.start(sys.argv[3])
after=service.cancel(sys.argv[3])
print(json.dumps({'before_status':before['status'],'owner_pid':after['owner_pid'],'cancel_requested':after['cancel_requested']}))
service.pool.shutdown(wait=True)
"""
        process=subprocess.run([sys.executable,'-c',script,str(rs.ROOT),self.temp.name,self.rid],
                               capture_output=True,text=True,timeout=15,check=True)
        observed=json.loads(process.stdout)
        self.assertEqual(observed['before_status'],'queued')
        self.assertEqual(observed['owner_pid'],os.getpid())
        self.assertTrue(observed['cancel_requested'])
        with self.assertRaises(rs.StopRun) as caught:
            self.service._check(self.rid)
        self.assertEqual(caught.exception.status,'cancelled')


if __name__=='__main__':unittest.main()
