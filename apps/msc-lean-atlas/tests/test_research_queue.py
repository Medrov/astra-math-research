"""Shared local workers, expiring claims and durable task handover."""
from pathlib import Path
import multiprocessing
import sys
import tempfile
import threading
import time
import unittest
from unittest.mock import patch

sys.path.insert(0,str(Path(__file__).resolve().parents[1]))
from research_programs import ProgramService
from research_queue import LeaseLost
from research_service import ResearchService


def contender(root, label, barrier, results, stop):
    research = ResearchService(root=root,recover=False)
    service = ProgramService(research,recover=False,worker_id=label)
    barrier.wait(10)
    lease = service.queue.claim()
    if lease:
        # Simulate a live but stalled worker just after reserving/creating its child.
        with patch.object(research,'start'):
            service._step_claim(lease)
        child = service.get(lease.program_id)['tasks'][0]['run_id']
        results.put((label,lease,child))
    else:
        results.put((label,None,None))
    stop.wait(15)
    research.pool.shutdown()


class ResearchQueue(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.runs = ResearchService(root=self.tmp.name)
        self.programs = ProgramService(self.runs,recover=False,worker_id='server')

    def tearDown(self):
        self.runs.pool.shutdown()
        self.tmp.cleanup()

    def create(self):
        goal = dict(imports=['Init'],prelude='',target='Demo.claim',statement='False')
        return self.programs.create({'question':'Верно ли это утверждение?'},goal_task=goal,
                                    goal_direction='refute',start=False)['id']

    def test_two_processes_one_owner_and_fenced_handover_of_same_run(self):
        pid = self.create()
        ctx = multiprocessing.get_context('spawn')
        barrier, results, stop = ctx.Barrier(2), ctx.Queue(), ctx.Event()
        workers = [ctx.Process(target=contender,args=(self.tmp.name,name,barrier,results,stop)) for name in ('one','two')]
        for worker in workers:
            worker.start()
        try:
            records = [results.get(timeout=15) for _ in workers]
            winners = [r for r in records if r[1]]
            self.assertEqual(len(winners),1,records)
            label,old,run_id = winners[0]
            self.assertEqual(self.programs.get(pid)['tasks'][0]['lease']['worker_id'],label)
            self.assertIsNone(self.programs.queue.claim())
            with self.programs._db() as db:
                db.execute('UPDATE task_queue SET expires_at=0 WHERE program_id=?',(pid,))
            self.assertTrue(all(p.is_alive() for p in workers))
            self.assertEqual(self.programs.queue.list()[0]['status'],'ready')
            current = self.programs.queue.claim()
            self.assertNotEqual(current.token,old.token)
            self.assertFalse(self.programs.queue.renew(old))
            self.assertFalse(self.programs.queue.release(old))
            self.programs._worker_local.acting = old
            try:
                with self.assertRaises(LeaseLost), self.programs._edit(pid) as state:
                    state['reason'] = 'stale'
            finally:
                self.programs._worker_local.acting = None
            with patch.object(self.runs,'_work',side_effect=lambda rid:self.runs.update(rid,status='failed',error='test-result')):
                self.assertTrue(self.programs._step_claim(current))
                self.runs.futures[run_id].result(timeout=3)
                self.assertTrue(self.programs._step_claim(current))
            finished = self.programs.get(pid)
            self.assertEqual(finished['tasks'][0]['status'],'complete')
            self.assertEqual(finished['tasks'][0]['run_id'],run_id)
            self.assertEqual([r['id'] for r in self.runs.list_runs()],[run_id])
            self.assertFalse(self.programs.queue.list())
            events = [e for e in finished['events'] if e.get('kind','').startswith('lease_')]
            self.assertEqual([(e['kind'],e['generation']) for e in events],[('lease_acquired',1),('lease_reassigned',2)])
            self.assertEqual(events[-1]['previous_worker_id'],label)
        finally:
            stop.set()
            for worker in workers:
                worker.join(5)
            results.close()
            results.join_thread()

    def test_heartbeat_and_release_across_programs(self):
        first,second = self.create(),self.create()
        self.programs.queue.ttl = .3
        lease = self.programs.queue.claim()
        seen,finish = threading.Event(),threading.Event()
        def slow(*args):
            seen.set()
            finish.wait(3)
        with patch.object(self.programs,'_assign',side_effect=slow):
            worker = threading.Thread(target=self.programs._step_claim,args=(lease,))
            worker.start()
            try:
                self.assertTrue(seen.wait(2))
                time.sleep(.55)
                self.assertEqual(self.programs.queue.list(first)[0]['status'],'leased')
                other = self.programs.queue.claim()
                self.assertEqual(other.program_id,second)
                self.assertTrue(self.programs.queue.release(other))
                self.assertEqual(self.programs.queue.list(second)[0]['status'],'ready')
            finally:
                finish.set()
                worker.join(2)
        self.assertEqual(len([e for e in self.programs.get(first)['events'] if e.get('kind')=='lease_acquired']),1)
        self.programs.cancel(first)
        self.assertFalse(self.programs.queue.renew(lease))
        self.assertEqual([r['program_id'] for r in self.programs.queue.list()],[second])

    def test_already_running_child_survives_takeover_and_dead_owner_is_detected(self):
        pid = self.create()
        owner = self.programs.queue.claim()
        with patch.object(self.runs,'start'):
            self.programs._step_claim(owner)
        child = self.programs.get(pid)['tasks'][0]['run_id']
        self.runs.update(child,status='running',program_dispatched=True)
        with patch.object(self.runs,'start') as start:
            self.assertTrue(self.programs._step_claim(owner))
            start.assert_not_called()
        self.runs.update(child,owner_pid=999999999)
        with patch.object(self.runs,'_work',side_effect=lambda rid: self.runs.update(rid,status='failed')) as work:
            self.assertTrue(self.programs._step_claim(owner))
            self.runs.futures[child].result(timeout=3)
            work.assert_called_once_with(child)
