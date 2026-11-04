"""Live progress must not change persisted usage or the actual time budget."""
import json
import os
from pathlib import Path
import sys
import tempfile
import unittest
from unittest.mock import patch

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
import research_service as rs


class LiveTimeTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.svc = rs.ResearchService(self.temp.name, recover=False)
        self.rid = self.svc.create(dict(mode='single', question='Controlled live time check',
                                      budget=dict(max_calls=8, timeout_seconds=600)), start=False)['id']
        self.svc.update(self.rid, usage=dict(calls=0, total_tokens=0, elapsed_seconds=37))

    def tearDown(self):
        self.svc.pool.shutdown(wait=True)
        self.temp.cleanup()

    def test_polling_adds_only_current_worker_segment_without_persisting_it(self):
        self.svc.update(self.rid, status='running')
        self.svc._started[self.rid] = 100
        saved = (self.svc.folder(self.rid) / 'run.json').read_bytes()
        with patch.object(rs.time, 'monotonic', return_value=165):
            self.assertEqual(self.svc.detail(self.rid)['live_elapsed_seconds'], 102)
            self.assertEqual(self.svc.detail(self.rid)['live_elapsed_seconds'], 102)
            self.assertEqual(self.svc._check(self.rid), 498)
        with patch.object(rs.time, 'monotonic', return_value=166.125):
            self.assertEqual(self.svc.detail(self.rid)['live_elapsed_seconds'], 103.125)
        self.assertEqual((self.svc.folder(self.rid) / 'run.json').read_bytes(), saved)
        self.assertEqual(self.svc.get(self.rid)['usage']['elapsed_seconds'], 37)
        self.assertNotIn('live_elapsed_seconds', self.svc.get(self.rid))

    def test_terminal_result_still_counts_uncommitted_publication_segment(self):
        self.svc.update(self.rid, status='complete')
        self.svc._started[self.rid] = 100
        with patch.object(rs.time, 'monotonic', return_value=165):
            self.assertEqual(self.svc.detail(self.rid)['live_elapsed_seconds'], 102)

    def test_queued_or_foreign_run_does_not_use_wall_clock_since_creation(self):
        for status in ('draft', 'queued', 'running', 'cancelled', 'complete'):
            self.svc.update(self.rid, status=status)
            self.assertEqual(self.svc.detail(self.rid)['live_elapsed_seconds'], 37)
        self.svc._started[self.rid] = 0
        self.svc.update(self.rid, status='running', owner_pid=os.getpid() + 100000)
        self.assertEqual(self.svc.detail(self.rid)['live_elapsed_seconds'], 37)

    def test_worker_cleanup_freezes_total_and_resume_adds_one_new_segment(self):
        clock = [100.0]

        def controlled_stop(_):
            clock[0] += 5
            raise rs.StopRun('cancelled', 'Controlled unit-test stop')

        with patch.object(rs.time, 'monotonic', side_effect=lambda: clock[0]), \
                patch.object(self.svc, '_retrieve', side_effect=controlled_stop), \
                patch.object(self.svc, '_record_transition_result'), \
                patch.object(self.svc, '_artifact_manifest', return_value=[]):
            self.svc._work(self.rid)
            self.assertNotIn(self.rid, self.svc._started)
            self.assertEqual(self.svc.detail(self.rid)['live_elapsed_seconds'], 42)
            clock[0] += 1000  # Time waiting between attempts is not research time.
            self.assertEqual(self.svc.detail(self.rid)['live_elapsed_seconds'], 42)
            self.svc._work(self.rid)
            self.assertNotIn(self.rid, self.svc._started)
            self.assertEqual(self.svc.detail(self.rid)['live_elapsed_seconds'], 47)
        persisted = json.loads((self.svc.folder(self.rid) / 'run.json').read_text(encoding='utf-8'))
        self.assertEqual(persisted['usage']['elapsed_seconds'], 47)
        self.assertNotIn('live_elapsed_seconds', persisted)

    def test_manifest_failure_preserves_time_and_stops_the_live_clock(self):
        clock = [100.0]

        def controlled_stop(_):
            clock[0] = 105.0
            raise rs.StopRun('cancelled', 'Controlled unit-test stop')

        with patch.object(rs.time, 'monotonic', side_effect=lambda: clock[0]), \
                patch.object(self.svc, '_retrieve', side_effect=controlled_stop), \
                patch.object(self.svc, '_record_transition_result'), \
                patch.object(self.svc, '_artifact_manifest', side_effect=OSError('Manifest unreadable')):
            with self.assertRaisesRegex(OSError, 'Manifest unreadable'):
                self.svc._work(self.rid)
            self.assertNotIn(self.rid, self.svc._started)
            clock[0] = 1000
            self.assertEqual(self.svc.detail(self.rid)['live_elapsed_seconds'], 42)

    def test_failed_usage_write_cannot_leave_a_running_clock(self):
        update = self.svc.update

        def reject_usage(run_id, **fields):
            if 'usage' in fields:
                raise OSError('Usage write rejected')
            return update(run_id, **fields)

        with patch.object(self.svc, '_retrieve', side_effect=rs.StopRun('cancelled', 'Test stop')), \
                patch.object(self.svc, '_record_transition_result'), \
                patch.object(self.svc, 'update', side_effect=reject_usage):
            with self.assertRaisesRegex(OSError, 'Usage write rejected'):
                self.svc._work(self.rid)
        self.assertNotIn(self.rid, self.svc._started)
        # The write failure propagates; the API reports the last persisted total,
        # not an ever-growing fictitious active segment.
        self.assertEqual(self.svc.detail(self.rid)['live_elapsed_seconds'], 37)


if __name__ == '__main__':
    unittest.main()
