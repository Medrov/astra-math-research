"""Real native subprocess checks for ownership, exclusion and cancellation."""
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import time
import unittest

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))
from platform_support import lock_file, unlock_file, process_exists, terminate_process_tree


def alive(pid):
    try:
        return process_exists(pid)
    except ProcessLookupError:
        return False


class NativeProcessTests(unittest.TestCase):
    def test_liveness_probe_does_not_terminate_worker(self):
        child = subprocess.Popen([sys.executable, '-c', 'import time; time.sleep(60)'],
                                 start_new_session=True)
        try:
            self.assertTrue(process_exists(child.pid))
            self.assertIsNone(child.poll())
        finally:
            terminate_process_tree(child)
        self.assertIsNotNone(child.poll())
        self.assertFalse(alive(child.pid))

    @unittest.skipUnless(os.name == 'nt', 'Native Windows descendant termination')
    def test_cancellation_terminates_worker_and_descendant(self):
        with tempfile.TemporaryDirectory() as temp:
            pid_file = Path(temp) / 'descendant.txt'
            code = """import pathlib, subprocess, sys, time
child = subprocess.Popen([sys.executable, '-c', 'import time; time.sleep(60)'])
pathlib.Path(sys.argv[1]).write_text(str(child.pid))
time.sleep(60)
"""
            parent = subprocess.Popen([sys.executable, '-c', code, str(pid_file)],
                                      start_new_session=True)
            try:
                deadline = time.monotonic() + 10
                while not pid_file.exists() and parent.poll() is None and time.monotonic() < deadline:
                    time.sleep(0.05)
                self.assertTrue(pid_file.exists(), 'Worker did not start its descendant')
                descendant = int(pid_file.read_text())
                self.assertTrue(process_exists(descendant))
                terminate_process_tree(parent)
                self.assertFalse(alive(descendant))
                self.assertIsNotNone(parent.poll())
            finally:
                terminate_process_tree(parent)


class NativeLockTests(unittest.TestCase):
    def test_nonblocking_lock_excludes_another_process_and_releases(self):
        script = """import pathlib, sys
sys.path.insert(0, sys.argv[1])
from platform_support import lock_file, unlock_file
with pathlib.Path(sys.argv[2]).open('a') as stream:
    try:
        lock_file(stream, blocking=False)
    except BlockingIOError:
        raise SystemExit(42)
    unlock_file(stream)
"""
        with tempfile.TemporaryDirectory() as temp:
            path = Path(temp) / 'exclusive.lock'
            command = [sys.executable, '-X', 'utf8', '-c', script, str(ROOT), str(path)]
            with path.open('a') as stream:
                lock_file(stream)
                try:
                    self.assertEqual(subprocess.run(command, timeout=10).returncode, 42)
                finally:
                    unlock_file(stream)
                self.assertEqual(subprocess.run(command, timeout=10).returncode, 0)

    def test_blocking_lock_preserves_concurrent_process_updates(self):
        script = """import pathlib, sys, time
sys.path.insert(0, sys.argv[1])
from platform_support import lock_file, unlock_file
root = pathlib.Path(sys.argv[2])
for _ in range(20):
    with (root / 'state.lock').open('a') as stream:
        lock_file(stream)
        try:
            value = int((root / 'counter').read_text())
            time.sleep(0.002)
            (root / 'counter').write_text(str(value + 1))
        finally:
            unlock_file(stream)
"""
        with tempfile.TemporaryDirectory() as temp:
            (Path(temp) / 'counter').write_text('0')
            command = [sys.executable, '-X', 'utf8', '-c', script, str(ROOT), temp]
            workers = [subprocess.Popen(command, start_new_session=True) for _ in range(2)]
            try:
                for worker in workers:
                    self.assertEqual(worker.wait(timeout=15), 0)
                self.assertEqual((Path(temp) / 'counter').read_text(), '40')
            finally:
                for worker in workers:
                    terminate_process_tree(worker)


if __name__ == '__main__':
    unittest.main()
