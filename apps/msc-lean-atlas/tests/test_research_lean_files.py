import hashlib
import io
import json
from pathlib import Path
import stat
import sys
import tempfile
import threading
import time
import unittest
from unittest import mock
import zipfile

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))
from archive_fixture import isolated_lean_available
import research_lean_files as files


def zip_bytes(items):
    out = io.BytesIO()
    with zipfile.ZipFile(out, 'w', zipfile.ZIP_DEFLATED) as archive:
        for name, data in items:
            archive.writestr(name, data)
    return out.getvalue()


class Fixture(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)
        self.svc = files.LeanFiles(self.root / 'uploads')


class ValidationTests(Fixture):
    def test_rejects_unsupported_uploads_before_storage(self):
        symlink = zipfile.ZipInfo('Link.lean')
        symlink.external_attr = (stat.S_IFLNK | 0o777) << 16
        cases = [
            ('../outside.lean', b'def a := 1'), ('a.pdf', b'%PDF'), ('a.zip', b'invalid'),
            ('a.zip', zip_bytes([('../A.lean', 'def a := 1')])),
            ('a.zip', zip_bytes([('A.lean', 'def a := 1'), ('lakefile.lean', 'import Lake')])),
            ('a.zip', zip_bytes([(symlink, '/dev/null')])),
            ('a.zip', zip_bytes([('a.lean', 'def x := 1'), ('A.lean', 'def y := 1')])),
            ('a.zip', zip_bytes([('A.lean', 'import B\ndef x := 1'), ('B.lean', 'import A\ndef y := 1')])),
            ('a.zip', zip_bytes([('A.lean', 'a' * (files.MAX_FILE_BYTES + 1))])),
            ('A.lean', b'import Unpinned.Package\n'), ('A.lean', b'#eval IO.println 37'),
            ('A.lean', b'theorem bad : False := by sorry')
        ]
        for name, raw in cases:
            with self.subTest(name=name, size=len(raw)), self.assertRaises(ValueError):
                self.svc.upload(name, raw)
        self.assertFalse(self.svc.root.exists())

    def test_download_follows_the_run_across_checkouts_and_checks_original_bytes(self):
        folder = self.root / 'current' / ('a' * 32)
        checked = folder / 'composition' / 'v0'
        checked.mkdir(parents=True)
        original = self.root / 'old' / folder.name / 'composition' / 'v0'
        original.mkdir(parents=True)
        for name, raw in [('Candidate.lean', b'theorem t : True := trivial'), ('sources.zip', b'checked bundle')]:
            with self.subTest(name=name):
                (original / name).write_bytes(raw)
                (checked / name).write_bytes(raw)
                receipt = dict(success=True, target_preserved=True, audit={'status':'passed'}, workspace=str(original))
                digest = hashlib.sha256(raw).hexdigest()
                if name.endswith('.zip'):
                    receipt.update(bundle_file=name, bundle_sha256=digest)
                else:
                    receipt.update(source_sha256=digest)
                run = {'result':{'verification':receipt}}
                self.assertEqual(self.svc.for_run(run, folder), (name, raw))
                receipt['workspace'] = 'C:\\archive\\' + folder.name + '\\composition\\v0'
                self.assertEqual(self.svc.for_run(run, folder), (name, raw))
                receipt['workspace'] = str(original)
                (checked / name).write_bytes(b'modified')
                with self.assertRaisesRegex(ValueError, 'сумма'):
                    self.svc.for_run(run, folder)
                (checked / name).unlink()
                # The old checkout still contains matching bytes, but is never opened.
                with self.assertRaisesRegex(ValueError, 'отсутствует'):
                    self.svc.for_run(run, folder)
                receipt['workspace'] = str(folder / '..' / '..' / 'old' / folder.name / 'composition' / 'v0')
                with self.assertRaisesRegex(ValueError, 'отсутствует'):
                    self.svc.for_run(run, folder)

    def test_invalid_and_missing_ids(self):
        with self.assertRaises(ValueError):
            self.svc.get('../')
        with self.assertRaises(FileNotFoundError):
            self.svc.get('0' * 32)

    def test_secondary_imports_determine_order_and_cycles(self):
        source = [('Result.lean', 'import Std Helper\n'), ('Helper.lean', 'theorem okay : True := trivial')]
        self.assertEqual([m['module'] for m in files._modules('set.zip', zip_bytes(source))], ['Helper', 'Result'])
        with self.assertRaisesRegex(ValueError, 'Циклические импорты'):
            files._modules('loop.zip', zip_bytes(source[:1] + [('Helper.lean', 'import Result\n')]))

    def test_cancellation_during_slot_wait(self):
        busy = threading.BoundedSemaphore(1)
        busy.acquire()
        stop = threading.Event()
        timer = threading.Timer(.2, stop.set)
        timer.start()
        self.addCleanup(timer.cancel)
        with mock.patch.object(files, 'SLOTS', busy):
            before = time.monotonic()
            result = self.svc.upload('Demo.lean', b'theorem okay : True := trivial', cancelled=stop)
            self.assertLess(time.monotonic() - before, 3)
        self.assertEqual(result['status'], 'cancelled')
        self.assertFalse(result['target_preserved'])
        self.assertFalse(busy.acquire(blocking=False))
        busy.release()


@unittest.skipUnless(isolated_lean_available(), 'Prepared Lean, mathlib and sandbox-exec or bubblewrap required')
class RealChecks(Fixture):
    def test_cancellation_kills_running_compiler(self):
        child = []
        original = files.subprocess.Popen
        def spawn(*args, **kwargs):
            proc = original(*args, **kwargs)
            if 'import time; time.sleep(60)' in args[0]:
                child.append(proc)
            return proc
        stub = [sys.executable, '-I', '-c', 'import time; time.sleep(60)']
        with mock.patch.object(files, '_isolated_command', return_value=stub), mock.patch.object(files.subprocess, 'Popen', spawn):
            result = self.svc.upload('Demo.lean', b'theorem okay : True := trivial', cancelled=lambda: bool(child))
        self.assertEqual(result['status'], 'cancelled', result)
        self.assertEqual(len(child), 1)
        self.assertIsNotNone(child[0].returncode)

    def test_scratch_modules_checked_in_dependency_order_archive_roundtrips(self):
        parts = [('archive/Goal.lean', 'import Base\ntheorem demo (n : Nat) : twice n = n + n := rfl\n'),
                 ('archive/Base.lean', 'def twice (n : Nat) := n + n\n')]
        report = self.svc.upload('Sources.zip', zip_bytes(parts), 'demo', '∀ n : Nat, twice n = n + n')
        self.assertEqual(report['status'], 'verified', report)
        self.assertTrue(report['target_preserved'])
        self.assertEqual([f['name'] for f in report['files']], ['Base.lean', 'Goal.lean'])
        self.assertIn('twice', next(d for d in report['declarations'] if d['name'] == 'demo')['type_dependencies'])
        aid = report['id']
        self.assertEqual(self.svc.evidence(aid)['order'], ['Base', 'Goal'])
        name, content = self.svc.download(aid)
        self.assertEqual(name, 'Sources.zip')
        replay = self.svc.upload(name, content)
        self.assertEqual(replay['status'], 'compiled', replay)
        self.assertFalse(replay['target_preserved'])
        self.assertEqual(replay['files'], report['files'])

    def test_wrong_target_and_input_tampering(self):
        raw = b'theorem demo : True := True.intro\n'
        report = self.svc.upload('Demo.lean', raw, 'demo', 'False')
        self.assertEqual(report['status'], 'failed')
        self.assertTrue(report['compilation_success'])
        self.assertFalse(report['target_preserved'])
        with self.assertRaises(ValueError):
            self.svc.evidence(report['id'])
        (self.svc.root / report['id'] / 'original').write_bytes(b'-- changed')
        with self.assertRaises(ValueError):
            self.svc.recheck(report['id'])

    def test_single_file_recheck_and_project_config_excluded(self):
        raw = b'theorem demo : True := True.intro\n'
        report = self.svc.upload('Demo.lean', raw)
        self.assertEqual(report['status'], 'compiled', report)
        self.assertEqual(self.svc.download(report['id']), ('Demo.lean', raw))
        self.assertEqual(self.svc.recheck(report['id'])['files'], report['files'])
        self.assertEqual(self.svc.get(report['id'])['status'], 'compiled')

    def test_program_bundle_rechecks_colliding_declarations_independently(self):
        runs = {}
        for i, suffix in enumerate(['one', 'two'], 1):
            raw = f'def weight := {i}\ntheorem {suffix} : weight = {i} := rfl\n'.encode()
            target, statement = suffix, f'weight = {i}'
            folder = self.root / suffix / 'checked'
            folder.mkdir(parents=True)
            (folder / 'Candidate.lean').write_bytes(raw)
            runs[suffix] = {'result': {'verification': {'success': True, 'audit': {'status': 'passed'},
                             'target_preserved': True, 'expected_statement': statement, 'target': target,
                             'workspace': str(folder), 'source_sha256': hashlib.sha256(raw).hexdigest()}}}
        # The second run additionally relies on an uploaded module. Its original
        # module names must resolve inside its group, independently of run one.
        two_zip = zip_bytes([('Defs.lean', 'def weight := 2\n'),
                             ('SHAIMResult.lean', 'import Defs\ntheorem two : weight = 2 := rfl\n')])
        (self.root / 'two' / 'checked' / 'sources.zip').write_bytes(two_zip)
        two_report = runs['two']['result']['verification']
        two_report.update(bundle_file='sources.zip', bundle_sha256=hashlib.sha256(two_zip).hexdigest())

        class Runs:
            get = staticmethod(runs.__getitem__)
            folder = staticmethod(lambda run_id: self.root / run_id)

        tasks = [{'run_id': 'one', 'formal_outcome': 'proved'}, {'run_id': 'two', 'formal_outcome': 'refuted'}]
        name, bundle = self.svc.for_program({'tasks': tasks}, Runs())
        self.assertTrue(name.endswith('.zip'))
        report = self.svc.upload(name, bundle)
        self.assertEqual(report['status'], 'compiled', report)
        self.assertFalse(report['target_preserved'])
        self.assertEqual([r['target'] for r in report['checks']], ['one', 'two'])
        self.assertTrue(all(r['target_preserved'] and r['contract_source'] == 'bundle' for r in report['checks']))
        self.assertEqual(self.svc.evidence(report['id'])['bundle_format'], files.BUNDLE_FORMAT)
        with self.assertRaises(ValueError):
            self.svc.select_member(report['id'], -1)
        selected = self.svc.select_member(report['id'], 1)
        self.assertEqual(selected['status'], 'compiled', selected)
        self.assertFalse(selected['target_preserved'])
        self.assertTrue(selected['checks'][0]['target_preserved'])
        self.assertEqual(selected['origin']['id'], report['id'])
        self.assertIsNone(self.svc.evidence(selected['id'])['bundle_format'])
        self.assertEqual(self.svc.recheck(selected['id'])['checks'], selected['checks'])
        name2, bundle2 = self.svc.download(report['id'])
        replay = self.svc.upload(name2, bundle2, 'two', 'weight = 2')
        self.assertEqual(replay['status'], 'verified', replay)
        self.assertEqual(replay['files'], report['files'])
        name, raw = self.svc.for_program({'tasks': tasks[:1]}, Runs())
        self.assertEqual(name, 'Candidate.lean')
        self.assertIn(b'theorem one', raw)
        self.assertEqual(self.svc.for_program({'tasks': tasks[1:]}, Runs()), ('sources.zip', two_zip))

        with zipfile.ZipFile(io.BytesIO(bundle)) as archive:
            items = [(n, archive.read(n)) for n in archive.namelist()]
        manifest = json.loads(items[-1][1])
        manifest['entries'][0]['sources'][0]['sha256'] = '0' * 64
        with self.assertRaisesRegex(ValueError, 'сумма'):
            self.svc.upload('tampered.zip', zip_bytes(items[:-1] + [(files.BUNDLE_MANIFEST, json.dumps(manifest))]))


if __name__ == '__main__':
    unittest.main()
