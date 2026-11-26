from pathlib import Path
import sys
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))
from archive_fixture import isolated_lean_available
from research_lean_files import LeanFiles
from research_source_context import verify_candidate


@unittest.skipUnless(isolated_lean_available(), 'Prepared Lean, mathlib and sandbox-exec or bubblewrap required')
class SourceContextTests(unittest.TestCase):
    def test_replays_original_module_and_rejects_a_changed_definition(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            store = LeanFiles(root / 'lean-files')
            item = store.upload('Counter.lean', b'def counter (n : Nat) := n + 1\n')
            source = store.evidence(item['id'])
            statement = 'counter 0 = 1'
            accepted = verify_candidate(root, [source], 'import Counter\ntheorem initial : counter 0 = 1 := rfl\n',
                                        'initial', root / 'first', statement)
            self.assertTrue(accepted['success'], accepted.get('error'))
            self.assertEqual(accepted['source_check']['declarations'], ['counter'])
            cert = accepted['kernel_recheck']
            self.assertEqual(cert['checked'], ['counter', 'initial'])
            self.assertEqual(set(cert['module_sha256']), {'Counter', 'AMRResult'})
            name, archive = store.for_run({'result':{'verification':accepted}}, root)
            checked = store.upload(name, archive, 'initial', statement)
            self.assertEqual(checked['status'], 'verified', checked.get('error'))
            changed = verify_candidate(root, [source], 'import Counter\ndef counter (_ : Nat) := 0\n'
                                       'theorem initial : counter 0 = 0 := rfl\n', 'initial', root / 'second', 'counter 0 = 0')
            self.assertFalse(changed['success'])
            unrelated = verify_candidate(root, [source], 'import Counter\ntheorem identity : True := True.intro\n',
                                         'identity', root / 'third', 'True')
            self.assertEqual(unrelated['source_check']['status'], 'unrelated')
