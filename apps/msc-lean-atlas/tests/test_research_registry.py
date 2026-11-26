import json
from pathlib import Path
import sys
import tempfile
import time
import unittest
from unittest.mock import patch

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))
import lean_service
import research_registry as registry
from research_service import ResearchService

from archive_fixture import archive_fixture, GRAPH_RUN as SOURCE_RUN
SEED = 'TriangleEnergy.graph_energy_eq'
TARGET = 'TriangleEnergy.laplacian_mono_first_weight'


class DependencyTests(unittest.TestCase):
    def test_only_compiled_proof_edges_reaching_target_count(self):
        card = dict(name='A', declared_names=['A'], source_run_id='prior', source_sha256='fingerprint')
        def decl(name, dependencies, types=()):
            return dict(name=name, dependencies=dependencies, type_dependencies=types)
        declarations = [decl('unused', ['A']), decl('step', ['A']), decl('final', ['step', 'A'], ['A'])]
        edges = registry.proof_edges(card, declarations, 'final')
        self.assertEqual([(e['source'], e['target']) for e in edges], [('A', 'step')])
        self.assertEqual(registry.proof_edges(card, declarations, 'missing'), [])


class ArchiveTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)
        self.archive = archive_fixture(self.root)
        registry.refresh(self.root)
        self.seed = next(c for c in registry.search(self.root, SEED) if c['name'] == SEED)
        self.plan = json.loads((self.archive / 'plan.json').read_text())

    def test_archive_is_relocatable_repeatable_and_bound_to_source_hash(self):
        self.assertEqual(self.seed['source_run_id'], SOURCE_RUN)
        certificate = self.seed['kernel_recheck']
        self.assertIn(SEED, certificate['checked'])
        self.assertEqual(certificate['module_sha256'], {'Candidate': self.seed['source_sha256']})
        self.assertIn('theorem ' + SEED, registry.load_source(self.root, self.seed))
        registry.refresh(self.root)
        self.assertEqual(sum(c['name'] == SEED for c in registry.search(self.root, SEED)), 1)
        self.assertEqual(registry.search(self.root, SEED, exclude_run=SOURCE_RUN), [])
        (self.archive / self.seed['artifact']).write_text('theorem changed : True := by trivial')
        with self.assertRaisesRegex(ValueError, 'изменилась'):
            registry.load_source(self.root, self.seed)

    def test_legacy_compiler_receipt_gets_a_fresh_kernel_certificate(self):
        receipt_path = (self.archive / self.seed['artifact']).with_name('verification.json')
        receipt = json.loads(receipt_path.read_text())
        receipt.pop('kernel_recheck')
        receipt_path.write_text(json.dumps(receipt), encoding='utf-8')
        (self.archive / 'run.json').touch()
        registry.refresh(self.root)
        card = next(item for item in registry.search(self.root, SEED) if item['name'] == SEED)
        self.assertEqual(card['kernel_recheck']['module_sha256'], {'Candidate': receipt['source_sha256']})
        self.assertIn(SEED, card['kernel_recheck']['checked'])
        self.assertNotIn('kernel_recheck', json.loads(receipt_path.read_text()))

    def test_failed_new_receipt_is_not_downgraded_to_a_legacy_card(self):
        path = (self.archive / self.seed['artifact']).with_name('verification.json')
        receipt = json.loads(path.read_text())
        receipt['kernel_recheck'] = {'status':'failed'}
        path.write_text(json.dumps(receipt))
        (self.archive / 'run.json').touch()
        registry.refresh(self.root)
        self.assertNotIn(SEED, [c['name'] for c in registry.search(self.root, SEED)])

    def test_incompatible_context_and_name_collision_are_not_injected(self):
        run_id = 'a' * 32
        args = dict(query='монотонность энергии', cancelled=lambda: False)
        self.assertIsNone(registry.pin_candidate(self.root, run_id, dict(self.plan, prelude='def changed := 1'), **args))
        self.assertIsNone(registry.pin_candidate(self.root, run_id, self.plan, **args))
        plan = dict(self.plan, target_id=TARGET, nodes=[dict(id=TARGET,statement='True')])
        with patch.object(lean_service,'_prepare',return_value=({'lean_version':'different'},{})), \
             patch('research_lean.verify_candidate') as replay:
            self.assertIsNone(registry.pin_candidate(self.root, run_id, plan, **args))
            replay.assert_not_called()

    def test_bundle_receipt_is_not_a_standalone_proof_and_stale_rows_are_rebuilt(self):
        import sqlite3
        receipt_path = (self.archive / self.seed['artifact']).with_name('verification.json')
        report = json.loads(receipt_path.read_text())
        # A valid multi-module proof has a successful contract and audit too.
        report.update(bundle_file='sources.zip', bundle_sha256='a'*64)
        receipt_path.write_text(json.dumps(report))
        with sqlite3.connect(self.root/'verified-lemmas.sqlite') as db:
            db.execute('PRAGMA user_version=0')
        registry.refresh(self.root)
        self.assertNotIn(SEED,[c['name'] for c in registry.search(self.root,SEED)])

    def test_archive_keeps_checked_negation_linked_to_the_positive_task(self):
        folder = archive_fixture(self.root, 'strict_inequality')
        run = json.loads((folder/'run.json').read_text())
        target = 'StrictInequality.counterexample'
        base = '∀ a b : ℝ, 2 * a * b < a ^ 2 + b ^ 2'
        run['contract']['program_context'] = dict(program_id='c'*32,task_id='L2',revision=2,
                                                 direction='refute',base_statement=base)
        (folder/'run.json').write_text(json.dumps(run))
        registry.refresh(self.root)
        card = next(c for c in registry.search(self.root,target) if c['name']==target)
        self.assertEqual(card['statement'],'¬ (' + base + ')')
        self.assertEqual(card['refutation_of']['statement'],base)
        self.assertEqual(card['refutation_of']['task_id'],'L2')
        run['contract']['program_context']['base_statement'] = 'False'
        (folder/'run.json').write_text(json.dumps(run))
        registry.refresh(self.root)
        self.assertNotIn(target,[c['name'] for c in registry.search(self.root,target)])

    def test_older_qed_null_semantic_review_is_not_a_registry_entry(self):
        self.assertEqual(list(registry._cards(self.archive,dict(mode='qed',status='complete',outcome='proved',semantic_review=None))),[])
        self.assertEqual(list(registry._cards(self.archive,dict(mode='multi',status='complete',outcome='proved',semantic_review=None))),[])

    @unittest.skipUnless(Path(lean_service.default_context()['lean']).is_file(), 'Prepared Lean unavailable')
    def test_normal_second_run_replays_seed_and_records_actual_lean_dependency(self):
        target_type = """∀ (a b w12 w02 x0 x1 x2 : ℝ), a ≤ b →
  TriangleEnergy.laplacianForm a w12 w02 x0 x1 x2 ≤
  TriangleEnergy.laplacianForm b w12 w02 x0 x1 x2"""
        proof = """by
  intro a b w12 w02 x0 x1 x2 hab
  rw [← TriangleEnergy.graph_energy_eq a w12 w02 x0 x1 x2,
      ← TriangleEnergy.graph_energy_eq b w12 w02 x0 x1 x2]
  unfold TriangleEnergy.graphEnergy
  exact add_le_add_right (add_le_add_right
    (mul_le_mul_of_nonneg_right hab (sq_nonneg (x0 - x1))) _) _"""
        task = dict(target=TARGET, statement=target_type, imports=self.plan['imports'], prelude=self.plan['prelude'])
        plan = dict(target_id=TARGET, imports=task['imports'], prelude=task['prelude'],
                    nodes=[dict(id=TARGET, statement=target_type, dependencies=[], proof='')])
        calls = []

        def answer(run_id, role, prompt, *args, **kwargs):
            calls.append(role)
            if role == 'prove':
                self.assertIn('theorem ' + SEED + ' :', prompt)
            values = {'plan':plan, 'critic':{'verdict':'accept'}, 'prove':{'proof':proof},
                      'semantic_review':{'status':'aligned'}}
            return {'text':json.dumps(values[role])}

        service = ResearchService(self.root, recover=False)
        self.addCleanup(service.pool.shutdown)
        run = service.create({'mode':'multi', 'question':'Может ли уменьшиться энергия треугольника при увеличении веса первого ребра?'},
                             start=False, fixed_task=task, program_context={'program_id':'b' * 32, 'direction':'prove'})
        run_id = run['id']
        service._started[run_id] = time.monotonic()
        # This slice exercises research-service integration. The program's
        # own clock and live transport are exercised in their respective tests.
        with patch.object(service, '_check', return_value=600), patch.object(service, '_call', side_effect=answer):
            service._retrieve({'run_id':run_id})
            service._model_workflow(run_id)
            service._publish({'run_id':run_id})
        run = service.get(run_id)
        self.assertEqual(run['outcome'], 'proved')
        self.assertEqual(run['library_selected']['name'], SEED)
        self.assertEqual([(e['source'], e['target']) for e in run['library_dependencies']], [(SEED, TARGET)])
        self.assertEqual(calls, ['plan', 'critic', 'prove', 'semantic_review'])
        self.assertIn(TARGET, [c['name'] for c in registry.search(self.root, TARGET)])
        # A running program owns a replayed copy; removal or corruption in the
        # original archive cannot change an already pinned proof context.
        (self.archive / self.seed['artifact']).unlink()
        self.assertIn('theorem ' + SEED, registry.pinned_source(service.folder(run_id), plan, run['library_selected']))
        (service.folder(run_id) / run['library_selected']['replay_artifact']).write_text('damaged')
        with self.assertRaisesRegex(ValueError, 'изменилась'):
            registry.pinned_source(service.folder(run_id), plan, run['library_selected'])


if __name__ == '__main__':
    unittest.main()
