"""Regression tests for grounded pattern discovery and bounded continuation."""
import json
from pathlib import Path
import sys
import tempfile
import unittest
from unittest.mock import patch

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT))
from research_lean_files import LeanFiles
from research_patterns import handoff
from research_programs import ProgramService
from research_registry import source_prefix
from research_service import ResearchService
from research_source_context import verify_candidate

from archive_fixture import archive_fixture, isolated_lean_available, GRAPH_RUN as ARCHIVE


class Patterns(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)
        self.research = ResearchService(self.root,recover=False)
        self.addCleanup(self.research.pool.shutdown)
        self.programs = ProgramService(self.research,recover=False)

    def fixture_search(self):
        archive_fixture(self.root)
        return self.programs.create(dict(mode='patterns',context_case_id='graph_energy'),start=False)

    def card(self, **kw):
        return dict(dict(question='Когда исчезает энергия треугольника?', reason='Проверяем граничный случай.',
                         pattern='Равенство двух представлений и оценка снизу позволяют исследовать случай нулевой энергии.',
                         source_ids=['S1','S2'],direction='prove',target='Candidate.newPattern',
                         statement='∀ a b c : ℝ, TriangleEnergy.graphEnergy a b c 0 0 0 = 0',
                         imports=[],prelude='',revision_of='',dependencies=[],needs_sketch=False),**kw)

    def test_validates_real_seed_citations_and_preserves_distinct_observation(self):
        p=self.fixture_search()
        self.assertEqual(p['mode'],'patterns')
        self.assertGreaterEqual(len(p['pattern_sources']),2)
        self.assertTrue(all(i['url'].startswith('/api/research/runs/') for i in p['pattern_sources']))
        state=self.programs._state(p['id'])
        before=self.programs._planning_prompt(state)
        for bad in (['S1'],['S1','S1'],['S1','S999']):
            with self.assertRaisesRegex(ValueError,'ID'):
                self.programs._add_task(state,self.card(source_ids=bad))
        exact=p['pattern_sources'][0]['statement']
        with self.assertRaisesRegex(ValueError,'исходная декларация'):
            self.programs._add_task(state,self.card(statement=exact.replace('∀','∀   ')))
        with self.assertRaisesRegex(ValueError,'общую математическую'):
            self.programs._add_task(state,self.card(pattern='',reason='Надо проверить S1 и S2.'))
        observation='S1 и S2 связывают два выражения энергии. Из их равенства и оценки следует проверяемая гипотеза о нулевом весе.'
        self.assertTrue(self.programs._add_task(state,self.card(pattern='',reason=observation)))
        task=state['tasks'][0]
        self.assertEqual(task['pattern'],observation)
        self.assertIn('pattern_sources',before)
        self.assertIn(observation,self.programs._planning_prompt(state))
        self.assertEqual([s['id'] for s in handoff(state,task)['pattern_sources']],['S1','S2'])
        task.update(outcome='proved',status='complete')
        with self.assertRaisesRegex(ValueError,'уже проверена'):
            self.programs._add_task(state,self.card(statement=task['statement']+' '))

    def test_continuation_extends_from_actual_spend_exactly_once(self):
        p=self.fixture_search()
        pid=p['id']
        with self.programs._edit(pid) as state:
            self.programs._add_task(state,self.card())
            state['tasks'][0].update(status='complete',outcome='proved')
            state['rounds']=[dict(n=1,status='completed',tokens=123)]
            state.update(status='budget_exhausted',reason='Конец этапа.',deadline=0,
                         remaining=840.5,resolution={'task_ids':['L1']})
        with patch.object(self.programs,'_launch') as launch:
            resumed=self.programs.continue_patterns(pid,dict(max_calls=3,timeout_seconds=60),generation=0)
            replay=self.programs.continue_patterns(pid,dict(max_calls=3,timeout_seconds=60),generation=0)
            self.assertEqual(launch.call_count,1)
        self.assertEqual(resumed['pattern_generation'],1)
        self.assertEqual(resumed['pattern_goal'],3)
        self.assertEqual(resumed['budget'],dict(max_calls=4,timeout_seconds=119.5))
        self.assertEqual(replay['budget'],resumed['budget'])
        self.assertEqual(resumed['pattern_checked'],1)
        self.assertNotIn('resolution',resumed)
        restored=ProgramService(self.research,recover=False).get(pid)
        self.assertEqual(restored['pattern_sources'],p['pattern_sources'])
        self.assertEqual(restored['tasks'][0]['source_ids'],['S1','S2'])
        self.assertEqual(restored['events'][-1]['previous_resolution'],{'task_ids':['L1']})
        self.assertEqual(self.programs.list_programs('research'),[])
        self.assertEqual(self.programs.list_programs('patterns')[0]['id'],pid)

    def test_counterexample_uses_the_same_pattern_sources_and_counts_only_a_checked_outcome(self):
        state = self.programs._state(self.fixture_search()['id'])
        self.programs._add_task(state, self.card())
        self.programs._prepare_counterexamples(state, state['tasks'][:])
        original, scout = state['tasks']
        self.assertEqual(handoff(state, original), handoff(state, scout))
        self.assertEqual((original['version'], original['fingerprint']), (scout['version'], scout['fingerprint']))
        self.assertEqual(scout['counterexample_for'], original['id'])
        self.assertEqual(scout['direction'], 'refute')
        self.assertEqual(original['outcome'], 'unknown')

    def test_citations_and_one_checked_candidate_cannot_close_a_two_pattern_search(self):
        pid=self.fixture_search()['id']
        with self.programs._edit(pid) as state:
            self.programs._add_task(state,self.card())
            state['tasks'][0].update(status='complete',outcome='proved')
        early={'decision':'answered','evidence_ids':['L1'],'reason':'Мы нашли закономерность.','tasks':[]}
        empty={'decision':'stalled','evidence_ids':[],'reason':'Не удалось предложить другую гипотезу.','tasks':[]}
        replies=[dict(status='completed',text=json.dumps(d),usage={}) for d in [early,empty]]
        with patch('research_codex.run_task',side_effect=replies) as model:
            self.programs._worker(pid)
        result=self.programs.get(pid)
        self.assertEqual(model.call_count,2)
        self.assertEqual(result['pattern_checked'],1)
        self.assertEqual(result['status'],'stalled')
        self.assertNotIn('resolution',result)

    def test_last_allowed_call_closes_stage_before_dispatching_queued_work(self):
        pid=self.fixture_search()['id']
        with self.programs._edit(pid) as state:
            self.programs._add_task(state,self.card())
            self.programs._add_task(state,self.card(target='Other',statement='∀ n : Nat, n > 0',direction='refute'))
            self.programs._add_task(state,self.card(target='Next',statement='True'))
            state['tasks'][0].update(status='complete',outcome='proved')
            state['tasks'][1].update(status='complete',outcome='refuted')
            state['budget']['max_calls']=1
            state['rounds']=[dict(n=1,status='completed',tokens=17)]
            state['deadline']=1
        with patch.object(self.programs,'_assign') as assign, patch('research_codex.run_task') as model:
            self.programs._worker(pid)
        assign.assert_not_called()
        model.assert_not_called()
        result=self.programs.get(pid)
        self.assertEqual(result['status'],'complete')
        self.assertEqual(result['usage']['calls'],result['budget']['max_calls'])
        self.assertEqual(result['resolution']['task_ids'],['L1','L2'])
        self.assertEqual(result['resolution']['assessment'],'checked_patterns')
        self.assertIn('опровергнуто 1',result['resolution']['summary'])
        self.assertEqual(result['tasks'][2]['status'],'queued')
        with patch.object(self.programs,'_launch'):
            resumed=self.programs.continue_patterns(pid,generation=0)
        self.assertEqual(resumed['pattern_goal'],4)
        self.assertEqual(resumed['tasks'][2]['status'],'queued')

    @unittest.skipUnless(isolated_lean_available(), 'Prepared Lean, mathlib and sandbox-exec or bubblewrap required')
    def test_case_and_attachment_are_both_available_to_lean(self):
        archive_fixture(self.root)
        store=LeanFiles(self.root/'lean-files')
        item=store.upload('Weights.lean','import Mathlib.Data.Real.Basic\ndef Extra.weight : ℝ := 0\n'.encode())
        sources=[store.evidence(item['id'])]
        program=self.programs.create(dict(mode='patterns',context_case_id='graph_energy'),sources=sources,start=False)
        state=self.programs._state(program['id'])
        self.assertEqual({s['kind'] for s in state['pattern_sources']},{'attachment','archive'})
        env=state['environment']
        self.assertIn('Weights',env['imports'])
        target='extra_weight_zero'
        statement='TriangleEnergy.graphEnergy Extra.weight 0 0 1 2 3 = 0'
        candidate=source_prefix(env)+'theorem '+target+' : '+statement+' := by simp [TriangleEnergy.graphEnergy, Extra.weight]\n'
        report=verify_candidate(self.root,sources,candidate,target,self.root/'combined',statement)
        self.assertTrue(report['success'],report.get('error'))
        self.assertIn('Extra.weight',report['source_check']['declarations'])

    def test_old_records_remain_research_even_without_mode(self):
        p=self.programs.create(dict(question='Исследовать оценку.'),start=False)
        with self.programs._edit(p['id']) as state:
            state.pop('mode')
        self.assertEqual(self.programs.get(p['id'])['mode'],'research')
        self.assertEqual(self.programs.list_programs('research')[0]['mode'],'research')
        with self.assertRaisesRegex(ValueError,'паттернов'):
            self.programs.continue_patterns(p['id'],{},generation=0)

    @unittest.skipUnless(isolated_lean_available(), 'Prepared Lean, mathlib and sandbox-exec or bubblewrap required')
    def test_real_uploaded_declarations_exclude_generated_helpers_and_duplicate_files(self):
        files=LeanFiles(self.root/'lean-files')
        source=b'def Pattern.double (n : Nat) : Nat := n+n\n'
        first=files.upload('Numbers.lean',source)
        duplicate=files.upload('Numbers.lean',source)
        self.assertEqual(first['status'],'compiled',first.get('error'))
        with self.assertRaisesRegex(ValueError,'минимум две'):
            self.programs.create({'mode':'patterns'},sources=[files.evidence(first['id']),files.evidence(duplicate['id'])],start=False)
        theorem=files.upload('Last.lean',b'theorem Pattern.left_zero (n : Nat) : 0+n=n := Nat.zero_add n\n')
        checked=[files.evidence(first['id']),files.evidence(theorem['id'])]
        p=self.programs.create({'mode':'patterns'},sources=checked,start=False)
        self.assertEqual({s['name'] for s in p['pattern_sources']},{'Pattern.double','Pattern.left_zero'})
        self.assertEqual({s['attachment_id'] for s in p['pattern_sources']},{first['id'],theorem['id']})
        self.assertTrue(all(s['url'].startswith('/api/research/lean-files/') for s in p['pattern_sources']))

    def test_scope_only_uses_verified_results_from_selected_msc(self):
        archive_fixture(self.root)
        p=self.programs.create(dict(mode='patterns',msc_codes=['05']),start=False)
        self.assertEqual(p['msc_codes'],['05'])
        self.assertEqual({s['source_run_id'] for s in p['pattern_sources']},{ARCHIVE})
        with self.assertRaisesRegex(ValueError,'MSC'):
            self.programs.create(dict(mode='patterns',msc_codes=['made-up']),start=False)


if __name__=='__main__':
    unittest.main()
