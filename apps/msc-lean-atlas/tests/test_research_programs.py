"""Research-program lifecycle, proof polarity and durable call accounting."""
import json
from pathlib import Path
import sys
import tempfile
import threading
import time
import unittest
from unittest.mock import patch

sys.path.insert(0,str(Path(__file__).resolve().parents[1]))
from research_programs import ProgramService, _certified, _fixed, next_task
from research_service import ResearchService

GOAL = dict(target='Demo.falseClaim',statement='∀ n : Nat, n = 0',prelude='',imports=['Init'])
QUESTION = 'Каждое ли натуральное число равно нулю?'


def candidate(**extra):
    return dict(dict(GOAL,question=QUESTION,direction='refute',reason='Проверить на числе один.',
                     revision_of='',dependencies=[],needs_sketch=True),**extra)


def answer(payload,status='completed'):
    return dict(status=status,text=json.dumps(payload),usage={'last':{'totalTokens':3}},
                thread_id='local-test',turn_id='recorded-test')


class Programs(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.runs = ResearchService(root=self.tmp.name)
        self.programs = ProgramService(self.runs,recover=False)

    def tearDown(self):
        self.runs.pool.shutdown()
        self.tmp.cleanup()

    def create(self,**extra):
        return self.programs.create(dict(question=QUESTION,**extra),start=False)

    def test_full_workflow_checks_exact_negation_in_lean_and_hands_off_qed(self):
        program_id = self.create(use_qed=True)['id']
        keys = []
        def model(prompt,folder,**kw):
            key = folder.name
            keys.append(key)
            if key=='proposal-1':
                return answer(dict(decision='propose', reason='',evidence_ids=[],tasks=[candidate()]))
            if key=='qed-survey':
                return answer(dict(body='Нужен контрпример.',difficulty='Easy',answer_kind='counterexample',
                                   proof='Один является контрпримером.'))
            if key=='plan':
                self.assertIn('Один является контрпримером.',prompt)
                fixed = _fixed(candidate())
                return answer(dict(target_id=fixed['target'],imports=fixed['imports'],prelude='',nodes=[
                    dict(id=fixed['target'],statement=fixed['statement'],dependencies=[],title='Лемма',proof='')]))
            if key=='critic-v0':
                return answer(dict(verdict='accept',reason='Утверждение зафиксировано.',issues=[]))
            if key.startswith('prove-v0'):
                return answer(dict(proof='by\n  intro h\n  have bad := h 1\n  contradiction',explanation=''))
            if key=='semantic-review-v0':
                return answer(dict(status='aligned',reason='Опровергнуто исходное утверждение.',limitations=[]))
            if key=='proposal-2':
                self.assertIn('refuted',prompt)
                return answer(dict(decision='answered',reason='Есть проверенный контрпример.',evidence_ids=['L1'],tasks=[]))
            self.fail(key)
        with patch('research_codex.run_task',side_effect=model):
            self.programs._worker(program_id)
        result = self.programs.get(program_id)
        task = result['tasks'][0]
        self.assertEqual(result['status'],'complete',result)
        self.assertEqual(task['outcome'],'refuted',task)
        self.assertEqual(task['formal_outcome'],'refuted')
        self.assertEqual(len(keys),7,keys)
        self.assertEqual(result['usage']['calls'],len(keys))
        self.assertEqual(result['usage']['total_tokens'],3*len(keys))
        self.assertEqual(result['resolution']['task_ids'],['L1'])
        run = self.runs.get(task['run_id'])
        self.assertEqual(run['outcome'],'refuted')
        self.assertTrue(run['result']['verification']['target_preserved'])
        self.assertEqual(_certified(dict(candidate(),statement='False'),run),('unknown','unknown'))
        with self.assertRaises(ValueError):
            self.runs.start(run['id'])

    def test_cancel_resume_after_dispatch_reuses_cached_proposal(self):
        program_id = self.create(budget=dict(max_calls=1,timeout_seconds=30))['id']
        entered,release = threading.Event(),threading.Event()
        def model(prompt,folder,**kw):
            entered.set()
            release.wait(3)
            return answer(dict(decision='stalled',reason='Нет дополнительных задач.',tasks=[],evidence_ids=[]))
        with patch('research_codex.run_task',side_effect=model) as calls:
            worker = threading.Thread(target=self.programs._worker,args=(program_id,))
            worker.start()
            self.assertTrue(entered.wait(3))
            self.assertEqual(self.programs.cancel(program_id)['status'],'paused')
            release.set()
            worker.join(4)
            self.assertFalse(worker.is_alive())
            self.assertEqual(self.programs.get(program_id)['status'],'paused')
            other = ProgramService(self.runs,recover=False)
            with patch.object(other,'_launch'):
                other.resume(program_id)
            other._worker(program_id)
            self.assertEqual(calls.call_count,1)
            self.assertEqual(other.get(program_id)['status'],'stalled')

    def test_program_respects_shared_budget_before_starting_child(self):
        program_id = self.create(budget=dict(max_calls=1,timeout_seconds=60))['id']
        proposal = answer(dict(decision='propose',reason='',evidence_ids=[],tasks=[candidate()]))
        with patch('research_codex.run_task',return_value=proposal):
            self.programs._worker(program_id)
        result = self.programs.get(program_id)
        self.assertEqual(result['status'],'budget_exhausted')
        self.assertEqual(result['usage']['calls'],1)
        self.assertIsNone(result['tasks'][0]['run_id'])

    def test_unverified_completion_sent_back_once_with_diagnostics(self):
        program_id = self.create()['id']
        def model(prompt,folder,**kw):
            if folder.name=='proposal-2':
                self.assertIn('без проверенного свидетельства',prompt)
            return answer(dict(decision='answered',reason='Агент утверждает, что готово.',evidence_ids=[],tasks=[]))
        with patch('research_codex.run_task',side_effect=model) as calls:
            self.programs._worker(program_id)
        result = self.programs.get(program_id)
        self.assertEqual(result['status'],'stalled')
        self.assertEqual(calls.call_count,2)
        self.assertEqual(result['usage']['total_tokens'],6)

    def test_cancelled_child_continues_same_run_and_reserves_one_new_turn(self):
        program_id = self.programs.create(dict(question=QUESTION),goal_task=GOAL,goal_direction='refute',start=False)['id']
        with self.programs._edit(program_id) as state:
            task = state['tasks'][0]
            self.assertEqual(_fixed(task)['statement'],'¬ ('+GOAL['statement']+')')
        run = self.runs.create(dict(question=QUESTION,mode='multi'),fixed_task=_fixed(task),program_context={
            'program_id':program_id,'task_id':task['id'],'direction':'refute','base_statement':task['statement']},start=False)
        run_id = run['id']
        self.runs.cancel_flags[run_id] = threading.Event()
        self.runs._started[run_id] = time.monotonic()
        cancelled = dict(answer({},status='cancelled'),interrupt_requested=True)
        with patch('research_codex.run_task',side_effect=[cancelled,answer({'verdict':'accept'})]) as model:
            with self.assertRaisesRegex(Exception,'Codex'):
                self.runs._call(run_id,'critic','fixed prompt','critic-v0')
            self.programs.cancel(program_id)
            with patch.object(self.programs,'_launch'):
                self.programs.resume(program_id)
            self.runs.update(run_id,program_resume_generation=1)
            result = self.runs._call(run_id,'critic','fixed prompt','critic-v0')
            self.assertEqual(self.runs._call(run_id,'critic','fixed prompt','critic-v0'),result)
            self.assertEqual(model.call_count,2)
        run = self.runs.get(run_id)
        self.assertEqual(run['usage']['calls'],2)
        self.assertEqual([a['id'] for a in run['attempts']],['critic-v0','critic-v0-resume-1'])

    def test_explicit_goal_cannot_be_closed_with_unrelated_evidence(self):
        p = self.programs.create(dict(question=QUESTION,counterexample_search=False),goal_task=GOAL,start=False)
        with self.programs._edit(p['id']) as state:
            state['tasks'][0].update(status='complete',outcome='unknown')
            self.programs._add_task(state,candidate(statement='True',target='Demo.side'))
            state['tasks'][1].update(status='complete',outcome='proved')
        with patch('research_codex.run_task',return_value=answer(dict(decision='answered',reason='Готово',tasks=[],evidence_ids=['L2']))):
            self.programs._worker(p['id'])
        self.assertEqual(self.programs.get(p['id'])['status'],'stalled')

    def test_same_statement_keeps_version_and_no_duplicate_on_direction_change(self):
        state = self.programs._state(self.create()['id'])
        self.assertTrue(self.programs._add_task(state,candidate(direction='prove')))
        self.assertFalse(self.programs._add_task(state,candidate(direction='prove')))
        self.assertTrue(self.programs._add_task(state,candidate()))
        left,right = state['tasks']
        self.assertEqual((left['version'],left['counterpart_id']),(right['version'],right['id']))
        self.assertEqual(right['counterpart_id'],left['id'])
        self.assertTrue(self.programs._add_task(state,candidate(statement='(0 : Nat) = 0',revision_of='L1')))
        self.assertEqual(state['tasks'][2]['version'],2)

    def test_sources_available_to_planner_after_restart(self):
        src = dict(id='abc',name='Claim.lean',status='verified',source='theorem marked : True := trivial')
        p = self.programs.create(dict(question=QUESTION),sources=[src],start=False)
        other = ProgramService(self.runs,recover=False)
        self.assertIn('theorem marked',other._planning_prompt(other._state(p['id'])))
        self.assertEqual(p['attachment_ids'],['abc'])
        self.assertEqual(p['sources'],[dict(id='abc',name='Claim.lean',status='verified')])

    def test_new_checked_prerequisite_allows_retry_of_unresolved_goal(self):
        state = self.programs._state(self.create()['id'])
        self.programs._add_task(state,candidate(direction='prove'))
        state['tasks'][0]['status']='complete'
        self.programs._add_task(state,candidate(direction='prove',target='Demo.helper',statement='True'))
        self.assertFalse(self.programs._add_task(state,candidate(direction='prove',dependencies=['L2'])))
        state['tasks'][1].update(status='complete',outcome='proved')
        self.assertTrue(self.programs._add_task(state,candidate(direction='prove',dependencies=['L2'])))
        self.assertEqual(state['tasks'][2]['retry_of'],'L1')
        self.assertFalse(self.programs._add_task(state,candidate(direction='prove',dependencies=['L2'])))

    def test_restore_between_reservation_and_creation_keeps_child_id(self):
        p = self.programs.create(dict(question=QUESTION),goal_task=GOAL,start=False)
        child_id = 'a'*32
        with self.programs._edit(p['id']) as state:
            state['tasks'][0].update(status='running',run_id=child_id,run_id_budget={'max_calls':4,'timeout_seconds':120})
        restored = ProgramService(self.runs,recover=False)
        with patch.object(self.runs,'start') as start:
            restored._tick(p['id'])
            restored._tick(p['id'])
        self.assertEqual([r['id'] for r in self.runs.list_runs()],[child_id])
        self.assertEqual(self.runs.get(child_id)['contract']['agent_task'],GOAL)
        self.assertEqual(restored.get(p['id'])['tasks'][0]['run_id'],child_id)

    def test_automatic_counterexample_supersedes_proof_only_after_lean_and_fresh_review(self):
        p = self.programs.create(dict(question=QUESTION),goal_task=GOAL,start=False)
        self.assertTrue(p['counterexample_search'])
        original, scout = p['tasks']
        self.assertEqual(scout['counterexample_for'], original['id'])
        self.assertEqual(original['counterexample_task_id'], scout['id'])
        restored = ProgramService(self.runs,recover=False)
        self.assertEqual(next_task(restored._state(p['id']))['id'], scout['id'])
        def model(prompt, folder, **kw):
            self.assertIsNone(kw.get('thread_id'))
            if folder.name == 'plan':
                self.assertIn('short independent counterexample search',prompt)
                return answer(dict(target_id=GOAL['target'], imports=GOAL['imports'], prelude='',
                    nodes=[dict(id=GOAL['target'], statement='¬ ('+GOAL['statement']+')', dependencies=[],
                                proof='by\n  intro h\n  have bad := h 1\n  contradiction')]))
            self.assertEqual(folder.name, 'semantic-review-v0')
            certificate = json.loads(prompt.split('Verified by the local Lean controller:\n')[1])
            self.assertTrue(certificate['target_preserved'])
            self.assertIn(GOAL['target'], certificate['kernel_checked_declarations'])
            return answer(dict(status='aligned', reason='Число 1 опровергает исходную формулировку.', limitations=[]))
        with patch('research_codex.run_task',side_effect=model):
            restored._worker(p['id'])
        final = restored.get(p['id'])
        original, scout = final['tasks']
        self.assertEqual((original['status'], original['run_id']), ('superseded', None))
        self.assertEqual((scout['formal_outcome'],scout['outcome']), ('refuted','refuted'))
        self.assertEqual(scout['version'], original['version'])
        self.assertEqual(final['resolution']['task_ids'], [scout['id']])
        self.assertEqual(final['usage']['calls'],2)
        child = self.runs.get(scout['run_id'])
        self.assertEqual(child['budget']['max_calls'],3)
        self.assertLessEqual(child['budget']['timeout_seconds'],120)
        self.assertEqual(child['contract']['program_context']['counterexample_for'],original['id'])
        self.assertTrue(child['result']['verification']['target_preserved'])

    def test_scout_can_report_no_witness_without_a_failed_run(self):
        goal = dict(GOAL, statement='∀ n : Nat, n = n')
        program = self.programs.create(dict(question=QUESTION), goal_task=goal, start=False)
        with patch('research_codex.run_task', return_value=answer(dict(nodes=[]))) as model:
            self.programs._tick(program['id'])
            run_id = self.programs.get(program['id'])['tasks'][1]['run_id']
            self.runs.futures[run_id].result(timeout=30)
            self.programs._tick(program['id'])
        child = self.runs.get(run_id)
        self.assertEqual((child['status'], child['outcome']), ('complete', 'unknown'))
        self.assertNotIn('verification', child['result'])
        self.assertIn('контрпример не найден', child['result']['reason'])
        self.assertEqual(model.call_count, 1)
        self.assertEqual(next_task(self.programs.get(program['id']))['direction'], 'prove')

    def test_inconclusive_counterexample_hands_positive_claim_to_regular_proof(self):
        goal = dict(GOAL, statement='∀ n : Nat, n = n')
        p = self.programs.create(dict(question='Равно ли натуральное число самому себе?'),goal_task=goal,start=False)
        def model(prompt, folder, **kw):
            if folder.name == 'plan':
                scout = 'short independent counterexample search' in prompt
                return answer(dict(target_id=goal['target'], imports=goal['imports'], prelude='',
                    nodes=[dict(id=goal['target'], statement='¬ ('+goal['statement']+')' if scout else goal['statement'],
                                dependencies=[], proof='by trivial' if scout else '')]))
            if folder.name.startswith('prove-'):
                proof = 'by trivial' if '¬ ('+goal['statement']+')' in prompt else 'by intro n; rfl'
                return answer(dict(proof=proof,explanation=''))
            if folder.name == 'critic-v0':
                return answer(dict(verdict='accept',reason='',issues=[]))
            self.assertEqual(folder.name, 'semantic-review-v0')
            return answer(dict(status='aligned',reason='Цель сохранена.',limitations=[]))
        with patch('research_codex.run_task',side_effect=model):
            self.programs._worker(p['id'])
        final = self.programs.get(p['id'])
        positive, scout = final['tasks']
        self.assertEqual(scout['outcome'], 'unknown')
        self.assertEqual(positive['outcome'], 'proved')
        self.assertEqual(final['resolution']['task_ids'], [positive['id']])
        self.assertEqual(len({positive['run_id'],scout['run_id']}), 2)
        self.assertLessEqual(self.runs.get(scout['run_id'])['usage']['calls'], 3)

    def test_scout_reserves_primary_budget_and_reuses_proposed_opposite(self):
        tight = self.programs.create(dict(question=QUESTION,budget=dict(max_calls=5)),goal_task=GOAL,start=False)
        self.assertEqual(len(tight['tasks']),1)
        self.assertTrue(tight['tasks'][0]['counterexample_skipped'])
        state = self.programs._state(self.create()['id'])
        self.programs._add_task(state,candidate(direction='prove'))
        self.programs._add_task(state,candidate(direction='refute'))
        self.programs._prepare_counterexamples(state, state['tasks'][:])
        self.assertEqual(len(state['tasks']),2)
        self.assertEqual(next_task(state)['id'],'L2')
        self.assertFalse(next_task(state)['needs_sketch'])
        old = self.programs._state(self.create()['id'])
        old.pop('counterexample_search')
        self.programs._add_task(old,candidate(direction='prove'))
        self.programs._prepare_counterexamples(old, old['tasks'][:])
        self.assertEqual([t['id'] for t in old['tasks']], ['L1'])
