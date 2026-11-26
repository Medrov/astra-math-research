"""QED branch and evidence regressions, using the real service and scripted App Server replies."""
import json
from pathlib import Path
import re
import sys
import tempfile
import threading
import time
import unittest
from unittest.mock import patch

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
import research_qed
import research_service


def survey(level='Medium', kind='inconclusive', proof=''):
    return dict(difficulty=level, body='Основания классификации', answer_kind=kind, proof=proof)


class QedWorkflowTests(unittest.TestCase):
    def setUp(self):
        temporary = tempfile.TemporaryDirectory()
        self.addCleanup(temporary.cleanup)
        self.service = research_service.ResearchService(root=temporary.name, recover=False)
        self.addCleanup(self.service.pool.shutdown)
        run = self.service.create(dict(case_id='strict_inequality', mode='qed',
                                       budget=dict(max_calls=24, timeout_seconds=150)), start=False)
        self.run_id = run['id']
        self.service._started[self.run_id] = time.monotonic()
        self.service.cancel_flags[self.run_id] = threading.Event()

    def run_roles(self, outputs, expected_draft=None):
        prompts = []
        def worker(prompt, *args, **kwargs):
            role, data = outputs[len(prompts)]
            self.assertIn('Role: ' + role, prompt)
            self.assertEqual(kwargs['model'], 'gpt-6-astra')
            self.assertEqual(kwargs['output_schema'], research_qed.SCHEMAS[role])
            if expected_draft and role in ('qed_prove', 'qed_plan'):
                inputs = json.loads(prompt.split('Stage inputs (JSON):\n')[1])
                self.assertEqual(inputs['previous_proof'], expected_draft)
            prompts.append(prompt)
            return dict(status='completed', text=json.dumps(data, ensure_ascii=False), thread_id='t',
                        turn_id=str(len(prompts)), usage={'last': {'totalTokens': 7}})
        with patch('research_codex.run_task', side_effect=worker):
            research_qed.run_workflow(self.service, self.run_id)
        self.assertEqual(len(outputs), len(prompts))
        return self.service.get(self.run_id)

    def test_easy_counterexample_is_unreviewed_and_replays_without_new_call(self):
        run = self.run_roles([('qed_survey', survey('Easy', 'counterexample', 'a=b=0 даёт 0 < 0.'))])
        result = run['result']
        self.assertEqual(result['review'], 'unreviewed')
        self.assertEqual(result['outcome'], 'draft')
        self.assertEqual(result['answer_kind'], 'counterexample')
        proof_path = self.service.folder(self.run_id) / 'qed/proof.txt'
        self.assertEqual(proof_path.read_text(encoding='utf-8').strip(), result['proof'])
        replayed = self.run_roles([])
        self.assertEqual(replayed['qed'], run['qed'])
        self.assertEqual(replayed['usage']['calls'], 1)

    def test_full_route_preserves_easy_survey_draft_through_both_reviews(self):
        run = self.service.create(dict(case_id='strict_inequality', mode='qed', qed_route='full'),
                                  start=False)
        self.run_id = run['id']
        self.service._started[self.run_id] = time.monotonic()
        self.service.cancel_flags[self.run_id] = threading.Event()
        first = 'Подставим a=b=0.'
        final = 'При a=b=0 получаем ложное 0 < 0.'
        run = self.run_roles([
            ('qed_survey', survey('Easy', 'counterexample', first)), ('qed_plan', {'body':'Сверить свидетель'}),
            ('qed_prove', {'answer_kind':'counterexample','body':final}),
            ('qed_structural', {'assessment':'PASS','body':'Верный тип'}), ('qed_verdict', {'decision':'DONE'}),
            ('qed_detailed', {'assessment':'PASS','body':'Подстановка корректна'}), ('qed_verdict', {'decision':'DONE'}),
            ('qed_summary', {'body':'Опровержение рецензировано'})], expected_draft=first)
        self.assertEqual(run['result']['difficulty'], 'Easy')
        self.assertEqual(run['result']['review'], 'model_reviewed')
        self.assertIn(first, run['qed']['steps'][0]['body'])
        self.assertEqual(run['result']['proof'], final)
        self.assertEqual(self.run_roles([])['usage']['calls'], 8)

    def test_writer_receives_markup_required_by_the_structural_reviewer(self):
        reviewer = research_qed._prompt('qed_structural', {}, {})
        writer = research_qed._prompt('qed_prove', {}, {})
        required_tags = set(re.findall(r'<([a-z][a-z-]*)>', reviewer))
        self.assertEqual(required_tags, {'cite', 'key-original-step', 'heuristics'})
        for tag in required_tags:
            self.assertIn(f'<{tag}>', writer)
            self.assertIn(f'</{tag}>', writer)
        self.assertIn('</key-original-step><heuristics>', writer)

    def test_rejected_structure_routes_to_regulator_even_if_judge_says_done(self):
        outputs = [
            ('qed_survey', survey()), ('qed_plan', {'body': 'План 1'}),
            ('qed_prove', {'answer_kind':'proof', 'body':'Первый аргумент'}),
            ('qed_structural', {'assessment':'FAIL', 'body':'Подменена цель'}),
            ('qed_verdict', {'decision':'DONE'}),
            ('qed_regulator', {'decision':'REVISE_PLAN', 'body':'Вернуть исходный квантор'}),
            ('qed_plan', {'body':'План 2'}),
            ('qed_prove', {'answer_kind':'counterexample', 'body':'Точный контрпример'}),
            ('qed_structural', {'assessment':'PASS', 'body':'Структура принята'}),
            ('qed_verdict', {'decision':'DONE'}),
            ('qed_detailed', {'assessment':'PASS', 'body':'Вычисление проверено'}),
            ('qed_verdict', {'decision':'DONE'}),
            ('qed_summary', {'body':'Исправлен квантор'})]
        run = self.run_roles(outputs)
        self.assertEqual(run['result']['review'], 'model_reviewed')
        self.assertEqual(run['result']['proof'], 'Точный контрпример')
        self.assertEqual([s['key'] for s in run['qed']['steps'] if s['role']=='qed_plan'],
                         ['qed-a1-r1-plan','qed-a1-r2-plan'])
        self.assertEqual(self.run_roles([])['usage']['total_tokens'], len(outputs) * 7)

    def test_detailed_reject_then_repair_then_rewrite_preserves_the_plan_only_for_repair(self):
        rejection = [('qed_structural', {'assessment':'PASS','body':'Структура'}),
                     ('qed_verdict', {'decision':'DONE'}),
                     ('qed_detailed', {'assessment':'FAIL','body':'Ошибочный знак'}),
                     ('qed_verdict', {'decision':'CONTINUE'})]
        candidate = ('qed_prove', {'answer_kind':'proof','body':'Вычисление'})
        outputs = [('qed_survey', survey('Hard')), ('qed_plan', {'body':'Первый подход'}), candidate,
                   *rejection, ('qed_regulator', {'decision':'REVISE_PROOF','body':'Исправить знак'}),
                   candidate, *rejection, ('qed_regulator', {'decision':'REWRITE','body':'Сменить подход'}),
                   ('qed_plan', {'body':'Новый подход'}), candidate,
                   ('qed_structural', {'assessment':'PASS','body':'Структура'}), ('qed_verdict', {'decision':'DONE'}),
                   ('qed_detailed', {'assessment':'PASS','body':'Детали'}), ('qed_verdict', {'decision':'DONE'}),
                   ('qed_summary', {'body':'Итоги'})]
        run = self.run_roles(outputs)
        keys = [s['key'] for s in run['qed']['steps'] if s['role'] in ('qed_plan','qed_prove')]
        self.assertEqual(keys, ['qed-a1-r1-plan','qed-a1-r1-p1-prove','qed-a1-r1-p2-prove',
                                'qed-a2-r1-plan','qed-a2-r1-p1-prove'])
        self.assertEqual(run['result']['review'], 'model_reviewed')

    def test_exact_budget_can_finish_after_two_passing_verdicts_without_summary(self):
        self.service.update(self.run_id, budget=dict(max_calls=7,timeout_seconds=150))
        run = self.run_roles([
            ('qed_survey', survey()), ('qed_plan', {'body':'План'}),
            ('qed_prove', {'answer_kind':'proof','body':'Решение'}),
            ('qed_structural', {'assessment':'PASS','body':'Структура'}), ('qed_verdict', {'decision':'DONE'}),
            ('qed_detailed', {'assessment':'PASS','body':'Детали'}), ('qed_verdict', {'decision':'DONE'})])
        self.assertEqual(run['result']['review'], 'model_reviewed')
        self.assertEqual(run['usage']['calls'], 7)
        self.assertEqual(self.run_roles([])['qed']['steps'], run['qed']['steps'])

    def test_inconclusive_easy_is_not_a_success(self):
        self.service.update(self.run_id, budget=dict(max_calls=1,timeout_seconds=150))
        with self.assertRaises(research_service.StopRun) as error:
            self.run_roles([('qed_survey', survey('Easy'))])
        self.assertEqual(error.exception.status, 'budget_exhausted')
        run = self.service.get(self.run_id)
        self.assertEqual(run['outcome'], 'unknown')
        self.assertEqual(run['qed']['review'], 'unreviewed')
        self.assertEqual(len(run['qed']['steps']), 1)


if __name__ == '__main__':
    unittest.main()
