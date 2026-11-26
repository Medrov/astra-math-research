"""QED HTTP contract, live App Server output, and durable call accounting without inference."""
from io import BytesIO
import json
from pathlib import Path
import sys
import tempfile
import threading
import time
import unittest
from unittest.mock import patch

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
import research_service
import server


class QEDLifecycleTests(unittest.TestCase):
    def setUp(self):
        temp = tempfile.TemporaryDirectory()
        self.addCleanup(temp.cleanup)
        self.service = research_service.ResearchService(temp.name)
        self.addCleanup(self.service.pool.shutdown)

    def request(self, method, path, payload=None):
        handler = server.Handler.__new__(server.Handler)
        body = json.dumps(payload).encode()
        handler.path, handler.rfile = path, BytesIO(body)
        handler.headers = {'Host':'localhost:8765', 'Content-Type':'application/json',
                           'Content-Length':str(len(body))}
        handler.server = type('LocalServer', (), {'server_port':8765})()
        response = []
        handler.json_response = lambda value, status=200: response.append((status, value))
        with patch.object(server, 'RESEARCH', self.service):
            getattr(handler, 'do_' + method)()
        return response[0]

    def test_qed_and_existing_histories_share_routes(self):
        with patch.object(self.service, 'start'):
            status, run = self.request('POST', '/api/research/runs',
                                       {'mode':'qed', 'case_id':'graph_energy'})
            old_status, old_run = self.request('POST', '/api/research/runs',
                                               {'case_id':'strict_inequality'})
        self.assertEqual((status, old_status), (202, 202))
        self.assertEqual(run['model'], 'gpt-6-astra')
        self.assertEqual(run['transport'], 'codex-app-server')
        self.assertEqual(run['contract']['qed_route'], 'auto')
        self.assertFalse(run['can_resume'])
        self.assertEqual(run['contract']['agent_task']['target'], 'TriangleEnergy.laplacian_nonnegative')
        self.assertEqual(old_run['mode'], 'pilot')
        self.assertNotIn('qed_route', old_run['contract'])
        self.assertEqual(self.request('GET', '/api/research/runs/' + old_run['id']), (200, old_run))
        self.assertEqual(len(self.request('GET', '/api/research/runs')[1]['runs']), 2)
        self.assertEqual([r['id'] for r in self.request('GET', '/api/research/runs?mode=qed')[1]['runs']],
                         [run['id']])

    def test_selected_route_is_validated_and_frozen(self):
        payload = {'mode':'qed', 'case_id':'graph_energy', 'qed_route':'full'}
        with patch.object(self.service, 'start'):
            status, run = self.request('POST', '/api/research/runs', payload)
            self.assertEqual(status, 202)
            fixed = json.loads(self.service.artifact(run['id'], 'contract-v1.json').read_text(encoding='utf-8'))
            self.assertEqual(fixed['qed_route'], 'full')
            self.assertEqual(research_service.sha(fixed), run['contract_sha256'])
            listed = self.request('GET', '/api/research/runs?mode=qed')[1]['runs']
            self.assertEqual(listed[0]['qed_route'], 'full')
            for change in ({'mode':'multi'}, {'qed_route':None}, {'qed_route':'other'}):
                self.assertEqual(self.request('POST', '/api/research/runs', {**payload, **change})[0], 400)

    def test_resume_availability_on_a_legacy_failed_qed_attempt(self):
        run = self.service.create({'mode':'qed', 'case_id':'graph_energy'}, start=False)
        rid = run['id']
        contract = run['contract']
        del contract['qed_route']
        self.service.update(rid, status='interrupted', contract=contract, contract_sha256=research_service.sha(contract))
        self.assertEqual(self.service.list_runs(mode='qed')[0]['qed_route'], 'auto')
        self.assertTrue(self.request('GET', '/api/research/runs/' + rid)[1]['can_resume'])
        self.service.update(rid, attempts=[{'id':'qed-survey', 'status':'cancelled'}])
        self.assertFalse(self.request('GET', '/api/research/runs/' + rid)[1]['can_resume'])
        self.assertEqual(self.request('POST', '/api/research/runs/' + rid + '/resume', {})[0], 400)

    def test_app_server_output_visible_before_return_and_reconciled_once(self):
        run = self.service.create({'mode':'qed', 'question':'Получить сумму двух квадратов.'}, start=False)
        rid = run['id']
        self.service._started[rid] = time.monotonic()
        self.service.cancel_flags[rid] = threading.Event()
        schema = {'type':'object', 'properties':{'proof':{'type':'string'}}}
        def answer(prompt, folder, **kwargs):
            self.assertEqual(kwargs['model'], 'gpt-6-astra')
            self.assertEqual(kwargs['output_schema'], schema)
            kwargs['on_event']({'method':'turn/started', 'params':{'threadId':'thread', 'turn':{'id':'turn'}}})
            kwargs['on_event']({'method':'item/agentMessage/delta', 'params':{'itemId':'msg', 'delta':'Часть ответа'}})
            live = self.request('GET', '/api/research/runs/' + rid)[1]['attempts'][0]
            self.assertEqual((live['live_text'], live['status'], live['thread_id']), ('Часть ответа', 'running', 'thread'))
            return dict(status='completed', text='Полный ответ', thread_id='thread', turn_id='turn',
                        usage={'last':{'totalTokens':17}}, model='gpt-6-astra')
        with patch('research_codex.run_task', side_effect=answer) as model:
            for _ in range(2):
                self.service._call(rid, 'qed_role', 'Задача', 'qed-role', output_schema=schema)
        model.assert_called_once()
        saved = self.service.get(rid)
        self.assertEqual(saved['attempts'][0]['live_text'], 'Полный ответ')
        self.assertEqual(saved['usage']['calls'], 1)
        self.assertEqual(saved['usage']['total_tokens'], 17)

    def test_resume_publishes_cached_last_call_after_a_restart(self):
        run = self.service.create({'mode':'qed', 'question':'Докажите, что ноль равен нулю.',
                                   'budget':{'max_calls':1, 'timeout_seconds':60}}, start=False)
        rid = run['id']
        reply = {'difficulty':'Easy', 'answer_kind':'proof', 'proof':'0 = 0 по рефлексивности.',
                 'body':'Прямое доказательство.'}
        response = dict(status='completed', text=json.dumps(reply, ensure_ascii=False), model='gpt-6-astra',
                        thread_id='thread', turn_id='turn', usage={'last':{'totalTokens':17}})
        with patch('research_retrieval.search', side_effect=AssertionError('QED must use its fixed input')), \
             patch('research_codex.run_task', return_value=response) as model:
            with patch.object(self.service, '_publish', side_effect=research_service.StopRun('interrupted', 'restart')):
                self.service.start(rid)
                self.service.futures[rid].result()
            self.assertEqual(self.service.get(rid)['status'], 'interrupted')
            self.assertTrue(self.request('GET', '/api/research/runs/' + rid)[1]['can_resume'])
            resumed, _ = self.request('POST', '/api/research/runs/' + rid + '/resume', {})
            self.assertEqual(resumed, 202)
            self.service.futures[rid].result()
        saved = self.service.get(rid)
        self.assertFalse(self.request('GET', '/api/research/runs/' + rid)[1]['can_resume'])
        model.assert_called_once()
        self.assertEqual((saved['status'], saved['outcome'], saved['result']['proof']), ('complete', 'draft', reply['proof']))
        self.assertEqual(self.service.artifact(rid, 'qed/proof.txt').read_text(encoding='utf-8').strip(), reply['proof'])
