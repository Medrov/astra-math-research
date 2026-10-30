import io
import json
from pathlib import Path
import queue
import sys
import tempfile
import time
import unittest
from unittest.mock import patch

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
import research_codex as rc


class FakeServer:
    scenarios = []
    calls = []
    def __init__(self, **kwargs):
        self.on_event = kwargs.get('on_event') or (lambda event: None)
        self.cancelled = kwargs.get('cancelled') or (lambda: False)
        self.scenario = self.scenarios.pop(0) if self.scenarios else 'success'
        self.closed = False
        self.events = []
    def models(self):
        if self.scenario == 'missing_model':
            return [{'model': 'gpt-6.1-sol'}]
        return [{'model': 'gpt-6-astra', 'supportedReasoningEfforts': [{'reasoningEffort':'medium'}]}]
    def request(self, method, params):
        self.calls.append((method, params))
        if method == 'account/read':
            return {'account': {'type':'chatgpt','email':'private@example.invalid','accessToken':'never-output'},'requiresOpenaiAuth':True}
        if method == 'thread/start':
            return {'thread': {'id':'thread-1'}, 'model':'gpt-6-astra'}
        if method == 'thread/resume':
            return {'thread': {'id':'thread-1'}}
        if method == 'thread/turns/list':
            return {'data': [{'id':'turn-1','status':'completed','items':[{'id':'answer','type':'agentMessage','phase':'final_answer','text':'recovered'}]}]}
        if method == 'turn/start':
            if self.scenario == 'disconnect':
                raise rc.ProtocolError('Connection lost after send')
            if self.scenario == 'timeout':
                self.events = [rc.DeadlineExceeded('deadline')]
            elif self.scenario == 'cancel':
                self.events = [rc.Cancelled('cancelled')]
            elif self.scenario == 'failed':
                self.events = [{'method':'turn/completed','params':{'threadId':'thread-1','turn':{'id':'turn-1','status':'failed','error':{'message':'quota exceeded'}}}}]
            elif self.scenario == 'rerouted':
                self.events = [{'method':'model/rerouted','params':{'threadId':'thread-1','turnId':'turn-1','fromModel':'gpt-6-astra','toModel':'gpt-6.1-sol'}}]
            else:
                self.events = [
                    {'method':'item/agentMessage/delta','params':{'threadId':'other-thread','itemId':'a','delta':'wrong thread'}},
                    {'method':'item/agentMessage/delta','params':{'threadId':'thread-1','turnId':'turn-1','itemId':'a','delta':'provisional'}},
                    {'method':'item/completed','params':{'threadId':'thread-1','turnId':'turn-1','item':{'id':'a','type':'agentMessage','text':'final authoritative','phase':'final_answer'}}},
                    {'method':'thread/tokenUsage/updated','params':{'threadId':'thread-1','tokenUsage':{'last':{'totalTokens':42}}}},
                    {'method':'turn/completed','params':{'threadId':'thread-1','turn':{'id':'turn-1','status':'completed','items':[]}}},
                ]
            return {'turn':{'id':'turn-1','status':'inProgress'}}
        return {}
    def receive(self):
        message = self.events.pop(0)
        if isinstance(message, Exception): raise message
        return message
    def interrupt(self, thread_id, turn_id):
        self.calls.append(('turn/interrupt', {'threadId':thread_id,'turnId':turn_id}))
        return bool(turn_id)
    def close(self): self.closed = True
    def __enter__(self): return self
    def __exit__(self,*args): self.close()


class CodexWorkerTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.folder = Path(self.temp.name)
        FakeServer.scenarios = []
        FakeServer.calls = []
        self.mock = patch.object(rc, 'AppServer', FakeServer)
        self.mock.start()
    def tearDown(self):
        self.mock.stop()
        self.temp.cleanup()
    def test_authoritative_final_usage_and_idempotency(self):
        events = []
        result = rc.run_task('claim',self.folder,on_event=events.append)
        self.assertEqual(result['status'],'completed')
        self.assertEqual(result['text'],'final authoritative')
        self.assertEqual(result['usage']['last']['totalTokens'],42)
        self.assertNotIn('wrong thread', json.dumps(events))
        self.assertEqual(result,rc.run_task('claim',self.folder))
        self.assertEqual(sum(m=='turn/start' for m,_ in FakeServer.calls),1)
        params = next(p for m,p in FakeServer.calls if m=='thread/start')
        self.assertFalse(params['allowProviderModelFallback'])
        self.assertEqual(params['sandbox'],'read-only')
    def test_changed_request_rejected(self):
        rc.run_task('claim',self.folder)
        with self.assertRaisesRegex(ValueError,'different immutable request'):
            rc.run_task('different',self.folder)
    def test_no_model_fallback(self):
        FakeServer.scenarios = ['missing_model']
        result = rc.run_task('claim',self.folder)
        self.assertEqual(result['status'],'unavailable')
        self.assertFalse(any(m=='thread/start' for m,_ in FakeServer.calls))
        with self.assertRaises(ValueError):
            rc.run_task('claim',self.folder,model='gpt-6.1-sol')
    def test_failure_is_not_success(self):
        FakeServer.scenarios = ['failed']
        result = rc.run_task('claim',self.folder)
        self.assertEqual(result['status'],'failed')
        self.assertEqual(result['error'],'quota exceeded')
    def test_timeout_interrupts(self):
        FakeServer.scenarios = ['timeout']
        result = rc.run_task('claim',self.folder)
        self.assertEqual(result['status'],'timeout')
        self.assertTrue(result['interrupt_requested'])
    def test_cancel_interrupts(self):
        FakeServer.scenarios = ['cancel']
        result = rc.run_task('claim',self.folder)
        self.assertEqual(result['status'],'cancelled')
        self.assertTrue(result['interrupt_requested'])
    def test_reroute_rejected(self):
        FakeServer.scenarios = ['rerouted']
        result = rc.run_task('claim',self.folder)
        self.assertEqual(result['status'],'model_mismatch')
        self.assertTrue(result['interrupt_requested'])
    def test_recover_interrupted_client_without_new_turn(self):
        result = rc.run_task('claim',self.folder)
        p=self.folder/'codex-state.json';state=json.loads(p.read_text())
        state.update(status='inProgress',text='')
        p.write_text(json.dumps(state))
        FakeServer.calls=[]
        result=rc.run_task('claim',self.folder)
        self.assertEqual(result['status'],'completed')
        self.assertEqual(result['text'],'recovered')
        self.assertFalse(any(m=='turn/start' for m,_ in FakeServer.calls))
    def test_unknown_dispatch_not_retried(self):
        FakeServer.scenarios=['disconnect']
        result=rc.run_task('claim',self.folder)
        self.assertEqual(result['status'],'needs_review')
        rc.run_task('claim',self.folder)
        self.assertEqual(sum(m=='turn/start' for m,_ in FakeServer.calls),1)
    def test_status_does_not_leak_account_details(self):
        result=rc.status()
        text=json.dumps(result)
        self.assertTrue(result['available'])
        self.assertNotIn('private',text)
        self.assertNotIn('never-output',text)
        self.assertFalse(result['inference_tested'])
    def test_schema_forwarded(self):
        schema={'type':'object','properties':{'value':{'type':'string'}}}
        rc.run_task('claim',self.folder,output_schema=schema)
        self.assertEqual(next(p for m,p in FakeServer.calls if m=='turn/start')['outputSchema'],schema)
    def test_attempt_lock(self):
        with rc._attempt_lock(self.folder):
            with self.assertRaisesRegex(rc.ProtocolError,'active Codex worker'):
                rc.run_task('claim',self.folder)


class ConnectionTests(unittest.TestCase):
    def connection(self, messages):
        server=rc.AppServer.__new__(rc.AppServer)
        server.messages=queue.Queue()
        for message in messages: server.messages.put(message)
        server.deadline=time.monotonic()+1
        server.cancelled=lambda:False
        server.pending={};server.sequence=0;server.sent=[];server.events=[]
        server.send=server.sent.append;server.on_event=server.events.append
        return server
    def test_notifications_and_out_of_order_responses(self):
        server=self.connection([{'method':'notice','params':{}},{'id':99,'result':{}},{'id':1,'result':{'ok':True}}])
        self.assertEqual(server.request('x',{}),{'ok':True})
        self.assertEqual(server.events,[{'method':'notice','params':{}}])
        self.assertIn(99,server.pending)
    def test_server_approval_is_refused(self):
        server=self.connection([{'id':33,'method':'item/commandExecution/requestApproval','params':{}},{'id':1,'result':{}}])
        server.request('x',{})
        self.assertEqual(server.sent[1]['id'],33)
        self.assertIn('error',server.sent[1])
    def test_protocol_error(self):
        server=self.connection([{'id':1,'error':{'message':'bad schema'}}])
        with self.assertRaisesRegex(rc.ProtocolError,'bad schema'):
            server.request('x',{})
    def test_unexpected_exit(self):
        server=self.connection([None])
        with self.assertRaisesRegex(rc.ProtocolError,'exited'):
            server.receive()


if __name__ == '__main__': unittest.main()
