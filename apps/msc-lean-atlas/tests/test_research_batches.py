"""Serial batch orchestration with deterministic fake existing research runs."""
import copy
import hashlib
import json
from pathlib import Path
import sys
import tempfile
import threading
import time
import unittest
from urllib.request import Request, urlopen
from unittest.mock import patch

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))
from research_batches import ResearchBatches, BatchConflict, exact_task
from research_object_examples import graph_for_case
from research_service import sha


class FakeService:
    def __init__(self, root):
        self.root = Path(root); self.environment_fingerprint = 'test-env'
        self.value = graph_for_case('graph_energy')
        self.value.update(id='a'*32, revision=1)
        self.value['sources'].append(dict(id='input', title='Pinned input', url='', locator='',
            structure_source_id='b'*32, structure_target='Source.goal', structure_source_sha256='c'*64))
        for t in self.value['transitions']: t['source_refs'] = ['input']
        self.rows = {}; self.created = []; self.started = []; self.cancelled = []; self.polls = {}
        self.outcomes = ['complete', 'complete']; self.create_failure = set(); self.hold = False

    def graph(self, identifier, revision):
        if identifier != self.value['id'] or revision != self.value['revision']: raise ValueError('Unknown graph version')
        return copy.deepcopy(self.value)

    def list_runs(self):
        return [dict(id=rid) for rid in reversed(self.rows)]

    def get(self, rid):
        run = self.rows[rid]
        if run['status'] == 'running' and not self.hold:
            self.polls[rid] = self.polls.get(rid, 0) + 1
            if self.polls[rid] >= 2:
                run.update(status=self.outcomes[min(self.started.index(rid),len(self.outcomes)-1)],
                           usage=dict(calls=2, total_tokens=7, elapsed_seconds=3))
        return copy.deepcopy(run)

    def create(self, payload, start=True):
        if payload['transition_id'] in self.create_failure: raise ValueError('Invalid selected contract')
        assert start is False
        assert payload['purpose'] == 'prove'
        assert payload['graph_revision'] == 1
        self.created.append(copy.deepcopy(payload)); rid=format(len(self.rows)+1, '032x')
        transition=next(t for t in self.value['transitions'] if t['id']==payload['transition_id'])
        self.rows[rid]=dict(id=rid,status='queued',purpose='prove',graph_ref=dict(id=self.value['id'],revision=1),
            selected_transition_id=transition['id'],contract={},outcome='unknown',usage=dict(calls=0,total_tokens=0,elapsed_seconds=0),
            object_contract=dict(graph=copy.deepcopy(self.value),transition_id=transition['id']))
        return copy.deepcopy(self.rows[rid])

    def start(self, rid):
        assert not any(r['status']=='running' for key,r in self.rows.items() if key!=rid), 'Concurrent proof runs'
        self.started.append(rid);self.rows[rid]['status']='running';return copy.deepcopy(self.rows[rid])

    def cancel(self, rid):
        self.cancelled.append(rid);self.rows[rid]['status']='cancelled';return copy.deepcopy(self.rows[rid])


class BatchTests(unittest.TestCase):
    def setUp(self):
        self.temp=tempfile.TemporaryDirectory();self.service=FakeService(self.temp.name)
        self.batch=ResearchBatches(self.service,poll_seconds=.01,dispatch=False)
        self.managers=[self.batch]
        self.ids=[t['id'] for t in self.service.value['transitions']]
        self.payload=dict(graph_id='a'*32,graph_revision=1,transition_ids=self.ids,mode='multi',
                          budget=dict(max_calls=4,timeout_seconds=60),idempotency_key='explicit-request-1')

    def tearDown(self):
        for manager in self.managers: manager.close()
        self.temp.cleanup()

    def test_preview_is_read_only_and_budget_is_per_candidate(self):
        before=copy.deepcopy(self.service.value)
        p=self.batch.preview(self.payload)
        self.assertEqual(p['aggregate'],dict(selected=2,eligible=2,skipped=0,max_calls=8,timeout_seconds=120,max_parallel_runs=1))
        self.assertEqual(self.service.created,[]);self.assertEqual(self.service.value,before)
        self.assertEqual(list(self.batch.root.glob('*/batch.json')),[])

    def test_normal_serial_execution_and_failed_candidate_continue(self):
        self.service.outcomes=['failed','complete']
        b=self.batch.create(self.payload);self.batch._work(b['id']);saved=self.batch.get(b['id'])
        self.assertEqual(saved['status'],'complete')
        self.assertEqual([i['status'] for i in saved['items']],['failed','complete'])
        self.assertEqual(len(self.service.started),2)
        self.assertEqual(saved['usage'],dict(calls=4,total_tokens=14,elapsed_seconds=6))
        self.assertEqual([p['transition_id'] for p in self.service.created],self.ids)
        self.assertTrue(all(p['budget']['max_calls']==4 for p in self.service.created))

    def test_create_failure_does_not_launch_that_item_or_stop_next(self):
        self.service.create_failure.add(self.ids[0])
        b=self.batch.create(self.payload);self.batch._work(b['id']);saved=self.batch.get(b['id'])
        self.assertEqual([i['status'] for i in saved['items']],['failed','complete'])
        self.assertEqual(len(self.service.started),1)

    def test_idempotency_and_request_conflict_survive_new_manager(self):
        first=self.batch.create(self.payload)
        again=self.batch.create(self.payload)
        self.assertEqual(first['id'],again['id'])
        observer=ResearchBatches(self.service,dispatch=False);self.managers.append(observer)
        self.assertEqual(observer.create(self.payload)['id'],first['id'])
        with self.assertRaises(BatchConflict):
            observer.create({**self.payload,'transition_ids':[self.ids[0]]})
        self.assertEqual(len(observer.list()),1);self.assertEqual(self.service.created,[])

    def test_cancellation_stops_running_and_unstarted_items(self):
        self.service.hold=True;b=self.batch.create(self.payload)
        worker=threading.Thread(target=self.batch._work,args=(b['id'],));worker.start()
        for _ in range(100):
            if self.service.started: break
            time.sleep(.01)
        self.assertEqual(len(self.service.started),1)
        self.batch.cancel(b['id']);worker.join(2);self.assertFalse(worker.is_alive())
        saved=self.batch.get(b['id'])
        self.assertEqual(saved['status'],'cancelled')
        self.assertEqual([i['status'] for i in saved['items']],['cancelled','cancelled'])
        self.assertEqual(len(self.service.created),1)

    def test_cancel_before_dispatch_creates_no_runs(self):
        b=self.batch.create(self.payload);self.batch.cancel(b['id']);self.batch._work(b['id'])
        self.assertEqual(self.batch.get(b['id'])['status'],'cancelled');self.assertFalse(self.service.created)

    def test_recovery_marks_only_dead_owner_and_never_restarts(self):
        b=self.batch.create(self.payload)
        with patch('research_batches.owner_alive',return_value=True):
            live=ResearchBatches(self.service,dispatch=False);self.managers.append(live)
        self.assertEqual(live.get(b['id'])['status'],'queued')
        with patch('research_batches.owner_alive',return_value=False):
            recovered=ResearchBatches(self.service,dispatch=False);self.managers.append(recovered)
        self.assertEqual(recovered.get(b['id'])['status'],'interrupted')
        self.assertTrue(all(i['status']=='interrupted' for i in recovered.get(b['id'])['items']))
        self.assertEqual(recovered.create(self.payload)['status'],'interrupted')
        self.assertFalse(self.service.created)

    def test_graph_hash_rechecked_before_each_dispatch(self):
        preview=self.batch.preview(self.payload)
        with self.assertRaises(BatchConflict):self.batch.create({**self.payload,'graph_sha256':'f'*64})
        b=self.batch.create({**self.payload,'graph_sha256':preview['graph_sha256']})
        self.service.value['transitions'][0]['claim']+=' changed'
        self.batch._work(b['id'])
        self.assertEqual(self.batch.get(b['id'])['status'],'interrupted');self.assertFalse(self.service.created)

    def test_input_rejects_discovery_and_missing_or_duplicate_explicit_selection(self):
        for change in [dict(purpose='discover'),dict(transition_ids=None),dict(transition_ids=[self.ids[0]]*2),
                       dict(transition_ids=['missing']),dict(mode='pilot'),dict(graph_revision=True),
                       dict(budget=dict(max_calls=25,timeout_seconds=60))]:
            with self.subTest(change=change),self.assertRaises(ValueError):self.batch.create({**self.payload,**change})
        self.service.value['transitions'][0].update(formulation_status='literature_only',agent_task=None,obligations=[],case_id=None)
        preview=self.batch.preview(self.payload)
        self.assertEqual(preview['candidates'][0]['status'],'ineligible')

    def _run(self, *, graph=None, status='failed'):
        graph=copy.deepcopy(graph or self.service.value);t=graph['transitions'][0]
        r=dict(id='d'*32,purpose='prove',status=status,selected_transition_id=t['id'],
               graph_ref=dict(id=graph['id'],revision=graph['revision']),contract={},
               object_contract=dict(graph=graph,transition_id=t['id']),outcome='unknown')
        self.service.rows[r['id']]=r;return r

    def test_invalid_preflight_requires_exact_task_environment_and_rejection(self):
        r=self._run();t=self.service.value['transitions'][0]
        r['contract_verification']=dict(kind='lean_contract_preflight',proof_checked=False,well_typed=False,status='rejected',
             contract_sha256=sha(exact_task(t)),environment_fingerprint='test-env',termination=dict(code='invalid_contract'))
        self.assertEqual(self.batch.preview(self.payload)['candidates'][0]['status'],'invalid_contract')
        r['contract_verification']['termination']['code']='infrastructure'
        self.assertTrue(self.batch.preview(self.payload)['candidates'][0]['eligible'])
        r['contract_verification']['termination']['code']='invalid_contract'
        r['contract_verification']['environment_fingerprint']='old-env'
        self.assertTrue(self.batch.preview(self.payload)['candidates'][0]['eligible'])

    def test_active_and_semantic_review_halt_are_not_duplicates(self):
        r=self._run(status='queued')
        self.assertEqual(self.batch.preview(self.payload)['candidates'][0]['status'],'checking')
        r.update(status='complete',requires_review=True)
        self.assertEqual(self.batch.preview(self.payload)['candidates'][0]['status'],'needs_review')

    def test_derived_narrow_failure_does_not_invalidate_broad_parent(self):
        different=copy.deepcopy(self.service.value);different['id']='e'*32
        different['transitions'][0]['claim']='Narrower claim'
        different['transitions'][0]['agent_task']['statement']='True'
        different['transitions'][0]['obligations'][0]['statement']='True'
        r=self._run(graph=different);r.update(source_graph_ref=dict(id='a'*32,revision=1),source_transition_id=self.ids[0],requires_review=True)
        p=self.batch.preview(self.payload)['candidates'][0]
        self.assertTrue(p['eligible']);self.assertEqual(p['status'],'not_proved')

    def test_exact_historical_verified_contract_is_neutral_not_current_certificate(self):
        different=copy.deepcopy(self.service.value);different['id']='e'*32
        r=self._run(graph=different,status='complete');t=different['transitions'][0]
        report=dict(success=True,compilation_success=True,target_preserved=True,obligations_passed=True,
                    target=t['agent_task']['target'],expected_statement=t['agent_task']['statement'],
                    audit=dict(status='passed'),axioms=[],environment_fingerprint='test-env',
                    obligations=[dict(id=o['id'],target=o['target'],ok=True,
                                      statement_sha256=hashlib.sha256(o['statement'].encode()).hexdigest()) for o in t['obligations']])
        r['result']=dict(verification=report,formal_outcome='proved',semantic_review=dict(status='aligned'))
        p=self.batch.preview(self.payload)['candidates'][0]
        self.assertEqual(p['status'],'historical_exact_evidence');self.assertFalse(p['eligible']);self.assertNotIn('certificate',p)
        self.service.value['transitions'][0]['claim']+=' A new broader claim requiring its own semantic review.'
        p=self.batch.preview(self.payload)['candidates'][0]
        self.assertTrue(p['eligible']);self.assertNotEqual(p['status'],'historical_exact_evidence')
        self.service.value['transitions'][0]['claim']=t['claim']
        r['result']['semantic_review']['status']='mismatch'
        self.assertTrue(self.batch.preview(self.payload)['candidates'][0]['eligible'])

    def test_two_managers_serialize_their_separate_packages(self):
        self.service.hold=True
        second=ResearchBatches(self.service,poll_seconds=.01,dispatch=False);self.managers.append(second)
        a=self.batch.create({**self.payload,'transition_ids':[self.ids[0]]})
        b=second.create({**self.payload,'transition_ids':[self.ids[1]],'idempotency_key':'explicit-request-2'})
        one=threading.Thread(target=self.batch._work,args=(a['id'],));two=threading.Thread(target=second._work,args=(b['id'],))
        one.start()
        for _ in range(100):
            if self.service.started: break
            time.sleep(.01)
        two.start();time.sleep(.05);self.assertEqual(len(self.service.started),1)
        self.service.hold=False;one.join(2);two.join(2)
        self.assertFalse(one.is_alive());self.assertFalse(two.is_alive());self.assertEqual(len(self.service.started),2)

    def test_real_registry_result_publication_does_not_change_pinned_graph_hash(self):
        from research_objects import GraphRegistry
        registry=GraphRegistry(Path(self.temp.name)/'objects.sqlite',environment_fingerprint='test-env')
        created=registry.create(self.service.value)
        self.service.value=created;self.payload['graph_id']=created['id']
        self.service.graph=lambda identifier,revision:registry.get(identifier,revision)
        original_get=self.service.get;published=set()
        def get_and_publish(rid):
            run=original_get(rid)
            if run['status']=='complete' and rid not in published:
                t=next(t for t in created['transitions'] if t['id']==run['selected_transition_id'])
                report=dict(success=True,compilation_success=True,target_preserved=True,obligations_passed=True,
                    target=t['agent_task']['target'],expected_statement=t['agent_task']['statement'],
                    audit=dict(status='passed'),axioms=[],environment_fingerprint='test-env',
                    obligations=[dict(id=o['id'],target=o['target'],ok=True,
                        statement_sha256=hashlib.sha256(o['statement'].encode()).hexdigest()) for o in t['obligations']])
                result=dict(verification=report,formal_outcome='proved',semantic_review=dict(status='aligned'),
                            environment_fingerprint='test-env')
                registry.record_result(created['id'],1,t['id'],rid,result)
                self.service.rows[rid]['result']=result;published.add(rid)
            return run
        self.service.get=get_and_publish
        before=self.batch.preview(self.payload)['graph_sha256']
        b=self.batch.create(self.payload);self.batch._work(b['id'])
        after=self.batch.preview(self.payload)
        self.assertEqual(before,after['graph_sha256'])
        self.assertEqual(len(published),2)
        self.assertEqual([i['status'] for i in self.batch.get(b['id'])['items']],['complete','complete'])
        self.assertEqual([i['status'] for i in after['candidates']],['verified','verified'])
        self.assertTrue(all(t['certificate'] for t in registry.get(created['id'],1)['transitions']))

    def test_http_preview_create_get_list_and_cancel_use_existing_controller(self):
        import server
        http=server.ThreadingHTTPServer(('127.0.0.1',0),server.Handler)
        thread=threading.Thread(target=http.serve_forever,daemon=True)
        base='http://127.0.0.1:'+str(http.server_port)
        def request(path,body=None):
            data=json.dumps(body).encode() if body is not None else None
            req=Request(base+path,data=data,headers={'Content-Type':'application/json'})
            with urlopen(req,timeout=3) as response:return response.status,json.loads(response.read())
        with patch.object(server,'RESEARCH',self.service),patch.object(server,'BATCHES',self.batch):
            thread.start()
            try:
                status,p=request('/api/research/batches/preview',self.payload)
                self.assertEqual(status,200);self.assertEqual(p['aggregate']['eligible'],2);self.assertFalse(self.service.created)
                status,b=request('/api/research/batches',self.payload);self.assertEqual(status,202)
                self.assertEqual(request('/api/research/batches/'+b['id'])[1]['id'],b['id'])
                self.assertEqual(len(request('/api/research/batches?graph_id='+'a'*32+'&graph_revision=1')[1]['batches']),1)
                self.assertEqual(request('/api/research/batches/'+b['id']+'/cancel',{})[1]['status'],'cancelled')
                self.assertFalse(self.service.created)
            finally:
                http.shutdown();http.server_close();thread.join(2)


if __name__=='__main__':unittest.main()
