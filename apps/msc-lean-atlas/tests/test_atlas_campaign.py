"""Campaign persistence/model doubles. Successful search is not a proof result."""
import copy
import hashlib
import json
from pathlib import Path
import sys
import tempfile
import unittest
from unittest.mock import Mock, patch

sys.path.insert(0,str(Path(__file__).resolve().parents[1]))
import research_atlas as atlas
import research_structure as structure
import research_service as rs
from test_structure_workflow import SOURCE, profile, proposal, HIT
from test_atlas_search import record


class Harness(structure.StructureResearchMixin):
    def __init__(self, root, source=SOURCE):
        self.root=Path(root);self.calls=[]
        self.runs={'a'*32:dict(id='a'*32,status='running',claim='Explore a mechanism',
            contract=dict(question='Explore a mechanism',search_scope='atlas',atlas_options=atlas.normalize_options(dict(max_deep_routes=12)),
                          atlas_seed=None,source_library=copy.deepcopy(source)),
            search_scope='atlas',atlas_options=atlas.normalize_options(dict(max_deep_routes=12)),atlas_seed=None,
            usage=dict(calls=0),budget=dict(max_calls=30))}
        self.runs['a'*32]['contract_sha256']=rs.sha(self.runs['a'*32]['contract'])
        self.source=copy.deepcopy(source)
    def get(self,key):return copy.deepcopy(self.runs[key])
    def update(self,key,**fields):self.runs[key].update(copy.deepcopy(fields))
    def folder(self,key):
        p=self.root/key;p.mkdir(parents=True,exist_ok=True);return p
    def event(self,*args):pass
    def _check(self,key):return 120
    def _cancelled(self,key):return False
    def cases(self):return []
    def mechanism_store(self):return Mock(search=Mock(return_value=[]),list=Mock(return_value=[]))
    def structure_store(self):return Mock(select=Mock(return_value=self.source))
    def _call(self,key,role,prompt,attempt):
        self.calls.append(role);self.runs[key]['usage']['calls']+=1
        if role=='structure_routes':
            result=profile();result['routes']=[]
        else:
            self.assert_rank(role)
            supplied=json.loads(prompt.split('\n',1)[1])['evidence']
            result=dict(summary='Fixture negative semantic judgment',assessments=[dict(id=x['id'],
                support='irrelevant',rationale='Incompatible fixture operations.',role_in_bridge='No supported map.',
                required_assumptions=[],missing_conditions=['No source identification']) for x in supplied])
        return dict(text=json.dumps(result))
    @staticmethod
    def assert_rank(role):
        if role!='structure_rank':raise AssertionError('Unwanted candidate or proof call: '+role)


def many_snapshot():
    codes=['05','11','13','15','20','37','54','60','68']
    inv=dict(nodes=[dict(id=c,parent_id=None,level=0,title='Quotient ideal '+c) for c in codes])
    # Explicit fixture labels; no assertion of actual MSC mathematical content.
    p=profile();p['routes']=[];p,_=structure.validate_routes(p,SOURCE,max_routes=0)
    return atlas.screen(inv,[record()],SOURCE,p)


def legacy_screen(*args,**kwargs):
    # Reproduce v1 topic extraction and its actual policy pin, without rewriting a run.
    with patch('research_atlas._topic_text',side_effect=lambda text:text):
        snapshot=atlas.screen(*args,**kwargs)
    body={k:v for k,v in snapshot.items() if k!='snapshot_sha256'}
    body.update(screening_method='local_token_inverted_v1',
                policy_sha256=atlas.digest(dict(stop=sorted(atlas.STOP),aliases=atlas.TOKEN_ALIASES)))
    return dict(body,snapshot_sha256=atlas.digest(body))


class CampaignTests(unittest.TestCase):
    def setUp(self):
        self.temp=tempfile.TemporaryDirectory();self.service=Harness(self.temp.name);self.id='a'*32
    def tearDown(self):self.temp.cleanup()
    def prepare(self):
        snap=many_snapshot()
        with patch('research_atlas.local_screen',return_value=snap):
            self.service._structure_profile(dict(run_id=self.id))
        return snap
    def test_all_routes_above_six_zero_candidates_and_resume_no_duplicate_calls(self):
        snap=self.prepare()
        self.service._structure_search(dict(run_id=self.id))
        count=len(self.service.calls)
        self.service._structure_search(dict(run_id=self.id))
        self.assertEqual(len(self.service.calls),count)
        run=self.service.get(self.id)
        self.assertEqual(len(run['structure_routes']),10)
        self.assertEqual(run['atlas_summary']['deep_completed'],10)
        self.assertEqual(run['atlas_summary']['candidates_found'],0)
        self.assertTrue(run['atlas_summary']['deep_complete'])
        self.assertEqual(self.service.calls.count('structure_rank'),10)
        self.assertNotIn('structure_candidates',self.service.calls)
        self.assertEqual(atlas.load(self.service.folder(self.id))[0],snap)

    def test_budget_leaves_queue_and_new_run_seed_does_not_mutate_parent(self):
        self.service.runs[self.id]['budget']['max_calls']=3
        snap=self.prepare();self.service._structure_search(dict(run_id=self.id))
        self.service.update(self.id,status='complete')
        before=(self.service.folder(self.id)/'atlas/progress.json').read_bytes()
        seed=self.service.atlas_continuation_seed(self.id,snap['snapshot_sha256'])
        self.assertEqual((self.service.folder(self.id)/'atlas/progress.json').read_bytes(),before)
        self.assertEqual(self.service.get(self.id)['atlas_summary']['deep_completed'],1)
        child=copy.deepcopy(self.service.get(self.id));childid='b'*32
        child.update(id=childid,status='running',atlas_seed=seed,usage=dict(calls=0),budget=dict(max_calls=30))
        for field in ('atlas_snapshot_sha256','structure_profile','structure_routes','atlas_summary'):child.pop(field,None)
        child['contract']['atlas_seed']=seed
        self.service.runs[childid]=child
        # A different atlas/corpus must reject continuation, not recompute silently.
        with self.assertRaisesRegex(ValueError,'MSC-атлас'):
            self.service._structure_profile(dict(run_id=childid))
        self.assertEqual((self.service.folder(self.id)/'atlas/progress.json').read_bytes(),before)
        self.assertFalse((self.service.folder(childid)/'atlas/snapshot.json').exists())

    def test_cancel_persists_active_items_and_read_only_overview(self):
        self.prepare();routes=self.service._atlas_routes(self.id)
        self.assertEqual(len(routes),10)
        self.service.finalize_atlas(self.id,'cancelled')
        snapshot,progress=atlas.load(self.service.folder(self.id))
        self.assertTrue(all(x['status']=='pending' for x in progress['queue']))
        before=(self.service.folder(self.id)/'atlas/progress.json').read_bytes()
        overview=self.service.atlas_overview(self.id)
        self.assertEqual(overview['summary']['status'],'partial')
        self.assertEqual((self.service.folder(self.id)/'atlas/progress.json').read_bytes(),before)
        self.assertNotIn('sources',overview)

    def test_changed_cached_pool_scope_rejected(self):
        self.prepare();routes=self.service._atlas_routes(self.id)
        path=self.service.folder(self.id)/'structure'/routes[0]['id']/'search.json'
        path.parent.mkdir(parents=True,exist_ok=True)
        path.write_text(json.dumps(dict(atlas_cache_key='tampered',pool=[])),encoding='utf-8')
        with self.assertRaisesRegex(ValueError,'fingerprint'):
            self.service._structure_search(dict(run_id=self.id))
        path.write_text(json.dumps(dict(atlas_cache_key=routes[0]['atlas_cache_key'],pool=[])),encoding='utf-8')
        with self.assertRaisesRegex(ValueError,'pinned evidence'):
            self.service._structure_search(dict(run_id=self.id))

    def test_progress_commit_crash_recovers_pinned_version_and_terminal_busy_rejects(self):
        snap=self.prepare();old=self.service.get(self.id)['atlas_summary']['progress_sha256']
        _,progress=atlas.load(self.service.folder(self.id),old)
        progress['queue'][0]['status']='complete'
        with patch.object(self.service,'update',side_effect=OSError('simulated crash before run pointer')):
            with self.assertRaises(OSError):self.service._atlas_save_progress(self.id,snap,progress)
        _,loaded=atlas.load(self.service.folder(self.id),old)
        self.assertEqual(loaded['queue'][0]['status'],'pending')
        # Even a missing/corrupt compatibility mirror cannot invalidate the commit.
        (self.service.folder(self.id)/'atlas/progress.json').write_text('{}',encoding='utf-8')
        self.assertEqual(self.service.atlas_overview(self.id)['summary']['deep_completed'],0)
        self.service.update(self.id,status='failed');self.service._started={self.id:1}
        with self.assertRaisesRegex(ValueError,'сохранение'):
            self.service.atlas_continuation_seed(self.id,snap['snapshot_sha256'])
        self.service._started={}
        future=Mock();future.done.return_value=False;self.service.futures={self.id:future}
        with self.assertRaisesRegex(ValueError,'сохранение'):
            self.service.atlas_continuation_seed(self.id,snap['snapshot_sha256'])

    def test_partial_coarse_scan_continues_locally_without_another_model_call(self):
        inv=json.loads(atlas.ATLAS_PATH.read_text(encoding='utf-8'))
        p=profile();p['routes']=[];p,_=structure.validate_routes(p,SOURCE,max_routes=0)
        manifest=dict(status='ready',test='pinned fixture')
        checksum=hashlib.sha256(atlas.ATLAS_PATH.read_bytes()).hexdigest()
        partial=legacy_screen(inv,[record()],SOURCE,p,options=dict(local_timeout_seconds=1),
            corpus_manifest=manifest,atlas_sha256=checksum,clock=iter([0,2]).__next__)
        with patch('research_atlas.local_screen',return_value=partial):
            self.service._structure_profile(dict(run_id=self.id))
        self.service.update(self.id,status='cancelled')
        original=(self.service.folder(self.id)/'atlas/snapshot.json').read_bytes()
        seed=self.service.atlas_continuation_seed(self.id,partial['snapshot_sha256'])
        childid='c'*32;child=copy.deepcopy(self.service.get(self.id))
        child.update(id=childid,status='running',atlas_seed=seed,usage=dict(calls=0))
        for field in ('atlas_snapshot_sha256','atlas_summary','structure_profile','structure_routes'):child.pop(field,None)
        child['contract']['atlas_seed']=seed
        self.service.runs[childid]=child
        complete=atlas.screen(inv,[record()],SOURCE,p,corpus_manifest=manifest,atlas_sha256=checksum)
        calls=len(self.service.calls)
        with patch('research_atlas.corpus_manifest',return_value=manifest),patch('research_atlas.local_screen',return_value=complete) as scanner:
            self.service._structure_profile(dict(run_id=childid))
        scanner.assert_called_once()
        self.assertEqual(len(self.service.calls),calls)
        new,progress=atlas.load(self.service.folder(childid))
        self.assertTrue(new['local_queries_complete']);self.assertEqual(new['continued_from'],seed)
        self.assertNotEqual(new['snapshot_sha256'],partial['snapshot_sha256'])
        self.assertNotEqual(new['policy_sha256'],partial['policy_sha256'])
        self.assertEqual(new['screening_method'],atlas.SCREENING_METHOD)
        self.assertEqual(new['nodes'],complete['nodes'])
        self.assertEqual(new['sources'],complete['sources'])
        self.assertEqual([row['id'] for row in progress['queue']],
                         [row['id'] for row in atlas.new_progress(complete)['queue']])
        self.assertEqual((self.service.folder(self.id)/'atlas/snapshot.json').read_bytes(),original)

    def test_complete_legacy_policy_continuation_keeps_exact_snapshot_without_rescreen(self):
        inv=json.loads(atlas.ATLAS_PATH.read_text(encoding='utf-8'))
        p=profile();p['routes']=[];p,_=structure.validate_routes(p,SOURCE,max_routes=0)
        manifest=dict(status='ready',test='pinned legacy fixture')
        checksum=hashlib.sha256(atlas.ATLAS_PATH.read_bytes()).hexdigest()
        original=legacy_screen(inv,[record()],SOURCE,p,corpus_manifest=manifest,atlas_sha256=checksum)
        with patch('research_atlas.local_screen',return_value=original):
            self.service._structure_profile(dict(run_id=self.id))
        self.service.update(self.id,status='cancelled')
        parent_bytes=(self.service.folder(self.id)/'atlas/snapshot.json').read_bytes()
        seed=self.service.atlas_continuation_seed(self.id,original['snapshot_sha256'])
        childid='d'*32;child=copy.deepcopy(self.service.get(self.id))
        child.update(id=childid,status='running',atlas_seed=seed,usage=dict(calls=0))
        for field in ('atlas_snapshot_sha256','atlas_summary','structure_profile','structure_routes'):child.pop(field,None)
        child['contract']['atlas_seed']=seed;child['contract_sha256']=rs.sha(child['contract'])
        self.service.runs[childid]=child;calls=len(self.service.calls)
        with patch('research_atlas.corpus_manifest',return_value=manifest),patch('research_atlas.local_screen') as scanner:
            self.service._structure_profile(dict(run_id=childid))
        scanner.assert_not_called();self.assertEqual(len(self.service.calls),calls)
        snapshot,progress=atlas.load(self.service.folder(childid))
        self.assertEqual(snapshot,original)
        self.assertEqual(snapshot['screening_method'],'local_token_inverted_v1')
        self.assertEqual(snapshot['policy_sha256'],original['policy_sha256'])
        self.assertEqual([row['id'] for row in progress['queue']],
                         [row['id'] for row in atlas.new_progress(original)['queue']])
        self.assertEqual((self.service.folder(self.id)/'atlas/snapshot.json').read_bytes(),parent_bytes)

    def test_candidate_key_deduplicates_only_exact_structural_content(self):
        _,routes=structure.validate_routes(profile(),SOURCE)
        graphs=[]
        for route in routes[:2]:
            route['hits']=[HIT]
            graph,_=structure.normalize_candidates(proposal(),route,SOURCE)
            graphs.append(graph)
        keys=[structure.candidate_identity(g,g['transitions'][0]) for g in graphs]
        self.assertEqual(keys[0],keys[1])
        graphs[1]['transitions'][0]['assumptions'].append('A new, stronger assumption')
        self.assertNotEqual(keys[0],structure.candidate_identity(graphs[1],graphs[1]['transitions'][0]))

    def test_partial_route_persists_candidate_key_before_merge(self):
        self.prepare();routes=self.service._atlas_routes(self.id)
        routes[0]['hits']=[HIT]
        graph,candidates=structure.normalize_candidates(proposal(),routes[0],SOURCE)
        self.service._atlas_bind_candidates(self.id,candidates)
        routes[0].update(status='complete',candidates=candidates)
        self.service.update(self.id,structure_routes=routes)
        self.service.finalize_atlas(self.id,'cancelled')
        _,progress=atlas.load(self.service.folder(self.id),self.service.get(self.id)['atlas_summary']['progress_sha256'])
        self.assertEqual(len(progress['queue'][0]['candidate_keys']),1)
        # Same mathematical text and source under a different route prefix.
        routes[1]['hits']=[HIT]
        _,second=structure.normalize_candidates(proposal(),routes[1],SOURCE)
        self.service._atlas_bind_candidates(self.id,second)
        self.assertEqual(second[0]['duplicate_of'],candidates[0]['transition_id'])
        self.assertIsNone(routes[0]['msc_code'])
        self.assertEqual(graph['msc_codes'],[])

    def test_parent_question_tamper_never_seeds_a_new_question(self):
        snap=self.prepare();self.service.update(self.id,status='failed',claim='Different mathematical question')
        with self.assertRaisesRegex(ValueError,'Цель'):
            self.service.atlas_continuation_seed(self.id,snap['snapshot_sha256'])

    def test_mutable_route_cannot_switch_pinned_pool_or_profile(self):
        self.prepare();self.service._atlas_routes(self.id)
        run=self.service.get(self.id);atlas.validate_atlas_integrity(self.service,run)
        bad=copy.deepcopy(run);bad['structure_routes'][0]['atlas_pool_ids']=[]
        with self.assertRaisesRegex(ValueError,'scope or pool'):
            atlas.validate_atlas_integrity(self.service,bad)
        bad=copy.deepcopy(run);bad['structure_profile']['mechanism']='Different question'
        with self.assertRaisesRegex(ValueError,'mechanism profile'):
            atlas.validate_atlas_integrity(self.service,bad)


if __name__=='__main__':unittest.main()
