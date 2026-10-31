"""Search/controller contract tests. Model replies are explicit doubles, not research results."""
import copy
import json
from pathlib import Path
import sys
import tempfile
import threading
import time
import unittest
from unittest.mock import Mock, patch

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
import research_service as rs
import research_structure as structure
from research_objects import graph_fingerprints, transition_contract, validate_graph


SOURCE = dict(source_id='a'*32, source_sha256='b'*64, title='Input theorem', content='import Init\n',
              environment_fingerprint='test', declarations=[],
              selected_declaration=dict(name='Input.original',kind='theorem',type='Input.shift = Input.shift',axioms=[]))
HIT = dict(id='library:Prod.shear', title='Prod.shear', name='Prod.shear', module='Mathlib.Logic.Equiv.Prod',
           statement='fiberwise translation equivalence', source_sha256='c'*64, extraction='textual_unverified')


def profile():
    return dict(summary='Fiberwise translations',objects=['polynomial coordinates'],operations=['translation'],
                assumptions=['commutative ring'],conclusion_shape='inverse maps',mechanism='fiberwise translation',
                routes=[dict(msc_code=c,rationale='Search compatible fiberwise maps.',queries=['fiber translation']) for c in ['14','20','54']])


def proposal():
    return dict(title='Candidate',question='Compare two exact maps.',msc_codes=['14'],
        objects=[dict(id='fiber',title='Fiber map',kind='function',definition='A fiberwise shift',parameters=[],
                      assumptions=[],msc_codes=['14'],lean_refs=[])],
        transitions=[dict(id='bridge',title='Compare shift maps',source_ids=['fiber'],target_ids=['fiber'],
            relation_type='representation',construction='Use a coordinate permutation and translation.',
            assumptions=['Only underlying functions, no automatic linearity'],claim='The evaluated input map is the fiberwise translation.',
            obligations=[],agent_task=None,case_id=None,formulation_status='literature_only',source_refs=['input','hit_1'])],
        sources=[dict(id='hit_1',title='ignored model title',url='',locator='')])


class StructureContracts(unittest.TestCase):
    def test_exactly_three_distinct_real_subjects(self):
        result,routes=structure.validate_routes(profile(),SOURCE)
        self.assertEqual([r['id'] for r in routes],['route_1','route_2','route_3'])
        self.assertEqual(result['formal']['type'],SOURCE['selected_declaration']['type'])
        for codes in (['14','14R10','54'],['14','20'],['14','20','XX']):
            bad=profile();bad['routes']=[dict(msc_code=c,rationale='structural reason',queries=['shift']) for c in codes]
            with self.subTest(codes=codes),self.assertRaises(ValueError):
                structure.validate_routes(bad,SOURCE)

    def test_ranking_uses_actual_retrieval_and_deduplicates(self):
        route=dict(queries=['one','two'])
        fake=Mock(return_value=[HIT,dict(HIT,id='other',statement='unrelated scalar')])
        hits=structure.ranked_hits(route,profile(),SOURCE,search=fake)
        self.assertEqual(fake.call_count,2)
        self.assertEqual(len(hits),2)
        self.assertEqual(hits[0]['id'],HIT['id'])
        self.assertEqual(hits[0]['query_matches'],['one','two'])

    def test_candidates_bound_to_actual_evidence_and_source(self):
        _,routes=structure.validate_routes(profile(),SOURCE);route=routes[0];route['hits']=[HIT]
        graph,candidates=structure.normalize_candidates(proposal(),route,SOURCE)
        transition=graph['transitions'][0]
        self.assertEqual(transition['formulation_status'],'candidate')
        self.assertEqual(transition_contract(transition),dict(task=None,obligations=[]))
        self.assertIn('input_object',transition['source_ids'])
        self.assertEqual(candidates[0]['transition_id'],transition['id'])
        self.assertEqual(graph['sources'][1]['title'],HIT['title'])
        self.assertEqual(graph['sources'][1]['library_evidence']['statement'],HIT['statement'])
        old=graph_fingerprints(graph)
        graph['sources'][0]['structure_source_sha256']='d'*64
        self.assertNotEqual(old,graph_fingerprints(graph))
        for refs in (['input'],['input','fabricated']):
            value=proposal();value['transitions'][0]['source_refs']=refs
            with self.subTest(refs=refs),self.assertRaises(ValueError):
                structure.normalize_candidates(value,route,SOURCE)
        value=proposal();value['sources'][0]['id']='invented'
        with self.assertRaises(ValueError):structure.normalize_candidates(value,route,SOURCE)

    def test_candidate_cannot_smuggle_formal_contract(self):
        _,routes=structure.validate_routes(profile(),SOURCE);routes[0]['hits']=[HIT]
        graph,_=structure.normalize_candidates(proposal(),routes[0],SOURCE)
        graph['transitions'][0]['agent_task']=dict(imports=['Init'],prelude='',target='Bridge.t',statement='True')
        with self.assertRaises(ValueError):validate_graph(graph)

    def test_structure_binding_cannot_be_omitted_from_transition_hash(self):
        _,routes=structure.validate_routes(profile(),SOURCE);routes[0]['hits']=[HIT]
        graph,_=structure.normalize_candidates(proposal(),routes[0],SOURCE)
        for refs in ([],['route_1_hit_1']):
            bad=copy.deepcopy(graph);bad['transitions'][0]['source_refs']=refs
            with self.subTest(refs=refs),self.assertRaisesRegex(ValueError,'pinned input source'):
                validate_graph(bad)
        before=graph_fingerprints(graph)
        graph['sources'][0]['structure_target']='Input.other'
        self.assertNotEqual(before,graph_fingerprints(graph))


class StructureWorkflow(unittest.TestCase):
    def setUp(self):
        self.temp=tempfile.TemporaryDirectory()
        self.service=rs.ResearchService(self.temp.name)
        self.store=Mock();self.store.select.return_value=copy.deepcopy(SOURCE)
        self.patcher=patch.object(self.service,'structure_store',return_value=self.store);self.patcher.start()

    def tearDown(self):
        self.service.pool.shutdown(wait=True);self.patcher.stop();self.temp.cleanup()

    def create(self):
        run=self.service.create(dict(purpose='structure',mode='single',source_id=SOURCE['source_id'],target='Input.original'),start=False)
        self.service._started[run['id']]=time.monotonic();self.service.cancel_flags[run['id']]=threading.Event()
        return run

    def test_three_routes_use_langgraph_and_never_prove_candidates(self):
        run=self.create()
        answers=[profile(),proposal(),proposal(),proposal()]
        responses=[dict(status='completed',text=json.dumps(v),usage={}) for v in answers]
        with patch('research_codex.run_task',side_effect=responses) as model, \
             patch('research_retrieval.search',return_value=[]), \
             patch('research_retrieval.search_library',return_value=[HIT]), \
             patch('research_lean.verify_candidate',side_effect=AssertionError('search is not proof')):
            self.service._work(run['id'])
        result=self.service.detail(run['id'])
        self.assertEqual(result['status'],'complete',result['error'])
        self.assertEqual(model.call_count,4)
        self.assertEqual(len(result['structure_routes']),3)
        self.assertEqual(len(result['object_graph']['transitions']),3)
        self.assertEqual(result['outcome'],'unknown')
        self.assertTrue(all(t['certificate'] is None for t in result['object_graph']['transitions']))
        graph=result['object_graph'];target=graph['transitions'][0]['id']
        child=self.service.create(dict(mode='single',graph_id=graph['id'],graph_revision=graph['revision'],transition_id=target),start=False)
        self.assertEqual(child['contract']['source_library'],SOURCE)
        self.assertEqual(child['target'],'Input.original')
        self.assertEqual(child['source_graph_ref'],result['graph_ref'])
        self.assertTrue((self.service.folder(run['id'])/'checkpoints.sqlite').exists())

    def test_failed_route_does_not_hide_other_routes_and_resume_skips_completed(self):
        run=self.create();p,routes=structure.validate_routes(profile(),SOURCE)
        self.service.update(run['id'],structure_profile=p,structure_routes=routes)
        bad=proposal();bad['transitions'][0]['source_refs']=['fabricated']
        answers=[dict(text=json.dumps(x)) for x in (proposal(),bad,proposal())]
        with patch.object(self.service,'_call',side_effect=answers) as model,patch('research_retrieval.search_library',return_value=[HIT]):
            self.service._structure_search({'run_id':run['id']})
            self.service._structure_search({'run_id':run['id']})
        self.assertEqual(model.call_count,3)
        self.assertEqual([r['status'] for r in self.service.get(run['id'])['structure_routes']],['complete','failed','complete'])

    def test_no_hits_is_unknown_and_does_not_spend_candidate_calls(self):
        run=self.create();p,routes=structure.validate_routes(profile(),SOURCE)
        self.service.update(run['id'],structure_profile=p,structure_routes=routes)
        with patch.object(self.service,'_call') as model,patch('research_retrieval.search_library',return_value=[]):
            self.service._structure_search({'run_id':run['id']});self.service._structure_merge({'run_id':run['id']})
        model.assert_not_called()
        result=self.service.detail(run['id'])
        self.assertEqual(result['result']['outcome'],'unknown')
        self.assertEqual(result['object_graph']['transitions'],[])

    def test_changed_source_rejected_and_final_requires_usage(self):
        run=self.create()
        self.assertFalse(self.service._structure_verify_kwargs(run,helper=True)['require_source_usage'])
        self.assertTrue(self.service._structure_verify_kwargs(run)['require_source_usage'])
        self.store.select.return_value=dict(SOURCE,source_sha256='e'*64)
        with self.assertRaisesRegex(ValueError,'Исходная Lean'):
            self.service._check(run['id'])


if __name__=='__main__':unittest.main()
