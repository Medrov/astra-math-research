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


def ranking(hits=None, support='supporting'):
    return dict(summary='Explicit semantic-ranking test double, not a mathematical result.', assessments=[dict(
        id=hit['id'], support=support, rationale='The supplied type supports a fiber map.',
        role_in_bridge='Use the equivalence after identifying coordinates.',
        required_assumptions=['The identified map has the required inverse.'], missing_conditions=['Prove the identification.'])
        for hit in (hits if hits is not None else [HIT])])


class StructureContracts(unittest.TestCase):
    def test_adaptive_routes_allow_zero_and_shared_or_source_subjects(self):
        result,routes=structure.validate_routes(profile(),SOURCE)
        self.assertEqual([r['id'] for r in routes],['route_1','route_2','route_3'])
        self.assertEqual(result['formal']['type'],SOURCE['selected_declaration']['type'])
        for codes in ([],['14'],['14','14R10','54'],['14','20']):
            value=profile();value['routes']=[dict(msc_code=c,rationale='structural reason',queries=['shift']) for c in codes]
            self.assertEqual(len(structure.validate_routes(value,SOURCE)[1]),len(codes))
        for codes in (['14','14'],['14','20','XX'],['14']*7):
            bad=profile();bad['routes']=[dict(msc_code=c,rationale='structural reason',queries=['shift']) for c in codes]
            with self.subTest(codes=codes),self.assertRaises(ValueError):
                structure.validate_routes(bad,SOURCE)

    def test_semantic_ranking_rejects_unrelated_and_fabricated_evidence(self):
        self.assertEqual(structure.validate_ranking(ranking(support='lexical_only'),[HIT]),[])
        accepted=structure.validate_ranking(ranking(),[HIT])
        self.assertEqual(accepted[0]['applicability_status'],'proposed_not_verified')
        for value in (dict(assessments=[]),ranking([dict(HIT,id='invented')]),ranking([HIT,HIT])):
            with self.subTest(value=value),self.assertRaises(ValueError):structure.validate_ranking(value,[HIT])

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

    def test_grounding_quotes_are_checked_before_id_remap(self):
        _,routes=structure.validate_routes(profile(),SOURCE);routes[0]['hits']=[HIT]
        value=proposal();value['transitions'][0]['grounding']=[
            dict(component='construction',source_ref='hit_1',quote=HIT['statement'],origin='source_excerpt'),
            dict(component='claim',source_ref='',quote='',origin='proposed_abstraction')]
        graph,_=structure.normalize_candidates(copy.deepcopy(value),routes[0],SOURCE)
        self.assertEqual(graph['transitions'][0]['grounding'][0]['source_ref'],'route_1_hit_1')
        value['transitions'][0]['grounding'][0]['quote']='Invented source quotation'
        with self.assertRaisesRegex(ValueError,'Цитата'):structure.normalize_candidates(value,routes[0],SOURCE)

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
        self.type_search=patch('research_retrieval.search_library_types',return_value=[]);self.type_search.start()
        self.type_resolution=patch('research_retrieval.resolve_library_types',side_effect=lambda hits,*a,**k:hits);self.type_resolution.start()

    def tearDown(self):
        self.service.pool.shutdown(wait=True);self.patcher.stop();self.type_search.stop();self.type_resolution.stop();self.temp.cleanup()

    def create(self):
        run=self.service.create(dict(purpose='structure',mode='single',source_id=SOURCE['source_id'],target='Input.original'),start=False)
        self.service._started[run['id']]=time.monotonic();self.service.cancel_flags[run['id']]=threading.Event()
        return run

    def test_three_routes_use_langgraph_and_never_prove_candidates(self):
        run=self.create()
        answers=[profile(),ranking(),proposal(),ranking(),proposal(),ranking(),proposal()]
        responses=[dict(status='completed',text=json.dumps(v),usage={}) for v in answers]
        with patch('research_codex.run_task',side_effect=responses) as model, \
             patch('research_retrieval.search',return_value=[]), \
             patch('research_retrieval.search_library',return_value=[HIT]), \
             patch('research_lean.verify_candidate',side_effect=AssertionError('search is not proof')):
            self.service._work(run['id'])
        result=self.service.detail(run['id'])
        self.assertEqual(result['status'],'complete',result['error'])
        self.assertEqual(model.call_count,7)
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
        answers=[dict(text=json.dumps(x)) for x in (ranking(),proposal(),ranking(),bad,ranking(),proposal())]
        with patch.object(self.service,'_call',side_effect=answers) as model,patch('research_retrieval.search_library',return_value=[HIT]):
            self.service._structure_search({'run_id':run['id']})
            self.service._structure_search({'run_id':run['id']})
        self.assertEqual(model.call_count,6)
        self.assertEqual([r['status'] for r in self.service.get(run['id'])['structure_routes']],['complete','failed','complete'])
        logs = [json.loads((self.service.folder(run['id'])/'structure'/f'route_{i}'/'source-reference-resolution.json').read_text(encoding='utf-8'))
                for i in range(1, 4)]
        self.assertEqual([log['status'] for log in logs], ['validated','rejected','validated'])
        self.assertTrue(all(log['input_source_sha256'] == SOURCE['source_sha256'] and not log['proof_checked'] for log in logs))
        self.assertIn('fabricated', logs[1]['reason'])

    def test_no_hits_is_unknown_and_does_not_spend_candidate_calls(self):
        run=self.create();p,routes=structure.validate_routes(profile(),SOURCE)
        self.service.update(run['id'],structure_profile=p,structure_routes=routes)
        with patch.object(self.service,'_call') as model,patch('research_retrieval.search_library',return_value=[]):
            self.service._structure_search({'run_id':run['id']});self.service._structure_merge({'run_id':run['id']})
        model.assert_not_called()
        result=self.service.detail(run['id'])
        self.assertEqual(result['result']['outcome'],'unknown')
        self.assertEqual(result['object_graph']['transitions'],[])

    def test_semantic_rejection_avoids_candidate_generation_and_zero_routes_are_valid(self):
        run=self.create();p,routes=structure.validate_routes(profile(),SOURCE)
        self.service.update(run['id'],structure_profile=p,structure_routes=routes[:1])
        with patch.object(self.service,'_call',return_value=dict(text=json.dumps(ranking(support='irrelevant')))) as model, \
             patch('research_retrieval.search_library',return_value=[HIT]):
            self.service._structure_search({'run_id':run['id']})
        self.assertEqual(model.call_count,1)
        self.assertEqual(model.call_args.args[1],'structure_rank')
        self.assertEqual(self.service.get(run['id'])['structure_routes'][0]['candidates'],[])
        self.service.update(run['id'],structure_routes=[])
        self.service._structure_merge({'run_id':run['id']})
        self.assertEqual(self.service.detail(run['id'])['object_graph']['transitions'],[])

    def test_ranking_is_cached_but_never_reused_for_different_pool(self):
        run=self.create();p,routes=structure.validate_routes(profile(),SOURCE);folder=self.service.folder(run['id'])/'rank-test'
        with patch.object(self.service,'_call',return_value=dict(text=json.dumps(ranking()))) as model:
            first=self.service._structure_rank(run['id'],routes[0],SOURCE,p,[HIT],folder)
            self.assertEqual(self.service._structure_rank(run['id'],routes[0],SOURCE,p,[HIT],folder),first)
            with self.assertRaisesRegex(ValueError,'Корпус'):
                self.service._structure_rank(run['id'],routes[0],SOURCE,p,[dict(HIT,statement='changed')],folder)
        self.assertEqual(model.call_count,1)

    def test_changed_source_rejected_and_final_requires_usage(self):
        run=self.create()
        self.assertFalse(self.service._structure_verify_kwargs(run,helper=True)['require_source_usage'])
        self.assertTrue(self.service._structure_verify_kwargs(run)['require_source_usage'])
        self.store.select.return_value=dict(SOURCE,source_sha256='e'*64)
        with self.assertRaisesRegex(ValueError,'Исходная Lean'):
            self.service._check(run['id'])

    def test_only_selected_mechanism_supplies_explicit_reuse_context(self):
        run=self.create();run['selected_transition_id']='chosen'
        run['object_graph']=dict(transitions=[dict(id='chosen',source_refs=['kept'])],sources=[
            dict(id='kept',library_evidence=dict(mechanism_id='d'*64,source_sha256='e'*64)),
            dict(id='other',library_evidence=dict(mechanism_id='f'*64,source_sha256='1'*64))])
        stored=dict(id='d'*64,status='verified_stored_contract',proof_sha256='e'*64,
                    formal_contract=dict(target='Prior.theorem',statement='True'),provenance=dict(title='Prior result'),
                    source_application_status='not_verified',proof_source='PRIOR_PROOF_EVIDENCE',source_library=None)
        catalog=Mock();catalog.get.return_value=stored
        with patch.object(self.service,'mechanism_store',return_value=catalog):
            context=self.service._structure_proof_context(run)
            self.assertIn('EXPLICIT REUSE',context);self.assertIn('PRIOR_PROOF_EVIDENCE',context)
            self.assertIn('require a new complete Lean check',context)
            catalog.get.assert_called_once_with('d'*64)
            catalog.get.return_value=dict(stored,status='needs_recheck')
            with self.assertRaisesRegex(ValueError,'механизм'):self.service._structure_proof_context(run)


if __name__=='__main__':unittest.main()
