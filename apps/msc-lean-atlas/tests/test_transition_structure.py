"""Literary input workflow tests with explicit model doubles, never research results."""
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
from research_objects import validate_graph, validate_source_transition, graph_fingerprints, _hash
from test_structure_workflow import HIT, proposal


def literary_graph():
    def obj(identifier, codes):
        return dict(id=identifier, title=identifier, kind='mathematical_object', definition='An explicit source object '+identifier,
                    parameters=['positive weight'], assumptions=['regular coordinate change'], msc_codes=codes, lean_refs=[])
    return dict(title='Article transition', question='Study an explicitly stated weighted change of coordinates.',
        msc_codes=['53A10','34B24','58J50'], objects=[obj('domain',['53A10']),obj('form',['34B24','58J50']),obj('unrelated',['11'])],
        transitions=[dict(id='coordinate_change',title='Weighted coordinate change',source_ids=['domain'],target_ids=['form'],
            relation_type='representation', construction='Transport a quadratic form and retain its changed measure weight.',
            assumptions=['The coordinate derivative is strictly positive.'], claim='The source form has the stated weighted representation.',
            obligations=[],agent_task=None,case_id=None,formulation_status='literature_only',source_refs=['paper_section'])],
        sources=[dict(id='paper_section',title='Retained test article',url='https://arxiv.org/html/2601.00001v1#S2',locator='Section 2',
                      versioned_id='2601.00001v1',section_id='S2',snapshot_sha256='c'*64)])


def profile(codes=('28','15','47')):
    return dict(summary='Transport of a weighted quadratic structure',objects=['function spaces','weighted forms'],
        operations=['composition','integration'],assumptions=['invertible regular change'],conclusion_shape='preservation of a quadratic form',
        mechanism='transport through a map with explicit weights',
        routes=[dict(msc_code=c,rationale='Look for a substantive preservation mechanism outside the source areas.',queries=['integral composition']) for c in codes])


class TransitionStructureTests(unittest.TestCase):
    def setUp(self):
        self.temp=tempfile.TemporaryDirectory();self.service=rs.ResearchService(self.temp.name)
        self.graph=self.service.registry.create(literary_graph())
        chunk=dict(id='article:S2:p1',title='Source section',section_id='S2',versioned_id='2601.00001v1',content='Source literary claim.',evidence_type='arxiv_section')
        self.paper=dict(versioned_id='2601.00001v1',title='Retained test article',snapshot_sha256={'article_html':'c'*64},
            source_urls={'article_html':'https://arxiv.org/html/2601.00001v1'},sections=[{'id':'S2'}],chunks=[chunk])
        self.service.arxiv=Mock();self.service.arxiv.get_paper.return_value=copy.deepcopy(self.paper);self.service.arxiv.evidence.return_value=[chunk]
        self.select=patch.object(self.service,'structure_store',side_effect=AssertionError('literature must not create a verified Lean source'));self.select.start()

    def tearDown(self):
        self.service.pool.shutdown(wait=True);self.select.stop();self.temp.cleanup()

    def create(self, **extra):
        payload=dict(purpose='structure',mode='single',graph_id=self.graph['id'],graph_revision=1,transition_id='coordinate_change',budget=dict(max_calls=12,timeout_seconds=600))
        payload.update(extra);run=self.service.create(payload,start=False)
        self.arm(run['id']);return run

    def arm(self, run_id):
        self.service._started[run_id]=time.monotonic();self.service.cancel_flags[run_id]=threading.Event()

    def search(self):
        run=self.create();responses=[dict(status='completed',text=json.dumps(value),usage={}) for value in [profile(),proposal(),proposal(),proposal()]]
        with patch('research_codex.run_task',side_effect=responses) as model,patch('research_retrieval.search',return_value=[]), \
             patch('research_retrieval.search_library',return_value=[HIT]),patch('research_lean.verify_candidate',side_effect=AssertionError('search never proves')):
            self.service._work(run['id'])
        result=self.service.detail(run['id']);self.assertEqual(result['status'],'complete',result.get('error'));self.assertEqual(model.call_count,4)
        return result

    def test_request_freezes_only_selected_objects_claim_assumptions_and_actual_refs(self):
        run=self.create(question='Find a conditional analogy without proving the article.')
        source=run['contract']['source_transition'];self.assertEqual(source['kind'],'literature_transition')
        self.assertNotIn('source_library',run['contract']);self.assertNotIn('source_id',run);self.assertNotIn('graph_ref',run)
        self.assertEqual(run['source_graph_ref'],dict(id=self.graph['id'],revision=1));self.assertEqual(run['source_transition_id'],'coordinate_change')
        self.assertEqual(run['structure_input_kind'],'literature_transition');self.assertEqual(run['source_application_status'],'not_verified')
        self.assertEqual({o['id'] for o in source['objects']},{'domain','form'});self.assertEqual(source['sources'][0]['snapshot_sha256'],'c'*64)
        self.assertEqual(source['transition']['claim'],self.graph['transitions'][0]['claim']);self.assertEqual(source['transition']['assumptions'],self.graph['transitions'][0]['assumptions'])
        self.assertEqual(run['paper_ids'],['2601.00001v1']);self.assertEqual(run['section_ids'],['S2']);self.assertEqual(validate_source_transition(source),source)
        self.assertEqual(self.service._structure_verify_kwargs(run),{})

    def test_mixed_input_and_inexact_graph_reference_are_rejected(self):
        for extra in ({'source_id':'a'*32},{'target':'Input.goal'},{'graph_revision':True},{'transition_id':'missing'}):
            with self.subTest(extra=extra),self.assertRaises(ValueError):self.create(**extra)

    def test_three_different_external_roots_are_required_only_for_literary_input(self):
        source=self.create()['contract']['source_transition'];p,routes=structure.validate_routes(profile(),source)
        self.assertEqual(p['excluded_msc_roots'],['34','53','58']);self.assertEqual(p['source_status'],'literature_not_compiler_verified');self.assertNotIn('formal',p)
        for codes in (('53','15','47'),('34B24','15','47'),('58','15','47'),('28','28A','47')):
            with self.subTest(codes=codes),self.assertRaises(ValueError):structure.validate_routes(profile(codes),source)
        self.assertEqual([r['msc_code'] for r in routes],['28','15','47'])

    def test_literature_evidence_and_prompts_have_no_fictitious_compiler_certificate(self):
        run=self.create();source=run['contract']['source_transition']
        evidence=structure.route_evidence(dict(hits=[HIT]),source)
        self.assertEqual(evidence[0]['extraction'],'literature_transition');self.assertNotIn('lean_environment',json.dumps(evidence))
        with patch.object(self.service,'_call',return_value={'text':json.dumps(profile())}) as call:self.service._structure_profile({'run_id':run['id']})
        prompt=call.call_args.args[2];self.assertIn('NOT been compiler verified',prompt);self.assertIn('excluded_msc_roots',prompt);self.assertNotIn('selected VERIFIED Lean theorem',prompt)
        context=self.service._structure_proof_context(run);self.assertIn('NOT VERIFIED',context);self.assertIn('not re-proving the original article',context);self.assertIn('tautological bridges',context)

    def test_complete_langgraph_search_retains_exact_origin_and_library_hits_into_child_proof(self):
        result=self.search();graph=result['object_graph']
        self.assertEqual(result['outcome'],'unknown');self.assertEqual(len(graph['transitions']),3)
        self.assertTrue((self.service.folder(result['id'])/'checkpoints.sqlite').exists())
        for transition in graph['transitions']:
            self.assertEqual(transition['formulation_status'],'candidate');self.assertIsNone(transition['certificate'])
            source=next(s for s in graph['sources'] if s['id']=='structure_input');self.assertEqual(source['structure_transition'],result['contract']['source_transition'])
            self.assertIn('structure_origin_1',transition['source_refs'])
        target=graph['transitions'][0]['id'];child=self.service.create(dict(mode='single',graph_id=graph['id'],graph_revision=graph['revision'],transition_id=target),start=False)
        self.assertEqual(child['contract']['source_transition'],result['contract']['source_transition']);self.assertNotIn('source_library',child['contract'])
        self.assertEqual(child['source_graph_ref'],result['graph_ref']);self.assertEqual(child['source_transition_id'],target)
        self.assertEqual(child['contract']['source_transition']['graph_ref'],dict(id=self.graph['id'],revision=1))
        context=self.service._structure_proof_context(child);self.assertIn(HIT['statement'],context);self.assertIn(self.graph['transitions'][0]['claim'],context)

    def test_snapshot_tampering_and_source_ref_removal_are_rejected(self):
        source=self.create()['contract']['source_transition'];bad=copy.deepcopy(source);bad['objects'][0]['definition']='Changed without source identity'
        with self.assertRaises(ValueError):validate_source_transition(bad)
        p,routes=structure.validate_routes(profile(),source);routes[0]['hits']=[HIT]
        graph,_=structure.normalize_candidates(proposal(),routes[0],source)
        self.assertIn('structure_transition',graph['sources'][0]);fingerprint=graph_fingerprints(graph)
        bad=copy.deepcopy(graph);bad['transitions'][0]['source_refs'].remove('structure_input')
        with self.assertRaisesRegex(ValueError,'pinned literature input'):validate_graph(bad)
        bad=copy.deepcopy(graph);bad['sources'][0]['structure_transition']['transition']['claim']='Forged claim'
        with self.assertRaises(ValueError):validate_graph(bad)
        self.assertEqual(graph_fingerprints(graph),fingerprint)
        with self.assertRaises(ValueError):structure.normalize_candidates(dict(proposal(),sources=[dict(id='invented')]),routes[0],source)

    def test_resume_checks_original_revision_and_does_not_repeat_saved_routes(self):
        run=self.create();source=run['contract']['source_transition'];p,routes=structure.validate_routes(profile(),source)
        self.service.update(run['id'],structure_profile=p,structure_routes=routes)
        with patch.object(self.service,'_call',side_effect=[{'text':json.dumps(proposal())}]*3) as model,patch('research_retrieval.search_library',return_value=[HIT]) as search:
            self.service._structure_search({'run_id':run['id']});self.service._structure_search({'run_id':run['id']})
        self.assertEqual(model.call_count,3);self.assertEqual(search.call_count,3)
        changed=validate_graph(self.graph);changed['transitions'][0]['claim']='An explicitly revised source claim.'
        self.service.registry.revise(self.graph['id'],changed,1)
        self.service._check(run['id']) # old pinned revision is still available and valid
        self.service.update(run['id'],source_transition_id='switched')
        with self.assertRaisesRegex(ValueError,'Привязка'):self.service._check(run['id'])

    def test_revision_cannot_strip_the_analogy_origin(self):
        result=self.search();graph=validate_graph(result['object_graph']);graph['sources']=[s for s in graph['sources'] if s['id']!='structure_input']
        for t in graph['transitions']:t['source_refs'].remove('structure_input')
        with self.assertRaisesRegex(ValueError,'Происхождение'):
            self.service.revise_graph(result['graph_ref']['id'],dict(graph=graph,expected_revision=1))

    def test_no_hits_consumes_no_candidate_calls_and_creates_no_proof(self):
        run=self.create();source=run['contract']['source_transition'];p,routes=structure.validate_routes(profile(),source)
        self.service.update(run['id'],structure_profile=p,structure_routes=routes)
        with patch.object(self.service,'_call') as model,patch('research_retrieval.search_library',return_value=[]):
            self.service._structure_search({'run_id':run['id']});self.service._structure_merge({'run_id':run['id']})
        model.assert_not_called();result=self.service.detail(run['id']);self.assertEqual(result['object_graph']['transitions'],[]);self.assertEqual(result['outcome'],'unknown')

    def test_formalization_and_review_receive_bridge_scope_and_cannot_import_fictitious_input(self):
        result=self.search();graph=result['object_graph'];target=graph['transitions'][0]['id']
        child=self.service.create(dict(mode='single',graph_id=graph['id'],graph_revision=1,transition_id=target),start=False);self.arm(child['id'])
        # This is a schema/flow double, not an assertion that it realizes the literary analogy.
        task=dict(imports=['Mathlib'],prelude='',target='Bridge.norm_transfer',statement='∀ (x : ℝ), |x| = |x|')
        ready=dict(status='ready',reason='Test schema only.',agent_task=task,obligations=[dict(id='bridge',title='Bridge',target=task['target'],statement=task['statement'],expected_outcome='proved')])
        bad=copy.deepcopy(ready);bad['agent_task']['imports']=['StructureInput']
        with patch.object(self.service,'_call',return_value={'text':json.dumps(bad)}),self.assertRaisesRegex(ValueError,'не имеет проверенного'):
            self.service._formalize_transition({'run_id':child['id']})
        with patch.object(self.service,'_call',return_value={'text':json.dumps(ready)}) as formalizer:
            self.service._formalize_transition({'run_id':child['id']})
        self.assertIn('COMMON-STRUCTURE BRIDGE, not the original article',formalizer.call_args.args[2])
        with patch.object(self.service,'_call',return_value={'text':json.dumps(dict(status='aligned',reason='Test only.',limitations=[]))}) as reviewer:
            self.service._validate_transition({'run_id':child['id']})
        self.assertIn('unrelated generic lemma',reviewer.call_args.args[2]);updated=self.service.get(child['id'])
        self.assertEqual(updated['contract_review']['scope'],'conditional_common_structure');self.assertEqual(updated['contract_review']['source_application_status'],'not_verified')
        self.assertNotEqual(updated['graph_ref'],updated['source_graph_ref']);self.assertNotIn('source_library',updated['contract'])

    def test_scope_limit_does_not_claim_a_failed_verification_succeeded(self):
        source=self.create()['contract']['source_transition'];_,routes=structure.validate_routes(profile(),source);routes[0]['hits']=[HIT]
        graph,_=structure.normalize_candidates(proposal(),routes[0],source);graph=self.service.registry.create(graph)
        child=self.service.create(dict(mode='single',graph_id=graph['id'],graph_revision=1,transition_id=graph['transitions'][0]['id']),start=False);self.arm(child['id'])
        # Deliberately failed verifier double: exercise the actual final-result
        # path without asserting that any mathematical bridge was proved.
        plan=dict(imports=['Init'],prelude='',summary='Workflow double',assumptions=[],relation_kind='representation',target_id='Bridge.goal',
                  nodes=[dict(id='Bridge.goal',title='Test goal',statement='∀ n : Nat, n = n',dependencies=[],proof='by intro n; rfl')])
        with patch.object(self.service,'_call',return_value={'text':json.dumps(plan)}) as model, \
             patch.object(self.service,'_prove_node',return_value={'declaration':'theorem Bridge.goal : ∀ n : Nat, n = n := by intro n; rfl'}), \
             patch('research_lean.verify_candidate',return_value={'status':'failed','success':False}) as verifier:
            self.service._model_workflow(child['id'])
        self.assertEqual(model.call_count,1);verifier.assert_called_once()
        result=self.service.get(child['id'])['result'];self.assertEqual(result['outcome'],'unknown');self.assertEqual(result['formal_outcome'],'unknown')
        self.assertEqual(result['semantic_review']['source_application_status'],'not_verified')
        self.assertTrue(any('Этот запуск относится только' in note for note in result['semantic_review']['limitations']))
        self.assertFalse(any('Проверен только' in note for note in result['semantic_review']['limitations']))


if __name__=='__main__':unittest.main()
