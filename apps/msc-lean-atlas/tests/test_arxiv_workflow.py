"""Article/controller integration: synthetic model replies, no external inference."""
import copy
import json
from pathlib import Path
import sys
import tempfile
import threading
import time
import unittest
from unittest.mock import patch

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
import research_service as rs
from research_objects import validate_graph


PAPER_ID = '2610.38474v1'


def article_pages(identifier=PAPER_ID, section='S1', paragraphs=None):
    base = identifier.rsplit('v', 1)[0]
    abstract = f'''<html><head><title>[{identifier}] Finite inverses</title>
      <meta name="citation_arxiv_id" content="{base}"><meta name="citation_title" content="Finite inverses">
      <meta name="citation_author" content="Author, A."><meta name="citation_abstract" content="A polynomial construction.">
      </head><body></body></html>'''
    body = paragraphs or '<p id="source-p1">For a nilpotent N, the finite inverse of I-N is a finite sum.</p>'
    article = f'''<html><body><div id="watermark-tr">arXiv:{identifier}</div>
      <article><div class="ltx_classification">Primary 14R10.</div>
      <section id="{section}"><h2>Finite inverse construction</h2>{body}</section>
      <section id="unselected"><h2>A different theorem</h2><p>UNSELECTED SOURCE TEXT</p></section>
      </article></body></html>'''
    return abstract.encode(), article.encode()


def article_proposal():
    return dict(title='Finite inverse', question='Model tried to replace the question', msc_codes=['05C50'],
        objects=[dict(id=identifier, title=identifier, kind='linear map', definition=definition,
                      parameters=['R'], assumptions=['nilpotence'], msc_codes=['14R10'], lean_refs=[])
                 for identifier, definition in [('operator','A nilpotent endomorphism N.'), ('inverse','The finite geometric sum.')]],
        transitions=[dict(id='finite_inverse', title='Finite inverse', source_ids=['operator'], target_ids=['inverse'],
            relation_type='construction', construction='Take the finite geometric sum.', assumptions=['N is nilpotent'],
            claim='The finite geometric sum is an inverse of I-N.', source_refs=['evidence-1'],
            formulation_status='literature_only', agent_task=None, obligations=[], case_id=None)],
        sources=[dict(id='evidence-1',title='Model title',url='https://invented.example/article',locator='Model locator')])


def formalization(status='ready'):
    # A small explicit synthetic type tests binding; it is not a claimed paper proof.
    return dict(status=status, reason='Synthetic formalization response for controller tests.', limitations=['Test double'],
                agent_task=dict(imports=['Init'],prelude='',target='Source.identity',statement='∀ n : Nat, n = n') if status=='ready' else None,
                obligations=[dict(id='identity',title='Synthetic obligation',target='Source.identity',
                                  statement='∀ n : Nat, n = n',expected_outcome='proved')] if status=='ready' else [])


def response(payload):
    return dict(status='completed',text=json.dumps(payload),usage={'last':{'totalTokens':17}})


class ArxivWorkflowTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        with patch.object(rs.ResearchService, '_environment_fingerprint', return_value='synthetic-environment'):
            self.service = rs.ResearchService(self.temp.name)
        self.addCleanup(self.service.pool.shutdown, wait=True)
        # Any accidental model or network request fails the test, including in workers.
        for target, kwargs in [
            ('research_codex.run_task', {'side_effect':AssertionError('No live model is allowed in integration tests')}),
            ('research_arxiv._fetch_html', {'side_effect':AssertionError('No live article fetch is allowed in tests')}),
            ('research_lean.verify_candidate', {'side_effect':AssertionError('These tests do not prove paper statements')}),
            ('research_retrieval.search', {'return_value':[]}),
            ('research_retrieval.documents', {'return_value':[]}),
            ('research_retrieval.manifest', {'return_value':{'kind':'test-local-corpus'}}),
        ]:
            patcher = patch(target, **kwargs); patcher.start(); self.addCleanup(patcher.stop)
        self.paper = self.import_fixture()

    def import_fixture(self, identifier=PAPER_ID, section='S1', paragraphs=None):
        with patch('research_arxiv._fetch_html', side_effect=article_pages(identifier,section,paragraphs)):
            return self.service.import_arxiv(identifier)

    def create(self, **payload):
        values = dict(purpose='discover',mode='single',question='Извлечь конкретную связь конечного обратного отображения.',
                      msc_codes=['14R10'],paper_ids=[PAPER_ID],section_ids=['S1'],
                      budget={'max_calls':1,'timeout_seconds':600})
        values.update(payload)
        run = self.service.create(values, start=False)
        self.service._started[run['id']] = time.monotonic()
        self.service.cancel_flags[run['id']] = threading.Event()
        return run

    def literature(self):
        graph = article_proposal()
        graph['question'] = graph['transitions'][0]['claim']
        graph['sources'][0].update(url=self.paper['source_urls']['html']+'#S1',locator='Finite inverse construction',
                                  versioned_id=PAPER_ID,section_id='S1',snapshot_sha256=self.paper['snapshot_sha256']['article_html'])
        return self.service.registry.create(graph)

    def proving(self, graph):
        return self.create(purpose='prove',question=graph['transitions'][0]['claim'],graph_id=graph['id'],
                           graph_revision=graph['revision'],transition_id='finite_inverse',paper_ids=[],section_ids=[])

    def test_selected_pinned_source_and_exact_excerpt_are_frozen(self):
        run = self.create()
        self.assertEqual(run['contract']['paper_ids'], [PAPER_ID])
        self.assertEqual(run['contract']['paper_manifest'][0]['snapshot_sha256'], self.paper['snapshot_sha256'])
        self.service._retrieve({'run_id':run['id']})
        saved = self.service.get(run['id'])
        self.assertEqual(saved['source_scope'][0]['requested_sections'], ['S1'])
        self.assertEqual(saved['source_scope'][0]['supplied_sections'], ['S1'])
        self.assertTrue(saved['source_scope'][0]['complete_selected_scope'])
        chunks = self.service.arxiv.evidence(PAPER_ID, ['S1'])
        self.assertEqual(saved['evidence'], chunks)
        self.assertNotIn('UNSELECTED', json.dumps(saved['evidence']))
        self.assertEqual(saved['contract_sha256'], run['contract_sha256'])

    def test_scope_rejects_unpinned_missing_and_unknown_section(self):
        for payload in [dict(paper_ids=['2610.38474']),dict(paper_ids=['2610.38475v1']),dict(section_ids=['absent'])]:
            with self.subTest(payload=payload), self.assertRaises(ValueError):
                self.create(**payload)

    def test_top_level_source_scope_cannot_bypass_frozen_contract(self):
        mutations = [dict(paper_ids=[]),dict(section_ids=['unselected']),dict(paper_manifest=[])]
        for mutation in mutations:
            run = self.create(); self.service.update(run['id'], **mutation)
            with self.subTest(mutation=mutation), self.assertRaises(ValueError):
                self.service._retrieve({'run_id':run['id']})

    def test_citation_snapshot_must_match_the_locally_pinned_article(self):
        graph = self.literature()
        changed = validate_graph(graph)
        changed['sources'][0]['snapshot_sha256'] = '0' * 64
        bad = self.service.registry.create(changed)
        with self.assertRaises(ValueError):
            self.proving(bad)

    def test_multi_paper_selection_cannot_expand_missing_section_to_whole_article(self):
        second = self.import_fixture('2610.38475v1', section='S2')
        with self.assertRaises(ValueError):
            self.create(paper_ids=[PAPER_ID,second['versioned_id']],section_ids=['S1'])

    def test_source_scope_records_truncation_instead_of_claiming_full_coverage(self):
        paragraphs = ''.join(f'<p id="p{i}">{("polynomial inverse " * 190)} {i}</p>' for i in range(12))
        paper = self.import_fixture('2610.38476v1',paragraphs=paragraphs)
        run = self.create(paper_ids=[paper['versioned_id']])
        self.service._retrieve({'run_id':run['id']})
        scope = self.service.get(run['id'])['source_scope'][0]
        self.assertFalse(scope['complete_selected_scope'])
        self.assertLess(scope['included_chunks'],scope['available_chunks'])
        self.assertLessEqual(sum(len(c['text']) for c in self.service.get(run['id'])['evidence']),28000)

    def test_article_discovery_is_literature_only_with_controller_owned_citations(self):
        run = self.create()
        proposal = article_proposal()
        # Even an unsolicited formal task in an article extraction cannot certify it.
        proposal['transitions'][0].update(formulation_status='formalized',agent_task=formalization()['agent_task'],
                                           obligations=formalization()['obligations'])
        with patch('research_codex.run_task',return_value=response(proposal)) as model:
            self.service.start(run['id']); self.service.futures[run['id']].result()
        saved = self.service.detail(run['id'])
        self.assertEqual(saved['status'],'complete',saved.get('error'))
        self.assertEqual(saved['outcome'],'unknown')
        self.assertEqual(saved['usage']['calls'],1)
        self.assertEqual(model.call_count,1)
        graph = saved['object_graph']; transition=graph['transitions'][0]; source=graph['sources'][0]
        self.assertEqual(graph['question'],run['claim'])
        self.assertEqual(graph['msc_codes'],run['msc_codes'])
        self.assertEqual(transition['formulation_status'],'literature_only')
        self.assertIsNone(transition['agent_task']);self.assertEqual(transition['obligations'],[])
        self.assertEqual(transition['status'],'proposed');self.assertIsNone(transition['certificate'])
        self.assertEqual(source['url'],self.paper['source_urls']['html']+'#S1')
        self.assertEqual(source['versioned_id'],PAPER_ID)
        self.assertEqual(source['snapshot_sha256'],self.paper['snapshot_sha256']['article_html'])
        self.assertNotIn('invented.example',json.dumps(graph))
        self.assertFalse(saved.get('object_contract'))

    def test_unknown_model_citation_is_rejected_without_saving_a_graph(self):
        run = self.create(); self.service._retrieve({'run_id':run['id']})
        proposal = article_proposal()
        proposal['sources'][0]['id'] = 'evidence-999'
        proposal['transitions'][0]['source_refs'] = ['evidence-999']
        with patch.object(self.service,'_call',return_value=response(proposal)), self.assertRaises(ValueError):
            self.service._prepare_transitions({'run_id':run['id']})
        self.assertEqual(self.service.registry.list_graphs(),[])

    def test_derived_formalization_preserves_original_and_recovers_create_bind_crash(self):
        graph = self.literature(); original = copy.deepcopy(self.service.graph(graph['id']))
        run = self.proving(graph); rid=run['id']; self.service._retrieve({'run_id':rid})
        with patch('research_codex.run_task',return_value=response(formalization())) as model, \
             patch.object(self.service,'_bind_graph',side_effect=RuntimeError('simulated crash after create')):
            with self.assertRaisesRegex(RuntimeError,'simulated crash'):
                self.service._formalize_transition({'run_id':rid})
        self.assertEqual(model.call_count,1)
        self.assertEqual(len(self.service.registry.list_graphs()),2)
        # The reply is durable and the budget is already exhausted: no resubmission.
        self.service._formalize_transition({'run_id':rid})
        saved=self.service.detail(rid)
        self.assertEqual(len(self.service.registry.list_graphs()),2)
        self.assertNotEqual(saved['graph_ref']['id'],graph['id'])
        self.assertEqual(saved['source_graph_ref'],{'id':graph['id'],'revision':1})
        self.assertEqual(self.service.graph(graph['id']),original)
        self.assertEqual(saved['object_graph']['sources'],original['sources'])
        self.assertEqual(saved['object_graph']['transitions'][0]['claim'],original['transitions'][0]['claim'])
        self.assertEqual(saved['object_graph']['transitions'][0]['formulation_status'],'formalized')
        self.assertIsNone(saved['object_graph']['transitions'][0]['certificate'])
        self.assertTrue(saved['object_contract_sha256'])
        self.assertEqual(self.service._effective_task(saved)['required_obligations'],formalization()['obligations'])
        self.assertEqual(saved['usage']['calls'],1)

    def test_cached_needs_review_stops_before_proof_and_preserves_literature_graph(self):
        graph=self.literature(); original=copy.deepcopy(graph)
        run=self.proving(graph);rid=run['id'];key='formalize-transition-v1'
        rs.atomic(self.service.folder(rid)/'attempts'/key/'result.json',response(formalization('needs_review')))
        self.service.update(rid,status='interrupted',usage={'calls':1,'total_tokens':0,'elapsed_seconds':0},
                            attempts=[{'id':key,'role':'formalize_transition','status':'running'}])
        self.service.start(rid);self.service.futures[rid].result()
        saved=self.service.detail(rid)
        self.assertEqual(saved['status'],'complete',saved.get('error'))
        self.assertTrue(saved['requires_review'])
        self.assertEqual(saved['outcome'],'unknown')
        self.assertEqual(saved['graph_ref'],{'id':graph['id'],'revision':1})
        self.assertFalse(saved.get('object_contract'))
        self.assertEqual(self.service.graph(graph['id']),original)
        self.assertEqual(len(self.service.registry.list_graphs()),1)
        self.assertEqual(saved['usage']['calls'],1)


if __name__ == '__main__':
    unittest.main()
