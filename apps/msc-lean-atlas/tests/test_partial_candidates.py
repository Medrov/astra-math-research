"""Offline recovery tests: saved model replies are explicit fixtures, not proofs."""
import copy
from concurrent.futures import Future, ThreadPoolExecutor
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
from test_structure_workflow import SOURCE, HIT, profile, proposal, ranking


class PartialCandidates(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        with patch.object(rs.ResearchService, '_environment_fingerprint', return_value='test'):
            self.service = rs.ResearchService(self.temp.name)
        self.store = Mock()
        self.store.select.return_value = copy.deepcopy(SOURCE)
        self.source_patch = patch.object(self.service, 'structure_store', return_value=self.store)
        self.source_patch.start()
        self.no_model = patch.object(self.service, '_call', side_effect=AssertionError('recovery must not call models'))
        self.no_model.start()
        self.no_lean = patch('research_lean.verify_candidate', side_effect=AssertionError('recovery is not proof'))
        self.no_lean.start()

    def tearDown(self):
        self.service.pool.shutdown(wait=True)
        self.no_lean.stop(); self.no_model.stop(); self.source_patch.stop()
        self.temp.cleanup()

    def stopped(self, count=2, status='cancelled'):
        run = self.service.create(dict(purpose='structure', mode='single', source_id=SOURCE['source_id'],
                                       target=SOURCE['selected_declaration']['name']), start=False)
        p, routes = structure.validate_routes(profile(), SOURCE)
        folder = self.service.folder(run['id'])
        for route in routes[:count]:
            route['hits'] = [copy.deepcopy(HIT)]
            bindings = []
            raw = proposal()
            graph, candidates = structure.normalize_candidates(raw, route, SOURCE, resolution_log=bindings)
            rs.atomic(folder/'structure'/route['id']/'candidates.json', graph)
            rs.atomic(folder/'structure'/route['id']/'source-reference-resolution.json',
                      dict(status='validated', proof_checked=False, input_source_sha256=SOURCE['source_sha256'], bindings=bindings))
            rs.atomic(folder/'attempts'/(route['id']+'-candidates-v1')/'result.json',
                      dict(status='completed', text=json.dumps(raw)))
            route.update(status='complete', candidates=candidates)
        self.service.update(run['id'], status=status, phase=status, structure_profile=p, structure_routes=routes,
                            outcome='unknown', result=dict(status=status, outcome='unknown'),
                            usage=dict(calls=5, total_tokens=12345, elapsed_seconds=91.25))
        return self.service.get(run['id'])

    def change_json(self, run, relative, change):
        path = self.service.folder(run['id']) / relative
        value = json.loads(path.read_text(encoding='utf-8'))
        change(value)
        rs.atomic(path, value)

    def materialize(self, run):
        view = self.service.partial_candidates(run['id'])
        return self.service.materialize_partial_candidates(run['id'], view['snapshot_sha256'])

    def test_preview_two_is_pure_and_materialization_leaves_parent_untouched(self):
        run = self.stopped(status='budget_exhausted')
        folder = self.service.folder(run['id'])
        before = {str(p.relative_to(folder)): p.read_bytes() for p in folder.rglob('*') if p.is_file()}
        view = self.service.partial_candidates(run['id'])
        self.assertEqual(view['status'], 'available')
        self.assertEqual(view['candidate_count'], 2)
        self.assertEqual(view['completed_route_ids'], ['route_1', 'route_2'])
        self.assertEqual(view['pending_route_ids'], ['route_3'])
        self.assertNotIn('object_graph', self.service.detail(run['id']))
        self.assertEqual(before, {str(p.relative_to(folder)): p.read_bytes() for p in folder.rglob('*') if p.is_file()})
        materialized = self.materialize(run)
        detail = self.service.enrich_partial_candidates(self.service.get(run['id']))
        self.assertEqual(detail['partial_graph_ref'], materialized['graph_ref'])
        self.assertEqual(detail['status'], 'budget_exhausted')
        self.assertNotIn('graph_ref', detail)
        self.assertEqual(self.service.get(run['id']), run)
        self.assertEqual([t['id'] for t in detail['object_graph']['transitions']], ['route_1_bridge', 'route_2_bridge'])
        for t in detail['object_graph']['transitions']:
            self.assertEqual(t['formulation_status'], 'candidate'); self.assertIsNone(t['certificate'])
            self.assertEqual(t['obligations'], []); self.assertIsNone(t['agent_task'])
        for relative, data in before.items():
            self.assertEqual((folder/relative).read_bytes(), data, relative)

    def test_zero_candidates_unavailable(self):
        run = self.stopped(0)
        self.assertEqual(self.service.partial_candidates(run['id'])['candidate_count'], 0)
        with self.assertRaisesRegex(ValueError, 'недоступны'):
            self.service.materialize_partial_candidates(run['id'], 'a'*64)

    def test_failed_route_does_not_hide_valid_sibling(self):
        run = self.stopped()
        routes = run['structure_routes']; routes[1].update(status='failed', reason='Bad candidate')
        self.service.update(run['id'], structure_routes=routes)
        view = self.service.partial_candidates(run['id'])
        self.assertEqual(view['candidate_count'], 1)
        self.assertEqual(view['issues'][0]['code'], 'failed_route')

    def test_corrupted_route_excluded_with_issue(self):
        mutations = [
            ('structure/route_2/candidates.json', lambda v: v['transitions'][0].update(claim='Forged replacement claim')),
            ('structure/route_2/source-reference-resolution.json', lambda v: v.update(input_source_sha256='f'*64)),
            ('structure/route_2/source-reference-resolution.json', lambda v: v['bindings'][0].update(provenance_sha256='f'*64)),
            ('attempts/route_2-candidates-v1/result.json', lambda v: v.update(status='cancelled')),
            ('attempts/route_2-candidates-v1/result.json', lambda v: v.update(text=None)),
            ('attempts/route_2-candidates-v1/result.json', lambda v: v.update(text='{}')),
        ]
        for path, mutate in mutations:
            with self.subTest(path=path):
                run = self.stopped()
                self.change_json(run, path, mutate)
                view = self.service.partial_candidates(run['id'])
                self.assertEqual(view['candidate_count'], 1)
                self.assertEqual(view['issues'][0]['route_id'], 'route_2')

    def test_changed_pinned_source_and_contract_fail_closed(self):
        run = self.stopped()
        self.store.select.return_value = dict(SOURCE, source_sha256='d'*64)
        self.assertEqual(self.service.partial_candidates(run['id'])['status'], 'unavailable')
        self.store.select.return_value = copy.deepcopy(SOURCE)
        contract = dict(run['contract'], question='Changed frozen question')
        self.service.update(run['id'], contract=contract)
        self.assertEqual(self.service.partial_candidates(run['id'])['issues'][0]['code'], 'invalid_source')

    def test_nonobject_artifact_is_route_issue_not_detail_failure(self):
        run = self.stopped()
        rs.atomic(self.service.folder(run['id'])/'structure/route_2/source-reference-resolution.json', [])
        detail = self.service.detail(run['id'])
        self.assertEqual(detail['partial_search']['candidate_count'], 1)
        self.assertEqual(detail['partial_search']['issues'][0]['code'], 'invalid_route')

    def test_stale_hash_rejected_before_registry_write(self):
        run = self.stopped()
        view = self.service.partial_candidates(run['id'])
        routes = run['structure_routes']; routes[1].update(status='failed', reason='Rejected')
        self.service.update(run['id'], structure_routes=routes)
        with self.assertRaisesRegex(ValueError, 'изменились'):
            self.service.materialize_partial_candidates(run['id'], view['snapshot_sha256'])
        self.assertEqual(self.service.registry.list_graphs(), [])

    def test_idempotent_and_concurrent_materialization(self):
        run = self.stopped(); digest = self.service.partial_candidates(run['id'])['snapshot_sha256']
        with ThreadPoolExecutor(max_workers=2) as pool:
            results = list(pool.map(lambda _: self.service.materialize_partial_candidates(run['id'], digest), range(2)))
        self.assertEqual(results[0], results[1])
        self.assertEqual(len(self.service.registry.list_graphs()), 1)
        self.assertEqual(self.materialize(run), results[0])

    def test_active_status_and_finishing_worker_block_recovery_but_live_idle_owner_does_not(self):
        run = self.stopped()
        self.assertEqual(self.service.partial_candidates(run['id'])['status'], 'available')
        for status in ('running', 'queued', 'cancelling'):
            self.service.update(run['id'], status=status)
            self.assertEqual(self.service.partial_candidates(run['id'])['status'], 'unavailable')
        self.service.update(run['id'], status='cancelled')
        future = Future(); self.service.futures[run['id']] = future
        self.assertEqual(self.service.partial_candidates(run['id'])['status'], 'unavailable')
        with self.assertRaisesRegex(ValueError, 'недоступны'):
            self.service.materialize_partial_candidates(run['id'], 'a'*64)
        future.set_result(None)
        self.assertEqual(self.service.partial_candidates(run['id'])['status'], 'available')

    def test_invalid_route_path_and_corrupt_sidecar_fail_closed(self):
        run = self.stopped()
        routes = copy.deepcopy(run['structure_routes']); routes[0]['id'] = '../outside'
        self.service.update(run['id'], structure_routes=routes)
        self.assertEqual(self.service.partial_candidates(run['id'])['status'], 'unavailable')
        self.service.update(run['id'], structure_routes=run['structure_routes'])
        saved = self.materialize(run)
        self.change_json(run, 'partial-candidates/'+saved['snapshot_sha256']+'/snapshot.json',
                         lambda v: v.update(proof_checked=True))
        self.assertEqual(self.service.partial_candidates(run['id'])['status'], 'unavailable')

    def test_child_proof_uses_snapshot_and_preserves_provenance(self):
        run = self.stopped(); saved = self.materialize(run); ref = saved['graph_ref']
        child = self.service.create(dict(purpose='prove', mode='single', graph_id=ref['id'],
                                         graph_revision=1, transition_id='route_1_bridge'), start=False)
        self.assertEqual(child['source_graph_ref'], ref)
        self.assertEqual(child['source_transition_id'], 'route_1_bridge')
        self.assertEqual(child['contract']['source_library'], SOURCE)
        self.assertEqual(child['usage']['calls'], 0)
        self.assertEqual(self.service.get(run['id']), run)

    def test_registry_result_metadata_does_not_invalidate_immutable_snapshot(self):
        run = self.stopped(); saved = self.materialize(run); ref = saved['graph_ref']
        self.service.registry.record_result(ref['id'], 1, 'route_1_bridge', 'f'*32,
            dict(formal_outcome='unknown', semantic_review=dict(status='not_performed')))
        detail = self.service.detail(run['id'])
        self.assertEqual(detail['partial_search']['status'], 'materialized')
        transition = detail['object_graph']['transitions'][0]
        self.assertEqual(len(transition['results']), 1)
        self.assertIsNone(transition['certificate'])
        self.assertEqual(self.materialize(run)['graph_ref'], ref)

    def test_literature_child_retains_exact_origin_snapshot(self):
        from test_transition_structure import literary_graph, profile as literary_profile
        original = self.service.registry.create(literary_graph())
        self.service.arxiv = Mock()
        self.service.arxiv.get_paper.return_value = dict(versioned_id='2601.00001v1', title='Retained test article',
            snapshot_sha256={'article_html':'c'*64}, source_urls={'article_html':'https://arxiv.org/html/2601.00001v1'},
            sections=[dict(id='S2')])
        run = self.service.create(dict(purpose='structure', mode='single', graph_id=original['id'],
                                       graph_revision=1, transition_id='coordinate_change'), start=False)
        source = run['contract']['source_transition']; p, routes = structure.validate_routes(literary_profile(), source)
        route = routes[0]; route['hits'] = [copy.deepcopy(HIT)]; bindings = []
        raw = proposal(); graph, candidates = structure.normalize_candidates(raw, route, source, resolution_log=bindings)
        folder = self.service.folder(run['id'])
        rs.atomic(folder/'structure/route_1/candidates.json', graph)
        rs.atomic(folder/'structure/route_1/source-reference-resolution.json',
                  dict(status='validated', proof_checked=False, input_source_sha256=source['source_sha256'], bindings=bindings))
        rs.atomic(folder/'attempts/route_1-transition-candidates-v1/result.json', dict(status='completed', text=json.dumps(raw)))
        route.update(status='complete', candidates=candidates)
        self.service.update(run['id'], status='interrupted', structure_profile=p, structure_routes=routes)
        ref = self.materialize(run)['graph_ref']
        child = self.service.create(dict(mode='single', purpose='prove', graph_id=ref['id'],
                                         graph_revision=1, transition_id='route_1_bridge'), start=False)
        self.assertEqual(child['contract']['source_transition'], source)
        self.assertEqual(child['source_application_status'], 'not_verified')
        self.assertEqual(child['source_graph_ref'], ref)
        self.assertEqual(child['paper_ids'], ['2601.00001v1'])
        self.assertEqual(child['section_ids'], ['S2'])
        self.assertEqual(child['usage']['calls'], 0)

    def test_resume_searches_remaining_route_then_creates_distinct_full_graph(self):
        run = self.stopped(); partial = self.materialize(run)
        self.service._started[run['id']] = time.monotonic()
        self.service.cancel_flags[run['id']] = threading.Event()
        self.service.update(run['id'], status='running', cancel_requested=False)
        replies = [dict(text=json.dumps(ranking())), dict(text=json.dumps(proposal()))]
        with patch.object(self.service, '_call', side_effect=replies) as model, \
             patch('research_retrieval.search_library_types', return_value=[]), \
             patch('research_retrieval.search_library', return_value=[HIT]), \
             patch('research_retrieval.resolve_library_types', side_effect=lambda hits,*a,**k:hits):
            self.service._structure_search(dict(run_id=run['id']))
            self.service._structure_merge(dict(run_id=run['id']))
        self.assertEqual(model.call_count, 2)
        final = self.service.get(run['id'])
        self.assertNotEqual(final['graph_ref'], partial['graph_ref'])
        self.assertEqual(len(final['object_graph']['transitions']), 3)
        self.assertEqual(len(self.service.registry.get(partial['graph_ref']['id'], 1)['transitions']), 2)
        self.assertNotIn('partial_search', self.service.enrich_partial_candidates(final))


    def test_atlas_stopped_routes_above_six_and_unclassified_channel_remain_available(self):
        import research_atlas as atlas
        run = self.service.create(dict(purpose='structure', mode='single', search_scope='atlas',
            atlas_options=dict(max_deep_routes=9), budget=dict(max_calls=18, timeout_seconds=600), source_id=SOURCE['source_id'],
            target=SOURCE['selected_declaration']['name']), start=False)
        inv = json.loads(atlas.ATLAS_PATH.read_text(encoding='utf-8'))
        mechanism = profile(); mechanism.pop('routes')
        # Explicit test-only navigation labels; no mathematical classification claim.
        indexed = dict(HIT, msc_codes=['05','11','13','15','20','37','54','60'])
        snap = atlas.screen(inv, [indexed], SOURCE, mechanism, options=run['atlas_options'])
        progress = atlas.new_progress(snap)
        folder = self.service.folder(run['id'])
        rs.atomic(folder/'atlas/snapshot.json', snap)
        rs.atomic(folder/'atlas/progress.json', progress)
        self.service.update(run['id'], structure_profile=mechanism, atlas_snapshot_sha256=snap['snapshot_sha256'],
            atlas_summary=atlas.overview(snap, progress)['summary'])
        routes = self.service._atlas_routes(run['id'])
        self.assertEqual(len(routes), 9); self.assertIsNone(routes[0]['msc_code'])
        for route in routes:
            route['hits'] = [copy.deepcopy(snap['sources'][route['atlas_pool_ids'][0]])]
            bindings = []; raw = proposal()
            graph, candidates = structure.normalize_candidates(raw, route, SOURCE, resolution_log=bindings)
            rs.atomic(folder/'structure'/route['id']/'candidates.json', graph)
            rs.atomic(folder/'structure'/route['id']/'source-reference-resolution.json', dict(status='validated',
                proof_checked=False, input_source_sha256=SOURCE['source_sha256'], bindings=bindings))
            rs.atomic(folder/'attempts'/(route['id']+'-candidates-v1')/'result.json', dict(status='completed', text=json.dumps(raw)))
            candidates[0]['canonical_key'] = structure.candidate_identity(graph, graph['transitions'][0])
            route.update(status='complete', candidates=candidates)
        self.service.update(run['id'], status='cancelled', structure_routes=routes)
        self.service.finalize_atlas(run['id'], 'cancelled')
        view = self.service.partial_candidates(run['id'])
        self.assertEqual(view['status'], 'available', view); self.assertEqual(view['candidate_count'], 9)
        saved = self.service.materialize_partial_candidates(run['id'], view['snapshot_sha256'])
        graph = self.service.registry.get(saved['graph_ref']['id'], 1)
        self.assertNotIn(None, graph['msc_codes']); self.assertNotIn('00', graph['msc_codes'])
        self.assertEqual(len(graph['transitions']), 9)


if __name__ == '__main__':
    unittest.main()
