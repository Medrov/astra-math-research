"""Real HTTP boundary, isolated files and model-free corpus fixtures."""
import json
from concurrent.futures import Future
import threading
import unittest
from unittest.mock import patch
from urllib.error import HTTPError
from urllib.request import Request, urlopen

import test_partial_candidates as fixtures
from test_atlas_search import inventory, record, PROFILE
import research_atlas as atlas
import research_service as rs
import server


class AtlasHTTP(unittest.TestCase):
    def setUp(self):
        self.fixture = fixtures.PartialCandidates('test_zero_candidates_unavailable')
        self.fixture.setUp(); self.addCleanup(self.fixture.tearDown)
        self.service = self.fixture.service
        self.run = self.service.create(dict(purpose='structure', mode='single', search_scope='atlas',
            source_id=fixtures.SOURCE['source_id'], target=fixtures.SOURCE['selected_declaration']['name']), start=False)
        source = self.run['contract']['source_library']
        self.snapshot = atlas.screen(inventory(), [record()], source, PROFILE)
        progress = atlas.new_progress(self.snapshot)
        self.folder = self.service.folder(self.run['id'])
        rs.atomic(self.folder/'atlas/snapshot.json', self.snapshot)
        rs.atomic(self.folder/'atlas/progress.json', progress)
        self.service.update(self.run['id'], status='budget_exhausted', atlas_snapshot_sha256=self.snapshot['snapshot_sha256'],
                            atlas_summary=atlas.overview(self.snapshot, progress)['summary'], structure_profile=self.snapshot['profile'])
        self.body = dict(budget=dict(max_calls=8, timeout_seconds=600), idempotency_key='continue-test-01',
                         expected_snapshot_sha256=self.snapshot['snapshot_sha256'])
        self.patch = patch.object(server, 'RESEARCH', self.service); self.patch.start(); self.addCleanup(self.patch.stop)
        class Quiet(server.Handler):
            def log_message(self, *args): pass
        self.http = server.ThreadingHTTPServer(('127.0.0.1', 0), Quiet)
        self.thread = threading.Thread(target=self.http.serve_forever, daemon=True); self.thread.start()
        self.addCleanup(self.close)
        self.base = 'http://127.0.0.1:' + str(self.http.server_port)
        self.path = '/api/research/runs/' + self.run['id']

    def close(self):
        self.http.shutdown(); self.http.server_close(); self.thread.join(2)

    def request(self, suffix, body=None, origin=None):
        headers = {'Content-Type':'application/json'}
        if origin: headers['Origin'] = origin
        req = Request(self.base + self.path + suffix, data=None if body is None else json.dumps(body).encode(), headers=headers)
        try: response = urlopen(req, timeout=10)
        except HTTPError as error: response = error
        with response: return response.status, json.loads(response.read())

    def test_read_only_overview_and_idempotent_new_draft(self):
        before = (self.folder/'run.json').read_bytes()
        status, view = self.request('/atlas')
        self.assertEqual(status, 200); self.assertEqual(view['summary']['queried_codes'], 5)
        status, child = self.request('/atlas-continue', self.body)
        self.assertEqual(status, 201); self.assertEqual(child['status'], 'draft')
        self.assertTrue(child['ready_to_start']); self.assertEqual(child['usage']['calls'], 0)
        self.assertEqual(child['contract']['source_library'], self.run['contract']['source_library'])
        self.assertEqual(child['contract']['atlas_budget'], self.body['budget'])
        self.assertEqual(self.request('/atlas-continue', self.body)[1]['id'], child['id'])
        self.assertEqual((self.folder/'run.json').read_bytes(), before)

    def test_wrong_hash_bad_budget_foreign_origin_and_reused_key(self):
        for body in (dict(self.body, expected_snapshot_sha256='f'*64), dict(self.body, retry_failed='yes'),
                     dict(self.body, budget=dict(max_calls=True, timeout_seconds=600)),
                     dict(self.body, budget=dict(max_calls=25, timeout_seconds=600))):
            self.assertEqual(self.request('/atlas-continue', body)[0], 400)
        self.assertEqual(self.request('/atlas-continue', self.body, 'https://foreign.example')[0], 403)
        self.assertEqual(self.request('/atlas-continue', self.body)[0], 201)
        self.assertEqual(self.request('/atlas-continue', dict(self.body, budget=dict(max_calls=9, timeout_seconds=600)))[0], 400)

    def test_crash_after_child_creation_recovers_same_draft(self):
        original = self.service.create
        created = []
        def crash(*args, **kwargs):
            child = original(*args, **kwargs); created.append(child['id']); raise RuntimeError('simulated interruption')
        with patch.object(self.service, 'create', side_effect=crash):
            with self.assertRaisesRegex(RuntimeError, 'simulated'):
                self.service.continue_atlas(self.run['id'], self.body)
        child = self.service.continue_atlas(self.run['id'], self.body)
        self.assertEqual(child['id'], created[0]); self.assertEqual(child['status'], 'draft')
        self.assertEqual(len(list(self.service.root.glob('*/run.json'))), 2)

    def test_retry_failed_is_explicit_and_pinned(self):
        progress = atlas.new_progress(self.snapshot)
        for row in progress['queue']: row.update(status='failed', reason='Fixture model response invalid')
        rs.atomic(self.folder/'atlas/progress.json', progress)
        self.service.update(self.run['id'], atlas_summary=atlas.overview(self.snapshot, progress)['summary'])
        self.assertEqual(self.request('/atlas-continue', self.body)[0], 400)
        status, child = self.request('/atlas-continue', dict(self.body, retry_failed=True))
        self.assertEqual(status, 201); self.assertTrue(child['contract']['atlas_seed']['retry_failed'])

    def test_frozen_scope_and_budget_tampering_rejected(self):
        self.service.update(self.run['id'], budget=dict(max_calls=24, timeout_seconds=600))
        with self.assertRaises(ValueError): self.service._check(self.run['id'])

    def test_changed_parent_question_cannot_reuse_old_profile(self):
        self.service.update(self.run['id'], claim='Changed source question requiring a new mechanism profile')
        self.assertEqual(self.request('/atlas-continue', self.body)[0], 400)
        self.assertEqual(len(list(self.service.root.glob('*/run.json'))), 1)

    def test_terminal_worker_must_finish_before_continuation(self):
        finishing = Future(); self.service.futures[self.run['id']] = finishing
        self.assertEqual(self.request('/atlas-continue', self.body)[0], 400)
        finishing.set_result(None)
        self.assertEqual(self.request('/atlas-continue', self.body)[0], 201)


if __name__ == '__main__': unittest.main()
