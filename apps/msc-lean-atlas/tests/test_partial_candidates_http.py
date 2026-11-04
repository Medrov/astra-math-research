"""Exercise the real HTTP boundary with saved, offline candidate fixtures."""
import json
import threading
import unittest
from unittest.mock import patch
from urllib.error import HTTPError
from urllib.request import Request, urlopen

import test_partial_candidates as fixtures
import server


class PartialCandidateHTTP(unittest.TestCase):
    def setUp(self):
        self.fixture = fixtures.PartialCandidates('test_zero_candidates_unavailable')
        self.fixture.setUp()
        self.addCleanup(self.fixture.tearDown)
        self.service = self.fixture.service
        self.run = self.fixture.stopped(status='budget_exhausted')
        self.patch = patch.object(server, 'RESEARCH', self.service)
        self.patch.start()
        self.addCleanup(self.patch.stop)

        class QuietHandler(server.Handler):
            def log_message(self, *args):
                pass

        self.http = server.ThreadingHTTPServer(('127.0.0.1', 0), QuietHandler)
        self.thread = threading.Thread(target=self.http.serve_forever, daemon=True)
        self.thread.start()
        self.addCleanup(self.close_server)
        self.base = 'http://127.0.0.1:' + str(self.http.server_port)
        self.path = '/api/research/runs/' + self.run['id']

    def close_server(self):
        self.http.shutdown()
        self.http.server_close()
        self.thread.join(2)

    def request(self, path, body=None, origin=None):
        headers = {'Content-Type': 'application/json'}
        if origin:
            headers['Origin'] = origin
        request = Request(self.base + path, data=None if body is None else json.dumps(body).encode(), headers=headers)
        try:
            response = urlopen(request, timeout=4)
        except HTTPError as error:
            response = error
        with response:
            return response.status, json.loads(response.read())

    def test_preview_recover_reload_and_stale_request_preserve_stopped_run(self):
        folder = self.service.folder(self.run['id'])
        original = (folder / 'run.json').read_bytes()
        status, preview = self.request(self.path)
        self.assertEqual(status, 200)
        self.assertEqual(preview['partial_search']['candidate_count'], 2)
        self.assertNotIn('object_graph', preview)
        self.assertFalse((folder / 'partial-candidates').exists())
        body = {'snapshot_sha256': preview['partial_search']['snapshot_sha256']}
        endpoint = self.path + '/partial-candidates'
        self.assertEqual(self.request(endpoint, {})[0], 400)
        self.assertEqual(self.request(endpoint, {'snapshot_sha256': 'f' * 64})[0], 400)
        self.assertEqual(self.request(endpoint, body, 'https://unrelated.example')[0], 403)
        self.assertFalse((folder / 'partial-candidates').exists())
        status, recovered = self.request(endpoint, body)
        self.assertEqual(status, 200)
        self.assertEqual(recovered['status'], 'budget_exhausted')
        self.assertNotIn('graph_ref', recovered)
        self.assertEqual(len(recovered['object_graph']['transitions']), 2)
        self.assertEqual(recovered['partial_search']['status'], 'materialized')
        self.assertEqual(self.request(endpoint, body)[1]['partial_graph_ref'], recovered['partial_graph_ref'])
        self.assertEqual(self.request(self.path)[1]['partial_graph_ref'], recovered['partial_graph_ref'])
        self.assertEqual((folder / 'run.json').read_bytes(), original)
        self.assertEqual(self.service.get(self.run['id'])['usage'], self.run['usage'])


if __name__ == '__main__':
    unittest.main()
