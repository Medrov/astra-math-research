"""Isolated UI replay. NO ResearchService, model, Lean, subprocess or POST proxy.

Run: .venv/Scripts/python.exe -X utf8 tests/serve_guided_replay.py --port 8870
Only verification/guided-ui receives writes. Research fixtures remain read-only.
"""
from __future__ import annotations

import argparse
import copy
from datetime import datetime, timezone
import hashlib
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer
import json
import mimetypes
import os
from pathlib import Path
import re
import threading
from urllib.parse import parse_qs, unquote, urlsplit
from urllib.request import Request, urlopen


ROOT = Path(__file__).resolve().parents[1]
DATA = ROOT / 'research_data'
OUTPUT = ROOT / 'verification/guided-ui'
SEARCH = '97fde89034994eb9ac0fbfe5576e8fcd'
PROOF = 'abf14508267f4c1a83e58b37d01e65dc'
SOURCE = 'c477901247234c02bd0ddc8fab3bd9cc'
SEARCH_REPLAY = '88700000000000000000000000000001'
PROOF_REPLAY = '88700000000000000000000000000002'
TARGET = 'Arxiv261038474.subtract_restore'
TRANSITION = 'route_2_bridge_spectrum'
LIMITS = {'max_calls': 16, 'timeout_seconds': 1800, 'max_parallel': 2}
BANNER = 'Тест интерфейса · воспроизведение сохранённых ответов · модели не вызываются'


def read_json(path):
    return json.loads(path.read_text(encoding='utf-8'))


def stamp():
    return datetime.now(timezone.utc).isoformat()


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


class Replay:
    def __init__(self, port, get_port):
        self.port, self.get_port = port, get_port
        self.lock = threading.RLock()
        self.actions, self.runs = [], {}
        self.search = read_json(DATA / SEARCH / 'run.json')
        self.proof = read_json(DATA / PROOF / 'run.json')
        if self.search['status'] != 'complete' or self.proof['status'] != 'complete':
            raise ValueError('Replay requires completed recorded fixtures.')
        self.source = read_json(DATA / 'structure_sources' / SOURCE / 'snapshot.json')
        self.source['content'] = (DATA / 'structure_sources' / SOURCE / 'StructureInput.lean').read_bytes().decode('utf-8')
        if hashlib.sha256(self.source['content'].encode('utf-8')).hexdigest() != self.source['source_sha256']:
            raise ValueError('Stored source content hash mismatch.')
        self.source['id'] = SOURCE
        self.paper = read_json(DATA / 'arxiv/2610.38474v1/paper.json')
        self.catalog = self.get_fixture('/api/structure/sources')
        keys = ('source_id', 'id', 'title', 'name', 'status', 'source_sha256', 'environment_fingerprint', 'created_at', 'provenance')
        self.catalog['sources'] = [{key: self.source.get(key) for key in keys}]
        self.cases = self.get_fixture('/api/research/cases')
        # The recorded proof was started from search graph revision 2 (saved excerpts).
        ref = self.proof['source_graph_ref']
        self.search_graph = self.get_fixture(f"/api/objects/graphs/{ref['id']}?revision={ref['revision']}")
        ref = self.proof['graph_ref']
        self.proof_graph = self.get_fixture(f"/api/objects/graphs/{ref['id']}?revision={ref['revision']}")
        self.search['object_graph'] = self.search_graph
        self.search['graph_ref'] = {'id': self.search_graph['id'], 'revision': self.search_graph['revision']}
        self.proof['object_graph'] = self.proof_graph
        self.graphs = {g['id']: g for g in (self.search_graph, self.proof_graph)}
        paths = [DATA / SEARCH / 'run.json', DATA / PROOF / 'run.json',
                 DATA / 'structure_sources' / SOURCE / 'snapshot.json', DATA / 'arxiv/2610.38474v1/paper.json']
        self.fixture_hashes = {str(p.relative_to(ROOT)).replace('\\', '/'): digest(p) for p in paths}
        OUTPUT.mkdir(parents=True, exist_ok=True)
        self.write('replay-actions.json', {'replay_only': True, 'actions': []})
        self.write('replay-ready.json', dict(replay_only=True, pid=os.getpid(), port=port,
            search_id=SEARCH_REPLAY, proof_id=PROOF_REPLAY, original_search=SEARCH, original_proof=PROOF,
            source_id=SOURCE, expected_budget=LIMITS, search_graph_ref=self.search['graph_ref'],
            fixture_sha256=self.fixture_hashes, banner=BANNER))

    def get_fixture(self, path):
        """A finite startup-only GET allowlist; never receives user-selected URLs."""
        allowed = path in ('/api/structure/sources', '/api/research/cases') or bool(
            re.fullmatch(r'/api/objects/graphs/[a-f0-9]{32}\?revision=[1-9][0-9]*', path))
        if not allowed:
            raise ValueError('Not an allowed fixture GET.')
        req = Request(f'http://127.0.0.1:{self.get_port}' + path, method='GET')
        with urlopen(req, timeout=15) as response:
            body = response.read(12 * 1024 * 1024 + 1)
        if len(body) > 12 * 1024 * 1024:
            raise ValueError('Fixture GET too large.')
        return json.loads(body)

    @staticmethod
    def write(name, value):
        destination = OUTPUT / name
        temporary = OUTPUT / (name + '.tmp')
        temporary.write_text(json.dumps(value, ensure_ascii=False, indent=2) + '\n', encoding='utf-8')
        temporary.replace(destination)

    def log_action(self, path, payload, accepted, reason=None):
        self.actions.append(dict(at=stamp(), path=path, payload=payload, accepted=accepted, reason=reason))
        self.write('replay-actions.json', dict(replay_only=True, model_calls=0, lean_calls=0,
            fixture_sha256=self.fixture_hashes, actions=self.actions))

    def start(self, payload):
        if payload.get('purpose') == 'structure':
            expected = dict(purpose='structure', mode='multi', source_id=SOURCE, target=TARGET, budget=LIMITS)
            identifier, fixture = SEARCH_REPLAY, self.search
        elif payload.get('purpose') == 'prove':
            if self.runs.get(SEARCH_REPLAY, {}).get('step', 0) < 3:
                raise ValueError('First complete the replay search through the UI.')
            expected = dict(purpose='prove', mode='multi', graph_id=self.search_graph['id'],
                graph_revision=self.search_graph['revision'], transition_id=TRANSITION,
                budget=LIMITS, msc_codes=self.search_graph['msc_codes'])
            identifier, fixture = PROOF_REPLAY, self.proof
        else:
            raise ValueError('Only the specified structure/proof UI sequence is accepted.')
        # Canonical JSON distinguishes booleans from numbers as well as unknown fields.
        if json.dumps(payload, sort_keys=True) != json.dumps(expected, sort_keys=True):
            raise ValueError('Replay payload mismatch. Expected: ' + json.dumps(expected, ensure_ascii=False))
        if identifier in self.runs:
            raise ValueError('This replay step was already started; no duplicate action accepted.')
        self.runs[identifier] = dict(fixture=fixture, step=0, received=copy.deepcopy(payload))
        return self.snapshot(identifier, advance=False)

    def snapshot(self, identifier, *, advance=True):
        if identifier not in self.runs:
            raise KeyError('Replay run not started.')
        entry = self.runs[identifier]
        if advance:
            entry['step'] = min(entry['step'] + 1, 3)
        step = entry['step']
        run = copy.deepcopy(entry['fixture'])
        run['replay'] = dict(enabled=True, original_run_id=run['id'], original_mode=run['mode'],
            original_usage=run.get('usage'), note=BANNER, new_model_calls=0, new_lean_calls=0)
        run.update(id=identifier, title='[REPLAY] ' + run['title'], mode='multi', budget=copy.deepcopy(LIMITS),
                   usage=dict(calls=0, total_tokens=0, elapsed_seconds=step), owner_pid=None)
        if step < 3:
            phase = 'queued' if step == 0 else ('structure_profile' if step == 1 else 'structure_search') if identifier == SEARCH_REPLAY else ('formalize_transition' if step == 1 else 'verify')
            run.update(status='queued' if step == 0 else 'running', phase=phase, outcome='unknown',
                       result=None, formal_outcome='unknown', semantic_review={'status': 'pending'},
                       nodes=[], edges=[], events=[{'id': 'replay-stage-' + str(step), 'at': stamp(),
                           'phase': phase, 'message': BANNER + ' · этап ' + str(step + 1)}],
                       object_graph=None, graph_ref=None, artifacts=[])
            run.pop('structure_routes', None)
            run.pop('structure_profile', None)
        else:
            run.setdefault('events', []).append({'id': 'replay-complete', 'at': stamp(), 'phase': 'complete',
                'message': 'Показан сохранённый результат; новое доказательство не выполнялось.'})
            for artifact in run.get('artifacts', []):
                artifact['url'] = '/api/research/runs/' + identifier + '/artifacts/' + artifact['path'].replace('\\', '/')
        return run


def handler_for(state):
    class Handler(BaseHTTPRequestHandler):
        def log_message(self, format, *args):
            print(stamp(), format % args, flush=True)

        def reply(self, value, status=200):
            self.body(json.dumps(value, ensure_ascii=False).encode('utf-8'), 'application/json; charset=utf-8', status)

        def body(self, content, kind, status=200):
            self.send_response(status)
            self.send_header('Content-Type', kind)
            self.send_header('Content-Length', str(len(content)))
            self.send_header('Cache-Control', 'no-store')
            self.send_header('X-Content-Type-Options', 'nosniff')
            self.send_header('X-SHAIM-Replay', 'saved-fixtures-no-model-no-lean')
            self.end_headers()
            self.wfile.write(content)

        def do_GET(self):
            parsed = urlsplit(self.path)
            path = unquote(parsed.path)
            try:
                with state.lock:
                    if path == '/api/replay/ready':
                        return self.reply(read_json(OUTPUT / 'replay-ready.json'))
                    if path == '/api/research/status':
                        return self.reply(dict(ready=True, replay_only=True, model='REPLAY — no model calls',
                            engine={'name': 'Replay сохранённых ответов'}, codex={'available': True, 'replay_only': True},
                            lean={'available': True, 'replay_only': True}, corpus=state.search.get('corpus', {})))
                    if path == '/api/graph':
                        return self.reply(read_json(ROOT / 'data/msc2020.json'))
                    if path == '/api/research/cases':
                        return self.reply(state.cases)
                    if path == '/api/structure/sources':
                        return self.reply(state.catalog)
                    if path == '/api/structure/sources/' + SOURCE:
                        return self.reply({'source': state.source})
                    if path == '/api/arxiv/papers':
                        return self.reply({'papers': [state.paper]})
                    if path == '/api/arxiv/papers/2610.38474v1':
                        return self.reply(state.paper)
                    if path == '/api/research/runs':
                        return self.reply({'runs': [state.snapshot(identifier, advance=False) for identifier in state.runs]})
                    if path == '/api/objects/graphs':
                        return self.reply({'graphs': list(state.graphs.values())})
                    if path.startswith('/api/objects/graphs/'):
                        graph = state.graphs[path.rsplit('/', 1)[1]]
                        revision = parse_qs(parsed.query).get('revision', [str(graph['revision'])])[0]
                        if revision != str(graph['revision']):
                            raise KeyError('Graph revision not in replay.')
                        return self.reply(graph)
                    match = re.fullmatch(r'/api/research/runs/([0-9a-f]{32})(?:/artifacts/(.+))?', path)
                    if match:
                        identifier, relative = match.groups()
                        if relative:
                            if identifier not in state.runs:
                                raise KeyError('Replay run not started.')
                            original = SEARCH if identifier == SEARCH_REPLAY else PROOF
                            base = (DATA / original).resolve()
                            artifact = (base / relative).resolve()
                            if not artifact.is_relative_to(base) or artifact.suffix not in ('.lean', '.json', '.log', '.txt'):
                                raise ValueError('Artifact outside recorded fixture.')
                            return self.body(artifact.read_bytes(), 'text/plain; charset=utf-8')
                        return self.reply(state.snapshot(identifier))
                    if path.startswith('/api/'):
                        raise KeyError('GET not supported by the isolated replay.')
                web = (ROOT / 'web').resolve()
                file = (web / (path.lstrip('/') or 'index.html')).resolve()
                if not file.is_relative_to(web) or not file.is_file():
                    raise KeyError('Static file not found.')
                body = file.read_bytes()
                kind = mimetypes.guess_type(file.name)[0] or 'application/octet-stream'
                if file.suffix == '.html':
                    banner = ('<aside role="status" style="position:sticky;top:0;z-index:2147483647;'
                        'padding:14px 18px;background:#8b271a;color:white;font:700 17px system-ui;'
                        'border-bottom:4px solid #ffcd70;text-align:center">' + BANNER + '</aside>')
                    body = re.sub(r'(<body\b[^>]*>)', lambda m: m.group(1) + banner,
                                  body.decode('utf-8'), count=1, flags=re.I).encode('utf-8')
                    kind = 'text/html; charset=utf-8'
                return self.body(body, kind)
            except (ValueError, KeyError, FileNotFoundError) as error:
                return self.reply({'error': str(error), 'replay_only': True}, 404)

        def do_POST(self):
            path = urlsplit(self.path).path
            payload = None
            try:
                if self.headers.get('Origin') not in (None, f'http://127.0.0.1:{state.port}', f'http://localhost:{state.port}'):
                    raise ValueError('Replay requires its own local origin.')
                if not self.headers.get('Content-Type', '').startswith('application/json'):
                    raise ValueError('JSON required.')
                size = int(self.headers.get('Content-Length', '0'))
                if not 1 <= size <= 65536:
                    raise ValueError('Replay body size rejected.')
                payload = json.loads(self.rfile.read(size))
                if not isinstance(payload, dict):
                    raise ValueError('JSON object required.')
                with state.lock:
                    if path == '/api/arxiv/import':
                        reference = payload.get('reference', '')
                        if set(payload) != {'reference'} or not isinstance(reference, str) or not re.fullmatch(
                            r'(?:arxiv:)?2610\.38474(?:v1)?|https://arxiv\.org/(?:abs|html|pdf)/2610\.38474(?:v1)?(?:\.pdf)?(?:#S9\.SS1)?', reference.strip()):
                            raise ValueError('Only the saved arXiv 2610.38474v1 article is allowed.')
                        value, code = state.paper, 200
                    elif path == '/api/research/runs':
                        value, code = state.start(payload), 202
                    else:
                        raise ValueError('POST rejected: replay never forwards or executes real actions.')
                    state.log_action(path, payload, True)
                    return self.reply(value, code)
            except (ValueError, KeyError, json.JSONDecodeError) as error:
                with state.lock:
                    state.log_action(path, payload, False, str(error))
                return self.reply({'error': str(error), 'replay_only': True}, 400)

    return Handler


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--port', type=int, default=8870)
    parser.add_argument('--get-port', type=int, default=8769)
    args = parser.parse_args()
    if not 1024 <= args.port <= 65535 or args.port == args.get_port:
        parser.error('Use a distinct local replay port.')
    state = Replay(args.port, args.get_port)
    server = ThreadingHTTPServer(('127.0.0.1', args.port), handler_for(state))
    print(json.dumps(dict(ready=True, url=f'http://127.0.0.1:{args.port}/#research',
        search_id=SEARCH_REPLAY, proof_id=PROOF_REPLAY, banner=BANNER), ensure_ascii=False), flush=True)
    server.serve_forever()


if __name__ == '__main__':
    main()
