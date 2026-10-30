#!/usr/bin/env python3
"""Exercise real localhost research lifecycle. This never requests a model run."""
import argparse
from datetime import datetime, timezone
import json
import os
from pathlib import Path
import time
import urllib.error
import urllib.parse
import urllib.request

ROOT = Path(__file__).resolve().parent


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--base-url', default=os.environ.get('ATLAS_BASE_URL', 'http://127.0.0.1:8766'))
    args = parser.parse_args()
    base = args.base_url.rstrip('/')
    if urllib.parse.urlsplit(base).hostname not in ('127.0.0.1', 'localhost'):
        raise SystemExit('This regression is restricted to localhost.')
    report = dict(checked_at=datetime.now(timezone.utc).isoformat(), base_url=base,
                  mocked=False, model_calls_started=False, checks=[], requests=[], run_id=None)

    def request(path, body=None, origin=None):
        headers = {'Accept': 'application/json'}
        data = None
        if body is not None:
            data = json.dumps(body).encode()
            headers['Content-Type'] = 'application/json'
        if origin:
            headers['Origin'] = origin
        req = urllib.request.Request(base + path, data=data, headers=headers)
        try:
            with urllib.request.urlopen(req, timeout=20) as response:
                code, raw = response.status, response.read()
        except urllib.error.HTTPError as e:
            code, raw = e.code, e.read()
        try:
            value = json.loads(raw)
        except ValueError:
            value = {'raw': raw.decode(errors='replace')[:1000]}
        report['requests'].append({'method': 'POST' if body is not None else 'GET', 'path': path, 'status': code})
        return code, value

    def check(name, fn):
        try:
            result = fn()
            report['checks'].append(dict(name=name, passed=True, evidence=result))
            print('PASS ' + name, flush=True)
            return result
        except Exception as e:
            report['checks'].append(dict(name=name, passed=False, error=str(e)))
            print('FAIL ' + name + ': ' + str(e), flush=True)
            return None

    def status(expected, response):
        code, data = response
        assert code == expected, f'Expected HTTP {expected}; got {code}: {data}'
        return data

    def poll(run_id, target, seconds=120):
        deadline = time.monotonic() + seconds
        observed = []
        while time.monotonic() < deadline:
            run = status(200, request('/api/research/runs/' + run_id))
            current = run['status']
            if not observed or observed[-1] != current:
                observed.append(current)
            if current == target:
                return run, observed
            if current not in ('queued', 'running'):
                raise AssertionError(f'Expected {target}; terminal status {current}: {run.get("error")}')
            time.sleep(.5)
        raise AssertionError(f'Timed out awaiting {target}; observed {observed}')

    initial = check('Research endpoints return saved cases and runs', lambda: {
        'cases': len(status(200, request('/api/research/cases'))['cases']),
        'runs': status(200, request('/api/research/runs'))['runs'],
    })
    initial_ids = {r['id'] for r in initial['runs']} if initial else set()
    state = {}

    def create_and_cancel():
        created = status(202, request('/api/research/runs', {
            'case_id': 'strict_inequality', 'mode': 'pilot',
            'title': 'API-проверка: остановка и продолжение локального пилота',
            'budget': {'max_calls': 0, 'timeout_seconds': 120},
        }))
        run_id = created['id']
        report['run_id'] = run_id
        state['id'], state['contract'] = run_id, created['contract_sha256']
        cancelled = status(200, request('/api/research/runs/' + run_id + '/cancel', {}))
        assert cancelled['id'] == run_id
        assert created['mode'] == 'pilot' and created['budget']['max_calls'] == 0
        final, observed = poll(run_id, 'cancelled', 30)
        assert final['usage']['calls'] == 0
        state['cancelled'] = final
        return {'run_id': run_id, 'statuses': observed, 'calls': 0, 'outcome': final['outcome']}

    created = check('Create, immediately cancel, and observe cancelled local pilot', create_and_cancel)

    def resume_idempotent():
        run_id = state['id']
        before = state['cancelled']
        state['before_verifications'] = sum(e.get('message') == 'Lean проверяет подготовленный пилот и извлекает зависимости.' for e in before['events'])
        resumed = status(202, request('/api/research/runs/' + run_id + '/resume', {}))
        assert resumed['status'] in ('queued', 'running')
        repeated = status(202, request('/api/research/runs/' + run_id + '/resume', {}))
        assert repeated['id'] == resumed['id'] == run_id
        assert repeated['status'] in ('queued', 'running')
        assert repeated['contract_sha256'] == state['contract']
        state['resume_response'] = repeated
        return {'same_id': run_id, 'status': repeated['status'], 'contract_unchanged': True}

    resumed = check('Resume while active is idempotent and preserves the contract', resume_idempotent) if created else None

    def completion():
        run, observed = poll(state['id'], 'complete', 120)
        assert run['outcome'] == 'refuted', run.get('result')
        assert run['usage']['calls'] == 0 and run['usage']['total_tokens'] == 0
        assert not run['attempts'], 'Local pilot unexpectedly created model attempts'
        assert run['contract_sha256'] == state['contract']
        launches = sum(e.get('message') == 'Lean проверяет подготовленный пилот и извлекает зависимости.' for e in run['events'])
        assert launches - state['before_verifications'] == 1, f'Duplicate work starts: {launches}'
        assert sum(e.get('phase') == 'complete' for e in run['events']) == 1
        all_runs = status(200, request('/api/research/runs'))['runs']
        assert sum(r['id'] == state['id'] for r in all_runs) == 1
        state['complete'] = run
        return {'statuses': observed, 'outcome': run['outcome'], 'calls': 0,
                'single_execution_after_resume': True, 'completion_events': 1,
                'run_was_new': state['id'] not in initial_ids}

    finished = check('Resumed pilot completes once with a real Lean refutation', completion) if resumed else None

    def persisted():
        run = status(200, request('/api/research/runs/' + state['id']))
        prior = state['complete']
        assert run['id'] == prior['id'] and run['status'] == 'complete'
        assert run['contract_sha256'] == prior['contract_sha256']
        assert run['result']['verification']['source_sha256'] == prior['result']['verification']['source_sha256']
        artifact = next(a for a in run['artifacts'] if a['path'] == 'contract-v1.json')
        artifact_body = status(200, request(artifact['url']))
        assert artifact_body == run['contract']
        return {'same_id': run['id'], 'contract_artifact_loaded': True, 'source_sha256': run['result']['verification']['source_sha256']}

    if finished:
        check('Fresh GET reloads the same result and persisted contract artifact', persisted)
        check('Completed research cannot be restarted', lambda: {'error': status(400, request('/api/research/runs/' + state['id'] + '/resume', {}))['error']})

    check('Foreign Origin is rejected before creating a run', lambda: {
        'error': status(403, request('/api/research/runs', {'case_id':'strict_inequality', 'mode':'pilot'}, origin='https://foreign.example'))['error']})
    if state.get('id'):
        check('Artifact traversal is unavailable with HTTP 404', lambda: {
            'error': status(404, request('/api/research/runs/' + state['id'] + '/artifacts/%2e%2e%2fcontract-v1.json'))['error']})
    report['passed'] = all(c['passed'] for c in report['checks'])
    report['finished_at'] = datetime.now(timezone.utc).isoformat()
    output = ROOT / 'verification/research-api.json'
    output.parent.mkdir(parents=True, exist_ok=True)
    output.write_text(json.dumps(report, ensure_ascii=False, indent=2) + '\n')
    print(json.dumps({'passed': report['passed'], 'checks': len(report['checks']), 'report': str(output)}, ensure_ascii=False))
    return 0 if report['passed'] else 1


if __name__ == '__main__':
    raise SystemExit(main())
