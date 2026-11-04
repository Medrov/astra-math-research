"""Compare native and adapted Goedel on fixed existing cases.

Default: print/save the protocol, without a model call. --live explicitly starts
account-usage research runs. --report reads an existing report without dispatch.
"""
from __future__ import annotations

import argparse
import copy
import json
from pathlib import Path
import sys
import time

APP = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(APP))
import research_service as rs
import research_goedel as goedel

PROTOCOL = Path(__file__).with_name('backend-benchmark.json')


def formal_input(run):
    contract = run.get('formal_contract') or run['contract'].get('agent_task') or {}
    values = {key: contract.get(key, [] if key in ('imports', 'required_obligations') else '')
              for key in ('target', 'statement', 'imports', 'prelude', 'required_obligations')}
    values['source_library_sha256'] = (run['contract'].get('source_library') or {}).get('source_sha256')
    values['source_transition_hash'] = run['contract'].get('source_transition_hash')
    values['question'] = run['contract'].get('question')
    return values


def measured_run(run):
    verification = (run.get('result') or {}).get('verification') or {}
    semantic = run.get('final_semantic_review') or run.get('semantic_review') or {}
    all_goals = bool(verification.get('success') and verification.get('target_preserved')
                     and verification.get('obligations_passed'))
    return dict(id=run['id'], case_id=run.get('case_id'), backend=run.get('proof_backend', 'native'),
                mode=run['mode'], status=run['status'], phase=run['phase'], outcome=run['outcome'],
                formal_outcome=run.get('formal_outcome'), formal_input_sha256=rs.sha(formal_input(run)),
                budget=run['budget'], usage=run['usage'], termination=run.get('termination'), error=run.get('error'),
                all_required_goals_lean_checked=all_goals, semantic_status=semantic.get('status'),
                fully_accepted=bool(all_goals and semantic.get('status') == 'aligned'),
                source_sha256=verification.get('source_sha256'),
                backend_metadata=run.get('proof_backend_metadata'),
                environment_fingerprint=verification.get('environment_fingerprint'),
                attempts=[{key: a.get(key) for key in ('id', 'role', 'status', 'accounted_tokens', 'usage', 'error')}
                          for a in run.get('attempts', [])])


def summarize(report):
    runs = report.get('runs', [])
    pairs = []
    for case in report.get('selected_cases', []):
        entries = [r for r in runs if r['case_id'] == case]
        complete_pair = len(entries) == 2 and {r['backend'] for r in entries} == {'native', goedel.BACKEND_ID}
        paired_inputs = complete_pair and len({r['formal_input_sha256'] for r in entries}) == 1
        paired_budgets = complete_pair and len({rs.sha(r['budget']) for r in entries}) == 1
        paired_modes = complete_pair and len({r['mode'] for r in entries}) == 1
        envs = [r.get('environment_fingerprint') for r in entries]
        same_checked_environment = complete_pair and all(envs) and len({rs.sha(v) for v in envs}) == 1
        pairs.append(dict(case_id=case, complete_pair=complete_pair,
                          exact_inputs_equal=paired_inputs, caps_equal=paired_budgets, mode_equal=paired_modes,
                          checked_environments_equal=bool(same_checked_environment),
                          comparable=bool(paired_inputs and paired_budgets and paired_modes and same_checked_environment)))
    totals = {}
    for backend in ('native', goedel.BACKEND_ID):
        selected = [r for r in runs if r['backend'] == backend]
        totals[backend] = dict(runs=len(selected), fully_accepted=sum(r['fully_accepted'] for r in selected),
            all_required_goals_lean_checked=sum(r['all_required_goals_lean_checked'] for r in selected),
            actual_calls=sum(r['usage'].get('calls', 0) for r in selected),
            actual_tokens=sum(r['usage'].get('total_tokens', 0) for r in selected),
            actual_elapsed_seconds=sum(r['usage'].get('elapsed_seconds', 0) for r in selected))
    return dict(pairs=pairs, totals=totals,
                interpretation='Measured engineering runs; unequal actual resource use and small sample do not establish superiority.')


def evaluate(output, *, case_ids=None, calls=None, seconds=None, work_dir=None):
    protocol = json.loads(PROTOCOL.read_text(encoding='utf-8'))
    case_ids = case_ids or protocol['default_case_ids']
    known = {row['case_id'] for row in protocol['cases']}
    if not case_ids or len(set(case_ids)) != len(case_ids) or any(case not in known for case in case_ids):
        raise ValueError('Choose distinct existing cases from the fixed benchmark protocol.')
    budget = copy.deepcopy(protocol['budget_per_run'])
    if calls is not None:
        budget['max_calls'] = calls
    if seconds is not None:
        budget['timeout_seconds'] = seconds
    output = Path(output).resolve()
    output.parent.mkdir(parents=True, exist_ok=True)
    work = Path(work_dir or APP / 'verification' / 'backend-runs').resolve()
    service = rs.ResearchService(root=work, recover=False)
    report = dict(protocol=protocol, selected_cases=case_ids, budget_per_run=budget,
                  backend=goedel.backend_metadata(), workspace=str(work), started_at=rs.now(), runs=[], status='running')
    rs.atomic(output, report)
    try:
        for case_id in case_ids:
            for backend in protocol['backends']:
                run = service.create(dict(case_id=case_id, mode=protocol['mode'], proof_backend=backend, budget=budget))
                report['runs'].append(measured_run(run))
                rs.atomic(output, report)
                print(json.dumps(dict(created=run['id'], case_id=case_id, backend=backend)), flush=True)
                future = service.futures[run['id']]
                previous = None
                while not future.done():
                    entry = measured_run(service.get(run['id']))
                    if entry != previous:
                        report['runs'][-1] = entry
                        rs.atomic(output, report)
                        previous = entry
                    time.sleep(1)
                future.result()
                report['runs'][-1] = measured_run(service.get(run['id']))
                rs.atomic(output, report)
        report.update(status='complete', summary=summarize(report))
    except BaseException as error:
        report.update(status='interrupted', error=str(error))
        for entry in report['runs']:
            service.cancel(entry['id'])
        raise
    finally:
        service.pool.shutdown(wait=True)
        report['finished_at'] = rs.now()
        rs.atomic(output, report)
    return report


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    mode = parser.add_mutually_exclusive_group()
    mode.add_argument('--live', action='store_true', help='Dispatch bounded account-usage model runs.')
    mode.add_argument('--report', type=Path, help='Read and summarize an existing report only.')
    parser.add_argument('--output', default=str(APP / 'verification' / 'backend-evaluation.json'))
    parser.add_argument('--work-dir', help='Research workspace; default stays inside the application verification directory.')
    parser.add_argument('--cases', nargs='+')
    parser.add_argument('--calls', type=int)
    parser.add_argument('--seconds', type=int)
    args = parser.parse_args()
    if args.live:
        value = evaluate(args.output, case_ids=args.cases, calls=args.calls, seconds=args.seconds, work_dir=args.work_dir)
    elif args.report:
        value = summarize(json.loads(args.report.read_text(encoding='utf-8')))
    else:
        value = dict(status='protocol_only_no_model_calls', protocol=json.loads(PROTOCOL.read_text(encoding='utf-8')))
    print(json.dumps(value, ensure_ascii=False, indent=2))
