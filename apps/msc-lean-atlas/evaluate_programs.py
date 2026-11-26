"""Paired live Astra/Lean acceptance check. Each arm gets an isolated copy of the same seed archive."""
import argparse
from concurrent.futures import ThreadPoolExecutor
import hashlib
import json
from pathlib import Path
import shutil
import time

import research_lean
from research_programs import ProgramService
from research_service import ResearchService, atomic, now, sha

ROOT = Path(__file__).resolve().parent


def cases():
    graph = next(c['agent_task'] for c in research_lean.fixtures() if c['id'] == 'graph_energy')
    graph_env = {k:graph[k] for k in ('imports','prelude')}
    def task(name, statement, question, environment, direction='prove'):
        return dict(name=name.rsplit('.',1)[-1], question=question, direction=direction,
                    base=dict(target=name, statement=statement, **environment))
    return [
        task('Heldout.mono_second_edge',
             '∀ (w01 a b w02 x0 x1 x2 : ℝ), a ≤ b → '
             'TriangleEnergy.laplacianForm w01 a w02 x0 x1 x2 ≤ TriangleEnergy.laplacianForm w01 b w02 x0 x1 x2',
             'Докажите, что увеличение веса ребра 1–2 взвешенного треугольника при фиксированных остальных данных '
             'не уменьшает квадратичную форму лапласиана.',graph_env),
        task('Heldout.refute_third_edge',
             '∀ (w01 w12 a b x0 x1 x2 : ℝ), a < b → '
             'TriangleEnergy.laplacianForm w01 w12 a x0 x1 x2 < TriangleEnergy.laplacianForm w01 w12 b x0 x1 x2',
             'Опровергните утверждение, что строгое увеличение веса ребра 0–2 при фиксированных остальных данных '
             'всегда строго увеличивает квадратичную форму треугольника.',graph_env,'refute'),
        task('Heldout.strict_quadratic',
             '∀ x y : ℝ, x ≠ y → 2 * x * y < x ^ 2 + y ^ 2',
             'Докажите строгое неравенство 2xy < x² + y² для двух различных действительных чисел.',
             dict(imports=['Mathlib.Data.Real.Basic','Mathlib.Tactic.Linarith'], prelude=''))
    ]


def seed(root, source):
    if source is None:
        return sha([])
    old, new = source, root/source.name
    source_files = [old/'plan.json', old/'proofs.json', old/'run.json', *sorted(old.glob('lean/**/Candidate.lean')),
                    *sorted(old.glob('lean/**/verification.json'))]
    manifest = []
    for path in source_files:
        relative = path.relative_to(old)
        dest = new / relative
        dest.parent.mkdir(parents=True, exist_ok=True)
        shutil.copyfile(path, dest)
        manifest.append((relative.as_posix(), hashlib.sha256(dest.read_bytes()).hexdigest()))
    return sha(manifest)


def run_arm(case, arm, root, budget, archive_seed=None):
    root.mkdir(parents=True, exist_ok=False)
    seed_hash = seed(root, archive_seed)
    research = ResearchService(root, recover=False)
    program = ProgramService(research, recover=False) if arm == 'program' else None
    base = case['base']
    fixed = dict(base, statement='¬ ('+base['statement']+')') if case['direction']=='refute' else base
    payload = dict(question=case['question'],budget=budget)
    started = time.monotonic()
    # Both arms receive the exact same signed proposition and toolchain.
    # The theorem here is the negation itself for a refutation question.
    if program:
        entity = program.create(payload, goal_task=fixed)
    else:
        entity = research.create(dict(payload,mode='multi'),fixed_task=fixed)
    print(json.dumps(dict(case=case['name'],arm=arm,id=entity['id'],started=now())),flush=True)
    atomic(root/'evaluation-job.json', dict(id=entity['id'], arm=arm, case=case['name'], budget=budget))
    while True:
        state = (program or research).get(entity['id'])
        if state['status'] not in {'queued','running'}:
            break
        time.sleep(1)
    research.pool.shutdown(wait=True)
    state = (program or research).get(entity['id'])
    children = [research.get(t['run_id']) for t in state['tasks'] if t.get('run_id')] if program else [state]
    checked = []
    for child in children:
        report = (child.get('result') or {}).get('verification') or {}
        certificate = Path(report.get('workspace',''))/'Candidate.lean'
        content_hash = hashlib.sha256(certificate.read_bytes()).hexdigest() if certificate.is_file() else None
        exact = bool(report.get('success') and report.get('target_preserved') and report.get('audit',{}).get('status')=='passed'
                     and report.get('target')==fixed['target'] and report.get('expected_statement')==fixed['statement']
                     and content_hash and content_hash==report.get('source_sha256'))
        artifact = certificate.relative_to(root).as_posix() if certificate.is_file() and certificate.is_relative_to(root) else None
        checked.append(dict(run_id=child['id'],status=child['status'],outcome=child['outcome'],error=child.get('error'),
                exact_goal_checked=exact,semantic_review=(child.get('semantic_review') or {}).get('status'),
                archive_card=(child.get('library_selected') or {}).get('id'),
                proof_dependencies=child.get('library_dependencies',[]),source_sha256=content_hash,source=artifact,
                lean_version=(report.get('context') or {}).get('lean_version'),
                mathlib_revision=(report.get('context') or {}).get('mathlib_revision')))
    solved = any(c['exact_goal_checked'] and c['semantic_review']=='aligned' and c['outcome'] in {'proved','refuted'} for c in checked)
    usage = state['usage']
    item = dict(case=case['name'],arm=arm,id=entity['id'],status=state['status'],reason=state.get('error') or state.get('reason'),
                fixed_goal_sha256=sha(fixed),seed_sha256=seed_hash,max_calls=budget['max_calls'],timeout_seconds=budget['timeout_seconds'],
                solved=solved,answer=('refuted' if case['direction']=='refute' else 'proved') if solved else 'unknown',
                calls=usage['calls'],tokens=usage['total_tokens'],elapsed_seconds=round(time.monotonic()-started,2),
                workspace=str(root),children=checked)
    atomic(root/'evaluation-result.json',item)
    print(json.dumps({k:item[k] for k in ('case','arm','status','answer','calls','tokens','elapsed_seconds')}),flush=True)
    return item


def audit_results(report):
    """Verify saved model receipts, paired contracts and Lean source fingerprints without making calls."""
    for item in report['results']:
        root = Path(item['workspace'])
        contracts, models = [], set()
        for child in item['children']:
            folder = root / child['run_id']
            state = json.loads((folder/'run.json').read_text())
            contracts.append(sha(state['contract']['agent_task']))
            for receipt in folder.glob('attempts/*/result.json'):
                response = json.loads(receipt.read_text())
                if response.get('model'):
                    models.add(response['model'])
            if child['source']:
                data = (root/child['source']).read_bytes()
                if hashlib.sha256(data).hexdigest() != child['source_sha256']:
                    raise ValueError('Изменился проверенный исходник: '+child['source'])
        item['recorded_child_contracts'] = contracts
        item['observed_models'] = sorted(models)
        if item['solved'] and (item['fixed_goal_sha256'] not in contracts or models != {'gpt-6-astra'}):
            raise ValueError('Подтверждение модели или постановки расходится с результатом.')
    report['paired_inputs_equal'] = all(
        len({(r['fixed_goal_sha256'],r['seed_sha256']) for r in report['results'] if r['case']==c['name']}) == 1
        for c in report['tasks'])
    for arm in ('multi','program'):
        results = [r for r in report['results'] if r['arm']==arm]
        report.setdefault('totals',{})[arm] = dict(solved=sum(r['solved'] for r in results),
            refuted=sum(r['answer']=='refuted' for r in results),calls=sum(r['calls'] for r in results),
            tokens=sum(r['tokens'] for r in results),elapsed_seconds=round(sum(r['elapsed_seconds'] for r in results),2),
            compiled_cross_run_edges=sum(len(child['proof_dependencies']) for r in results for child in r['children']))
    return report


def evaluate(workspace, output, max_calls=8, timeout_seconds=420, archive_seed=None):
    workspace, output = Path(workspace).resolve(), Path(output).resolve()
    # Never dispatch duplicate paid turns when pointed at an existing benchmark.
    if archive_seed is not None:
        archive_seed = Path(archive_seed).resolve()
        if not all((archive_seed/name).is_file() for name in ('run.json','plan.json','proofs.json')):
            raise ValueError('Expected a completed run with run.json, plan.json and proofs.json')
    if output.exists():
        raise FileExistsError('A previous report exists: '+str(output))
    workspace.mkdir(parents=True, exist_ok=False)
    budget = dict(max_calls=max_calls,timeout_seconds=timeout_seconds)
    suite = cases()
    report = dict(protocol='heldout-paired-astra-v1',started_at=now(),model='gpt-6-astra',transport='codex-app-server',
                  tasks=suite, shared_limits=budget,archive_seed_run=archive_seed.name if archive_seed else None,independent_roots=True,
                  note='Small fixed-task acceptance sample; task statements contain no reference proofs. A negated exact goal counts as a checked refutation.',
                  results=[])
    atomic(output, report)
    with ThreadPoolExecutor(max_workers=2) as pool:
        for case in suite:
            pair = [pool.submit(run_arm,case,arm,workspace/case['name']/arm,budget,archive_seed) for arm in ('multi','program')]
            for future in pair:
                report['results'].append(future.result())
                atomic(output,report)
    report['finished_at'] = now()
    atomic(output,audit_results(report))
    return report


if __name__=='__main__':
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--workspace',type=Path,default=ROOT/'runs'/'program-evaluation-2026-11-24')
    p.add_argument('--output',type=Path,default=ROOT/'verification'/'program-evaluation-2026-11-24.json')
    p.add_argument('--archive-seed',type=Path,help='Optional directory of a local completed AMR run shared by both arms.')
    p.add_argument('--max-calls',type=int,default=8)
    p.add_argument('--timeout-seconds',type=int,default=420)
    p.add_argument('--verify-only',action='store_true',help='Recheck the saved report and its files without using the model.')
    args=p.parse_args()
    if args.verify_only:
        report = json.loads(args.output.read_text())
        if not report.get('finished_at'):
            p.error('The paired run is still in progress.')
        atomic(args.output,audit_results(report))
    else:
        evaluate(args.workspace,args.output,args.max_calls,args.timeout_seconds,args.archive_seed)
