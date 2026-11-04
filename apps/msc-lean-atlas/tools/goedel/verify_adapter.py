"""Real Lean compatibility check using the existing graph_energy solution.

No model is called. This is an available-solution replay, not an evaluation of
autonomous discovery or semantic review. Artifacts are stored in the given path.
"""
from __future__ import annotations

import argparse
import json
from pathlib import Path
import sys
import threading
import time
from unittest.mock import patch

APP = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(APP))
import research_goedel as goedel
import research_lean
import research_service as rs


def run(output, work_dir=None):
    output = Path(output).resolve()
    output.mkdir(parents=True, exist_ok=True)
    work = Path(work_dir or APP / 'verification' / 'goedel-compatibility').resolve()
    work.mkdir(parents=True, exist_ok=True)
    service = rs.ResearchService(root=work / 'replay', recover=False)
    report = dict(kind='goedel_adapter_compatibility', backend=goedel.backend_metadata(),
                  source='existing graph_energy fixture',
                  methodology='available_solution_replay_not_blind_rediscovery',
                  model_calls=0, semantic_review='not_performed', novelty='not_assessed',
                  seed=None, seed_note='Deterministic known-solution replay; no sampling.',
                  objective='All existing energy obligations pass independent pinned Lean verification.',
                  stop_condition='One blueprint, two nodes and one final composition; abort on failure.',
                  success=False, started_at=rs.now())
    try:
        created = service.create(dict(case_id='graph_energy', mode='single', proof_backend=goedel.BACKEND_ID,
            budget=dict(max_calls=4, timeout_seconds=600)), start=False)
        rid = created['id']
        report['run_id'] = rid
        service._started[rid] = time.monotonic()
        service.cancel_flags[rid] = threading.Event()
        task = service._effective_task(created)
        first, second = task['required_obligations']
        plan = dict(imports=task['imports'], prelude=task['prelude'], summary='Replay the checked graph-energy solution.',
                    assumptions=[], relation_kind='representation', target_id=task['target'], nodes=[
            dict(id=first['target'], title='Energy identity', statement=first['statement'], dependencies=[],
                 proof='by\n  intro w01 w12 w02 x0 x1 x2\n  unfold TriangleEnergy.graphEnergy TriangleEnergy.laplacianForm\n  ring'),
            dict(id=second['target'], title='Transfer nonnegativity', statement=second['statement'], dependencies=[first['target']],
                 proof='by\n  intro w01 w12 w02 x0 x1 x2 h01 h12 h02\n  rw [← TriangleEnergy.graph_energy_eq]\n  unfold TriangleEnergy.graphEnergy\n  positivity')])
        plan = goedel.validate_blueprint(plan, task)
        service._formal_contract(rid, plan)
        service._save_plan(rid, plan)
        # Any accidental inference makes the compatibility check fail.
        with patch.object(service, '_call', side_effect=AssertionError('Compatibility replay must never call a model.')):
            result = goedel.build_proofs(service, rid)
        if result is None:
            raise ValueError('Replay did not close every required goal.')
        plan, established, contract = result
        final_source = service._source(plan, established)
        final = research_lean.verify_candidate(final_source, contract['target'], work / 'composition',
            expected_statement=contract['statement'], required_obligations=contract['required_obligations'])
        report.update(success=bool(final.get('success')), verification=final,
                      budget=created['budget'], node_count=len(established),
                      upstream_grafts=sum(bool(p.get('upstream_graft')) for p in established.values()),
                      model_calls=service.get(rid)['usage']['calls'],
                      artifact_directory=str(service.folder(rid)))
        service.update(rid, status='complete', outcome='unknown', formal_outcome='proved' if final.get('success') else 'unknown',
            result=dict(status='complete', outcome='unknown', verification=final,
                        semantic_review=dict(status='not_performed', reason='Compatibility replay only.')))
    except Exception as error:
        report['error'] = str(error)
    finally:
        service.pool.shutdown(wait=True)
        report['finished_at'] = rs.now()
        rs.atomic(output / 'compatibility.json', report)
    return report


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', required=True)
    parser.add_argument('--work-dir', help='Lean workspace; default is inside the application verification directory.')
    args = parser.parse_args()
    result = run(args.output, args.work_dir)
    print(json.dumps({k: result.get(k) for k in ('success', 'run_id', 'node_count', 'upstream_grafts', 'model_calls', 'error')}, ensure_ascii=False))
    sys.exit(0 if result.get('success') else 1)
