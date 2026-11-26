"""Build a small certified archive from the checked-in mathematical examples."""
from functools import lru_cache
import json
from pathlib import Path
import shutil
import sys
import tempfile
import unittest

import lean_service
import research_lean
from research_registry import source_prefix

def isolated_lean_available():
    env = lean_service.default_context()
    isolation = ((sys.platform == 'darwin' and Path('/usr/bin/sandbox-exec').is_file())
                 or (sys.platform.startswith('linux') and shutil.which('bwrap')))
    return bool(isolation and Path(env['lean']).is_file() and env['mathlib'] and Path(env['mathlib']).is_dir())


GRAPH_RUN = 'a1' * 16
REFUTE_RUN = 'b2' * 16


@lru_cache(maxsize=2)
def _compiled_fixture(case):
    env = lean_service.default_context()
    if not Path(env['lean']).is_file() or not env['mathlib'] or not Path(env['mathlib']).is_dir():
        raise unittest.SkipTest('Prepared Lean and mathlib required for a certified archive')
    root = tempfile.TemporaryDirectory(prefix='shaim-test-fixture-')
    run_id = GRAPH_RUN if case == 'graph_energy' else REFUTE_RUN
    fixture = next(item for item in research_lean.fixtures() if item['id'] == case)
    task = fixture['agent_task']
    run_dir = Path(root.name) / run_id
    run_dir.mkdir()
    if case == 'graph_energy':
        declarations = [
            ('TriangleEnergy.graph_energy_eq', research_lean.ENERGY_STATEMENT,
             'by intro w01 w12 w02 x0 x1 x2; unfold TriangleEnergy.graphEnergy TriangleEnergy.laplacianForm; ring'),
            ('TriangleEnergy.laplacian_nonnegative', research_lean.NONNEGATIVE_STATEMENT,
             'by intro w01 w12 w02 x0 x1 x2 h01 h12 h02; rw [← TriangleEnergy.graph_energy_eq]; unfold TriangleEnergy.graphEnergy; positivity'),
        ]
    else:
        declarations = [(task['target'], task['statement'], 'by intro h; have hzero := h 0 0; norm_num at hzero')]
    plan = dict(imports=task['imports'], prelude=task['prelude'], target_id=declarations[-1][0], nodes=[])
    proofs = {}
    source = source_prefix(plan)
    for name, statement, proof in declarations:
        plan['nodes'].append(dict(id=name, statement=statement))
        source += f'theorem {name} : {statement} := {proof}\n\n'
        receipt = research_lean.verify_candidate(source, name, run_dir / 'lean' / name, statement)
        if not receipt['success']:
            raise AssertionError(receipt.get('error'))
        proofs[name] = dict(verification=receipt)
    run = dict(id=run_id, mode='multi', status='complete', outcome=fixture['expected_outcome'], claim=fixture['claim'],
               msc_codes=fixture['msc_codes'], semantic_review=dict(status='aligned'), contract={})
    for path, value in [('plan.json', plan), ('proofs.json', proofs), ('run.json', run)]:
        (run_dir / path).write_text(json.dumps(value), encoding='utf-8')
    return root, run_dir


def archive_fixture(destination, case='graph_energy'):
    _, original = _compiled_fixture(case)
    target = Path(destination) / original.name
    shutil.copytree(original, target, ignore=shutil.ignore_patterns('*.olean', 'Atlas*.lean', 'SHAIMKernel.lean'))
    return target
