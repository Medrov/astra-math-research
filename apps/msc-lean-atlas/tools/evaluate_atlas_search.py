#!/usr/bin/env python3
"""Offline atlas inventory/shortlist regression, not semantic or proof accuracy."""
from __future__ import annotations
import argparse
import hashlib
import json
from pathlib import Path
import sys
import time

ROOT=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT))
import research_atlas as atlas


def _memory():
    if sys.platform!='win32':
        return dict(status='not_measured')
    import ctypes
    from ctypes import wintypes
    class Counters(ctypes.Structure):
        _fields_=[('cb',wintypes.DWORD),('PageFaultCount',wintypes.DWORD)]+[(name,ctypes.c_size_t) for name in
            ('PeakWorkingSetSize','WorkingSetSize','QuotaPeakPagedPoolUsage','QuotaPagedPoolUsage',
             'QuotaPeakNonPagedPoolUsage','QuotaNonPagedPoolUsage','PagefileUsage','PeakPagefileUsage')]
    counters=Counters();counters.cb=ctypes.sizeof(counters)
    ctypes.windll.kernel32.GetCurrentProcess.restype=wintypes.HANDLE
    fn=ctypes.windll.psapi.GetProcessMemoryInfo
    fn.argtypes=[wintypes.HANDLE,ctypes.POINTER(Counters),wintypes.DWORD]
    if not fn(ctypes.windll.kernel32.GetCurrentProcess(),ctypes.byref(counters),counters.cb):
        return dict(status='unavailable')
    return dict(status='measured_process_working_set',peak_bytes=counters.PeakWorkingSetSize,current_bytes=counters.WorkingSetSize)


def measure_local():
    """Read-only performance probe of the installed index; no model or Lean."""
    started=time.monotonic()
    profile=dict(summary='Polynomial quotient factorization',objects=['polynomial','ring'],operations=['evaluation'],
        assumptions=['commutative ring'],conclusion_shape='factorization',mechanism='ideal quotient kernel homomorphism')
    source=dict(source_sha256=atlas.digest(profile),selected_declaration=dict(type='commutative ring ideal quotient'))
    print('Reading installed index for local coverage measurement.',flush=True)
    snapshot=atlas.local_screen(source,profile)
    print('Local scan returned; measuring snapshot and overview.',flush=True)
    result=atlas.overview(snapshot,atlas.new_progress(snapshot))
    return dict(schema_version=1,kind='read_only_installed_corpus_performance',
        elapsed_seconds=round(time.monotonic()-started,3),corpus_records_processed=snapshot['corpus_records_processed'],
        snapshot_bytes=len(json.dumps(snapshot,ensure_ascii=False).encode('utf-8')),
        overview_bytes=len(json.dumps(result,ensure_ascii=False).encode('utf-8')),summary=result['summary'],
        memory=_memory(),
        interruption=snapshot['interruption'],corpus_manifest=snapshot['corpus_manifest'],
        usage=dict(model=None,model_calls=0,input_tokens=0,output_tokens=0),
        passed=snapshot['local_queries_complete'],limitations=atlas.LIMITATIONS)


def evaluate(fixture_path=None):
    path=Path(fixture_path or ROOT/'benchmarks/atlas-search.json')
    raw=path.read_bytes();fixture=json.loads(raw)
    inventory_raw=atlas.ATLAS_PATH.read_bytes();inventory=json.loads(inventory_raw)
    started=time.monotonic();rows=[]
    for case in fixture['cases']:
        profile=dict(summary=case['mechanism'],objects=[],operations=[],assumptions=[],
                     conclusion_shape='research proposal, not theorem',mechanism=case['mechanism'])
        source=dict(source_sha256=atlas.digest(case),selected_declaration=dict(type=case['mechanism']))
        snapshot=atlas.screen(inventory,fixture['records'],source,profile,options=fixture['options'],
            corpus_manifest=dict(status='ready',fixture_sha256=hashlib.sha256(raw).hexdigest()),
            atlas_sha256=hashlib.sha256(inventory_raw).hexdigest())
        progress=atlas.new_progress(snapshot);summary=atlas.overview(snapshot,progress)['summary']
        node=next(n for n in snapshot['nodes'] if n['code']==case['code'])
        ids=set(node['pool_ids'])|set(snapshot['global_channel']['pool_ids'])
        relevant=set(case['relevant'])
        rows.append(dict(id=case['id'],split=case['split'],code=case['code'],snapshot_sha256=snapshot['snapshot_sha256'],
            inventory_coverage=summary['queried_codes']/summary['total_codes'],
            positive_pool_recall=len(ids&relevant)/len(relevant) if relevant else None,
            global_pool_ids=snapshot['global_channel']['pool_ids'],code_pool_ids=node['pool_ids'],
            known_relevant=sorted(relevant),negative_control=case.get('negative_control'),
            candidates_generated=0,proof_verified=summary['proof_verified'],
            semantic_assessment='not_run',deep_queue_count=summary['queue_total']))
    thresholds=fixture['thresholds']
    checks=dict(all_codes_queried=all(x['inventory_coverage']>=thresholds['min_inventory_coverage'] for x in rows),
        known_source_recall=all(x['positive_pool_recall']>=thresholds['min_positive_pool_recall'] for x in rows if x['positive_pool_recall'] is not None),
        no_fabricated_proof=all(x['proof_verified']<=thresholds['max_proof_verified'] for x in rows),
        empty_control=all(not x['global_pool_ids'] for x in rows if x['negative_control']=='empty_global_pool_expected'),
        lexical_collision_retained_as_unassessed=all(x['global_pool_ids'] and x['candidates_generated']==0 for x in rows if x['negative_control']=='lexical_hits_are_not_candidates'))
    return dict(schema_version=1,benchmark=fixture['name'],fixture_sha256=hashlib.sha256(raw).hexdigest(),
        atlas_sha256=hashlib.sha256(inventory_raw).hexdigest(),thresholds=thresholds,checks=checks,passed=all(checks.values()),
        cases=rows,corpus_records=len(fixture['records']),mathlib_revision=fixture['mathlib_revision'],
        usage=dict(model=None,model_calls=0,input_tokens=0,output_tokens=0,seed=None,elapsed_seconds=round(time.monotonic()-started,3)),
        limitations=[fixture['labeling'],'All records remain textual snapshots, not newly compiler-checked declarations.',
            'Local shortlist recall is measured; semantic abstention, mathematical novelty and proof success are not measured.',
            'Known negative labels describe these controls, not impossibility of any mathematical bridge.'])


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--fixture',type=Path)
    parser.add_argument('--local-performance',action='store_true')
    parser.add_argument('--output',type=Path,default=ROOT/'verification/atlas-search-benchmark.json')
    args=parser.parse_args();result=measure_local() if args.local_performance else evaluate(args.fixture)
    args.output.parent.mkdir(parents=True,exist_ok=True)
    args.output.write_text(json.dumps(result,ensure_ascii=False,indent=2)+'\n',encoding='utf-8')
    print(json.dumps(dict(output=str(args.output.resolve()),passed=result['passed'],checks=result.get('checks'),usage=result['usage'],
                         elapsed_seconds=result.get('elapsed_seconds')),ensure_ascii=False))
    return 0 if result['passed'] else 1


if __name__=='__main__':raise SystemExit(main())
