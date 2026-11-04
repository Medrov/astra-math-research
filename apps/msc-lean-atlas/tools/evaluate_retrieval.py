#!/usr/bin/env python3
"""Fixed, offline retrieval regression. No model dispatch, downloads or proof runs.

Optional --rankings scores previously captured model assessments; without it the
semantic component is explicitly NOT measured. The fixture is a small developer-
labelled regression set, not evidence of scientific novelty or general accuracy.
"""
from __future__ import annotations

import argparse
from datetime import datetime, timezone
import hashlib
import json
import math
from pathlib import Path
import sqlite3
import sys
import tempfile
import time

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))
import research_retrieval as retrieval
from research_structure import validate_ranking


def metrics(ids, relevance, k=5):
    relevant = {key for key, grade in relevance.items() if grade > 0}
    top = ids[:k]
    dcg = sum((2 ** relevance.get(key, 0) - 1) / math.log2(rank + 2) for rank, key in enumerate(top))
    ideal = sum((2 ** grade - 1) / math.log2(rank + 2)
                for rank, grade in enumerate(sorted(relevance.values(), reverse=True)[:k]))
    return dict(precision_at_5=sum(key in relevant for key in top) / k,
                recall_at_5=len(set(top) & relevant) / len(relevant) if relevant else None,
                ndcg_at_5=dcg / ideal if ideal else None,
                recall_in_pool=len(set(ids) & relevant) / len(relevant) if relevant else None,
                negative_has_hits=bool(ids) if not relevant else None,
                returned=len(ids), top_ids=top)


def build_fixture_index(path, records):
    connection = sqlite3.connect(path)
    try:
        retrieval._schema(connection)
        for record in records:
            cursor = connection.execute('INSERT INTO declarations(id,file,payload) VALUES (?,?,?)',
                (record['id'], record['file'], json.dumps(record, ensure_ascii=False)))
            connection.execute('INSERT INTO declaration_search(rowid,name,module,signature,documentation) VALUES (?,?,?,?,?)',
                (cursor.lastrowid, retrieval._split_names(record['name']), retrieval._split_names(record['module']),
                 retrieval._split_names(record['statement']), record.get('doc_comment', '')))
        connection.commit()
    finally:
        connection.close()


def _aggregate(rows):
    summary = {}
    for name in ('lexical_only', 'hybrid_pool', 'semantic_reranked'):
        groups = {}
        for split in ('development', 'held_out', 'negative'):
            values = [row[name] for row in rows if row['split'] == split and name in row]
            averages = {}
            for key in ('precision_at_5', 'recall_at_5', 'ndcg_at_5', 'recall_in_pool', 'negative_has_hits'):
                present = [float(value[key]) for value in values if value[key] is not None]
                averages[key] = round(sum(present) / len(present), 6) if present else None
            groups[split] = dict(cases=len(values), **averages)
        summary[name] = groups
    return summary


def evaluate(fixture_path=None, rankings_path=None):
    path = Path(fixture_path or ROOT / 'benchmarks/retrieval_v1.json')
    raw = path.read_bytes()
    fixture = json.loads(raw)
    fixture_hash = hashlib.sha256(raw).hexdigest()
    captured = None
    if rankings_path:
        captured = json.loads(Path(rankings_path).read_text(encoding='utf-8'))
        if captured.get('fixture_sha256') != fixture_hash or not captured.get('model') or not isinstance(captured.get('usage'), dict):
            raise ValueError('Captured ranking requires matching fixture hash, actual model and usage metadata.')
        if not isinstance(captured.get('assessments'), dict):
            raise ValueError('Captured ranking requires per-case assessments and exact pool hashes.')
    started, rows = time.monotonic(), []
    with tempfile.TemporaryDirectory(prefix='retrieval-benchmark-') as temporary:
        index = Path(temporary) / 'snapshot.sqlite'
        build_fixture_index(index, fixture['records'])
        for case in fixture['cases']:
            case_started = time.monotonic()
            lexical = {}
            for query in case['queries']:
                for rank, hit in enumerate(retrieval.search_library(query, limit=8, index_path=index), 1):
                    lexical[hit['id']] = lexical.get(hit['id'], 0) + 1 / (60 + rank)
            baseline = sorted(lexical, key=lambda key: (-lexical[key], key))[:5]
            pool = retrieval.hybrid_pool(case['queries'], case['profile'], case['source_statement'], limit=24, index_path=index)
            pool_hash = hashlib.sha256(json.dumps(pool, sort_keys=True, ensure_ascii=False).encode()).hexdigest()
            row = dict(id=case['id'], split=case['split'], queries=case['queries'],
                       source_statement=case['source_statement'], relevance=case['relevance'], pool_sha256=pool_hash,
                       lexical_only=metrics(baseline, case['relevance']),
                       hybrid_pool=metrics([hit['id'] for hit in pool], case['relevance']))
            if captured and case['id'] in captured['assessments']:
                assessment = captured['assessments'][case['id']]
                if assessment.get('pool_sha256') != pool_hash:
                    raise ValueError('Captured semantic ranking uses a different pool: ' + case['id'])
                selected = validate_ranking(assessment['response'], pool)
                row['semantic_reranked'] = metrics([hit['id'] for hit in selected], case['relevance'])
            row['elapsed_seconds'] = round(time.monotonic() - case_started, 6)
            rows.append(row)
    return dict(schema_version=1, benchmark=fixture['name'], measured_at=datetime.now(timezone.utc).isoformat(),
                fixture_sha256=fixture_hash, corpus_records=len(fixture['records']), cases=rows, summary=_aggregate(rows),
                mathlib_revision=fixture['mathlib_revision'], source_status='fixed_textual_snapshots_not_elaborated_types',
                baseline='current-tokenizer FTS5 rank fusion, top 5; no model semantic ranking',
                hybrid='lexical + explicit vocabulary expansion + textual type-signature channel; pool up to 24',
                semantic_reranking=dict(status='scored_captured_outputs' if captured else 'not_run',
                    model=captured.get('model') if captured else None,
                    captured_usage=captured.get('usage') if captured else None,
                    reason=None if captured else 'No paid model calls for ordinary tests. Semantic quality is not measured by lexical overlap.'),
                execution_usage=dict(model_calls=0,input_tokens=0,output_tokens=0,model=None,seed=None,
                                     elapsed_seconds=round(time.monotonic()-started,6)),
                limitations=[fixture['labeling'], 'Known relevance labels may be incomplete; inspect per-case judgments.',
                    'Candidate-pool negative hits are not accepted mathematical claims; the separate semantic stage must reject them.',
                    'No success-rate, proof-quality or scientific-novelty claim follows from this small retrieval regression.'])


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--fixture',type=Path)
    parser.add_argument('--rankings',type=Path)
    parser.add_argument('--output',type=Path,default=ROOT/'verification/retrieval-benchmark-v1.json')
    args=parser.parse_args()
    result=evaluate(args.fixture,args.rankings)
    args.output.parent.mkdir(parents=True,exist_ok=True)
    args.output.write_text(json.dumps(result,ensure_ascii=False,indent=2)+'\n',encoding='utf-8')
    print(json.dumps(dict(output=str(args.output.resolve()),summary=result['summary'],
                         semantic_reranking=result['semantic_reranking'],usage=result['execution_usage']),ensure_ascii=False))
    return 0


if __name__=='__main__':raise SystemExit(main())
