#!/usr/bin/env python3
"""Explicit live Astra pilot: identical per-case call/time caps, measured token usage.

This is an engineering check on known examples, not a statistical claim that one
architecture is better. Running this script dispatches four paid/account-usage
Codex research runs. No model calls occur on import.
"""
import argparse
import json
from pathlib import Path
import time

from research_service import ResearchService, atomic, now, sha


def evaluate(output, cases, calls=8, seconds=600):
    service = ResearchService(recover=False)
    report = dict(started_at=now(), protocol='known-link-and-negative-control-v1', model='gpt-6-astra',
                  budget_per_run=dict(max_calls=calls, timeout_seconds=seconds),
                  same_formal_contract=True, prepared_proofs_in_prompt=False, strict_token_cap=False,
                  note='Equal maximum calls and wall time; actual token usage differs. Small engineering pilot; not an efficacy benchmark.', runs=[])
    output = Path(output)
    for case in cases:
        for mode in ('single', 'multi'):
            run = service.create({'case_id':case, 'mode':mode, 'budget':report['budget_per_run']})
            report['runs'].append(dict(id=run['id'], case_id=case, mode=mode, contract_sha256=run['contract_sha256']))
            print(json.dumps({'created':run['id'], 'case':case, 'mode':mode}), flush=True)
    atomic(output, report)
    # All accepted requests are bounded; the service runs at most two at once.
    while any(not f.done() for f in service.futures.values()):
        for entry in report['runs']:
            run = service.get(entry['id'])
            entry.update(status=run['status'], phase=run['phase'], outcome=run['outcome'], usage=run['usage'])
        atomic(output, report)
        time.sleep(1)
    for entry in report['runs']:
        run = service.get(entry['id'])
        entry.update(status=run['status'], phase=run['phase'], outcome=run['outcome'], formal_outcome=run.get('formal_outcome'),
                     semantic_review=run.get('semantic_review'), usage=run['usage'], error=run.get('error'),
                     nodes=len(run['nodes']), edges=len(run['edges']), source_sha256=run.get('result',{}).get('verification',{}).get('source_sha256'))
    report['finished_at'] = now()
    report['paired_contracts_equal'] = all(len({r['contract_sha256'] for r in report['runs'] if r['case_id']==case})==1 for case in cases)
    atomic(output, report)
    lines = ['# Проверка исследовательских режимов', '', report['note'], '',
             '| Задача | Режим | Исполнение | Результат | Вызовы | Токены | Секунды |',
             '|---|---|---|---|---:|---:|---:|']
    for r in report['runs']:
        u=r['usage']; lines.append(f"| {r['case_id']} | {r['mode']} | {r['status']} | {r['outcome']} | {u['calls']} | {u['total_tokens']} | {u['elapsed_seconds']:.1f} |")
    lines += ['', 'У каждой пары совпадает исходный формальный контракт: ' + str(report['paired_contracts_equal']),
              '', 'Доказательства решений не включены во вход агента. Постановки и возможные вспомогательные леммы заданы; '
              'это восстановление известных связей. Пересечение с обучающими данными модели не исключено. '
              'Разные режимы имеют одинаковые верхние пределы вызовов и времени, но не гарантированно одинаковые вычислительные затраты. '
              'Победа на этих примерах не доказывает преимущество архитектуры или способность к новым открытиям.']
    output.with_suffix('.md').write_text('\n'.join(lines)+'\n')
    print(json.dumps(report, ensure_ascii=False, indent=2), flush=True)
    return report


if __name__ == '__main__':
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', default='verification/research-evaluation.json')
    parser.add_argument('--cases', nargs='+', default=['graph_energy','strict_inequality'])
    parser.add_argument('--calls', type=int, default=8)
    parser.add_argument('--seconds', type=int, default=600)
    args=parser.parse_args()
    evaluate(args.output,args.cases,args.calls,args.seconds)
