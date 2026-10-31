"""Fresh Lean verification of the retained bridge; no model calls.

Run with the application's Python environment. --spectrum selects the Astra
spectrum bridge; --control selects the independently prepared prodShear control.
"""
from __future__ import annotations

import argparse
import json
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))
import research_lean
from research_service import ResearchService
from research_structure_sources import StructureSourceStore


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    choice = parser.add_mutually_exclusive_group()
    choice.add_argument('--control', action='store_true')
    choice.add_argument('--spectrum', action='store_true')
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    if args.output is None:
        folder = ('common-structure-spectrum-reproduction' if args.spectrum else
                  'common-structure-control-reproduction' if args.control else
                  'common-structure-reproduction')
        args.output = ROOT/'verification'/folder
    examples = ROOT/'examples/common_structure'
    source_path = ROOT/'research_fixtures/Arxiv261038474.lean'
    candidate_name = ('Bridge' if args.control else
                      'AstraSpectrumHomeomorphism' if args.spectrum else
                      'AstraCoordinateAutomorphism')
    candidate = examples/(candidate_name + '.lean')
    if args.control:
        contract = dict(target='CommonStructure.graphSubtract_eq_prodShear',
                        input_target='Arxiv261038474.graph_to_axis',
                        statement='∀ {K : Type*} [CommRing K] (b w : Polynomial K) (p : K × (K × K)), '
                            'CommonStructure.evaluateTriple (Arxiv261038474.graphSubtract b w) p = '
                            'CommonStructure.fiberShear (CommonStructure.polynomialProfile b w) (CommonStructure.reorder p)')
    else:
        contract = json.loads((examples/(candidate_name + '.contract.json')).read_text(encoding='utf-8'))
    environment = ResearchService._environment_fingerprint()
    store = StructureSourceStore(args.output/'sources', environment)
    source = store.create(dict(name=source_path.name, content=source_path.read_text(encoding='utf-8'),
                               provenance=dict(kind='reproduction', arxiv_id='2610.38474v1', section='S9.SS1')))
    selected = store.select(source['source_id'], contract['input_target'])
    report = research_lean.verify_candidate(candidate.read_text(encoding='utf-8'), contract['target'], args.output/'proof',
        expected_statement=contract.get('statement'), required_obligations=contract.get('required_obligations'),
        source_library=selected, require_source_usage=True)
    report.update(environment_fingerprint=environment, model_calls=0,
                  reproduction_kind='prepared_control' if args.control else 'retained_astra_result',
                  example=candidate_name)
    args.output.mkdir(parents=True, exist_ok=True)
    report_path = args.output/'verification.json'
    report_path.write_text(json.dumps(report, ensure_ascii=False, indent=2)+'\n', encoding='utf-8')
    print(json.dumps(dict(success=report.get('success'), target=report.get('target'),
        source_usage=report.get('source_usage'), report=str(report_path.resolve())), ensure_ascii=False, indent=2))
    return 0 if report.get('success') else 1


if __name__=='__main__':
    raise SystemExit(main())
