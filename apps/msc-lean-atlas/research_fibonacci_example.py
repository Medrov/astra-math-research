"""Portable known proof, explicitly outside fixtures and the search corpus.

Opening this demo rechecks its fixed contract locally. It neither creates a
research run nor registers a reusable mechanism or a certificate for the paper.
"""
from __future__ import annotations

import hashlib
import json
from pathlib import Path


PACKAGE = Path(__file__).resolve().parent / 'examples' / 'fibonacci_composition'
EXAMPLE_ID = 'fibonacci_composition_bridge'
TARGET = 'CompositionBridge.conditional_transfer'
OBLIGATIONS = {
    'structure': 'CompositionBridge.structural_laws',
    'comparison': 'CompositionBridge.comparison_substitution',
    'transfer': TARGET,
    'normalization': 'CompositionBridge.normalization',
}
TITLE = 'Фибоначчи · композиция квадратичной формы (4 обязательства)'
SCOPE = ('Проверенный условный мост над ℚ × ℚ: композиция квадратичной формы и перенос '
         'полиномиального равенства. Предпосылки c = a + b и (b² − a·c)² = 1 остаются явными. '
         'Это не формализация последовательности Фибоначчи или всей статьи; применение '
         'к исходному переходу статьи не проверено. MSC 15A63 — предположенная рубрика.')


def _sha(value):
    return hashlib.sha256(value.encode('utf-8') if isinstance(value, str) else value).hexdigest()


def load():
    """Read only fixed package files; never accept a client-provided proof/type."""
    provenance = json.loads((PACKAGE / 'provenance.json').read_text(encoding='utf-8'))
    files = {}
    for name in ('Candidate.lean', 'contract.json'):
        raw = (PACKAGE / name).read_bytes()
        if _sha(raw) != provenance['files_sha256'].get(name):
            raise ValueError('Содержимое готовой демонстрации изменилось: ' + name)
        files[name] = raw.decode('utf-8')
    contract = json.loads(files['contract.json'])
    goals = contract.get('required_obligations', [])
    if (contract.get('target') != TARGET or len(goals) != 4 or
            {item.get('id'): item.get('target') for item in goals} != OBLIGATIONS or
            any(not isinstance(item.get('statement'), str) or not item['statement'].strip() or
                item.get('expected_outcome') != 'proved' for item in goals) or
            contract.get('statement') != next(item['statement'] for item in goals if item['id'] == 'transfer')):
        raise ValueError('Демонстрация требует исходный точный контракт всех четырёх обязательств.')
    return files['Candidate.lean'], contract, provenance


def metadata():
    source, contract, provenance = load()
    return dict(id=EXAMPLE_ID, title=TITLE, recommended_target=TARGET,
                source_sha256=_sha(source), source_kind='portable_demo',
                verification_kind='exact_demo_contract', required_obligation_count=4,
                url=provenance['source']['section_url'], scope_note=SCOPE)


def import_source(store):
    """Inspect the source, then independently check all four frozen obligations."""
    import research_lean

    content, contract, provenance = load()
    source = store.create(dict(name='FibonacciComposition.lean', title=TITLE, content=content,
        provenance=dict(kind='portable_known_proof_example', example_id=EXAMPLE_ID,
                        recommended_target=TARGET, url=provenance['source']['section_url'],
                        scope=SCOPE, source_application_status='not_verified',
                        msc=[dict(code='15A63', origin='reviewer_inferred', source_verified=False)])))
    if source.get('status') != 'ready' or source.get('inspection', {}).get('success') is not True:
        return source
    if source.get('source_sha256') != _sha(content):
        raise ValueError('Проверяемый источник не совпал с готовой демонстрацией.')
    report = research_lean.verify_candidate(content, TARGET,
        store.root / source['source_id'] / 'demo-verification', contract['statement'],
        required_obligations=contract['required_obligations'])
    checked = report.get('obligations', [])
    goals = contract['required_obligations']
    exact = (len(checked) == 4 and all(sum(
        row.get('id') == goal['id'] and row.get('target') == goal['target'] and
        row.get('statement_sha256') == _sha(goal['statement']) and row.get('ok') is True
        for row in checked) == 1 for goal in goals))
    verified = (report.get('status') == 'complete' and report.get('success') is True and
                report.get('compilation_success') is True and report.get('target_preserved') is True and
                report.get('obligations_passed') is True and report.get('audit', {}).get('status') == 'passed' and
                report.get('source_sha256') == _sha(content) and report.get('target') == TARGET and
                report.get('expected_statement') == contract['statement'] and exact)
    # The full fresh verification.json stays in the local runtime source folder.
    # Return a compact view; do not modify the immutable source snapshot.
    view = {key: report.get(key) for key in ('status', 'success', 'compilation_success',
        'target_preserved', 'obligations_passed', 'target', 'expected_statement', 'source_sha256',
        'audit', 'obligations', 'finished_at')}
    return dict(source, demo_verification=dict(example_id=EXAMPLE_ID, verified=verified,
        fresh_local_check=True, model_calls=0, formal_contract=contract, verification=view,
        source_application_status='not_verified', msc=source['provenance']['msc'],
        scope_note=SCOPE, origin_url=provenance['source']['section_url']))
