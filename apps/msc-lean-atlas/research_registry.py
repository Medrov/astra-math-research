"""Local, content-addressed index of Lean-checked declarations from completed runs."""
from __future__ import annotations

from contextlib import closing
import hashlib
import json
from pathlib import Path, PurePosixPath
import re
import sqlite3
import subprocess
import tempfile

import lean_service

INDEX_VERSION = 2


def _sha(value):
    return hashlib.sha256(value if isinstance(value, bytes) else value.encode()).hexdigest()


def source_prefix(task):
    return '\n'.join('import ' + module for module in task.get('imports', ['Mathlib'])) + '\n\n' + task.get('prelude', '') + '\n\n'


def context_hash(task):
    return _sha(source_prefix(task))


def _environment(context):
    # Research candidates can import Mathlib, Std and Init. The unrelated
    # application checkout is not a formal dependency of this restricted source.
    return {key: context.get(key) for key in ('lean_version', 'mathlib_revision', 'mathlib_manifest_sha256')}


def _valid_report(report, name, statement):
    return (not report.get('bundle_file') and not report.get('bundle_sha256')
            and bool(report.get('olean_sha256'))
            and report.get('success') is True and report.get('target_preserved') is True
            and report.get('target') == name and report.get('expected_statement') == statement
            and report.get('contract_sha256') == _sha(statement)
            and report.get('audit', {}).get('status') == 'passed'
            and any(d['name'] == name and d['kind'] == 'theorem' and d.get('module') == 'Candidate'
                    for d in report.get('declarations', [])))


def _checked_kernel(report):
    certificate = report.get('kernel_recheck')
    return (isinstance(certificate, dict) and certificate.get('version') == 1 and certificate.get('status') == 'passed'
            and certificate.get('scope') == 'project_dependency_closure'
            and certificate.get('target') == report.get('target')
            and certificate.get('module_sha256') == {'Candidate': report['source_sha256']}
            and certificate.get('contract_sha256') == report['contract_sha256']
            and _environment(certificate) == _environment(report['context'])
            and isinstance(certificate.get('checked'), list)
            and report['target'] in certificate['checked']
            and certificate.get('checked_count') == len(certificate['checked']))


class _ReplayUnavailable(Exception):
    """Retry legacy migration when the pinned Lean environment is available."""


def _archive_certificate(receipt, data):
    if 'kernel_recheck' in receipt:
        return receipt['kernel_recheck'] if _checked_kernel(receipt) else None
    # Older signed-off runs only have compiler receipts. Check the original,
    # hash-matched bytes before admitting a legacy card into the new index.
    import research_lean
    with tempfile.TemporaryDirectory(prefix='amr-archive-recheck-') as tmp:
        try:
            current, _ = lean_service._prepare({'project_root': ''}, Path(tmp))
        except (ValueError, OSError, subprocess.SubprocessError) as error:
            raise _ReplayUnavailable from error
        if _environment(current) != _environment(receipt['context']):
            raise _ReplayUnavailable
        replay = research_lean.verify_candidate(data.decode(), receipt['target'], tmp, receipt['expected_statement'])
    if replay['status'] in {'failed', 'timeout', 'cancelled'}:
        raise _ReplayUnavailable
    if (_valid_report(replay, receipt['target'], receipt['expected_statement']) and _checked_kernel(replay)
            and replay['source_sha256'] == receipt['source_sha256']):
        return replay['kernel_recheck']
    return None


def run_artifact_path(run_dir, recorded_workspace, filename):
    """Locate an archived artifact under this run, discarding the original checkout prefix."""
    if not isinstance(recorded_workspace, str) or filename not in ('Candidate.lean', 'sources.zip'):
        return None
    folder = Path(run_dir).resolve()
    # A verifier receipt may have come from Windows or POSIX. Do not touch the
    # recorded absolute path: only the suffix following this run ID is meaningful.
    parts = PurePosixPath(recorded_workspace.replace('\\', '/')).parts
    if folder.name not in parts or '..' in parts:
        return None
    suffix = parts[len(parts) - parts[::-1].index(folder.name):]
    workspace = folder.joinpath(*suffix).resolve()
    if not workspace.is_relative_to(folder):
        return None
    candidate = (workspace / filename).resolve()
    if candidate.is_relative_to(workspace) and candidate.is_file():
        return candidate
    return None


def _cards(run_dir, run):
    if (run.get('mode') not in ('multi', 'single') or run.get('status') != 'complete'
            or run.get('outcome') not in {'proved', 'refuted'} or (run.get('semantic_review') or {}).get('status') != 'aligned'):
        return
    plan_file, proofs_file = run_dir / 'plan.json', run_dir / 'proofs.json'
    if not (plan_file.is_file() and proofs_file.is_file()):
        return
    plan = json.loads(plan_file.read_text())
    nodes = {n['id']: n for n in plan['nodes']}
    prefix = source_prefix(plan).encode()
    for name, proof in json.loads(proofs_file.read_text()).items():
        node = nodes.get(name)
        report = proof.get('verification', {})
        if node is None or not _valid_report(report, name, node['statement']):
            continue
        path = run_artifact_path(run_dir, report.get('workspace'), 'Candidate.lean')
        if path is None or not path.is_relative_to((run_dir/'lean').resolve()) or path.stat().st_size > 250000:
            continue
        # Only index the original Candidate module and its verifier receipt.
        # A sources.zip certificate verifies a different unit of compilation.
        receipt_path = path.with_name('verification.json')
        if not receipt_path.is_file():
            continue
        receipt = json.loads(receipt_path.read_text())
        if not _valid_report(receipt, name, node['statement']) or receipt['source_sha256'] != report.get('source_sha256'):
            continue
        report = receipt
        data = path.read_bytes()
        if _sha(data) != report.get('source_sha256') or not data.startswith(prefix):
            continue
        env = _environment(report.get('context', {}))
        if not env['lean_version'] or not env['mathlib_revision']:
            continue
        artifact = path.relative_to(run_dir.resolve()).as_posix()
        url_base = '/api/research/runs/' + run_dir.name + '/artifacts/'
        handoff = (run.get('contract') or {}).get('program_context') or {}
        refutation = None
        if name == plan.get('target_id') and handoff.get('direction') == 'refute':
            base = handoff.get('base_statement')
            if not isinstance(base,str) or node['statement'] != '¬ (' + base + ')' or run['outcome'] != 'refuted':
                continue
            refutation = dict(statement=base, statement_sha256=_sha(base), program_id=handoff.get('program_id'),
                              task_id=handoff.get('task_id'), revision=handoff.get('revision'))
        certificate = _archive_certificate(report, data)
        if not certificate:
            continue
        yield dict(id='verified:' + run_dir.name + ':' + name, name=name, target=name,
                   title=node.get('title') or name, statement=node['statement'], source_run_id=run_dir.name,
                   refutation_of=refutation, kernel_recheck=certificate,
                   msc_codes=run.get('msc_codes', []), research_question=run.get('claim', ''),
                   source_sha256=_sha(data), statement_sha256=_sha(node['statement']), context_sha256=_sha(prefix),
                   **env, proof_status='lean_checked', evidence_type='verified_run_lemma', artifact=artifact,
                   url=url_base + artifact, verification_url=url_base + str(Path(artifact).with_name('verification.json')),
                   source_bytes=len(data), declared_names=[d['name'] for d in report['declarations']],
                   theorem_names=[d['name'] for d in report['declarations'] if d['kind'] == 'theorem'])


def _db(root):
    db = sqlite3.connect(Path(root) / 'verified-lemmas.sqlite', timeout=15)
    db.executescript("""
        CREATE TABLE IF NOT EXISTS indexed_runs (id TEXT PRIMARY KEY, changed INTEGER NOT NULL);
        CREATE TABLE IF NOT EXISTS lemmas (id TEXT PRIMARY KEY, run TEXT NOT NULL, card TEXT NOT NULL);
        CREATE INDEX IF NOT EXISTS lemmas_run ON lemmas(run);
    """)
    if db.execute('PRAGMA user_version').fetchone()[0] < INDEX_VERSION:
        # Rebuild derived metadata for older workspaces. Never touch proofs or run state.
        with db:
            db.execute('BEGIN IMMEDIATE')
            if db.execute('PRAGMA user_version').fetchone()[0] < INDEX_VERSION:
                db.execute('DELETE FROM lemmas')
                db.execute('DELETE FROM indexed_runs')
                db.execute(f'PRAGMA user_version={INDEX_VERSION}')
    return db


def refresh(root, only_run=None):
    """Idempotent archive index. Selected sources are replayed in the consuming run."""
    root = Path(root)
    root.mkdir(parents=True, exist_ok=True)
    paths = [root / only_run / 'run.json'] if only_run else sorted(root.glob('*/run.json'))
    with closing(_db(root)) as db:
        for path in paths:
            if not re.fullmatch('[0-9a-f]{32}', path.parent.name) or not path.is_file():
                continue
            run_id = path.parent.name
            changed = path.stat().st_mtime_ns
            if db.execute('SELECT 1 FROM indexed_runs WHERE id=? AND changed=?', (run_id, changed)).fetchone():
                continue
            run = json.loads(path.read_text())
            if run.get('status') in {'queued', 'running'}:
                continue
            try:
                cards = list(_cards(path.parent, run))
            except _ReplayUnavailable:
                cards = None
            with db:
                db.execute('BEGIN IMMEDIATE')
                if path.stat().st_mtime_ns != changed:
                    continue
                if cards is None:
                    # Keep a concurrent successful migration for the same bytes.
                    indexed = db.execute('SELECT changed FROM indexed_runs WHERE id=?', (run_id,)).fetchone()
                    if indexed and indexed[0] != changed:
                        db.execute('DELETE FROM indexed_runs WHERE id=?', (run_id,))
                        db.execute('DELETE FROM lemmas WHERE run=?', (run_id,))
                    continue
                db.execute('DELETE FROM lemmas WHERE run=?', (run_id,))
                db.executemany('INSERT INTO lemmas VALUES(?,?,?)', (
                    (c['id'], run_id, json.dumps(c, ensure_ascii=False)) for c in cards))
                db.execute('INSERT OR REPLACE INTO indexed_runs VALUES(?,?)', (run_id, changed))


def _tokens(text):
    words = re.sub(r'([a-z])([A-Z])', r'\1 \2', str(text)).lower()
    return set(re.findall(r'[^\W_]{3,}', words))


def search(root, query, task=None, exclude_run=None, limit=8, *, scope_codes=None, scope_context=None):
    """Return source metadata only. Full Lean source must pass compatible replay before use."""
    from research_retrieval import _terms
    path = Path(root) / 'verified-lemmas.sqlite'
    if not path.is_file():
        return []
    terms = _tokens(query) | set(_terms(query))
    candidates = []
    with closing(sqlite3.connect(path, timeout=10)) as db:
        if db.execute('PRAGMA user_version').fetchone()[0] < INDEX_VERSION:
            return []
        for (encoded,) in db.execute('SELECT card FROM lemmas WHERE run<>?', (exclude_run or '',)):
            card = json.loads(encoded)
            if scope_codes is not None and not scope_codes.intersection(card.get('msc_codes', [])):
                continue
            if scope_context is not None and card['context_sha256'] != scope_context:
                continue
            if not (Path(root) / card['source_run_id'] / card['artifact']).is_file():
                continue
            exact_context = bool(task and card['context_sha256'] == context_hash(task))
            # A stored solution to the same formal question is not an intermediate lemma.
            if task and (task.get('target') in card['declared_names'] or card['statement'] == task.get('statement')):
                continue
            name_hits = terms & _tokens(card['name'])
            topic_hits = terms & _tokens(card['statement'] + ' ' + card['title'] + ' ' + card['research_question'])
            if exact_context or name_hits or topic_hits or scope_context is not None or scope_codes is not None:
                candidates.append((exact_context, len(name_hits), len(topic_hits), card))
    candidates.sort(key=lambda row: (-row[0], -row[1], -row[2], row[3]['source_bytes'], row[3]['id']))
    seen, result = set(), []
    for _, _, _, card in candidates:
        key = (card['name'], card['context_sha256'], card['statement_sha256'])
        if key in seen:
            continue
        seen.add(key)
        result.append(card)
        if len(result) >= limit:
            break
    return result


def load_source(root, card):
    run_dir = (Path(root) / card['source_run_id']).resolve()
    path = (run_dir / card['artifact']).resolve()
    if not path.is_relative_to(run_dir) or not path.is_file() or path.stat().st_size > 250000:
        raise ValueError('Исходник архивной леммы недоступен.')
    data = path.read_bytes()
    if _sha(data) != card['source_sha256']:
        raise ValueError('Контрольная сумма исходника архивной леммы изменилась.')
    return data.decode()


def check_pinned_environment(card, work):
    current, _ = lean_service._prepare({}, Path(work))
    if _environment(current) != _environment(card):
        raise ValueError('Версия Lean или mathlib изменилась после подключения архивной леммы.')


def pin_candidate(root, run_id, plan, query, cancelled):
    """Replay one compatible archive candidate and return immutable provenance for this run."""
    import research_lean
    work = Path(root) / run_id / 'library-replay'
    names = {node['id'] for node in plan['nodes']}
    target = next(node for node in plan['nodes'] if node['id'] == plan['target_id'])
    task = dict(plan, target=target['id'], statement=target['statement'])
    cards = search(root, query, task=task, exclude_run=run_id)
    cards = [c for c in cards if c['context_sha256'] == context_hash(task) and names.isdisjoint(c['declared_names'])]
    if not cards:
        return None
    current, _ = lean_service._prepare({}, work)
    # Each artifact includes its own prerequisites. Prefer a small reusable
    # premise over a larger result which happens to include the same premise.
    cards.sort(key=lambda c: (c['name'].lower() not in query.lower(), len(c.get('theorem_names', c['declared_names']))))
    for card in cards:
        if cancelled():
            return None
        if _environment(current) != _environment(card):
            continue
        try:
            source = load_source(root, card)
        except (OSError, ValueError):
            continue
        if not source.startswith(source_prefix(task)):
            continue
        receipt = research_lean.verify_candidate(source, card['name'], work, expected_statement=card['statement'], cancelled=cancelled)
        if (_valid_report(receipt, card['name'], card['statement']) and _checked_kernel(receipt)
                and _environment(receipt['context']) == _environment(card)):
            snapshot = Path(receipt['workspace']) / 'Candidate.lean'
            return dict(card, replay_artifact=snapshot.relative_to((Path(root) / run_id).resolve()).as_posix())
    return None


def pinned_source(run_dir, plan, card):
    if context_hash(plan) != card['context_sha256']:
        raise ValueError('Контекст сохранённой библиотечной леммы изменился.')
    if any(node['id'] in card['declared_names'] for node in plan['nodes']):
        raise ValueError('План повторно объявил имя из подключённого Lean-файла.')
    path = (Path(run_dir) / card['replay_artifact']).resolve()
    if not path.is_relative_to(Path(run_dir).resolve()):
        raise ValueError('Путь к библиотечному исходнику вышел за пределы исследования.')
    data = path.read_bytes()
    if _sha(data) != card['source_sha256']:
        raise ValueError('Контрольная сумма подключённой леммы изменилась.')
    return data.decode() + '\n\n'


def proof_edges(card, declarations, target):
    """Only value edges on a path to the final theorem count as cross-run proof reuse."""
    if not card:
        return []
    by_name = {d['name']: d for d in declarations}
    pending, visited, edges = [target], set(), []
    while pending:
        name = pending.pop()
        if name in visited or name not in by_name or name in card['declared_names']:
            continue
        visited.add(name)
        decl = by_name[name]
        deps = set(decl.get('dependencies', [])) - set(decl.get('type_dependencies', []))
        for used in sorted(deps.intersection(card.get('theorem_names', [card['name']]))):
            edges.append(dict(source=used, target=name, source_run_id=card['source_run_id'],
                              source_sha256=card['source_sha256'], type='proof_dependency', evidence='lean_environment'))
        pending.extend(sorted(deps.intersection(by_name)))
    return edges
