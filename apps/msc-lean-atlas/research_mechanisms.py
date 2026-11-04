"""Persistent, audited mechanisms. Reuse is evidence, never a new certificate.

Only register() writes entries. It independently recompiles the entire frozen
contract; a success flag supplied by a caller is not an import format.
"""
from __future__ import annotations

from contextlib import contextmanager
from datetime import datetime, timezone
import copy
import hashlib
import json
import os
from pathlib import Path
import re
import sqlite3
import time
import uuid

import lean_service
from platform_support import lock_file, unlock_file


def _json(value):
    return json.dumps(value, sort_keys=True, ensure_ascii=False, separators=(',', ':'))


def _sha(value):
    return hashlib.sha256((value if isinstance(value, str) else _json(value)).encode('utf-8')).hexdigest()


def _write(path, value):
    temporary = path.with_name('.' + path.name + '.' + uuid.uuid4().hex + '.tmp')
    temporary.write_text(_json(value), encoding='utf-8')
    os.replace(temporary, path)


def _validate_contract_context(proof_source, contract):
    """Bind the stored context to the canonical source emitted by _source.

    This intentionally accepts the application's theorem-only proof suffix,
    not arbitrary Lean programs. The suffix cannot redefine the context or
    change name resolution after the frozen prelude.
    """
    import research_lean
    imports, prelude = contract.get('imports'), contract.get('prelude')
    if not isinstance(imports, list) or not imports or any(
            not isinstance(module, str) or not research_lean.MODULE_NAME.fullmatch(module) for module in imports):
        raise ValueError('Нужен точный список импортов контракта механизма.')
    if not isinstance(prelude, str) or re.search(r'\b(?:theorem|lemma)\b', lean_service._mask(prelude)):
        raise ValueError('Нужен точный контекст определений без теорем в prelude.')
    prefix = '\n'.join('import ' + module for module in imports) + '\n\n' + prelude + '\n\n'
    if not proof_source.startswith(prefix):
        raise ValueError('Исходник механизма не совпадает с каноническими imports/prelude контракта.')
    tail = lean_service._mask(proof_source[len(prefix):])
    # A proved theorem may use local let/have bindings, but cannot introduce
    # module commands, definitions, notation or namespace changes. Comments and
    # strings are masked so an explanation cannot trigger this restriction.
    commands = ('import|prelude|def|abbrev|opaque|inductive|structure|class|instance|'
                'namespace|section|end|variable|variables|parameter|parameters|'
                'universe|universes|open|export|attribute|notation|infix|infixl|'
                'infixr|prefix|postfix|scoped|local|noncomputable|private|protected')
    if re.search(r'(?<![\w.])(?:' + commands + r')(?![\w.])', tail) or '@[' in tail or '`' in tail:
        raise ValueError('Хвост доказательства механизма изменяет закреплённый контекст.')
    if not re.match(r'\s*(?:theorem|lemma)\s+', tail):
        raise ValueError('После контекста механизма ожидаются только доказательства теорем.')


def _independent_verify(source, target, work_dir, expected_statement, **kwargs):
    import research_lean
    import research_structure_sources
    report = research_lean.verify_candidate(source, target, work_dir, expected_statement, **kwargs)
    # verify_candidate already prints axioms for source_library-backed candidates.
    # A literary bridge also needs literal output for every authored theorem.
    if report.get('success') and not report.get('print_axioms'):
        context, work = report['context'], Path(report['workspace'])
        env = os.environ.copy()
        env['LEAN_PATH'] = os.pathsep.join(context['lean_search_paths'])
        report['print_axioms'] = research_structure_sources.print_axioms(
            source, report['declarations'], context, env, work, report['diagnostics'],
            kwargs.get('cancelled'), module='Candidate')
    return report


class MechanismStore:
    def __init__(self, root, environment_fingerprint):
        self.root = Path(root)
        self.environment_fingerprint = str(environment_fingerprint)

    @contextmanager
    def _guard(self):
        self.root.mkdir(parents=True, exist_ok=True)
        with (self.root / '.lock').open('a+b') as stream:
            lock_file(stream)
            try:
                yield
            finally:
                unlock_file(stream)

    @staticmethod
    def _validate_report(report, proof_source, contract, source_library):
        from research_structure_sources import _authored
        if not isinstance(report, dict) or not all(report.get(k) is True for k in
                ('success', 'compilation_success', 'target_preserved', 'obligations_passed')):
            raise ValueError('Механизм требует свежей полной проверки доказательства и всех обязательств.')
        if report.get('source_sha256') != _sha(proof_source) or report.get('target') != contract['target']:
            raise ValueError('Свежий отчёт не соответствует исходнику или цели механизма.')
        if report.get('expected_statement') != contract['statement'] or report.get('contract_sha256') != _sha(contract['statement']):
            raise ValueError('Свежий отчёт не соответствует точному типу цели.')
        expected = {(o['id'], o['target'], _sha(o['statement']), o['expected_outcome'])
                    for o in contract['required_obligations']}
        actual = {(o.get('id'), o.get('target'), o.get('statement_sha256'), o.get('expected_outcome'))
                  for o in report.get('obligations', []) if o.get('ok') is True}
        if actual != expected or len(report.get('obligations', [])) != len(expected):
            raise ValueError('Проверка потеряла или изменила обязательства механизма.')
        audit = report.get('audit') or {}
        if audit.get('status') != 'passed' or audit.get('unexpected_axioms') or audit.get('unsafe_declarations'):
            raise ValueError('Аудит механизма отклонён.')
        if set(report.get('axioms', [])) - lean_service.ALLOWED_AXIOMS:
            raise ValueError('Недопустимые аксиомы механизма.')
        declarations = report.get('declarations') or []
        if any(set(d.get('axioms', [])) - lean_service.ALLOWED_AXIOMS for d in declarations if d.get('kind') == 'theorem'):
            raise ValueError('Недопустимые аксиомы вспомогательной теоремы.')
        printed = report.get('print_axioms') or {}
        if printed.get('exit_code') != 0 or not isinstance(printed.get('theorems'), list) or not printed.get('stdout'):
            raise ValueError('Нет успешного буквального #print axioms для механизма.')
        targets = {o['target'] for o in contract['required_obligations']} | {contract['target']}
        targets.update(d['name'] for d in declarations if d.get('kind') == 'theorem' and _authored(proof_source, d))
        if not targets <= set(printed['theorems']):
            raise ValueError('Вывод #print axioms не покрывает все обязательные цели.')
        if source_library:
            checked = report.get('source_library') or {}
            if checked.get('source_sha256') != source_library['source_sha256'] or not checked.get('fresh_compilation'):
                raise ValueError('Не подтверждён неизменный исходный Lean-источник.')
            if (report.get('source_usage') or {}).get('status') != 'related':
                raise ValueError('Не подтверждено участие исходной теоремы или её определений.')

    def register(self, *, proof_source, formal_contract, provenance, semantic_review,
                 source_library=None, verifier=None, cancelled=None, timeout_seconds=None):
        """Recheck and atomically publish an exact theorem; no model calls.

        verifier is an internal dependency injection point, never an HTTP field.
        It has research_lean.verify_candidate's signature. Cancellation bounds
        the independent check by the caller's remaining overall budget.
        """
        import research_lean
        contract, origin = copy.deepcopy(formal_contract), copy.deepcopy(provenance)
        research_lean._validate_source(proof_source)
        if not isinstance(contract, dict) or not research_lean.NAME.fullmatch(str(contract.get('target', ''))):
            raise ValueError('Нужен точный формальный контракт механизма.')
        _validate_contract_context(proof_source, contract)
        research_lean._validate_type_contract(contract.get('statement'))
        contract['required_obligations'] = research_lean._validate_obligations(contract.get('required_obligations'))
        if not contract['required_obligations'] or not any(o['target'] == contract['target'] and o['statement'] == contract['statement']
                                                          for o in contract['required_obligations']):
            raise ValueError('Основная цель должна входить в полный список обязательств.')
        if not isinstance(semantic_review, dict) or semantic_review.get('status') != 'aligned':
            raise ValueError('Для каталога нужна отдельная согласованная смысловая рецензия.')
        if not isinstance(origin, dict) or not re.fullmatch(r'[a-f0-9]{32}', str(origin.get('run_id', ''))):
            raise ValueError('Нужен исходный идентификатор исследования.')
        if not isinstance(origin.get('title'), str) or not origin['title'].strip():
            raise ValueError('Нужно название проверенного механизма.')
        if not re.fullmatch(r'[a-f0-9]{64}', str(origin.get('source_sha256', ''))):
            raise ValueError('Нужен хеш исходного математического источника.')
        if origin.get('source_kind') not in {'lean', 'literature', 'formal_contract'} or not isinstance(origin.get('assumptions'), list) or any(
                not isinstance(s, str) for s in origin['assumptions']):
            raise ValueError('Нужны тип источника и явный список условий.')
        if (origin['source_kind'] == 'lean') != bool(source_library):
            raise ValueError('Lean-источник требует закреплённого source_library.')
        if source_library and source_library.get('source_sha256') != origin['source_sha256']:
            raise ValueError('Хеш происхождения отличается от исходного Lean-модуля.')
        if origin['source_kind'] == 'formal_contract' and origin['source_sha256'] != _sha(proof_source):
            raise ValueError('Самостоятельный контракт должен ссылаться на точный проверяемый исходник.')
        if timeout_seconds is not None and (not isinstance(timeout_seconds, (int, float)) or timeout_seconds <= 0):
            raise ValueError('Нет бюджета времени для независимой проверки механизма.')
        identity = dict(proof_sha256=_sha(proof_source), contract_sha256=_sha(contract),
                        source_sha256=origin['source_sha256'], environment_fingerprint=self.environment_fingerprint)
        identifier = _sha(identity)
        # A duplicate is an already independently checked, immutable exact entry.
        if (self.root / identifier / 'mechanism.json').is_file():
            return self.get(identifier)
        started = time.monotonic()
        def stopped():
            return bool(cancelled and cancelled()) or (timeout_seconds is not None and time.monotonic() - started >= timeout_seconds)
        if stopped():
            raise InterruptedError('Проверка каталога отменена.')
        work = self.root / 'checks' / uuid.uuid4().hex
        work.mkdir(parents=True, exist_ok=True)
        checker = verifier or _independent_verify
        report = checker(proof_source, contract['target'], work, expected_statement=contract['statement'],
                         required_obligations=contract['required_obligations'], source_library=source_library,
                         require_source_usage=True, cancelled=stopped)
        if stopped():
            raise InterruptedError('Лимит времени независимой проверки каталога исчерпан.')
        self._validate_report(report, proof_source, contract, source_library)
        payload = dict(id=identifier, schema_version=1, created_at=datetime.now(timezone.utc).isoformat(),
                       **identity, title=origin['title'], formal_contract=contract, provenance=origin,
                       semantic_review=copy.deepcopy(semantic_review), source_library=copy.deepcopy(source_library),
                       verification=report, verification_sha256=_sha(report), proof_source=proof_source,
                       source_application_status='source_usage_checked' if source_library else
                           'formal_statement_only' if origin['source_kind']=='formal_contract' else 'not_verified',
                       verification_scope='stored_contract_only', reuse=True, requires_new_proof=True)
        payload['payload_sha256'] = _sha(payload)
        with self._guard():
            folder = self.root / identifier
            folder.mkdir(exist_ok=True)
            if not (folder / 'mechanism.json').exists():
                _write(folder / 'mechanism.json', payload)
        return self.get(identifier)

    def get(self, identifier):
        if not isinstance(identifier, str) or not re.fullmatch(r'[a-f0-9]{64}', identifier):
            raise ValueError('Некорректный идентификатор механизма.')
        value = json.loads((self.root / identifier / 'mechanism.json').read_text(encoding='utf-8'))
        checksum = value.pop('payload_sha256', None)
        if checksum != _sha(value) or value.get('id') != identifier:
            raise ValueError('Нарушена целостность записи механизма.')
        if value.get('proof_sha256') != _sha(value['proof_source']) or value.get('contract_sha256') != _sha(value['formal_contract']):
            raise ValueError('Изменён исходник или контракт механизма.')
        if value.get('verification_sha256') != _sha(value['verification']):
            raise ValueError('Изменён отчёт проверки механизма.')
        _validate_contract_context(value['proof_source'], value['formal_contract'])
        self._validate_report(value['verification'], value['proof_source'], value['formal_contract'], value.get('source_library'))
        value['payload_sha256'] = checksum
        value['status'] = 'verified_stored_contract' if value['environment_fingerprint'] == self.environment_fingerprint else 'needs_recheck'
        value['requires_new_proof'] = True
        value['description'] = value['formal_contract']['statement']
        value['scope'] = 'Проверен сохранённый точный контракт; применение к новой задаче требует нового доказательства.'
        return value

    def list(self):
        values = []
        for path in sorted(self.root.glob('*/mechanism.json')):
            try:
                value = self.get(path.parent.name)
            except (OSError, ValueError, KeyError):
                continue  # Corrupt records must never be searchable as verified.
            summary={key: value[key] for key in ('id', 'title', 'created_at', 'status', 'formal_contract',
                'provenance', 'source_application_status', 'environment_fingerprint', 'proof_sha256',
                'contract_sha256', 'verification_scope', 'reuse', 'requires_new_proof')}
            summary.update(description=value['formal_contract']['statement'], scope='Проверен сохранённый точный контракт; применение к новой задаче требует нового доказательства.')
            values.append(summary)
        return values

    def search(self, query, limit=8):
        import research_retrieval
        if not isinstance(limit, int) or isinstance(limit, bool) or not 1 <= limit <= 48:
            raise ValueError('Некорректный лимит поиска механизмов.')
        terms = research_retrieval._terms(query)
        entries = [entry for entry in self.list() if entry['status'] == 'verified_stored_contract']
        if not terms or not entries:
            return []
        connection = sqlite3.connect(':memory:')
        try:
            connection.execute('CREATE VIRTUAL TABLE search USING fts5(id UNINDEXED, title, content)')
            for entry in entries:
                content = _json(dict(contract=entry['formal_contract'], assumptions=entry['provenance']['assumptions']))
                connection.execute('INSERT INTO search VALUES (?,?,?)', (entry['id'], entry['title'], research_retrieval._split_names(content)))
            found = connection.execute('SELECT id,bm25(search) FROM search WHERE search MATCH ? ORDER BY bm25(search) LIMIT ?',
                                       (research_retrieval._query(terms), limit)).fetchall()
        finally:
            connection.close()
        by_id = {entry['id']: entry for entry in entries}
        return [dict(id='mechanism:' + identifier, mechanism_id=identifier, title=by_id[identifier]['title'],
                     name=by_id[identifier]['formal_contract']['target'],
                     statement=by_id[identifier]['formal_contract']['statement'],
                     assumptions=by_id[identifier]['provenance']['assumptions'],
                     mechanism_contract=by_id[identifier]['formal_contract'], provenance=by_id[identifier]['provenance'],
                     source_sha256=by_id[identifier]['proof_sha256'], retrieval_score=-score,
                     retrieval_backend='mechanism_fts5', extraction='independently_checked_stored_contract',
                     type_status='verified_stored_contract', evidence_type='verified_mechanism_reuse',
                     verification_scope='stored_contract_only', reuse=True, requires_new_proof=True,
                     source_application_status=by_id[identifier]['source_application_status'],
                     applicability_status='not_verified_for_current_task') for identifier, score in found]
