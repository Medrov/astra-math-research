"""Compile generated proofs together with the original, hash-checked Lean modules."""
from __future__ import annotations

import hashlib
import io
import json
from pathlib import Path
import uuid
import zipfile

from research_lean_files import LeanFiles


def module_names(sources):
    """Independent proof collections have no shared Lean namespace."""
    return list(dict.fromkeys(f['module'] for s in sources if not s.get('bundle_format')
                              for f in s.get('files', [])))


def _linked_names(declarations, target, modules):
    by_name = {d['name']: d for d in declarations}
    names, seen, pending = set(), set(), [target]
    while pending:
        name = pending.pop()
        if name in seen or name not in by_name:
            continue
        seen.add(name)
        decl = by_name[name]
        if decl['module'] in modules:
            names.add(name)
        else:
            pending.extend(decl['dependencies'])
    return sorted(names)


def verify_candidate(root, sources, source, target, work_dir, expected_statement, *, cancelled=None):
    work = Path(work_dir).resolve() / ('lean-' + uuid.uuid4().hex[:12])
    work.mkdir(parents=True)
    report = dict(workspace=str(work), target=target, expected_statement=expected_statement,
                  source_sha256=hashlib.sha256(source.encode()).hexdigest(),
                  status='failed', success=False, target_preserved=False, diagnostics=[], declarations=[])
    try:
        files = {}
        originals = LeanFiles(Path(root) / 'lean-files')
        for spec in sources:
            if spec.get('bundle_format'):
                continue
            meta, modules = originals._load(spec['id'])
            if meta['sha256'] != spec['sha256']:
                raise ValueError('Изменился хеш исходного вложения.')
            for module in modules:
                body = module['content'].encode()
                if module['name'] in files and files[module['name']] != body:
                    raise ValueError('Два вложения задают разные версии модуля ' + module['module'])
                files[module['name']] = body
        module = 'SHAIMResult'
        while module + '.lean' in files:
            module += 'Proof'
        (work / 'Candidate.lean').write_text(source, encoding='utf-8')
        package = io.BytesIO()
        with zipfile.ZipFile(package, 'w', zipfile.ZIP_DEFLATED) as archive:
            for name, content in files.items():
                archive.writestr(name, content)
            archive.writestr(module + '.lean', source.encode())
        raw = package.getvalue()
        result = LeanFiles(work / 'check').upload('sources.zip', raw, target, expected_statement, cancelled=cancelled)
        report.update({k: result[k] for k in ('audit','declarations','diagnostics','target_preserved','compilation_success')})
        report['kernel_recheck'] = result.get('kernel_recheck', {'status':'pending', 'target':target})
        decl = next((d for d in report['declarations'] if d['name'] == target and d['module'] == module), None)
        if result['status'] != 'verified' or not decl:
            raise ValueError(result.get('error') or 'Цель не объявлена в созданном модуле.')
        (work / 'sources.zip').write_bytes(raw)
        linked = _linked_names(report['declarations'], target, set(module_names(sources)))
        report.update(status='complete', success=True, outcome='proved', axioms=decl['axioms'],
                      actual_statement=decl['type'], contract_sha256=hashlib.sha256(expected_statement.encode()).hexdigest(),
                      context={'lean_version': result['lean_version'], 'mathlib_revision': result['mathlib_revision']},
                      bundle_file='sources.zip', bundle_sha256=hashlib.sha256(raw).hexdigest(),
                      source_check={'status':'verified' if linked else 'unrelated',
                                    'source_ids':[s['id'] for s in sources if not s.get('bundle_format')],
                                    'declarations':linked,
                                    'reason':'Lean перепроверил исходные модули и зависимость теоремы от них.' if linked
                                             else 'В типе и доказательстве отсутствуют ссылки на декларации приложенных модулей.'})
    except (OSError, ValueError, KeyError) as exc:
        report.update(error=str(exc), success=False)
    (work / 'verification.json').write_text(json.dumps(report, ensure_ascii=False, indent=2))
    return report


def verify_linked_result(research, run, source_ids):
    verification = (run.get('result') or {}).get('verification') or {}
    check = verification.get('source_check') or {}
    if verification.get('success') and check.get('status') in ('verified','unrelated') and set(check['source_ids']).issubset(source_ids):
        return check
    return {'status':'unconfirmed', 'reason':'У доказательства отсутствует проверенная связь с загруженными исходниками.'}
