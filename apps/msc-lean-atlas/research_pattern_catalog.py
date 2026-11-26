"""Resolve search hits to typed theorem declarations in the installed mathlib."""
from contextlib import closing
import hashlib
import json
from pathlib import Path
import re
import sqlite3
import tempfile

import lean_service
import research_lean
import research_retrieval


STOP_WORDS = {'a','an','and','as','at','by','etc','for','from','in','of','on','or','other','the',
              'to','with','general','generalizations','поиск','закономерностей'}


def _source_path(card, root):
    module = card['module']
    if not re.fullmatch(r"Mathlib(?:\.[\w']+)+", module):
        return None
    path = root.joinpath(*module.split('.')).with_suffix('.lean').resolve()
    if path == Path(card['file']).resolve() and path.is_relative_to(root / 'Mathlib') and path.is_file():
        return path
    return None


def read_source(identifier, expected_sha):
    index = research_retrieval.INDEX_PATH
    if not index.is_file():
        raise FileNotFoundError('Локальный индекс Lean отсутствует.')
    with closing(sqlite3.connect(index.as_uri() + '?mode=ro', uri=True)) as db:
        row = db.execute('SELECT payload FROM declarations WHERE id=?', ('lean:' + identifier,)).fetchone()
    if not row:
        raise FileNotFoundError('Декларация отсутствует в локальном индексе.')
    card = json.loads(row[0])
    path = _source_path(card, Path(lean_service.default_context()['mathlib']).resolve())
    if path is None:
        raise FileNotFoundError('Исходник mathlib недоступен.')
    body = path.read_bytes()
    if hashlib.sha256(body).hexdigest() != expected_sha or card['source_sha256'] != expected_sha:
        raise ValueError('Версия исходника mathlib изменилась после этого поиска.')
    return body


def find_theorems(topic, codes, limit):
    if codes:
        nodes = json.loads((research_retrieval.ROOT / 'data/msc2020.json').read_text())['nodes']
        labels = [n['title'] for n in nodes if n['id'] in codes]
        topic = ' '.join(labels) + ' ' + topic
    keywords = [w for w in re.findall(r'[^\W_]+', topic.lower()) if w not in STOP_WORDS and not w.isdigit()]
    hits = research_retrieval.search_library(' '.join(keywords), limit=40)
    root = Path(lean_service.default_context()['mathlib']).resolve()
    hashes, candidates, modules = {}, {}, []
    for h in hits:
        if h['kind'] not in ('theorem', 'lemma'):
            continue
        path = _source_path(h, root)
        if path is None:
            continue
        module = h['module']
        if module not in modules and len(modules) >= 8:
            continue
        if path not in hashes:
            hashes[path] = hashlib.sha256(path.read_bytes()).hexdigest()
        if hashes[path] != h['source_sha256']:
            continue
        if module not in modules:
            modules.append(module)
        candidates[h['name']] = h
    if len(candidates) < 2:
        return []
    # The text index can include partial signatures and wrong namespace guesses.
    # Only exact name/module pairs present in Lean's environment become sources.
    with tempfile.TemporaryDirectory(prefix='amr-pattern-library-') as tmp:
        work = Path(tmp)
        context, env = lean_service._prepare({'project_root': ''}, work)
        code = (research_retrieval.ROOT / 'tools/PatternSources.lean').read_text()
        roots = '\n'.join('import ' + module for module in modules)
        names = json.dumps(list(candidates), ensure_ascii=False)
        (work / 'Resolve.lean').write_text(roots + '\n' + code + '\n#pattern_sources ' + names + ' "sources.json"\n')
        research_lean._run(context, env, work, 'Resolve.lean', [], None, output=False)
        declarations = json.loads((work / 'sources.json').read_text())
    sources = []
    seen_types = set()
    for decl in declarations:
        h = candidates[decl['name']]
        statement = decl['statement']
        if decl['module'] != h['module'] or set(decl['axioms']) - lean_service.ALLOWED_AXIOMS:
            continue
        if statement in seen_types or len(statement) > 20000:
            continue
        seen_types.add(statement)
        identifier = h['id'].removeprefix('lean:')
        sources.append(dict(name=h['name'], title=h['name'], kind='mathlib', declaration_kind='theorem',
                            module=h['module'], statement=statement, sha256=h['source_sha256'],
                            lean_version=context['lean_version'], mathlib_revision=context['mathlib_revision'],
                            axioms=decl['axioms'], line=h['line'], match='msc_title' if codes else 'topic',
                            url='/api/research/library-sources/' + identifier + '?sha256=' + h['source_sha256']))
        if len(sources) == limit:
            break
    return sources
