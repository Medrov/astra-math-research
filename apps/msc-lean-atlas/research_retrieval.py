"""Versioned local mathematical source retrieval. Scores are search hints, not proofs."""
from pathlib import Path
from bisect import bisect_right
from contextlib import closing
import hashlib
import json
import re
import sqlite3
import time

import lean_service

ROOT = Path(__file__).resolve().parent
INDEX_PATH = ROOT / 'research_data' / 'library-index.sqlite'
INDEX_VERSION = 2
ALIASES = {'граф':'graph', 'графы':'graph', 'графов':'graph', 'энергия':'energy', 'энергии':'energy',
           'сумма':'sum', 'суммы':'sum', 'норма':'norm', 'нормы':'norm', 'квадрат':'sq',
           'порядок':'order', 'порядка':'order', 'выпуклый':'convex', 'выпуклость':'convex',
           'множество':'set', 'множества':'set', 'градиент':'gradient', 'лапласиан':'laplacian'}
DECLARATION = re.compile(r'(?m)^[ \t]*(?:@\[[^\n]*?\][ \t]*)*(?:(?:private|protected|noncomputable|unsafe|partial)\s+)*'
                         r'(?P<kind>theorem|lemma|def|abbrev|class|structure|inductive)\s+'
                         r'(?P<name>(?:«[^»]+»|[^\s(:=])+)|^[ \t]*(?:noncomputable[ \t]+)?(?P<scope>namespace|section|end)(?:[ \t]+(?P<scope_name>[^\s]+))?')


def digest(text):
    return hashlib.sha256(text.encode()).hexdigest()


def documents(cases):
    result = []
    for case in cases:
        task = case.get('agent_task', {})
        statement = task.get('statement', case.get('claim', ''))
        result.append(dict(id='case:' + case['id'], title=case['title'],
                           statement=statement, content='\n'.join([case.get('description', ''), statement,
                           task.get('prelude', '')]), source=case.get('source', 'local pilot specification'),
                           msc_codes=case.get('msc_codes', []), evidence_type='research_specification'))
    # A finite, pinned corpus; no hidden web calls and no prepared benchmark solutions.
    path = ROOT / 'catalog/bridges.json'
    if path.exists():
        data = json.loads(path.read_text())
        items = data if isinstance(data, list) else data.get('edges', data.get('bridges', []))
        for i, item in enumerate(items):
            result.append(dict(id='catalog:' + str(i), title=item.get('label', item.get('title', item.get('name', 'Связь из каталога'))),
                               statement=item.get('claim', item.get('description', '')), content=json.dumps(item, ensure_ascii=False),
                               source=item.get('source_url', item.get('sources', item.get('source', 'catalog/bridges.json'))),
                               msc_codes=item.get('msc_codes', [x for x in [item.get('source_msc'), item.get('target_msc')] if x]), evidence_type='literature_hint'))
    for item in result:
        item['sha256'] = digest(item['content'])
    return result


def _terms(query):
    raw = re.findall(r'[^\W_]+', str(query).lower(), re.UNICODE)[:24]
    words = []
    for word in raw:
        if word not in words:
            words.append(word)
        translated = ALIASES.get(word)
        if not translated and word.startswith('выпукл'):
            translated = 'convex'
        if translated and translated not in words:
            words.append(translated)
    return words


def _query(terms, operator='OR'):
    return (' ' + operator + ' ').join('"' + t.replace('"', '""') + '"' for t in terms)


def _curated_search(query, cases, limit):
    docs = documents(cases)
    terms = _terms(query)
    if not terms:
        return docs[:limit]
    conn = sqlite3.connect(':memory:')
    try:
        conn.execute('CREATE VIRTUAL TABLE corpus USING fts5(id UNINDEXED, title, content, tokenize="unicode61")')
        conn.executemany('INSERT INTO corpus VALUES (?,?,?)', [(d['id'], d['title'], d['content']) for d in docs])
        q = _query(terms)
        rows = conn.execute('SELECT id, bm25(corpus) FROM corpus WHERE corpus MATCH ? ORDER BY bm25(corpus) LIMIT ?',
                            (q, limit)).fetchall()
        indexed = {d['id']: d for d in docs}
        return [dict(indexed[key], retrieval_score=-score, retrieval_backend='curated_fts5') for key, score in rows]
    finally:
        conn.close()


def extract_declarations(source, module, path, source_sha256):
    """Conservative textual headers only; names/types are NOT elaborated by Lean.

    The first assignment/equation/where starts the body and is never indexed.
    A type containing a let-assignment can therefore yield a shorter excerpt.
    """
    masked = lean_service._mask(source)
    newlines = [i for i, char in enumerate(masked) if char == '\n']
    matches = list(DECLARATION.finditer(masked))
    comments = list(re.finditer(r'/--([\s\S]*?)-/', source))
    comment_ends = [c.end() for c in comments]
    scopes = []
    for i, match in enumerate(matches):
        scope = match.group('scope')
        if scope:
            if scope == 'end':
                if scopes:
                    scopes.pop()
            else:
                scopes.append((scope, match.group('scope_name') or ''))
            continue
        name = match.group('name')
        namespace = '.'.join(n for kind, n in scopes if kind == 'namespace')
        if name.startswith('_root_.'):
            qualified = name[7:]
        else:
            qualified = '.'.join(x for x in (namespace, name) if x)
        next_start = matches[i + 1].start() if i + 1 < len(matches) else len(source)
        header_start = match.start('kind')
        header = masked[header_start:min(next_start, header_start + 3000)]
        body = re.search(r':=|\bwhere\b|\||\bderiving\b', header)
        if body:
            header = header[:body.start()]
        statement = header.strip()
        # Do not expose arbitrary trailing text when a declaration uses equations.
        if not statement:
            continue
        documentation = ''
        previous = bisect_right(comment_ends, match.start()) - 1
        if previous >= 0:
            comment = comments[previous]
            between = masked[comment.end():match.start()]
            if not re.sub(r'@\[[\s\S]*?\]', '', between).strip():
                documentation = re.sub(r'```[\s\S]*?```', '', comment.group(1)).strip()
                documentation = '\n'.join(line for line in documentation.splitlines() if ':=' not in line)[:1500]
        line = bisect_right(newlines, header_start) + 1
        yield dict(id='lean:' + digest(str(path) + ':' + str(line) + ':' + qualified), title=qualified,
                   name=qualified, declared_name=name, kind=match.group('kind'), module=module,
                   file=str(path), line=line, statement=statement[:2500], doc_comment=documentation,
                   content='\n'.join([qualified, statement[:2500], documentation]), source=str(path),
                   source_sha256=source_sha256, msc_codes=[], evidence_type='library_declaration',
                   extraction='textual_unverified', proof_status='not_checked',
                   sha256=digest(statement + '\n' + documentation))


def _default_roots():
    context = lean_service.default_context()
    roots = []
    for key, prefix in [('mathlib', 'Mathlib'), ('project_root', 'MathResearch')]:
        if context.get(key):
            repository = Path(context[key])
            folder = repository / prefix
            if folder.is_dir():
                roots.append(dict(name=prefix, path=str(folder), repository=str(repository), module_prefix=prefix))
    return roots


def _schema(connection):
    connection.executescript('''
        CREATE TABLE IF NOT EXISTS metadata (key TEXT PRIMARY KEY, value TEXT NOT NULL);
        CREATE TABLE IF NOT EXISTS files (path TEXT PRIMARY KEY, sha256 TEXT NOT NULL, size INTEGER NOT NULL);
        CREATE TABLE IF NOT EXISTS declarations (id TEXT UNIQUE NOT NULL, file TEXT NOT NULL, payload TEXT NOT NULL);
        CREATE INDEX IF NOT EXISTS declarations_file ON declarations(file);
        CREATE VIRTUAL TABLE IF NOT EXISTS declaration_search USING fts5(name, module, signature, documentation, tokenize='unicode61');
    ''')


def _split_names(value):
    return re.sub(r'[_\.]+', ' ', value)


def build_index(index_path=None, roots=None, progress=None):
    """Explicit incremental build. Search and manifest never build the index.

    Optional roots are dicts with path/repository/module_prefix/name, useful for
    isolated fixtures. Each build reads source hashes; unchanged files aren't
    parsed again. A transaction keeps the previous snapshot readable while
    rebuilding. Source files are read-only.
    """
    path = Path(index_path or INDEX_PATH)
    path.parent.mkdir(parents=True, exist_ok=True)
    started = time.monotonic()
    selected = roots if roots is not None else _default_roots()
    connection = sqlite3.connect(path, timeout=60)
    try:
        connection.execute('PRAGMA journal_mode=WAL')
        _schema(connection)
        metadata_row = connection.execute("SELECT value FROM metadata WHERE key='manifest'").fetchone()
        old = json.loads(metadata_row[0]) if metadata_row else {}
        existing = dict(connection.execute('SELECT path,sha256 FROM files'))
        seen, checksums, changed, skipped, sources = set(), [], 0, 0, []
        connection.execute('BEGIN IMMEDIATE')
        if old.get('index_version') != INDEX_VERSION:
            connection.execute('DELETE FROM declaration_search')
            connection.execute('DELETE FROM declarations')
            connection.execute('DELETE FROM files')
            existing = {}
        for spec in selected:
            folder = Path(spec['path']).resolve()
            repository = Path(spec.get('repository', folder)).resolve()
            prefix = spec.get('module_prefix', folder.name)
            source_info = dict(name=spec.get('name', prefix), path=str(folder), repository=str(repository),
                               revision=lean_service._git_revision(str(repository)))
            toolchain = repository / 'lean-toolchain'
            source_info['lean_toolchain'] = toolchain.read_text().strip() if toolchain.is_file() else None
            source_files = sorted(folder.rglob('*.lean')) if folder.is_dir() else []
            source_info['files'] = len(source_files)
            sources.append(source_info)
            for number, file in enumerate(source_files):
                absolute = str(file.resolve())
                raw = file.read_bytes()
                checksum = hashlib.sha256(raw).hexdigest()
                seen.add(absolute)
                checksums.append((absolute, checksum))
                if existing.get(absolute) == checksum:
                    skipped += 1
                    continue
                rows = connection.execute('SELECT rowid FROM declarations WHERE file=?', (absolute,)).fetchall()
                connection.executemany('DELETE FROM declaration_search WHERE rowid=?', rows)
                connection.execute('DELETE FROM declarations WHERE file=?', (absolute,))
                module = prefix + '.' + '.'.join(file.relative_to(folder).with_suffix('').parts)
                for record in extract_declarations(raw.decode('utf-8', errors='replace'), module, absolute, checksum):
                    cursor = connection.execute('INSERT INTO declarations(id,file,payload) VALUES (?,?,?)',
                                                (record['id'], absolute, json.dumps(record, ensure_ascii=False)))
                    connection.execute('INSERT INTO declaration_search(rowid,name,module,signature,documentation) VALUES (?,?,?,?,?)',
                                       (cursor.lastrowid, _split_names(record['name']), _split_names(module),
                                        _split_names(record['statement']), record['doc_comment']))
                connection.execute('INSERT OR REPLACE INTO files VALUES (?,?,?)', (absolute, checksum, len(raw)))
                changed += 1
                if progress and number % 500 == 0:
                    progress(dict(source=source_info['name'], files_processed=number + 1, files_total=len(source_files)))
        for obsolete in set(existing) - seen:
            rows = connection.execute('SELECT rowid FROM declarations WHERE file=?', (obsolete,)).fetchall()
            connection.executemany('DELETE FROM declaration_search WHERE rowid=?', rows)
            connection.execute('DELETE FROM declarations WHERE file=?', (obsolete,))
            connection.execute('DELETE FROM files WHERE path=?', (obsolete,))
        manifest_value = dict(index_version=INDEX_VERSION, status='ready', built_at=time.strftime('%Y-%m-%dT%H:%M:%SZ', time.gmtime()),
                              files=len(seen), declarations=connection.execute('SELECT count(*) FROM declarations').fetchone()[0],
                              source_sha256=digest(json.dumps(sorted(checksums), ensure_ascii=False)),
                              sources=sources, changed_files=changed, unchanged_files=skipped,
                              elapsed_seconds=round(time.monotonic() - started, 3),
                              extraction='textual_unverified', includes_proof_bodies=False,
                              limitations=['Text extraction does not include declarations generated by attributes such as to_additive.',
                                           'Statement excerpts may omit binder context and are not elaborated types.'],
                              scope='Installed Lean source declaration headers and doc comments; not proof certificates.')
        connection.execute("INSERT OR REPLACE INTO metadata VALUES ('manifest',?)", (json.dumps(manifest_value, ensure_ascii=False),))
        connection.commit()
        return manifest_value
    except Exception:
        connection.rollback()
        raise
    finally:
        connection.close()


def library_manifest(index_path=None):
    path = Path(index_path or INDEX_PATH)
    if not path.is_file():
        return dict(status='not_built', declarations=0, files=0)
    try:
        with closing(sqlite3.connect('file:' + str(path) + '?mode=ro', uri=True, timeout=2)) as connection:
            row = connection.execute("SELECT value FROM metadata WHERE key='manifest'").fetchone()
            return json.loads(row[0]) if row else dict(status='not_built', declarations=0, files=0)
    except sqlite3.Error as error:
        return dict(status='unavailable', declarations=0, files=0, error=str(error))


def search_library(query, limit=8, index_path=None):
    terms = _terms(query)
    path = Path(index_path or INDEX_PATH)
    if not terms or not path.is_file():
        return []
    with closing(sqlite3.connect('file:' + str(path) + '?mode=ro', uri=True, timeout=2)) as connection:
        # Exact token conjunction is preferred for symbol searches; OR fallback
        # handles broad natural-language queries without pretending equivalence.
        primary = [t for t in terms if t not in ALIASES and not t.startswith('выпукл')]
        strict = primary or terms
        rows = connection.execute('''SELECT d.payload, bm25(declaration_search,8,2,1,1)
            FROM declaration_search JOIN declarations d ON d.rowid=declaration_search.rowid
            WHERE declaration_search MATCH ? ORDER BY bm25(declaration_search,8,2,1,1) LIMIT ?''', (_query(strict, 'AND'), limit)).fetchall()
        if not rows:
            rows = connection.execute('''SELECT d.payload, bm25(declaration_search,8,2,1,1)
                FROM declaration_search JOIN declarations d ON d.rowid=declaration_search.rowid
                WHERE declaration_search MATCH ? ORDER BY bm25(declaration_search,8,2,1,1) LIMIT ?''', (_query(terms), limit)).fetchall()
        return [dict(json.loads(payload), retrieval_score=-score, retrieval_backend='library_fts5') for payload, score in rows]


def search(query, cases, limit=8):
    """Rank fusion of two lexical indexes; never triggers a rebuild or model call."""
    curated = _curated_search(query, cases, limit)
    try:
        library = search_library(query, limit)
    except sqlite3.Error:
        library = []
    # Scores from different corpora aren't directly comparable. Reciprocal ranks
    # keep both sources discoverable and preserve the score only as a local hint.
    symbol_query = bool(re.search(r'[A-Za-z][A-Za-z0-9]*[_.][A-Za-z0-9]', str(query)))
    rows = [dict(item, fused_rank_score=(1.15 if symbol_query and backend == 'library' else 1) / (60 + rank))
            for backend, results in (('library', library), ('curated', curated))
            for rank, item in enumerate(results, start=1)]
    return sorted(rows, key=lambda d: -d['fused_rank_score'])[:limit]


def manifest(cases):
    docs = documents(cases)
    library = library_manifest()
    base_hash = digest(json.dumps(docs, sort_keys=True, ensure_ascii=False))
    return dict(kind='local_fts5_bm25', documents=len(docs) + library.get('declarations', 0), curated_documents=len(docs),
                sha256=digest(base_hash + str(library.get('index_version')) + library.get('source_sha256', '')) if library.get('status') == 'ready' else base_hash,
                library_index=library,
                scope='Постановки пилота, литературные карточки и явно построенный локальный индекс Lean-деклараций; не весь arXiv.',
                prepared_solutions_included=False)
