"""Versioned mathematical objects and transitions, with bound Lean evidence.

Graph versions are immutable. Results are append-only records for an exact
graph revision and transition; they never certify a later revision implicitly.
This module stores verifier reports supplied by the local research controller.
It is not an endpoint for trusting proof claims submitted by a browser.
"""
from __future__ import annotations

from contextlib import closing
from datetime import datetime, timezone
from functools import lru_cache
import hashlib
import json
from pathlib import Path
import re
import sqlite3
from urllib.parse import urlsplit
import uuid


RELATION_TYPES = {'construction', 'representation', 'property_transfer', 'equivalence', 'reduction'}
LOCAL_ID = re.compile(r'^[A-Za-z0-9_][A-Za-z0-9_.-]{0,79}$')
LEAN_NAME = re.compile(r"^[A-Za-z_][A-Za-z0-9_']*(?:\.[A-Za-z_][A-Za-z0-9_']*)*$")
UUID_HEX = re.compile(r'^[a-f0-9]{32}$')
ALLOWED_AXIOMS = {'propext', 'Classical.choice', 'Quot.sound'}
ROOT = Path(__file__).resolve().parent


def _json(value):
    try:
        return json.dumps(value, sort_keys=True, ensure_ascii=False, separators=(',', ':'), allow_nan=False)
    except (TypeError, ValueError) as error:
        raise ValueError('Expected finite JSON data') from error


def _hash(value):
    return hashlib.sha256(_json(value).encode('utf-8')).hexdigest()


def _now():
    return datetime.now(timezone.utc).isoformat()


def _text(value, label, *, limit=30000, empty=False):
    if not isinstance(value, str) or '\x00' in value or len(value) > limit:
        raise ValueError('Invalid ' + label)
    value = value.replace('\r\n', '\n').replace('\r', '\n').strip()
    if not value and not empty:
        raise ValueError('Empty ' + label)
    return value


def _identifier(value, label='id', pattern=LOCAL_ID):
    if not isinstance(value, str) or not pattern.fullmatch(value):
        raise ValueError('Invalid ' + label)
    return value


def _strings(value, label, *, limit=128):
    if not isinstance(value, list) or len(value) > limit:
        raise ValueError('Invalid ' + label)
    return [_text(item, label, limit=12000) for item in value]


def _fields(value, allowed, label, generated=()):
    if not isinstance(value, dict):
        raise ValueError(label + ' must be an object')
    unknown = set(value) - set(allowed) - set(generated)
    if unknown:
        raise ValueError('Unknown ' + label + ' fields: ' + ', '.join(sorted(map(str, unknown))))


def _array(value, label, *, limit=128, nonempty=False):
    if not isinstance(value, list) or len(value) > limit or (nonempty and not value):
        raise ValueError('Invalid ' + label)
    return value


def _unique(items, label):
    if len(items) != len(set(items)):
        raise ValueError('Duplicate ' + label)


@lru_cache(maxsize=1)
def _known_msc():
    return frozenset(node['id'] for node in json.loads((ROOT / 'data' / 'msc2020.json').read_text(encoding='utf-8'))['nodes'])


def _msc(value):
    codes = _strings(value, 'MSC codes', limit=32)
    _unique(codes, 'MSC codes')
    if any(code not in _known_msc() for code in codes):
        raise ValueError('Unknown MSC code')
    return codes


def _agent_task(value):
    _fields(value, {'imports', 'prelude', 'target', 'statement'}, 'agent_task')
    imports = _strings(value.get('imports'), 'imports', limit=40)
    if not imports or any(not LEAN_NAME.fullmatch(module) for module in imports):
        raise ValueError('Invalid Lean imports')
    _unique(imports, 'imports')
    prelude = value.get('prelude')
    _text(prelude, 'prelude', limit=80000, empty=True)
    # The controller compares pinned fixture definitions exactly, including
    # surrounding newlines. Do not strip source while normalizing display text.
    prelude = prelude.replace('\r\n', '\n').replace('\r', '\n')
    return dict(imports=imports, prelude=prelude,
                target=_identifier(value.get('target'), 'Lean target', LEAN_NAME),
                statement=_text(value.get('statement'), 'target statement'))


def validate_source_transition(value):
    """Validate an exact literature input snapshot, never a Lean certificate."""
    _fields(value, {'kind', 'graph_ref', 'question', 'msc_codes', 'transition', 'objects', 'sources',
                    'semantic_hash', 'source_sha256'}, 'source transition')
    if value.get('kind') != 'literature_transition':
        raise ValueError('Source transition must be explicitly literary, not compiler verified')
    ref = value.get('graph_ref')
    _fields(ref, {'id', 'revision'}, 'source graph reference')
    identifier = _identifier(ref.get('id'), 'source graph', UUID_HEX)
    revision = ref.get('revision')
    if not isinstance(revision, int) or isinstance(revision, bool) or revision < 1:
        raise ValueError('Source graph revision must be exact')
    sources = _array(value.get('sources'), 'source transition sources')
    if any(not isinstance(s, dict) or s.get('structure_transition') or s.get('structure_source_id') for s in sources):
        raise ValueError('A literary input must cite original sources, not another structure input')
    clean = validate_graph(dict(title='Literature input', question=value.get('question'),
        msc_codes=value.get('msc_codes'), objects=value.get('objects'), transitions=[value.get('transition')], sources=sources))
    transition = clean['transitions'][0]
    if {o['id'] for o in clean['objects']} != set(transition['source_ids'] + transition['target_ids']):
        raise ValueError('Source snapshot must contain exactly the transition endpoint objects')
    if {s['id'] for s in clean['sources']} != set(transition.get('source_refs', [])):
        raise ValueError('Source snapshot must contain exactly the cited sources')
    semantic = _fingerprints(clean)['transitions'][transition['id']]
    if value.get('semantic_hash') != semantic:
        raise ValueError('Source transition semantic hash mismatch')
    normalized = dict(kind='literature_transition', graph_ref=dict(id=identifier, revision=revision),
        question=clean['question'], msc_codes=clean['msc_codes'], transition=transition,
        objects=clean['objects'], sources=clean['sources'], semantic_hash=semantic)
    if value.get('source_sha256') != _hash(normalized):
        raise ValueError('Source transition snapshot hash mismatch')
    return dict(normalized, source_sha256=value['source_sha256'])


def validate_graph(graph):
    """Return a clean input graph; derived server fields cannot confer status.

    A get() result can be edited and submitted as a new revision. Known derived
    fields are discarded, while misspelled/unrecognized input fields fail.
    Cycles among objects are valid; proof-plan acyclicity is a separate concern.
    """
    _fields(graph, {'title', 'question', 'msc_codes', 'objects', 'transitions', 'sources', 'layout'}, 'graph',
            {'id', 'revision', 'semantic_hash', 'created_at', 'updated_at', 'environment_fingerprint',
             'current_revision', 'active_environment_fingerprint'})
    clean = dict(title=_text(graph.get('title'), 'graph title', limit=300),
                 question=_text(graph.get('question'), 'question', limit=12000),
                 msc_codes=_msc(graph.get('msc_codes', [])), objects=[], transitions=[], sources=[])
    for item in _array(graph.get('objects'), 'objects', nonempty=True):
        _fields(item, {'id', 'title', 'kind', 'definition', 'parameters', 'assumptions', 'msc_codes', 'lean_refs'},
                'object', {'semantic_hash', 'revision', 'status'})
        clean['objects'].append(dict(id=_identifier(item.get('id')), title=_text(item.get('title'), 'object title', limit=300),
            kind=_text(item.get('kind'), 'object kind', limit=100), definition=_text(item.get('definition'), 'definition'),
            parameters=_strings(item.get('parameters', []), 'parameters'), assumptions=_strings(item.get('assumptions', []), 'assumptions'),
            msc_codes=_msc(item.get('msc_codes', [])), lean_refs=_strings(item.get('lean_refs', []), 'Lean refs')))
    object_ids = [item['id'] for item in clean['objects']]
    _unique(object_ids, 'object ids')
    for item in _array(graph.get('transitions'), 'transitions'):
        _fields(item, {'id', 'title', 'source_ids', 'target_ids', 'relation_type', 'construction', 'assumptions',
                       'claim', 'obligations', 'agent_task', 'case_id', 'formulation_status', 'source_refs'}, 'transition',
                {'semantic_hash', 'status', 'formal_outcome', 'semantic_review', 'results', 'last_result',
                 'certificate', 'previous_certificate', 'dependency_error'})
        relation = item.get('relation_type')
        if not isinstance(relation, str) or relation not in RELATION_TYPES:
            raise ValueError('Invalid relation_type')
        formulation = item.get('formulation_status', 'formalized')
        if formulation not in ('formalized', 'literature_only', 'candidate'):
            raise ValueError('Invalid formulation_status')
        literature_only = formulation in ('literature_only', 'candidate')
        if literature_only and (item.get('agent_task') is not None or item.get('obligations') != [] or item.get('case_id') is not None):
            raise ValueError('Literature-only transitions cannot contain a formal task, obligations, or case_id')
        transition = dict(id=_identifier(item.get('id')), title=_text(item.get('title'), 'transition title', limit=300),
            source_ids=_strings(item.get('source_ids'), 'source_ids'), target_ids=_strings(item.get('target_ids'), 'target_ids'),
            relation_type=relation, construction=_text(item.get('construction'), 'construction'),
            assumptions=_strings(item.get('assumptions', []), 'assumptions'), claim=_text(item.get('claim'), 'claim'),
            obligations=[], agent_task=None if literature_only else _agent_task(item.get('agent_task')), case_id=item.get('case_id'))
        # Do not add optional defaults: old immutable payloads/idempotency keys stay exact.
        if 'formulation_status' in item:
            transition['formulation_status'] = formulation
        if 'source_refs' in item:
            transition['source_refs'] = [_identifier(ref, 'source reference') for ref in _strings(item['source_refs'], 'source_refs')]
            _unique(transition['source_refs'], 'source references')
        for key in ('source_ids', 'target_ids'):
            if not transition[key] or any(ref not in object_ids for ref in transition[key]):
                raise ValueError('Unknown or empty object references: ' + key)
            _unique(transition[key], key)
        if transition['case_id'] is not None:
            _identifier(transition['case_id'], 'case_id')
        for obligation in _array(item.get('obligations'), 'obligations', limit=32, nonempty=not literature_only):
            _fields(obligation, {'id', 'title', 'target', 'statement', 'expected_outcome'}, 'obligation')
            outcome = obligation.get('expected_outcome')
            if outcome not in ('proved', 'refuted'):
                raise ValueError('Invalid expected_outcome')
            transition['obligations'].append(dict(id=_identifier(obligation.get('id')),
                title=_text(obligation.get('title'), 'obligation title', limit=300),
                target=_identifier(obligation.get('target'), 'Lean target', LEAN_NAME),
                statement=_text(obligation.get('statement'), 'obligation statement'), expected_outcome=outcome))
        _unique([obligation['id'] for obligation in transition['obligations']], 'obligation ids')
        _unique([obligation['target'] for obligation in transition['obligations']], 'obligation targets')
        task = transition['agent_task']
        if not literature_only and not any(obligation['target'] == task['target'] and obligation['statement'] == task['statement']
                   for obligation in transition['obligations']):
            raise ValueError('The final target/type must be an explicit obligation')
        clean['transitions'].append(transition)
    _unique([item['id'] for item in clean['transitions']], 'transition ids')
    for item in _array(graph.get('sources', []), 'sources'):
        _fields(item, {'id', 'title', 'url', 'locator', 'versioned_id', 'snapshot_sha256', 'section_id',
                       'structure_source_id', 'structure_target', 'structure_source_sha256', 'structure_transition', 'library_evidence'}, 'source')
        url = _text(item.get('url'), 'source URL', limit=4000, empty=True)
        parsed = urlsplit(url)
        if url and (parsed.scheme not in ('http', 'https') or not parsed.netloc):
            raise ValueError('Source URL must use HTTP(S)')
        source = dict(id=_identifier(item.get('id')), title=_text(item.get('title'), 'source title', limit=500),
                      url=url, locator=_text(item.get('locator'), 'source locator', limit=3000, empty=True))
        for key in ('versioned_id', 'snapshot_sha256', 'section_id'):
            if key in item:
                source[key] = _text(item[key], 'source ' + key, limit=512)
        structure_keys = {'structure_source_id', 'structure_target', 'structure_source_sha256'}
        if structure_keys.intersection(item):
            if not structure_keys.issubset(item):
                raise ValueError('Incomplete structure source binding')
            source['structure_source_id'] = _identifier(item['structure_source_id'], 'structure source', UUID_HEX)
            source['structure_target'] = _identifier(item['structure_target'], 'structure target', LEAN_NAME)
            source['structure_source_sha256'] = _identifier(item['structure_source_sha256'], 'source hash', re.compile(r'^[a-f0-9]{64}$'))
        if 'library_evidence' in item:
            evidence = item['library_evidence']
            _fields(evidence, {'id','title','name','module','statement','doc_comment','source_sha256','extraction'}, 'library evidence')
            source['library_evidence'] = {key:_text(value, 'library '+key, limit=30000, empty=True) for key,value in evidence.items()}
        if 'structure_transition' in item:
            source['structure_transition'] = validate_source_transition(item['structure_transition'])
            if structure_keys.intersection(item):
                raise ValueError('A source cannot be both a Lean theorem and a literature transition')
        clean['sources'].append(source)
    _unique([item['id'] for item in clean['sources']], 'source ids')
    source_ids = {item['id'] for item in clean['sources']}
    structure_ids = {item['id'] for item in clean['sources'] if item.get('structure_source_id')}
    literature_ids = {item['id'] for item in clean['sources'] if item.get('structure_transition')}
    if structure_ids and literature_ids:
        raise ValueError('A structure graph must have exactly one kind of original input')
    for transition in clean['transitions']:
        if set(transition.get('source_refs', [])) - source_ids:
            raise ValueError('Unknown source reference')
        uses_input = 'StructureInput' in (transition.get('agent_task') or {}).get('imports', [])
        if (structure_ids or uses_input) and len(structure_ids & set(transition.get('source_refs', []))) != 1:
            raise ValueError('Every structure transition must reference exactly one pinned input source')
        if literature_ids and len(literature_ids & set(transition.get('source_refs', []))) != 1:
            raise ValueError('Every analogy transition must reference exactly one pinned literature input')
        if literature_ids and not any(s.get('library_evidence') and s['id'] in transition.get('source_refs', []) for s in clean['sources']):
            raise ValueError('An analogy transition requires retained library evidence')
    if 'layout' in graph:
        if not isinstance(graph['layout'], dict) or len(_json(graph['layout'])) > 100000:
            raise ValueError('Invalid layout')
        clean['layout'] = json.loads(_json(graph['layout']))
    if len(_json(clean)) > 1500000:
        raise ValueError('Graph is too large')
    return clean


def transition_contract(transition):
    """Formal task for the existing controller, plus all mandatory goals."""
    if transition.get('formulation_status', 'formalized') in ('literature_only', 'candidate'):
        return dict(task=None, obligations=[])
    return dict(**json.loads(_json(transition['agent_task'])),
                obligations=[{key: item[key] for key in ('id', 'target', 'statement', 'expected_outcome')}
                             for item in transition['obligations']])


def _fingerprints(graph):
    objects = {item['id']: _hash({key: item[key] for key in
               ('kind', 'definition', 'parameters', 'assumptions', 'lean_refs')}) for item in graph['objects']}
    transitions = {}
    sources = {source['id']: source for source in graph['sources']}
    for transition in graph['transitions']:
        value = {key: transition[key] for key in ('relation_type', 'construction', 'assumptions', 'claim', 'case_id')}
        value.update(question=graph['question'], contract=transition_contract(transition),
                     source_objects=sorted((ref, objects[ref]) for ref in transition['source_ids']),
                     target_objects=sorted((ref, objects[ref]) for ref in transition['target_ids']))
        if transition.get('formulation_status', 'formalized') in ('literature_only', 'candidate'):
            value['formulation_status'] = transition['formulation_status']
        if 'source_refs' in transition:
            value['source_provenance'] = [{key: source[key] for key in
                ('id', 'url', 'locator', 'versioned_id', 'snapshot_sha256', 'section_id',
                  'structure_source_id', 'structure_target', 'structure_source_sha256', 'structure_transition', 'library_evidence') if key in source}
                for source in (sources[ref] for ref in sorted(transition['source_refs']))]
        transitions[transition['id']] = _hash(value)
    return dict(semantic_hash=_hash(dict(question=graph['question'], objects=objects, transitions=transitions)),
                objects=objects, transitions=transitions)


def graph_fingerprints(graph):
    return _fingerprints(validate_graph(graph))


def transition_fingerprint(graph, transition_id):
    hashes = graph_fingerprints(graph)['transitions']
    if transition_id not in hashes:
        raise ValueError('Unknown transition')
    return hashes[transition_id]


def _environment(value):
    return None if value is None else _text(value, 'environment fingerprint', limit=256)


def _verdict(transition, result):
    """A claimed outcome is never sufficient; check all bound goal witnesses."""
    if transition.get('formulation_status', 'formalized') in ('literature_only', 'candidate'):
        return 'unknown', ['literature-only transition has no formal contract']
    errors = []
    report = result.get('verification')
    report = report if isinstance(report, dict) else {}
    for flag in ('success', 'compilation_success', 'target_preserved', 'obligations_passed'):
        if report.get(flag) is not True:
            errors.append('verification.' + flag)
    task = transition['agent_task']
    if report.get('target') != task['target'] or report.get('expected_statement') != task['statement']:
        errors.append('final target/type mismatch')
    audit = report.get('audit')
    if not isinstance(audit, dict) or audit.get('status') != 'passed' or audit.get('unexpected_axioms') or audit.get('unsafe_declarations'):
        errors.append('axiom audit')
    axioms = report.get('axioms', [])
    if not isinstance(axioms, list) or any(axiom not in ALLOWED_AXIOMS for axiom in axioms):
        errors.append('unexpected target axioms')
    entries = report.get('obligations')
    expected = {item['id']: item for item in transition['obligations']}
    if not isinstance(entries, list) or any(not isinstance(item, dict) for item in entries):
        entries = []
    ids = [entry.get('id') for entry in entries]
    if len(ids) != len(expected) or any(not isinstance(key, str) for key in ids) or set(ids) != set(expected):
        errors.append('obligation set mismatch')
    else:
        for entry in entries:
            obligation = expected[entry['id']]
            statement_hash = hashlib.sha256(obligation['statement'].encode('utf-8')).hexdigest()
            if entry.get('ok') is not True or entry.get('target') != obligation['target'] or entry.get('statement_sha256') != statement_hash:
                errors.append('obligation mismatch: ' + obligation['id'])
    final = next(item for item in transition['obligations'] if item['target'] == task['target'])
    outcome = final['expected_outcome']
    if result.get('formal_outcome') != outcome:
        errors.append('formal outcome mismatch')
    environment = result.get('environment_fingerprint')
    if not isinstance(environment, str) or not environment.strip():
        errors.append('missing environment fingerprint')
    return ('unknown' if errors else outcome), errors


class RevisionConflict(ValueError):
    pass


class GraphRegistry:
    """Disk-backed registry. Each operation owns and closes its SQLite handle."""
    def __init__(self, path, environment_fingerprint=None):
        self.path = Path(path)
        self.path.parent.mkdir(parents=True, exist_ok=True)
        self.environment_fingerprint = _environment(environment_fingerprint)
        with closing(self._connect()) as connection, connection:
            connection.executescript('''
                CREATE TABLE IF NOT EXISTS graphs (
                    id TEXT PRIMARY KEY, current_revision INTEGER NOT NULL, created_at TEXT NOT NULL);
                CREATE TABLE IF NOT EXISTS graph_versions (
                    graph_id TEXT NOT NULL REFERENCES graphs(id), revision INTEGER NOT NULL,
                    payload TEXT NOT NULL, semantic_hash TEXT NOT NULL, environment_fingerprint TEXT,
                    created_at TEXT NOT NULL, PRIMARY KEY (graph_id, revision));
                CREATE TABLE IF NOT EXISTS graph_results (
                    graph_id TEXT NOT NULL, revision INTEGER NOT NULL, transition_id TEXT NOT NULL,
                    run_id TEXT NOT NULL, publication_id TEXT NOT NULL DEFAULT '', payload TEXT NOT NULL, payload_sha256 TEXT NOT NULL,
                    semantic_hash TEXT NOT NULL, verdict TEXT NOT NULL, errors TEXT NOT NULL,
                    environment_fingerprint TEXT, created_at TEXT NOT NULL,
                    PRIMARY KEY (graph_id, revision, transition_id, run_id, publication_id),
                    FOREIGN KEY (graph_id, revision) REFERENCES graph_versions(graph_id, revision));
                CREATE TABLE IF NOT EXISTS graph_carryovers (
                    graph_id TEXT NOT NULL, revision INTEGER NOT NULL, transition_id TEXT NOT NULL,
                    source_revision INTEGER NOT NULL, source_transition_id TEXT NOT NULL,
                    source_run_id TEXT NOT NULL, source_publication_id TEXT NOT NULL DEFAULT '', accepted INTEGER NOT NULL,
                    PRIMARY KEY (graph_id, revision, transition_id),
                    FOREIGN KEY (graph_id, revision) REFERENCES graph_versions(graph_id, revision));
                CREATE TABLE IF NOT EXISTS graph_creation_keys (
                    idempotency_key TEXT PRIMARY KEY, graph_id TEXT NOT NULL REFERENCES graphs(id),
                    payload_sha256 TEXT NOT NULL);
            ''')
            self._migrate_publications(connection)

    @staticmethod
    def _migrate_publications(connection):
        """Preserve records from the initial run-keyed local registry format."""
        connection.execute('BEGIN IMMEDIATE')
        columns = {row['name'] for row in connection.execute('PRAGMA table_info(graph_results)')}
        if 'publication_id' not in columns:
            connection.execute('ALTER TABLE graph_results RENAME TO graph_results_legacy')
            connection.execute('''CREATE TABLE graph_results (
                graph_id TEXT NOT NULL, revision INTEGER NOT NULL, transition_id TEXT NOT NULL,
                run_id TEXT NOT NULL, publication_id TEXT NOT NULL DEFAULT '', payload TEXT NOT NULL, payload_sha256 TEXT NOT NULL,
                semantic_hash TEXT NOT NULL, verdict TEXT NOT NULL, errors TEXT NOT NULL,
                environment_fingerprint TEXT, created_at TEXT NOT NULL,
                PRIMARY KEY (graph_id, revision, transition_id, run_id, publication_id),
                FOREIGN KEY (graph_id, revision) REFERENCES graph_versions(graph_id, revision))''')
            connection.execute('''INSERT INTO graph_results
                SELECT graph_id,revision,transition_id,run_id,'',payload,payload_sha256,semantic_hash,verdict,errors,
                       environment_fingerprint,created_at FROM graph_results_legacy''')
            connection.execute('DROP TABLE graph_results_legacy')
        carry_columns = {row['name'] for row in connection.execute('PRAGMA table_info(graph_carryovers)')}
        if 'source_publication_id' not in carry_columns:
            connection.execute("ALTER TABLE graph_carryovers ADD COLUMN source_publication_id TEXT NOT NULL DEFAULT ''")

    def _connect(self):
        connection = sqlite3.connect(self.path, timeout=30)
        connection.row_factory = sqlite3.Row
        connection.execute('PRAGMA foreign_keys=ON')
        return connection

    def create(self, graph, *, idempotency_key=None):
        graph = validate_graph(graph)
        payload, hashes = _json(graph), _fingerprints(graph)
        key = _text(idempotency_key, 'idempotency key', limit=300) if idempotency_key is not None else None
        with closing(self._connect()) as connection, connection:
            connection.execute('BEGIN IMMEDIATE')
            if key:
                existing = connection.execute('SELECT * FROM graph_creation_keys WHERE idempotency_key=?', (key,)).fetchone()
                if existing:
                    if existing['payload_sha256'] != _hash(graph):
                        raise ValueError('Idempotency key belongs to a different graph')
                    return self._get(connection, existing['graph_id'], 1)
            graph_id, created = uuid.uuid4().hex, _now()
            connection.execute('INSERT INTO graphs VALUES (?,?,?)', (graph_id, 1, created))
            connection.execute('INSERT INTO graph_versions VALUES (?,?,?,?,?,?)',
                (graph_id, 1, payload, hashes['semantic_hash'], self.environment_fingerprint, created))
            if key:
                connection.execute('INSERT INTO graph_creation_keys VALUES (?,?,?)', (key, graph_id, _hash(graph)))
            return self._get(connection, graph_id, 1)

    def get(self, graph_id, revision=None):
        _identifier(graph_id, 'graph id', UUID_HEX)
        with closing(self._connect()) as connection:
            return self._get(connection, graph_id, revision)

    def _get(self, connection, graph_id, revision=None):
        head = connection.execute('SELECT * FROM graphs WHERE id=?', (graph_id,)).fetchone()
        if not head:
            raise FileNotFoundError('Object graph not found')
        revision = head['current_revision'] if revision is None else revision
        if not isinstance(revision, int) or isinstance(revision, bool) or revision < 1:
            raise ValueError('Invalid graph revision')
        version = connection.execute('SELECT * FROM graph_versions WHERE graph_id=? AND revision=?', (graph_id, revision)).fetchone()
        if not version:
            raise FileNotFoundError('Object graph revision not found')
        graph = json.loads(version['payload'])
        hashes = _fingerprints(graph)
        graph.update(id=graph_id, revision=revision, current_revision=head['current_revision'],
                     semantic_hash=version['semantic_hash'], created_at=version['created_at'],
                     environment_fingerprint=version['environment_fingerprint'])
        current_env = self.environment_fingerprint or version['environment_fingerprint']
        graph['active_environment_fingerprint'] = current_env
        for obj in graph['objects']:
            obj['semantic_hash'] = hashes['objects'][obj['id']]
        for transition in graph['transitions']:
            transition_hash = hashes['transitions'][transition['id']]
            rows = connection.execute('SELECT * FROM graph_results WHERE graph_id=? AND revision=? AND transition_id=? ORDER BY rowid',
                                      (graph_id, revision, transition['id'])).fetchall()
            results = [self._result_view(row) for row in rows]
            carry = connection.execute('''SELECT r.*, c.accepted FROM graph_carryovers c JOIN graph_results r
                    ON r.graph_id=c.graph_id AND r.revision=c.source_revision AND r.transition_id=c.source_transition_id
                    AND r.run_id=c.source_run_id AND r.publication_id=c.source_publication_id
                    WHERE c.graph_id=? AND c.revision=? AND c.transition_id=?''',
                    (graph_id, revision, transition['id'])).fetchone()
            candidates = [(row, True) for row in rows if row['verdict'] in ('proved', 'refuted')]
            if carry:
                candidates.insert(0, (carry, bool(carry['accepted'])))
            certificate, previous = None, None
            for row, accepted in candidates:
                previous = self._result_view(row)
                if accepted and row['semantic_hash'] == transition_hash and (not current_env or current_env == row['environment_fingerprint']):
                    certificate = previous
            status = certificate['formal_outcome'] if certificate else ('needs_recheck' if previous else 'unknown' if results else 'proposed')
            selected = certificate or (results[-1] if results else None)
            semantic = selected['result'].get('semantic_review') if selected else None
            transition.update(semantic_hash=transition_hash, status=status,
                              formal_outcome=certificate['formal_outcome'] if certificate else 'unknown',
                              semantic_review=semantic if isinstance(semantic, dict) else {'status': 'pending'},
                              results=results, last_result=results[-1] if results else None,
                              certificate=certificate, previous_certificate=previous if certificate is None else None)
        return graph

    @staticmethod
    def _result_view(row):
        return dict(graph_id=row['graph_id'], revision=row['revision'], transition_id=row['transition_id'],
                    run_id=row['run_id'], publication_id=row['publication_id'] or None,
                    semantic_hash=row['semantic_hash'], formal_outcome=row['verdict'],
                    environment_fingerprint=row['environment_fingerprint'], recorded_at=row['created_at'],
                    validation_errors=json.loads(row['errors']), result=json.loads(row['payload']))

    def list_graphs(self):
        with closing(self._connect()) as connection:
            rows = connection.execute('''SELECT v.* FROM graphs g JOIN graph_versions v
                    ON v.graph_id=g.id AND v.revision=g.current_revision ORDER BY g.created_at DESC, g.id''').fetchall()
            return [dict(id=row['graph_id'], revision=row['revision'], title=json.loads(row['payload'])['title'],
                         question=json.loads(row['payload'])['question'], semantic_hash=row['semantic_hash'],
                         created_at=row['created_at']) for row in rows]

    def revise(self, graph_id, graph, expected_revision, *, environment_fingerprint=None):
        _identifier(graph_id, 'graph id', UUID_HEX)
        if not isinstance(expected_revision, int) or isinstance(expected_revision, bool) or expected_revision < 1:
            raise ValueError('Invalid expected_revision')
        graph = validate_graph(graph)
        hashes = _fingerprints(graph)
        environment = _environment(environment_fingerprint) if environment_fingerprint is not None else self.environment_fingerprint
        with closing(self._connect()) as connection, connection:
            connection.execute('BEGIN IMMEDIATE')
            previous = self._get(connection, graph_id)
            if previous['revision'] != expected_revision:
                raise RevisionConflict('Graph changed; reload its current revision')
            revision = expected_revision + 1
            connection.execute('INSERT INTO graph_versions VALUES (?,?,?,?,?,?)',
                (graph_id, revision, _json(graph), hashes['semantic_hash'], environment, _now()))
            for transition in graph['transitions']:
                old = next((item for item in previous['transitions'] if item['id'] == transition['id']), None)
                candidate = (old.get('certificate') or old.get('previous_certificate')) if old else None
                if candidate:
                    accepted = bool(environment and environment == candidate['environment_fingerprint'] and
                                    hashes['transitions'][transition['id']] == candidate['semantic_hash'])
                    connection.execute('''INSERT INTO graph_carryovers
                        (graph_id,revision,transition_id,source_revision,source_transition_id,source_run_id,source_publication_id,accepted)
                        VALUES (?,?,?,?,?,?,?,?)''',
                        (graph_id, revision, transition['id'], candidate['revision'], candidate['transition_id'],
                         candidate['run_id'], candidate.get('publication_id') or '', int(accepted)))
            connection.execute('UPDATE graphs SET current_revision=? WHERE id=?', (revision, graph_id))
            return self._get(connection, graph_id, revision)

    def record_result(self, graph_id, revision, transition_id, run_id, result):
        _identifier(graph_id, 'graph id', UUID_HEX)
        _identifier(transition_id, 'transition id')
        _identifier(run_id, 'run id', UUID_HEX)
        if not isinstance(revision, int) or isinstance(revision, bool) or revision < 1:
            raise ValueError('A result requires an explicit graph revision')
        if not isinstance(result, dict):
            raise ValueError('Result must be an object')
        publication_id = result.get('publication_id')
        if publication_id is not None:
            _identifier(publication_id, 'publication id', UUID_HEX)
        publication_id = publication_id or ''
        payload = _json(result)
        if len(payload) > 12000000:
            raise ValueError('Result is too large')
        with closing(self._connect()) as connection, connection:
            connection.execute('BEGIN IMMEDIATE')
            graph = self._get(connection, graph_id, revision)
            transition = next((item for item in graph['transitions'] if item['id'] == transition_id), None)
            if transition is None:
                raise ValueError('Unknown transition')
            prior = connection.execute('''SELECT payload_sha256 FROM graph_results
                WHERE graph_id=? AND revision=? AND transition_id=? AND run_id=? AND publication_id=?''',
                (graph_id, revision, transition_id, run_id, publication_id)).fetchone()
            digest = _hash(result)
            if prior:
                if prior['payload_sha256'] != digest:
                    raise ValueError('Run result is immutable; use a new run id for another attempt')
                return graph
            verdict, errors = _verdict(transition, result)
            environment = result.get('environment_fingerprint')
            if environment is not None:
                environment = _environment(environment)
            connection.execute('INSERT INTO graph_results VALUES (?,?,?,?,?,?,?,?,?,?,?,?)',
                (graph_id, revision, transition_id, run_id, publication_id, payload, digest, transition['semantic_hash'], verdict,
                 _json(errors), environment, _now()))
            return self._get(connection, graph_id, revision)
