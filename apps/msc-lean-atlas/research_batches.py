"""Durable serial orchestration of existing proof runs; never a proof engine."""
from concurrent.futures import ThreadPoolExecutor
from contextlib import contextmanager
import copy
import hashlib
import json
import os
from pathlib import Path
import re
import threading

from platform_support import lock_file, unlock_file
from research_service import now, owner_alive, sha
from research_objects import validate_graph, transition_fingerprint, _verdict

ACTIVE = {'queued', 'running', 'cancelling'}
RUN_ACTIVE = {'queued', 'running', 'cancelling'}


def exact_task(transition):
    return dict(transition['agent_task'], required_obligations=transition['obligations']) if transition.get('agent_task') else None


def source_pins(graph, transition):
    refs = set(transition.get('source_refs', []))
    return sorted((sha({k:s[k] for k in ('structure_transition', 'structure_source_id', 'structure_target',
                                       'structure_source_sha256') if k in s})
                   for s in graph.get('sources', []) if s['id'] in refs and
                   any(k in s for k in ('structure_transition', 'structure_source_id'))))


class BatchConflict(ValueError):
    pass


class ResearchBatches:
    def __init__(self, service, root=None, *, poll_seconds=1, dispatch=True):
        self.service = service
        self.root = Path(root or service.root / 'batches').resolve()
        self.root.mkdir(parents=True, exist_ok=True)
        self.lock = threading.RLock()
        self.pool = ThreadPoolExecutor(max_workers=1, thread_name_prefix='research-batch')
        self.stop = threading.Event()
        self.poll_seconds = poll_seconds
        self.dispatch = dispatch  # deterministic tests may drive _work explicitly
        self.futures = {}
        with self._guard():
            for path in self.root.glob('*/batch.json'):
                batch = json.loads(path.read_text(encoding='utf-8'))
                if batch['status'] in ACTIVE and not owner_alive(batch.get('owner_pid')):
                    batch.update(status='interrupted', reason='Сервер остановился; пакет автоматически не возобновляется.', finished_at=now())
                    for item in batch['items']:
                        if item['status'] in ACTIVE:
                            item.update(status='interrupted', reason='Запуск пакета прерван; продолжение требует нового явного запроса.')
                    self._save(batch)

    @contextmanager
    def _guard(self):
        with self.lock, (self.root / 'state.lock').open('a+b') as stream:
            lock_file(stream)
            try:
                yield
            finally:
                unlock_file(stream)

    def _path(self, identifier):
        if not isinstance(identifier, str) or not re.fullmatch('[a-f0-9]{32}', identifier):
            raise ValueError('Недопустимый ID пакета.')
        return self.root / identifier / 'batch.json'

    def _read(self, identifier):
        return json.loads(self._path(identifier).read_text(encoding='utf-8'))

    def _save(self, batch):
        path = self._path(batch['id']); path.parent.mkdir(parents=True, exist_ok=True)
        batch['updated_at'] = now()
        batch['usage'] = {key:sum(item.get('usage', {}).get(key, 0) for item in batch['items'])
                          for key in ('calls', 'total_tokens', 'elapsed_seconds')}
        temporary = path.with_suffix('.tmp')
        temporary.write_text(json.dumps(batch, ensure_ascii=False, indent=2) + '\n', encoding='utf-8')
        temporary.replace(path)

    @staticmethod
    def _request(payload, *, creating=False):
        allowed = {'graph_id', 'graph_revision', 'transition_ids', 'mode', 'budget', 'graph_sha256', 'idempotency_key'}
        if not isinstance(payload, dict) or set(payload) - allowed:
            raise ValueError('Неизвестные поля запроса пакетной проверки.')
        identifier, revision = payload.get('graph_id'), payload.get('graph_revision')
        if not isinstance(identifier, str) or not re.fullmatch('[a-f0-9]{32}', identifier):
            raise ValueError('Нужен ID сохранённой карты.')
        if type(revision) is not int or revision < 1:
            raise ValueError('Нужна точная версия карты.')
        ids = payload.get('transition_ids')
        if ids is not None and (not isinstance(ids, list) or not 1 <= len(ids) <= 32 or
                               any(not isinstance(i, str) for i in ids) or len(set(ids)) != len(ids)):
            raise ValueError('Выберите от 1 до 32 разных переходов.')
        if creating and ids is None:
            raise ValueError('Для запуска нужен явный список transition_ids.')
        mode, budget = payload.get('mode', 'multi'), payload.get('budget', {})
        if mode not in ('single', 'multi') or not isinstance(budget, dict) or set(budget) - {'max_calls', 'timeout_seconds', 'max_parallel'}:
            raise ValueError('Нужны режим single/multi и бюджет одной связи.')
        calls, seconds = budget.get('max_calls', 8), budget.get('timeout_seconds', 600)
        if type(calls) is not int or not 1 <= calls <= 24 or type(seconds) is not int or not 30 <= seconds <= 1800:
            raise ValueError('Бюджет одной связи: 1–24 вызова и 30–1800 секунд.')
        if budget.get('max_parallel', 2) != 2:
            raise ValueError('Внутренний лимит существующего исследователя max_parallel равен 2; связи запускаются последовательно.')
        digest = payload.get('graph_sha256')
        if digest is not None and (not isinstance(digest, str) or not re.fullmatch('[a-f0-9]{64}', digest)):
            raise ValueError('Некорректный хеш карты.')
        return dict(graph_id=identifier, graph_revision=revision, transition_ids=ids, mode=mode,
                    budget=dict(max_calls=calls, timeout_seconds=seconds, max_parallel=2), graph_sha256=digest)

    def _saved_runs(self):
        # Full contracts are needed for equivalence checks; summaries are not certificates.
        return [self.service.get(row['id']) for row in self.service.list_runs()]

    def _candidate(self, graph, transition, runs):
        row = dict(transition_id=transition['id'], title=transition['title'], eligible=True,
                   status='proposed', reason='Связь доступна для отдельной проверки.', reason_code='available')
        def verdict(status, reason, code, run=None, eligible=False):
            row.update(status=status, reason=reason, reason_code=code, eligible=eligible)
            if run:
                row.update(run_id=run['id'], termination=run.get('termination'), run_status=run.get('status'))
                cv = run.get('contract_verification') or {}
                row['contract_verification'] = {k:cv[k] for k in ('kind','status','well_typed','proof_checked','error') if k in cv}
            return row
        bridge = transition.get('formulation_status') == 'candidate' or bool(source_pins(graph, transition))
        if not bridge or transition.get('formulation_status') == 'literature_only':
            return verdict('ineligible', 'Пакет проверяет предложенные связи; исходные переходы статьи запускаются отдельно.', 'not_bridge')
        if transition.get('dependency_error'):
            return verdict('invalid_contract', transition['dependency_error'], 'source_changed')
        ref = dict(id=graph['id'], revision=graph['revision'])
        fixed = exact_task(transition)
        matches, historical = [], []
        for run in runs:
            if run.get('purpose', 'prove') != 'prove':
                continue
            direct = run.get('graph_ref') == ref and run.get('selected_transition_id') == transition['id']
            derived = run.get('source_graph_ref') == ref and run.get('source_transition_id', run.get('selected_transition_id')) == transition['id']
            contract = run.get('object_contract') or {}
            previous_graph = contract.get('graph') or {}
            previous = next((t for t in previous_graph.get('transitions', []) if t['id'] == contract.get('transition_id')), None)
            same_task = bool(fixed and previous and exact_task(previous) == fixed and
                             source_pins(previous_graph, previous) == source_pins(graph, transition))
            same_semantic = bool(previous and transition_fingerprint(previous_graph, previous['id']) == transition_fingerprint(graph, transition['id']))
            if direct or derived:
                if run.get('status') in RUN_ACTIVE:
                    return verdict('checking', 'Уже выполняется проверка этой связи или её производной постановки.', 'active_run', run)
                matches.append((run, direct or same_semantic, same_task))
            if same_task and same_semantic:
                historical.append(run)
        # Registry certificates are actual exact-goal witnesses, but semantic
        # alignment must also be established to call the current link verified.
        certificate = transition.get('certificate') or {}
        if certificate and certificate.get('environment_fingerprint') == self.service.environment_fingerprint:
            sem = (certificate.get('result') or {}).get('semantic_review') or {}
            if sem.get('status') in ('aligned', 'reviewed_fixture'):
                return verdict('verified', 'Эта версия связи уже проверена; повторный расход бюджета не нужен.', 'verified', {'id':certificate['run_id']})
            return verdict('needs_review', 'Формальная цель проверена, но смысл связи требует уточнения.', 'semantic_review_required', {'id':certificate['run_id']})
        for run in historical:
            result = run.get('result') or {}; report = result.get('verification') or {}
            environment = report.get('environment_fingerprint', result.get('environment_fingerprint'))
            sem = run.get('final_semantic_review') or result.get('semantic_review') or {}
            if environment == self.service.environment_fingerprint and sem.get('status') in ('aligned', 'reviewed_fixture'):
                outcome, errors = _verdict(transition, dict(result, environment_fingerprint=environment))
                if not errors and outcome in ('proved', 'refuted'):
                    return verdict('historical_exact_evidence', 'Такая же формальная постановка уже проверена в другом запуске. Это не перенос сертификата на всю текущую связь.', 'exact_formal_result', run)
        for run, semantic_match, task_match in matches:
            cv = run.get('contract_verification') or {}
            invalid = (fixed and task_match and cv.get('kind') == 'lean_contract_preflight' and cv.get('proof_checked') is False
                       and cv.get('well_typed') is False and cv.get('status') == 'rejected'
                       and cv.get('termination', {}).get('code') == 'invalid_contract'
                       and cv.get('contract_sha256') == sha(fixed) and cv.get('environment_fingerprint') == self.service.environment_fingerprint)
            if invalid:
                return verdict('invalid_contract', 'Lean отклонил эту формальную постановку. Сначала нужна новая версия.', 'invalid_contract', run)
            if semantic_match and (run.get('requires_review') or (run.get('termination') or {}).get('code') == 'needs_review'):
                return verdict('needs_review', 'Эта постановка требует уточнения перед новой проверкой.', 'needs_review', run)
        if matches:
            return verdict('not_proved', 'Доказательство в предыдущем запуске не получено. Возможна отдельная новая попытка.', 'not_proved', matches[0][0], eligible=True)
        return row

    def preview(self, payload):
        request = self._request(payload)
        graph = self.service.graph(request['graph_id'], request['graph_revision'])
        digest = sha(validate_graph(graph))
        if request['graph_sha256'] and request['graph_sha256'] != digest:
            raise BatchConflict('Карта изменилась относительно предварительного просмотра.')
        by_id = {t['id']:t for t in graph['transitions']}
        ids = request['transition_ids'] or list(by_id)
        if any(identifier not in by_id for identifier in ids):
            raise ValueError('Выбранный переход отсутствует в этой версии карты.')
        runs = self._saved_runs()
        candidates = [self._candidate(graph, by_id[identifier], runs) for identifier in ids]
        count = sum(item['eligible'] for item in candidates)
        return dict(graph_ref=dict(id=graph['id'], revision=graph['revision']), graph_sha256=digest,
                    mode=request['mode'], budget=request['budget'], candidates=candidates,
                    aggregate=dict(selected=len(ids), eligible=count, skipped=len(ids)-count,
                                   max_calls=count*request['budget']['max_calls'],
                                   timeout_seconds=count*request['budget']['timeout_seconds'], max_parallel_runs=1))

    def create(self, payload):
        request = self._request(payload, creating=True)
        key = payload.get('idempotency_key')
        if not isinstance(key, str) or not re.fullmatch(r'[A-Za-z0-9_.:-]{8,128}', key):
            raise ValueError('Нужен явный idempotency_key длиной 8–128 символов.')
        identifier = hashlib.sha256(key.encode()).hexdigest()[:32]
        with self._guard():
            if self._path(identifier).exists():
                previous = self._read(identifier)
                if previous['request_sha256'] != sha(request):
                    raise BatchConflict('Этот idempotency_key уже относится к другому запросу.')
                return previous
            preview = self.preview(payload)
            batch = dict(id=identifier, status='queued', created_at=now(), owner_pid=os.getpid(), cancel_requested=False,
                         request=request, request_sha256=sha(request), graph_ref=preview['graph_ref'],
                         graph_sha256=preview['graph_sha256'], mode=preview['mode'], budget=preview['budget'],
                         aggregate=preview['aggregate'], items=[dict(item, status='queued' if item['eligible'] else 'skipped',
                             preview_status=item['status']) for item in preview['candidates']])
            if not preview['aggregate']['eligible']:
                batch.update(status='complete', finished_at=now())
            self._save(batch)
        if batch['status'] == 'queued' and self.dispatch:
            self.futures[identifier] = self.pool.submit(self._work, identifier)
        return self.get(identifier)

    def get(self, identifier):
        with self._guard():
            return self._read(identifier)

    def list(self, graph_id=None, revision=None):
        with self._guard():
            values = [json.loads(p.read_text(encoding='utf-8')) for p in self.root.glob('*/batch.json')]
        return sorted((b for b in values if (graph_id is None or b['graph_ref']['id'] == graph_id) and
                       (revision is None or b['graph_ref']['revision'] == revision)), key=lambda b:b['created_at'], reverse=True)

    def cancel(self, identifier):
        with self._guard():
            batch = self._read(identifier)
            if batch['status'] not in ACTIVE:
                return batch
            batch.update(cancel_requested=True, status='cancelling')
            running = []
            for item in batch['items']:
                if item['status'] == 'queued':
                    item.update(status='cancelled', reason='Отменено до запуска.')
                elif item['status'] == 'running' and item.get('run_id'):
                    running.append(item['run_id'])
            if not running:
                batch.update(status='cancelled', finished_at=now())
            self._save(batch)
        for run_id in running:
            self.service.cancel(run_id)
        return self.get(identifier)

    def _work(self, identifier):
        # The lease serializes packages even across two live localhost servers.
        with (self.root/'worker.lock').open('a+b') as lease:
            acquired = False
            try:
                while not acquired:
                    if self.stop.is_set() or self.get(identifier)['status'] not in ACTIVE:
                        return
                    try:
                        lock_file(lease, blocking=False); acquired = True
                    except BlockingIOError:
                        self.stop.wait(self.poll_seconds)
                self._run_items(identifier)
            except Exception as error:
                with self._guard():
                    batch = self._read(identifier)
                    batch.update(status='interrupted', reason=str(error), finished_at=now())
                    for item in batch['items']:
                        if item['status'] in ACTIVE: item.update(status='interrupted', reason=str(error))
                    self._save(batch)
            finally:
                if acquired: unlock_file(lease)

    def _run_items(self, identifier):
        for index in range(len(self.get(identifier)['items'])):
            with self._guard():
                batch = self._read(identifier)
                if batch['cancel_requested'] or self.stop.is_set(): break
                item = batch['items'][index]
                if item['status'] != 'queued': continue
                # Recheck current evidence immediately before each paid dispatch.
                request = dict(batch['request'], transition_ids=[item['transition_id']], graph_sha256=batch['graph_sha256'])
                current = self.preview(request)['candidates'][0]
                if not current['eligible']:
                    item.update(current, status='skipped', preview_status=current['status']); self._save(batch); continue
                payload = dict(purpose='prove', graph_id=batch['graph_ref']['id'], graph_revision=batch['graph_ref']['revision'],
                               transition_id=item['transition_id'], mode=batch['mode'], budget=batch['budget'])
                try:
                    run = self.service.create(payload, start=False)
                except (ValueError, FileNotFoundError) as error:
                    item.update(status='failed', reason=str(error), termination=dict(code='invalid_contract', stage='create', message=str(error)))
                    self._save(batch); continue
                item.update(status='running', run_id=run['id'], started_at=now())
                batch['status'] = 'running'; self._save(batch)
                # Binding is durable before launch. A crash cannot create a duplicate run on restart.
                self.service.start(run['id'])
            while True:
                run = self.service.get(run['id'])
                with self._guard():
                    batch = self._read(identifier); item = batch['items'][index]
                    item.update(run_status=run['status'], outcome=run.get('outcome', 'unknown'),
                                formal_outcome=run.get('formal_outcome', 'unknown'), termination=run.get('termination'),
                                usage=run.get('usage', {}))
                    if run['status'] not in RUN_ACTIVE:
                        item.update(status='complete' if run['status'] == 'complete' else 'cancelled' if run['status'] == 'cancelled' else 'failed',
                                    finished_at=now(), reason=run.get('error') or (run.get('result') or {}).get('reason') or '')
                    self._save(batch)
                if run['status'] not in RUN_ACTIVE: break
                if self.stop.wait(self.poll_seconds):
                    raise RuntimeError('Наблюдение пакета остановлено; автоматически запускать следующие связи нельзя.')
        with self._guard():
            batch = self._read(identifier)
            batch.update(status='cancelled' if batch['cancel_requested'] else 'interrupted' if self.stop.is_set() else 'complete', finished_at=now())
            self._save(batch)

    def close(self):
        self.stop.set()
        self.pool.shutdown(wait=True)
