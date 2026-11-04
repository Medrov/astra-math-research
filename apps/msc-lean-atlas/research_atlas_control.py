"""Explicit, idempotent continuation with a new budget and immutable parent."""
from __future__ import annotations

import copy
import json
import re


class AtlasContinuationMixin:
    def continue_atlas(self, run_id, payload):
        from research_service import atomic, sha
        if not isinstance(payload, dict) or set(payload) - {'budget', 'idempotency_key', 'expected_snapshot_sha256', 'atlas_options', 'retry_failed'}:
            raise ValueError('Некорректные параметры продолжения поиска.')
        key = payload.get('idempotency_key')
        if not isinstance(key, str) or not re.fullmatch(r'[A-Za-z0-9_-]{8,128}', key):
            raise ValueError('Для продолжения нужен ключ повторной отправки.')
        expected = payload.get('expected_snapshot_sha256')
        if not isinstance(expected, str) or not re.fullmatch(r'[a-f0-9]{64}', expected):
            raise ValueError('Укажите точный снимок поиска, который нужно продолжить.')
        budget = payload.get('budget')
        if not isinstance(budget, dict) or set(budget) != {'max_calls', 'timeout_seconds'} or any(
                not isinstance(v, int) or isinstance(v, bool) for v in budget.values()):
            raise ValueError('Нужен явный новый бюджет вызовов и времени.')
        if not 1 <= budget['max_calls'] <= 24 or not 30 <= budget['timeout_seconds'] <= 1800:
            raise ValueError('Бюджет: 1–24 вызова и 30–1800 секунд.')
        retry_failed = payload.get('retry_failed', False)
        if type(retry_failed) is not bool:
            raise ValueError('Повтор ошибок должен быть выбран явно.')
        request = dict(parent_run_id=run_id, payload=copy.deepcopy(payload))
        receipt_path = self.root / 'atlas-continuations' / (sha([run_id, key]) + '.json')
        with self._guard(run_id):
            child_id = sha(['atlas-continuation', run_id, key])[:32]
            if receipt_path.exists():
                saved = json.loads(receipt_path.read_text(encoding='utf-8'))
                if saved.get('request_sha256') != sha(request):
                    raise ValueError('Ключ повторной отправки уже использован с другими параметрами.')
                if saved.get('child_run_id') != child_id:
                    raise ValueError('ID сохранённого продолжения изменён.')
                if (self.root / child_id / 'run.json').exists():
                    # The durable intent is written before creation. A retry after
                    # a crash completes this same draft instead of creating a twin.
                    child = self.get(child_id)
                    if saved.get('contract_sha256') and saved['contract_sha256'] != child['contract_sha256']:
                        raise ValueError('Контракт сохранённого продолжения изменён.')
                    return self._finish_atlas_continuation(receipt_path, saved, child)
            parent = self.get(run_id)
            seed = self.atlas_continuation_seed(run_id, expected, retry_failed=retry_failed)
            contract = parent['contract']
            values = dict(purpose='structure', mode=parent['mode'], proof_backend=parent.get('proof_backend', 'native'),
                          search_scope='atlas', atlas_seed=seed,
                          atlas_options=payload.get('atlas_options') or parent['atlas_options'],
                          budget=budget, question=parent['claim'], title=parent['title'])
            if contract.get('source_transition'):
                ref = contract['source_graph_ref']
                values.update(graph_id=ref['id'], graph_revision=ref['revision'], transition_id=contract['source_transition_id'])
            elif contract.get('source_library'):
                source = contract['source_library']
                values.update(source_id=source['source_id'], target=source['selected_declaration']['name'])
            else:
                raise ValueError('В поиске отсутствует зафиксированный математический вход.')
            intent = dict(request_sha256=sha(request), child_run_id=child_id, status='creating')
            atomic(receipt_path, intent)
            child = self.create(values, start=False, _run_id=child_id)
            return self._finish_atlas_continuation(receipt_path, intent, child)

    def _finish_atlas_continuation(self, path, receipt, child):
        from research_service import atomic
        if child['status'] == 'queued' and child['usage']['calls'] == 0:
            self.update(child['id'], status='draft', phase='draft', ready_to_start=True)
            self.event(child['id'], 'draft', 'Продолжение поиска сохранено. Новый бюджет расходуется только после отдельного запуска.')
        if receipt.get('status') != 'ready':
            atomic(path, dict(receipt, status='ready', contract_sha256=child['contract_sha256']))
        return self.detail(child['id'])
