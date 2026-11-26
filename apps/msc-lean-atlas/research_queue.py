"""Shared SQLite leases for mathematical research cards and a local worker CLI."""
from __future__ import annotations

import argparse
from dataclasses import dataclass
from datetime import datetime, timezone
import json
import os
import time
import uuid

LEASE_SECONDS = 30


class LeaseLost(Exception):
    """The worker may no longer change this card."""


@dataclass(frozen=True)
class Lease:
    program_id: str
    task_id: str
    token: str


class TaskQueue:
    def __init__(self, database, worker_id=None, ttl=LEASE_SECONDS):
        self.database = database
        self.worker_id = worker_id or f'local-{os.getpid()}-{uuid.uuid4().hex[:5]}'
        self.ttl = ttl

    @staticmethod
    def install(db):
        db.execute('''CREATE TABLE IF NOT EXISTS task_queue (
            program_id TEXT PRIMARY KEY, task_id TEXT NOT NULL, queued_at REAL NOT NULL,
            worker_id TEXT, token TEXT, expires_at REAL, generation INTEGER NOT NULL DEFAULT 0)''')

    @staticmethod
    def sync(db, state, task):
        # The queue and its source of truth are committed in the same transaction.
        if task is None or state['status'] != 'running':
            db.execute('DELETE FROM task_queue WHERE program_id=?', (state['id'],))
            return
        db.execute('''INSERT INTO task_queue (program_id, task_id, queued_at) VALUES (?, ?, ?)
            ON CONFLICT(program_id) DO UPDATE SET task_id=excluded.task_id, queued_at=excluded.queued_at,
                worker_id=NULL, token=NULL, expires_at=NULL, generation=0
            WHERE task_queue.task_id != excluded.task_id''', (state['id'], task['id'], time.time()))

    def claim(self, program_id=None, task_id=None):
        with self.database() as db:
            db.execute('BEGIN IMMEDIATE')
            now = time.time()
            row = db.execute('''SELECT q.program_id,q.task_id,q.worker_id,q.generation FROM task_queue AS q JOIN programs AS p ON p.id=q.program_id
                WHERE p.status='running' AND p.deadline>? AND (q.token IS NULL OR q.expires_at<=?)
                AND (? IS NULL OR q.program_id=?) AND (? IS NULL OR q.task_id=?)
                ORDER BY q.queued_at,q.program_id LIMIT 1''', (now, now, program_id, program_id, task_id, task_id)).fetchone()
            if row is None:
                return None
            lease = Lease(row['program_id'], row['task_id'], uuid.uuid4().hex)
            db.execute('''UPDATE task_queue SET worker_id=?,token=?,expires_at=?,generation=generation+1
                WHERE program_id=?''', (self.worker_id, lease.token, now+self.ttl, lease.program_id))
            at = datetime.now(timezone.utc).isoformat()
            event = dict(at=at, kind='lease_acquired', task_id=lease.task_id, worker_id=self.worker_id,
                         generation=row['generation']+1, message='Исполнитель взял карточку: '+self.worker_id+'.')
            if row['worker_id'] is not None:
                event.update(kind='lease_reassigned', previous_worker_id=row['worker_id'],
                             message='Истекла аренда. Карточку принял исполнитель '+self.worker_id+'.')
            db.execute('''UPDATE programs SET state=json_set(json_insert(state,'$.events[#]',json(?)),
                '$.updated_at',?) WHERE id=?''', (json.dumps(event, ensure_ascii=False), at, lease.program_id))
            return lease

    @staticmethod
    def require(db, lease):
        valid = db.execute('''SELECT 1 FROM task_queue WHERE program_id=? AND task_id=? AND token=? AND expires_at>?''',
                           (lease.program_id, lease.task_id, lease.token, time.time())).fetchone()
        if valid is None:
            raise LeaseLost()

    def renew(self, lease):
        with self.database() as db:
            db.execute('BEGIN IMMEDIATE')
            now = time.time()
            return bool(db.execute('''UPDATE task_queue SET expires_at=? WHERE program_id=? AND task_id=?
                AND token=? AND expires_at>?''', (now+self.ttl, lease.program_id, lease.task_id, lease.token, now)).rowcount)

    def release(self, lease):
        with self.database() as db:
            return bool(db.execute('''UPDATE task_queue SET worker_id=NULL, token=NULL, expires_at=NULL
                WHERE program_id=? AND task_id=? AND token=?''', (lease.program_id, lease.task_id, lease.token)).rowcount)

    def list(self, program_id=None):
        with self.database() as db:
            rows = db.execute('''SELECT q.*,p.state FROM task_queue AS q JOIN programs AS p ON p.id=q.program_id
                WHERE p.status='running' AND p.deadline>? AND (? IS NULL OR q.program_id=?)
                ORDER BY q.queued_at,q.program_id''', (time.time(), program_id, program_id)).fetchall()
        result = []
        for row in rows:
            state = json.loads(row['state'])
            task = next(t for t in state['tasks'] if t['id']==row['task_id'])
            busy = row['expires_at'] is not None and row['expires_at'] > time.time()
            result.append(dict(program_id=row['program_id'],program_title=state['title'],mode=state.get('mode','research'),
                               task_id=task['id'],question=task['question'],direction=task['direction'],
                               status='leased' if busy else 'ready', generation=row['generation'],
                               worker_id=row['worker_id'] if busy else None, expires_at=row['expires_at'] if busy else None))
        return result


def main():
    parser = argparse.ArgumentParser(description='Выполнять карточки из общей локальной очереди SHAIM.')
    parser.add_argument('--root', help='Каталог research_data, общий с сервером SHAIM.')
    parser.add_argument('--worker-id', help='Отображаемое имя исполнителя.')
    parser.add_argument('--once', action='store_true', help='Обработать одну доступную карточку и завершить работу.')
    args = parser.parse_args()
    from research_programs import ProgramService
    from research_service import ResearchService
    research = ResearchService(root=args.root)
    programs = ProgramService(research, recover=False, worker_id=args.worker_id)
    try:
        while True:
            worked = programs.work_next_card()
            if args.once:
                break
            if not worked:
                time.sleep(.25)
    except KeyboardInterrupt:
        pass
    finally:
        research.pool.shutdown()


if __name__ == '__main__':
    main()
