"""A failed parallel node must not discard a completed independent proof."""
import json
from pathlib import Path
import sys
import tempfile
import threading
import time
import unittest
from unittest.mock import patch

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))
from research_service import ResearchService, WorkflowFailure


class PartialProofPersistenceTests(unittest.TestCase):
    def test_successful_sibling_is_saved_before_error_and_reused_on_resume(self):
        with tempfile.TemporaryDirectory() as folder:
            svc = ResearchService(folder, recover=False)
            try:
                run = svc.create(dict(mode='multi', case_id='graph_energy'), start=False)
                rid = run['id']; svc._started[rid] = time.monotonic()
                task = svc._effective_task(run)
                nodes = [dict(id=o['target'], title=o['title'], statement=o['statement'], dependencies=[], proof='')
                         for o in task['required_obligations']]
                self.assertEqual(len(nodes), 2)
                plan = dict(imports=task['imports'], prelude=task['prelude'], summary='Test scheduling', assumptions=[],
                            relation_kind='test', target_id=task['target'], nodes=nodes)
                attempted = []; failed = threading.Event()
                def prove(run_id, current_plan, node, established):
                    attempted.append(node['id'])
                    if node['id'] == nodes[0]['id'] and attempted.count(node['id']) == 1:
                        failed.set()
                        raise WorkflowFailure('infrastructure', 'prove', 'Controlled worker failure')
                    if node['id'] == nodes[1]['id']:
                        self.assertTrue(failed.wait(2))
                    return dict(statement=node['statement'], dependencies=[], declaration='unit-test placeholder',
                                verification={'success':True})
                def model(run_id, role, *args, **kwargs):
                    return {'text':json.dumps(plan if role == 'plan' else {'verdict':'accept','reason':'test','issues':[]})}
                with patch.object(svc, '_call', side_effect=model), patch.object(svc, '_prove_node', side_effect=prove), \
                     patch.object(svc, '_validate_established', side_effect=lambda plan, values: values), \
                     patch.object(svc, '_finish_model_workflow') as finish:
                    with self.assertRaises(WorkflowFailure):
                        svc._model_workflow(rid)
                    stored = json.loads((svc.folder(rid)/'proofs.json').read_text(encoding='utf8'))
                    self.assertIn(nodes[1]['id'], stored)
                    self.assertNotIn(nodes[0]['id'], stored)
                    svc._model_workflow(rid)
                self.assertEqual(attempted.count(nodes[1]['id']), 1)
                finish.assert_called_once()
            finally:
                svc.pool.shutdown(wait=True)


if __name__ == '__main__':
    unittest.main()
