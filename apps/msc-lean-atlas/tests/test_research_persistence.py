"""Check the real SQLite workflow boundary without generating or compiling proofs."""
import json
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch

import sys
sys.path.insert(0,str(Path(__file__).resolve().parents[1]))
from research_service import ResearchService, StopRun, validate_plan


class PersistenceTests(unittest.TestCase):
    def test_completed_lean_stage_is_not_repeated_after_publish_interruption(self):
        with tempfile.TemporaryDirectory() as folder:
            service=ResearchService(folder)
            run=service.create({'case_id':'strict_inequality','mode':'pilot'},start=False)
            result={'status':'complete','outcome':'refuted','nodes':[],'edges':[]}
            with patch('research_lean.run_pilot',return_value=result) as lean:
                with patch.object(service,'_publish',side_effect=StopRun('interrupted','test interruption')):
                    service.start(run['id']);service.futures[run['id']].result()
                self.assertEqual(service.get(run['id'])['status'],'interrupted')
                self.assertTrue((Path(folder)/run['id']/'checkpoints.sqlite').exists())
                service.start(run['id']);service.futures[run['id']].result()
                self.assertEqual(service.get(run['id'])['status'],'complete')
                self.assertEqual(service.get(run['id'])['outcome'],'refuted')
                self.assertEqual(lean.call_count,1)
            service.pool.shutdown()

    def test_cycle_and_missing_dependency_are_rejected(self):
        for deps in (['b'],['missing']):
            with self.subTest(deps=deps):
                with self.assertRaises(ValueError):
                    validate_plan({'imports':['Mathlib'],'prelude':'','target_id':'a','nodes':[
                        {'id':'a','statement':'True','dependencies':deps},
                        {'id':'b','statement':'True','dependencies':['a']}]})

    def test_artifact_cannot_escape_run(self):
        with tempfile.TemporaryDirectory() as folder:
            service=ResearchService(folder)
            run=service.create({'case_id':'strict_inequality','mode':'pilot'},start=False)
            (Path(folder)/'outside.json').write_text('{}')
            with self.assertRaises(FileNotFoundError):service.artifact(run['id'],'../outside.json')
            self.assertEqual(service.artifact(run['id'],'contract-v1.json').name,'contract-v1.json')
            service.pool.shutdown()


if __name__=='__main__':unittest.main()
