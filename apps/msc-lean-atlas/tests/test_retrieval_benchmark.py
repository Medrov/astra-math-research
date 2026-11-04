"""Fixed offline evaluation integrity; never calls a model."""
import json
from pathlib import Path
import sys
import tempfile
import unittest
from unittest.mock import patch

ROOT=Path(__file__).resolve().parents[1]
sys.path[:0]=[str(ROOT),str(ROOT/'tools')]
import evaluate_retrieval as benchmark


class RetrievalBenchmarkTests(unittest.TestCase):
    def test_fixed_dataset_has_separate_families_and_negative_controls(self):
        data=json.loads((ROOT/'benchmarks/retrieval_v1.json').read_text(encoding='utf-8'))
        records={r['id'] for r in data['records']}
        development={key for c in data['cases'] if c['split']=='development' for key in c['relevance']}
        heldout={key for c in data['cases'] if c['split']=='held_out' for key in c['relevance']}
        self.assertTrue(development);self.assertTrue(heldout);self.assertFalse(development&heldout)
        self.assertTrue((development|heldout)<=records)
        self.assertTrue(any(c['split']=='negative' and not c['relevance'] for c in data['cases']))

    def test_offline_run_is_deterministic_and_does_not_claim_semantic_evaluation(self):
        with patch('research_codex.run_task',side_effect=AssertionError('offline evaluation cannot spend model calls')):
            first=benchmark.evaluate();second=benchmark.evaluate()
        self.assertEqual(first['summary'],second['summary'])
        self.assertEqual([c['pool_sha256'] for c in first['cases']],[c['pool_sha256'] for c in second['cases']])
        self.assertEqual(first['execution_usage']['model_calls'],0)
        self.assertEqual(first['semantic_reranking']['status'],'not_run')
        self.assertEqual(first['summary']['semantic_reranked']['held_out']['cases'],0)

    def test_captured_evaluation_cannot_use_wrong_fixture(self):
        with tempfile.TemporaryDirectory() as directory:
            path=Path(directory)/'captured.json';path.write_text(json.dumps(dict(fixture_sha256='0'*64,model='gpt-6-astra',usage={},assessments={})))
            with self.assertRaisesRegex(ValueError,'fixture hash'):benchmark.evaluate(rankings_path=path)


if __name__=='__main__':unittest.main()
