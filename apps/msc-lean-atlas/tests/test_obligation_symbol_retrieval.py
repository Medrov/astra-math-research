"""Compiler names must survive a goal longer than the lexical token budget."""
from pathlib import Path
import sys
import sqlite3
import tempfile
import unittest
from unittest.mock import patch

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))
import research_retrieval as retrieval


class ObligationSymbolRetrieval(unittest.TestCase):
    def test_unknown_symbol_is_searched_separately_ahead_of_long_goal(self):
        with tempfile.TemporaryDirectory() as directory:
            folder = Path(directory)
            source = folder / 'Mathlib'
            source.mkdir()
            (source / 'Example.lean').write_text('theorem add_pow (n : Nat) : n = n := by rfl\n')
            index = folder / 'index.sqlite'
            retrieval.build_index(index, [dict(path=str(source), repository=str(folder), module_prefix='Mathlib')])
            goal = ' '.join('longGoalToken' + str(i) for i in range(60))
            diagnostic = dict(diagnostics=[dict(stdout="Candidate.lean:4:5: error: unknown identifier 'add_pow'")])
            original = retrieval.search_library
            with patch.object(retrieval, 'search_library', side_effect=lambda q, limit: original(q, limit, index)) as names, \
                 patch.object(retrieval, 'search', return_value=[dict(id='generic-goal-hint')]):
                queries, rows = retrieval.search_obligation(goal, diagnostic, [])
            names.assert_called_once_with('add_pow', limit=6)
            self.assertEqual(rows[0]['name'], 'add_pow')
            self.assertEqual(rows[0]['obligation_query']['kind'], 'compiler_symbol')
            self.assertEqual(queries[0]['text'], 'add_pow')
            self.assertEqual(queries[-1]['text'], goal)

    def test_duplicate_hits_are_once_and_non_identifier_payload_is_ignored(self):
        report = dict(diagnostics=[dict(stdout="unknown identifier 'Nat.foo'\nunknown identifier 'k'\n"
            "unknown identifier 'foo;bad'\nunknown constant 'Nat.foo'")])
        with patch.object(retrieval, 'search_library', return_value=[dict(id='same', name='Nat.foo')]) as names, \
             patch.object(retrieval, 'search', return_value=[dict(id='same'), dict(id='goal')]):
            queries, rows = retrieval.search_obligation('goal type', report, [], limit=2)
        names.assert_called_once_with('Nat.foo', limit=2)
        self.assertEqual([row['id'] for row in rows], ['same', 'goal'])
        self.assertEqual(len(queries), 2)

    def test_broken_symbol_index_keeps_goal_and_curated_fallback(self):
        report = dict(diagnostics=[dict(stdout="unknown identifier 'add_pow'")])
        with patch.object(retrieval, 'search_library', side_effect=sqlite3.OperationalError('no such table')), \
             patch.object(retrieval, 'search', return_value=[dict(id='curated-goal')]) as goal:
            queries, rows = retrieval.search_obligation('original goal', report, [])
        goal.assert_called_once_with('original goal', [], limit=6)
        self.assertEqual([row['id'] for row in rows], ['curated-goal'])
        self.assertEqual(queries[0]['status'], 'unavailable')
        self.assertIn('no such table', queries[0]['error'])


if __name__ == '__main__':
    unittest.main()
