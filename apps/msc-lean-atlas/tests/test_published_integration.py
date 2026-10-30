"""Publication boundaries with synthetic reports; no model or Lean execution."""
import copy
import hashlib
import os
from pathlib import Path
import re
import sys
import tempfile
import threading
import time
import unittest
from unittest.mock import patch
import uuid

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))
import research_lean
import research_project_library as library
import research_published_example as published
import research_service as rs
from research_object_examples import graph_for_case
from research_objects import validate_graph


def without_pin(source):
    return re.sub(r'(?m)^-- atlas-project-library-sha256: [0-9a-f]{64}\r?\n', '', source)


def synthetic_report(transition):
    """A registry test double, not evidence that a Lean proof was executed."""
    task = transition['agent_task']
    return dict(formal_outcome='proved', environment_fingerprint='synthetic-environment',
        semantic_review={'status': 'test_double'}, verification=dict(
            success=True, compilation_success=True, target_preserved=True,
            target=task['target'], expected_statement=task['statement'],
            audit=dict(status='passed', unexpected_axioms=[], unsafe_declarations=[]), axioms=[],
            obligations_passed=True,
            obligations=[dict(id=item['id'], target=item['target'], ok=True,
                              statement_sha256=hashlib.sha256(item['statement'].encode('utf-8')).hexdigest())
                         for item in transition['obligations']]))


class PublishedIntegrationTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        with patch.object(rs.ResearchService, '_environment_fingerprint', return_value='synthetic-environment'):
            self.service = rs.ResearchService(self.temp.name)
        self.addCleanup(self.service.pool.shutdown, wait=True)
        for target in ('research_codex.run_task', 'research_arxiv._fetch_html', 'research_lean._run'):
            guard = patch(target, side_effect=AssertionError('No external execution in boundary tests'))
            guard.start()
            self.addCleanup(guard.stop)

    def certify_synthetically(self, graph):
        stored = self.service.registry.create(graph)
        transition = stored['transitions'][0]
        self.service.registry.record_result(stored['id'], 1, transition['id'], uuid.uuid4().hex,
                                            synthetic_report(transition))
        return self.service.graph(stored['id'])

    def test_public_examples_are_exactly_two_and_historical_controls_remain_available(self):
        cases = self.service.public_cases()
        self.assertEqual([case['id'] for case in cases],
                         ['arxiv_2610_38474_graph_subtraction', published.CASE_ID])
        self.assertTrue(all(case['object_graph']['transitions'] for case in cases))
        self.assertTrue({'seminar_gradient', 'graph_energy_negative'} <=
                        {case['id'] for case in self.service.cases()})

    def test_project_import_allowlist_rejects_quoted_spellings_and_other_modules(self):
        research_lean._validate_source(published.source())
        for name in ('MathResearch.AlbertMatrix', 'MathResearch.Unknown',
                     'MathResearch.«AlbertSpectralGeometry»', '«MathResearch».AlbertSpectralGeometry'):
            with self.subTest(module=name), self.assertRaises(ValueError):
                research_lean._validate_source('import ' + name + '\ntheorem check : True := True.intro\n')

    def test_controller_binds_missing_pin_once_before_freeze_without_mutating_input(self):
        graph = published.graph_for_published_example()
        graph['transitions'][0]['agent_task']['prelude'] = without_pin(
            graph['transitions'][0]['agent_task']['prelude'])
        original = copy.deepcopy(graph)
        with patch.object(library, 'fingerprint', return_value='b' * 64):
            bound = self.service._validate_graph_contracts(graph)
            self.assertEqual(bound, self.service._validate_graph_contracts(bound))
        self.assertEqual(graph, original)
        self.assertEqual(library.pinned_fingerprint(bound['transitions'][0]['agent_task']['prelude']), 'b' * 64)

    def test_existing_pin_is_never_silently_upgraded(self):
        graph = published.graph_for_published_example()
        original = copy.deepcopy(graph)
        with patch.object(library, 'fingerprint', return_value='b' * 64), self.assertRaises(ValueError):
            self.service._validate_graph_contracts(graph)
        self.assertEqual(graph, original)

    def test_changed_project_sources_invalidate_only_the_dependent_certificate(self):
        local = self.certify_synthetically(published.graph_for_published_example())
        case = next(case for case in self.service.cases() if case['id'] == 'arxiv_2610_38474_graph_subtraction')
        article = self.certify_synthetically(graph_for_case(case))
        self.assertEqual(local['transitions'][0]['status'], 'proved')
        self.assertEqual(article['transitions'][0]['status'], 'proved')
        with patch.object(library, 'fingerprint', return_value='b' * 64):
            stale = self.service.graph(local['id'])
            unaffected = self.service.graph(article['id'])
        transition = stale['transitions'][0]
        self.assertEqual(transition['status'], 'needs_recheck')
        self.assertEqual(transition['formal_outcome'], 'unknown')
        self.assertIsNone(transition['certificate'])
        self.assertEqual(transition['previous_certificate'], local['transitions'][0]['certificate'])
        self.assertTrue(transition['dependency_error'])
        self.assertEqual(unaffected['transitions'][0]['certificate'], article['transitions'][0]['certificate'])
        # The display invalidation preserves the immutable historical publication.
        self.assertEqual(self.service.registry.get(local['id'])['transitions'][0]['status'], 'proved')
        # GET -> edit -> validation must ignore this controller-owned diagnostic.
        self.assertEqual(validate_graph(stale), validate_graph(local))

    def test_running_contract_checks_project_pin_without_invalidating_arxiv(self):
        runs = [self.service.create(dict(case_id=case, mode='pilot'), start=False)
                for case in (published.CASE_ID, 'arxiv_2610_38474_graph_subtraction')]
        for run in runs:
            self.service._started[run['id']] = time.monotonic()
            self.service.cancel_flags[run['id']] = threading.Event()
        with patch.object(library, 'fingerprint', return_value='b' * 64):
            with self.assertRaises(ValueError):
                self.service._check(runs[0]['id'])
            self.assertGreater(self.service._check(runs[1]['id']), 0)

    def fake_context(self, _unused, work):
        project = ROOT.parents[1]
        paths = [str(work), str(project), str(project / '.lake/build/lib/lean'),
                 str(Path(self.temp.name) / 'external-mathlib')]
        return dict(project_root=str(project), lean='not-executed', lean_search_paths=paths), {
            'LEAN_PATH': os.pathsep.join(paths)}

    def test_missing_or_stale_source_pin_fails_before_any_compiler_invocation(self):
        source = published.source()
        stale = without_pin(source) + '\n-- atlas-project-library-sha256: ' + 'b' * 64 + '\n'
        for candidate in (without_pin(source), stale):
            with self.subTest(pin=library.pinned_fingerprint(candidate)), \
                 patch.object(rs.lean_service, '_prepare', side_effect=self.fake_context), \
                 patch.object(research_lean, '_run') as compiler:
                result = research_lean.verify_candidate(candidate, published.TARGET, self.temp.name,
                    published.STATEMENT, required_obligations=published.obligations())
            self.assertEqual(result['status'], 'rejected')
            self.assertFalse(result['success'])
            self.assertFalse(result['obligations_passed'])
            compiler.assert_not_called()

    def test_fresh_builder_is_bound_to_source_pin_and_runs_before_candidate(self):
        order = []
        def build(context, env, work, runner, cancelled=None, *, expected_fingerprint=None):
            order.append('library')
            self.assertEqual(expected_fingerprint, library.pinned_fingerprint(published.source(), required=True))
            project = Path(context['project_root']).resolve()
            self.assertNotIn(project, {Path(p).resolve() for p in context['lean_search_paths']})
            self.assertNotIn(project / '.lake/build/lib/lean', {Path(p).resolve() for p in context['lean_search_paths']})
            return {'status': 'test_double', 'fingerprint': expected_fingerprint}
        def stop_at_candidate(context, env, work, filename, diagnostics, cancelled=None):
            order.append(filename)
            raise RuntimeError('Synthetic compiler stop')
        with patch.object(rs.lean_service, '_prepare', side_effect=self.fake_context), \
             patch.object(library, 'prepare_library', side_effect=build), \
             patch.object(research_lean, '_run', side_effect=stop_at_candidate):
            result = research_lean.verify_candidate(published.source(), published.TARGET, self.temp.name,
                                                    published.STATEMENT)
        self.assertEqual(order, ['library', 'Candidate.lean'])
        self.assertEqual(result['project_library']['fingerprint'], library.pinned_fingerprint(published.source()))
        self.assertFalse(result['success'])

    def test_plain_candidate_cannot_inherit_checkout_olean_cache(self):
        observed = []
        def inspect_paths(context, env, work, filename, diagnostics, cancelled=None):
            observed.append(list(context['lean_search_paths']))
            self.assertEqual(env['LEAN_PATH'].split(os.pathsep), context['lean_search_paths'])
            raise RuntimeError('Synthetic compiler stop')
        with patch.object(rs.lean_service, '_prepare', side_effect=self.fake_context), \
             patch.object(library, 'prepare_library') as builder, \
             patch.object(research_lean, '_run', side_effect=inspect_paths):
            result = research_lean.verify_candidate('import Init\ntheorem check : True := True.intro',
                                                     'check', self.temp.name, 'True')
        builder.assert_not_called()
        self.assertEqual(len(observed), 1)
        project = ROOT.parents[1]
        self.assertNotIn(str(project), observed[0])
        self.assertNotIn(str(project / '.lake/build/lib/lean'), observed[0])
        self.assertFalse(result['success'])


if __name__ == '__main__':
    unittest.main()
