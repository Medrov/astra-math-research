"""Version boundaries and certification rules for the mathematical registry."""
from concurrent.futures import ThreadPoolExecutor
import copy
import hashlib
import json
from pathlib import Path
import sys
import sqlite3
import tempfile
import unittest
import uuid

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))
from research_objects import (GraphRegistry, RevisionConflict, graph_fingerprints,
                              transition_contract, transition_fingerprint, validate_graph)


def sample_graph():
    return {
        'title': 'Energy representation', 'question': 'Show equality of two energy definitions.', 'msc_codes': ['05C50'],
        'objects': [dict(id=name, title=name, kind='function', definition='def ' + name + ' : Nat := 0',
                         parameters=[], assumptions=[], msc_codes=['05C50'], lean_refs=[name]) for name in ('energy', 'quadratic')],
        'transitions': [dict(id='representation', title='Energy equality', source_ids=['energy'], target_ids=['quadratic'],
            relation_type='representation', construction='The identity representation', assumptions=[], claim='The energies agree.',
            obligations=[dict(id='equality', title='Equality theorem', target='Bridge.equal', statement='True', expected_outcome='proved'),
                         dict(id='preservation', title='Preserved invariant', target='Bridge.preserve', statement='True', expected_outcome='proved')],
            agent_task=dict(imports=['Init'], prelude='', target='Bridge.equal', statement='True'), case_id=None)],
        'sources': [dict(id='source-1', title='A source', url='https://example.org/paper', locator='Theorem 1')],
    }


def checked_result(graph=None, *, environment='env-a', semantic='aligned'):
    transition = (graph or sample_graph())['transitions'][0]
    task = transition['agent_task']
    final = next(item for item in transition['obligations'] if item['target'] == task['target'])
    return dict(formal_outcome=final['expected_outcome'], environment_fingerprint=environment,
        semantic_review={'status': semantic}, verification=dict(success=True, compilation_success=True,
            target_preserved=True, target=task['target'], expected_statement=task['statement'],
            audit=dict(status='passed', unexpected_axioms=[], unsafe_declarations=[]), axioms=[], obligations_passed=True,
            obligations=[dict(id=item['id'], target=item['target'],
                              statement_sha256=hashlib.sha256(item['statement'].encode('utf-8')).hexdigest(), ok=True)
                         for item in transition['obligations']]))


def literature_graph():
    graph = sample_graph()
    graph['transitions'][0].update(formulation_status='literature_only', agent_task=None,
                                    obligations=[], source_refs=['source-1'])
    graph['sources'][0].update(versioned_id='2610.38474v1', snapshot_sha256='a' * 64, section_id='S9.SS3')
    return graph


class SchemaTests(unittest.TestCase):
    def test_literature_extension_preserves_preexisting_fixture_hashes_and_payloads(self):
        import research_lean
        from research_object_examples import graph_for_case
        baselines = {
            'seminar_gradient': ('db18f44ffaa1bb5f83174449f2a0caecc632043177354cb4ac9bdf2ce8bf0d29', '16ba2b61792fc5a41800e990b3109039239efba761d73c9c547366a19a090512'),
            'strict_inequality': ('37664f56546fbf69757a0eedaf57142703c2620659428a3e7e64f9c6a1a18a27', 'b9bebd5daf847124623e664064515648f693f40d57f8481e759ce8237c505c2b'),
            'graph_energy': ('5312a5f5e9ed03972089d66a7ddff6ee3e950ca429636367895a65f695f34319', '247fa7b0bc2422e3b063319d99d28b9b398542983fa139dc49217cd6538c0ee2'),
            'graph_energy_negative': ('dd29e59819f28e2010aeb739f72f45a01343873816eab93feea65d8ef8aa44e2', '44e48b4479c5e8e74228c39a5ecfbb7be6722ecfcddda4bc3319c8928297cb9d'),
        }
        for case in research_lean.fixtures():
            if case['id'] not in baselines:
                continue
            with self.subTest(case=case['id']):
                graph = validate_graph(graph_for_case(case))
                self.assertEqual(graph_fingerprints(graph)['semantic_hash'], baselines[case['id']][0])
                payload = json.dumps(graph, sort_keys=True, ensure_ascii=False, separators=(',', ':'), allow_nan=False)
                self.assertEqual(hashlib.sha256(payload.encode('utf-8')).hexdigest(), baselines[case['id']][1])
                self.assertTrue(all('source_refs' not in t and 'formulation_status' not in t for t in graph['transitions']))

    def test_literature_card_has_no_formal_contract_and_sources_are_bound(self):
        graph = validate_graph(literature_graph())
        self.assertEqual(transition_contract(graph['transitions'][0]), {'task':None, 'obligations':[]})
        original = graph_fingerprints(graph)
        graph['sources'][0]['title'] = 'Display correction'
        self.assertEqual(original, graph_fingerprints(graph))
        for field, value in [('snapshot_sha256','b'*64), ('versioned_id','2610.38474v2'),
                             ('section_id','S10'), ('url','https://arxiv.org/html/2610.38474v1#S10')]:
            edited = copy.deepcopy(graph); edited['sources'][0][field] = value
            self.assertNotEqual(original, graph_fingerprints(edited))
        formal = sample_graph()
        formal['transitions'][0]['formulation_status'] = 'formalized'
        self.assertEqual(graph_fingerprints(formal), graph_fingerprints(sample_graph()))
        self.assertEqual(set(validate_graph(sample_graph())['sources'][0]), {'id','title','url','locator'})

    def test_literature_or_source_schema_cannot_smuggle_formal_status(self):
        mutations = [lambda g:g['transitions'][0].update(agent_task=sample_graph()['transitions'][0]['agent_task']),
                     lambda g:g['transitions'][0].update(obligations=sample_graph()['transitions'][0]['obligations']),
                     lambda g:g['transitions'][0].update(case_id='graph_energy'),
                     lambda g:g['transitions'][0].update(formulation_status='proved'),
                     lambda g:g['transitions'][0].update(source_refs=['missing']),
                     lambda g:g['transitions'][0].update(source_refs=['source-1','source-1']),
                     lambda g:g['sources'][0].update(versioned_id=None),
                     lambda g:g['sources'][0].update(section_id='x'*513)]
        for mutate in mutations:
            graph = literature_graph(); mutate(graph)
            with self.subTest(graph=graph), self.assertRaises(ValueError):
                validate_graph(graph)

    def test_prepared_case_contracts_preserve_exact_definition_sources(self):
        import research_lean
        from research_object_examples import graph_for_case
        for case in research_lean.fixtures():
            with self.subTest(case=case['id']):
                graph = validate_graph(graph_for_case(case))
                for transition in graph['transitions']:
                    self.assertEqual(transition['agent_task']['prelude'], case['agent_task']['prelude'])
                    self.assertEqual(transition['agent_task']['imports'], case['agent_task']['imports'])

    def test_object_cycles_are_valid_and_contract_contains_every_obligation(self):
        graph = sample_graph()
        reverse = copy.deepcopy(graph['transitions'][0])
        reverse.update(id='reverse', source_ids=['quadratic'], target_ids=['energy'])
        graph['transitions'].append(reverse)
        normalized = validate_graph(graph)
        self.assertEqual(len(normalized['transitions']), 2)
        contract = transition_contract(normalized['transitions'][0])
        self.assertEqual([item['id'] for item in contract['obligations']], ['equality', 'preservation'])

    def test_broken_references_empty_goals_duplicates_and_invalid_schemas_rejected(self):
        mutations = [
            lambda g: g['transitions'][0].update(source_ids=['missing']),
            lambda g: g['transitions'][0].update(target_ids=[]),
            lambda g: g['transitions'][0].update(obligations=[]),
            lambda g: g['transitions'].append(copy.deepcopy(g['transitions'][0])),
            lambda g: g['objects'].append(copy.deepcopy(g['objects'][0])),
            lambda g: g['transitions'][0]['obligations'].append(copy.deepcopy(g['transitions'][0]['obligations'][0])),
            lambda g: g['transitions'][0]['agent_task'].update(target='Different.goal'),
            lambda g: g['transitions'][0].update(relation_type='guess'),
            lambda g: g['objects'][0].update(parameters='x'),
            lambda g: g.update(msc_codes=['invalid']),
            lambda g: g.update(queston='misspelled'),
            lambda g: g['sources'][0].update(url='javascript:alert(1)'),
        ]
        for index, mutate in enumerate(mutations):
            with self.subTest(index=index):
                graph = sample_graph(); mutate(graph)
                with self.assertRaises(ValueError):
                    validate_graph(graph)

    def test_display_changes_do_not_change_semantics(self):
        graph = sample_graph(); original = graph_fingerprints(graph)
        graph.update(title='Renamed', msc_codes=['15A63'], layout={'energy': {'x': 3, 'y': 4}})
        graph['objects'][0].update(title='Different label', msc_codes=['15A63'])
        graph['transitions'][0]['title'] = 'Short label'
        graph['transitions'][0]['obligations'][0]['title'] = 'Short theorem label'
        graph['sources'][0]['title'] = 'Citation spelling'
        self.assertEqual(original, graph_fingerprints(graph))

    def test_semantic_changes_invalidate_related_transition_hash(self):
        original = transition_fingerprint(sample_graph(), 'representation')
        mutations = [lambda g: g['objects'][0].update(definition='def energy : Nat := 1'),
                     lambda g: g['objects'][0].update(assumptions=['positive weights']),
                     lambda g: g['transitions'][0].update(assumptions=['finite graph']),
                     lambda g: g['transitions'][0]['agent_task'].update(prelude='def auxiliary := 1'),
                     lambda g: g.update(question='A different mathematical question')]
        for mutate in mutations:
            graph = sample_graph(); mutate(graph)
            self.assertNotEqual(original, transition_fingerprint(graph, 'representation'))


class RegistryTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory(prefix='object-registry-')
        self.path = Path(self.temp.name) / 'objects.sqlite'
        self.registry = GraphRegistry(self.path)
        self.created = self.registry.create(sample_graph())
        self.gid = self.created['id']

    def tearDown(self):
        self.temp.cleanup()  # Also verifies that SQLite handles were closed on Windows.

    def publish(self, result=None, revision=1, run_id=None):
        return self.registry.record_result(self.gid, revision, 'representation', run_id or uuid.uuid4().hex,
                                           checked_result() if result is None else result)

    def test_literature_reports_fail_closed_and_formalization_has_separate_revision(self):
        created = self.registry.create(literature_graph())
        gid = created['id']; rid = uuid.uuid4().hex
        self.assertEqual(created['transitions'][0]['status'], 'proposed')
        attempted = self.registry.record_result(gid, 1, 'representation', rid, checked_result())
        transition = attempted['transitions'][0]
        self.assertEqual(transition['status'], 'unknown')
        self.assertIsNone(transition['certificate'])
        self.assertIn('literature-only', transition['last_result']['validation_errors'][0])
        formal = sample_graph()
        formal['transitions'][0]['formulation_status'] = 'formalized'
        second = self.registry.revise(gid, formal, expected_revision=1)
        self.assertEqual(second['revision'], 2)
        proved = self.registry.record_result(gid, 2, 'representation', uuid.uuid4().hex, checked_result())
        self.assertEqual(proved['transitions'][0]['status'], 'proved')
        self.assertEqual(self.registry.get(gid, 1)['transitions'][0]['status'], 'unknown')
        self.registry.record_result(gid, 1, 'representation', uuid.uuid4().hex, checked_result())
        self.assertEqual(self.registry.get(gid)['transitions'][0]['status'], 'proved')

    def test_persistence_and_generated_fields_cannot_forge_certificates(self):
        self.assertRegex(self.gid, r'^[a-f0-9]{32}$')
        self.assertEqual(self.created['transitions'][0]['status'], 'proposed')
        self.assertEqual(GraphRegistry(self.path).get(self.gid)['semantic_hash'], self.created['semantic_hash'])
        forged = self.registry.get(self.gid)
        forged['transitions'][0].update(status='proved', certificate={'forged': True})
        clean = self.registry.create(forged)
        self.assertEqual(clean['transitions'][0]['status'], 'proposed')
        self.assertEqual(len(self.registry.list_graphs()), 2)

    def test_create_idempotency_is_atomic_and_bound_to_input(self):
        def create(_):
            return GraphRegistry(self.path).create(sample_graph(), idempotency_key='run-proposal')
        with ThreadPoolExecutor(max_workers=2) as pool:
            graphs = list(pool.map(create, range(2)))
        self.assertEqual(graphs[0]['id'], graphs[1]['id'])
        self.registry.revise(graphs[0]['id'], sample_graph(), 1)
        self.assertEqual(create(None)['revision'], 1)
        changed = sample_graph(); changed['title'] = 'Different request'
        with self.assertRaisesRegex(ValueError, 'Idempotency'):
            self.registry.create(changed, idempotency_key='run-proposal')

    def test_revision_conflicts_and_historical_payloads(self):
        changed = self.registry.get(self.gid)
        changed['title'] = 'New title'
        second = self.registry.revise(self.gid, changed, 1)
        self.assertEqual(second['revision'], 2)
        self.assertEqual(self.registry.get(self.gid, 1)['title'], 'Energy representation')
        with self.assertRaises(RevisionConflict):
            self.registry.revise(self.gid, sample_graph(), 1)
        self.assertEqual(self.registry.get(self.gid)['revision'], 2)

    def test_certificate_requires_every_obligation_and_final_composition(self):
        mutations = [lambda r: r['verification'].update(success=False),
                     lambda r: r['verification'].update(compilation_success=False),
                     lambda r: r['verification'].update(target_preserved=False),
                     lambda r: r['verification'].update(obligations_passed=False),
                     lambda r: r['verification'].update(target='Wrong.goal'),
                     lambda r: r['verification'].update(expected_statement='False'),
                     lambda r: r['verification']['audit'].update(status='rejected'),
                     lambda r: r['verification'].update(axioms=['inventedAxiom']),
                     lambda r: r['verification']['obligations'].pop(),
                     lambda r: r['verification']['obligations'][0].update(ok=False),
                     lambda r: r['verification']['obligations'][0].update(target='Wrong.goal'),
                     lambda r: r['verification']['obligations'][0].update(statement_sha256='wrong'),
                     lambda r: r['verification']['obligations'][0].update(id='preservation'),
                     lambda r: r.update(environment_fingerprint=None),
                     lambda r: r.update(formal_outcome='refuted')]
        for index, mutate in enumerate(mutations):
            with self.subTest(index=index):
                result = checked_result(); mutate(result)
                transition = self.publish(result)['transitions'][0]
                self.assertEqual(transition['status'], 'unknown')
                self.assertIsNone(transition['certificate'])
                self.assertTrue(transition['last_result']['validation_errors'])
        self.assertEqual(len(transition['results']), len(mutations))
        self.assertEqual(self.publish()['transitions'][0]['status'], 'proved')

    def test_partial_results_and_semantic_review_are_separate_from_formal_status(self):
        partial = self.publish({'status': 'timeout', 'error': 'Budget expired'})['transitions'][0]
        self.assertEqual(partial['status'], 'unknown')
        self.assertEqual(partial['last_result']['result']['error'], 'Budget expired')
        checked = self.publish(checked_result(semantic='mismatch'))['transitions'][0]
        self.assertEqual(checked['status'], 'proved')
        self.assertEqual(checked['semantic_review']['status'], 'mismatch')

    def test_failed_later_attempt_does_not_remove_exact_certificate(self):
        first = self.publish()['transitions'][0]['certificate']
        later = self.publish({'status': 'failed', 'verification': {'success': False}})['transitions'][0]
        self.assertEqual(later['status'], 'proved')
        self.assertEqual(later['certificate']['run_id'], first['run_id'])
        self.assertEqual(later['last_result']['formal_outcome'], 'unknown')

    def test_result_replay_is_idempotent_and_run_payload_immutable(self):
        run = uuid.uuid4().hex
        first = self.publish(run_id=run)
        second = self.publish(run_id=run)
        self.assertEqual(first, second)
        self.assertEqual(len(second['transitions'][0]['results']), 1)
        with self.assertRaisesRegex(ValueError, 'immutable'):
            self.publish({'status': 'failed'}, run_id=run)

    def test_resumed_run_appends_a_new_publication_without_rewriting_history(self):
        run, interrupted_id, complete_id = uuid.uuid4().hex, uuid.uuid4().hex, uuid.uuid4().hex
        interrupted = {'publication_id': interrupted_id, 'status': 'cancelled'}
        first = self.publish(interrupted, run_id=run)
        self.assertEqual(first['transitions'][0]['status'], 'unknown')
        completed = checked_result(); completed['publication_id'] = complete_id
        second = self.publish(completed, run_id=run)
        transition = second['transitions'][0]
        self.assertEqual(transition['status'], 'proved')
        self.assertEqual(len(transition['results']), 2)
        self.assertEqual(transition['results'][0]['result'], interrupted)
        self.assertEqual(transition['certificate']['publication_id'], complete_id)
        self.assertEqual(self.publish(completed, run_id=run), second)
        with self.assertRaisesRegex(ValueError, 'immutable'):
            self.publish({'publication_id': complete_id, 'status': 'failed'}, run_id=run)
        revised = self.registry.revise(self.gid, sample_graph(), 1, environment_fingerprint='env-a')
        self.assertEqual(revised['transitions'][0]['certificate']['publication_id'], complete_id)

    def test_legacy_database_migration_keeps_results_and_carryover_bindings(self):
        certificate = self.publish()['transitions'][0]['certificate']
        self.registry.revise(self.gid, sample_graph(), 1, environment_fingerprint='env-a')
        # Reconstruct the original local schema with its already-saved evidence.
        with sqlite3.connect(self.path) as connection:
            connection.execute('ALTER TABLE graph_results RENAME TO saved_results')
            connection.execute('''CREATE TABLE graph_results AS
                SELECT graph_id,revision,transition_id,run_id,payload,payload_sha256,semantic_hash,verdict,errors,
                       environment_fingerprint,created_at FROM saved_results''')
            connection.execute('DROP TABLE saved_results')
            connection.execute('ALTER TABLE graph_carryovers DROP COLUMN source_publication_id')
        connection.close()
        restored = GraphRegistry(self.path).get(self.gid)
        self.assertEqual(restored['transitions'][0]['status'], 'proved')
        self.assertEqual(restored['transitions'][0]['certificate']['run_id'], certificate['run_id'])

    def test_late_old_revision_result_never_certifies_new_revision(self):
        self.registry.revise(self.gid, sample_graph(), 1, environment_fingerprint='env-a')
        old = self.publish(revision=1)
        self.assertEqual(old['transitions'][0]['status'], 'proved')
        current = self.registry.get(self.gid)
        self.assertEqual(current['revision'], 2)
        self.assertEqual(current['transitions'][0]['status'], 'proposed')
        self.assertFalse(current['transitions'][0]['results'])

    def test_cosmetic_revision_reuses_certificate_only_with_explicit_exact_environment(self):
        original = self.publish()
        graph = copy.deepcopy(original); graph['title'] = 'Another title'
        second = self.registry.revise(self.gid, graph, 1)
        self.assertEqual(second['semantic_hash'], original['semantic_hash'])
        self.assertEqual(second['transitions'][0]['status'], 'needs_recheck')
        third = self.registry.revise(self.gid, graph, 2, environment_fingerprint='env-a')
        self.assertEqual(third['transitions'][0]['status'], 'proved')
        self.assertEqual(third['transitions'][0]['certificate']['revision'], 1)
        fourth = self.registry.revise(self.gid, graph, 3, environment_fingerprint='env-b')
        self.assertEqual(fourth['transitions'][0]['status'], 'needs_recheck')

    def test_semantic_change_invalidates_even_with_same_environment(self):
        graph = self.publish()
        graph['objects'][0]['definition'] = 'def energy : Nat := 1'
        changed = self.registry.revise(self.gid, graph, 1, environment_fingerprint='env-a')
        self.assertEqual(changed['transitions'][0]['status'], 'needs_recheck')
        self.assertIsNone(changed['transitions'][0]['certificate'])
        self.assertEqual(self.registry.get(self.gid, 1)['transitions'][0]['status'], 'proved')

    def test_bound_environment_rejects_certificate_from_another_installation(self):
        self.registry = GraphRegistry(self.path, environment_fingerprint='env-a')
        self.created = self.registry.create(sample_graph()); self.gid = self.created['id']
        transition = self.publish(checked_result(environment='env-b'))['transitions'][0]
        self.assertEqual(transition['status'], 'needs_recheck')
        self.assertIsNone(transition['certificate'])

    def test_environment_change_requires_a_fresh_certificate_for_the_same_revision(self):
        self.registry = GraphRegistry(self.path, environment_fingerprint='env-a')
        self.created = self.registry.create(sample_graph()); self.gid = self.created['id']
        first = self.publish()['transitions'][0]['certificate']
        self.registry = GraphRegistry(self.path, environment_fingerprint='env-b')
        reopened = self.registry.get(self.gid)
        self.assertEqual(reopened['environment_fingerprint'], 'env-a')
        self.assertEqual(reopened['active_environment_fingerprint'], 'env-b')
        self.assertEqual(reopened['transitions'][0]['status'], 'needs_recheck')
        fresh = self.publish(checked_result(environment='env-b'))['transitions'][0]
        self.assertEqual(fresh['status'], 'proved')
        self.assertEqual(fresh['certificate']['environment_fingerprint'], 'env-b')
        self.assertEqual(fresh['results'][0]['run_id'], first['run_id'])

    def test_refuted_status_requires_the_pinned_negative_goal(self):
        graph = sample_graph()
        graph['transitions'][0]['obligations'][0]['expected_outcome'] = 'refuted'
        created = self.registry.create(graph)
        result = self.registry.record_result(created['id'], 1, 'representation', uuid.uuid4().hex, checked_result(graph))
        self.assertEqual(result['transitions'][0]['status'], 'refuted')

    def test_unknown_revision_transition_and_invalid_ids_rejected(self):
        with self.assertRaises(FileNotFoundError):
            self.registry.get(self.gid, 100)
        for revision in (None, True, 0):
            with self.subTest(revision=revision), self.assertRaises(ValueError):
                self.registry.record_result(self.gid, revision, 'representation', uuid.uuid4().hex, checked_result())
        with self.assertRaises(ValueError):
            self.registry.record_result(self.gid, 1, 'missing', uuid.uuid4().hex, checked_result())
        with self.assertRaises(ValueError):
            self.registry.record_result(self.gid, 1, 'representation', '../run', checked_result())


if __name__ == '__main__':
    unittest.main()
