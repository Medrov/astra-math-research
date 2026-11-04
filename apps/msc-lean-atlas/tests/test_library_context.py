"""Prefreeze library context: compiler/model doubles, no paid calls or Lean runs."""
import copy
import hashlib
import json
import sqlite3
from pathlib import Path
import sys
import tempfile
import threading
import time
import unittest
from unittest.mock import Mock, patch

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
import research_library_context as library
import research_service as rs
import research_goedel
from test_transition_structure import literary_graph


BASE = 'Mathlib.Test.Base'
EXTRA = 'Mathlib.Test.Extra'
SIGNATURE = '∀ (n : Nat), n + 0 = n'


def draft():
    statement = '∀ (n : Nat), n = n'
    return dict(status='ready', reason='Test-only typed draft', limitations=[],
        agent_task=dict(imports=[BASE], prelude='', target='identity', statement=statement),
        obligations=[dict(id='identity_goal', title='Identity', target='identity', statement=statement,
                          expected_outcome='proved')])


def requests():
    return dict(requests=[dict(query='natural addition zero', preferred_names=['Nat.add_zero'],
        obligation_ids=['identity_goal'], intended_use='A relevant arithmetic identity, still requires a new proof.')])


class LibraryContextTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.root = Path(self.temp.name)
        with patch.object(rs.ResearchService, '_environment_fingerprint', return_value='context-test-environment'):
            self.svc = rs.ResearchService(self.root / 'runs', recover=False)
        graph = self.svc.registry.create(literary_graph())
        self.svc.arxiv = Mock()
        self.svc.arxiv.get_paper.return_value = dict(versioned_id='2601.00001v1', title='Pinned article',
            snapshot_sha256={'article_html': 'c'*64}, source_urls={'html': 'https://arxiv.org/html/2601.00001v1'},
            sections=[dict(id='S2')])
        self.run = self.svc.create(dict(mode='multi', purpose='prove', graph_id=graph['id'], graph_revision=1,
            transition_id='coordinate_change', budget=dict(max_calls=8, timeout_seconds=600)), start=False)
        self.rid = self.run['id']
        self.arm(self.rid)
        self.context = dict(mathlib=str(self.root / 'mathlib'),
            lean_search_paths=[str(self.root / 'mathlib/.lake/build/lib/lean')],
            lean_version='Lean test fixture', mathlib_revision='fixture', mathlib_manifest_sha256='f'*64)
        self.hit = self.module(EXTRA, 'Nat.add_zero')
        self.baseline = dict(well_typed=True, proof_checked=False, status='complete', context=self.context,
                             audit=dict(status='passed'))
        self.manifest = dict(status='ready', index_version=3, source_sha256='1'*64)
        self.model_values = [requests()]
        self.model_prompts = []
        self.patches = [patch('research_retrieval.library_manifest', side_effect=lambda: copy.deepcopy(self.manifest)),
            patch('research_retrieval.search_library', side_effect=lambda *a, **k: [copy.deepcopy(self.hit)]),
            patch('research_retrieval.resolve_library_types', side_effect=self.resolve),
            patch('research_codex.run_task', side_effect=self.model),
            patch('research_retrieval.lookup_library_name', side_effect=lambda name, **k:
                  [copy.deepcopy(self.hit)] if name == self.hit['name'] else []),
            patch.object(self.svc, '_preflight_contract', side_effect=lambda *a, **k: copy.deepcopy(self.baseline))]
        self.mocks = [p.start() for p in self.patches]

    def tearDown(self):
        for p in reversed(self.patches):
            p.stop()
        self.svc.pool.shutdown(wait=True)
        self.temp.cleanup()

    def arm(self, rid):
        self.svc._started[rid] = time.monotonic()
        self.svc.cancel_flags[rid] = threading.Event()

    def module(self, name, declaration):
        root = self.root / 'mathlib'
        source = root.joinpath(*name.split('.')).with_suffix('.lean')
        compiled = root.joinpath('.lake/build/lib/lean', *name.split('.')).with_suffix('.olean')
        source.parent.mkdir(parents=True, exist_ok=True)
        compiled.parent.mkdir(parents=True, exist_ok=True)
        source.write_text('-- Test-only source: ' + declaration, encoding='utf-8')
        compiled.write_bytes(b'test-double-not-a-real-olean')
        return dict(id=name + ':' + declaration, name=declaration, module=name, kind='theorem',
                    file=str(source), source_sha256=hashlib.sha256(source.read_bytes()).hexdigest(),
                    evidence_type='library_declaration', statement='textual header')

    def model(self, prompt, folder, **kwargs):
        self.model_prompts.append(prompt)
        self.assertTrue(self.model_values, 'Unexpected additional model invocation')
        return dict(status='completed', text=json.dumps(self.model_values.pop(0)), usage=dict(total_tokens=17))

    def resolve(self, hits, folder, **kwargs):
        folder = Path(folder); folder.mkdir(parents=True, exist_ok=True)
        values = [dict(h, type_status='compiler_resolved', elaborated_type=SIGNATURE, axioms=['propext'],
            resolved_imports=[h['module']], type_dependencies=['Nat'],
            type_environment={k: self.context[k] for k in ('lean_version', 'mathlib_revision', 'mathlib_manifest_sha256')},
            verification_scope='existing_library_type_only', requires_new_proof=True) for h in hits]
        rs.atomic(folder / 'type-resolution.json', dict(hits=values, status='complete', model_calls=0))
        return values

    def prepare(self):
        return library.prepare(self.svc, self.rid, draft(), self.baseline)

    def receipt(self):
        run = self.svc.get(self.rid)
        return library._read_receipt(self.svc, run, required=True)

    def formalize(self):
        self.model_values = [draft(), requests()]
        self.svc._formalize_transition(dict(run_id=self.rid))
        return self.svc.get(self.rid)

    def test_new_literature_policy_is_explicit_and_legacy_no_policy_is_noop(self):
        self.assertEqual(self.run['contract']['library_context_policy'], library.POLICY)
        contract = copy.deepcopy(self.run['contract']); contract.pop('library_context_policy')
        self.svc.update(self.rid, contract=contract, contract_sha256=rs.sha(contract))
        self.assertEqual(self.prepare(), draft())
        self.assertEqual(self.svc.get(self.rid)['usage']['calls'], 0)
        self.assertFalse((self.svc.folder(self.rid) / 'library-context').exists())

    def test_resolved_import_is_additive_and_all_math_and_provenance_are_retained(self):
        before = draft()
        out = self.prepare()
        self.assertEqual(out['agent_task']['imports'], [BASE, EXTRA])
        self.assertEqual(library._math(out), library._math(before))
        saved = self.receipt()
        self.assertEqual(saved['selected'][0]['elaborated_type'], SIGNATURE)
        self.assertEqual(saved['selected'][0]['obligation_ids'], ['identity_goal'])
        self.assertEqual(saved['imports_added'], [EXTRA])
        self.assertFalse(saved['proof_checked'])
        self.assertEqual(saved['input_draft_sha256'], rs.sha(before))
        self.assertEqual(self.svc.get(self.rid)['usage']['calls'], 1)
        preflight = self.mocks[-1]
        self.assertEqual(preflight.call_args.args[1]['imports'], [BASE, EXTRA])
        folder = self.svc.folder(self.rid) / 'library-context' / saved['input_sha256']
        raw = json.loads((folder / 'retrieval.json').read_text())
        self.assertEqual([r['channel'] for r in raw['searches']], ['exact_name', 'phrase'])
        self.assertEqual(raw['searches'][0]['query'], 'Nat.add_zero')
        self.assertEqual(self.svc.get(self.rid)['outcome'], 'unknown')

    def test_prefreeze_hook_and_first_prompts_of_both_backends_contain_exact_types(self):
        run = self.formalize()
        self.assertEqual(self.svc._effective_task(run)['imports'], [BASE, EXTRA])
        self.assertEqual(run['object_contract']['library_context'], run['library_context'])
        self.assertIn(SIGNATURE, self.svc._plan_prompt(run))
        task = self.svc._effective_task(run)
        node = dict(id=task['target'], title='Identity', statement=task['statement'], proof='', dependencies=[])
        plan = dict(imports=task['imports'], prelude=task['prelude'], target_id=node['id'], nodes=[node], order=[node['id']], revision=0)
        for backend in ('native', 'goedel'):
            with self.subTest(backend=backend), patch.object(self.svc, '_call', return_value={
                    'text': json.dumps(dict(proof='by\n  intro n\n  rfl', explanation='Mock proof'))}) as call, \
                    patch('research_lean.verify_candidate', return_value=dict(success=True, declarations=[
                        dict(name=node['id'], kind='theorem', unsafe=False, axioms=[], dependency_walk_truncated=False)])):
                result = (self.svc._prove_node(self.rid, plan, node, {}) if backend == 'native' else
                          research_goedel._prove_node(self.svc, self.rid, plan, node, {}))
                self.assertIsNotNone(result)
                self.assertIn(SIGNATURE, call.call_args.args[2])
                self.assertIn('existing library declarations, not proofs', call.call_args.args[2])
                self.assertEqual(call.call_count, 1)
        frozen = self.svc._formal_contract(self.rid)
        self.assertEqual(frozen['library_context'], run['library_context'])

    def pin_preserved(self, value):
        contract = copy.deepcopy(self.svc.get(self.rid)['contract'])
        contract.update(preserve_formalization=True, revision_draft_sha256=rs.sha(value))
        self.svc.update(self.rid, contract=contract, contract_sha256=rs.sha(contract), revision_draft=value)

    def test_preserved_revision_context_cannot_add_imports(self):
        before = draft()
        self.pin_preserved(before)
        out = library.prepare(self.svc, self.rid, before, self.baseline)
        self.assertEqual(out, before)
        self.assertEqual(self.receipt()['imports_added'], [])
        self.assertTrue(any(x['reason'] == 'preserved_import_context' for x in self.receipt()['issues']))
        self.assertFalse(self.receipt()['proof_checked'])

    def test_preserved_revision_can_inspect_existing_import_without_changing_task(self):
        before = draft()
        before['agent_task']['imports'].append(EXTRA)
        self.pin_preserved(before)
        out = library.prepare(self.svc, self.rid, before, self.baseline)
        self.assertEqual(out, before)
        self.assertEqual([x['name'] for x in self.receipt()['selected']], ['Nat.add_zero'])
        self.assertEqual(self.receipt()['imports_added'], [])

    def test_preserved_revision_rejects_drift_before_model_or_compiler(self):
        before = draft()
        self.pin_preserved(before)
        changed = copy.deepcopy(before)
        changed['agent_task']['imports'].append(EXTRA)
        with self.assertRaisesRegex(ValueError, 'Сохранённая постановка'):
            library.prepare(self.svc, self.rid, changed, self.baseline)
        self.assertEqual(self.model_prompts, [])

    def test_seed_revision_gets_context_without_changing_seed_or_parent(self):
        self.formalize()
        self.svc.update(self.rid, status='complete', phase='complete')
        parent = self.svc.folder(self.rid)
        hashes = {p.relative_to(parent).as_posix(): p.read_bytes() for p in parent.rglob('*') if p.is_file()}
        child = self.svc.revise_run(self.rid, dict(reason='Find useful library lemmas; preserve all formulas.'))
        self.arm(child['id'])
        seed = copy.deepcopy(child['revision_draft'])
        self.model_values = [requests()]
        self.svc._formalize_transition(dict(run_id=child['id']))
        after = self.svc.get(child['id'])
        self.assertEqual(after['revision_draft'], seed)
        self.assertEqual(rs.sha(seed), after['contract']['revision_draft_sha256'])
        self.assertEqual(after['usage']['calls'], 1)
        self.assertIn(child['source_lineage']['reason'], self.model_prompts[-1])
        self.assertIn(SIGNATURE, self.svc._plan_prompt(after))
        for relative, data in hashes.items():
            self.assertEqual((parent / relative).read_bytes(), data, relative)

    def test_completed_context_is_reused_after_restart_without_new_model_or_compiler(self):
        expected = self.prepare()
        with patch.object(rs.ResearchService, '_environment_fingerprint', return_value=self.svc.environment_fingerprint):
            resumed = rs.ResearchService(self.svc.root, recover=False)
        try:
            resumed._started[self.rid] = time.monotonic()
            resumed.cancel_flags[self.rid] = threading.Event()
            with patch('research_retrieval.resolve_library_types', side_effect=AssertionError('No repeat export')), \
                    patch.object(resumed, '_call', side_effect=AssertionError('No repeat model')):
                self.assertEqual(library.prepare(resumed, self.rid, draft(), self.baseline), expected)
            self.assertEqual(resumed.get(self.rid)['usage']['calls'], 1)
        finally:
            resumed.pool.shutdown(wait=True)

    def test_interrupted_local_stage_reuses_accounted_model_result(self):
        with patch('research_retrieval.resolve_library_types', side_effect=rs.StopRun('cancelled', 'test cancellation')):
            with self.assertRaises(rs.StopRun):
                self.prepare()
        self.assertEqual(self.svc.get(self.rid)['usage']['calls'], 1)
        self.assertEqual(self.prepare()['agent_task']['imports'], [BASE, EXTRA])
        self.assertEqual(len(self.model_prompts), 1)
        self.assertEqual(self.svc.get(self.rid)['usage']['calls'], 1)

    def test_saved_receipt_and_export_artifacts_cannot_be_modified(self):
        self.prepare()
        run = self.svc.get(self.rid)
        folder = self.svc.folder(self.rid) / 'library-context' / run['library_context']['input_sha256']
        target = folder / 'types/type-resolution.json'
        target.write_text('{}', encoding='utf-8')
        with self.assertRaisesRegex(ValueError, 'Артефакт'):
            library.check_integrity(self.svc, run)

    def test_receipt_type_tampering_is_rejected_before_prompt(self):
        self.prepare()
        run = self.svc.get(self.rid)
        path = self.svc.folder(self.rid) / 'library-context' / run['library_context']['input_sha256'] / 'context.json'
        value = json.loads(path.read_text()); value['selected'][0]['elaborated_type'] = 'False'
        rs.atomic(path, value)
        with self.assertRaisesRegex(ValueError, 'контекст изменён'):
            library.prompt_context(self.svc, run)

    def test_missing_source_cache_stale_external_paths_and_untrusted_type_are_not_imported(self):
        cases = ['source', 'cache', 'stale', 'external', 'traversal', 'axioms', 'unsafe', 'environment', 'unresolved']
        for kind in cases:
            with self.subTest(kind=kind):
                hit = copy.deepcopy(self.hit)
                context = copy.deepcopy(self.context)
                if kind == 'source':
                    hit['module'] = 'Mathlib.Missing.Source'
                elif kind == 'cache':
                    hit = self.module('Mathlib.Missing.Cache', 'Nat.add_zero')
                    Path(context['mathlib']).joinpath('.lake/build/lib/lean/Mathlib/Missing/Cache.olean').unlink()
                elif kind == 'stale':
                    hit['source_sha256'] = '0'*64
                elif kind == 'external':
                    outside = self.root / 'external.lean'; outside.write_text('-- external')
                    hit['file'] = str(outside)
                elif kind == 'traversal':
                    hit['module'] = 'Mathlib../Test/Extra'
                if kind in {'source', 'cache', 'stale', 'external', 'traversal'}:
                    with self.assertRaises(ValueError):
                        library._module_evidence(hit, context)
                else:
                    original_resolve = self.resolve
                    def bad_resolve(hits, folder, **kwargs):
                        values = original_resolve(hits, folder, **kwargs)
                        for v in values:
                            if kind == 'axioms': v['axioms'] = ['newAxiom']
                            elif kind == 'unsafe': v['unsafe'] = True
                            elif kind == 'environment': v['type_environment'] = {}
                            else: v['type_status'] = 'not_resolved'
                        return values
                    # Each subcase has a new immutable input/run, not overwritten history.
                    graph = self.svc.registry.create(literary_graph())
                    run = self.svc.create(dict(mode='multi', graph_id=graph['id'], graph_revision=1,
                        transition_id='coordinate_change'), start=False)
                    self.arm(run['id']); self.model_values = [requests()]
                    with patch('research_retrieval.resolve_library_types', side_effect=bad_resolve):
                        out = library.prepare(self.svc, run['id'], draft(), self.baseline)
                    self.assertEqual(out, draft())

    def test_conflicting_added_imports_are_rejected_with_original_typed_context(self):
        self.mocks[-1].side_effect = lambda *a, **k: dict(well_typed=False, status='rejected', error='Conflict')
        self.assertEqual(self.prepare(), draft())
        receipt = self.receipt()
        self.assertEqual(receipt['selected'], [])
        self.assertEqual(receipt['imports_added'], [])
        self.assertIn('expanded_preflight_rejected', [i['reason'] for i in receipt['issues']])
        self.assertTrue(self.svc.get(self.rid)['contract_verification']['well_typed'])

    def test_cancellation_and_call_budget_are_not_optional_fallbacks(self):
        self.svc.cancel_flags[self.rid].set()
        with self.assertRaises(rs.StopRun) as stopped:
            self.prepare()
        self.assertEqual(stopped.exception.status, 'cancelled')
        self.svc.cancel_flags[self.rid].clear()
        usage = self.svc.get(self.rid)['usage']; usage['calls'] = self.run['budget']['max_calls']
        self.svc.update(self.rid, usage=usage)
        with self.assertRaises(rs.StopRun) as stopped:
            self.prepare()
        self.assertEqual(stopped.exception.status, 'budget_exhausted')
        self.assertEqual(self.model_prompts, [])

    def test_empty_requests_is_recorded_noop_with_one_bounded_model_call(self):
        self.model_values = [dict(requests=[])]
        self.assertEqual(self.prepare(), draft())
        self.assertEqual(self.receipt()['status'], 'no_additions')
        self.mocks[1].assert_not_called()
        self.mocks[2].assert_not_called()

    def test_requests_cannot_change_math_or_refer_to_nonexistent_obligation(self):
        variants = [dict(requests(), imports=['Mathlib']), {'requests': [dict(requests()['requests'][0], obligation_ids=['wrong'])]},
                    {'requests': [dict(requests()['requests'][0], preferred_names=['by exact False.elim'])]},
                    {'requests': [dict(requests()['requests'][0], query='x ' * 17)]}]
        for value in variants:
            with self.subTest(value=value), self.assertRaises(ValueError):
                library.validate_requests(value, draft()['obligations'])

    def test_rebuilt_optional_index_does_not_invalidate_compiler_pinned_context(self):
        expected = self.prepare()
        self.manifest['source_sha256'] = '2'*64
        self.assertEqual(self.prepare(), expected)
        self.assertEqual(len(self.model_prompts), 1)

    def test_changed_input_requires_new_version_not_a_second_call(self):
        self.prepare()
        changed = draft(); changed['agent_task']['statement'] = '∀ (n : Nat), n + 0 = n'
        with self.assertRaisesRegex(ValueError, 'Вход сохранённого'):
            library.prepare(self.svc, self.rid, changed, self.baseline)
        self.assertEqual(len(self.model_prompts), 1)

    def test_corrupt_optional_index_retains_typed_draft_with_explicit_diagnostic(self):
        self.mocks[1].side_effect = sqlite3.OperationalError('database is malformed')
        self.mocks[4].side_effect = sqlite3.OperationalError('database is malformed')
        self.assertEqual(self.prepare(), draft())
        self.assertIn('library_index_unavailable', [i['reason'] for i in self.receipt()['issues']])
        self.assertEqual(self.svc.get(self.rid)['usage']['calls'], 1)

    def test_exact_names_use_dedicated_lookup_and_request_order_before_module_cap(self):
        # A real observed name is a regression fixture, never an algorithm branch.
        wanted = self.module('Mathlib.Data.Nat.Choose.Sum', 'add_pow')
        fillers = [self.module('Mathlib.Algebra.Earlier' + str(i), 'earlier' + str(i)) for i in range(5)]
        hits = [wanted] + fillers
        self.model_values = [dict(requests=[dict(query='power expansion', preferred_names=['add_pow'],
            obligation_ids=['identity_goal'], intended_use='First requested proof strategy.')] + [
            dict(query='support operation ' + str(i), preferred_names=[h['name']],
                 obligation_ids=['identity_goal'], intended_use='Secondary supporting identity.')
            for i, h in enumerate(fillers)])]
        self.mocks[1].side_effect = lambda *a, **k: list(reversed(fillers))  # FTS does not return the exact target.
        self.mocks[4].side_effect = lambda name, **k: [h for h in hits if h['name'] == name]
        self.prepare()
        saved = self.receipt()
        self.assertEqual(saved['selected'][0]['name'], 'add_pow')
        self.assertEqual(saved['imports_added'][0], wanted['module'])
        self.assertEqual(len(saved['imports_added']), library.POLICY['max_new_modules'])
        self.assertEqual([h['name'] for h in saved['selected']], ['add_pow', 'earlier0', 'earlier1', 'earlier2'])
        self.assertEqual(self.mocks[4].call_args_list[0].args, ('add_pow',))
        self.assertNotIn('add_pow', [call.args[0] for call in self.mocks[1].call_args_list])
        self.assertEqual(self.svc.get(self.rid)['usage']['calls'], 1)

    def test_same_request_preserves_preferred_name_order_and_exact_precedes_phrase(self):
        first = self.module('Mathlib.Zed.Final', 'first')
        second = self.module('Mathlib.Algebra.Earlier', 'second')
        phrase = self.module('Mathlib.Algebra.Aardvark', 'phraseOnly')
        query = dict(requests=[dict(query='query support', preferred_names=['first', 'second'],
            obligation_ids=['identity_goal'], intended_use='Respect explicit preference order.')])
        self.model_values = [query]
        self.mocks[4].side_effect = lambda name, **k: [h for h in [first, second] if h['name'] == name]
        self.mocks[1].side_effect = lambda *a, **k: [phrase, second, first]
        self.prepare()
        self.assertEqual([h['name'] for h in self.receipt()['selected']], ['first', 'second', 'phraseOnly'])

    def test_ambiguous_full_name_is_not_reintroduced_by_phrase_fallback(self):
        one = self.module('Mathlib.Test.First', 'Nat.add_zero')
        two = self.module('Mathlib.Test.Second', 'Nat.add_zero')
        self.mocks[4].side_effect = lambda *a, **k: [one, two]
        self.mocks[1].side_effect = lambda *a, **k: [one, two]
        self.assertEqual(self.prepare(), draft())
        self.assertEqual(self.receipt()['selected'], [])
        self.assertIn('name_not_found_or_ambiguous', [issue['reason'] for issue in self.receipt()['issues']])

    def test_after_bind_context_cannot_be_prepared_again_or_detached(self):
        self.formalize()
        with self.assertRaisesRegex(ValueError, 'зафиксированный'):
            self.prepare()
        self.svc.update(self.rid, library_context=None)
        with self.assertRaisesRegex(ValueError, 'потеряла библиотечный'):
            self.svc._check(self.rid)

    def test_module_source_or_cache_drift_is_rejected_on_resume(self):
        self.prepare()
        Path(self.hit['file']).write_text('-- changed', encoding='utf-8')
        with self.assertRaisesRegex(ValueError, 'исходник или кэш изменён'):
            self.prepare()

    def test_local_timeout_stops_retrieval_without_claiming_model_or_proof_success(self):
        with patch('research_library_context.time.time', side_effect=[0, 121]):
            out = self.prepare()
        self.assertEqual(out, draft())
        self.assertIn('local_timeout', [i['reason'] for i in self.receipt()['issues']])
        self.assertFalse(self.receipt()['proof_checked'])


if __name__ == '__main__':
    unittest.main()
