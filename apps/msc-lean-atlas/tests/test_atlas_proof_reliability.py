"""Exact logical roots and preserved revision data; no model or Lean calls.

The saved-live replay reads existing compiler output when available. Synthetic
negative audit rows exercise the trust boundary, not invented successful proofs.
"""
import copy
import hashlib
import json
from pathlib import Path
import sys
import tempfile
import threading
import time
import unittest
from unittest.mock import Mock, patch

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))
import research_lean as lean
import research_goedel as goedel
from research_objects import validate_graph
from research_service import ResearchService, atomic, sha
from research_versions import _accepted_seed
from test_transition_structure import literary_graph


class LogicalRootTests(unittest.TestCase):
    helper = 'Finset.sum._at.localDef._spec_1'
    source = 'def localDef : Nat := 0\ntheorem finished : localDef = 0 := by rfl\n'

    def declarations(self):
        return [dict(name='localDef', kind='definition', unsafe=False, axioms=['Classical.choice']),
                dict(name='finished', kind='theorem', unsafe=False, axioms=['propext', 'Quot.sound']),
                dict(name=self.helper, kind='axiom', unsafe=True, axioms=[self.helper])]

    def test_common_roots_ignore_only_unreferenced_runtime_specialization(self):
        deps = lean.audited_logical_axioms(self.declarations(), self.source, 'finished')
        self.assertEqual(deps, {'Classical.choice', 'propext', 'Quot.sound'})
        self.assertEqual(goedel.core.classify_axioms(deps)[0], 'LEGIT')

    def test_actual_helper_dependency_is_not_subtracted(self):
        for root in (0, 1):
            with self.subTest(root=root):
                declarations = self.declarations()
                declarations[root]['axioms'].append(self.helper)
                with self.assertRaisesRegex(ValueError, self.helper.replace('.', r'\.')):
                    lean.audited_logical_axioms(declarations, self.source, 'finished')

    def test_sorry_native_decide_and_custom_axiom_closures_reject(self):
        for axiom in ('sorryAx', 'Lean.ofReduceBool', 'untrustedPremise'):
            with self.subTest(axiom=axiom):
                declarations = self.declarations()
                declarations[1]['axioms'].append(axiom)
                with self.assertRaises(ValueError):
                    lean.audited_logical_axioms(declarations, self.source, 'finished')

    def test_explicit_helper_unsafe_nonhelper_and_absent_target_reject(self):
        with self.assertRaises(ValueError):
            lean.audited_logical_axioms(self.declarations(), self.source + '\naxiom ' + self.helper + ' : True', 'finished')
        declarations = self.declarations()
        declarations[2]['name'] = 'otherUnsafeImplementation'
        with self.assertRaises(ValueError):
            lean.audited_logical_axioms(declarations, self.source, 'finished')
        for declarations in ([], [dict(name='finished', kind='definition', axioms=[])]):
            with self.assertRaises(ValueError):
                lean.audited_logical_axioms(declarations, self.source, 'finished')

    def test_saved_compiler_specialization_failure_replays_logical_roots(self):
        workspace = ROOT / 'research_data/1e25a4f031714048b8a79c7ec6f1894b/lean/v0/polynomial_quotient_relations/0/lean-0e244fea5c35'
        if not (workspace / 'verification.json').exists():
            self.skipTest('Historical compiler report is local, not a portable test fixture')
        report = json.loads((workspace / 'verification.json').read_text(encoding='utf-8'))
        source = (workspace / 'Candidate.lean').read_text(encoding='utf-8')
        self.assertTrue(report['success'])
        roots = lean.audited_logical_axioms(report['declarations'], source, 'polynomial_quotient_relations')
        self.assertEqual(goedel.core.classify_axioms(roots)[0], 'LEGIT')
        raw = {axiom for row in report['declarations'] for axiom in row.get('axioms', [])}
        self.assertEqual(goedel.core.classify_axioms(raw)[0], 'CUSTOM_AXIOM')
        self.assertEqual(lean._audit_declarations(report['declarations'], source, 'polynomial_quotient_relations'), report['audit'])


def formalization():
    statement = '∀ n : Nat, n + 0 = n'
    return dict(status='ready', reason='Accepted full repaired formalization', limitations=['Only the selected transition'],
        agent_task=dict(imports=['Mathlib.Data.Nat.Basic', 'Mathlib.Algebra.Ring.Defs'],
                        prelude='noncomputable section\ndef baseValue : Nat := 0', target='identity', statement=statement),
        obligations=[dict(id='all_n', title='Every natural n', target='identity', statement=statement, expected_outcome='proved')])


class PreservedRevisionTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        with patch.object(ResearchService, '_environment_fingerprint', return_value='revision-reliability-test'):
            self.service = ResearchService(self.temp.name, recover=False)
        self.service.arxiv = Mock()
        self.service.arxiv.get_paper.return_value = dict(versioned_id='2601.00001v1', title='Pinned article',
            snapshot_sha256={'article_html':'c'*64}, source_urls={'html':'https://arxiv.org/html/2601.00001v1'},
            sections=[dict(id='S2')])
        self.stored = self.service.registry.create(literary_graph())
        self.parent = self.service.create(dict(mode='single', purpose='prove', graph_id=self.stored['id'],
            graph_revision=1, transition_id='coordinate_change', budget=dict(max_calls=8, timeout_seconds=600)), start=False)
        self.rid = self.parent['id']
        self.service.update(self.rid, status='failed', phase='failed')

    def tearDown(self):
        self.service.pool.shutdown(wait=True)
        self.temp.cleanup()

    def arm(self, rid):
        self.service._started[rid] = time.monotonic()
        self.service.cancel_flags[rid] = threading.Event()

    def typed_draft(self, draft, version=0, previous=None, well_typed=True):
        graph = validate_graph(self.service.detail(self.rid)['object_graph'])
        folder = self.service.folder(self.rid) / 'drafts' / ('v' + str(version))
        harness = folder / 'workspace' / 'ContractTypes.lean'
        harness.parent.mkdir(parents=True, exist_ok=True)
        harness.write_text('-- Mocked preflight harness, not a proof\n', encoding='utf-8')
        record = dict(version=version, intent_sha256=sha(graph), parent_sha256=previous,
                      draft_sha256=sha(draft), formalization=draft)
        report = dict(status='complete', well_typed=well_typed, proof_checked=False, audit=dict(status='passed'),
            contract_sha256=sha(dict(draft['agent_task'], required_obligations=draft['obligations'])),
            workspace=str(harness.parent), source_sha256=hashlib.sha256(harness.read_bytes()).hexdigest())
        atomic(folder / 'draft.json', record)
        atomic(folder / 'verification.json', report)
        return record, report

    def bind_accepted(self, draft):
        # Model a legacy fully bound graph without a library receipt. Tests of
        # the new policy below exercise the real child lifecycle separately.
        old = self.service.get(self.rid)
        contract = copy.deepcopy(old['contract'])
        contract.pop('library_context_policy', None)
        self.service.update(self.rid, contract=contract, contract_sha256=sha(contract))
        graph = validate_graph(self.service.detail(self.rid)['object_graph'])
        selected = self.service._transition(graph, 'coordinate_change')
        selected.update(formulation_status='formalized', agent_task=copy.deepcopy(draft['agent_task']),
                        obligations=copy.deepcopy(draft['obligations']))
        stored = self.service.registry.create(graph)
        self.service._bind_graph(self.rid, stored, selected['id'])
        self.service.update(self.rid, formalization_review=copy.deepcopy(draft))

    def test_last_typed_repair_before_binding_is_preserved_whole_and_hash_bound(self):
        initial = formalization()
        initial['agent_task']['imports'] = ['Mathlib.Missing.Module']
        first, _ = self.typed_draft(initial, well_typed=False)
        accepted = formalization()
        self.typed_draft(accepted, version=1, previous=first['draft_sha256'])
        folder = self.service.folder(self.rid)
        before = {str(p.relative_to(folder)): p.read_bytes() for p in folder.rglob('*') if p.is_file()}
        self.assertEqual(self.service.revision_options(self.service.detail(self.rid))['source'], 'typed_draft')
        child = self.service.revise_run(self.rid, dict(reason='Repeat the exact accepted formalization'))
        self.assertEqual(child['revision_draft'], accepted)
        self.assertEqual(child['contract']['revision_draft_sha256'], sha(accepted))
        self.assertTrue(child['contract']['preserve_formalization'])
        origin = child['contract']['revision_seed_provenance']
        self.assertEqual(origin['source'], 'typed_draft')
        self.assertEqual(origin['version'], 1)
        self.assertEqual(origin['parent_run_id'], self.rid)
        self.assertEqual(origin['parent_contract_sha256'], self.parent['contract_sha256'])
        self.assertEqual(child['usage']['calls'], 0)
        self.assertNotIn('object_contract', child)
        self.assertNotIn('contract_verification', child)
        self.assertNotIn('contract_review', child)
        self.assertEqual(child['paper_manifest'], self.parent['paper_manifest'])
        for relative, data in before.items():
            self.assertEqual((folder / relative).read_bytes(), data, relative)
        self.arm(child['id'])
        self.service.update(child['id'], revision_draft=dict(accepted, reason='Tampered'))
        with self.assertRaisesRegex(ValueError, 'черновик'):
            self.service._check(child['id'])

    def test_bound_full_review_keeps_metadata_and_all_final_imports(self):
        accepted = formalization()
        self.bind_accepted(accepted)
        child = self.service.revise_run(self.rid, dict(reason='Retry accepted context', corrections={'title':'Readable title'}))
        self.assertEqual(child['revision_draft'], accepted)
        self.assertEqual(child['contract']['revision_seed_provenance']['source'], 'bound_graph_task')
        self.assertEqual(child['source_card']['title'], 'Readable title')

    def test_library_receipt_is_preferred_and_preserved_in_full(self):
        accepted = formalization()
        self.bind_accepted(accepted)
        reference = dict(input_sha256='a'*64, receipt_sha256='b'*64)
        self.service.update(self.rid, library_context=reference)
        with patch('research_library_context._read_receipt', return_value=dict(formalization=accepted)) as read:
            child = self.service.revise_run(self.rid, dict(reason='Keep library enriched accepted context'))
        self.assertTrue(read.called)
        self.assertTrue(all(call.kwargs == {'required':True} for call in read.call_args_list))
        self.assertEqual(child['revision_draft'], accepted)
        origin = child['contract']['revision_seed_provenance']
        self.assertEqual(origin['source'], 'library_context')
        self.assertEqual(origin['library_context'], reference)
        self.assertEqual(origin['seed_sha256'], sha(accepted))

    def test_optout_and_mathematical_edits_never_silently_reuse(self):
        self.bind_accepted(formalization())
        for payload, policy in ((dict(preserve_formalization=False), 'reformalize_requested'),
                                (dict(corrections={'claim':'New mathematics'}), 'mathematical_changes')):
            with self.subTest(policy=policy):
                child = self.service.revise_run(self.rid, dict(reason='Explicit new version', **payload))
                self.assertIsNone(child['revision_draft'])
                self.assertFalse(child['contract']['preserve_formalization'])
                self.assertEqual(child['contract']['revision_seed_policy'], policy)
        with self.assertRaises(ValueError):
            self.service.revise_run(self.rid, dict(reason='Invalid preservation flag', preserve_formalization='true'))

    def test_tampered_chain_or_harness_is_not_an_accepted_seed(self):
        accepted = formalization()
        record, report = self.typed_draft(accepted)
        path = self.service.folder(self.rid) / 'drafts/v0/draft.json'
        for invalid in (dict(record, intent_sha256='f'*64), dict(record, parent_sha256='f'*64),
                        dict(record, formalization=dict(accepted, reason='Changed'))):
            with self.subTest(invalid=invalid):
                atomic(path, invalid)
                run = self.service.detail(self.rid)
                self.assertFalse(self.service.revision_options(run)['can_preserve_formalization'])
                with self.assertRaises(ValueError):
                    _accepted_seed(self.service, run)
        atomic(path, record)
        (Path(report['workspace']) / 'ContractTypes.lean').write_text('Changed', encoding='utf-8')
        with self.assertRaisesRegex(ValueError, 'артефактами'):
            _accepted_seed(self.service, self.service.detail(self.rid))

    def test_unchecked_draft_does_not_become_preservable(self):
        self.typed_draft(formalization(), well_typed=False)
        child = self.service.revise_run(self.rid, dict(reason='Retry after untyped draft'))
        self.assertIsNone(child['revision_draft'])
        self.assertEqual(child['contract']['revision_seed_policy'], 'no_accepted_formalization')

    def test_preserved_seed_runs_fresh_type_and_semantic_gates_without_formalizer(self):
        accepted = formalization()
        self.bind_accepted(accepted)
        child = self.service.revise_run(self.rid, dict(reason='Keep the exact accepted contract'))
        rid = child['id']
        self.arm(rid)
        calls = []

        def response(run_id, role, prompt, key):
            calls.append(role)
            if role == 'library_context':
                value = dict(requests=[])
            elif role == 'semantic_review':
                value = dict(status='aligned', reason='Mock semantic gate', limitations=[])
            else:
                raise AssertionError('Unexpected model role: ' + role)
            return dict(text=json.dumps(value))

        with patch.object(self.service, '_call', side_effect=response), \
             patch.object(self.service, '_preflight_contract', return_value=dict(well_typed=True)) as preflight, \
             patch('research_retrieval.library_manifest', return_value=dict(status='unavailable')):
            self.service._formalize_transition(dict(run_id=rid))
            self.service._validate_transition(dict(run_id=rid))
        self.assertEqual(calls, ['library_context', 'semantic_review'])
        self.assertEqual(preflight.call_count, 2)
        for call in preflight.call_args_list:
            self.assertEqual(call.args[0], rid)
            self.assertEqual(call.args[1], dict(accepted['agent_task'], required_obligations=accepted['obligations']))
        current = self.service.get(rid)
        self.assertEqual(current['formalization_review'], accepted)
        self.assertEqual(current['contract_review']['status'], 'aligned')
        self.assertEqual(current['outcome'], 'unknown')
        self.assertEqual(current['contract']['revision_draft_sha256'], sha(accepted))


if __name__ == '__main__':
    unittest.main()
