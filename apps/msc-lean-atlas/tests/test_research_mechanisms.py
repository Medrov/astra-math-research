"""Catalog gates, provenance and reuse. Model-free checks, not research claims."""
import copy
import hashlib
import json
from pathlib import Path
import sys
import tempfile
import unittest
from unittest.mock import Mock

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
import lean_service
from research_mechanisms import MechanismStore, _sha


PROOF = 'import Init\n\n\n\ntheorem MechanismSmoke.identity (n : Nat) : n = n := by rfl\n'
CONTRACT = dict(imports=['Init'], prelude='', target='MechanismSmoke.identity', statement='∀ n : Nat, n = n',
    required_obligations=[dict(id='identity', target='MechanismSmoke.identity', statement='∀ n : Nat, n = n', expected_outcome='proved')])
ORIGIN = dict(run_id='a'*32, title='Identity fixture', source_sha256=_sha('test fixture context'),
              source_kind='literature', assumptions=[], sources=[dict(kind='test_fixture', source='unit test')])
REVIEW = dict(status='aligned', reason='Test fixture only; not an independent review of new research.')


def checked(source, target, work_dir, expected_statement, **kwargs):
    """Explicit checker double. Its logs must never be presented as a Lean run."""
    return dict(success=True, compilation_success=True, target_preserved=True, obligations_passed=True,
        target=target, source_sha256=_sha(source), expected_statement=expected_statement, contract_sha256=_sha(expected_statement),
        obligations=[dict(id=o['id'], target=o['target'], statement_sha256=_sha(o['statement']), expected_outcome=o['expected_outcome'], ok=True)
                     for o in kwargs['required_obligations']],
        axioms=[], audit=dict(status='passed', unexpected_axioms=[], unsafe_declarations=[]),
        declarations=[dict(name=target, kind='theorem', axioms=[])],
        print_axioms=dict(exit_code=0, theorems=[target], stdout='TEST DOUBLE: no compiler invoked.'),
        checker='test_double')


class MechanismTests(unittest.TestCase):
    def test_unicode_declaration_support_does_not_expand_import_paths(self):
        from research_mechanisms import _validate_contract_context
        for module in ('Mathlib.Δ', 'Mathlib.Eval₂', "Mathlib.Eval'", 'Mathlib..Eval'):
            with self.subTest(module=module), self.assertRaises(ValueError):
                _validate_contract_context('import ' + module + '\n\n\n\ntheorem foo : True := by trivial',
                    dict(CONTRACT, imports=[module]))

    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.store = MechanismStore(self.temp.name, 'env-a')

    def tearDown(self):
        self.temp.cleanup()

    def register(self, **kwargs):
        payload = dict(proof_source=PROOF, formal_contract=copy.deepcopy(CONTRACT), provenance=copy.deepcopy(ORIGIN),
                       semantic_review=copy.deepcopy(REVIEW), verifier=checked)
        payload.update(kwargs)
        return self.store.register(**payload)

    def test_only_fresh_complete_independent_check_can_publish(self):
        for field in ('success','compilation_success','target_preserved','obligations_passed'):
            def incomplete(*args, **kwargs):
                report=checked(*args,**kwargs);report[field]=False;return report
            with self.subTest(field=field),self.assertRaises(ValueError):self.register(verifier=incomplete)
        self.assertEqual(self.store.list(),[])
        checker=Mock(side_effect=checked);item=self.register(verifier=checker)
        self.assertEqual(checker.call_count,1)
        self.assertEqual(item['verification']['checker'],'test_double')
        self.assertEqual(item['source_application_status'],'not_verified')
        self.assertTrue(item['requires_new_proof'])

    def test_changed_contract_missing_obligation_and_unexpected_axioms_rejected(self):
        for mutation in ('source','obligation','axiom','print','target'):
            def incorrect(*args, **kwargs):
                result=checked(*args,**kwargs)
                if mutation=='source':result['source_sha256']='0'*64
                if mutation=='obligation':result['obligations']=[]
                if mutation=='axiom':result['axioms']=['Untrusted.assumption']
                if mutation=='print':result['print_axioms']['theorems']=[]
                if mutation=='target':result['expected_statement']='True'
                return result
            with self.subTest(mutation=mutation),self.assertRaises(ValueError):self.register(verifier=incorrect)

    def test_invalid_provenance_and_semantic_review_rejected_before_checker(self):
        checker=Mock(side_effect=AssertionError('must not reach checker'))
        invalids=[dict(semantic_review={'status':'uncertain'}),dict(provenance=dict(ORIGIN,source_sha256='unknown')),
                  dict(provenance=dict(ORIGIN,source_kind='lean')),dict(formal_contract=dict(CONTRACT,required_obligations=[]))]
        for invalid in invalids:
            with self.subTest(invalid=invalid),self.assertRaises(ValueError):self.register(verifier=checker,**invalid)
        checker.assert_not_called()

    def test_context_mismatch_and_commands_after_prelude_rejected_before_checker(self):
        checker=Mock(side_effect=AssertionError('must not reach checker'))
        source=('import Init\nnamespace CatalogReview\ndef flag : Prop := True\n'
                'theorem target : flag := by trivial\nend CatalogReview\n')
        contract=dict(imports=['Init'], prelude='namespace CatalogReview\ndef flag : Prop := False\nend CatalogReview\n',
            target='CatalogReview.target', statement='CatalogReview.flag', required_obligations=[dict(
                id='target',target='CatalogReview.target',statement='CatalogReview.flag',expected_outcome='proved')])
        payloads=[dict(proof_source=source,formal_contract=contract),
                  dict(formal_contract=dict(CONTRACT,imports=['Std'])),
                  dict(formal_contract=dict(CONTRACT,prelude='def flag : Prop := False\n')),
                  dict(proof_source=PROOF+'\ndef extra : Prop := True\n'),
                  dict(proof_source=PROOF+'\nnamespace Shadow\nend Shadow\n'),
                  dict(proof_source=PROOF+'\nopen Classical\n'),
                  dict(proof_source=PROOF+'\nimport Std\n')]
        for payload in payloads:
            with self.subTest(payload=payload),self.assertRaisesRegex(ValueError,'контекст|imports/prelude'):
                self.register(verifier=checker,**payload)
        checker.assert_not_called()
        self.assertEqual(self.store.list(),[])

    def test_context_in_old_record_is_revalidated_even_with_consistent_checksums(self):
        item=self.register()
        path=Path(self.temp.name)/item['id']/'mechanism.json'
        data=json.loads(path.read_text(encoding='utf-8'))
        data['formal_contract']['prelude']='def flag : Prop := False\n'
        data['contract_sha256']=_sha(data['formal_contract'])
        data.pop('payload_sha256');data['payload_sha256']=_sha(data)
        path.write_text(json.dumps(data),encoding='utf-8')
        with self.assertRaisesRegex(ValueError,'imports/prelude'):self.store.get(item['id'])
        self.assertEqual(self.store.list(),[])

    def test_search_is_reuse_without_automatic_application_or_stale_certificate(self):
        item=self.register()
        results=self.store.search('identity')
        self.assertEqual(results[0]['mechanism_id'],item['id'])
        self.assertEqual(results[0]['evidence_type'],'verified_mechanism_reuse')
        self.assertEqual(results[0]['applicability_status'],'not_verified_for_current_task')
        stale=MechanismStore(self.temp.name,'other-environment')
        self.assertEqual(stale.get(item['id'])['status'],'needs_recheck')
        self.assertEqual(stale.search('identity'),[])
        self.assertEqual(self.store.search('inexistentword'),[])

    def test_duplicate_idempotence_tamper_and_path_guards(self):
        item=self.register()
        self.assertEqual(self.register(verifier=Mock(side_effect=AssertionError('duplicate')) )['id'],item['id'])
        path=Path(self.temp.name)/item['id']/'mechanism.json'
        data=json.loads(path.read_text(encoding='utf-8'));data['formal_contract']['statement']='False'
        path.write_text(json.dumps(data),encoding='utf-8')
        with self.assertRaisesRegex(ValueError,'целостность'):self.store.get(item['id'])
        self.assertEqual(self.store.list(),[])
        for name in ('../outside','a'*32,'x'*64):
            with self.assertRaises(ValueError):self.store.get(name)

    def test_cancellation_and_zero_budget_never_publish(self):
        with self.assertRaises(InterruptedError):self.register(cancelled=lambda:True)
        with self.assertRaises(ValueError):self.register(timeout_seconds=0)
        self.assertEqual(self.store.list(),[])


@unittest.skipUnless(Path(lean_service.default_context()['lean']).is_file(),'Prepared Lean unavailable')
class RealMechanismCheck(unittest.TestCase):
    def test_complete_init_proof_is_independently_compiled_and_axioms_printed(self):
        with tempfile.TemporaryDirectory(prefix='mechanism-real-') as directory:
            store=MechanismStore(directory,'real-local-test')
            item=store.register(proof_source=PROOF,formal_contract=CONTRACT,provenance=ORIGIN,semantic_review=REVIEW,
                                timeout_seconds=60)
            self.assertTrue(item['verification']['success'])
            self.assertEqual(item['verification']['print_axioms']['exit_code'],0)
            self.assertIn('MechanismSmoke.identity',item['verification']['print_axioms']['stdout'])
            self.assertNotIn('checker',item['verification'])

    def test_exact_context_definition_is_compiled_and_false_contract_rejected(self):
        prelude='namespace CatalogReview\ndef flag : Prop := True\nend CatalogReview\n'
        proof='import Init\n\n'+prelude+'\n\ntheorem CatalogReview.target : CatalogReview.flag := by trivial\n'
        contract=dict(imports=['Init'],prelude=prelude,target='CatalogReview.target',statement='CatalogReview.flag',
            required_obligations=[dict(id='target',target='CatalogReview.target',statement='CatalogReview.flag',expected_outcome='proved')])
        origin=dict(ORIGIN,source_kind='formal_contract',source_sha256=_sha(proof))
        with tempfile.TemporaryDirectory(prefix='mechanism-context-') as directory:
            store=MechanismStore(directory,'real-local-test')
            false_contract=dict(contract,prelude=prelude.replace('True','False'))
            with self.assertRaisesRegex(ValueError,'imports/prelude'):
                store.register(proof_source=proof,formal_contract=false_contract,provenance=origin,
                               semantic_review=REVIEW,timeout_seconds=60)
            self.assertEqual(store.list(),[])
            item=store.register(proof_source=proof,formal_contract=contract,provenance=origin,
                                semantic_review=REVIEW,timeout_seconds=60)
            self.assertTrue(item['verification']['success'])
            self.assertEqual(item['formal_contract']['prelude'],prelude)
            self.assertIn('CatalogReview.target',item['verification']['print_axioms']['stdout'])


if __name__=='__main__':unittest.main()
