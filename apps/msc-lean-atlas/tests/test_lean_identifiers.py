"""Exact safe declaration names across retrieval/repair/export boundaries.

Compiler execution is mocked here. Real pinned exporter/lookup regressions are
owned by the coordinator in test_targeted_library_export/test_exact_library_names.
"""
import copy
from contextlib import closing
import json
from pathlib import Path
import sqlite3
import sys
import tempfile
import unittest
from unittest.mock import patch

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
import lean_identifiers as identifiers
import research_drafts as drafts
import research_lean as lean
import research_library_context as context
import research_retrieval as retrieval


C_NAME = 'MvPolynomial.eval₂Hom_C'
X_NAME = "MvPolynomial.eval₂Hom_X'"


def diagnostic(name):
    return dict(diagnostics=[dict(stdout="error: unknown identifier '" + name + "'", stderr='')])


def formalization(name=C_NAME):
    statement = name + ' = ' + name
    return dict(status='ready', reason='Fixture', limitations=[],
        agent_task=dict(imports=['Mathlib.Algebra.MvPolynomial.Eval'], prelude='', target='fixture_goal', statement=statement),
        obligations=[dict(id='one', target='fixture_goal', title='Fixture', statement=statement, expected_outcome='proved')])


class LeanIdentifierTests(unittest.TestCase):
    def test_shared_matcher_accepts_actual_names_without_normalization(self):
        self.assertIs(lean.NAME, identifiers.DECLARATION_NAME)
        self.assertIs(drafts.SYMBOL, identifiers.DECLARATION_NAME)
        self.assertIs(context.NAME, identifiers.DECLARATION_NAME)
        accepted = [C_NAME, X_NAME, "foo'", "Greek.αβ_γ'", 'Ω.result₀', 'δ₁.ε₂', 'Space.ℝ', '𝒜.mapₙ']
        for name in accepted:
            with self.subTest(name=name):
                self.assertEqual(identifiers.DECLARATION_NAME.fullmatch(name).group(), name)
                self.assertTrue(lean.theorem_header(name, 'True').startswith('theorem ' + name + ' :'))

    def test_injection_controls_operators_escapes_and_malformed_components_are_rejected(self):
        invalid = ['', '.Name', 'Name.', 'Name..other', '3name', '₂name', "'name", 'α β',
            'a\nb', 'a\rb', 'a\tb', 'a\x00b', 'a\u200bb', 'a\u202eb', 'a\u00a0b',
            'a;import', 'a:=b', 'a+b', 'a-b', 'a*b', 'a/b', 'a\\b', 'a→b', 'a∧b',
            'a"b', '`foo', '«foo»', r'a\u2082', 'foo!', 'foo?', 'α\u0301', 'λ', 'Π', 'Σ',
            'name' * 51, 'имя', '名']
        for name in invalid:
            with self.subTest(name=repr(name)):
                self.assertIsNone(identifiers.DECLARATION_NAME.fullmatch(name))

    def test_module_paths_remain_ascii_and_have_nonempty_components(self):
        for module in ['Mathlib', 'Init', 'Std', 'Mathlib.Algebra.MvPolynomial.Eval', 'StructureInput']:
            self.assertIsNotNone(identifiers.MODULE_NAME.fullmatch(module))
        for module in [C_NAME, X_NAME, 'Mathlib.α', "Mathlib.Foo'", 'Mathlib..Foo',
                       'Mathlib../Foo', 'Mathlib.Foo;import', 'Mathlib/Bar']:
            self.assertIsNone(identifiers.MODULE_NAME.fullmatch(module))
            with self.subTest(module=module), self.assertRaises(ValueError):
                lean._validate_source('import ' + module + '\n')

    def test_exact_lookup_keeps_unicode_subscript_prime_and_namespace_distinct(self):
        with tempfile.TemporaryDirectory() as temporary:
            index = Path(temporary) / 'names.sqlite'
            with closing(sqlite3.connect(index)) as db:
                db.execute('CREATE TABLE declarations (id TEXT, payload TEXT)')
                for i, name in enumerate([C_NAME, X_NAME, 'Greek.α']):
                    db.execute('INSERT INTO declarations VALUES (?,?)', (str(i), json.dumps(dict(id=str(i), name=name))))
                db.commit()
            for name in [C_NAME, X_NAME, 'Greek.α']:
                self.assertEqual([h['name'] for h in retrieval.lookup_library_name(name, index_path=index)], [name])
            for missing in ['MvPolynomial.eval2Hom_C', 'MvPolynomial.eval₂Hom_X', 'eval₂Hom_C', 'Greek.a']:
                self.assertEqual(retrieval.lookup_library_name(missing, index_path=index), [])
            for invalid in ['Mathlib;import X', '«eval₂Hom_C»']:
                self.assertEqual(retrieval.lookup_library_name(invalid, index_path=index), [])

    def test_search_signature_tokens_do_not_truncate_subscripts_or_apostrophes(self):
        names = retrieval.type_symbols(C_NAME + ' f g r = ' + X_NAME + ' f g i')
        self.assertIn(C_NAME, names)
        self.assertIn(X_NAME, names)
        self.assertNotIn('MvPolynomial.eval', names)
        self.assertNotIn('MvPolynomial.eval₂Hom_X', names)

    def test_diagnostic_quotes_retain_trailing_prime_and_filter_injection(self):
        text = '\n'.join(["unknown identifier '" + C_NAME + "'", "unknown constant '" + X_NAME + "'",
            'unknown namespace `Greek.α`', 'unknown identifier ‘Greek.β₂’',
            "unknown identifier 'x;import'", "unknown constant 'foo bar'"])
        self.assertEqual(drafts.unknown_symbols(dict(error=text)), {C_NAME, X_NAME, 'Greek.α', 'Greek.β₂'})

    def test_obligation_retry_prioritizes_complete_unicode_name(self):
        with patch.object(retrieval, 'search_library', return_value=[]) as lookup, \
                patch.object(retrieval, 'search', return_value=[]):
            queries, _ = retrieval.search_obligation('Long immutable goal', diagnostic(X_NAME), [])
        self.assertEqual(queries[0]['text'], X_NAME)
        self.assertEqual(lookup.call_args.args[0], X_NAME)

    def test_library_request_accepts_unicode_but_not_code(self):
        request = dict(requests=[dict(query='evaluation constants', preferred_names=[C_NAME, X_NAME],
            obligation_ids=['one'], intended_use='Exact library request')])
        self.assertEqual(context.validate_requests(request, formalization()['obligations']), request['requests'])
        bad = copy.deepcopy(request); bad['requests'][0]['preferred_names'] = [C_NAME + ';import Init']
        with self.assertRaises(ValueError):
            context.validate_requests(bad, formalization()['obligations'])

    def test_exact_repair_does_not_change_subscript_or_prime_neighbors(self):
        old, new = 'Greek.α', 'Greek.β₂'
        source = old + ' ' + old + "' " + old + '₂ ' + old + '.nested ' + 'prefix' + old
        replaced, count = identifiers.replace_identifier(source, old, new)
        self.assertEqual(count, 1)
        self.assertEqual(replaced, new + source[len(old):])
        original = formalization(X_NAME)
        changed = drafts.apply_repair(original, dict(reason='Explicit compiler-driven rename only',
            imports_additions=[], replacements=[dict(old=X_NAME, new='Greek.γ₂')]), diagnostic(X_NAME))
        self.assertIn('Greek.γ₂', changed['agent_task']['statement'])
        self.assertEqual(original, formalization(X_NAME))
        self.assertEqual(changed['obligations'][0]['id'], original['obligations'][0]['id'])

    def test_unsupported_lean_rest_does_not_create_partial_tokens_or_repairs(self):
        # Lean accepts these suffixes, but our safe declaration subset does not.
        # Boundaries must still treat each whole spelling as one name.
        source = 'foo foo! foo? foo℀ ℀foo foo᾽ foo℘'
        self.assertEqual(identifiers.identifier_tokens(source), ['foo'])
        changed, count = identifiers.replace_identifier(source, 'foo', 'bar')
        self.assertEqual(count, 1)
        self.assertEqual(changed, 'bar' + source[3:])

    def test_repair_cannot_add_unicode_module_or_silently_alias_missing_prime(self):
        value = formalization('MvPolynomial.eval₂Hom_X')
        self.assertEqual(drafts.unknown_symbols(diagnostic('MvPolynomial.eval₂Hom_X')), {'MvPolynomial.eval₂Hom_X'})
        with self.assertRaises(ValueError):
            drafts.apply_repair(value, dict(reason='Invalid module fixture',
                imports_additions=['Mathlib.α'], replacements=[]), diagnostic('MvPolynomial.eval₂Hom_X'))
        # Validation alone never substitutes the prime-suffixed library name.
        self.assertEqual(value['agent_task']['statement'], 'MvPolynomial.eval₂Hom_X = MvPolynomial.eval₂Hom_X')

    def test_export_writes_literal_unicode_utf8_with_strict_ascii_imports(self):
        with tempfile.TemporaryDirectory() as temporary:
            folder = Path(temporary)
            def compiler(context_, env, work, filename, *args, **kwargs):
                if filename == 'AtlasDump.lean':
                    (work / 'compiler-declarations.json').write_text(json.dumps({'declarations': [{'name': C_NAME}]},
                        ensure_ascii=False), encoding='utf-8')
            with patch.object(lean, '_run', side_effect=compiler):
                result = lean._export({}, {}, folder, [], None, modules=['Mathlib.Algebra.MvPolynomial.Eval'], names=[C_NAME, X_NAME])
            generated = (folder / 'AtlasDump.lean').read_text(encoding='utf-8')
            self.assertIn('"' + C_NAME + '"', generated)
            self.assertIn('"' + X_NAME + '"', generated)
            self.assertNotIn(r'\u2082', generated)
            self.assertEqual(result['declarations'][0]['name'], C_NAME)
            with patch.object(lean, '_run'), self.assertRaises(ValueError):
                lean._export({}, {}, folder, [], None, modules=['Mathlib.α'], names=[C_NAME])


if __name__ == '__main__':
    unittest.main()
