"""Offline regressions for the two 2403.19691v1 candidate-source failures.

Fixtures reproduce the saved reference shapes, not a new model/Lean result.
"""
import copy
from pathlib import Path
import sys
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
import research_structure as structure
from research_objects import validate_graph
from research_transition_schema import CANDIDATE_GRAPH_SCHEMA, GRAPH_SCHEMA


URL = 'https://arxiv.org/html/2403.19691v1'
QUOTE = 'If $m=n$, then $A$ and $B$ are square.'
DOC = 'If `f` is a monoid homomorphism then `f (a * b) = f a * f b`.'


def source_snapshot(ids=('evidence-2',)):
    obj = dict(id='matrices', title='Square matrices', kind='matrix', definition='Two square complex matrices.',
        parameters=['n'], assumptions=[], msc_codes=['15'], lean_refs=[])
    graph = dict(title='Theorem 2', question='The square case of the determinant identity.', msc_codes=['15'],
        objects=[obj], transitions=[dict(id='square_equality', title='Square equality', source_ids=['matrices'],
            target_ids=['matrices'], relation_type='property_transfer', construction='Expand the determinant of the Gram product.',
            assumptions=['The matrices are square.'], claim='The determinant equality holds for square matrices.',
            formulation_status='literature_only', obligations=[], agent_task=None, case_id=None, source_refs=list(ids),
            grounding=[dict(component='assumption:0', source_ref=ids[0], quote=QUOTE, origin='source_excerpt')])],
        sources=[dict(id=ref, title='Retained article', url=URL, locator='Theorem 2',
            versioned_id='2403.19691v1', snapshot_sha256='b'*64, section_id='document') for ref in ids])
    graph = dict(validate_graph(graph), id='a'*32, revision=1)
    return structure.transition_snapshot(graph, 'square_equality')


def route():
    return dict(id='route_1', title='Representation', msc_code='16', hits=[
        dict(title='Matrix.det_conjTranspose', name='Matrix.det_conjTranspose', module='Mathlib.Data.Matrix.ConjTranspose',
             statement='det A.conjTranspose = star (det A)', source_sha256='c'*64, extraction='lean_environment',
             type_status='compiler_resolved', elaborated_type='det A.conjTranspose = star (det A)'),
        dict(title='MonoidHom.map_mul', name='MonoidHom.map_mul', module='Mathlib.Algebra.Group.Hom.Basic',
             statement='f (a * b) = f a * f b', doc_comment=DOC, source_sha256='d'*64, extraction='textual_unverified')])


def proposal(*, cite_origin=False, two=False):
    """Route 1 nested alias in grounding only; route 3 also in source_refs."""
    graph = dict(title='Proposed bridge', question='Compare determinant structures.', msc_codes=['16'],
        objects=[dict(id='representation', title='Multiplicative representation', kind='representation',
            definition='A representation with explicitly required determinant preservation.', parameters=[],
            assumptions=['The identification must be proved separately.'], msc_codes=['16'], lean_refs=[])],
        transitions=[dict(id='bridge', title='Conditional determinant transport', source_ids=['representation'],
            target_ids=['representation'], relation_type='property_transfer', construction='Transport a determinant through a multiplicative representation.',
            assumptions=['The representation preserves the specified determinant.'], claim='The determinant identity transfers under the stated hypotheses.',
            formulation_status='literature_only', obligations=[], agent_task=None, case_id=None,
            source_refs=['input', 'hit_1', 'hit_2'] + (['evidence-2'] if cite_origin else []),
            grounding=[dict(component='assumption:0', source_ref='evidence-2', quote=QUOTE, origin='source_excerpt'),
                       dict(component='construction', source_ref='hit_2', quote=DOC, origin='source_excerpt')])],
        sources=[dict(id='input', title='Input', url='', locator='square_equality'),
                 dict(id='evidence-2', title='Article (model display title)', url=URL, locator='Theorem 2, formula (7)'),
                 dict(id='hit_1', title='Matrix.det_conjTranspose', url='', locator=''),
                 dict(id='hit_2', title='MonoidHom.map_mul', url='', locator='')])
    if two:
        graph['transitions'].append(dict(copy.deepcopy(graph['transitions'][0]), id='restriction_bridge'))
    return graph


class SourceProvenanceRepairTests(unittest.TestCase):
    def setUp(self):
        self.source = source_snapshot()
        self.route = route()

    def normalize(self, graph, source=None, **kwargs):
        return structure.normalize_candidates(graph, self.route, source or self.source, **kwargs)

    def test_original_route_1_alias_in_grounding_resolves_without_rewriting_input(self):
        raw = proposal(); before = copy.deepcopy(raw); log = []
        graph, candidates = self.normalize(raw, resolution_log=log)
        self.assertEqual(raw, before)
        self.assertEqual(len(candidates), 1)
        transition = graph['transitions'][0]
        self.assertEqual(transition['grounding'][0]['source_ref'], 'structure_origin_1')
        self.assertEqual(transition['grounding'][1]['source_ref'], 'route_1_hit_2')
        self.assertEqual(transition['formulation_status'], 'candidate')
        self.assertIsNone(transition['agent_task']); self.assertEqual(transition['obligations'], [])
        self.assertEqual(next(s for s in graph['sources'] if s['id'] == 'structure_input')['structure_transition'], self.source)
        origin = next(s for s in graph['sources'] if s['id'] == 'structure_origin_1')
        self.assertEqual(origin['title'], self.source['sources'][0]['title'])
        self.assertEqual(origin['snapshot_sha256'], 'b'*64)
        self.assertTrue(any(b['source_ref'] == 'evidence-2' and b['method'] == 'pinned_legacy_alias' for b in log))

    def test_original_route_3_alias_in_source_refs_keeps_both_candidates(self):
        graph, candidates = self.normalize(proposal(cite_origin=True, two=True))
        self.assertEqual(len(candidates), 2)
        for transition in graph['transitions']:
            self.assertEqual(transition['source_refs'].count('structure_origin_1'), 1)
            self.assertIn('route_1_hit_1', transition['source_refs'])
            self.assertNotIn('route_1_evidence-2', transition['source_refs'])

    def test_new_flat_catalogue_has_pins_and_only_retained_quotes_for_origins(self):
        evidence = structure.route_evidence(self.route, self.source)
        self.assertEqual([e['id'] for e in evidence], ['input', 'hit_1', 'hit_2', 'origin_1'])
        self.assertTrue(all(len(e['provenance_sha256']) == 64 for e in evidence))
        origin = evidence[-1]
        self.assertEqual(origin['statement'], QUOTE)
        self.assertEqual(origin['origin_source'], self.source['sources'][0])
        self.assertNotIn('provenance_sha256', GRAPH_SCHEMA['properties']['sources']['items']['properties'])
        self.assertIn('provenance_sha256', CANDIDATE_GRAPH_SCHEMA['properties']['sources']['items']['required'])
        graph = proposal(cite_origin=True)
        graph['sources'][1].update(id='origin_1', provenance_sha256=origin['provenance_sha256'])
        graph['transitions'][0]['source_refs'][-1] = 'origin_1'
        graph['transitions'][0]['grounding'][0]['source_ref'] = 'origin_1'
        normalized, _ = self.normalize(graph)
        self.assertEqual(normalized['transitions'][0]['grounding'][0]['source_ref'], 'structure_origin_1')

    def test_origin_pin_is_required_and_checked(self):
        for pin in (None, '', 'e'*64):
            graph = proposal(); graph['sources'][1]['id'] = 'origin_1'
            graph['transitions'][0]['grounding'][0]['source_ref'] = 'origin_1'
            if pin is not None: graph['sources'][1]['provenance_sha256'] = pin
            with self.subTest(pin=pin), self.assertRaises(ValueError): self.normalize(graph)

    def test_unknown_alias_is_rejected_even_with_correct_url_and_quote(self):
        graph = proposal(); graph['sources'][1]['id'] = 'evidence-999'
        graph['transitions'][0]['grounding'][0]['source_ref'] = 'evidence-999'
        with self.assertRaisesRegex(ValueError, 'Неизвестный'): self.normalize(graph)

    def test_alias_id_alone_or_wrong_url_is_not_provenance(self):
        for url in ('', 'https://arxiv.org/html/2403.19691v2', 'https://example.org/article'):
            graph = proposal(); graph['sources'][1]['url'] = url
            with self.subTest(url=url), self.assertRaisesRegex(ValueError, 'URL'): self.normalize(graph)
        graph = proposal(); del graph['sources'][1]
        with self.assertRaisesRegex(ValueError, 'явную привязку'): self.normalize(graph)

    def test_optional_origin_metadata_cannot_conflict(self):
        for key, value in [('versioned_id', '2403.19691v2'), ('snapshot_sha256', 'e'*64),
                           ('section_id', 'other'), ('provenance_sha256', 'e'*64), ('source_sha256', 'e'*64),
                           ('extraction', 'lean_environment'), ('untrusted_certificate', 'verified')]:
            graph = proposal(); graph['sources'][1][key] = value
            with self.subTest(key=key), self.assertRaises(ValueError): self.normalize(graph)

    def test_duplicate_source_declarations_are_rejected(self):
        graph = proposal(); graph['sources'].append(copy.deepcopy(graph['sources'][1]))
        with self.assertRaisesRegex(ValueError, 'Повторный'): self.normalize(graph)

    def test_nested_alias_collision_with_flat_namespace_fails_closed(self):
        for alias in ('input', 'hit_1', 'origin_2'):
            source = source_snapshot((alias, 'other'))
            graph = proposal(); graph['sources'][1]['id'] = alias
            graph['transitions'][0]['grounding'][0]['source_ref'] = alias
            # Avoid a duplicate declaration, testing the namespace collision itself.
            graph['sources'] = [s for i, s in enumerate(graph['sources']) if i == 1 or s['id'] != alias]
            with self.subTest(alias=alias), self.assertRaisesRegex(ValueError, 'Неоднозначный'):
                self.normalize(graph, source)

    def test_nested_alias_matching_its_own_canonical_id_still_requires_pin(self):
        source = source_snapshot(('origin_1',))
        graph = proposal(); graph['sources'][1]['id'] = 'origin_1'
        graph['transitions'][0]['grounding'][0]['source_ref'] = 'origin_1'
        with self.assertRaisesRegex(ValueError, 'provenance_sha256'): self.normalize(graph, source)

    def test_source_excerpt_must_be_in_its_bound_source(self):
        for quote in ('An invented stronger article claim.', DOC):
            graph = proposal(); graph['transitions'][0]['grounding'][0]['quote'] = quote
            with self.subTest(quote=quote), self.assertRaisesRegex(ValueError, 'Цитата'): self.normalize(graph)
        source = source_snapshot(('evidence-2', 'other'))
        graph = proposal(); graph['sources'][1]['id'] = 'other'
        graph['transitions'][0]['grounding'][0]['source_ref'] = 'other'
        with self.assertRaisesRegex(ValueError, 'Цитата'): self.normalize(graph, source)

    def test_unknown_grounding_ref_is_rejected_independently(self):
        graph = proposal(); graph['transitions'][0]['grounding'][0]['source_ref'] = 'invented'
        with self.assertRaisesRegex(ValueError, 'Неизвестный'): self.normalize(graph)

    def test_no_library_hit_and_fabricated_hit_are_rejected(self):
        for refs in (['input', 'evidence-2'], ['input', 'hit_999']):
            graph = proposal(); graph['transitions'][0]['source_refs'] = refs
            with self.subTest(refs=refs), self.assertRaises(ValueError): self.normalize(graph)

    def test_input_and_hit_digest_or_source_hash_conflicts_are_rejected(self):
        for index in (0, 2):
            for key in ('provenance_sha256', 'source_sha256'):
                graph = proposal(); graph['sources'][index][key] = 'e'*64
                with self.subTest(index=index, key=key), self.assertRaises(ValueError): self.normalize(graph)

    def test_pin_from_another_snapshot_or_hit_cannot_be_replayed(self):
        evidence = structure.route_evidence(self.route, self.source)
        graph = proposal(); graph['sources'][2]['provenance_sha256'] = evidence[2]['provenance_sha256']
        with self.assertRaisesRegex(ValueError, 'provenance_sha256'): self.normalize(graph)
        other = source_snapshot(('evidence-2', 'another'))
        graph = proposal(); graph['sources'][1]['provenance_sha256'] = evidence[-1]['provenance_sha256']
        with self.assertRaisesRegex(ValueError, 'provenance_sha256'): self.normalize(graph, other)

    def test_snapshot_tampering_is_rejected_before_alias_resolution(self):
        source = copy.deepcopy(self.source); source['sources'][0]['snapshot_sha256'] = 'e'*64
        with self.assertRaises(ValueError): self.normalize(proposal(), source)

    def test_zero_candidates_remains_valid(self):
        graph = proposal(); graph.update(objects=[], transitions=[], sources=[])
        normalized, candidates = self.normalize(graph)
        self.assertEqual(normalized['transitions'], []); self.assertEqual(candidates, [])

    def test_all_object_grounding_components_follow_the_object_id_remap(self):
        graph = proposal()
        identifiers = ['matrix_source', 'point_evaluation', 'scalar_kernel']
        graph['objects'] = [dict(copy.deepcopy(graph['objects'][0]), id=identifier) for identifier in identifiers]
        transition = graph['transitions'][0]
        transition.update(source_ids=['matrix_source'], target_ids=['point_evaluation', 'scalar_kernel'])
        transition['grounding'] += [
            dict(component='object:matrix_source', origin='source_excerpt', source_ref='evidence-2', quote=QUOTE),
            dict(component='object:point_evaluation', origin='source_excerpt', source_ref='hit_2', quote=DOC),
            dict(component='object:scalar_kernel', origin='proposed_abstraction', source_ref='', quote='')]
        before = copy.deepcopy(graph)
        normalized, _ = self.normalize(graph)
        grounding = normalized['transitions'][0]['grounding']
        self.assertEqual([g['component'] for g in grounding[-3:]], ['object:route_1_' + i for i in identifiers])
        self.assertEqual([g['source_ref'] for g in grounding[-3:]], ['structure_origin_1', 'route_1_hit_2', ''])
        self.assertEqual([g['quote'] for g in grounding[-3:]], [QUOTE, DOC, ''])
        self.assertEqual([g['component'] for g in grounding[:2]], ['assumption:0', 'construction'])
        object_ids = {obj['id'] for obj in normalized['objects']}
        self.assertTrue(all(g['component'].split(':', 1)[1] in object_ids for g in grounding if g['component'].startswith('object:')))
        self.assertEqual(graph, before)

    def test_existing_canonical_object_components_are_not_double_prefixed(self):
        graph = proposal()
        graph['transitions'][0]['grounding'] += [dict(component='object:' + identifier,
            origin='proposed_abstraction', source_ref='', quote='')
            for identifier in ('route_1_representation', 'input_object')]
        normalized, _ = self.normalize(graph)
        self.assertEqual([g['component'] for g in normalized['transitions'][0]['grounding'][-2:]],
                         ['object:route_1_representation', 'object:input_object'])

    def test_unknown_local_or_prefixed_object_components_are_rejected(self):
        for identifier in ('invented', 'route_1_invented', 'route_2_representation', ''):
            graph = proposal()
            graph['transitions'][0]['grounding'].append(dict(component='object:' + identifier,
                origin='proposed_abstraction', source_ref='', quote=''))
            with self.subTest(identifier=identifier), self.assertRaisesRegex(ValueError, 'Неизвестный объект'):
                self.normalize(graph)

    def test_ambiguous_local_and_canonical_object_components_are_rejected(self):
        graph = proposal()
        graph['objects'].append(dict(copy.deepcopy(graph['objects'][0]), id='route_1_representation'))
        graph['transitions'][0]['grounding'].append(dict(component='object:route_1_representation',
            origin='proposed_abstraction', source_ref='', quote=''))
        with self.assertRaisesRegex(ValueError, 'Неоднозначный объект'): self.normalize(graph)


if __name__ == '__main__':
    unittest.main()
