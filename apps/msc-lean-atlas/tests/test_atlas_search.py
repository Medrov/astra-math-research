"""Deterministic local coverage controls; no models and no mathematical proof."""
import copy
import json
from pathlib import Path
import sys
import tempfile
import unittest

sys.path.insert(0,str(Path(__file__).resolve().parents[1]))
import research_atlas as atlas


SOURCE=dict(source_sha256='a'*64,selected_declaration=dict(type='Ring homomorphism quotient ideal'))
PROFILE=dict(summary='Quotient ring transfer',objects=['polynomial'],operations=['evaluation'],
             assumptions=['commutative ring'],conclusion_shape='factorization',mechanism='ideal quotient homomorphism')


def inventory():
    return dict(nodes=[dict(id='13',parent_id=None,level=0,title='Commutative algebra'),
        dict(id='13A',parent_id='13',level=1,title='General commutative rings'),
        dict(id='13A15',parent_id='13A',level=2,title='Ideals and multiplicative ideal theory in commutative rings'),
        dict(id='54',parent_id=None,level=0,title='General topology'),
        dict(id='54C25',parent_id='54',level=2,title='Embedding')])


def record(identifier='ideal'):
    return dict(id=identifier,name='Ideal.Quotient.lift',module='Mathlib.RingTheory.Ideal.Quotient.Defs',
        title='Ideal quotient lift',statement='An ideal quotient ring homomorphism',source_sha256='b'*64,
        msc_codes=[],type_status='textual_unverified')


class AtlasSearchTests(unittest.TestCase):
    def test_actual_inventory_every_code_is_accounted_and_no_parent_inheritance(self):
        inv=json.loads(atlas.ATLAS_PATH.read_text(encoding='utf-8'))
        snapshot=atlas.screen(inv,[record()],SOURCE,PROFILE)
        result=atlas.overview(snapshot,atlas.new_progress(snapshot))
        self.assertEqual(result['summary']['total_codes'],6603)
        self.assertEqual(result['summary']['level_counts'],dict(roots=63,groups=534,leaves=6006))
        self.assertEqual(result['summary']['queried_codes'],6603)
        self.assertEqual(len({n['code'] for n in result['nodes']}),6603)
        self.assertFalse(result['summary']['deep_complete'])
        self.assertEqual(result['summary']['proof_verified'],0)
        self.assertTrue(all(n['proof_status']=='not_checked' for n in result['nodes']))
        self.assertTrue(all(n['corpus_status']!='mapped' for n in result['nodes']))

    def test_many_to_many_provenance_requires_pin_and_retains_unclassified(self):
        doc=record();doc['msc_mappings']=[
            dict(code='13A15',provenance_kind='curated',evidence='reviewed module scope',source_sha256='b'*64),
            dict(code='54',provenance_kind='source_reported',evidence='article metadata',source_sha256='c'*64)]
        doc['msc_codes']=['54C25']
        value=atlas.screen(inventory(),[doc],SOURCE,PROFILE)
        nodes={n['code']:n for n in value['nodes']}
        self.assertEqual(nodes['13A15']['corpus_status'],'mapped')
        self.assertNotEqual(nodes['13']['corpus_status'],'mapped')
        self.assertNotEqual(nodes['54']['corpus_status'],'mapped')
        self.assertEqual(nodes['54C25']['corpus_status'],'inferred_only')
        self.assertIn('ideal',value['global_channel']['pool_ids'])
        self.assertEqual(len({x['code'] for x in value['source_links'] if x['source_id']=='ideal'})>=2,True)

    def test_missing_corpus_is_not_a_negative_and_timeout_is_partial(self):
        missing=atlas.screen(inventory(),[],SOURCE,PROFILE,corpus_manifest=dict(status='not_built'))
        overview=atlas.overview(missing,atlas.new_progress(missing))
        self.assertEqual(overview['summary']['queried_codes'],0)
        self.assertEqual(overview['summary']['status'],'partial')
        self.assertTrue(all(n['query_status']=='unavailable' for n in overview['nodes']))
        ticks=iter([0,2])
        timed=atlas.screen(inventory(),[record()],SOURCE,PROFILE,
            options=dict(local_timeout_seconds=1),clock=lambda:next(ticks))
        self.assertFalse(timed['local_queries_complete'])
        self.assertEqual(timed['interruption'],'local_budget_exhausted')
        with tempfile.TemporaryDirectory() as temp:
            value=atlas.local_screen(SOURCE,PROFILE,index_path=Path(temp)/'missing.sqlite')
            self.assertFalse((Path(temp)/'missing.sqlite').exists())
            self.assertFalse(value['local_queries_complete'])

    def test_zero_matches_complete_local_search_without_inventing_bridge(self):
        value=atlas.screen(inventory(),[],SOURCE,PROFILE,corpus_manifest=dict(status='ready',declarations=0))
        result=atlas.overview(value,atlas.new_progress(value))
        self.assertEqual(result['summary']['status'],'complete')
        self.assertEqual(result['summary']['candidates_found'],0)
        self.assertEqual(result['summary']['corpus_gaps'],5)
        self.assertEqual(result['queue'],[])
        self.assertEqual(result['summary']['proof_verified'],0)

    def test_determinism_caps_and_corruption(self):
        docs=[dict(record(str(i)),statement='ideal quotient '+str(i)) for i in range(20)]
        a=atlas.screen(inventory(),docs,SOURCE,PROFILE,options=dict(coarse_limit=2))
        b=atlas.screen(inventory(),list(reversed(docs)),SOURCE,PROFILE,options=dict(coarse_limit=2))
        self.assertEqual(a,b)
        node=next(n for n in a['nodes'] if n['code']=='13A15')
        self.assertEqual(len(node['pool_ids']),2);self.assertEqual(node['pool_truncated'],18)
        before=copy.deepcopy(a);progress=atlas.new_progress(a);before_progress=copy.deepcopy(progress)
        result=atlas.overview(a,progress)
        exposed=next(n for n in result['nodes'] if n['code']=='13A15')
        self.assertEqual((exposed['source_count'],exposed['retained_count'],exposed['pool_truncated']),(20,2,18))
        self.assertTrue(all(n['source_count']==n['retained_count']+n['pool_truncated'] for n in result['nodes']))
        self.assertEqual(a,before);self.assertEqual(progress,before_progress)
        bad=copy.deepcopy(a);bad['nodes'][0]['title']='tampered'
        with self.assertRaisesRegex(ValueError,'checksum'):atlas.verify_snapshot(bad)
        progress=atlas.new_progress(a);progress['queue'].pop()
        with self.assertRaisesRegex(ValueError,'inventory'):atlas.verify_progress(progress,a)
        with self.assertRaisesRegex(ValueError,'Duplicate'):atlas.screen(inventory(),[record(),record()],SOURCE,PROFILE)
        for options in (dict(max_deep_routes=0),dict(pool_limit=True),dict(invented=1)):
            with self.subTest(options=options),self.assertRaises(ValueError):atlas.normalize_options(options)

    def test_diverse_queue_and_continuation_keep_completed_results(self):
        records=[record(),dict(record('embedding'),title='Topology embedding',statement='continuous embedding topology')]
        snap=atlas.screen(inventory(),records,SOURCE,PROFILE)
        progress=atlas.new_progress(snap)
        self.assertEqual(progress['queue'][0]['id'],'global_unclassified')
        bycode={n['code']:n for n in snap['nodes']}
        roots=[bycode[x['code']]['root_code'] for x in progress['queue'][1:3]]
        self.assertEqual(len(set(roots)),2)
        progress['queue'][0].update(status='complete',candidate_count=0,semantic_status='model_assessed')
        progress['queue'][1].update(status='active')
        resumed=atlas.new_progress(snap,progress)
        self.assertEqual(resumed['queue'][0]['status'],'complete')
        self.assertEqual(resumed['queue'][1]['status'],'pending')
        self.assertEqual(progress['queue'][1]['status'],'active')

    def test_msc_cross_references_do_not_rank_as_topic_but_history_stays_searchable(self):
        inv=inventory()
        inv['nodes'].append(dict(id='13-03',parent_id='13',level=2,title='History of commutative algebra',
            description='History of commutative algebra [Consider also classification numbers from Section 01-XX]'))
        doc=dict(record('history'),title='History of commutative algebra',statement='history commutative algebra')
        profile=dict(PROFILE,mechanism='commutative numbers')
        snap=atlas.screen(inv,[doc],SOURCE,profile)
        node=next(n for n in snap['nodes'] if n['code']=='13-03')
        self.assertEqual(node['priority'],1)  # Only commutative; the reference's numbers is not a topic.
        self.assertTrue({'history','commutative','algebra'}<=set(node['query']['tokens']))
        self.assertFalse({'number','classification','section','consider'}&set(node['query']['tokens']))
        self.assertIn('history',node['pool_ids'])
        self.assertIn('msc_13-03',[row['id'] for row in atlas.new_progress(snap)['queue']])
        self.assertEqual(atlas.overview(snap,atlas.new_progress(snap))['summary']['queried_codes'],len(inv['nodes']))
        for reference in ('[Consider also classification numbers from Section01-XX]',
                          '[See also 11B39, 13A15]',
                          '[Should also be assigned at least one other classification number in Section 49-XX]'):
            with self.subTest(reference=reference):
                self.assertEqual(atlas.tokens(atlas._topic_text('History of numbers '+reference)),{'history','number'})
        self.assertEqual(atlas._topic_text('Numbers [greater than zero]'),'Numbers [greater than zero]')


if __name__=='__main__':unittest.main()
