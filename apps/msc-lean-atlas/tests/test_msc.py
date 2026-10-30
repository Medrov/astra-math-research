import collections
import json
from pathlib import Path
import sys
import tempfile
import unittest
from unittest import mock

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT))
from import_msc import build_graph, extract_references, normalize_code, read_rows, validate_graph
import import_msc


class MSCImportTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.graph=json.loads((ROOT/'data/msc2020.json').read_text())
        cls.nodes={node['id']:node for node in cls.graph['nodes']}
        cls.edges={(e['source'],e['target'],e['type']):e for e in cls.graph['edges']}

    def test_preserves_every_official_source_row(self):
        rows=read_rows((ROOT/'data/MSC_2020.csv').read_bytes())
        self.assertEqual(len(rows),6603)
        self.assertEqual({normalize_code(r['code']) for r in rows},set(self.nodes))
        self.assertEqual(collections.Counter(n['level'] for n in self.nodes.values()),{0:63,1:534,2:6006})
        validate_graph(self.graph)

    def test_official_csv_and_tex_exactly_agree(self):
        meta=json.loads((ROOT/'data/source-metadata.json').read_text())
        rebuilt=build_graph((ROOT/'data/MSC_2020.csv').read_bytes(),(ROOT/'data/MSC_2020.tex').read_bytes(),meta)
        self.assertEqual(rebuilt,self.graph)
        self.assertTrue(rebuilt['meta']['inventory_validation']['csv_tex_code_sets_equal'])
        self.assertTrue(rebuilt['meta']['inventory_validation']['csv_tex_literal_references_equal'])
        self.assertEqual(rebuilt['meta']['inventory_validation']['literal_reference_occurrences'],3114)

    def test_special_codes_have_real_parent(self):
        self.assertEqual(self.nodes['05-00']['parent_id'],'05')
        self.assertEqual(self.nodes['05C50']['parent_id'],'05C')
        self.assertEqual(self.nodes['05C']['parent_id'],'05')
        self.assertIsNone(self.nodes['05']['parent_id'])

    def test_related_and_conditional_references_are_distinct(self):
        self.assertIn(('00A30','03A05','see_also'),self.edges)
        self.assertIn(('00A07','00A27','classify_elsewhere'),self.edges)
        self.assertIn(('05','11T','classify_elsewhere'),self.edges)
        self.assertIn(('03C05','08A','see_also'),self.edges)

    def test_exclusion_is_not_a_related_edge(self):
        self.assertIn(('65J10','65F','avoid_classification'),self.edges)
        self.assertNotIn(('65J10','65F','see_also'),self.edges)
        self.assertIn(('16D30','16K','avoid_classification'),self.edges)
        self.assertNotIn(('33','33','related_topic'),self.edges)

    def test_range_expands_existing_roots_only(self):
        expected={'70','74','76','78','80','81','82','83','85','86'}
        found={target for source,target,kind in self.edges if source=='00A79' and kind=='classify_elsewhere'}
        self.assertEqual(found,expected)
        self.assertNotIn('71',self.nodes)

    def test_suffix_rule_is_exhaustive_but_contextual_rule_stays_unresolved(self):
        expected={code for code in self.nodes if code.endswith('-00') and code[:2]!='00'}
        found={target for source,target,kind in self.edges if source=='00A20' and kind=='see_also'}
        self.assertEqual(found,expected)
        rules=[r for r in self.graph['reference_rules'] if r['source']=='68']
        self.assertEqual(rules[0]['resolution'],'context_required')
        self.assertFalse(any(source=='68' and target.endswith('-04') for source,target,_ in self.edges))

    def test_unknown_reference_is_reported_not_invented(self):
        links,rules,unresolved=extract_references('05C50','[See also 99Z99]',set(self.nodes))
        self.assertEqual(links,[])
        self.assertEqual(unresolved[0]['raw_target'],'99Z99')

    def test_local_section_instruction_and_source_anomaly_retained(self):
        self.assertIn(('40B05','40','co_classify'),self.edges)
        self.assertIn(('78A97','78','co_classify'),self.edges)
        self.assertIn(('00A69','00A79','classify_elsewhere'),self.edges)
        self.assertEqual(self.graph['meta']['source_anomalies'][0]['code'],'00A69')

    def test_failed_refresh_preserves_prior_snapshot(self):
        names=['MSC_2020.csv','MSC_2020.tex','source-metadata.json','msc2020.json']
        with tempfile.TemporaryDirectory() as temporary:
            data=Path(temporary)
            before={name:(ROOT/'data'/name).read_bytes() for name in names}
            for name,raw in before.items():(data/name).write_bytes(raw)
            def fake_download(url,target):
                if target.suffix=='.tex':raise OSError('Simulated second-download failure')
                target.write_bytes(before['MSC_2020.csv'])
                return {'url':url,'file':target.name,'sha256':import_msc.sha256(target.read_bytes()),'retrieved_at':'test'}
            with mock.patch.object(import_msc,'DATA',data),mock.patch.object(import_msc,'download',side_effect=fake_download):
                with self.assertRaisesRegex(OSError,'second-download'):
                    import_msc.main(['--refresh'])
            self.assertEqual({name:(data/name).read_bytes() for name in names},before)


if __name__=='__main__':
    unittest.main()
