"""Meaningful boundaries: taxonomy suggestions must never become proof claims."""
import http.client
from http.server import ThreadingHTTPServer
import json
from pathlib import Path
import sys
import threading
import unittest
from unittest import mock

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT))
import analysis_engine as engine
import server


def input_pair():
    return [dict(name='A.lean',content='namespace A\ndef a : Nat := 0\nend A\n'),
            dict(name='B.lean',content='namespace B\ndef b : Nat := 1\nend B\n')]


def inspection_pair():
    return dict(status='complete',semantic_extraction=True,diagnostics=[],files=[
        dict(name='A.lean',inspection_status='compiled',declarations=[
            dict(name='A.a',kind='definition',type='Nat',dependencies=['Nat'])]),
        dict(name='B.lean',inspection_status='compiled',declarations=[
            dict(name='B.b',kind='definition',type='Nat',dependencies=['Nat'])])])


class AnalysisBoundaryTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.dataset=json.loads((ROOT/'data/msc2020.json').read_text())

    def test_catalog_counts_are_source_derived_and_complete(self):
        data=self.dataset
        by_id={n['id']:n for n in data['nodes']}
        counts=data['meta']['counts']
        self.assertEqual(len(by_id),counts['nodes'])
        self.assertEqual(len(by_id),counts['source_rows'])
        self.assertEqual(len(by_id),counts['tex_labels'])
        self.assertEqual(len(data['edges']),counts['edges'])
        self.assertTrue(all(e['source'] in by_id and e['target'] in by_id for e in data['edges']))

    def test_unknown_override_rejected_and_manual_label_is_not_proof(self):
        with self.assertRaisesRegex(ValueError,'отсутствуют'):
            engine.classify('def a := 0',[],self.dataset,['99Z99'])
        labels=engine.classify('',[],self.dataset,['05C50','05C50'])
        self.assertEqual(len(labels),1)
        self.assertEqual(labels[0]['status'],'user_confirmed')
        self.assertIsNone(labels[0]['score'])
        self.assertIn('не математическое доказательство',labels[0]['evidence'][0])

    def test_auto_classification_stays_suggested(self):
        decls=[dict(name='Demo.graphLaplacian',type='Matrix V V Rat',dependencies=['SimpleGraph.lapMatrix'])]
        labels=engine.classify('import Mathlib\ndef graphLaplacian := 0',decls,self.dataset)
        self.assertTrue(labels)
        self.assertTrue(all(label['status']=='suggested' for label in labels))

    def test_navigation_does_not_use_exclusion_shortcut(self):
        data=dict(nodes=[dict(id=x) for x in ('A','R','B','S')],edges=[
            dict(source='A',target='R',type='broader'),
            dict(source='B',target='S',type='broader'),
            dict(source='R',target='S',type='see_also'),
            dict(source='A',target='B',type='avoid_classification'),
            dict(source='A',target='B',type='classify_elsewhere'),
            dict(source='A',target='B',type='co_classify')])
        route=engine.navigation_path('A','B',data)
        self.assertEqual(route['status'],'navigation_only')
        self.assertEqual(route['nodes'],['A','R','S','B'])
        self.assertEqual(route['edge_types'],['broader','see_also','narrower'])
        reverse=engine.navigation_path('B','A',data)
        self.assertEqual(reverse['nodes'],[])
        self.assertEqual(reverse['status'],'navigation_only')
        self.assertIn('не доказывает отсутствия',reverse['explanation'])

    def test_unrelated_pair_never_claims_verified_correspondence(self):
        result=engine.assemble_analysis('test',input_pair(),inspection_pair(),self.dataset,
            targets=['A.a','B.b'],overrides=[['01'],['97']],examples=[])
        self.assertEqual(result['candidates'],[])
        self.assertNotIn('bridge_source',result)
        self.assertTrue(all(p['status']=='navigation_only' for p in result['taxonomy_paths']))

    def test_shared_dependency_and_type_are_only_candidates(self):
        left=dict(selected_declarations=[dict(name='A.x',type='(x : Nat) → Nat',dependencies=['Submodule.span','Nat.add'])])
        right=dict(selected_declarations=[dict(name='B.y',type='(x : Nat) → Nat',dependencies=['Submodule.span','Nat.mul'])])
        candidates,shared=engine.structural_candidates(left,right)
        self.assertEqual(shared,['Submodule.span'])
        self.assertEqual({c['kind'] for c in candidates},{'shared_dependency','same_printed_type'})
        self.assertTrue(all(c['status']=='candidate' for c in candidates))

    def test_literature_bridge_applicability_is_not_inherited(self):
        candidates=engine.catalog_candidates(dict(msc_matches=[dict(code='05')]),dict(msc_matches=[dict(code='15')]))
        self.assertTrue(candidates)
        self.assertTrue(all(c['status']=='candidate' and c['application_status']=='unverified' for c in candidates))

    def test_failed_inspection_preserves_original_diagnostic(self):
        inspection=inspection_pair()
        inspection.update(status='failed',semantic_extraction=False,error='Lean import missing')
        inspection['files'][0]['declarations'][0]['name']='a'
        inspection['files'][1]['declarations'][0]['name']='b'
        result=engine.assemble_analysis('test',input_pair(),inspection,self.dataset,
            targets=['A.a','B.b'],overrides=[['01'],['97']])
        self.assertEqual(result['inspection']['error'],'Lean import missing')
        self.assertTrue(all(f['target_unresolved'] for f in result['files']))
        self.assertEqual(result['candidates'],[])

    def test_real_missing_selected_declaration_is_rejected(self):
        with self.assertRaisesRegex(ValueError,'декларация не найдена'):
            engine.assemble_analysis('test',input_pair(),inspection_pair(),self.dataset,
                targets=['A.typo','B.b'],overrides=[['01'],['97']])


class APINormalizationTests(unittest.TestCase):
    def test_bad_override_shapes_and_unknown_codes_rejected_before_lean(self):
        for overrides in ([0,{}],[[],['99Z99']],[[],[{}]],[[],['05']*13]):
            with self.subTest(overrides=overrides),self.assertRaises(ValueError):
                server.normalized_inputs(dict(files=input_pair(),msc_overrides=overrides))

    def test_two_files_paths_and_targets_validated(self):
        for names in (['../A.lean','B.lean'],['/A.lean','B.lean'],['A.lean','A.lean'],
                      ['C:/A.lean','B.lean'],['C:A.lean','B.lean'],['//host/share/A.lean','B.lean']):
            pair=input_pair()
            for item,name in zip(pair,names):item['name']=name
            with self.subTest(names=names),self.assertRaises(ValueError):
                server.normalized_inputs(dict(files=pair))
        with self.assertRaises(ValueError):
            server.normalized_inputs(dict(files=input_pair(),targets=['A.a']))


class LocalHTTPBoundaryTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        class QuietHandler(server.Handler):
            def log_message(self,*args):pass
        cls.httpd=ThreadingHTTPServer(('127.0.0.1',0),QuietHandler)
        cls.thread=threading.Thread(target=cls.httpd.serve_forever,daemon=True)
        cls.thread.start()

    @classmethod
    def tearDownClass(cls):
        cls.httpd.shutdown();cls.httpd.server_close();cls.thread.join(timeout=2)

    def request(self,method,path,headers=None,body=None):
        connection=http.client.HTTPConnection('127.0.0.1',self.httpd.server_port,timeout=5)
        try:
            connection.request(method,path,body=body,headers=headers or {})
            response=connection.getresponse()
            return response.status,response.read()
        finally:connection.close()

    def test_foreign_host_get_cannot_read_saved_run(self):
        code,body=self.request('GET','/api/runs/'+'0'*32,{'Host':'example.test'})
        self.assertEqual(code,403)
        self.assertIn('localhost',body.decode())

    def test_local_get_still_works(self):
        code,body=self.request('GET','/api/runs/'+'0'*32)
        self.assertEqual(code,404)

    def test_cross_origin_post_is_rejected_without_work(self):
        with mock.patch.object(server,'submit') as submit:
            code,_=self.request('POST','/api/analyze',{'Content-Type':'application/json','Origin':'https://example.test'},json.dumps(dict(files=input_pair())))
        self.assertEqual(code,403)
        submit.assert_not_called()


if __name__=='__main__':
    unittest.main()
