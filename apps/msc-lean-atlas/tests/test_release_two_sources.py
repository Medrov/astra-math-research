"""Prepared-source release coverage; no generated research or model calls."""
import copy
import json
from pathlib import Path
import sys
import tempfile
import unittest
from unittest.mock import Mock, patch

ROOT=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT))
import lean_service
import research_lean as lean
import research_structure as structure
import research_structure_sources as sources
import research_project_library as library
import research_published_example as published


class PreparedPublishedSourceGuards(unittest.TestCase):
    def setUp(self):
        self.mixin=structure.StructureResearchMixin()
        self.store=Mock();self.store.list_sources.return_value=[]
        self.mixin.structure_store=Mock(return_value=self.store)

    def test_catalog_has_two_distinct_exact_sources_without_compiling(self):
        with patch.object(lean_service,'_prepare',side_effect=AssertionError('metadata must not compile')):
            rows=self.mixin.structure_sources()['examples']
        self.assertEqual([x['id'] for x in rows],['arxiv_2610_38474_graph_subtraction',published.CASE_ID])
        self.assertEqual(rows[0]['recommended_target'],'Arxiv261038474.subtract_restore')
        self.assertEqual(rows[1]['recommended_target'],published.TARGET)
        self.assertEqual(rows[1]['source_sha256'],sources._sha(sources.prepared_published_source()))
        self.assertIn('не формализация всего препринта',rows[1]['scope_note'])
        self.assertNotIn('arxiv_id',rows[1])
        self.assertNotIn('content',rows[1])
        self.assertNotIn('inspection',rows[1])

    def test_prepared_route_uses_canonical_loader_not_browser_supplied_content(self):
        self.mixin.import_structure_source(dict(example_id=published.CASE_ID,content='import Evil\n',prepared_example_id='forged'))
        self.store.create.assert_not_called()
        args,kwargs=self.store.create_prepared.call_args
        self.assertEqual(args,(published.CASE_ID,))
        self.assertEqual(kwargs['provenance']['kind'],'prepared_published_reuse')
        self.assertEqual(kwargs['provenance']['recommended_target'],published.TARGET)
        self.assertIn(published.PUBLICATION_COMMIT,kwargs['provenance']['url'])
        self.assertNotIn('content',kwargs)

    def test_upload_cannot_enable_preset_project_import_exception(self):
        content=sources.prepared_published_source()
        with tempfile.TemporaryDirectory() as directory, patch.object(lean_service,'_prepare') as prepare:
            store=sources.StructureSourceStore(directory,'test')
            for payload in [dict(content=content),dict(content=content,prepared_example_id=published.CASE_ID),
                            dict(content=content,provenance=dict(kind='prepared_published_reuse',example_id=published.CASE_ID)),
                            dict(content='import MathResearch.AlbertMatrix\n')]:
                with self.subTest(payload=payload.keys()),self.assertRaises(ValueError):store.create(payload)
            prepare.assert_not_called()
            self.assertEqual(list(Path(directory).iterdir()),[])

    def test_payload_marker_content_and_dependency_pin_are_checked(self):
        content=sources.prepared_published_source()
        payload=dict(source_id='a'*32,content=content,source_sha256=sources._sha(content),
                     prepared_example_id=published.CASE_ID,environment_fingerprint='env',
                     selected_declaration=dict(name=published.TARGET,kind='theorem',type=published.STATEMENT))
        self.assertEqual(sources.validate_library_payload(payload)['prepared_example_id'],published.CASE_ID)
        changed=content+'\n-- changed\n'
        for value in [{**payload,'content':changed,'source_sha256':sources._sha(changed)},
                      {**payload,'prepared_example_id':'other'},
                      {k:v for k,v in payload.items() if k!='prepared_example_id'}]:
            with self.subTest(value=value.get('prepared_example_id')),self.assertRaises(ValueError):sources.validate_library_payload(value)
        with patch.object(library,'fingerprint',return_value='0'*64),self.assertRaisesRegex(ValueError,'изменились'):
            sources.validate_library_payload(payload)


@unittest.skipUnless(Path(lean_service.default_context()['lean']).is_file(),'Prepared Lean unavailable')
class RealPreparedPublishedSource(unittest.TestCase):
    def test_import_select_preflight_and_reuse_compile_fresh_exact_dependencies(self):
        from research_service import ResearchService, atomic
        with tempfile.TemporaryDirectory(prefix='release-published-source-') as directory:
            root=Path(directory)
            service=ResearchService(root/'service',recover=False)
            store=sources.StructureSourceStore(root/'sources',service.environment_fingerprint)
            service.structure_store=lambda:store
            try:
                with patch('research_codex.run_task',side_effect=AssertionError('No model calls')):
                    imported=service.import_structure_source(dict(example_id=published.CASE_ID))
                    self.assertEqual(imported['status'],'ready',json.dumps(imported,ensure_ascii=False))
                    self.assertEqual(imported['inspection']['project_library']['fingerprint'],library.fingerprint())
                    self.assertEqual(len(imported['inspection']['project_library']['sources']),4)
                    self.assertEqual(imported['inspection']['print_axioms']['exit_code'],0)
                    selected=store.select(imported['source_id'],published.TARGET)
                    run=service.create(dict(purpose='structure',mode='multi',source_id=imported['source_id'],
                                           target=published.TARGET,budget=dict(max_calls=4,timeout_seconds=60)),start=False)
                    self.assertEqual(run['contract']['source_library']['prepared_example_id'],published.CASE_ID)
                    self.assertEqual(run['usage']['calls'],0)
                pin=sources.PIN_PREFIX+selected['source_sha256']+'\n'
                target='PublishedReuse.energy'
                source='import StructureInput\n'+pin+lean.theorem_header(target,published.STATEMENT)+'by\n  exact Bridge.energy_correspondence\n'
                proof=lean.verify_candidate(source,target,root/'proof',published.STATEMENT,source_library=selected)
                self.assertTrue(proof['success'],json.dumps(proof,ensure_ascii=False))
                self.assertEqual(proof['project_library']['status'],'complete')
                self.assertTrue(proof['project_library']['fresh_local_build'])
                self.assertEqual(proof['source_usage']['status'],'related')
                self.assertTrue(proof['source_usage']['selected_theorem_used'])
                self.assertEqual(proof['audit']['status'],'passed')
                self.assertEqual(proof['source_library']['audit']['status'],'passed')
                self.assertEqual(proof['print_axioms']['exit_code'],0)
                self.assertIn(target,proof['print_axioms']['stdout'])
                task=dict(imports=['StructureInput'],prelude=pin,target=target,statement=published.STATEMENT,
                          required_obligations=[dict(id='reuse',target=target,statement=published.STATEMENT,expected_outcome='proved')])
                preflight=lean.verify_contract(task,root/'preflight',source_library=selected)
                self.assertTrue(preflight['well_typed'],json.dumps(preflight,ensure_ascii=False))
                self.assertFalse(preflight['proof_checked'])
                self.assertEqual(preflight['project_library']['status'],'complete')
                self.assertNotEqual(proof['workspace'],preflight['workspace'])
                for report in (imported['inspection'],proof,preflight):
                    self.assertEqual(len(report['project_library']['sources']),4)
                    self.assertTrue(all(entry['exit_code']==0 for entry in report['diagnostics']))
                # Source staleness is checked on read; unrelated uploaded input is unchanged.
                with patch.object(library,'fingerprint',return_value='0'*64):
                    self.assertEqual(store.list_sources()[0]['status'],'stale')
                    with self.assertRaises(ValueError):store.select(imported['source_id'],published.TARGET)
                atomic(ROOT/'verification/release-two-sources-2026-11-01.json',
                       dict(kind='prepared_published_reuse_test_not_new_discovery',source_id=imported['source_id'],
                            source_sha256=imported['source_sha256'],inspection=imported['inspection'],
                            proof=proof,contract_preflight=preflight,model_calls=0))
            finally:
                service.pool.shutdown(wait=True)


if __name__=='__main__':unittest.main()
