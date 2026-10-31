"""Metadata/linkage checks only; synthetic snapshots do not claim Lean verification."""
import hashlib
import json
from pathlib import Path
import sys
import tempfile
import unittest
from unittest.mock import Mock, patch

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))

import lean_service
import research_structure as structure
import research_structure_sources as sources


class PreparedExampleMetadataTests(unittest.TestCase):
    def setUp(self):
        self.service = structure.StructureResearchMixin()
        self.store = Mock()
        self.store.list_sources.return_value = []
        self.service.structure_store = Mock(return_value=self.store)

    def test_metadata_links_exact_article_section_and_declared_theorem(self):
        with patch.object(lean_service, '_prepare', side_effect=AssertionError('must not compile')):
            result = self.service.structure_sources()
        self.assertEqual(len(result['examples']), 2)
        self.assertEqual({item['id'] for item in result['examples']},
                         {'arxiv_2610_38474_graph_subtraction', 'published_associator_laplacian'})
        example = result['examples'][0]
        self.assertEqual(example['id'], 'arxiv_2610_38474_graph_subtraction')
        self.assertEqual(example['arxiv_id'], '2610.38474')
        self.assertEqual(example['versioned_id'], '2610.38474v1')
        self.assertEqual(example['section_id'], 'S9.SS1')
        self.assertEqual(example['recommended_target'], 'Arxiv261038474.subtract_restore')
        source = (ROOT / 'research_fixtures/Arxiv261038474.lean').read_text(encoding='utf-8-sig')
        self.assertIn('namespace Arxiv261038474', source)
        self.assertIn('theorem subtract_restore ', source)
        self.assertEqual(example['source_sha256'], hashlib.sha256(source.encode('utf-8')).hexdigest())
        self.assertIn('не формализация всей статьи', example['scope_note'])
        self.assertNotIn('content', example)
        self.assertNotIn('inspection', example)
        self.store.create.assert_not_called()

    def test_import_payload_matches_catalogue_hash_and_provenance(self):
        example = self.service.structure_sources()['examples'][0]
        self.service.import_structure_source({'example_id': example['id']})
        payload = self.store.create.call_args.args[0]
        self.assertEqual(hashlib.sha256(payload['content'].encode('utf-8')).hexdigest(), example['source_sha256'])
        provenance = payload['provenance']
        for key in ('versioned_id', 'section_id', 'recommended_target'):
            self.assertEqual(provenance[key], example[key])
        self.assertEqual(provenance['example_id'], example['id'])
        self.assertEqual(provenance['kind'], 'prepared_formalization')
        self.assertEqual(provenance['scope'], example['scope_note'])
        # Preserve old provenance consumers as the explicit fields are added.
        self.assertEqual(provenance['arxiv_id'], example['versioned_id'])
        self.assertEqual(provenance['section'], example['section_id'])
        self.assertEqual(provenance['url'], 'https://arxiv.org/html/2610.38474v1#S9.SS1')

    def test_windows_newlines_and_bom_hash_imported_content_not_raw_bytes(self):
        normalized = 'import Init\nnamespace Arxiv261038474\ntheorem subtract_restore : True := by trivial\nend Arxiv261038474\n'
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            fixture = root / 'research_fixtures/Arxiv261038474.lean'
            fixture.parent.mkdir()
            fixture.write_bytes(b'\xef\xbb\xbf' + normalized.replace('\n', '\r\n').encode('utf-8'))
            with patch.object(structure, 'ROOT', root):
                example = self.service.structure_sources()['examples'][0]
                self.service.import_structure_source({'example_id': example['id']})
                payload = self.store.create.call_args.args[0]
                self.assertEqual(payload['content'], normalized)
                self.assertEqual(example['source_sha256'], hashlib.sha256(normalized.encode('utf-8')).hexdigest())
                fixture.write_bytes((normalized + '-- actual source change\n').encode('utf-8'))
                changed = self.service.structure_sources()['examples'][0]
                self.assertNotEqual(changed['source_sha256'], example['source_sha256'])

    def test_unknown_example_never_reaches_source_creation(self):
        with self.assertRaisesRegex(ValueError, 'Неизвестный'):
            self.service.import_structure_source({'example_id': 'another_article'})
        self.store.create.assert_not_called()


class SourceSummaryMetadataTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.store = sources.StructureSourceStore(self.temp.name, 'metadata-test-env')
        self.source_id = 'a' * 32
        self.folder = Path(self.temp.name) / self.source_id
        self.folder.mkdir()
        self.content = 'import Init\ntheorem Example.result : True := by trivial\n'
        (self.folder / 'StructureInput.lean').write_bytes(self.content.encode('utf-8'))
        self.snapshot = dict(source_id=self.source_id, title='Synthetic metadata', name='Example.lean',
            status='ready', source_sha256=sources._sha(self.content), environment_fingerprint='metadata-test-env',
            created_at='2026-10-31T00:00:00+00:00', provenance={'kind': 'test_fixture', 'versioned_id': '2610.38474v1'},
            inspection={'success': True}, declarations=[{'name': 'Example.result', 'kind': 'theorem', 'type': 'True'}])
        self._write_snapshot()

    def _write_snapshot(self):
        snapshot = dict(self.snapshot, snapshot_sha256=sources._sha(sources._json(self.snapshot)))
        (self.folder / 'snapshot.json').write_text(json.dumps(snapshot), encoding='utf-8')

    def test_list_exposes_provenance_and_hash_without_content_or_compilation(self):
        with patch.object(lean_service, '_prepare', side_effect=AssertionError('must not compile')):
            summary = self.store.list_sources()[0]
        self.assertEqual(summary['provenance'], self.snapshot['provenance'])
        self.assertEqual(summary['source_sha256'], sources._sha(self.content))
        self.assertEqual(summary['status'], 'ready')
        for hidden in ('content', 'inspection', 'declarations'):
            self.assertNotIn(hidden, summary)

    def test_legacy_snapshot_without_provenance_is_still_listed(self):
        self.snapshot.pop('provenance')
        self._write_snapshot()
        summary = self.store.list_sources()[0]
        self.assertEqual(summary['status'], 'ready')
        self.assertIsNone(summary['provenance'])

    def test_changed_source_or_environment_is_not_advertised_as_ready(self):
        other = sources.StructureSourceStore(self.temp.name, 'changed-environment')
        self.assertEqual(other.list_sources()[0]['status'], 'stale')
        (self.folder / 'StructureInput.lean').write_bytes((self.content + '-- changed\n').encode('utf-8'))
        summary = self.store.list_sources()[0]
        self.assertEqual(summary['status'], 'stale')
        self.assertNotIn('source_sha256', summary)
        with self.assertRaisesRegex(ValueError, 'Содержимое'):
            self.store.select(self.source_id, 'Example.result')


if __name__ == '__main__':
    unittest.main()
