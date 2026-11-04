"""Source-reported MSC from retained HTML; no network or model execution."""
import copy
import hashlib
import json
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch

import research_arxiv as arxiv


PAPER_ID = '2403.19691v1'
ABS = b'''<html><head><title>[2403.19691v1] Determinants</title>
<meta name="citation_arxiv_id" content="2403.19691">
<meta name="citation_title" content="Determinants"><meta name="citation_author" content="Author">
<meta name="citation_abstract" content="A determinant equality."></head><body></body></html>'''


def article(classification='', extra=''):
    # The ordinary paragraph shape is the one missed in the real Sidi import.
    return ('''<html><body><div id="watermark-tr">arXiv:2403.19691v1</div><article>
        <h1>Determinants</h1>''' + classification + '''
        <section id="S1"><h2>Theorem 2</h2><p>If m=n, equality holds.</p></section>'''
        + extra + '</article></body></html>').encode('utf-8')


class ArxivMSCMetadataTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.library = arxiv.ArxivLibrary(self.temp.name)

    def imported(self, body='', *, extra='', abstract=ABS):
        raw = article(body, extra)
        with patch.object(arxiv, '_fetch_html', side_effect=[abstract, raw]) as fetch:
            paper = self.library.import_paper(PAPER_ID)
        self.assertEqual(fetch.call_count, 2)
        return paper, raw

    def test_sidi_plain_body_label_is_source_reported_with_pinned_quote(self):
        paper, raw = self.imported('<p id="p1.1">Mathematics Subject Classification 2020: 15A15</p>')
        self.assertEqual(paper['msc_codes'], ['15A15'])
        self.assertEqual(paper['msc_status'], 'source_reported')
        self.assertEqual(paper['msc_extraction_version'], arxiv.MSC_EXTRACTION_VERSION)
        self.assertEqual(paper['msc_evidence'], [dict(codes=['15A15'], source_document='article_html',
            source_sha256=hashlib.sha256(raw).hexdigest(), locator='p1.1',
            quote='Mathematics Subject Classification 2020: 15A15')])

    def test_label_variants_inline_markup_and_primary_secondary_lists(self):
        cases = [
            '<p>Mathematics Subject Classification 2020:15A15</p>',
            '<p>2020 Mathematics Subject Classification: Primary 15A15; Secondary 15A45.</p>',
            '<p><b>Mathematics Subject Classification</b> (2020): <span>15A15</span>, 15A45</p>',
            '<div>MSC2020: 15a15 (primary), 15A45 (secondary)</div>',
            '<p>MSC 2010: 15A15 and 15A45</p>',
            '<div class="ltx_classification"><h6>2020 Mathematics Subject Classification</h6>Primary 15A15; Secondary 15A45.</div>',
        ]
        for html in cases:
            with self.subTest(html=html):
                fields = arxiv._msc_fields(arxiv._msc_evidence(arxiv._Tree(article(html)).root, 'article_html', 'a'*64))
                self.assertEqual(fields['msc_status'], 'source_reported')
                self.assertIn('15A15', fields['msc_codes'])
                self.assertEqual(len(fields['msc_evidence']), 1)
                if '15A45' in html: self.assertIn('15A45', fields['msc_codes'])

    def test_explicit_abstract_fields_and_body_codes_merge_without_duplicates(self):
        abstract = ABS.replace(b'</head>', b'<meta name="citation_msc_class" content="15A15; 15A23"></head>')
        paper, _ = self.imported('<p>MSC2020: 15A15, 15A45</p>', abstract=abstract)
        self.assertEqual(paper['msc_codes'], ['15A15', '15A23', '15A45'])
        self.assertEqual({e['source_document'] for e in paper['msc_evidence']}, {'abstract_html','article_html'})
        abs_evidence = next(e for e in paper['msc_evidence'] if e['source_document']=='abstract_html')
        self.assertEqual(abs_evidence['source_sha256'], hashlib.sha256(abstract).hexdigest())

    def test_existing_arxiv_math_class_table_is_supported(self):
        abstract = ABS.replace(b'</body>', b'<table><tr><td>MSC classes:</td><td class="math-class">15A15; 15A45</td></tr></table></body>')
        paper, _ = self.imported(abstract=abstract)
        self.assertEqual(paper['msc_codes'], ['15A15','15A45'])
        self.assertEqual(paper['msc_status'], 'source_reported')

    def test_source_reported_broad_codes_are_retained_and_years_are_not_codes(self):
        abstract = ABS.replace(b'</body>', b'<table><tr><td>MSC classes:</td><td class="msc-classes">15</td></tr></table></body>')
        paper, _ = self.imported('<p>Mathematics Subject Classification 2020: 15A, 15A15</p>', abstract=abstract)
        self.assertEqual(paper['msc_codes'], ['15', '15A', '15A15'])
        self.assertEqual(len(paper['msc_evidence']), 2)
        self.assertEqual(paper['msc_evidence'][0]['quote'], 'MSC classes: 15')
        self.assertEqual(paper['msc_evidence'][0]['codes'], ['15'])
        self.assertNotIn('20', paper['msc_codes'])

    def test_classification_years_are_never_split_into_broad_codes(self):
        for year in ('2020', '2010', '1991'):
            for label in (f'{year} Mathematics Subject Classification:', f'MSC ({year}):', 'MSC: Primary ' + year):
                html=article('<p>' + label + ' 15A15</p>')
                fields=arxiv._msc_fields(arxiv._msc_evidence(arxiv._Tree(html).root,'article_html','a'*64))
                with self.subTest(label=label):
                    self.assertFalse({'20','10','19','91'} & set(fields['msc_codes']))
                    if not label.startswith('MSC: Primary'):self.assertEqual(fields['msc_codes'],['15A15'])

    def test_reference_numbers_in_local_text_are_not_broad_codes(self):
        for tail in (' [12]', '. See references [12] and [35].', ' <span class="ltx_cite">[12]</span>'):
            html=article('<p>MSC: 15A15' + tail + '</p>')
            fields=arxiv._msc_fields(arxiv._msc_evidence(arxiv._Tree(html).root,'article_html','a'*64))
            with self.subTest(tail=tail):self.assertEqual(fields['msc_codes'],['15A15'])

    def test_codes_in_prose_references_scripts_and_quoted_papers_are_not_metadata(self):
        fake = '''<p>This discussion mentions 15A15 and MSC 2020: 15A45.</p>
        <p>MSC is an abbreviation, not a classification field. 35Q55</p>
        <script>Mathematics Subject Classification 2020: 15A15</script>
        <style>.msc { content: 'MSC: 15A15'; }</style>
        <nav><p>MSC: 15A15</p></nav>
        <section id="bib"><p>MSC: 15A15</p></section>
        <section class="ltx_bibliography"><div class="ltx_classification">Primary 15A15</div></section>
        <p class="ltx_cite">MSC: 15A15</p>
        <blockquote><p>MSC: 15A15</p></blockquote>'''
        paper, _ = self.imported(extra=fake)
        self.assertEqual(paper['msc_codes'], [])
        self.assertEqual(paper['msc_status'], 'not_found_in_retained_html')
        self.assertEqual(paper['msc_evidence'], [])

    def test_unlabelled_code_is_not_found_not_claimed_absent_from_the_paper(self):
        paper, _ = self.imported('<p>A theorem related to 15A15.</p>')
        self.assertEqual(paper['msc_codes'], [])
        self.assertEqual(paper['msc_status'], 'not_found_in_retained_html')
        self.assertEqual(paper['msc_evidence'], [])

    def test_explicit_label_with_unparsed_classification_is_unknown(self):
        for body in ('<p>Mathematics Subject Classification 2020: unreadable</p>',
                     '<div class="ltx_classification">15Axx</div>'):
            with self.subTest(body=body):
                fields = arxiv._msc_fields(arxiv._msc_evidence(arxiv._Tree(article(body)).root, 'article_html', 'a'*64))
                self.assertEqual(fields['msc_status'], 'unknown')
                self.assertEqual(fields['msc_codes'], [])
                self.assertEqual(len(fields['msc_evidence']), 1)

    def test_scan_stops_at_prose_and_rejects_embedded_or_unbounded_codes(self):
        for body, expected in [
            ('<p>MSC: 15A15. See the reference with code 35Q55.</p>', ['15A15']),
            ('<p>MSC: prefix15A15suffix; 35Q55</p>', []),
            ('<p>MSC: 15A15 ' + 'unrelated text ' * 100 + '35Q55</p>', []),
        ]:
            with self.subTest(body=body[:80]):
                fields = arxiv._msc_fields(arxiv._msc_evidence(arxiv._Tree(article(body)).root, 'article_html', 'a'*64))
                self.assertEqual(fields['msc_codes'], expected)
                self.assertTrue(all(len(e['quote'])<=1000 for e in fields['msc_evidence']))

    def test_cached_import_get_list_refresh_overlay_without_rewriting_any_snapshot(self):
        paper, _ = self.imported('<p id="msc-label">Mathematics Subject Classification 2020: 15A15</p>')
        folder = Path(self.temp.name)/PAPER_ID
        # Recreate the historical cache's missed metadata, keeping retained HTML.
        old = json.loads((folder/'paper.json').read_text(encoding='utf-8'))
        old.update(msc_codes=[],msc_status='not_reported_in_html')
        old.pop('msc_evidence');old.pop('msc_extraction_version')
        chunks = json.loads((folder/'chunks.json').read_text(encoding='utf-8'))
        for chunk in chunks:chunk['msc_codes']=[]
        chunk_bytes=arxiv._json(chunks)
        old['snapshot_sha256']['chunks']=hashlib.sha256(chunk_bytes).hexdigest()
        (folder/'chunks.json').write_bytes(chunk_bytes)
        (folder/'paper.json').write_bytes(arxiv._json(old))
        historical_run=Path(self.temp.name)/'historical-run.json'
        historical_run.write_bytes(arxiv._json(dict(paper_manifest=copy.deepcopy(old),evidence=copy.deepcopy(chunks))))
        paths=[*folder.iterdir(),historical_run]
        before={path:path.read_bytes() for path in paths}
        with patch.object(arxiv, '_fetch_html', side_effect=AssertionError('cached reading must not fetch')):
            current=self.library.get_paper(PAPER_ID)
            self.assertEqual(self.library.import_paper(PAPER_ID), current)
            listed=self.library.list_papers()[0]
            self.assertEqual(listed['msc_codes'], ['15A15'])
            self.assertEqual(listed['msc_evidence'], current['msc_evidence'])
        self.assertEqual(current['msc_codes'], ['15A15'])
        self.assertEqual(current['msc_status'], 'source_reported')
        self.assertEqual(current['snapshot_sha256'], old['snapshot_sha256'])
        self.assertEqual(current['chunks'], chunks)
        self.assertEqual({path:path.read_bytes() for path in paths}, before)

    def test_stale_or_forged_cached_msc_is_not_trusted_over_html(self):
        self.imported('<p>No classification supplied here.</p>')
        folder=Path(self.temp.name)/PAPER_ID
        old=json.loads((folder/'paper.json').read_text(encoding='utf-8'))
        old.update(msc_codes=['35Q55'],msc_status='source_reported',msc_evidence=[dict(codes=['35Q55'])])
        (folder/'paper.json').write_bytes(arxiv._json(old))
        current=self.library.get_paper(PAPER_ID)
        self.assertEqual(current['msc_codes'], [])
        self.assertEqual(current['msc_status'], 'not_found_in_retained_html')

    def test_html_digest_is_checked_before_refreshing_metadata(self):
        self.imported('<p>MSC: 15A15</p>')
        path=Path(self.temp.name)/PAPER_ID/'article.html'
        path.write_bytes(path.read_bytes().replace(b'15A15', b'35Q55'))
        with self.assertRaisesRegex(arxiv.ArxivImportError, 'Хеш'):
            self.library.get_paper(PAPER_ID)


if __name__ == '__main__':
    unittest.main()
