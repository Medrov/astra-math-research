import hashlib
import io
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch
from email.message import Message
from urllib.request import Request

import research_arxiv as arxiv


ABS = b'''<!doctype html><html><head>
<title>[2610.38474v1] A finite inverse</title>
<meta name="citation_arxiv_id" content="2610.38474">
<meta name="citation_title" content="A finite inverse">
<meta name="citation_author" content="Author, A."><meta name="citation_author" content="Author, B.">
<meta name="citation_abstract" content="We study polynomial maps.">
</head><body><a href="/abs/2610.38474v1">this version</a></body></html>'''

ARTICLE = br'''<!doctype html><html><body>
<div id="watermark-tr">arXiv:2610.38474v1 [math.AG]</div>
<article class="ltx_document"><h1>A finite inverse</h1>
<div class="ltx_classification"><h6>2020 Mathematics Subject Classification</h6>Primary 14R10; Secondary 14F42.</div>
<div class="ltx_abstract" id="abstract1"><h6>Abstract</h6><p>We study polynomial maps.</p></div>
<nav><p>This navigation must not become evidence.</p></nav>
<section id="S1"><h2>1. Finite inverse</h2>
<div id="S1.Thm1" class="ltx_theorem"><h6 class="ltx_title_theorem">Lemma 1</h6>
<p id="S1.p1">If <math alttext="N^2=0"><mi>N</mi><annotation encoding="application/x-tex">duplicated</annotation></math>, then the inverse is finite.</p>
<table id="S1.E1" class="ltx_equation"><tr><td><span class="ltx_tag_equation">(1)</span></td><td>
<math display="block" alttext="(I-N)(I+N)=I"><mi>IGNORED PRESENTATION</mi></math></td></tr></table></div>
<section id="S1.SS1"><h3>1.1 Polynomial consequence</h3>
<p id="S1.SS1.p1">A polynomial automorphism <math><semantics><mi>T</mi><annotation encoding="application/x-tex">T(x,y)=(x,y+x^2)</annotation></semantics></math>.</p>
<script>alert('untrusted')</script></section></section>
<section id="S2"><h2>2. Other topic</h2><p>Elliptic curves and topology.</p></section>
</article></body></html>'''


class ArxivTests(unittest.TestCase):
    def setUp(self):
        self.temporary = tempfile.TemporaryDirectory()
        self.library = arxiv.ArxivLibrary(self.temporary.name)

    def tearDown(self):
        self.temporary.cleanup()

    def imported(self):
        with patch.object(arxiv, '_fetch_html', side_effect=[ABS, ARTICLE]) as fetch:
            paper = self.library.import_paper('https://arxiv.org/abs/2610.38474v1')
        self.assertEqual(fetch.call_count, 2)
        return paper

    def test_modern_legacy_ids_and_official_urls(self):
        for value, expected in [('2610.38474', ('2610.38474', None)), ('arXiv:0704.0001v2', ('0704.0001', 2)),
                ('math.AG/0601001v3', ('math.AG/0601001', 3)),
                ('https://export.arxiv.org/pdf/hep-th/9901001v2.pdf', ('hep-th/9901001', 2)),
                ('https://arxiv.org/html/2610.38474v1#S9.SS3', ('2610.38474', 1))]:
            with self.subTest(value=value):
                self.assertEqual(arxiv.parse_reference(value), expected)

    def test_rejects_external_localhost_credentials_ports_and_paths(self):
        for value in ['https://arxiv.org.evil.test/abs/2610.38474v1', 'https://127.0.0.1/abs/2610.38474v1',
                      'http://arxiv.org/abs/2610.38474v1', 'https://user@arxiv.org/abs/2610.38474v1',
                      'https://arxiv.org:8443/abs/2610.38474v1', 'https://arxiv.org/search/2610.38474',
                      'https://arxiv.org/abs/2610.38474?url=http://localhost', '../2610.38474v1',
                      'https://arxiv.org/abs/%2e%2e/2610.38474', '2613.38474', '2610.38474v0']:
            with self.subTest(value=value), patch.object(arxiv, '_fetch_html') as fetch:
                with self.assertRaises(ValueError):
                    self.library.import_paper(value)
                fetch.assert_not_called()

    def test_redirect_is_checked_before_fetching_destination(self):
        handler = arxiv._SafeRedirect()
        request = Request('https://arxiv.org/abs/2610.38474v1')
        for destination in ['https://localhost/x', 'https://evil.test/', 'http://arxiv.org/x', 'https://arxiv.org@127.0.0.1/x']:
            with self.subTest(destination=destination), self.assertRaises(arxiv.ArxivImportError):
                handler.redirect_request(request, None, 302, 'Moved', {}, destination)
        redirect = handler.redirect_request(request, None, 302, 'Moved', {}, 'https://export.arxiv.org/abs/2610.38474v1')
        self.assertEqual(redirect.host, 'export.arxiv.org')

    def test_snapshot_metadata_formulas_and_stable_sections(self):
        paper = self.imported()
        self.assertEqual(paper['authors'], ['Author, A.', 'Author, B.'])
        self.assertEqual(paper['msc_codes'], ['14F42', '14R10'])
        self.assertEqual(paper['math_extraction'], {'total':3, 'latex_preserved':3, 'without_latex':0})
        section = next(s for s in paper['sections'] if s['id'] == 'S1')
        self.assertEqual(section['equations'][0]['label'], '(1)')
        self.assertEqual(section['equations'][0]['latex'], ['(I-N)(I+N)=I'])
        text = '\n'.join(c['text'] for c in paper['chunks'])
        self.assertIn('$N^2=0$', text)
        self.assertIn('$$' + '(I-N)(I+N)=I' + '$$', text)
        self.assertIn('$T(x,y)=(x,y+x^2)$', text)
        for unwanted in ['duplicated', 'IGNORED PRESENTATION', 'alert(', 'navigation must']:
            self.assertNotIn(unwanted, text)
        self.assertEqual(paper['sha256'], hashlib.sha256(ARTICLE).hexdigest())
        self.assertEqual(self.library.get_paper(paper['versioned_id']), paper)
        folder = Path(self.temporary.name) / '2610.38474v1'
        self.assertEqual((folder/'article.html').read_bytes(), ARTICLE)

    def test_pinned_cache_and_local_operations_never_fetch(self):
        paper = self.imported()
        with patch.object(arxiv, '_fetch_html', side_effect=AssertionError('network forbidden')):
            self.assertEqual(self.library.import_paper(paper['versioned_id']), paper)
            self.assertEqual(len(self.library.list_papers()), 1)
            self.assertTrue(self.library.search('inverse', [paper['versioned_id']]))
            self.assertTrue(self.library.evidence(paper['versioned_id']))

    def test_unversioned_import_resolves_and_refetches_pinned_metadata(self):
        with patch.object(arxiv, '_fetch_html', side_effect=[ABS, ABS, ARTICLE]) as fetch:
            paper = self.library.import_paper('2610.38474')
        self.assertEqual(paper['versioned_id'], '2610.38474v1')
        self.assertEqual([call.args[0] for call in fetch.call_args_list], [
            'https://arxiv.org/abs/2610.38474', 'https://arxiv.org/abs/2610.38474v1', 'https://arxiv.org/html/2610.38474v1'])

    def test_wrong_metadata_or_fulltext_version_cannot_be_saved(self):
        for metadata, html in [(ABS.replace(b'2610.38474', b'2610.38475'), ARTICLE),
                               (ABS, ARTICLE.replace(b'2610.38474v1', b'2610.38474v2')),
                               (ABS.replace(b'[2610.38474v1]', b'[2610.38474v2]'), ARTICLE)]:
            with self.subTest(), patch.object(arxiv, '_fetch_html', side_effect=[metadata, html]):
                with self.assertRaises(arxiv.ArxivImportError):
                    self.library.import_paper('2610.38474v1')
                self.assertEqual(self.library.list_papers(), [])

    def test_missing_html_is_explicit_failure_not_abstract_substitution(self):
        with patch.object(arxiv, '_fetch_html', side_effect=[ABS, b'<html>HTML unavailable</html>']):
            with self.assertRaises(arxiv.ArxivImportError):
                self.library.import_paper('2610.38474v1')
        self.assertEqual(list(Path(self.temporary.name).iterdir()), [])

    def test_snapshot_tampering_is_detected(self):
        self.imported()
        (Path(self.temporary.name)/'2610.38474v1'/'article.html').write_bytes(b'changed')
        with self.assertRaisesRegex(arxiv.ArxivImportError, 'Хеш'):
            self.library.get_paper('2610.38474v1')

    def test_section_evidence_has_exact_text_and_respects_budget(self):
        paper = self.imported()
        evidence = self.library.evidence(paper['versioned_id'], ['S1'], max_chars=1000)
        self.assertTrue(evidence)
        self.assertTrue(all(e['section_id'] == 'S1' for e in evidence))
        for item in evidence:
            self.assertEqual(item['text'], item['content'])
            self.assertEqual(item['sha256'], hashlib.sha256(item['text'].encode()).hexdigest())
            self.assertEqual(item['source_url'], 'https://arxiv.org/html/2610.38474v1#S1')
            self.assertEqual(item['snapshot_sha256'], hashlib.sha256(ARTICLE).hexdigest())
            self.assertEqual(item['source']['versioned_id'], paper['versioned_id'])
        self.assertEqual(self.library.evidence(paper['versioned_id'], ['S1'], max_chars=1), [])
        with self.assertRaises(arxiv.ArxivImportError):
            self.library.evidence(paper['versioned_id'], ['missing'])

    def test_search_is_deterministic_and_excludes_nonmatching_chunks(self):
        paper = self.imported()
        result = self.library.search('finite inverse', [paper['versioned_id']], limit=1)
        self.assertEqual(result[0]['section_id'], 'S1')
        self.assertEqual(result, self.library.search('finite inverse', [paper['versioned_id']], limit=1))
        self.assertEqual(self.library.search('unfindable', [paper['versioned_id']]), [])
        self.assertEqual(self.library.search('finite', []), [])
        with self.assertRaises(arxiv.ArxivImportError):
            self.library.get_paper('2610.38474')

    def test_math_tex_whitespace_is_preserved_and_fallback_is_disclosed(self):
        html = ARTICLE.replace(b'alttext="N^2=0"', b'alttext="N^2 =  0"')
        html = html.replace(b'<mi>T</mi><annotation encoding="application/x-tex">T(x,y)=(x,y+x^2)</annotation>', b'<mi>T</mi>')
        with patch.object(arxiv, '_fetch_html', side_effect=[ABS, html]):
            paper = self.library.import_paper('2610.38474v1')
        self.assertIn('$N^2 =  0$', ''.join(c['text'] for c in paper['chunks']))
        self.assertEqual(paper['math_extraction']['without_latex'], 1)
        self.assertTrue(any('lack TeX' in value for value in paper['limitations']))

    def test_http_rejects_oversized_or_non_html_response(self):
        class Response(io.BytesIO):
            def geturl(self):
                return 'https://arxiv.org/html/2610.38474v1'
        for content_type, length, body in [('application/pdf', '2', b'xx'), ('text/html', str(arxiv.MAX_BYTES+1), b'x'),
                                          ('text/html', None, b'123456')]:
            response = Response(body)
            response.headers = Message()
            response.headers['Content-Type'] = content_type
            if length:
                response.headers['Content-Length'] = length
            with self.subTest(content_type=content_type, length=length), patch.object(arxiv, 'build_opener') as opener:
                opener.return_value.open.return_value = response
                with patch.object(arxiv, 'MAX_BYTES', 5), self.assertRaises(arxiv.ArxivImportError):
                    arxiv._fetch_html('https://arxiv.org/html/2610.38474v1')


if __name__ == '__main__':
    unittest.main()
