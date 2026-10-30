"""Explicit, versioned arXiv HTML imports and deterministic local retrieval.

Source prose and MathML LaTeX are evidence, never a Lean certificate. No method
except import_paper performs network I/O; imports do not follow article links.
"""
from collections import Counter
from datetime import datetime, timezone
import hashlib
from html.parser import HTMLParser
import json
import math
from pathlib import Path
import re
import tempfile
import time
from urllib.error import HTTPError, URLError
from urllib.parse import quote, unquote, urljoin, urlsplit
from urllib.request import HTTPRedirectHandler, Request, build_opener


MAX_BYTES = 8 * 1024 * 1024
HTTP_TIMEOUT = 25
ALLOWED_HOSTS = {'arxiv.org', 'export.arxiv.org'}
IDENTIFIER = re.compile(r'(?P<base>(?:\d{4}\.\d{4,5}|[A-Za-z][A-Za-z.\-]*/\d{7}))(?:(?:v)(?P<version>[1-9]\d{0,4}))?\Z')
VOID = {'area', 'base', 'br', 'col', 'embed', 'hr', 'img', 'input', 'link', 'meta', 'param', 'source', 'track', 'wbr'}
SKIP = {'script', 'style', 'nav', 'aside', 'footer', 'header', 'noscript'}


class ArxivImportError(ValueError):
    """An explicit source could not be imported faithfully."""


def _sha(value):
    return hashlib.sha256(value if isinstance(value, bytes) else value.encode('utf-8')).hexdigest()


def _json(value):
    return json.dumps(value, ensure_ascii=False, sort_keys=True, indent=2).encode('utf-8')


def _clean(value):
    # Normalize prose spacing without rewriting LaTeX from MathML alttext.
    parts = re.split(r'(\$\$.*?\$\$|\$(?:\\.|[^$])*\$)', value, flags=re.S)
    return ''.join(part if index % 2 else re.sub(r'\s+', ' ', part)
                   for index, part in enumerate(parts)).strip()


def _safe_url(url):
    parsed = urlsplit(url)
    if (parsed.scheme != 'https' or parsed.hostname not in ALLOWED_HOSTS or
            parsed.username is not None or parsed.password is not None or
            parsed.port not in (None, 443) or '\\' in url or any(ord(c) < 32 for c in url)):
        raise ArxivImportError('Разрешены только HTTPS-адреса arxiv.org и export.arxiv.org.')
    return url


def parse_reference(reference):
    """Return an arXiv base ID and optional version, never an arbitrary URL."""
    if not isinstance(reference, str) or not 1 <= len(reference.strip()) <= 400:
        raise ArxivImportError('Нужен явный arXiv ID или ссылка на статью.')
    value = reference.strip()
    if '://' in value:
        _safe_url(value)
        parsed = urlsplit(value)
        if parsed.query:
            raise ArxivImportError('Ссылка на статью не должна содержать параметры запроса.')
        match = re.fullmatch(r'/(?:abs|html|pdf)/(.+?)/?', unquote(parsed.path))
        if not match:
            raise ArxivImportError('Ожидается ссылка arXiv /abs/, /html/ или /pdf/.')
        value = match.group(1)
        if value.endswith('.pdf'):
            value = value[:-4]
    elif value.lower().startswith('arxiv:'):
        value = value[6:]
    match = IDENTIFIER.fullmatch(value)
    if not match:
        raise ArxivImportError('Некорректный arXiv ID.')
    base = match.group('base')
    date = base.split('/')[-1] if '/' in base else base.split('.')[0]
    if not 1 <= int(date[2:4]) <= 12:
        raise ArxivImportError('Некорректный месяц в arXiv ID.')
    version = int(match.group('version')) if match.group('version') else None
    return base, version


class _SafeRedirect(HTTPRedirectHandler):
    max_redirections = 3
    max_repeats = 2

    def redirect_request(self, request, fp, code, msg, headers, newurl):
        _safe_url(urljoin(request.full_url, newurl))
        return super().redirect_request(request, fp, code, msg, headers, newurl)


def _fetch_html(url):
    """Bound the body and elapsed read time, checking every redirect before I/O."""
    _safe_url(url)
    request = Request(url, headers={'User-Agent': 'SHAIM-local-research/0.1 (explicit article import)',
                                    'Accept': 'text/html', 'Accept-Encoding': 'identity'})
    started = time.monotonic()
    try:
        with build_opener(_SafeRedirect()).open(request, timeout=HTTP_TIMEOUT) as response:
            _safe_url(response.geturl())
            if response.headers.get_content_type() not in ('text/html', 'application/xhtml+xml'):
                raise ArxivImportError('arXiv не вернул HTML; текст статьи не извлечён.')
            length = response.headers.get('Content-Length')
            if length and int(length) > MAX_BYTES:
                raise ArxivImportError('HTML статьи превышает допустимый размер.')
            pieces, total = [], 0
            while True:
                if time.monotonic() - started > HTTP_TIMEOUT:
                    raise ArxivImportError('Истёк срок загрузки HTML arXiv.')
                piece = response.read(min(65536, MAX_BYTES + 1 - total))
                if not piece:
                    break
                total += len(piece)
                if total > MAX_BYTES:
                    raise ArxivImportError('HTML статьи превышает допустимый размер.')
                pieces.append(piece)
            raw = b''.join(pieces)
            if not raw.strip():
                raise ArxivImportError('arXiv вернул пустой HTML.')
            return raw
    except (HTTPError, URLError, TimeoutError, OSError) as error:
        raise ArxivImportError('Не удалось получить HTML arXiv: ' + str(error)) from error


class _Node:
    def __init__(self, tag, attrs=()):
        self.tag, self.attrs, self.children = tag, dict(attrs), []

    def has(self, name):
        return name in self.attrs.get('class', '').split()


class _Tree(HTMLParser):
    def __init__(self, raw):
        super().__init__(convert_charrefs=True)
        self.root = _Node('root')
        self.stack = [self.root]
        self.count = 0
        try:
            self.feed(raw.decode('utf-8-sig', errors='strict'))
            self.close()
        except UnicodeError as error:
            raise ArxivImportError('HTML arXiv не является корректным UTF-8.') from error

    def handle_starttag(self, tag, attrs):
        self.count += 1
        if self.count > 250000 or len(self.stack) > 250:
            raise ArxivImportError('Слишком сложная структура HTML.')
        node = _Node(tag, attrs)
        self.stack[-1].children.append(node)
        if tag not in VOID:
            self.stack.append(node)

    def handle_startendtag(self, tag, attrs):
        self.handle_starttag(tag, attrs)
        if tag not in VOID:
            self.handle_endtag(tag)

    def handle_endtag(self, tag):
        for index in range(len(self.stack) - 1, 0, -1):
            if self.stack[index].tag == tag:
                del self.stack[index:]
                break

    def handle_data(self, data):
        self.stack[-1].children.append(data)


def _walk(node):
    if isinstance(node, _Node):
        yield node
        for child in node.children:
            yield from _walk(child)


def _plain(node):
    return node if isinstance(node, str) else ''.join(_plain(child) for child in node.children)


def _latex(node):
    if node.attrs.get('alttext'):
        return node.attrs['alttext'].strip()
    annotation = next((n for n in _walk(node) if n.tag == 'annotation' and
                       n.attrs.get('encoding') in ('application/x-tex', 'application/x-latex')), None)
    return _plain(annotation).strip() if annotation else None


def _render(node):
    if isinstance(node, str):
        return node
    if node.tag == 'math':
        latex = _latex(node)
        if latex is not None:
            marker = '$$' if node.attrs.get('display') == 'block' else '$'
            return marker + latex + marker
        return ''.join(_render(child) for child in node.children if not isinstance(child, _Node) or child.tag != 'annotation')
    if node.tag == 'script' and node.attrs.get('type', '').startswith('math/tex'):
        return '$' + _plain(node).strip() + '$'
    if node.tag in SKIP or node.tag in ('annotation', 'annotation-xml'):
        return ''
    if node.tag == 'br':
        return '\n'
    if node.tag == 'img':
        return node.attrs.get('alt', '')
    return ''.join(_render(child) for child in node.children)


def _metadata(raw, base, requested_version):
    root = _Tree(raw).root
    meta = {}
    for node in _walk(root):
        if node.tag == 'meta':
            key = node.attrs.get('name', node.attrs.get('property', '')).lower()
            meta.setdefault(key, []).append(node.attrs.get('content', ''))
    citation_id = (meta.get('citation_arxiv_id') or [''])[0]
    if citation_id and parse_reference(citation_id)[0] != base:
        raise ArxivImportError('arXiv вернул метаданные другой статьи.')
    versions, displayed_versions = set(), set()
    for node in _walk(root):
        candidates = []
        if node.tag == 'a':
            candidates.append(node.attrs.get('href', ''))
        if node.tag == 'meta':
            candidates.append(node.attrs.get('content', ''))
        if node.tag in ('title', 'strong'):
            candidates.append(_plain(node))
        for value in candidates:
            found = {int(v) for v in re.findall(re.escape(base) + r'v([1-9]\d*)(?!\d)', value)}
            versions.update(found)
            if node.tag in ('title', 'strong') or (node.tag == 'meta' and node.attrs.get('property') == 'og:url'):
                displayed_versions.update(found)
    if requested_version is not None:
        if requested_version not in versions or (displayed_versions and displayed_versions != {requested_version}):
            raise ArxivImportError('Метаданные не подтверждают запрошенную версию статьи.')
        version = requested_version
    elif versions:
        version = max(versions)
    else:
        raise ArxivImportError('Не удалось установить версию статьи; импорт не сохранён.')
    title = _clean((meta.get('citation_title') or [''])[0])
    authors = [_clean(v) for v in meta.get('citation_author', []) if v.strip()]
    abstract = _clean((meta.get('citation_abstract') or [''])[0])
    if not abstract:
        block = next((n for n in _walk(root) if n.tag == 'blockquote' and n.has('abstract')), None)
        abstract = re.sub(r'^Abstract:\s*', '', _clean(_render(block))) if block else ''
    if not title or not authors or not abstract:
        raise ArxivImportError('Неполные метаданные arXiv: нужны заголовок, авторы и аннотация.')
    msc_nodes = [n for n in _walk(root) if 'msc' in n.attrs.get('class', '').lower() or n.has('math-class')]
    codes = sorted(set(re.findall(r'\b\d{2}[A-Z]\d{2}\b', ' '.join(_plain(n) for n in msc_nodes))))
    return dict(arxiv_id=base, version=version, versioned_id=f'{base}v{version}',
                title=title, authors=authors, abstract=abstract, msc_codes=codes)


def _extract_article(raw, paper):
    root = _Tree(raw).root
    watermarks = [n for n in _walk(root) if n.attrs.get('id') == 'watermark-tr']
    displayed = ' '.join(_plain(n) for n in watermarks)
    if not re.search(r'arXiv:\s*' + re.escape(paper['versioned_id']) + r'(?!\d)', displayed):
        raise ArxivImportError('HTML статьи не подтверждает зафиксированную версию arXiv.')
    article = next((n for n in _walk(root) if n.tag == 'article'), None)
    if article is None:
        raise ArxivImportError('Полный HTML статьи недоступен: отсутствует article. Аннотация не подменяет статью.')
    classifications = [n for n in _walk(article) if n.has('ltx_classification')]
    codes = re.findall(r'\b\d{2}[A-Z]\d{2}\b', ' '.join(_plain(n) for n in classifications))
    paper['msc_codes'] = sorted(set(paper['msc_codes'] + codes))
    paper['msc_status'] = 'source_reported' if paper['msc_codes'] else 'not_reported_in_html'
    base_url = paper['source_urls']['html']
    sections, section_ids = [], set()
    math_nodes = [n for n in _walk(article) if n.tag == 'math']
    paper['math_extraction'] = dict(total=len(math_nodes), latex_preserved=sum(_latex(n) is not None for n in math_nodes),
                                    without_latex=sum(_latex(n) is None for n in math_nodes))

    def new_section(node, parent):
        identifier = node.attrs.get('id') or ('abstract' if node.has('ltx_abstract') else 'section-' + str(len(sections) + 1))
        if identifier in section_ids:
            raise ArxivImportError('HTML содержит повторный ID раздела.')
        section_ids.add(identifier)
        heading = next((c for c in node.children if isinstance(c, _Node) and re.fullmatch(r'h[1-6]', c.tag)), None)
        title = _clean(_render(heading)) if heading else ('Abstract' if identifier == 'abstract' else identifier)
        value = dict(id=identifier, title=title, heading=title, parent_id=parent['id'] if parent else None,
                     url=base_url + '#' + quote(identifier, safe='.-_'), paragraphs=[], equations=[], chunk_ids=[], _blocks=[])
        sections.append(value)
        return value

    document = dict(id='document', title=paper['title'], heading=paper['title'], parent_id=None,
                    url=base_url, paragraphs=[], equations=[], chunk_ids=[], _blocks=[])
    sections.append(document)
    section_ids.add('document')

    def visit(node, section):
        if not isinstance(node, _Node) or node.tag in SKIP:
            return
        if node.tag == 'section' or node.has('ltx_abstract'):
            section = new_section(node, section)
        equation = node.has('ltx_equation') or node.has('ltx_equationgroup')
        paragraph = node.tag == 'p' or node.has('ltx_bibitem')
        theorem_heading = re.fullmatch(r'h[1-6]', node.tag) and node.has('ltx_title_theorem')
        if equation or paragraph or theorem_heading:
            text = _clean(_render(node))
            if not text:
                return
            identifier = node.attrs.get('id') or section['id'] + '.block' + str(len(section['_blocks']) + 1)
            if equation:
                labels = [_clean(_render(n)) for n in _walk(node) if n.has('ltx_tag_equation')]
                item = dict(id=identifier, label=' '.join(dict.fromkeys(labels)),
                            latex=[_latex(n) for n in _walk(node) if n.tag == 'math' and _latex(n) is not None], text=text)
                section['equations'].append(item)
            else:
                section['paragraphs'].append(dict(id=identifier, text=text,
                    equation_ids=[n.attrs['id'] for n in _walk(node) if n.has('ltx_equation') and n.attrs.get('id')]))
            section['_blocks'].append((identifier, text))
            return
        for child in node.children:
            visit(child, section)

    visit(article, document)
    chunks = []
    for section in sections:
        # Preserve paragraphs/formulas, splitting only long blocks at whitespace.
        pieces = []
        for identifier, text in section.pop('_blocks'):
            while len(text) > 4500:
                cut = text.rfind(' ', 0, 4500)
                cut = cut if cut > 0 else 4500
                pieces.append((identifier, text[:cut]))
                text = text[cut:].lstrip()
            if text:
                pieces.append((identifier, text))
        groups, group, size = [], [], 0
        for piece in pieces:
            if group and size + len(piece[1]) > 4500:
                groups.append(group); group, size = [], 0
            group.append(piece); size += len(piece[1]) + 2
        if group:
            groups.append(group)
        for index, blocks in enumerate(groups, 1):
            text = '\n\n'.join(b[1] for b in blocks)
            identifier = 'arxiv:' + paper['versioned_id'] + ':' + section['id'] + ':' + str(index)
            source = dict(url=section['url'], locator=section['heading'], paper_id=paper['versioned_id'],
                          versioned_id=paper['versioned_id'], snapshot_sha256=_sha(raw), section_id=section['id'])
            chunk = dict(id=identifier, paper_id=paper['versioned_id'], versioned_id=paper['versioned_id'],
                         section_id=section['id'], section_title=section['heading'], title=paper['title'] + ' — ' + section['heading'],
                         text=text, content=text, block_ids=list(dict.fromkeys(b[0] for b in blocks)), source=source,
                         source_url=section['url'], sha256=_sha(text), snapshot_sha256=_sha(raw), msc_codes=paper['msc_codes'],
                         evidence_type='arxiv_section', extraction='html_mathml_alttext', proof_status='not_checked')
            chunks.append(chunk); section['chunk_ids'].append(identifier)
    if not chunks or not any(s['id'] not in ('document', 'abstract') and s['chunk_ids'] for s in sections):
        raise ArxivImportError('В HTML не найдены содержательные разделы статьи.')
    paper['sections'] = sections
    return chunks


class ArxivLibrary:
    def __init__(self, root):
        self.root = Path(root).resolve()
        self.root.mkdir(parents=True, exist_ok=True)

    def _folder(self, reference):
        base, version = parse_reference(reference)
        if version is None:
            raise ArxivImportError('Для локального чтения нужна зафиксированная версия arXiv.')
        return self.root / (base.replace('/', '_') + 'v' + str(version))

    def import_paper(self, reference):
        base, version = parse_reference(reference)
        if version and self._folder(reference).exists():
            return self.get_paper(f'{base}v{version}')
        abstract_url = 'https://arxiv.org/abs/' + base + (f'v{version}' if version else '')
        abstract_raw = _fetch_html(abstract_url)
        paper = _metadata(abstract_raw, base, version)
        pinned = paper['versioned_id']
        if self._folder(pinned).exists():
            return self.get_paper(pinned)
        if version is None:
            abstract_raw = _fetch_html('https://arxiv.org/abs/' + pinned)
            paper = _metadata(abstract_raw, base, paper['version'])
        paper['source_urls'] = dict(abstract='https://arxiv.org/abs/' + pinned,
                                    html='https://arxiv.org/html/' + pinned, pdf='https://arxiv.org/pdf/' + pinned)
        article_raw = _fetch_html(paper['source_urls']['html'])
        chunks = _extract_article(article_raw, paper)
        chunks_raw = _json(chunks)
        paper.update(fetched_at=datetime.now(timezone.utc).isoformat(), import_status='ready',
                     sha256=_sha(article_raw), snapshot_sha256=dict(abstract_html=_sha(abstract_raw), article_html=_sha(article_raw), chunks=_sha(chunks_raw)),
                     limitations=['HTML article text is source evidence, not a verified theorem or a novelty assessment.',
                                  'Whitespace is normalized; MathML alttext/TeX annotations are retained without OCR.'])
        if paper['math_extraction']['without_latex']:
            paper['limitations'].append('Some MathML expressions lack TeX: their presentation text is retained, with possible loss of structure.')
        folder = self._folder(pinned)
        with tempfile.TemporaryDirectory(prefix='.import-', dir=self.root) as temporary:
            staging = Path(temporary) / 'snapshot'
            staging.mkdir()
            for name, content in [('abstract.html', abstract_raw), ('article.html', article_raw), ('chunks.json', chunks_raw), ('paper.json', _json(paper))]:
                (staging / name).write_bytes(content)
            try:
                staging.rename(folder)
            except OSError:
                if not folder.is_dir():
                    raise
        return self.get_paper(pinned)

    def get_paper(self, versioned_id):
        folder = self._folder(versioned_id)
        try:
            paper = json.loads((folder / 'paper.json').read_text(encoding='utf-8'))
            for filename, key in [('abstract.html', 'abstract_html'), ('article.html', 'article_html'), ('chunks.json', 'chunks')]:
                if _sha((folder / filename).read_bytes()) != paper['snapshot_sha256'][key]:
                    raise ArxivImportError('Хеш сохранённого источника arXiv не совпадает: ' + filename)
            base, version = parse_reference(versioned_id)
            if paper['versioned_id'] != f'{base}v{version}':
                raise ArxivImportError('Сохранённая версия arXiv не совпадает с запросом.')
            paper['chunks'] = json.loads((folder / 'chunks.json').read_text(encoding='utf-8'))
            # Derive provenance for older snapshots without rewriting pinned files.
            for chunk in paper['chunks']:
                chunk.setdefault('snapshot_sha256', paper['snapshot_sha256']['article_html'])
                chunk['source'].setdefault('snapshot_sha256', paper['snapshot_sha256']['article_html'])
                chunk['source'].setdefault('versioned_id', paper['versioned_id'])
            return paper
        except FileNotFoundError as error:
            raise ArxivImportError('Эта версия arXiv ещё не импортирована локально.') from error

    def list_papers(self):
        result = []
        for path in sorted(self.root.glob('*/paper.json')):
            if path.parent.name.startswith('.'):
                continue
            paper = json.loads(path.read_text(encoding='utf-8'))
            loaded = self.get_paper(paper['versioned_id'])
            result.append({key: value for key, value in loaded.items() if key not in ('chunks', 'sections')})
        return result

    def evidence(self, paper_id, section_ids=None, limit=12, max_chars=24000):
        self._limit(limit)
        if isinstance(max_chars, bool) or not isinstance(max_chars, int) or not 1 <= max_chars <= 200000:
            raise ArxivImportError('Некорректный бюджет текста источников.')
        paper = self.get_paper(paper_id)
        if section_ids is not None and (not isinstance(section_ids, list) or any(not isinstance(v, str) for v in section_ids)):
            raise ArxivImportError('section_ids должен быть списком ID разделов.')
        selected = set(section_ids or [])
        if selected - {s['id'] for s in paper['sections']}:
            raise ArxivImportError('Указан неизвестный раздел статьи.')
        results, remaining = [], max_chars
        for chunk in paper['chunks']:
            if selected and chunk['section_id'] not in selected:
                continue
            if len(chunk['text']) > remaining:
                continue
            results.append(chunk); remaining -= len(chunk['text'])
            if len(results) == limit:
                break
        return results

    @staticmethod
    def _limit(limit):
        if isinstance(limit, bool) or not isinstance(limit, int) or not 1 <= limit <= 100:
            raise ArxivImportError('limit должен быть целым числом от 1 до 100.')

    def search(self, query, paper_ids, limit=6):
        self._limit(limit)
        if not isinstance(query, str) or len(query) > 20000:
            raise ArxivImportError('Некорректный поисковый запрос.')
        if not isinstance(paper_ids, list) or len(paper_ids) > 20 or any(not isinstance(p, str) for p in paper_ids):
            raise ArxivImportError('paper_ids должен быть списком не более 20 версий статей.')
        docs = [chunk for key in sorted(set(paper_ids)) for chunk in self.get_paper(key)['chunks']]
        terms = sorted(set(re.findall(r'[^\W_]+', query.casefold())))
        if not terms:
            return docs[:limit]
        tokens = [Counter(re.findall(r'[^\W_]+', (d['section_title'] + ' ' + d['text']).casefold())) for d in docs]
        average = sum(sum(t.values()) for t in tokens) / max(len(tokens), 1)
        frequency = {term: sum(term in t for t in tokens) for term in terms}
        ranked = []
        for doc, counts in zip(docs, tokens):
            length = sum(counts.values())
            score = sum(math.log(1 + (len(docs) - frequency[t] + .5) / (frequency[t] + .5)) *
                        counts[t] * 2.2 / (counts[t] + 1.2 * (.25 + .75 * length / max(average, 1))) for t in terms if counts[t])
            if score:
                ranked.append(dict(doc, retrieval_score=round(score, 12), retrieval_backend='arxiv_local_bm25'))
        return sorted(ranked, key=lambda d: (-d['retrieval_score'], d['id']))[:limit]
