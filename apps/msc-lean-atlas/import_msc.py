#!/usr/bin/env python3
"""Import the complete official MSC2020 export without inventing math relations.

The upstream .csv is actually a Windows-1252, tab-separated three-column file.
Its node inventory is cross-checked against every label in the official TeX.
Run without arguments to rebuild from preserved sources; --refresh downloads a
new snapshot and replaces its provenance. Network failures never replace files.
"""
import argparse
import collections
import csv
from datetime import datetime, timezone
import hashlib
import io
import json
from pathlib import Path
import re
import tempfile
import urllib.request


ROOT = Path(__file__).resolve().parent
DATA = ROOT / "data"
SOURCE_URL = "https://msc2020.org/MSC_2020.csv"
TEX_URL = "https://msc2020.org/MSC_2020.tex"
LICENSE_URL = "https://creativecommons.org/licenses/by-nc-sa/4.0/"
CODE_PATTERN = r"\d{2}(?:-[0-9X]{2}|[A-Z](?:\d{2}|xx))"
CODE_RE = re.compile(r"(?<![A-Za-z0-9])" + CODE_PATTERN + r"(?![A-Za-z0-9])")
RANGE_RE = re.compile(r"(?P<start>\d{2}-XX)\s+through\s+(?P<end>\d{2}-XX)", re.I)
BLOCK_RE = re.compile(r"\[[^\]]*\]|\\+\{[Ff]or .*?(?:\\+\}|$)", re.S)
SUFFIX_RE = re.compile(r"classification number\s+(?:--|–|—|-)(\d{2})", re.I)


def utc_now():
    return datetime.now(timezone.utc).isoformat()


def sha256(raw):
    return hashlib.sha256(raw).hexdigest()


def atomic_write(path, raw):
    path.parent.mkdir(parents=True, exist_ok=True)
    with tempfile.NamedTemporaryFile(dir=path.parent, delete=False) as stream:
        temporary = Path(stream.name)
        stream.write(raw)
    temporary.replace(path)


def download(url, target):
    request = urllib.request.Request(url, headers={"User-Agent": "MSC-Lean-Atlas/0.1 (local research prototype)"})
    with urllib.request.urlopen(request, timeout=60) as response:
        raw = response.read()
        headers = {key.lower(): value for key, value in response.headers.items()
                   if key.lower() in {"etag", "last-modified", "content-type"}}
    if len(raw) < 100_000:
        raise ValueError("Downloaded source is unexpectedly short: " + url)
    atomic_write(target, raw)
    return {"url": url, "file": target.name, "sha256": sha256(raw),
            "bytes": len(raw), "retrieved_at": utc_now(), "http": headers}


def normalize_code(raw):
    """Normalize only MSC's documented group/root shorthand, not arbitrary text."""
    raw = raw.strip()
    if re.fullmatch(r"\d{2}-XX", raw):
        return raw[:2]
    if re.fullmatch(r"\d{2}[A-Z]xx", raw):
        return raw[:3]
    if re.fullmatch(r"\d{2}[A-Z]\d{2}|\d{2}-\d{2}|\d{2}[A-Z]|\d{2}", raw):
        return raw
    raise ValueError("Invalid MSC code: " + raw)


def node_level(code):
    if len(code) == 2:
        return 0
    if len(code) == 3:
        return 1
    return 2


def parent_id(code):
    if len(code) == 2:
        return None
    if len(code) == 3 or "-" in code:
        return code[:2]
    return code[:3]


def display_text(raw):
    """Keep mathematical TeX intact, only unescape layout braces and spacing."""
    unescaped = re.sub(r"\\+([{}])", r"\1", raw)
    return re.sub(r"\s+", " ", unescaped.replace("~", " ")).strip()


def read_rows(raw):
    rows = list(csv.DictReader(io.StringIO(raw.decode("cp1252")), delimiter="\t"))
    if not rows or set(rows[0]) != {"code", "text", "description"}:
        raise ValueError("Unexpected official export columns")
    if any(None in row or any(row[key] is None for key in row) for row in rows):
        raise ValueError("Malformed source row")
    return rows


def reference_context(description, start, end):
    for match in BLOCK_RE.finditer(description):
        if match.start() <= start and match.end() >= end:
            return match.group(), match.start(), match.end()
    # The export also has explicit references in parentheses (exceptions and
    # one mention of nonlinear versions), outside the usual reference blocks.
    left = description.rfind("(", 0, start)
    right = description.find(")", end)
    if left >= 0 and right >= end:
        return description[left:right + 1], left, right + 1
    return description, 0, len(description)


def reference_type(context):
    lower = context.lower()
    if "do not use" in lower or "except as in" in lower:
        return "avoid_classification"
    if "if not placed" in lower:
        return "classification_alternative"
    if "should also be assigned" in lower or "must also be assigned" in lower:
        return "co_classify"
    if re.search(r"\\+\{for\b", lower) or "use more specific entries" in lower:
        return "classify_elsewhere"
    if "see" in lower or "consider also" in lower:
        return "see_also"
    return "related_topic"


def extract_references(source, description, node_ids):
    """Return explicit navigational links plus unresolved/context-dependent rules.

    Broad ranges expand only to existing roots. '...xx' references stay at the
    group level, never expand to an asserted mathematical link to every leaf.
    A contextual suffix (e.g. '-04 in that area') is retained as a rule because
    it has no single target until a paper's subject has been supplied.
    """
    links, rules, unresolved = [], [], []
    ranges = list(RANGE_RE.finditer(description))
    covered = set()
    for match in ranges:
        context, _, _ = reference_context(description, *match.span())
        first, last = int(match['start'][:2]), int(match['end'][:2])
        targets = sorted(code for code in node_ids if len(code) == 2 and first <= int(code) <= last)
        rule = {"source": source, "type": reference_type(context),
                "pattern": match.group(), "resolution": "existing_roots_in_range",
                "targets": targets, "reference_text": display_text(context)}
        rules.append(rule)
        for target in targets:
            links.append({"source": source, "target": target, "type": rule['type'],
                          "reference_text": rule['reference_text'], "raw_target": match.group(),
                          "expansion": "root_range"})
        covered.update(range(match.start(), match.end()))
    for match in CODE_RE.finditer(description):
        if match.start() in covered:
            continue
        raw_target = match.group()
        target = normalize_code(raw_target)
        context, _, _ = reference_context(description, *match.span())
        # 33-XX explains its own scope in prose. It is not a cross-reference.
        if target == source and not re.search(r"see|assigned|classification", context.lower()):
            continue
        if target not in node_ids:
            unresolved.append({"source": source, "raw_target": raw_target,
                               "reference_text": display_text(context), "reason": "target_missing_from_source_inventory"})
            continue
        links.append({"source": source, "target": target, "type": reference_type(context),
                      "reference_text": display_text(context), "raw_target": raw_target})
    for match in SUFFIX_RE.finditer(description):
        context, _, _ = reference_context(description, *match.span())
        suffix = "-" + match.group(1)
        if "other sections" in context.lower():
            targets = sorted(code for code in node_ids if code.endswith(suffix) and code[:2] != source[:2])
            rule = {"source": source, "type": reference_type(context), "pattern": "*" + suffix,
                    "resolution": "existing_suffix_codes_in_other_sections", "targets": targets,
                    "reference_text": display_text(context)}
            rules.append(rule)
            for target in targets:
                links.append({"source": source, "target": target, "type": rule['type'],
                              "reference_text": rule['reference_text'], "raw_target": "*" + suffix,
                              "expansion": "suffix_in_other_sections"})
        else:
            rule = {"source": source, "type": reference_type(context), "pattern": "*" + suffix,
                    "resolution": "context_required", "reference_text": display_text(context),
                    "reason": "The source says 'in that area'; the area's code is supplied by the classified work."}
            rules.append(rule)
            unresolved.append(rule)
    # A local instruction with no literal code still has a precise section scope.
    for match in BLOCK_RE.finditer(description):
        if "this section" in match.group().lower() and not CODE_RE.search(match.group()):
            links.append({"source": source, "target": source[:2], "type": reference_type(match.group()),
                          "reference_text": display_text(match.group()), "raw_target": "this section",
                          "target_scope": "another_classification_in_section"})
    return links, rules, unresolved


def validate_graph(graph):
    nodes = graph['nodes']
    lookup = {node['id']: node for node in nodes}
    if len(lookup) != len(nodes):
        raise ValueError("Duplicate normalized codes")
    edge_ids = set()
    for node in nodes:
        parent = node['parent_id']
        if parent is not None and parent not in lookup:
            raise ValueError("Missing parent: " + node['id'])
        visited = {node['id']}
        while parent is not None:
            if parent in visited:
                raise ValueError("Hierarchy cycle: " + node['id'])
            visited.add(parent)
            parent = lookup[parent]['parent_id']
    for edge in graph['edges']:
        if edge['id'] in edge_ids:
            raise ValueError("Duplicate edge ID")
        edge_ids.add(edge['id'])
        if edge['source'] not in lookup or edge['target'] not in lookup:
            raise ValueError("Dangling edge: " + edge['id'])
        if edge['type'] == 'broader' and lookup[edge['source']]['parent_id'] != edge['target']:
            raise ValueError("Hierarchy edge disagrees with parent")


def build_graph(raw_csv, raw_tex, provenance):
    rows = read_rows(raw_csv)
    raw_codes = [row['code'] for row in rows]
    if len(set(raw_codes)) != len(raw_codes):
        raise ValueError("Duplicate source codes")
    tex_text = raw_tex.decode('utf-8')
    tex_labels = re.findall(r"\\label\{(" + CODE_PATTERN + r")\}", tex_text)
    if len(tex_labels) != len(set(tex_labels)):
        raise ValueError("Duplicate TeX labels")
    if set(tex_labels) != set(raw_codes):
        raise ValueError("Official CSV and TeX inventories differ: " + json.dumps({
            "csv_only": sorted(set(raw_codes)-set(tex_labels)), "tex_only": sorted(set(tex_labels)-set(raw_codes))}))
    # Independently audit literal source→target references against TeX hyperlinks,
    # including references located inside section headings before their labels.
    starts = list(re.finditer(r"\\(?:sub)?section\*\{\s*(?P<header>"+CODE_PATTERN+r")|\\item\s*\[(?P<item>"+CODE_PATTERN+r")\]", tex_text))
    tex_references = collections.Counter()
    for i, match in enumerate(starts):
        source = match['header'] or match['item']
        segment = tex_text[match.start():starts[i+1].start() if i+1<len(starts) else len(tex_text)]
        for target in re.findall(r"\\hyperref\[("+CODE_PATTERN+r")\]", segment):
            tex_references[(source,target)] += 1
    csv_references = collections.Counter()
    for row in rows:
        for match in CODE_RE.finditer(row['description']):
            context, _, _ = reference_context(row['description'], *match.span())
            if match.group()==row['code'] and not re.search(r"see|assigned|classification",context.lower()):
                continue
            csv_references[(row['code'],match.group())] += 1
    if csv_references != tex_references:
        raise ValueError('Literal cross-references in official CSV and TeX disagree: '+repr({
            'csv_only':list((csv_references-tex_references).items()),
            'tex_only':list((tex_references-csv_references).items())}))
    nodes = []
    source_anomalies = []
    for index, row in enumerate(rows, 2):
        code = normalize_code(row['code'])
        nodes.append({"id": code, "code": code, "source_code": row['code'],
                      "title": display_text(row['text']), "description": display_text(row['description']),
                      "raw_title": row['text'], "raw_description": row['description'],
                      "parent_id": parent_id(code), "level": node_level(code), "source_row": index})
        if re.search(r"\\+\{[Ff]or", row['description']) and not re.search(r"\\+\}", row['description']):
            source_anomalies.append({"code": code, "kind": "unclosed_reference_brace",
                                     "handling": "Reference parsed through end of row; original text preserved."})
    node_ids = {node['id'] for node in nodes}
    edges = [{"id": "broader:"+node['id']+":"+node['parent_id'], "source": node['id'],
              "target": node['parent_id'], "type": "broader"}
             for node in nodes if node['parent_id'] is not None]
    by_key, rules, unresolved = {}, [], []
    for node, row in zip(nodes, rows):
        links, local_rules, local_unresolved = extract_references(node['id'], row['description'], node_ids)
        rules.extend(local_rules)
        unresolved.extend(local_unresolved)
        for link in links:
            key = (link['source'], link['target'], link['type'])
            if key not in by_key:
                by_key[key] = dict(link, id=link['type']+":"+link['source']+":"+link['target'],
                                   reference_texts=[link['reference_text']], raw_targets=[link['raw_target']])
            else:
                existing = by_key[key]
                if link['reference_text'] not in existing['reference_texts']:
                    existing['reference_texts'].append(link['reference_text'])
                if link['raw_target'] not in existing['raw_targets']:
                    existing['raw_targets'].append(link['raw_target'])
    edges.extend(sorted(by_key.values(), key=lambda edge: edge['id']))
    level_counts = collections.Counter(node['level'] for node in nodes)
    type_counts = collections.Counter(edge['type'] for edge in edges)
    counts = {"nodes": len(nodes), "edges": len(edges), "roots": level_counts[0],
              "groups": level_counts[1], "leaves": level_counts[2],
              "hyphen_codes": sum(bool(re.fullmatch(r'\d{2}-\d{2}', node['id'])) for node in nodes),
              "hierarchy_edges": type_counts['broader'], "cross_reference_edges": len(by_key),
              "edge_types": dict(sorted(type_counts.items())), "reference_rules": len(rules),
              "unresolved_references": len(unresolved), "source_rows": len(rows),
              "tex_labels": len(tex_labels)}
    graph = {"meta": {"version": "MSC2020", "schema_version": 1,
                       "source_url": SOURCE_URL, "source_sha256": sha256(raw_csv),
                       "retrieved_at": provenance['csv']['retrieved_at'], "sources": provenance,
                       "license": "CC BY-NC-SA 4.0", "license_url": LICENSE_URL,
                       "attribution": "MSC2020, jointly maintained and published by Mathematical Reviews (American Mathematical Society) and zbMATH. Graph conversion by the SHAIM project.",
                       "changes": "Normalized category IDs; derived child-to-parent edges; typed and expanded explicit navigation references. Original source files and wording retained.",
                       "counts": counts,
                       "published_website_counts": {"roots": 63, "groups": 529, "leaves": 6022},
                       "count_note": f"The official downloaded CSV and TeX agree exactly on {len(nodes)} entries: {level_counts[0]} roots, {level_counts[1]} groups and {level_counts[2]} terminal codes. The prose on msc2020.org states 63/529/6022. This graph preserves the downloaded inventory and does not add or remove codes to match the prose totals.",
                       "inventory_validation": {"csv_tex_code_sets_equal": True, "all_rows_preserved": True,
                                                "csv_tex_literal_references_equal": True,
                                                "literal_reference_occurrences": sum(csv_references.values())},
                       "reference_semantics": "All edges describe classification/navigation instructions, not mathematical equivalences, theorem dependencies or proven transfers.",
                       "edge_type_descriptions": {
                           "broader": "Child category belongs to parent category.",
                           "see_also": "Related or additionally suggested classification; preserve the original qualifier.",
                           "classify_elsewhere": "Conditional instruction to classify the described subject in another category.",
                           "co_classify": "Instruction to also assign a code in the referenced section, not evidence of a mathematical bridge.",
                           "avoid_classification": "Explicit exclusion/do-not-use instruction; not a suggested search path.",
                           "classification_alternative": "Conditional alternative ('if not placed in ...').",
                           "related_topic": "An explicit subject reference outside the standard reference brackets."},
                       "source_anomalies": source_anomalies, "unresolved_references": unresolved},
             "nodes": nodes, "edges": edges, "reference_rules": rules}
    validate_graph(graph)
    return graph


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--refresh', action='store_true', help='Download a new official source snapshot.')
    args = parser.parse_args(argv)
    DATA.mkdir(parents=True, exist_ok=True)
    metadata_path = DATA/'source-metadata.json'
    provenance = json.loads(metadata_path.read_text()) if metadata_path.exists() else {}
    sources = {}
    # Stage both downloads and validate them together. A failed download or
    # mismatching upstream release must leave the usable old snapshot untouched.
    with tempfile.TemporaryDirectory(prefix='.msc-import-',dir=DATA) as staging:
        for key, url, filename in [('csv', SOURCE_URL, 'MSC_2020.csv'), ('tex', TEX_URL, 'MSC_2020.tex')]:
            path = DATA/filename
            if args.refresh or not path.exists():
                path = Path(staging)/filename
                provenance[key] = download(url,path)
            elif key not in provenance:
                # Bootstrap provenance of a source downloaded during setup. mtime
                # is a filesystem observation, not a fabricated HTTP timestamp.
                raw = path.read_bytes()
                provenance[key] = {"url": url, "file": filename, "sha256": sha256(raw),
                                   "bytes": len(raw), "retrieved_at": datetime.fromtimestamp(path.stat().st_mtime, timezone.utc).isoformat(),
                                   "timestamp_basis": "saved download file modification time"}
            sources[key] = path.read_bytes()
            if sha256(sources[key]) != provenance[key]['sha256']:
                raise ValueError('Preserved source hash differs from provenance: '+filename)
        graph = build_graph(sources['csv'],sources['tex'],provenance)
        for key in ['csv','tex']:
            atomic_write(DATA/provenance[key]['file'],sources[key])
        atomic_write(metadata_path, (json.dumps(provenance,ensure_ascii=False,indent=2)+'\n').encode())
        atomic_write(DATA/'msc2020.json', (json.dumps(graph,ensure_ascii=False,indent=2)+'\n').encode())
    print(json.dumps(graph['meta']['counts'],ensure_ascii=False))
    print(graph['meta']['count_note'])


if __name__ == '__main__':
    main()
