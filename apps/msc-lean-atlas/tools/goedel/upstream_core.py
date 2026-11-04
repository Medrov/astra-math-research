"""Selected Goedel-Architect core, adapted for data-only SHAIM blueprints.

Apache-2.0. See LICENSE, NOTICE and upstream-manifest.json.
This module never creates or compiles unfinished Lean declarations.
"""
from __future__ import annotations
import re
import textwrap
from dataclasses import dataclass, field


# Upstream graph.py:44
@dataclass
class BlueprintNode:
    name: str                        # "factorial_decomposition"
    kind: str                        # "theorem"|"lemma"|"def"|"abbrev"|"structure"|"noncomputable_def"|"inductive"|"class"
    is_target: bool                  # True iff it's a theorem/lemma with `sorry_using` body
    raw_source: str                  # full declaration text (attribute + body)
    attr_source: str                 # `@[blueprint ...]` text
    decl_source: str                 # declaration text (no attribute)
    signature: str                   # "theorem foo ... : T" (everything before `:=`)
    body_source: str                 # `:= by sorry_using [...]` portion (may be empty for defs)
    informal_statement: str          # from `(statement := /-- ... -/)`
    informal_proof: str              # from `(proof := /-- ... -/)`
    depends_on: list[str] = field(default_factory=list)
    # File-absolute offsets for in-place substitution:
    attr_start: int = 0
    decl_start: int = 0
    decl_end: int = 0
    # sorry_using token offsets (only set for target nodes):
    sorry_start: int = -1
    sorry_end: int = -1


# Upstream graph.py:231
_LET_VALUE_COLON_EQ_RE = re.compile(
    r'\blet\s+'
    r'(?:[^\s(),;:=⟨⟩]+|\([^=;]*\)|⟨[^=;]*⟩)'  # ident (unicode) | (tuple) | ⟨anon ctor⟩
    r'(?:\s*:\s*[^=;]+)?'                       # optional `: type`
    r'\s*$',
)


# Upstream graph.py:786
def _find_real_proof_by(text: str):
    """Find the `:= by` that starts the REAL proof body, skipping any
    `:= by` that appears as a ``let <name>[: <type>] := by <term>``
    construct inside the type signature.  Uses the same heuristic as
    `_split_signature_and_body`: skip any `:=` immediately preceded by
    ``let <name>[: <type>]``."""
    for m in re.finditer(r':=\s*by\b', text):
        pre = text[:m.start()].rstrip()
        if _LET_VALUE_COLON_EQ_RE.search(pre):
            continue
        return m
    return None


# Upstream graph.py:800
def graft_proof_body(
    model_code: str, node: BlueprintNode,
) -> tuple[str | None, str | None]:
    """Extract the model's tactic body for `node.name` and attach it
    to the node's canonical signature (from the skeleton).

    Returns `(grafted_declaration, proof_body)`. `grafted_declaration`
    is the full theorem ready to compile: `<signature> := by <body>`.
    `proof_body` is just the tactic block after `:= by` (for final
    assembly substitution). Returns `(None, None)` on failure."""
    # `(?![\w'])` instead of `\b` — see check_theorem_present for why.
    pattern = (
        r"\b(?:theorem|lemma)\s+" + re.escape(node.name) + r"(?![\w'])"
    )
    m = re.search(pattern, model_code)
    if not m:
        # Fallback: last theorem/lemma keyword
        matches = list(re.finditer(
            r'\b(?:theorem|lemma)\s+\S+', model_code,
        ))
        if not matches:
            return None, None
        m = matches[-1]
    rest = model_code[m.end():]
    by_match = _find_real_proof_by(rest)
    if not by_match:
        return None, None
    proof_body = rest[by_match.end():]
    # Drop trailing #print axioms
    proof_body = re.sub(
        r'\n*#print\s+axioms\s+\S+\s*$', '', proof_body,
    ).rstrip()
    # Strip leading whitespace/newlines
    proof_body = proof_body.lstrip('\n').rstrip()
    if not proof_body:
        return None, None
    sig = node.signature.rstrip()
    grafted = f"{sig} := by\n{_reindent_tactics(proof_body, '  ')}"
    return grafted, proof_body


# Upstream graph.py:841
def _reindent_tactics(body: str, target_indent: str) -> str:
    """Strip common leading whitespace from `body` and re-indent every
    non-empty line with `target_indent`."""
    # Dedent to remove whatever the model used
    dedented = textwrap.dedent(body)
    out_lines = []
    for line in dedented.split('\n'):
        if line.strip():
            out_lines.append(target_indent + line)
        else:
            out_lines.append('')
    return '\n'.join(out_lines)


# Upstream graph.py:567
FOUNDATIONAL_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}


# Upstream graph.py:587
def classify_axioms(axioms: set[str]) -> tuple[str, set[str]]:
    """Bucket a set of axiom dependencies.

    Buckets (most-rejected first):
      USES_SORRY    — sorryAx in axioms (proof is incomplete)
      CUSTOM_AXIOM  — non-foundational axioms (extra returned)
      VACUOUS       — no axioms (e.g. proof by rfl)
      LEGIT         — exactly the foundational set
      PARTIAL       — strict, non-empty subset of foundational
    """
    if "sorryAx" in axioms:
        return "USES_SORRY", set()
    foundational = FOUNDATIONAL_AXIOMS
    extra = axioms - foundational
    if extra:
        return "CUSTOM_AXIOM", extra
    if not axioms:
        return "VACUOUS", set()
    if axioms == foundational:
        return "LEGIT", set()
    return "PARTIAL", set()


# Upstream graph.py:1182
@dataclass
class AnalysisResult:
    """Summary of reachability analysis on a blueprint partial assembly.

    All fields are sets of node names. `effective_deps` maps every node
    name to its computed dep set (debug / logging aid).
    """

    reachable: set[str]         = field(default_factory=set)
    unsolved_targets: set[str]  = field(default_factory=set)
    dead: set[str]              = field(default_factory=set)
    frozen: set[str]            = field(default_factory=set)
    effective_deps: dict[str, set[str]] = field(default_factory=dict)


# Upstream graph.py:1197
_IDENT_CHAR = r"[\w']"  # Lean identifier chars: \w plus prime


# Upstream graph.py:1200
def strip_lean_comments(text: str) -> str:
    """Strip `--`, `/- ... -/`, and `/-- ... -/` from `text`.

    Block comments nest (Lean spec); depth is tracked. Line comments
    end at the next newline. Removed regions are dropped entirely;
    positions don't matter — we only care about identifier matches.
    """
    if not text:
        return text
    out: list[str] = []
    i = 0
    n = len(text)
    depth = 0
    while i < n:
        if depth == 0:
            if text[i:i + 2] == "/-":
                depth = 1
                i += 2
                continue
            if text[i:i + 2] == "--":
                eol = text.find("\n", i)
                if eol < 0:
                    break
                i = eol
                continue
            out.append(text[i])
            i += 1
        else:
            if text[i:i + 2] == "-/":
                depth -= 1
                i += 2
                continue
            if text[i:i + 2] == "/-":
                depth += 1
                i += 2
                continue
            i += 1
    return "".join(out)


# Upstream graph.py:1240
def _regex_used_names(text: str, candidates: set[str]) -> set[str]:
    """Subset of `candidates` that appear as Lean identifiers in `text`.

    Uses negative lookaround on `[\\w']` so names ending in `'` (e.g.
    `foo'`) match correctly — Python's `\\b` treats `'` as non-word and
    would fail at the boundary.

    `.` is a namespace separator, not an identifier char, so `M.foo` IS
    a reference to `foo` and we match it. False positives from string
    literals (we strip comments but not strings) only over-keep, never
    drop, so they're safe.
    """
    if not text:
        return set()
    text = strip_lean_comments(text)
    out: set[str] = set()
    for name in candidates:
        pat = rf"(?<!{_IDENT_CHAR}){re.escape(name)}(?!{_IDENT_CHAR})"
        if re.search(pat, text):
            out.add(name)
    return out


# Upstream graph.py:1263
def analyze_blueprint_from_trace(
    trace: dict,
    main_name: str,
    *,
    skeleton: str | None = None,
    parsed_nodes: list[BlueprintNode],
) -> AnalysisResult:
    """Compute reachability from `main_name` using the prover's trace.

    For every blueprint node parsed from `skeleton` (or
    `trace['skeleton_code']` / `trace['upstream_skeleton']` if `skeleton`
    is None), the effective dep set is the union of blueprint-node names
    that textually appear in:

      - the declaration's signature (skeleton's
        attr_start..sorry_start for targets, attr_start..decl_end for
        non-targets such as `def`), and
      - the prover's `proof_body` for that node, if any.

    When a target node has no `proof_body` (prover failed) but does have
    a declared `depends_on` list (from `sorry_using [...]`), fall back
    to the declared list — it's the most conservative answer and
    matches what the skeleton author intended.

    Raises ValueError if `main_name` isn't a parsed node.
    """
    skel = skeleton or trace.get("skeleton_code") or trace.get("upstream_skeleton") or ""
    nr = trace.get("node_results") or {}

    parsed = list(parsed_nodes)
    name_to_node = {n.name: n for n in parsed}
    all_names: set[str] = set(name_to_node.keys()) | set(nr.keys())

    if main_name not in all_names:
        raise ValueError(
            f"analyze_blueprint_from_trace: main `{main_name}` not in "
            f"parsed nodes (got {sorted(all_names)})"
        )

    solved_set: set[str] = set()
    unsolved_set: set[str] = set()
    for n in parsed:
        if not n.is_target:
            solved_set.add(n.name)
        elif isinstance(nr.get(n.name), dict) and nr[n.name].get("success"):
            solved_set.add(n.name)
        else:
            unsolved_set.add(n.name)

    effective: dict[str, set[str]] = {}
    for name in all_names:
        candidates = all_names - {name}
        node = name_to_node.get(name)

        sig_text = ""
        if node is not None:
            if node.is_target and node.sorry_start >= 0:
                sig_text = skel[node.attr_start:node.sorry_start]
            else:
                sig_text = skel[node.attr_start:node.decl_end]

        r = nr.get(name) if isinstance(nr.get(name), dict) else None
        body = (r or {}).get("proof_body") or ""
        scan_text = (sig_text + "\n" + body) if (sig_text or body) else ""

        is_target = node.is_target if node is not None else (name in nr)
        declared_raw = (r or {}).get("depends_on")
        body_attempted = bool(body)

        if scan_text:
            effective[name] = _regex_used_names(scan_text, candidates)
        elif is_target and declared_raw is not None and not body_attempted:
            effective[name] = set(declared_raw) & candidates
        else:
            effective[name] = candidates

    reachable: set[str] = set()
    stack = [main_name]
    while stack:
        cur = stack.pop()
        if cur in reachable:
            continue
        reachable.add(cur)
        for d in effective.get(cur, ()):
            if d not in reachable:
                stack.append(d)

    return AnalysisResult(
        reachable=reachable,
        unsolved_targets=reachable & unsolved_set,
        dead=all_names - reachable,
        frozen=reachable & solved_set,
        effective_deps=effective,
    )


# Upstream blueprint.py:258
def _highlight_line_span(line_text: str, col: int, end_col: int) -> str:
    """Wrap `line_text[col:end_col]` in `<error></error>` markers."""
    return (
        f"{line_text[:col]}<error>{line_text[col:end_col]}</error>"
        f"{line_text[end_col:]}"
    )


# Upstream blueprint.py:280
def _violation_synthetic(display: str, message: str) -> dict:
    """Build a violation dict with a pre-rendered display block. Pass an
    empty string for `display` to omit the top-level fenced block entirely
    (used when there's no real offending span and the required content is
    embedded in a nested ```lean4 block inside `message` instead)."""
    return {"display": display, "message": message}


# Upstream blueprint.py:703
def _highlight_decl_line(code: str, name: str) -> str | None:
    """Return the line containing `theorem|lemma|def|... <name>` with the
    `kind name` keyword span wrapped in `<error></error>`. Returns None
    if no such decl is found (caller falls back to a synthetic display).
    """
    pattern = (
        r"\b(theorem|lemma|def|abbrev|structure|instance|inductive|class)"
        r"\s+" + re.escape(name) + r"(?![\w'])"
    )
    m = re.search(pattern, code)
    if m is None:
        return None
    line_start = code.rfind('\n', 0, m.start()) + 1
    line_end = code.find('\n', m.end())
    if line_end == -1:
        line_end = len(code)
    line_text = code[line_start:line_end]
    col = m.start() - line_start
    end_col = m.end() - line_start
    return _highlight_line_span(line_text, col, end_col)


# Upstream blueprint.py:725
def _highlight_sorry_using_line(code: str, name: str) -> str | None:
    """Find the `sorry_using [...]` token associated with the decl
    `<name>` and return its source line with the bracketed list wrapped
    in `<error></error>`. Returns None if not located."""
    pattern = (
        r"\b(?:theorem|lemma)\s+" + re.escape(name)
        + r"(?![\w'])[\s\S]*?sorry_using\s*(\[[^\]]*\])"
    )
    m = re.search(pattern, code)
    if m is None:
        return None
    list_start = m.start(1)
    list_end = m.end(1)
    line_start = code.rfind('\n', 0, list_start) + 1
    line_end = code.find('\n', list_end)
    if line_end == -1:
        line_end = len(code)
    line_text = code[line_start:line_end]
    col = list_start - line_start
    end_col = list_end - line_start
    return _highlight_line_span(line_text, col, end_col)


# Upstream blueprint.py:765
def validate_blueprint_graph(
    code: str,
    blueprint_nodes: list,
    theorem_name: str | None,
) -> list[dict] | None:
    """Run structural validation on a model-authored blueprint graph.

    `blueprint_nodes` must come from `graph.parse_blueprint_file` on
    `code`. Returns a list of {display, message} issues or None if the
    graph is valid.
    """
    if not blueprint_nodes:
        return [_violation_synthetic(
            "<error>(no @[blueprint] declarations found)</error>",
            (
                "The Lean file has no `@[blueprint]`-annotated "
                "declarations. Every node of your decomposition "
                "(definitions, lemmas, and the main theorem) must be a "
                "`@[blueprint]`-annotated declaration."
            ),
        )]

    nodes_by_name: dict[str, object] = {n.name: n for n in blueprint_nodes}
    target_kinds = {"theorem", "lemma"}
    issues: list[dict] = []

    # --- Statement / proof field presence on each node ------------------
    for n in blueprint_nodes:
        if not (n.informal_statement or "").strip():
            display = (_highlight_decl_line(code, n.name)
                       or f"<error>@[blueprint] {n.kind} {n.name}</error>")
            issues.append(_violation_synthetic(
                display,
                (
                    f"`{n.kind} {n.name}` is missing a non-empty "
                    f"`(statement := /-- ... -/)` field in its "
                    f"`@[blueprint]` annotation. Every node must carry "
                    f"an NL statement field, e.g. `@[blueprint "
                    f"(statement := /-- claim text -/)]`."
                ),
            ))
        if n.kind in target_kinds and not (n.informal_proof or "").strip():
            display = (_highlight_decl_line(code, n.name)
                       or f"<error>@[blueprint] {n.kind} {n.name}</error>")
            issues.append(_violation_synthetic(
                display,
                (
                    f"`{n.kind} {n.name}` is missing a non-empty "
                    f"`(proof := /-- ... -/)` field in its "
                    f"`@[blueprint]` annotation. Every Lemma and the "
                    f"Theorem must carry an NL proof sketch field, e.g. "
                    f"`@[blueprint (statement := /-- claim -/), "
                    f"(proof := /-- sketch -/)]`."
                ),
            ))

    # --- Self-loops -----------------------------------------------------
    for n in blueprint_nodes:
        if n.name in (n.depends_on or []):
            display = (_highlight_sorry_using_line(code, n.name)
                       or f"<error>{n.kind} {n.name} ... "
                          f"sorry_using [..., {n.name}, ...]</error>")
            issues.append(_violation_synthetic(
                display,
                (
                    f"Node `{n.name}` lists itself in its `sorry_using "
                    f"[...]` (self-loop). A node cannot depend on itself."
                ),
            ))

    # --- Undeclared deps ------------------------------------------------
    for n in blueprint_nodes:
        for d in (n.depends_on or []):
            if d == n.name:
                continue  # already reported as self-loop
            if d not in nodes_by_name:
                display = (_highlight_sorry_using_line(code, n.name)
                           or f"<error>sorry_using [..., {d}, ...]</error>")
                issues.append(_violation_synthetic(
                    display,
                    (
                        f"`{n.kind} {n.name}`'s `sorry_using [...]` "
                        f"references `{d}`, which is not the name of any "
                        f"`@[blueprint]`-annotated declaration in this "
                        f"file. Either add a `@[blueprint]` decl named "
                        f"`{d}` or drop it from `sorry_using`."
                    ),
                ))

    # --- Cycle detection (Kahn's algorithm) -----------------------------
    out_adj: dict[str, list[str]] = {}
    in_adj: dict[str, list[str]] = {}
    for n in blueprint_nodes:
        for d in (n.depends_on or []):
            if d in nodes_by_name and d != n.name:
                out_adj.setdefault(d, []).append(n.name)
                in_adj.setdefault(n.name, []).append(d)
    indeg = {nm: len(in_adj.get(nm, [])) for nm in nodes_by_name}
    work = dict(indeg)
    queue = [nm for nm, k in work.items() if k == 0]
    visited: list[str] = []
    while queue:
        t = queue.pop()
        visited.append(t)
        for nb in out_adj.get(t, []):
            work[nb] -= 1
            if work[nb] == 0:
                queue.append(nb)
    if len(visited) != len(nodes_by_name):
        cycle_members = sorted(set(nodes_by_name) - set(visited))
        if cycle_members:
            display_lines = []
            for nm in cycle_members[:6]:
                hl = _highlight_sorry_using_line(code, nm)
                if hl:
                    display_lines.append(hl)
                else:
                    node = nodes_by_name[nm]
                    display_lines.append(
                        f"<error>{node.kind} {nm}</error>"
                    )
            display = "\n".join(display_lines)
        else:
            display = "<error>(cyclic sorry_using graph)</error>"
        issues.append(_violation_synthetic(
            display,
            (
                f"Cyclic `sorry_using` dependencies through "
                f"{cycle_members}. The graph must be acyclic — break the "
                f"cycle by removing one or more dep edges."
            ),
        ))

    # --- Theorem existence + reachability -------------------------------
    if theorem_name is not None:
        thm_node = nodes_by_name.get(theorem_name)
        if thm_node is None:
            issues.append(_violation_synthetic(
                f"<error>theorem {theorem_name} ... "
                f":= by sorry_using [...]</error>",
                (
                    f"No `@[blueprint]`-annotated declaration named "
                    f"`{theorem_name}` (the canonical theorem "
                    f"identifier). The blueprint must include the main "
                    f"Theorem under its canonical name."
                ),
            ))
        elif thm_node.kind not in target_kinds:
            display = (_highlight_decl_line(code, theorem_name)
                       or f"<error>{thm_node.kind} {theorem_name}</error>")
            issues.append(_violation_synthetic(
                display,
                (
                    f"`{theorem_name}` is declared as `{thm_node.kind}` "
                    f"but the canonical Lean identifier expects a "
                    f"`theorem` (or `lemma`). Re-emit it with the right "
                    f"keyword."
                ),
            ))
        else:
            reachable = {theorem_name}
            stack = [theorem_name]
            while stack:
                t = stack.pop()
                for d in in_adj.get(t, []):
                    if d not in reachable:
                        reachable.add(d)
                        stack.append(d)
            dead = sorted(nm for nm in nodes_by_name if nm not in reachable)
            if dead:
                display_lines: list[str] = []
                for nm in dead[:10]:
                    hl = _highlight_decl_line(code, nm)
                    if hl:
                        display_lines.append(hl)
                    else:
                        node = nodes_by_name[nm]
                        display_lines.append(
                            f"<error>{node.kind} {nm}</error>"
                        )
                display = "\n".join(display_lines)
                issues.append(_violation_synthetic(
                    display,
                    (
                        f"{len(dead)} node(s) not reachable from the "
                        f"main Theorem `{theorem_name}`: {dead}. The "
                        f"Theorem must transitively depend on every "
                        f"other node — wire each dead node into some "
                        f"path that reaches the Theorem (via the "
                        f"`sorry_using` deps), or remove it."
                    ),
                ))

    return issues or None

