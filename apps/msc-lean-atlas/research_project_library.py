"""Fresh, source-bound build of the published example's local Lean library.

Integration: validate a candidate's project imports with ``allowed_imports``.
When it imports that entry point, call ``prepare_library`` after lean_service
prepares the environment and before Candidate.lean is compiled. ``runner`` is
a callback accepting a project-relative POSIX filename; it must compile that
file in ``work`` with the supplied (mutated) context/env and raise on failure.
For example: lambda file: _run(context, env, work, file, diagnostics, cancelled).
Store the returned manifest in the verification report. Bind ``fingerprint``
in the exact source/prelude with the source pin comment and pass that expected
fingerprint to the builder. Source staleness is scoped to this import, without
invalidating unrelated examples. No shared local .olean is reused.
"""
from __future__ import annotations

from datetime import datetime, timezone
import hashlib
import json
import os
from pathlib import Path
import re

import lean_service


ENTRY_POINT = "MathResearch.AlbertSpectralGeometry"
MODULE = re.compile(r"MathResearch(?:\.[A-Za-z_][A-Za-z0-9_]*)+")
PIN_PREFIX = "-- atlas-project-library-sha256: "


def pinned_fingerprint(source, required=False):
    """Read one exact source pin; never silently refresh an existing contract."""
    lines = [line.strip() for line in source.splitlines() if "atlas-project-library-sha256:" in line]
    if not lines:
        if required:
            raise ValueError("Published library source fingerprint pin is required.")
        return None
    if len(lines) != 1 or not re.fullmatch(re.escape(PIN_PREFIX) + r"[0-9a-f]{64}", lines[0]):
        raise ValueError("Published library source fingerprint pin is malformed or duplicated.")
    return lines[0][len(PIN_PREFIX):]


def allowed_imports():
    """Only this project import may appear directly in a research candidate."""
    return frozenset({ENTRY_POINT})


def _root(project_root=None):
    return Path(project_root or lean_service.default_context()["project_root"]).resolve()


def _sha(data):
    return hashlib.sha256(data).hexdigest()


def _snapshot(project_root=None):
    root = _root(project_root)
    ordered, content, active = [], {}, set()

    def visit(module):
        if module in content:
            return
        if module in active:
            raise ValueError("Cyclic project library imports: " + module)
        if not MODULE.fullmatch(module):
            raise ValueError("Invalid project library module: " + module)
        relative = module.replace(".", "/") + ".lean"
        path = (root / relative).resolve()
        if not path.is_relative_to(root / "MathResearch"):
            raise ValueError("Project library source escapes MathResearch: " + module)
        data = path.read_bytes()
        if len(data) > 2_000_000:
            raise ValueError("Project library source exceeds 2 MB: " + module)
        imports = lean_service._imports(data.decode("utf-8"))
        active.add(module)
        for dependency in imports:
            if dependency.startswith("MathResearch."):
                visit(dependency)
            elif dependency not in {"Mathlib", "Init", "Std"} and not dependency.startswith("Mathlib."):
                raise ValueError("Unsupported dependency in published library: " + dependency)
        active.remove(module)
        content[module] = data
        ordered.append(dict(module=module, path=relative, sha256=_sha(data), imports=imports))

    visit(ENTRY_POINT)
    identity = json.dumps(ordered, sort_keys=True, separators=(",", ":")).encode("utf-8")
    return dict(entry_point=ENTRY_POINT, fingerprint=_sha(identity), sources=ordered), content


def source_manifest(project_root=None):
    """Hash exact current source bytes for the entire reachable local closure."""
    return _snapshot(project_root)[0]


def fingerprint(project_root=None):
    return source_manifest(project_root)["fingerprint"]


def _cancelled(value):
    return bool(value() if callable(value) else value.is_set() if hasattr(value, "is_set") else value)


def prepare_library(context, env, work, runner, cancelled=None, *, expected_fingerprint=None):
    """Copy and freshly compile the source closure, rejecting stale source pins.

    Mutates context/env LEAN_PATH to remove the checkout and shared project
    build directories. It retains only this workspace and the pinned external
    library search paths. Existing project .oleans in this workspace are an
    error, not a cache hit. A source edit during the build invalidates it.
    """
    work = Path(work).resolve()
    root = _root(context.get("project_root"))
    manifest, content = _snapshot(root)
    if expected_fingerprint is not None and manifest["fingerprint"] != expected_fingerprint:
        raise ValueError("Published library source fingerprint changed; a new run contract is required.")
    if not work.is_dir():
        raise ValueError("The candidate workspace must already exist.")
    if _cancelled(cancelled):
        raise InterruptedError("Published library preparation cancelled.")

    # Search only this run and the externally prepared libraries. In particular,
    # project-root .olean files and .lake/build cannot satisfy local imports.
    old_paths = context.get("lean_search_paths") or env.get("LEAN_PATH", "").split(os.pathsep)
    excluded = {root, (root / ".lake/build/lib/lean").resolve()}
    paths = [work]
    for value in old_paths:
        if not value:
            continue
        path = Path(value).resolve()
        if path not in excluded and path != work and path not in paths:
            paths.append(path)
    env["LEAN_PATH"] = os.pathsep.join(map(str, paths))
    context["lean_search_paths"] = list(map(str, paths))
    context["project_library_fingerprint"] = manifest["fingerprint"]

    manifest.update(status="building", started_at=datetime.now(timezone.utc).isoformat(),
                    compiler=context["lean"], fresh_local_build=True, external_mathlib_cache_reused=True)
    report_path = work / "project-library.json"

    def save():
        report_path.write_text(json.dumps(manifest, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")

    try:
        for item in manifest["sources"]:
            target = work / item["path"]
            if not target.resolve().is_relative_to(work):
                raise ValueError("Local library destination escapes workspace.")
            if target.with_suffix(".olean").exists():
                raise ValueError("Refusing pre-existing local library .olean: " + item["module"])
            target.parent.mkdir(parents=True, exist_ok=True)
            target.write_bytes(content[item["module"]])
        save()
        for item in manifest["sources"]:
            if _cancelled(cancelled):
                raise InterruptedError("Published library preparation cancelled.")
            runner(item["path"])
            output = (work / item["path"]).with_suffix(".olean")
            if not output.is_file() or output.stat().st_size == 0:
                raise RuntimeError("Fresh local compilation produced no .olean: " + item["module"])
            if (work / item["path"]).read_bytes() != content[item["module"]]:
                raise ValueError("Copied project source changed while compiling: " + item["module"])
            item["olean_sha256"] = _sha(output.read_bytes())
            save()
        if fingerprint(root) != manifest["fingerprint"]:
            raise ValueError("Published library sources changed during compilation; result is stale.")
        manifest.update(status="complete", sources_unchanged=True, finished_at=datetime.now(timezone.utc).isoformat())
        context["dependency_note"] = ("Reachable published MathResearch sources are freshly compiled in this run; "
                                      "external mathlib dependencies use pinned prepared .olean caches.")
        save()
        return manifest
    except Exception as error:
        manifest.update(status="failed", error=str(error), finished_at=datetime.now(timezone.utc).isoformat())
        save()
        raise
