"""Fresh local Lean inspection and bridge verification.

The classifier/search layer is deliberately separate. Compiling a theorem and
seeing both inputs in its dependency graph proves only that formal statement;
it does not certify the mathematical importance or novelty of a correspondence.
All writes and builds happen in a new subdirectory of the supplied run directory.
"""
from datetime import datetime, timezone
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import time
import uuid

ROOT = Path(__file__).resolve().parent
ALLOWED_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}
PROJECT_DEFAULT = str(next((p for p in ROOT.parents if (p / 'MathResearch.lean').is_file()), ROOT))
LEAN_DEFAULT = shutil.which("lean") or str(Path(PROJECT_DEFAULT) / ".missing-lean")
MATHLIB_DEFAULT = str(Path(PROJECT_DEFAULT) / ".lake/packages/mathlib")
MODULE_FILE = re.compile(r"^[A-Za-z_][A-Za-z0-9_]*(?:/[A-Za-z_][A-Za-z0-9_]*)*\.lean$")
DECL = re.compile(r"(?m)^\s*(?:(?:private|protected|noncomputable|unsafe|partial)\s+)*(def|theorem|lemma|abbrev|structure|class|inductive|opaque|axiom)\s+([^\s(:=]+)")


def _now():
    return datetime.now(timezone.utc).isoformat()


def _sha(data):
    if isinstance(data, str):
        data = data.encode("utf-8")
    return hashlib.sha256(data).hexdigest()


def _write_json(path, value):
    temporary = path.with_suffix(path.suffix + ".tmp")
    temporary.write_text(json.dumps(value, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
    temporary.replace(path)


def default_context():
    """Local defaults, overridable per request; no installation or network calls."""
    return {
        "lean": os.environ.get("ATLAS_LEAN", LEAN_DEFAULT),
        "mathlib": os.environ.get("ATLAS_MATHLIB", MATHLIB_DEFAULT),
        "project_root": os.environ.get("ATLAS_PROJECT_ROOT", PROJECT_DEFAULT),
        "timeout_seconds": 120,
    }


def _context(value):
    result = default_context()
    result.update({k: v for k, v in (value or {}).items() if k in result and v is not None})
    result["timeout_seconds"] = max(5, min(300, int(result.get("timeout_seconds", 120))))
    for key in ("lean", "mathlib", "project_root"):
        if result[key]:
            result[key] = str(Path(result[key]).expanduser().absolute())
    return result


def _mask(source):
    """Mask comments and string literals while preserving offsets/newlines."""
    out = list(source)
    i, depth, in_string = 0, 0, False
    while i < len(source):
        if depth:
            if source[i:i+2] == "/-":
                out[i:i+2] = [" ", " "]; depth += 1; i += 2
            elif source[i:i+2] == "-/":
                out[i:i+2] = [" ", " "]; depth -= 1; i += 2
            else:
                if source[i] != "\n": out[i] = " "
                i += 1
        elif in_string:
            if source[i] == "\\" and i+1 < len(source):
                out[i:i+2] = [" ", "\n" if source[i+1] == "\n" else " "]; i += 2
            elif source[i] == '"':
                out[i] = " "; in_string = False; i += 1
            else:
                if source[i] != "\n": out[i] = " "
                i += 1
        elif source[i:i+2] == "/-":
            out[i:i+2] = [" ", " "]; depth = 1; i += 2
        elif source[i:i+2] == "--":
            while i < len(source) and source[i] != "\n": out[i] = " "; i += 1
        elif source[i] == '"':
            out[i] = " "; in_string = True; i += 1
        else:
            i += 1
    return "".join(out)


def lexical_declarations(source):
    masked = _mask(source)
    result = []
    for match in DECL.finditer(masked):
        line = masked.count("\n", 0, match.start(1)) + 1
        result.append({"name": match.group(2), "kind": match.group(1), "line": line,
                       "type": "", "dependencies": [], "extraction": "lexical_unverified"})
    return result


def _imports(source):
    return [word for line in re.findall(r"(?m)^\s*import\s+([^\n]+)", _mask(source))
            for word in line.split() if re.fullmatch(r"[A-Za-z_][A-Za-z0-9_.]*", word)]


def _validate_files(files):
    if not isinstance(files, list) or len(files) != 2:
        raise ValueError("Нужны ровно два Lean-файла.")
    seen, result = set(), []
    for item in files:
        name, source = item.get("name", ""), item.get("content", "")
        if not isinstance(source, str) or len(source.encode("utf-8")) > 2_000_000:
            raise ValueError("Lean-файл должен быть текстом размером не более 2 МБ.")
        if not isinstance(name, str) or not MODULE_FILE.fullmatch(name):
            raise ValueError("Имя файла: латинские имена модулей, например InputA.lean или Demo/InputA.lean.")
        if name in seen or name.split("/")[0] in {"AtlasInspect.lean", "AtlasDump.lean", "Bridge.lean"}:
            raise ValueError("Имена двух файлов должны отличаться и не использовать зарезервированные Bridge/AtlasInspect/AtlasDump.")
        seen.add(name)
        result.append({"name": name, "content": source, "sha256": _sha(source),
                       "module": name[:-5].replace("/", ".")})
    return result


def _order(files):
    pending = {f["module"]: f for f in files}
    result, built = [], set()
    while pending:
        ready = [f for f in pending.values() if not (set(_imports(f["content"])) & set(pending))]
        if not ready:
            raise ValueError("Циклические импорты между входными файлами.")
        for f in ready:
            result.append(f); built.add(f["module"]); del pending[f["module"]]
    return result


def _git_revision(folder):
    if not folder:
        return None
    try:
        p = subprocess.run(["git", "-C", folder, "rev-parse", "HEAD"], capture_output=True, text=True, timeout=10)
        return p.stdout.strip() if p.returncode == 0 else None
    except (OSError, subprocess.TimeoutExpired):
        return None


def _prepare(context, workspace):
    context = _context(context)
    lean = Path(context["lean"])
    if not lean.is_file() or not os.access(str(lean), os.X_OK):
        raise ValueError("Исполняемый Lean не найден. Укажите путь в настройках окружения.")
    version = subprocess.run([str(lean), "--version"], capture_output=True, text=True, timeout=15)
    if version.returncode:
        raise ValueError("Не удалось получить версию Lean: " + version.stderr[:1000])
    context["lean_version"] = version.stdout.strip()
    paths = [workspace]
    project = Path(context["project_root"]) if context["project_root"] else None
    if project:
        if not project.is_dir(): raise ValueError("Каталог проекта не найден.")
        lib = project / ".lake/build/lib/lean"
        if lib.is_dir(): paths.append(lib)
        paths.append(project)
        context["project_revision"] = _git_revision(str(project))
    mathlib = Path(context["mathlib"]) if context["mathlib"] else None
    if mathlib:
        lib = mathlib / ".lake/build/lib/lean"
        if not lib.is_dir(): raise ValueError("Не найден подготовленный кэш mathlib (.lake/build/lib/lean).")
        paths.append(lib)
        manifest = mathlib / "lake-manifest.json"
        if manifest.exists():
            context["mathlib_manifest_sha256"] = _sha(manifest.read_bytes())
            for package in json.loads(manifest.read_text())["packages"]:
                for path in (mathlib.parent / package["name"] / ".lake/build/lib/lean",
                             mathlib / ".lake/packages" / package["name"] / ".lake/build/lib/lean"):
                    if path.is_dir() and path not in paths: paths.append(path)
        context["mathlib_revision"] = _git_revision(str(mathlib))
    env = os.environ.copy()
    env["LEAN_PATH"] = os.pathsep.join(map(str, paths))
    context["dependency_note"] = "Входные файлы и Bridge компилируются заново; внешние библиотеки используют подготовленные .olean-кэши."
    context["lean_search_paths"] = list(map(str, paths))
    return context, env


def _run(context, env, workspace, relative, diagnostics, output=True):
    args = [context["lean"]]
    if output:
        args.extend(["-o", str(Path(relative).with_suffix(".olean"))])
    args.append(relative)
    started = time.monotonic()
    try:
        p = subprocess.run(args, cwd=workspace, env=env, capture_output=True, text=True,
                           timeout=context["timeout_seconds"])
        entry = {"file": relative, "command": args, "exit_code": p.returncode,
                 "elapsed_seconds": round(time.monotonic()-started, 3),
                 "stdout": p.stdout[-200000:], "stderr": p.stderr[-200000:]}
    except subprocess.TimeoutExpired as error:
        def text(v): return v.decode(errors="replace") if isinstance(v, bytes) else v or ""
        entry = {"file": relative, "command": args, "exit_code": None, "timeout": True,
                 "elapsed_seconds": round(time.monotonic()-started, 3),
                 "stdout": text(error.stdout)[-200000:], "stderr": text(error.stderr)[-200000:]}
    diagnostics.append(entry)
    (workspace / (relative.replace("/", "_") + ".log")).write_text(entry["stdout"] + entry["stderr"], encoding="utf-8")
    if entry["exit_code"] != 0:
        raise RuntimeError("Lean не завершил проверку: " + relative + (" (тайм-аут)" if entry.get("timeout") else ""))


def _compile_inputs(files, context, env, workspace, diagnostics):
    for f in files:
        path = workspace / f["name"]
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(f["content"], encoding="utf-8")
    for f in _order(files):
        _run(context, env, workspace, f["name"], diagnostics)


def _export(modules, input_modules, context, env, workspace, diagnostics):
    shutil.copyfile(ROOT / "tools/AtlasInspect.lean", workspace / "AtlasInspect.lean")
    _run(context, env, workspace, "AtlasInspect.lean", diagnostics)
    def literals(xs): return ", ".join(json.dumps(x) for x in xs)
    output = workspace / "compiler-declarations.json"
    imports = "\n".join("import " + m for m in modules)
    text = f'import AtlasInspect\n{imports}\nset_option maxRecDepth 8192\nset_option maxHeartbeats 2000000\n#atlas_export [{literals(modules)}] [{literals(input_modules)}] {json.dumps(str(output))}\n'
    (workspace / "AtlasDump.lean").write_text(text, encoding="utf-8")
    _run(context, env, workspace, "AtlasDump.lean", diagnostics, output=False)
    if not output.is_file(): raise RuntimeError("Lean не создал файл семантического экспорта.")
    return json.loads(output.read_text(encoding="utf-8"))


def inspect_files(files, context, run_dir):
    run_dir = Path(run_dir).resolve()
    run_dir.mkdir(parents=True, exist_ok=True)
    workspace = run_dir / ("inspect-" + uuid.uuid4().hex[:12])
    workspace.mkdir()
    report = {"status": "failed", "files": [], "diagnostics": [], "context": _context(context),
              "workspace": str(workspace), "started_at": _now(), "checked_at": None,
              "semantic_extraction": False}
    try:
        files = _validate_files(files)
        report["files"] = [{"name": f["name"], "sha256": f["sha256"], "module": f["module"],
                            "source_path": str(workspace / f["name"]), "declarations": lexical_declarations(f["content"]),
                            "inspection_status": "lexical_unverified"} for f in files]
        context, env = _prepare(context, workspace)
        report["context"] = context
        _compile_inputs(files, context, env, workspace, report["diagnostics"])
        exported = _export([f["module"] for f in files], [], context, env, workspace, report["diagnostics"])
        report["imported_modules"] = exported["imported_modules"]
        for file in report["files"]:
            raw = next(f["content"] for f in files if f["name"] == file["name"])
            lines = {d["name"]: d["line"] for d in lexical_declarations(raw)}
            declarations = [d for d in exported["declarations"] if d["module"] == file["module"]]
            for d in declarations:
                d["line"] = lines.get(d["name"], lines.get(d["name"].split(".")[-1]))
                d["extraction"] = "lean_environment"
            declarations.sort(key=lambda d: (d["line"] or 1000000, d["name"]))
            file["declarations"] = declarations
            unexpected = sorted({a for d in declarations for a in d["axioms"]} - ALLOWED_AXIOMS)
            file["unexpected_axioms"] = unexpected
            file["inspection_status"] = "compiled_untrusted" if unexpected else "compiled"
            file["olean_sha256"] = _sha((workspace / file["name"]).with_suffix(".olean").read_bytes())
        report["status"] = "compiled_untrusted" if any(f["unexpected_axioms"] for f in report["files"]) else "complete"
        report["semantic_extraction"] = True
    except (ValueError, RuntimeError, OSError, subprocess.SubprocessError, KeyError) as error:
        report["error"] = str(error)
    report["checked_at"] = _now()
    _write_json(workspace / "inspection.json", report)
    return report


def verify_bridge(source, targets, context, run_dir, inspection=None):
    run_dir = Path(run_dir).resolve()
    run_dir.mkdir(parents=True, exist_ok=True)
    workspace = run_dir / ("verify-" + uuid.uuid4().hex[:12])
    workspace.mkdir()
    report = {"status": "failed", "success": False, "source_sha256": _sha(source) if isinstance(source, str) else None,
              "diagnostics": [], "targets": targets or [], "axioms": [], "context": _context(context),
              "workspace": str(workspace), "started_at": _now(), "checked_at": None,
              "interpretation": "Проверяется формальная теорема и участие обоих входов. Содержательность и новизна связи требуют отдельной оценки."}
    try:
        if not isinstance(source, str) or not source.strip() or len(source.encode("utf-8")) > 2_000_000:
            raise ValueError("Нужен непустой исходник Bridge.lean размером до 2 МБ.")
        (workspace / "Bridge.lean").write_text(source, encoding="utf-8")
        forbidden = sorted(set(re.findall(r"\b(?:sorry|admit|axiom|unsafe|native_decide)\b", _mask(source))))
        if forbidden:
            report["status"] = "rejected"
            raise ValueError("Bridge содержит запрещённые для сертификата конструкции: " + ", ".join(forbidden))
        if not isinstance(targets, list) or not targets or any(not isinstance(t, str) or not t.strip() or len(t) > 500 for t in targets):
            raise ValueError("Укажите полные имена проверяемых теорем (например Bridge.energy_correspondence).")
        if not inspection or not inspection.get("semantic_extraction"):
            raise ValueError("Сначала требуется успешный семантический разбор двух входных файлов.")
        if len(inspection.get("files", [])) != 2:
            raise ValueError("Отчёт анализа должен содержать два входа.")
        files = []
        for file in inspection["files"]:
            path = Path(file["source_path"])
            raw = path.read_text(encoding="utf-8")
            if _sha(raw) != file["sha256"]:
                raise ValueError("Входной файл изменился после анализа; выполните анализ заново: " + file["name"])
            files.append({"name": file["name"], "content": raw})
        files = _validate_files(files)
        report["input_sha256"] = {f["name"]: f["sha256"] for f in files}
        context, env = _prepare(context or inspection.get("context"), workspace)
        report["context"] = context
        _compile_inputs(files, context, env, workspace, report["diagnostics"])
        _run(context, env, workspace, "Bridge.lean", report["diagnostics"])
        exported = _export(["Bridge"], [f["module"] for f in files], context, env, workspace, report["diagnostics"])
        declarations = {d["name"]: d for d in exported["declarations"]}
        target_results = []
        for target in targets:
            if target not in declarations:
                raise ValueError("В Bridge.lean не найдена декларация: " + target)
            d = declarations[target]
            if d["kind"] != "theorem":
                raise ValueError("Цель должна быть теоремой, а не определением: " + target)
            unexpected = sorted(set(d["axioms"]) - ALLOWED_AXIOMS)
            if unexpected:
                report["status"] = "rejected"
                raise ValueError("Теорема зависит от недопустимых аксиом: " + ", ".join(unexpected))
            if d.get("dependency_walk_truncated"):
                raise ValueError("Обход зависимостей достиг лимита; участие входов не подтверждено.")
            reachable = set(d["reachable_input_declarations"])
            coverage = {}
            for file in inspection["files"]:
                coverage[file["name"]] = sorted(reachable & {c["name"] for c in file["declarations"]})
            selected = inspection.get("selected_targets", [])
            selected_coverage = {}
            for i, file in enumerate(inspection["files"]):
                wanted = selected[i].strip() if i < len(selected) and isinstance(selected[i], str) else ""
                if wanted:
                    selected_coverage[wanted] = wanted in reachable
            target_results.append({"name": target, "type": d["type"], "axioms": d["axioms"],
                                   "input_coverage": coverage, "type_dependencies": d["type_dependencies"],
                                   "selected_target_coverage": selected_coverage,
                                   "both_inputs_participate": all(coverage.values()) and all(selected_coverage.values())})
        report["target_results"] = target_results
        report["axioms"] = sorted({a for t in target_results for a in t["axioms"]})
        report["lean_compilation_success"] = True
        report["olean_sha256"] = _sha((workspace / "Bridge.olean").read_bytes())
        if not all(t["both_inputs_participate"] for t in target_results):
            report["status"] = "unrelated"
            report["error"] = "Lean проверил теорему, но участие обоих входных модулей или выбранных деклараций не подтверждено. Это не сертификат связи выбранной пары."
        else:
            report.update(status="verified", success=True)
    except (ValueError, RuntimeError, OSError, subprocess.SubprocessError, KeyError) as error:
        report["error"] = str(error)
    report["checked_at"] = _now()
    _write_json(workspace / "verification.json", report)
    return report


def load_examples():
    result = []
    for manifest in sorted((ROOT / "examples").glob("*/example.json")):
        item = json.loads(manifest.read_text(encoding="utf-8"))
        item["files"] = [{"name": name, "content": (manifest.parent / name).read_text(encoding="utf-8")} for name in item["files"]]
        if item.get("bridge_file"):
            item["bridge_source"] = (manifest.parent / item.pop("bridge_file")).read_text(encoding="utf-8")
        story = manifest.parent / "story.json"
        if story.is_file():
            item["story"] = json.loads(story.read_text(encoding="utf-8"))
        item["context"] = default_context()
        result.append(item)
    return result
