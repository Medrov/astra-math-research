"""Recheck uploaded Lean source modules in isolation and export reproducible source files."""
from __future__ import annotations

from contextlib import contextmanager
from graphlib import CycleError, TopologicalSorter
import hashlib
import io
import json
import os
from pathlib import Path
import re
import shutil
import signal
import stat
import subprocess
import sys
import tempfile
import threading
import time
import uuid
import zipfile
import zlib

import lean_service
import research_lean


MAX_UPLOAD_BYTES = 2 * 1024 * 1024
MAX_FILE_BYTES = 250_000
MAX_FILES = 32
MODULE = r"[A-Za-z_][A-Za-z0-9_]*"
MODULE_NAME = re.compile(rf"{MODULE}(?:\.{MODULE})*")
TARGET_NAME = re.compile(r"[A-Za-z_][A-Za-z0-9_']*(?:\.[A-Za-z_][A-Za-z0-9_']*)*")
RESERVED = {"Init", "Lean", "Std", "Lake", "Mathlib", "AtlasInspect", "AtlasDump", "SHAIMContract"}
SLOTS = threading.BoundedSemaphore(2)
BUNDLE_MANIFEST = "SHAIM-lean-bundle.json"
BUNDLE_FORMAT = "shaim-independent-lean-v1"


def _sha(data):
    return hashlib.sha256(data).hexdigest()


def _bundle_name(name):
    if not isinstance(name, str) or not name or len(name) > 200 or any(
        ch in '/\\' or ord(ch) < 32 or ord(ch) == 127 for ch in name
    ):
        raise ValueError("Некорректное имя загружаемого файла.")
    return name


def _entries(filename, data):
    suffix = Path(filename).suffix.lower()
    if suffix == ".lean":
        if Path(filename).stem.casefold() == "lakefile":
            raise ValueError("Загрузите модули с доказательствами без конфигурации Lake.")
        name = filename if lean_service.MODULE_FILE.fullmatch(filename) else "Input.lean"
        return {name: data}, None
    if suffix != ".zip":
        raise ValueError("Поддерживаются исходники .lean и ZIP с модулями Lean.")
    entries, manifest = {}, None
    try:
        with zipfile.ZipFile(io.BytesIO(data)) as archive:
            members = archive.infolist()
            if len(members) > MAX_FILES * 8:
                raise ValueError("Слишком много записей в ZIP.")
            total = 0
            for item in members:
                parts = item.orig_filename.removesuffix("/").split("/")
                if (len(parts) > 16 or len(item.orig_filename) > 240 or "\\" in item.orig_filename
                        or any(p in ("", ".", "..") or ":" in p or any(ord(c) < 32 for c in p) for p in parts)):
                    raise ValueError("Недопустимый путь в ZIP.")
                mode = stat.S_IFMT(item.external_attr >> 16)
                if mode not in (0, stat.S_IFREG, stat.S_IFDIR) or item.flag_bits & 1:
                    raise ValueError("В ZIP допускаются обычные незашифрованные файлы.")
                if item.is_dir() or parts[0] == "__MACOSX" or parts[-1] == ".DS_Store":
                    continue
                is_manifest = item.filename == BUNDLE_MANIFEST
                if not is_manifest and (not item.filename.endswith(".lean") or parts[-1].casefold() == "lakefile.lean"):
                    raise ValueError("ZIP должен содержать только исходники .lean без конфигурации Lake.")
                total += item.file_size
                max_entry = MAX_UPLOAD_BYTES if is_manifest else MAX_FILE_BYTES
                if item.file_size > max_entry or total > MAX_UPLOAD_BYTES or (not is_manifest and len(entries) >= MAX_FILES):
                    raise ValueError("ZIP превышает лимит 32 модулей, 250 КБ на модуль и 2 МиБ в сумме.")
                if item.filename in entries or (is_manifest and manifest is not None):
                    raise ValueError("Имя модуля в ZIP повторяется.")
                if item.compress_type not in (zipfile.ZIP_DEFLATED, zipfile.ZIP_STORED):
                    raise ValueError("ZIP должен использовать обычное сжатие DEFLATE или хранение без сжатия.")
                with archive.open(item) as source:
                    content = source.read(max_entry + 1)
                if len(content) != item.file_size:
                    raise ValueError("Размер файла в ZIP не соответствует содержимому.")
                if is_manifest:
                    manifest = content
                else:
                    entries[item.filename] = content
    except (zipfile.BadZipFile, EOFError, RuntimeError, zlib.error) as error:
        raise ValueError("Повреждённый или неподдерживаемый ZIP.") from error
    return entries, manifest


def _modules(filename, data):
    if not isinstance(data, bytes) or not 0 < len(data) <= MAX_UPLOAD_BYTES:
        raise ValueError("Размер вложения должен быть от 1 байта до 2 МиБ.")
    entries, manifest = _entries(filename, data)
    if not entries:
        raise ValueError("В архиве нет файлов .lean.")
    if manifest is not None:
        return _independent_modules(entries, manifest)
    return _source_modules(entries)


def _source_modules(entries):
    files = []
    for path, raw in entries.items():
        if len(raw) > MAX_FILE_BYTES:
            raise ValueError("Максимальный размер одного исходника — 250 КБ.")
        try:
            source = raw.decode("utf-8")
        except UnicodeDecodeError as error:
            raise ValueError("Исходники Lean должны быть в UTF-8.") from error
        masked = lean_service._mask(source)
        imports = []
        # Keep local imports out of the single-candidate validator. Validate their
        # grammar and allowlist separately, including dependency order below.
        for match in re.finditer(r"(?m)^[ \t]*import\b([^\n]*)", masked):
            names = match.group(1).split()
            if not names or any(not MODULE_NAME.fullmatch(m) for m in names):
                raise ValueError("Ожидается строка import с полными именами модулей.")
            imports.extend(names)
        body = re.sub(r"(?m)^[ \t]*import\b[^\n]*", "", masked)
        if re.search(r"\b(?:import|prelude|meta|attribute|simproc|builtin_simproc|deriving_handler)\b", body):
            raise ValueError("Команды расширения среды и нестандартная форма import не поддерживаются.")
        research_lean._validate_source(body if body.strip() else "-- imports only")
        files.append(dict(path=path, content=source, sha256=_sha(raw), imports=imports))

    # Finder often wraps the actual module root in one extra folder. Select the
    # shallowest shared root in which every local import has an exact match.
    prefix = ""
    while True:
        names = [f["path"][len(prefix):] for f in files]
        if all(lean_service.MODULE_FILE.fullmatch(name) for name in names):
            modules = [name[:-5].replace("/", ".") for name in names]
            if len({m.casefold() for m in modules}) != len(modules):
                raise ValueError("Имена модулей должны различаться, включая регистр файловой системы.")
            if any(m.split(".")[0].casefold() in {v.casefold() for v in RESERVED} for m in modules):
                raise ValueError("Загруженный модуль использует зарезервированное имя.")
            if all(m in modules or m.split(".", 1)[0] in ("Init", "Std", "Mathlib")
                   for f in files for m in f["imports"]):
                for f, name, module in zip(files, names, modules):
                    f.update(name=name, module=module)
                by_module = {f["module"]: f for f in files}
                order = TopologicalSorter({m: [i for i in f["imports"] if i in by_module]
                                           for m, f in by_module.items()})
                try:
                    return [by_module[m] for m in order.static_order()]
                except CycleError as error:
                    raise ValueError("Циклические импорты между входными файлами.") from error
        heads = {name.split("/", 1)[0] for name in names}
        if len(heads) != 1 or any("/" not in name for name in names):
            raise ValueError("Импорты должны вести в приложенные модули или закреплённые Init, Std и Mathlib.")
        prefix += heads.pop() + "/"


def _independent_modules(entries, raw_manifest):
    try:
        manifest = json.loads(raw_manifest.decode("utf-8"))
    except (ValueError, RecursionError) as error:
        raise ValueError("Некорректный JSON манифеста доказательств.") from error
    if not isinstance(manifest, dict) or manifest.get("format") != BUNDLE_FORMAT:
        raise ValueError("Неизвестный формат манифеста доказательств.")
    specs = manifest.get("entries")
    if not isinstance(specs, list) or not 0 < len(specs) <= len(entries):
        raise ValueError("Манифест должен описывать каждый исходник.")
    files, groups, seen = [], set(), set()
    for spec in specs:
        if not isinstance(spec, dict) or not isinstance(spec.get("root"), str):
            raise ValueError("Некорректная запись манифеста доказательств.")
        group = spec["root"]
        if not re.fullmatch(MODULE, group) or group.casefold() in groups:
            raise ValueError("Имена групп в манифесте должны быть различными.")
        groups.add(group.casefold())
        sources = spec.get("sources")
        if not isinstance(sources, list) or not 0 < len(sources) <= MAX_FILES:
            raise ValueError("Нужен список модулей доказательства.")
        local = {}
        for source in sources:
            if not isinstance(source, dict) or not isinstance(source.get("name"), str):
                raise ValueError("Некорректное имя модуля в манифесте.")
            name = source["name"]
            member = group + "/" + name
            if not lean_service.MODULE_FILE.fullmatch(name) or member not in entries or member.casefold() in seen:
                raise ValueError("Запись манифеста ссылается на отсутствующий или повторяющийся файл.")
            if source.get("sha256") != _sha(entries[member]):
                raise ValueError("Контрольная сумма исходника не совпадает с манифестом.")
            seen.add(member.casefold())
            local[name] = entries[member]
        target, statement = _contract(spec.get("target"), spec.get("expected_statement"))
        if not target or not statement:
            raise ValueError("В манифесте для каждого доказательства нужны цель и тип.")
        for f in _source_modules(local):
            files.append(dict(f, name=group + "/" + f["path"], single_name=f["name"], group=group,
                              bundle_contract=dict(target=target, expected_statement=statement)))
    if len(seen) != len(entries):
        raise ValueError("Не все исходники перечислены в манифесте.")
    return files


def _contract(target, statement):
    if not isinstance(target, str) or not isinstance(statement, str):
        raise ValueError("Имя теоремы и тип должны быть строками.")
    target, statement = target.strip(), statement.strip()
    if target and (not TARGET_NAME.fullmatch(target) or len(target) > 300):
        raise ValueError("Укажите полное Lean-имя теоремы.")
    if statement:
        if not target or len(statement) > 30000 or re.search(r":=|[#;]|^\s*(?:import|end|command|def|theorem|example|attribute)\b", statement, re.M):
            raise ValueError("Для контракта нужны имя теоремы и один Lean-тип.")
        research_lean._validate_source(statement)
    return target, statement


def _isolated_command(binary, workspace, scratch, libraries):
    read_paths = list(dict.fromkeys([binary.parent.parent, *libraries, workspace]))
    if sys.platform == "darwin" and Path("/usr/bin/sandbox-exec").is_file():
        quote = lambda path: json.dumps(str(path), ensure_ascii=False)
        reads = " ".join("(subpath " + quote(p) + ")" for p in read_paths)
        profile = (
            '(version 1)(deny default)(allow sysctl-read)(allow file-read-metadata)'
            '(allow process-exec (literal ' + quote(binary) + '))'
            '(allow file-read* (literal "/")(literal "/dev/urandom")(literal "/dev/null")'
            '(subpath "/System/Library")(subpath "/System/Volumes/Preboot/Cryptexes")'
            '(subpath "/usr/lib") ' + reads + ')'
            '(allow file-write* (subpath ' + quote(scratch) + '))'
        )
        return ["/usr/bin/sandbox-exec", "-p", profile, str(binary)]
    if sys.platform.startswith("linux") and shutil.which("bwrap"):
        args = [shutil.which("bwrap"), "--die-with-parent", "--unshare-all", "--new-session",
                "--proc", "/proc", "--dev", "/dev"]
        for path in [Path("/usr"), Path("/lib"), Path("/lib64"), *read_paths]:
            if path.exists():
                args += ["--ro-bind", str(path), str(path)]
        return args + ["--bind", str(scratch), str(scratch), "--chdir", str(workspace), str(binary)]
    raise RuntimeError("Для изолированной проверки нужен sandbox-exec (macOS) или bubblewrap (Linux).")


def _check_cancelled(cancelled):
    if research_lean._cancelled(cancelled):
        raise InterruptedError("Проверка Lean отменена.")


@contextmanager
def _slot(cancelled, deadline):
    while True:
        _check_cancelled(cancelled)
        if time.monotonic() >= deadline:
            raise TimeoutError("Общий лимит времени Lean исчерпан в очереди.")
        if SLOTS.acquire(timeout=0.1):
            break
    try:
        _check_cancelled(cancelled)
        yield
    finally:
        SLOTS.release()


def _run_step(filename, output, context, env, work, scratch, deadline, diagnostics, cancelled=None):
    _check_cancelled(cancelled)
    binary = Path(context["lean"]).resolve()
    libraries = [Path(p).resolve() for p in context["lean_search_paths"] if Path(p).resolve() != work]
    command = _isolated_command(binary, work, scratch, libraries)
    command += ["-j", "2"]
    if output:
        command += ["-o", str(scratch / "result.olean")]
    command.append(filename)
    # Apply resource limits before exec, without preexec_fn in the HTTP server's threads.
    wrapper = ("import os,resource,sys; "
               "resource.setrlimit(resource.RLIMIT_FSIZE,(64<<20,64<<20)); "
               "os.execv(sys.argv[1],sys.argv[1:])")
    started = time.monotonic()
    expires = min(started + 90, deadline)
    if expires <= started:
        raise TimeoutError("Общий лимит времени Lean исчерпан.")
    with tempfile.TemporaryFile() as log:
        proc = subprocess.Popen([sys.executable, "-I", "-c", wrapper, *command], cwd=work,
                                env={"LEAN_PATH": env["LEAN_PATH"], "LANG": "en_US.UTF-8"},
                                stdout=log, stderr=subprocess.STDOUT, stdin=subprocess.DEVNULL, start_new_session=True)
        try:
            while proc.poll() is None:
                _check_cancelled(cancelled)
                remaining = expires - time.monotonic()
                if remaining <= 0:
                    raise TimeoutError("Lean превысил лимит времени при проверке " + filename)
                try:
                    proc.wait(timeout=min(remaining, 0.1) if cancelled is not None else remaining)
                except subprocess.TimeoutExpired:
                    pass
            _check_cancelled(cancelled)
        finally:
            if proc.poll() is None:
                try:
                    os.killpg(proc.pid, signal.SIGKILL)
                except ProcessLookupError:
                    pass
                proc.wait()
        log.seek(max(0, log.tell() - 8000))
        diag = dict(file=filename, exit_code=proc.returncode, stdout=log.read().decode("utf-8", "replace"),
                    elapsed_seconds=round(time.monotonic() - started, 3))
        diagnostics.append(diag)
        if proc.returncode:
            raise ValueError("Lean отклонил " + filename + ". " + diag["stdout"][-700:])
    if output:
        result = scratch / "result.olean"
        if result.is_symlink() or not result.is_file():
            raise ValueError("Lean не создал обычный файл .olean.")
        result.replace((work / filename).with_suffix(".olean"))


def _check(files, target, statement, report, deadline, extra_statement="", cancelled=None):
    _check_cancelled(cancelled)
    with tempfile.TemporaryDirectory(prefix="shaim-recheck-") as folder:
        work = Path(folder).resolve()
        context, env = lean_service._prepare({"project_root": ""}, work)
        report["lean_version"] = context["lean_version"]
        report["mathlib_revision"] = context.get("mathlib_revision")
        report["mathlib_manifest_sha256"] = context.get("mathlib_manifest_sha256")
        libraries = [Path(p) for p in context["lean_search_paths"] if Path(p) != work]
        libraries.append(Path(context["lean"]).resolve().parents[1] / "lib/lean")

        def step(filename, output=True, export_command=None):
            with tempfile.TemporaryDirectory(dir=work, prefix="out-") as temp:
                scratch = Path(temp)
                if export_command is not None:
                    path = scratch / "declarations.json"
                    (work / filename).write_text(export_command + json.dumps(str(path)) + "\n", encoding="utf-8")
                _run_step(filename, output, context, env, work, scratch, deadline, report["diagnostics"], cancelled)
                if export_command is not None:
                    if path.is_symlink() or not path.is_file() or path.stat().st_size > 16_000_000:
                        raise ValueError("Некорректный результат экспорта деклараций.")
                    return json.loads(path.read_text())

        for f in files:
            path = work / f["name"]
            if any((library / Path(f["name"]).with_suffix(".olean")).exists() for library in libraries):
                raise ValueError("Имя загруженного модуля совпадает с установленной библиотекой: " + f["module"])
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_bytes(f["content"].encode("utf-8"))
            step(f["name"])
        report["compilation_success"] = True
        shutil.copyfile(lean_service.ROOT / "tools/AtlasInspect.lean", work / "AtlasInspect.lean")
        step("AtlasInspect.lean")
        modules = [f["module"] for f in files]
        imports = "".join("import " + m + "\n" for m in modules)
        command = ("import AtlasInspect\n" + imports + "set_option maxRecDepth 8192\n"
                   "set_option maxHeartbeats 2000000\n#atlas_export " + json.dumps(modules) + " [] ")
        decls = step("AtlasDump.lean", False, command)["declarations"]
        audit = research_lean._audit_declarations(decls, "\n".join(f["content"] for f in files), target)
        report["audit"] = audit
        if audit["status"] != "passed":
            raise ValueError("Проверка аксиом или безопасных деклараций не пройдена.")
        # Keep private helpers and constructors in the dependency graph: a target
        # can refer to an uploaded module by way of either.
        fields = ("name", "kind", "module", "type", "axioms", "dependencies", "type_dependencies", "unsafe")
        report["declarations"] = [{k: d[k] for k in fields} for d in decls]
        if target:
            declaration = next((d for d in decls if d["name"] == target and d["kind"] == "theorem"), None)
            if declaration is None:
                raise ValueError("Указанная теорема не найдена среди деклараций вложения.")
            report["actual_statement"] = declaration["type"]
        if statement:
            # Definitional equality of complete types, including all hypotheses.
            contract = (imports + "universe u v w\nset_option autoImplicit false\n"
                        "private def SHAIMActualType.{a} {α : Sort a} (_ : α) := α\n")
            for checked_type in dict.fromkeys([statement, extra_statement]):
                if checked_type:
                    contract += "example : SHAIMActualType (@" + target + ") = (" + checked_type + ") := rfl\n"
            (work / "SHAIMContract.lean").write_text(contract)
            step("SHAIMContract.lean", False)
            report["target_preserved"] = True
        if target:
            report["kernel_recheck"] = dict(status="failed", target=target)
            # Keep previously valid uploads that happen to use the driver's name.
            driver = "SHAIMKernel"
            while (work / (driver + ".lean")).exists():
                driver += "Check"
            raw = step(driver + ".lean", False, research_lean.kernel_command(modules, target))
            hashes = {f["module"]: _sha(f["content"].encode()) for f in files}
            report["kernel_recheck"] = research_lean.kernel_certificate(raw, target, hashes, statement, context)
        report["status"] = "verified" if statement else "compiled"


def _check_bundle(files, meta, report, deadline, cancelled=None):
    target = meta["target"]
    groups = {}
    for f in files:
        groups.setdefault(f["group"], []).append(f)
    matches = [group for group, members in groups.items() if members[0]["bundle_contract"]["target"] == target]
    if target and len(matches) != 1:
        raise ValueError("Внешний контракт должен однозначно выбрать одну цель из манифеста.")
    report.update(bundle_format=BUNDLE_FORMAT, checks=[])
    for group, members in groups.items():
        spec = members[0]["bundle_contract"]
        check = dict(name=group, **spec, contract_source="bundle", status="failed", audit={"status": "pending"},
                     target_preserved=False, diagnostics=[], declarations=[], compilation_success=False)
        try:
            _check([dict(f, name=f["single_name"]) for f in members], spec["target"], spec["expected_statement"], check, deadline,
                   meta["expected_statement"] if group in matches else "", cancelled)
        finally:
            report["checks"].append({k: check[k] for k in
                                      ("name", "target", "expected_statement", "contract_source", "status", "target_preserved", "kernel_recheck")
                                      if k in check})
            report["diagnostics"].extend(dict(d, group=group) for d in check["diagnostics"])
        report["declarations"].extend(dict(d, group=group) for d in check["declarations"])
        report.update(lean_version=check["lean_version"], mathlib_revision=check["mathlib_revision"],
                      mathlib_manifest_sha256=check["mathlib_manifest_sha256"])
        if group in matches:
            report["actual_statement"] = check["actual_statement"]
            report["kernel_recheck"] = check["kernel_recheck"]
    report.update(compilation_success=True, audit={"status": "passed", "files_checked": len(files)},
                  target_preserved=bool(meta["expected_statement"]),
                  status="verified" if meta["expected_statement"] else "compiled")


class LeanFiles:
    """Immutable originals; every recheck recompiles all modules in a fresh directory."""

    def __init__(self, root):
        self.root = Path(root).resolve()

    def _folder(self, attachment_id):
        if not isinstance(attachment_id, str) or not re.fullmatch("[0-9a-f]{32}", attachment_id):
            raise ValueError("Некорректный ID вложения.")
        folder = self.root / attachment_id
        if not (folder / "input.json").is_file():
            raise FileNotFoundError("Вложение не найдено.")
        return folder

    def _load(self, attachment_id):
        folder = self._folder(attachment_id)
        meta = json.loads((folder / "input.json").read_text())
        data = (folder / "original").read_bytes()
        if _sha(data) != meta["sha256"]:
            raise ValueError("Контрольная сумма вложения изменилась.")
        return meta, _modules(meta["filename"], data)

    def upload(self, filename, data, target="", expected_statement="", *, cancelled=None):
        return self._store(filename, data, target, expected_statement, cancelled=cancelled)

    def _store(self, filename, data, target, expected_statement, origin=None, cancelled=None):
        filename = _bundle_name(filename)
        target, expected_statement = _contract(target, expected_statement)
        files = _modules(filename, data)
        attachment_id = uuid.uuid4().hex
        meta = dict(id=attachment_id, filename=filename, sha256=_sha(data), target=target, expected_statement=expected_statement,
                    files=[{k: f[k] for k in ("name", "module", "sha256")} for f in files])
        if origin:
            meta["origin"] = origin
        self.root.mkdir(parents=True, exist_ok=True)
        folder = self.root / attachment_id
        folder.mkdir(mode=0o700)
        (folder / "original").write_bytes(data)
        (folder / "input.json").write_text(json.dumps(meta, ensure_ascii=False))
        return self._verify(meta, files, cancelled)

    def _verify(self, meta, files, cancelled=None):
        report = dict(meta, status="failed", compilation_success=False, target_preserved=False,
                      contract_source="bundle" if meta.get("origin") else "user" if meta["expected_statement"] else None,
                      audit={"status": "pending"}, declarations=[], diagnostics=[])
        deadline = time.monotonic() + 180
        try:
            with _slot(cancelled, deadline):
                if "bundle_contract" in files[0]:
                    _check_bundle(files, meta, report, deadline, cancelled)
                else:
                    _check(files, meta["target"], meta["expected_statement"], report, deadline, cancelled=cancelled)
                    if meta.get("origin"):
                        report["checks"] = [dict(name=meta["origin"]["group"], contract_source="bundle",
                                                 target=meta["target"], expected_statement=meta["expected_statement"],
                                                 status="verified", target_preserved=True)]
                        report.update(status="compiled", target_preserved=False)
                _check_cancelled(cancelled)
        except InterruptedError as error:
            report.update(status="cancelled", error=str(error), target_preserved=False)
        except (OSError, TimeoutError, ValueError, RuntimeError, KeyError, subprocess.SubprocessError) as error:
            report["error"] = str(error)
        report["checked_at"] = research_lean._now()
        folder = self._folder(meta["id"])
        path = folder / (uuid.uuid4().hex + ".tmp")
        path.write_text(json.dumps(report, ensure_ascii=False), encoding="utf-8")
        path.replace(folder / "report.json")
        return report

    def get(self, attachment_id):
        return json.loads((self._folder(attachment_id) / "report.json").read_text())

    def recheck(self, attachment_id):
        return self._verify(*self._load(attachment_id))

    def select_member(self, attachment_id, index):
        meta, files = self._load(attachment_id)
        report = self.get(attachment_id)
        checks = report.get("checks", [])
        if (report["status"] not in ("verified", "compiled") or report.get("bundle_format") != BUNDLE_FORMAT
                or meta["sha256"] != report["sha256"]):
            raise ValueError("Выберите группу в успешно проверенном архиве программы.")
        if type(index) is not int or not 0 <= index < len(checks):
            raise ValueError("Указанная группа отсутствует в манифесте.")
        checked = checks[index]
        if not checked["target_preserved"] or checked["status"] != "verified":
            raise ValueError("Тип выбранного результата не прошёл проверку.")
        group = checked["name"]
        members = [f for f in files if f["group"] == group]
        if not members:
            raise ValueError("Исходники выбранного результата отсутствуют.")
        if len(members) == 1 and "/" not in members[0]["single_name"]:
            name, data = members[0]["single_name"], members[0]["content"].encode()
        else:
            name = group + ".zip"
            out = io.BytesIO()
            with zipfile.ZipFile(out, "w", zipfile.ZIP_DEFLATED) as archive:
                for f in members:
                    archive.writestr(f["single_name"], f["content"])
            data = out.getvalue()
        origin = dict(id=attachment_id, sha256=meta["sha256"], index=index, group=group, contract_source="bundle")
        return self._store(name, data, checked["target"], checked["expected_statement"], origin)

    def evidence(self, attachment_id):
        report = self.get(attachment_id)
        meta, files = self._load(attachment_id)
        if report["status"] not in ("verified", "compiled") or report["sha256"] != meta["sha256"]:
            raise ValueError("Для исследовательской программы нужен успешно проверенный комплект исходников.")
        text = "\n".join("-- " + f["name"] + "\n" + f["content"] for f in files)
        public = [d for d in report["declarations"] if d["kind"] in ("def", "theorem", "inductive", "opaque")
                  and not any(part.startswith("_") for part in d["name"].split("."))]
        return dict(id=attachment_id, name=meta["filename"], files=meta["files"], sha256=meta["sha256"],
                    bundle_format=report.get("bundle_format"),
                    contract_source="bundle" if meta.get("origin") else "user" if meta.get("expected_statement") else None,
                    status=report["status"], target=meta["target"], expected_statement=meta["expected_statement"],
                    target_preserved=report["target_preserved"], order=[f["module"] for f in files],
                    declarations=[{"name": d["name"], "type": d["type"][:600]} for d in public[:24]],
                    source=text[:12000], source_truncated=len(text) > 12000)

    def download(self, attachment_id):
        meta, files = self._load(attachment_id)
        if "bundle_contract" in files[0]:
            # Preserve the hash-checked group manifest and module paths for replay.
            original = (self._folder(attachment_id) / "original").read_bytes()
            if _sha(original) != meta["sha256"]:
                raise ValueError("Контрольная сумма вложения изменилась.")
            return meta["filename"], original
        if len(files) == 1:
            return Path(files[0]["name"]).name, files[0]["content"].encode()
        output = io.BytesIO()
        with zipfile.ZipFile(output, "w", zipfile.ZIP_DEFLATED) as archive:
            for f in files:
                archive.writestr(f["name"], f["content"])
        return Path(meta["filename"]).stem + ".zip", output.getvalue()

    @staticmethod
    def for_run(run, run_dir):
        verification = (run.get("result") or {}).get("verification") or {}
        if not (isinstance(verification, dict) and verification.get("success") and verification.get("target_preserved") and
                verification.get("audit", {}).get("status") == "passed" and verification.get("workspace")):
            raise ValueError("У запуска пока нет принятого Lean-исходника с проверенным типом.")
        folder = Path(run_dir).resolve()
        workspace = Path(verification["workspace"]).resolve()
        bundle = verification.get("bundle_file")
        name = bundle or "Candidate.lean"
        source = (workspace / name).resolve()
        if not workspace.is_relative_to(folder) or not source.is_relative_to(workspace) or not source.is_file():
            raise ValueError("Проверенный исходник отсутствует в каталоге запуска.")
        raw = source.read_bytes()
        if _sha(raw) != verification.get("bundle_sha256" if bundle else "source_sha256"):
            raise ValueError("Контрольная сумма доказательства не совпадает с проверкой.")
        return ("sources.zip" if bundle else "Candidate.lean"), raw

    def for_program(self, program_detail, research):
        accepted = [t for t in program_detail.get("tasks", []) if t.get("formal_outcome") in ("proved", "refuted")]
        ids = list(dict.fromkeys(t["run_id"] for t in accepted if t.get("run_id")))
        if not ids:
            raise ValueError("У программы пока нет результатов с проверенным Lean-типом.")
        if len(ids) > MAX_FILES:
            raise ValueError("Комплект превышает лимит 32 исходников. Отдельные доказательства доступны в карточках.")
        output = io.BytesIO()
        entries, size, count = [], 0, 0
        with zipfile.ZipFile(output, "w", zipfile.ZIP_DEFLATED) as archive:
            for index, run_id in enumerate(ids, 1):
                run = research.get(run_id)
                filename, raw = self.for_run(run, research.folder(run_id))
                if len(ids) == 1:
                    return filename, raw
                group = f"Result_{index:02d}"
                verification = run["result"]["verification"]
                members = _modules(filename, raw)
                if any("bundle_contract" in f for f in members):
                    raise ValueError("Вложенные архивы независимых программ не поддерживаются.")
                sources = []
                for f in members:
                    content = f["content"].encode()
                    size += len(content)
                    count += 1
                    if count > MAX_FILES or size > MAX_UPLOAD_BYTES:
                        raise ValueError("Превышен лимит архива. Отдельные доказательства доступны в карточках.")
                    sources.append(dict(name=f["name"], sha256=f["sha256"]))
                    archive.writestr(group + "/" + f["name"], content)
                entries.append(dict(root=group, target=verification["target"], expected_statement=verification["expected_statement"],
                                    sources=sources))
            manifest = json.dumps(dict(format=BUNDLE_FORMAT, entries=entries), ensure_ascii=False).encode("utf-8")
            if size + len(manifest) > MAX_UPLOAD_BYTES:
                raise ValueError("Результаты превышают лимит 2 МиБ. Отдельные доказательства доступны в карточках.")
            archive.writestr(BUNDLE_MANIFEST, manifest)
        data = output.getvalue()
        if len(data) > MAX_UPLOAD_BYTES:
            raise ValueError("ZIP превышает лимит загрузки 2 МиБ. Доказательства доступны по отдельности.")
        return "SHAIM-proofs.zip", data
