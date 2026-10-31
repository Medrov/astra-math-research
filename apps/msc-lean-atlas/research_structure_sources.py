"""One immutable Lean input, freshly inspected and reused as StructureInput.

This conservative source filter is not a sandbox. Only Mathlib/Init/Std imports
are accepted for the uploaded input; paths, local project imports, dependencies
supplied as files, and arbitrary executable elaborators are outside this MVP.
The built-in published example has a separate exact-content gate and freshly
compiled pinned project dependencies; uploads cannot enable that exception.
Previously proved input theorems remain visible: this is reuse, not rediscovery.
"""
from __future__ import annotations

from datetime import datetime, timezone
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import uuid

import lean_service


MODULE = "StructureInput"
PIN_PREFIX = "-- atlas-structure-source-sha256: "
SOURCE_ID = re.compile(r"[0-9a-f]{32}")
HASH = re.compile(r"[0-9a-f]{64}")
DEFINITION_KINDS = {"def", "opaque", "inductive"}
PUBLISHED_EXAMPLE = 'published_associator_laplacian'


def _sha(value):
    return hashlib.sha256(value.encode("utf-8") if isinstance(value, str) else value).hexdigest()


def _json(value):
    return json.dumps(value, ensure_ascii=False, sort_keys=True, separators=(",", ":"))


def validate_input(content):
    import research_lean
    if isinstance(content, str):
        content = content.removeprefix("\ufeff")
    research_lean._validate_source(content)
    for module in lean_service._imports(content):
        if module not in {"Mathlib", "Init", "Std"} and not module.startswith("Mathlib."):
            raise ValueError("Входной StructureInput допускает только импорты Mathlib/Init/Std: " + module)
    return content


def prepared_published_source():
    """Only this repository-owned source can use the published project import."""
    import research_published_example as published
    return (published.ROOT / 'research_fixtures' / published.FILE).read_text(encoding='utf-8-sig')


def _validate_prepared_content(content, example_id):
    import research_lean
    import research_project_library as library
    if example_id != PUBLISHED_EXAMPLE or not isinstance(content, str) or content != prepared_published_source():
        raise ValueError('Готовый источник должен точно совпадать с опубликованным примером репозитория.')
    research_lean._validate_source(content)
    if lean_service._imports(content) != [library.ENTRY_POINT]:
        raise ValueError('Недопустимые импорты готового опубликованного источника.')
    if library.pinned_fingerprint(content, required=True) != library.fingerprint():
        raise ValueError('Закреплённые исходники опубликованного примера изменились; нужен новый согласованный снимок.')
    return content


def prepare_source_dependencies(payload, context, env, work, runner, cancelled=None):
    """Prepare only the canonical preset's pinned dependency closure in this run.

    A prior fresh build in this same workspace may already serve a candidate's
    direct project import; it is verified against its manifest before reuse.
    """
    example_id = payload.get('prepared_example_id')
    if example_id is None:
        return None
    import research_project_library as library
    content = _validate_prepared_content(payload.get('content'), example_id)
    expected = library.pinned_fingerprint(content, required=True)
    manifest_path = Path(work) / 'project-library.json'
    if context.get('project_library_fingerprint'):
        if context['project_library_fingerprint'] != expected or not manifest_path.is_file():
            raise ValueError('Сборка проектной библиотеки не соответствует готовому источнику.')
        manifest = json.loads(manifest_path.read_text(encoding='utf-8'))
        if manifest.get('status') != 'complete' or manifest.get('fingerprint') != expected or not manifest.get('fresh_local_build'):
            raise ValueError('Нет успешной свежей сборки проектной библиотеки в этом запуске.')
        for item in manifest['sources']:
            path = (Path(work) / item['path']).resolve()
            if not path.is_relative_to(Path(work).resolve()) or _sha(path.read_bytes()) != item['sha256'] or _sha(path.with_suffix('.olean').read_bytes()) != item['olean_sha256']:
                raise ValueError('Артефакты свежей проектной библиотеки изменились.')
        return manifest
    return library.prepare_library(context, env, work, runner, cancelled, expected_fingerprint=expected)


def pinned_fingerprint(source, required=False):
    lines = [line.strip() for line in source.splitlines() if "atlas-structure-source-sha256:" in line]
    if not lines:
        if required:
            raise ValueError("Нужен SHA-256 pin исходного StructureInput.")
        return None
    if len(lines) != 1 or not re.fullmatch(re.escape(PIN_PREFIX) + r"[0-9a-f]{64}", lines[0]):
        raise ValueError("Pin StructureInput повреждён или указан несколько раз.")
    return lines[0][len(PIN_PREFIX):]


def validate_library_payload(payload):
    """Validate a content payload without opening any supplied filesystem path."""
    import research_lean
    if not isinstance(payload, dict):
        raise ValueError("Нужен снимок содержимого StructureInput, а не путь к файлу.")
    identifier = payload.get("source_id")
    if not isinstance(identifier, str) or not SOURCE_ID.fullmatch(identifier):
        raise ValueError("Некорректный source_id StructureInput.")
    prepared = payload.get('prepared_example_id')
    content = (_validate_prepared_content(payload.get('content'), prepared) if prepared is not None else
               validate_input(payload.get("content")))
    if not isinstance(payload.get("source_sha256"), str) or not HASH.fullmatch(payload["source_sha256"]) or _sha(content) != payload["source_sha256"]:
        raise ValueError("SHA-256 содержимого StructureInput не совпадает со снимком.")
    selected = payload.get("selected_declaration")
    if not isinstance(selected, dict) or selected.get("kind") != "theorem" or not isinstance(selected.get("name"), str) or not research_lean.NAME.fullmatch(selected["name"]):
        raise ValueError("Нужно полное имя выбранной теоремы StructureInput.")
    if not isinstance(selected.get("type"), str) or not selected["type"].strip():
        raise ValueError("Нужен экспортированный тип выбранной теоремы StructureInput.")
    environment = payload.get("environment_fingerprint")
    if not isinstance(environment, str) or not environment or len(environment) > 256:
        raise ValueError("Нужен fingerprint окружения снимка StructureInput.")
    result = dict(source_id=identifier, content=content, source_sha256=payload["source_sha256"],
                selected_declaration={key: selected[key] for key in ("name", "kind", "type")},
                environment_fingerprint=environment)
    if prepared is not None:
        result['prepared_example_id'] = prepared
    return result


def isolated_environment(context, env, work):
    """Exclude compiled local project modules, while keeping pinned mathlib."""
    project = Path(context["project_root"]).resolve() if context.get("project_root") else None
    excluded = {project, (project / ".lake/build/lib/lean").resolve()} if project else set()
    paths = [str(Path(work).resolve())]
    for value in context.get("lean_search_paths", []):
        resolved = Path(value).resolve()
        if resolved not in excluded and str(resolved) not in paths:
            paths.append(str(resolved))
    context["lean_search_paths"] = paths
    env["LEAN_PATH"] = os.pathsep.join(paths)


def _authored(source, declaration):
    return any(declaration["name"] == item["name"] or declaration["name"].endswith("." + item["name"])
               for item in lean_service.lexical_declarations(source))


def definitions(source, declarations):
    return [item for item in declarations if item.get("kind") in DEFINITION_KINDS and _authored(source, item)]


def print_axioms(source, declarations, context, env, work, diagnostics, cancelled=None, *, module=MODULE):
    """Keep literal #print axioms output outside the filtered input/candidate."""
    import research_lean
    if module not in {MODULE, "Candidate"}:
        raise ValueError("Неподдерживаемый модуль команд аудита.")
    names = [item["name"] for item in declarations if item.get("kind") == "theorem" and _authored(source, item)]
    for name in names:
        if any(character in name for character in ("\n", "\r", "«", "»")):
            raise ValueError("Имя теоремы не поддерживается командой аудита: " + name)
    def quoted(name):
        return ".".join(part if part.isdigit() else "«" + part + "»" for part in name.split("."))
    path = Path(work) / (module + "Axioms.lean")
    path.write_text("import " + module + "\n" + "".join("#print axioms " + quoted(name) + "\n" for name in names), encoding="utf-8")
    research_lean._run(context, env, Path(work), path.name, diagnostics, cancelled, output=False)
    return dict(theorems=names, file=path.name, command=diagnostics[-1]["command"], exit_code=diagnostics[-1]["exit_code"],
                stdout=diagnostics[-1]["stdout"], stderr=diagnostics[-1]["stderr"])


def source_usage(target, candidate_declarations, input_declarations, selected_name, content):
    """Only input-defined anchors count; shared Mathlib constants do not."""
    by_name = {item["name"]: item for item in input_declarations + candidate_declarations}
    def closure(seeds):
        seen, todo = set(), list(seeds)
        while todo:
            name = todo.pop()
            if name in seen:
                continue
            seen.add(name)
            if name in by_name:
                todo.extend(by_name[name].get("dependencies", []))
        return seen
    selected = by_name[selected_name]
    relevant = closure(selected.get("type_dependencies", [])) & {item["name"] for item in definitions(content, input_declarations)}
    declaration = by_name[target]
    type_used = closure(declaration.get("type_dependencies", []))
    all_used = closure(declaration.get("dependencies", [])) | type_used
    anchors = relevant | {selected_name}
    type_participation = sorted(type_used & anchors)
    proof_only = sorted((all_used - type_used) & anchors)
    return dict(status="related" if (type_participation or proof_only) else "unrelated",
                selected_theorem=selected_name, selected_theorem_used=selected_name in all_used,
                relevant_definitions=sorted(relevant), used_definitions=sorted(relevant & all_used),
                type_participation=type_participation, proof_only_participation=proof_only,
                reachable_input_declarations=sorted(all_used & {item["name"] for item in input_declarations}),
                scope="selected_theorem_or_input_definitions_in_its_transitive_type_dependencies",
                limitation="Участие в типе или доказательстве — структурный сигнал, не гарантия смысловой связи или новизны.")


class StructureSourceStore:
    def __init__(self, root, environment_fingerprint):
        self.root = Path(root).resolve()
        self.root.mkdir(parents=True, exist_ok=True)
        if not isinstance(environment_fingerprint, str) or not environment_fingerprint or len(environment_fingerprint) > 256:
            raise ValueError("Нужен fingerprint окружения хранилища источников.")
        self.environment_fingerprint = environment_fingerprint

    def _folder(self, source_id):
        if not isinstance(source_id, str) or not SOURCE_ID.fullmatch(source_id):
            raise ValueError("Некорректный идентификатор источника.")
        folder = (self.root / source_id).resolve()
        if not folder.is_relative_to(self.root):
            raise ValueError("Снимок источника находится вне хранилища.")
        return folder

    def create(self, payload):
        if isinstance(payload, dict) and 'prepared_example_id' in payload:
            raise ValueError('Для готового примера используйте отдельный example_id; загрузка файлов не разрешает проектные импорты.')
        return self._create(payload)

    def create_prepared(self, example_id, *, title, provenance):
        if example_id != PUBLISHED_EXAMPLE:
            raise ValueError('Неизвестный готовый проектный источник.')
        return self._create(dict(content=prepared_published_source(), name='PublishedAssociator.lean',
                                 title=title, provenance=provenance), prepared_example_id=example_id)

    def _create(self, payload, *, prepared_example_id=None):
        import research_lean
        if not isinstance(payload, dict):
            raise ValueError("Нужно содержимое одного Lean-исходника.")
        content = (_validate_prepared_content(payload.get('content'), prepared_example_id) if prepared_example_id is not None else
                   validate_input(payload.get("content")))
        name, title = payload.get("name") or "StructureInput.lean", payload.get("title") or payload.get("name") or "Lean-источник"
        if not isinstance(name, str) or len(name) > 200 or any(character in name for character in ("/", "\\", "\n", "\r")):
            raise ValueError("name — название файла, не путь.")
        if not isinstance(title, str) or not title.strip() or len(title) > 500:
            raise ValueError("Некорректное название источника.")
        provenance = payload.get("provenance")
        try:
            if len(_json(provenance).encode("utf-8")) > 16000:
                raise ValueError("Описание происхождения слишком велико.")
        except (TypeError, OverflowError) as error:
            raise ValueError("Происхождение должно быть JSON-данными.") from error
        identifier = uuid.uuid4().hex
        folder = self._folder(identifier)
        folder.mkdir()
        (folder / "StructureInput.lean").write_bytes(content.encode("utf-8"))
        work = folder / "inspection"
        work.mkdir()
        (work / "StructureInput.lean").write_bytes(content.encode("utf-8"))
        inspection = dict(status="failed", success=False, diagnostics=[], declarations=[],
                          audit={"status": "pending"}, workspace=str(work))
        try:
            context, env = lean_service._prepare({}, work)
            isolated_environment(context, env, work)
            inspection["context"] = context
            if prepared_example_id is not None:
                inspection['project_library'] = prepare_source_dependencies(
                    dict(content=content, prepared_example_id=prepared_example_id), context, env, work,
                    lambda filename: research_lean._run(context, env, work, filename, inspection['diagnostics']))
            research_lean._run(context, env, work, "StructureInput.lean", inspection["diagnostics"])
            if (work / "StructureInput.lean").read_bytes() != content.encode("utf-8"):
                raise ValueError("StructureInput изменён во время компиляции.")
            exported = research_lean._export(context, env, work, inspection["diagnostics"], None, modules=[MODULE])
            inspection["declarations"] = exported["declarations"]
            inspection["audit"] = research_lean._audit_declarations(exported["declarations"], content, "")
            if inspection["audit"]["status"] != "passed":
                raise ValueError("Аудит входного источника отклонил аксиомы или unsafe-декларации.")
            inspection["print_axioms"] = print_axioms(content, exported["declarations"], context, env, work, inspection["diagnostics"])
            if (work / "StructureInput.lean").read_bytes() != content.encode("utf-8"):
                raise ValueError("StructureInput изменён во время инспекции.")
            inspection.update(status="complete", success=True, olean_sha256=_sha((work / "StructureInput.olean").read_bytes()))
        except (ValueError, RuntimeError, OSError, TimeoutError, subprocess.SubprocessError) as error:
            inspection["error"] = str(error)
        snapshot = dict(source_id=identifier, status="ready" if inspection["success"] else "failed", name=name, title=title,
                        module=MODULE, source_sha256=_sha(content), environment_fingerprint=self.environment_fingerprint,
                        imports=lean_service._imports(content), provenance=provenance, inspection=inspection,
                        declarations=inspection["declarations"], definitions=definitions(content, inspection["declarations"]),
                        created_at=datetime.now(timezone.utc).isoformat(), reuse_note="Исходные доказательства доступны; это повторное использование, не слепое переоткрытие.")
        if prepared_example_id is not None:
            snapshot['prepared_example_id'] = prepared_example_id
        snapshot["snapshot_sha256"] = _sha(_json(snapshot))
        (folder / "snapshot.json").write_text(json.dumps(snapshot, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
        return self.get(identifier)

    def get(self, source_id):
        folder = self._folder(source_id)
        snapshot = json.loads((folder / "snapshot.json").read_text(encoding="utf-8"))
        expected = snapshot.pop("snapshot_sha256", None)
        if expected != _sha(_json(snapshot)) or snapshot.get("source_id") != source_id:
            raise ValueError("Метаданные снимка источника изменены.")
        snapshot["snapshot_sha256"] = expected
        source_path = (folder / "StructureInput.lean").resolve()
        if not source_path.is_relative_to(folder):
            raise ValueError("Исходник находится вне снимка.")
        content = source_path.read_bytes().decode("utf-8")
        if _sha(content) != snapshot.get("source_sha256"):
            raise ValueError("Содержимое снимка источника изменено.")
        if snapshot.get("environment_fingerprint") != self.environment_fingerprint:
            raise ValueError("Окружение снимка изменилось; нужен новый импорт источника.")
        if snapshot.get('prepared_example_id') is not None:
            _validate_prepared_content(content, snapshot['prepared_example_id'])
        return dict(snapshot, content=content)

    def list_sources(self):
        result = []
        for folder in sorted(self.root.iterdir(), key=lambda path: path.name):
            if not folder.is_dir() or not SOURCE_ID.fullmatch(folder.name):
                continue
            try:
                source = self.get(folder.name)
                summary = {key: source[key] for key in ("source_id", "title", "name", "status", "source_sha256", "environment_fingerprint", "created_at")}
                summary["provenance"] = source.get("provenance")
                result.append(summary)
            except (ValueError, OSError, KeyError) as error:
                result.append(dict(source_id=folder.name, status="stale", error=str(error)))
        return result

    def select(self, source_id, target):
        source = self.get(source_id)
        if source["status"] != "ready" or not source["inspection"]["success"]:
            raise ValueError("Выбирать теорему можно только из успешно проверенного источника.")
        selected = next((item for item in source["declarations"] if item["name"] == target and item["kind"] == "theorem"), None)
        if selected is None:
            raise ValueError("Выбранная теорема не объявлена в проверенном источнике.")
        payload = dict(source, selected_declaration=selected)
        validate_library_payload(payload)
        return payload
