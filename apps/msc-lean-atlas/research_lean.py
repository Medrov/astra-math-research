"""Pinned Lean checks and reproducible research pilots.

The candidate target is checked against a separately supplied immutable type.
The surrounding definitions must also be pinned by the caller: checking a type
which refers to a changed definition does not establish semantic alignment.
External mathlib .olean caches are reused and recorded, not rebuilt here.
"""
from __future__ import annotations

from datetime import datetime, timezone
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import signal
import subprocess
import time
import uuid

import lean_service

ROOT = Path(__file__).resolve().parent
FIXTURES = ROOT / "research_fixtures"
NAME = re.compile(r"^[A-Za-z_][A-Za-z0-9_'.]*(?:\.[A-Za-z_][A-Za-z0-9_']*)*$")

GRADIENT_STATEMENT = """∀ {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  (f : E → ℝ) (g : E → E) {μ L : ℝ},
  0 < μ → μ ≤ L → UpperQuad f g L → LowerQuad f g μ →
  ∀ (x : ℕ → E), (∀ k, x (k + 1) = x k - (1 / L) • g (x k)) →
  ∀ (xstar : E) (k : ℕ),
  f (x k) - f xstar ≤ (1 - μ / L) ^ k * (f (x 0) - f xstar)"""
ENERGY_STATEMENT = """∀ (w01 w12 w02 x0 x1 x2 : ℝ),
  TriangleEnergy.graphEnergy w01 w12 w02 x0 x1 x2 =
  TriangleEnergy.laplacianForm w01 w12 w02 x0 x1 x2"""
NONNEGATIVE_STATEMENT = """∀ (w01 w12 w02 x0 x1 x2 : ℝ), 0 ≤ w01 → 0 ≤ w12 → 0 ≤ w02 →
  0 ≤ TriangleEnergy.laplacianForm w01 w12 w02 x0 x1 x2"""
COUNTEREXAMPLE_STATEMENT = "¬ (∀ a b : ℝ, 2 * a * b < a ^ 2 + b ^ 2)"


def _now():
    return datetime.now(timezone.utc).isoformat()


def _sha(value):
    return hashlib.sha256(value.encode() if isinstance(value, str) else value).hexdigest()


def _save(path, value):
    path.write_text(json.dumps(value, ensure_ascii=False, indent=2, default=str) + "\n")


def _cancelled(value):
    return bool(value() if callable(value) else value.is_set() if hasattr(value, "is_set") else value)


def _source(file):
    return (FIXTURES / file).read_text()


def fixtures():
    """Public metadata and fixed agent tasks; solutions are not in agent_task."""
    gradient = _source("SeminarGradient.lean")
    gradient_prelude = gradient[:gradient.index("theorem descent")] + "\nuniverse u\n"
    energy = _source("GraphEnergy.lean")
    energy_prelude = energy[:energy.index("theorem graph_energy_eq")] + "\nend TriangleEnergy\n"
    definitions = [
        dict(id="seminar_gradient", title="Градиентный метод: граф лемм", msc_codes=["90C25", "90C30"],
             description="Квадратичные оценки → две независимые леммы → один шаг → оценка итераций.",
             claim="При UpperQuad, LowerQuad, 0 < μ ≤ L и заданной итерации выполняется gd_rate для опорной точки xstar.",
             target="gd_rate", expected_statement=GRADIENT_STATEMENT, file="SeminarGradient.lean",
             expected_outcome="proved", source="Иван Фомин, Основы языка Lean, 27.10.2026, hw_sol.lean",
             evidence=[dict(kind="seminar_source", url="https://disk.360.yandex.ru/d/U4LZDftMoV55kg",
                            path=str(FIXTURES / "SeminarOriginal.lean"))],
             preview_nodes=["UpperQuad", "LowerQuad", "descent", "pl_ineq", "one_step", "gd_rate"],
             preview_edges=[["UpperQuad", "descent"], ["LowerQuad", "pl_ineq"], ["descent", "one_step"],
                            ["pl_ineq", "one_step"], ["one_step", "gd_rate"]],
             agent_task=dict(imports=["Mathlib.Analysis.InnerProductSpace.Basic"], prelude=gradient_prelude,
                             target="gd_rate", statement=GRADIENT_STATEMENT,
                             context="Докажите оценку итераций. xstar — опорная точка, не предположенный минимизатор. Разрешены вспомогательные леммы. Не меняйте определения или тип цели.")),
        dict(id="strict_inequality", title="Ложная аналогия: строгое неравенство", msc_codes=["26D05"],
             description="Отрицательный контроль: доказать опровержение универсального утверждения свидетелем a=b=0.",
             claim="Для всех a,b ∈ ℝ выполняется 2ab < a²+b².", target="StrictInequality.counterexample",
             expected_statement=COUNTEREXAMPLE_STATEMENT, file="StrictCounterexample.lean", expected_outcome="refuted",
             source="Незавершённое упражнение из sem.lean, семинар 27.10.2026",
             evidence=[dict(kind="seminar_source", url="https://disk.360.yandex.ru/d/U4LZDftMoV55kg")],
             preview_nodes=["StrictInequality.counterexample"], preview_edges=[],
             agent_task=dict(imports=["Mathlib.Data.Real.Basic"], prelude="import Mathlib.Data.Real.Basic\n",
                             target="StrictInequality.counterexample", statement=COUNTEREXAMPLE_STATEMENT,
                             context="Проверьте универсальное строгое неравенство. Если ложно, докажите указанное отрицание. Искомый результат — контрпример, не ложное доказательство.")),
        dict(id="graph_energy", title="Граф и линейная алгебра: энергия", msc_codes=["05C50", "15A63"],
             description="Энергия взвешенного треугольника совпадает с xᵀLx; неотрицательность переносится через равенство.",
             claim="Для взвешенного треугольника сумма wᵢⱼ(xᵢ−xⱼ)² равна квадратичной форме лапласиана; при неотрицательных весах форма неотрицательна.",
             target="TriangleEnergy.laplacian_nonnegative", expected_statement=NONNEGATIVE_STATEMENT, file="GraphEnergy.lean",
             expected_outcome="proved", source="Известное тождество лапласиана; явная координатная модель треугольника",
             evidence=[dict(kind="local_formal_fixture", path=str(FIXTURES / "GraphEnergy.lean"))],
             preview_nodes=["TriangleEnergy.graphEnergy", "TriangleEnergy.laplacianForm", "TriangleEnergy.graph_energy_eq", "TriangleEnergy.laplacian_nonnegative"],
             preview_edges=[["TriangleEnergy.graphEnergy", "TriangleEnergy.graph_energy_eq"],
                            ["TriangleEnergy.laplacianForm", "TriangleEnergy.graph_energy_eq"],
                            ["TriangleEnergy.graph_energy_eq", "TriangleEnergy.laplacian_nonnegative"]],
             agent_task=dict(imports=["Mathlib.Data.Real.Basic", "Mathlib.Tactic.Ring", "Mathlib.Tactic.Positivity"], prelude=energy_prelude,
                             target="TriangleEnergy.laplacian_nonnegative", statement=NONNEGATIVE_STATEMENT,
                             context="Известная связь графовой энергии и квадратичной формы. Восстановите доказательство для явной модели треугольника. Это контроль восстановления связи, не заявление о новом открытии.")),
    ]
    for item in definitions:
        item["source_sha256"] = _sha(_source(item["file"]))
        item["agent_task"]["prelude_sha256"] = _sha(item["agent_task"]["prelude"])
        item["agent_task"]["statement_sha256"] = _sha(item["agent_task"]["statement"])
    gradient_tasks = [
        dict(id="descent", target="descent", dependencies=[], statement="""∀ {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
          (f : E → ℝ) (g : E → E) {L : ℝ}, 0 < L → UpperQuad f g L → ∀ x : E,
          f (x - (1 / L) • g x) ≤ f x - 1 / (2 * L) * ‖g x‖ ^ 2"""),
        dict(id="pl_ineq", target="pl_ineq", dependencies=[], statement="""∀ {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
          (f : E → ℝ) (g : E → E) {μ : ℝ}, 0 < μ → LowerQuad f g μ → ∀ x z : E,
          2 * μ * (f x - f z) ≤ ‖g x‖ ^ 2"""),
        dict(id="one_step", target="one_step", dependencies=["descent", "pl_ineq"], statement="""∀ {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
          (f : E → ℝ) (g : E → E) {μ L : ℝ}, 0 < μ → μ ≤ L → UpperQuad f g L → LowerQuad f g μ →
          ∀ x z : E, f (x - (1 / L) • g x) - f z ≤ (1 - μ / L) * (f x - f z)"""),
        dict(id="gd_rate", target="gd_rate", dependencies=["one_step"], statement=GRADIENT_STATEMENT),
    ]
    definitions[0]["agent_task"]["lemmas"] = gradient_tasks
    definitions[1]["agent_task"]["lemmas"] = [dict(id="counterexample", target="StrictInequality.counterexample", dependencies=[], statement=COUNTEREXAMPLE_STATEMENT)]
    definitions[2]["agent_task"]["lemmas"] = [
        dict(id="graph_energy_eq", target="TriangleEnergy.graph_energy_eq", dependencies=[], statement=ENERGY_STATEMENT),
        dict(id="laplacian_nonnegative", target="TriangleEnergy.laplacian_nonnegative", dependencies=["graph_energy_eq"],
             statement=NONNEGATIVE_STATEMENT),
    ]
    return definitions


def _validate_source(source):
    if not isinstance(source, str) or not source.strip() or len(source.encode()) > 250000:
        raise ValueError("Нужен Lean-исходник до 250 КБ.")
    masked = lean_service._mask(source)
    # Conservative local research subset. This is not a general Lean sandbox.
    forbidden = sorted(set(re.findall(r"\b(?:sorry|admit|axiom|unsafe|partial|native_decide|run_tac|run_elab|elab|elab_rules|macro|macro_rules|syntax|initialize|builtin_initialize|set_option|implemented_by|extern|IO|System|Lean)\b", masked)))
    if forbidden or "#" in masked or "@[_" in masked:
        raise ValueError("Недопустимые конструкции кандидата: " + ", ".join(forbidden or ["команда #"]))
    for module in lean_service._imports(source):
        if not module.startswith("Mathlib.") and module not in {"Mathlib", "Init", "Std"}:
            raise ValueError("Для кандидата разрешены только закреплённые Mathlib/Init/Std импорты: " + module)


def _run(context, env, work, filename, diagnostics, cancelled=None, output=True):
    if _cancelled(cancelled):
        raise InterruptedError("Проверка отменена.")
    args = [context["lean"]]
    if output:
        args += ["-o", str(Path(filename).with_suffix(".olean"))]
    args += [filename]
    started = time.monotonic()
    out_path, err_path = work / (filename + ".stdout.log"), work / (filename + ".stderr.log")
    with out_path.open("w") as stdout, err_path.open("w") as stderr:
        proc = subprocess.Popen(args, cwd=work, env=env, stdout=stdout, stderr=stderr, start_new_session=True)
        interrupted, timed_out = False, False
        while proc.poll() is None:
            interrupted = _cancelled(cancelled)
            timed_out = time.monotonic() - started > context["timeout_seconds"]
            if interrupted or timed_out:
                os.killpg(proc.pid, signal.SIGTERM)
                try:
                    proc.wait(timeout=3)
                except subprocess.TimeoutExpired:
                    os.killpg(proc.pid, signal.SIGKILL)
                    proc.wait()
                break
            time.sleep(0.1)
    entry = dict(file=filename, command=args, exit_code=proc.returncode,
                 elapsed_seconds=round(time.monotonic() - started, 3),
                 stdout=out_path.read_text(errors="replace")[-50000:],
                 stderr=err_path.read_text(errors="replace")[-50000:],
                 timeout=timed_out, cancelled=interrupted)
    diagnostics.append(entry)
    if interrupted:
        raise InterruptedError("Проверка отменена.")
    if timed_out:
        raise TimeoutError("Лимит времени Lean: " + filename)
    if proc.returncode:
        raise RuntimeError("Lean отклонил " + filename)


def _export(context, env, work, diagnostics, cancelled):
    shutil.copyfile(ROOT / "tools/AtlasInspect.lean", work / "AtlasInspect.lean")
    _run(context, env, work, "AtlasInspect.lean", diagnostics, cancelled)
    export_path = work / "compiler-declarations.json"
    text = 'import AtlasInspect\nimport Candidate\nset_option maxRecDepth 8192\nset_option maxHeartbeats 2000000\n#atlas_export ["Candidate"] [] ' + json.dumps(str(export_path)) + "\n"
    (work / "AtlasDump.lean").write_text(text)
    _run(context, env, work, "AtlasDump.lean", diagnostics, cancelled, output=False)
    return json.loads(export_path.read_text())


def _audit_declarations(declarations, source, target):
    """Audit logical roots, retaining their full transitive axiom closures.

    Lean 4.19 emits unsafe axiomInfo entries for runtime specializations of pure
    definitions (e.g. Finset.sum._at.edgeEnergy._spec_1). These are compiler
    implementation artifacts, not logical premises of the definition. Exclude
    only this narrow generated category as *roots*. Never subtract their names
    from any logical declaration's axiom closure: a logical dependency on one
    must still reject the candidate.
    """
    explicit = {d['name'] for d in lean_service.lexical_declarations(source)}
    roots, helpers = [], []
    for decl in declarations:
        name = decl['name']
        source_declared = any(name == raw or name.endswith('.' + raw) for raw in explicit)
        runtime_specialization = (decl.get('unsafe') and decl.get('kind') == 'axiom'
                                  and re.search(r'\._at\..+\._spec_\d+$', name)
                                  and not source_declared and name != target)
        if runtime_specialization:
            helpers.append(dict(name=name, kind=decl['kind'], unsafe=True,
                                reason='compiler_runtime_specialization_not_a_logical_audit_root'))
        else:
            roots.append(decl)
    unexpected = sorted({a for d in roots for a in d.get('axioms', [])} - lean_service.ALLOWED_AXIOMS)
    unsafe = sorted({d['name'] for d in roots if d.get('unsafe')})
    return dict(status='rejected' if unexpected or unsafe else 'passed',
                allowed_axioms=sorted(lean_service.ALLOWED_AXIOMS), unexpected_axioms=unexpected,
                unsafe_declarations=unsafe, ignored_implementation_helpers=helpers,
                audited_roots=sorted(d['name'] for d in roots),
                scope='logical_local_declarations_and_target_axiom_closure')


def verify_candidate(source, target, work_dir, expected_statement=None, *, cancelled=None, progress=None):
    """Check a source, theorem target, axiom closure and an independent type contract.

    expected_statement is the complete Lean TYPE, e.g. ``∀ n : Nat, n = n``.
    `u`, `v`, `w` universes are available in the contract module. A missing
    contract permits formal checking but reports target_preserved=False.
    """
    work = Path(work_dir).resolve() / ("lean-" + uuid.uuid4().hex[:12])
    work.mkdir(parents=True)
    result = dict(status="failed", outcome="unknown", success=False, target=target,
                  source_sha256=_sha(source) if isinstance(source, str) else None,
                  expected_statement=expected_statement, target_preserved=False,
                  workspace=str(work), started_at=_now(), diagnostics=[], declarations=[], axioms=[],
                  audit=dict(status="pending", allowed_axioms=sorted(lean_service.ALLOWED_AXIOMS)),
                  semantic_review=dict(status="not_established", note="Lean проверяет тип; смысл и неизменность определений проверяются отдельно."))
    try:
        _validate_source(source)
        if not isinstance(target, str) or not NAME.fullmatch(target):
            raise ValueError("Нужно полное имя одной теоремы.")
        if expected_statement is not None:
            if not isinstance(expected_statement, str) or not expected_statement.strip() or len(expected_statement) > 30000:
                raise ValueError("Некорректный контракт типа цели.")
            # A type contract is supplied by the controller, never by the prover.
            if any(token in expected_statement for token in ("\nimport ", "\ntheorem ", "\nend", "#", ":=")):
                raise ValueError("Контракт должен быть одним Lean-типом, без команд.")
            _validate_source(expected_statement)
        (work / "Candidate.lean").write_text(source)
        context, env = lean_service._prepare({}, work)
        result["context"] = context
        if progress:
            progress("Lean компилирует исходник и проверяет целевое утверждение.")
        _run(context, env, work, "Candidate.lean", result["diagnostics"], cancelled)
        result["compilation_success"] = True
        exported = _export(context, env, work, result["diagnostics"], cancelled)
        result["declarations"] = exported["declarations"]
        decl = next((d for d in exported["declarations"] if d["name"] == target), None)
        if not decl or decl["kind"] != "theorem":
            raise ValueError("Цель должна быть теоремой, объявленной в проверяемом исходнике.")
        result["actual_statement"] = decl["type"]
        # Audit all logical local roots and the goal, excluding only generated
        # runtime specialization roots (their appearance in a closure still fails).
        audit = _audit_declarations(exported["declarations"], source, target)
        unexpected, unsafe = audit['unexpected_axioms'], audit['unsafe_declarations']
        result["axioms"] = decl["axioms"]
        result["audit"] = audit
        if unexpected or unsafe:
            raise ValueError("Аудит Lean отклонил аксиомы или unsafe-декларации: " + ", ".join(unexpected + unsafe))
        if expected_statement is not None:
            contract = "import Candidate\nuniverse u v w\nset_option autoImplicit false\nexample : (" + expected_statement + ") := @" + target + "\n"
            (work / "Contract.lean").write_text(contract)
            _run(context, env, work, "Contract.lean", result["diagnostics"], cancelled)
            result["target_preserved"] = True
            result["contract_sha256"] = _sha(expected_statement)
        result.update(status="complete", outcome="proved", success=True,
                      olean_sha256=_sha((work / "Candidate.olean").read_bytes()))
    except InterruptedError as error:
        result.update(status="cancelled", error=str(error))
    except TimeoutError as error:
        result.update(status="timeout", error=str(error))
    except ValueError as error:
        result.update(status="rejected", error=str(error))
    except (RuntimeError, OSError, subprocess.SubprocessError, KeyError) as error:
        result.update(status="failed", error=str(error))
    result["finished_at"] = _now()
    _save(work / "verification.json", result)
    return result


def _graph(declarations):
    # Elaboration emits helper theorems too. Keep user-facing declarations only.
    keep = [d for d in declarations if not any(part.startswith("_") for part in d["name"].split(".")) and ".proof_" not in d["name"]]
    names = {d["name"] for d in keep}
    nodes = [dict(id=d["name"], label=d["name"].split(".")[-1], kind=d["kind"], target=d["name"],
                  status="proved" if d["kind"] == "theorem" else "defined", statement=d["type"],
                  dependencies=sorted(names.intersection(d["dependencies"])), axioms=d["axioms"],
                  extraction="lean_environment") for d in keep]
    edges = []
    for d in keep:
        type_deps = set(d["type_dependencies"])
        for dep in sorted(names.intersection(d["dependencies"])):
            edges.append(dict(source=dep, target=d["name"], type="type_dependency" if dep in type_deps else "proof_dependency", evidence="lean_environment"))
    return nodes, edges


def run_pilot(case_id, work_dir, progress=None, cancelled=None):
    fixture = next((f for f in fixtures() if f["id"] == case_id), None)
    if not fixture:
        raise ValueError("Неизвестный пилот: " + str(case_id))
    result = verify_candidate(_source(fixture["file"]), fixture["target"], work_dir,
                              fixture["expected_statement"], cancelled=cancelled, progress=progress)
    nodes, edges = _graph(result.get("declarations", [])) if result["success"] else ([], [])
    outcome = fixture["expected_outcome"] if result["success"] else "unknown"
    if case_id == "seminar_gradient":
        semantic = dict(status="reviewed_fixture", scope="Оценка значений функции относительно произвольной опорной точки.",
                        findings=["xstar : E не объявлен минимизатором. Результат нельзя автоматически переименовать в сходимость к минимуму.",
                                  "UpperQuad/LowerQuad — предпосылки данной теоремы, не автоматически установленные свойства произвольной функции."],
                        source_change="В производном файле после field_simp добавлен ring; формулировки исходных теорем сохранены.", novelty="known_seminar_result")
    elif case_id == "strict_inequality":
        semantic = dict(status="reviewed_fixture", findings=["Свидетель a=b=0 нарушает строгий знак. Доказано отрицание универсального утверждения."],
                        counterexample=dict(a=0, b=0, left=0, right=0), novelty="negative_control")
    else:
        semantic = dict(status="reviewed_fixture", findings=["Явная модель треугольника с тремя весами. Не утверждается теорема обо всех графах.",
                                  "Тождество не требует положительности весов; перенос неотрицательности требует w01,w12,w02 ≥ 0."],
                        novelty="known_identity_recovery", useful_transfer="Неотрицательность графовой энергии переносится на квадратичную форму.")
    pilot = dict(status="complete" if result["success"] else result["status"], outcome=outcome,
                 case_id=case_id, fixture=fixture, nodes=nodes, edges=edges, verification=result,
                 checks=[dict(id="lean_compilation", passed=bool(result.get("compilation_success"))),
                         dict(id="axiom_audit", passed=result["audit"]["status"] == "passed"),
                         dict(id="immutable_target_type", passed=result["target_preserved"]),
                         dict(id="final_composition", passed=result["success"])],
                 semantic_review=semantic,
                 artifacts=[dict(kind="lean_source", path=str(Path(result["workspace"]) / "Candidate.lean")),
                            dict(kind="verification", path=str(Path(result["workspace"]) / "verification.json"))],
                 started_at=result["started_at"], finished_at=result["finished_at"])
    _save(Path(result["workspace"]) / "pilot.json", pilot)
    return pilot
