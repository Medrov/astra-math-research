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
import subprocess
import time
import uuid

import lean_service
from platform_support import terminate_process_tree

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
NEGATIVE_ENERGY_STATEMENT = """¬ (∀ (w01 w12 w02 x0 x1 x2 : ℝ),
  0 ≤ TriangleEnergy.laplacianForm w01 w12 w02 x0 x1 x2)"""
NEGATIVE_WEIGHT_STATEMENT = "TriangleEnergy.laplacianForm (-1) 0 0 1 0 0 = -1"


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
    negative_energy = _source("GraphEnergyNegative.lean")
    negative_prelude = negative_energy[:negative_energy.index("theorem graph_energy_eq")] + "\nend TriangleEnergy\n"
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
        dict(id="graph_energy_negative", title="Отрицательный вес: граница переноса", msc_codes=["05C50", "15A63"],
             description="Тождество энергии и формы сохраняется, но отрицательный вес опровергает безусловную неотрицательность.",
             claim="Квадратичная форма лапласиана неотрицательна для любых вещественных весов.",
             target="TriangleEnergyNegative.unconditional_nonnegativity_refuted",
             expected_statement=NEGATIVE_ENERGY_STATEMENT, file="GraphEnergyNegative.lean",
             expected_outcome="refuted", source="Отрицательный контроль явной координатной модели треугольника",
             evidence=[dict(kind="local_formal_fixture", path=str(FIXTURES / "GraphEnergyNegative.lean"))],
             preview_nodes=["TriangleEnergy.graphEnergy", "TriangleEnergy.laplacianForm",
                            "TriangleEnergy.graph_energy_eq", "TriangleEnergyNegative.negative_weight_witness",
                            "TriangleEnergyNegative.unconditional_nonnegativity_refuted"],
             preview_edges=[["TriangleEnergy.graph_energy_eq", "TriangleEnergyNegative.negative_weight_witness"],
                            ["TriangleEnergyNegative.negative_weight_witness", "TriangleEnergyNegative.unconditional_nonnegativity_refuted"]],
             agent_task=dict(imports=["Mathlib.Data.Real.Basic", "Mathlib.Tactic.Ring", "Mathlib.Tactic.NormNum"],
                             prelude=negative_prelude, target="TriangleEnergyNegative.unconditional_nonnegativity_refuted",
                             statement=NEGATIVE_ENERGY_STATEMENT,
                             context="Сохраните безусловное тождество энергии и формы. Проверьте веса (-1,0,0) и координаты (1,0,0); докажите отрицание безусловной неотрицательности.")),
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
    definitions[3]["agent_task"]["lemmas"] = [
        dict(id="graph_energy_eq", target="TriangleEnergy.graph_energy_eq", dependencies=[], statement=ENERGY_STATEMENT),
        dict(id="negative_weight_witness", target="TriangleEnergyNegative.negative_weight_witness",
             dependencies=["graph_energy_eq"], statement=NEGATIVE_WEIGHT_STATEMENT),
        dict(id="unconditional_nonnegativity_refuted", target="TriangleEnergyNegative.unconditional_nonnegativity_refuted",
             dependencies=["negative_weight_witness"], statement=NEGATIVE_ENERGY_STATEMENT),
    ]
    for index in (2, 3):
        item = definitions[index]
        item["required_obligations"] = [dict(id=lemma["id"], target=lemma["target"], statement=lemma["statement"],
                                             expected_outcome="refuted" if lemma["target"] == item["target"] and index == 3 else "proved")
                                        for lemma in item["agent_task"]["lemmas"]]
        item["agent_task"]["required_obligations"] = item["required_obligations"]
    from research_arxiv_example import fixture as arxiv_fixture
    definitions.append(arxiv_fixture())
    from research_published_example import fixture as published_fixture
    definitions.append(published_fixture())
    return definitions


def _validate_source(source):
    if not isinstance(source, str) or not source.strip() or len(source.encode()) > 250000:
        raise ValueError("Нужен Lean-исходник до 250 КБ.")
    masked = lean_service._mask(source)
    # Conservative local research subset. This is not a general Lean sandbox.
    forbidden = sorted(set(re.findall(r"\b(?:sorry|admit|axiom|unsafe|partial|native_decide|run_tac|run_elab|elab|elab_rules|macro|macro_rules|syntax|initialize|builtin_initialize|set_option|implemented_by|extern|IO|System|Lean)\b", masked)))
    if forbidden or "#" in masked or "@[_" in masked:
        raise ValueError("Недопустимые конструкции кандидата: " + ", ".join(forbidden or ["команда #"]))
    from research_project_library import allowed_imports
    for header in re.findall(r'(?m)^\s*import\s+([^\n]+)', masked):
        if any(not re.fullmatch(r'[A-Za-z_][A-Za-z0-9_.]*', word) for word in header.split()):
            raise ValueError('В импортах кандидата разрешены только явные ASCII-имена закреплённых модулей.')
    for module in lean_service._imports(source):
        if not module.startswith("Mathlib.") and module not in {"Mathlib", "Init", "Std", "StructureInput"} and module not in allowed_imports():
            raise ValueError("Импорт отсутствует в закреплённой библиотеке кандидата: " + module)


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
                terminate_process_tree(proc)
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


def _export(context, env, work, diagnostics, cancelled, *, modules=None):
    shutil.copyfile(ROOT / "tools/AtlasInspect.lean", work / "AtlasInspect.lean")
    _run(context, env, work, "AtlasInspect.lean", diagnostics, cancelled)
    export_path = work / "compiler-declarations.json"
    modules = list(modules or ["Candidate"])
    if any(not NAME.fullmatch(module) for module in modules):
        raise ValueError("Некорректный модуль семантического экспорта.")
    text = ('import AtlasInspect\n' + ''.join('import ' + module + '\n' for module in modules) +
            'set_option maxRecDepth 8192\nset_option maxHeartbeats 2000000\n#atlas_export [' +
            ', '.join(json.dumps(module) for module in modules) + '] [] ' + json.dumps(str(export_path)) + "\n")
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


def _validate_type_contract(statement):
    if not isinstance(statement, str) or not statement.strip() or len(statement) > 30000:
        raise ValueError("Некорректный контракт типа цели.")
    _validate_source(statement)
    # This is a conservative lexical boundary check, not a Lean parser or a
    # sandbox. Lean elaboration and the independent exact-type audit remain
    # authoritative. In particular := is legal in let/letI, named arguments
    # and record terms; it must not be confused with a theorem's proof boundary.
    masked = list(statement)
    i, depth, string = 0, 0, False
    while i < len(statement):
        pair, char = statement[i:i + 2], statement[i]
        if depth:
            if pair in ('/-', '-/'):
                depth += 1 if pair == '/-' else -1
                masked[i:i + 2] = '  '; i += 2; continue
            if char != '\n': masked[i] = ' '
        elif string:
            if char == '\\' and i + 1 < len(statement):
                masked[i:i + 2] = '  '; i += 2; continue
            if char == '"': string = False
            if char != '\n': masked[i] = ' '
        elif pair == '/-':
            depth = 1; masked[i:i + 2] = '  '; i += 2; continue
        elif pair == '-/':
            raise ValueError('Закрытие комментария без начала в Lean-типе.')
        elif pair == '--':
            while i < len(statement) and statement[i] != '\n':
                masked[i] = ' '; i += 1
            continue
        elif char == '"':
            string = True; masked[i] = ' '
        elif char == "'" and (i == 0 or not (statement[i - 1].isalnum() or statement[i - 1] in "_'")):
            literal = re.match(r"'(?:\\.|[^'\\\n])'", statement[i:])
            if literal:
                length = len(literal.group()); masked[i:i + length] = ' ' * length; i += length; continue
        i += 1
    if depth or string:
        raise ValueError('Незакрытый комментарий или строка в Lean-типе.')
    masked = ''.join(masked)
    commands = r'\b(?:import|theorem|lemma|def|abbrev|opaque|inductive|structure|class|instance|namespace|section|end|variable|variables|universe|universes|attribute|export|notation|infix|infixl|infixr|prefix|postfix)\b'
    if re.search(commands, masked) or any(token in masked for token in ('#', '@[', '`')):
        raise ValueError('Контракт должен быть одним Lean-типом, без команд.')
    pairs = {'(': ')', '[': ']', '{': '}', '⦃': '⦄', '⟨': '⟩', '⟦': '⟧'}
    stack, lets = [], [0]
    for token in re.findall(r':=|[^\W\d]\w*|[^\s]', masked, re.UNICODE):
        if token in pairs:
            stack.append(pairs[token]); lets.append(0)
        elif token in pairs.values():
            if not stack or stack.pop() != token:
                raise ValueError('Несогласованные скобки в Lean-типе.')
            lets.pop()
        elif token in ('let', 'letI', 'letI\'', 'letI!'):
            lets[-1] += 1
        elif token == ':=':
            if lets[-1]:
                lets[-1] -= 1
            elif not stack:
                raise ValueError('Внешнее := не является частью Lean-типа; передайте только тип.')
    if stack:
        raise ValueError('Незакрытая скобка в Lean-типе.')


def type_expression(statement):
    """Isolate a validated frozen type, including trailing line comments."""
    _validate_type_contract(statement)
    return '(\n' + statement + '\n)'


def theorem_header(name, statement):
    if not isinstance(name, str) or not NAME.fullmatch(name):
        raise ValueError('Нужно полное имя теоремы.')
    return 'theorem ' + name + ' : ' + type_expression(statement) + ' := '


def verify_contract(task, work_dir, *, cancelled=None, source_library=None):
    """Elaborate frozen definitions and propositions; never prove the propositions.

    The trusted harness defines values of type Prop, not inhabitants of those
    propositions. No theorem certificate or success=True field is produced.
    """
    work = Path(work_dir).resolve() / ('contract-' + uuid.uuid4().hex[:12])
    work.mkdir(parents=True)
    report = dict(kind='lean_contract_preflight', status='failed', well_typed=False,
                  proof_checked=False, outcome='unknown', target=task.get('target'),
                  contract_sha256=_sha(json.dumps(task, sort_keys=True, ensure_ascii=False)),
                  workspace=str(work), started_at=_now(), diagnostics=[], declarations=[],
                  checked_obligations=[], audit=dict(status='pending'))
    stage = 'lean_contract_preflight'
    infrastructure = False
    try:
        imports, prelude = task.get('imports', ['Mathlib']), task.get('prelude', '')
        if not isinstance(imports, list) or not imports or any(not isinstance(m, str) or not NAME.fullmatch(m) for m in imports):
            raise ValueError('Некорректные импорты формальной постановки.')
        if not isinstance(prelude, str) or re.search(r'\b(?:theorem|lemma)\b', lean_service._mask(prelude)):
            raise ValueError('Контекст постановки должен содержать определения, а не доказанные теоремы.')
        if not isinstance(task.get('target'), str) or not NAME.fullmatch(task['target']):
            raise ValueError('Некорректная цель постановки.')
        obligations = _validate_obligations(task.get('required_obligations'))
        items = [dict(id='primary', target=task['target'], statement=task.get('statement'))] + obligations
        header = '\n'.join('import ' + module for module in imports) + '\n\n' + prelude + '\n\n'
        _validate_source(header)
        declarations, namespace = [], 'AtlasContract_' + uuid.uuid4().hex
        for i, item in enumerate(items):
            name = namespace + '.expectedType' + str(i)
            declarations.append('def ' + name + ' : Prop := ' + type_expression(item['statement']))
            report['checked_obligations'].append(dict(id=item['id'], target=item['target'],
                                                       statement_sha256=_sha(item['statement']), declaration=name))
        source = header + 'universe u v w\nset_option autoImplicit false\nnoncomputable section\n' + '\n\n'.join(declarations) + '\n'
        source_path = work / 'ContractTypes.lean'
        source_path.write_text(source, encoding='utf-8')
        report['source_sha256'] = _sha(source_path.read_bytes())
        infrastructure = True
        context, env = lean_service._prepare({}, work)
        report['context'] = context
        import research_structure_sources as structure_sources
        structure_sources.isolated_environment(context, env, work)
        import research_project_library as project_library
        if set(imports) & project_library.allowed_imports():
            report['project_library'] = project_library.prepare_library(
                context, env, work,
                lambda filename: _run(context, env, work, filename, report['diagnostics'], cancelled), cancelled,
                expected_fingerprint=project_library.pinned_fingerprint(header, required=True))
        modules = ['ContractTypes']
        payload = None
        if 'StructureInput' in imports or source_library is not None:
            if 'StructureInput' not in imports or source_library is None:
                raise ValueError('Для StructureInput нужен закреплённый снимок содержимого.')
            payload = structure_sources.validate_library_payload(source_library)
            if structure_sources.pinned_fingerprint(header, required=True) != payload['source_sha256']:
                raise ValueError('Pin StructureInput не совпадает с исходным снимком.')
            dependencies = structure_sources.prepare_source_dependencies(payload, context, env, work,
                lambda filename: _run(context, env, work, filename, report['diagnostics'], cancelled), cancelled)
            if dependencies is not None:
                report['project_library'] = dependencies
            (work / 'StructureInput.lean').write_bytes(payload['content'].encode('utf-8'))
            _run(context, env, work, 'StructureInput.lean', report['diagnostics'], cancelled)
            modules.append('StructureInput')
        infrastructure = False
        _run(context, env, work, source_path.name, report['diagnostics'], cancelled)
        exported = _export(context, env, work, report['diagnostics'], cancelled, modules=modules)
        local = [d for d in exported['declarations'] if d['module'] == 'ContractTypes']
        report['declarations'] = local
        by_name = {d['name']: d for d in local}
        for item in report['checked_obligations']:
            actual = by_name.get(item['declaration'])
            if not actual or actual.get('kind') not in ('def', 'definition') or actual.get('type') != 'Prop':
                raise ValueError('Lean не экспортировал ожидаемое определение пропозиции: ' + item['target'])
        report['audit'] = _audit_declarations(local, source, report['checked_obligations'][0]['declaration'])
        if report['audit']['status'] != 'passed':
            raise ValueError('Аудит определений постановки отклонён.')
        if payload:
            input_declarations = [d for d in exported['declarations'] if d['module'] == 'StructureInput']
            selected = payload['selected_declaration']
            actual = next((d for d in input_declarations if d['name'] == selected['name']), None)
            audit = _audit_declarations(input_declarations, payload['content'], selected['name'])
            if not actual or actual['type'] != selected['type'] or actual['kind'] != 'theorem' or audit['status'] != 'passed':
                raise ValueError('Свежая проверка исходного StructureInput не соответствует снимку.')
            if _sha((work / 'StructureInput.lean').read_bytes()) != payload['source_sha256']:
                raise ValueError('StructureInput изменён во время проверки.')
            report['source_library'] = dict(source_sha256=payload['source_sha256'], audit=audit)
        if _sha(source_path.read_bytes()) != report['source_sha256']:
            raise ValueError('Контекст постановки изменён во время проверки.')
        report.update(status='complete', well_typed=True)
    except (ValueError, RuntimeError, OSError, subprocess.SubprocessError, InterruptedError, TimeoutError) as error:
        code = ('cancelled' if isinstance(error, InterruptedError) else 'lean_timeout' if isinstance(error, TimeoutError)
                else 'infrastructure' if isinstance(error, OSError) or infrastructure and not isinstance(error, ValueError)
                else 'invalid_contract')
        status = 'cancelled' if code == 'cancelled' else 'timeout' if code == 'lean_timeout' else 'rejected' if code == 'invalid_contract' else 'failed'
        report.update(status=status, error=str(error), termination=dict(code=code, stage=stage, message=str(error)))
    report['finished_at'] = _now()
    _save(work / 'contract-verification.json', report)
    return report


def _validate_obligations(value):
    if value is None:
        return []
    if not isinstance(value, list) or len(value) > 32:
        raise ValueError("Обязательства должны быть списком не более 32 контрактов.")
    seen, result = set(), []
    for item in value:
        if not isinstance(item, dict):
            raise ValueError("Обязательство должно содержать id, target, statement, expected_outcome.")
        identifier, target, statement = item.get("id"), item.get("target"), item.get("statement")
        if not isinstance(identifier, str) or not re.fullmatch(r"[A-Za-z0-9_.:-]{1,128}", identifier) or identifier in seen:
            raise ValueError("Идентификаторы обязательств должны быть непустыми и уникальными.")
        if not isinstance(target, str) or not NAME.fullmatch(target):
            raise ValueError("Нужно полное имя теоремы каждого обязательства.")
        if item.get("expected_outcome") not in {"proved", "refuted"}:
            raise ValueError("Результат обязательства должен быть proved или refuted.")
        _validate_type_contract(statement)
        seen.add(identifier)
        result.append(dict(id=identifier, target=target, statement=statement,
                           expected_outcome=item["expected_outcome"]))
    if sum(len(item["statement"]) for item in result) > 250000:
        raise ValueError("Суммарный контракт обязательств слишком велик.")
    return result


def verify_candidate(source, target, work_dir, expected_statement=None, *, required_obligations=None,
                     cancelled=None, progress=None, source_library=None, require_source_usage=True):
    """Check a source, theorem target, axiom closure and an independent type contract.

    expected_statement is the complete Lean TYPE, e.g. ``∀ n : Nat, n = n``.
    `u`, `v`, `w` universes are available in the contract module. A missing
    contract permits formal checking but reports target_preserved=False.
    Optional required_obligations pin additional local theorem types. All types
    are checked together in one Contract.lean compilation and accepted atomically;
    expected_outcome labels the meaning of a checked type, never changes its proof.
    StructureInput imports require a pinned immutable content payload. Its source
    is recompiled and audited on every check. Final results must participate in
    the selected source theorem or its local type definitions; intermediate
    helper nodes may explicitly set require_source_usage=False.
    """
    work = Path(work_dir).resolve() / ("lean-" + uuid.uuid4().hex[:12])
    work.mkdir(parents=True)
    result = dict(status="failed", outcome="unknown", success=False, target=target,
                  source_sha256=_sha(source) if isinstance(source, str) else None,
                  expected_statement=expected_statement, target_preserved=False,
                  obligations=[], obligations_passed=False,
                  workspace=str(work), started_at=_now(), diagnostics=[], declarations=[], axioms=[],
                  audit=dict(status="pending", allowed_axioms=sorted(lean_service.ALLOWED_AXIOMS)),
                  semantic_review=dict(status="not_established", note="Lean проверяет тип; смысл и неизменность определений проверяются отдельно."))
    stage = 'validate_candidate'
    try:
        _validate_source(source)
        structure_payload = None
        has_structure_input = 'StructureInput' in lean_service._imports(source)
        if has_structure_input or source_library is not None:
            import research_structure_sources as structure_sources
            if not has_structure_input or source_library is None:
                raise ValueError('import StructureInput требует ровно один закреплённый source_library payload.')
            structure_payload = structure_sources.validate_library_payload(source_library)
            if structure_sources.pinned_fingerprint(source, required=True) != structure_payload['source_sha256']:
                raise ValueError('Pin кандидата не совпадает с SHA-256 исходного StructureInput.')
            if not isinstance(require_source_usage, bool):
                raise ValueError('require_source_usage должен быть логическим значением.')
        if not isinstance(target, str) or not NAME.fullmatch(target):
            raise ValueError("Нужно полное имя одной теоремы.")
        if expected_statement is not None:
            _validate_type_contract(expected_statement)
        obligations = _validate_obligations(required_obligations)
        result["obligations"] = [dict(id=item["id"], target=item["target"],
                                      statement_sha256=_sha(item["statement"]), ok=False,
                                      expected_outcome=item["expected_outcome"])
                                 for item in obligations]
        (work / "Candidate.lean").write_text(source)
        stage = 'lean_environment'
        context, env = lean_service._prepare({}, work)
        result["context"] = context
        # Candidates never inherit compiled project modules from the checkout.
        # The sole supported project entry point is built below from pinned sources.
        if context.get('project_root'):
            project_root = Path(context['project_root']).resolve()
            excluded = {project_root, (project_root / '.lake/build/lib/lean').resolve()}
            paths = [p for p in context['lean_search_paths'] if Path(p).resolve() not in excluded]
            context['lean_search_paths'] = paths
            env['LEAN_PATH'] = os.pathsep.join(paths)
        import research_project_library
        if set(lean_service._imports(source)) & research_project_library.allowed_imports():
            pin = research_project_library.pinned_fingerprint(source, required=True)
            result['project_library'] = research_project_library.prepare_library(
                context, env, work,
                lambda filename: _run(context, env, work, filename, result['diagnostics'], cancelled),
                cancelled, expected_fingerprint=pin)
        if structure_payload is not None:
            dependencies = structure_sources.prepare_source_dependencies(structure_payload, context, env, work,
                lambda filename: _run(context, env, work, filename, result['diagnostics'], cancelled), cancelled)
            if dependencies is not None:
                result['project_library'] = dependencies
            (work / 'StructureInput.lean').write_bytes(structure_payload['content'].encode('utf-8'))
            if progress:
                progress('Lean заново компилирует закреплённый исходный StructureInput.')
            _run(context, env, work, 'StructureInput.lean', result['diagnostics'], cancelled)
            if _sha((work / 'StructureInput.lean').read_bytes()) != structure_payload['source_sha256']:
                raise ValueError('StructureInput изменён во время компиляции.')
            result['source_library'] = dict(
                source_id=structure_payload['source_id'], source_sha256=structure_payload['source_sha256'],
                selected_declaration=structure_payload['selected_declaration'],
                environment_fingerprint=structure_payload['environment_fingerprint'],
                fresh_compilation=True, olean_sha256=_sha((work / 'StructureInput.olean').read_bytes()))
        if progress:
            progress("Lean компилирует исходник и проверяет целевое утверждение.")
        stage = 'lean_candidate'
        _run(context, env, work, "Candidate.lean", result["diagnostics"], cancelled)
        result["compilation_success"] = True
        stage = 'lean_audit'
        if structure_payload is None:
            exported = _export(context, env, work, result["diagnostics"], cancelled)
        else:
            exported = _export(context, env, work, result["diagnostics"], cancelled, modules=['Candidate', 'StructureInput'])
        candidate_declarations = [d for d in exported['declarations'] if d['module'] == 'Candidate']
        result["declarations"] = candidate_declarations
        decl = next((d for d in candidate_declarations if d["name"] == target), None)
        if not decl or decl["kind"] != "theorem":
            raise ValueError("Цель должна быть теоремой, объявленной в проверяемом исходнике.")
        declarations_by_name = {d["name"]: d for d in candidate_declarations}
        for item in obligations:
            obligation_decl = declarations_by_name.get(item["target"])
            if not obligation_decl or obligation_decl["kind"] != "theorem":
                raise ValueError("Обязательство должно быть локальной теоремой: " + item["target"])
        result["actual_statement"] = decl["type"]
        # Audit all logical local roots and the goal, excluding only generated
        # runtime specialization roots (their appearance in a closure still fails).
        audit = _audit_declarations(candidate_declarations, source, target)
        unexpected, unsafe = audit['unexpected_axioms'], audit['unsafe_declarations']
        result["axioms"] = decl["axioms"]
        result["audit"] = audit
        if unexpected or unsafe:
            raise ValueError("Аудит Lean отклонил аксиомы или unsafe-декларации: " + ", ".join(unexpected + unsafe))
        if structure_payload is not None:
            input_declarations = [d for d in exported['declarations'] if d['module'] == 'StructureInput']
            selected = structure_payload['selected_declaration']
            actual = next((d for d in input_declarations if d['name'] == selected['name'] and d['kind'] == 'theorem'), None)
            if actual is None or actual['type'] != selected['type']:
                raise ValueError('Выбранная теорема или её тип не совпадают со свежим экспортом StructureInput.')
            input_audit = _audit_declarations(input_declarations, structure_payload['content'], selected['name'])
            result['source_library'].update(declarations=input_declarations, audit=input_audit)
            if input_audit['status'] != 'passed':
                raise ValueError('Аудит входного StructureInput отклонил аксиомы или unsafe-декларации.')
            result['source_library']['print_axioms'] = structure_sources.print_axioms(
                structure_payload['content'], input_declarations, context, env, work, result['diagnostics'], cancelled)
            result['print_axioms'] = structure_sources.print_axioms(
                source, candidate_declarations, context, env, work, result['diagnostics'], cancelled, module='Candidate')
            if _sha((work / 'StructureInput.lean').read_bytes()) != structure_payload['source_sha256']:
                raise ValueError('StructureInput изменён во время проверки кандидата.')
            usage = structure_sources.source_usage(target, candidate_declarations, input_declarations,
                                                    selected['name'], structure_payload['content'])
            usage['required'] = require_source_usage
            result['source_usage'] = usage
            if require_source_usage and usage['status'] != 'related':
                result['outcome'] = 'unrelated'
                raise ValueError('Итоговая теорема не использует выбранную исходную теорему или определения её типа; одного импорта недостаточно.')
        contracts = [(target, expected_statement)] if expected_statement is not None else []
        contracts.extend((item["target"], item["statement"]) for item in obligations)
        if contracts:
            stage = 'lean_contract'
            contract = "import Candidate\nuniverse u v w\nset_option autoImplicit false\n" + "".join(
                "example : " + type_expression(statement) + " := @" + name + "\n" for name, statement in contracts)
            (work / "Contract.lean").write_text(contract)
            _run(context, env, work, "Contract.lean", result["diagnostics"], cancelled)
            result["contract_file_sha256"] = _sha(contract)
        if expected_statement is not None:
            result["target_preserved"] = True
            result["contract_sha256"] = _sha(expected_statement)
        for item in result["obligations"]:
            item["ok"] = True
        result["obligations_passed"] = True
        result.update(status="complete", outcome="proved", success=True,
                      olean_sha256=_sha((work / "Candidate.olean").read_bytes()))
    except InterruptedError as error:
        result.update(status="cancelled", error=str(error), termination=dict(code='cancelled', stage=stage, message=str(error)))
    except TimeoutError as error:
        result.update(status="timeout", error=str(error), termination=dict(code='lean_timeout', stage=stage, message=str(error)))
    except ValueError as error:
        result.update(status="rejected", error=str(error), termination=dict(code='invalid_contract', stage=stage, message=str(error)))
    except (RuntimeError, OSError, subprocess.SubprocessError, KeyError) as error:
        code = 'infrastructure' if stage == 'lean_environment' or isinstance(error, OSError) else 'invalid_contract' if stage == 'lean_contract' else 'lean_unproved'
        result.update(status="failed", error=str(error), termination=dict(code=code, stage=stage, message=str(error)))
    if not result["success"]:
        result["obligations_passed"] = False
        for item in result["obligations"]:
            item["ok"] = False
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


def run_pilot(case_id, work_dir, progress=None, cancelled=None, *, transition_task=None):
    fixture = next((f for f in fixtures() if f["id"] == case_id), None)
    if not fixture:
        raise ValueError("Неизвестный пилот: " + str(case_id))
    target, statement = fixture["target"], fixture["expected_statement"]
    obligations, expected_outcome = fixture.get("required_obligations"), fixture["expected_outcome"]
    selected_target = None
    if transition_task is not None:
        if not isinstance(transition_task, dict):
            raise ValueError("Нужен зафиксированный контракт выбранного перехода.")
        canonical = fixture["agent_task"]
        if transition_task.get("imports") != canonical["imports"] or transition_task.get("prelude") != canonical["prelude"]:
            raise ValueError("Определения и импорты перехода отличаются от подготовленного примера.")
        target, statement = transition_task.get("target"), transition_task.get("statement")
        obligations = _validate_obligations(transition_task.get("required_obligations"))
        primary = [item for item in obligations if item["target"] == target and item["statement"] == statement]
        if len(primary) != 1:
            raise ValueError("Основная цель перехода должна совпадать с одним обязательством.")
        expected_outcome = primary[0]["expected_outcome"]
        selected_target = dict(target=target, statement=statement, statement_sha256=_sha(statement),
                               expected_outcome=expected_outcome, obligation_ids=[item["id"] for item in obligations])
    # Selected transitions change only the independent contract. The checked
    # source is always the canonical fixture, never supplied through the request.
    result = verify_candidate(_source(fixture["file"]), target, work_dir,
                              statement, required_obligations=obligations,
                              cancelled=cancelled, progress=progress)
    nodes, edges = _graph(result.get("declarations", [])) if result["success"] else ([], [])
    outcome = expected_outcome if result["success"] else "unknown"
    if fixture.get("semantic_review"):
        semantic = fixture["semantic_review"]
    elif case_id == "seminar_gradient":
        semantic = dict(status="reviewed_fixture", scope="Оценка значений функции относительно произвольной опорной точки.",
                        findings=["xstar : E не объявлен минимизатором. Результат нельзя автоматически переименовать в сходимость к минимуму.",
                                  "UpperQuad/LowerQuad — предпосылки данной теоремы, не автоматически установленные свойства произвольной функции."],
                        source_change="В производном файле после field_simp добавлен ring; формулировки исходных теорем сохранены.", novelty="known_seminar_result")
    elif case_id == "strict_inequality":
        semantic = dict(status="reviewed_fixture", findings=["Свидетель a=b=0 нарушает строгий знак. Доказано отрицание универсального утверждения."],
                        counterexample=dict(a=0, b=0, left=0, right=0), novelty="negative_control")
    elif case_id == "graph_energy_negative":
        semantic = dict(status="reviewed_fixture", findings=[
                            "Тождество графовой энергии и квадратичной формы не требует знаковых условий.",
                            "Вес w01=-1 при остальных нулевых весах и x=(1,0,0) даёт значение -1.",
                            "Опровергнута только неотрицательность без предпосылок; теорема при неотрицательных весах не опровергнута."],
                        counterexample=dict(weights=[-1, 0, 0], coordinates=[1, 0, 0], form_value=-1),
                        novelty="negative_control")
    else:
        semantic = dict(status="reviewed_fixture", findings=["Явная модель треугольника с тремя весами. Не утверждается теорема обо всех графах.",
                                  "Тождество не требует положительности весов; перенос неотрицательности требует w01,w12,w02 ≥ 0."],
                        novelty="known_identity_recovery", useful_transfer="Неотрицательность графовой энергии переносится на квадратичную форму.")
    if selected_target and target == "TriangleEnergy.graph_energy_eq":
        semantic = dict(status="reviewed_fixture", scope="Безусловное тождество энергии и квадратичной формы явного треугольника.",
                        findings=["Все три веса могут быть любыми вещественными числами, в том числе отрицательными.",
                                  "Выбранный переход удостоверяет равенство представлений; неотрицательность не входит в его контракт."],
                        assumptions=[], novelty="known_identity_recovery")
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
    if obligations:
        pilot["checks"].append(dict(id="required_obligations", passed=result["obligations_passed"]))
    if selected_target:
        pilot["selected_target"] = selected_target
    _save(Path(result["workspace"]) / "pilot.json", pilot)
    return pilot
