"""Fixed mathematical objects and explicit transition contracts for local pilots.

Object relations describe mathematical claims; they are not theorem dependency
edges or proof certificates. A controller must verify the transition's complete
obligation list against its pinned definitions before assigning a final status.
"""
from __future__ import annotations

from copy import deepcopy

import research_lean


def _obligation(identifier, title, target, statement, outcome="proved"):
    return dict(id=identifier, title=title, target=target, statement=statement, expected_outcome=outcome)


def _task(fixture, target=None, statement=None):
    original = fixture["agent_task"]
    return dict(imports=list(original["imports"]), prelude=original["prelude"],
                target=target or original["target"], statement=statement or original["statement"])


def _object(identifier, title, kind, definition, parameters, assumptions, codes, refs):
    return dict(id=identifier, title=title, kind=kind, definition=definition,
                parameters=parameters, assumptions=assumptions, msc_codes=codes, lean_refs=refs)


def _source(fixture):
    seminar = fixture["id"] in {"seminar_gradient", "strict_inequality"}
    return dict(id="prepared_source", title=fixture["source"],
                url="https://disk.360.yandex.ru/d/U4LZDftMoV55kg" if seminar else "https://github.com/Medrov/astra-math-research",
                locator="apps/msc-lean-atlas/research_fixtures/" + fixture["file"])


def _energy_graph(fixture):
    negative = fixture["id"] == "graph_energy_negative"
    parameters = ["w01, w12, w02 : ℝ — веса трёх рёбер", "x0, x1, x2 : ℝ — значения на вершинах"]
    identity = _obligation("graph_energy_eq", "Тождество для любых весов", "TriangleEnergy.graph_energy_eq",
                           research_lean.ENERGY_STATEMENT)
    transfer_assumptions = [] if negative else ["0 ≤ w01", "0 ≤ w12", "0 ≤ w02"]
    property_id = "unconditional_positivity_claim" if negative else "nonnegative_form"
    objects = [
        _object("edge_energy", "Энергия взвешенного треугольника", "energy",
                "E(w,x) = w01(x0−x1)² + w12(x1−x2)² + w02(x0−x2)².",
                parameters, [], ["05C50"], ["TriangleEnergy.graphEnergy"]),
        _object("laplacian_form", "Квадратичная форма лапласиана", "quadratic_form",
                "Q(w,x) = xᵀL(w)x для трёх вершин; Lii — сумма инцидентных весов, Lij = −wij.",
                parameters, [], ["15A63", "05C50"], ["TriangleEnergy.laplacianForm"]),
        _object(property_id, "Гипотеза: Q ≥ 0 при любых весах" if negative else "Неотрицательная квадратичная форма",
                "claim" if negative else "property",
                "∀ w,x, Q(w,x) ≥ 0 без знаковых условий." if negative else "∀ x, Q(w,x) ≥ 0 при неотрицательных весах.",
                parameters, transfer_assumptions, ["15A63"], [fixture["target"]]),
    ]
    identity_transition = dict(
        id="energy_identity", title="Представить энергию как xᵀLx", source_ids=["edge_energy"],
        target_ids=["laplacian_form"], relation_type="representation",
        construction="Раскрыть три квадрата и собрать коэффициенты той же тройки весов и координат в xᵀLx.",
        assumptions=[], claim="E(w,x) = Q(w,x) для всех вещественных весов и координат.",
        obligations=[identity], agent_task=_task(fixture, identity["target"], identity["statement"]),
        case_id=fixture["id"])
    if negative:
        obligations = [identity,
                       _obligation("negative_weight_witness", "Явное значение −1", "TriangleEnergyNegative.negative_weight_witness",
                                   research_lean.NEGATIVE_WEIGHT_STATEMENT),
                       _obligation("unconditional_nonnegativity_refuted", "Опровержение универсальной неотрицательности",
                                   fixture["target"], fixture["expected_statement"], "refuted")]
        construction = "Подставить веса (−1,0,0), координаты (1,0,0): E = Q = −1; опровергнуть универсальное утверждение."
        claim = "Без знаковых предпосылок утверждение ∀ w,x, Q(w,x) ≥ 0 ложно. Тождество E = Q сохраняется."
    else:
        obligations = [identity, _obligation("laplacian_nonnegative", "Перенос неотрицательности", fixture["target"],
                                             fixture["expected_statement"])]
        construction = "Каждое wᵢⱼ(xᵢ−xⱼ)² неотрицательно; перенести знак суммы на Q через проверенное равенство E = Q."
        claim = "При w01,w12,w02 ≥ 0 квадратичная форма Q(w,x) неотрицательна для всех x."
    transfer = dict(id="nonnegative_transfer", title="Проверить перенос без условий" if negative else "Перенести неотрицательность",
                    source_ids=["edge_energy", "laplacian_form"], target_ids=[property_id], relation_type="property_transfer",
                    construction=construction, assumptions=transfer_assumptions, claim=claim,
                    obligations=obligations, agent_task=_task(fixture), case_id=fixture["id"])
    return dict(title=fixture["title"], question=fixture["claim"], msc_codes=fixture["msc_codes"],
                objects=objects, transitions=[identity_transition, transfer], sources=[_source(fixture)])


def _gradient_graph(fixture):
    objects = [
        _object("quadratic_models", "Двусторонние квадратичные оценки", "assumptions",
                "UpperQuad f g L и LowerQuad f g μ связывают приращение f с g и квадратом нормы.",
                ["E — вещественное пространство со скалярным произведением", "f : E → ℝ", "g : E → E", "μ,L : ℝ"],
                ["0 < μ", "μ ≤ L", "UpperQuad f g L", "LowerQuad f g μ"], ["90C25"], ["UpperQuad", "LowerQuad"]),
        _object("gradient_iteration", "Градиентная итерация", "iteration",
                "x(k+1) = x(k) − (1/L) • g(x(k)).", ["x : ℕ → E", "k : ℕ"],
                ["Итерационное равенство для каждого k"], ["90C30"], []),
        _object("value_bound", "Оценка относительно опорной точки", "bound",
                "f(x(k))−f(xstar) ≤ (1−μ/L)^k · (f(x(0))−f(xstar)).", ["xstar : E — произвольная опорная точка"],
                ["Все квадратичные предпосылки и заданная итерация"], ["90C25", "90C30"], [fixture["target"]]),
    ]
    obligation = _obligation("gradient_rate", "Полная оценка итераций", fixture["target"], fixture["expected_statement"])
    transition = dict(id="gradient_rate", title="Получить оценку итераций", source_ids=["quadratic_models", "gradient_iteration"],
                      target_ids=["value_bound"], relation_type="property_transfer",
                      construction="Оценка убывания и нижняя квадратичная оценка дают один шаг; индукция даёт степень (1−μ/L).",
                      assumptions=["0 < μ ≤ L", "UpperQuad f g L", "LowerQuad f g μ", "Заданная градиентная итерация"],
                      claim="Оценка верна относительно произвольной xstar; минимальность xstar не утверждается.",
                      obligations=[obligation], agent_task=_task(fixture), case_id=fixture["id"])
    return dict(title=fixture["title"], question=fixture["claim"], msc_codes=fixture["msc_codes"],
                objects=objects, transitions=[transition], sources=[_source(fixture)])


def _strict_graph(fixture):
    objects = [
        _object("real_pair", "Пара вещественных чисел", "parameter_space", "(a,b) ∈ ℝ².", ["a,b : ℝ"], [], ["26D05"], []),
        _object("strict_comparison", "Гипотеза строгого сравнения", "claim", "∀ a,b : ℝ, 2ab < a²+b².",
                ["a,b : ℝ"], [], ["26D05"], [fixture["target"]]),
    ]
    obligation = _obligation("strict_counterexample", "Отрицание универсального утверждения", fixture["target"],
                             fixture["expected_statement"], "refuted")
    transition = dict(id="strict_comparison", title="Проверить универсальный строгий знак", source_ids=["real_pair"],
                      target_ids=["strict_comparison"], relation_type="property_transfer",
                      construction="Проверить пару a=b=0: обе части равны нулю, строгий знак не выполняется.", assumptions=[],
                      claim="Универсальное строгое неравенство ложно.", obligations=[obligation],
                      agent_task=_task(fixture), case_id=fixture["id"])
    return dict(title=fixture["title"], question=fixture["claim"], msc_codes=fixture["msc_codes"],
                objects=objects, transitions=[transition], sources=[_source(fixture)])


def graph_for_case(case):
    """Return fresh canonical metadata for a prepared case ID or fixture dict."""
    case_id = case.get("id", case.get("case_id")) if isinstance(case, dict) else case
    fixture = next((item for item in research_lean.fixtures() if item["id"] == case_id), None)
    if fixture is None:
        raise ValueError("Неизвестный подготовленный пример: " + str(case_id))
    if case_id == "arxiv_2610_38474_graph_subtraction":
        from research_arxiv_example import graph_for_article
        graph = graph_for_article()
    elif case_id == "published_associator_laplacian":
        from research_published_example import graph_for_published_example
        graph = graph_for_published_example()
    elif case_id in {"graph_energy", "graph_energy_negative"}:
        graph = _energy_graph(fixture)
    elif case_id == "seminar_gradient":
        graph = _gradient_graph(fixture)
    else:
        graph = _strict_graph(fixture)
    return deepcopy(graph)
