"""One bounded, source-linked formal transition from arXiv:2610.38474v1.

This is the final graph subtraction in Section 9.1, not a verification of
the preceding coordinate lift, the trefoil formulas, or the motivic results.
The checked equalities live in polynomial rings, not only on field points.
"""
from __future__ import annotations

import hashlib
from pathlib import Path


ROOT = Path(__file__).resolve().parent
CASE_ID = "arxiv_2610_38474_graph_subtraction"
FILE = "Arxiv261038474.lean"
SOURCE_URL = "https://arxiv.org/html/2610.38474v1#S9.SS1"
PUBLICATION_TITLE = "On the motivic approach to the Abhyankar rectifiability problem and concrete rectifications"
SOURCE_LOCATOR = "§9.1, Lemma 9.1, equations (9.1)–(9.2): final permutation and graph subtraction"
IMPORTS = ["Mathlib.Algebra.MvPolynomial.Eval", "Mathlib.Algebra.MvPolynomial.CommRing",
           "Mathlib.Algebra.Polynomial.Eval.Coeff", "Mathlib.Data.Fin.VecNotation", "Mathlib.Tactic.FinCases"]
PREFIX = "∀ {R : Type u} [CommRing R] (b w : Polynomial R),\n  "
SUBTRACT_RESTORE = PREFIX + "Arxiv261038474.compose (Arxiv261038474.graphSubtract b w) (Arxiv261038474.graphRestore b w) = MvPolynomial.X"
RESTORE_SUBTRACT = PREFIX + "Arxiv261038474.compose (Arxiv261038474.graphRestore b w) (Arxiv261038474.graphSubtract b w) = MvPolynomial.X"
GRAPH_TO_AXIS = PREFIX + "Arxiv261038474.alongGraph (Arxiv261038474.graphSubtract b w) b w = ![Polynomial.X, 0, 0]"
EVAL_UNIVARIATE = """∀ {R : Type u} [CommRing R] {S : Type v} [CommRing S]
  (f : R →+* S) (v : Fin 3 → S) (p : Polynomial R) (i : Fin 3),
  MvPolynomial.eval₂ f v (Arxiv261038474.univariate p i) = p.eval₂ f (v i)"""
LIMITATIONS = [
    "Проверен заключительный шаг §9.1 для уже заданного полиномиального графа (b(t),t,w(t)).",
    "Предшествующий автоморфизм A=(x,H,W), условие H∘i=t и переход произвольной кривой в этот граф не построены.",
    "Формулы трефойла и гармонической восьмёрки, точная делимость §9.3/§9.7/§9.8 и мотивная часть статьи не проверены.",
    "Это воспроизведение известного алгебраического шага статьи, не утверждение научной новизны.",
]


def source():
    return (ROOT / "research_fixtures" / FILE).read_text(encoding="utf-8")


def obligations():
    return [dict(id=identifier, title=title, target="Arxiv261038474." + identifier,
                 statement=statement, expected_outcome="proved")
            for identifier, title, statement in [
                ("subtract_restore", "S ∘ S⁻¹ = id в кольце полиномов", SUBTRACT_RESTORE),
                ("restore_subtract", "S⁻¹ ∘ S = id в кольце полиномов", RESTORE_SUBTRACT),
                ("graph_to_axis", "Полиномиальный граф переходит в ось", GRAPH_TO_AXIS),
            ]]


def fixture():
    """Canonical fixture metadata, without registering it in the pilot registry."""
    text = source()
    prelude = text[:text.index("theorem eval_univariate")] + "end\n\nend Arxiv261038474\n"
    goals = obligations()
    helper = dict(id="eval_univariate", target="Arxiv261038474.eval_univariate", dependencies=[],
                  statement=EVAL_UNIVARIATE)
    lemmas = [helper] + [dict(id=o["id"], target=o["target"], statement=o["statement"],
                              dependencies=["eval_univariate"]) for o in goals]
    task = dict(imports=list(IMPORTS), prelude=prelude, target="Arxiv261038474.graph_to_axis",
                statement=GRAPH_TO_AXIS, required_obligations=goals, lemmas=lemmas,
                context="Докажите три полиномиальных равенства для заключительного шага §9.1. "
                        "Координаты принадлежат MvPolynomial (Fin 3) R; равенство только значений на поле недостаточно. "
                        "Не добавляйте x≠0 или деление. Предшествующий автоморфизм статьи не является целью.")
    task.update(prelude_sha256=hashlib.sha256(prelude.encode()).hexdigest(),
                statement_sha256=hashlib.sha256(GRAPH_TO_AXIS.encode()).hexdigest())
    return dict(id=CASE_ID, title="Frolov–Dorofeev: полиномиальный граф → ось", msc_codes=["14R10", "13F20"],
                description="Заключительная перестановка и вычитание графа из §9.1; обе композиции проверяются как полиномы.",
                claim="Для любого коммутативного кольца R и b,w∈R[t] полиномиальные S=(y,x−b(y),z−w(y)) "
                      "и S⁻¹=(X+b(T),T,Z+w(T)) взаимно обратны, а S(b(t),t,w(t))=(t,0,0).",
                target=task["target"], expected_statement=GRAPH_TO_AXIS, expected_outcome="proved", file=FILE,
                source=PUBLICATION_TITLE + ". A. S. Frolov, I. S. Dorofeev. arXiv:2610.38474v1, §9.1, заключительный шаг",
                source_sha256=hashlib.sha256(text.encode()).hexdigest(),
                evidence=[dict(kind="arxiv_source", title=PUBLICATION_TITLE, description="A. S. Frolov, I. S. Dorofeev · arXiv:2610.38474v1 · §9.1", url=SOURCE_URL, locator=SOURCE_LOCATOR)],
                required_obligations=goals, agent_task=task,
                preview_nodes=[lemma["target"] for lemma in lemmas],
                preview_edges=[[helper["target"], o["target"]] for o in goals],
                semantic_review=dict(status="reviewed_fixture", scope="Полиномиальный заключительный шаг §9.1.",
                                     findings=list(LIMITATIONS), novelty="known_source_result"))


def graph_for_article():
    prepared = fixture()
    task = prepared["agent_task"]
    parameters = ["R — произвольное коммутативное кольцо с единицей", "b,w ∈ R[t]"]
    assumptions = ["CommRing R", "Кривая уже имеет вид (b(t),t,w(t))"]
    objects = [
        dict(id="polynomial_graph", title="Полиномиальный граф в трёхмерном пространстве", kind="parametrized_curve",
             definition="γ(t)=(b(t),t,w(t)); координаты заданы полиномами из R[t].", parameters=parameters,
             assumptions=assumptions, msc_codes=["14R10", "13F20"], lean_refs=["Arxiv261038474.graphCurve"]),
        dict(id="coordinate_axis", title="Координатная ось", kind="parametrized_curve",
             definition="ℓ(t)=(t,0,0) над тем же кольцом R.", parameters=[parameters[0]],
             assumptions=["CommRing R"], msc_codes=["14R10"], lean_refs=[]),
    ]
    transition = dict(id="graph_subtraction", title="Вычесть граф и переставить координаты",
                      source_ids=["polynomial_graph"], target_ids=["coordinate_axis"], relation_type="equivalence",
                      construction="S(x,y,z)=(y,x−b(y),z−w(y)); S⁻¹(T,X,Z)=(X+b(T),T,Z+w(T)). "
                                   "Сравнить координаты обеих композиций в R[x,y,z] и образ графа в R[t].",
                      assumptions=assumptions, claim=prepared["claim"] + " Это заключительный шаг §9.1, не весь выпрямитель статьи.",
                      obligations=obligations(), agent_task={key: task[key] for key in ("imports", "prelude", "target", "statement")},
                      case_id=CASE_ID)
    return dict(title=prepared["title"], question="Как полиномиальный автоморфизм переводит уже полученный граф в координатную ось?",
                msc_codes=list(prepared["msc_codes"]), objects=objects, transitions=[transition],
                sources=[dict(id="arxiv_2610_38474_v1", title="On the motivic approach to the Abhyankar rectifiability problem and concrete rectifications",
                              url=SOURCE_URL, locator=SOURCE_LOCATOR)])


def example():
    """Source locator and explicit scope for callers that do not need the graph."""
    return dict(case_id=CASE_ID, title=fixture()["title"], source_url=SOURCE_URL, source_locator=SOURCE_LOCATOR,
                selected_transition="graph_subtraction", scope="Заключительный полиномиальный шаг §9.1",
                assumptions=["CommRing R", "b,w : Polynomial R"], limitations=list(LIMITATIONS),
                obligation_ids=[item["id"] for item in obligations()], graph=graph_for_article())
