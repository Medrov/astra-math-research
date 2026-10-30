"""Published associator/Laplacian identity, explicitly reused rather than rediscovered."""
from __future__ import annotations

import hashlib
from pathlib import Path


ROOT = Path(__file__).resolve().parent
CASE_ID = "published_associator_laplacian"
FILE = "PublishedAssociator.lean"
IMPORT = "MathResearch.AlbertSpectralGeometry"
TARGET = "Bridge.energy_correspondence"
STATEMENT = "∀ (d f : Fin 3 → ℚ), AlgebraObject.energy d f = GraphObject.energy d f"
PUBLICATION_COMMIT = "4898f7013d626fef293d17bddfd860791e6daed0"
PUBLICATION_TITLE = "Связи математических объектов и общие структуры: три пары с проверкой в Lean"
BASE_URL = "https://github.com/Medrov/astra-math-research/blob/" + PUBLICATION_COMMIT + "/"
LIMITATIONS = [
    "Повторно используется опубликованная теорема associatorDirichlet_graphLaplacian; это проверка известной связи, не слепое переоткрытие.",
    "Утверждение относится к рациональной 27-координатной модели и трём вершинам с весами (dᵢ−dⱼ)²/4.",
    "Диагональный ассоциатор действует на октонионных рёберных координатах и сам по себе не является лапласианом на вершинах; равенство связывает энергии после градиентного вложения и спаривания.",
    "Не утверждаются полная формализация алгебры Альберта, тождество произвольных алгебр и графов или научная новизна.",
    "Новая сборка охватывает четыре зависимых модуля этого примера; полный исходный комплект 11/149 этим запуском не перепроверяется.",
]


def source():
    return (ROOT / "research_fixtures" / FILE).read_text(encoding="utf-8")


def obligations():
    return [dict(id="energy_correspondence", title="Равенство энергий опубликованной модели", target=TARGET,
                 statement=STATEMENT, expected_outcome="proved")]


def fixture():
    text = source()
    prelude = text[:text.index("namespace Bridge")]
    task = dict(imports=[IMPORT], prelude=prelude, target=TARGET, statement=STATEMENT,
                required_obligations=obligations(),
                lemmas=[dict(id="energy_correspondence", target=TARGET, statement=STATEMENT, dependencies=[])],
                context="Используйте опубликованную associatorDirichlet_graphLaplacian для точных адаптеров AlgebraObject.energy и GraphObject.energy. "
                        "Не заменяйте ассоциатор произвольной суммой квадратов. Это повторное использование готового доказательства.")
    task.update(prelude_sha256=hashlib.sha256(prelude.encode()).hexdigest(),
                statement_sha256=hashlib.sha256(STATEMENT.encode()).hexdigest())
    return dict(id=CASE_ID, title="Опубликованный пример: ассоциатор ↔ лапласиан", msc_codes=["17C40", "05C50"],
                description="Энергия реального диагонального ассоциатора рациональной модели совпадает с энергией взвешенного лапласиана.",
                claim="Для d,f:Fin 3→ℚ энергия диагонального ассоциатора, спаренного со скалярным градиентом f, равна fᵀL_df; веса L_d равны (dᵢ−dⱼ)²/4.",
                target=TARGET, expected_statement=STATEMENT, expected_outcome="proved", file=FILE,
                source=PUBLICATION_TITLE + ", v1.5, 29 октября 2026 года",
                evidence=[dict(kind="published_project_source", url=BASE_URL + "docs/Preprint.pdf",
                               locator="v1.5, §3.4 «Графовая интерпретация», формула eq:energy; associatorDirichlet_graphLaplacian"),
                          dict(kind="published_lean_source", url=BASE_URL + "MathResearch/AlbertSpectralGeometry.lean",
                               locator="associatorDirichlet; graphLaplacian; associatorDirichlet_graphLaplacian")],
                source_sha256=hashlib.sha256(text.encode()).hexdigest(), required_obligations=obligations(), agent_task=task,
                preview_nodes=["AlgebraObject.energy", "GraphObject.energy", TARGET],
                preview_edges=[["AlgebraObject.energy", TARGET], ["GraphObject.energy", TARGET]],
                semantic_review=dict(status="reviewed_fixture", scope="Повторное использование опубликованной связи энергий в точной рациональной модели.",
                                     findings=list(LIMITATIONS), novelty="published_proof_reuse"))


def graph_for_published_example():
    item = fixture()
    parameters = ["d : Fin 3 → ℚ — диагональные значения", "f : Fin 3 → ℚ — значения на трёх вершинах"]
    common = ["Рациональная 27-координатная модель MathResearch.Albert", "Вес ребра ij равен (dᵢ−dⱼ)²/4"]
    objects = [
        dict(id="associator_energy", title="Энергия диагонального ассоциатора", kind="algebraic_energy",
             definition="associatorDirichlet d f: спаривание diagonalDefect d (gradient f) со скалярными разностями fᵢ−fⱼ в трёх октонионных рёберных координатах.",
             parameters=parameters, assumptions=common, msc_codes=["17C40"],
             lean_refs=["AlgebraObject.energy", "MathResearch.AlbertSpectralGeometry.associatorDirichlet"]),
        dict(id="laplacian_energy", title="Энергия лапласиана с теми же весами", kind="graph_energy",
             definition="fᵀL_df = Σᵢ fᵢ(L_df)ᵢ; graphLaplacian d использует веса (dᵢ−dⱼ)²/4.",
             parameters=parameters, assumptions=common, msc_codes=["05C50"],
             lean_refs=["GraphObject.energy", "MathResearch.AlbertSpectralGeometry.graphLaplacian"]),
    ]
    task = item["agent_task"]
    transition = dict(id="energy_correspondence", title="От ассоциатора к энергии лапласиана",
                      source_ids=["associator_energy"], target_ids=["laplacian_energy"], relation_type="representation",
                      construction="Вложить градиент в скалярные компоненты октонионных рёбер, применить диагональный ассоциатор и спарить с теми же разностями. Применить опубликованную теорему равенства энергий.",
                      assumptions=common, claim=item["claim"], obligations=obligations(),
                      agent_task={key: task[key] for key in ("imports", "prelude", "target", "statement")}, case_id=CASE_ID)
    return dict(title=item["title"], question="Как энергия диагонального ассоциатора опубликованной модели представляется энергией графового лапласиана?",
                msc_codes=list(item["msc_codes"]), objects=objects, transitions=[transition],
                sources=[dict(id="published_preprint", title=PUBLICATION_TITLE + " — v1.5, 29.10.2026", url=BASE_URL + "docs/Preprint.pdf", locator="§3.4 «Графовая интерпретация», формула eq:energy"),
                         dict(id="published_lean", title="AlbertSpectralGeometry.lean", url=BASE_URL + "MathResearch/AlbertSpectralGeometry.lean", locator="associatorDirichlet_graphLaplacian")])
