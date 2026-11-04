# Pipeline and UI upgrade — 2026-11-03

Historical plan and completion record for the 3 November stage. Its publication
authorization and Mobbin availability describe that stage only. For the current
interface and later work, see [README.md](README.md) and
[UI_MOBBIN_REVIEW.md](../../docs/UI_MOBBIN_REVIEW.md).

Authorized scope: eight As Is → To Be tasks agreed in the Codex conversation.
Work branch: `codex/research-pipeline-ui`. The original MathResearch kit is immutable.

| Task | Acceptance | Owner |
| --- | --- | --- |
| Source-grounded transition card | Objects, operations, assumptions, precise conclusion, citations and proposed abstractions are inspectable; edits create a new version | coordinator |
| Draft contract repair | Bounded Lean diagnostics/repair before freeze, immutable semantic intent, complete obligations, durable attempts, cancellation and budget | coordinator |
| Hybrid retrieval | Lexical/type candidate retrieval plus separately measured semantic reranking; 0–6 justified MSC routes; empty results supported | project_review |
| Goedel integration | Actual pinned upstream code, explicit compliant adaptation, no proof holes or new axioms, independent local Lean acceptance, runtime provenance | goedel_engine |
| Verified mechanisms | Searchable catalog; registration rechecks full proof and provenance; new applications require their own proof | project_review + coordinator hooks |
| Research controls | Visible source/version/stage/budget and useful recovery; preserved history and resumability | coordinator + frontend_checks |
| Evaluation | Fixed fixtures with negatives and held-out cases; truthful metrics; regression checks and final report | all scoped checks, coordinator final |
| UI redesign | Documented design decisions, complete UI states, responsive/keyboard checks and Computer Use. Mobbin MCP returned a paid-plan requirement; the user explicitly authorized proceeding without Mobbin on 2026-11-03. | frontend_checks + coordinator verification |

Sequence: baseline and interface contracts → independent implementation → integration → review → frozen-source full checks → browser acceptance.

Evidence lives in `runs/current/pipeline-upgrade-2026-11-03/`. The completion report must distinguish compilation, semantic review, useful retrieval, and novelty. No external publication is authorized. No success may be inferred from old reports. Any unresolved external dependency remains explicit.

## Completion — 2026-11-03

All eight implementation tasks are complete. Final frozen-source checks: 342 Python tests and 219 JavaScript tests passed without skips; `npm run test:graph` passed 17 checks. The unchanged original kit passed a fresh 11-file/149-declaration Lean check. A real correction through the UI repaired `Function.iterate`, proved all four dynamics obligations through the adapted Goedel backend, and registered a separately rechecked mechanism. A subsequent search used the semantic ranking stage and found that catalog entry, without inheriting its proof certificate.

Computer Use verified history filters, keyboard map selection, version comparison and responsive widths. The live check caught and fixed a global JS export collision and hard-coded route placeholders. Narrow viewport screenshot capture was unavailable; DOM layout checks and desktop screenshots are retained. Semantic benchmark statistics beyond the small live case are not claimed; the fixed offline benchmark measures candidate retrieval separately.

The complete As Is → To Be outcome, actual commands, unsuccessful preliminary attempts, metrics and limits are recorded in `../../runs/current/pipeline-upgrade-2026-11-03/result.md` (relative to the repository root: `runs/current/pipeline-upgrade-2026-11-03/result.md`). Mobbin was waived explicitly by the user. No repository publication was performed.
