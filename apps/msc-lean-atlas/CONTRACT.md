# Implementation contract

Local Python 3.9+ standard-library backend, static HTML/CSS/JS UI; bind 127.0.0.1.
Keep existing SHAIM and astra-math-research proof sources and reports unchanged.

## Dataset

`data/msc2020.json`: `{meta, nodes, edges}`.
Nodes: `{id, code, title, parent_id, level, description?}`. IDs are normalized codes
(`05`, `05C`, `05C50`, preserving special codes such as `05-00`). Levels 0,1,2.
Edges: `{id, source, target, type, reference_text?}` with type `broader`,
`see_also`, or `classify_elsewhere` (more explicit types permitted if needed).
For broader edges source is child, target is parent. Do not invent semantic edges.
Metadata contains source URL, file hash, retrieval time, license/attribution,
actual counts, unresolved references. Preserve original source file.

## HTTP API (parent owns server/analysis integration)

GET `/api/graph` returns dataset.
GET `/api/status` returns `{ready, context, data, capabilities}`.
GET `/api/examples` returns list of `{id,title,description,files:[{name,content}],context,targets?,bridge_source?,bridge_targets?}`.
POST `/api/analyze`: `{files:[{name,content},{name,content}], context:{project_root?,lean?,mathlib?}, targets?:[string,string], msc_overrides?:[string[],string[]]}`.
POST `/api/verify`: `{analysis_id, bridge_source, bridge_targets:[string]}`.
POST returns `{job_id}`. GET `/api/jobs/{job_id}` returns
`{status:'queued'|'running'|'complete'|'failed', progress, result?, error?}`.
GET `/api/runs/{analysis_id}` returns saved analysis.

Analysis result: `{id,files:[{name,sha256,declarations,inspection_status,msc_matches}], taxonomy_paths, candidates, inspection, bridge_source?,bridge_targets?,notes}`.
Declaration: `{name,kind,type?,dependencies?,line?}`.
MSC match: `{code,title,score,evidence,status:'suggested'|'user_confirmed'}`.
Candidate: `{id,title,status:'candidate'|'known_bridge',kind,explanation,evidence,source_declarations?,target_declarations?,source_url?,requirements?}`.
Taxonomy paths explicitly have `status:'navigation_only'`.

## Lean service (agent owns lean_service.py, tools/, examples/, own tests)

`default_context() -> dict`
`inspect_files(files, context, run_dir: Path) -> dict` with `files` as above and
result `{status, files:[{name,sha256,declarations,inspection_status}], diagnostics,
context, ...}`. Failure must not claim semantic extraction succeeded. Lexical
fallback explicitly marked if needed. Prefer compiler-resolved declarations.
`verify_bridge(source: str, targets: list[str], context: dict, run_dir: Path,
 inspection: dict | None = None) -> dict`: `{status,success,diagnostics,targets,
axioms,source_sha256,checked_at,context,...}`. A source hash and current run required.
No success with sorry/admit or extra axioms. No stale success on failure. Include
source evidence for declarations from both input modules or report unrelated proof.
`load_examples() -> list[dict]` per endpoint schema.

Environment already prepared:
Lean: `ATLAS_LEAN` (Lean 4.19.0).
mathlib: `ATLAS_MATHLIB` (revision pinned in the repository).
Project: `ATLAS_PROJECT_ROOT` (repository root).
