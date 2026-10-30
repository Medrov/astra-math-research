# MSC × Lean: completion criteria

The current goal is a local, working research prototype, not a theorem that any
two mathematical objects admit a useful relationship.

- [x] Entire official MSC source imported, including hierarchy, special codes,
  typed cross references, original source and provenance; discrepancies recorded.
- [x] All imported categories reachable through navigation/search in the UI.
- [x] Two arbitrary Lean source files can be supplied with their project context.
- [x] Compiler-resolved declarations or an explicitly unverified fallback are
  visible; classification suggestions can be corrected by the user.
- [x] Navigation-only paths and candidate mathematical bridges stay separate.
- [x] A bridge can be checked with real Lean; a current proof, axiom audit and
  source hashes are required before a verified status is shown.
- [x] Reproducible project example traverses upload → classification → candidates
  → bridge → successful verification. A failed/unrelated proof stays unverified.
- [x] Backend tests, browser interaction/layout checks, startup documentation and
  a saved end-to-end report are complete.

Implementation is isolated here. Existing published mathematical sources,
certificates and Git repository remain unchanged. No publishing is required.
