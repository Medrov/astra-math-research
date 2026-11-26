import Lean
import Lean.Util.CollectAxioms

open Lean Elab Command Meta

/-- Resolve a short list of index hits against the imported, compiled library. -/
syntax "#pattern_sources " "[" str,* "]" str : command

elab_rules : command
  | `(#pattern_sources [$names:str,*] $output:str) => do
    let env ← getEnv
    let mut records := #[]
    for literal in names.getElems do
      let name := literal.getString.toName
      let some ci := env.find? name | continue
      let .thmInfo _ := ci | continue
      let some idx := env.getModuleIdxFor? name | continue
      let ty ← liftTermElabM <| Meta.ppExpr ci.type
      let axioms ← collectAxioms name
      records := records.push <| Json.mkObj [
        ("name", toJson name.toString), ("module", toJson env.header.moduleNames[idx]!.toString),
        ("statement", toJson ty.pretty), ("axioms", toJson (axioms.map Name.toString))]
    liftIO <| IO.FS.writeFile output.getString (toJson records).compress
