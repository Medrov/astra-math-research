import Lean
import Lean.Util.CollectAxioms
import Lean.Util.FoldConsts
import Lean.Replay

open Lean Elab Command Meta

namespace AtlasInspect

def kindOf : ConstantInfo → String
  | .axiomInfo _ => "axiom"
  | .defnInfo _ => "def"
  | .thmInfo _ => "theorem"
  | .opaqueInfo _ => "opaque"
  | .quotInfo _ => "quotient"
  | .inductInfo _ => "inductive"
  | .ctorInfo _ => "constructor"
  | .recInfo _ => "recursor"

def moduleOf (env : Environment) (n : Name) : String :=
  match env.getModuleIdxFor? n with
  | some idx => (env.header.moduleNames[idx]!).toString
  | none => env.mainModule.toString

-- Record syntactic participation, not mathematical usefulness of a theorem.
def reachableInputs (env : Environment) (ci : ConstantInfo) (inputs : Array String) : Array String × Bool := Id.run do
  if inputs.isEmpty then return (#[], false)
  let mut todo := ci.getUsedConstantsAsSet.toArray
  let mut visited : NameSet := {}
  let mut found : Array String := #[]
  let mut foundModules : Array String := #[]
  -- Most bridge statements mention both input objects directly. Check these
  -- before exploring potentially large proof dependencies from mathlib.
  for n in todo do
    let m := moduleOf env n
    if inputs.contains m then
      found := found.push n.toString
      unless foundModules.contains m do foundModules := foundModules.push m
  if inputs.all foundModules.contains then return (found, false)
  let mut steps := 0
  while !todo.isEmpty && steps < 100000 do
    let n := todo.back!
    todo := todo.pop
    unless visited.contains n do
      steps := steps + 1
      visited := visited.insert n
      let m := moduleOf env n
      if inputs.contains m then
        unless found.contains n.toString do found := found.push n.toString
        unless foundModules.contains m do foundModules := foundModules.push m
        if inputs.all foundModules.contains then return (found, false)
      if let some dep := env.find? n then
        todo := todo ++ dep.getUsedConstantsAsSet.toArray
  return (found, !todo.isEmpty)

syntax "#atlas_export " "[" str,* "]" "[" str,* "]" str : command
elab_rules : command
  | `(#atlas_export [$mods:str,*] [$inputs:str,*] $output:str) => do
    let wanted := mods.getElems.map (·.getString)
    let inputModules := inputs.getElems.map (·.getString)
    let env ← getEnv
    let mut records : Array Json := #[]
    for idx in [:env.header.moduleNames.size] do
      let module := env.header.moduleNames[idx]!.toString
      if wanted.contains module then
        for ci in env.header.moduleData[idx]!.constants do
          let name := ci.name
          unless name.anyS (·.startsWith "_cstage") do
            let formatted ← liftTermElabM <| Meta.ppExpr ci.type
            let ax ← collectAxioms name
            let (reachable, truncated) := reachableInputs env ci inputModules
            records := records.push <| Json.mkObj [
              ("name", toJson name.toString),
              ("module", toJson module),
              ("kind", toJson (kindOf ci)),
              ("unsafe", toJson ci.isUnsafe),
              ("type", toJson formatted.pretty),
              ("type_dependencies", toJson (ci.type.getUsedConstants.map Name.toString)),
              ("dependencies", toJson (ci.getUsedConstantsAsSet.toArray.map Name.toString)),
              ("axioms", toJson (ax.map Name.toString)),
              ("reachable_input_declarations", toJson reachable),
              ("dependency_walk_truncated", toJson truncated)]
    let result := Json.mkObj [
      ("declarations", toJson records),
      ("imported_modules", toJson (env.header.moduleNames.map Name.toString))]
    liftIO <| IO.FS.writeFile output.getString result.compress
-- Resolve only requested constants, avoiding a full module dependency dump.
syntax "#atlas_export_names " "[" str,* "]" "[" str,* "]" str : command
elab_rules : command
  | `(#atlas_export_names [$names:str,*] [$inputs:str,*] $output:str) => do
    let inputModules := inputs.getElems.map (·.getString)
    let env ← getEnv
    let mut records : Array Json := #[]
    let mut missing : Array String := #[]
    for text in names.getElems.map (·.getString) do
      let name := text.toName
      if let some ci := env.find? name then
        let formatted ← liftTermElabM <| Meta.ppExpr ci.type
        let ax ← collectAxioms name
        let (reachable, truncated) := reachableInputs env ci inputModules
        records := records.push <| Json.mkObj [
          ("name", toJson name.toString),
          ("module", toJson (moduleOf env name)),
          ("kind", toJson (kindOf ci)),
          ("unsafe", toJson ci.isUnsafe),
          ("type", toJson formatted.pretty),
          ("type_dependencies", toJson (ci.type.getUsedConstants.map Name.toString)),
          ("dependencies", toJson (ci.getUsedConstantsAsSet.toArray.map Name.toString)),
          ("axioms", toJson (ax.map Name.toString)),
          ("reachable_input_declarations", toJson reachable),
          ("dependency_walk_truncated", toJson truncated)]
      else
        missing := missing.push text
    let result := Json.mkObj [
      ("declarations", toJson records),
      ("missing_names", toJson missing),
      ("imported_modules", toJson (env.header.moduleNames.map Name.toString))]
    liftIO <| IO.FS.writeFile output.getString result.compress
/-- Replay just the target's compiled project declarations into a fresh kernel
    environment. Only the installed libraries imported by the project are trusted. -/
def kernelRecheck (env : Environment) (modules : Array String) (target : Name) : IO Json := do
  let mut imports : Array Import := #[]
  for mod in modules do
    let some idx := env.header.moduleNames.idxOf? mod.toName
      | throw <| IO.userError s!"Missing project module {mod}"
    for imp in env.header.moduleData[idx]!.imports do
      unless modules.contains imp.module.toString || imports.any (·.module == imp.module) do
        imports := imports.push imp
  let base ← importModules imports {} 0
  if base.header.moduleNames.any (fun n => modules.contains n.toString) then
    throw <| IO.userError "The base environment already imports a project module"
  unless modules.contains (moduleOf env target) && (env.find? target).any (·.isTheorem) do
    throw <| IO.userError s!"Expected a local theorem: {target}"
  let mut decls : Std.HashMap Name ConstantInfo := {}
  let mut todo := #[target]
  while !todo.isEmpty do
    let n := todo.back!
    todo := todo.pop
    if !decls.contains n && modules.contains (moduleOf env n) then
      let some ci := env.find? n | throw <| IO.userError s!"Missing declaration {n}"
      if ci.isUnsafe || ci.isPartial || ci.isAxiom then
        throw <| IO.userError s!"Uncheckable project dependency: {n}"
      decls := decls.insert n ci
      todo := todo ++ ci.getUsedConstantsAsSet.toArray
      -- Reconstruct mutual inductive blocks in their entirety, including
      -- constructors that are not explicitly mentioned in this proof term.
      if let .inductInfo info := ci then todo := todo ++ info.all.toArray
  let checked ← Environment.replay decls base
  for (n, _) in decls do
    unless checked.contains n do throw <| IO.userError s!"Kernel did not replay {n}"
  let names := (decls.toArray.map (fun p => p.1.toString)).qsort (· < ·)
  return Json.mkObj [("target", toJson target.toString), ("checked", toJson names),
                     ("checked_count", toJson names.size), ("status", "passed"),
                     ("scope", "project_dependency_closure")]

syntax "#atlas_recheck " "[" str,* "]" str str : command
elab_rules : command
  | `(#atlas_recheck [$mods:str,*] $target:str $output:str) => do
    let result ← liftIO <| kernelRecheck (← getEnv) (mods.getElems.map (·.getString)) target.getString.toName
    liftIO <| IO.FS.writeFile output.getString result.compress

end AtlasInspect
