import Lean
import Lean.Util.CollectAxioms
import Lean.Util.FoldConsts

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
end AtlasInspect
