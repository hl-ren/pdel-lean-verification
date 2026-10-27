import PdelIntegration
open Lean Elab Command
run_cmd do
  let env ← getEnv
  let namesJson := fun (ns : Array Name) => Json.arr (ns.map (fun n => Json.str n.toString))
  for (n, info) in env.constants do
    if let some idx := env.getModuleIdxFor? n then
      let mod := env.allImportedModuleNames[idx.toNat]!
      if mod.toString.startsWith "Pdel" then
        let valueDeps := match info.value? with
          | some v => v.getUsedConstants
          | none => #[]
        let kind := match info with
          | .axiomInfo _ => "axiom"
          | .thmInfo _ => "theorem"
          | .defnInfo _ => "definition"
          | .opaqueInfo _ => "opaque"
          | .inductInfo _ => "inductive"
          | .ctorInfo _ => "constructor"
          | .recInfo _ => "recursor"
          | .quotInfo _ => "quotient"
        let record := Json.mkObj [("name", Json.str n.toString),
          ("module", Json.str mod.toString), ("kind", Json.str kind),
          ("unsafe", Json.bool info.isUnsafe),
          ("kernel_present", Json.bool ((env.checked.get.find? n).isSome)),
          ("type_dependencies", namesJson info.type.getUsedConstants),
          ("value_dependencies", namesJson valueDeps)]
        logInfo m!"PDEL_DEP {record.compress}"
  for mod in env.allImportedModuleNames do
    if mod.toString.startsWith "Pdel" then
      let path ← findOLean mod
      let record := Json.mkObj [("module",Json.str mod.toString),("olean",Json.str path.toString)]
      logInfo m!"PDEL_MODULE {record.compress}"
