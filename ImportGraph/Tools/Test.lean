module

import ImportGraph.Tools.MinImports
public meta import Lean.Elab.Command

#min_imports

-- run_cmd do

open Lean

run_cmd do
  logInfo m!"{(← getEnv).header.imports}"

run_cmd do
  let env ← getEnv
  let mut encountered : Std.HashSet Name := {}
  let mut outOfOrder : Std.HashMap (Name × Nat) (Array Import) := {}
  for h : i in 0...env.header.moduleData.size do
    let { imports .. } := env.header.moduleData[i]
    let name := env.allImportedModuleNames[i]!
    let notEncountered := imports.filter (!encountered.contains ·.module)
    unless notEncountered.isEmpty do
      outOfOrder := outOfOrder.insert (name, i) notEncountered
    encountered := encountered.insert name
  logInfo m!"{outOfOrder.toArray.qsort (·.1.2 < ·.1.2)}"

-- hello
-- goodbye
