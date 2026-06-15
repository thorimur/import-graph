/-
Copyright (c) 2023 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison, Paul Lezeau
-/
module

public meta import Lean.Elab.Command
public meta import Lean.Widget.UserWidget
public meta import ImportGraph.Imports.RequiredModules
public meta import ImportGraph.Imports.Redundant
public meta import ImportGraph.Shake.Environment
public meta import ImportGraph.Shake.Algebra
public meta import ImportGraph.Shake.Basic
public meta import ImportGraph.Imports.Pretty
import all ImportGraph.Shake.Environment
import Lean

public meta section

open Lean

/--
Return the names of the modules in which constants used in the current file were defined,
with modules already transitively imported removed.

Note that this will *not* account for tactics and syntax used in the file,
so the results may not suffice as imports.
-/
def Lean.Environment.minimalRequiredModules (env : Environment) : Array Name :=
  let required := env.requiredModules.toArray.erase env.header.mainModule
  let redundant := findRedundantImports env required
  required.filter fun n => ¬ redundant.contains n

def ImportGraph.parseCurrentHeader {m} [Monad m] [MonadLog m] [MonadLiftT IO m] :
    m (TSyntax `Lean.Parser.Module.header × Parser.ModuleParserState × MessageLog) := do
  Parser.parseHeader (Parser.mkInputContext (← getFileMap).source (← getFileName))

open ImportGraph

elab "#min_imports" : command => do
  let transDeps := (← getEnv).mkTransDeps
  let transNeeds := (← getEnv).transNeeds transDeps
  -- let reducedImps := transNeeds.reduce transDeps |>.toImports (← getEnv)
  -- let reducedImps := Import.includeAll (← getEnv).header.imports reducedImps
  -- let (header, _, log) ← parseCurrentHeader
  -- if log.hasErrors then return
  -- let impsWithRefs := headerToImportRefsWithWhitespace header
  logInfo m!"{transNeeds.toImports (← getEnv)}"
  -- let msg := Import.prettyWithWhitespaceFromSourceAndErrorComment reducedImps impsWithRefs
  -- let str := msg.pretty
  -- let _e ← Elab.Command.liftCoreM <|
  --   Meta.Hint.mkSuggestionsMessage #[{ suggestion := str, diffGranularity := .word}] (mkNullNode (impsWithRefs.map (·.1.stx.raw))) none false
  -- logInfo m!"{e}"

-- #min_imports

run_cmd do
  let env ← getEnv
  let mut encountered : Std.HashSet Name := {}
  let mut outOfOrder : Std.HashMap (Name × Nat) (Array Import) := {}
  for h : i in 0...env.header.moduleData.size do
    let { imports .. } := env.header.moduleData[i]
    let name := env.header.modules[i]!.module
    let notEncounteredYet := imports.filter (!encountered.contains ·.module)
    unless notEncounteredYet.isEmpty do
      outOfOrder := outOfOrder.insert (name, i) notEncounteredYet
    encountered := encountered.insert name
  let (eventuallyEncountered, notEncountered) :=
    outOfOrder.valuesArray.flatten.partition (encountered.contains ·.module)
  logInfo m!"\n\
    total := {env.header.moduleData.size}\n\
    eventuallyEncountered := {eventuallyEncountered.size}\n\
    notEncountered := {notEncountered.size}\n\
    {outOfOrder.toArray.qsort (·.1.2 < ·.1.2)}"


-- /--
-- Try to compute a minimal set of imports for this file,
-- by analyzing the declarations.

-- This must be run at the end of the file,
-- and is not aware of syntax and tactics,
-- so the results will likely need to be adjusted by hand.
-- -/
-- elab "#min_imports" : command => do
--   let imports := (← getEnv).minimalRequiredModules.qsort (·.toString < ·.toString)
--     |>.toList.map (fun n => "public import " ++ n.toString)
--   logInfo <| Format.joinSep imports "\n"

-- deprecated since 2024-07-06
elab "#minimize_imports" : command => do
  logWarning m!"'#minimize_imports' is deprecated: please use '#min_imports'"
  Elab.Command.elabCommand (← `(command| #min_imports))
