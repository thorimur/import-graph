/-
Copyright (c) 2023 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison, Paul Lezeau
-/
module

public import Lean.Elab.Command

public meta import ImportGraph.Shake.DeclNeeds
public meta import ImportGraph.Imports.FromSource
public meta import ImportGraph.Imports.Pretty
public meta import ImportGraph.Shake.Environment
public meta import ImportGraph.Shake.Workspace
public meta import ImportGraph.Util.RunLater

/-
Comments were present when importing `ImportGraph.Util.RunLater`, but this module is now imported differently as `import ImportGraph.Util.RunLater`.
Decide if the following original comments still apply:
```
-- public meta import ImportGraph.Tools.NeedsGrid
public meta import ImportGraph.Util.RunLater
```

Comments were present when importing `Lean.Elab.Command`, but this module is now imported differently as `public import Lean.Elab.Command`.
Decide if the following original comments still apply:
```
import all Lean.Elab.Command -- for `recordUsedSyntaxKinds`
```

The following imports did not appear in the new import list, but had comments around them:
```
-- import all ImportGraph.Tools.NeedsGrid
import all ImportGraph.Shake.DeclNeeds
```

-/

open ImportGraph Lean Elab Command Shake

meta def getModuleDeclNeeds (cmds : Array Syntax) :
    CommandElabM (DeclNeeds × Std.HashMap Name (Option Stance)) := do
  let mut declNeeds := ∅
  -- TODO: more accurate targeting of declarations and commands.
  for (decl, _) in (← getEnv).constants.map₂ do
    declNeeds := calcDeclConstInfoNeeds decl (← getEnv) declNeeds
  for cmd in cmds do
    declNeeds ← declNeeds.calcSyntaxNeeds (← getEnv) (declNeeds.keysArray) cmd
  liftCoreM <| StanceM.run <| declNeeds.calcIRNeeds

-- TODO: process shake annotations instead of leaving them in the error.
elab tk:"#min_imports" : command => do
  runLaterWithSyntax fun cmds => withRef tk do
    let (declNeeds, s) ← getModuleDeclNeeds cmds
    let env ← getEnv
    let metas := declNeeds.filter fun decl _ => isMarkedMeta env decl
    let metas := metas.keys.map (m!"• {.ofConstName ·}")
    unless metas.isEmpty do
      logWarning m!"Some declarations are marked meta. `#min_imports` does not yet handle meta IR.\
        Specifically:{indentD <| m!"\n".joinSep metas}"
    let importNeeds ← liftCoreM do StanceM.run' (s := s) do
      (← getEnv).toSimultaneousImportNeeds declNeeds
    let reducedImps := (← getEnv).toRawImports <| importNeeds.toNeeds.reduce (← getEnv).mkTransDeps

    let (header, _, log) ← parseCurrentHeader
    if log.hasErrors then
      -- This should be impossible.
      throwError m!"The current imports failed to parse. Errors:\n\
        {m!"\n".joinSep <| log.toList.map (·.data)}"
    let sourceImps := headerToImportRefsWithWhitespace header

    let some (msg, errs) ← liftCoreM <| Import.mkImportSuggestionMessage tk reducedImps sourceImps
      | logInfo m!"Imports are minimal."
    let formattingChangeAtMost := Import.beqUpToOrder (sourceImps.map (·.1.toImport)) reducedImps
    -- TODO: if imports are the same but not normalized, different message
    if errs.isEmpty then
      if formattingChangeAtMost then
        logInfo m!"Imports can be reformatted, but are otherwise minimal:{msg}"
      else
        logWarning m!"Imports can be reduced:{msg}"
    else
      if formattingChangeAtMost then
        logInfo m!"Imports can be reformatted, but are otherwise minimal.\n\n\
          However, some comments could not be carried over. \
          Please review the source comment that will be inserted after the imports.\n\
          {msg}"
      else
        logWarning m!"Imports can be reduced, but some comments could not be carried over. \
          Please review the source comment that will be inserted after the imports.\n\
          {msg}"


-- /--
-- Return the names of the modules in which constants used in the current file were defined,
-- with modules already transitively imported removed.

-- Note that this will *not* account for tactics and syntax used in the file,
-- so the results may not suffice as imports.
-- -/
-- @[deprecated
--   "Use `Environment.mkTransDeps` and `Needs.reduce` to handle imports in the module system"
--   (since := "2026-07-18")]
-- def Lean.Environment.minimalRequiredModules (env : Environment) : Array Name :=
--   let required := env.requiredModules.toArray.erase env.header.mainModule
--   let redundant := findRedundantImports env required
--   required.filter fun n => ¬ redundant.contains n

-- #norm_imports
-- #min_imports

-- run_cmd do
--   let env ← getEnv
--   let mut encountered : Std.HashSet Name := {}
--   let mut outOfOrder : Std.HashMap (Name × Nat) (Array Import) := {}
--   for h : i in 0...env.header.moduleData.size do
--     let { imports .. } := env.header.moduleData[i]
--     let name := env.header.modules[i]!.module
--     let notEncounteredYet := imports.filter (!encountered.contains ·.module)
--     unless notEncounteredYet.isEmpty do
--       outOfOrder := outOfOrder.insert (name, i) notEncounteredYet
--     encountered := encountered.insert name
--   let (eventuallyEncountered, notEncountered) :=
--     outOfOrder.valuesArray.flatten.partition (encountered.contains ·.module)
--   logInfo m!"\n\
--     total := {env.header.moduleData.size}\n\
--     eventuallyEncountered := {eventuallyEncountered.size}\n\
--     notEncountered := {notEncountered.size}\n\
--     {outOfOrder.toArray.qsort (·.1.2 < ·.1.2)}"



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

-- -- deprecated since 2024-07-06
-- elab "#minimize_imports" : command => do
--   logWarning m!"'#minimize_imports' is deprecated: please use '#min_imports'"
--   Elab.Command.elabCommand (← `(command| #min_imports))
