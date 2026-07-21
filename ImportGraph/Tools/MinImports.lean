/-
Copyright (c) 2023 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison, Paul Lezeau
-/
module

public meta import ImportGraph.Imports.Pretty
public meta import ImportGraph.Imports.Redundant
public meta import ImportGraph.Imports.RequiredModules
public meta import ImportGraph.Lean.Environment
public meta import ImportGraph.Imports.FromSource
public meta import ImportGraph.Lean.Syntax
public meta import ImportGraph.Shake.Algebra
public meta import ImportGraph.Shake.DeclNeeds
public meta import ImportGraph.Shake.Environment
public meta import ImportGraph.Tools.NeedsGrid
public import ImportGraph.Util.RunLater

import Lean
import ImportGraph.Lean.Environment
import ImportGraph.Shake.Algebra
import ImportGraph.Shake.Basic
import Lake.CLI.Shake

import all ImportGraph.Shake.Environment
import all ImportGraph.Tools.NeedsGrid
import all ImportGraph.Shake.DeclNeeds
import all Lean.Elab.Command -- for `recordUsedSyntaxKinds`
import all ImportGraph.Shake.EnvExtension

open ImportGraph Lean Elab Command Lake Shake

#check calcDeclNeeds

meta def getModuleNeeds (cmds : Array Syntax) : CommandElabM Needs := do
  for cmd in cmds do
    recordUsedSyntaxKinds cmd
  let mut declNeeds : DeclNeeds := ∅
  for (decl, _) in (← getEnv).constants.map₂ do
    declNeeds := calcDeclNeeds decl (← getEnv) declNeeds
  -- logInfo m!"DeclNeeds: {declNeeds.toArray.map fun (decl, declneed) =>
  --   have fixed : Array (ModuleIdx × NameMap (NeedsKindSet × Bool)) := declneed.fixedDecls.toArray
  --   let fixed := fixed.flatMap fun a : ModuleIdx × NameMap (NeedsKindSet × Bool) => a.2.toArray.map fun a : Name × (NeedsKindSet × Bool) => m!"{MessageData.ofConstName a.1}{a.2.1.toArray}"
  --   m!"{MessageData.ofConstName decl}: {fixed}"}"
  for (decl, need) in declNeeds do
    let env ← getEnv
    logInfo m!"{decl} requires {need.fixedDecls.keysArray.map (env.header.modules[·]!.module)}\n\
      Std.Do.Triple.SpecLemmas: {need.fixedDecls[env.getModuleIdx! `Std.Do.Triple.SpecLemmas]?.map (·.toArray.map fun (a, b) => (MessageData.ofConstName a, b.2))}"
  let mut needs := declNeeds.fullNeeds
  let (modUses, _) := getExtraModUsesState (← getEnv)
  logInfo m!"Extra mod uses: {modUses.map (·.module)}"
  for { module, isExported, isMeta } in modUses do
    let idx := (← getEnv).getModuleIdx! module
    needs := needs.union { isExported, isMeta } {idx}
  -- Note: current indirect mod uses are not relevant, since they are only signals to downstream
  -- modules to import the current module.
  return needs

-- TODO: process shake annotations instead of leaving them in the error.
elab tk:"#min_imports" : command => do
  runLaterWithSyntax (ref? := tk) fun cmds => do
    let needs ← getModuleNeeds cmds
    let needs := needs.reduce (← getEnv).mkTransDeps
    let reducedImps := needs.toRawImports (← getEnv)
    -- TODO: transitive
    let reducedImps := Import.includeAll (← getEnv).header.imports reducedImps

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

-- #min_imports

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
