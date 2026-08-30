/-
Copyright (c) 2026 Thomas R. Murrills. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas R. Murrills
-/
module

public import ImportGraph.Shake.Algebra
public import ImportGraph.Shake.DeclNeeds
public import ImportGraph.WorkspaceModel.Build
public import ImportGraph.WorkspaceModel.Model
public import Lean.Elab.Command
import ImportGraph.Shake.EnvExtension

public section

open ImportGraph Shake Lean

namespace ImportGraph

/-- Assuming that the indices in `Needs` correspond to module indices in the provided environment, record an `Import` for each set index in `Needs` in some order. -/
def WorkspaceModel.toRawImports (w : WorkspaceModel) (n : Needs) (skipInit := true) :
  Array Import := Id.run do
  let mut out := #[]
  for (k, i) in n.highToLow do
    let module := w.getMod! i |>.name
    if skipInit && (`Init).isPrefixOf module then continue
    out := out.push { k with module, importAll := k.isAll }
  return out

namespace Shake

-- TODO: make this take in a monadic interface for the module index, so that we can use it both for an environment and more generally
/-- Collapse the `ImportNeeds` of all declarations in `DeclNeeds`. This is incorrect for splitting up declarations, but adequate for moving them to a single place.  -/
def DeclNeeds.toSimultaneousImportNeeds
    (w : WorkspaceModel)
    (declNeeds : DeclNeeds)
    (declImportNeeds : ImportNeeds := {}) :
    StanceM ImportNeeds := do
  let mut declImportNeeds := declImportNeeds
  for (decl, declNeeds) in declNeeds do
    let some stance ← getStance? decl | continue
    for (modName, usedDecls) in declNeeds.fixedDecls do
      let some modIdx := w.idxOfMod[modName]? | continue
      for (usedDecl, ks) in usedDecls do
        let some usedStance ← getStance? usedDecl | continue
        let mut usedKs : DeclDeclNeedsKindSet := {}
        for k in ks do
          if usedKs.contains k then continue
          usedKs := usedKs.insert k
          if let .comptime <| .indirect _ mods := k then
            for modName in mods do
              let some modIdx := w.idxOfMod[modName]? | continue
              declImportNeeds := declImportNeeds.union
                { isExported := false, isMeta := false, allowMeta := true } {modIdx}
          let k := stance.toImportNeedsKind k usedStance
          declImportNeeds := declImportNeeds.union k {modIdx}
  return declImportNeeds

/-- Like `DeclNeeds.toSimultaneousImportNeeds`, but uses the environment's notion of `ModuleIdx` instead of a workspace model's. -/
def Lean.Environment.toSimultaneousImportNeeds
    (env : Environment)
    (declNeeds : DeclNeeds)
    (declImportNeeds : ImportNeeds := {}) :
    StanceM ImportNeeds := do
  let mut declImportNeeds := declImportNeeds
  for (decl, declNeeds) in declNeeds do
    withTraceNode `ImportGraph.Shake.ImportNeeds
      (fun _ => return m!"`{.ofConstName decl}`") do←
    let some stance ← getStance? decl | continue
    for (modName, usedDecls) in declNeeds.fixedDecls do
      withTraceNode `ImportGraph.Shake.ImportNeeds (collapsed := false)
        (fun _ => return m!"Uses module `{modName}`") do←
      let some modIdx := env.getModuleIdx? modName | continue
      for (usedDecl, ks) in usedDecls do
        withTraceNode `ImportGraph.Shake.ImportNeeds
          (fun _ => return m!"Uses decl `{.ofConstName usedDecl}`") do←
        let some usedStance ← getStance? usedDecl | continue
        let mut usedKs : DeclDeclNeedsKindSet := {}
        for k in ks do
          trace[ImportGraph.Shake.ImportNeeds] "{k.pretty}"
          if usedKs.contains k then continue
          usedKs := usedKs.insert k
          if let .comptime <| .indirect _ mods := k then
            for modName in mods do
              let some modIdx := env.getModuleIdx? modName | continue
              trace[ImportGraph.Shake.ImportNeeds] "indirect usage of `{modName}`"
              declImportNeeds := declImportNeeds.union
                { isExported := false, isMeta := false, allowMeta := true } {modIdx}
          let k := stance.toImportNeedsKind k usedStance
          declImportNeeds := declImportNeeds.union k {modIdx}
  return declImportNeeds

-- def addCurrentExtraModUses (env : Environment) (needs : Needs) : Needs := Id.run do
--   let mut needs := needs
--   for use in getExtraModUsesState env |>.1 do
--     needs := needs.union { use with } {env.getModuleIdx! use.module}
--   return needs

-- TODO(NOW): add tracing to other version
-- TODO(NOW): unify tracing names?

open Lean Elab Command in
/-- Note: does **not** capture extra rev mod uses influencing the file as a whole. -/
def withElabCommandCapturingNeeds (cmd : Syntax.Command) :
    CommandElabM (DeclNeeds × Array Name) := do
  withFreshModRecords do
    let oldEnv ← getEnv
    elabCommand cmd
    let env ← getEnv
    let newDecls := env.constants.foldStage2 (s := #[]) fun acc decl _ =>
      if oldEnv.contains decl then acc else acc.push decl
    let mut declNeeds := {}
    let mut autoDecls := #[] -- Save auto decls, and ensure we found them
    -- TODO-TAG: auto decl handling
    for new in newDecls do
      if isDeclNeedsAutoDecl env new then
        autoDecls := autoDecls.push new
      else
        declNeeds := calcDeclConstInfoNeeds new env declNeeds
    for autoDecl in autoDecls do
      -- TODO: this should recurse into autodecls of autodecls. Not entirely happy with handling
      unless declNeeds.contains autoDecl do
        declNeeds := calcDeclConstInfoNeeds autoDecl env declNeeds
    -- TODO-TAG: extra mod uses. Should be at the command level and decls organized by command
    let extraModUses := getExtraModUsesState env |>.1
    for new in newDecls do
      declNeeds := declNeeds.insertExtraModUsesFor new extraModUses
    -- TODO: restore
    declNeeds ← declNeeds.calcSyntaxNeeds env newDecls cmd
    declNeeds ← liftCoreM <| declNeeds.calcIRNeeds.run'
    return (declNeeds, newDecls)

initialize registerTraceClass `ImportGraph.Shake.ImportNeeds
