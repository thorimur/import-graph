/-
Copyright (c) 2023 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison, Paul Lezeau
-/
module

public meta import Lean.Elab.Command
public meta import Lean.Widget.UserWidget
public meta import ImportGraph.Imports.ImportGraph
public meta import ImportGraph.Imports.Pretty
public meta import ImportGraph.Lean.MessageData
public meta import ImportGraph.Shake.Workspace
public meta import Lean.Meta.Tactic.TryThis
public import ImportGraph.Widget.Collapsible
public import ImportGraph.Widget.Copy
public import ImportGraph.Widget.GoToModule
import Lean
import all Lean

public meta section

open Lean

namespace ImportGraph

syntax diffAbsolute :=
  (&"from" ppLine sepByIndentSemicolon(Parser.Module.import))?
  &"to" ppLine sepByIndentSemicolon(Parser.Module.import)

/-- Removes an import among the current imports to this file. -/
syntax importMinus := &"-"
syntax importPlus := &"+"

syntax diffCurrentItem :=
  withPosition(importMinus (colGt Parser.Module.import)?)
    <|> withPosition(importPlus colGt Parser.Module.import)

syntax diffCurrent := sepByIndentSemicolon(diffCurrentItem)

syntax "#import_diff " (diffAbsolute <|> diffCurrent) : command

open Shake Elab Command

#check Shake.NeedsKind

def WorkspaceModel.modInfoOfImport (w : WorkspaceModel) :
    TSyntax ``Parser.Module.import → CommandElabM (NeedsKind × Name × ModIdx)
  | `(Parser.Module.import|
      $[public%$pubTk]? $[meta%$metaTk]? import $[all%$allTk]? $mod) => do
    if h : pubTk.isSome && allTk.isSome then
      throwErrorAt (mkNullNode #[pubTk.get!, allTk.get!]) m!"Cannot use `public` with `all`."
    else
      if mod.getId.isAnonymous then
        throwUnsupportedSyntax
      let some idx := w.getModIdx? mod.getId
        | throwErrorAt mod "Could not find module `{mod}` in the workspace."
      let k : NeedsKind :=
        { isExported := pubTk.isSome, isMeta := metaTk.isSome, isAll := allTk.isSome }
      pure (k, mod.getId, idx)
  | _ => throwUnsupportedSyntax

def WorkspaceModel.modInfoOfSyntax (w : WorkspaceModel) :
    TSyntax ``Parser.Module.import → CommandElabM (NeedsKind × Name × ModIdx)
  | `(Parser.Module.import|
      $[public%$pubTk]? $[meta%$metaTk]? import $[all%$allTk]? $mod) => do
    if h : pubTk.isSome && allTk.isSome then
      throwErrorAt (mkNullNode #[pubTk.get!, allTk.get!]) m!"Cannot use `public` with `all`."
    else
      if mod.getId.isAnonymous then
        throwUnsupportedSyntax
      let some idx := w.getModIdx? mod.getId
        | throwErrorAt mod "Could not find module `{mod}` in the workspace."
      let k : NeedsKind :=
        { isExported := pubTk.isSome, isMeta := metaTk.isSome, isAll := allTk.isSome }
      pure (k, mod.getId, idx)
  | _ => throwUnsupportedSyntax

def WorkspaceModel.irNeeds (w : WorkspaceModel) (n : Needs) : Bitset := Id.run do
  let n := w⟦n.linearize⟧
  let irTrans := n.get .metaPriv ∪ n.get .metaPub
  -- not perfect `all` handling but uncommon anyway
  let mut irs := irTrans ∪ n.get .privOfPriv ∪ n.get .metaPrivOfPriv
  for idx in irTrans.highToLow do
    irs := irs ∪ w.mods[idx]!.prevs
  return irs

@[inline] def String.padRightTo (s : String) (n : Nat) (c : Char := ' ') :=
  s.pushn c (n - s.length)

@[inline] def String.padLeftTo (s : String) (n : Nat) (c : Char := ' ') :=
  "".pushn c (n - s.length) ++ s

open ImportGraph
/--
Given a matrix (row-major) of strings, arranges them in tabular form.
Single space as column separator.

Assumes the array is non-empty and all rows are the same size (panics otherwise).
-/
def formatTable! (rows : Array (Array String)) : String := Id.run do
  let mut colWidths := rows[0]!.map (·.length)
  for h : i in 1...rows.size do
    colWidths := colWidths.zipWith (max · ·.length) rows[i]
  let mut table := ""
  for h : rowIdx in 0...rows.size do
    for h : i in 0...rows[rowIdx].size do
      unless i == 0 do
        table := table.push ' '
      table := table ++ rows[rowIdx][i].padRightTo colWidths[i]!
    unless rowIdx + 1 == rows.size do
      table := table.push '\n'
  return table

namespace ImportDiff

structure Tally where
  plus   : Nat := 0
  minus  : Nat := 0
  shared : Nat := 0

namespace Tally

def toString (t : Tally) : String := s!"+{t.plus} -{t.minus} ={t.shared}"
def toStrings (header : String) (t : Tally) : Array String :=
  #[header, s!"+{t.plus}", s!"-{t.minus}", s!"={t.shared}"]

open Meta.Tactic.TryThis in
elab_rules : command
| `(#import_diff%$tk $spec) => do
  let w ← getWorkspaceModel (extraMods := #[← getMainModule])
  if w.hasErrors then
    logErrorAt tk m!"Errors when building the import hierarchy:\n\n\
      {m!"\n\n".joinSep (w.errors.map toMessageData |>.toList)}"
  let currentModInfo : CommandElabM (Array <| NeedsKind × Name × ModIdx) := do
    (← getEnv).header.imports.filterMapM fun imp => do
      if (`Init).isPrefixOf imp.module then return none
      let k : NeedsKind := .ofImport imp
      let some idx := w.getModIdx? imp.module
        | throwError "Could not find already-imported module `{imp.module}` in the workspace."
      pure (k, imp.module, idx)
  let (initMods, finalMods) ← match spec with
    | `(diffAbsolute| $[from $initMods*]? to $finalMods*) =>
      let inits ← if let some initMods := initMods then
          initMods.getElems.mapM w.modInfoOfSyntax
        else currentModInfo
      let finals ← finalMods.getElems.mapM w.modInfoOfSyntax
      pure (inits, finals)
    | `(diffCurrent| $items:diffCurrentItem*) =>
      let inits ← currentModInfo
      let mut removed := #[]
      let mut added := #[]
      for item in items.getElems do
        match item with
        | `(diffCurrentItem| +$imp:import) => do
          let info ← w.modInfoOfSyntax imp
          if removed.contains info then
            throwErrorAt item "The import `{imp}` has also been removed from the set."
          added := added.push info
        | `(diffCurrentItem| -$imp:import) => do
          let info ← w.modInfoOfSyntax imp
          -- Don't error if we've already erased it (e.g. the user wrote it twice)
          unless inits.contains info do
            throwErrorAt item "The current imports do not include `{imp}`."
          if added.contains info then
            throwErrorAt item "The import `{imp}` has also been added to the set."
          removed := removed.push info
        | `(diffCurrentItem| -%$dangling) =>
          let removable := (← getEnv).header.imports.filter fun imp =>
            !((`Init).isPrefixOf imp.module)
              && !removed.any fun (k, name, _) => imp == k.toImport name
          if removable.isEmpty then
            logWarningAt dangling m!"No imports can be removed."
          else
            let suggestions : Array Suggestion := removable.map (s!"-{·}")
            liftCoreM <| addSuggestions dangling suggestions
              (header := "The following imports in this file may be deleted:")
              (codeActionPrefix? := "")
              (diffGranularity := .char)
          return
        | _ => throwUnsupportedSyntax
      let finals := inits.filter (!removed.contains ·) ++ added
      pure (inits, finals)
    | _ => throwUnsupportedSyntax

  let transNeedsOfMods (mods : Array (NeedsKind × Name × ModIdx)) : Needs := Id.run do
    let mut needs : Needs := ∅
    for (k, _, idx) in mods do
      needs := needs.union k {idx}
    -- Include `Init` (as non-`prelude` files do) and then transitively close,
    -- to avoid reporting weird (and untrue) `Init` differences
    pure w⟦w.implicitInitNeeds needs |>.linearize⟧
  let initNeeds := transNeedsOfMods initMods
  let finalNeeds := transNeedsOfMods finalMods
  let plus := (finalNeeds \ initNeeds).antilinearize
  let minus := (initNeeds \ finalNeeds).antilinearize
  let shared := (finalNeeds.map₂ initNeeds (· ∩ ·) \ w.transInitNeeds).antilinearize
  -- let splitImps (needs : Needs) :=
  --   let reducedImps := w.toRawImports <| needs.reduce w
  --   let nonReducedImps := w.toRawImports needs |>.filter (!reducedImps.contains ·)
  --   (reducedImps, nonReducedImps)
  -- let plusImps := splitImps plus
  -- let minusImps := splitImps minus
  -- let sharedImps := splitImps shared
  let initIrNeeds := w.irNeeds initNeeds
  let finalIrNeeds := w.irNeeds finalNeeds
  let irPlus := finalIrNeeds \ initIrNeeds
  let irMinus := initIrNeeds \ finalIrNeeds
  let irShared := (finalIrNeeds ∩ initIrNeeds) \ w.irNeeds w.transInitNeeds
  let irTally := { plus := irPlus.size, minus := irMinus.size, shared := irShared.size : Tally }
  let irLabel := "ir"

  let initDepth := initMods.map (w.mods[·.2.2]!.depth) |>.max?.getD 0
  let finalDepth := finalMods.map (w.mods[·.2.2]!.depth) |>.max?.getD 0
  let depthMsgs :=
    #["depth", s!"{finalDepth}", s!"{initDepth}", s!"(Δ = {(finalDepth : Int) - (initDepth : Int)})"]
  -- TODO: prevs?
  let initPrevs := initMods.foldl (init := ∅) (fun acc (_,_,idx) => acc ∪ w.mods[idx]!.prevs)
  let finalPrevs := finalMods.foldl (init := ∅) (fun acc (_,_,idx) => acc ∪ w.mods[idx]!.prevs)
  let prevTally := { plus := (finalPrevs \ initPrevs).size, minus := (initPrevs \ finalPrevs).size, shared := (initPrevs ∩ finalPrevs).size : Tally }
  let prevMsgs :=
    prevTally.toStrings "prevs"

  let tallies := NeedsKind.all.map fun k => (k, {
    plus := plus.get k |>.size
    minus := minus.get k |>.size
    shared := shared.get k |>.size : Tally})
  let tableMsgs := (tallies.map fun (k, t) => t.toStrings s!"{k}")
    |>.push (irTally.toStrings irLabel) |>.push prevMsgs |>.push depthMsgs
  let header := match !plus.isEmpty, !minus.isEmpty with
    | true,  true  => s!""
    | true,  false => s!"Imports strictly increased.\n\n"
    | false, true  => s!"Imports strictly decreased.\n\n"
    | false, false => s!"No changes to imports.\n\n"
  logInfo <| s!"{header}{formatTable! tableMsgs}"
  -- TODO: show each import. Should exclude "obvious" user-specified imports, right? No, no, the entire point is to see the other ones. So we should show the user-specified ones but just annotate.
  -- TODO: should also allow removing imports that "can't" really be removed, and just say that this is virtual?
  -- TODO: With no arguments, show current stats in a nicer table? Maybe with totals?
  -- TODO: Hmm, show totals somehow anyway. Total public increase, total private increase (including public/private only?)⋯
  -- Equals is confusing
  -- table would be good

















#import_diff









#exit

/-- `#import_diff foo bar ...` computes the new transitive imports that are added to a given file when
modules `foo, bar, ...` are added to the set of imports of the file. More precisely, it computes the
import diff between when `foo, bar, ...` are added to the imports and when `foo, bar, ...` are removed
from the imports.

Note: the command also works when some of the modules passed as arguments are already present in the file's
imports. -/
elab "#import_diff" n:ident* : command => do
  let name_arr : Array Name := n.map (·.getId)
  let sp ← searchPathRef.get
  -- First, make sure the files exist.
  for name in name_arr do
    if (← sp.findWithExt "olean" name).isSome then continue
    throwError m!"File {name} cannot be found."
  let env ← getEnv
  -- Next, check for redundancies:
  let current_all_imports := env.allImportedModuleNames
  let redundancies := name_arr.filter current_all_imports.contains
  unless redundancies.isEmpty do
    let out := "\n".intercalate <| redundancies.map Name.toString |>.qsort (· < ·) |>.toList
    Lean.logInfo <| m!"The following are already imported (possibly transitively):\n{out}"
  -- Now compute the import diffs.
  let current_imports := env.imports
  let reduced_imports := env.imports.filter (!name_arr.contains ·.module)
  let extended_imports := current_imports ++ (name_arr.map ({ module := · }))
  let reduced_all_imports := (← Lean.importModules reduced_imports {}).allImportedModuleNames
  let extended_all_imports := (← Lean.importModules extended_imports {}).allImportedModuleNames
  let import_diff := extended_all_imports.filter (· ∉ reduced_all_imports)
  let out := "\n".intercalate <| import_diff.map Name.toString |>.qsort (· < ·) |>.toList
  Lean.logInfo s!"Found {import_diff.size} additional imports:\n{out}"
