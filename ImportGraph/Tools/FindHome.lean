/-
Copyright (c) 2023 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison, Paul Lezeau
-/
module

public meta import Lean.Elab.Command
public meta import Lean.Widget.UserWidget
public meta import ImportGraph.Imports.RequiredModules
public meta import ImportGraph.Imports.ImportGraph
public meta import ImportGraph.Graph.TransitiveClosure
meta import all Lean.ExtraModUses
public meta import Lake.CLI.Shake
public meta import ImportGraph.Lean.Environment
import all Lake.CLI.Shake
import all Lean.Elab.Command
import all ImportGraph.Shake.Basic
import all ImportGraph.Shake.Algebra
import all ImportGraph.Shake.DeclNeeds
import all ImportGraph.Shake.EnvExtension
import all ImportGraph.Shake.Precedes


open Lean Lake Shake

/-
# New design

We have some functionality we need.

- decl → visibility → needed import set
- union: import sets → union
- minimize: full import set → minimal direct imports
- import set → meet


thinking a bit: we could track not only which imports are needed, but why. Which declarations are needed from those modules? This is harder.

-/

meta section

/--
This declaration exists in `Batteries`, but we don't want to make `ImportGraph` depend on batteries. We therefore just bear the duplication cost and make this private (and primed, in case someone `imports all`).
-/
private protected def Lean.Position.getDeclsAfter' (env : Environment) (pos : Position)
    (asyncMode := EnvExtension.AsyncMode.local) : Array Name :=
  declRangeExt.getState env asyncMode |>.foldl (init := #[])
    fun acc name { selectionRange .. } =>
      if selectionRange.pos.lt pos then acc else acc.push name

/--
Likewise
-/
@[inline] private protected def _root_.String.Pos.Raw.getDeclsAfter' (env : Environment) (map : FileMap)
    (pos : String.Pos.Raw) (asyncMode := EnvExtension.AsyncMode.local) : Array Name :=
  map.toPosition pos |>.getDeclsAfter' env asyncMode


/-
#min_imports as widget that waits for everything by adding a linter that holds a handle to a promise, which is resolved in the infoview? Is that possible?

Also something that just minimizes your existing imports into something canonical.

Should respect shake directives.
-/

namespace Lake.Shake
/-
`#find_home` now just needs
- turn `Needs` into surface imports (easy)
- meet operation on `Needs`. Might need transitive deps after all.
-/




elab "#trans_deps" : command => do
  let { transDeps .. } := initStateFromEnv (← getEnv)
  let mut isReflexive := #[]
  let mut composed := #[]
  for h : i in 0...transDeps.size do
    if transDeps[i].has .pub i then
      isReflexive := isReflexive.push i
    for k in NeedsKind.all do
      composed := composed.push (i, k, ((Needs.mapComposeSingle transDeps i k).has k i))
  let env ← getEnv
  logInfo m!"reflexives: {isReflexive}\ncomposed: {composed}"

def _root_.Lean.Environment.transImps (env : Environment) (transDeps : Array Needs) : Needs := Id.run do
  let mut transImps := .empty
  for imp in env.header.imports do
    let i := env.getModuleIdx! imp.module
    transImps := addTransitiveImps transImps imp i transDeps[i]!
  return transImps

-- TODO: `#min_imports!` needs to consider extraRevModUse. So does

open Elab Command in
elab "#min_imports" : command => do
  let { transDeps .. } := initStateFromEnv (← getEnv)
  let transImps := (← getEnv).transImps transDeps
  let mut newImports := transImps.reduce transDeps |>.toImports (← getEnv) |>.filter
    fun { module .. } => !(`Init).isPrefixOf module
  for imp in (← getEnv).header.imports do
    if imp.importAll then
      if let some ⟨idx,_⟩ := newImports.findFinIdx? (fun { module, isMeta, .. } =>
          module = imp.module && isMeta = imp.isMeta)
      then
        newImports := newImports.set idx imp
      else
        newImports := newImports.push imp


  -- TODO: postprocessing step that adds back in import all's in place of imports where relevant
  -- logInfo m!"{transImps.toMessageData (← getEnv)}"
  logInfo m!"{newImports}"

def addCurrentExtraModUses (env : Environment) (needs : Needs) : Needs := Id.run do
  let mut needs := needs
  for use in getExtraModUsesState env |>.1 do
    needs := needs.union { use with } {env.getModuleIdx! use.module}
  return needs


open Elab Command
/-- Note: does **not** capture extra rev mod uses influencing the file as a whole. -/
def withElabCommandCapturingNeeds (cmd : Syntax.Command)
    (f : Needs → DeclNeeds → CommandElabM β) : CommandElabM β := do
  withFreshModRecords do
    let oldEnv ← getEnv
    elabCommand cmd
    recordUsedSyntaxKinds cmd
    let decls := cmd.raw.getPos?.get!.getDeclsAfter' (← getEnv) (← getFileMap)
    let mut needs := .empty
    let mut declNeeds := {}
    for decl in decls do
      (needs, declNeeds) := calcDeclNeeds decl (← getEnv) needs declNeeds
    let env ← getEnv
    -- Not great tbh.
    (needs, declNeeds) := env.constants.foldStage2 (s := (needs, declNeeds))
      fun acc@(needs, declNeeds) decl _ =>
        if oldEnv.contains decl then acc else calcDeclNeeds decl env needs declNeeds
    needs := addCurrentExtraModUses env needs
    f needs declNeeds

def

def addExtraRevModUses (env : Environment) (needs : Needs) : Needs := Id.run do
  let mut needs := needs
  for entry in isExtraRevModUseExt.toEnvExtension.getState env |>.importedEntries do
    unless entry.isEmpty do
      needs := -- need to union it with the way the modules is imported now




-- One version that does this; another version that minimizes it on your actual file, with some hackery perhaps to ensure it's at the end.
-- Ideally a widget with a promise that gets filled in by a linter at the end?
-- Or not a promise, because that might not be editable. Just a ref that gets updated, maybe? Plus a ringing of a bell to update the widget...
#min_imports
-- Also, try-this for replacing imports and such. Should `#min_imports` just be a lightbulb?



def elabCommandCapturingDeps

#trans_deps
open Elab Command in
elab "#show_imports" ppLine cmd:command : command => do
  let { transDeps .. } := initStateFromEnv (← getEnv)
  let needs ← withFreshModRecords do
    elabCommand cmd
    recordUsedSyntaxKinds cmd
    let indirect := getIndirectModUsesState (← getEnv)
    let (extras, _) := getExtraModUsesState (← getEnv)
    let decls := cmd.raw.getPos?.get!.getDeclsAfter' (← getEnv) (← getFileMap)
    let mut needs := .empty
    let mut declNeeds := {}
    for decl in decls do
      (needs, declNeeds) := calcDeclNeeds decl (← getEnv) needs declNeeds
    pure (needs, declNeeds, indirect, extras)
  logInfo m!"{needs.1.toMessageData (← getEnv)}{needs.2.2}\n\n\n\
    {transDeps[3]!.toMessageData (← getEnv)}\n\
    {needs.1.reduce transDeps |>.toMessageData (← getEnv)}"


#show_imports
/--
Find locations as high as possible in the import hierarchy
where the named declaration could live.
-/
def Lean.Name.findHome (n : Name) (env : Option Environment) : CoreM NameSet := do
  let current? := match env with | some env => env.header.mainModule | _ => default
  let required := (← n.requiredModules).toArray.erase current?
  let imports := (← getEnv).importGraph.transitiveClosure
  let mut candidates : NameSet := {}
  for (n, i) in imports do
    if required.all fun r => n == r || i.contains r then
      candidates := candidates.insert n
  for c in candidates do
    for i in candidates do
      if imports.find? i |>.getD {} |>.contains c then
        candidates := candidates.erase i
  return candidates

#check Environment.getModuleIdx?

def fooooo := Name.requiredModules

open Elab Command

meta def fooLinter : Linter where
  name := `foo
  run _ := do
    let env ← getEnv
    let ind := indirectModUseExt.getState (← getEnv) |>.toArray.map fun (a, b) => (a, b.map (env.header.moduleNames[·]!))
    let extra := extraModUses.getState (← getEnv) |>.toList
    -- logInfo m!"{ind}"
    logInfo m!"{repr extra}"
    -- let r := isExtraRevModUseExt.getState (← getEnv)

-- #check record

#check initStateFromEnv

run_cmd do
  lintersRef.modify fun ls => ls.filter (·.name != `foo)
  -- addLinter fooLinter

-- run_cmd do
--   let env ← getEnv
--   let ind := indirectModUseExt.getState (← getEnv) |>.toArray.map fun (a, b) => (a, b.map (env.header.moduleNames[·]!))
--   let extra := extraModUses.getState (← getEnv) |>.toList
--   -- logInfo m!"{ind}"
--   let r := isExtraRevModUseExt.getState (← getEnv)
--   logInfo m!"{repr extra}"


open Server in
/-- Tries to resolve the module `modName` to a source file URI.
This has to be done in the Lean server
since the `Environment` does not keep track of source URIs. -/
@[server_rpc_method]
def getModuleUri (modName : Name) : RequestM (RequestTask Lsp.DocumentUri) :=
  RequestM.asTask do
    let some uri ← documentUriFromModule? modName
      | throw $ RequestError.invalidParams s!"couldn't find URI for module '{modName}'"
    return uri

structure GoToModuleLinkProps where
  modName : Name
  deriving Server.RpcEncodable

/-- When clicked, this widget component jumps to the source of the module `modName`,
assuming a source URI can be found for the module. -/
@[widget_module]
def GoToModuleLink : Widget.Module where
  javascript := "
    import * as React from 'react'
    import { EditorContext, useRpcSession } from '@leanprover/infoview'

    export default function(props) {
      const ec = React.useContext(EditorContext)
      const rs = useRpcSession()
      return React.createElement('a',
        {
          className: 'link pointer dim',
          onClick: async () => {
            try {
              const uri = await rs.call('getModuleUri', props.modName)
              ec.revealPosition({ uri, line: 0, character: 0 })
            } catch {}
          }
        },
        props.modName)
    }
  "

open Elab Command in
/--
Find locations as high as possible in the import hierarchy
where the named declaration could live.
Using `#find_home!` will forcefully remove the current file.
Note that this works best if used in a file with `import Mathlib`.

The current file could still be the only suggestion, even using `#find_home! lemma`.
The reason is that `#find_home!` scans the import graph below the current file,
selects all the files containing declarations appearing in `lemma`, excluding
the current file itself and looks for all least upper bounds of such files.

For a simple example, if `lemma` is in a file importing only `A.lean` and `B.lean` and
uses one lemma from each, then `#find_home! lemma` returns the current file.
-/
elab "#find_home" bang:"!"? n:ident : command => do
  let stx ← getRef
  let mut homes : Array MessageData := #[]
  let n ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo n
  let env? ← bang.mapM fun _ => getEnv
  for modName in (← Elab.Command.liftCoreM do n.findHome env?) do
    let p : GoToModuleLinkProps := { modName }
    homes := homes.push $ .ofWidget
      (← liftCoreM $ Widget.WidgetInstance.ofHash
        GoToModuleLink.javascriptHash $
        Server.RpcEncodable.rpcEncode p)
      (toString modName)
  logInfoAt stx[0] m!"{homes}"
