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
import all Lake.CLI.Shake

open Lean Lake Shake

/-
# New design

We have some functionality we need.

- decl → visibility → needed import set
- union: import sets → union
- minimize: full import set → minimal direct imports
- import set → meet

-/

/-- Debugging: list every `(j, k)` entry in `needs` as a literal `Import`, with no deduplication
across kinds. `modNames` maps `ModuleIdx` to `Name` (e.g. `State.modNames`). -/
meta def Lake.Shake.Needs.toImports (env : Environment) (needs : Needs) : Array Import := Id.run do
  let mut out := #[]
  for k in NeedsKind.all do
    let s := needs.get k
    for j in 0...env.allImportedModuleNames.size do
      if s.has j then
        out := out.push
          { module := env.allImportedModuleNames[j]!, isExported := k.isExported, isMeta := k.isMeta, importAll := false }
  return out

meta instance : ToMessageData NeedsKind where
  toMessageData
    | .pub => "public"
    | .metaPub => "public meta"
    | .priv => "private"
    | .metaPriv => "private meta"


/-- Debugging: list every `(j, k)` entry in `needs` as a literal `Import`, with no deduplication
across kinds. `modNames` maps `ModuleIdx` to `Name` (e.g. `State.modNames`). -/
meta def Lake.Shake.Needs.toMessageData (env : Environment) (needs : Needs)
    (filter : Name → NeedsKind → Bool := fun _ _ => true) : MessageData := Id.run do
  let mut msg := m!""
  for k in NeedsKind.all do
    msg := msg ++ m!"{k}:\n"
    let s := needs.get k
    for j in 0...env.allImportedModuleNames.size do
      if s.has j && filter env.allImportedModuleNames[j]! k then
        msg := msg ++ m!"  {toString env.allImportedModuleNames[j]!}\n"
  return msg

meta def Lean.Environment.getModuleIdx! (env : Environment) (moduleName : Name) : ModuleIdx :=
  env.getModuleIdx? moduleName |>.get!

elab "#foo" : command => do
  let s := initStateFromEnv (← getEnv)
  logInfo m!"{s.transDeps[(← getEnv).getModuleIdx! `ImportGraph.Graph.TransitiveClosure]!
    |>.toMessageData (← getEnv) fun n _ => !(`Init).isPrefixOf n}"

#foo

/--
Given an `Expr` reference, returns the declaration name that should be considered the reference, if
any, but from the environment directly.
-/
def Lean.Environment.getDepConstName? (ref : Name) (env : Environment) : Option Name := do
  -- Ignore references to reserved names, they can be re-generated in-place
  guard <| !isReservedName env ref
  -- `_simp_...` constants are similar, use base decl instead
  return if ref.isStr && ref.getString!.startsWith "_simp_" then
    ref.getPrefix
  else
    ref

deriving instance Ord for NeedsKind
-- TODO: custom structure
/-- A set of `NeedsKind`s. -/
abbrev NeedsKindSet := Std.TreeSet NeedsKind

/-- States that the (local) declarations `foo` are needed at their assigned sets of `NeedsKind`s. For instance, if `foo` is used in an exporting position, such as a public def's type, it will acquire `foo ↦ {{ isExported := true, isMeta := false }}`. -/
-- We might be able to simplify this to not be a set.
abbrev DeclNeeds := NameMap NeedsKindSet

nonrec def DeclNeeds.insert (k : NeedsKind) (decl : Name) (needs : DeclNeeds) :=
  needs.alter decl fun
    | none => some {k}
    | some ks => ks.insert k

/--
Calculates the needs for a given module `mod` from constants and recorded extra uses.

Does not account for `extraModUses`, since these are not decl-linked per se.

Collects needed declarations from the current module in `DeclNeeds`, together with the visibiility they're needed at.
-/
def calcDeclNeeds? (decl : Name) (env : Environment)
    (needs : Needs := .empty) (extraDecls : DeclNeeds := {}) : Option (Needs × DeclNeeds) :=
  Id.run do
  let mut needs := needs
  let mut extraDecls := extraDecls
  let indirectModUses := indirectModUseExt.getState env
  let some ci := env.find? decl | return none
  -- Added guard for cases like `structure` that are still exported even if private
  let pubCI? := guard (!isPrivateName ci.name) *> (env.setExporting true).find? ci.name
  let k := { isExported := pubCI?.isSome, isMeta := isDeclMeta' env ci.name }
  (needs, extraDecls) := visitExpr indirectModUses k ci.type needs extraDecls
  if let some e := ci.value? (allowOpaque := true) then
    -- type and value has identical visibility under `meta`
    let k := if k.isMeta then k else
      if pubCI?.any (·.hasValue (allowOpaque := true)) then .pub else .priv
    (needs, extraDecls) := visitExpr indirectModUses k e needs extraDecls

  return (needs, extraDecls)
where
  /-- Accumulate the results from expression `e` into `deps`. -/
  visitExpr (indirectModUses : Std.HashMap Name (Array ModuleIdx)) (k : NeedsKind) (e : Expr)
      (deps : Needs) (extras : DeclNeeds) : (Needs × DeclNeeds) :=
    Lean.Expr.foldConsts e (deps, extras) fun c (deps, extras) => Id.run do
      let mut deps := deps
      let mut extras := extras
      if let some c := env.getDepConstName? c then
        if let some (j : Nat) := env.getModuleIdxFor? c then
          let k := { k with isMeta := k.isMeta && !isDeclMeta' env c }
          deps := deps.union k {j}
          for (indMod : Nat) in indirectModUses[c]?.getD #[] do
            /- The commented-out gate is only relevant if we're downstream of the imports we want to minimize, and may know about more indirectModUses than were known about now. -/
            -- if s.transDeps[i]!.has k indMod then
              deps := deps.union k {indMod}
        else
          -- `c` is from the same module--we need it at the given `k`
          extras := extras.insert k c
      return (deps, extras)

def

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
