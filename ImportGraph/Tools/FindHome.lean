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
public meta import ImportGraph.Imports.Pretty
public meta import ImportGraph.Graph.TransitiveClosure
public meta import ImportGraph.Shake.EnvExtension
public meta import ImportGraph.Shake.DeclNeeds
public meta import ImportGraph.Shake.Environment
public meta import ImportGraph.Shake.Algebra
public meta import ImportGraph.Shake.Basic
public meta import ImportGraph.Shake.Coverings
public meta import ImportGraph.Tools.NeedsGrid
public meta import ImportGraph.Util.GoTo
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
import all ImportGraph.Shake.Environment
import all ImportGraph.Shake.Coverings
import all ImportGraph.Tools.NeedsGrid
public meta import ImportGraph.Tools.Collapsible
public meta import ImportGraph.Tools.Copy
meta import all ImportGraph.WorkspaceModel.Build
import all ImportGraph.WorkspaceModel.Build
public meta import ImportGraph.WorkspaceModel.Summary
public meta import ImportGraph.WorkspaceModel.Model
public meta import ImportGraph.WorkspaceModel.Build


open Lean
open Lake hiding logInfo
open Shake

/-
# New design

We have some functionality we need.

- decl → visibility → needed import set
- union: import sets → union
- minimize: full import set → minimal direct imports
- import set → meet


thinking a bit: we could track not only which imports are needed, but why. Which declarations are needed from those modules? This is harder.

## TODO

### Features

- Better handling for recursive declarations.
- Queries. E.g. don't depend on modules in this folder; do export to that module. (Declaration-level queries, too? E.g. make sure `foo` is available? Not too hard.)
- Consider exports, not just imports
- Mutation: suggest adding an import under certain conditions (e.g. a private import that is blindly reachable through the current imports). Requires thinking through what sorts of "edits" to the import hierarchy are permissible or desirable; can hook into queries.
- `#scope` inclusion.
- "Agent mode", which emits simplified textual information instead of fancy UX. And, crucially, which works under `lake build`; see "universal import hierarchy handling"
- Leave behind `relocated_to` commands.
- More rankings

### Fixes

- Universal import hierarchy handling. Need to parse source, possibly load lake workspace; should allow us to work outside of the language server, too.
- Mutual blocks may be tricky. (FOR NOW: test? warning?)
- More explanations

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

-- To get the current

/-
Right now:


- `#show_imports`
- fix prevs
- end-of-file min_imports
-/


-- elab "#trans_deps" : command => do
--   let { transDeps .. } := initStateFromEnv (← getEnv)
--   let mut isReflexive := #[]
--   let mut composed := #[]
--   for h : i in 0...transDeps.size do
--     if transDeps[i].has .pub i then
--       isReflexive := isReflexive.push i
--     for k in NeedsKind.all do
--       composed := composed.push (i, k, ((Needs.mapComposeSingle transDeps i k).has k i))
--   let env ← getEnv
--   logInfo m!"reflexives: {isReflexive}\ncomposed: {composed}"



-- TODO: `#min_imports!` needs to consider extraRevModUse. So does

def addCurrentExtraModUses (env : Environment) (needs : Needs) : Needs := Id.run do
  let mut needs := needs
  for use in getExtraModUsesState env |>.1 do
    needs := needs.union { use with } {env.getModuleIdx! use.module}
  return needs

open Lean Elab Command in
private partial def recordUsedSyntaxKindsWithNew (stx : Syntax) : CommandElabM NameSet := do
  let mut new := {}
  for stx in stx.topDown do
    if let .node _ k .. := stx then
      -- do not record builtin parsers, they do not have to be imported
      if !(← Parser.builtinSyntaxNodeKindSetRef.get).contains k then
        if (← getEnv).isImportedConst k then
          recordExtraModUseFromDecl (isMeta := true) k
        else
          new := new.insert k
  return new

-- TODO:
-- switch argument order
-- include array of new constants?
open Elab Command
/-- Note: does **not** capture extra rev mod uses influencing the file as a whole. -/
def withElabCommandCapturingNeeds (cmd : Syntax.Command)
    (f : Needs → DeclNeeeds → Array Name → CommandElabM β) : CommandElabM β := do
  withFreshModRecords do
    let oldEnv ← getEnv
    elabCommand cmd
    let new ← recordUsedSyntaxKindsWithNew cmd
    let env ← getEnv
    -- let decls := cmd.raw.getPos?.get!.getDeclsAfter' (← getEnv) (← getFileMap)
    let mut declNeeds := new.foldl (init := {}) fun acc decl => calcDeclNeeds decl env acc
    -- for decl in decls do
    --   declNeeds := calcDeclNeeds decl (← getEnv) declNeeds

    -- Not great tbh.
    let mut newDecls := #[]
    (newDecls, declNeeds) := env.constants.foldStage2 (s := (#[], declNeeds))
      fun acc decl _ =>
        if oldEnv.contains decl then acc else (acc.1.push decl, calcDeclNeeds decl env acc.2)
    let extraNeeds := addCurrentExtraModUses env .empty
    f extraNeeds declNeeds newDecls

open Elab Command in
elab "#show_imports" ppLine cmd:command : command => do
  let transDeps := (← getEnv).mkTransDeps
  let (extraNeeds, declNeeds) ← withElabCommandCapturingNeeds cmd
    fun extraNeeds declNeeds _ => return (extraNeeds, declNeeds)
  let needs := extraNeeds ∪ declNeeds.fullNeeds
  let reduced := needs.reduce transDeps |>.toRawImports (← getEnv)
  Lean.logInfo m!"{declNeeds.keysArray.map MessageData.ofConstName}: {ImportGraph.Lean.Import.pretty reduced}"

def _root_.Lean.MessageData.bulletedList (msgs : List MessageData) (forceList := true) :
    MessageData := Id.run do
  if let [msg] := msgs then
    unless forceList do return msg
  m!"\n".joinSep (msgs.map (m!"• {.nest 2 ·}"))

/-
- Recursive locating for previous lemmas
  - "all at once" UX
  - local meta (`syntax`/`macro` etc.) dependencies! Not accounted for yet.
  - auxiliary meta dependencies by traversing lemma syntax. `ModuleLinter`.
- In-file location
  - Line number in typical case
  - Top or bottom of file; correct namespaces, scopes, etc.
  - Visibility especially, and be sure to match it
  - RELATED: code action for attaching current visibilities
- Fine-tuning UX
  - Exclude and downrank dependencies on given globs/files
  - Allow certain imports to be added (requires masking `Needs` + recording unmasked version and recomputing dependencies in new file)
- Messages and reporting
  - Should have a dropdown to show what the (minimized) imports of the new file are
  - Possibly depth and size here...also "width"? How would that be computed?
- Testing suite: `lake serve` and in-server only
- (v2) full hierarchy, beyond current imports
  - add import of out-of-slice location to current file

## Concrete tasks

- :check: Link for module + line
- (codicon + effect generic tooling to layer click effects on strings/messagedata?)
- edits in other files
- batch edits (hint revamp?)

- Decide on games and how to display
  - Toggles between games?

- Should `#check` and other term info dives be supported? Maybe instead of environment range nonsense?
- Need to handle autogenerated declarations without ranges correctly.
  - Are parent declarations determinable by some extension or other?

-/


/-
Different ways to filter + rank possible homes
- Exports
- queries
- Which dependencies matter? upstream vs. same-project
  - league (affects: do I move it out of the project or not? Which upstream targets are acceptable?)
- Different games to play for
  - knockout
  - ranking
- mutation!
- How to handhold? Visibility into problem space, but sensible defaults. How to curate?
  - Has to teach user what it can do and why; guidance in defaults
  - Show what axis it's ranked on, why
    - How to show this?
  - what other axes it could be ranked on?
- Explanation why: what imports necessary, what declarations in your project/others it depends on
- upstream togglability

- Audience: ???
  - "new" users who have not thought about this problem, but could be trained by the tool
  - power users

- v0: multiple rankings
  - Recommended:
    - Best overall (all dependencies matter), but league := current project
    - Upstream (all dependencies matter), league := all
  - upstreamability by upstream project (where in upstream it can go in general)
  - league := current project, best by project imports
  - explanations! (why this file, what do your declarations need:
    - explain which declarations need to be moved
    - what imports are necessary

- Then:
  - Get feedback from different users
    - What automations/actions should exist (file modifications, copying, etc.); what's the workflow
    - What information do you want to see
      - How interactive should the display and queries be? Toggle lists? Badges?
    - What suggestions are best

- v1
  - queries/exclusions
  - improve UX with suggestions
  - (if necessary, mutations!)

  - recursive uses of definitions????
  - `#scope` synergy: interaction that actually moves the declarations and leaves behind `relocated_to` commands

- v2 mutations


-/

open ImportGraph

/-
Maybe the league should be the package? hmmm...
-/

-- def displayImport


def _root_.Lean.Lsp.Position.max (pos₁ pos₂ : Lsp.Position) : Lsp.Position :=
  match compare pos₁ pos₂ with
  | .lt => pos₂
  | .gt | .eq => pos₁

local instance {m} [Monad m] : MonadEnv (StateT Environment m) where
  getEnv := get
  modifyEnv := modify


-- TODO: check if declarations without ranges are sub-declarations of an existing declaration with a range.
def _root_.ImportGraph.DeclNeeeds.getLineInMod? (env : Environment) (modIdx : ModuleIdx) (declNeeds : DeclNeeeds) : Option Nat := Id.run <| StateT.run' (s := env) do
  let mut lastLine := 0
  for (_, need) in declNeeds do
    let some deps := need.fixedDecls[modIdx]? | continue
    for (decl, (_,isIndirect)) in deps do
      unless isIndirect do
        let some { range .. } ← findDeclarationRangesCore? decl | continue -- TODO: different behavior if we can't find the range? consider subdeclarationhood
        lastLine := max lastLine (range.endPos.line - 1)
  if lastLine == 0 then return none else return lastLine

syntax (name := findHomeStx) "#find_home" ppSpace &"for" ppLine colGe command : command

/--
`#find_home <ident>` is deprecated. Instead, use
```
#find_home for
<command>
```
where `<command>` declares `<ident>`. This ensures that the imports necessary for the syntax and
tactics used in the declaration are present too.
-/
syntax (name := oldFindHomeStx) "#find_home " ident : command

-- elab_rules : command
-- | `(oldFindHomeStx| #find_home%$tk $id:ident) => do
--   pure ()
  -- Linter.logLintIf Linter.linter.deprecated tk
  --   m!"The syntax `#find_home <ident>` is deprecated. Instead, use\n\
  --   ```\n\
  --   #find_home for\n\
  --   <command>\n\
  --   ```\n\
  --   where `<command>` declares `<ident>`. This ensures that the imports necessary for the syntax \
  --   and tactics used in the declaration are present too."
  -- unless id.raw.isMissing do
  --   discard <| liftCoreM <| realizeGlobalConstNoOverloadWithInfo id

-- instance : ToMessageData Preceding where
--   toMessageData _ := "[p]"

open ImportGraph.Widget
open Elab Command in
elab_rules : command
| `(findHomeStx| #find_home%$tk for $cmd:command) => do
  unless Elab.inServer.get (← getOptions) do
    logWarningAt tk m!"`#find_home` currently only operates interactively."
    return
  let env ← getEnv
  let s ← ImportGraph.initStateWithPrecedingIO env
  let (extraNeeds, declNeeds, newDecls) ← withElabCommandCapturingNeeds cmd
    fun extraNeeds declNeeds newDecls => return (extraNeeds, declNeeds, newDecls)
  let needs := extraNeeds ∪ declNeeds.fullNeeds
  -- logInfo m!"{← liftCoreM <| needs.toWidget env}"
  let minimals := Needs.coveringsByProject s needs
  let auxDecls := declNeeds.keysArray.filter (!newDecls.contains ·)
  if newDecls.isEmpty then
    logWarningAt tk m!"This command did not produce any declarations."
  -- For more useful messages, we log on the whole command, so that the message appears
  -- in the infoview when the cursor is at any point within `#find_home for <command>`.
  else if minimals.all fun _ arr => arr.isEmpty then
    Lean.logInfo m!"This command is as high in the import hierarchy as it can be \
      (among transitive imports to this file).\n\n`#find_home` attempted to move the following \
      new declarations:\
      {indentD <| .bulletedList (newDecls.toList.map .ofConstName)}\
      {if auxDecls.isEmpty then m!"" else
        m!"\nas well as the following existing declarations in this file, on which those depend:\
        {indentD <| .bulletedList (auxDecls.toList.map .ofConstName)}"}"
  else
    let mut msgs := #[]
    unless auxDecls.isEmpty do
      msgs := msgs.push
        m!"This command depends on earlier declarations in this file:\
        {indentD <| .bulletedList (auxDecls.toList.map .ofConstName)}\n\
        Consider running `#find_home` on those first."
    let mainRoot := (← getMainModule).getRoot
    let mkModLinks (mods : Array (ModuleIdx × Preceding)) : CoreM (Array MessageData) := do
      let env ← getEnv
      mods.mapM fun (idx, _) => do
        let lastPos := (declNeeds.getLineInMod? env idx).elim pastEndOfFile
          ({ line := · + 1, character := 0 })
        mkGoToModuleLink env.header.modules[idx]!.module lastPos
    let andItsDepsMsg := if auxDecls.isEmpty then "" else "(and its dependencies from this file) "
    let env ← getEnv
    Lean.logInfo m!"{minimals.toArray.map fun (a, bs) =>
      (a, bs.map fun idx : ModuleIdx × Preceding => let idx := idx.1; env.header.modules[idx]!.module)}"
    for (root, mods) in minimals do
      if root == mainRoot || root.isAnonymous then continue -- handled separately; different message
      unless mods.isEmpty do
        let modLinks ← liftCoreM <| mkModLinks mods
        let pkg := (← getEnv).getModulePackageByIdx? mods[0]!.1 |>.elim "core" (s!"`{·}`")
        msgs := msgs.push m!"This command {andItsDepsMsg}can be upstreamed to `{root}` in {pkg}! \
          Specifically:\
          {indentD <| .bulletedList modLinks.toList}"
    if let some mods := minimals[mainRoot]? then
      unless mods.isEmpty do
        let modLinks ← liftCoreM <| mkModLinks mods
        msgs := msgs.push m!"In the current library, this command {andItsDepsMsg}\
          can be moved to:\
          {indentD <| .bulletedList modLinks.toList}"
    let reducedImps := needs.reduce s.transDeps |>.toRawImports (← getEnv)
    -- -- TODO: remove private imports that come from `import all`
    -- let reducedImps := Import.includeAll (← getEnv).header.imports reducedImps
    let moreInfo ← liftCoreM do
      let minImports ← do
        if reducedImps.isEmpty then pure m!"No imports required." else
          collapsible "Minimal imports" (Lean.Import.pretty reducedImps)
      let producedConsts := m!"\nNew constants\
        {indentD <| .bulletedList (newDecls.toList.map MessageData.ofConstName)}"
      let auxDeclsMsg := if auxDecls.isEmpty then m!"" else
        m!"\nAuxiliary constants\
        {indentD <| .bulletedList (auxDecls.toList.map MessageData.ofConstName)}"
      collapsible "More information" m!"{minImports}{producedConsts}{auxDeclsMsg}"
    let cmdRange := cmd.raw.getRangeWithTrailing?.get!
    let source := cmdRange.start.extract (← getFileMap).source cmdRange.stop |>.trimAscii
    let copySource ← liftCoreM do
      displayCopy s!"\n{source}\n" (display :=
        .text s!"[copy source{if auxDecls.isEmpty then "" else " - without dependencies"}]")
    Lean.logInfo m!"{m!"\n\n".joinSep msgs.toList}\n\n{copySource}\n\n{moreInfo}"


-- TODO: Is there something fundamentally wrong about `calcDeclNeeds`? Why do we not need to know the *position* at which the declaration is used? Likewise, isn't there a way-of-needing the meta declarations which would let us say they were used in a meta position?


  -- -- Lake.CLI.Shake
  -- let minimals := minimals.map fun (project, vals) =>
  --   (project, vals.map (fun a : ModuleIdx × _ => env.header.modules[a.1]!.module))
  -- logInfo m!"{minimals}"
  -- let reduced := needs.reduce transDeps |>.toImports (← getEnv)
  -- logInfo m!"{decls.map MessageData.ofConstName}: {Import.prettyGrouped reduced}"

-- #find_home



-- -- One version that does this; another version that minimizes it on your actual file, with some hackery perhaps to ensure it's at the end.
-- -- Ideally a widget with a promise that gets filled in by a linter at the end?
-- -- Or not a promise, because that might not be editable. Just a ref that gets updated, maybe? Plus a ringing of a bell to update the widget...
-- #min_imports
-- -- Also, try-this for replacing imports and such. Should `#min_imports` just be a lightbulb?




-- #show_imports
-- /--
-- Find locations as high as possible in the import hierarchy
-- where the named declaration could live.
-- -/
-- def Lean.Name.findHome (n : Name) (env : Option Environment) : CoreM NameSet := do
--   let current? := match env with | some env => env.header.mainModule | _ => default
--   let required := (← n.requiredModules).toArray.erase current?
--   let imports := (← getEnv).importGraph.transitiveClosure
--   let mut candidates : NameSet := {}
--   for (n, i) in imports do
--     if required.all fun r => n == r || i.contains r then
--       candidates := candidates.insert n
--   for c in candidates do
--     for i in candidates do
--       if imports.find? i |>.getD {} |>.contains c then
--         candidates := candidates.erase i
--   return candidates

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

#exit

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
