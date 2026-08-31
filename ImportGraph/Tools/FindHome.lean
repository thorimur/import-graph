/-
Copyright (c) 2023 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison, Paul Lezeau
-/
module

public meta import ImportGraph.Imports.Pretty
public meta import ImportGraph.Lean.MessageData
public meta import ImportGraph.Shake.Coverings
public meta import ImportGraph.Shake.Environment
public meta import ImportGraph.Shake.Workspace
public import ImportGraph.Tools.Collapsible
public import ImportGraph.Tools.Copy
public import ImportGraph.Util.GoTo

/-!
# `#find_home`

This module provides the `#find_home` utility in the module system, which suggests places a given command (and its dependencies from the current file) can live.

## Future work

### UI

- Provide more information about the extracted dependencies of the given commands and declarations
  (e.g. *why* certain imports are necessary, what role certain declarations play). This information
  is available internally and needs only to be rendered helpfully.
- Provide more ranking options by default, and broadly improve the UI to be more informative (may
  involve moving off of `MessageData` to HTML)
- In the other direction, provide an "agent mode" that emits simplified textual information
- Provide more visibility into the import hierarchy. This may also be in the remit of related UX
  instead of `#find_home` per se.

### Functionality

- Provide better support for moving declarations with same-file dependencies:
  - Capture the syntax needs of dependencies, e.g. via a stateful linter
  - Allow copying all of the dependencies at once
- Capture and copy over scopes/namespaces.
- Optionally leave behind `relocated ... to ...` commands
- Handle meta definitions.
- Allow for "mutation": find near-misses, where slight alterations to (1) the import hierarchy or
  (2) aspects of the current commands might allow other "homes" to be found.
- Allow for configurable queries, which could express e.g. e.g. "only consider modules which don't
  import <module A>" or "only consider modules downstream/upstream of <certain set of modules>" or
  "minimize the (nonzero) amount of category theory imported"
  - Handle configurable export preservation (e.g. "the highest place which provides this to
    <module>")
-/


open Lean

-- TODO(NOW): warn when we attempt to move meta definitions
-- TODO(NOW): check for runtime IR handling of constructors
-- TODO(NOW): import prettification outside module system

meta section

-- open Lake hiding logInfo
-- open Shake



-- meta section

-- /--
-- This declaration exists in `Batteries`, but we don't want to make `ImportGraph` depend on batteries. We therefore just bear the duplication cost and make this private (and primed, in case someone `imports all`).
-- -/
-- private protected def Lean.Position.getDeclsAfter' (env : Environment) (pos : Position)
--     (asyncMode := EnvExtension.AsyncMode.local) : Array Name :=
--   declRangeExt.getState env asyncMode |>.foldl (init := #[])
--     fun acc name { selectionRange .. } =>
--       if selectionRange.pos.lt pos then acc else acc.push name

-- /--
-- Likewise
-- -/
-- @[inline] private protected def _root_.String.Pos.Raw.getDeclsAfter' (env : Environment) (map : FileMap)
--     (pos : String.Pos.Raw) (asyncMode := EnvExtension.AsyncMode.local) : Array Name :=
--   map.toPosition pos |>.getDeclsAfter' env asyncMode


/-
#min_imports as widget that waits for everything by adding a linter that holds a handle to a promise, which is resolved in the infoview? Is that possible?

Also something that just minimizes your existing imports into something canonical.

Should respect shake directives.
-/

namespace ImportGraph.Shake
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

-- def addCurrentExtraModUses (env : Environment) (needs : Needs) : Needs := Id.run do
--   let mut needs := needs
--   for use in getExtraModUsesState env |>.1 do
--     needs := needs.union { use with } {env.getModuleIdx! use.module}
--   return needs

-- TODO:
-- switch argument order
-- include array of new constants?

open ImportGraph Shake

open Lean Elab Command in
elab "#show_imports" ppLine cmd:command : command => do
  let transDeps := (← getEnv).mkTransDeps
  let (declNeeds, newDecls) ← withElabCommandCapturingNeeds cmd
  let importNeeds ← liftCoreM ((← getEnv).toSimultaneousImportNeeds declNeeds).run'
  let reduced := (← getEnv).toRawImports <| importNeeds.toNeeds.reduce transDeps

  Lean.logInfo m!"Found the following new declarations:\n\
    {newDecls.map MessageData.ofConstName}\n\n\
    Necessary imports:\n\n\
    {ImportGraph.Lean.Import.pretty reduced}"



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

-- TODO(NOW): check for aboveness wrt the current module via lib trans deps
-- TODO(NOW): exclude non-default targets?

-- TODO: we can handle recursive declarations by reversing the hierarchy
-- we need a place to cache all this stuff...

-- TODO: do we need to traverse the infotrees? maybe a config option.

instance : ToMessageData WorkspaceModel.Error where
  toMessageData
    | .noLibOfModule mod => m!"Could not find library for module `{mod}`."
    | .readImportsFailure mod path ioError =>
      m!"Failed to read imports of `{mod}`:{indentD ioError.toString}\n\n\
        Path to module: {path}"

open ImportGraph.Widget Elab Command in
elab_rules : command
| `(findHomeStx| #find_home%$tk for $cmd:command) => do
  let w ← getWorkspaceModel #[← getMainModule]
  if w.hasErrors then
    logErrorAt tk m!"Errors when building the import hierarchy:\n\n\
      {m!"\n\n".joinSep (w.errors.map toMessageData |>.toList)}"
  let (declNeeds, newDecls) ← withElabCommandCapturingNeeds cmd
  if ← MonadLog.hasErrors then -- Also stop if the command produced errors
    return
  if newDecls.isEmpty then
    -- TODO: remove, allow finding homes for commands like `attribute`
    logWarningAt tk m!"This command did not produce any declarations."
    return
  -- TODO: better handling of recursive import needs
  let importNeeds ← liftCoreM <| declNeeds.toSimultaneousImportNeeds w |>.run'
  -- logInfo m!"{← liftCoreM <| needs.toWidget env}"
  -- Previously defined declarations from the same file (excluding autogenerated declarations).
  let priorDecls := declNeeds.keysArray.filter fun decl =>
    !newDecls.contains decl && !(declNeeds.get! decl |>.isAutoDecl)

  let some currentModIdx := w.getModIdx? (← getMainModule)
    | logErrorAt tk m!"Could not find current module `{← getMainModule}` in workspace."
  let currentLibIdx := w.libIdxOfModIdx! currentModIdx
  let currentPkgIdx := w.pkgIdxOfModIdx! currentModIdx
  let currentPrevs := w.getMod! currentModIdx |>.prevs
  let currentTransDeps := w.getMod! currentModIdx |>.transDeps
  let mut msgs := #[]
  let mkModLinks (mods : Array ModIdx) : CommandElabM (Array MessageData) := liftCoreM do
    let mut links := #[]
    for modIdx in mods do
      let modName := w.getMod! modIdx |>.name
      let mut decls : NameSet := {}
      for (_, need) in declNeeds do
        let some declsFromMod := need.fixedDecls[modName]? | continue
        decls := decls.insertMany declsFromMod.keysArray
      links := links.push <|← goToModuleOfDecls decls.toArray (fallbackModule := modName)
    return links
  let minimals := importNeeds.providersByLib w
  -- TODO: currently this is a simple-minded check to see if it exists in the private scope.
  -- (Note that since `public` ⊆ `private`, this includes publicly-imported modules.)
  -- In the future we want to check the stance is preserved, allow meta if relevant, and so on.
  let minimalsProvidedHere := importNeeds.providersByLib w (league := currentTransDeps.get .priv)
  let otherSameLib :=
    minimals[currentLibIdx]?.getD #[] |>.filter (· != currentModIdx)
  let (aboveSameLib, adjSameLib) := otherSameLib.partition currentPrevs.has
  let providedHereSameLib :=
    minimalsProvidedHere[currentLibIdx]?.getD #[] |>.filter fun modIdx =>
      modIdx != currentModIdx && !(aboveSameLib.contains modIdx)
  -- Note that `providedHereSameLib` is disjoint from both `aboveSameLib` and `adjSameLib`.
  -- Note that `aboveSameLib.isEmpty` implies `providedHereSameLib` is empty.
  if aboveSameLib.isEmpty then
    msgs := msgs.push m!"In this library, this command \
      {if priorDecls.isEmpty then "is " else "and its dependencies from this file are "}\
      as high in the import hierarchy as {if priorDecls.isEmpty then "it" else "they"} can be\
      {if adjSameLib.isEmpty then "" else " above the current module"}."
  else
    unless aboveSameLib.isEmpty do
      let modLinks ← mkModLinks aboveSameLib
      let modLinks := modLinks.zipWith (fun msg isProvidedHere => if isProvidedHere then
        msg else m!"{msg} (not imported here)") (aboveSameLib.map (currentTransDeps.get .priv).has)
      msgs := msgs.push <|
        m!"This command {if priorDecls.isEmpty then "" else "and its dependencies "}\
          can be moved to the following module\
          {if aboveSameLib.size = 1 then "" else "s"} above this module:\
          {indentD <| .bulletList modLinks.toList}"
    unless providedHereSameLib.isEmpty do
      let modLinks ← mkModLinks providedHereSameLib
      msgs := msgs.push <|← liftCoreM <|
        collapsible m!"This command can also be moved to modules which are highest in the \
          hierarchy among modules currently imported in this file, but are not highest among all \
          modules."
          m!"{.bulletList modLinks.toList}"
  unless adjSameLib.isEmpty do
    let modLinks ← mkModLinks adjSameLib
    msgs := msgs.push <|← liftCoreM <|
      collapsible m!"{if aboveSameLib.isEmpty then
        "However, this command can be moved to" else "This command can also be moved to"} \
        files adjacent to the current module in the import hierarchy."
        m!"{.bulletList modLinks.toList}"
  if aboveSameLib.isEmpty && adjSameLib.isEmpty then
    msgs := msgs.push <|
      m!"`#find_home` attempted to move the following new declaration\
        {if newDecls.size = 1 then "" else "s"}:\
      {indentD <| .bulletList (newDecls.toList.map .ofConstName)}\
      {if priorDecls.isEmpty then m!"" else
        m!"\n\
          as well as the following existing declaration{if priorDecls.size = 1 then "" else "s"} \
          in this file, on which {if newDecls.size = 1 then "it depends" else "they depend"}:\
          {indentD <| .bulletList (priorDecls.toList.map .ofConstName)}"}"
  let upstreams := minimals.filter fun libIdx _ => libIdx != currentLibIdx &&
  -- TODO: we assume all unequal packages are upstream. This is not necessarily the case.
    (w.pkgIdxOfLibIdx! libIdx != currentPkgIdx)
  unless upstreams.isEmpty do
    let mut upstreamTo := #[]
    for (libIdx, modIdxs) in upstreams do
      upstreamTo := upstreamTo.push <|← liftCoreM <|
        collapsible m!"To `{w.getLib! libIdx |>.name}` in `{w.pkgOfLibIdx! libIdx |>.origName}`:"
          m!"{.bulletList <| (← mkModLinks modIdxs).toList}"
    msgs := msgs.push <|← liftCoreM <|
      collapsible m!"Note: this command does not depend on the current package, \
        and may be upstreamed."
        m!"{m!"".joinSep upstreamTo.toList}"
  -- "More information" message:
  let reducedImps := w.toRawImports <| importNeeds.toNeeds.reduce w
  let moreInfo ← liftCoreM do
    -- TODO: more information from declNeeds.
    let minImports ← do
      if reducedImps.isEmpty then pure m!"This command does not require any imports." else
        collapsible "Imports needed" (Lean.Import.pretty reducedImps)
    let producedConsts ← collapsible m!"New constants from this command"
      m!"{.bulletList (newDecls.toList.map MessageData.ofConstName)}"
    let priorDeclsMsg ← if priorDecls.isEmpty then pure m!"" else
      collapsible m!"Prior constants used in this command"
        m!"{.bulletList (priorDecls.toList.map MessageData.ofConstName)}"
    collapsible "More information" m!"{minImports}{producedConsts}{priorDeclsMsg}"
  let cmdRange := cmd.raw.getRangeWithTrailing?.get!
  let source := cmdRange.start.extract (← getFileMap).source cmdRange.stop |>.trimAscii
  -- TODO: copy over prior declarations as well
  let disclaimerComment := "-- NOTE: necessary scopes and namespaces may not have been copied over."
  let copySource ← liftCoreM do
    copyToClipboard s!"\n{disclaimerComment}\n{source}\n" (display :=
      .text s!"[copy source{if priorDecls.isEmpty then "" else " (without prior declarations)"}]")
  Lean.logInfo m!"{m!"\n".joinSep msgs.toList}\
    \n\n\
    {if priorDecls.isEmpty then m!"" else m!"Be sure to also move the following prior declarations:\
      {indentD <| .bulletList (priorDecls.toList.map MessageData.ofConstName)}\
      \n\n"}\
    {copySource}\n\n{moreInfo}"


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

-- #check Environment.getModuleIdx?

open Elab Command

-- run_cmd do
--   let env ← getEnv
--   let ind := indirectModUseExt.getState (← getEnv) |>.toArray.map fun (a, b) => (a, b.map (env.header.moduleNames[·]!))
--   let extra := extraModUses.getState (← getEnv) |>.toList
--   -- logInfo m!"{ind}"
--   let r := isExtraRevModUseExt.getState (← getEnv)
--   logInfo m!"{repr extra}"

-- #exit

-- open Elab Command in
-- /--
-- Find locations as high as possible in the import hierarchy
-- where the named declaration could live.
-- Using `#find_home!` will forcefully remove the current file.
-- Note that this works best if used in a file with `import Mathlib`.

-- The current file could still be the only suggestion, even using `#find_home! lemma`.
-- The reason is that `#find_home!` scans the import graph below the current file,
-- selects all the files containing declarations appearing in `lemma`, excluding
-- the current file itself and looks for all least upper bounds of such files.

-- For a simple example, if `lemma` is in a file importing only `A.lean` and `B.lean` and
-- uses one lemma from each, then `#find_home! lemma` returns the current file.
-- -/
-- elab "#find_home" bang:"!"? n:ident : command => do
--   let stx ← getRef
--   let mut homes : Array MessageData := #[]
--   let n ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo n
--   let env? ← bang.mapM fun _ => getEnv
--   for modName in (← Elab.Command.liftCoreM do n.findHome env?) do
--     let p : GoToModuleLinkProps := { modName }
--     homes := homes.push $ .ofWidget
--       (← liftCoreM $ Widget.WidgetInstance.ofHash
--         GoToModuleLink.javascriptHash $
--         Server.RpcEncodable.rpcEncode p)
--       (toString modName)
--   logInfoAt stx[0] m!"{homes}"
