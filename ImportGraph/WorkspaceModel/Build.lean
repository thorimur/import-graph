/-
Copyright (c) 2026 Thomas Murrills. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Murrills
-/
module

import ImportGraph.WorkspaceModel.Summary
import all ImportGraph.WorkspaceModel.Model
import all ImportGraph.Shake.Basic
import all ImportGraph.Shake.Algebra
import Lean.Elab.ParseImportsFast
public import ImportGraph.WorkspaceModel.Lake

import Lake

/-!
# Building a `WorkspaceModel`

This file turns raw workspace data into the bitset-form model:

1. `fetchRaw` obtains a `WorkspaceSummary` by spawning `lake exe import-graph-raw` (see
   `ImportGraph.WorkspaceModel.Emit`) — the acquisition path for consumers that cannot
   load a Lake workspace in-process, the language server in particular. No caching: the
   model is meant to live in server state, and if the workspace configuration changes
   under a running server, everything is stale anyway.

2. `WorkspaceModel.ofRaw` elaborates the raw data: it appends the toolchain
   pseudo-package, flattens the libraries, enumerates the selected libraries' modules
   from their source trees, parses all headers in parallel (with `Lean.parseImports'`,
   the fast header parser), and computes the intrinsic arrow and relational bitsets —
   direct and kind-aware-transitive imports, previous modules, inferred library
   dependencies, and package/library membership.

`WorkspaceModel.load` composes the two.

Which modules enter the model: each selected library contributes its *source tree* — the
modules under its `roots` plus its `globs`' matches, as found on disk. This can be a
superset of what `lake build` would build (with default globs Lake builds the roots'
*import closure*), but for "where can this declaration live?" questions the source tree
is the honest universe. By default all Lake libraries are selected; the toolchain
pseudo-libraries can be selected too, at the cost of enumerating several thousand core
modules.

Note: this module must be imported via `import all`.
-/

open ImportGraph Lean System Lake Lake.Shake

namespace ImportGraph

-- TODO: deduce this from core's lakefile instead of hardcoding it, ideally during `Emit`
-- Somehow exclude "LakeMain", "LeanIR", "Leanc", "LeanChecker"? Or will these be ignored by not being above the current package?
/-- A hardcoded list of the four libraries we want to consider in the toolchain (`Init`, `Std`, `Lean`, `Lake`) with directories relative to the `sysroot`. -/
private def toolchainLibs (sysroot : FilePath) : Array Lake.LibrarySummary :=
  #[{ name := `Init, srcDir := sysroot / "src" / "lean" / "Init" },
    { name := `Std, srcDir := sysroot / "src" / "lean" / "Std" },
    { name := `Lean, srcDir := sysroot / "src" / "lean" / "Lean"
      globs := #[`Lean, `Lean.Compiler.IR.EmitLLVM, `Lean.Compiler.LCNF.Probing] },
    { name := `Lake, srcDir := sysroot / "src" / "lean" / "lake"
      globs := #[`Lake.*] }]

-- TODO: just alter `parseImports'` to account for this.
private def hasImplicitPrelude (header : Lean.ModuleHeader) : Bool :=
  header.imports[0]?.isEqSome { module := `Init } &&
  header.imports[1]?.isEqSome { module := `Init, isMeta := true }

-- TODO: surely this exists?
private def _root_.Except.getError! [Inhabited ε] : Except ε α → ε
  | .error e => e
  | _ => default

/--
Collect `mod` and its local imports **into `wm`**, adapting `LeanLib.recCollectLocalModules`:
recurse into imports *first*, then record `mod`. Because a module is recorded only after
everything it imports, `wm.mods` comes out topologically sorted (no separate topo pass), and
everything a new module contributes to the model is known at that point — so `collect` folds
it into every relational bitset in one shot:

* it is pushed onto `wm.mods` at the next index, and `wm.idxOfMod` maps its name there;
* that index is added to its library's and package's `mods`;
* its library's `deps` gains the libraries of its (already-indexed) direct imports.

The only fields left unfilled are the transitive closures `Module.transDeps`/`prevs`, which
need a global pass over the finished dag (the caller's seam). So `wm` is a **partial model**
throughout collection — valid to grow via `collect`, but not to query until the seam runs.

We follow every import that resolves to *some* library (`libIdxOfMod?`), pulling in the core
modules that are actually imported (core is in the model, reachable slice only — we never
walk the filesystem, so nobody's scratch files leak in). Imports under no library are
external and stop the recursion.

`wm.idxOfMod` is the only seen-structure, written once per module — at exit, with its real
index. Assuming no import cycles, a module is re-encountered only after it has finished, so
this is enough to dedupe (an *in-progress* re-encounter would be a cycle). -/
private partial def collect (mod : Name) (wm : WorkspaceModel) : IO WorkspaceModel := do
  if wm.idxOfMod.contains mod then return wm
  let some libIdx := wm.libIdxOfMod? mod | return { wm with
    errors := wm.errors.push <| .noLibOfModule mod }
  let srcFile := (wm.getLib! libIdx).srcPathOfMod mod
  let headerE ← observing do Lean.parseImports' (← IO.FS.readFile srcFile) srcFile.toString
  -- TODO: clean up to avoid `getError!`
  let .ok header := headerE | return { wm with
    errors := wm.errors.push <| .readImportsFailure mod srcFile headerE.getError! }
  let mut wm := wm
  for imp in header.imports do
    wm ← collect imp.module wm
  -- All local imports of `mod` are indexed now; gather the libraries they live in.
  let pkgIdx := wm.pkgIdxOfLibIdx! libIdx

  -- Module aggregates. TODO: consider consolidating?
  let mut transPkgDeps : PackageBitset := ∅
  let mut transLibDeps : LibraryBitset := ∅
  let mut transDeps := Needs.empty
  let mut prevs := ∅
  for imp in header.imports do
    -- TODO: Potentially we ought to record an error if we can't find it here.
    if let some j := wm.idxOfMod[imp.module]? then
      let impModData := wm.getMod! j
      transLibDeps := transLibDeps ∪ impModData.transLibDeps ∪ {impModData.libIdx}
      transPkgDeps := transPkgDeps ∪ impModData.transPkgDeps ∪ {impModData.pkgIdx}
      transDeps := addTransitiveImps transDeps imp j impModData.transDeps
      prevs := prevs ∪ impModData.prevs ∪ {j}
  let isPrelude := hasImplicitPrelude header
  let modData : WorkspaceModel.Module := { header with
    name := mod, srcFile, isPrelude, prevs, transDeps, transLibDeps, transPkgDeps, libIdx, pkgIdx }
  let modIdx := wm.mods.size -- the position of `modData` in `mods` below
  return { wm with
    idxOfMod := wm.idxOfMod.insert mod modIdx
    mods := wm.mods.push modData
    packages := wm.packages.modify pkgIdx fun p => { p with mods := insert modIdx p.mods }
    libs := wm.libs.modify libIdx fun l =>
      { l with mods := insert modIdx l.mods, revealedDeps := l.revealedDeps ∪ transLibDeps } }

/--
Elaborate a `WorkspaceSummary` into a `WorkspaceModel` by following imports from the
libraries' roots, plus `extraMods` (curated modules not reachable from any root — e.g. a new
file not yet added to `Mathlib.lean`) and their imports. We do *not* walk the filesystem, so
scratch files that no root imports and that aren't in `extraMods` stay out. The resulting
`mods` array is topologically sorted (see `collect`).

The model is built incrementally: after the packages/libraries scaffold is in place we seed
an otherwise-empty model and grow it with `collect`, which fills every field except the
transitive closures `Module.transDeps`/`prevs` (the seam below). Until that seam runs the
returned model is partial.

Deliberately unoptimized: collection is one sequential recursive pass. Parallel header
parsing and caching the (per-toolchain, fixed) core graph are later iterations. -/
def Lake.WorkspaceSummary.toWorkspaceModel (ws : WorkspaceSummary)
    (extraMods : Array Name := #[]) : IO WorkspaceModel := do
  -- === Packages & libraries: flat indexing, toolchain pseudo-package/-libraries last. ===
  let toolchainPkgIdx := ws.packages.size
  let mut packages : Array WorkspaceModel.Package := ws.packages.map fun pkg =>
    { toBasePackage := pkg.toBasePackage
      deps := Bitset.ofArray pkg.deps ∪ {toolchainPkgIdx}
      -- Filled in later:
      libs := ∅, mods := ∅ }
  let toolchainName := ws.version.toToolchainName
  packages := packages.push
    { baseName := toolchainName, origName := toolchainName, wsIdx := toolchainPkgIdx
      dir := ws.sysroot, leanLibDir := ws.sysroot / "lib" / "lean", deps := ∅
      -- Filled in later:
      libs := ∅, mods := ∅ }
  let mut libs : Array WorkspaceModel.Library := #[]
  for pkg in ws.packages do
    for l in pkg.libs do
      libs := libs.push { l with pkgIdx := pkg.wsIdx, revealedDeps := ∅, mods := ∅ }
  for lib in toolchainLibs ws.sysroot do
    libs := libs.push { lib with pkgIdx := toolchainPkgIdx, revealedDeps := ∅, mods := ∅ }
  for lib in libs, libIdx in 0...libs.size do
    packages := packages.modify lib.pkgIdx fun p => { p with libs := insert libIdx p.libs }

  -- TODO: split off part up to here into thing which returns packages and libraries?
  -- === Grow the model by following imports from each library's roots (packages in reverse
  -- order to reduce recursion), then from the extra modules. Toolchain roots are *not* seeded —
  -- core enters only via imports that actually reference it. `collect` maintains `mods` (in
  -- topological order), `idxOfMod`, and the library/package relational bitsets as it goes. ===
  let mut wm : WorkspaceModel :=
    { ws with packages, libs, mods := #[], idxOfMod := ∅ }
  -- This array should be relatively small, so bite the copying here to ensure
  -- we have no sharing bugs later
  let allGlobs := wm.libs.flatMap fun { globs, srcDir .. } => globs.map ((·,srcDir))
  -- TODO: there should really be a better way to `for ... in` through an array in reverse, right?
  for (glob, srcDir) in allGlobs.reverse do
    for (mod, _) in glob.modulesIn srcDir do
      wm ← collect mod wm
  for mod in extraMods do
    wm ← collect mod wm
  return wm

initialize workspaceModelCache : IO.Ref (Option WorkspaceModel) ← IO.mkRef none

def getWorkspaceModel (extraMods : Array Name := #[])
    (useCache := true) (cwd : Option System.FilePath := none) :
    IO WorkspaceModel := do
  if useCache then if let some wm ← workspaceModelCache.get then
    return wm
  let summary ← getWorkspaceSummary cwd
  let wm ← summary.toWorkspaceModel extraMods
  workspaceModelCache.set wm
  return wm

end ImportGraph
