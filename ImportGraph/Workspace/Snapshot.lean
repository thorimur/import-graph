/-
Copyright (c) 2026 Thomas Murrills. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Murrills
-/
import Lake
import ImportGraph.Workspace.Index
import ImportGraph.Workspace.Dag

/-!
# Workspace snapshots

The structural facts `#find_home` (and friends) need about a workspace — which packages
exist and how they depend on each other, which libraries they define, where module sources
and `.olean`s live — are all known to Lake, but *loading* a Lake workspace requires
elaborating `lakefile.lean` configurations, which needs Lake's native code in-process.
The language server does not load Lake's shared library, so workspace loading fails there.

This file defines `WorkspaceInfo`: a plain-data, JSON-serializable snapshot of exactly the
structural part of a `Lake.Workspace`. It can be produced wherever workspace loading *does*
work (the `import-graph-info` executable — see `ImportGraph.Workspace.Emit`; or a facet or
script with a `Lake.Workspace` in hand, via `Lake.Workspace.toWorkspaceInfo`) and consumed
anywhere (see `ImportGraph.Workspace.Fetch` for the in-server acquisition path).

Design notes:

* **Module lists are deliberately absent.** A snapshot records each library's `srcDir`,
  `roots`, and `globs` — the *rule* for which modules belong to it — rather than the modules
  themselves. Consumers resolve the rule against the filesystem (see
  `ImportGraph.Workspace.Modules`), so a snapshot stays valid when files are added or
  removed, and only genuine configuration changes (tracked by `Fingerprint`) invalidate it.

* **The toolchain is a pseudo-package.** Modules like `Init.*` or `Lean.*` belong to no Lake
  package, but every classification question ("which library is this module in?", "can this
  declaration move to that package?") should have a uniform answer. So the snapshot appends
  one extra `PackageInfo` for the toolchain, with libraries `Init`, `Std`, `Lean`, and
  `Lake`, and gives every Lake package an (explicit) dependency on it. Lake packages occupy
  indices `0, ..., n - 1` in Lake's own workspace order (root first), so `Idx PackageInfo`
  agrees with Lake's `wsIdx` on real packages; the toolchain is the final index.
-/

open Lean System

namespace ImportGraph

/-! ## JSON codecs for foreign types

These are `local` so that we do not export instances for types we do not own.
-/

private local instance : ToJson FilePath := ⟨fun p => .str p.toString⟩
private local instance : FromJson FilePath := ⟨fun j => FilePath.mk <$> fromJson? j⟩

/-- Serialized in Lake's glob notation: `A`, `A.+` (strict submodules), `A.*` (both). -/
private local instance : ToJson Lake.Glob := ⟨fun g =>
  match g with
  | .one n => .str (n.toString (escape := false))
  | .submodules n => .str (n.toString (escape := false) ++ ".+")
  | .andSubmodules n => .str (n.toString (escape := false) ++ ".*")⟩

private local instance : FromJson Lake.Glob := ⟨fun j => do
  let s : String ← fromJson? j
  if let some s := s.dropSuffix? ".+" then
    return .submodules s.toString.toName
  else if let some s := s.dropSuffix? ".*" then
    return .andSubmodules s.toString.toName
  else
    return .one s.toName⟩

/-! ## The snapshot -/

/--
A snapshot of one package of a workspace: either a Lake package, or the pseudo-package
representing the toolchain (see the module docstring).

All paths are absolute.
-/
structure PackageInfo where
  /-- The package's (assigned) name, or `toolchain` for the toolchain pseudo-package. -/
  name : Name
  /-- Whether this is the pseudo-package representing the Lean toolchain. -/
  isToolchain : Bool := false
  /-- The package's root directory (for the toolchain: the sysroot). -/
  dir : FilePath
  /-- The workspace indices of the package's direct dependencies. For Lake packages this is
  Lake's resolved dependency list plus the toolchain pseudo-package. -/
  deps : Array (Idx PackageInfo) := #[]
  /-- The directory holding the package's compiled module artifacts (`.olean`s etc.),
  e.g. `<dir>/.lake/build/lib/lean` (for the toolchain: `<sysroot>/lib/lean`). -/
  leanLibDir : FilePath
  /-- The names of the package's default targets. -/
  defaultTargets : Array Name := #[]
  deriving ToJson, FromJson, Repr, Inhabited

/-- A typed index of a package within a `WorkspaceInfo`. Agrees with Lake's
`Package.wsIdx` for Lake packages. -/
abbrev PkgIdx := Idx PackageInfo

/--
A snapshot of one Lean library (`lean_lib`) of a workspace, including the pseudo-libraries
`Init`/`Std`/`Lean`/`Lake` of the toolchain pseudo-package.

A library does not carry its list of modules; it carries the *rule* (`srcDir`, `roots`,
`globs`) by which its modules are found. See `ImportGraph.Workspace.Modules` for resolving
the rule against the filesystem, and `WorkspaceInfo.owningLibs` for the pure membership
test.
-/
structure LibraryInfo where
  /-- The library's name. -/
  name : Name
  /-- The package the library belongs to. -/
  pkg : PkgIdx
  /-- The directory relative to which the library's module names locate source files
  (absolute). -/
  srcDir : FilePath
  /-- The library's root module names. -/
  roots : Array Name
  /-- The globs specifying the library's buildable modules. -/
  globs : Array Lake.Glob
  deriving ToJson, FromJson, Repr, Inhabited

/-- A typed index of a library within a `WorkspaceInfo`. -/
abbrev LibIdx := Idx LibraryInfo

/--
A cheap summary of the inputs that determine a workspace's structure. If a stored
snapshot's fingerprint matches a freshly computed one, the snapshot can be reused;
see `Fingerprint.compute`.

(This is a heuristic: it does not observe the configuration files of dependencies, which
can change for path dependencies without the root manifest changing. Use
`ImportGraph.Workspace.Fetch` with `fresh := true` to force regeneration.)
-/
structure Fingerprint where
  /-- The contents of the workspace root's `lean-toolchain` (trimmed), if present. -/
  toolchain : String := ""
  /-- A hash of the root package's configuration file contents. -/
  configHash : Nat := 0
  /-- A hash of the root package's manifest contents. -/
  manifestHash : Nat := 0
  deriving ToJson, FromJson, BEq, Repr, Inhabited

/-- The current `WorkspaceInfo.formatVersion`. Bump when the JSON format changes. -/
def WorkspaceInfo.currentFormatVersion : Nat := 1

/--
A plain-data snapshot of the structure of a Lake workspace: its packages (plus the
toolchain pseudo-package), their dependency graph, and their Lean libraries. See the
module docstring for the overall design, and `ImportGraph.Workspace.Fetch` for how to
obtain one from inside the language server.
-/
structure WorkspaceInfo where
  /-- The version of this data format (`WorkspaceInfo.currentFormatVersion`). -/
  formatVersion : Nat := WorkspaceInfo.currentFormatVersion
  /-- The workspace root directory (absolute). -/
  dir : FilePath
  /-- The Lean toolchain's sysroot (absolute). -/
  sysroot : FilePath
  /-- The root package's configuration file (absolute); an input to `fingerprint`. -/
  rootConfigFile : FilePath
  /-- The root package's manifest file (absolute); an input to `fingerprint`. -/
  rootManifestFile : FilePath
  /-- A summary of the snapshot's inputs, for staleness detection. -/
  fingerprint : Fingerprint := {}
  /-- The packages of the workspace: Lake packages in Lake's workspace order (root first),
  followed by the toolchain pseudo-package (last). -/
  packages : Table PackageInfo PackageInfo
  /-- The Lean libraries of all packages, flattened (in package order). -/
  libs : Table LibraryInfo LibraryInfo
  deriving ToJson, FromJson, Repr, Inhabited

namespace WorkspaceInfo

/-- The root package of the workspace. -/
@[inline] def root (info : WorkspaceInfo) : PackageInfo := info.packages.get! ⟨0⟩

/-- The index of the toolchain pseudo-package (the last package). -/
@[inline] def toolchainPkg (info : WorkspaceInfo) : PkgIdx := ⟨info.packages.size - 1⟩

/-- The index of the package named `name`, if any. -/
def findPackage? (info : WorkspaceInfo) (name : Name) : Option PkgIdx :=
  info.packages.findIdx? (·.name == name)

/-- The index of the library named `name`, if any. (Library names are not necessarily
unique across packages; this returns the first, in package order.) -/
def findLib? (info : WorkspaceInfo) (name : Name) : Option LibIdx :=
  info.libs.findIdx? (·.name == name)

/-- The direct package dependency graph: an edge `p → q` means `p` directly depends
on `q`. -/
def packageDag (info : WorkspaceInfo) : Dag PackageInfo :=
  ⟨info.packages.map fun pkg => .ofArray pkg.deps⟩

/-- The libraries of each package. -/
def libsByPkg (info : WorkspaceInfo) : Table PackageInfo (IdxSet LibraryInfo) := Id.run do
  let mut t : Table PackageInfo (IdxSet LibraryInfo) := .replicate info.packages.size ∅
  for (i, lib) in info.libs do
    t := t.modify lib.pkg (·.insert i)
  return t

/-- Whether `mod` is considered local to the library `lib` (it is a submodule of one of the
library's `roots`, or matches one of its `globs`). This is a pure test on the module
*name*; it does not consult the filesystem. -/
def isLocalModuleOf (info : WorkspaceInfo) (lib : LibIdx) (mod : Name) : Bool :=
  let lib := info.libs.get! lib
  lib.roots.any (·.isPrefixOf mod) || lib.globs.any (·.matches mod)

/--
The libraries that consider `mod` local (see `isLocalModuleOf`).

This classifies *any* module name — including toolchain modules like `Init.Data.Nat` —
without touching the filesystem, which makes it suitable for classifying the modules of an
`Environment` by library or package.
-/
def owningLibs (info : WorkspaceInfo) (mod : Name) : IdxSet LibraryInfo := Id.run do
  let mut acc : IdxSet LibraryInfo := ∅
  for (i, _) in info.libs do
    if info.isLocalModuleOf i mod then
      acc := acc.insert i
  return acc

/-- The packages owning a library that considers `mod` local (see `owningLibs`). -/
def owningPackages (info : WorkspaceInfo) (mod : Name) : IdxSet PackageInfo :=
  info.owningLibs mod |>.foldl (init := ∅) fun acc i =>
    acc.insert (info.libs.get! i).pkg

/-- The `.olean` file for a module of library `lib`, i.e. the module's path under the
owning package's `leanLibDir`. (Its existence depends on the module having been built.) -/
def oleanFile (info : WorkspaceInfo) (lib : LibIdx) (mod : Name) : FilePath :=
  modToFilePath (info.packages.get! (info.libs.get! lib).pkg).leanLibDir mod "olean"

/-- The source file for a module of library `lib`, i.e. the module's path under the
library's `srcDir`. -/
def srcFile (info : WorkspaceInfo) (lib : LibIdx) (mod : Name) : FilePath :=
  modToFilePath (info.libs.get! lib).srcDir mod "lean"

end WorkspaceInfo

/-! ## Fingerprints -/

/-- The `hash` of a file's contents (`0` if the file does not exist). -/
private def fileContentHash (path : FilePath) : IO Nat := do
  if ← path.pathExists then
    return (hash (← IO.FS.readFile path)).toNat
  else
    return 0

/-- Compute the `Fingerprint` of the workspace at `wsDir` whose root package configuration
and manifest live at the given (absolute) paths. Cheap: reads at most three files. -/
def Fingerprint.compute (wsDir rootConfigFile rootManifestFile : FilePath) :
    IO Fingerprint := do
  let toolchainFile := wsDir / "lean-toolchain"
  let toolchain ←
    if ← toolchainFile.pathExists then
      pure (← IO.FS.readFile toolchainFile).trimAscii.copy
    else
      pure ""
  return {
    toolchain
    configHash := ← fileContentHash rootConfigFile
    manifestHash := ← fileContentHash rootManifestFile
  }

/-! ## Snapshotting a loaded `Lake.Workspace` -/

/-- The names of the libraries of the toolchain pseudo-package, with their source
directories relative to the sysroot. -/
def toolchainLibs (sysroot : FilePath) : Array (Name × FilePath) :=
  #[(`Init, sysroot / "src" / "lean"),
    (`Std, sysroot / "src" / "lean"),
    (`Lean, sysroot / "src" / "lean"),
    (`Lake, sysroot / "src" / "lean" / "lake")]

/--
Snapshot the structural part of a loaded `Lake.Workspace` (see the module docstring).
The `fingerprint` is not computable from the `Workspace` alone; compute it with
`Fingerprint.compute` (as `Lake.Workspace.toWorkspaceInfo` does) or leave it empty.
-/
def WorkspaceInfo.ofWorkspace (ws : Lake.Workspace) (fingerprint : Fingerprint := {}) :
    WorkspaceInfo := Id.run do
  let sysroot := ws.lakeEnv.lean.sysroot
  let toolchainIdx : PkgIdx := ⟨ws.packages.size⟩
  let mut packages : Table PackageInfo PackageInfo := ⟨ws.packages.map fun pkg => {
    name := pkg.baseName
    dir := pkg.dir
    deps := pkg.depPkgs.map (fun dep => ⟨dep.wsIdx⟩) |>.push toolchainIdx
    leanLibDir := pkg.leanLibDir
    defaultTargets := pkg.defaultTargets
  }⟩
  packages := packages.push {
    name := `toolchain
    isToolchain := true
    dir := sysroot
    leanLibDir := sysroot / "lib" / "lean"
  }
  let mut libs : Table LibraryInfo LibraryInfo := ∅
  for pkg in ws.packages do
    for lib in pkg.leanLibs do
      libs := libs.push {
        name := lib.name
        pkg := ⟨pkg.wsIdx⟩
        srcDir := lib.srcDir
        roots := lib.roots
        globs := lib.config.globs
      }
  for (name, srcDir) in toolchainLibs sysroot do
    libs := libs.push {
      name
      pkg := toolchainIdx
      srcDir
      roots := #[name]
      globs := #[.andSubmodules name]
    }
  return {
    dir := ws.dir
    sysroot
    rootConfigFile := ws.root.configFile
    rootManifestFile := ws.root.dir / ws.root.relManifestFile
    fingerprint
    packages
    libs
  }

/-- Snapshot a loaded `Lake.Workspace`, computing its `Fingerprint` from the filesystem. -/
def _root_.Lake.Workspace.toWorkspaceInfo (ws : Lake.Workspace) : IO WorkspaceInfo := do
  let rootManifestFile := ws.root.dir / ws.root.relManifestFile
  let fingerprint ← Fingerprint.compute ws.dir ws.root.configFile rootManifestFile
  return .ofWorkspace ws fingerprint

end ImportGraph
