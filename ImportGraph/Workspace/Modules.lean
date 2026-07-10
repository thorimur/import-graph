/-
Copyright (c) 2026 Thomas Murrills. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Murrills
-/
import ImportGraph.Workspace.Snapshot

/-!
# Resolving a workspace's modules

A `WorkspaceInfo` records the *rules* (library `srcDir`s, `roots`, and `globs`) by which
modules are found; this file resolves those rules against the filesystem, producing a
`ModuleTable`: the canonical enumeration of the modules of (a chosen set of libraries of)
the workspace, with

* module name ↔ `ModIdx` in both directions,
* each module's owning library and source file,
* the `IdxSet` of modules of each library.

The table is the index space over which import graphs are built (see
`ImportGraph.Workspace.Scan`); its indices are deterministic (sorted by library, then by
module name), so equal filesystem states yield equal tables.

Everything here is plain filesystem inspection — no Lake loading — so it can run anywhere,
including inside the language server, and can be re-run cheaply to pick up created or
deleted files without regenerating the snapshot.
-/

open Lean System

namespace ImportGraph

/-- One module of a `ModuleTable`: its name, owning library, and source file. -/
structure ModuleInfo where
  /-- The module's name. -/
  name : Name
  /-- The library the module belongs to. (If several libraries claim it, the first in
  library order wins.) -/
  lib : LibIdx
  /-- The module's source file (absolute), i.e. its path under the library's `srcDir`. -/
  srcFile : FilePath
  deriving Repr, Inhabited

/-- A typed index of a module within a `ModuleTable`. -/
abbrev ModIdx := Idx ModuleInfo

/--
The canonical enumeration of the modules of (a chosen set of libraries of) a workspace;
see the module docstring. Build one with `WorkspaceInfo.resolveModules`.
-/
structure ModuleTable where
  /-- The modules, sorted by library, then by module name. -/
  mods : Table ModuleInfo ModuleInfo
  /-- Module name → index. -/
  byName : NameMap ModIdx
  /-- The set of modules of each library. (Libraries outside the resolved set have `∅`.) -/
  byLib : Table LibraryInfo (IdxSet ModuleInfo)
  deriving Inhabited

namespace ModuleTable

@[inline] def size (t : ModuleTable) : Nat := t.mods.size

/-- The full module index set. -/
@[inline] def univ (t : ModuleTable) : IdxSet ModuleInfo := t.mods.univ

instance : GetElem ModuleTable ModIdx ModuleInfo fun t i => i.toNat < t.size where
  getElem t i h := t.mods[i]

@[inline] def get! (t : ModuleTable) (i : ModIdx) : ModuleInfo := t.mods.get! i

/-- The index of the module named `mod`, if it is in the table. -/
@[inline] def find? (t : ModuleTable) (mod : Name) : Option ModIdx := t.byName.find? mod

@[inline] def contains (t : ModuleTable) (mod : Name) : Bool := t.byName.contains mod

/-- The modules of library `lib` (`∅` for libraries outside the resolved set). -/
@[inline] def modsOfLib (t : ModuleTable) (lib : LibIdx) : IdxSet ModuleInfo :=
  t.byLib.get! lib

/-- The `.olean` file of module `i` (see `WorkspaceInfo.oleanFile`). -/
@[inline] def oleanFile (t : ModuleTable) (info : WorkspaceInfo) (i : ModIdx) : FilePath :=
  let m := t.get! i
  info.oleanFile m.lib m.name

end ModuleTable

namespace WorkspaceInfo

/-- The libraries of the Lake packages of the workspace — i.e. all libraries except those
of the toolchain pseudo-package. The usual set to resolve and scan. -/
def lakeLibs (info : WorkspaceInfo) : IdxSet LibraryInfo :=
  info.libs.foldlIdx (init := ∅) fun acc i lib =>
    if (info.packages.get! lib.pkg).isToolchain then acc else acc.insert i

/-- All libraries of the workspace, including the toolchain's `Init`/`Std`/`Lean`/`Lake`.
Resolving the toolchain libraries enumerates several thousand core modules; only include
them when the analysis genuinely needs per-file information about core. -/
def allLibs (info : WorkspaceInfo) : IdxSet LibraryInfo := info.libs.univ

/-- The libraries of the root package. -/
def rootLibs (info : WorkspaceInfo) : IdxSet LibraryInfo :=
  info.libs.foldlIdx (init := ∅) fun acc i lib =>
    if lib.pkg == ⟨0⟩ then acc.insert i else acc

/--
The modules of library `lib` present on the filesystem: every module local to the library
(a submodule of one of its `roots`, or a match of one of its `globs` — the same test as
`isLocalModuleOf`) whose source file exists.

Note that this is the library's *source tree*, which can be a superset of what `lake
build` would build for it: with the default configuration (`globs := roots.map .one`),
Lake builds the *import closure* of the roots, which cannot be known without parsing
sources (see `ImportGraph.Workspace.Scan`) and usually — though not necessarily —
coincides with the source tree. For "where can this declaration live?" questions the
source tree is the honest universe.
-/
private def libModulesOnDisk (info : WorkspaceInfo) (lib : LibIdx) : IO (Array Name) := do
  let l := info.libs.get! lib
  let seen ← IO.mkRef ({} : NameSet)
  let mods ← IO.mkRef (#[] : Array Name)
  let add (n : Name) : IO Unit := do
    unless (← seen.get).contains n do
      seen.modify (·.insert n)
      mods.modify (·.push n)
  let addTree (n : Name) : IO Unit := do
    if ← (modToFilePath l.srcDir n "lean").pathExists then
      add n
    let dir := modToFilePath l.srcDir n ""
    if ← dir.isDir then
      forEachModuleInDir dir fun sub => add (n ++ sub)
  for root in l.roots do
    addTree root
  for glob in l.globs do
    match glob with
    | .one n =>
      if ← (modToFilePath l.srcDir n "lean").pathExists then
        add n
    | .andSubmodules n => addTree n
    | .submodules n =>
      let dir := modToFilePath l.srcDir n ""
      if ← dir.isDir then
        forEachModuleInDir dir fun sub => add (n ++ sub)
  mods.get

/--
Resolve the modules of the given libraries (default: `lakeLibs`) against the filesystem,
producing the canonical `ModuleTable`; see the module docstring.

If several of the given libraries claim the same module name, the first library (in
library order) wins.
-/
def resolveModules (info : WorkspaceInfo) (libs : Option (IdxSet LibraryInfo) := none) :
    IO ModuleTable := do
  let libs := libs.getD info.lakeLibs
  let mut rows : Array ModuleInfo := #[]
  let mut seen : NameSet := {}
  for lib in libs do
    let l := info.libs.get! lib
    for name in ← info.libModulesOnDisk lib do
      unless seen.contains name do
        seen := seen.insert name
        rows := rows.push { name, lib, srcFile := modToFilePath l.srcDir name "lean" }
  -- Sort by library, then by name, so that indices are deterministic.
  rows := rows.qsort fun a b =>
    a.lib < b.lib || (a.lib == b.lib && a.name.quickCmp b.name == .lt)
  let mut byName : NameMap ModIdx := {}
  let mut byLib : Table LibraryInfo (IdxSet ModuleInfo) := .replicate info.libs.size ∅
  for h : i in 0...rows.size do
    let row := rows[i]
    byName := byName.insert row.name ⟨i⟩
    byLib := byLib.modify row.lib (·.insert ⟨i⟩)
  return { mods := ⟨rows⟩, byName, byLib }

/--
The library and module name corresponding to a source file path, determined purely from
the workspace structure (no filesystem access): the path is matched against each library's
`srcDir` (longest match first), and the resulting module name is checked against the
library's `roots`/`globs`.

The path should be absolute (as e.g. `Lean.MessageLog` file names in the server are).
-/
def moduleForPath? (info : WorkspaceInfo) (path : FilePath) : Option (LibIdx × Name) := Id.run do
  let path := path.normalize
  let some path := path.toString.dropSuffix? ".lean" | return none
  let mut best : Option (LibIdx × Name × Nat) := none
  for (i, lib) in info.libs do
    let srcDir := lib.srcDir.normalize.toString
    let some rel := path.dropPrefix? (srcDir ++ FilePath.pathSeparator.toString) | continue
    let mod := rel.toString.splitOn FilePath.pathSeparator.toString
      |>.foldl (init := Name.anonymous) (·.str ·)
    if info.isLocalModuleOf i mod then
      if best.all fun (_, _, len) => srcDir.length > len then
        best := some (i, mod, srcDir.length)
  return best.map fun (i, mod, _) => (i, mod)

end WorkspaceInfo

end ImportGraph
