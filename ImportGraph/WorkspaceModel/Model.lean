/-
Copyright (c) 2026 Thomas Murrills. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Murrills
-/
module

import Lake
import all ImportGraph.Shake.Basic
import ImportGraph.WorkspaceModel.Base
import all ImportGraph.WorkspaceModel.Daglike
import Lean
public import Lean.Data.Json.FromToJson.Basic

/-!
# The workspace model: three daglikes

A `WorkspaceModel` is the elaborated, bitset-form view of a workspace that `#find_home`
(and friends) query. It consists of three daglikes (see
`ImportGraph.WorkspaceModel.Daglike`) — packages, libraries, and modules — each an `Array`
of object data whose arrow and relational fields are `Bitset`s. Build one from a
`WorkspaceSummary` with `ImportGraph.WorkspaceModel.Build`.

Indexing is *flat*: every library across every package gets one global index, and every
module across every package and library gets one global index. Structural relationships
are recovered from the relational fields (`Package.libs`, `Library.mods`, `Module.pkg`,
…), not from nesting. The bit positions of a `PackageBitset`/`LibraryBitset`/
`ModuleBitset` are exactly the indices into `packages`/`libs`/`mods`. (These abbreviations
are for readability only — nothing stops you from indexing the wrong array; keep track.)

Two conventions:

* **The toolchain is a pseudo-package.** Modules like `Init.Data.Nat` belong to no Lake
  package, but every classification question ("which library is this module in?", "can
  this declaration move to that package?") should have a uniform answer. So `packages`
  ends with one extra entry for the toolchain (recognizable by `lakeIdx? = none`), whose
  libraries are `Init`/`Std`/`Lean`/`Lake`, and every Lake package depends on it. Lake
  packages sit at indices `0, ..., n - 1` in Lake's own order, so model indices agree with
  `lakeIdx` on real packages.

* **Direct is intrinsic, transitive is intrinsic or cached.** Each object carries its
  direct arrows, plus those transitive arrows that are computed during construction anyway
  (`Module.transDeps`, `Module.prevs`). Everything else that is *derived* from the dags —
  importers, depths, transitive package/library dependencies — is computed on demand and
  cached in the model itself; use the `ModelM` accessors (`importedBy`, `modDepths`, …),
  which fill the corresponding `…?` cache field on first use.

Note: this module must be imported via `import all`.
-/

open Lean System ImportGraph Lake Lake.Shake

namespace ImportGraph

/-- A `Bitset` whose bit positions are indices into `WorkspaceModel.packages`. -/
abbrev PackageBitset := Bitset

/-- A `Bitset` whose bit positions are indices into `WorkspaceModel.libs`. -/
abbrev LibraryBitset := Bitset

/-- A `Bitset` whose bit positions are indices into `WorkspaceModel.mods`. -/
abbrev ModuleBitset := Bitset

abbrev LibIdx := Nat
abbrev PkgIdx := Nat
abbrev ModIdx := Nat

namespace WorkspaceModel

/--
One package of the model: a Lake package, or the toolchain pseudo-package (last; see the
module docstring). All paths are absolute.
-/
structure Package extends BasePackage where
  /-- Arrows: the package's *direct* dependencies, as resolved by Lake (plus the
  toolchain pseudo-package). Transitive: `WorkspaceModel.pkgTransDeps`. -/
  deps : PackageBitset
  /-- Relational: the libraries belonging to the package. -/
  libs : LibraryBitset
  /-- Relational: the modules belonging to the package (the union over `libs`). -/
  mods : ModuleBitset
deriving Repr, BEq, Inhabited

/--
One Lean library of the model, including the pseudo-libraries `Init`/`Std`/`Lean`/`Lake`
of the toolchain pseudo-package.
-/
structure Library extends BaseLibrary where
  -- TODO: revealedPkgDeps?
  /-- Arrows: the libraries whose modules this library's modules *directly* import —
  inferred from module imports during construction, so empty for libraries that were not
  enumerated. Not necessarily acyclic: two libraries' modules can interleave even though
  the module graph is a dag. Transitive: `WorkspaceModel.libTransDeps`. -/
  revealedDeps : LibraryBitset
  /-- Relational: the enumerated modules contained *in* the library (found on disk under
  its `roots`/`globs`) — not everything that gets built when the library is built. -/
  mods : ModuleBitset
  /-- Relational: the package the library belongs to. -/
  pkgIdx : PkgIdx
deriving Repr, BEq, Inhabited

/--
One module of the model. Modules enter the model by enumerating the source trees of a
chosen set of libraries (see `ImportGraph.WorkspaceModel.Build`); imports of modules
outside that enumeration remain visible in `imports` but have no bits anywhere.
-/
structure Module extends ModuleHeader where
  /-- The module's name. -/
  name : Name
  /-- The module's source file (absolute). -/
  srcFile : FilePath
  /-- Whether the module has the `prelude` keyword (and hence no implicit `Init`
  imports). -/
  isPrelude : Bool
  -- /-- Arrows: `imports` as a `Needs`. -/
  -- deps : Needs := .empty
  /-- Arrows: Transitive dependencies in the module system.  -/
  transDeps : Needs
  /-- Arrows: Every module that must be built before the current module. -/
  prevs : ModuleBitset
  /-- The transitively reachable libraries this depends on. -/
  transLibDeps : LibraryBitset
  /-- The transitively reachable packages this depends on. -/
  transPkgDeps : PackageBitset
  /-- Relational: The library this module belongs to. -/
  libIdx : LibIdx
  -- TODO: technically we can get this from the library.
  /-- Relational: the package the module belongs to. Redundant, but we store it here for
  convenience. -/
  pkgIdx : PkgIdx
  -- TODO: some more data on library and package?
deriving Inhabited

end WorkspaceModel

-- TODO: move
public instance : ToJson UInt32 where
  toJson uint := uint.toNat

public instance : FromJson UInt32 where
  fromJson? uint := fromJson? (α := Nat) uint |>.map .ofNat

deriving instance ToJson, FromJson, Repr for IO.Error

inductive WorkspaceModel.Error where
  | readImportsFailure (mod : Name) (modPath : System.FilePath) (ioError : IO.Error) : Error
  | noLibOfModule (mod : Name)
deriving Repr, Inhabited, ToJson, FromJson

/-- The elaborated, bitset-form view of a workspace; see the module docstring. Build one
with `WorkspaceModel.load` (or `WorkspaceModel.ofRaw`) from `ImportGraph.WorkspaceModel.Build`. -/
structure WorkspaceModel extends BaseWorkspace where
  /-- The packages: Lake packages in Lake's order, with the toolchain "package" last. The index in this array is the index used in `PackageBitset`s. -/
  packages : Array WorkspaceModel.Package
  /-- The libraries of all packages, flat, in package order (toolchain libraries last). The index of the library in this array matches its index in `LibraryBitset`s. -/
  libs : Array WorkspaceModel.Library
  /-- The enumerated modules, flat, in some topological order, with imported modules coming first
  and the modules that import them afterwards. The index of a module in this array matches the index in `ModuleBitset`s. -/
  mods : Array WorkspaceModel.Module
  /-- Module name → module index. -/
  idxOfMod : Std.HashMap Name ModIdx
  -- /-- A topological order of `mods`: every module appears before everything it imports. -/
  -- topo : Array Nat
  -- TODO: eeeehhh, really, they probably shouldn't be in the module.
  -- /-- Modules whose source could not be read or whose header could not be parsed, with
  -- the error message. (Such modules stay in the model, with empty `imports`.) -/
  errors : Array WorkspaceModel.Error := #[]
  -- TODO: don't need this yet, nice in the future
  -- /-- Cache: the transpose of the module import dag (see `importedBy`). -/
  -- exported? : Option (Array ModuleBitset) := none
  /-- Cache: module depths per library. Built incrementally. -/
  modDepths : Std.HashMap (Name × LibIdx) Nat := {}
  /-- Cache: transitive package dependencies (see `pkgTransDeps`). -/
  pkgTransDeps? : Option (Array PackageBitset) := none
  /-- Cache: transitive library dependencies (see `libTransDeps`). -/
  libTransDeps? : Option (Array LibraryBitset) := none
deriving Inhabited

namespace WorkspaceModel

-- /-- The model computations' monad: a `WorkspaceModel` in state, so that derived data can
-- be cached (see the module docstring). Run with `StateT.run`, or against a stored model
-- with `modifyGet`-style adapters. -/
-- abbrev ModelM := StateM WorkspaceModel

/-! ## Lookups -/

variable (m : WorkspaceModel)

/-- The index of the toolchain pseudo-package (the last package). -/
def toolchainPkgIdx : PkgIdx := m.packages.size - 1

/-- The index of the module named `mod`, if it is in the model. -/
@[inline] def getModIdx? (mod : Name) : Option ModIdx := m.idxOfMod[mod]?

-- TODO: Linear scans are fine, for now. But maybe that should change if we do a lot.

/-- The index of the package with original name `name`, if any. -/
@[inline] def getPkgIdx? (origName : Name) : Option PkgIdx :=
  m.packages.findIdx? (·.origName == origName)

/-- The index of the library named `name`, if any. (Library names are not necessarily
unique across packages, so we ask for the package index as well.) -/
@[inline] def getLibIdx? (pkgIdx : PkgIdx) (libName : Name) : Option LibIdx :=
  m.libs.findIdx? fun lib => lib.pkgIdx == pkgIdx && lib.name == libName

@[inline] def getMod! (modIdx : ModIdx) : Module  := m.mods[modIdx]!
@[inline] def getLib! (libIdx : LibIdx) : Library := m.libs[libIdx]!
@[inline] def getPkg! (pkgIdx : PkgIdx) : Package := m.packages[pkgIdx]!

@[inline] def libOfMod! (mod : Module) : Library := m.getLib! mod.libIdx
@[inline] def pkgOfMod! (mod : Module) : Package := m.getPkg! mod.pkgIdx
@[inline] def pkgOfLib! (lib : Library) : Package := m.getPkg! lib.pkgIdx

@[inline] def libIdxOfModIdx! (modIdx : ModIdx) : LibIdx := m.getMod! modIdx |>.libIdx
@[inline] def pkgIdxOfModIdx! (modIdx : ModIdx) : PkgIdx := m.getMod! modIdx |>.pkgIdx
@[inline] def pkgIdxOfLibIdx! (libIdx : LibIdx) : PkgIdx := m.getLib! libIdx |>.pkgIdx

/-! ## Lake lifts -/

/-- `LeanLib.isLocalModule`, but lifted to `WorkspaceModel.Library`. -/
def Library.isLocalModule (l : Library) (mod : Name) : Bool :=
  l.roots.any (·.isPrefixOf mod) || l.globs.any (·.matches mod)

def rawLibIdxOfMod? (libs : Array WorkspaceModel.Library) (mod : Name) : Option LibIdx :=
  libs.findIdx? (·.isLocalModule mod)

@[inline] def libIdxOfMod? (mod : Name) : Option LibIdx :=
  m.libs.findIdx? (·.isLocalModule mod)

/-- Like `Lake.Module.leanLibFile`, but for `WorkspaceModel.Module`. -/
def Module.leanLibFile (mod : Module) (ext : String) : FilePath :=
  modToFilePath (m.pkgOfMod! mod).leanLibDir mod.name ext

def Library.srcPathOfMod (lib : Library) (mod : Name) : FilePath :=
  modToFilePath lib.srcDir mod "lean"

def srcPathOfMod? (mod : Name) : Option FilePath :=
  m.libIdxOfMod? mod |>.map (modToFilePath m.libs[·]!.srcDir mod "lean")

def Module.srcPath (mod : Module) : FilePath :=
  modToFilePath (m.libOfMod! mod).srcDir mod.name "lean"


-- /--
-- The index of the module whose source file is `path` (absolute, as e.g. server file names
-- are), determined by matching `path` against the libraries' `srcDir`s — no filesystem
-- access. `none` if the path lies under no library, or resolves to a module that was not
-- enumerated.
-- -/
-- def moduleForPath? (m : WorkspaceModel) (path : FilePath) : Option Nat := Id.run do
--   let path := path.normalize
--   let some path := path.toString.dropSuffix? ".lean" | return none
--   for l in m.libs do
--     let srcDir := l.srcDir.normalize.toString
--     let some rel := path.dropPrefix? (srcDir ++ FilePath.pathSeparator.toString) | continue
--     let mod := rel.toString.splitOn FilePath.pathSeparator.toString
--       |>.foldl (init := Name.anonymous) (·.str ·)
--     if let some i := m.getModIdx? mod then
--       return some i
--   return none

/-! ## Derived, cached data

Each accessor computes its result from the dags on first use and stores it in the model's
corresponding `…?` field.
-/

-- TODO(F): Nah. We should alter WorkspaceModels. And the caches should be partial, probably. Hashmaps.

-- /-- The direct arrow data of the module daglike (row `i` is `mods[i].deps`). -/
-- def modDeps (m : WorkspaceModel) : Array ModuleBitset := m.mods.map (·.deps)

-- /-- The transpose of the module import dag: `(← importedBy)[i]` is the set of modules
-- that *directly* import `i`. -/
-- def importedBy : ModelM (Array ModuleBitset) := do
--   if let some r := (← get).importedBy? then return r
--   let r := Daglike.transpose (← get).modDeps
--   modify fun m => { m with importedBy? := some r }
--   return r



-- /-- The depth of each module: the length of the longest import chain below it (sinks such
-- as `Init.Prelude` have depth `0`). -/
-- def modDepths : ModelM (Array Nat) := do
--   if let some r := (← get).modDepths? then return r
--   let m ← get
--   let r := Daglike.depthsOfTopo m.modDeps m.topo
--   modify fun m => { m with modDepths? := some r }
--   return r

-- /-- The transitive package dependencies: `(← pkgTransDeps)[p]` is every package reachable
-- from `p` through `Package.deps`. -/
-- def pkgTransDeps : ModelM (Array PackageBitset) := do
--   if let some r := (← get).pkgTransDeps? then return r
--   let r := Daglike.closure ((← get).packages.map (·.deps))
--   modify fun m => { m with pkgTransDeps? := some r }
--   return r

-- /-- The transitive library dependencies: `(← libTransDeps)[l]` is every library reachable
-- from `l` through `Library.deps` — which includes `l` itself iff `l` lies on a dependency
-- cycle. -/
-- def libTransDeps : ModelM (Array LibraryBitset) := do
--   if let some r := (← get).libTransDeps? then return r
--   let r := Daglike.closure ((← get).libs.map (·.deps))
--   modify fun m => { m with libTransDeps? := some r }
--   return r

-- /-! ## Module queries -/

-- /-- Everything the module at index `i` transitively imports is `mods[i].prevs`; this is
-- its complement: the modules that transitively import `i` (computed against `importedBy`). -/
-- def below (i : Nat) (includeSelf := false) : ModelM ModuleBitset := do
--   let r := Daglike.reachable (← importedBy) {i}
--   return if includeSelf then r else r.erase i

-- /-- The modules that do *not* transitively import `i` (and are not `i` itself): the
-- candidate destinations when moving a declaration out of `i` without creating an import
-- cycle. -/
-- def notBelow (i : Nat) : ModelM ModuleBitset := do
--   return Bitset.univ (← get).mods.size \ (← below i (includeSelf := true))

/-! ## Revealed structure -/

-- /-- The package dependencies *revealed* by actual module imports: `(revealedPkgDeps m)[p]`
-- is the set of packages (other than `p`) whose modules are directly imported by modules of
-- `p`. A subset of what `pkgTransDeps` allows — useful for spotting dependencies a workspace
-- declares but does not use, or uses only transitively. -/
-- def revealedPkgDeps (m : WorkspaceModel) : Array PackageBitset := Id.run do
--   let mut r : Array PackageBitset := .replicate m.packages.size ∅
--   for mod in m.mods do
--     let mut tgts : PackageBitset := ∅
--     for j in mod.deps do
--       tgts := insert m.mods[j]!.pkg tgts
--     r := r.modify mod.pkg (· ∪ tgts.erase mod.pkg)
--   return r

end WorkspaceModel

end ImportGraph
