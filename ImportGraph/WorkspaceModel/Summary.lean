/-
Copyright (c) 2026 Thomas Murrills. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Murrills
-/
module

public import Lake.Config.Workspace
public import Lean.Data.Json

/-!
# Raw workspace data

-- The structural facts `#find_home` (and friends) need about a workspace are all known to
-- Lake, but *loading* a Lake workspace requires elaborating `lakefile.lean` configurations,
-- which needs Lake's native code in-process — and the language server does not load Lake's
-- shared library.

-- This file defines `WorkspaceSummary`: the JSON payload that crosses the process boundary. It
-- is deliberately *raw* — the easily-inspectable, intrinsic facts of the workspace exactly
-- as Lake reports them (package names, Lake indices, paths, targets, dependencies by Lake
-- index, and each package's libraries with their roots and globs), with no derived data: no
-- index choices of our own, no bitsets, no pseudo-entities. All of that is the consumer's
-- business (see `ImportGraph.WorkspaceModel.Build`, which elaborates a payload into the
-- bitset-form `WorkspaceModel`).

-- Produce a payload with `WorkspaceSummary.ofWorkspace` wherever workspace loading works — the
-- `import-graph-raw` executable (`ImportGraph.WorkspaceModel.Emit`), or any facet or script
-- with a `Lake.Workspace` in hand.
-/

public section

open Lean System Lake

namespace ImportGraph.Lake

deriving instance ToJson, FromJson for Lake.Glob

/-- One Lean library (`lean_lib`) of a package, as configured: its name and the rule
(`srcDir`, `roots`, `globs`) by which its modules are found. -/
structure LibrarySummary where
  /-- The library's name. -/
  name : Name
  /-- The directory relative to which the library's module names locate source files
  (absolute). -/
  srcDir : FilePath
  /-- The library's root module names. -/
  roots : Array Name
  /-- The globs specifying the library's buildable modules. -/
  globs : Array Lake.Glob
deriving ToJson, FromJson, Inhabited

/-- One package of the workspace, as resolved by Lake. All paths are absolute. -/
structure PackageSummary where
  /-- The package's assigned name (`Package.baseName`). -/
  baseName : Name
  /-- The package's original name (`Package.origName`). -/
  origName : Name
  /-- Lake's index for the package (`Package.wsIdx`), which is also its position in
  `WorkspaceSummary.packages`. Together with `name`, this disambiguates packages. -/
  wsIdx : Nat
  /-- The package's root directory (absolute). -/
  dir : FilePath
  /-- The directory holding the package's compiled module artifacts (`.olean`s etc.),
  e.g. `<dir>/.lake/build/lib/lean`. -/
  leanLibDir : FilePath
  /-- The Lake indices of the package's *direct* dependencies (Lake's resolved
  `depPkgs`). -/
  deps : Array Nat
  /-- The package's Lean libraries. -/
  libs : Array LibrarySummary
deriving ToJson, FromJson, Inhabited

-- TODO: ensure `dir` brings us to package source.

/-- The raw structural data of a Lake workspace; see the module docstring. -/
structure WorkspaceSummary where
  /-- The workspace root directory (absolute). -/
  dir : FilePath
  /-- The Lean toolchain's sysroot (absolute). -/
  sysroot : FilePath
  /-- The packages of the workspace, in Lake's workspace order (root first); each
  package's position is its `lakeIdx`. -/
  packages : Array PackageSummary
deriving ToJson, FromJson, Inhabited

/-- Extract the hierarchy and path data of a loaded `Lake.Workspace`. -/
def WorkspaceSummary.ofWorkspace (ws : Lake.Workspace) : WorkspaceSummary where
  dir := ws.dir
  sysroot := ws.lakeEnv.lean.sysroot
  packages := ws.packages.map fun pkg => { pkg with
    leanLibDir := pkg.leanLibDir
    deps := pkg.depPkgs.map (·.wsIdx)
    libs := pkg.leanLibs.map fun lib => {
      name := lib.name
      srcDir := lib.srcDir
      roots := lib.roots
      globs := lib.config.globs
    }
  }

end ImportGraph.Lake
