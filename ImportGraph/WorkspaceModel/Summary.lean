/-
Copyright (c) 2026 Thomas Murrills. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Murrills
-/
module

public import Lake.Config.Workspace
public import Lean.Data.Json
public import ImportGraph.WorkspaceModel.Base

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
abbrev LibrarySummary := BaseLibrary

/-- One package of the workspace, as resolved by Lake. All paths are absolute. -/
structure PackageSummary extends BasePackage where
  /-- The Lake indices of the package's *direct* dependencies (Lake's resolved
  `depPkgs`). -/
  deps : Array Nat
  /-- The package's Lean libraries. -/
  libs : Array LibrarySummary
deriving ToJson, FromJson, Repr, Inhabited

-- TODO: ensure `dir` brings us to package source.

/-- The raw structural data of a Lake workspace; see the module docstring. -/
structure WorkspaceSummary extends BaseWorkspace where
  /-- The packages of the workspace, in Lake's workspace order (root first); each
  package's position is its `lakeIdx`. -/
  packages : Array PackageSummary
deriving ToJson, FromJson, Repr, Inhabited

/-- Extract the hierarchy and path data of a loaded `Lake.Workspace`. -/
def WorkspaceSummary.ofWorkspace (ws : Lake.Workspace) : WorkspaceSummary where
  dir := ws.dir
  sysroot := ws.lakeEnv.lean.sysroot
  packages := ws.packages.map fun pkg => { pkg with
    leanLibDir := pkg.leanLibDir
    deps := pkg.depPkgs.map (·.wsIdx)
    libs := pkg.leanLibs.filterMap fun lib => do
      -- TODO: check we don't need to filter by roots instead? Probably not.
      guard <| pkg.defaultTargets.contains lib.name
      return {
        name := lib.name
        srcDir := lib.srcDir
        roots := lib.roots
        globs := lib.config.globs
      }
  }

/-- The name of the executable with root `ImportGraph.WorkspaceModel.Emit`.
Should be synchronized with the lakefile. -/
def WorkspaceSummary.exeName : String := "import-graph-workspace-summary"

/--
Get the workspace summary by calling out to `lake exe import-graph-workspace-summary`, which emits j
json that this function parses.

This is a workaround for the fact that the language server does not load the lake shared library.
-/
def getWorkspaceSummary (cwd : Option FilePath := none) : IO WorkspaceSummary := do
  let out ← IO.Process.run {
    cmd := "lake"
    args := #["exe", WorkspaceSummary.exeName]
    cwd
    /-
    Search-path variables inherited from the spawning process (e.g. the language server) describe *its* setup and must not leak into a fresh `lake` invocation.
    -- TODO(F): really?
    -/
    env := #[("LEAN_PATH", none), ("LEAN_SRC_PATH", none), ("LAKE", none)] }
  let msgHeader := s!"Failed to get workspace summary"
  let json ← IO.ofExcept <| Json.parse out |>.mapError
    (s!"{msgHeader}: invalid JSON:\n{·}")
  IO.ofExcept <| (fromJson? json : Except String WorkspaceSummary).mapError
    (s!"{msgHeader}: malformed workspace summary JSON:\n{·}")

end ImportGraph.Lake
