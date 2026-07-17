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
  /-- The hash of inputs to this workspace summary: the lakefile, the lake manifest, and the
  toolchain version. -/
  inputHash : Hash
deriving ToJson, FromJson, Repr, Inhabited

deriving instance Hashable for SemVerCore
deriving instance Hashable for StdVer
deriving instance Hashable for LeanVer
deriving instance Hashable for Date
deriving instance Hashable for ToolchainVer

def _root_.Lake.Workspace.getToolchainVer (ws : Lake.Workspace) : IO ToolchainVer := do
  let some ver ← ToolchainVer.ofDir? ws.dir
    | throw (.userError s!"Could not find toolchain file in {ws.dir}")
  return ver

def computeSummaryInputHash (ver : ToolchainVer)
    (manifestFile rootConfigFile : System.FilePath) : IO Hash := do
  let hash := Hash.ofHashable ver
  let hash := hash.mix <|← Hash.ofText <$> IO.FS.readFile manifestFile
  return hash.mix <|← Hash.ofText <$> IO.FS.readFile rootConfigFile

def WorkspaceSummary.isUpToDate (ws : WorkspaceSummary) : IO Bool := do
  let some newVer ← ToolchainVer.ofDir? ws.dir
    | throw (.userError s!"Could not find toolchain file in {ws.dir}")
  let newHash ← computeSummaryInputHash newVer ws.manifestFile ws.rootConfigFile
  return newHash == ws.inputHash

/-- Extract the hierarchy and path data of a loaded `Lake.Workspace`. -/
def WorkspaceSummary.ofWorkspace (ws : Lake.Workspace)
    (version : ToolchainVer) (inputHash : Hash) : WorkspaceSummary where
  dir := ws.dir
  sysroot := ws.lakeEnv.lean.sysroot
  version := version
  inputHash
  manifestFile := ws.manifestFile
  rootConfigFile := ws.root.configFile
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

-- TODO: surely this must be somewhere
def lakeDirPath (wsDir : Option FilePath) : IO System.FilePath :=
  return (← wsDir.getDM IO.currentDir) / ".lake"

def importGraphBuildDirPath (lakeFolderPath : System.FilePath) : System.FilePath :=
  lakeFolderPath / "importGraph"

def cachePath (importGraphBuildDirPath : System.FilePath) : System.FilePath :=
  importGraphBuildDirPath / "workspace-summary.json"

open System (FilePath)

-- TODO: think about this more, this is from claude.
/-- Atomically write `content` to `path` via a sibling temp file + rename. -/
def atomicWriteFileViaTempSibling (path : FilePath) (content : String) : IO Unit := do
  let dir := path.parent.getD "."
  IO.FS.createDirAll dir
  -- Unique temp name IN THE SAME DIRECTORY, so the rename stays on one filesystem.
  let stamp ← IO.monoNanosNow
  let tmp := dir / s!"{path.fileName.getD "cache"}.{stamp}.tmp"
  try
    IO.FS.writeFile tmp content   -- open, write, deterministic close+flush
    IO.FS.rename tmp path         -- atomic same-fs replace
  catch e =>
    try IO.FS.removeFile tmp catch _ => pure ()  -- best-effort cleanup
    throw e

/--
Get the workspace summary by calling out to `lake exe import-graph-workspace-summary`, which emits j
json that this function parses.

This is a workaround for the fact that the language server does not load the lake shared library.
-/
def getWorkspaceSummary (wsDir : Option FilePath := none) : IO WorkspaceSummary := do
  dbg_trace s!"current time: {← IO.monoMsNow}"
  let lakeDirPath ← lakeDirPath wsDir
  unless ← lakeDirPath.isDir do
    throw (.userError "Could not find `.lake` folder at {lakeFolderPath}")
  let importGraphBuildDirPath := importGraphBuildDirPath lakeDirPath
  let cachePath := cachePath importGraphBuildDirPath
  if ← cachePath.pathExists then
    let ws ← jsonOfString s!"Failed to get workspace summary from cache file at {cachePath}"
      (← IO.FS.readFile cachePath)
    if ← ws.isUpToDate then
      return ws
  let { stdout := out, stderr, exitCode } ← IO.Process.output {
    cmd := "lake"
    args := #["exe", WorkspaceSummary.exeName]
    cwd := wsDir
    /-
    Search-path variables inherited from the spawning process (e.g. the language server) describe *its* setup and must not leak into a fresh `lake` invocation.
    -- TODO(F): really?
    -/
    env := #[("LEAN_PATH", none), ("LEAN_SRC_PATH", none), ("LAKE", none)] }
  if exitCode != 0 then throw (.userError "broke!")
  dbg_trace s!"Logs:{stderr}"
  -- Note: `.lake` is expected to still exist from the earlier check
  IO.FS.createDirAll importGraphBuildDirPath
  atomicWriteFileViaTempSibling cachePath out -- TODO: potentially do this more...atomically?
  jsonOfString "Failed to get workspace summary" out
where jsonOfString msgHeader str : IO WorkspaceSummary := do
  let json ← IO.ofExcept <| Json.parse str |>.mapError
    (s!"{msgHeader}: invalid JSON:\n{·}")
  IO.ofExcept <| (fromJson? json : Except String WorkspaceSummary).mapError
    (s!"{msgHeader}: malformed workspace summary JSON:\n{·}")

end ImportGraph.Lake
