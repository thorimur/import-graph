/-
Copyright (c) 2026 Thomas Murrills. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Murrills
-/
import ImportGraph.Workspace.Snapshot

/-!
# Fetching a `WorkspaceInfo` from inside a workspace

`fetchWorkspaceInfo` is the acquisition path for consumers — the language server in
particular — that cannot load a Lake workspace in-process (see the docstring of
`ImportGraph.Workspace.Snapshot`):

1. If a cached snapshot exists (at `.lake/importGraph/workspace-info.json`) with a
   matching format version and `Fingerprint`, it is used.
2. Otherwise, `lake exe import-graph-info` is spawned in the workspace directory. Lake
   resolves the executable across all packages of the workspace, so this works from any
   workspace that (transitively) depends on `importGraph` — including `importGraph`
   itself. The result is cached and returned.

Notes:

* The first regeneration in a workspace pays for `lake` building the executable; both
  that build and the subsequent workspace loads are cached by Lake, and the resulting
  snapshot is cached here, so steady-state calls are one file read.
* Fingerprints are a heuristic (they do not observe dependencies' configuration files);
  pass `fresh := true` to force regeneration.
* If the workspace has no manifest yet, the spawned `lake` will resolve dependencies and
  write one, exactly as a first `lake build` would.
-/

open Lean System

namespace ImportGraph

/-- The name of the snapshot-emitting executable provided by `importGraph`
(see `ImportGraph.Workspace.Emit`). -/
def workspaceInfoExe : String := "import-graph-info"

/-- The snapshot cache location for the workspace at `wsDir`. -/
def workspaceInfoCacheFile (wsDir : FilePath) : FilePath :=
  wsDir / ".lake" / "importGraph" / "workspace-info.json"

/--
Environment sanitization for the spawned `lake`: search-path variables inherited from the
spawning process (e.g. the language server) describe *its* setup and must not leak into a
fresh `lake` invocation.
-/
private def sanitizedEnv : Array (String × Option String) :=
  #[("LEAN_PATH", none), ("LEAN_SRC_PATH", none), ("LAKE", none)]

private def parseWorkspaceInfo (source : String) (jsonString : String) :
    IO WorkspaceInfo := do
  let json ← IO.ofExcept <| Json.parse jsonString |>.mapError
    (s!"{source}: invalid JSON: {·}")
  -- Check the format version first, for a clear error on version skew.
  let version ← IO.ofExcept <| json.getObjValAs? Nat "formatVersion" |>.mapError
    (s!"{source}: not a workspace snapshot: {·}")
  unless version == WorkspaceInfo.currentFormatVersion do
    throw <| IO.userError s!"{source}: workspace snapshot has format version {version}, \
      but this consumer expects {WorkspaceInfo.currentFormatVersion} (is the workspace's \
      `importGraph` dependency a different version?)"
  IO.ofExcept <| fromJson? json |>.mapError
    (s!"{source}: malformed workspace snapshot: {·}")

/-- Try to read a cached snapshot with a matching format version and fingerprint. -/
private def readCache? (wsDir : FilePath) : IO (Option WorkspaceInfo) := do
  let cacheFile := workspaceInfoCacheFile wsDir
  unless ← cacheFile.pathExists do return none
  try
    let info ← parseWorkspaceInfo cacheFile.toString (← IO.FS.readFile cacheFile)
    let fingerprint ← Fingerprint.compute wsDir info.rootConfigFile info.rootManifestFile
    if info.fingerprint == fingerprint then
      return some info
    else
      return none
  catch _ =>
    -- A stale or corrupt cache is not an error; it is simply regenerated.
    return none

/--
Obtain the `WorkspaceInfo` of the workspace rooted at `wsDir` (in the language server,
the server process's current directory is the workspace root), using the cache unless
`fresh := true` or the cache is stale; see the module docstring.
-/
def fetchWorkspaceInfo (wsDir : FilePath) (fresh := false) : IO WorkspaceInfo := do
  unless fresh do
    if let some info ← readCache? wsDir then
      return info
  let out ← IO.Process.output {
    cmd := "lake"
    args := #["exe", workspaceInfoExe]
    cwd := wsDir
    env := sanitizedEnv
  }
  unless out.exitCode == 0 do
    throw <| IO.userError s!"`lake exe {workspaceInfoExe}` in `{wsDir}` failed with exit \
      code {out.exitCode}:\n{out.stderr.takeEnd 2000}"
  let info ← parseWorkspaceInfo s!"`lake exe {workspaceInfoExe}`" out.stdout
  let cacheFile := workspaceInfoCacheFile wsDir
  try
    if let some dir := cacheFile.parent then
      IO.FS.createDirAll dir
    IO.FS.writeFile cacheFile out.stdout
  catch _ =>
    pure () -- failing to write the cache should not fail the fetch
  return info

end ImportGraph
