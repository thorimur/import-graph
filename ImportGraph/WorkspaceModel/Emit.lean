/-
Copyright (c) 2026 Thomas Murrills. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Murrills
-/
module

import Lake.Load.Workspace
import ImportGraph.WorkspaceModel.Summary

/-!
# `lake exe import-graph-workspace-summary`

-- TODO(F): rewrite
-- The entry point of the `import-graph-workspace-summary` executable, which loads the Lake workspace
-- rooted at the current directory (or at the directory given as an argument) and prints its
-- `WorkspaceSummary` data as JSON on stdout. Pass `--pretty` for indented output. Progress and
-- errors go to stderr.

-- This is the acquisition path for consumers that cannot load a Lake workspace in-process —
-- in particular the language server, which does not load Lake's shared library. Because
-- `lean_exe`s link Lake natively, this executable can do what the server cannot; and because
-- `lake exe` resolves executables across all packages of a workspace, any workspace that
-- (transitively) depends on `importGraph` can dump its own structure with
-- `lake exe import-graph-raw`. See `ImportGraph.WorkspaceModel.Build` for the programmatic
-- client.
-/

open Lean ImportGraph Lake

-- TODO: explore making this a lake script or facet, since we're essentially loading the lake
-- workspace twice by calling this with `lake exe`.
public def main (args : List String) : IO UInt32 := do
  let wsDir : System.FilePath ← do
    match args with
    | [] => IO.currentDir
    | [dir] => IO.FS.realPath dir
    | _ => IO.eprintln "Expected either no arguments or a path to a package's root."; return 2
  let (elan?, lean?, lake?) ← findInstall?
  let some lean := lean?
    | IO.eprintln "error: no Lean installation found"; return 1
  -- This executable is not co-located with the toolchain (unlike `lake` itself), so
  -- `findInstall?` cannot always detect the Lake installation; but Lake ships with the
  -- toolchain, so it can be derived from the Lean installation.
  -- TODO(F): review this more thoroughly, I'm skeptical.
  let lake := lake?.getD (.ofLean lean)
  let lakeEnv ← (Env.compute lake lean elan?).toIO (IO.userError ·)
  let cfg : LoadConfig := { lakeEnv, wsDir }
  let (ws?, log) ← (loadWorkspace cfg).run?
  if log.any (·.level matches .error) then
    IO.eprintln s!"error: Errors were produced while loading the Lake workspace at {wsDir}.\n\
      Log:\n{log}"; return 1
  let some ws := ws?
    | IO.eprintln s!"error: Failed to load the Lake workspace at {wsDir}.\n\
        Log:\n{log}"; return 1
  let ver ← ws.getToolchainVer
  let hash ← computeSummaryInputHash ver ws.manifestFile ws.root.configFile
  let json := toJson (WorkspaceSummary.ofWorkspace ws ver hash)
  IO.println json.compress
  return 0
