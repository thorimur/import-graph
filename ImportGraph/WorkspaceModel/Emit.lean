/-
Copyright (c) 2026 Thomas Murrills. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Murrills
-/
module

import Lake
import Lake.Load
import all ImportGraph.WorkspaceModel.Raw

/-!
# `lake exe import-graph-raw`

The entry point of the `import-graph-raw` executable, which loads the Lake workspace
rooted at the current directory (or at the directory given as an argument) and prints its
`WorkspaceSummary` data as JSON on stdout. Pass `--pretty` for indented output. Progress and
errors go to stderr.

This is the acquisition path for consumers that cannot load a Lake workspace in-process —
in particular the language server, which does not load Lake's shared library. Because
`lean_exe`s link Lake natively, this executable can do what the server cannot; and because
`lake exe` resolves executables across all packages of a workspace, any workspace that
(transitively) depends on `importGraph` can dump its own structure with
`lake exe import-graph-raw`. See `ImportGraph.WorkspaceModel.Build` for the programmatic
client.
-/

open Lean Lake System ImportGraph

private def usage : String :=
  "usage: import-graph-raw [--pretty] [dir]

Loads the Lake workspace rooted at `dir` (default: the current directory) and
prints its raw structure (packages, dependencies, libraries) as JSON on stdout."

public def main (args : List String) : IO UInt32 := do
  let wsDir : FilePath ← do
    match args with
    | [] => IO.currentDir
    | [dir] => IO.FS.realPath dir
    | _ => IO.eprintln usage; return 2
  let (elan?, lean?, lake?) ← findInstall?
  let some lean := lean?
    | IO.eprintln "error: no Lean installation found"; return 1
  -- This executable is not co-located with the toolchain (unlike `lake` itself), so
  -- `findInstall?` cannot always detect the Lake installation; but Lake ships with the
  -- toolchain, so it can be derived from the Lean installation.
  let lake := lake?.getD (.ofLean lean)
  let lakeEnv ← (Env.compute lake lean elan?).toIO (IO.userError ·)
  let cfg : LoadConfig := { lakeEnv, wsDir }
  let some ws ← (loadWorkspace cfg).run?' fun entry =>
      (IO.eprintln entry.toString).catchExceptions fun _ => pure ()
    | IO.eprintln s!"error: failed to load the Lake workspace at {wsDir}"; return 1
  let json := toJson (WorkspaceSummary.ofWorkspace ws)
  IO.println json.compress
  return 0
