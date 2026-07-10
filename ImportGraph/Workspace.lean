/-
Copyright (c) 2026 Thomas Murrills. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Murrills
-/
import ImportGraph.Workspace.Index
import ImportGraph.Workspace.Dag
import ImportGraph.Workspace.Snapshot
import ImportGraph.Workspace.Modules
import ImportGraph.Workspace.Scan
import ImportGraph.Workspace.Fetch
-- `ImportGraph.Workspace.Emit` is deliberately not imported: it is the root module of the
-- `import-graph-info` executable and declares `main`.

/-!
# Workspace structure, module resolution, and source-level import graphs

This directory provides the structural substrate for import analyses like `#find_home`:
what a workspace's packages and libraries are, how they depend on each other, where any
module's source and `.olean` live, and what the source-level import graph looks like —
available *anywhere*, including inside the language server (where Lake workspaces cannot
be loaded in-process, since Lake's shared library is not loaded there).

## Architecture

The pipeline is split so that the part requiring Lake is minimal, serializable, and
runs out of process, while everything else is plain filesystem inspection:

1. **`Snapshot`** (`WorkspaceInfo`): a plain-data, JSON-round-tripping snapshot of a
   workspace's structure — packages (with their dependency DAG and artifact directories)
   and libraries (with their `srcDir`/`roots`/`globs` module rules). The toolchain appears
   as a final pseudo-package with libraries `Init`/`Std`/`Lean`/`Lake`, so every module
   name can be classified uniformly (`owningLibs`, `owningPackages`, `moduleForPath?`).
   Module *lists* are deliberately not part of a snapshot; only the rules are, so a
   snapshot survives file creation/deletion and is invalidated (via `Fingerprint`) only by
   configuration changes.

2. **`Emit`** (`lake exe import-graph-info`): the out-of-process producer. A `lean_exe`
   links Lake natively, so it can do what the server cannot: load the workspace and print
   its `WorkspaceInfo` as JSON. Any workspace depending on `importGraph` can snapshot
   itself this way. (`Lake.Workspace.toWorkspaceInfo` is also available directly, for
   facets/scripts that already hold a `Lake.Workspace`.)

3. **`Fetch`** (`fetchWorkspaceInfo`): the consumer side — returns the cached snapshot
   (`.lake/importGraph/workspace-info.json`) when its fingerprint still matches, and
   otherwise spawns `lake exe import-graph-info` and caches the result.

4. **`Modules`** (`WorkspaceInfo.resolveModules` → `ModuleTable`): resolves the module
   rules of a chosen set of libraries against the filesystem, yielding the canonical
   (deterministically ordered) enumeration of modules — name ↔ index, owning library,
   source file, per-library module sets — plus `.olean` lookup via the owning package.

5. **`Scan`** (`scanModules`/`scanAbove` → `ModuleGraph`): parses module headers (fast
   header parser, parallel chunks, full module-system flags retained) into an import
   `Dag` over the table. `scanAbove` touches only files above the start modules (enough
   for "what do I import?"); a full scan supports `below`/`notBelow` ("who imports me?",
   "where could I move?").

All of this sits on two generic layers:

* **`Index`**: `Idx α` / `IdxSet α` / `Table α β` — phantom-typed indices, `Nat`-bitmask
  sets, and array-backed total maps, so that package/library/module index spaces cannot be
  confused while everything compiles down to `Nat` and `Array` operations.

* **`Dag`**: directed graphs as tables of successor `IdxSet`s — transpose, reachability,
  topological order, transitive closure/reduction, heights.

## Typical use (in-server)

```lean
let info ← fetchWorkspaceInfo (← IO.currentDir)   -- cached after the first call
let table ← info.resolveModules                    -- lake libraries, fresh from disk
let g ← scanModules table                          -- full scan; or `scanAbove` from a file
let some (lib, mod) := info.moduleForPath? path | ...
let some i := table.find? mod | ...
let candidates := g.notBelow g.importers i         -- modules that don't import `i`
```
-/
