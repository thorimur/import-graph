/-
Copyright (c) 2026 Thomas Murrills. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Murrills
-/
import Lean.Elab.ParseImportsFast
import ImportGraph.Workspace.Modules
import ImportGraph.Workspace.Dag

/-!
# Scanning imports from source

Given a `ModuleTable`, this file parses module headers from source files (with
`Lean.parseImports'`, the fast header parser) and assembles a `ModuleGraph`: the parsed
headers plus the in-table import `Dag`.

Two scanning modes cover the two restrictions `#find_home`-style analyses need:

* `scanModules` parses all (or a given subset of) the table's modules. A full scan is what
  supports *downward* questions — "what lies below this module?" (`below`, `notBelow`) —
  since knowing a module's importers requires having looked at every candidate importer.

* `scanAbove` parses only the modules reachable by imports from a set of start modules,
  discovering files as it goes. This is the cheap mode for *upward* questions — "what does
  this module transitively import?" — e.g. for analyzing the current file against only the
  modules above it.

Headers are retained in full (`Lean.ModuleHeader`), so flags of the module system
(`public`/`meta`/`all` imports, `isModule`) remain available for finer-grained analyses;
the `Dag` itself is flag-agnostic, with one edge per in-table import.
-/

open Lean System

namespace ImportGraph

/--
Parsed headers over a `ModuleTable`, with the in-table import graph. Produced by
`scanModules` or `scanAbove`.
-/
structure ModuleGraph where
  /-- The module enumeration this graph is built over. -/
  table : ModuleTable
  /-- The modules whose headers were parsed. Rows outside this set are empty. -/
  scanned : IdxSet ModuleInfo
  /-- The parsed header of each scanned module. -/
  headers : Table ModuleInfo ModuleHeader
  /-- The import graph: an edge `i → j` for each import of `j` in the header of `i` (with
  `j` in the table; see `foreignImports` for the rest). -/
  imports : Dag ModuleInfo
  /-- Modules whose source could not be read or parsed, with the error message. -/
  errors : Array (ModIdx × String) := #[]

namespace ModuleGraph

/-- The imports of `i` that are not modules of the table (e.g. imports of toolchain
modules when the toolchain libraries were not resolved). -/
def foreignImports (g : ModuleGraph) (i : ModIdx) : Array Import :=
  (g.headers.get! i).imports.filter (!g.table.contains ·.module)

/--
Everything `i` transitively imports (within the table).

Only meaningful if the modules above `i` have been scanned (`scanAbove` from `i`, or a
full `scanModules`).
-/
def above (g : ModuleGraph) (i : ModIdx) (includeSelf := false) : IdxSet ModuleInfo :=
  g.imports.reachable {i} (includeInit := includeSelf)

/-- The transpose of `imports`: an edge `j → i` for each import of `j` by `i`. Compute
once and reuse for repeated `below`-style queries. -/
def importers (g : ModuleGraph) : Dag ModuleInfo := g.imports.transpose

/--
Everything that transitively imports `i` (within the scanned modules) — computed against
`importers`, which the caller supplies (`g.importers`) so it can be reused across queries.

Only meaningful after a full scan: an unscanned module's imports are unknown, so it cannot
be ruled out as an importer.
-/
def below (_g : ModuleGraph) (importers : Dag ModuleInfo) (i : ModIdx)
    (includeSelf := false) : IdxSet ModuleInfo :=
  importers.reachable {i} (includeInit := includeSelf)

/--
The scanned modules that do *not* transitively import `i` (and are not `i` itself): the
candidate destinations when moving a declaration out of `i` without creating an import
cycle. See `below` for the `importers` parameter and the full-scan requirement.
-/
def notBelow (g : ModuleGraph) (importers : Dag ModuleInfo) (i : ModIdx) :
    IdxSet ModuleInfo :=
  g.scanned \ below g importers i (includeSelf := true)

end ModuleGraph

/-- Parse the header of the source file of module `i`. -/
private def parseHeaderOf (t : ModuleTable) (i : ModIdx) : IO ModuleHeader := do
  let m := t.get! i
  Lean.parseImports' (← IO.FS.readFile m.srcFile) m.srcFile.toString

/-- Parse the headers of `mods`, in parallel chunks of `chunkSize`. -/
private def parseHeaders (t : ModuleTable) (mods : Array ModIdx) (chunkSize : Nat) :
    IO (Array (ModIdx × Except String ModuleHeader)) := do
  let chunkSize := max 1 chunkSize
  let mut tasks := #[]
  let mut start := 0
  while start < mods.size do
    let chunk := mods.extract start (start + chunkSize)
    tasks := tasks.push <|← IO.asTask <| chunk.mapM fun i => do
      let hdr ← try .ok <$> parseHeaderOf t i catch e => pure (.error (toString e))
      pure (i, hdr)
    start := start + chunkSize
  let mut results := #[]
  for task in tasks do
    results := results ++ (← IO.ofExcept task.get)
  return results

/-- Assemble a `ModuleGraph` from parse results, adding them to `g₀` (used as the
accumulator both for full scans, starting from `emptyGraph`, and for the layered BFS of
`scanAbove`). -/
private def addResults (g₀ : ModuleGraph)
    (results : Array (ModIdx × Except String ModuleHeader)) : ModuleGraph := Id.run do
  let mut g := g₀
  for (i, res) in results do
    match res with
    | .error e =>
      g := { g with errors := g.errors.push (i, e), scanned := g.scanned.insert i }
    | .ok hdr =>
      let mut edges : IdxSet ModuleInfo := ∅
      for imp in hdr.imports do
        if let some j := g.table.find? imp.module then
          edges := edges.insert j
      g := { g with
        scanned := g.scanned.insert i
        headers := g.headers.set i hdr
        imports := ⟨g.imports.succs.set i edges⟩ }
  return g

/-- The `ModuleGraph` over `t` with nothing scanned. -/
def emptyGraph (t : ModuleTable) : ModuleGraph where
  table := t
  scanned := ∅
  headers := .replicate t.size { imports := #[], isModule := false }
  imports := .empty t.size

/--
Parse the headers of `mods` (default: the whole table) and build the resulting
`ModuleGraph`. Parsing is parallelized in chunks of `chunkSize`.

Failures to read or parse individual files do not abort the scan; they are recorded in
`ModuleGraph.errors` (and the failed modules count as scanned, with empty headers).
-/
def scanModules (t : ModuleTable) (mods : Option (IdxSet ModuleInfo) := none)
    (chunkSize : Nat := 64) : IO ModuleGraph := do
  let mods := (mods.getD t.univ).toArray
  return addResults (emptyGraph t) (← parseHeaders t mods chunkSize)

/--
Scan upward from `start`: parse the headers of the start modules, then of their in-table
imports, and so on — touching only files at or above the start set in the import
hierarchy. See the module docstring for when this suffices.
-/
def scanAbove (t : ModuleTable) (start : IdxSet ModuleInfo) (chunkSize : Nat := 64) :
    IO ModuleGraph := do
  let mut g := emptyGraph t
  let mut frontier := start
  while !frontier.isEmpty do
    g := addResults g (← parseHeaders t frontier.toArray chunkSize)
    let mut next : IdxSet ModuleInfo := ∅
    for i in frontier do
      next := next ∪ g.imports.succsOf i
    frontier := next \ g.scanned
  return g

end ImportGraph
