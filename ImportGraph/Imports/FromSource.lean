/-
Copyright (c) 2025 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import Lean.Elab.ParseImportsFast

/-!
# Source-File-Based Import Analysis

This module provides functions for analyzing imports by parsing source files directly,
as an alternative to the Environment-based functions in `ImportGraph.Imports`.

## Functions

- `findImportsFromSource`: Parse direct imports from a single file
- `findTransitiveImportsFromSource`: Compute transitive closure of imports from source files
-/

open Lean System

/--
Parse all imports in a source file at `path` and return their module names.

This is a thin wrapper around `Lean.parseImports'` that:
- Reads the file from disk
- Parses the import statements
- Filters out `Init` (part of the prelude)

Note: This only sees syntactic imports in the source file.
It does not account for what declarations are actually used.
-/
public def findImportsFromSource (path : System.FilePath) : IO (Array Name) := do
  -- Note: we use `filter` rather than `erase`, since module-system files may contain
  -- both an implicit `public import Init` and a `meta import Init`, so `Init` can
  -- appear more than once in the parsed imports.
  return (← Lean.parseImports' (← IO.FS.readFile path) path.toString).imports
    |>.map (·.module) |>.filter (· != `Init)

/--
Compute the transitive closure of imports starting from a source file.

Returns a `NameSet` of all modules that are transitively imported by the given file,
by recursively parsing source files.

**Example:**
```lean
-- Get all transitive Mathlib imports
let imports ← findTransitiveImportsFromSource "Mathlib/Algebra/Ring/Basic.lean" (some `Mathlib)

-- Get all transitive imports regardless of namespace
let allImports ← findTransitiveImportsFromSource "MyFile.lean"
```
-/
public def findTransitiveImportsFromSource
  (startPath : System.FilePath)
  (rootFilter : Option Name := none)
  : IO NameSet := do
  let mut visited : NameSet := {}
  let mut queue := #[]

  -- Initialize with direct imports from the start file
  for imp in ← findImportsFromSource startPath do
    match rootFilter with
    | some root => if imp.getRoot == root then queue := queue.push imp
    | none => queue := queue.push imp

  -- Process queue with BFS
  while h : queue.size > 0 do
    let module := queue[0]
    queue := queue.eraseIdx 0

    if visited.contains module then continue
    visited := visited.insert module

    -- Convert module name to file path
    let path := System.mkFilePath (module.components.map (·.toString)) |>.addExtension "lean"

    if ← path.pathExists then
      for imp in ← findImportsFromSource path do
        match rootFilter with
        | some root =>
          if imp.getRoot == root && !visited.contains imp then
            queue := queue.push imp
        | none =>
          if !visited.contains imp then
            queue := queue.push imp

  return visited

/--
Build an import graph by parsing source files, starting from `roots` and walking
direct imports recursively. Returns a `NameMap` from each visited module to its
array of direct imports.

Like `findTransitiveImportsFromSource`, this only sees syntactic imports.
Modules whose source file does not exist (e.g., `Lean.*` from outside the CWD)
are recorded with an empty import list rather than recursed into.

Used to support a no-`olean` mode of `lake exe graph`.
-/
public partial def buildGraphFromSource (roots : Array Name) : IO (NameMap (Array Name)) := do
  let mut graph : NameMap (Array Name) := {}
  let mut queue := roots.toList
  while !queue.isEmpty do
    let module := queue.head!
    queue := queue.tail!
    if graph.contains module then continue
    let path := System.mkFilePath (module.components.map (·.toString)) |>.addExtension "lean"
    let imports ← if ← path.pathExists then findImportsFromSource path else pure #[]
    graph := graph.insert module imports
    for imp in imports do
      if !graph.contains imp then queue := imp :: queue
  return graph
