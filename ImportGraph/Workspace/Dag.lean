/-
Copyright (c) 2026 Thomas Murrills. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Murrills
-/
import ImportGraph.Workspace.Index

/-!
# Bitset-backed directed graphs

A `Dag α` is a directed graph on the index space `Idx α`, stored as a `Table` of successor
`IdxSet`s — the classic "array of bitsets" representation, wrapped in the typed-index layer
of `ImportGraph.Workspace.Index`.

For import graphs we orient edges from a module *to the modules it imports*, so "successors"
point *up* the import hierarchy: `reachable {i}` is everything above `i` (its transitive
imports), and `transpose` turns the graph around to ask what lies below (its transitive
importers).

Nothing here assumes acyclicity except the operations whose names end in `?` — those return
`none` when the graph has a cycle (which, for an import graph, indicates malformed input).
-/

namespace ImportGraph

/-- A directed graph on `Idx α`, as a table of successor sets. See the module docstring. -/
structure Dag (α : Type u) where
  /-- Row `i` is the set of direct successors of `i` (for import graphs: its direct imports). -/
  succs : Table α (IdxSet α)

namespace Dag

instance : Inhabited (Dag α) := ⟨⟨∅⟩⟩

/-- The graph on `n` nodes with no edges. -/
@[inline] def empty (n : Nat) : Dag α := ⟨.replicate n ∅⟩

/-- The number of nodes. -/
@[inline] def size (g : Dag α) : Nat := g.succs.size

/-- The full node set. -/
@[inline] def univ (g : Dag α) : IdxSet α := g.succs.univ

/-- The direct successors of `i`. -/
@[inline] def succsOf (g : Dag α) (i : Idx α) : IdxSet α := g.succs.get! i

/-- Whether the edge `i → j` is present. -/
@[inline] def hasEdge (g : Dag α) (i j : Idx α) : Bool := (g.succsOf i).contains j

@[inline] def addEdge (g : Dag α) (i j : Idx α) : Dag α :=
  ⟨g.succs.modify i (·.insert j)⟩

/-- Build a graph on `n` nodes from an explicit edge list. -/
def ofEdges (n : Nat) (edges : Array (Idx α × Idx α)) : Dag α :=
  edges.foldl (init := empty n) fun g (i, j) => g.addEdge i j

/-- The graph with every edge reversed. -/
def transpose (g : Dag α) : Dag α := Id.run do
  let mut preds : Table α (IdxSet α) := .replicate g.size ∅
  for (i, js) in g.succs do
    for j in js do
      preds := preds.modify j (·.insert i)
  return ⟨preds⟩

/-- The nodes with no predecessors (for import graphs: modules nothing scanned imports). -/
def sources (g : Dag α) : IdxSet α :=
  g.succs.foldlIdx (init := g.univ) fun acc _ js => acc \ js

/-- The nodes with no successors (for import graphs: modules with no imports). -/
def sinks (g : Dag α) : IdxSet α :=
  g.succs.foldlIdx (init := ∅) fun acc i js =>
    if js.isEmpty then acc.insert i else acc

/-- The graph induced on `mask`: only nodes in `mask` keep their edges, and only edges into
`mask` are kept. -/
def restrict (g : Dag α) (mask : IdxSet α) : Dag α :=
  ⟨g.succs.mapIdx fun i js => if i ∈ mask then js ∩ mask else ∅⟩

/--
All nodes reachable from `init` by following successor edges (for import graphs:
everything `init` transitively imports). Includes `init` itself iff `includeInit := true`.

Works on cyclic graphs.
-/
def reachable (g : Dag α) (init : IdxSet α) (includeInit := true) : IdxSet α := Id.run do
  let mut acc := init
  let mut frontier := init
  while !frontier.isEmpty do
    let mut next : IdxSet α := ∅
    for i in frontier do
      next := next ∪ g.succsOf i
    frontier := next \ acc
    acc := acc ∪ next
  return if includeInit then acc else acc \ init

/--
A topological ordering of the nodes in which every node appears *before* its successors
(for import graphs: every module appears before anything it imports), or `none` if the
graph is cyclic.

Among valid orderings, ties are broken by index, lowest first.
-/
def topo? (g : Dag α) : Option (Array (Idx α)) := Id.run do
  let n := g.size
  let mut indeg : Table α Nat := .replicate n 0
  for (_, js) in g.succs do
    for j in js do
      indeg := indeg.modify j (· + 1)
  -- The "ready" set is an `IdxSet`, so popping its minimum gives deterministic order.
  let mut ready : IdxSet α := ∅
  for (i, d) in indeg do
    if d == 0 then ready := ready.insert i
  let mut order := Array.emptyWithCapacity n
  repeat
    let some i := ready.min? | break
    ready := ready.erase i
    order := order.push i
    for j in g.succsOf i do
      let d := indeg.get! j - 1
      indeg := indeg.set j d
      if d == 0 then ready := ready.insert j
  return if order.size == n then some order else none

/--
The transitive closure: `(g.transClosure?).succsOf i` is everything reachable from `i`,
not including `i` itself. Returns `none` if the graph is cyclic.
-/
def transClosure? (g : Dag α) : Option (Dag α) := do
  let order ← g.topo?
  -- Process in reverse topological order, so that each node's successors are already closed.
  let mut closure : Table α (IdxSet α) := .replicate g.size ∅
  for i in order.reverse do
    let mut acc : IdxSet α := ∅
    for j in g.succsOf i do
      acc := acc ∪ (closure.get! j).insert j
    closure := closure.set i acc
  return ⟨closure⟩

/--
The transitive reduction of an acyclic graph: the unique minimal subgraph with the same
reachability relation (for import graphs: the minimal direct imports realizing the same
transitive imports). Returns `none` if the graph is cyclic.

`closure?` can be supplied if `g.transClosure?` has already been computed.
-/
def reduction? (g : Dag α) (closure? : Option (Dag α) := none) : Option (Dag α) := do
  let closure ← match closure? with
    | some c => some c
    | none => g.transClosure?
  return ⟨g.succs.mapIdx fun _ js =>
    -- An edge `i → j` is redundant iff `j` is reachable from another successor of `i`.
    -- (In a DAG, `j` is never in its own closure, so we can union over all of `js`.)
    js \ (js.foldl (init := ∅) fun acc k => acc ∪ closure.succsOf k)⟩

/--
The height of each node: the length of the longest path following successor edges (for
import graphs: sinks such as `Init.Prelude` have height `0`, and a module's height is one
more than the maximum height of its imports). Returns `none` if the graph is cyclic.
-/
def heights? (g : Dag α) : Option (Table α Nat) := do
  let order ← g.topo?
  let mut heights : Table α Nat := .replicate g.size 0
  for i in order.reverse do
    let mut h := 0
    for j in g.succsOf i do
      h := max h (heights.get! j + 1)
    heights := heights.set i h
  return heights

end Dag

end ImportGraph
