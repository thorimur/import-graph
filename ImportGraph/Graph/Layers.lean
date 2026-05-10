/-
Copyright (c) 2026 Thomas Murrills. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Murrills
-/
module

public import Lean.Data.NameMap.Basic

/-!
# Topological layers of an import graph

Computes a layer index for each node in a DAG, where layer 0 is assigned to
nodes with no (in-graph) dependencies, and otherwise
`layer(n) = 1 + max(layer(j))` over `n`'s dependencies `j`.

Edges follow the `NameMap (Array Name)` convention used elsewhere in this
package: `m[n]` is the array of modules `n` imports.
-/

namespace Lean.NameMap

/--
Compute the topological layer of each node in the graph `m`. The graph must be
a DAG.

Runs depth-first with memoisation: each node and edge is visited at most once,
giving `O(V + E)` total work.
-/
public partial def topologicalLayers (m : NameMap (Array Name)) : NameMap Nat :=
  m.foldl (fun layers n _ => visit layers n) {}
where
  visit (layers : NameMap Nat) (n : Name) : NameMap Nat :=
    if layers.contains n then layers
    else
      let deps := (m.find? n).getD #[]
      let layers := deps.foldl visit layers
      let l := deps.foldl (fun acc j => max acc ((layers.find? j).getD 0 + 1)) 0
      layers.insert n l

end Lean.NameMap
