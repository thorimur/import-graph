/-
Copyright (c) 2026 Thomas Murrills. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Murrills
-/
module

public import ImportGraph.Graph.Layers
public import ImportGraph.Lean.Name

/-!
# Layered layout: within-layer ordering

Given a topologically-layered DAG, computes a within-layer x-index for each
node using a Sugiyama-style barycenter heuristic to reduce edge crossings.
The intent is for this to be computed at GEXF generation time so the browser
can render layered views without running a layout engine itself.

The graph follows the same convention as elsewhere in this package:
`m[n]` is the array of modules `n` imports, so edges flow from imports to
importers.
-/

namespace Lean.NameMap

/--
Within-layer x-indices for a layered layout. Returns a `Nat` per node giving
its index within its layer (0 = leftmost). Uses alternating top-down and
bottom-up barycenter sweeps over `iters` iterations.

`layers` must agree with `topologicalLayers m`.
-/
public def withinLayerIndices (m : NameMap (Array Name)) (layers : NameMap Nat)
    (iters : Nat := 8) : NameMap Nat := Id.run do
  -- Reverse adjacency: `succ[n]` = modules that import `n`.
  let mut succ : NameMap (Array Name) := {}
  for (n, deps) in m do
    for d in deps do
      succ := succ.insert d (((succ.find? d).getD #[]).push n)

  -- Bucket nodes by layer.
  let maxLayer := layers.foldl (init := 0) (fun acc _ l => max acc l)
  let mut buckets : Array (Array Name) := Array.replicate (maxLayer + 1) #[]
  for (n, _) in m do
    let l := (layers.find? n).getD 0
    buckets := buckets.modify l (·.push n)

  -- Initial within-layer order: alphabetical. Seeds the barycenter sweeps.
  buckets := buckets.map (fun b => b.qsort (·.toString < ·.toString))
  let mut xs : NameMap Float := {}
  for b in buckets do
    for i in [0:b.size] do
      xs := xs.insert b[i]! (Float.ofNat i)

  -- Alternating sweeps. On a top-down pass, each node's new x is the mean of
  -- its predecessors' (lower-layer) x; on a bottom-up pass, the mean of its
  -- successors' (higher-layer) x. After sorting, we rewrite xs with the new
  -- integer indices so the next layer in the sweep sees the updated order.
  for iter in [0:iters] do
    let topDown := iter % 2 == 0
    for k₀ in [0:buckets.size] do
      let k := if topDown then k₀ else buckets.size - 1 - k₀
      let bucket := buckets[k]!
      let scored := bucket.map fun n =>
        let neighbors :=
          if topDown then (m.find? n).getD #[]
          else (succ.find? n).getD #[]
        let x : Float :=
          if neighbors.isEmpty then (xs.find? n).getD 0.0
          else neighbors.foldl (init := (0.0 : Float))
                (fun acc nb => acc + (xs.find? nb).getD 0.0)
              / Float.ofNat neighbors.size
        (n, x)
      let sorted := scored.qsort (fun (_, a) (_, b) => a < b)
      let newBucket := sorted.map (·.fst)
      buckets := buckets.set! k newBucket
      for i in [0:newBucket.size] do
        xs := xs.insert newBucket[i]! (Float.ofNat i)

  -- Final integer indices follow the sorted order in each bucket.
  let mut result : NameMap Nat := {}
  for b in buckets do
    for i in [0:b.size] do
      result := result.insert b[i]! i
  return result

/--
Layered layout with one variable-width column per folder. Each folder
(= first sub-component of the name after stripping `module`) gets its own
column whose width is the largest count of folder-members at any single
layer. Within each (folder, layer) cell, an alternating top-down/bottom-up
**barycenter sweep constrained to the cell** orders the nodes — so the
layout still tries to minimise crossings with adjacent layers, but only by
permuting nodes inside their fixed folder column. Adjacent folder columns
are separated by `gap` slots.
-/
public def withFolderColumns (m : NameMap (Array Name)) (module : Name)
    (layers : NameMap Nat) (iters : Nat := 8) (gap : Nat := 1) :
    NameMap Nat := Id.run do
  let maxLayer := layers.foldl (init := 0) (fun acc _ l => max acc l)
  let numLayers := maxLayer + 1
  let folderOf (n : Name) : Name := n.folderUnder module

  -- `cells[folder]` is indexed by layer; each entry is the list of nodes in
  -- that (folder, layer) cell, initially in alphabetical order.
  let mut cells : NameMap (Array (Array Name)) := {}
  for (n, _) in m do
    let f := folderOf n
    let l := (layers.find? n).getD 0
    let layerArr := (cells.find? f).getD (Array.replicate numLayers #[])
    cells := cells.insert f (layerArr.modify l (·.push n))
  cells := cells.foldl (init := {}) (fun acc f layerArr =>
    acc.insert f (layerArr.map (·.qsort (·.toString < ·.toString))))

  -- Folder widths and x-offsets. Folder column order = `NameMap` order.
  let folderWidth : NameMap Nat :=
    cells.foldl (init := {}) (fun acc f layerArr =>
      acc.insert f (layerArr.foldl (init := 0) (fun w arr => max w arr.size)))
  let mut folderOffset : NameMap Nat := {}
  let mut offsetAcc := 0
  let mut firstFolder := true
  for (f, _) in cells do
    if !firstFolder then offsetAcc := offsetAcc + gap
    firstFolder := false
    folderOffset := folderOffset.insert f offsetAcc
    offsetAcc := offsetAcc + (folderWidth.find? f).getD 1

  -- Compute positions for every node from the current order in a folder's
  -- `layerArr`, centering each layer's cell inside the folder's column.
  let cellPositions (layerArr : Array (Array Name)) (offset width : Nat) :
      Array (Name × Nat) := Id.run do
    let mut out : Array (Name × Nat) := #[]
    for layer in [0:numLayers] do
      let nodes := layerArr[layer]!
      let centerPad := (width - nodes.size) / 2
      for i in [0:nodes.size] do
        out := out.push (nodes[i]!, offset + centerPad + i)
    return out

  let mut xs : NameMap Float := {}
  for (f, layerArr) in cells do
    let offset := (folderOffset.find? f).getD 0
    let width := (folderWidth.find? f).getD 1
    for (n, p) in cellPositions layerArr offset width do
      xs := xs.insert n (Float.ofNat p)

  -- Reverse adjacency: nodes that import `n`.
  let mut succ : NameMap (Array Name) := {}
  for (n, deps) in m do
    for d in deps do
      succ := succ.insert d (((succ.find? d).getD #[]).push n)

  -- Constrained barycenter sweeps: each (folder, layer) cell is re-sorted
  -- using the mean x of neighbours in the adjacent layer, then assigned
  -- positions inside the folder's column. `xs` is updated as we go so later
  -- cells see the new positions.
  for iter in [0:iters] do
    let topDown := iter % 2 == 0
    for k₀ in [0:numLayers] do
      let layer := if topDown then k₀ else numLayers - 1 - k₀
      for (f, layerArr) in cells do
        let nodes := layerArr[layer]!
        if nodes.size ≤ 1 then continue
        let scored := nodes.map fun n =>
          let neighbors :=
            if topDown then (m.find? n).getD #[]
            else (succ.find? n).getD #[]
          let x : Float :=
            if neighbors.isEmpty then (xs.find? n).getD 0.0
            else neighbors.foldl (init := (0.0 : Float))
                  (fun a nb => a + (xs.find? nb).getD 0.0)
                / Float.ofNat neighbors.size
          (n, x)
        let sorted := (scored.qsort (fun (_, a) (_, b) => a < b)).map (·.fst)
        cells := cells.insert f (layerArr.set! layer sorted)
        let offset := (folderOffset.find? f).getD 0
        let width := (folderWidth.find? f).getD 1
        let centerPad := (width - sorted.size) / 2
        for i in [0:sorted.size] do
          xs := xs.insert sorted[i]! (Float.ofNat (offset + centerPad + i))

  let mut result : NameMap Nat := {}
  for (f, layerArr) in cells do
    let offset := (folderOffset.find? f).getD 0
    let width := (folderWidth.find? f).getD 1
    for (n, p) in cellPositions layerArr offset width do
      result := result.insert n p
  return result

end Lean.NameMap
