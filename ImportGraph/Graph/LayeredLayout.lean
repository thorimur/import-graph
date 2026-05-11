/-
Copyright (c) 2026 Thomas Murrills. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Murrills
-/
module

public import ImportGraph.Graph.Layers

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
Re-index `layerXs` so each folder (= first sub-component of the name after
stripping `module`) occupies its own variable-width column spanning all
layers. A folder's column width is the largest count of folder-members at
any single layer; within each layer, that folder's nodes (if any) are
centered inside the column, with the within-column order taken from the
incoming `layerXs`. Adjacent folder columns are separated by `gap` slots.
-/
public def withFolderColumns (m : NameMap (Array Name)) (module : Name)
    (layers : NameMap Nat) (layerXs : NameMap Nat) (gap : Nat := 1) :
    NameMap Nat := Id.run do
  let maxLayer := layers.foldl (init := 0) (fun acc _ l => max acc l)
  let numLayers := maxLayer + 1
  let folderOf (n : Name) : Name :=
    (n.replacePrefix module .anonymous).components.head?.getD .anonymous

  -- Per-(folder, layer) counts → per-folder width (max count over layers).
  let mut folderCounts : NameMap (Array Nat) := {}
  for (n, _) in m do
    let f := folderOf n
    let l := (layers.find? n).getD 0
    let counts := (folderCounts.find? f).getD (Array.replicate numLayers 0)
    folderCounts := folderCounts.insert f (counts.modify l (· + 1))
  let folderWidth : NameMap Nat :=
    folderCounts.foldl (init := {}) (fun acc f counts =>
      acc.insert f (counts.foldl max 0))

  -- Folder x-offsets in `NameMap` (alphabetical) iteration order.
  let mut folderOffset : NameMap Nat := {}
  let mut acc := 0
  let mut first := true
  for (f, _) in folderCounts do
    if !first then acc := acc + gap
    first := false
    folderOffset := folderOffset.insert f acc
    acc := acc + (folderWidth.find? f).getD 1

  -- Bucket nodes by layer, ordered by incoming layerXs (so within-folder
  -- order follows the barycenter / alphabetical sort that produced it).
  let mut byLayer : Array (Array Name) := Array.replicate numLayers #[]
  for (n, _) in m do
    let l := (layers.find? n).getD 0
    byLayer := byLayer.modify l (·.push n)

  let mut result : NameMap Nat := {}
  for layer in [0:byLayer.size] do
    let sorted := byLayer[layer]!.qsort (fun a b =>
      (layerXs.find? a).getD 0 < (layerXs.find? b).getD 0)
    let mut byFolder : NameMap (Array Name) := {}
    for n in sorted do
      let f := folderOf n
      byFolder := byFolder.insert f (((byFolder.find? f).getD #[]).push n)
    -- Within each folder, center this layer's nodes inside the column.
    for (f, nodes) in byFolder do
      let width := (folderWidth.find? f).getD 1
      let offset := (folderOffset.find? f).getD 0
      let centerPad := (width - nodes.size) / 2
      for i in [0:nodes.size] do
        result := result.insert nodes[i]! (offset + centerPad + i)
  return result

end Lean.NameMap
