/-
Copyright (c) 2026 Thomas R. Murrills. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas R. Murrills
-/
module

public import ImportGraph.Shake.DeclNeeds
public import ImportGraph.WorkspaceModel.Build

import Std.Data.HashMap.AdditionalOperations

open ImportGraph Lean Lake Shake

public section

namespace ImportGraph.Shake

/-- Computes a mapping `LibIdx → Array ModIdx` assigning to each library in the workspace model an
array of modules which provide `needs : ImportNeeds` and are minimal (by sets of previous modules).
Modules which provide strict supersets of other candidate modules are knocked out.

It then ranks the "winning" modules first by import depth
*among imports from the same library* (i.e. not counting imports of upstream libraries towards the
depth), then by number of previous modules, then alphabetically.

`league : ModuleBitset` specifies the modules among which the competition is conducted. If `none`,
this is all modules. -/
def ImportNeeds.providersByLib (w : WorkspaceModel) (needs : ImportNeeds)
    (league : Option ModuleBitset := none) :
    Std.HashMap LibIdx (Array ModIdx) := Id.run do
  let mut minimals : Std.HashMap LibIdx (Array (Option (ModIdx × ModuleBitset))) := {}
  for h : i in 0...(Hierarchy.size w) do
    if needs.isProvidedBy w[i] && league.elim true (·.has i) then
      let iLibPrevs := (w.getMod! i).prevs
      minimals := minimals.incorporateBelowAt (w.libIdxOfModIdx! i) (i, iLibPrevs)
        fun (_, iPrevs) (_, jPrevs) => iPrevs.lt jPrevs
  return minimals.map fun libIdx arr => (arr.reduceOption.qsort fun (i,pᵢ) (j,pⱼ) =>
    (compare (w.libDepth! i libIdx) (w.libDepth! j libIdx)) -- passing `libIdx` only for efficiency
      |>.then (compare pᵢ.size pⱼ.size)
      |>.then (Name.cmp (w.getMod! i).name (w.getMod! j).name) -- for stability if all else fails
      |>.isLT).map (·.1)
