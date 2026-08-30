module

public import ImportGraph.Shake.DeclNeeds
public import ImportGraph.WorkspaceModel.Build

import Std.Data.HashMap.AdditionalOperations

open ImportGraph Lean Lake Shake

public section

namespace ImportGraph.Shake

/- The thing this does, though, is it says...

For each covering element, incorporate it into the set of minimal elements for each project it participates in. But! We only consider minimality *in that project*. Hypothetically, we could consider different minimality metrics. For example, the minimal elements among a certain league could compete on their batteries uses. We could ask which leagues we care about...the league is essentially "which do we want to consider". The game (`lt`) is "what makes such-and-such better". The two common cases, I think, are best-in-project and best-overall. But this should be customizable. Also, we might have other sorts of games: what has the smallest public scope available, for instance. All sorts of things.

We also want to consider different notions of "available". For instance: "where in mathlib can I put this, if I'm allowed to insert new core or batteries imports?"

-/

-- /-- Finds the modules `i` that provide `needs` according to `transDeps` (including `i`'s public and
-- private scopes), and are lowest according to `lt`. `needs` does not need to be
-- transitively closed, nor does `transDeps` need to be filled. -/

/-- For each library in which `needs` is satisfied, records the providing modules by `ModIdx` as well as the set of modules in that library which precede it.

Winners are given by those with minimal subsets of previous modules *from the given library*. Rankings are given first by which has the lowest depth in that library, then by which depends on the fewest modules in that library. -/
def ImportNeeds.coveringsByLibAmongLib (w : WorkspaceModel) (needs : ImportNeeds) :
    Std.HashMap LibIdx (Array (ModIdx × ModuleBitset)) := Id.run do
  let mut minimals : Std.HashMap LibIdx (Array (Option (ModIdx × ModuleBitset))) := {}
  for h : i in 0...(Hierarchy.size w) do
    if needs.isProvidedBy w[i] then
      let iLibPrevs := (w.getMod! i).prevs ∩ (w.libOfModIdx! i).mods
      minimals := minimals.incorporateBelowAt (w.libIdxOfModIdx! i) (i, iLibPrevs)
        fun (_, iLibPrevs) (_, jLibPrevs) => iLibPrevs.lt jLibPrevs
  -- TODO: maybe this sorting should come afterwards?
  return minimals.map (fun libIdx arr => arr.reduceOption.qsort fun (i,pᵢ) (j,pⱼ) =>
    -- Note that since `i, j ∈ library(libIdx)`, both `libDepth!`s will be nonzero.
    (compare (w.libDepth! i libIdx) (w.libDepth! j libIdx)) -- passing `libIdx` only for efficiency
      |>.then (compare pᵢ.size pⱼ.size)
      |>.then (Name.cmp (w.getMod! i).name (w.getMod! j).name) -- for stability if all else fails
      |>.isLT)

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

-- def FindHomeResult.isEmpty : FindHomeResult → Bool
--   | { inCurrentByCurrent, inAnyByAll } =>
--     inCurrentByCurrent.isEmpty && inAnyByAll.all fun _ arr => arr.isEmpty

-- /-- Single-purpose function for the current implementation of `#find_home`. -/
-- def Needs.coveringsFindHome (w : WorkspaceModel) (needs : ImportNeeds)
--     (currentRoot : Name) : FindHomeResult := Id.run do
--   let mut inCurrentByCurrent : Array (Option <| ModuleIdx × Preceding) := #[]
--   let mut inAnyByAll : Std.HashMap Name (Array (Option <| ModuleIdx × Preceding)) := {}
--   let some allKey := s.toKeyStore.getIdxOf? .anonymous | return {}
--   for i in 0...s.transDeps.size do
--     if needs.coveredBy i s.transDeps then
--       -- TODO: be cleverer about this? Can we skip entire attempts?
--       -- Or maybe totally different data structure? List, perhaps?
--       -- Traversing in one direction or another
--       let allVal? := s.vals[i]![allKey]?.join
--       for val? in s.vals[i]!, key in s.ofIdx do
--         if let some val@{ participating := true, .. } := val? then
--           if key == currentRoot then
--             -- `participating := true` above means it's in the current project.
--             -- Adjust both `inCurrent*`s within this branch.
--             inCurrentByCurrent := inCurrentByCurrent.incorporateBelow (i, val) fun (_,p₁) (_,p₂) =>
--               p₁.prev.lt p₂.prev
--           if let some allVal := allVal? then
--             inAnyByAll := inAnyByAll.incorporateBelowAt key (i, allVal) fun (_,p₁) (_,p₂) =>
--               p₁.prev.lt p₂.prev
--   return {
--     inCurrentByCurrent := inCurrentByCurrent.reduceOption
--     inAnyByAll := inAnyByAll.map fun _ arr => arr.reduceOption }

-- -- -- Are there different senses of `lt`? Should this be a `KeyedArray Bool` or such?
-- -- def PrecedingVals.lt (ps₁ ps₂ : KeyedArray Preceding) : Bool :=
-- --   ps₁
