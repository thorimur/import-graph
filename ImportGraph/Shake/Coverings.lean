module

import all ImportGraph.Shake.Environment
import all ImportGraph.Shake.Algebra
import Std.Data.HashMap.AdditionalOperations

open ImportGraph Lean Lake Shake

/- The thing this does, though, is it says...

For each covering element, incorporate it into the set of minimal elements for each project it participates in. But! We only consider minimality *in that project*. Hypothetically, we could consider different minimality metrics. For example, the minimal elements among a certain league could compete on their batteries uses. We could ask which leagues we care about...the league is essentially "which do we want to consider". The game (`lt`) is "what makes such-and-such better". The two common cases, I think, are best-in-project and best-overall. But this should be customizable. Also, we might have other sorts of games: what has the smallest public scope available, for instance. All sorts of things.

We also want to consider different notions of "available". For instance: "where in mathlib can I put this, if I'm allowed to insert new core or batteries imports?"

-/

-- /-- Finds the modules `i` that provide `needs` according to `transDeps` (including `i`'s public and
-- private scopes), and are lowest according to `lt`. `needs` does not need to be
-- transitively closed, nor does `transDeps` need to be filled. -/

def ImportGraph.Preceding.compareByDepthThenSize (p₁ p₂ : Preceding) :=
  compare p₁.depth p₂.depth |>.then <| compare p₁.prev.size p₂.prev.size

def Needs.coveringsByProject (s : ImportGraph.Shake.StateWithPreceding) (needs : Needs) :
    Std.HashMap Name (Array (ModuleIdx × Preceding)) := Id.run do
  let mut minimals : Std.HashMap Name (Array (Option (ModuleIdx × Preceding))) := {}
  let some allKey := s.toKeyStore.getIdxOf? .anonymous | return {}
  for i in 0...s.transDeps.size do
    if needs.coveredBy i s.transDeps then
      -- TODO: be cleverer about this? Can we skip entire attempts?
      -- Or maybe totally different data structure? List, perhaps?
      -- Traversing in one direction or another
      if let some allVal := s.vals[i]![allKey]?.join then
        for val in s.vals[i]!, key in s.ofIdx do
          if let some { participating := true, .. } := val then
            minimals := minimals.incorporateBelowAt key (i, allVal) fun (_,p₁) (_,p₂) =>
              p₁.prev.lt p₂.prev
  return minimals.map (fun _ arr => arr.reduceOption.qsort fun (_,p₁) (_,p₂) =>
    p₁.compareByDepthThenSize p₂ |>.isLT)

structure FindHomeResult where
  inCurrentByCurrent : Array (ModuleIdx × Preceding) := #[]
  inAnyByAll : Std.HashMap Name (Array (ModuleIdx × Preceding)) := {}

def FindHomeResult.isEmpty : FindHomeResult → Bool
  | { inCurrentByCurrent, inAnyByAll } =>
    inCurrentByCurrent.isEmpty && inAnyByAll.all fun _ arr => arr.isEmpty

/-- Single-purpose function for the current implementation of `#find_home`. -/
def Needs.coveringsFindHome (s : ImportGraph.Shake.StateWithPreceding) (needs : Needs)
    (currentRoot : Name) : FindHomeResult := Id.run do
  let mut inCurrentByCurrent : Array (Option <| ModuleIdx × Preceding) := #[]
  let mut inAnyByAll : Std.HashMap Name (Array (Option <| ModuleIdx × Preceding)) := {}
  let some allKey := s.toKeyStore.getIdxOf? .anonymous | return {}
  for i in 0...s.transDeps.size do
    if needs.coveredBy i s.transDeps then
      -- TODO: be cleverer about this? Can we skip entire attempts?
      -- Or maybe totally different data structure? List, perhaps?
      -- Traversing in one direction or another
      let allVal? := s.vals[i]![allKey]?.join
      for val? in s.vals[i]!, key in s.ofIdx do
        if let some val@{ participating := true, .. } := val? then
          if key == currentRoot then
            -- `participating := true` above means it's in the current project.
            -- Adjust both `inCurrent*`s within this branch.
            inCurrentByCurrent := inCurrentByCurrent.incorporateBelow (i, val) fun (_,p₁) (_,p₂) =>
              p₁.prev.lt p₂.prev
          if let some allVal := allVal? then
            inAnyByAll := inAnyByAll.incorporateBelowAt key (i, allVal) fun (_,p₁) (_,p₂) =>
              p₁.prev.lt p₂.prev
  return {
    inCurrentByCurrent := inCurrentByCurrent.reduceOption
    inAnyByAll := inAnyByAll.map fun _ arr => arr.reduceOption }

-- -- Are there different senses of `lt`? Should this be a `KeyedArray Bool` or such?
-- def PrecedingVals.lt (ps₁ ps₂ : KeyedArray Preceding) : Bool :=
--   ps₁
