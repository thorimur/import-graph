module

import all ImportGraph.Shake.Environment
import all ImportGraph.Shake.Algebra

open ImportGraph Lean Lake Shake

/-- Finds the modules `i` that provide `needs` according to `transDeps` (including `i`'s public and
private scopes), and are lowest according to `lt`. `needs` does not need to be
transitively closed, nor does `transDeps` need to be filled. -/
def Needs.coveringsByProject (s : ImportGraph.Shake.StateWithPreceding) (needs : Needs) :
    Array (Name × (Array (ModuleIdx × Preceding))) := Id.run do
  let mut minimals : Std.HashMap Name (Array (Option (ModuleIdx × Preceding))) := {}
  for i in 0...s.transDeps.size do
    if needs.coveredBy i s.transDeps then
      -- dbg_trace "got one"
      -- TODO: be cleverer about this? Can we skip entire attempts?
      -- Or maybe totally different data structure? List, perhaps?
      -- Traversing in one direction or another
      -- dbg_trace s!"{repr (id s.vals[i]! : Array _)}"
      for val in (id s.vals[i]! : Array _), key in s.ofIdx do
        if let some val@{ participating := true, .. } := val then
          minimals := minimals.incorporateBelowAt key (i, val) fun (_,p₁) (_,p₂) =>
            p₁.prev.lt p₂.prev
  return minimals.toArray.map fun (key, vals) => (key, vals.reduceOption)

-- -- Are there different senses of `lt`? Should this be a `KeyedArray Bool` or such?
-- def PrecedingVals.lt (ps₁ ps₂ : KeyedArray Preceding) : Bool :=
--   ps₁
