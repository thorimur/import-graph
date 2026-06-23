module

import all ImportGraph.Shake.Environment
import all ImportGraph.Shake.Algebra

open ImportGraph Lean Lake Shake

/- The thing this does, though, is it says...

For each covering element, incorporate it into the set of minimal elements for each project it participates in. But! We only consider minimality *in that project*. Hypothetically, we could consider different minimality metrics. For example, the minimal elements among a certain league could compete on their batteries uses. We could ask which leagues we care about...the league is essentially "which do we want to consider". The game (`lt`) is "what makes such-and-such better". The two common cases, I think, are best-in-project and best-overall. But this should be customizable. Also, we might have other sorts of games: what has the smallest public scope available, for instance. All sorts of things.

We also want to consider different notions of "available". For instance: "where in mathlib can I put this, if I'm allowed to insert new core or batteries imports?"

-/

-- /-- Finds the modules `i` that provide `needs` according to `transDeps` (including `i`'s public and
-- private scopes), and are lowest according to `lt`. `needs` does not need to be
-- transitively closed, nor does `transDeps` need to be filled. -/
def Needs.coveringsByProject (s : ImportGraph.Shake.StateWithPreceding) (needs : Needs) :
    Array (Name × (Array (ModuleIdx × Preceding))) := Id.run do
  let mut minimals : Std.HashMap Name (Array (Option (ModuleIdx × Preceding))) := {}
  for i in 0...s.transDeps.size do
    if needs.coveredBy i s.transDeps then
      -- TODO: be cleverer about this? Can we skip entire attempts?
      -- Or maybe totally different data structure? List, perhaps?
      -- Traversing in one direction or another
      for val in (id s.vals[i]! : Array _), key in s.ofIdx do
        if let some val@{ participating := true, .. } := val then
          minimals := minimals.incorporateBelowAt key (i, val) fun (_,p₁) (_,p₂) =>
            p₁.prev.lt p₂.prev
  return minimals.toArray.map fun (key, vals) => (key, vals.reduceOption)

-- -- Are there different senses of `lt`? Should this be a `KeyedArray Bool` or such?
-- def PrecedingVals.lt (ps₁ ps₂ : KeyedArray Preceding) : Bool :=
--   ps₁
