/-
Copyright (c) 2026 Thomas R. Murrills. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas R. Murrills
-/
module

public import ImportGraph.Shake.Basic

open Lean ImportGraph Shake

namespace ImportGraph.Shake

public protected class HPostcomp (α) (β) (γ : outParam (Type u)) where
  protected hpostcomp : α → β → γ

scoped infixl:80 " ≫ " => HPostcomp.hpostcomp

public protected class HTransClosure (α) (β) (γ : outParam (Type u)) where
  protected htransClosure : α → β → γ

scoped notation:max I "⟦" n "⟧" => HTransClosure.htransClosure I n

abbrev Hierarchy := Array Provides

/-- Given an abstract `NeedsKind` `[kImp⟩` and a collection of prearrows `j [k⟩ ·` (`Provides`), add to `base` the composed prearrows `j [k⟩[imp⟩ ·` where composition is possible. Does not account for `public` ⊆ `private` on the codomain side (see `linearize`).

Note that this does *not* add the original collection of prearrows to `base`. -/
def Needs.addAndThen (impTransDeps : Needs) (kImp : NeedsKind)
    (base : Needs := ∅) : Needs := Id.run do
  let mut composed := base
  -- `{ j [k⟩[kImp⟩ · | j, k s.t. (j [k⟩ ·) ∈ impTransDeps ∧ k.target = kImp.source }`
  if _ : kImp.isAll then
    for h : k in NeedsKind.toPrivate do
      composed := composed.union
        (k.andThen kImp (by simp; grind))
        (impTransDeps.get k)
  else
    for h : k in NeedsKind.toPublic do
      composed := composed.union
        (k.andThen kImp (by simp; grind))
        (impTransDeps.get k)
  return composed

@[inline] def Needs.andThen (impTransDeps : Needs) (kImp : NeedsKind) : Needs :=
  impTransDeps.addAndThen kImp (base := ∅)

scoped instance : Shake.HPostcomp Needs NeedsKind Needs where
  hpostcomp n k := n.andThen k

/-- Given an abstract `Import` `[kImp⟩` and a collection of prearrows `j [k⟩ ·` (`Provides`), add to `base` the composed prearrows `j [k⟩[imp⟩ ·` where composition is possible.

Note that this does *not* add the original collection of prearrows to `base`. -/
@[inline] def Lean.Import.addAndThen (impTransDeps : Needs) (imp : Import)
    (base : Needs := ∅) : Needs := Id.run do
  impTransDeps.addAndThen (NeedsKind.ofImport imp) base

/-- Given an abstract import `[m,p⟩` and a collection of prearrows `j ⟦m',p'⟫ ·` (`Needs`), forms the composed prearrows `j ⟦m',p'⟫[m,p⟩ ·` where composition is possible. -/
@[inline] def Lean.Import.andThen (impTransDeps : Needs) (imp : Import) : Needs :=
  imp.addAndThen (base := .empty) impTransDeps

scoped instance : Shake.HPostcomp Needs Import Needs where
  hpostcomp n imp := imp.andThen n

/-- Given an import hierarchy of arrows `j' [_⟩ j` and a preimport `i [imp⟩ ·`, forms the set of prearrows obtained by transitively closing `i [imp⟩ ·` with respect to the import hierarchy. This is `i [imp⟩ ·` together with compositions `j [_⟩ i [imp⟩ ·`. `transDeps` is assumed to be reflexified.  -/
@[inline] def NeedsKind.transitiveClosureSingle (i : Nat) (k : NeedsKind)
    (transDeps : Hierarchy) : Needs :=
  transDeps[i]! ≫ k

scoped instance : Shake.HTransClosure Hierarchy (Nat × NeedsKind) Needs where
  htransClosure := fun transDeps (i, imp) => imp.transitiveClosureSingle i transDeps

/-- Given an import hierarchy of arrows `j' [_⟩ j` and a preimport `i [imp⟩ ·`, forms the set of prearrows obtained by transitively closing `i [imp⟩ ·` with respect to the import hierarchy. This is `i [imp⟩ ·` together with compositions `j [_⟩ i [imp⟩ ·`. `transDeps` is assumed to be reflexified.  -/
@[inline] def Lean.Import.transitiveClosureSingle (i : Nat) (imp : Import)
    (transDeps : Hierarchy) : Needs :=
  transDeps[i]! ≫ imp

@[inline] scoped instance : Shake.HTransClosure Hierarchy (Nat × Import) Needs where
  htransClosure := fun transDeps (i, imp) => imp.transitiveClosureSingle i transDeps

/-- Given a set of prearrows `i [k⟩ ·` and an import hierarchy, includes in `base` the compositions of arrows `j [k'⟩ i [k⟩ ·` where composition is possible. Assumes every index is valid. -/
def Hierarchy.addAndThen (transDeps : Hierarchy) (n : Needs)
    (base := Needs.empty) : Needs := Id.run do
  let mut composed := base
  for (k, i) in n.highToLow do
    composed := composed ∪ transDeps[i]! ≫ k
  composed

/-- Given a set of prearrows `i [k⟩ ·` and an import hierarchy, forms the compositions of arrows `j [k'⟩ i [k⟩ ·` where composition is possible. -/
@[inline] def Hierarchy.andThen (transDeps : Hierarchy) (n : Needs) : Needs :=
  transDeps.addAndThen n (base := .empty)

scoped instance : Shake.HPostcomp Hierarchy Needs Needs where
  hpostcomp transDeps n := transDeps.andThen n

@[inline] def Needs.addTransitiveClosure (base n : Needs) (transDeps : Hierarchy) : Needs :=
  transDeps.addAndThen n (base := base ∪ n)

/-- `n ∪ (transDeps ≫ n)` -/
@[inline] def Needs.transitiveClosure (n : Needs) (transDeps : Hierarchy) : Needs :=
  transDeps.addAndThen n (base := n)

scoped instance : Shake.HTransClosure Hierarchy Needs Needs where
  htransClosure transDeps n := n.transitiveClosure transDeps

/--
Includes the public visibilities in the corresponding private visibilities, to represent a "provides" relationship.
-/
@[inline] def Needs.linearize (a : Needs) : Needs :=
  { a with priv := a.priv ∪ a.pub, metaPriv := a.metaPriv ∪ a.metaPub }

@[inline] def Needs.isLinear (a : Needs) : Bool :=
  a.pub.le a.priv && a.metaPub.le a.metaPriv

@[inline] def Needs.antilinearize (a : Needs) : Needs :=
  { a with priv := a.priv \ a.pub, metaPriv := a.metaPriv \ a.metaPub }

@[inline] def Needs.isAntilinear (a : Needs) : Bool :=
  (a.pub ∩ a.priv == {}) && (a.metaPub ∩ a.metaPriv == {})

/--
Adds in the reflexive availibilities of a given module, which are just the public and private availabilities and not the meta lifted versions. This matches what is available within a given module. Equivalent to `a ∪ .reflOf i`.

Note that this operation does *not* necessarily commute with transitive closure.
-/
@[inline] def Needs.reflexify (i : Nat) (a : Needs) : Needs := { a with
  pub := a.pub ∪ {i}
  priv := a.priv ∪ {i}
  privOfPriv := a.privOfPriv ∪ {i} }

@[inline] def Needs.unreflexify (i : Nat) (a : Needs) : Needs :=
  a.map (· \ {i})

/-- Checks if the arrows `j [k⟩ i` are covered by `transDeps`'s entry for `i`. Assumes `transDeps` is a `Provides` hierearchy. -/
@[inline] def Needs.coveredBy (needs : Needs) (i : Nat) (transDeps : Hierarchy) : Bool :=
  needs.directLe <| transDeps[i]!

/-- Checks if the prearrows `j [k⟩ ·` in `n₁` are included in the arrows provided by the transitive closure of `n₂` with respect to the import hierarchy. Linearizes `n₂` first, which ensures `n₁` is not penalized for respecting `public` ⊆ `private`. Assumes `transDeps` is reflexified. -/
@[inline] def Needs.subsumedBy (n₁ n₂ : Needs) (transDeps : Hierarchy) : Bool :=
  n₁.directLe transDeps⟦n₂.linearize⟧

/--
Returns an antilinearized `reduced : Needs` such that
```
a ≤ transDeps⟦reduced.linearize⟧
```
and `reduced` is minimal (perhaps non-uniquely) among such `Needs`.

Does not assume `a` is linearized.
-/
def Needs.reduce (a : Needs) (transDeps : Hierarchy) : Needs := Id.run do
  let mut reduced := a.linearize
  let a := a.antilinearize -- avoids unnecessary checks
  -- ensure we handle public/private first, since these may reduce meta
  for k in #[NeedsKind.pub, .priv, .privOfPriv, .metaPub, .metaPriv, .metaPrivOfPriv] do
    for i in a.get k |>.highToLow do
      if reduced.has k i then -- `(k, i)` may have been eliminated already
        reduced := (reduced \ transDeps⟦(i, k)⟧.linearize).union k {i}
  return reduced.antilinearize

/-- Attempts to insert `a` among the set `as` of minimal elements as a new minimal element according to `lt`. Clears elements of `as` that are above `a`, and ignores `a` if we already have an element lower than `a`.  -/
@[inline] private def _root_.Array.incorporateBelow (as : Array (Option α)) (a : α)
    (lt : α → α → Bool) : Array (Option α) := Id.run do
  let mut as := as
  for i in 0...as.size do
    let some aᵢ := as[i]! | continue
    if lt a aᵢ then
      -- Erase elements of `as` that are (strictly) above `a`
      as := as.set! i none
    else if lt aᵢ a then
      -- If `a` is strictly below any pre-existing element, we don't need to add it
      return as
  return as.push a

@[inline] def Std.HashMap.incorporateBelowAt {κ} [BEq κ] [Hashable κ]
    (map : Std.HashMap κ (Array (Option α))) (k : κ) (a : α) (lt : α → α → Bool) :
    Std.HashMap κ (Array (Option α)) := map.alter k fun arr? =>
      arr?.getD #[] |>.incorporateBelow a lt

-- TODO: might want to sort by things like "fewest public imports" instead?
/-- Finds the modules `i` that provide `needs` according to `transDeps` (including `i`'s public and
private scopes), and are lowest according to `lt`. `needs` does not need to be
transitively closed. -/
def Needs.coveringsBy (transDeps : Hierarchy) (needs : Needs) (lt : ModuleIdx → ModuleIdx → Bool) :
    Array ModuleIdx := Id.run do
  let mut mods := #[]
  for i in 0...transDeps.size do
    if needs.coveredBy i transDeps then
      -- TODO: be cleverer about this? Can we skip entire attempts?
      -- Or maybe totally different data structure? List, perhaps?
      -- Traversing in one direction or another
      mods := mods.incorporateBelow i lt
  return mods.reduceOption

/-- Finds the modules `i` that provide `needs` according to `transDeps` (including `i`'s public and
private scopes), and are lowest in the hierarchy according to `prevs`. `needs` does not need to be
transitively closed. -/
@[inline] def Needs.coverings (transDeps : Hierarchy) (prevs : Array Bitset) (needs : Needs) :
    Array ModuleIdx :=
  needs.coveringsBy transDeps fun i j => prevs[i]!.lt prevs[j]!

def sortByDepthThenSize (mods : Array ModuleIdx) (depths : Array Nat) (prevs : Array Bitset) :
    Array ModuleIdx :=
  mods.qsort fun i j =>
    (compare depths[i]! depths[j]! |>.then <| compare prevs[i]!.size prevs[j]!.size).isLT

end ImportGraph.Shake
