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

-- TODO: check
def Lean.Import.addPostcompose (impTransDeps : Provides) (imp : Import)
    (base : Provides := ∅) : Needs := Id.run do
  let mut composed := base
  let kImp := NeedsKind.ofImport imp
  if h : kImp.isAll then
    for h : k in NeedsKind.toPrivate do
      composed := composed.union
        (k.postcompose kImp (by
          simp only [NeedsKind.toPrivate] at h
          simp; grind))
        (impTransDeps.get k) -- `{ j | j ⟦k⟫ · }`
  else
    for k in NeedsKind.toPublicTrans do -- `∀ (m, 1)`
      composed := composed.union
        { isMeta := k.isMeta || imp.isMeta
          isExported := imp.isExported
          isAll := false }
        (impTransDeps.get k) -- `{ j ⟦m, 1⟫ · | j }`
  return composed

/-- Given an abstract import `[m,p⟩` and a collection of prearrows `j ⟦m',p'⟫ ·` (`Provides`), add to `base` the composed prearrows `j ⟦m',p'⟫[m,p⟩ ·` where composition is possible, taking into account `public` ⊆ `private`.

Note that this does *not* add the original collection of prearrows to `base`. -/
def Lean.Import.addPostcompose (impTransDeps : Provides) (imp : Import)
    (base : Provides := ∅) : Needs := Id.run do
  let mut composed := base
  -- `⟦m, 1⟫[m', p⟩  ⇒  ⟦m ∨ m', p⟫`
  let kImp := NeedsKind.ofImport imp
  if h : kImp.isAll then
    for k in NeedsKind.toPrivate do
      composed := composed.union
        (k.postcompose kImp)
        (impTransDeps.get k) -- `{ j | j ⟦k⟫ ·}`
  else
    for k in NeedsKind.toPublicTrans do -- `∀ (m, 1)`
      composed := composed.union
        { isMeta := k.isMeta || imp.isMeta
          isExported := imp.isExported
          isAll := false }
        (impTransDeps.get k) -- `{ j ⟦m, 1⟫ · | j }`

  -- Maybe we should think about this as arrows with different domains instead?
  -- `(j, 0)` vs. `(j, 1)`.
  -- Arrows enriched in Bool for meta phase?
  -- `(j, 0) ↦ (j, 0)` .privOfPriv
  --
  composed

/-- Given an abstract import `[m,p⟩` and a collection of prearrows `j ⟦m',p'⟫ ·` (`Needs`), add to `base` the composed prearrows `j ⟦m',p'⟫[m,p⟩ ·` where composition is possible. -/
def Lean.Import.addPostcomposeNoAll (impTransDeps : Needs) (imp : Import)
    (base := Needs.empty) : Needs := Id.run do
  let mut composed := base
  -- `⟦m, 1⟫[m', p⟩  ⇒  ⟦m ∨ m', p⟫`
  for k' in #[NeedsKind.pub, .metaPub] do -- `∀ (m, 1)`
    composed := composed.union
      { isMeta := k'.isMeta || imp.isMeta, isExported := imp.isExported } -- `m' ∨ m, p`
      (impTransDeps.get k') -- `j ⟦m, 1⟫ ·`
  -- `⟦m, 0⟫[0, 2⟩  ⇒  ⟦m, 0⟫`
  if imp.importAll && !imp.isMeta then -- only apply to `[0, 2⟩` -- SQ: why?
    for k in #[NeedsKind.priv, .metaPriv] do -- `∀ (m, 0)`
      composed := composed.union k (impTransDeps.get k)
  composed

/-- Given an abstract import `[m,p⟩` and a collection of prearrows `j ⟦m',p'⟫ ·` (`Needs`), forms the composed prearrows `j ⟦m',p'⟫[m,p⟩ ·` where composition is possible. -/
@[inline] def Lean.Import.postcompose
    (impTransDeps : Needs) (imp : Import) : Needs :=
  imp.addPostcompose (base := .empty) impTransDeps

scoped instance : Shake.HPostcomp Needs Import Needs where
  hpostcomp n imp := imp.postcompose n

/-- Given an import hierarchy of arrows `j' ⟦_⟫ j` and a preimport `i [imp⟩ ·`, forms the set of prearrows obtained by transitively closing `i [imp⟩ ·` with respect to the import hierarchy. This is `i [imp⟩ ·` together with compositions `j ⟦_⟫ i [imp⟩ ·`. -/
@[inline] def Lean.Import.transitiveClosureSingle (i : Nat) (imp : Import)
    (transDeps : Hierarchy) : Needs :=
  (.single i { imp with }) ∪ (transDeps[i]! ≫ imp)

scoped instance : Shake.HTransClosure Hierarchy (ModuleIdx × Import) Needs where
  htransClosure := fun transDeps (i, imp) => imp.transitiveClosureSingle i transDeps

-- /-- Given an import hierarchy of arrows `j' ⟦_⟫ j` and a preimport `i [imp⟩ ·`, adds to `n` the set of prearrows obtained by transitively closing `i [imp⟩ ·` with respect to the import hierarchy. This is `i [imp⟩ ·` together with compositions `j ⟦_⟫ i [imp⟩ ·`. -/
-- @[inline] def _root_.Lean.Import.addTransitiveClosureSingle (n : Needs) (i : Nat) (imp : Import)
--     (transDeps : Hierarchy) : Needs :=
--   imp.addPostcompose (Needs.empty.union { imp with } {i}) transDeps[i]!

/-- Given an abstract `NeedsKind` `⟦m, p⟫` and a collection of prearrows `j ⟦m',p'⟫ ·` (`Needs`), forms the composed prearrows `j ⟦m',p'⟫⟦m,p⟫ ·` where composition is possible. -/
def NeedsKind.postcompose (n : Needs) (k : NeedsKind) : Needs := Id.run do
  let mut composed := .empty
  -- `⟦m, 1⟫⟦m', p⟫  ⇒  ⟦m ∨ m', p⟫`
  for m in #[NeedsKind.pub, .metaPub] do -- ∀ (m, 1)
    composed := composed.union
      { isMeta := m.isMeta || k.isMeta, isExported := k.isExported }
      (n.get m) -- `j ⟦m, 1⟫ ·`
  composed

scoped instance : Shake.HPostcomp Needs NeedsKind Needs where
  hpostcomp n k := k.postcompose n

/-- Given a set of prearrows `i ⟦m, p⟫ ·` and an import hierarchy, includes in `base` the compositions of arrows `j ⟦m',p'⟫ i ⟦m,p⟫ ·` where composition is possible. -/
def Needs.addPostcompose (transDeps : Hierarchy) (n : Needs)
    (base := Needs.empty) : Needs := Id.run do
  let mut composed := base
  for (k, i) in n.highToLow do
    composed := composed ∪ transDeps[i]! ≫ k
  composed

/-- Given a set of prearrows `i ⟦m, p⟫ ·` and an import hierarchy, forms the compositions of arrows `j ⟦m',p'⟫ i ⟦m,p⟫ ·` where composition is possible. -/
@[inline] def Needs.postcompose (transDeps : Hierarchy) (n : Needs) : Needs :=
  n.addPostcompose (base := .empty) transDeps

scoped instance : Shake.HPostcomp Hierarchy Needs Needs where
  hpostcomp transDeps n := n.postcompose transDeps

@[inline] def Needs.addTransitiveClosure (base n : Needs) (transDeps : Hierarchy) : Needs :=
  n.addPostcompose (base := base ∪ n) transDeps

/-- `n ∪ (transDeps ≫ n)` -/
@[inline] def Needs.transitiveClosure (n : Needs) (transDeps : Hierarchy) : Needs :=
  n.addPostcompose (base := n) transDeps

scoped instance : Shake.HTransClosure Hierarchy Needs Needs where
  htransClosure transDeps n := n.transitiveClosure transDeps

end ImportGraph.Shake

namespace Lake.Shake

open ImportGraph.Shake

-- -- Following is via `addTransitiveImps`.
-- -- Could also do it via `Needs.postcompose` + `n ∪ ·`
-- /-- Transitively closes a `Needs` with respect to an import hierarchy `transDeps`. -/
-- def Needs.transitiveClosure' (transDeps : Array Needs) (n : Needs) : Needs := Id.run do
--   let mut needs := n
--   for (k, i) in n do
--     needs := addTransitiveImps needs { k with module := .anonymous } i transDeps[i]!
--   return needs

/-
Can decompose `addTransitiveImps` into `transitiveImps` (on `empty`); `addTransitiveImps n .. = n ∪ transitiveImps ..`; `transitiveImps = Import.generate = .prearrow i k ∪ Import.postcompose `
-/

-- Widget that's a sort of grid with hovers, for debugging

-- def NeedsKind.publics : Array NeedsKind := NeedsKind.all.filter (·.isExported)

/--
Includes the public visibilities in the corresponding private visibilities, to represent a "has" relationship. Note that
```
a.transitiveClosure transDeps |>.linearize = a.linearize.transitiveClosure transDeps
```
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
Adds in the reflexive availibilities of a given module, which are just the public and private availabilities and not the meta phase versions. This matches what is available within a given module. Equivalent to `a ∪ .reflOf i`.

Note that this operation does *not* necessarily commute with transitive closure.
-/
@[inline] def Needs.reflexify (i : Nat) (a : Needs) : Needs := { a with
  pub := a.pub ∪ {i}
  priv := a.priv ∪ {i} }

@[inline] def Needs.unreflexify (i : Nat) (a : Needs) : Needs :=
  a.map (· \ {i})

@[inline] def Needs.fill (i : Nat) (a : Needs) : Needs := a.linearize.reflexify i

def Needs.fillHierarchy (transDeps : Hierarchy) : Hierarchy :=
  /- Note that `.linearize` commutes with `.reflexify`. -/
  transDeps.mapIdx fun i n => n.fill i

/-- Checks if the arrows `j ⟦m, p⟫ i` are covered by `transDeps`, after filling (linearizing and reflexifying). Does not assume `transDeps` are filled. -/
def Needs.coveredBy (needs : Needs) (i : Nat) (transDeps : Hierarchy) : Bool :=
  /- Note that `.linearize` commutes with `.reflexify`. -/
  needs.directLe <| transDeps[i]!.fill i

/-- Checks if the prearrows `j ⟦m, p⟫ ·` in `n₁` are included in the arrows provided by the transitive closure of `n₂` with respect to the import hierarchy. Linearizes `n₂`, and therefore the transitive closure we're comparing against. -/
def Needs.subsumedBy (n₁ n₂ : Needs) (transDeps : Hierarchy) : Bool :=
  n₁.directLe transDeps⟦n₂.linearize⟧

/--
Returns an antilinearized `reduced : Needs` such that
```
a ≤ reduced.linearize.transitiveClosure transDeps
```
and `reduced` is minimal (perhaps non-uniquely) among such `Needs`.

Does not assume any linearization of `transDeps` or `a`.
-/
def Needs.reduce (a : Needs) (transDeps : Hierarchy) : Needs := Id.run do
  let mut reduced := a.linearize
  let a := a.antilinearize -- avoids unnecessary checks
  -- ensure we handle public/private first, since these may reduce meta
  for k in #[NeedsKind.pub, .priv, .metaPub, .metaPriv] do
    for i in a.get k |>.highToLow do -- note: traverses high to low
      if reduced.has k i then -- `(k, i)` may have been eliminated already
        reduced := reduced \ (transDeps[i]! ≫ k).linearize
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
transitively closed, nor does `transDeps` need to be filled. -/
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
transitively closed, nor does `transDeps` need to be filled. -/
@[inline] def Needs.coverings (transDeps : Hierarchy) (prevs : Array Bitset) (needs : Needs) :
    Array ModuleIdx :=
  needs.coveringsBy transDeps fun i j => prevs[i]!.lt prevs[j]!

end Lake.Shake

namespace ImportGraph

def sortByDepthThenSize (mods : Array ModuleIdx) (depths : Array Nat) (prevs : Array Bitset) :
    Array ModuleIdx :=
  mods.qsort fun i j =>
    (compare depths[i]! depths[j]! |>.then <| compare prevs[i]!.size prevs[j]!.size).isLT

end ImportGraph
