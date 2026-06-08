module

import all ImportGraph.Shake.Basic

open Lean Lake.Shake

namespace Lean

/-- Given an abstract import `[m,p⟩` and a collection of prearrows `j ⟦m',p'⟫ ·` (`Needs`), add to `composed` the composed prearrows `j ⟦m',p'⟫[m,p⟩ ·` where composition is possible. -/
def Import.addPostcompose (composed : Needs) (imp : Import) (impTransDeps : Needs) :
    Needs :=Id.run do
  let mut composed := composed
  -- `⟦m, 1⟫[m', p⟩  ⇒  ⟦m ∨ m', p⟫`
  for k' in #[NeedsKind.pub, .metaPub] do -- `∀ (m, 1)`
    composed := composed.union
      { isMeta := k'.isMeta || imp.isMeta, isExported := imp.isExported }
      (impTransDeps.get k') -- `j ⟦m, 1⟫ ·`
  -- `⟦m, 0⟫[0, 2⟩  ⇒  ⟦m, 0⟫`
  if imp.importAll && !imp.isMeta then -- only apply to `[0, 2⟩`
    for k in #[NeedsKind.priv, .metaPriv] do -- `∀ (m, 0)`
      composed := composed.union k (impTransDeps.get k)
  composed

/-- Given an abstract import `[m,p⟩` and a collection of prearrows `j ⟦m',p'⟫ ·` (`Needs`), forms the composed prearrows `j ⟦m',p'⟫[m,p⟩ ·` where composition is possible. -/
@[inline] def Import.postcompose (imp : Import) (impTransDeps : Needs) : Needs :=
  imp.addPostcompose .empty impTransDeps

/-- Given an import hierarchy of arrows `j' ⟦_⟫ j` and a preimport `i [imp⟩ ·`, forms the set of prearrows obtained by transitively closing `i [imp⟩ ·` with respect to the import hierarchy. This is `i [imp⟩ ·` together with compositions `j ⟦_⟫ i [imp⟩ ·`. -/
@[inline] def Import.transitiveClosure (i : Nat) (imp : Import) (transDeps : Array Needs) : Needs :=
  imp.addPostcompose (.single { imp with } i) transDeps[i]!

/-- Given an import hierarchy of arrows `j' ⟦_⟫ j` and a preimport `i [imp⟩ ·`, adds to `n` the set of prearrows obtained by transitively closing `i [imp⟩ ·` with respect to the import hierarchy. This is `i [imp⟩ ·` together with compositions `j ⟦_⟫ i [imp⟩ ·`. -/
@[inline] def Import.addTransitiveClosure (n : Needs) (i : Nat) (imp : Import)
    (transDeps : Array Needs) : Needs :=
  imp.addPostcompose (n.union { imp with } {i}) transDeps[i]!

end Lean

namespace Lake.Shake

/-- Given an abstract `NeedsKind` `⟦m, p⟫` and a collection of prearrows `j ⟦m',p'⟫ ·` (`Needs`), forms the composed prearrows `j ⟦m',p'⟫⟦m,p⟫ ·` where composition is possible. -/
def NeedsKind.postcompose (k : NeedsKind) (n : Needs) : Needs := Id.run do
  let mut composed := .empty
  -- `⟦m, 1⟫⟦m', p⟫  ⇒  ⟦m ∨ m', p⟫`
  for k' in #[NeedsKind.pub, .metaPub] do -- ∀ (m, 1)
    composed := composed.union
      { isMeta := k'.isMeta || k.isMeta, isExported := k.isExported }
      (n.get k') -- `j ⟦m, 1⟫ ·`
  composed

/-- Given a set of prearrows `i ⟦m, p⟫ ·` and an import hierarchy, includes in `base` the compositions of arrows `j ⟦m',p'⟫ i ⟦m,p⟫ ·` where composition is possible. -/
def Needs.addPostcompose (base n : Needs) (transDeps : Array Needs) : Needs := Id.run do
  let mut composed := base
  for (k, i) in n do
    composed := composed ∪ k.postcompose transDeps[i]!
  composed

/-- Given a set of prearrows `i ⟦m, p⟫ ·` and an import hierarchy, forms the compositions of arrows `j ⟦m',p'⟫ i ⟦m,p⟫ ·` where composition is possible. -/
@[inline] def Needs.postcompose (n : Needs) (transDeps : Array Needs) : Needs :=
  addPostcompose (base := .empty) n transDeps

@[inline] def Needs.addTransitiveClosure (base n : Needs) (transDeps : Array Needs) : Needs :=
  addPostcompose (base := base ∪ n) n transDeps

/-- `n ∪ (transDeps ≫ n)` -/
@[inline] def Needs.transitiveClosure (n : Needs) (transDeps : Array Needs) : Needs :=
  addPostcompose (base := n) n transDeps


-- Following is via `addTransitiveImps`.
-- Could also do it via `Needs.postcompose` + `n ∪ ·`
/-- Transitively closes a `Needs` with respect to an import hierarchy `transDeps`. -/
def Needs.transitiveClosure' (transDeps : Array Needs) (n : Needs) : Needs := Id.run do
  let mut needs := n
  for (k, i) in n do
    needs := addTransitiveImps needs { k with module := .anonymous } i transDeps[i]!
  return needs

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

/--
Adds in the reflexive availibilities of a given module, which are just the public and private availabilities and not the meta phase versions. This matches what is available within a given module. Equivalent to `a ∪ .reflOf i`.

Note that this operation does *not* necessarily commute with transitive closure.
-/
@[inline] def Needs.reflexify (i : Nat) (a : Needs) : Needs := { a with
  pub := a.pub ∪ {i}
  priv := a.priv ∪ {i} }

@[inline] def Needs.unreflexify (i : Nat) (a : Needs) : Needs :=
  a.map (· \ {i})

def Needs.fillTransDeps (transDeps : Array Needs) : Array Needs :=
  /- Note that `.linearize` commutes with `.reflexify`. -/
  transDeps.mapIdx fun i n => n.linearize.reflexify i

/--
Returns an antilinearized `reduced : Needs` such that
```
a ≤ reduced.linearize.transitiveClosure transDeps
```
and `reduced` is minimal (perhaps non-uniquely) among such `Needs`.
-/
def Needs.reduce (a : Needs) (transDeps : Array Needs) : Needs := Id.run do
  let mut reduced := a.linearize
  let a := a.antilinearize -- avoids unnecessary checks
  -- ensure we handle public/private first, since these may reduce meta
  for k in #[NeedsKind.pub, .priv, .metaPub, .metaPriv] do
    for i in a.get k do -- note: traverses high to low
      if reduced.has k i then -- may have been eliminated already
        reduced := reduced \ (k.postcompose transDeps[i]!).linearize
  return reduced.antilinearize
