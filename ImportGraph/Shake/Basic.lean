module

import all Lake.CLI.Shake

open Lean Lake.Shake

def Nat.numSetBits (n : Nat) : Nat := Id.run do
  let mut n := n
  let mut acc := 0
  while n != 0 do
    n := n &&& (n - 1) -- clears the lowest set bit
    acc := acc + 1
  return acc

namespace Lake.Shake

/-!
Note: this module must be imported via `import all`.
-/

-- TODO: document

section bitset

@[inline] def Bitset.size (s : Bitset) : Nat := s.toNat.numSetBits

@[specialize f]
def Bitset.foldOneIdxs (s : Bitset) (init : α) (f : α → Nat → α) : α := Id.run do
  let mut n := s.toNat
  let mut acc := init
  while n != 0 do
    let i := n.log2 -- highest bit idx
    acc := f acc i
    n := n ^^^ (1 <<< i)
  return acc

/-- High to low. -/
@[inline] def Bitset.toIdxs (s : Bitset) : Array Nat := s.foldOneIdxs #[] (·.push ·)
@[inline] def Bitset.highestIdx? (s : Bitset) : Option Nat :=
  if s.toNat != 0 then s.toNat.log2 else none
@[inline] def Bitset.isEmpty (s : Bitset) : Bool := s.toNat == 0
-- TODO: notation? use `∩`?
@[inline] def Bitset.le (a b : Bitset) : Bool := a.toNat &&& b.toNat == a.toNat
@[inline] def Bitset.lt (a b : Bitset) : Bool := a.le b && a != b

instance : SDiff Bitset where
  sdiff a b := { toNat := a.toNat &&& (a.toNat ^^^ b.toNat) }

@[specialize f]
protected def Bitset.forIn {m} [Monad m] {β : Type} (s : Bitset) (init : β)
    (f : Nat → β → m (ForInStep β)) : m β := do
  let mut n := s.toNat
  let mut acc := init
  while n != 0 do
    let i := n.log2
    match ← f i acc with
    | .done b => return b
    | .yield b => acc := b
    n := n ^^^ (1 <<< i)
  return acc

instance {m} [Monad m] : ForIn m Bitset Nat where
  forIn := Bitset.forIn

end bitset

section needs

deriving instance BEq for Needs

@[specialize f]
protected def Needs.forIn {m} [Monad m] {β : Type} (s : Needs) (init : β)
    (f : (NeedsKind × Nat) → β → m (ForInStep β)) : m β := do
  let mut acc := init
  for k in NeedsKind.all do
    let mut n := s.get k |>.toNat
    while n != 0 do
      let i := n.log2
      match ← f (k, i) acc with
      | .done b => return b
      | .yield b => acc := b
      n := n ^^^ (1 <<< i)
  return acc

instance {m} [Monad m] : ForIn m Needs (NeedsKind × Nat) where
  forIn := Needs.forIn

def Needs.single (i : Nat) (k : NeedsKind) : Needs := Needs.empty.set k {i}

@[inline] def Needs.onAll (n : Needs) (via : Array NeedsKind → (NeedsKind → β) → α)
    (f : Bitset → β) : α := via NeedsKind.all (f <| n.get ·)
@[inline] def Needs.onAllWithKind (n : Needs) (via : Array NeedsKind → (NeedsKind → β) → α)
    (f : NeedsKind → Bitset → β) : α := via NeedsKind.all fun k => f k <| n.get k

@[inline] def Needs.any (n : Needs) (f : Bitset → Bool) : Bool := n.onAll (·.any) f
@[inline] def Needs.all (n : Needs) (f : Bitset → Bool) : Bool := n.onAll (·.all) f
@[inline] def Needs.fold (n : Needs) (f : Bitset → α → α) (init : α) : α :=
  n.onAll (·.foldr (init := init)) f

@[inline] def Needs.anyWithKind (n : Needs) (f : NeedsKind → Bitset → Bool) : Bool :=
  n.onAllWithKind (·.any) f
@[inline] def Needs.allWithKind (n : Needs) (f : NeedsKind → Bitset → Bool) : Bool :=
  n.onAllWithKind (·.all) f
@[inline] def Needs.foldWithKind (n : Needs) (f : NeedsKind → Bitset → α → α) (init : α) : α :=
  n.onAllWithKind (·.foldr (init := init)) f

@[specialize f] def Needs.map (n : Needs) (f : Bitset → Bitset) : Needs where
  pub := f n.pub
  priv := f n.priv
  metaPub := f n.metaPub
  metaPriv := f n.metaPriv

@[specialize f] def Needs.mapWithKind (n : Needs) (f : NeedsKind → Bitset → Bitset) : Needs where
  pub := f .pub n.pub
  priv := f .priv n.priv
  metaPub := f .metaPub n.metaPub
  metaPriv := f .metaPriv n.metaPriv

@[specialize f] def Needs.map₂ (n₁ n₂ : Needs) (f : Bitset → Bitset → Bitset) : Needs where
  pub := f n₁.pub n₂.pub
  priv := f n₁.priv n₂.priv
  metaPub := f n₁.metaPub n₂.metaPub
  metaPriv := f n₁.metaPriv n₂.metaPriv

@[specialize f] def Needs.mapWithKind₂ (n₁ n₂ : Needs)
    (f : NeedsKind → Bitset → Bitset → Bitset) : Needs where
  pub := f .pub n₁.pub n₂.pub
  priv := f .priv n₁.priv n₂.priv
  metaPub := f .metaPub n₁.metaPub n₂.metaPub
  metaPriv := f .metaPriv n₁.metaPriv n₂.metaPriv

@[inline] def Needs.isEmpty (n : Needs) : Bool := n.all (·.isEmpty)
@[inline] def Needs.isEmptyAt (k : NeedsKind) (n : Needs) : Bool := n.get k |>.isEmpty

def Needs.toImports (env : Environment) (n : Needs) (skipInit := true) : Array Import := Id.run do
  let mut out := #[]
  for (k, i) in n do
    let some module := env.allImportedModuleNames[i]?
      | dbg_trace "yikes! ({i})"
        continue
    if skipInit && (`Init).isPrefixOf module then continue
    out := out.push {
      module
      isExported := k.isExported
      isMeta := k.isMeta
      importAll := false }
  return out

def _root_.Lean.Import.includeAll (sourceImports newImports : Array Import) :
    Array Import := Id.run do
  let mut newImports := newImports
  for imp in sourceImports do
    if imp.importAll then
      -- Delete any which match up to `importAll`, then include the `all`
      newImports := newImports.filter fun newImp =>
        newImp != { imp with importAll := newImp.importAll}
      newImports := newImports.push imp
  return newImports

instance : SDiff Needs where
  sdiff a b := a.map₂ b (· \ ·)

instance : ToMessageData NeedsKind where
  toMessageData
    | .pub => "public"
    | .metaPub => "public meta"
    | .priv => "private"
    | .metaPriv => "private meta"
/- Note: we run this a lot, so implement it directly and ensure it stays up-to-date with
`NeedsKind.all` via proof. -/

/-- Whether each field of the first `Needs` is contained within the corresponding field of the second. Use with caution: this does not necessarily indicate that one `Needs` subsumes another. See also `Needs.coveredBy` for testing against an import hierarchy. -/
def Needs.directLe (n m : Needs) : Bool :=
  n.pub.le m.pub &&
  n.priv.le m.priv &&
  n.metaPub.le m.metaPub &&
  n.metaPriv.le m.metaPriv

private def Needs.directLe' (n m : Needs) : Bool := n.allWithKind fun k set => set.le <| m.get k

theorem Needs.directLe_eq_directLe' : Needs.directLe = Needs.directLe' := by
  ext; simp [directLe, directLe', allWithKind, onAllWithKind, NeedsKind.all, get, Bool.and_assoc]
