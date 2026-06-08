module

import all Lake.CLI.Shake

open Lean Lake.Shake

namespace Lake.Shake

/-!
Note: this module must be imported via `import all`.
-/

-- TODO: document

section bitset

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

def Needs.single (k : NeedsKind) (i : Nat) : Needs := Needs.empty.set k {i}

@[inline] def Needs.onAll (n : Needs) (via : Array NeedsKind → (NeedsKind → β) → α)
    (f : Bitset → β) : α := via NeedsKind.all (f <| n.get ·)

def Needs.any (n : Needs) (f : Bitset → Bool) : Bool := n.onAll (·.any) f
def Needs.all (n : Needs) (f : Bitset → Bool) : Bool := n.onAll (·.all) f
@[inline] def Needs.fold (n : Needs) (f : Bitset → α → α) (init : α) : α :=
  n.onAll (·.foldr (init := init)) f

@[specialize f] def Needs.map (n : Needs) (f : Bitset → Bitset) : Needs where
  pub := f n.pub
  priv := f n.priv
  metaPub := f n.metaPub
  metaPriv := f n.metaPriv

@[specialize f] def Needs.map₂ (n₁ n₂ : Needs) (f : Bitset → Bitset → Bitset) : Needs where
  pub := f n₁.pub n₂.pub
  priv := f n₁.priv n₂.priv
  metaPub := f n₁.metaPub n₂.metaPub
  metaPriv := f n₁.metaPriv n₂.metaPriv

@[inline] def Needs.isEmpty (n : Needs) : Bool := n.all (·.isEmpty)
@[inline] def Needs.isEmptyAt (k : NeedsKind) (n : Needs) : Bool := n.get k |>.isEmpty

def Needs.toImports (env : Environment) (n : Needs) : Array Import := Id.run do
  let mut out := #[]
  for (k, i) in n do
    out := out.push {
      module := env.allImportedModuleNames[i]!
      isExported := k.isExported
      isMeta := k.isMeta
      importAll := false }
  return out

instance : SDiff Needs where
  sdiff a b := a.map₂ b (· \ ·)

instance : ToMessageData NeedsKind where
  toMessageData
    | .pub => "public"
    | .metaPub => "public meta"
    | .priv => "private"
    | .metaPriv => "private meta"
