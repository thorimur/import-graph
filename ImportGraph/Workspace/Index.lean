/-
Copyright (c) 2026 Thomas Murrills. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Murrills
-/
import Lean.Data.Json.FromToJson

/-!
# Typed indices, index sets, and index-keyed tables

Dense integer indexing is the efficient representation for the entities of a workspace
(packages, libraries, modules): sets become bitmasks, maps become arrays, and graphs become
arrays of bitmasks. The trouble with using raw `Nat`s everywhere is that a package index, a
library index, and a module index are all `Nat`, and nothing stops you from using one where
another is expected.

This file provides zero-cost *typed* wrappers around that representation:

* `Idx α` — a `Nat` index into the canonical enumeration of `α`s (e.g. `Idx PackageInfo`).
* `IdxSet α` — a set of `Idx α`, backed by a single `Nat` bitmask.
* `Table α β` — a total map `Idx α → β`, backed by an `Array β`.

The phantom parameter `α` names the *index space*: two index spaces are interchangeable
exactly when their `α`s are the same type. All operations are `@[inline]` wrappers around
the underlying `Nat`/`Array` operations, so none of this costs anything at runtime.
-/

namespace ImportGraph

open Lean (Json ToJson FromJson toJson fromJson?)

/-! ## `Idx` -/

/--
A typed index into the canonical enumeration of `α`s in some ambient structure
(e.g. the packages of a `WorkspaceInfo`, or the modules of a `ModuleTable`).

The phantom parameter `α` prevents accidentally using an index into one enumeration as an
index into another: `Idx PackageInfo` and `Idx LibraryInfo` are distinct types.
-/
structure Idx (α : Type u) where
  /-- The underlying numeric index. -/
  toNat : Nat

namespace Idx

-- Instances are written by hand rather than derived: `α` is phantom, and `deriving` would
-- needlessly require instances for it (e.g. `[BEq α]`).
instance : BEq (Idx α) := ⟨(·.toNat == ·.toNat)⟩
instance : Hashable (Idx α) := ⟨(hash ·.toNat)⟩
instance : Ord (Idx α) := ⟨(compare ·.toNat ·.toNat)⟩
instance : DecidableEq (Idx α) := fun a b =>
  match a, b with
  | ⟨m⟩, ⟨n⟩ => decidable_of_iff (m = n) (by simp)
instance : Repr (Idx α) := ⟨fun i n => reprPrec i.toNat n⟩
instance : Inhabited (Idx α) := ⟨⟨0⟩⟩
instance : LT (Idx α) := ⟨(·.toNat < ·.toNat)⟩
instance : LE (Idx α) := ⟨(·.toNat ≤ ·.toNat)⟩
instance (a b : Idx α) : Decidable (a < b) := Nat.decLt a.toNat b.toNat
instance (a b : Idx α) : Decidable (a ≤ b) := Nat.decLe a.toNat b.toNat
instance : ToString (Idx α) := ⟨(toString ·.toNat)⟩
instance : ToJson (Idx α) := ⟨(toJson ·.toNat)⟩
instance : FromJson (Idx α) := ⟨fun j => Idx.mk <$> fromJson? j⟩

end Idx

/-! ## `IdxSet` -/

/--
A set of typed indices `Idx α`, backed by a single `Nat` bitmask: `i ∈ s` iff bit `i` of
`s.toNat` is set.

This is the efficient representation for subsets of a dense enumeration (e.g. "the modules
belonging to this library"): union, intersection, difference, and inclusion are single
(GMP-backed) `Nat` operations, regardless of how many elements the set contains.
-/
structure IdxSet (α : Type u) where
  /-- The underlying bitmask. -/
  toNat : Nat := 0

namespace IdxSet

-- Hand-written instances; see the note on `Idx`.
instance : BEq (IdxSet α) := ⟨(·.toNat == ·.toNat)⟩
instance : Hashable (IdxSet α) := ⟨(hash ·.toNat)⟩
instance : DecidableEq (IdxSet α) := fun s t =>
  match s, t with
  | ⟨m⟩, ⟨n⟩ => decidable_of_iff (m = n) (by simp)
instance : Inhabited (IdxSet α) := ⟨⟨0⟩⟩

/-- The empty set. -/
@[inline] def empty : IdxSet α := {}

instance : EmptyCollection (IdxSet α) := ⟨.empty⟩

/-- The set `{0, ..., n - 1}`, i.e. the full index space of an enumeration of size `n`. -/
@[inline] def univ (n : Nat) : IdxSet α := ⟨(1 <<< n) - 1⟩

/-- The singleton set `{i}`. -/
@[inline] def singleton (i : Idx α) : IdxSet α := ⟨1 <<< i.toNat⟩

instance : Singleton (Idx α) (IdxSet α) := ⟨singleton⟩

@[inline] def contains (s : IdxSet α) (i : Idx α) : Bool :=
  (s.toNat >>> i.toNat) &&& 1 == 1

instance : Membership (Idx α) (IdxSet α) := ⟨fun s i => s.contains i = true⟩
instance (i : Idx α) (s : IdxSet α) : Decidable (i ∈ s) :=
  inferInstanceAs (Decidable (_ = _))

@[inline] def insert (s : IdxSet α) (i : Idx α) : IdxSet α :=
  ⟨s.toNat ||| (1 <<< i.toNat)⟩

instance : Insert (Idx α) (IdxSet α) := ⟨fun i s => s.insert i⟩

@[inline] def erase (s : IdxSet α) (i : Idx α) : IdxSet α :=
  if s.contains i then ⟨s.toNat ^^^ (1 <<< i.toNat)⟩ else s

@[inline] def union (s t : IdxSet α) : IdxSet α := ⟨s.toNat ||| t.toNat⟩
@[inline] def inter (s t : IdxSet α) : IdxSet α := ⟨s.toNat &&& t.toNat⟩

/-- Set difference. (`Nat` has no complement, so this isolates the bits of `s` not in `t`.) -/
@[inline] def sdiff (s t : IdxSet α) : IdxSet α := ⟨s.toNat &&& (s.toNat ^^^ t.toNat)⟩

instance : Union (IdxSet α) := ⟨union⟩
instance : Inter (IdxSet α) := ⟨inter⟩
instance : SDiff (IdxSet α) := ⟨sdiff⟩

@[inline] def isEmpty (s : IdxSet α) : Bool := s.toNat == 0

/-- Subset (not necessarily strict). -/
@[inline] def subset (s t : IdxSet α) : Bool := s.toNat &&& t.toNat == s.toNat

/-- Strict subset. -/
@[inline] def ssubset (s t : IdxSet α) : Bool := s.subset t && s != t

instance : HasSubset (IdxSet α) := ⟨fun s t => s.subset t = true⟩
instance (s t : IdxSet α) : Decidable (s ⊆ t) :=
  inferInstanceAs (Decidable (_ = _))
instance : HasSSubset (IdxSet α) := ⟨fun s t => s.ssubset t = true⟩
instance (s t : IdxSet α) : Decidable (s ⊂ t) :=
  inferInstanceAs (Decidable (_ = _))

/-- Whether `s` and `t` have an element in common. -/
@[inline] def intersects (s t : IdxSet α) : Bool := s.toNat &&& t.toNat != 0

/-- The number of elements in the set (population count). -/
def size (s : IdxSet α) : Nat := Id.run do
  let mut n := s.toNat
  let mut acc := 0
  while n != 0 do
    n := n &&& (n - 1) -- clears the lowest set bit
    acc := acc + 1
  return acc

/-- The least element, if the set is nonempty. -/
@[inline] def min? (s : IdxSet α) : Option (Idx α) :=
  if s.toNat == 0 then none else
    some ⟨(s.toNat ^^^ (s.toNat &&& (s.toNat - 1))).log2⟩

/-- The greatest element, if the set is nonempty. -/
@[inline] def max? (s : IdxSet α) : Option (Idx α) :=
  if s.toNat == 0 then none else some ⟨s.toNat.log2⟩

/--
Fold `f` over the elements of `s` in increasing index order, with early exit.
(The binder order matches `ForIn.forIn`, so that this can directly serve as the
`ForIn` instance.)
-/
@[specialize f]
protected def forIn {m : Type v → Type w} {β : Type v} [Monad m] (s : IdxSet α) (init : β)
    (f : Idx α → β → m (ForInStep β)) : m β :=
  -- `fuel` is an upper bound on the number of bits remaining in `n`;
  -- structural recursion on it sidesteps a well-foundedness argument.
  go (s.toNat.log2 + 1) s.toNat 0 init
where
  @[specialize f]
  go : (fuel n i : Nat) → β → m β
  | 0, _, _, acc | _, 0, _, acc => pure acc
  | fuel + 1, n, i, acc => do
    if n &&& 1 == 1 then
      match ← f ⟨i⟩ acc with
      | .done b => return b
      | .yield b => go fuel (n >>> 1) (i + 1) b
    else
      go fuel (n >>> 1) (i + 1) acc

/-- Iteration is in increasing index order. -/
instance [Monad m] : ForIn m (IdxSet α) (Idx α) := ⟨IdxSet.forIn⟩

@[specialize f]
def foldl (s : IdxSet α) (f : β → Idx α → β) (init : β) : β := Id.run do
  let mut acc := init
  for i in s do
    acc := f acc i
  return acc

@[inline] def any (s : IdxSet α) (f : Idx α → Bool) : Bool := Id.run do
  for i in s do
    if f i then return true
  return false

@[inline] def all (s : IdxSet α) (f : Idx α → Bool) : Bool := Id.run do
  for i in s do
    unless f i do return false
  return true

@[inline] def filter (s : IdxSet α) (f : Idx α → Bool) : IdxSet α :=
  s.foldl (init := ∅) fun acc i => if f i then acc.insert i else acc

/-- The elements of the set, in increasing order. -/
@[inline] def toArray (s : IdxSet α) : Array (Idx α) :=
  s.foldl (init := #[]) (·.push ·)

@[inline] def ofArray (a : Array (Idx α)) : IdxSet α :=
  a.foldl (init := ∅) (·.insert ·)

instance : ToString (IdxSet α) := ⟨fun s => toString (s.toArray.map (·.toNat))⟩

private def hexDigit? (c : Char) : Option Nat :=
  if '0' ≤ c && c ≤ '9' then some (c.toNat - '0'.toNat)
  else if 'a' ≤ c && c ≤ 'f' then some (c.toNat - 'a'.toNat + 10)
  else if 'A' ≤ c && c ≤ 'F' then some (c.toNat - 'A'.toNat + 10)
  else none

/-- Serialized as the underlying bitmask (in hex, as a JSON string), for compactness. -/
instance : ToJson (IdxSet α) := ⟨fun s => toJson (String.ofList (Nat.toDigits 16 s.toNat))⟩
instance : FromJson (IdxSet α) := ⟨fun j => do
  let s : String ← fromJson? j
  let mut n := 0
  for c in s.toList do
    let some d := hexDigit? c
      | throw s!"invalid bitmask digit '{c}'"
    n := n <<< 4 ||| d
  return ⟨n⟩⟩

end IdxSet

/-! ## `Table` -/

/--
A total map `Idx α → β`, backed by an `Array β`: row `i` holds the datum for the `i`-th `α`
of the canonical enumeration.

`Table α β` is to `Array β` what `Idx α` is to `Nat`: the same representation, tagged with
the index space it is meant to be indexed by. A `Table ModuleInfo FilePath` cannot be
accidentally indexed by an `Idx LibraryInfo`.
-/
structure Table (α : Type u) (β : Type v) where
  /-- The underlying array of rows. -/
  toArray : Array β

namespace Table

-- Hand-written instances; see the note on `Idx`.
instance [BEq β] : BEq (Table α β) := ⟨(·.toArray == ·.toArray)⟩
instance [Repr β] : Repr (Table α β) := ⟨fun t n => reprPrec t.toArray n⟩
instance : Inhabited (Table α β) := ⟨⟨#[]⟩⟩

@[inline] def empty : Table α β := ⟨#[]⟩

instance : EmptyCollection (Table α β) := ⟨.empty⟩

@[inline] def size (t : Table α β) : Nat := t.toArray.size

@[inline] def isEmpty (t : Table α β) : Bool := t.toArray.isEmpty

instance : GetElem (Table α β) (Idx α) β fun t i => i.toNat < t.size where
  getElem t i h := t.toArray[i.toNat]

@[inline] def get! [Inhabited β] (t : Table α β) (i : Idx α) : β := t.toArray[i.toNat]!

@[inline] def get? (t : Table α β) (i : Idx α) : Option β := t.toArray[i.toNat]?

@[inline] def set (t : Table α β) (i : Idx α) (b : β) : Table α β :=
  ⟨t.toArray.set! i.toNat b⟩

@[inline] def modify (t : Table α β) (i : Idx α) (f : β → β) : Table α β :=
  ⟨t.toArray.modify i.toNat f⟩

@[inline] def push (t : Table α β) (b : β) : Table α β := ⟨t.toArray.push b⟩

/-- The index that `push` would assign to the next row. -/
@[inline] def nextIdx (t : Table α β) : Idx α := ⟨t.size⟩

@[inline] def map (f : β → γ) (t : Table α β) : Table α γ := ⟨t.toArray.map f⟩

@[inline] def mapIdx (f : Idx α → β → γ) (t : Table α β) : Table α γ :=
  ⟨t.toArray.mapIdx fun i b => f ⟨i⟩ b⟩

/-- A table with `n` copies of `b`. -/
@[inline] def replicate (n : Nat) (b : β) : Table α β := ⟨.replicate n b⟩

/-- All indices of the table, in increasing order. -/
@[inline] def idxs (t : Table α β) : Array (Idx α) :=
  Array.ofFn (n := t.size) fun i => ⟨i⟩

/-- The full index set `{0, ..., size - 1}` of the table. -/
@[inline] def univ (t : Table α β) : IdxSet α := .univ t.size

/-- Fold over `(index, row)` pairs in increasing index order. -/
@[specialize f]
def foldlIdx (t : Table α β) (f : γ → Idx α → β → γ) (init : γ) : γ := Id.run do
  let mut acc := init
  for h : i in 0...t.size do
    acc := f acc ⟨i⟩ t.toArray[i]
  return acc

@[inline] def findIdx? (t : Table α β) (f : β → Bool) : Option (Idx α) :=
  t.toArray.findIdx? f |>.map (⟨·⟩)

/-- Iteration yields `(index, row)` pairs in increasing index order. -/
instance [Monad m] : ForIn m (Table α β) (Idx α × β) where
  forIn t init f := do
    let mut acc := init
    for h : i in 0...t.size do
      match ← f (⟨i⟩, t.toArray[i]) acc with
      | .done b => return b
      | .yield b => acc := b
    return acc

instance [Lean.ToJson β] : ToJson (Table α β) := ⟨fun t => toJson t.toArray⟩
instance [Lean.FromJson β] : FromJson (Table α β) := ⟨fun j => Table.mk <$> fromJson? j⟩

end Table

end ImportGraph
