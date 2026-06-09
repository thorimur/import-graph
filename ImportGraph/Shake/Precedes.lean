module

import all Lake.CLI.Shake
import all ImportGraph.Shake.Basic
import ImportGraph.Lean.Environment

open Lean Lake.Shake

structure Postcedes extends Needs where
  previous : Bitset

def Postcedes.mapNeeds (p : Postcedes) (f : Needs → Needs) : Postcedes :=
  { p with toNeeds := f p.toNeeds }

def Postcedes.modifyKind (p : Postcedes) (k : NeedsKind) (f : Bitset → Bitset) : Postcedes :=
  { p with toNeeds := p.toNeeds.modify k f }

def Postcedes.mapPrevious (p : Postcedes) (f : Bitset → Bitset) : Postcedes :=
  { p with previous := f p.previous }

def Postcedes.map (p : Postcedes) (f : Needs → Needs) (onPrev : Bitset → Bitset) : Postcedes :=
  { toNeeds := f p.toNeeds, previous := onPrev p.previous }

@[inline] def Postcedes.map₂ (p₁ p₂  : Postcedes) (f : Needs → Needs → Needs)
    (onPrev : Bitset → Bitset → Bitset) : Postcedes :=
  { toNeeds := f p₁.toNeeds p₂.toNeeds, previous := onPrev p₁.previous p₂.previous }

instance : Union Postcedes where
  union a b := a.map₂ b (· ∪ ·) (· ∪ ·)

def Postcedes.hierarchyLe (p₁ p₂ : Postcedes) : Bool := p₁.previous.le p₂.previous

-- unbundled?
