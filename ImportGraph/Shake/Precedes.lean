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

partial def Lean.Environment.mkTransDeps (env : Environment) : Array Needs := Id.run do
  let mut transDeps := Array.mkEmpty env.header.moduleData.size
  for i in 0...env.header.moduleData.size do
    let mod := env.header.moduleData[i]!
    let mut transImps := Needs.empty
    for imp in mod.imports do
      let j := env.getModuleIdx! imp.module
      transImps := addTransitiveImps transImps imp j transDeps[j]!
    transDeps := transDeps.push transImps
  return transDeps

partial def Lean.Environment.mkTransDepsAndPrev (env : Environment) :
    Array Needs × Array Bitset := Id.run do
  let mut transDeps := Array.mkEmpty env.header.moduleData.size
  let mut prevs := Array.mkEmpty env.header.moduleData.size
  for i in 0...env.header.moduleData.size do
    let mod := env.header.moduleData[i]!
    let mut transImps := Needs.empty
    let mut prev := {}
    for imp in mod.imports do
      let j := env.getModuleIdx! imp.module
      prev := prev ∪ {j} ∪ prevs[j]!
      transImps := addTransitiveImps transImps imp j transDeps[j]!
    transDeps := transDeps.push transImps
    prevs := prevs.push prev
  return (transDeps, prevs)

partial def Lean.Environment.mkPrevious (env : Environment) : Array Bitset := Id.run do
  let mut prevs := Array.mkEmpty env.header.moduleData.size
  for i in 0...env.header.moduleData.size do
    let mod := env.header.moduleData[i]!
    let mut prev := {}
    for imp in mod.imports do
      let j := env.getModuleIdx! imp.module
      prev := prev ∪ {j} ∪ prevs[j]!
    prevs := prevs.push prev
  return prevs
