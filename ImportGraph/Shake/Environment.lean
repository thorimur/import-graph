module

import all ImportGraph.Shake.Algebra
import ImportGraph.Lean.Environment

open Lean Lake Shake

/-- Computes the transitive closure of a set of imports with respect to an import hierarchy `transDeps`. -/
def _root_.Lean.Environment.transitiveClosureOf (env : Environment)
    (imps : Array Import) (transDeps : Array Needs) (base : Needs := .empty): Needs :=
  imps.foldl (init := base) fun needs imp =>
    imp.addTransitiveClosureSingle needs (env.getModuleIdx! imp.module) transDeps

@[inline] def _root_.Lean.Environment.transNeeds (env : Environment) (transDeps : Array Needs) :
    Needs :=
  env.transitiveClosureOf env.header.imports transDeps

/-
def _root_.Lean.Environment.transImps (env : Environment) (transDeps : Array Needs) : Needs := Id.run do
  let mut transImps := .empty
  for imp in env.header.imports do
    let i := env.getModuleIdx! imp.module
    transImps := addTransitiveImps transImps imp i transDeps[i]!
  return transImps
-/

def _root_.Lean.Environment.currentExtraRevUses (env : Environment) : Bitset := Id.run do
  let mut s := {}
  for idx in 0...env.header.moduleData.size do
    if isExtraRevModUse env idx then
      s := s ∪ {idx}
  return s

def setAtNeeds (s : Bitset) (transNeeds : Needs) := transNeeds.map (· ∩ s)

/-- Not transitively closed. -/
def _root_.Lean.Environment.currentExtraRevNeeds (env : Environment) (transNeeds : Needs)
    (base : Needs := .empty) : Needs := Id.run do
  let mut needs := base
  for idx in 0...env.header.moduleData.size do
    if isExtraRevModUse env idx then
      for k in NeedsKind.all do
        if transNeeds.has k idx then
          needs := needs.union k {idx}
  return needs


-- TODO: Okay, I need a way to chain all these things conveniently


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

partial def Lean.Environment.mkPreviousWithDepths (env : Environment)
    (skipInit := true) : Array Bitset × Array Nat := Id.run do
  let mut prevs := Array.mkEmpty env.header.moduleData.size
  let mut depths := Array.mkEmpty env.header.moduleData.size
  for i in 0...env.header.moduleData.size do
    let mod := env.header.moduleData[i]!
    let mut prev := {}
    let mut depth := 0
    for imp in mod.imports do
      unless !skipInit || (`Init).isPrefixOf imp.module do
        let j := env.getModuleIdx! imp.module
        prev := prev ∪ {j} ∪ prevs[j]!
        depth := max depth (depths[j]! + 1)
    prevs := prevs.push prev
    depths := depths.push depth
  return (prevs, depths)

protected structure ImportGraph.State extends Lake.Shake.State where
  prevs : Array Bitset := #[]
  depths : Array Nat := #[]

protected partial def ImportGraph.initStateFromEnv (env : Environment) : ImportGraph.State :=
    Id.run do
  let mut s := {
    env
    transDeps := Array.mkEmpty env.header.moduleData.size
    prevs := Array.mkEmpty env.header.moduleData.size
    depths := Array.mkEmpty env.header.moduleData.size }
  for i in 0...env.header.moduleData.size do
    let mod := env.header.moduleData[i]!
    -- let mut imps := #[]
    let mut prev := {}
    let mut depth := 0
    let mut transImps := Needs.empty
    for imp in mod.imports do
      let j := env.getModuleIdx? imp.module |>.get!
      -- imps := imps.push j
      transImps := addTransitiveImps transImps imp j s.transDeps[j]!
      prev := prev ∪ {j} ∪ s.prevs[j]!
      depth := max depth (s.depths[j]! + 1)
    s := { s with
      transDeps := s.transDeps.push transImps
      prevs := s.prevs.push prev
      depths := s.depths.push depth }
  s := { s with transDepsOrig := s.transDeps }
  return s
