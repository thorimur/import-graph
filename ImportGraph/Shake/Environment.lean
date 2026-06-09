module

import all ImportGraph.Shake.Algebra
import ImportGraph.Lean.Environment

open Lean Lake Shake

def _root_.Lean.Environment.transitiveClosureOf (env : Environment)
    (imps : Array Import) (transDeps : Array Needs) : Needs :=
  imps.foldl (init := .empty) fun needs imp =>
    imp.addTransitiveClosure needs (env.getModuleIdx! imp.module) transDeps

@[inline] def _root_.Lean.Environment.transNeeds (env : Environment) (transDeps : Array Needs) :
    Needs :=
  env.transitiveClosureOf env.header.imports transDeps

-- TODO: Okay, I need a way to chain all these things

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
