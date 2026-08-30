module

import ImportGraph.Shake.Algebra
import ImportGraph.Lean.Environment
import Lake.CLI.Shake
public import Lean.Environment
public import ImportGraph.Shake.Algebra

open Lean ImportGraph Shake Lean

namespace ImportGraph.Shake

public section

/-!
# TODO

This should never interact with the workspace model approach, and we should disclaim that.
-/

/-- Computes the transitive closure of a set of imports with respect to an import hierarchy `transDeps`. -/
def Lean.Environment.transitiveClosureOf (env : Environment)
    (imps : Array Import) (transDeps : ArrayHierarchy) (base : Needs := .empty) : Needs :=
  imps.foldl (init := base) fun needs imp =>
    needs ∪ transDeps⟦(id (α := Nat) (env.getModuleIdx! imp.module), imp)⟧

@[inline] def Lean.Environment.currentTransNeeds (env : Environment)
    (transDeps : ArrayHierarchy) (excluding : NameSet := {}) : Needs :=
  env.transitiveClosureOf (env.header.imports.filter (!excluding.contains ·.module)) transDeps

/-
def _root_.Lean.Environment.transImps (env : Environment) (transDeps : Array Needs) : Needs := Id.run do
  let mut transImps := .empty
  for imp in env.header.imports do
    let i := env.getModuleIdx! imp.module
    transImps := addTransitiveImps transImps imp i transDeps[i]!
  return transImps
-/

-- def Lean.Environment.currentExtraRevUses (env : Environment) : Bitset := Id.run do
--   let mut s := {}
--   for idx in 0...env.header.moduleData.size do
--     if isExtraRevModUse env idx then
--       s := s ∪ {idx}
--   return s

-- def setAtNeeds (s : Bitset) (transNeeds : Needs) := transNeeds.map (· ∩ s)

-- /-- Not transitively closed. -/
-- def _root_.Lean.Environment.currentExtraRevNeeds (env : Environment) (transNeeds : Needs)
--     (base : Needs := .empty) : Needs := Id.run do
--   let mut needs := base
--   for idx in 0...env.header.moduleData.size do
--     if isExtraRevModUse env idx then
--       for k in NeedsKind.all do
--         if transNeeds.has k idx then
--           needs := needs.union k {idx}
--   return needs


-- TODO: Okay, I need a way to chain all these things conveniently

/-- Creates an `Array Needs` of transitive dependencies among modules present in the environment.
Assumes that modules in the environment are topologically sorted.

**Caution:** Lean imports more modules when in the language server than during a typical
`lake build`. As such, this should *only* be used in cases where `Needs` information for the
modules guaranteed to be present in the environment during build is sufficient, or else behavior
should be gated on the value of the option `Elab.inServer`. -/
partial def Lean.Environment.mkTransDeps (env : Environment) : ArrayHierarchy := Id.run do
  let mut transDeps := Array.mkEmpty env.header.moduleData.size
  for h : i in 0...env.header.moduleData.size do
    let mod := env.header.moduleData[i]
    let mut transImps := Needs.reflOf i
    for imp in mod.imports do
      -- As per the module system, not every import-of-an-import is also imported.
      let some j := env.getModuleIdx? imp.module | continue
      let some transDepsj := transDeps[j]?
        -- We expect a topological order. Break if Lean breaks this.
        | panic! "Nontopological order encountered:\n\
            `{imp.module}` is imported by `{env.header.modules[i]!.module}`, \
            but comes afterwards in the environment"
          continue
      transImps := transImps ∪ (transDepsj ≫ imp)
    transDeps := transDeps.push transImps.linearize
  return transDeps

-- partial def Lean.Environment.mkTransDepsAndPrev (env : Environment) :
--     Hierarchy × Array Bitset := Id.run do
--   let mut transDeps := Array.mkEmpty env.header.moduleData.size
--   let mut prevs := Array.mkEmpty env.header.moduleData.size
--   for i in 0...env.header.moduleData.size do
--     let mod := env.header.moduleData[i]!
--     let mut transImps := Needs.reflOf i
--     let mut prev := {}
--     for imp in mod.imports do
--       let j := env.getModuleIdx! imp.module
--       prev := prev ∪ {j} ∪ prevs[j]!
--       transImps := transDeps[j]! ≫
--     transDeps := transDeps.push transImps
--     prevs := prevs.push prev
--   return (transDeps, prevs)

-- partial def Lean.Environment.mkPrevious (env : Environment) : Array Bitset := Id.run do
--   let mut prevs := Array.mkEmpty env.header.moduleData.size
--   for i in 0...env.header.moduleData.size do
--     let mod := env.header.moduleData[i]!
--     let mut prev := {}
--     for imp in mod.imports do
--       let j := env.getModuleIdx! imp.module
--       prev := prev ∪ {j} ∪ prevs[j]!
--     prevs := prevs.push prev
--   return prevs

partial def Lean.Environment.mkPreviousWithDepths (env : Environment)
    (filter : Import → Bool := fun _ => true)
    (skipInit := true) : Array Bitset × Array Nat := Id.run do
  let mut prevs := Array.mkEmpty env.header.moduleData.size
  let mut depths := Array.mkEmpty env.header.moduleData.size
  for i in 0...env.header.moduleData.size do
    let mod := env.header.moduleData[i]!
    let mut prev := {}
    let mut depth := 0
    for imp in mod.imports do
      unless (!skipInit || (`Init).isPrefixOf imp.module) && !(filter imp) do
        let j := env.getModuleIdx! imp.module
        prev := prev ∪ {j} ∪ prevs[j]!
        depth := max depth (depths[j]! + 1)
    prevs := prevs.push prev
    depths := depths.push depth
  return (prevs, depths)
