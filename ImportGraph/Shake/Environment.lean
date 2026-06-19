module

import all ImportGraph.Shake.Algebra
import ImportGraph.Lean.Environment

open Lean Lake ImportGraph Shake

/-- Computes the transitive closure of a set of imports with respect to an import hierarchy `transDeps`. -/
def _root_.Lean.Environment.transitiveClosureOf (env : Environment)
    (imps : Array Import) (transDeps : Hierarchy) (base : Needs := .empty): Needs :=
  imps.foldl (init := base) fun needs imp =>
    needs ∪ (transDeps⟦(env.getModuleIdx! imp.module, imp)⟧)

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
    let some mod := env.header.moduleData[i]?
      | dbg_trace "yiiikes! {i}"
        continue
    let mut transImps := Needs.empty
    for imp in mod.imports do
      let some j := env.getModuleIdx? imp.module
        | dbg_trace "yiiikes! (2) i := {i}; imp := ({imp});"
          continue
      let some transDepsj := transDeps[j]?
        | dbg_trace "yiiikes! (3) transDeps.size := {transDeps.size}; j := {j}; imp := ({imp}); i := {i}{if transDeps.size + 1 == j then s!"\n{env.header.moduleData[(0 : Nat)...(j : Nat)].toArray.mapIdx fun idx i => s!"{env.allImportedModuleNames[idx]!} with {i.imports}\n"}" else ""}"
          continue
      transImps := addTransitiveImps transImps imp j transDepsj
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

structure KeyStore (α) [BEq α] [Hashable α] where
  store : Std.HashMap α Nat := {}
  ofIdx : Array α := #[]
  fresh : Nat := 0

def KeyStore.getIdxOf {m} {α} [BEq α] [Hashable α] [Monad m] [MonadState (KeyStore α) m] (a : α) :
    m Nat := do
  -- TODO: consider getThenInsertIfNew
  if let some idx := (← get).store.get? a then return idx else
    modifyGet fun keys =>
      let newIdx := keys.fresh
      (newIdx, { keys with
        store := keys.store.insert a newIdx,
        fresh := newIdx + 1
        ofIdx := keys.ofIdx.push a })

def KeyedArray (γ) := Array (Option γ)
deriving Inhabited

def KeyedArray.get? {γ} (arr : KeyedArray γ) (i : Nat) : Option γ :=
  if h : i < arr.size then (id arr : Array _)[i] else none

def KeyedArray.get?' {γ} (arr : KeyedArray γ) (i : Nat) : Option γ :=
  (id arr : Array _)[i]?.join

def KeyedArray.alter {γ} (arr : KeyedArray γ) (i : Nat) (f : Option γ → Option γ) :=
  match compare i arr.size with
  | .lt => arr.modify i f
  | .eq => arr.push (f none)
  | .gt => (id arr : Array _) ++ Array.replicate (i - arr.size - 1) none |>.push (f none)

protected structure ImportGraph.CoreState extends Lake.Shake.State where
  prevs : Array (KeyedArray Bitset) := #[]
  depths : Array (KeyedArray Nat) := #[]

structure ModificationKey (α) where
  target : α
  sources : Array α

def KeyedArray.mkEmptyForKeys (keyIdxs : Array (ModificationKey Nat)) :
    KeyedArray γ :=
  let size := keyIdxs.foldl (init := 0) fun size { target .. } => max size (target + 1)
  Array.replicate size none

def KeyedArray.mkEmptyForIdxs (keyIdxs : Array Nat) :
    KeyedArray γ :=
  let size := keyIdxs.foldl (init := 0) fun size n => max size (n + 1)
  Array.replicate size none
-- TODO: consider moving to `importModules`, or managing with `lake`
-- (see also environment linter internals, which may eventually do the latter)
/-- A lowercase short name for the given database. Useful when exporting to JSON. -/
structure ImportKeyGen (α) [BEq α] [Hashable α] where
  initKeys : ModuleIdx → ImportGraph.CoreState → Array α
  toKeys : ModuleIdx → Import → ModuleIdx → ImportGraph.CoreState → Array (ModificationKey α)

structure ImportGraph.State (α := Unit) [BEq α] [Hashable α] extends
  ImportGraph.CoreState, ImportKeyGen α, KeyStore α

class TreeFlow (γ) where
  init : γ
  -- add src acc
  -- Should this be `Option γ → γ → γ`? Or even just `γ → γ → γ`.
  add : Option γ → Option γ → Option γ

def KeyedArray.mkInitForIdxs (keyIdxs : Array Nat) [TreeFlow γ] :
    KeyedArray γ := Id.run do
  let mut arr := mkEmptyForIdxs keyIdxs
  for idx in keyIdxs do
    arr := arr.set! idx (some TreeFlow.init)
  return arr

instance : TreeFlow Bitset where
  init := {}
  add a b := a.elim b fun a => return a ∪ (← b)

-- Avoid making it `none`
instance : TreeFlow Nat where
  init := 0
  add a b := a.elim b fun a => return max (a + 1) (← b)

-- Instead of `KeyedArray`s inside, we could have a `HashMap` or `TreeMap` of `LateArray`s which start later. The ModificationKey thing is mostly the same, but now we don't need to have `Nat`s.
-- Alternatively: flat but effectively rectangular array where each block is of length `env.header.moduleData.size`. When we encounter a new key, we add another block.
-- Really depends on what sort of locality we want I guess.

-- what if we want different modification key layouts for different values?
-- Ideally this is a thing we can iterate on? Would be nice to do it all in a single loop...
-- But really, the structure is now importKey + TreeFlow, I think...
-- Can they be combined?

-- What if we allowed just an arbitrary function that had access to the module data and module index, but had a nice API for adding data to keys by working in a nice monad?
-- `∪ {j}` shows we need more freedom here.

protected partial def ImportGraph.initStateFromEnv {α} [BEq α] [Hashable α] (env : Environment)
    (importKey : ImportKeyGen α) : ImportGraph.State α := Id.run do
  let (s, keyStore) := StateT.run (m := Id) (s := { : KeyStore α }) do
    let mut s : ImportGraph.CoreState := {
      env
      transDeps := Array.mkEmpty env.header.moduleData.size
      prevs := Array.mkEmpty env.header.moduleData.size
      depths := Array.mkEmpty env.header.moduleData.size }
    for i in 0...env.header.moduleData.size do
      let mod := env.header.moduleData[i]!
      let mut transImps := Needs.empty
      let mut idxs ← importKey.initKeys i s |>.mapM KeyStore.getIdxOf
      let mut prevs : KeyedArray Bitset := KeyedArray.mkInitForIdxs idxs
      let mut depths : KeyedArray Nat := KeyedArray.mkInitForIdxs idxs
      for imp in mod.imports do
        let j := env.getModuleIdx! imp.module
        let keyIdxs ← importKey.toKeys j imp i s |>.mapM fun { target, sources } => do
          let tgtIdx ← KeyStore.getIdxOf target
          return {
            target := tgtIdx,
            sources := ← sources.mapM KeyStore.getIdxOf : ModificationKey Nat }
        -- imps := imps.push j
        transImps := addTransitiveImps transImps imp j s.transDeps[j]!
        for { target, sources } in keyIdxs do
          for srcIdx in sources do
            prevs := prevs.alter target (TreeFlow.add (s.prevs[j]!.get? srcIdx) · |>.map (· ∪ {j}))
            depths := depths.alter target (TreeFlow.add (s.depths[j]!.get? srcIdx))
        -- if prevFilter imp then
        --   prev := prev ∪ {j} ∪ s.prevs[j]!
        --   depth := max depth (s.depths[j]! + 1)
      s := { s with
        transDeps := s.transDeps.push transImps
        prevs := s.prevs.push prevs
        depths := s.depths.push depths }
    s := { s with transDepsOrig := s.transDeps }
    return s
  return { s with toImportKeyGen := importKey, toKeyStore := keyStore }
