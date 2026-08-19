module

import all ImportGraph.Shake.Algebra
import ImportGraph.Lean.Environment

open Lean Lake ImportGraph Shake

/-- Computes the transitive closure of a set of imports with respect to an import hierarchy `transDeps`. -/
def _root_.Lean.Environment.transitiveClosureOf (env : Environment)
    (imps : Array Import) (transDeps : Hierarchy) (base : Needs := .empty): Needs :=
  imps.foldl (init := base) fun needs imp =>
    needs ∪ (transDeps⟦(env.getModuleIdx! imp.module, imp)⟧)

@[inline] def _root_.Lean.Environment.currentTransNeeds (env : Environment)
    (transDeps : Array Needs) : Needs :=
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


/-- Creates an `Array Needs` of transitive dependencies among modules present in the environment.
Assumes that modules in the environment are topologically sorted.

**Caution:** Lean imports more modules when in the language server than during a typical
`lake build`. As such, this should *only* be used in cases where `Needs` information for the
modules guaranteed to be present in the environment during build is sufficient, or else behavior
should be gated on the value of the option `Elab.inServer`. -/
partial def Lean.Environment.mkTransDeps (env : Environment) : Array Needs := Id.run do
  let mut transDeps := Array.mkEmpty env.header.moduleData.size
  for h : i in 0...env.header.moduleData.size do
    let mod := env.header.moduleData[i]
    let mut transImps := Needs.empty
    for imp in mod.imports do
      -- Not every import is imported in the current file.
      let some j := env.getModuleIdx? imp.module | continue
      let some transDepsj := transDeps[j]?
        | panic! "Nontopological order encountered:\n\
            `{imp.module}` is imported by `{env.header.modules[i]!.module}`, \
            but comes afterwards in the environment"
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

structure KeyStore (α : Type) [BEq α] [Hashable α] where
  store : Std.HashMap α Nat := {}
  ofIdx : Array α := #[]

def KeyStore.getIdxOf? {α} [BEq α] [Hashable α] (keys : KeyStore α) (a : α) : Option Nat :=
  keys.store.get? a

def KeyStore.getIdxOf {m} {α} [BEq α] [Hashable α] [Monad m] [MonadState (KeyStore α) m] (a : α) :
    m Nat := do
  -- TODO: consider getThenInsertIfNew
  if let some idx := (← get).store.get? a then return idx else
    modifyGet fun keys =>
      let newIdx := keys.ofIdx.size
      (newIdx, { keys with
        store := keys.store.insert a newIdx,
        ofIdx := keys.ofIdx.push a })

@[inline] def KeyStore.ofIdx? {m} {α} [BEq α] [Hashable α] [Monad m] [MonadState (KeyStore α) m]
    (keyIdx : Nat) : m (Option α) := do
  -- TODO: consider getThenInsertIfNew
  return (← get).ofIdx[keyIdx]?

abbrev KeyedArray (γ) := Array (Option γ)

def KeyedArray.get? {γ} (arr : KeyedArray γ) (i : Nat) : Option γ :=
  if h : i < arr.size then arr[i] else none

def KeyedArray.get?' {γ} (arr : KeyedArray γ) (i : Nat) : Option γ :=
  arr[i]?.join

def KeyedArray.alter {γ} (arr : KeyedArray γ) (i : Nat) (f : Option γ → Option γ) :=
  match compare i arr.size with
  | .lt => arr.modify i f
  | .eq => arr.push (f none)
  | .gt => arr ++ Array.replicate (i - arr.size) none |>.push (f none)

nonrec def KeyedArray.set! {γ} (arr : KeyedArray γ) (i : Nat) (val : γ) :=
  match compare i arr.size with
  | .lt => arr.set! i val
  | .eq => arr.push val
  | .gt => arr ++ Array.replicate (i - arr.size) none |>.push val

def KeyedArray.mkEmptyForIdxs (keyIdxs : Array Nat) :
    KeyedArray γ :=
  let size := keyIdxs.foldl (init := 0) fun size n => max size (n + 1)
  Array.replicate size none

-- def KeyedArray.forKeysOf (arr₁ arr₂ : KeyedArray γ)

/-
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

#check ModuleData
-/
namespace ImportGraph
-- TODO: make γ dependent?
class MonadImportFlow (κ γ : Type) (m : Type → Type) where
  -- getImportState : m Lake.Shake.State -- todo: remove? we don't need the whole thing. maybe just env...
  getCurrent : m ModuleIdx -- Should this be somewhere else...? read-only?
  -- setCurrent : ModuleIdx → m Unit
  setCurrentVal : κ → γ → m Unit
  modifyCurrentVal : κ → (Option γ → Option γ) → m Unit
  getPreviousVal? : ModuleIdx → (k : κ) → m (Option γ)

  -- setCurrentValRaw : Nat → γ → m Unit
  -- modifyCurrentValRaw : Nat → (Option γ → Option γ) → m Unit
  -- getPreviousValRaw? : ModuleIdx → Nat → m (Option γ)

class MonadImportFlowOf (κ γ : Type) (m : Type → Type) where
  setTheCurrent : κ → m Unit
  getThePreviousVal : ModuleIdx → Import → (k : κ) → Option γ

structure ImportFlowState (κ γ : Type) where
  currentIdx : ModuleIdx := (0 : Nat) -- Should this be a read-only value?
  currentVals : KeyedArray γ := #[]
  vals : Array (KeyedArray γ) := #[] -- maybe this should be read-only too? or in a different ref?
  currentIdx_eq_vals_size : currentIdx = vals.size := by grind

section

variable {κ γ m} [BEq κ] [Hashable κ] [Monad m] [MonadStateOf (ImportFlowState κ γ) m]



variable (κ) in
@[inline] def setCurrentValRaw (keyIdx : Nat) (val : γ) : m Unit := do
  modifyThe (ImportFlowState κ γ) fun s => { s with
    currentVals := s.currentVals.set! keyIdx val }
variable (κ) in
@[inline] def modifyCurrentValRaw (keyIdx : Nat) (f : Option γ → Option γ) : m Unit := do
    modifyThe (ImportFlowState κ γ) fun s => { s with
      currentVals := s.currentVals.alter keyIdx f }
variable (κ) in
@[inline] def getPreviousValRaw? (j : ModuleIdx) (keyIdx : Nat) : m (Option γ) := do
    return (← getThe (ImportFlowState κ γ)).vals[j]!.get? keyIdx
variable (κ) in
@[inline] def getPreviousValsRaw? (j : ModuleIdx) : m (KeyedArray γ) := do
    return (← getThe (ImportFlowState κ γ)).vals[j]!

instance [MonadStateOf (KeyStore κ) m] : MonadImportFlow κ γ m where
  -- getImportState :=
  getCurrent := return (← getThe (ImportFlowState κ γ)).currentIdx
  -- Assumes `vals[currentModIdx]` exists.
  -- setCurrent idx := modifyThe (ImportFlowState κ γ) fun s => { s with currentIdx := idx }
  setCurrentVal k val := do
    setCurrentValRaw κ (← KeyStore.getIdxOf k) val
  modifyCurrentVal k f := do
    modifyCurrentValRaw κ (← KeyStore.getIdxOf k) f
  getPreviousVal? j k := do
    getPreviousValRaw? κ j (← KeyStore.getIdxOf k)

  -- setCurrentValRaw keyIdx val := do
  --   modifyThe (ImportFlowState κ γ) fun s => { s with
  --     currentVals := s.currentVals.set! keyIdx val }
  -- modifyCurrentValRaw keyIdx f := do
  --   modifyThe (ImportFlowState κ γ) fun s => { s with
  --     currentVals := s.currentVals.alter keyIdx f }
  -- getPreviousValRaw? modIdx keyIdx :=
  --   return (← getThe (ImportFlowState κ γ)).vals[modIdx]!.get? keyIdx

def ImportFlowState.next (κ γ : Type) [MonadStateOf (ImportFlowState κ γ) m] : m Unit := do
  modifyThe (ImportFlowState κ γ) fun s => { s with
    currentIdx := (id s.currentIdx : Nat) + 1
    currentVals := #[]
    vals := s.vals.push s.currentVals
    currentIdx_eq_vals_size := by grind [s.currentIdx_eq_vals_size] }

abbrev ImportFlowRefT (κ) [BEq κ] [Hashable κ] (γ) (m : Type → Type)
    {ω : outParam Type} [STWorld ω m] :=
  StateRefT (ImportFlowState κ γ) $ StateRefT (KeyStore κ) m

nonrec def ImportFlowRefT.run {ω} {κ} [BEq κ] [Hashable κ] {γ}
    {m : Type → Type} [Monad m] [MonadLiftT (ST ω) m] [STWorld ω m]
    {α} (x : ImportFlowRefT κ γ m α) (s : ImportFlowState κ γ := {}) (keys : KeyStore κ := {}) :=
  x.run s |>.run keys

-- nonrec def ImportFlowRefT.run' {ω} {κ} [BEq κ] [Hashable κ] {γ}
--     (m : Type → Type) [Monad m] [MonadLiftT (ST ω) m] [STWorld ω m]
--     {α} (x : ImportFlowRefT κ γ m α) (s : ImportFlowState κ γ) (keys : KeyStore κ := {}) :=
--   x.run' s |>.run' keys

-- TODO: useful return value is `KeyStore` + the vals...we should discard currentIdx and currentVal though.

abbrev ImportFlowT (κ) [BEq κ] [Hashable κ] (γ) (m : Type → Type) :=
  StateT (ImportFlowState κ γ) <| StateT (KeyStore κ) m

nonrec def ImportFlowT.run {κ} [BEq κ] [Hashable κ] {γ}
    {m : Type → Type} [Monad m]
    {α} (x : ImportFlowT κ γ m α) (s : ImportFlowState κ γ := {}) (keys : KeyStore κ := {}) :=
  x.run s |>.run keys

-- nonrec def ImportFlowT.run' {κ} [BEq κ] [Hashable κ] {γ}
--     (m : Type → Type) [Monad m]
--     {α} (x : ImportFlowT κ γ m α) (s : ImportFlowState κ γ) (keys : KeyStore κ := {}) :=
--   x.run' s |>.run' keys

structure Preceding where
  prev : Bitset := {}
  depth : Nat := 0
  participating := false
deriving Inhabited, BEq, Repr

-- just `let { prev, depth } := iPreceding?.getD {}` + second branch?
def Preceding.add (i : ModuleIdx) (iPreceding? : Option Preceding) (p : Preceding) : Preceding :=
  match iPreceding? with
  | none => { p with
    prev := p.prev ∪ {i}
    depth := max p.depth 1 }
  | some { prev, depth .. } => { p with
    prev  := p.prev ∪ {i} ∪ prev
    depth := max p.depth (depth + 1) }

/-- If either of `p₁`, `p₂` are `none`, yields `p₁ <|> p₂`. Else, yields the union and max of the `Preceding` fields. -/
def Preceding.union (p₁ p₂ : Option Preceding) : Option Preceding :=
  match p₁, p₂  with
  | some p₁, some p₂ => some { p₂ with prev := p₁.prev ∪ p₂.prev, depth := max p₁.depth p₂.depth }
  | p₁, p₂ => (p₁ <|> p₂).map ({ · with participating := p₂.elim false participating })

structure ImportGraph.State (κ) (γ) [BEq κ] [Hashable κ] extends Lake.Shake.State, KeyStore κ where
  vals : Array (KeyedArray γ)

structure ModificationFlow (κ) where
  target : κ
  sources : Array (ModuleIdx × κ)

@[specialize add]
def ModificationFlow.ofAdd {κ m γ} (d : ModificationFlow κ)
    (init : γ) (add : ModuleIdx → Option γ → γ)
    [Monad m] [MonadImportFlow κ γ m] : m Unit := do
  let mut val := init
  for (idx, key) in d.sources do
    val := add idx (← MonadImportFlow.getPreviousVal? idx key)
  MonadImportFlow.setCurrentVal d.target val

-- TODO: we should get rid of these `*Raw` fields.
-- What we really want is something which does This, I think?
-- Or maybe we want to deal only with `Nat` indices, and feed those nat indices from the extra `KeyStore` we have in the downstream
@[specialize add]
def addForAllSourceKeysM {κ m γ} [BEq κ] [Hashable κ] (j : ModuleIdx)
    (add : κ → Option γ → Option γ → Option γ) -- source → tgt →
    [Monad m] [MonadStateOf (ImportFlowState κ γ) m] [MonadStateOf (KeyStore κ) m] : m Unit := do
  let vals ← getPreviousValsRaw? (γ := γ) κ j
  for keyIdx in 0...vals.size do
    let sourceVal ← getPreviousValRaw? κ j keyIdx
    -- Could probably be more efficient than doing it one by one, since we know exactly when we need to switch to `push`.
    let some key ← KeyStore.ofIdx? keyIdx | continue -- unreachable
    modifyCurrentValRaw κ keyIdx (add key sourceVal)

@[specialize add]
def addForAllKeysOfImports
    [MonadStateOf (ImportFlowState κ γ) m] [MonadStateOf (KeyStore κ) m]
    (env : Environment)
    (imps : Array Import)
    -- [source import] → [target key] → [source val] → [target val] → [new target val]
    (add : ModuleIdx → Import → κ → Option γ → Option γ → Option γ) : m Unit := do
  for imp in imps do
    let j := env.getModuleIdx! imp.module
    addForAllSourceKeysM j (add j imp)

@[inline] def addValOfParticipating (j : ModuleIdx)
    (jVal? tgtVal? : Option Preceding) : Option Preceding :=
  -- If the key is `.anonymous` or the root of `j`, then include `j`.
  -- Else, copy over `j`'s priors.
  if jVal?.elim false (·.participating) then
    Preceding.add j jVal? (tgtVal?.getD {})
  else
    Preceding.union jVal? tgtVal?
-- There's a sense in which we need to compare the key being copied to the root of the module and if so, copy it.
-- def addProjectRootValsOfImports
--     [MonadStateOf (ImportFlowState Name Preceding) m] [MonadStateOf (KeyStore Name) m]
--     (env : Environment)
--     (imps : Array Import)
--     (mod : Name)
--     : m Unit := do
--   MonadImportFlow.setCurrentVal mod.getRoot { : Preceding }
--   MonadImportFlow.setCurrentVal Name.anonymous { : Preceding }
--   addForAllKeysOfImports env imps fun j _ _ => addProjectRootValOfImport j


-- General case:
-- Function `Environment → ModuleIdx → Array ModificationFlow`
-- Get the imports and their indices manually inside that function.
-- "Local version": something that produces an array of keys given a single import and a key for the current target.

/-
Concretely:

We want prevs by root. So for each module, we have its root, and for each import, we...look at all prevs? Okay, that's interesting. So this whole structure is wrong. We actually want to copy over all keys from all imports. We need "get all key values"...or something. Some way to do full key operations. Or iterate through all keys? Easy to do on the index level, but.
-/

-- def mkPrecedingRootModificationFlow (targetKeys : Array κ) (imps : Array Import)
--     (env : Environment)
--     -- targetKey? → [import] → [keys for import]
--     (mkKey? : κ → ModuleIdx → Import → Option κ) :
--     Array (ModificationFlow κ) := Id.run do
--   let mut flows := #[]
--   for targetKey in targetKeys do
--     let mut sources := #[]
--     for imp in imps do
--       let j := env.getModuleIdx! imp.module
--       let some key := κ → ModuleIdx → Import → Option κ

--         let keys := mkKeys targetKey j imp
--         unless keys.isEmpty do
--           flows := flows ++ keys.map ((j,·))
--   return flows

-- TODO(NOW): `filter` is not quite right.
-- TODO: collapse `leagues` and `allFilter` into ``leagues := fun _ imp => if (`Init).isPrefixOf imp.module then #[] else #[.anonymous, imp.module.getRoot]``? Requires people to reimplement filter...
@[specialize filter leagues]
protected def initStateWithPrecedingM (env : Environment)
    {m} [Monad m]
    [MonadStateOf (KeyStore Name) m] [MonadStateOf (ImportFlowState Name Preceding) m]
    (filter : ModuleIdx → EffectiveImport → Bool :=
      fun _ imp => !(`Init).isPrefixOf imp.module)
    (leagues : ModuleIdx → EffectiveImport → Array Name :=
      fun _ imp => #[imp.module.getRoot]) :
    m Lake.Shake.State := do
  let mut s : Lake.Shake.State := { env, transDeps := Array.mkEmpty env.header.moduleData.size }
  for i in 0...env.header.moduleData.size do
    let mod := env.header.moduleData[i]!
    let mut transImps := Needs.empty
    let modData := env.header.modules[i]!
    if filter i modData then
      MonadImportFlow.setCurrentVal Name.anonymous { participating := true : Preceding }
      for league in leagues i modData do
        MonadImportFlow.setCurrentVal league { participating := true : Preceding }
    for imp in mod.imports do
      let j := env.getModuleIdx! imp.module
      transImps := addTransitiveImps transImps imp j s.transDeps[j]!
      addForAllSourceKeysM j (fun _ : Name => addValOfParticipating j)
    s := { s with transDeps := s.transDeps.push transImps }
    ImportFlowState.next Name Preceding
  return s

def Shake.StateWithPreceding := ImportGraph.State Name Preceding

@[inline] protected def initStateWithPrecedingIO (env : Environment)
    (filter : ModuleIdx → EffectiveImport → Bool :=
      fun _ imp => !(`Init).isPrefixOf imp.module)
    (leagues : ModuleIdx → EffectiveImport → Array Name :=
      fun _ imp => #[imp.module.getRoot]) :
    BaseIO Shake.StateWithPreceding := do
  let ((s, flow), keys) ← ImportFlowRefT.run do initStateWithPrecedingM env filter leagues
  return { s with toKeyStore := keys, vals := flow.vals }

@[inline] protected def initStateWithPreceding (env : Environment)
    (filter : ModuleIdx → EffectiveImport → Bool :=
      fun _ imp => !(`Init).isPrefixOf imp.module)
    (leagues : ModuleIdx → EffectiveImport → Array Name :=
      fun _ imp => #[imp.module.getRoot]) :
    Shake.StateWithPreceding := Id.run do
  let ((s, flow), keys) ← ImportFlowT.run do initStateWithPrecedingM env filter leagues
  return { s with toKeyStore := keys, vals := flow.vals }





-- Instead of `KeyedArray`s inside, we could have a `HashMap` or `TreeMap` of `LateArray`s which start later. The ModificationKey thing is mostly the same, but now we don't need to have `Nat`s.
-- Alternatively: flat but effectively rectangular array where each block is of length `env.header.moduleData.size`. When we encounter a new key, we add another block.
-- Really depends on what sort of locality we want I guess.

-- what if we want different modification key layouts for different values?
-- Ideally this is a thing we can iterate on? Would be nice to do it all in a single loop...
-- But really, the structure is now importKey + TreeFlow, I think...
-- Can they be combined?

-- What if we allowed just an arbitrary function that had access to the module data and module index, but had a nice API for adding data to keys by working in a nice monad?
-- `∪ {j}` shows we need more freedom here.
