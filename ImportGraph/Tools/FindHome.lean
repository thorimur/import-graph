/-
Copyright (c) 2023 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison, Paul Lezeau
-/
module

public meta import Lean.Elab.Command
public meta import Lean.Widget.UserWidget
public meta import ImportGraph.Imports.RequiredModules
public meta import ImportGraph.Imports.ImportGraph
public meta import ImportGraph.Graph.TransitiveClosure
meta import all Lean.ExtraModUses
public meta import Lake.CLI.Shake
import all Lake.CLI.Shake
import all Lean.Elab.Command

open Lean Lake Shake

/-
# New design

We have some functionality we need.

- decl → visibility → needed import set
- union: import sets → union
- minimize: full import set → minimal direct imports
- import set → meet


thinking a bit: we could track not only which imports are needed, but why. Which declarations are needed from those modules? This is harder.

-/

meta section

/--
This declaration exists in `Batteries`, but we don't want to make `ImportGraph` depend on batteries. We therefore just bear the duplication cost and make this private (and primed, in case someone `imports all`).
-/
private protected def Lean.Position.getDeclsAfter' (env : Environment) (pos : Position)
    (asyncMode := EnvExtension.AsyncMode.local) : Array Name :=
  declRangeExt.getState env asyncMode |>.foldl (init := #[])
    fun acc name { selectionRange .. } =>
      if selectionRange.pos.lt pos then acc else acc.push name

/--
Likewise
-/
@[inline] private protected def _root_.String.Pos.Raw.getDeclsAfter' (env : Environment) (map : FileMap)
    (pos : String.Pos.Raw) (asyncMode := EnvExtension.AsyncMode.local) : Array Name :=
  map.toPosition pos |>.getDeclsAfter' env asyncMode


/-- Debugging: list every `(j, k)` entry in `needs` as a literal `Import`, with no deduplication
across kinds. `modNames` maps `ModuleIdx` to `Name` (e.g. `State.modNames`). -/
meta def Lake.Shake.Needs.toImports (env : Environment) (needs : Needs) : Array Import := Id.run do
  let mut out := #[]
  for k in NeedsKind.all do
    let s := needs.get k
    for j in 0...env.allImportedModuleNames.size do
      if s.has j then
        out := out.push
          { module := env.allImportedModuleNames[j]!, isExported := k.isExported, isMeta := k.isMeta, importAll := false }
  return out

meta instance : ToMessageData NeedsKind where
  toMessageData
    | .pub => "public"
    | .metaPub => "public meta"
    | .priv => "private"
    | .metaPriv => "private meta"


/-- Debugging: list every `(j, k)` entry in `needs` as a literal `Import`, with no deduplication
across kinds. `modNames` maps `ModuleIdx` to `Name` (e.g. `State.modNames`). -/
meta def Lake.Shake.Needs.toMessageData (env : Environment) (needs : Needs)
    (filter : Name → NeedsKind → Bool := fun _ _ => true) : MessageData := Id.run do
  let mut msg := m!""
  for k in NeedsKind.all do
    msg := msg ++ m!"{k}:\n"
    let s := needs.get k
    for j in 0...env.allImportedModuleNames.size do
      if s.has j && filter env.allImportedModuleNames[j]! k then
        msg := msg ++ m!"  {toString env.allImportedModuleNames[j]!}\n"
  return msg

meta def Lean.Environment.getModuleIdx! (env : Environment) (moduleName : Name) : ModuleIdx :=
  env.getModuleIdx? moduleName |>.get!

elab "#foo" : command => do
  let s := initStateFromEnv (← getEnv)
  logInfo m!"{s.transDeps[(← getEnv).getModuleIdx! `ImportGraph.Graph.TransitiveClosure]!
    |>.toMessageData (← getEnv) fun n _ => !(`Init).isPrefixOf n}"

#foo

/--
Given an `Expr` reference, returns the declaration name that should be considered the reference, if
any, but from the environment directly.
-/
def Lean.Environment.getDepConstName? (ref : Name) (env : Environment) : Option Name := do
  -- Ignore references to reserved names, they can be re-generated in-place
  guard <| !isReservedName env ref
  -- `_simp_...` constants are similar, use base decl instead
  return if ref.isStr && ref.getString!.startsWith "_simp_" then
    ref.getPrefix
  else
    ref

deriving instance Ord for NeedsKind
-- TODO: custom structure
/-- A set of `NeedsKind`s. -/
abbrev NeedsKindSet := Std.TreeSet NeedsKind

/-- Assigns `bar` to the (local) declarations `foo` that are needed at their assigned sets of `NeedsKind`s. For instance, if `foo` is used in an exporting position, such as a public def's type, it will acquire `foo ↦ {{ isExported := true, isMeta := false }}`. -/
-- We might be able to simplify this quite a bit.
abbrev DeclNeeds := NameMap (NameMap NeedsKindSet)

nonrec def DeclNeeds.insert (k : NeedsKind) (decl usedDecl : Name) (needs : DeclNeeds) :=
  needs.alter decl fun
    | none => some (.empty |>.insert usedDecl {k})
    | some usedDecls => some <| usedDecls.alter usedDecl fun
      | none => some {k}
      | some ks => ks.insert k

/--
Calculates the needs for a given module `mod` from constants and recorded extra uses. Note that this does not calculate transitive needs, and assumes we're running from within the same file as the declaration.

Does not account for `extraModUses`, since these are not decl-linked per se.

Collects needed declarations from the current module in `DeclNeeds`, together with the visibiility they're needed at. Includes the needs of those declarations (not accounting for elaborator needs in their respective commands).
-/
-- Largely copied from `calcNeeds`, but with some key differences.
partial def calcDeclNeeds (decl : Name) (env : Environment)
    (needs : Needs := .empty) (extraDecls : DeclNeeds := {}) : Needs × DeclNeeds :=
  Id.run do
  let mut needs := needs
  let mut extraDecls := extraDecls
  let indirectModUses := indirectModUseExt.getState env
  let some ci := env.find? decl | return default
  -- Added guard for cases like `structure` that are still exported even if private
  let pubCI? := guard (!isPrivateName ci.name) *> (env.setExporting true).find? ci.name
  let k := { isExported := pubCI?.isSome, isMeta := isDeclMeta' env ci.name }
  (needs, extraDecls) := visitExpr indirectModUses k ci.type needs extraDecls
  if let some e := ci.value? (allowOpaque := true) then
    -- type and value has identical visibility under `meta`
    let k := if k.isMeta then k else
      if pubCI?.any (·.hasValue (allowOpaque := true)) then .pub else .priv
    (needs, extraDecls) := visitExpr indirectModUses k e needs extraDecls
  return (needs, extraDecls)
where
  /-- Accumulate the results from expression `e` into `deps`. -/
  visitExpr (indirectModUses : Std.HashMap Name (Array ModuleIdx)) (k : NeedsKind) (e : Expr)
      (deps : Needs) (extras : DeclNeeds) : Needs × DeclNeeds :=
    Lean.Expr.foldConsts e (deps, extras) fun c (deps, extras) => Id.run do
      let mut deps := deps
      let mut extras := extras
      if let some c := env.getDepConstName? c then
        if let some (j : Nat) := env.getModuleIdxFor? c then
          let k := { k with isMeta := k.isMeta && !isDeclMeta' env c }
          deps := deps.union k {j}
          for (indMod : Nat) in indirectModUses[c]?.getD #[] do
            /- The commented-out gate is only relevant if we're downstream of the imports we want to minimize, and may know about more indirectModUses than were known about now. -/
            -- if s.transDeps[i]!.has k indMod then
              deps := deps.union k {indMod}
        else
          -- `c` is from the same module--we need it at the given `k`
          unless extras.contains c || c == decl do -- just in case
            extras := extras.insert k decl c
            (deps, extras) := calcDeclNeeds c env deps extras
      return (deps, extras)

meta instance : ToMessageData ExtraModUse where
  toMessageData a := m!"⟦{if a.isExported then "public " else ""}{if a.isMeta then "meta " else ""}{a.module.toString}⟧"

meta instance : ToMessageData IndirectModUse where
  toMessageData a := m!"⟦{a.kind}{.ofConstName a.declName}⟧"

meta def Std.HashMap.subtractArray {α} {β} [BEq α] [BEq β] [Hashable α]
    (s₁ s₂ : Std.HashMap α (Array β)) (deleteEmpty := true) : Std.HashMap α (Array β) := Id.run do
  let mut s := s₁
  for (key, vals₂) in s₂ do
    s := s.alter key fun
      | none => none
      | some vals =>
        let vals := vals.filter (!vals₂.contains ·)
        if vals.isEmpty && deleteEmpty then none else vals
  return s

open Elab Command in
elab "#show_shake" ppLine cmd:command : command => do
  let env ← getEnv
  let initExtraModUses := PersistentEnvExtension.getState extraModUses env
  let initIndirectModUses := PersistentEnvExtension.getState indirectModUseExt env
  let initIsRev := !(isExtraRevModUseExt.getEntries env |>.isEmpty)
  elabCommandTopLevel cmd
  recordUsedSyntaxKinds cmd
  let env ← getEnv

  let extraModUses := PersistentEnvExtension.getState extraModUses env .sync
  let indirectModUses := PersistentEnvExtension.getState indirectModUseExt env
  let isRev := !(isExtraRevModUseExt.getEntries env |>.isEmpty)
  logInfo m!"extraModUses:\n  \
    {extraModUses.1.filter (!initExtraModUses.1.contains ·)}\n  \
    {extraModUses.2.toList.filter (!initExtraModUses.2.contains ·)}\n\
  indirectModUses:\n  \
    {indirectModUses.1.filter (!initIndirectModUses.1.contains ·)}\n  \
    {indirectModUses.2.subtractArray initIndirectModUses.2 |>.toList}\n\
  isNewRev: {isRev && !initIsRev}"

/-
Notes:

- Macros and tactic elaborators automatically record extraModUses.
- Term and command elaborators do not.
- `elabCommandTopLevel` runs the private def `recordUsedSyntaxKinds` which records an extra mod use for every syntax kind.
  - Usually, this suffices to cover the modules of term and command elaborators, which are usually defined in the same module as the syntax.
  - Ones that aren't should record the extra module use manually.


-/

-- set_option Elab.async false
#show_shake
def foo : MetaM Bool := do
  let stx ← `(term| NameMap.transitiveClosure)
  return test2%


#check indirectModUseExt
#show_shake
macro "aa" : command => `(command|#check true)

meta section

def Lean.SimplePersistentEnvExtension.modifyEntries (env : Environment)
    (ext : SimplePersistentEnvExtension α σ) (f : List α → List α)
    (asyncMode : EnvExtension.AsyncMode := ext.toEnvExtension.asyncMode)
    (asyncDecl : Name := Name.anonymous) : Environment :=
  PersistentEnvExtension.modifyState ext env (fun (entries, s) => (f entries, s))
    asyncMode asyncDecl

def Lean.SimplePersistentEnvExtension.setEntries (env : Environment)
    (ext : SimplePersistentEnvExtension α σ) (entries : List α)
    (asyncMode : EnvExtension.AsyncMode := ext.toEnvExtension.asyncMode)
    (asyncDecl : Name := Name.anonymous) : Environment :=
  PersistentEnvExtension.modifyState ext env (fun (_, s) => (entries, s))
    asyncMode asyncDecl


/-- Resets the state of the `indirectModUse` extension. Note that the state is never altered in the course of the file, as it only represents imported entries. Only the entries list is gotten/reset. -/
@[inline] def resetIndirectModUses (env : Environment)
    (asyncMode : EnvExtension.AsyncMode := indirectModUseExt.toEnvExtension.asyncMode)
    (asyncDecl : Name := Name.anonymous) :
    Environment :=
  indirectModUseExt.setEntries env [] asyncMode asyncDecl

@[inline] def getIndirectModUsesState (env : Environment)
    (asyncMode : EnvExtension.AsyncMode := indirectModUseExt.toEnvExtension.asyncMode) :
    List IndirectModUse :=
  indirectModUseExt.getEntries env asyncMode

@[inline] def setIndirectModUsesState (env : Environment) (entries : List IndirectModUse)
    (asyncMode : EnvExtension.AsyncMode := indirectModUseExt.toEnvExtension.asyncMode)
    (asyncDecl : Name := Name.anonymous) :
    Environment :=
  indirectModUseExt.setEntries env entries asyncMode asyncDecl

/-- Gets and resets the state of the `indirectModUse` extension. Note that the state is never altered in the course of the file, as it only represents imported entries. Only the entries list is gotten/reset. -/
def getResetIndirectModUses (env : Environment)
    (asyncMode : EnvExtension.AsyncMode := indirectModUseExt.toEnvExtension.asyncMode)
    (asyncDecl : Name := Name.anonymous) :
    List IndirectModUse × Environment :=
  letI indirect := indirectModUseExt.getEntries env asyncMode
  (indirect, resetIndirectModUses env asyncMode asyncDecl)

@[inline] def resetExtraModUses (env : Environment) :
    Environment :=
  PersistentEnvExtension.setState extraModUses env ([], {})

@[inline] def getExtraModUsesState (env : Environment)
    (asyncMode : EnvExtension.AsyncMode := extraModUses.toEnvExtension.asyncMode)
    (asyncDecl : Name := Name.anonymous) :
    List ExtraModUse × PHashSet ExtraModUse :=
  PersistentEnvExtension.getState extraModUses env asyncMode asyncDecl

@[inline] def setExtraModUsesState (env : Environment)
    (entries : List ExtraModUse)
    (state : PHashSet ExtraModUse) :
    Environment :=
  PersistentEnvExtension.setState extraModUses env (entries, state)


/-- Gets and resets the state of the `extraModUses` extension. Note that the state does not include imported entries. -/
def getResetExtraModUses (env : Environment)
    (asyncMode : EnvExtension.AsyncMode := extraModUses.toEnvExtension.asyncMode)
    (asyncDecl : Name := Name.anonymous) :
    (List ExtraModUse × PHashSet ExtraModUse) × Environment :=
  (getExtraModUsesState env asyncMode asyncDecl, resetExtraModUses env)


/-- Gets the state of the `extraModUses` extension. -/
@[inline] def getIsExtraRevModUse (env : Environment) : Bool :=
  !(isExtraRevModUseExt.getEntries env |>.isEmpty)

/-- Resets the state of the `extraModUses` extension. -/
@[inline] def resetIsExtraRevModUse (env : Environment)
    (asyncMode : EnvExtension.AsyncMode := isExtraRevModUseExt.toEnvExtension.asyncMode)
    (asyncDecl : Name := Name.anonymous) :
    Environment :=
  if getIsExtraRevModUse env then
    isExtraRevModUseExt.setEntries env [] asyncMode asyncDecl else env

/-- Resets the state of the `extraModUses` extension. -/
@[inline] def setIsExtraRevModUse (env : Environment) (isRev : Bool)
    (asyncMode : EnvExtension.AsyncMode := isExtraRevModUseExt.toEnvExtension.asyncMode)
    (asyncDecl : Name := Name.anonymous) :
    Environment :=
  if getIsExtraRevModUse env == isRev then env else
    isExtraRevModUseExt.setEntries env (if isRev then [()] else []) asyncMode asyncDecl

/-- Merges the state of the `extraModUses` extension (using "or" semantics). -/
@[inline] def mergeIsExtraRevModUse (env : Environment) (old : Bool)
    (asyncMode : EnvExtension.AsyncMode := isExtraRevModUseExt.toEnvExtension.asyncMode)
    (asyncDecl : Name := Name.anonymous) :
    Environment :=
  if old then setIsExtraRevModUse env old asyncMode asyncDecl else env

/-- Gets and resets the state of the `extraModUses` extension. -/
def getResetIsExtraRevModUse (env : Environment)
    (asyncMode : EnvExtension.AsyncMode := isExtraRevModUseExt.toEnvExtension.asyncMode)
    (asyncDecl : Name := Name.anonymous) :
    Bool × Environment :=
  if isExtraRevModUseExt.getEntries env |>.isEmpty then
    (false, env)
  else
    (true, isExtraRevModUseExt.setEntries env [] asyncMode asyncDecl)

def resetShakeExts (env : Environment) (asyncMode : EnvExtension.AsyncMode := .sync)
    (asyncDecl : Name := Name.anonymous) : Environment :=
  letI env := resetIndirectModUses env asyncMode asyncDecl
  letI env := resetExtraModUses env
  resetIsExtraRevModUse env asyncMode asyncDecl

def List.prependWithoutDuplicating [BEq α] (as bs : List α) : List α :=
  match as with
  | [] => bs
  | a :: as => let new := as.prependWithoutDuplicating bs; if new.contains a then new else a :: new

def Lean.PHashSet.union {α} [BEq α] [Hashable α] (as bs : PHashSet α) : PHashSet α := Id.run do
  let mut bs := bs
  for a in as do
    unless bs.contains a do
      bs := bs.insert a
  return bs

-- TODO: could take an approach more like `copyExtraModUses`, possibly even use it. But we don't need to retain the whole environment...
/-- Resets the shake extensions that record modules, then restores them after running the given action, merging any new records into the new ones. -/
def withFreshModRecords [Monad m] [MonadEnv m] [MonadFinally m] {α} (x : m α)
    (asyncMode : EnvExtension.AsyncMode := .sync)
    (asyncDecl : Name := Name.anonymous) : m α := do
  let indirect := getIndirectModUsesState (← getEnv) asyncMode
  let (extraEntries, extraState) := getExtraModUsesState (← getEnv) asyncMode asyncDecl
  let isRev := getIsExtraRevModUse (← getEnv)
  modifyEnv (resetShakeExts · asyncMode asyncDecl)
  try
    x
  finally
    modifyEnv fun env =>
      letI newIndirect := getIndirectModUsesState env asyncMode
      letI env := setIndirectModUsesState env (newIndirect.prependWithoutDuplicating indirect) asyncMode asyncDecl
      let (newExtraEntries, newExtraState) := getExtraModUsesState env asyncMode asyncDecl
      letI env := setExtraModUsesState env
        (newExtraEntries.prependWithoutDuplicating extraEntries)
        (newExtraState.union extraState)
      mergeIsExtraRevModUse env isRev asyncMode asyncDecl

open Elab Command in
elab "#show_imports" ppLine cmd:command : command => do
  let needs ← withFreshModRecords do
    elabCommand cmd
    recordUsedSyntaxKinds cmd
    let indirect := getIndirectModUsesState (← getEnv)
    let (extras, _) := getExtraModUsesState (← getEnv)
    let decls := cmd.raw.getPos?.get!.getDeclsAfter' (← getEnv) (← getFileMap)
    let mut needs := .empty
    let mut declNeeds := {}
    for decl in decls do
      (needs, declNeeds) := calcDeclNeeds decl (← getEnv) needs declNeeds
    pure (needs, declNeeds, indirect, extras)
  logInfo m!"{needs.1.toMessageData (← getEnv)}{needs.2.2}"

/-
#min_imports as widget that waits for everything by adding a linter that holds a handle to a promise, which is resolved in the infoview? Is that possible?

Also something that just minimizes your existing imports into something canonical.

Should respect shake directives.
-/

/-- Written mostly by claude. -/
@[specialize f]
def Lake.Shake.Bitset.foldOneIdxs (s : Bitset) (init : α) (f : α → Nat → α) : α := Id.run do
  let mut n := s.toNat
  let mut acc := init
  while n != 0 do
    let i := n.log2  -- highest bit, O(1) on GMP
    acc := f acc i   -- (visits high→low; flip if you need low→high)
    n := n ^^^ (1 <<< i)
  return acc

/-- High to low. -/
def Lake.Shake.Bitset.toIdxs (s : Bitset) : Array Nat := s.foldOneIdxs #[] (·.push ·)

instance {m} [Monad m] : ForIn m Bitset Nat where
  forIn s init f := do
    let mut n := s.toNat
    let mut acc := init
    while n != 0 do
      let i := n.log2
      match ← f i acc with
      | .done b => return b
      | .yield b => acc := b
      n := n ^^^ (1 <<< i)
    return acc

instance {m} [Monad m] : ForIn m Needs (NeedsKind × Nat) where
  forIn s init f := do
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

namespace Lake.Shake
/-
`#find_home` now just needs
- turn `Needs` into surface imports (easy)
- meet operation on `Needs`. Might need transitive deps after all.
-/

/-- Reflexively transitively closes a `Needs`. -/
def Needs.transitiveClosure (directNeeds : Needs) (transDeps : Array Needs) : Needs := Id.run do
  let mut needs := directNeeds
  for (k, i) in directNeeds do
    needs := addTransitiveImps needs { k with module := .anonymous } i transDeps[i]!
  return needs
  -- or:
  -- let mut needs := directNeeds
  -- for h : i in 0...transDeps.size do
  --   for k in NeedsKind.all do
  --     if directNeeds.has k i then
  --       needs := addTransitiveImps needs { k with module := .anonymous } i transDeps[i]
  -- return needs

@[inline] def Bitset.le (a b : Bitset) : Bool := a.toNat &&& b.toNat == a.toNat
@[inline] def Bitset.intersect (a b : Bitset) : Bitset where
  toNat := a.toNat &&& b.toNat

/-- Assumes the second argument is already transitively closed (not necessarily the first), and also has b.pub ≤ b.priv. Does not transitively close the `Needs`. `false` includes incomparable. -/
@[inline] def Needs.le (a b : Needs) : Bool :=
  -- NeedsKind.all.all fun k => a.get k |>.le b.get k
  a.pub.le b.pub
    && a.priv.le b.priv
    && a.metaPub.le b.metaPub
    && a.metaPriv.le b.metaPriv

theorem le_eq_all_get_le_get (a b : Needs) :
    a.le b = NeedsKind.all.all fun k => a.get k |>.le <| b.get k := by
  simp [NeedsKind.all, Needs.get, Needs.le, Bool.and_assoc]

def Needs.fillPriv (a : Needs) : Needs :=
  { a with priv := a.priv ∪ a.pub, metaPriv := a.metaPriv ∪ a.metaPub }

/-- Assumes the second argument is already transitively closed (not necessarily the first). Does not transitively close the `Needs`. `false` includes incomparable. -/
def Needs.le' (a b : Needs) : Bool :=
  a.pub.le b.pub
    && a.metaPub.le b.metaPub
    && a.priv.le (b.priv ∪ b.pub)
    && a.metaPriv.le (b.metaPriv ∪ b.metaPub)

@[inline] def Needs.reflexify (i : Nat) (a : Needs) : Needs where
  pub := a.pub ∪ {i}
  priv := a.priv ∪ {i}
  metaPub := a.metaPub ∪ {i}
  metaPriv := a.metaPriv ∪ {i}

def Needs.fillTransDeps (transDeps : Array Needs) : Array Needs :=
  transDeps.mapIdx fun i n => n.fillPriv.reflexify i

@[inline] def _root_.Array.filter' (a : Array α) (f : α → Bool) : Array α × Bool :=
  let s := a.size
  let a := a.filter f
  (a, a.size ≠ s)

@[inline] def _root_.Array.incorporateBelow (as : Array (Option α)) (a : α)
    (le : α → α → Bool) : Array (Option α) := Id.run do
  let mut as := as
  for i in 0...as.size do
    let some aᵢ := as[i]! | continue
    if le a aᵢ then
      as := as.set! i none
    else if le aᵢ a then
      return as
  return as.push a


/-- `needs` does not need to be transitively closed. -/
def Needs.coverings (filledRflTransDeps : Array Needs) (needs : Needs) : Array ModuleIdx := Id.run do
  let mut mods := #[]
  let mut b := false
  for h : i in 0...filledRflTransDeps.size do
    if needs.le filledRflTransDeps[i] then
      mods := mods.incorporateBelow i fun a b => filledRflTransDeps[a]!.le filledRflTransDeps[b]!
  return mods.reduceOption




#show_imports
/--
Find locations as high as possible in the import hierarchy
where the named declaration could live.
-/
def Lean.Name.findHome (n : Name) (env : Option Environment) : CoreM NameSet := do
  let current? := match env with | some env => env.header.mainModule | _ => default
  let required := (← n.requiredModules).toArray.erase current?
  let imports := (← getEnv).importGraph.transitiveClosure
  let mut candidates : NameSet := {}
  for (n, i) in imports do
    if required.all fun r => n == r || i.contains r then
      candidates := candidates.insert n
  for c in candidates do
    for i in candidates do
      if imports.find? i |>.getD {} |>.contains c then
        candidates := candidates.erase i
  return candidates

#check Environment.getModuleIdx?

def fooooo := Name.requiredModules

open Elab Command

meta def fooLinter : Linter where
  name := `foo
  run _ := do
    let env ← getEnv
    let ind := indirectModUseExt.getState (← getEnv) |>.toArray.map fun (a, b) => (a, b.map (env.header.moduleNames[·]!))
    let extra := extraModUses.getState (← getEnv) |>.toList
    -- logInfo m!"{ind}"
    logInfo m!"{repr extra}"
    -- let r := isExtraRevModUseExt.getState (← getEnv)

-- #check record

#check initStateFromEnv

run_cmd do
  lintersRef.modify fun ls => ls.filter (·.name != `foo)
  -- addLinter fooLinter

-- run_cmd do
--   let env ← getEnv
--   let ind := indirectModUseExt.getState (← getEnv) |>.toArray.map fun (a, b) => (a, b.map (env.header.moduleNames[·]!))
--   let extra := extraModUses.getState (← getEnv) |>.toList
--   -- logInfo m!"{ind}"
--   let r := isExtraRevModUseExt.getState (← getEnv)
--   logInfo m!"{repr extra}"


open Server in
/-- Tries to resolve the module `modName` to a source file URI.
This has to be done in the Lean server
since the `Environment` does not keep track of source URIs. -/
@[server_rpc_method]
def getModuleUri (modName : Name) : RequestM (RequestTask Lsp.DocumentUri) :=
  RequestM.asTask do
    let some uri ← documentUriFromModule? modName
      | throw $ RequestError.invalidParams s!"couldn't find URI for module '{modName}'"
    return uri

structure GoToModuleLinkProps where
  modName : Name
  deriving Server.RpcEncodable

/-- When clicked, this widget component jumps to the source of the module `modName`,
assuming a source URI can be found for the module. -/
@[widget_module]
def GoToModuleLink : Widget.Module where
  javascript := "
    import * as React from 'react'
    import { EditorContext, useRpcSession } from '@leanprover/infoview'

    export default function(props) {
      const ec = React.useContext(EditorContext)
      const rs = useRpcSession()
      return React.createElement('a',
        {
          className: 'link pointer dim',
          onClick: async () => {
            try {
              const uri = await rs.call('getModuleUri', props.modName)
              ec.revealPosition({ uri, line: 0, character: 0 })
            } catch {}
          }
        },
        props.modName)
    }
  "

open Elab Command in
/--
Find locations as high as possible in the import hierarchy
where the named declaration could live.
Using `#find_home!` will forcefully remove the current file.
Note that this works best if used in a file with `import Mathlib`.

The current file could still be the only suggestion, even using `#find_home! lemma`.
The reason is that `#find_home!` scans the import graph below the current file,
selects all the files containing declarations appearing in `lemma`, excluding
the current file itself and looks for all least upper bounds of such files.

For a simple example, if `lemma` is in a file importing only `A.lean` and `B.lean` and
uses one lemma from each, then `#find_home! lemma` returns the current file.
-/
elab "#find_home" bang:"!"? n:ident : command => do
  let stx ← getRef
  let mut homes : Array MessageData := #[]
  let n ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo n
  let env? ← bang.mapM fun _ => getEnv
  for modName in (← Elab.Command.liftCoreM do n.findHome env?) do
    let p : GoToModuleLinkProps := { modName }
    homes := homes.push $ .ofWidget
      (← liftCoreM $ Widget.WidgetInstance.ofHash
        GoToModuleLink.javascriptHash $
        Server.RpcEncodable.rpcEncode p)
      (toString modName)
  logInfoAt stx[0] m!"{homes}"
