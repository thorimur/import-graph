module

import all Lake.CLI.Shake
import ImportGraph.Lean.Environment
public import ImportGraph.Shake.Basic

open Lean Lake Shake

/--
Given an `Expr` reference, returns the declaration name that should be considered the reference, if
any, but from the environment directly.
-/
-- TODO: just give in and use `State`?
def Lean.Environment.getDepConstName? (ref : Name) (env : Environment) : Option Name := do
  -- Ignore references to reserved names, they can be re-generated in-place
  guard <| !isReservedName env ref
  -- `_simp_...` constants are similar, use base decl instead
  return if ref.isStr && ref.getString!.startsWith "_simp_" then
    ref.getPrefix
  else ref

-- TODO: to handle recursive declarations, we need separate `Needs` for each declaration. And we need to hold off on unioning the needs of subdeclarations with the overall needs, since the place the subdeclaration might end up .

-- This decl needs these declarations at these availabilities from these modules, implying an overall `Needs` by incorporating each module. However, we don't know yet what modules some of the declarations are going to come from.
-- Indirect module uses—maybe we should record these separately?
deriving instance Ord for NeedsKind

abbrev NeedsKindSet := Std.TreeSet NeedsKind

/-- The `Needs` of a given declaration. -/
structure DeclNeed where
  needs : Needs := .empty
  freeDecls : NameMap NeedsKindSet := {}
  -- TODO: collect the reasons instead of a `Bool` for `isIndirect`.
  -- TODO: more efficient data structure?
  fixedDecls : Std.TreeMap ModuleIdx (NameMap (NeedsKindSet × Bool)) := {}
deriving Inhabited

/-- Records that the ambient declaration needs the declaration `decl` at availability `k`, where the module of `decl` is left free. -/
def DeclNeed.insertFreeDecl (k : NeedsKind) (decl : Name) (declNeed : DeclNeed) : DeclNeed :=
  { declNeed with freeDecls := declNeed.freeDecls.alter decl fun
    | set? => set?.elim (some {k}) (·.insert k) }

/-- Records that the ambient declaration needs the imported declaration `decl` from module `i` at availability `k`, where `decl` is expected to stay in `i`. -/
def DeclNeed.insertFixedDecl (k : NeedsKind) (i : ModuleIdx) (decl : Name)
    (declNeed : DeclNeed) (isIndirect : Bool := false) : DeclNeed :=
  { declNeed with
    needs := declNeed.needs.union k {i}
    fixedDecls := declNeed.fixedDecls.alter i fun
      | none => some (.empty |>.insert decl ({k}, isIndirect))
      | some map => some <| map.alter decl fun
        | set? => set?.elim (some ({k}, isIndirect)) fun (ks, reasons) =>
          (ks.insert k, reasons || isIndirect) } -- Note: generally, we should never have "both".

/-- A collection of needs per declaration. -/
abbrev DeclNeeds := NameMap DeclNeed

-- TODO: better `none` behavior?

@[inline] def DeclNeeds.insertFreeDeclFor (currentDecl : Name) (k : NeedsKind) (usedDecl : Name)
    (declNeeds : DeclNeeds) : DeclNeeds := declNeeds.alter currentDecl fun
      | need? => need?.getD {} |>.insertFreeDecl k usedDecl

@[inline] def DeclNeeds.insertFixedDeclFor (currentDecl : Name) (k : NeedsKind) (i : ModuleIdx)
    (usedDecl : Name) (declNeeds : DeclNeeds) (isIndirect : Bool := false) : DeclNeeds :=
  declNeeds.alter currentDecl fun
    | need? => need?.getD {} |>.insertFixedDecl k i usedDecl isIndirect

@[inline] def DeclNeeds.fullNeeds (declNeeds : DeclNeeds) : Needs :=
  declNeeds.foldl (init := .empty) fun acc _ { needs .. } => acc ∪ needs

/--
Calculates the needs for a given module `mod` from constants and recorded extra uses. Note that this does not calculate transitive needs, and assumes we're running from within the same file as the declaration.

Does not account for `extraModUses`, since these are not decl-linked per se.

Collects needed declarations from the current module in `DeclNeeds`, together with the availability they're needed at. Recursively includes the needs of those declarations (not accounting for elaborator needs in their respective commands) in the result.
-/
-- Largely copied from `calcNeeds`, but with some key differences.
partial def calcDeclNeeds (decl : Name) (env : Environment)
    (currentDecls : DeclNeeds := {}) :
    DeclNeeds := Id.run do
  if env.isImportedConst decl || currentDecls.contains decl then return currentDecls
  let mut declNeeds : DeclNeeds := currentDecls.insert decl {}
  -- TODO: should we be getting the reason, and do our own custom import? Maybe.
  -- We could also look up the reason later.
  let indirectModUses := indirectModUseExt.getState env
  let some ci := env.find? decl | return declNeeds
  -- Added guard for cases like `structure` that are still exported even if private
  let pubCI? := guard (!isPrivateName ci.name) *> (env.setExporting true).find? ci.name
  let k := { isExported := pubCI?.isSome, isMeta := isDeclMeta' env ci.name }
  declNeeds := visitExpr indirectModUses k ci.type declNeeds
  if let some e := ci.value? (allowOpaque := true) then
    -- type and value has identical visibility under `meta`
    let k := if k.isMeta then k else
      if pubCI?.any (·.hasValue (allowOpaque := true)) then .pub else .priv
    declNeeds := visitExpr indirectModUses k e declNeeds
  return declNeeds
where
  /-- Accumulate the results from expression `e` into `deps`. -/
  visitExpr (indirectModUses : Std.HashMap Name (Array ModuleIdx)) (k : NeedsKind) (e : Expr)
      (declNeeds : DeclNeeds) : DeclNeeds :=
    Lean.Expr.foldConsts e declNeeds fun c declNeeds => Id.run do
      let mut declNeeds := declNeeds
      if let some c := env.getDepConstName? c then
        if let some (j : ModuleIdx) := env.getModuleIdxFor? c then
          let k := { k with isMeta := k.isMeta && !isDeclMeta' env c }
          declNeeds := declNeeds.insertFixedDeclFor decl k j c
          -- extras := extras.push { needer := decl, needed := c, kind := k, neededModuleIdx? := j }
          for (indMod : ModuleIdx) in indirectModUses[c]?.getD #[] do
            /- The commented-out gate is only relevant if we're downstream of the imports we want
            to minimize, and may know about more indirectModUses than were known about in `i`.

            Supporting downstream runs would mean supplying the `originalMod?` of the top-level
            `decl` to `visitExpr`, and providing `transDeps`. -/
            -- if s.transDeps[i]!.has k indMod then
              declNeeds := declNeeds.insertFixedDeclFor decl k indMod c (isIndirect := true)
        else
          -- TODO: should we do the same `isDeclMeta'` dance as in the other branch to construct `k`?
          -- `c` is from the same module--we need it at the given `k`, but also need whatever it needs.
          unless c == decl do -- just in case
            declNeeds := calcDeclNeeds c env <| declNeeds.insertFreeDeclFor decl k c
      return declNeeds
