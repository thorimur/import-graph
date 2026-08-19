module

meta import ImportGraph.Lean.Environment
public import ImportGraph.Shake.Basic
meta import Lean.Environment
import Lean
import Lean.ResolveName

open Lean ImportGraph Shake

namespace ImportGraph.Shake

section fromShake

/-! This section is inlined from shake. -/

-- SQ: what's the TODO mean?
def isDeclMeta' (env : Environment) (declName : Name) : Bool :=
  -- Matchers are not compiled by themselves but inlined by the compiler, so there is no IR decl
  -- to be tagged as `meta`.
  -- TODO: It would be better to base the entire `meta` inference on the IR only and consider module
  -- references from any other context as compatible with both phases.
  let inferFor :=
    if declName.isStr && (declName.getString!.startsWith "match_" || declName.getString! == "_unsafe_rec") then declName.getPrefix else declName
  -- `isMarkedMeta` knows about non-defs such as `meta structure`, isDeclMeta knows about decls
  -- implicitly marked meta
  isMarkedMeta env inferFor || isDeclMeta env inferFor

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
  else ref

end fromShake

/-- A way in which a declaration might demand an imported module. Note that there may be multiple demands on the same module from the same declaration, which thus may require multiple of these. -/
structure DeclImportNeedsKind extends NeedsKind where
  /-- A flag for the case where the ambient declaration needs a meta declaration from the needed
  module. In that case, the import is allowed to be meta, but does not have to be. Note that
  ordinary expression uses also `allowMeta`; it is only usage in the computational content (LCNF)
  that will *disallow* meta and set this to false.

  However, to allow `NeedsKinds` constructors to not conflict with `.allowMetaPub`, we set this to
  `isMeta` by default. -/
  allowMeta : Bool := isMeta
  /-- Needing a meta import implies `allowMeta = true`. -/
  allowMeta_if_isMeta : !isMeta || allowMeta := by grind

namespace DeclImportNeedsKind


-- We give these distinct names to avoid ambiguity.
@[match_pattern] def pubNoMeta : DeclImportNeedsKind :=
  { NeedsKind.pub with allowMeta := false }
@[match_pattern] def privNoMeta : DeclImportNeedsKind :=
  { NeedsKind.priv with allowMeta := false }
@[match_pattern] def privOfPrivNoMeta : DeclImportNeedsKind :=
  { NeedsKind.privOfPriv with allowMeta := false }
@[match_pattern] def metaPub : DeclImportNeedsKind :=
  { NeedsKind.metaPub with }
@[match_pattern] def metaPriv : DeclImportNeedsKind :=
  { NeedsKind.metaPriv with }
@[match_pattern] def metaPrivOfPriv : DeclImportNeedsKind :=
  { NeedsKind.metaPrivOfPriv with }
@[match_pattern] def pubAllowMeta : DeclImportNeedsKind :=
  { NeedsKind.pub with allowMeta := true }
@[match_pattern] def privAllowMeta : DeclImportNeedsKind :=
  { NeedsKind.priv with allowMeta := true }
@[match_pattern] def privOfPrivAllowMeta : DeclImportNeedsKind :=
  { NeedsKind.privOfPriv with allowMeta := true }

def providedBy (p : ProvisionKind) (k : DeclImportNeedsKind) : Bool :=
  if k.isMeta then
    if k.isExported then p.metaPub else
      if k.isAll then p.metaPrivOfPriv else
        p.metaPriv
  else
    if k.isExported then p.pub || k.allowMeta && p.metaPub else
      if k.isAll then p.privOfPriv || k.allowMeta && p.metaPrivOfPriv else
        p.priv || k.allowMeta && p.metaPriv

/-- Like `Needs`, but preserves `allowMeta`. We interpret `pub`/`priv`/`privOfPriv` from
`NeedsKind` as having `allowMeta := false`, i.e. as specifically *disallowing* a meta import.  -/
structure DeclImportNeeds extends Needs where
  /-- The modules which may be imported as meta or non-meta which are needed in the public scope. -/
  allowMetaPub : Bitset
  /--
  The modules which may be imported as meta or non-meta whose public scopes must be available in the current private scope.
  -/
  allowMetaPriv : Bitset
  /--
  The modules which may be imported as meta or non-meta whose private scopes must be available in the current private scope.
  -/
  allowMetaPrivOfPriv : Bitset

/-- Assumes that `Provides` is properly constructed, i.e. is linearized and transitively closed. -/
def isProvidedBy (n : DeclImportNeeds) (p : Provides) :=
  n.metaPub ⊆ p.metaPub
    && n.metaPriv ⊆ p.metaPriv
    && n.metaPrivOfPriv ⊆ p.metaPrivOfPriv
    && n.pub ⊆ p.pub && n.allowMetaPub ⊆ p.pub ∪ p.metaPub
    && n.priv ⊆ p.priv && n.allowMetaPriv ⊆ p.priv ∪ p.metaPriv
    && n.privOfPriv ⊆ p.privOfPriv && n.allowMetaPrivOfPriv ⊆ p.privOfPriv ∪ p.metaPrivOfPriv

def NeedsKind.toDeclImportNeedsKind (k : NeedsKind) (allowMeta : Bool) :
    DeclImportNeedsKind :=
  { k with allowMeta := k.isMeta || allowMeta }

-- TODO: might not need this.
-- /-- A position at which a declaration `tgt` might need another declaration `src`. In general, the
-- same `src` and `tgt` may be related by multiple `DeclDeclNeedsPos`s. -/
-- inductive DeclDeclNeedsPos where
-- | /-- `tgt` uses `src` in its type. -/  type
-- | /-- `tgt` uses `src` in its value. -/ value
-- | /-- `tgt` uses `src` in its LCNF. -/  lcnf

local instance : Ord Name := ⟨Name.quickCmp⟩

/-- A way in which a declaration `tgt` might need another declaration `src`. In general, the same `src` and `tgt` may be related by multiple `DeclDeclNeedsKind`s. -/
inductive DeclDeclNeedsKind where
| expr (isExported : Bool)
| /--
  This expresses a meta LCNF reference need. (We do not consider non-meta LCNF needs, at least for now.) I.e., `tgt` references `src` in its LCNF.

  Note a quirk about handling `.metaLCNF (isExported := true)`: a `public meta` definition `tgt` is allowed to have this need of a `private meta` declaration `src` as long as `src` is *from the same module* (since this induces the private meta decl's LCNF to be exported). This is not allowed across a module boundary.

  Further, `tgt` then needs `src`'s dependencies at `.metaLCNF (isExported := true)` (i.e. that they are `public meta import`ed), even though `src` per se doesn't. This only needs to be addressed by `tgt` itself if `src` is private and `tgt` is public, and they are in the same module.

  We record this separately to handle inlining of constants into LCNF, which affects the necessary dependencies. Suppose `public def inlinableFoo` is imported from `A`. Then
  ```
  module
  meta import A

  meta def a := f inlinableFoo

  public meta def b := g a
  ```
  is accepted, since `inlinableFoo` is inlined into the exported LCNF of `a` and thus does not need to be re-meta-exported to downstream consumers by the import of `A`. In this case, we have:
  - `a`'s need of `inlinableFoo`:
    `.expr (isExported := false) (isMeta := true)`
  - `a`'s need of `inlinableFoo`'s dependencies (since they've been inlined in `a`'s LCNF):
    `.metaLCNF (isExported := false)`
  - `b`'s needs of `a`:
    `.expr (isExported := false) (isMeta := true)`
    `.metaLCNF (isExported := true)`
  - `b`'s need of `inlinableFoo`:
    (no dependencies)
  - `b`'s need of `inlinableFoo`'s inlined dependencies in `a`:
    ``.metaLCNF (isExported := true) (through := [`a])``

  If `inlinableFoo` were just `foo` and *not* inlinable, `b` would need `foo` at
  ``.metaLCNF (isExported := true) (through := [`a])`` (and not need its dependencies).

  We might get rid of `through` if it is not helpful.
  -/
  lcnf (isExported isMeta : Bool) (through : List Name := [])
| /--
  A compile-time dependency of `tgt` (e.g. a parser used for notation in the command for  `tgt`).

  If this arises due to an indirect mod use, we record the declaration that demanded it (if we
  can). Note that shake extensions do not expose this; this is known during the expression
  traversal. So some indirect mod uses will end up in `extraModUses` without any indication as to
  the declaration that drew them (at least, not in a way that's accessible to us, though this
  information is traced by shake).
  -/
  comptime (indirectlyFrom : Option Name := none)
deriving Inhabited, BEq, Repr, Hashable, Ord

/-- The intrinsic visibility and phase of some data (not necessarily a declaration per se; possibly LCNF, a declaration's body, etc.). -/
structure VisibilityPhase where
  isExported : Bool
  isMeta : Bool

namespace DeclDeclNeedsKind

@[inline] protected def isExported : DeclDeclNeedsKind → Bool
  | .expr isExported
  | .lcnf (isExported := isExported) .. => isExported
  | .comptime _ => false

/-- `some true` if this demands meta; `some false` if it demands *non*-meta. `none` if the need
itself is not sensitive to `meta`, as is the case for expressions per se. -/
@[inline] protected def isMeta? : DeclDeclNeedsKind → Option Bool
  | .expr _ => none
  | .lcnf (isMeta := isMeta) .. => isMeta
  -- we assume that code we're running at compile time was marked meta originally
  -- and so does not demand a meta import
  | .comptime _ => none

-- TODO: we could pass in a structure here that has `isExported, isMeta` (the original `NeedsKind`).

-- TODO: not clear we need this...

-- TODO: we might not need this section at all, yet.
-- After all, if we can go directly from the intrinsic data about the declarations involved to
-- import needs, we can just act on the hierarchy.
-- This may be necessary if we start mutating declaration's visibilities.
section provisioned

structure LCNFVisibilityPhase extends VisibilityPhase where
  /-- Local declarations are handled differently by compilation, so we record this here. -/
  isLocal : Bool

/-- How a declaration has been provisioned to us. This therefore already takes into account the way
it has been imported and/or whether it's from the same file. A `private meta def` from the same
file has `lcnf? := some { isExported := false, isMeta := true, isLocal := true }`, and thus we can satisfy a need of `.lcnf (isExported := true) (isMeta := true) _`. -/
structure DeclProvisionedKind where
  expr : Environment.Visibility
  lcnf? : Option LCNFVisibilityPhase
  irPhases : IRPhases

-- Hang on. Each of these handles a different part of `DeclProvisionedKind`. We can probably do better.
/-- Whether `src` being provisioned according to `DeclProvisionedKind` satsifies the `DeclDeclNeedsKind`. -/
def satisfies (src : DeclProvisionedKind) : DeclDeclNeedsKind → Bool
  | .expr isExported => !isExported || src.expr.isExported
  | .lcnf isExported isMeta _ => src.lcnf?.any fun lcnf =>
    (!isExported || lcnf.isExported || lcnf.isLocal) && (isMeta == lcnf.isMeta)
  | .comptime _ => src.irPhases != .runtime

-- TODO
-- def toDeclProvisionedKind (src : VisibilityPhase) (via : NeedsKind) : DeclProvisionedKind

end provisioned


end DeclDeclNeedsKind

-- TODO: to handle recursive declarations, we need separate `Needs` for each declaration. And we need to hold off on unioning the needs of subdeclarations with the overall needs, since the place the subdeclaration might end up .

-- -- This decl needs these declarations at these availabilities from these modules, implying an overall `Needs` by incorporating each module. However, we don't know yet what modules some of the declarations are going to come from.
-- -- Indirect module uses—maybe we should record these separately?
-- deriving instance Ord for NeedsKind

-- TODO

/-- A set of declaration needs.

TODO: make this more efficient, ideally a tiny `BitsetOf`, if such API were created. Also consider
just a small `List` or `Array` that avoids duplicate insertion at insertion time. -/
abbrev DeclDeclNeedsKindSet := Std.TreeSet DeclDeclNeedsKind

def DeclDeclNeedsKindSet.toDeclImportNeedsKindOfSatisfiable (s : DeclDeclNeedsKindSet) (src : VisibilityPhase)

/-- The `Needs` of a given declaration. -/
structure DeclNeed where
  /-- Declarations that are not fixed to a given import. -/
  freeDecls : NameMap DeclDeclNeedsKindSet := {}
  -- TODO: collect the reasons instead of a `Bool` for `isIndirect`.
  -- TODO: more efficient data structure?
  /-- A map `[module name] ↦ [decls needed from that module]`. -/
  fixedDecls : Std.TreeMap Name (NameMap DeclDeclNeedsKindSet) := {}
  /-- Extra module uses recorded in shake extensions during the command. Note that if several declarations were created during the command, we distribute these to all of them. -/
  extraModUses : NameSet := {}
deriving Inhabited

/-- Records that the ambient declaration needs the declaration `decl` at availability `k`, where the module of `decl` is left free. -/
@[inline] def DeclNeed.insertFreeDecl (k : DeclDeclNeedsKind) (decl : Name) (declNeed : DeclNeed) :
    DeclNeed :=
  { declNeed with freeDecls := declNeed.freeDecls.alter decl fun
    set? => set?.getD {} |>.insert k }

/-- Records that the ambient declaration needs the imported declaration `decl` from module `i` at availability `k`, where `decl` is expected to stay in `i`. -/
def DeclNeed.insertFixedDecl (k : DeclDeclNeedsKind) (mod : Name) (decl : Name)
    (declNeed : DeclNeed) : DeclNeed :=
  { declNeed with
    fixedDecls := declNeed.fixedDecls.alter mod fun map? =>
      some <| map?.getD {} |>.alter decl fun set? =>
        set?.getD {} |>.insert k }

/-- A collection of needs per declaration. -/
-- TODO: make this more efficient.
abbrev DeclNeeds := NameMap DeclNeed

-- TODO: better `none` behavior?

@[inline] def DeclNeeds.insertFreeDeclFor (currentDecl : Name) (k : DeclDeclNeedsKind)
    (usedDecl : Name) (declNeeds : DeclNeeds) : DeclNeeds :=
  declNeeds.alter currentDecl fun need? => need?.getD {} |>.insertFreeDecl k usedDecl

@[inline] def DeclNeeds.insertFixedDeclFor (currentDecl : Name) (k : DeclDeclNeedsKind)
    (mod : Name) (usedDecl : Name) (declNeeds : DeclNeeds) :
    DeclNeeds :=
  declNeeds.alter currentDecl fun need? => need?.getD {} |>.insertFixedDecl k mod usedDecl

-- @[inline] def DeclNeeds.fullNeeds (declNeeds : DeclNeeds) : Needs :=
--   declNeeds.foldl (init := .empty) fun acc _ { needs .. } => acc ∪ needs

structure DeclNode where
  type      : NameSet
  value     : NameSet

-- Can expect three stages: deps, caller availability application(?), source-module aggregation...

abbrev DeclDeps := NameMap DeclNode

structure ModuleNeed where
  /-- The name of the declaration that was used, implying the need for this module directly. -/
  -- TODO: `ModuleIdx` is redundant given the env. Exclude it?
  usedDecl : Name
  /-- The module index of the needed module, or `none` if from the current module. -/
  -- TODO: use module name instead?
  idx? : Option ModuleIdx
  /-- The availability the module is needed at, after accountign for intrinsic availabilities. -/
  -- TODO: maybe we should flip this; have API that says "attach this module at this availabiltiy to this decl" intead of potentially duplicating modules.
  availability : NeedsKind
  /-- The indirectly-used modules. -/
  indirect : Array ModuleIdx := #[]

/-- Given the intrinsic availability of `usedDecl`, what demanding a use of this decl at
`demanding : NeedsKind` implies in terms of needed modules. -/
def Lean.Environment.getModuleDepOfConst (usedDecl : Name) (demanding : NeedsKind)
    (env : Environment) : Option ModuleNeed := do
  let usedDecl ← env.getDepConstName? usedDecl
  let idx? := env.getModuleIdxFor? usedDecl
  let availability := { demanding with isMeta := demanding.isMeta && !isDeclMeta' env usedDecl }
  return {
    usedDecl, idx?, availability
    indirect := (indirectModUseExt.getState env)[usedDecl]?.getD #[] }

-- The thing is that isExported for LCNF essentially changes with private availability!
-- When the private scope is available, private definitions are able to satisfy a need for exported code.

partial def calcDeclNeeds (decl : Name) (env : Environment)
    (currentDecls : DeclNeeds := {}) : DeclNeeds := Id.run do
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
    -- Really this is a proxy for public meta = in the LCNF...also not true in our case, since the meta *closure* is what's important.
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
          -- Not needed at meta visibility if already intrinsically meta
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


/--
Calculates the needs for a given module `mod` from constants.

Does not account for `extraModUses`, since these are not decl-linked per se.

Collects needed declarations from the current module in `DeclNeeds`, together with the availability they're needed at. Recursively includes the needs of those declarations (not accounting for elaborator needs in their respective commands) in the result.
-/
-- Largely copied from `calcNeeds`, but with some key differences.
partial def calcDeclNeeds (decl : Name) (env : Environment)
    (currentDecls : DeclNeeds := {}) : DeclNeeds := Id.run do
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
          -- Not needed at meta visibility if already intrinsically meta
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
