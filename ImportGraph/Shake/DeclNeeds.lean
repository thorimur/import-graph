module

import all Lake.CLI.Shake

open Lean Lake.Shake

/-!
Note: this file needs to be imported with `import all`.
-/

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

Collects needed declarations from the current module in `DeclNeeds`, together with the availability they're needed at. Recursively includes the needs of those declarations (not accounting for elaborator needs in their respective commands) in the result.
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
        if let some (j : ModuleIdx) := env.getModuleIdxFor? c then
          let k := { k with isMeta := k.isMeta && !isDeclMeta' env c }
          deps := deps.union k {j}
          for (indMod : ModuleIdx) in indirectModUses[c]?.getD #[] do
            /- The commented-out gate is only relevant if we're downstream of the imports we want
            to minimize, and may know about more indirectModUses than were known about in `i`.

            Supporting downstream runs would mean supplying the `originalMod?` of the top-level
            `decl` to `visitExpr`, and providing `transDeps`. -/
            -- if s.transDeps[i]!.has k indMod then
              deps := deps.union k {indMod}
        else
          -- `c` is from the same module--we need it at the given `k`
          unless extras.contains c || c == decl do -- just in case
            extras := extras.insert k decl c
            (deps, extras) := calcDeclNeeds c env deps extras
      return (deps, extras)
