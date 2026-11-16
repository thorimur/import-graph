/-
Copyright (c) 2023 Jon Eugster. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Eugster
-/
module

import Lean.Meta.Match.MatcherInfo
public import Lean.CoreM

/-!
TODO: Some declarations in this file are duplicated from mathlib, but especially `isBlacklisted`
is deemed to specific for upstreaming to Batteries.
-/
namespace ImportGraph

open Lean Meta Elab

namespace Lean.Name

/-- Note: copied from `Mathlib.Lean.Name` -/
private def isBlackListed (declName : Name) : CoreM Bool := do
  if declName.toString.startsWith "Lean" then return true
  let env ← getEnv
  pure $ declName.isInternalDetail
   || isAuxRecursor env declName
   || isNoConfusion env declName
  <||> isRec declName <||> isMatcher declName

/--
Retrieve all names in the environment satisfying a predicate.

Note: copied from `Mathlib.Lean.Name`
-/
public def allNames (p : Name → Bool) : CoreM (Array Name) := do
  (← getEnv).constants.foldM (init := #[]) fun names n _ => do
    if p n && !(← isBlackListed n) then
      return names.push n
    else
      return names

/--
Retrieve all names in the environment satisfying a predicate,
gathered together into a `HashMap` according to the module they are defined in.

Note: copied from `Mathlib.Lean.Name`
-/
public def allNamesByModule (p : Name → Bool) : CoreM (Std.HashMap Name (Array Name)) := do
  (← getEnv).constants.foldM (init := ∅) fun names n _ => do
    if p n && !(← isBlackListed n) then
      let some m ← findModuleOf? n | return names
      -- TODO use `modify`/`alter` when available
      match names[m]? with
      | some others => return names.insert m (others.push n)
      | none => return names.insert m #[n]
    else
      return names

/--
Folds `f` over the prefixes of `Name`, starting with the longest. E.g.
``(`a.b.c).foldrPrefixesM f init`` results in
```
let v₁ ← f `a.b.c init
let v₂ ← f `a.b v₁
let v₃ ← f `a v₂
f .anonymous v₃
```
This is useful for certain `namespace`-related operations.
-/
@[specialize]
public def foldrPrefixesM {α} {m} [Monad m] (f : Name → α → m α) (init : α) (n : Name) : m α := do
  let val ← f n init
  match n with
  | .anonymous => pure val
  | .str pre _ | .num pre _ => foldrPrefixesM f val pre

open ImportGraph in
/--
Folds `f` over the prefixes of `Name`, starting with the longest. E.g.
``(`a.b.c).foldrPrefixes f init`` results in
```
let v₁ := f `a.b.c init
let v₂ := f `a.b v₁
let v₃ := f `a v₂
f .anonymous v₃
```
This is useful for certain `namespace`-related operations.
-/
@[inline]
public def foldrPrefixes {α} (f : Name → α → α) (init : α) (n : Name) : α :=
  n.foldrPrefixesM (m := Id) f init

end ImportGraph.Lean.Name

section deprecated

namespace Lean.Name.ImportGraph

@[deprecated ImportGraph.Lean.Name.allNamesByModule (since := "2026-11-14")]
public abbrev allNamesByModule := ImportGraph.Lean.Name.allNamesByModule

@[deprecated ImportGraph.Lean.Name.allNames (since := "2026-11-14")]
public abbrev allNames := ImportGraph.Lean.Name.allNames

/-- Returns the very first part of a name: for `ImportGraph.Lean.NameMap` it
returns `ImportGraph`. -/
@[deprecated Lean.Name.getRoot
  "Use `Lean.Name.getRoot`; if using the `s : String` parameter, check for `Name.anonymous`."
  +typeChanged (since := "2026-11-14")]
public def getModule (name : Name) (s := "") : Name :=
  match name with
    | .anonymous => .mkSimple s
    | .num _ _ => panic s!"panic in `getModule`: did not expect numerical name: {name}."
    | .str pre s => getModule pre s

end Lean.Name.ImportGraph
