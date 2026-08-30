/-
Copyright (c) 2023 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import Lean.Environment
public import Lean.Data.LOption

namespace Lean

/-- Return the name of the module in which a declaration was defined.
Returns the main module for declarations defined in the current environment. -/
public def Environment.getModuleFor? (env : Environment) (declName : Name) (skipRealize := false) :
    Option Name :=
  match env.getModuleIdxFor? declName with
  | none =>
    if env.findAsync? declName skipRealize |>.isSome then
      env.header.mainModule
    else none
  | some idx => env.header.moduleNames[idx.toNat]!

@[inline]
public def Environment.getModuleIdx! (env : Environment) (moduleName : Name) : ModuleIdx :=
  env.getModuleIdx? moduleName |>.get!

namespace IRPhases

/-- Whether having a constant at `φ₁` implies having that constant at `φ₂`. -/
def includes (φ₁ φ₂ : IRPhases) : Bool :=
  match φ₁ with
  | .all => true
  | .runtime => φ₂ == .runtime
  | .comptime => φ₂ == .comptime

/-- The smallest phase which includes both `φ₁` and `φ₂`. -/
def union (φ₁ φ₂ : IRPhases) : IRPhases :=
  match φ₁, φ₂ with
  | .runtime, .runtime => .runtime
  | .comptime, .comptime => .comptime
  | _, _ => .all

/-- The largest phase included by both `φ₁` and `φ₂`, if any. -/
def inter? (φ₁ φ₂ : IRPhases) : Option IRPhases :=
  match φ₁, φ₂ with
  | .all, .all => some .all
  | .runtime,  .runtime  | .runtime,  .all | .all, .runtime  => some .runtime
  | .comptime, .comptime | .comptime, .all | .all, .comptime => some .comptime
  | .runtime,  .comptime | .comptime, .runtime => none

instance : LE IRPhases where
  le φ₁ φ₂ := φ₂.includes φ₁ -- Note: swapped

instance : Union IRPhases where
  union := .union

end IRPhases

end Lean
