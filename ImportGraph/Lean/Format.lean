/-
Copyright (c) 2026 Thomas R. Murrills. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas R. Murrills
-/
module

public section

/--
Puts `Format` into a comma-separated list with `"and"` at the back (with the serial comma).

Best used on non-empty lists; returns `"– none –"` for an empty list.
-/
def Std.Format.andList [ToFormat α] (xs : List α) : Format :=
  match xs with
  | [] => "– none –"
  | [x] => format x
  | [x₀, x₁] => f!"{x₀} and {x₁}"
  | xs@(_ :: _ :: _) => f!"{f!", ".joinSep xs.dropLast}, and {xs.getLast (by grind)}"
