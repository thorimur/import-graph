/-
Copyright (c) 2026 Thomas R. Murrills. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas R. Murrills
-/
module

public import Lean.Syntax

import Lean.Parser.Extra
import Lean.Parser.Command

import all Lean.Syntax -- We use `all` to access `updateLeadingAux`.

public section

namespace Lean

deriving instance Ord for Syntax.Range

/-- Like `Lean.Syntax.updateLeading`, but preserves the starting position of the syntax if it
exists (instead of setting it to `0`). See the docstring of `updateLeading` for more details. -/
def Syntax.updateLeadingPreservingStart : Syntax → Syntax :=
  fun stx => (replaceM updateLeadingAux stx).run' (stx.getPos?.getD 0)

/-- Like `Lean.TSyntax.updateLeading`, but preserves the starting position of the syntax if it
exists (instead of setting it to `0`). See the docstring of `updateLeading` for more details. -/
def TSyntax.updateLeadingPreservingStart {ks} (stx : TSyntax ks) : TSyntax ks :=
  ⟨stx.raw.updateLeadingPreservingStart⟩

/-- Gets the leading whitespace of `.original` `SourceInfo`, or `none` if not `.original`. -/
def SourceInfo.getLeading? : SourceInfo → Option Substring.Raw
  | .original (leading := leading) .. => leading
  | _ => none

/-- Gets the leading whitespace of `.original` `SourceInfo`, or the empty substring if not
`.original`. -/
@[inline] def SourceInfo.getLeading (info : SourceInfo) : Substring.Raw :=
  info.getLeading?.getD "".toRawSubstring

/-- Gets the trailing whitespace of `.original` `SourceInfo`, or the empty substring if not
`.original`. -/
@[inline] def SourceInfo.getTrailing (info : SourceInfo) : Substring.Raw :=
  info.getTrailing?.getD "".toRawSubstring

/-- Clear the `leading` whitespace of the given syntax if the head `SourceInfo` is `.original`, and
otherwise leave it unchanged. See `Syntax.unsetTrailing` for removing trailing whitespace. -/
def Syntax.unsetLeading (stx : Syntax) : Syntax :=
  stx.setHeadInfo <|
    match stx.getHeadInfo with
    | .original _ pos trailing endPos => .original "".toRawSubstring pos trailing endPos
    | info => info

/-- Get the start position of the leading whitespace of `.original` `SourceInfo`, or `none` if it
is not `.original`. -/
def SourceInfo.getOriginalLeadingPos? : SourceInfo → Option String.Pos.Raw
  | .original (leading := leading) .. => some leading.startPos
  | _ => none

/-- Get the start position of the leading whitespace of `.original` `SourceInfo`, or the start
position of `.synthetic` `SourceInfo` (and `none` otherwise).

If `canonicalOnly := false` (the default), also returns `none` on non-canonical `.synthetic`
`SourceInfo`. -/
def SourceInfo.getLeadingPos? (info : SourceInfo) (canonicalOnly := false) :
    Option String.Pos.Raw :=
  match info, canonicalOnly with
  | .original (leading := leading) ..,              _     => some leading.startPos
  | .synthetic (pos := pos) (canonical := true) .., _
  | .synthetic (pos := pos) ..,                     false => some pos
  | _,                                              _     => none

/--
Get the start position of the leading whitespace of the `Syntax` if it is original, or the
start position if synthetic (and `none` otherwise).

If `canonicalOnly := false` (the default), also returns `none` on non-canonical synthetic `Syntax`.
-/
@[inline] def Syntax.getLeadingPos? (stx : Syntax) (canonicalOnly := false) :
    Option String.Pos.Raw :=
  stx.getHeadInfo.getLeadingPos? canonicalOnly

/--
Converts a `DataValue` that may appear as the value of some `set_option` to appropriate `Syntax`.
This only returns `some _` on user-writable `set_option` `DataValue`s (`.ofBool`, `.ofNat`,
`.ofString`) and `none` on the rest.

Note that the parser responsible for the option values is
```
def Parser.Command.optionValue :=
  nonReservedSymbol "true" <|> nonReservedSymbol "false" <|> strLit <|> numLit
```
but this is not a `leading_parser`, and creates no corresponding syntax node. Instead, syntax
quotations constructing a `set_option` expect a ``TSyntax [`str, `num]``.
-/
def DataValue.toSetOptionValueSyntaxFrom? (ref : Syntax) (val : DataValue) (canonical := false)
    : Option (TSyntax ``Parser.Command.optionValue) :=
  match val with
  | .ofNat n      => some ⟨Syntax.mkNumLit (toString n) (info := .fromRef ref canonical)⟩
  | .ofBool true     => some ⟨mkAtomFrom ref "true" canonical⟩
  | .ofString str => some ⟨Syntax.mkStrLit str (info := .fromRef ref canonical)⟩
  | _ => none

@[inherit_doc DataValue.toSetOptionValueSyntaxFrom?]
def DataValue.toSetOptionValueSyntax? (val : DataValue)
    : Option (TSyntax ``Parser.Command.optionValue) :=
  val.toSetOptionValueSyntaxFrom? .missing

instance : Coe (TSyntax [`str, `num]) (TSyntax ``Parser.Command.optionValue) := ⟨(⟨·.raw⟩)⟩
instance : Coe (TSyntax ``Parser.Command.optionValue) (TSyntax [`str, `num]) := ⟨(⟨·.raw⟩)⟩

end Lean
