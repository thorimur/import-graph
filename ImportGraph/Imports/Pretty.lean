module

public import Lean.Setup
public meta import Lean.Parser.Module.Syntax

/-!
# Pretty-printing and normalizing `import` syntax

This module defines utilities for pretty-printing imports.
-/

public section

namespace Lean

protected abbrev Syntax.Import := TSyntax ``Parser.Module.import

/-- Extends `Import` with ``stx : TSyntax `Lean.Parser.Module.import`` to allow reporting at the
given import. -/
structure ImportRef extends Import where
  stx : TSyntax ``Parser.Module.import

/-- Returns the module `Ident` (following `(public)? (meta)? import (all)?` of a given
`ImportRef`. -/
def ImportRef.getIdent (i : ImportRef) : Ident :=
  match i.stx with
  | `(Parser.Module.import|
      $[public]? $[meta]? import $[all]? $n:ident) => n
  | _ => ⟨.missing⟩

/-- Destructures header syntax (`(module)? (prelude)? $imports*`) into an array of `Import`s
together with the import syntax that gave rise to them. See also `headerToImports`. -/
def headerToImportRefs (header : TSyntax ``Parser.Module.header) : Array ImportRef :=
  match header with
  | `(Parser.Module.header| $[module%$moduleTk]? $[prelude]? $imports*) =>
    imports.map fun
      | stx@`(Parser.Module.import|
          $[public%$publicTk]? $[meta%$metaTk]? import $[all%$allTk]? $n:ident) =>
        { module := n.getId
          importAll := allTk.isSome
          isExported := publicTk.isSome || moduleTk.isNone
          isMeta := metaTk.isSome
          stx := ⟨stx⟩ }
      | _ => { module := `illformedStx, stx := ⟨.missing⟩ }
  | _ => #[{ module := `illformedStx, stx := ⟨.missing⟩ }]

namespace Import

local instance : Ord Import where
  compare i₁ i₂ := (compare i₁.isExported i₂.isExported).swap -- `public import < import`
    |>.then (compare i₁.importAll i₂.importAll) -- `import < import all`
    |>.then (compare i₁.isMeta i₂.isMeta).swap -- `meta import < import`
    |>.then (Name.cmp i₁.module i₂.module) -- alphabetical

local instance : Ord ImportRef where
  compare i₁ i₂ := compare i₁.toImport i₂.toImport

/--
Sorts an array of imports into groups. Schematically:
```null
#[
  public meta import ...
  public import ...
  meta import ...
  import ...
  meta import all ...
  import all ...
]
```
-/
@[inline] def sortPretty (imports : Array Import) : Array Import := imports.qsortOrd

@[inline] def pretty (imports : Array Import) : Format := f!"\n".joinSep imports.qsortOrd.toList

def prettyGrouped (imports : Array Import) : Format :=
  let imps := (sortPretty imports).toList.splitBy fun i₁ i₂ =>
    i₁.isExported == i₂.isExported && i₁.importAll == i₂.importAll
  f!"\n\n".joinSep <| imps.map (f!"\n".joinSep ·)

-- #eval prettyGrouped #[{ module := `Foo.Baaaz, isMeta := true }, { module := `Foo }, { module := `Foo.Baz }, { module := `Foo.Baaaz, isExported := false, importAll := true }, { module := `Foo.Baz, isExported := false }, { module := `Foo.Baaaz, isMeta := true, isExported := false },  { module := `Foo.Bar }, { module := `Foo.Baaaz, isExported := false, isMeta := true, importAll := true }, ]

/-- Attaches non-blank whitespace following imports in `ImportRef` to the corresponding entries in `Import`, if they exist. If `last := true` (the default), attaches all whitespace following the last `ImportRef` to the end of the result. If `sameLine := true` (the default) discards comments not on the same line. -/
def prettyWithTrailingFromSource (imps : Array Import) (sourceImps : Array ImportRef)
    (last := true) (sameLine := true) : Format := sorry

def _root_.Lean.SourceInfo.trailingString? : SourceInfo → Option String
  | .original (trailing := trailing) .. => trailing.toString
  | _ => none

@[inline] def _root_.Lean.SourceInfo.trailingString (info : SourceInfo) : String :=
  info.trailingString?.getD ""

def ImportRef.formatWithTrailing (i : ImportRef) (sameLine := true) : Format :=
  let trailing := i.stx.raw.getTailInfo.trailingString
  let trailing :=
    if sameLine then trailing.takeWhile (· != '\n') |>.take 1 |>.toString else trailing
  f!"{i.toImport}{trailing}"
