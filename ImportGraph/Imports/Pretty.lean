module

public import Lean.Setup
public meta import Lean.Parser.Module.Syntax
public import Lean.Elab.Command
public meta import Lean.Elab.Command
import all Lean.Syntax

/-!
# Pretty-printing and normalizing `import` syntax

This module defines utilities for pretty-printing imports.
-/

public section

namespace Lean

def Syntax.updateLeadingPreservingStart : Syntax → Syntax :=
  fun stx => (replaceM updateLeadingAux stx).run' (stx.getPos?.getD 0)

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
def headerToImportStx (header : TSyntax ``Parser.Module.header) :
    TSyntaxArray ``Parser.Module.import :=
  match header with
  | `(Parser.Module.header| $[module%$moduleTk]? $[prelude]? $imports*) =>
    imports
  | _ => #[⟨.missing⟩]

/-- Destructures header syntax (`(module)? (prelude)? $imports*`) into an array of `Import`s
together with the import syntax that gave rise to them. See also `headerToImports`. -/
def getModule (header : TSyntax ``Parser.Module.header) : Option Syntax :=
  match header with
  | `(Parser.Module.header| $[module%$moduleTk]? $[prelude]? $_*) => moduleTk
  | _ => none

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
open Lean Elab Command

def replaceLinter (l : Linter) : IO Unit := do
  lintersRef.modify fun ls => ls.filter (·.name != l.name)
  addLinter l

#check Syntax.reprint
partial def reprint' (stx : Syntax) : Option String := do
  let mut s := ""
  for stx in stx.topDown (firstChoiceOnly := true) do
    match stx with
    | .atom info val           => s := s ++ reprintLeaf info val
    | .ident info rawVal _ _   => s := s ++ reprintLeaf info rawVal.toString
    | .node _    kind args     =>
      if kind == choiceKind then
        -- this visit the first arg twice, but that should hardly be a problem
        -- given that choice nodes are quite rare and small
        let s0 ← reprint' args[0]!
        for arg in args[1...*] do
          let s' ← reprint' arg
          guard (s0 == s')
    | _ => pure ()
  return s
where
  reprintLeaf (info : SourceInfo) (val : String) : String :=
    match info with
    | SourceInfo.original lead _ trail _ => s!"[{lead}|{val}|{trail}]"
    -- no source info => add gracious amounts of whitespace to definitely separate tokens
    -- Note that the proper pretty printer does not use this function.
    -- The parser as well always produces source info, so round-tripping is still
    -- guaranteed.
    | _  => s!"⟦{val}⟧"

def showWhitespace : Linter where
  run cmd := logInfo m!"{reprint' cmd.updateLeading |>.getD "<could not reprint>"}"

run_cmd replaceLinter showWhitespace

elab "#test" Parser.Module.header : command => pure ()

-- The right way to do this is "preserve all whitespace around imports" after splitting.
-- We kind of want "pretty-print with whitespace"...

#test
/- copyright -/
module

import Foo.Bar -- shake: milk
-- Comment 1
-- comment2
import Baz.Baz -- other

--some stuff

example : True := trivial

-- Honestly, should these just be strings...?
/-- Whitespace surrounding an import. We make no guarantees about the meaningfulness of the positions in these `Substring.Raw`s, which might be synthetic.

Includes exactly one newline at the end of `leading` iff there are other non-whitespace characters in it. -/
structure Whitespace where
  leading : Substring.Raw
  trailing : Substring.Raw

def _root_.Lean.TSyntax.updateLeading {ks} (t : TSyntax ks) : TSyntax ks :=
  ⟨t.raw.updateLeading⟩

def _root_.Lean.TSyntax.updateLeadingPreservingStart {ks} (t : TSyntax ks) : TSyntax ks :=
  ⟨t.raw.updateLeadingPreservingStart⟩


def _root_.Lean.SourceInfo.getLeading : SourceInfo → Substring.Raw
  | .original (leading := leading) .. => leading
  | _ => "".toRawSubstring

def _root_.Lean.SourceInfo.getTrailing : SourceInfo → Substring.Raw
  | .original (trailing := trailing) .. => trailing
  | _                                  => "".toRawSubstring



/- Consider the edge case:
```
import Foo
-- Comment about Foo

-- Comment about Bar
import Bar
```
We could detect this, but don't yet. Note: we'd need to not count newlines that appear within `/- -/`.

We also don't handle
```
/-
Copyright ...
-/
import
```
but that's only a problem in non-modules, which we don't handle anyway yet.

We also don't account for trailing comments on lines after the line of the final import.
-/
private def headerToImportRefsWithWhitespace (header : TSyntax ``Parser.Module.header) :
    Array (ImportRef × Whitespace) :=
  let imps := headerToImportRefs header.updateLeadingPreservingStart
  imps.map fun imp =>
    let leading := imp.stx.raw.getHeadInfo.getLeading.trim
    let leading := if leading.isEmpty then leading else leading.toString ++ "\n" |>.toRawSubstring
    let trailing := imp.stx.raw.getTailInfo.getTrailing -- does not include `'\n'`
    (imp, { leading, trailing })

-- #eval prettyGrouped #[{ module := `Foo.Baaaz, isMeta := true }, { module := `Foo }, { module := `Foo.Baz }, { module := `Foo.Baaaz, isExported := false, importAll := true }, { module := `Foo.Baz, isExported := false }, { module := `Foo.Baaaz, isMeta := true, isExported := false },  { module := `Foo.Bar }, { module := `Foo.Baaaz, isExported := false, isMeta := true, importAll := true }, ]

def Whitespace.around (a : α) (ws : Whitespace) [ToFormat α] : Format :=
  f!"{ws.leading}{a}{ws.trailing}"

/-- {ws₁leading}{ws₂.leading}___{ws₁.trailing}{ws₂.trailing} -/
def Whitespace.appendBoth (ws₁ ws₂ : Whitespace) : Whitespace where
  leading := ws₁.leading.toString ++ ws₂.leading.toString |>.toRawSubstring
  trailing := ws₁.trailing.toString ++ ws₂.trailing.toString |>.toRawSubstring

def _root_.String.joinNonempty (sep s₁ s₂ : String) : String :=
  if s₁.isEmpty then s₂ else if s₂.isEmpty then s₁ else s!"{s₁}{sep}{s₂}"

/-- {ws₁leading}{ws₂.leading}___{ws₁.trailing}{ws₂.trailing} -/
def Whitespace.joinNewline (ws₁ ws₂ : Whitespace) : Whitespace where
  leading := "\n".joinNonempty ws₁.leading.toString ws₂.leading.toString |>.toRawSubstring
  trailing := "\n".joinNonempty ws₁.trailing.toString ws₂.trailing.toString |>.toRawSubstring

def Whitespace.empty : Whitespace where
  leading := "".toRawSubstring
  trailing := "".toRawSubstring

/-- Assumes whitespace has been created with `headerToImportRefsWithWhitespace` -/
def prettyWithWhitespaceFromSource (imps : Array Import)
    (sourceImps : Array (ImportRef × Whitespace)) : Format := Id.run do
  let mut names : NameSet := {}
  let mut impsWithWs : Array (Import × Array (ImportRef × Whitespace)) := #[]
  for imp in imps do
    let refs := if names.contains imp.module then #[] else
      sourceImps.foldl (init := #[]) fun acc impRefWithWs =>
        if impRefWithWs.1.module == imp.module then
          acc.push impRefWithWs
        else acc
    impsWithWs := impsWithWs.push (imp, refs)
    names := names.insert imp.module
  let mut fmt := Format.nil
  let mut allErrors := #[]
  for (imp, refs) in impsWithWs do
    let mut totalLeading := ""
    let mut trailings := #[]
    let mut errors := #[]
    let mut impFmt := f!"{imp}"
    for (ref, { leading, trailing }) in refs do
      unless leading.isEmpty do
        totalLeading := totalLeading ++ leading.toString
      unless trailing.isEmpty do
        if imp == ref.toImport then
          trailings := trailings.push trailing
        else
          errors := errors.push (ref, trailing.toString)
    if let #[trailing] := trailings then
      impFmt := f!"{impFmt}{trailing.toString}"
    if trailings.size > 1 then
      allErrors := allErrors.push f!"Multiple annotations were found: {trailings}"

  if trailings.size > 1 then
  sorry







      -- for (impRef, nextWs) in sourceImps do
      --   if impRef.module == imp.module then
      --     if !ws.trailing.isEmpty && !nextWs.trailing.isEmpty then
      --       errors := errors.push (impRef, imp, nextWs)
      --     let trailing ← do
      --       if ws.trailing.isEmpty then
      --         if impRef.toImport == imp then
      --           pure nextWs.trailing
      --         else
      --           errors := errors.push (impRef, imp, nextWs)
      --           pure ws.trailing
      --       else pure ws.trailing
      --     ws := {
      --       leading := ws.leading.toString ++ nextWs.leading.toString |>.toRawSubstring
      --       trailing
      --     }
      -- fmts.push f!"{ws.lead}"



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

def mkImportReplacement ()
