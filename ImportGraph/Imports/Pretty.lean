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

-- Honestly, should these just be strings...?
/-- Whitespace surrounding an import. We make no guarantees about the meaningfulness of the positions in these `Substring.Raw`s, which might be synthetic.

Includes exactly one newline at the end of `leading` iff there are other non-whitespace characters in it. -/
structure Whitespace where
  leading : String
  trailing : String

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
    let leading := if leading.isEmpty then leading.toString else leading.toString ++ "\n"
    let trailing := imp.stx.raw.getTailInfo.getTrailing.toString -- does not include `'\n'`
    (imp, { leading, trailing })


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

def Whitespace.around (a : α) (ws : Whitespace) [ToFormat α] : Format :=
  f!"{ws.leading}{a}{ws.trailing}"

/-- {ws₁leading}{ws₂.leading}___{ws₁.trailing}{ws₂.trailing} -/
def Whitespace.appendBoth (ws₁ ws₂ : Whitespace) : Whitespace where
  leading := ws₁.leading ++ ws₂.leading
  trailing := ws₁.trailing ++ ws₂.trailing

def _root_.String.joinNonempty (sep s₁ s₂ : String) : String :=
  if s₁.isEmpty then s₂ else if s₂.isEmpty then s₁ else s!"{s₁}{sep}{s₂}"

/-- {ws₁leading}{ws₂.leading}___{ws₁.trailing}{ws₂.trailing} -/
def Whitespace.joinNewline (ws₁ ws₂ : Whitespace) : Whitespace where
  leading := "\n".joinNonempty ws₁.leading ws₂.leading
  trailing := "\n".joinNonempty ws₁.trailing ws₂.trailing

def Whitespace.empty : Whitespace where
  leading := ""
  trailing := ""

protected inductive Import.FormatError where
| /-- In this case, `ref.toImport` matches the `imp` exactly. -/
  multipleTrailing (imp : Import) (trailings : Array (ImportRef × String))
| /-- We don't attach the trailing if there's a mismatch between the `imp` and `ref.toImport`, as
  the user should review the annotation to make sure it still makes sense. -/
  reviewTrailing (imp : Import) (refsWithTrailing : Array (ImportRef × String))
| unusedLeading (refsWithLeading : Array (ImportRef × String))

deriving instance Repr for Whitespace

deriving instance Repr for ImportRef

/-- Assumes whitespace has been created with `headerToImportRefsWithWhitespace` -/
def collectWithWhitespaceFromSource (imps : Array Import)
    (sourceImps : Array (ImportRef × Whitespace)) :
    Array (Import × Whitespace) × Array Import.FormatError := Id.run do
  let mut names : NameSet := {}
  let mut impsWithRefs : Array (Import × Array (ImportRef × Whitespace)) := #[]
  for imp in imps do
    let refs := if names.contains imp.module then #[] else
      sourceImps.foldl (init := #[]) fun acc ref =>
        if ref.1.module == imp.module then
          acc.push ref
        else acc
    impsWithRefs := impsWithRefs.push (imp, refs)
    names := names.insert imp.module

  let mut allErrors : Array Import.FormatError := #[]
  let unusedRefsWithLeading := sourceImps.filterMap fun (ref, { leading .. }) =>
    if names.contains ref.module || leading.isEmpty then none else some (ref, leading)
  unless unusedRefsWithLeading.isEmpty do
    allErrors := allErrors.push <| .unusedLeading unusedRefsWithLeading
  let mut impsWithWs : Array (Import × Whitespace) := #[] -- The final array
  for (imp, refs) in impsWithRefs do
    let mut totalLeading := ""
    let mut trailings := #[]
    let mut review : Array (ImportRef × String) := #[]
    for (ref, { leading, trailing }) in refs do
      unless leading.isEmpty do
        totalLeading := totalLeading ++ leading
      unless trailing.isEmpty do
        if imp == ref.toImport then
          trailings := trailings.push (ref, trailing)
        else
          review := review.push (ref, trailing)
    unless review.isEmpty do
      allErrors := allErrors.push <| .reviewTrailing imp review
    if trailings.size > 1 then
      allErrors := allErrors.push <| .multipleTrailing imp trailings
    let trailing := if let #[(_,trailing)] := trailings then trailing else ""
    impsWithWs := impsWithWs.push (imp, { leading := totalLeading, trailing })
  return (impsWithWs, allErrors)

-- TODO: group annotations instead of
instance : ToFormat Import.FormatError where
  format
    | .multipleTrailing imp refsWithTrailing => Id.run do
      let annotations := f!"\n".joinSep (refsWithTrailing.map fun (ref, trailing) =>
        f!"{ref.toImport}{trailing}").toList
      f!"Multiple annotations were given for `{imp}`:\n```\n{annotations}\n```"
    | .reviewTrailing imp refsWithTrailing => Id.run do
      let mut msg := f!"Annotations were present when importing `{imp.module}`, but this module is \
        now imported differently as `{imp}`. Decide if the following original annotations still \
        apply.\n```"
      for (ref, trailing) in refsWithTrailing do
        msg := f!"{msg}\n{ref.toImport}{trailing}"
      return f!"{msg}\n```"
    | .unusedLeading refsWithLeading => Id.run do
      let mut msg := f!"The following imports did not appear in the new import list, but had \
        comments preceding them:\n```"
      for (ref, leading) in refsWithLeading do
        msg := f!"{msg}\n{leading}{ref.toImport}"
      return f!"{msg}\n```"

local instance Whitespace.prettyOrd : Ord Whitespace where
  compare ws₁ ws₂ :=
    (compare ws₁.leading.length ws₂.leading.length).swap -- Longer leading comments come first
      |>.then (compare ws₁.trailing.length ws₂.trailing.length) -- Annotations come last
      |>.then (compare ws₁.leading ws₂.leading) -- Alphabetical for completeness
      |>.then (compare ws₂.trailing ws₂.trailing)

local instance : Ord (Import × Whitespace) where
  compare := fun (i₁, ws₁) (i₂, ws₂) =>
    compare i₁ i₂ |>.then (compare ws₁ ws₂)

/-- Assumes sorted. -/
private def Import.splitGroups (imps : List Import) (splitMeta := false) : List (List Import) :=
  imps.splitBy fun i₁ i₂ =>
    i₁.isExported == i₂.isExported &&
    i₁.importAll == i₂.importAll &&
    (!splitMeta || i₁.isMeta == i₂.isMeta)

/-- Assumes sorted. -/
private def Import.splitGroupsWithWhitespace (imps : List (Import × Whitespace))
    (splitMeta := false) : List (List (Import × Whitespace)) :=
  imps.splitBy fun (i₁,_) (i₂,_) =>
    i₁.isExported == i₂.isExported &&
    i₁.importAll == i₂.importAll &&
    (!splitMeta || i₁.isMeta == i₂.isMeta)

protected inductive Import.FormatBehavior where
| none
| sorted
| grouped (splitMeta := false)

instance : ToFormat (Import × Whitespace) where
  format := fun (imp, ws) => ws.around imp

def prettyWithWhitespace (imps : Array (Import × Whitespace))
    (fmtBehavior := Import.FormatBehavior.grouped) : Format := Id.run do
  let imps := if fmtBehavior matches .none then imps else imps.qsortOrd
  if let .grouped splitMeta := fmtBehavior then
    let groups := Import.splitGroupsWithWhitespace imps.toList splitMeta
    f!"\n\n".joinSep (groups.map (f!"\n".joinSep ·))
  else
    f!"\n".joinSep imps.toList

@[inline] def prettyWithWhitespaceFromSource (imps : Array Import)
    (sourceImps : Array (ImportRef × Whitespace)) (fmtBehavior := Import.FormatBehavior.grouped) : Format × Option Format :=
  let (impsWithWs, errs) := collectWithWhitespaceFromSource imps sourceImps
  (prettyWithWhitespace impsWithWs fmtBehavior,
    if errs.isEmpty then none else f!"\n\n".joinSep errs.toList)

@[inline] def prettyWithWhitespaceFromSourceAndErrorComment (imps : Array Import)
    (sourceImps : Array (ImportRef × Whitespace)) (fmtBehavior := Import.FormatBehavior.grouped) :
    Format :=
  let (impsFmt, errComment?) := prettyWithWhitespaceFromSource imps sourceImps fmtBehavior
  if let some errComment := errComment? then f!"{impsFmt}\n\n/-\n{errComment}\n-/" else impsFmt


section silly

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

elab "#test" Parser.Module.header "#then" Parser.Module.header  : command => pure ()

def showWhitespace : Linter where
  run cmd := do
    match cmd with
    | `(command| #test $header₁ #then $header₂) => do
      let imps₁ := headerToImportRefs header₁ |>.map (·.toImport)
      let imps₂ := headerToImportRefsWithWhitespace header₂
      logInfo m!"{imps₂.map (·.1.module)}"
      logInfo m!"{prettyWithWhitespaceFromSourceAndErrorComment imps₁ imps₂}"
    | _ => pure ()
    -- logInfo m!"{reprint' cmd.updateLeading |>.getD "<could not reprint>"}"
    return

run_cmd replaceLinter showWhitespace



-- The right way to do this is "preserve all whitespace around imports" after splitting.
-- We kind of want "pretty-print with whitespace"...

#test
/- copyright -/
module

public import Foo.Bar -- shake: milk
-- Comment 1
-- comment2
import Baz.Baz -- other

--some stuff

#then

module

public import Foo.Bar -- shake: milk
-- Comment 1
-- comment2
import Baz.Baz -- other

import Baz.Baz -- other₂

-- aAAAAAA
import Qq


--oof
import G

--some stuff

example : True := trivial

end silly
