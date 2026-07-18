/-
Copyright (c) 2023 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison, Paul Lezeau
-/
module

public meta import ImportGraph.Imports.Pretty
public meta import ImportGraph.Imports.Redundant
public meta import ImportGraph.Imports.RequiredModules
public meta import ImportGraph.Lean.Environment
public meta import ImportGraph.Shake.Algebra
public meta import ImportGraph.Shake.Environment
public meta import ImportGraph.Tools.NeedsGrid

import Lean
import ImportGraph.Lean.Environment
import ImportGraph.Shake.Algebra
import ImportGraph.Shake.Basic
import Lake.CLI.Shake

import all ImportGraph.Shake.Environment
import all ImportGraph.Tools.NeedsGrid

public meta section

open Lean

/--
Return the names of the modules in which constants used in the current file were defined,
with modules already transitively imported removed.

Note that this will *not* account for tactics and syntax used in the file,
so the results may not suffice as imports.
-/
def Lean.Environment.minimalRequiredModules (env : Environment) : Array Name :=
  let required := env.requiredModules.toArray.erase env.header.mainModule
  let redundant := findRedundantImports env required
  required.filter fun n => ¬ redundant.contains n

def ImportGraph.parseCurrentHeader {m} [Monad m] [MonadLog m] [MonadLiftT IO m] :
    m (TSyntax `Lean.Parser.Module.header × Parser.ModuleParserState × MessageLog) := do
  Parser.parseHeader (Parser.mkInputContext (← getFileMap).source (← getFileName))

open ImportGraph

def _root_.Lean.Syntax.unsetLeading (stx : Syntax) : Syntax :=
  stx.setHeadInfo <|
    match stx.getHeadInfo with
    | .original _ pos trailing endPos => .original "".toRawSubstring pos trailing endPos
    | info => info

def _root_.Lean.SourceInfo.getLeadingPos? (info : SourceInfo) (canonicalOnly := false) :
    Option String.Pos.Raw :=
  match info, canonicalOnly with
  | .original (leading := leading) ..,  _ => some leading.startPos
  | .synthetic (pos := pos) (canonical := true) .., _
  | .synthetic (pos := pos) .., false => some pos
  | _,                         _     => none

def _root_.Lean.Syntax.getLeadingPos? (stx : Syntax) (canonicalOnly := false) :
    Option String.Pos.Raw :=
  stx.getHeadInfo.getLeadingPos? canonicalOnly

open ImportGraph Lean

elab tk:"#norm_imports" : command => do
  let transDeps := (← getEnv).mkTransDeps
  let transNeeds := (← getEnv).transNeeds transDeps
  let reducedImps := transNeeds.reduce transDeps |>.toImports (← getEnv)
  -- TODO: remove private imports that come from `import all`
  let reducedImps := Import.includeAll (← getEnv).header.imports reducedImps
  let (header, _, log) ← parseCurrentHeader
  if log.hasErrors then
    -- This should be impossible.
    throwError m!"The current imports failed to parse. Errors:\n\
      {m!"\n".joinSep <| log.toList.map (·.data) }"
  let impsWithRefs := headerToImportRefsWithWhitespace header
  let (msg, hasErrors) := Import.prettyWithSourceWhitespaceAndErrorComment reducedImps impsWithRefs
  let stxRef := mkNullNode (impsWithRefs.map (·.1.stx.raw))
  let sourceSubstr : Substring.Raw := {
      str := (← getFileMap).source
      startPos := stxRef.getLeadingPos?.getD (stxRef.getPos?.get!)
      -- Ensure we include any annotation after the last import
      stopPos := stxRef.getTrailingTailPos?.get! }
  let (sourceSubstr, str) :=
    -- We want two newlines in front of the suggestion to separate it from `module`.
    -- Either chop these off the source if we can, or add them to our new string.
    -- Chopping off allows us to avoid unsightly whitespace at the top of the suggestion.
    let str := msg.pretty (width := Std.Format.getWidth <|← getOptions)
    if let some sourceSubstr := sourceSubstr.dropPrefix? "\n\n".toRawSubstring then
      (sourceSubstr, str)
    else
      (sourceSubstr, s!"\n\n{str}")
  if sourceSubstr.toString == str then
    logInfo m!"Imports are normalized."
  else
    let newImports ← Elab.Command.liftCoreM <|
      -- Need `.ofRange` here to insist on overwriting trailing whitespace.
      Meta.Hint.mkSuggestionsMessage #[{
          suggestion := str
          span? := Syntax.ofRange ⟨sourceSubstr.startPos, sourceSubstr.stopPos⟩
          diffGranularity := if hasErrors then .none else .word }]
        tk "Normalize imports: " false
    if hasErrors then
      logWarning m!"Imports can be normalized, but some comments could not be carried over. \
        Please review the following description after normalizing.\n{newImports}"
    else
      -- Note: the widget nature of `diffGranularity := .word` effectively gives us a newline
      -- before `{newImports}`.
      logWarning m!"Imports can be normalized:{newImports}"

#norm_imports

-- #norm_imports
-- #min_imports

run_cmd do
  let env ← getEnv
  let mut encountered : Std.HashSet Name := {}
  let mut outOfOrder : Std.HashMap (Name × Nat) (Array Import) := {}
  for h : i in 0...env.header.moduleData.size do
    let { imports .. } := env.header.moduleData[i]
    let name := env.header.modules[i]!.module
    let notEncounteredYet := imports.filter (!encountered.contains ·.module)
    unless notEncounteredYet.isEmpty do
      outOfOrder := outOfOrder.insert (name, i) notEncounteredYet
    encountered := encountered.insert name
  let (eventuallyEncountered, notEncountered) :=
    outOfOrder.valuesArray.flatten.partition (encountered.contains ·.module)
  logInfo m!"\n\
    total := {env.header.moduleData.size}\n\
    eventuallyEncountered := {eventuallyEncountered.size}\n\
    notEncountered := {notEncountered.size}\n\
    {outOfOrder.toArray.qsort (·.1.2 < ·.1.2)}"


-- /--
-- Try to compute a minimal set of imports for this file,
-- by analyzing the declarations.

-- This must be run at the end of the file,
-- and is not aware of syntax and tactics,
-- so the results will likely need to be adjusted by hand.
-- -/
-- elab "#min_imports" : command => do
--   let imports := (← getEnv).minimalRequiredModules.qsort (·.toString < ·.toString)
--     |>.toList.map (fun n => "public import " ++ n.toString)
--   logInfo <| Format.joinSep imports "\n"

-- -- deprecated since 2024-07-06
-- elab "#minimize_imports" : command => do
--   logWarning m!"'#minimize_imports' is deprecated: please use '#min_imports'"
--   Elab.Command.elabCommand (← `(command| #min_imports))
