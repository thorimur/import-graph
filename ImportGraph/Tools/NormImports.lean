/-
Copyright (c) 2026 Thomas R. Murrills. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas R. Murrills
-/
module

public meta import ImportGraph.Imports.FromSource
public meta import ImportGraph.Imports.Pretty
public meta import ImportGraph.Lean.Syntax
public meta import ImportGraph.Shake.Algebra
public meta import ImportGraph.Shake.Basic
public meta import ImportGraph.Shake.Environment
public meta import Lean.Elab.Command

meta import all ImportGraph.Shake.Environment

open ImportGraph Lean

/-- Normalizes the imports of the current file. This ensures that the same modules are available at the same visibilities and phases. It does not take into account the declarations or usages of those modules in the current file; for that, see `#min_imports`. -/
elab tk:"#norm_imports" : command => do
  unless (← getEnv).header.isModule do
    -- TODO: handle non-modules. Modifying the final `Import` array might be sufficient;
    -- all shake internals likely still work.
    throwError "`#norm_imports` currently only works in the module system."
  let transDeps := (← getEnv).mkTransDeps
  let transNeeds := (← getEnv).transNeeds transDeps
  let reducedImps := transNeeds.reduce transDeps |>.toRawImports (← getEnv)
  -- TODO: remove private imports that are implied by `import all`.
  let reducedImps := Lake.Shake.Import.includeAll (← getEnv).header.imports reducedImps
  let (header, _, log) ← parseCurrentHeader
  if log.hasErrors then
    -- This should be impossible.
    throwError m!"The current imports failed to parse. Errors:\n\
      {m!"\n".joinSep <| log.toList.map (·.data)}"
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
    -- Note: we never need to consider the trivial case of no imports, since running this command
    -- requires imports.
    -- TODO: Allow the user to filter out this `ImportGraph` import?
    let newImports ← Elab.Command.liftCoreM <|
      -- Need `.ofRange` here to insist on overwriting trailing whitespace.
      Meta.Hint.mkSuggestionsMessage #[{
          suggestion := str
          span? := Syntax.ofRange ⟨sourceSubstr.startPos, sourceSubstr.stopPos⟩
          -- The diff view often gets confused by imports that are shown in the error comment.
          diffGranularity := if hasErrors then .none else .word
          toCodeActionTitle? := some fun _ => "Normalize imports" }]
        tk none (forceList := false)
    if hasErrors then
      logWarning m!"Imports can be normalized, but some comments could not be carried over. \
        Please review the comment that will be inserted after the imports.\n{newImports}"
    else
      -- Note: the widget nature of `diffGranularity := .word` effectively gives us a newline
      -- before `{newImports}`.
      logWarning m!"Imports can be normalized:{newImports}"
