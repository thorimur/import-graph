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

open ImportGraph Lean Elab Command

/-- Normalizes the imports of the current file. This ensures that the same modules are available at the same visibilities and phases. It does not take into account the declarations or usages of those modules in the current file; for that, see `#min_imports`. -/
elab tk:"#norm_imports" : command => do
  unless (← getEnv).header.isModule do
    -- TODO: handle non-modules. Modifying the final `Import` array might be sufficient;
    -- all shake internals likely still work.
    throwError "`#norm_imports` currently only works in the module system."
  let transDeps := (← getEnv).mkTransDeps
  let currentTransNeeds := (← getEnv).currentTransNeeds transDeps
  let reducedImps := currentTransNeeds.reduce transDeps |>.toRawImports (← getEnv)
  -- TODO: remove private imports that are transitively (not just directly) implied by `import all`.
  let reducedImps := Lake.Shake.Import.includeAll (← getEnv).header.imports reducedImps
  -- TODO: allow the user to filter out the `#norm_imports` import?
  let (header, _, log) ← parseCurrentHeader
  if log.hasErrors then
    -- This should be impossible.
    throwError m!"The current imports failed to parse. Errors:\n\
      {m!"\n".joinSep <| log.toList.map (·.data)}"
  let impsWithRefs := headerToImportRefsWithWhitespace header
  let some (msg, errs) ← liftCoreM <| Import.mkImportSuggestionMessage tk reducedImps impsWithRefs
    | logInfo m!"Imports are normalized."
  if errs.isEmpty then
    -- Note: the widget nature of `diffGranularity := .word` effectively gives us a newline
    -- before `{newImports}`.
    logWarning m!"Imports can be normalized:{msg}"
  else
    logWarning m!"Imports can be normalized, but some comments could not be carried over. \
      Please review the comment that will be inserted after the imports.\n{msg}"
