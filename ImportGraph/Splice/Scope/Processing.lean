/-
Copyright (c) 2026 Thomas R. Murrills. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas R. Murrills
-/
module

public import Lean.Data.OpenDecl
public import Lean.Environment

import Lean.Parser.Extension
import ImportGraph.Lean.Name
public import Lean.Elab.Command

open Lean

public section

namespace ImportGraph.Splice

open ImportGraph Splice Lean Elab Command

/-- An extension we can trust to always be present, whose active scopes reflect the result of
`open`s and are likely not altered separately from the rest of the scoped environment extensions by
some metaprogram. We use the parser extension. -/
@[inline] private def referenceScopedExt := Parser.parserExtension.ext

/-- The active scopes in scoped environment extensions, as determined by a reference
extension. Does not account for alterations to individual environment extensions that may
be performed by some metaprograms. -/
def Lean.Environment.activeScopes (env : Environment) : NameSet :=
  match referenceScopedExt.getState (asyncMode := .local) env |>.stateStack with
  | s :: _ => s.activeScopes
  | _ => {}

/-- The scopes that have been opened due to the given `OpenDecl`s and the current namespace.

This assumes that the namespace and `OpenDecl`s are coming from `namespace` and `open` commands as
usual, which activate scopes during elaboration. If not, this may not be accurate. -/
def Scope.impliedActiveScopes (currNamespace : Name) (openDecls : List OpenDecl) : NameSet :=
  -- Note that each `open` that adds `.simple` activates the corresponding scopes.
  let impliedScopes : NameSet := openDecls.foldl (init := {}) fun
    | acc, .simple ns _ => if ns.isAnonymous then acc else acc.insert ns
    | acc, _ => acc
  -- When `namespace ns` happened (or whatever sequence of `namespace`s), `addScopes` traversed all
  -- prefixes of `ns`. So we expect those to be there.
  -- Note that `addScope` in `elabNamespace` does not add to the open decls, so this is necessary.
  currNamespace.foldrPrefixes (init := impliedScopes) fun n acc =>
    if n.isAnonymous then acc else acc.insert n

/-- The active scopes in scoped env extensions that are *not* implied by the
given namespace and open decls (as determined by the active scopes in a reference environment
extension). These extra active scopes are typically produced by `open scoped`. -/
def Lean.Environment.extraActiveScopes
    (currNamespace : Name) (openDecls : List OpenDecl) (env : Environment) : NameSet := Id.run do
  return env.activeScopes \ Scope.impliedActiveScopes currNamespace openDecls

-- TODO: find other options (max memory?) and make this extensible?
/-- Gets the current options after erasing the options set by Lean itself, including `Elab.async`
(only) if it has not been changed by the user from the default of `true`. Note that this includes
the options set in the lakefile.

The result should be the same in both the language server and `lake build`. -/
def Lean.Options.toUserOptions (opts : Options) : Options :=
  let opts := opts.erase `internal.cmdlineSnapshots |>.erase `Elab.inServer
  if opts.get? `Elab.async matches some true then opts.erase `Elab.async else opts

section reset

/-- Pops all but the base scope from the `stateStack`. Note that the base scope may still be
modified. -/
def Lean.ScopedEnvExtension.popAllScopes {α β σ} (ext : ScopedEnvExtension α β σ)
    (env : Environment) : Environment :=
  ext.ext.modifyState (asyncMode := .local) env fun s =>
    { s with stateStack := s.stateStack.getLast?.toList }

@[inherit_doc Lean.ScopedEnvExtension.popAllScopes]
def popAllScopes {m : Type → Type} [Monad m] [MonadEnv m] [MonadLiftT (ST IO.RealWorld) m] :
    m Unit :=
  for ext in ← scopedEnvExtensionsRef.get do
    modifyEnv ext.popAllScopes

/-- Reconstructs the initial state stack of the given `ScopedEnvExtension` from the imported
entries. -/
def Lean.ScopedEnvExtension.reconstructInitialStateStack {α β σ}
    (ext : ScopedEnvExtension α β σ) (env : Environment) (opts : Options) :
    IO (ScopedEnvExtension.StateStack α β σ) :=
  ReaderT.run (m := IO) (r := { env, opts }) <|
    ext.ext.addImportedFn (ext.ext.toEnvExtension.getState env .sync).importedEntries

/-- Resets the full state of all scoped env extensions by rebuilding it from the imported entries.

Note that this means that scoped entries added earlier in the current file will no longer be
activatable.

If `clearNewEntries := true` (the default), resets all the to-be-exported entries as well. -/
def resetScopedEnvExtensions {m : Type → Type} [Monad m] [MonadEnv m]
    [MonadLiftT (ST IO.RealWorld) m] [MonadLiftT IO m]
    (opts : Options) (clearNewEntries := true) : m Unit := do
  for ext in ← scopedEnvExtensionsRef.get do
    let env ← getEnv
    let init ← ext.reconstructInitialStateStack env opts
    let init := if clearNewEntries then init else
      { init with newEntries := (ext.ext.getState env .sync).newEntries }
    modifyEnv fun env => ext.ext.setState env init

/-- Creates a base scope with the same header (usually `""`) and options as the base scope.
(Discards other fields of the base scope.) -/
def mkFreshBaseScope (scopes : List Scope) : Scope := Id.run do
  let some { header, opts .. } := scopes.getLast? | pure { header := "", opts := {} }
  { header, opts }

/-- A setting determining how far to reset `ScopedEnvExtension`s. -/
inductive Lean.ScopedEnvExtension.ResetTo where
| /-- Does not reset at all. -/
  current
| /-- Resets to the base scope in the `StateStack`, which may be polluted. -/
  baseScope
| /-- Reconstructs the initial state from the imported entries. If `clearNewEntries := false` (the
  default), preserves the new entries that will be exported at the end of the file. Otherwise,
  clears them. -/
  initialState (clearNewEntries := false)

/-- Resets the scopes. Preserves the options and header in the base scope. Note, however, that this
may include user-set options at the top of the file in addition to the lakefile options.

If `resetEnvExtensions : Option Bool` is `some false` (the default), resets scoped environment
extensions but does not clear the entries that will be exported at the end of the file. If
`some true`, these new entries are cleared as well. If `none`, all scopes are popped, but the base
scope is not reconstructed from imports and therefore may be polluted. -/
def resetScopes (resetScopedEnvExtensionsTo : Lean.ScopedEnvExtension.ResetTo := .initialState) :
    CommandElabM Unit := do
  modify fun s => { s with scopes := [mkFreshBaseScope s.scopes] }
  match resetScopedEnvExtensionsTo with
  | .current => pure ()
  | .baseScope => popAllScopes
  | .initialState clearNewEntries => resetScopedEnvExtensions (← getOptions) clearNewEntries

end reset
