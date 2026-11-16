/-
Copyright (c) 2026 Thomas R. Murrills. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas R. Murrills
-/
module

public meta import ImportGraph.Lean.Syntax
public meta import ImportGraph.Lean.Name
public meta import ImportGraph.Splice.Scope.Processing
public meta import ImportGraph.Splice.Scope.Capsule
public meta import Lean.Elab.BuiltinCommand
public import ImportGraph.Splice.Scope.Parser
public meta import Lean.Meta.Tactic.TryThis
public meta import Lean.Elab.Declaration

/-!
# Scope manipulation tools

This module provides utilities for fully capturing the effectful parts of the current scope
(namespaces, open declarations, options, etc.) and transporting it between modules. Specifically,
it provides `#scope`, which reifies the semantically-relevant parts of the current scope into
portable syntax capturing the current scope that may be moved between files.

This is not intended to capture `section` behavior, nor is it intended to be used for user-friendly
visibility into the current scope structure. The reified scope specification is primarily intended
to be easy to act on with metaprogramming automation. In this sense it is not trying to replace
`#where`.

## TODO

- `#scope? (<scope specification>)` for producing appropriate Lean commands to integrate the given
  full scope specification with the current scope
-/

/- Note: some declarations are marked `private` despite already living in private sections. These
should stay private or be carefully considered even if the API becomes public. -/

open ImportGraph Lean Meta Elab Command

public meta section

namespace ImportGraph.Splice

open ImportGraph.Splice Lean

/-- Capture a `Scope` into a `ScopeCapsule`. This additionally requires the `activeScopes`, which
come from the `Environment`. -/
def Lean.Elab.Command.Scope.capture (s : Scope) (activeScopes : NameSet) : ScopeCapsule :=
  { s with
    isExposed := s.attrs.any fun
      | `(Parser.Term.attrInstance| expose) => true
      | _ => false
    activeScopes
    userOpts := s.opts.toUserOptions
    vars := s.toVars
  }

/-- Sets the current scope to the scope given in `ScopeCapsule`, ignoring the current scope
entirely. -/
def ScopeCapsule.restore (capsule : ScopeCapsule)
    (resetScopedTo : ScopedEnvExtension.ResetTo := .initialState) : CommandElabM Unit := do
  resetScopes resetScopedTo


namespace Scope

section header

open Parser.Command


/-- Isolates the part of a `Scope` that contains `SectionHeader` information. -/
@[inline] def reifySectionHeader {m} [Monad m] [MonadQuotation m] :
    Scope → m (Option (TSyntax ``sectionHeader))
  | { isPublic, isMeta, isNoncomputable, attrs .. } => do
    -- Currently `attrs` holds at most `expose`, but we match for future-proofing.
    let exposeTk? := attrs.find? fun stx => match stx.raw with
      | `(Parser.Term.attrInstance| expose) => true
      | _ => false
    unless exposeTk?.isSome || isPublic || isMeta || isNoncomputable do
      return none
    -- This is a hack to exploit antiquotations. `$[$foo%$tk]?` yields `foo` iff `tk.isSome`.
    let r ← getRef
    letI toDummyOptional? (b : Bool) : Option Syntax :=
      if b then some r else none
    let pubTk    := toDummyOptional? isPublic
    let metaTk   := toDummyOptional? isMeta
    let ncTk     := toDummyOptional? isNoncomputable
    `(sectionHeader|
      $[@[expose%$exposeTk?]]? $[public%$pubTk]? $[noncomputable%$ncTk]? $[meta%$metaTk]?)

/-- Applies a `sectionHeader` syntax of the form `(@[expose])? (public)? (noncomputable)? (meta)?`
to the current scope, overwriting the values (rather than merging them). For instance, if `public`
is absent, the resulting scope now has `isPublic := false`, even if it was `true` before. -/
def unreifySectionHeader : TSyntax ``Parser.Command.sectionHeader → CommandElabM Unit
  | `(Parser.Command.sectionHeader|
      $[@[expose%$exposeTk]]? $[public%$pubTk]? $[noncomputable%$ncTk]? $[meta%$metaTk]?) => do
      let isPublic := pubTk.isSome
      let isMeta := metaTk.isSome
      -- `sectionHeader` parses `expose` directly, not as an `attrInstance`.
      let attrs : List (TSyntax ``Parser.Term.attrInstance) ←
        if let some exposeTk := exposeTk then
          pure [← withRef exposeTk `(Parser.Term.attrInstance| expose)] else pure []
      let isNoncomputable := ncTk.isSome
      modifyScope fun s => { s with isPublic, isMeta, isNoncomputable, attrs }
  | _ => throwUnsupportedSyntax

end header

section openDecls

/-- Convert `OpenDecl`s into reified `open @id₁ @id₂ ...` syntax. -/
def reifyOpenDecls {m} [Monad m] [MonadQuotation m] (openDecls : List OpenDecl) (dedup := true) :
    m (Option (TSyntax ``reifiedOpenStx)) := do
  if openDecls.isEmpty then return none
  /- The outermost elements of `openDecls` are the most recent, and should come last in an `open` -/
  let revOpenDecls := openDecls.reverse
  /- Lean may duplicate open declarations occasionally due to leanprover/lean4#13353. This function
  deduplicates exactly-duplicated `OpenDecl`s by removing the later occurrences.

  The innermost elements of `openDecls` actually affect name resolution first, so we want to keep
  the first instances of duplicate elements in `revOpenDecls`, not in `openDecls`. -/
  -- TODO: consider a better approach than `eraseDups` if possible
  let revOpenDecls := if dedup then revOpenDecls.eraseDups else revOpenDecls
  -- Note that the last element of `openDecls` becomes the first element of `reifiedOpens`,
  -- since the outermost `OpenDecl` is the most recent.
  let reifiedOpens ← revOpenDecls.toArray.mapM fun
    | .explicit id declName =>
      `(reifiedOpenDecl| ($(mkIdent id) → @$(mkIdent declName)))
    | .simple ns except =>
      if except.isEmpty then `(reifiedOpenDecl| @$(mkIdent ns)) else
        let except := except.toArray.map mkIdent
        `(reifiedOpenDecl| (@$(mkIdent ns) hiding $except*))
  `(reifiedOpenStx| open $reifiedOpens*)

/-- Activates scopes associated with an `OpenDecl` as `open` would when creating that `OpenDecl`. -/
def _root_.Lean.OpenDecl.activate {m : Type → Type}
    [Monad m] [MonadEnv m] [MonadLiftT (ST IO.RealWorld) m] :
    OpenDecl → m Unit
  | .simple ns _  => activateScoped ns
  | .explicit _ _ => pure () -- `open` never activates scopes when creating these

-- TODO: it's possible we should register namespaces if they don't exist.
/-- Turns reified syntax for a single `open` such as `@foo.bar` into an `OpenDecl`, activating
scopes as `open` would if `activateScopes := true` (the default). -/
def unreifyOpenDecl (openDecl : TSyntax ``reifiedOpenDecl) (activateScopes := true) :
    CommandElabM OpenDecl :=
  match openDecl with
  | `(reifiedOpenDecl| @$id) => do
    if activateScopes then activateScoped id.getId
    return .simple id.getId []
  | `(reifiedOpenDecl| (@$id hiding $hidden*)) => do
    if activateScopes then activateScoped id.getId
    return .simple id.getId <| (hidden.map (·.getId)).toList
  | `(reifiedOpenDecl| ($id → @$decl)) =>
    -- `open` never activates scopes in these cases. See `elabOpenDecl`.
    return .explicit id.getId decl.getId
  | _ => throwUnsupportedSyntax

/-- Turns reified syntax for `open @id ...` such as `open @foo.bar ...` into `OpenDecl`s
(activating scopes as appropriate) and modifies the current scope to use exactly those open
declarations (erasing whatever open declarations were present before). Note that the resulting
`openDecls` do not depend on the original `openDecls` or original scope in any way. -/
def unreifyOpenDecls (openDeclsStx : TSyntaxArray ``reifiedOpenDecl) : CommandElabM Unit := do
  let openDecls ← openDeclsStx.foldlM (init := []) fun openDecls openDeclStx =>
    return (← unreifyOpenDecl openDeclStx) :: openDecls
  modifyScope fun s => { s with openDecls }

section openScoped

/-- `current.minus without` yields a `NameSet` containing the elements of `current` not present in
`without`. -/
@[inline] private def _root_.Lean.NameSet.minus (current without : NameSet) : NameSet :=
  if without.isEmpty then current else current.filter (!without.contains ·)

/-- An extension we can trust to always be present, whose active scopes reflect the result of
`open`s and are likely not altered separately from the rest of the scoped environment extensions by
some metaprogram. We use the parser extension. -/
@[inline] private def referenceScopedExt := Parser.parserExtension.ext

/-- The active scopes in scoped environment extensions, as determined by a reference
extension. Does not account for alterations to individual environment extensions that may
be performed by some metaprograms. -/
def _root_.Lean.Environment.activeScopes (env : Environment) : NameSet :=
  match referenceScopedExt.getState (asyncMode := .local) env |>.stateStack with
  | s :: _ => s.activeScopes
  | _ => {}

/-- The active scopes in scoped env extensions that are *not* implied by the
given namespace and open decls (as determined by the active scopes in a reference environment
extension). These extra active scopes are typically produced by `open scoped`. See also
`Lean.Elab.Command.extraScoped : CommandElabM NameSet`. -/
protected def _root_.Lean.Environment.extraActiveScopes (env : Environment)
    (currNamespace : Name) (openDecls : List OpenDecl) : NameSet := Id.run do
  -- Note that each `open` that adds `.simple` activates the corresponding scopes.
  let impliedScopes : NameSet := openDecls.foldl (init := {}) fun
    | acc, .simple ns _ => if ns.isAnonymous then acc else acc.insert ns
    | acc, _ => acc
  -- When `namespace ns` happened (or whatever sequence of `namespace`s), `addScopes` traversed all
  -- prefixes of `ns`. So we expect those to be there.
  -- Note that `addScope` in `elabNamespace` does not add to the open decls, so this is necessary.
  let impliedScopes := currNamespace.foldrPrefixes (init := impliedScopes) fun n acc =>
    if n.isAnonymous then acc else acc.insert n
  return env.activeScopes.minus impliedScopes

/-- The active scopes in scoped env extensions that are *not* implied by the current namespace and
open decls (as determined by the active scopes in a reference environment extension). These extra
active scopes are typically produced by `open scoped`. -/
def _root_.Lean.Elab.Command.extraActiveScopes : CommandElabM NameSet :=
  return (← getEnv).extraActiveScopes (← getCurrNamespace) (← getOpenDecls)

/-- Converts the extra active scopes into reified `open scoped` syntax. -/
def reifyExtraOpenScopes : CommandElabM (Option (TSyntax ``reifiedOpenScopedStx)) := do
  let extra ← extraActiveScopes
  if extra.isEmpty then return none
  let extraScoped ← extra.toArray.mapM fun n => `(reifiedSimpleOpenIdent| @$(mkIdent n))
  `(reifiedOpenScopedStx| open scoped $extraScoped*)

/-- Directly activates the scopes in reified `open scoped @id₁ @id₂ ...` syntax. Does *not* reset
the scopes first. -/
def unreifyOpenScoped : TSyntax ``reifiedOpenScopedStx → CommandElabM Unit
  | `(reifiedOpenScopedStx| open scoped $[@$openScopedDecls:ident]*) => do
    for openScoped in openScopedDecls do
      activateScoped openScoped.getId.eraseMacroScopes
  | _ => throwUnsupportedSyntax

end openScoped

end openDecls

section setOption

/-
Note: options set in the lakefile are commingled in the base scope with options set in the
module, so it is not easy to split them up. Though, including the lakefile options is arguably
better for transportation between libraries, so we only exclude internal or editor options.

TODO: make ignored options extensible.
-/

/-- Gets the current options after erasing the options set by Lean itself, including `Elab.async`
(only) if it has not been changed by the user from the default of `true`. Note that this includes
the options set in the lakefile.

The result should be the same in both the language server and `lake build`. -/
def getUserOptions : CommandElabM Options := do
  let opts := (← getOptions).erase `internal.cmdlineSnapshots |>.erase `Elab.inServer
  if opts.get? `Elab.async matches some true then return opts.erase `Elab.async else return opts

/-- Reifies the given `Options` into `set_options ...` syntax if there are any. -/
def reifySetOptions? (opts : Options) : CommandElabM (Option (TSyntax ``reifiedSetOptionsStx)) := do
  let mut kvs := #[]
  for (key, val) in opts do
    let some val := val.toSetOptionValueSyntax? | continue
    kvs := kvs.push <|← `(reifiedOptionKeyValue| $(mkIdent key) $val)
  if kvs.isEmpty then pure none else some <$> `(reifiedSetOptionsStx| set_options $kvs,*)

/-- Overwrites the current options with those given in the `set_options ...` syntax. Elaborates the
option values normally, populating the infotrees for hovers. -/
def unreifySetOptions : TSyntax ``reifiedSetOptionsStx → CommandElabM Unit
  | `(reifiedSetOptionsStx| set_options $keyVals:reifiedOptionKeyValue,*) => do
  for keyVal in keyVals.getElems do
    let `(reifiedOptionKeyValue| $id $val) := keyVal | throwUnsupportedSyntax
    -- Note that `elabSetOption` adds to the current options.
    let (opts, _) ← Elab.elabSetOption id val
    modifyScope fun s => { s with opts }
  | _ => throwUnsupportedSyntax

end setOption

section universes

/-- Reifies the current level names into `universe ...` syntax if there are any. -/
def reifyLevelNames? : CommandElabM (Option (TSyntax ``Parser.Command.universe)) := do
  let levelNames ← getLevelNames
  if levelNames.isEmpty then pure none else
    some <$> `(Parser.Command.universe| universe $(levelNames.toArray.reverse.map mkIdent)*)

end universes

section namespaces

/-- Reifies the current namespace into `namespace ...` syntax if not in the root namespace. -/
def reifyCurrNamespace? : CommandElabM (Option (TSyntax ``Parser.Command.namespace)) := do
  let ns ← getCurrNamespace
  if ns.isAnonymous then pure none else `(Parser.Command.namespace| namespace $(mkIdent ns))

end namespaces

section variables

/-- Reifies current section variables into `variable ...` syntax if there are any. -/
def reifyVariables? : CommandElabM (Option (TSyntax ``Parser.Command.variable)) := do
  let { varDecls .. } ← getScope
  if varDecls.isEmpty then return none
  let varDecls := varDecls.map (⟨·.raw.unsetTrailing⟩)
  `(Parser.Command.variable| variable $varDecls*)

/-- Reifies current `include`d section variables into `include ...` syntax if there are any. -/
def reifyInclude? : CommandElabM (Option (TSyntax ``Parser.Command.include)) := do
  let { includedVars .. } ← getScope
  if includedVars.isEmpty then return none
  `(Parser.Command.include| include $(includedVars.toArray.map (mkIdent ·.eraseMacroScopes))*)

/-- Reifies current `omit`ted section variables into `omit ...` syntax if there are any. -/
def reifyOmit? : CommandElabM (Option (TSyntax ``Parser.Command.omit)) := do
  let { omittedVars, varUIds, varDecls .. } ← getScope
  if omittedVars.isEmpty then return none
  let mut omittedIdentOrBinder : TSyntaxArray [`ident, `Lean.Parser.Term.instBinder] := #[]
  for var in omittedVars do
    for uid in varUIds, stx in varDecls do
      if uid = var then
        if stx.raw.isOfKind ``Parser.Term.instBinder then
          omittedIdentOrBinder := omittedIdentOrBinder.push ⟨stx.raw.unsetTrailing⟩
        else
          omittedIdentOrBinder := omittedIdentOrBinder.push (mkIdent uid.eraseMacroScopes)
        break
  `(Parser.Command.omit| omit $(omittedIdentOrBinder)*)

/-- Elaborates the `variable`, `include`, and `omit` syntax in the reified variable syntax. Does
*not* reset the scopes first. -/
def unreifyVariables : TSyntax ``reifiedVariableStx → CommandElabM Unit
  | `(reifiedVariableStx| $vars $[$included]? $[$omitted]?) => do
      elabVariable vars
      -- Note: we assume these are disjoint, and order of elaboration is irrelevant.
      included.forM (elabInclude ·)
      omitted.forM (elabOmit ·)
  | _ => throwUnsupportedSyntax

end variables



/-- Resets the scopes, then creates the scope described in the syntactic scope specification. By
default, this resets scoped environment extensions by reconstructing their initial state from
imported entries, but does *not* clear the exported entries. See `ScopedEnvExtension.ResetTo` for
other possibilities. -/
def unreifyScope (stx : TSyntax ``scopeStx)
    (resetEnvExtensionsTo : ScopedEnvExtension.ResetTo := .initialState) :
    CommandElabM Unit :=
  match stx with
  | `(scopeStx| $[$sectionHeader section]?
      $[$universeStx:universe]?
      $[$namespaceStx:namespace]?
      $[open $openDecls:reifiedOpenDecl*]?
      $[$openScoped:reifiedOpenScopedStx]?
      $[$setOptions:reifiedSetOptionsStx]?
      $[$vars]?) => do
    resetScopes resetEnvExtensionsTo
    sectionHeader.forM unreifySectionHeader
    universeStx.forM (elabUniverse ·)
    namespaceStx.forM (elabNamespace ·)
    openDecls.forM unreifyOpenDecls
    openScoped.forM unreifyOpenScoped
    setOptions.forM unreifySetOptions
    vars.forM unreifyVariables
  | _ => throwUnsupportedSyntax

/-- Reifies aspects of the current scope into a `scopeStx` scope specification. See `scopeStx`. -/
def reifyScope : CommandElabM (TSyntax ``scopeStx) := do
  let sectionHeader ← reifySectionHeader (← getScope)
  let universes ← reifyLevelNames?
  let namespaceStx ← reifyCurrNamespace?
  let opens ← reifyOpenDecls (← getOpenDecls)
  let extraOpenScoped ← reifyExtraOpenScopes
  let setOptions ← reifySetOptions? (← getUserOptions)
  let variables ← (← reifyVariables?).mapM fun vars => do
    `(reifiedVariableStx| $vars $(← reifyInclude?)? $(← reifyOmit?)?)
  `(scopeStx| $[$sectionHeader section]?
    $[$universes]?
    $[$namespaceStx]?
    $[$opens]?
    $[$extraOpenScoped]?
    $[$setOptions]?
    $[$variables]?)
    /- TODO: technically the variable parsing could change if a scope is opened earlier. This is
    probably important...it'll mean (1) detecting if any variable syntax is scoped (2) writing a
    more detailed parser for `scopeStx` that opens the named scopes! -/

    -- We also could account for `open (scoped) ... in variable` but it would have to be ad-hoc.

def toRawSurfaceSyntax : TSyntax ``scopeStx → CommandElabM (TSyntaxArray `command)
  | `(scopeStx| $[$sectionHeader section]?
      $[$universes]?
      $[$namespaceStx]?
      $[$opens]?
      $[$extraOpenScoped]?
      $[$setOptions]?
      $[$variables]?) => do
    let s ← get
    resetScopes
    let mut cmds := #[]
    if let some header := sectionHeader then
      let cmd ← `(command| $header:sectionHeader section)
      elabCommand cmd
      cmds := cmds.push cmd
    if let some us := universes then
      let cmd ← `(command| $us:universe)
      elabCommand cmd
      cmds := cmds.push cmd
    if let some ns := namespaceStx then
      let cmd ← `(command| $ns:namespace)
      elabCommand cmd
      cmds := cmds.push cmd
    if let some us := universes then
      let cmd ← `(command| $us:universe)
      elabCommand cmd
      cmds := cmds.push cmd
    if let some opens := opens then
      let `(reifiedOpenStx| open $decls:reifiedOpenDecl*) := opens | throwUnsupportedSyntax
      for decl in decls do
        elabOpenDecl


    return cmds
  | _ => throwUnsupportedSyntax

public section

/--
`#scope` reifies the current scope into syntax so that it can be transported into another file,
e.g. along with a following declaration that depends on this scope. (No use of `in` is needed.)

Copy-pasting `#scope <scope specification>` into another file, then changing `#scope` to `#scope!`,
will have the effect of resetting the scope to the given scope specification at that point. This
allows quickly jumping back and forth between different states.

`#scope` will log a try-this suggestion suggesting reified syntax that matches the current scope,
or else remain silent. If the reified scope syntax no longer matches the current scope, `#scope`
suggests an updated replacement.

NOTE: `#scope` is currently in development. Soon, `#scope?` will provide more
features for suggesting new ordinary scope syntax to merge the two scopes.
-/
syntax "#scope" (ppLine scopeStx)? : command

elab_rules : command
| `(#scope%$tk) => do
  let stx ← `(command| #scope%$tk $(← reifyScope))
  -- Note: we use `getRef` to expand the range on which the code action works.
  liftCoreM <| Tactic.TryThis.addSuggestion (← getRef) stx
| `(#scope%$tk $scopeStx) => do
  let scopeStx' ← withRef scopeStx reifyScope
  unless scopeStx.raw.structEq scopeStx' do
    let stx ← `(command| #scope%$tk $scopeStx')
    liftCoreM <| Meta.Tactic.TryThis.addSuggestion (← getRef) (origSpan? := (← getRef)) stx
      (diffGranularity := .word)

/--
`#scope!` resets the current scope to the scope specification given afterwards. This includes
resetting all scoped environment extensions to their initial states, as constructed at the top of
the file.

`#scope` will suggest modifying the following scope specification to the current scope.

Note that while this does manage to preserve the exported entries for downstream files, any new
scoped entries created in this file will not be activatable after `#scope!`, even though they will
still be accessible in downstream files (if not local).
-/
syntax "#scope!" (&" new" <|> (ppLine scopeStx))? : command

elab_rules : command
| `(#scope!) => do
  let h ← liftCoreM <| MessageData.hint "You can also reset the scope using"
    #[← `(command| #scope! new)]
  logWarning m!"Expected a scope specification generated by `#scope`.{h}"
| `(#scope! new) => resetScopes
| `(#scope! $scopeStx:scopeStx) => unreifyScope scopeStx
