/-
Copyright (c) 2026 Thomas R. Murrills. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas R. Murrills
-/
module

public meta import Lean.Elab.BuiltinCommand

public section

open Lean

namespace ImportGraph.Splice.Scope

/-!
# Reified scope syntax

This module defines syntax that enables a serializable, contextless record of the current scope,
suitable for transport between Lean modules.

This is only intended to capture the "semantic" scope, and as such is not intended to capture
`section` behavior, nor is it intended to be used for user-friendly visibility into the current
scope structure. The reified scope syntax is primarily intended to be easy to act on with
automation.

## Implementation notes

The "inlinable" parsers here exist to enable syntax quotations, which help with
constructing and processing these later.

The parsers without docstrings are intentionally without docstrings in order to keep hovers uniform
and uncluttered.
-/

section openDecls

/-- `(from → @fullyResolvedName)` in reified `open` syntax unambiguously represents the result of
ordinary Lean syntax of the form `open ns renaming from → to, ...` and `open ns (id₁ id₂ ...)`.
Internally, both of these produce the same kind of effect: they record mapping(s) from an
unresolved identifier to a fully resolved name. (`ns` is not directly recorded in this mapping.) -/
syntax reifiedExplicitOpenStx := ident " → " &"@" noWs ident

syntax reifiedSimpleOpenIdent := &"@" noWs ident

syntax reifiedSimpleOpenHidingStx := &"@" noWs ident " hiding " ident*

syntax reifiedOpenDecl := ppSpace colGt
  (reifiedSimpleOpenIdent <|> ("(" reifiedSimpleOpenHidingStx <|> reifiedExplicitOpenStx ")"))

/-- Renders the result of `open` by prefixing identifiers with `@` to indicate that this syntax
only renders fully-resolved namespaces and identifiers. (Surrounded by `()` when `hiding` is
present.)

Uses `(... → @...)` to render the mappings produced by ordinary Lean syntax such as
`open ns renaming from → to, ...` and `open ns (id₁ id₂ ...)`, which internally both produce the
same sort of mapping(s) from an unresolved identifier to a fully-resolved name. -/
syntax reifiedOpenStx := withPosition(
  atomic("open" notFollowedBy("scoped")) ppIndent(reifiedOpenDecl*))

/-- Renders the open scopes that are not accounted for by generic `open`s. Prefixes identifiers
with `@` to show the fully-resolved name. -/
syntax reifiedOpenScopedStx := withPosition("open " "scoped"
  ppIndent((ppSpace colGt reifiedSimpleOpenIdent)*))

end openDecls

-- Parser of convenience, since we handle these together.
-- TODO: technically this may be influenced by open scopes.
-- It needs to incorporate that in the parser.
syntax reifiedVariableStx := Parser.Command.variable
  (ppLine Parser.Command.include)?
  (ppLine Parser.Command.omit)?

section setOptions

syntax reifiedOptionKeyValue := ppSpace colGt ident ppSpace optionValue
/-- `set_options key₁ val₁, key₂ val₂, ...` renders the options set in a single line. -/
syntax reifiedSetOptionsStx := withPosition("set_options " ppIndent(reifiedOptionKeyValue,*))

end setOptions

/--
A scope specification of the form
```
((@[expose])? (public)? (noncomputable)? (meta)? scope)?
  (universe ...)?
  (namespace ...)?
  (open @id₁ @id₂ ...)?
  (open scoped @id₁ @id₂ ...)?
  (set_options key₁ val₁, key₂ val₂ ...)?
  (variable ...)?
  (include ...)?
  (omit ...)?
```
Notice the differences from typical scope-related syntax, especially in the usage of `@` in
identifiers for `open` and the use of `set_options` instead of `set_option`.

Note also that this is intended to reify semantic and instantaneous aspects of a given scope for
transportation purposes, and is *not* intended to reify the entire scope stack. This means that
the effects of `section`s and local scopes are not accounted for here.
-/
syntax scopeStx := (Parser.Command.sectionHeader "section")?
  (ppLine colGt Parser.Command.universe)?
  (ppLine colGt Parser.Command.namespace)?
  atomic((ppLine colGt reifiedOpenStx)?)
  (ppLine colGt reifiedOpenScopedStx)?
  (ppLine colGt reifiedSetOptionsStx)?
  (ppLine colGt reifiedVariableStx)?
