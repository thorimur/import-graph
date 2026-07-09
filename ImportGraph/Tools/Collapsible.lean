/-
Copyright (c) 2026 Thomas R. Murrills. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas R. Murrills
-/
module

public meta import Lean.Widget.UserWidget

/-!
# A collapsible `MessageData` dropdown widget

`ImportGraph.Widget.collapsible summary body` produces a `MessageData` that
renders in the infoview as a native `<details>` disclosure: `summary` is the
always-visible header, and `body` — itself arbitrary `MessageData` — is shown
only when expanded.

Unlike `MessageData.trace`, this carries no trace styling or `cls` tag; it is a
plain dropdown whose header you control.

The collapsed `body` is handed to the widget as a `WithRpcRef MessageData` prop
(the same by-reference mechanism core uses for lazy trace children) and rendered
client-side with `InteractiveMessageData`, so nested expressions, goals, and
even further widgets inside `body` remain fully interactive.
-/

open Lean Server

namespace ImportGraph.Widget

meta section

/-! ## Props -/

/-- Props for the `Collapsible` widget.

* `summary`: the always-visible header `MessageData`, passed by RPC reference and
  rendered interactively client-side.
* `body`: the `MessageData` revealed when expanded, passed by RPC reference and
  rendered interactively client-side.
* `initiallyOpen`: whether the dropdown starts expanded. -/
public structure CollapsibleProps where
  summary       : WithRpcRef MessageData
  body          : WithRpcRef MessageData
  initiallyOpen : Bool := false
  deriving Server.RpcEncodable

/-! ## The widget -/

/-- The dropdown JS: a native `<details>` whose body renders the embedded
`MessageData` reference via `InteractiveMessageData`.

The body is mounted lazily: its `InteractiveMessageData` (and hence the
`msgToInteractive` RPC call that renders it) is not created until the dropdown is
first opened. A closed `<details>` still *mounts* unconditional children — it
only hides them visually — so we instead gate the body on an `everOpened` flag,
mirroring the infoview's own `Details` component. Once opened, the body stays
mounted so its resolved state survives subsequent collapse/expand without
re-fetching. The summary is always rendered. -/
private def collapsibleJs : String := "
  import * as React from 'react'
  import { InteractiveMessageData } from '@leanprover/infoview'
  const h = React.createElement

  export default function (props) {
    const { summary, body, initiallyOpen } = props
    const [open, setOpen] = React.useState(!!initiallyOpen)
    const everOpened = React.useRef(!!initiallyOpen)
    if (open) everOpened.current = true
    return h('details', { open },
      h('summary',
        { style: { cursor: 'pointer', userSelect: 'none' },
          onClick: e => { e.preventDefault(); setOpen(o => !o) } },
        h(InteractiveMessageData, { msg: summary })),
      everOpened.current && h('div',
        { style: { marginLeft: '1em', marginTop: '0.25em' } },
        h(InteractiveMessageData, { msg: body })))
  }
"

@[widget_module]
public def Collapsible : Widget.Module where
  javascript := collapsibleJs

/-! ## Producing the `MessageData` -/

/-- Build a `MessageData` that renders as a collapsible dropdown: `summary` is
the clickable header and `body` is the `MessageData` revealed when expanded.

`initiallyOpen` controls whether it starts expanded (default `false`).

The second argument to `.ofWidget` is the non-widget fallback approximation,
which preserves `body` (under an indented `summary` header) for environments
that cannot display user widgets. -/
public def collapsible {m : Type → Type} [Monad m] [MonadLiftT CoreM m]
    [AddMessageContext m] (summary body : MessageData)
    (initiallyOpen : Bool := false) : m MessageData := do
  let summary ← addMessageContext summary
  let body ← addMessageContext body
  let props : CollapsibleProps := {
    summary := ← (WithRpcRef.mk summary : CoreM _)
    body := ← (WithRpcRef.mk body : CoreM _ )
    initiallyOpen }
  return .ofWidget (← Widget.WidgetInstance.ofHash Collapsible.javascriptHash
          (Server.RpcEncodable.rpcEncode props))
          m!"▼ {summary}{indentD body}"

/-- Like `collapsible`, but `body` is produced lazily by a `MetaM` action that is
not run until the message is *rendered* — which, thanks to the widget's lazy
mount, happens only when the dropdown is first opened. So neither body
construction nor its rendering occurs unless the user actually expands it. (Plain
`collapsible` defers only *rendering*; its `body` value is constructed eagerly by
the caller before the call.)

This uses `MessageData.ofLazyM`, the mechanism Lean itself uses pervasively for
lazy error/trace messages (e.g. `Meta.Check`, `Elab.Tactic.Decide`). At render
time the action is run via `PPContext.runMetaM` against the `PPContext` captured
here by `collapsible`'s `addMessageContext`, so it sees the environment, local
context, and metavariables — exactly the same context a normal `logInfo` would
print under. `MetaM` is the natural choice (it is the monad pretty-printing runs
in, and `CoreM` actions lift into it) without pinning to `CoreM`.

`es` lists the expressions appearing in the message; as in `ofLazyM` they set the
`hasSyntheticSorry` flag so messages for terms with synthetic sorries can be
filtered.

Write `body` as a `do` block so the construction sits inside the action and is
genuinely deferred (a bare `pure msg` would build `msg` at the call site). -/
public def collapsibleLazy {m : Type → Type} [Monad m] [MonadLiftT CoreM m]
    [AddMessageContext m] (summary : MessageData) (body : MetaM MessageData)
    (es : Array Expr := #[]) (initiallyOpen : Bool := false) : m MessageData :=
  collapsible summary (.ofLazyM body es) initiallyOpen

end

end ImportGraph.Widget
