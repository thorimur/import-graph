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

/-- Props for the `Collapsible` widget. -/
public structure CollapsibleProps where
  /-- The always-visible header `MessageData`. -/
  summary       : WithRpcRef MessageData
  /-- The hideable body revealed when the dropdown is expanded. -/
  body          : WithRpcRef MessageData
  /-- Whether the dropdown starts expanded. -/
  initiallyOpen : Bool := false
deriving Server.RpcEncodable

/-- The dropdown widget: a `<details>` component with `MessageData` header and body.

Note: The body is mounted lazily. Since an ordinary closed `<details>` component would still mount
the body even if it were closed, we track whether the `<details>` component has ever been opened
manually and mount it on first open. It then stays mounted. -/
@[widget_module]
public def Collapsible : Widget.Module where javascript :=
r###"
import * as React from 'react'
import { InteractiveMessageData } from '@leanprover/infoview'
const h = React.createElement

export default function (props) {
  const { summary, body, initiallyOpen } = props
  const [open, setOpen] = React.useState(!!initiallyOpen)
  const [everOpened, setEverOpened] = React.useState(!!initiallyOpen)
  const onClick = e => {
    // Clicks inside React portals (e.g. pinned tooltips) bubble here through
    // the React tree, but their DOM nodes live outside the summary.
    if (!(e.target instanceof Node)) return
    if (!e.currentTarget.contains(e.target)) return
    e.preventDefault()
    setEverOpened(true)
    setOpen(o => !o)
  }
  return h('details', { open },
    h('summary',
      { style: { cursor: 'pointer', userSelect: 'none' }, onClick },
      h(InteractiveMessageData, { msg: summary })),
    everOpened && h('div',
      { style: { marginLeft: '1em', marginTop: '0.25em' } },
      h(InteractiveMessageData, { msg: body })))
}
"###

/-- Build a `MessageData` that renders as a collapsible dropdown: `summary` is
the header and `body` is the `MessageData` revealed when expanded. For example:
```
⯈ This is the header!
```
may be clicked to expand to
```
▼ This is the header!
  And this is the body.
```

`initiallyOpen` controls whether the dropdown starts expanded (default `false`). -/
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

end

end ImportGraph.Widget
