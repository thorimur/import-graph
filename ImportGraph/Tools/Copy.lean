/-
Copyright (c) 2026 Thomas R. Murrills. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas R. Murrills, Claude Opus 4.8
-/
module

public meta import Lean.Widget.UserWidget

/-!
# A "copy to clipboard" infoview widget

`displayCopy` builds a `MessageData` widget that copies a fixed string to the
clipboard when clicked.

* If `display := some s`, the widget renders `s` as a clickable link.
* If `display := none`, it renders a small copy icon instead.

Either way, clicking copies `copyText`. A clipboard write requires a real user
gesture, which the `onClick` handler provides; the text to copy is shipped in
the props, so no round-trip is needed at click time.
-/

open Lean Server

namespace ImportGraph.Widget

meta section

/-! ## Props -/

/-- Props for the copy widget.

* `display`: if `some s`, render `s` as the label of a clickable link; if `none`,
  render just a copy icon.
* `copyText`: the string written to the clipboard on click.
* `hasIcon`: whether to show the copy/check codicon. Only consulted when `display`
  is `some`; with `display := none` the icon *is* the button, so it always shows.
  Note that with `hasIcon := false` there is no in-place copy→check feedback —
  only the hover `title` changes. -/
public structure CopyProps where
  display  : Option String := none
  copyText : String
  hasIcon  : Bool := true
  deriving Server.RpcEncodable

/-! ## The widget -/

/-- The copy-widget JS. Renders either a blue link (`display := some s`) or a
bare codicon button (`display := none`), styled like the infoview's own icon
buttons (`link pointer dim`). Clicking copies `copyText`; feedback is the copy
codicon flipping in place to a check for ~1s. -/
private def copyJs : String := "
  import * as React from 'react'
  const h = React.createElement

  export default function ({ display, copyText, hasIcon }) {
    const [copied, setCopied] = React.useState(false)
    const timer = React.useRef(null)

    const onClick = () => {
      // The click is a genuine user gesture, so the clipboard write is allowed.
      void navigator.clipboard.writeText(copyText)
      setCopied(true)
      clearTimeout(timer.current)
      timer.current = setTimeout(() => setCopied(false), 1000)
    }
    React.useEffect(() => () => clearTimeout(timer.current), [])

    const icon = 'codicon codicon-' + (copied ? 'check' : 'copy')
    const title = copied ? 'Copied!' : 'Copy to clipboard'

    // Icon-only: the codicon is the button.
    if (display == null)
      return h('a', { onClick, title, className: 'link pointer dim ' + icon })

    // Link text, optionally preceded by the codicon (flips copy → check in place).
    return h('a', { onClick, title, className: 'link pointer dim' },
      hasIcon && h('span', { className: 'font-codicon ' + icon }),
      hasIcon && ' ',
      display)
  }
"

@[widget_module]
public def Copy : Widget.Module where
  javascript := copyJs

/-! ## Producing a `MessageData` widget -/

public inductive DisplayText where
| text (s : String) (hasIcon := true)
| iconOnly
| copiedText (hasIcon := true)

instance : Coe String DisplayText where
  coe s := .text s

/-- Build a `MessageData` widget that copies `copyText` to the clipboard when
clicked.

* `display := some s` renders `s` as a clickable link.
* `display := none` renders a copy icon.

Use as e.g. `logInfo <| ← displayCopy "<thing>" (display := "click to copy")`. -/
public def displayCopy (copyText : String) (display : DisplayText := .iconOnly) :
    CoreM MessageData := do
  let (display, hasIcon) := match display with
    | .iconOnly => (none, true)
    | .copiedText hasIcon => (copyText, hasIcon)
    | .text s hasIcon => (s, hasIcon)
  let props : CopyProps := { display, copyText, hasIcon }
  return .ofWidget
    (← Widget.WidgetInstance.ofHash Copy.javascriptHash
        (Server.RpcEncodable.rpcEncode props))
    m!"[copy]{if let some display := display then m!" {display}" else m!""}"

end

run_meta do
  logInfo m!"{← displayCopy "foooo" "Copy foooo"}"


end ImportGraph.Widget
