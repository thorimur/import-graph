/-
Copyright (c) 2026 Thomas Murrills. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Murrills, Claude Opus 4.8
-/
module

public meta import Lean.Widget.UserWidget
public meta import Lake.CLI.Shake
public meta import ImportGraph.Shake.Basic
import all Lake.CLI.Shake
import all ImportGraph.Shake.Basic

/-!
# Infoview widgets for `Bitset` and `Needs`

A small grid widget that visualizes a `Bitset` (on/off squares) or a `Needs`
(square-with-inset-disc icons encoding the four `NeedsKind` bits per index).

The same JS module handles both flavors; the Lean side picks one via the
`kind` field of the props.

For `Needs` cells, the four regions of the icon are:

* outer top half     ↔ `metaPub`   (public, meta phase)     — light blue when on
* outer bottom half  ↔ `pub`       (public, non-meta)       — black when on
* inner top half     ↔ `metaPriv`  (private, meta phase)    — light blue when on
* inner bottom half  ↔ `priv`      (private, non-meta)      — black when on

"Above the equator" = meta; "outside the disc" = public.
-/

open Lean Server Lake Shake

namespace ImportGraph.Widget

meta section

/-! ## Cell types and props -/

/-- A cell in a bitset grid: on or off, with a tooltip name and optional
"needed by" string. The rendered tooltip is `"{name}"`, or `"{name} > {neededBy}"`
when `neededBy` is supplied. -/
public structure BitsetCell where
  on       : Bool
  name     : String
  neededBy : Option String := none
  deriving Server.RpcEncodable

/-- A cell in a `Needs` grid. Each cell carries four independent bits — one per
`NeedsKind` — visualized as four regions of a square-with-inset-disc icon.

The rendered tooltip is `"{name}"`, or `"{name} > {neededBy}"` when `neededBy`
is supplied. -/
public structure NeedsCell where
  metaPub  : Bool
  pub      : Bool
  metaPriv : Bool
  priv     : Bool
  name     : String
  neededBy : Option String := none
  deriving Server.RpcEncodable

public structure BitsetGridRow where
  /-- Optional row label, shown to the left if any row in the grid has one. -/
  name  : Option String := none
  cells : Array BitsetCell
  deriving Server.RpcEncodable

public structure NeedsGridRow where
  name  : Option String := none
  cells : Array NeedsCell
  deriving Server.RpcEncodable

public structure BitsetGridProps where
  kind        : String := "bitset"
  /-- Optional column labels, drawn rotated above the grid. -/
  columnNames : Option (Array String) := none
  rows        : Array BitsetGridRow
  deriving Server.RpcEncodable

public structure NeedsGridProps where
  kind        : String := "needs"
  columnNames : Option (Array String) := none
  rows        : Array NeedsGridRow
  deriving Server.RpcEncodable

/-! ## The widget -/

/-- The grid widget JS, shared between `Bitset` and `Needs` displays.
Dispatches on `props.kind`. -/
private def gridJs : String := "
  import * as React from 'react'
  const META = '#7FBEEB'
  const NONMETA = '#000000'
  const OFF = '#ffffff'
  const STROKE = '#888888'
  const h = React.createElement

  function tooltipOf(cell) {
    return cell.neededBy ? cell.name + ' > ' + cell.neededBy : cell.name
  }

  function bitsetCell(cell) {
    return h('div', {
      style: {
        width: '20px', height: '20px',
        background: cell.on ? NONMETA : OFF,
        border: '1px solid ' + STROKE,
        boxSizing: 'border-box',
        borderRadius: '2px',
      }
    })
  }

  function needsCell(cell) {
    const outerTop = cell.metaPub  ? META    : OFF
    const outerBot = cell.pub      ? NONMETA : OFF
    const innerTop = cell.metaPriv ? META    : OFF
    const innerBot = cell.priv     ? NONMETA : OFF
    return h('svg',
      { viewBox: '0 0 20 20', width: 20, height: 20, style: { display: 'block' } },
      h('path', { d: 'M 0 0 H 20 V 10 H 16 A 6 6 0 0 0 4 10 H 0 Z', fill: outerTop }),
      h('path', { d: 'M 0 20 H 20 V 10 H 16 A 6 6 0 0 1 4 10 H 0 Z', fill: outerBot }),
      h('path', { d: 'M 4 10 A 6 6 0 0 1 16 10 Z', fill: innerTop }),
      h('path', { d: 'M 4 10 A 6 6 0 0 0 16 10 Z', fill: innerBot }),
      h('rect',   { x: 0.5, y: 0.5, width: 19, height: 19, fill: 'none',
                    stroke: STROKE, strokeWidth: 1 }),
      h('circle', { cx: 10, cy: 10, r: 6, fill: 'none',
                    stroke: STROKE, strokeWidth: 0.5 }),
    )
  }

  function CellWithTooltip({ tooltip, children }) {
    const [hover, setHover] = React.useState(false)
    return h('div', {
      style: { position: 'relative', display: 'inline-block', lineHeight: 0 },
      onMouseEnter: () => setHover(true),
      onMouseLeave: () => setHover(false),
    },
      children,
      hover && h('div', {
        style: {
          position: 'absolute',
          bottom: '100%',
          left: '50%',
          transform: 'translateX(-50%)',
          marginBottom: '2px',
          background: 'var(--vscode-editorHoverWidget-background, rgba(0,0,0,0.85))',
          color: 'var(--vscode-editorHoverWidget-foreground, #fff)',
          border: '1px solid var(--vscode-editorHoverWidget-border, transparent)',
          padding: '2px 6px',
          borderRadius: '3px',
          fontSize: '11px',
          lineHeight: 1.4,
          whiteSpace: 'nowrap',
          pointerEvents: 'none',
          zIndex: 100,
        }
      }, tooltip),
    )
  }

  export default function (props) {
    const { kind, columnNames, rows } = props
    const renderCell = kind === 'needs' ? needsCell : bitsetCell
    const ncols = (rows[0] && rows[0].cells.length) || 0
    const hasColNames = columnNames && columnNames.length > 0
    const hasRowNames = rows.some(r => r.name != null)

    const gridStyle = {
      display: 'inline-grid',
      gridTemplateColumns:
        (hasRowNames ? 'auto ' : '') + 'repeat(' + ncols + ', 20px)',
      gap: 0,
      alignItems: 'center',
      fontFamily: 'var(--vscode-font-family)',
      fontSize: '11px',
    }

    const children = []
    let key = 0
    if (hasColNames) {
      if (hasRowNames) children.push(h('div', { key: key++ }))
      for (const name of columnNames) {
        children.push(h('div', {
          key: key++,
          style: {
            writingMode: 'vertical-rl',
            transform: 'rotate(180deg)',
            whiteSpace: 'nowrap',
            textAlign: 'left',
            alignSelf: 'end',
            fontSize: '11px',
          }
        }, name))
      }
    }
    for (const row of rows) {
      if (hasRowNames) {
        children.push(h('div', {
          key: key++,
          style: { textAlign: 'right', paddingRight: '4px' }
        }, row.name || ''))
      }
      for (const cell of row.cells) {
        children.push(h(CellWithTooltip,
          { key: key++, tooltip: tooltipOf(cell) },
          renderCell(cell)))
      }
    }
    return h('div', { style: gridStyle }, ...children)
  }
"

@[widget_module]
public def Grid : Widget.Module where
  javascript := gridJs

/-! ## Helpers: extracting structure -/

open Lake Shake

/-- The highest index set in any of `n`'s four bitsets, or `none` if all are empty. -/
def _root_.Lake.Shake.Needs.max? (n : Needs) : Option Nat :=
  let combine (a b : Option Nat) : Option Nat := match a, b with
    | none, x => x
    | x, none => x
    | some a, some b => some (max a b)
  combine (combine n.pub.max? n.priv.max?)
          (combine n.metaPub.max? n.metaPriv.max?)

/-! ## Helpers: building grid cells from `Bitset` and `Needs` -/

/-- The length to use when rendering `s`, given an optional explicit `padding`:
`padding` if supplied, else `s.max? + 1` (or 0 if `s` is empty). -/
private def bitsetRenderLen (s : Bitset) (padding : Option Nat) : Nat :=
  padding.getD (s.max?.map (· + 1) |>.getD 0)

/-- The length to use when rendering `n`, given an optional explicit `padding`:
`padding` if supplied, else `n.max? + 1` (or 0 if all of `n`'s bitsets
are empty). -/
private def needsRenderLen (n : Needs) (padding : Option Nat) : Nat :=
  padding.getD (n.max?.map (· + 1) |>.getD 0)

/-- Build a row of `BitsetCell`s. The output array has length

* `padding`, if supplied;
* otherwise `s.max? + 1` (or `0` if `s` is empty).

The cell at index `i` is on iff `s.has i`. Its `name` is `names[i]?.getD ""`
and `neededBy` is `neededBy[i]?.getD none`. -/
def _root_.Lake.Shake.Bitset.toBitsetCells (s : Bitset)
    (names : Array String) (neededBy : Array (Option String) := #[])
    (padding : Option Nat := none) : Array BitsetCell :=
  let len := bitsetRenderLen s padding
  (Array.range len).map fun i =>
    { on       := s.has i
      name     := names[i]?.getD ""
      neededBy := neededBy[i]?.getD none }

/-- Build a row of `NeedsCell`s. The output array has length

* `padding`, if supplied;
* otherwise `n.max? + 1` (or `0` if all of `n`'s bitsets are empty).

Each cell's four bits come from the corresponding `NeedsKind` bitsets of `n`.
Its `name` is `names[i]?.getD ""` and `neededBy` is `neededBy[i]?.getD none`. -/
def _root_.Lake.Shake.Needs.toNeedsCells (n : Needs)
    (names : Array String) (neededBy : Array (Option String) := #[])
    (padding : Option Nat := none) : Array NeedsCell :=
  let len := needsRenderLen n padding
  (Array.range len).map fun i =>
    { metaPub  := n.metaPub.has  i
      pub      := n.pub.has      i
      metaPriv := n.metaPriv.has i
      priv     := n.priv.has     i
      name     := names[i]?.getD ""
      neededBy := neededBy[i]?.getD none }

/-! ## Helpers: producing `MessageData` widgets -/

private def mkWidgetMsg [Server.RpcEncodable α] (props : α) (title : String) :
    CoreM MessageData := do
  return .ofWidget
    (← Widget.WidgetInstance.ofHash Grid.javascriptHash
        (Server.RpcEncodable.rpcEncode props))
    title

/-- Build a `MessageData` widget displaying a single `Bitset` as a row of
on/off squares. See `Bitset.toBitsetCells` for how `padding` and the optional
`neededBy` array are used. -/
def displayBitset (s : Bitset) (names : Array String)
    (neededBy : Array (Option String) := #[])
    (columnNames : Option (Array String) := none)
    (padding : Option Nat := none) (title : String := "bitset") :
    CoreM MessageData := do
  let row : BitsetGridRow := { cells := s.toBitsetCells names neededBy padding }
  mkWidgetMsg ({ columnNames, rows := #[row] } : BitsetGridProps) title

/-- Build a `MessageData` widget displaying a single `Needs` as a row of
four-region icons. See `Needs.toNeedsCells` for how `padding` and the optional
`neededBy` array are used. -/
def displayNeeds (n : Needs) (names : Array String)
    (neededBy : Array (Option String) := #[])
    (columnNames : Option (Array String) := none)
    (padding : Option Nat := none) (title : String := "needs") :
    CoreM MessageData := do
  let row : NeedsGridRow := { cells := n.toNeedsCells names neededBy padding }
  mkWidgetMsg ({ columnNames, rows := #[row] } : NeedsGridProps) title

/-- The smallest column count that fits every bitset in `rows`. -/
private def maxBitsetLen (rows : Array (Option String × Bitset)) : Nat := Id.run do
  let mut m := 0
  for (_, s) in rows do
    if let some i := s.max? then
      m := max m (i + 1)
  return m

/-- The smallest column count that fits every `Needs` in `rows`. -/
private def maxNeedsLen (rows : Array (Option String × Needs)) : Nat := Id.run do
  let mut m := 0
  for (_, n) in rows do
    if let some i := n.max? then
      m := max m (i + 1)
  return m

/-- Build a `MessageData` widget displaying multiple `Bitset`s, one per row,
each labeled by the (optional) row name. The column count is `padding` if
supplied, otherwise the smallest length that fits every row. -/
def displayBitsetRows (rows : Array (Option String × Bitset))
    (names : Array String) (neededBy : Array (Option String) := #[])
    (columnNames : Option (Array String) := none)
    (padding : Option Nat := none) (title : String := "bitsets") :
    CoreM MessageData := do
  let len := padding.getD (maxBitsetLen rows)
  let gridRows : Array BitsetGridRow := rows.map fun (name, s) =>
    { name, cells := s.toBitsetCells names neededBy (padding := some len) }
  mkWidgetMsg ({ columnNames, rows := gridRows } : BitsetGridProps) title

/-- Build a `MessageData` widget displaying multiple `Needs`, one per row,
each labeled by the (optional) row name. The column count is `padding` if
supplied, otherwise the smallest length that fits every row. -/
def displayNeedsRows (rows : Array (Option String × Needs))
    (names : Array String) (neededBy : Array (Option String) := #[])
    (columnNames : Option (Array String) := none)
    (padding : Option Nat := none) (title : String := "needs") :
    CoreM MessageData := do
  let len := padding.getD (maxNeedsLen rows)
  let gridRows : Array NeedsGridRow := rows.map fun (name, n) =>
    { name, cells := n.toNeedsCells names neededBy (padding := some len) }
  mkWidgetMsg ({ columnNames, rows := gridRows } : NeedsGridProps) title

/-! ## Convenience: derive names from the environment

These let you write `logInfo <| ← needs.toWidget env`, pulling tooltip names
from `env.allImportedModuleNames`. -/

private def moduleNames (env : Environment) : Array String :=
  env.allImportedModuleNames.map (·.toString)

/-- Display `s` as a `MessageData` widget, using module names from `env`
for tooltips. -/
def _root_.Lake.Shake.Bitset.toWidget (s : Bitset) (env : Environment)
    (neededBy : Array (Option String) := #[])
    (columnNames : Option (Array String) := none)
    (padding : Option Nat := none) (title : String := "bitset") :
    CoreM MessageData :=
  displayBitset s (moduleNames env) neededBy columnNames padding title

/-- Display `n` as a `MessageData` widget, using module names from `env`
for tooltips. -/
def _root_.Lake.Shake.Needs.toWidget (n : Needs) (env : Environment)
    (neededBy : Array (Option String) := #[])
    (columnNames : Option (Array String) := none)
    (padding : Option Nat := none) (title : String := "needs") :
    CoreM MessageData :=
  displayNeeds n (moduleNames env) neededBy columnNames padding title

end

end ImportGraph.Widget
