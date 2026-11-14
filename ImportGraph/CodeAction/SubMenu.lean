module

public import Lean.Server.CodeActions.Basic
import Lean
open Lean Server Lsp

meta section

/-!
# Two-stage code-action menu (MWE)

Put the cursor (or a selection) anywhere *below* the provider and press `Ctrl+.` / `Cmd+.`.
The first menu shows **Lean clipboard (3)…** under the *Move* header. Choosing it runs
`editor.action.codeAction` filtered to `refactor.move.lean.clipboard`, which reopens the menu
showing only the clipboard entries. Choosing an entry pastes it at the cursor.

You can also bind a key straight to the second menu (keybindings.json):

    { "key": "ctrl+alt+v", "command": "editor.action.codeAction",
      "args": { "kind": "refactor.move.lean.clipboard", "apply": "never" },
      "when": "editorLangId == lean4" }

The clipboard is hard-coded: this file tests only the menu.
-/

def clipKind : String := "refactor.move.lean.clipboard"

/-- Fake clipboard: (label shown in the menu, text pasted). -/
def fakeClipboard : Array (String × String) := #[
  ("theorem add_zero' (from Foo.lean:12)", "theorem add_zero' (n : Nat) : n + 0 = n := rfl\n"),
  ("def double (from Bar.lean:40, branch feat/x)", "def double (n : Nat) : Nat := 2 * n\n"),
  ("instance : Inhabited Widget (from Baz.lean:7)", "instance : Inhabited Nat := ⟨0⟩\n")]

/-- When `false`, the actions are offered only to explicit requests (`Ctrl+.`, Refactor…,
keybindings), so the clipboard never produces a lightbulb by itself. -/
def showLightbulb : Bool := false

namespace Lean.Lsp

/-- Request a submenu of code actions with a `kind?` that begins with `kindPrefix`. -/
def Command.requestCodeActionKind (title kindPrefix : String) (autoApplySingle := false)
    : Lsp.Command where
  title
  command := "editor.action.codeAction"
  arguments? := some #[
    Json.mkObj [("kind", kindPrefix), ("apply", if autoApplySingle then "ifSingle" else "never")]]

/-- Returns `true` if `key == segment` or `key == s!"{segment}.<rest>"`. -/
def CodeActionKind.startsWithSegment (kind : CodeActionKind) (segment : String) : Bool := Id.run do
  let some rest := kind.dropPrefix? segment | return false
  rest.isEmpty || rest.startsWith '.'

/-- Whether the current code action is specifically requesting a kind of action under `kindPrefix`.

Note that any code action sent after this should likely have `kind?` starting with `kindPrefix`. -/
@[inline] def CodeActionContext.isRequestingOnly (kindPrefix : String)
    (ctx : CodeActionContext) : Bool :=
  ctx.only?.any (·.any (·.startsWithSegment kindPrefix))

@[code_action_provider]
public def clipboardMenu : CodeActionProvider := fun params _snap => do
  let ctx := params.context
  let invoked := match ctx.triggerKind? with
    | some .automatic => false
    | some .invoked => true
    | none => true -- also show for other editors
  unless invoked do return #[]
  let doc ← RequestM.readDoc
  if ctx.isRequestingOnly clipKind then
    -- Second stage: one action per entry. VS Code drops anything not under `clipKind`.
    return fakeClipboard.mapIdx fun i (label, text) => {
      eager := {
        title := s!"Paste {label}"
        kind? := s!"{clipKind}.paste.{i}"
        edit? := some {
          documentChanges? := some #[.edit {
            textDocument := doc.versionedIdentifier
            edits := #[{ range := params.range, newText := text }] }] } } }
  else
    -- First stage: a command-only action that opens the filtered menu.
    return #[{
      eager := {
        title := s!"Paste ({fakeClipboard.size})"
        kind? := "refactor.move.lean"
        command? := some <| .requestCodeActionKind "Open Lean clipboard" clipKind } }]


example : 1 + 1 = 2 := rfl
