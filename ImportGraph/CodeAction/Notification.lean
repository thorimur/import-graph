module

public import Lean.Server.CodeActions.Basic
import Lean
open Lean Server Lsp

/-! A code action whose resolve step asks the user a question and builds its edit from the answer. -/

@[code_action_provider]
public meta def askingAction : CodeActionProvider := fun params _snap => do
  let ctx ← read
  let doc ← RequestM.readDoc
  let ask : RequestM String := do
    -- The link runs `workbench.action.quickOpen` with argument `["CADialog"]` (URL-encoded JSON array).
    let param := Json.mkObj [("type", 3),
      ("message", "Which one? [Find a file](command:workbench.action.quickOpen?%5B%22CADialog%22%5D)"),
      ("actions", Json.arr #[
        Json.mkObj [("title", "Option B"), ("payload", Json.mkObj [("entryId", 1)])],
        Json.mkObj [("title", "Option B"), ("payload", Json.mkObj [("entryId", 2)])]])]
    let t ← RequestM.sendServerRequest Json Json "window/showMessageRequest" param
    match t.get with
    | .success .null => return "(dismissed)"
    | .success j => return j.compress
    | .failure _ msg => return s!"(failed: {msg})"
  let lazy : IO CodeAction := do
    let answer ← match ← (ask.run ctx).toBaseIO with
      | .ok a => pure a
      | .error e => throw (IO.userError s!"request error: {e.message}")
    return { title := "Ask, then insert", kind? := "refactor", edit? := some {
      documentChanges? := some #[.edit {
        textDocument := doc.versionedIdentifier
        edits := #[{ range := params.range, newText := s!"-- you chose {answer}\n" }] }] } }
  return #[{ eager := { title := "Ask, then insert", kind? := "refactor" }, lazy? := some lazy }]

-- here-- you chose (dismissed)

-- you chose (dismissed)
-- you chose (dismissed)
-- you chose {"payload":{"entryId":2},"title":"Option A"}
-- you chose {"payload":{"entryId":1},"title":"Option B"}
-- you chose {"payload":{"entryId":2},"title":"Option B"}
-- you chose {"payload":{"entryId":1},"title":"Option B"}

-- you chose {"payload":{"entryId":2},"title":"Option B"}
