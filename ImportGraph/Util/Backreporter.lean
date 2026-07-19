/-
Copyright (c) 2026 Thomas R. Murrills. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas R. Murrills
-/
module

public meta import Lean.Elab.Command
public meta import Lean.Language.Basic
meta import Lean

/-!
# Backreporters: reporting back to commands at the end of the file

Some questions a command asks can only be answered once the rest of the file has been
elaborated: "is this declaration still unused at the end of the file?", "which of these
imports did the file end up needing?". A *backreporter* lets a command file a *request*
during elaboration and receive a report — at the requesting command's position — once the
whole file has been processed.

To define a backreporter, call `registerBackreporter` from an `initialize` block, providing
the handler that will run at the end of the file:

```lean
initialize stillAbsentReporter : Backreporter Name ←
  registerBackreporter fun cmds requests => do
    for req in requests do
      unless (← getEnv).contains req.data do
        req.logWarning m!"`{req.data}` was never defined in this file"
      req.markCompleted
```

Any command elaborator (in a file that imports the `initialize` above) can then file requests:

```lean
elab "#expect_eventually " x:ident : command => do
  stillAbsentReporter.sendRequest x.getId
```

Messages logged via `Request.log*` appear at the requesting command, but are computed at the
end of the file — here, warning on `#expect_eventually foo` only if `foo` never appears.

## Progress reporting

While the rest of the file elaborates, each requesting command is marked as in-progress (the
"yellow bar" in editors), just like commands with asynchronously elaborated proofs. The bar
clears once the backreporter has handled the request:

* automatically, once the handler returns (or throws), or
* eagerly, when the handler calls `Request.markCompleted` — useful for handlers that work
  through many requests, so that each bar clears as soon as its request is actually handled.

`markCompleted` is idempotent and optional; requests never handled by the handler are marked
completed afterwards regardless. Pass `showProgress := false` to `sendRequest` to file a
request with no progress indication at all.

## What handlers can see

Handlers receive the syntax of every command in the file and run against the *final*
environment, after all elaboration has finished; this is what makes end-of-file answers
possible. Some care is still needed:

* Info trees of earlier commands are not available. Capture anything the report needs, beyond
  the final environment and the file's syntax, in the request payload.
* Any state the handler modifies is discarded; only its messages and traces are reported.
* Handlers run at the end of *every* file that imports their `initialize` declaration, even
  when no requests were filed (`requests` is then empty). This permits whole-file reports and
  "an expected request never arrived" errors; handlers that are purely request-driven should
  simply return when `requests.isEmpty`.
* Handler messages (for every backreporter) are delivered together, once all of the file's
  module linters have finished — `markCompleted` affects only progress reporting, not message
  delivery.

## Main declarations

* `Backreporter`: token identifying a registered backreporter; required to file requests.
* `registerBackreporter`: defines a backreporter (from an `initialize` block).
* `Backreporter.sendRequest`: files a request from a command elaborator.
* `Backreporter.Request`: a filed request, as seen by the handler: a syntax location to report
  at (`Request.log*`), a typed payload, and completion state (`Request.markCompleted`).

## Implementation notes

A backreporter is a `ModuleLinter` plus a per-backreporter environment extension holding the
file's requests. Storing requests in the environment (rather than, say, alongside the linter
in its `IO.Ref`) is what makes them well-behaved during interactive editing: re-elaborating a
command replaces its requests, deleting a command deletes them, and incrementally reused
commands have their requests replayed — including their in-flight progress state.

Progress bars are implemented by logging, at request time, a snapshot task over the requesting
command's syntax, backed by a `Unit`-typed `IO.Promise`. The promise is intentionally a bare
completion signal: report content must flow through messages, not through the promise, since
an incrementally reused command keeps its already-resolved snapshot task, which would pin a
stale report (promise resolution is first-wins). The same first-wins semantics is what makes
`markCompleted` safe to expose: the worst it can do is clear a bar early. The snapshot task is
built with `IO.Promise.resultD`, so even a promise dropped without resolution (e.g. when
elaboration of the rest of the file is abandoned) cannot block reporting.
-/

open Lean Elab Command Language

public meta section

namespace ImportGraph

namespace Backreporter

/-- A single report-back request, as seen by a backreporter's handler. -/
structure Request (α : Type) where private mk' ::
  /-- The syntax the report should attach to; by default, the requesting command. -/
  ref : Syntax
  /-- The payload provided at request time. Since handlers only otherwise see the final
  environment and the file's command syntax, anything else the report needs — names, positions,
  elaborated data — should be captured here. -/
  data : α
  /-- The promise backing this request's progress task, if progress was requested. `Unit`-typed
  by design: resolving it signals completion and nothing else. Use `Request.markCompleted`. -/
  private promise? : Option (IO.Promise Unit)

/-- A request that carries no data. -/
abbrev SimpleRequest := Request Unit

/-- Creates a standalone request with no progress task, not filed with any backreporter — for
example, to drive a handler directly in tests. To file a request, use
`Backreporter.sendRequest`, which manages progress tasks via its `showProgress` flag. -/
def Request.mkPure (ref : Syntax) (data : α) : Request α :=
  { ref, data, promise? := none }

/-- Creates a standalone simple request with no progress task, not filed with any backreporter —
for example, to drive a handler directly in tests. To file a request, use
`Backreporter.sendSimpleRequest`, which manages progress tasks via its `showProgress` flag. -/
def SimpleRequest.mkPure (ref : Syntax) : SimpleRequest :=
  { ref, data := (), promise? := none }

/--
Marks this request as handled, clearing its progress bar now rather than when the handler
returns. Call it as each request's processing completes so that progress clears in sync with
actual completions. Optional and idempotent: every request is marked completed once the
handler has run (even if it threw). Note that this affects progress reporting only — the
handler's *messages* are all delivered together, once the file's module linters have finished.
-/
def Request.markCompleted (req : Request α) : BaseIO Unit :=
  req.promise?.forM (·.resolve ())

/-- Whether this request was filed with a progress task (`sendRequest`'s `showProgress`). -/
def Request.hasProgressTask (req : Request α) : Bool :=
  req.promise?.isSome

/-- If this request has a progress task, whether it has been marked completed
(see `Request.markCompleted`). Returns `none` if the request has no progress task. -/
def Request.isComplete? (req : Request α) : BaseIO (Option Bool) :=
  req.promise?.mapM (·.isResolved)

/-- `true` if this request has no progress task, or has a progress task that has not yet been
marked completed (see `Request.markCompleted`). -/
def Request.isPending (req : Request α) : BaseIO Bool :=
  match req.promise? with
  | none => pure true
  | some promise => notM promise.isResolved

/-- Logs a message at the request site; a thin wrapper around `logAt req.ref msg severity`. -/
@[inline] def Request.log [Monad m] [MonadLog m] [AddMessageContext m] [MonadOptions m]
    (req : Request α) (msg : MessageData) (severity : MessageSeverity := .information) :
    m Unit :=
  logAt req.ref msg severity

@[inline, inherit_doc Request.log]
def Request.logInfo (req : Request α) (msg : MessageData) : CommandElabM Unit :=
  req.log msg .information

@[inline, inherit_doc Request.log]
def Request.logWarning (req : Request α) (msg : MessageData) : CommandElabM Unit :=
  req.log msg .warning

@[inline, inherit_doc Request.log]
def Request.logError (req : Request α) (msg : MessageData) : CommandElabM Unit :=
  req.log msg .error

/-- Runs `f` on each pending request's data (no progress task or an incomplete progress task), with
that request's `ref` as the ambient ref, and marks each request completed as soon as its `f` has
finished — so progress clears request by request rather than all at once. Requests whose progress
task is already marked completed are skipped; requests with no progress task count as always
pending, so repeated calls run `f` on them again.

If `f` throws, requests not yet visited are neither run nor marked completed here; when running
inside a backreporter's handler, they are still marked completed once the handler exits. -/
def Request.forPendingM [Monad m] [MonadRef m] [MonadLiftT BaseIO m] [MonadFinally m]
    (requests : Array (Request α)) (f : α → m Unit) : m Unit := do
  for request in requests do
    if ← request.isPending then
      try
        withRef request.ref <| f request.data
      finally
        request.markCompleted

end Backreporter

/--
Token identifying a registered backreporter with payload type `α`; created by
`registerBackreporter` and required to file requests via `Backreporter.sendRequest`.
-/
structure Backreporter (α : Type) where
  /-- The backreporter's name, used to identify it in trace output. -/
  name : Name
  /-- The handler: receives the syntax of every command in the file together with the requests
  filed during elaboration (in file order), and runs at the end of the file. Exposed here so
  that it can also be invoked directly, e.g. on requests built with `Request.mkPure`. -/
  run : Array Syntax → Array (Backreporter.Request α) → CommandElabM Unit
  /-- The per-backreporter request registry. Requests live in the environment so that they are
  rolled back and replayed correctly during interactive editing. -/
  ext : EnvExtension (Array (Backreporter.Request α))
deriving Nonempty

/-- A backreporter whose requests carry no data. -/
abbrev SimpleBackreporter := Backreporter Unit

/--
Defines a backreporter: at the end of any file that imports this definition, `run` receives the
syntax of every command in the file together with the requests filed during elaboration (in
file order), and reports back — typically at each request's position, via `Request.log*`.

Must be called during initialization:

```lean
initialize myReporter : Backreporter Payload ←
  registerBackreporter fun cmds requests => ...
```

The handler runs against the file's final environment. It runs even when no requests were
filed — return early on `requests.isEmpty` for purely request-driven behavior, or use the
unconditional invocation for whole-file reports or to complain that an expected request never
arrived. See the module docstring for more on what handlers can observe and report.
-/
def registerBackreporter
    (run : Array Syntax → Array (Backreporter.Request α) → CommandElabM Unit)
    (name : Name := by exact decl_name%) :
    IO (Backreporter α) := do
  let ext ← registerEnvExtension (pure #[]) (asyncMode := .mainOnly)
  addModuleLinter {
    name
    run cmds := do
      let requests := ext.getState (← getEnv)
      try
        run cmds requests
      finally
        -- Completion is guaranteed regardless of handler behavior; a request left pending
        -- would freeze its command's progress bar until the next edit.
        for req in requests do
          req.markCompleted
  }
  return { name, run, ext }

@[inherit_doc registerBackreporter]
def registerSimpleBackreporter
    (run : Array Syntax → Array Backreporter.SimpleRequest → CommandElabM Unit)
    (name : Name := by exact decl_name%) :
    IO SimpleBackreporter :=
  registerBackreporter run name

namespace Backreporter

/--
Files a request with backreporter `b`, to be answered by its handler at the end of the file.
The report attaches to `ref?` (default: the current command), and that range is marked as
in-progress ("yellow bar") until the handler has handled the request (see
`Request.markCompleted`). Pass `showProgress := false` to file the request without any
progress indication — e.g. for purely informational aggregation where a lingering bar on the
command would be noise.

Must be called at the command-elaboration level, not from inside an asynchronous elaboration
branch (such as an async proof body).
-/
def sendRequest (b : Backreporter α) (data : α)
    (ref? : Option Syntax := none) (showProgress : Bool := true) : CommandElabM Unit := do
  let ref := ref?.getD (← getRef)
  let promise? ← if showProgress then some <$> IO.Promise.new else pure none
  modifyEnv fun env => b.ext.modifyState env (·.push { ref, data, promise? })
  if let some promise := promise? then
    -- An unfinished snapshot task over `ref` marks it as in-progress in the language server.
    -- `resultD` (rather than `result!`) ensures the task finishes even if the promise is
    -- dropped without resolution, e.g. when elaboration of the rest of the file is abandoned.
    logSnapshotTask {
      stx? := some ref
      cancelTk? := none
      task := promise.resultD () |>.map (sync := true) fun _ =>
        SnapshotTree.mk { desc := s!"backreport from {b.name}", diagnostics := .empty } #[]
    }

@[inline, inherit_doc Backreporter.sendRequest]
def sendSimpleRequest (b : SimpleBackreporter)
    (ref : Syntax) (showProgress : Bool := true) : CommandElabM Unit :=
  sendRequest b () ref showProgress

/--
The requests filed with `b` so far in the current file that are still pending (see
`Request.isPending`), in file order. Useful e.g. for deduplicating at request time.
-/
def pendingRequests (b : Backreporter α) : CommandElabM (Array (Request α)) := do
  b.ext.getState (← getEnv) |>.filterM (·.isPending)

end Backreporter

end ImportGraph
