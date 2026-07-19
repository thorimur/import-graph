/-
Copyright (c) 2026 Thomas Murrills. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Murrills
-/
module

public meta import Lean.Elab.Command
public meta import Lean.Language.Basic
meta import Lean

/-!
# ReportBack (sketch)

Sketch of the recommended surface from `DESIGN.md` (Design B): a command files a *request* with
a statically registered `ModuleLinter` ("backreporter"), which reports back at the requesting
command's position when it runs at the end of the file. The requesting command shows the
"yellow bar" until the report is in.

Key structural decisions (see `DESIGN.md` for the analysis):
* Linter code is registered once, at `initialize` time; per-elaboration requests live in a
  non-persistent, `mainOnly` environment extension minted per backreporter, so requests are
  rolled back / replayed correctly under interactive editing and incremental reuse.
* Report *content* flows through the module linter's own snapshot (fresh on every edit);
  each request's optional promise is `Unit`-typed *by design* — resolving it is a pure
  completion signal, never a content channel — so first-wins resolution and snapshot reuse
  cannot pin stale reports.
* Handlers may clear an individual request's yellow bar early (`Request.clearProgress`) as
  they work through their requests; this is safe because resolution is idempotent and the
  framework backstops every promise in `finally`, so a crashed or forgetful handler can never
  freeze a bar. Tasks are built with `resultD`, so a dropped promise can never hang reporting.
  Progress is opt-in per request (`showProgress := false` files a request with no yellow bar).
* Handlers run unconditionally at the end of the file, even with zero requests — mechanism,
  not policy; early-out on `requests.isEmpty` yourself if you only want request-driven
  behavior.
-/

open Lean Elab Command Language

public meta section

namespace ImportGraph.ReportBack

/-- A single report-back request, as seen by a backreporter's handler. -/
structure Request (α : Type) where private mk' ::
  /-- Syntax the report should attach to; defaults to the requesting command's ref. -/
  ref : Syntax
  /-- Payload provided at request time. Capture everything you need here: backreporters see
  the final environment and whole-file syntax, but *not* earlier commands' info trees. -/
  data : α
  /-- Promise backing this request's "yellow bar" snapshot task, if progress was requested
  (`Backreporter.request`'s `showProgress`). `Unit`-typed by design: resolving it is a pure
  completion signal — report content never flows through it (content through a promise goes
  stale under snapshot reuse; see `DESIGN.md`). Handlers may resolve it early via
  `Request.clearProgress`; the framework resolves any survivors after the handler runs.
  Both are safe: resolution is idempotent (first-wins). -/
  private promise? : Option (IO.Promise Unit)

/-- A request that carries no data. -/
abbrev SimpleRequest := Request Unit

/-- Creates a request with no progress task.

To register a task in the environment instead, use `sendRequest` with the `showProgress` flag
controlling whether a progress task is created for the request. -/
def Request.mkPure (ref : Syntax) (data : α) : Request α :=
  { ref, data, promise? := none }

/-- Creates a simple request with no progress task.

To register a task in the environment instead, use `sendRequest` with the `showProgress` flag
controlling whether a progress task is created for the request. -/
def SimpleRequest.mkPure (ref : Syntax) : SimpleRequest :=
  { ref, data := (), promise? := none }

/--
Clears this request's progress bar ("yellow bar") now, rather than when the handler returns.
Call it as each request's processing completes so that bars clear in sync with actual
completions rather than all at once — module linters can be arbitrarily slow. Optional and
idempotent: the framework clears every remaining bar once the handler has run (even if it
threw). Progress-UI only: report *messages* from module linters are delivered together, once
all module linters have finished.
-/
def Request.markCompleted (req : Request α) : BaseIO Unit :=
  req.promise?.forM (·.resolve ())

variable {m} [Monad m] [MonadLog m] [AddMessageContext m] [MonadOptions m]

/-- Log a message at the request site. A thin wrapper around `log req.ref msg` for convenience. -/
@[inline] def Request.log (req : Request α) (msg : MessageData)
    (severity : MessageSeverity := .information) : m Unit :=
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

/--
Token identifying a registered backreporter with payload type `α`; created by
`registerBackreporter` and required to file requests. Holding the token is the capability to
request reports.
-/
structure Backreporter (α : Type) where
  name : Name
  run : Array Syntax → Array (Request α) → CommandElabM Unit
  /-- Per-reporter request registry. Environment-extension state is versioned with the
  environment, which is what makes requests behave correctly under editing and reuse. -/
  ext : EnvExtension (Array (Request α))
deriving Nonempty

abbrev SimpleBackreporter := Backreporter Unit

/--
Registers a backreporter: a `ModuleLinter` that, at the end of the file, receives the requests
filed by commands during elaboration (in file order) together with the whole file's command
syntax, and reports back — typically at each request's position, via `Request.log*`.

The handler runs against the *final* environment; any environment/state changes it makes are
discarded (only messages and traces escape). It runs even when *no* requests were filed —
early-out on `requests.isEmpty` if you only want request-driven behavior; running
unconditionally enables e.g. whole-file reports, or complaining that an expected request never
arrived. Must be called during initialization, i.e. from an `initialize` block:

```
initialize myReporter : Backreporter Payload ←
  registerBackreporter `myReporter fun cmds requests => ...
```
-/
def registerBackreporter
    (run : Array Syntax → Array (Request α) → CommandElabM Unit)
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
        -- Backstop resolution (first-wins, so early `clearProgress` calls are unaffected):
        -- an unresolved-but-retained promise would freeze a progress bar until the next edit.
        for req in requests do
          req.markCompleted
  }
  return { name, run, ext }

def registerSimpleBackreporter
    (run : Array Syntax → Array SimpleRequest → CommandElabM Unit)
    (name : Name := by exact decl_name%) :=
  registerBackreporter run name

/--
Files a request with backreporter `b`, to be answered when `b` runs at the end of the file.
The report attaches to `ref?` (default: the current command's ref), and that range shows as
in-progress ("yellow bar") until the backreporter has run. Pass `showProgress := false` to
file the request without any progress indication — e.g. for purely informational aggregation
where a lingering bar on the command would be noise.

Must be called at the command-elaboration level, not from inside an async elaboration branch
(the registry's `mainOnly` access mode panics otherwise).
-/
def Backreporter.sendRequest (b : Backreporter α) (data : α)
    (ref? : Option Syntax := none) (showProgress : Bool := true) : CommandElabM Unit := do
  let ref := ref?.getD (← getRef)
  let promise? ← if showProgress then some <$> IO.Promise.new else pure none
  modifyEnv fun env => b.ext.modifyState env (·.push { ref, data, promise? })
  if let some promise := promise? then
    -- Progress reporting (F4/F5 in DESIGN.md): an unfinished snapshot task over `ref` is shown
    -- as a processing range; `resultD` guarantees termination even if the promise is dropped
    -- (tail canceled, `#exit` above, fatal error) — never use `result!` here.
    logSnapshotTask {
      stx? := some ref
      cancelTk? := none
      task := promise.resultD () |>.map (sync := true) fun _ =>
        SnapshotTree.mk { desc := s!"backreport from {b.name}", diagnostics := .empty } #[]
    }

@[inline] def Backreporter.sendSimpleRequest (b : SimpleBackreporter)
    (ref : Syntax) (showProgress : Bool := true) :=
  sendRequest b () ref showProgress

def Request.hasProgressTask (r : Request α) : Bool :=
  r.promise?.isSome

/-- If the `Request` has a progress task, whether that task is marked as complete. Returns `none`
if there is no progress task associated with it. -/
def Request.isComplete? (r : Request α) : BaseIO (Option Bool) :=
  r.promise?.mapM (·.isResolved)

/-- `true` only if the given request has an associated progress task in the first place and that progress task is not completed. -/
def Request.isPending (r : Request α) : BaseIO Bool :=
  match r.promise? with
  | none => pure false
  | some promise => notM promise.isResolved

/-- Evaluates `f` on each pending request with the request's `ref` as the ambient `ref` during
execution, and marks each one completed when `f` is finished.

`f` should not error. If it does, the requests on which `f` was not yet run will not be marked
completed during this function. However, if this is being used within `registerBackreporter`, note
that the `Backreporter` framework will still eventually mark all requests as completed regardless
of whether they error. -/
def Request.forPendingM [MonadRef m] [MonadLiftT BaseIO m] [MonadFinally m]
    (requests : Array (Request α)) (f : α → m Unit) :
    m Unit := do
  for request in requests do
    if ← request.isPending then
      try
        withRef request.ref <| f request.data
      finally
        request.markCompleted

/--
The requests filed with `b` so far in the current file, in file order. Useful e.g. for
deduplicating at request time.
-/
def Backreporter.pendingRequests (b : Backreporter α) : CommandElabM (Array (Request α)) :=
  do b.ext.getState (← getEnv) |>.filterM (·.isPending)

/-!
## Demo

`#report_at_eof foo` reports back, at the `#report_at_eof` command itself, whether `foo` is
still present in the environment at the end of the file — something no ordinary command
elaborator can know at elaboration time.
-/

namespace Demo

/-- Payload for the demo backreporter. -/
structure Payload where
  /-- Constant to look up in the final environment. -/
  constName : Name

initialize demoReporter : Backreporter Payload ←
  registerBackreporter fun cmds requests => do
    let env ← getEnv
    for req in requests do
      let status :=
        if env.contains req.data.constName then "present in" else "absent from"
      req.logInfo
        m!"backreport: `{req.data.constName}` is {status} the final environment \
           ({cmds.size} commands elaborated)"

/-- Ask the demo backreporter whether `x` exists once the whole file has elaborated. -/
elab "#find_later " x:ident : command => do
  unless x.raw.isMissing do
    demoReporter.sendRequest { constName := x.getId }

end Demo

end ImportGraph.ReportBack
