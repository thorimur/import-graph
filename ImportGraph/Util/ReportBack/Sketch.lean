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
  the per-request promise carries *progress only*, so first-wins resolution and snapshot
  reuse cannot pin stale reports.
* The framework — not the handler — resolves every promise, in `finally`; tasks are built
  with `resultD`, so a dropped promise can never hang reporting.
-/

open Lean Elab Command Language

public meta section

namespace ImportGraph.ReportBack

/-- A single report-back request, as seen by a backreporter's handler. -/
structure Request (α : Type) where
  /-- Syntax the report should attach to; defaults to the requesting command's ref. -/
  ref : Syntax
  /-- Payload provided at request time. Capture everything you need here: backreporters see
  the final environment and whole-file syntax, but *not* earlier commands' info trees. -/
  data : α
  -- /-- Progress-only promise; resolved by the framework after the handler runs. Handlers must
  -- not resolve it themselves, and no report content ever flows through it. -/
  -- promise : IO.Promise Unit

abbrev SimpleRequest := Request Unit

/-- Log a message at the request site. Runs inside the backreporter, whose messages are
reported from the end-of-file lint snapshot but positioned at `req.ref`. -/
def Request.log (req : Request α) (msg : MessageData)
    (severity : MessageSeverity := .information) : CommandElabM Unit :=
  withRef req.ref <| logAt req.ref msg severity

@[inherit_doc Request.log]
def Request.logInfo (req : Request α) (msg : MessageData) : CommandElabM Unit :=
  req.log msg .information

@[inherit_doc Request.log]
def Request.logWarning (req : Request α) (msg : MessageData) : CommandElabM Unit :=
  req.log msg .warning

@[inherit_doc Request.log]
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
  ext : EnvExtension (Array (Request α) × Array (IO.Promise Unit))
deriving Nonempty

/--
Registers a backreporter: a `ModuleLinter` that, at the end of the file, receives the requests
filed by commands during elaboration (in file order) together with the whole file's command
syntax, and reports back — typically at each request's position, via `Request.log*`.

The handler runs against the *final* environment; any environment/state changes it makes are
discarded (only messages and traces escape). It is only invoked if at least one request was
filed. Must be called during initialization, i.e. from an `initialize` block:

```
initialize myReporter : Backreporter Payload ←
  registerBackreporter `myReporter fun cmds requests => ...
```
-/
def registerBackreporter
    (run : Array Syntax → Array (Request α) → CommandElabM Unit)
    (name : Name := by exact decl_name%) :
    IO (Backreporter α) := do
  let ext ← registerEnvExtension (pure (#[], #[]))
  addModuleLinter {
    name
    run := fun cmds => do
      let (requests, promises) := ext.getState (← getEnv)
      if requests.isEmpty then return
      try
        run cmds requests
      finally
        for promise in promises do
          promise.resolve ()
  }
  return { name, run, ext }

/--
Files a request with backreporter `b`, to be answered when `b` runs at the end of the file.
The report attaches to `ref?` (default: the current command's ref), and that range shows as
in-progress ("yellow bar") until the backreporter has run.

Must be called at the command-elaboration level, not from inside an async elaboration branch
(the registry's `mainOnly` access mode panics otherwise).
-/
def Backreporter.request (b : Backreporter α) (data : α) (ref? : Option Syntax := none) :
    CommandElabM Unit := do
  let ref := ref?.getD (← getRef)
  let promise ← IO.Promise.new
  modifyEnv fun env => b.ext.modifyState env (·.push { ref, data, promise })
  -- Progress reporting (F4/F5 in DESIGN.md): an unfinished snapshot task over `ref` is shown
  -- as a processing range; `resultD` guarantees termination even if the promise is dropped
  -- (tail canceled, `#exit` above, fatal error) — never use `result!` here.
  logSnapshotTask {
    stx? := some ref
    cancelTk? := none
    task := promise.resultD () |>.map (sync := true) fun _ =>
      SnapshotTree.mk { desc := s!"backreport from {b.name}", diagnostics := .empty } #[]
  }

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
    demoReporter.request { constName := x.getId }

end Demo

end ImportGraph.ReportBack
