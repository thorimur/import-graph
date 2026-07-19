module

public import ImportGraph.Util.Backreporter

namespace ImportGraph

open Lean Elab Command Backreporter

public meta section

/-- Runs `Array Syntax → CommandElabM Unit` requests at the end of the file on the module's syntax,
in the same manner as a linter (i.e. only preserving messages and the trace state between
requests). -/
initialize runReporter : Backreporter (Array Syntax → CommandElabM Unit) ←
  registerBackreporter fun cmds requests => do
    for request in requests do withRef request.ref do
      if ← request.isPending then
        let savedState ← get
        try
          request.data cmds
        catch
          | Exception.error ref msg =>
            logException (.error ref m!"Backreporting request failed: {msg}")
          | ex@(Exception.internal _ _) =>
            logException ex
        finally
          modify fun s => { savedState with messages := s.messages, traceState := s.traceState }

/-- Runs `x` at the end of the file. -/
def runLater (x : CommandElabM Unit) (ref? : Option Syntax := none) (showProgress := true) :
    CommandElabM Unit :=
  runReporter.sendRequest (fun _ => x) ref? showProgress

/-- Runs `f` at the end of the file on the module's full `Array Syntax`. -/
def runLaterWithSyntax (f : Array Syntax → CommandElabM Unit)
    (ref? : Option Syntax := none) (showProgress := true) :
    CommandElabM Unit :=
  runReporter.sendRequest f ref? showProgress
