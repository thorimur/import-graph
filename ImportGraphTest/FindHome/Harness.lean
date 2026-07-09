/-
Copyright (c) 2026 Thomas Murrills. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Murrills
-/
import Lean.Data.Lsp.Communication
import Lean.Data.Lsp.Diagnostics
import Lean.Data.Lsp.Extra
import Lean.Elab.Command

/-!
# A minimal LSP-client harness for golden-file testing of in-server-only commands

`#find_home` (and potentially other commands) only produce useful output when run in the
language server. Rather than building a full interactive testing framework, we take a
golden-file approach:

* fixture files live in small lake packages (e.g. under `ImportGraphTest/FindHome/`)
  which may depend on each other, and on `importGraph` itself via a relative path;
* an orchestrating Lean file (e.g. `ImportGraphTest/FindHome/Serve.lean`) uses the
  commands below to spawn `lake serve` in a fixture package, open a file, and wait for
  its diagnostics;
* the diagnostics are then re-logged in the orchestrating file, where `#guard_msgs`
  provides the golden-file comparison.

The main entry points are:

* `#lake_build "<pkg-dir>"` — sync the fixture package's `lean-toolchain` with the
  workspace root's, run `lake update` (fixture manifests are gitignored, so they are
  regenerated rather than going stale), and run `lake build` (pre-building the fixture
  files' imports so that the server tests are fast and deterministic);
* `#lake_serve "<pkg-dir>" <Module.Name>` — serve the given module and re-log its
  diagnostics.
-/

open Lean Lsp JsonRpc

namespace ImportGraph.Test.Serve

/-- Environment sanitization for nested `lake` invocations: the outer `lake build`/server
sets search-path variables that must not leak into the fixture package's server. -/
def sanitizedEnv : Array (String × Option String) :=
  #[("LEAN_PATH", none), ("LEAN_SRC_PATH", none), ("LAKE", none)]

/-- A running `lake serve` process together with LSP streams. -/
structure Server where
  child : IO.Process.Child ⟨.piped, .piped, .inherit⟩
  stdin : IO.FS.Stream
  stdout : IO.FS.Stream

/-- Read LSP messages until the response for request `id` arrives, returning its result.
Other messages are passed to `onMessage`. Throws on a response error for `id`. -/
partial def readUntilResponse (out : IO.FS.Stream) (id : RequestID)
    (onMessage : JsonRpc.Message → IO Unit := fun _ => pure ()) : IO Json := do
  repeat
    let msg ← out.readLspMessage
    match msg with
    | .response id' result =>
      if id' == id then return result else onMessage msg
    | .responseError id' _ e _ =>
      if id' == id then throw <| IO.userError s!"LSP request {id} failed: {e}"
      else onMessage msg
    | _ => onMessage msg
  unreachable!

/-- Spawn `lake serve` in `dir` and perform the LSP initialization handshake. -/
def Server.start (dir : System.FilePath) : IO Server := do
  let child ← IO.Process.spawn {
    cmd := "lake"
    args := #["serve"]
    cwd := dir
    stdin := .piped
    stdout := .piped
    stderr := .inherit
    env := sanitizedEnv
  }
  let stdin := IO.FS.Stream.ofHandle child.stdin
  let stdout := IO.FS.Stream.ofHandle child.stdout
  let rootUri := s!"file://{← realPathNormalized dir}"
  stdin.writeLspRequest ⟨0, "initialize", Json.mkObj [
    ("processId", Json.null),
    ("rootUri", rootUri),
    ("capabilities", Json.mkObj [])
  ]⟩
  discard <| readUntilResponse stdout 0
  stdin.writeLspNotification ⟨"initialized", Json.mkObj []⟩
  return { child, stdin, stdout }

/-- Politely shut the server down, killing it if that fails. -/
def Server.shutdown (srv : Server) : IO Unit := do
  try
    srv.stdin.writeLspRequest ⟨(2 : RequestID), "shutdown", Json.null⟩
    discard <| readUntilResponse srv.stdout 2
    srv.stdin.writeLspNotification ⟨"exit", Json.null⟩
    discard <| srv.child.wait
  catch _ =>
    srv.child.kill

/-- Open `path` (absolute) on the server and block until all of its diagnostics are ready,
via the Lean-specific `textDocument/waitForDiagnostics` request. Returns the final
diagnostics for the file. -/
def Server.openAndAwaitDiagnostics (srv : Server) (path : System.FilePath) :
    IO (Array Diagnostic) := do
  let uri : DocumentUri := s!"file://{path}"
  let text ← IO.FS.readFile path
  srv.stdin.writeLspNotification ⟨"textDocument/didOpen", Json.mkObj [
    ("textDocument", Json.mkObj [
      ("uri", uri),
      ("languageId", "lean4"),
      ("version", (1 : Nat)),
      ("text", text)
    ])
  ]⟩
  srv.stdin.writeLspRequest ⟨(1 : RequestID), "textDocument/waitForDiagnostics",
    Json.mkObj [("uri", uri), ("version", (1 : Nat))]⟩
  let diags ← IO.mkRef (#[] : Array Diagnostic)
  discard <| readUntilResponse srv.stdout 1 fun msg => do
    let some notif := Notification.ofMessage? msg | return
    unless notif.method == "textDocument/publishDiagnostics" do return
    let .ok (params : PublishDiagnosticsParams) := fromJson? notif.param | return
    unless params.uri == uri do return
    diags.set params.diagnostics
  diags.get

def _root_.Lean.Lsp.DiagnosticSeverity.toMessageSeverity? :
    DiagnosticSeverity → Option MessageSeverity
  | .error       => some .error
  | .information => some .information
  | .warning     => some .warning
  | _ => none

def _root_.Lean.Lsp.Diagnostic.logWithPos {m} [Monad m] [MonadLog m] [AddMessageContext m]
    [MonadOptions m] (d : Diagnostic) : m Unit := do
  log (severity := d.severity?.bind (·.toMessageSeverity?) |>.getD .information )
    m!"@{d.fullRange.start.line}:{d.fullRange.start.character}-\
    {d.fullRange.end.line}:{d.fullRange.end.character}\
    {if d.severity? matches some .hint then " (hint)" else ""}:\n\
    {d.message}"

/-- Run `act`, but fail (running `cleanup`) if it takes longer than `timeoutMs`. -/
def withTimeout (timeoutMs : Nat) (act : IO α) (cleanup : IO Unit) : IO α := do
  let task ← IO.asTask act
  let start ← IO.monoMsNow
  let mut time := 0
  while time - start ≤ timeoutMs do
    if ← IO.hasFinished task then
      return (← IO.ofExcept task.get)
    IO.sleep 50
    time ← IO.monoMsNow
  cleanup
  throw <| IO.userError s!"LSP test timed out after {timeoutMs}ms"

/-- Serve the module `mod` of the package at `pkgDir` (which is interpreted relative to
the current working directory — the workspace root, under `lake build`/`serve`) and
return its final diagnostics. -/
def serveAndCollect (pkgDir : System.FilePath) (mod : Name) (timeoutMs : Nat := 300000) :
    IO (Array Diagnostic) := do
  unless ← pkgDir.isDir do
    throw <| IO.userError s!"fixture package not found at `{pkgDir}` \
      (cwd: {← IO.currentDir}); paths are relative to the workspace root"
  let file := modToFilePath pkgDir mod "lean"
  unless ← file.pathExists do
    throw <| IO.userError s!"no source file for module `{mod}` at `{file}`"
  let path ← IO.FS.realPath file
  let srv ← Server.start pkgDir
  try
    let diags ← withTimeout timeoutMs (srv.openAndAwaitDiagnostics path) srv.child.kill
    srv.shutdown
    return diags
  catch e =>
    srv.child.kill
    throw e

open Elab Command

/-- Overwrite the fixture package's `lean-toolchain` with the workspace root's (found via
the cwd, which is the workspace root under `lake build`/`serve`), so that fixture
toolchains — which are gitignored — never go stale. -/
def syncToolchain (pkgDir : System.FilePath) : IO Unit := do
  let rootToolchain : System.FilePath := "lean-toolchain"
  unless ← rootToolchain.pathExists do
    throw <| IO.userError s!"expected a `lean-toolchain` file at the workspace root \
      (cwd: {← IO.currentDir})"
  let toolchain ← IO.FS.readFile rootToolchain
  let target := pkgDir / "lean-toolchain"
  -- Avoid dirtying the file's mtime when it is already in sync.
  unless (← target.pathExists) && (← IO.FS.readFile target) == toolchain do
    IO.FS.writeFile target toolchain

/-- Run `lake <args>` in `pkgDir` with a sanitized environment, throwing on failure. -/
def runLake (pkgDir : System.FilePath) (args : Array String) : IO Unit := do
  let out ← IO.Process.output {
    cmd := "lake", args, cwd := pkgDir, env := sanitizedEnv
  }
  unless out.exitCode == 0 do
    throw <| IO.userError s!"`lake {" ".intercalate args.toList}` in `{pkgDir}` failed \
      with exit code {out.exitCode}:\n{out.stdout}\n{out.stderr}"

/-- `#lake_build "<pkg-dir>"` prepares the given fixture package, so that subsequent
`#lake_serve` tests do not pay (possibly nondeterministic) resolution and build costs:

1. syncs its `lean-toolchain` with the workspace root's;
2. runs `lake update`, regenerating its (gitignored) manifest so it cannot go stale;
3. runs `lake build`.

The path is relative to the workspace root. -/
elab tk:"#lake_build" dir:str : command => do
  let pkgDir : System.FilePath := dir.getString
  unless ← pkgDir.isDir do
    throwErrorAt tk "fixture package not found at '{pkgDir}' \
      (cwd: {← IO.currentDir}); paths are relative to the workspace root"
  try
    syncToolchain pkgDir
    runLake pkgDir #["update"]
    runLake pkgDir #["build"]
  catch e =>
    throwErrorAt tk (e.toMessageData)

/-- `#lake_serve "<pkg-dir>" <Module.Name>` spawns `lake serve` in the fixture package
`<pkg-dir>` (relative to the workspace root), opens the source file of the given module
(relative to `<pkg-dir>`), waits for its diagnostics, and re-logs each of them here — so
that `#guard_msgs` can be used as a golden-file test. Each logged message carries the
fixture diagnostic's range in its text. -/
elab "#lake_serve" dir:str mod:ident : command => do
  let diags ← serveAndCollect dir.getString mod.getId
  if diags.isEmpty then
    logInfo "Process completed without producing messages."
  else
    for d in diags do d.logWithPos

end ImportGraph.Test.Serve
