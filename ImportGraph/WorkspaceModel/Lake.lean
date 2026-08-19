module

public import Lake.Config.Workspace
import Lake.Load.Workspace

open Lean Lake

public section

namespace ImportGraph

namespace System.FilePath

structure Modules where
  dir : System.FilePath
  root : Name := .anonymous

@[inline] def modules (dir : System.FilePath) (root := Name.anonymous) : Modules := { dir, root }

/--
Iterates over the module name corresponding to each `.lean` file found under `dir`, descending into
subdirectories, top-down and left-to-right, accumulating the module-name prefix `pre` and threading
the `ForInStep` state so that early termination propagates across subdirectories.

Auxiliary to the `ForIn` instance for `Modules`; see it for details.
-/
@[specialize]
partial def Modules.forInAux [Monad m] [MonadLiftT IO m] {β}
    (dir : System.FilePath) (pre : Name) (b : β)
    (f : Name × IO.FS.DirEntry → β → m (ForInStep β)) : m (ForInStep β) := do
  let mut b := b
  for entry in ← dir.readDir do
    if (← liftM (m := IO) <| entry.path.isDir) then
      match (← Modules.forInAux entry.path (.str pre entry.fileName) b f) with
      | ForInStep.yield b' => b := b'
      | ForInStep.done b'  => return ForInStep.done b'
    else if entry.path.extension.isEqSome "lean" then
      let mod := .str pre <| (System.FilePath.withExtension entry.fileName "").toString
      match (← f (mod, entry) b) with
      | ForInStep.yield b' => b := b'
      | ForInStep.done b'  => return ForInStep.done b'
  return ForInStep.yield b

/--
`for (mod, dirEntry) in dir.modules` iterates over the module name corresponding to each
`.lean` file contained in `dir`, descending into subdirectories, top-down and left-to-right.

For example, if `dir` contains `A/B/C.lean`, the loop visits `(A.B.C, ⟨"A/B", "C.lean"⟩)`.
-/
instance [Monad m] [MonadLiftT IO m] : ForIn m Modules (Name × IO.FS.DirEntry) where
  forIn spec init f := ForInStep.value <$> Modules.forInAux spec.dir spec.root init f

/--
Splits `path` into the `DirEntry` for its enclosing directory and file name, as `readDir` would
report it. `path.parent` (rather than `path.withFileName ""`) is used for `root` so that it carries
no trailing separator and `root / fileName` round-trips back to `path` — matching the entries
produced when iterating a directory.
-/
def toDirEntry (path : System.FilePath) : IO.FS.DirEntry where
  root := path.parent.getD ""
  fileName := path.fileName.getD ""

end System.FilePath

namespace Lake

open ImportGraph

structure Glob.Modules where
  glob : Glob
  dir : System.FilePath

@[inline] def Glob.modulesIn (dir : System.FilePath) (glob : Glob) : Glob.Modules :=
  { glob, dir }

/--
Iterates over the module names selected by `glob`, resolving submodule globs against the `.lean`
files found under `dir`.

Auxiliary to the `ForIn` instance for `Glob.Modules`; see it for details.
-/
@[specialize]
def Glob.Modules.forIn [Monad m] [MonadLiftT IO m] {β}
    (spec : Glob.Modules) (init : β)
    (f : Name × IO.FS.DirEntry → β → m (ForInStep β)) : m β := do
  match spec.glob with
  | .one n =>
    -- Like Lake's `Glob.forEachModuleIn`, which yields `n` unconditionally: we must not require
    -- `n`'s source file to exist, so build its `DirEntry` without touching the filesystem.
    let modFile := modToFilePath spec.dir n "lean"
    return (← f (n, modFile.toDirEntry) init).value
  | .submodules n =>
    let modDir := modToFilePath spec.dir n ""
    -- `ForIn.forIn`, not the `forIn` being defined here (which the local name would shadow).
    ForIn.forIn (modDir.modules (root := n)) init f
  | .andSubmodules n =>
    let modFile := modToFilePath spec.dir n "lean"
    match ← f (n, modFile.toDirEntry) init with
    | ForInStep.done b => return b
    | ForInStep.yield b =>
      let modDir := modToFilePath spec.dir n ""
      ForIn.forIn (modDir.modules (root := n)) b f

/--
`for (mod, dirEntry) in glob.modulesIn dir` iterates over the module names selected by `glob`,
resolving submodule globs against the `.lean` files found under `dir`.
-/
instance [Monad m] [MonadLiftT IO m] : ForIn m Glob.Modules (Name × IO.FS.DirEntry) where
  forIn := Glob.Modules.forIn

namespace IO

-- TODO: change signature to `EIO`?
/-- Loads the lake workspace from the current directory (or, if specified, from `wsDir?`). Note
that in the language server, the current working directory is the workspace root, so this may be
called during elaboration. -/
public def getWorkspace (wsDir? : Option System.FilePath := none) : IO Workspace := do
  let wsDir ← wsDir?.getDM IO.currentDir
  let (elan?, lean?, lake?) ← findInstall?
  let some lean := lean?
    | throw (.userError "error: no Lean installation found")
  let lake := lake?.getD (.ofLean lean)
  let lakeEnv ← (Env.compute lake lean elan?).toIO (IO.userError ·)
  let (ws?, log) ← (Lake.loadWorkspace { lakeEnv, wsDir }).run?
  if log.any (·.level matches .error) then
    throw <| .userError
      s!"error: Errors were produced while loading the Lake workspace at {wsDir}.\n\
        Log:\n{log}"
  let some ws := ws?
    | throw <| .userError s!"error: Failed to load the Lake workspace at {wsDir}.\n\
        Log:\n{log}"
  return ws

end ImportGraph.Lake.IO
