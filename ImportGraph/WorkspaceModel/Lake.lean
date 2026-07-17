module

public import Lake.Config.Workspace
import Lake.Load.Workspace

open Lean Lake

namespace ImportGraph

namespace System.FilePath

structure Modules where
  dir : System.FilePath
  root : Name := .anonymous

@[inline] def modules (dir : System.FilePath) (root := Name.anonymous) : Modules := { dir, root }

/--
`for (mod, dirEntry) in dir.modules` iterates over the module name corresponding to each
`.lean` file contained in `dir`, descending into subdirectories, top-down and left-to-right.

For example, if `dir` contains `A/B/C.lean`, the loop visits `(A.B.C, ⟨"A/B", "C.lean"⟩)`.
-/
partial instance [Monad m] [MonadLiftT IO m] : ForIn m Modules (Name × IO.FS.DirEntry) where
  forIn {β} spec init f :=
    let rec @[specialize f] loop (dir : System.FilePath) (pre : Name) (b : β) := do
      let mut b := b
      for entry in ← dir.readDir do
        if (← liftM (m := IO) <| entry.path.isDir) then
          match (← loop entry.path (.str pre entry.fileName) b) with
          | ForInStep.yield b' => b := b'
          | ForInStep.done b'  => return ForInStep.done b'
        else if entry.path.extension.isEqSome "lean" then
          let mod := .str pre <| (System.FilePath.withExtension entry.fileName "").toString
          match (← f (mod, entry) b) with
          | ForInStep.yield b' => b := b'
          | ForInStep.done b'  => return ForInStep.done b'
      return ForInStep.yield b
    return (← loop spec.dir spec.root init).value

def toDirEntry (path : System.FilePath) : IO.FS.DirEntry where
  root := path.withFileName ""
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
`for (mod, dirEntry) in glob.modulesIn dir` iterates over the module names selected by `glob`, resolving
submodule globs against the `.lean` files found under `dir`.
-/
instance [Monad m] [MonadLiftT IO m] : ForIn m Glob.Modules (Name × IO.FS.DirEntry) where
  forIn := fun { glob, dir } init f => do
    match glob with
    | .one n =>
      let modFile ← realPathNormalized <| modToFilePath dir n "lean"
      return (← f (n, modFile.toDirEntry) init).value
    | .submodules n =>
      let modDir := modToFilePath dir n ""
      forIn (modDir.modules (root := n)) init fun (mod, entry) b => f (n ++ mod, entry) b
    | .andSubmodules n =>
      let modFile ← realPathNormalized <| modToFilePath dir n "lean"
      match ← f (n, modFile.toDirEntry) init with
      | ForInStep.done b => return b
      | ForInStep.yield b =>
        let modDir := modToFilePath dir n ""
        forIn (modDir.modules (root := n)) b f

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
