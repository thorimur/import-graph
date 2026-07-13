module

public import Lake.Config.Workspace
import Lake.Load.Workspace

open Lean Lake

namespace ImportGraph.Lake.IO

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
