module

public import Lean.ExtraModUses
import all Lean.ExtraModUses
public import ImportGraph.Lean.EnvExtension

open Lean

public section

/-- Resets the state of the `indirectModUse` extension. Note that the state is never altered in the course of the file, as it only represents imported entries. Only the entries list is gotten/reset. -/
@[inline] def resetIndirectModUses (env : Environment)
    (asyncMode : EnvExtension.AsyncMode := indirectModUseExt.toEnvExtension.asyncMode)
    (asyncDecl : Name := Name.anonymous) :
    Environment :=
  indirectModUseExt.setEntries env [] asyncMode asyncDecl

@[inline] def getIndirectModUsesState (env : Environment)
    (asyncMode : EnvExtension.AsyncMode := indirectModUseExt.toEnvExtension.asyncMode) :
    List IndirectModUse :=
  indirectModUseExt.getEntries env asyncMode

@[inline] def setIndirectModUsesState (env : Environment) (entries : List IndirectModUse)
    (asyncMode : EnvExtension.AsyncMode := indirectModUseExt.toEnvExtension.asyncMode)
    (asyncDecl : Name := Name.anonymous) :
    Environment :=
  indirectModUseExt.setEntries env entries asyncMode asyncDecl

/-- Gets and resets the state of the `indirectModUse` extension. Note that the state is never altered in the course of the file, as it only represents imported entries. Only the entries list is gotten/reset. -/
def getResetIndirectModUses (env : Environment)
    (asyncMode : EnvExtension.AsyncMode := indirectModUseExt.toEnvExtension.asyncMode)
    (asyncDecl : Name := Name.anonymous) :
    List IndirectModUse × Environment :=
  letI indirect := indirectModUseExt.getEntries env asyncMode
  (indirect, resetIndirectModUses env asyncMode asyncDecl)

/-- A wrapper for `extraModUses.toEnvExtension.asyncMode` to allow it to appear as an `optParam` in
a public-facing type. -/
@[inline] def extraModUsesAsyncMode := extraModUses.toEnvExtension.asyncMode

@[inline] def resetExtraModUses (env : Environment) :
    Environment :=
  PersistentEnvExtension.setState extraModUses env ([], {})

@[inline] def getExtraModUsesState (env : Environment)
    (asyncMode : EnvExtension.AsyncMode := extraModUsesAsyncMode)
    (asyncDecl : Name := Name.anonymous) :
    List ExtraModUse × PHashSet ExtraModUse :=
  PersistentEnvExtension.getState extraModUses env asyncMode asyncDecl

@[inline] def setExtraModUsesState (env : Environment)
    (entries : List ExtraModUse)
    (state : PHashSet ExtraModUse) :
    Environment :=
  PersistentEnvExtension.setState extraModUses env (entries, state)

/-- Gets and resets the state of the `extraModUses` extension. Note that the state does not include imported entries. -/
def getResetExtraModUses (env : Environment)
    (asyncMode : EnvExtension.AsyncMode := extraModUsesAsyncMode)
    (asyncDecl : Name := Name.anonymous) :
    (List ExtraModUse × PHashSet ExtraModUse) × Environment :=
  (getExtraModUsesState env asyncMode asyncDecl, resetExtraModUses env)

/-- A wrapper for `isExtraRevModUseExt.toEnvExtension.asyncMode` to allow it to appear as an
`optParam` in a public-facing type. -/
@[inline] def isExtraRevModUseExtAsyncMode := isExtraRevModUseExt.toEnvExtension.asyncMode

/-- Gets the state of the `extraModUses` extension. -/
@[inline] def getIsExtraRevModUse (env : Environment) : Bool :=
  !(isExtraRevModUseExt.getEntries env |>.isEmpty)

/-- Resets the state of the `extraModUses` extension. -/
@[inline] def resetIsExtraRevModUse (env : Environment)
    (asyncMode : EnvExtension.AsyncMode := isExtraRevModUseExtAsyncMode)
    (asyncDecl : Name := Name.anonymous) :
    Environment :=
  if getIsExtraRevModUse env then
    isExtraRevModUseExt.setEntries env [] asyncMode asyncDecl else env

/-- Resets the state of the `extraModUses` extension. -/
@[inline] def setIsExtraRevModUse (env : Environment) (isRev : Bool)
    (asyncMode : EnvExtension.AsyncMode := isExtraRevModUseExtAsyncMode)
    (asyncDecl : Name := Name.anonymous) :
    Environment :=
  if getIsExtraRevModUse env == isRev then env else
    isExtraRevModUseExt.setEntries env (if isRev then [()] else []) asyncMode asyncDecl

/-- Merges the state of the `extraModUses` extension (using "or" semantics). -/
@[inline] def mergeIsExtraRevModUse (env : Environment) (old : Bool)
    (asyncMode : EnvExtension.AsyncMode := isExtraRevModUseExtAsyncMode)
    (asyncDecl : Name := Name.anonymous) :
    Environment :=
  if old then setIsExtraRevModUse env old asyncMode asyncDecl else env

/-- Gets and resets the state of the `extraModUses` extension. -/
def getResetIsExtraRevModUse (env : Environment)
    (asyncMode : EnvExtension.AsyncMode := isExtraRevModUseExtAsyncMode)
    (asyncDecl : Name := Name.anonymous) :
    Bool × Environment :=
  if isExtraRevModUseExt.getEntries env |>.isEmpty then
    (false, env)
  else
    (true, isExtraRevModUseExt.setEntries env [] asyncMode asyncDecl)

def resetShakeExts (env : Environment) (asyncMode : EnvExtension.AsyncMode := .sync)
    (asyncDecl : Name := Name.anonymous) : Environment :=
  letI env := resetIndirectModUses env asyncMode asyncDecl
  letI env := resetExtraModUses env
  resetIsExtraRevModUse env asyncMode asyncDecl

/-- Essentially `(as ++ bs).deleteDuplicatesRev`, keeping later-occurring elements. -/
private def List.prependWithoutDuplicating [BEq α] (as bs : List α) : List α :=
  match as with
  | [] => bs
  | a :: as => let new := as.prependWithoutDuplicating bs; if new.contains a then new else a :: new

/-- Iterates through the first set, inserting elements into the second set unless they exist already. -/
private def Lean.PHashSet.union {α} [BEq α] [Hashable α] (as bs : PHashSet α) :
    PHashSet α := Id.run do
  let mut bs := bs
  for a in as do
    unless bs.contains a do
      bs := bs.insert a
  return bs

open EnvExtension

-- TODO: not sure if these really can all use `.local`. Seems a bit scary to me.

public def copyExtraModUses' (src dest : Environment)
    (srcAsyncMode := extraModUsesAsyncMode)
    (destAsyncMode := extraModUsesAsyncMode) (destAsyncDecl := Name.anonymous) :
    Environment := Id.run do
  let mut env := dest
  for entry in extraModUses.getEntries src srcAsyncMode do
    if !(extraModUses.getState env destAsyncMode destAsyncDecl).contains entry then
      env := extraModUses.addEntry env entry destAsyncMode destAsyncDecl
  env

def copyIndirectModUses (src dest : Environment)
    (srcAsyncMode := indirectModUseExt.toEnvExtension.asyncMode)
    (destAsyncMode := indirectModUseExt.toEnvExtension.asyncMode)
    (destAsyncDecl := Name.anonymous) :
    Environment := Id.run do
  let mut dest := dest
  for i in indirectModUseExt.getEntries src srcAsyncMode do
    dest := indirectModUseExt.addEntry dest i destAsyncMode destAsyncDecl
  return dest

def copyExtraRevModUse (src dest : Environment)
    (srcAsyncMode := isExtraRevModUseExtAsyncMode)
    (destAsyncMode := isExtraRevModUseExtAsyncMode) (destAsyncDecl := Name.anonymous) :
    Environment :=
  if (isExtraRevModUseExt.getEntries src (asyncMode := srcAsyncMode)).isEmpty ||
    (isExtraRevModUseExt.getEntries src destAsyncMode ).isEmpty
  then dest else isExtraRevModUseExt.addEntry dest () destAsyncMode destAsyncDecl

-- Note: the asyncmodes of all these extensions are `.sync`.
@[inline] def copyShakeExts (src dest : Environment)
    (srcAsyncMode := AsyncMode.sync)
    (destAsyncMode := AsyncMode.sync)
    (destAsyncDecl := Name.anonymous) : Environment :=
  copyExtraModUses' src dest
    (srcAsyncMode  := srcAsyncMode)
    (destAsyncMode := destAsyncMode)
    (destAsyncDecl := destAsyncDecl)
  |> copyIndirectModUses src
    (srcAsyncMode  := srcAsyncMode)
    (destAsyncMode := destAsyncMode)
    (destAsyncDecl := destAsyncDecl)
  |> copyExtraRevModUse src
    (srcAsyncMode  := srcAsyncMode)
    (destAsyncMode := destAsyncMode)
    (destAsyncDecl := destAsyncDecl)

-- TODO: could take an approach more like `copyExtraModUses`, possibly even use it. But we don't need to retain the whole environment...
/-- Resets the shake extensions that record modules, then restores them after running the given action, merging any new records into the new ones. -/
def withFreshModRecords' [Monad m] [MonadEnv m] [MonadFinally m] {α} (x : m α)
    (asyncMode : EnvExtension.AsyncMode := .sync)
    (asyncDecl : Name := Name.anonymous) : m α := do
  let indirect := getIndirectModUsesState (← getEnv) asyncMode
  let (extraEntries, extraState) := getExtraModUsesState (← getEnv) asyncMode asyncDecl
  let isRev := getIsExtraRevModUse (← getEnv)
  modifyEnv (resetShakeExts · asyncMode asyncDecl)
  try
    x
  finally
    modifyEnv fun env =>
      letI newIndirect := getIndirectModUsesState env asyncMode
      letI env := setIndirectModUsesState env (newIndirect.prependWithoutDuplicating indirect) asyncMode asyncDecl
      let (newExtraEntries, newExtraState) := getExtraModUsesState env asyncMode asyncDecl
      letI env := setExtraModUsesState env
        (newExtraEntries.prependWithoutDuplicating extraEntries)
        (newExtraState.union extraState)
      mergeIsExtraRevModUse env isRev asyncMode asyncDecl

/-- Resets the shake extensions that record modules, then restores them after running the given action, merging any new records into the new ones. -/
def withFreshModRecords [Monad m] [MonadEnv m] [MonadFinally m] {α} (x : m α) : m α := do
  let oldEnv ← getEnv
  try x finally modifyEnv fun newEnv => copyShakeExts newEnv oldEnv

-- TODO: the above is overzealous around recording rev mod uses, I think.
