module

public import Lean.EnvExtension

public section

open Lean

/-- Modifies the `List α` of entries of a `SimplePersistentEnvExtension`. -/
def Lean.SimplePersistentEnvExtension.modifyEntries {α σ} (env : Environment)
    (ext : SimplePersistentEnvExtension α σ) (f : List α → List α)
    (asyncMode : EnvExtension.AsyncMode := ext.toEnvExtension.asyncMode)
    (asyncDecl : Name := Name.anonymous) : Environment :=
  PersistentEnvExtension.modifyState ext env (fun (entries, s) => (f entries, s))
    asyncMode asyncDecl

/-- Sets the `List α` of entries of a `SimplePersistentEnvExtension`. -/
def Lean.SimplePersistentEnvExtension.setEntries {α σ} (env : Environment)
    (ext : SimplePersistentEnvExtension α σ) (entries : List α)
    (asyncMode : EnvExtension.AsyncMode := ext.toEnvExtension.asyncMode)
    (asyncDecl : Name := Name.anonymous) : Environment :=
  PersistentEnvExtension.modifyState ext env (fun (_, s) => (entries, s))
    asyncMode asyncDecl
