/-
Copyright (c) 2026 Thomas R. Murrills. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison, Paul Lezeau
-/
module

public import Lean.Server.Rpc.RequestHandling
public meta import Lean.Widget.UserWidget
public meta import ImportGraph.Lean.Environment

open Lean

public meta section

open Server in
/-- Tries to resolve the module `modName` to a source file URI.
This has to be done in the Lean server
since the `Environment` does not keep track of source URIs. -/
@[server_rpc_method]
meta def getModuleUri (modName : Name) : RequestM (RequestTask Lsp.DocumentUri) :=
  RequestM.asTask do
    let some uri ← documentUriFromModule? modName
      | throw $ RequestError.invalidParams s!"couldn't find URI for module '{modName}'"
    return uri

structure GoToModuleLinkProps where
  modName : Name
  pos : Lsp.Position := { line := 0, character := 0 }
  deriving Server.RpcEncodable

/-- When clicked, this widget component jumps to the source of the module `modName`,
assuming a source URI can be found for the module. -/
@[widget_module]
def GoToModuleLink : Widget.Module where
  javascript := "
    import * as React from 'react'
    import { EditorContext, useRpcSession } from '@leanprover/infoview'

    export default function(props) {
      const ec = React.useContext(EditorContext)
      const rs = useRpcSession()
      return React.createElement('a',
        {
          className: 'link pointer dim',
          onClick: async () => {
            try {
              const uri = await rs.call('getModuleUri', props.modName)
              ec.revealPosition({ uri, line: props.pos.line, character: props.pos.character })
            } catch {}
          }
        },
        props.modName)
    }
  "

def mkGoToModuleLink (modName : Name) (pos : Lsp.Position := ⟨0,0⟩) : CoreM  MessageData := do
  let p : GoToModuleLinkProps := { modName, pos }
  return .ofWidget
    (← Widget.WidgetInstance.ofHash GoToModuleLink.javascriptHash <|
      Server.RpcEncodable.rpcEncode p)
    (toString modName)

/-- A position past the end of any file, assuming no file has more than 4294967296 lines. -/
def pastEndOfFile : Lsp.Position := { line := 1 <<< 32, character := 0 }

def Lean.Lsp.Position.lineAfter : Lsp.Position → Lsp.Position
  | { line .. } => { line := line + 1, character := 0 }

-- Could also load unimported module's
def mkGoToAfterOfImported? (decl : Name) (lineAfter := true) : CoreM (Option MessageData) := do
  let some { range .. } ← findDeclarationRanges? decl | return none
  let pos := range.toLspRange.end
  let pos := if lineAfter then { line := pos.line + 1, character := 0 } else pos
  let mod ← (← getEnv).getModuleFor? decl |>.getDM getMainModule
  mkGoToModuleLink mod pos

def mkGoToAfterOfImported (decl : Name) (lineAfter := true) : CoreM MessageData := do
  let pos := (← findDeclarationRanges? decl).elim pastEndOfFile fun { range .. } =>
    let pos := range.toLspRange.end
    if lineAfter then pos.lineAfter else pos
  let mod ← (← getEnv).getModuleFor? decl |>.getDM getMainModule
  mkGoToModuleLink mod pos
