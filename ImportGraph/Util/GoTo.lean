/-
Copyright (c) 2026 Thomas R. Murrills. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison, Paul Lezeau
-/
module

public import Lean.Server.Rpc.RequestHandling
public meta import Lean.Widget.UserWidget

open Lean

public meta section

namespace ImportGraph

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
  overrideText : Option String := none
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
              const uri = await rs.call('ImportGraph.getModuleUri', props.modName)
              ec.revealPosition({ uri, line: props.pos.line, character: props.pos.character })
            } catch {}
          }
        },
        props.modName)
    }
  "

/-- Creates a clickable link which takes the user to the provided module.

By default, takes the user to the top of the module. Providing `pos` will bring the user to that
position in the file.

By default, the module name is used as the link's text. The text can be overridden by providing
`overrideText`.
-/
def mkGoToModuleLink (modName : Name) (pos : Lsp.Position := ⟨0,0⟩)
    (overrideText : Option String := none) : CoreM MessageData := do
  let p : GoToModuleLinkProps := { modName, pos, overrideText }
  return .ofWidget
    (← Widget.WidgetInstance.ofHash GoToModuleLink.javascriptHash <|
      Server.RpcEncodable.rpcEncode p)
    (overrideText.getD <| toString modName)

/-- A position past the end of any file, assuming no file has more than 4294967296 lines. -/
def pastEndOfFile : Lsp.Position := { line := 1 <<< 32, character := 0 }

/--
Goes to a position after the command defining `decl`. By default, goes to the start of the line
after the end of `decl`'s command (not including whitespace). If instead `lineAfter := false`, then
goes to the end position of `decl`'s command (not including whitespace).

Errors if `decl` is not present in the environment. If no range can be found, goes to the end of
the file. May go to the current module.

By default, the link text is the name of `decl`s module. The text can be overridden with
`overrideText`.
-/
def mkGoToModuleAfterDecl (decl : Name) (overrideText : Option String := none)
    (lineAfter := true) : CoreM MessageData := do
  let pos := (← findDeclarationRanges? decl).elim pastEndOfFile fun { range .. } =>
    let pos := range.toLspRange.end
    if lineAfter then { line := pos.line + 1, character := 0 } else pos
  let mod ← (← findModuleOf? decl).getDM getMainModule
  mkGoToModuleLink mod pos overrideText

/--
Goes to a position just before the command defining `decl`. By default, goes to the start of the
line after the end of `decl`'s command (not including whitespace). If instead `lineAfter := false`,
then goes to the end position of `decl`'s command (not including whitespace).

Errors if `decl` is not present in the environment. If no range can be found, goes to the end of
the file. May go to the current module.

By default, the link text is the name of `decl`s module. The text can be overridden with
`overrideText`.
-/
def mkGoToModuleBeforeDecl (decl : Name) (overrideText : Option String := none)
    (lineBefore := true) : CoreM MessageData := do
  let pos := (← findDeclarationRanges? decl).elim pastEndOfFile fun { range .. } =>
    let pos := range.toLspRange.start
    if lineBefore then { line := pos.line - 1, character := 0 } else pos
  let mod ← (← findModuleOf? decl).getDM getMainModule
  mkGoToModuleLink mod pos overrideText
