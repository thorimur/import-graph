module

import all ImportGraph.Tools.Test1
public meta import ImportGraph.Tools.Test1
public meta import Lean.Elab.Command

elab "#show_pls " id:ident : command => do
  Lean.logInfo m!"{showPriv id.getId}"
