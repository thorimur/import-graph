module

import ImportGraph.Tools.FindHome
import FindHomeA.Upper

/-! A declaration with (essentially) no dependencies beyond the prelude: candidate homes
should be as high in the hierarchy as possible (core). -/

#find_home for
def noDeps : Nat := 1
