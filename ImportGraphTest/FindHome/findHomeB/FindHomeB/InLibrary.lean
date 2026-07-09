module

import ImportGraph.Tools.FindHome
import FindHomeB.Local1
import FindHomeA.Upper

/-! `inLibrary` depends on `localHelper` (from `FindHomeB.Local1`, in *this* library) and
`compA`, which `FindHomeB.Local1` already sees. Expect an in-current-library suggestion
to move to `FindHomeB.Local1`. -/

#find_home for
def inLibrary : Nat := localHelper + compA
