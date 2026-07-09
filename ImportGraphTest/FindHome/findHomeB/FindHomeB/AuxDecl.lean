module

import ImportGraph.Tools.FindHome
import FindHomeA.Upper

/-! `usesAux` depends on `auxHelper`, an earlier declaration in this same file, which is
not among the declarations produced by the `#find_home` command itself. Expect the
"depends on earlier declarations in this file" message listing `auxHelper`, and homes
that account for `auxHelper`'s needs (`compA`) as well as `usesAux`'s (`compB`) — i.e.
still `FindHomeA.Meet`. -/

def auxHelper : Nat := compA + 1

#find_home for
def usesAux : Nat := auxHelper + compB
