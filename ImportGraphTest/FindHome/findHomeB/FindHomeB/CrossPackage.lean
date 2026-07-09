module

import ImportGraph.Tools.FindHome
import FindHomeA.Upper

/-! `crossPackage` depends on exactly `compA` (from `FindHomeA.ComponentA`) and `compB`
(from `FindHomeA.ComponentB`). Among this file's transitive imports, their meet is
`FindHomeA.Meet`, so `#find_home` should suggest upstreaming there — in the *other*
package `findHomeA`. -/

#find_home for
def crossPackage : Nat := compA + compB
