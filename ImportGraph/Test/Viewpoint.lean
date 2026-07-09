module

import ImportGraph.Tools.FindHome
import ImportGraph.Test.FakeHome
import ImportGraph.Test.SecondRealHome

/-
`bar₁` is from `ImportGraph.Test.ComponentHome1`
`bar₂` is from `ImportGraph.Test.ComponentHome2`

`ImportGraph.Test.RealHome` imports both
So does `ImportGraph.Test.SecondRealHome`
What if we include `foo`
from `ImportGraph.Test.RealHome`?
-/


def y := false

macro "aa" : term => ``(true)

#find_home for
def x' := true
