module

import ImportGraph.Tools.FindHome

/-! A command that produces no declarations: expect the "did not produce any
declarations" warning. -/

#find_home for
#eval 1 + 1
