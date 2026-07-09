module

public import FindHomeA.ComponentA

/-! A module within `findHomeB` itself, for testing in-library relocation suggestions. -/

public def localHelper : Nat := compA + 10
