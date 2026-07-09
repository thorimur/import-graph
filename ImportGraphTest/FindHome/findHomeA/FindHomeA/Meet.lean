module

public import FindHomeA.ComponentA
public import FindHomeA.ComponentB

/-! The meet of `FindHomeA.ComponentA` and `FindHomeA.ComponentB`: the highest module in
this hierarchy that sees both components. Declarations depending on exactly `compA` and
`compB` should find their home here. -/

public def meetResident : Nat := compA + compB
