module

public import FindHomeA.Meet

/-! A module strictly above the meet; `#find_home` should prefer `FindHomeA.Meet` to this
file for declarations that only need the components. -/

public def upperResident : Nat := meetResident + 1
