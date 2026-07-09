module

import ImportGraph.Tools.FindHome
import FindHomeA.Upper

/-! A mutual block. Both declarations (and their auxiliary recursors/equation lemmas)
should be picked up as produced declarations; the home must account for `compA`
(used by `mutualOdd`). -/

#find_home for
mutual
  def mutualEven : Nat → Bool
    | 0 => true
    | n + 1 => mutualOdd n
  def mutualOdd : Nat → Bool
    | 0 => compA == 1
    | n + 1 => mutualEven n
end
