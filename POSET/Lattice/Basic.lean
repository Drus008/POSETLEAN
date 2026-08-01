import POSET.Lattice.Defs
import POSET.Lattice.Dual
import POSET.ExtremeElements.BasicProp
import POSET.ExtremeElements.Subsets
import POSET.Sets.Defs

variable {A : Type}




theorem Join_Is_UpperBound_Pair (J : JoinSemilattice A) (a b : A) : UpperBound J.toPOSET (J.join a b) (pairSet a b) := by
  exact Greater_Two_Elements_UpperBound_Pair (J.up1 a b) (J.up2 a b)

theorem Meet_Is_UpperBound_Pair (M : MeetSemilattice A) (a b : A) : LowerBound M.toPOSET (M.meet a b) (pairSet a b) := by
  let J := Meet_Is_Dual_Join M
  have h := Join_Is_UpperBound_Pair J a b
  exact Dual_UpperBound_Is_LowerBound h


theorem Join_Is_Sup_Pair (J : JoinSemilattice A) (a b : A) : Supremum J.toPOSET (J.join a b) (pairSet a b) := by
  unfold Supremum
  constructor
  · exact Join_Is_UpperBound_Pair J a b
  · intro U h
    have h' := UpperBound_Pair_Greater_Two_Elements h
    exact J.sup a b U h'

theorem Meet_Is_Inf_Pair (M : MeetSemilattice A) (a b : A) : Infimum M.toPOSET (M.meet a b) (pairSet a b) := by
  let J := Meet_Is_Dual_Join M
  have h := Join_Is_Sup_Pair J a b
  exact Dual_Supremum_Is_Infimum h
