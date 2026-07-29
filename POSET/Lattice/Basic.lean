import POSET.Lattice.Defs
import POSET.ExtremeElements.BasicProp
import POSET.Sets.Defs

variable {A : Type}

-- This will be better placed in another file
theorem Greater_Two_Elements_UpperBound_Pair {P : POSET A} {a b U : A} (ha : P.rel a U) (hb : P.rel b U) :
  UpperBound P U (pairSet a b) := by
  unfold UpperBound pairSet
  intro x h
  cases h with
  | inl ha' =>
    rw [ha']
    exact ha
  | inr hb' =>
    rw [hb']
    exact hb

theorem UpperBound_Pair_Greater_Two_Elements {P : POSET A} {a b U : A} (h : UpperBound P U (pairSet a b)) :
  (P.rel a U) ∧ (P.rel b U) := by
  unfold UpperBound pairSet at h
  have ha := h a
  have hb := h b
  simp at ha
  simp at hb
  exact ⟨ha, hb⟩



theorem Join_Is_UpperBound_Pair (J : JoinSemilattice A) (a b : A) : UpperBound J.toPOSET (J.join a b) (pairSet a b) := by
  exact Greater_Two_Elements_UpperBound_Pair (J.up1 a b) (J.up2 a b)


theorem Join_Is_Sup_Pair (J : JoinSemilattice A) (a b : A) : Supremum J.toPOSET (J.join a b) (pairSet a b) := by
  unfold Supremum
  constructor
  · exact Join_Is_UpperBound_Pair J a b
  · intro U h
    have h' := UpperBound_Pair_Greater_Two_Elements h
    exact J.sup a b U h'
