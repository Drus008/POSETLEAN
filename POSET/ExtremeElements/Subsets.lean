import POSET.Sets.Basic
import POSET.ExtremeElements.Defs
import POSET.DualOrder
import POSET.ExtremeElements.BasicProp

variable {A : Type} {P : POSET A}

section empty

theorem all_Elements_Are_UpperBound_Of_EmptySet (P : POSET A) (x : A) :
  UpperBound P x emptySet := by
  unfold UpperBound
  intro y h
  rw [emptySet] at h
  contradiction

theorem all_Elements_Are_LowerBound_Of_EmptySet (P : POSET A) (x : A) :
  LowerBound P x emptySet := by
  have h := all_Elements_Are_UpperBound_Of_EmptySet (DualPOSET P) x
  exact Dual_UpperBound_Is_LowerBound h

theorem Max_Is_Inf_EmptySet {M : A} (h : MaxElement P M) :
  Infimum P M emptySet := by
  constructor
  · exact all_Elements_Are_LowerBound_Of_EmptySet P M
  · intro U h1
    unfold MaxElement at h
    exact h U

theorem Min_Is_Sup_EmptySet {m : A} (h : MinElement P m) :
  Supremum P m emptySet := by
  have h1 := Min_Is_Dual_Max h
  have h1 := Max_Is_Inf_EmptySet h1
  exact Dual_Infimum_Is_Supremum h1

end empty


section univ

theorem Global_UpperBound_Is_Max {U : A} (h1 : UpperBound P U universeSet) : MaxElement P U
  := by
  unfold MaxElement
  unfold UpperBound at h1
  intro x
  have h1 := h1 x True.intro
  exact h1

theorem Global_LowerBound_Is_Min {L : A} (h1 : LowerBound P L universeSet) : MinElement P L
  := by
  have h2 := LowerBound_Is_Dual_UpperBound h1
  have h3 := Global_UpperBound_Is_Max h2
  exact Dual_Max_Is_Min h3

end univ


section single


local infix:50 " ≤ " => P.rel

theorem Greater_Is_UpperBound_Singleton (a U : A) (h : a ≤ U) :
  UpperBound P U (unitarySet a) := by
  unfold UpperBound
  intro x h1
  unfold unitarySet at h1
  rw [h1]
  exact h

theorem Lower_Is_LowerBound_Singelton (a L : A) (h : L ≤ a) :
  LowerBound P L (unitarySet a) := by
  have h1 := Greater_Is_UpperBound_Singleton (P := DualPOSET P) a L h
  exact Dual_UpperBound_Is_LowerBound h1

theorem Element_Is_UpperBound_His_Singleton (P : POSET A) (a : A) :
  UpperBound P a (unitarySet a) :=
  Greater_Is_UpperBound_Singleton a a (P.refl a)

theorem Element_Is_LowerBound_His_Singleton (P : POSET A) (a : A) :
  LowerBound P a (unitarySet a) :=
  Lower_Is_LowerBound_Singelton a a (P.refl a)

theorem Element_Singleton_Is_Supremum (P : POSET A) (a : A) :
  Supremum P a (unitarySet a) := by
  apply UpperBound_In_Subset_Is_Supremum
  · exact Element_Is_UpperBound_His_Singleton P a
  · rfl

theorem Element_Singleton_Is_Infimum (P : POSET A) (a : A) :
  Infimum P a (unitarySet a) := by
  have h := Element_Singleton_Is_Supremum (DualPOSET P) a
  exact Dual_Supremum_Is_Infimum h

end single

section pair

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

theorem Lesser_Two_Elements_LowerBound_Pair {P : POSET A} {a b L : A} (ha : P.rel L a) (hb : P.rel L b) :
  LowerBound P L (pairSet a b) := by
  have ha : (DualPOSET P).rel a L := ha
  have hb : (DualPOSET P).rel b L := hb
  have h := Greater_Two_Elements_UpperBound_Pair  ha hb
  exact Dual_UpperBound_Is_LowerBound h

theorem UpperBound_Pair_Greater_Two_Elements {P : POSET A} {a b U : A} (h : UpperBound P U (pairSet a b)) :
  (P.rel a U) ∧ (P.rel b U) := by
  unfold UpperBound pairSet at h
  have ha := h a
  have hb := h b
  simp at ha
  simp at hb
  exact ⟨ha, hb⟩

theorem LowerBound_Pair_Lower_Two_Elements {P : POSET A} {a b L : A} (h : LowerBound P L (pairSet a b)) :
  (P.rel L a) ∧ (P.rel L b) := by
  have h := LowerBound_Is_Dual_UpperBound h
  exact UpperBound_Pair_Greater_Two_Elements h

theorem Greater_Is_UpperBound_Pair {P : POSET A} {a b : A} (h : P.rel a b) : UpperBound P b (pairSet a b) := by
  have h' := P.refl b
  exact Greater_Two_Elements_UpperBound_Pair h h'

theorem Lower_Is_LowerBound_Pair {P : POSET A} {a b : A} (h : P.rel a b) : LowerBound P a (pairSet a b) := by
  have h : (DualPOSET P).rel b a := h
  have h' := Greater_Is_UpperBound_Pair h
  rw [PairSet_Is_Comm a b]
  exact Dual_UpperBound_Is_LowerBound h'

theorem Greater_Is_Sup_Pair {P : POSET A} {a b : A} (h : P.rel a b) : Supremum P b (pairSet a b) := by
  have h := Greater_Is_UpperBound_Pair h
  have h' := R_In_Pair a b
  exact UpperBound_In_Subset_Is_Supremum h h'

theorem Lower_Is_Inf_Pair {P : POSET A} {a b : A} (h : P.rel a b) : Infimum P a (pairSet a b) := by
  have h : (DualPOSET P).rel b a := h
  have h := Greater_Is_Sup_Pair h
  rw [PairSet_Is_Comm a b]
  exact Dual_Supremum_Is_Infimum h

end pair


section subs

theorem UpperBound_Is_UpperBound_Subset {S1 S2 : A → Prop} {U : A} (hU : UpperBound P U S2) (hS : subset S1 S2) :
  UpperBound P U S1 := by
  unfold UpperBound
  intro x h
  have h := hS x h
  exact hU x h

theorem LowerBound_Is_LowerBound_Subset {S1 S2 : A → Prop} {L : A} (hL : LowerBound P L S2) (hS : subset S1 S2) :
  LowerBound P L S1 := by
  have h := LowerBound_Is_Dual_UpperBound hL
  have h := UpperBound_Is_UpperBound_Subset h hS
  exact Dual_UpperBound_Is_LowerBound h

end subs
