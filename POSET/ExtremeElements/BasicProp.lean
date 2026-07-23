import POSET.ExtremeElements.Defs
import POSET.ExtremeElements.Dual

variable {A : Type} {P : POSET A}

local infix:50 " ≤ " => P.rel

theorem Max_unique {M1 M2 : A} (h1 : MaxElement P M1) (h2 : MaxElement P M2) : M1 = M2
  := by
  have P1 := h1 M2
  have P2 := h2 M1
  exact P.antisym M1 M2 P2 P1

theorem Min_unique {m1 m2 : A} (h1 : MinElement P m1) (h2 : MinElement P m2) : m1 = m2
  := by
  have P1 := Min_Is_Dual_Max h1
  have P2 := Min_Is_Dual_Max h2
  exact Max_unique P1 P2

theorem Sup_Unique {s1 s2 : A} {S : A → Prop} (h1 : Supremum P s1 S) (h2 : Supremum P s2 S) : s1 = s2
  := by
  have h1' := h1.left
  have h2' := h2.left
  have h1'' := h1.right s2 h2'
  have h2'' := h2.right s1 h1'
  exact antisym P h1'' h2''

theorem Inf_Unique {i1 i2 : A} {S : A → Prop} (h1 : Infimum P i1 S) (h2 : Infimum P i2 S) : i1 = i2
  := by
  have h1' := Infimum_Is_Dual_Supremum h1
  have h2' := Infimum_Is_Dual_Supremum h2
  exact Sup_Unique h1' h2'

theorem Max_Is_Maximal {M : A} (h : MaxElement P M) : MaximalElement P M := by
  unfold MaximalElement
  unfold MaxElement at h
  intro x h1
  have h2 := h x
  exact P.antisym x M h2 h1

theorem Min_Is_Minimal {m : A} (h : MinElement P m) : MinimalElement P m := by
  have h := Min_Is_Dual_Max h
  have h := Max_Is_Maximal h
  exact Dual_Maximal_Is_Minimal h

theorem Global_UpperBound_Is_Max {U : A} (h1 : UpperBound P U (fun _ => True)) : MaxElement P U
  := by
  unfold MaxElement
  unfold UpperBound at h1
  intro x
  have h1 := h1 x True.intro
  exact h1

theorem Global_LowerBound_Is_Min {L : A} (h1 : LowerBound P L (fun _ => True)) : MinElement P L
  := by
  have h2 := LowerBound_Is_Dual_UpperBound h1
  have h3 := Global_UpperBound_Is_Max h2
  exact Dual_Max_Is_Min h3

theorem Max_Is_UpperBound {M : A} (h : MaxElement P M) (S : A → Prop) : UpperBound P M S
  := by
  unfold UpperBound
  unfold MaxElement at h
  intro x h1
  exact h x

theorem Min_Is_LowerBound {m : A} (h : MinElement P m) (S : A → Prop) : LowerBound P m S
  := by
  have h1 := Min_Is_Dual_Max h
  have h1 := Max_Is_UpperBound h1 S
  exact LowerBound_Is_Dual_UpperBound h1


theorem UpperBound_In_Subset_Is_Supremum {S : A → Prop} {U : A} (h : UpperBound P U S) (hU : S U) :
  Supremum P U S := by
  unfold Supremum
  constructor
  · exact h
  · intro U'
    intro h'
    unfold UpperBound at h'
    exact h' U hU

theorem LowerBound_In_Subset_Is_Infimum {S : A → Prop} {I : A} (h : LowerBound P I S) (hI : S I) :
  Infimum P I S := by
  have h' := LowerBound_Is_Dual_UpperBound h
  have h' := UpperBound_In_Subset_Is_Supremum h' hI
  exact Supremum_Is_Dual_Infimum h'
