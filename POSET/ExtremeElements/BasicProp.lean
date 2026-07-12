import POSET.ExtremeElements.Defs
import POSET.ExtremeElements.Dual

variable (A : Type) (P : POSET A)

local infix:50 " ≤ " => P.rel

theorem Max_unique (M1 M2 : A) (h1 : MaxElement A P M1) (h2 : MaxElement A P M2) : M1 = M2
  := by
  have P1 := h1 M2
  have P2 := h2 M1
  exact P.antisym M1 M2 P2 P1

theorem Min_unique (m1 m2 : A) (h1 : MinElement A P m1) (h2 : MinElement A P m2) : m1 = m2
  := by
  have P1 := Min_Is_Dual_Max A P m1 h1
  have P2 := Min_Is_Dual_Max A P m2 h2
  exact Max_unique A (DualPOSET A P) m1 m2 P1 P2

theorem Max_Is_Maximal (M : A) (h : MaxElement A P M) : MaximalElement A P M := by
  unfold MaximalElement
  unfold MaxElement at h
  intro x h1
  have h2 := h x
  exact P.antisym x M h2 h1

theorem Min_Is_Minimal (m : A) (h : MinElement A P m) : MinimalElement A P m := by
  have h := Min_Is_Dual_Max A P m h
  have h := Max_Is_Maximal A (DualPOSET A P) m h
  exact Dual_Maximal_Is_Minimal A P m h

theorem Global_UpperBound_Is_Max (U : A) (h1 : UpperBound A P U (fun _ => True)) : MaxElement A P U
  := by
  unfold MaxElement
  unfold UpperBound at h1
  intro x
  have h1 := h1 x True.intro
  exact h1

theorem Global_LowerBound_Is_Min (L : A) (h1 : LowerBound A P L (fun _ => True)) : MinElement A P L
  := by
  have h2 := LowerBound_Is_Dual_UpperBound A P L (fun _ => True) h1
  have h3 := Global_UpperBound_Is_Max A (DualPOSET A P) L h2
  exact Dual_Max_Is_Min A P L h3

theorem Max_Is_UpperBound (M : A) (h : MaxElement A P M) (S : A → Prop) : UpperBound A P M S
  := by
  unfold UpperBound
  unfold MaxElement at h
  intro x h1
  exact h x

theorem Min_Is_LowerBound (m : A) (h : MinElement A P m) (S : A → Prop) : LowerBound A P m S
  := by
  have h1 := Min_Is_Dual_Max A P m h
  have h1 := Max_Is_UpperBound A (DualPOSET A P) m h1 S
  exact LowerBound_Is_Dual_UpperBound A P m S h1
