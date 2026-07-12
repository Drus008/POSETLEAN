import POSET.ExtremeElements.Defs
import POSET.DualOrder

variable (A : Type) (P : POSET A)

local infix:50 " ≤ " => P.rel

theorem Max_Is_Dual_Min (M : A) (h : MaxElement A P M) : MinElement A (DualPOSET A P) M
  := by
  unfold MinElement DualPOSET
  intro x
  dsimp
  exact h x

theorem Min_Is_Dual_Max (m : A) (h : MinElement A P m) : MaxElement A (DualPOSET A P) m
  := by
  unfold MaxElement DualPOSET
  intro x
  dsimp
  exact h x

theorem Dual_Max_Is_Min (M : A) (h : MaxElement A (DualPOSET A P) M) : MinElement A P M
  := by
  have h2 := Max_Is_Dual_Min A (DualPOSET A P) M h
  rw [Dual_Dual_Is_OG A P] at h2
  exact h2

theorem Dual_Min_Is_Max (m : A) (h : MinElement A (DualPOSET A P) m) : MaxElement A P m
  := by
  have h2 := Min_Is_Dual_Max A (DualPOSET A P) m h
  rw [Dual_Dual_Is_OG A P] at h2
  exact h2

theorem Maximal_Is_Dual_Minimal (M : A) (h : MaximalElement A P M) : MinimalElement A (DualPOSET A P) M
  := by
  unfold MinimalElement DualPOSET
  intro x
  dsimp
  exact h x

theorem Minimal_Is_Dual_Maximal (m : A) (h : MinimalElement A P m) : MaximalElement A (DualPOSET A P) m
  := by
  unfold MaximalElement DualPOSET
  intro x
  dsimp
  exact h x

theorem Dual_Maximal_Is_Minimal (M : A) (h : MaximalElement A (DualPOSET A P) M) : MinimalElement A P M
  := by
  have h2 := Maximal_Is_Dual_Minimal A (DualPOSET A P) M h
  rw [Dual_Dual_Is_OG A P] at h2
  exact h2

theorem Dual_Minimal_Is_Maximal (m : A) (h : MinimalElement A (DualPOSET A P) m) : MaximalElement A P m
  := by
  have h2 := Minimal_Is_Dual_Maximal A (DualPOSET A P) m h
  rw [Dual_Dual_Is_OG A P] at h2
  exact h2

theorem UpperBound_Is_Dual_LowerBound (U : A) (S : A → Prop) (h : UpperBound A P U S) : LowerBound A (DualPOSET A P) U S
  := by
  unfold LowerBound DualPOSET
  intro x
  dsimp
  exact h x

theorem LowerBound_Is_Dual_UpperBound (L : A) (S : A → Prop) (h : LowerBound A P L S) : UpperBound A (DualPOSET A P) L S
  := by
  unfold UpperBound DualPOSET
  intro x
  dsimp
  exact h x

theorem Dual_UpperBound_Is_LowerBound (U : A) (S : A → Prop) (h : UpperBound A (DualPOSET A P) U S) : LowerBound A P U S
  := by
  have h2 := UpperBound_Is_Dual_LowerBound A (DualPOSET A P) U S h
  rw [Dual_Dual_Is_OG A P] at h2
  exact h2

theorem Dual_LowerBound_Is_UpperBound (L : A) (S : A → Prop) (h : LowerBound A (DualPOSET A P) L S) : UpperBound A P L S
  := by
  have h2 := LowerBound_Is_Dual_UpperBound A (DualPOSET A P) L S h
  rw [Dual_Dual_Is_OG A P] at h2
  exact h2

theorem Supremum_Is_Dual_Infimum (s : A) (S : A → Prop) (h : Supremum A P s S) : Infimum A (DualPOSET A P) s S
  := by
  unfold Infimum
  constructor
  · have U : UpperBound A P s S := h.left
    exact UpperBound_Is_Dual_LowerBound A P s S U
  · intro L h2
    unfold DualPOSET
    dsimp
    have h2 := Dual_LowerBound_Is_UpperBound A P L S h2
    have h := h.right
    exact h L h2

theorem Infimum_Is_Dual_Supremum (i : A) (S : A → Prop) (h : Infimum A P i S) : Supremum A (DualPOSET A P) i S
  := by
  unfold Supremum
  constructor
  · have U : LowerBound A P i S := h.left
    exact LowerBound_Is_Dual_UpperBound A P i S U
  · intro L h2
    unfold DualPOSET
    dsimp
    have h2 := Dual_UpperBound_Is_LowerBound A P L S h2
    have h := h.right
    exact h L h2

theorem Dual_Supremum_Is_Infimum (s : A) (S : A → Prop) (h : Supremum A (DualPOSET A P) s S) : Infimum A P s S
  := by
  have h2 := Supremum_Is_Dual_Infimum A (DualPOSET A P) s S h
  rw [Dual_Dual_Is_OG A P] at h2
  exact h2

theorem Dual_Infimum_Is_Supremum (i : A) (S : A → Prop) (h : Infimum A (DualPOSET A P) i S) : Supremum A P i S
  := by
  have h2 := Infimum_Is_Dual_Supremum A (DualPOSET A P) i S h
  rw [Dual_Dual_Is_OG A P] at h2
  exact h2
