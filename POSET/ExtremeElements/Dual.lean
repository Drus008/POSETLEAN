import POSET.ExtremeElements.Defs
import POSET.DualOrder

variable {A : Type} (P : POSET A)

local infix:50 " ≤ " => P.rel

theorem Max_Is_Dual_Min (M : A) (h : MaxElement P M) : MinElement (DualPOSET P) M
  := by
  unfold MinElement DualPOSET
  intro x
  dsimp
  exact h x

theorem Min_Is_Dual_Max (m : A) (h : MinElement P m) : MaxElement (DualPOSET P) m
  := by
  unfold MaxElement DualPOSET
  intro x
  dsimp
  exact h x

theorem Dual_Max_Is_Min (M : A) (h : MaxElement (DualPOSET P) M) : MinElement P M
  := by
  have h2 := Max_Is_Dual_Min (DualPOSET P) M h
  rw [Dual_Dual_Is_OG P] at h2
  exact h2

theorem Dual_Min_Is_Max (m : A) (h : MinElement (DualPOSET P) m) : MaxElement P m
  := by
  have h2 := Min_Is_Dual_Max (DualPOSET P) m h
  rw [Dual_Dual_Is_OG P] at h2
  exact h2

theorem Maximal_Is_Dual_Minimal (M : A) (h : MaximalElement P M) : MinimalElement (DualPOSET P) M
  := by
  unfold MinimalElement DualPOSET
  intro x
  dsimp
  exact h x

theorem Minimal_Is_Dual_Maximal (m : A) (h : MinimalElement P m) : MaximalElement (DualPOSET P) m
  := by
  unfold MaximalElement DualPOSET
  intro x
  dsimp
  exact h x

theorem Dual_Maximal_Is_Minimal (M : A) (h : MaximalElement (DualPOSET P) M) : MinimalElement P M
  := by
  have h2 := Maximal_Is_Dual_Minimal (DualPOSET P) M h
  rw [Dual_Dual_Is_OG P] at h2
  exact h2

theorem Dual_Minimal_Is_Maximal (m : A) (h : MinimalElement (DualPOSET P) m) : MaximalElement P m
  := by
  have h2 := Minimal_Is_Dual_Maximal (DualPOSET P) m h
  rw [Dual_Dual_Is_OG P] at h2
  exact h2

theorem UpperBound_Is_Dual_LowerBound (U : A) (S : A → Prop) (h : UpperBound P U S) : LowerBound (DualPOSET P) U S
  := by
  unfold LowerBound DualPOSET
  intro x
  dsimp
  exact h x

theorem LowerBound_Is_Dual_UpperBound (L : A) (S : A → Prop) (h : LowerBound P L S) : UpperBound (DualPOSET P) L S
  := by
  unfold UpperBound DualPOSET
  intro x
  dsimp
  exact h x

theorem Dual_UpperBound_Is_LowerBound (U : A) (S : A → Prop) (h : UpperBound (DualPOSET P) U S) : LowerBound P U S
  := by
  have h2 := UpperBound_Is_Dual_LowerBound (DualPOSET P) U S h
  rw [Dual_Dual_Is_OG P] at h2
  exact h2

theorem Dual_LowerBound_Is_UpperBound (L : A) (S : A → Prop) (h : LowerBound (DualPOSET P) L S) : UpperBound P L S
  := by
  have h2 := LowerBound_Is_Dual_UpperBound (DualPOSET P) L S h
  rw [Dual_Dual_Is_OG P] at h2
  exact h2

theorem Supremum_Is_Dual_Infimum (s : A) (S : A → Prop) (h : Supremum P s S) : Infimum (DualPOSET P) s S
  := by
  unfold Infimum
  constructor
  · have U : UpperBound P s S := h.left
    exact UpperBound_Is_Dual_LowerBound P s S U
  · intro L h2
    unfold DualPOSET
    dsimp
    have h2 := Dual_LowerBound_Is_UpperBound P L S h2
    have h := h.right
    exact h L h2

theorem Infimum_Is_Dual_Supremum (i : A) (S : A → Prop) (h : Infimum P i S) : Supremum (DualPOSET P) i S
  := by
  unfold Supremum
  constructor
  · have U : LowerBound P i S := h.left
    exact LowerBound_Is_Dual_UpperBound P i S U
  · intro L h2
    unfold DualPOSET
    dsimp
    have h2 := Dual_UpperBound_Is_LowerBound P L S h2
    have h := h.right
    exact h L h2

theorem Dual_Supremum_Is_Infimum (s : A) (S : A → Prop) (h : Supremum (DualPOSET P) s S) : Infimum P s S
  := by
  have h2 := Supremum_Is_Dual_Infimum (DualPOSET P) s S h
  rw [Dual_Dual_Is_OG P] at h2
  exact h2

theorem Dual_Infimum_Is_Supremum (i : A) (S : A → Prop) (h : Infimum (DualPOSET P) i S) : Supremum P i S
  := by
  have h2 := Infimum_Is_Dual_Supremum (DualPOSET P) i S h
  rw [Dual_Dual_Is_OG P] at h2
  exact h2
