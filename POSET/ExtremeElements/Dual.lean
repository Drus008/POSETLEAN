import POSET.ExtremeElements.Basic
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
