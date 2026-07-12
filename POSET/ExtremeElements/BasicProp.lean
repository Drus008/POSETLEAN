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
