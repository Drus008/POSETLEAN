import POSET.Morphisms.BasicProp
import POSET.Sets.Algebra.Defs
import POSET.Sets.SetPOSET.Defs
import POSET.Morphisms.Defs
import POSET.DualOrder

theorem Compl_Decreasing (A : Type) : Decreasing (SetPOSET A) Complementary := by
  unfold Decreasing
  intro S1 S2 h x h' absurd
  change subset S1 S2 at h
  have h := h x absurd
  exact h' h

def Compl_Monotone (A : Type) : Monotone (SetPOSET A) (DualPOSET (SetPOSET A)) :=
  Decreasing_Is_DualMonotone (Compl_Decreasing A)
