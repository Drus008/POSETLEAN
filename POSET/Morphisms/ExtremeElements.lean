import POSET.ExtremeElements.BasicProp
import POSET.Morphisms.BasicProp
import POSET.Sets.Maps.Defs

variable {A B : Type} {PA : POSET A} {PB : POSET B}

theorem Image_Max_Surjective_Monotone_Is_Max {M : A} (h : MaxElement PA M)
  (f : Monotone PA PB) (hf : surjective f) : MaxElement PB (f M) := by
  intro y
  have ⟨x,h'⟩ := hf y
  rw [← h']
  have h := h x
  exact f.mon x M h

theorem Image_Min_Surjective_Monotone_Is_Min {M : A} (h : MinElement PA M)
  (f : Monotone PA PB) (hf : surjective f) : MinElement PB (f M) := by
  let f' := Monotone_Is_DualMonotone f
  have h := Min_Is_Dual_Max h
  have h := Image_Max_Surjective_Monotone_Is_Max h f' hf
  exact Dual_Max_Is_Min h
