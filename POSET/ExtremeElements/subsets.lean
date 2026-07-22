import POSET.ExtremeElements.Defs
import POSET.DualOrder
import POSET.ExtremeElements.BasicProp

variable {A : Type} {P : POSET A}

section empty

def emptySet (_ : A) : Prop := False

theorem all_Elements_Are_UpperBound_Of_EmptySet (P : POSET A) (x : A) :
  UpperBound P x emptySet := by
  unfold UpperBound
  intro y h
  rw [emptySet] at h
  contradiction

theorem all_Elements_Are_LowerBound_Of_EmptySet (x : A) :
  LowerBound P x emptySet := by
  have h := all_Elements_Are_UpperBound_Of_EmptySet (DualPOSET P) x
  exact Dual_UpperBound_Is_LowerBound h

end empty



section single

def singleton (a : A) (x : A) : Prop := x = a


end single
