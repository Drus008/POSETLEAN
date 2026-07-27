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



section single

def Unitary (a : A) (x : A) : Prop := x = a

local infix:50 " ≤ " => P.rel

theorem Greater_Is_UpperBound_Singleton (a U : A) (h : a ≤ U) :
  UpperBound P U (Unitary a) := by
  unfold UpperBound
  intro x h1
  unfold Unitary at h1
  rw [h1]
  exact h

theorem Lower_Is_LowerBound_Singelton (a L : A) (h : L ≤ a) :
  LowerBound P L (Unitary a) := by
  have h1 := Greater_Is_UpperBound_Singleton (P := DualPOSET P) a L h
  exact Dual_UpperBound_Is_LowerBound h1

theorem Element_Is_UpperBound_His_Singleton (P : POSET A) (a : A) :
  UpperBound P a (Unitary a) :=
  Greater_Is_UpperBound_Singleton a a (P.refl a)

theorem Element_Is_LowerBound_His_Singleton (P : POSET A) (a : A) :
  LowerBound P a (Unitary a) :=
  Lower_Is_LowerBound_Singelton a a (P.refl a)

theorem Element_Singleton_Is_Supremum (P : POSET A) (a : A) :
  Supremum P a (Unitary a) := by
  apply UpperBound_In_Subset_Is_Supremum
  · exact Element_Is_UpperBound_His_Singleton P a
  · rfl

theorem Element_Singleton_Is_Infimum (P : POSET A) (a : A) :
  Infimum P a (Unitary a) := by
  have h := Element_Singleton_Is_Supremum (DualPOSET P) a
  exact Dual_Supremum_Is_Infimum h

end single
