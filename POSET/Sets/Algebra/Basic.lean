import POSET.Sets.Algebra.Defs
import POSET.Sets.Defs
import POSET.Sets.SetFamilies.Algebra
import POSET.Sets.SetFamilies.Basic

variable {A : Type}

theorem Set_Subset_Double_Complement (S1 : A → Prop) : subset S1 (Complementary (Complementary S1)):= by
  intro x h
  intro nh
  exact nh h


theorem U_Comm (S1 S2 : A → Prop) : UnionS S1 S2 = UnionS S2 S1 := by
  ext x
  constructor
  · intro h
    cases h
    case inl h' =>
      right
      exact h'
    case inr h' =>
      left
      exact h'
  · intro h
    cases h
    case inl h' =>
      right
      exact h'
    case inr h' =>
      left
      exact h'

theorem I_Comm (S1 S2 : A → Prop) : IntersectionS S1 S2 = IntersectionS S2 S1 := by
  ext x
  constructor
  · intro h
    exact ⟨h.right,h.left⟩
  · intro h
    exact ⟨h.right,h.left⟩

theorem I_Subset_L (S1 S2 : A → Prop) : subset (IntersectionS S1 S2) S1 := by
  rw [IntersectionS_Is_Intersection_Pair]
  have h := L_In_Pair S1 S2
  exact Intersection_Subset_Element_Family h

theorem I_Subset_R (S1 S2 : A → Prop) : subset (IntersectionS S1 S2) S2 := by
  rw [I_Comm]
  exact I_Subset_L S2 S1

theorem L_Subset_U (S1 S2 : A → Prop) : subset S1 (UnionS S1 S2) := by
  rw [UnionS_Is_UnionF_Pair]
  have h := L_In_Pair S1 S2
  exact Element_Family_Subset_Union h

theorem R_Subset_U (S1 S2 : A → Prop) : subset S2 (UnionS S1 S2) := by
  rw [U_Comm]
  exact L_Subset_U S2 S1
