import POSET.Sets.Algebra.Defs
import POSET.Sets.Basic
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

theorem R_Distr_I_To_U_Subset (S1 S2 S3 : A → Prop) :
  subset (UnionS S1 (IntersectionS S2 S3)) (IntersectionS (UnionS S1 S2) (UnionS S1 S3)) := by
  intro x h
  cases h with
  |inl h =>
    have h1 : UnionS S1 S2 x := by
      left
      exact h
    have h2 : UnionS S1 S3 x := by
      left
      exact h
    exact ⟨h1, h2⟩
  |inr h =>
    have h1 : UnionS S1 S2 x := by
      right
      exact h.left
    have h2 : UnionS S1 S3 x := by
      right
      exact h.right
    exact ⟨h1, h2⟩

theorem R_Distr_I_To_U_Subset2 (S1 S2 S3 : A → Prop) :
  subset (IntersectionS (UnionS S1 S2) (UnionS S1 S3)) (UnionS S1 (IntersectionS S2 S3)) := by
  intro x h
  have ⟨h2,h3⟩ := h
  cases h2 with
  | inl h1 =>
    left
    exact h1
  | inr h2 =>
    cases h3 with
    | inl h1 =>
      left
      exact h1
    | inr h3 =>
      right
      exact ⟨h2,h3⟩


theorem R_Distr_I_To_U (S1 S2 S3 : A → Prop):
  UnionS S1 (IntersectionS S2 S3) = IntersectionS (UnionS S1 S2) (UnionS S1 S3) :=
  SubsetAntisymetric (R_Distr_I_To_U_Subset S1 S2 S3) (R_Distr_I_To_U_Subset2 S1 S2 S3)
