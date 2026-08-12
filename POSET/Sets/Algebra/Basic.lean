import POSET.Sets.Algebra.Defs
import POSET.Sets.Defs

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
