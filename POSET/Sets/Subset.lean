import POSET.Sets.Defs

variable {A : Type}

theorem subset_Reflexive (S : A → Prop) : subset S S := by
  unfold subset
  intro x h
  exact h
