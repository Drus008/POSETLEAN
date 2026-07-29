import POSET.Sets.Defs

variable {A : Type}


section unitary

theorem UnitarySet_Determines_Element {a b : A} (h : (unitarySet a) = (unitarySet b)) :
  a = b := by
  unfold unitarySet at h
  have h1 := congrFun h a
  have h2 : a = a := by rfl
  rw [h1] at h2
  exact h2

end unitary

section pair

-- theorem PairSet_Determines_Elements {a1 b1 a2 b2 : A} (h : (pairSet a1 b1) = (pairSet a2 b2))
--  : (((a1 = a2) ∧ (b1 = b2)) ∨ ((a1 = b2) ∧ (b1 = a2))) := by
--  unfold pairSet at h
--  have h1 := congrFun h a1
--  have h2 := congrFun h b1
--  have taut1 : a1 = a1 := rfl
--  have taut1 : a1 = a1 ∨ a1 = b1 := Or.inl taut1
--  have taut2 : b1 = b1 := rfl
--  have taut2 : b1 = a1 ∨ b1 = b1 := Or.inr taut2
--  rw [h1] at taut1
--  rw [h2] at taut2
--
--  rcases taut1 with h_a1_a2 | h_a1_b2
--  · rcases taut2 with h_b1_a2 | h_b1_b2
--    · sorry
--    · left
--      exact ⟨h_a1_a2, h_b1_b2⟩
--  · rcases taut2 with h_b1_a2 | h_b1_b2
--    · right
--      exact ⟨h_a1_b2, h_b1_a2⟩
--    ·sorry


end pair
