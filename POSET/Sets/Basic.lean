import POSET.Sets.Defs

variable {A B C : Type}

section empty

theorem defEmpty1 {S : A → Prop} (h : ¬∃ x : A, S x) : S = @emptySet A := by
  funext x
  apply propext
  unfold emptySet
  constructor
  · intro hS
    have hS : ∃ x : A, S x := ⟨x,hS⟩
    exact h hS
  · intro h
    contradiction

theorem NoEmpty_Has_Element {S : A → Prop} (h : S ≠ emptySet) : ∃ x : A, S x := by
  apply Classical.byContradiction
  intro h_contra
  apply h
  funext x
  apply propext
  constructor
  · intro hx
    apply False.elim
    apply h_contra
    exact ⟨x, hx⟩
  · intro hx_empty
    exact False.elim hx_empty

theorem EmptyNotProper : ¬ proper (@emptySet A) := by
  intro h
  have ⟨x,y,hx,hy⟩ := h
  exact hx

theorem ProperNotEmpty {S : A → Prop} (h : proper S) : ¬ S = (@emptySet A) := by
  intro h'
  have ⟨x, y, hx, hy⟩ := h
  have h' := congrFun h' x
  exact h'.mp hx


end empty


section univ

theorem defUniverse1 {S : A → Prop} (h : ∀ x : A, S x) : S = @universeSet A := by
  funext x
  ext
  constructor
  · intro h
    trivial
  · intro hx
    exact h x

theorem UniverseNotProper : ¬ proper (@universeSet A) := by
  intro h
  have ⟨x,y,hx,hy⟩ := h
  unfold universeSet at hy
  exact hy ⟨⟩

end univ

section unitary

theorem Unitary_Has_Element (a : A) : unitarySet a a := rfl

theorem UnitarySet_Determines_Element {a b : A} (h : (unitarySet a) = (unitarySet b)) :
  a = b := by
  unfold unitarySet at h
  have h1 := congrFun h a
  have h2 : a = a := by rfl
  rw [h1] at h2
  exact h2

theorem Unitary_Not_Empty (a : A) : unitarySet a ≠ emptySet := by
  unfold unitarySet emptySet
  intro h
  have h := congrFun h a
  have ha : a = a := rfl
  rw [h] at ha
  exact ha

theorem Unitary_Subset_Containing_Element (a : A) (S : A → Prop) (h : S a) :
  subset (unitarySet a) S := by
  unfold subset unitarySet
  intro x h1
  rw [← h1] at h
  exact h

end unitary

section pair


theorem PairSet_Is_Comm (a b : A) : pairSet a b = pairSet b a := by
  funext x
  ext
  unfold pairSet
  constructor
  · intro h
    cases h with
    | inl h =>
      right
      exact h
    | inr h =>
      left
      exact h
  · intro h
    cases h with
    | inl h =>
      right
      exact h
    | inr h =>
      left
      exact h

theorem L_In_Pair (a b : A) : (pairSet a b) a := by
  unfold pairSet
  left
  rfl

theorem R_In_Pair (a b : A) : (pairSet a b) b:= by
  rw [PairSet_Is_Comm]
  exact L_In_Pair b a

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

section subset

theorem SubsetReflexive (S : A → Prop) : subset S S := by
  unfold subset
  intro x h
  exact h

theorem SubsetTransitive {S1 S2 S3 : A → Prop} (h1 : subset S1 S2) (h2 : subset S2 S3)
  : subset S1 S3 := by
  unfold subset
  intro x
  intro h
  exact h2 x (h1 x h)

theorem SubsetAntisymetric {S1 S2 : A → Prop} (h1 : subset S1 S2) (h2 : subset S2 S1)
  : S1 = S2 := by
  ext x
  constructor
  · exact h1 x
  · exact h2 x

end subset


section SetOp

theorem SetOp_Comm {Op : A → A → C} (h : ∀ x y : A, Op x y = Op y x) (S1 S2 : A → Prop) :
  SetOperation Op S1 S2 = SetOperation Op S2 S1 := by
  ext x
  constructor
  · intro h'
    have ⟨a1, a2, h1, h2, h'⟩ := h'
    rw [h a1 a2] at h'
    exact ⟨a2, a1, h2, h1, h'⟩
  · intro h'
    have ⟨a1, a2, h1, h2, h'⟩ := h'
    rw [h a1 a2] at h'
    exact ⟨a2, a1, h2, h1, h'⟩



end SetOp
