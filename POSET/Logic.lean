theorem neg_implication_elim {A B : Prop} (h : ¬(A → B)) : A ∧ ¬B := by
  constructor
  · apply Classical.byContradiction
    intro hna
    apply h
    intro a
    exact False.elim (hna a)
  · intro hb
    apply h
    intro a
    exact hb

theorem not_or_elim {P Q : Prop} (h : ¬(P ∨ Q)) : ¬P ∧ ¬Q := by
  constructor
  · intro p
    apply h
    exact Or.inl p
  · intro q
    apply h
    exact Or.inr q

theorem not_not_iff (P : Prop) : ¬¬P ↔ P := by
  constructor
  · intro hnn
    cases Classical.em P with
    | inl hp =>
      exact hp
    | inr hnp =>
      have h_falso : False := hnn hnp
      exact False.elim h_falso
  · intro hp hnp
    exact hnp hp
