import POSET.Sets.Algebra.Defs
import POSET.Sets.SetFamilies.Defs
import POSET.Sets.Basic

variable {A : Type}

theorem UnionS_Is_UnionF_Pair (S1 S2 : A → Prop) : (UnionS S1 S2) = UnionF (pairSet S1 S2) := by
  ext x
  unfold UnionS UnionF
  constructor
  · intro h
    cases h with
    | inl hl =>
      have hl' := L_In_Pair S1 S2
      exact ⟨S1, hl', hl⟩
    | inr hr =>
      have hr' := R_In_Pair S1 S2
      exact ⟨S2, hr', hr⟩
  · intro h
    have ⟨S,h,hx⟩ := h
    unfold pairSet at h
    cases h with
    | inl hl =>
      left
      rw [hl] at hx
      exact hx
    | inr hr =>
      right
      rw [hr] at hx
      exact hx

theorem IntersectionS_Is_Intersection_Pair (S1 S2 : A → Prop) :
  (IntersectionS S1 S2) = InterseccionF (pairSet S1 S2) := by
  ext x
  constructor
  · intro h S hS
    cases hS with
    | inl hS =>
      rw [hS]
      exact h.left
    | inr hS =>
      rw [hS]
      exact h.right
  · intro h
    unfold InterseccionF at h
    have h1 := h S1 (L_In_Pair S1 S2)
    have h2 := h S2 (R_In_Pair S1 S2)
    exact ⟨h1, h2⟩
