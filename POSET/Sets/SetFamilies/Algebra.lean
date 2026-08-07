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
