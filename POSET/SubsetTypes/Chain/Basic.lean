import POSET.SubsetTypes.Chain.Defs
import POSET.Sets.Algebra.Defs
import POSET.ExtremeElements.Defs
import POSET.DualOrder
import POSET.Sets.SetFamilies.Defs
import POSET.Sets.Defs
import POSET.Sets.SetPOSET.Defs

variable {A : Type} {P : POSET A}

theorem Chain_Is_Dual_Chain {C : A → Prop} (h : Chain P C) : Chain (DualPOSET P) C := by
  unfold Chain
  intro x y hx hy
  have h := h x y hx hy
  cases h
  case inl h =>
    right
    exact h
  case inr h =>
    left
    exact h

theorem Union_Chain_Share_Upp_Low_Bound_Is_Chain {B : A} {CU CL : A → Prop}
  (hCU : Chain P CU) (hCL : Chain P CL) (hU : UpperBound P B CL) (hL : LowerBound P B CU) :
  Chain P (UnionS CU CL) := by
  intro x y hx hy
  unfold UnionS at hx
  unfold UnionS at hy
  cases hx
  case inl hx =>
    cases hy
    case inl hy =>
      exact hCU x y hx hy
    case inr hy =>
      right
      have hx := hL x hx
      have hy := hU y hy
      exact P.trans y B x hy hx
  case inr hx =>
    cases hy
    case inl hy =>
      left
      have hx := hU x hx
      have hy := hL y hy
      exact P.trans x B y hx hy
    case inr hy =>
      exact hCL x y hx hy

theorem Union_Chain_Of_Chains_Is_Chain {F : Family A} (h : Chain (SetPOSET A) F)
  (h' : subset F (Chain P)):
  Chain P (UnionF F) := by
  intro x1 x2 h1 h2
  have ⟨C1, hC1, h1'⟩ := h1
  have ⟨C2, hC2, h2'⟩ := h2
  have h := h C1 C2 hC1 hC2
  cases h with
  | inl h =>
    have h1' := h x1 h1'
    have hC2 := h' C2 hC2
    exact hC2 x1 x2 h1' h2'
  |inr h =>
    have h2' := h x2 h2'
    have hC1 := h' C1 hC1
    exact hC1 x1 x2 h1' h2'


theorem Intersection_NoEmpty_Chains_Is_Chain {F : Family A} {C : A → Prop}
  (h : subset F (Chain P)) (hC : F C) : Chain P (InterseccionF F) := by
  intro x y hx hy
  have hx := hx C hC
  have hy := hy C hC
  have h := h C hC
  exact h x y hx hy
