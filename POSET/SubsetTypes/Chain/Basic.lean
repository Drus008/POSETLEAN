import POSET.SubsetTypes.Chain.Defs
import POSET.Sets.Algebra.Defs
import POSET.ExtremeElements.Defs
import POSET.DualOrder

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
