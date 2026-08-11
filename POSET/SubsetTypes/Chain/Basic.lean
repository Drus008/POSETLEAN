import POSET.SubsetTypes.Chain.Defs
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


-- TODO: Chain and LOSET!, Union chain sharing upper/Lower bounds
