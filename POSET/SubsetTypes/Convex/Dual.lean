import POSET.DualOrder
import POSET.SubsetTypes.Convex.Defs

variable {A : Type} {P : POSET A} {S : A → Prop}

theorem Convex_Is_Dual_Convex (h : Convex P S) : Convex (DualPOSET P) S := by
  unfold Convex DualPOSET
  simp
  unfold Convex at h
  intro x a b ha hb hxa hxb
  exact h x b a hb ha hxb hxa

theorem Dual_Convex_Is_Convex (h : Convex (DualPOSET P) S) : Convex P S := by
  have h := Convex_Is_Dual_Convex h
  rw [Dual_Dual_Is_OG P] at h
  exact h
