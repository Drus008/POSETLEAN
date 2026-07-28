import POSET.SubsetTypes.ClosedSubsets.Dual
import POSET.SubsetTypes.Convex.Defs
import POSET.SubsetTypes.Convex.Dual

variable {A : Type} {P : POSET A} {S : A → Prop}

theorem UpwardClosed_Is_Convex (h : UpwardClosed P S) : Convex P S := by
  unfold Convex
  intro x a b ha hb hax hxb
  unfold UpwardClosed at h
  exact h a x ha hax

theorem DownwardClosed_Is_Convex (h : DownwardClosed P S) : Convex P S := by
  have h := DownwardClosed_Is_Dual_UpwardClosed P h
  have h := UpwardClosed_Is_Convex h
  exact Dual_Convex_Is_Convex h
