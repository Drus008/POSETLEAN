import POSET.SubsetTypes.ClosedSubsets.Defs
import POSET.DualOrder

variable {A : Type} (P : POSET A)
local infix:50 " ≤ " => P.rel

theorem UpwardClosed_Is_Dual_DownwardClosed {U : A → Prop} (h : UpwardClosed P U) : DownwardClosed (DualPOSET P) U
  := by
  unfold DownwardClosed
  unfold UpwardClosed at h
  intro a x h1
  have h := h a x
  exact h h1

theorem DownwardClosed_Is_Dual_UpwardClosed {D : A → Prop} (h : DownwardClosed P D) : UpwardClosed (DualPOSET P) D
  := by
  unfold UpwardClosed
  unfold DownwardClosed at h
  intro a x h1
  have h := h a x
  exact h h1

theorem Dual_UpwardClosed_Is_DownwardClosed {U : A → Prop} (h : UpwardClosed (DualPOSET P) U) : DownwardClosed P U
  := by
  have h := UpwardClosed_Is_Dual_DownwardClosed (DualPOSET P) h
  rw [Dual_Dual_Is_OG] at h
  exact h

theorem Dual_DownwardClosed_Is_UpwardClosed {D : A → Prop} (h : DownwardClosed (DualPOSET P) D) : UpwardClosed P D
  := by
  have h := DownwardClosed_Is_Dual_UpwardClosed (DualPOSET P) h
  rw [Dual_Dual_Is_OG] at h
  exact h
