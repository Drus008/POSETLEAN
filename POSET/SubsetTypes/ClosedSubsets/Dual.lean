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

theorem UpwardClosure_Is_Dual_DownwardClosure (S : A → Prop) :
  (UpwardClosure P S) = (DownwardClosure (DualPOSET P) S) := by
  funext x
  apply propext
  constructor
  · intro h
    exact h
  · intro h
    exact h

theorem DownwardClosure_Is_Dual_UpwardClosure (S : A → Prop) :
  (DownwardClosure P S) = (UpwardClosure (DualPOSET P) S) := by
  have h := UpwardClosure_Is_Dual_DownwardClosure (DualPOSET P) S
  rw [Dual_Dual_Is_OG P] at h
  exact h

theorem ElementUpwardClosure_Is_Dual_ElementDownwardClosure (a : A) :
  (ElementUpwardClosure P a) = (ElementDownwardClosure (DualPOSET P) a) := by
  unfold ElementUpwardClosure ElementDownwardClosure DualPOSET
  simp

theorem ElementDownwardClosure_Is_Dual_ElementUpwardClosure (a : A) :
  (ElementDownwardClosure P a) = (ElementUpwardClosure (DualPOSET P) a) := by
  have h := ElementUpwardClosure_Is_Dual_ElementDownwardClosure (DualPOSET P) a
  rw [Dual_Dual_Is_OG] at h
  exact h


theorem UDirectedSet_Is_Dual_DDirectedSet {S : A → Prop} (h : UDirectedSet P S) :
  DDirectedSet (DualPOSET P) S := by
  trivial

theorem DDirectedSet_Is_Dual_UDirectedSet {S : A → Prop} (h : DDirectedSet P S) :
  UDirectedSet (DualPOSET P) S := by
  trivial

theorem Dual_UDirectedSet_Is_DDirectedSet {S : A → Prop} (h : UDirectedSet (DualPOSET P) S) :
  DDirectedSet P S := by
  trivial

theorem Dual_DDirectedSet_Is_UDirectedSet {S : A → Prop} (h : DDirectedSet (DualPOSET P) S) :
  UDirectedSet P S := by
  trivial

theorem Filter_Is_Dual_Ideal {S : A → Prop} (h : Filter P S) :
  Ideal (DualPOSET P) S := by
  trivial

theorem Ideal_Is_Dual_Filter {S : A → Prop} (h : Ideal P S) :
  Filter (DualPOSET P) S := by
  trivial

theorem Dual_Filter_Is_Ideal {S : A → Prop} (h : Filter (DualPOSET P) S) :
  Ideal P S := by
  trivial

theorem Dual_Ideal_Is_Filter {S : A → Prop} (h : Ideal (DualPOSET P) S) :
  Filter P S := by
  trivial
