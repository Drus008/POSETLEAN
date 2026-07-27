import POSET.SubsetTypes.ClosedSubsets.Defs
import POSET.SubsetTypes.ClosedSubsets.Dual
import POSET.Sets.Defs

variable {A : Type} (P : POSET A)
local infix:50 " ≤ " => P.rel

theorem UpwardClausure_Is_UpwardClosed (P : POSET A) (S : A → Prop) :
  UpwardClosed P (UpwardClausure P S) := by
  unfold UpwardClosed
  intro a x h
  have ha := h.right
  have h := h.left
  unfold UpwardClausure at h
  obtain ⟨a',ha'⟩ := h
  have hx := P.trans a' a x ha'.right ha
  unfold UpwardClausure
  exists a'
  constructor
  · exact ha'.left
  · exact hx

theorem DownwardClausure_Is_DownwardClosed (P : POSET A) (S : A → Prop) :
  DownwardClosed P (DownwardClausure P S) := by
  have h := UpwardClausure_Is_UpwardClosed (DualPOSET P) S
  rw [DownwardClausure_Is_Dual_UpwardClausure]
  exact Dual_UpwardClosed_Is_DownwardClosed P h

theorem ElementUpwardClausure_Is_Singleton_UpwardClausure (P : POSET A) (a : A) :
  (ElementUpwardClausure P a) = UpwardClausure P (unitarySet a) := by
  funext
  apply propext
  constructor
  · unfold ElementUpwardClausure UpwardClausure
    simp [unitarySet]
  · unfold ElementUpwardClausure UpwardClausure
    simp [unitarySet]


theorem ElementDownwardClausure_Is_Singleton_DownwardClausure (P : POSET A) (a : A) :
  (ElementDownwardClausure P a) = DownwardClausure P (unitarySet a) := by
  have h := ElementUpwardClausure_Is_Singleton_UpwardClausure (DualPOSET P) a
  rw [ElementDownwardClausure_Is_Dual_ElementUpwardClausure, DownwardClausure_Is_Dual_UpwardClausure]
  exact h
