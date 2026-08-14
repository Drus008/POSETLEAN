import POSET.SubsetTypes.ClosedSubsets.Defs
import POSET.SubsetTypes.ClosedSubsets.Dual
import POSET.Sets.Defs
import POSET.Sets.SetFamilies.Defs

variable {A : Type} (P : POSET A)
local infix:50 " ≤ " => P.rel

theorem UpwardClosure_Is_UpwardClosed (P : POSET A) (S : A → Prop) :
  UpwardClosed P (UpwardClosure P S) := by
  unfold UpwardClosed
  intro a x h h1
  unfold UpwardClosure at h
  obtain ⟨a1, ha1⟩ := h
  unfold UpwardClosure
  have h1 := P.trans a1 a x ha1.right h1
  exact ⟨a1, ha1.left, h1⟩

theorem DownwardClosure_Is_DownwardClosed (P : POSET A) (S : A → Prop) :
  DownwardClosed P (DownwardClosure P S) := by
  have h := UpwardClosure_Is_UpwardClosed (DualPOSET P) S
  rw [DownwardClosure_Is_Dual_UpwardClosure]
  exact Dual_UpwardClosed_Is_DownwardClosed P h

theorem ElementUpwardClosure_Is_Singleton_UpwardClosure (P : POSET A) (a : A) :
  (ElementUpwardClosure P a) = UpwardClosure P (unitarySet a) := by
  funext
  apply propext
  constructor
  · unfold ElementUpwardClosure UpwardClosure
    simp [unitarySet]
  · unfold ElementUpwardClosure UpwardClosure
    simp [unitarySet]


theorem ElementDownwardClosure_Is_Singleton_DownwardClosure (P : POSET A) (a : A) :
  (ElementDownwardClosure P a) = DownwardClosure P (unitarySet a) := by
  have h := ElementUpwardClosure_Is_Singleton_UpwardClosure (DualPOSET P) a
  rw [ElementDownwardClosure_Is_Dual_ElementUpwardClosure, DownwardClosure_Is_Dual_UpwardClosure]
  exact h

theorem UpwardClosure_UpwardClosed_Is_Itself {P : POSET A} {S : A → Prop} (h : UpwardClosed P S) :
  (UpwardClosure P S) = S := by
  funext x
  apply propext
  unfold UpwardClosure
  unfold UpwardClosed at h
  constructor
  · intro h1
    obtain ⟨a, h1⟩ := h1
    exact h a x h1.left h1.right
  · intro h1
    have hx := P.refl x
    exact ⟨x, h1, hx⟩

theorem DownwardClosure_DownwardClosed_Is_Itself {P : POSET A} {S: A → Prop} (h : DownwardClosed P S) :
  (DownwardClosure P S) = S := by
  rw [DownwardClosure_Is_Dual_UpwardClosure]
  have h := DownwardClosed_Is_Dual_UpwardClosed P h
  exact UpwardClosure_UpwardClosed_Is_Itself h


theorem UnionUpwardClosed_Is_UpwardClosed {P : POSET A} {F : Family A} (h : subset F (UpwardClosed P)) :
  UpwardClosed P (UnionF F) := by
  unfold UpwardClosed UnionF
  intro a x hF hx
  have ⟨S,hF,ha⟩ := hF
  have hS := h S hF
  have h := hS a x ha hx
  exact ⟨S,hF,h⟩

theorem UnionDownwardClosed_Is_DownwardClosed {P : POSET A} {F : Family A} (h : subset F (DownwardClosed P)) :
  DownwardClosed P (UnionF F) := by
  apply Dual_UpwardClosed_Is_DownwardClosed
  apply UnionUpwardClosed_Is_UpwardClosed
  intro S hS
  have hS := h S hS
  exact DownwardClosed_Is_Dual_UpwardClosed P hS
