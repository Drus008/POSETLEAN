import POSET.SubsetTypes.ClosedSubsets.Defs
import POSET.SubsetTypes.ClosedSubsets.Dual
import POSET.Sets.Defs
import POSET.Sets.SetFamilies.Defs
import POSET.ExtremeElements.BasicProp

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

theorem DownwardClosure_Is_Subset (P : POSET A) (S : A → Prop) :
  subset S (DownwardClosure P S) := by
  intro x h
  exact ⟨x, h, P.refl x⟩

theorem UpwardClosure_Is_Subset (P : POSET A) (S : A → Prop) :
  subset S (UpwardClosure P S) := by
  intro x h
  exact ⟨x, h, P.refl x⟩

theorem UClosure_DDirected_Is_DDirected {P : POSET A} {S : A → Prop} (h : DDirectedSet P S) :
  DDirectedSet P (UpwardClosure P S) := by
  intro a b ⟨⟨a',ha⟩,⟨b',hb⟩⟩
  have ⟨c,hc⟩ := h a' b' ⟨ha.left,hb.left⟩
  have ha := P.trans c a' a hc.right.left ha.right
  have hb := P.trans c b' b hc.right.right hb.right
  have hc := UpwardClosure_Is_Subset P S c hc.left
  exact ⟨c,hc,ha,hb⟩

theorem DClosure_UDirected_Is_UDirected {P : POSET A} {S : A → Prop} (h : UDirectedSet P S) :
  UDirectedSet P (DownwardClosure P S) := by
  have h := UDirectedSet_Is_Dual_DDirectedSet P h
  apply Dual_DDirectedSet_Is_UDirectedSet P
  have h := UClosure_DDirected_Is_DDirected h
  apply h

theorem UClosure_DDirected_Is_Filter {P : POSET A} {S : A → Prop} (h : DDirectedSet P S) :
  Filter P (UpwardClosure P S) :=
  ⟨UpwardClosure_Is_UpwardClosed P S, UClosure_DDirected_Is_DDirected h⟩

theorem DClosure_UDirected_Is_Ideal {P : POSET A} {S : A → Prop} (h : UDirectedSet P S) :
  Ideal P (DownwardClosure P S) :=
  ⟨DownwardClosure_Is_DownwardClosed P S, DClosure_UDirected_Is_UDirected h⟩


section extreme

theorem If_Subset_Has_UBound_Then_Is_UDirected {P : POSET A} {U : A} {S : A → Prop}
  (hU : UpperBound P U S) (hS : S U) : UDirectedSet P S := by
  intro a b ⟨ha, hb⟩
  have ha := hU a ha
  have hb := hU b hb
  exact ⟨U, hS, ha, hb⟩

theorem If_Subset_Has_LBound_Then_Is_DDirected {P : POSET A} {L : A} {S : A → Prop}
  (hL : LowerBound P L S) (hS : S L) : DDirectedSet P S := by
  have hL := LowerBound_Is_Dual_UpperBound hL
  apply Dual_UDirectedSet_Is_DDirectedSet
  exact If_Subset_Has_UBound_Then_Is_UDirected hL hS

theorem If_Subset_Has_Max_Then_Is_UDirected {P : POSET A} {M : A} {S : A → Prop}
  (hM : MaxElement P M) (hS : S M) : UDirectedSet P S := by
  have h := Max_Is_UpperBound hM S
  exact If_Subset_Has_UBound_Then_Is_UDirected h hS

theorem If_Subset_Has_Min_Then_Is_DDirected {P : POSET A} {m : A} {S : A → Prop}
  (hm : MinElement P m) (hS : S m) : DDirectedSet P S := by
  have h := Min_Is_LowerBound hm S
  exact If_Subset_Has_LBound_Then_Is_DDirected h hS
end extreme

section Families

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

end Families
