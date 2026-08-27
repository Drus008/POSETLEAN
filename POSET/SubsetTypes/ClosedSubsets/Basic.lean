import POSET.SubsetTypes.ClosedSubsets.Defs
import POSET.SubsetTypes.ClosedSubsets.Dual
import POSET.Sets.Basic
import POSET.Sets.SetPOSET.ExtremeElements
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

theorem If_UClosure_Is_DDirected_Then_Is_DDirected {P : POSET A} {S : A → Prop}
  (h : DDirectedSet P (UpwardClosure P S)) : DDirectedSet P S := by
  intro a b ⟨ha,hb⟩
  have ha := UpwardClosure_Is_Subset P S a ha
  have hb := UpwardClosure_Is_Subset P S b hb
  have ⟨c',hc'⟩ := h a b ⟨ha,hb⟩
  have ⟨c, hc⟩ := hc'.left
  have ha := P.trans c c' a hc.right hc'.right.left
  have hb := P.trans c c' b hc.right hc'.right.right
  exact ⟨c, hc.left, ha, hb⟩

theorem If_DClosure_Is_UDirected_Then_Is_UDirected {P : POSET A} {S : A → Prop}
  (h : UDirectedSet P (DownwardClosure P S)) : UDirectedSet P S := by
  have h := UDirectedSet_Is_Dual_DDirectedSet P h
  rw [DownwardClosure_Is_Dual_UpwardClosure] at h
  have h := If_UClosure_Is_DDirected_Then_Is_DDirected h
  exact Dual_DDirectedSet_Is_UDirectedSet P h

theorem If_UClosure_Is_Filter_Then_Is_DDirected {P : POSET A} {S : A → Prop}
  (h : Filter P (UpwardClosure P S)) : DDirectedSet P S :=
  If_UClosure_Is_DDirected_Then_Is_DDirected h.right

theorem If_DClosure_Is_Ideal_Then_Is_UDirected {P : POSET A} {S : A → Prop}
  (h : Ideal P (DownwardClosure P S)) : UDirectedSet P S :=
  If_DClosure_Is_UDirected_Then_Is_UDirected h.right

section extreme

theorem If_DClosed_Has_Max_Then_Is_Universe {P : POSET A} {M : A} {S : A → Prop}
  (hM : MaxElement P M) (hS : DownwardClosed P S) (hSM : S M) : S = @universeSet A := by
  apply SubsetAntisymetric
  · exact Universe_Is_Max A S
  · intro x _
    have hx := hM x
    exact hS M x hSM hx

theorem If_UClosed_Has_Min_Then_Is_Universe {P : POSET A} {m : A} {S : A → Prop}
  (hm : MinElement P m) (hS : UpwardClosed P S) (hSm : S m) : S = @universeSet A := by
  have hm := Min_Is_Dual_Max hm
  have mS := UpwardClosed_Is_Dual_DownwardClosed P hS
  exact If_DClosed_Has_Max_Then_Is_Universe hm hS hSm

theorem NoEmpty_UClosed_Has_Max {P : POSET A} {M a : A} {U : A → Prop}
  (hM : MaxElement P M) (hU : UpwardClosed P U) (ha : U a) :
  U M := by
  have h := hM a
  exact hU a M ha h

theorem NoEmpty_DClosed_Has_Min {P : POSET A} {m a : A} {D : A → Prop}
  (hm : MinElement P m) (hD : DownwardClosed P D) (ha : D a) :
  D m := by
  exact hD a m ha (hm a)

theorem UBound_Is_UBound_DClousure {P : POSET A} {u : A} {S : A → Prop}
  (h : UpperBound P u S) : UpperBound P u (DownwardClosure P S) := by
  intro x hx
  have ⟨x', hx', hx⟩ := hx
  have hu := h x' hx'
  exact P.trans x x' u hx hu

theorem LBound_Is_LBound_UClosure {P : POSET A} {l : A} {S : A → Prop}
  (h : LowerBound P l S) : LowerBound P l (UpwardClosure P S) := by
  rw [UpwardClosure_Is_Dual_DownwardClosure P S]
  have h := LowerBound_Is_Dual_UpperBound h
  have h := UBound_Is_UBound_DClousure h
  exact Dual_UpperBound_Is_LowerBound h

theorem UBound_DClousure_Is_UBound {P : POSET A} {u : A} {S : A → Prop}
  (h : UpperBound P u (DownwardClosure P S)) : UpperBound P u S := by
  intro x hx
  have hx := DownwardClosure_Is_Subset P S x hx
  exact h x hx

theorem LBound_UClosure_Is_LBound {P : POSET A} {l : A} {S : A → Prop}
  (h : LowerBound P l (UpwardClosure P S)) : LowerBound P l S := by
  intro x hx
  have hx := UpwardClosure_Is_Subset P S x hx
  exact h x hx

theorem Sup_Is_Sup_DClosure {P : POSET A} {s : A} {S : A → Prop}
  (hs : Supremum P s S) : Supremum P s (DownwardClosure P S) := by
  constructor
  · exact UBound_Is_UBound_DClousure hs.left
  · intro U h
    have h := UBound_DClousure_Is_UBound h
    exact hs.right U h

theorem Inf_Is_Inf_UClosure {P : POSET A} {i : A} {S : A → Prop}
  (hi : Infimum P i S) : Infimum P i (UpwardClosure P S) := by
  rw [UpwardClosure_Is_Dual_DownwardClosure]
  have h := Infimum_Is_Dual_Supremum hi
  apply Dual_Supremum_Is_Infimum
  exact Sup_Is_Sup_DClosure h


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

theorem IntersectionUClosed_Is_UClosed {P : POSET A} {F : Family A}
  (h : subset F (UpwardClosed P)) : UpwardClosed P (InterseccionF F) := by
  intro a x ha hx S hS
  have ha := ha S hS
  have h := h S hS
  exact h a x ha hx

theorem IntersectionDClosed_Is_DClosed {P : POSET A} {F : Family A}
  (h : subset F (DownwardClosed P)) : DownwardClosed P (InterseccionF F) := by
  intro a x ha hx S hS
  have ha := ha S hS
  have h := h S hS
  exact h a x ha hx

theorem Family_Filter_Is_Family_UClosed {P : POSET A} {F : Family A}
  (h : subset F (Filter P)) : subset F (UpwardClosed P) := by
  intro S hS
  unfold subset at h
  exact (h S hS).left

theorem Family_Ideal_Is_Family_DClosed {P : POSET A} {F : Family A}
  (h : subset F (Ideal P)) : subset F (DownwardClosed P) := by
  intro S hS
  unfold subset at h
  exact (h S hS).left

theorem Family_Filter_Is_DDirected {P : POSET A} {F : Family A}
  (h : subset F (Filter P)) : subset F (DDirectedSet P) := by
  intro S hS
  unfold subset at h
  exact (h S hS).right

theorem Family_Ideal_Is_UDirected {P : POSET A} {F : Family A}
  (h : subset F (Ideal P)) : subset F (UDirectedSet P) := by
  intro S hS
  unfold subset at h
  exact (h S hS).right

end Families
