import POSET.SubsetTypes.ClosedSubsets.Basic
import POSET.Sets.SetFamilies.Defs
import POSET.Sets.SetPOSET.Defs
import POSET.SubsetTypes.Chain.Defs

variable {A : Type} {P : POSET A} {F : Family A}
local infix:50 " ≤ " => P.rel

theorem UnionUpwardClosed_Is_UpwardClosed (h : subset F (UpwardClosed P)) :
  UpwardClosed P (UnionF F) := by
  unfold UpwardClosed UnionF
  intro a x hF hx
  have ⟨S,hF,ha⟩ := hF
  have hS := h S hF
  have h := hS a x ha hx
  exact ⟨S,hF,h⟩

theorem UnionDownwardClosed_Is_DownwardClosed (h : subset F (DownwardClosed P)) :
  DownwardClosed P (UnionF F) := by
  apply Dual_UpwardClosed_Is_DownwardClosed
  apply UnionUpwardClosed_Is_UpwardClosed
  intro S hS
  have hS := h S hS
  exact DownwardClosed_Is_Dual_UpwardClosed P hS

theorem IntersectionUClosed_Is_UClosed (h : subset F (UpwardClosed P)) :
  UpwardClosed P (InterseccionF F) := by
  intro a x ha hx S hS
  have ha := ha S hS
  have h := h S hS
  exact h a x ha hx

theorem IntersectionDClosed_Is_DClosed (h : subset F (DownwardClosed P)) :
  DownwardClosed P (InterseccionF F) := by
  intro a x ha hx S hS
  have ha := ha S hS
  have h := h S hS
  exact h a x ha hx

theorem Family_Filter_Is_Family_UClosed (h : subset F (Filter P)) :
  subset F (UpwardClosed P) := by
  intro S hS
  unfold subset at h
  exact (h S hS).left

theorem Family_Ideal_Is_Family_DClosed (h : subset F (Ideal P)) :
  subset F (DownwardClosed P) := by
  intro S hS
  unfold subset at h
  exact (h S hS).left

theorem Family_Filter_Is_DDirected (h : subset F (Filter P)) :
  subset F (DDirectedSet P) := by
  intro S hS
  unfold subset at h
  exact (h S hS).right

theorem Family_Ideal_Is_UDirected (h : subset F (Ideal P)) :
  subset F (UDirectedSet P) := by
  intro S hS
  unfold subset at h
  exact (h S hS).right

theorem Union_Chain_Of_UDirected_Is_UDirected (h : subset F (UDirectedSet P))
  (h' : Chain (SetPOSET A) F) : UDirectedSet P (UnionF F) := by
  intro a b ⟨ha,hb⟩
  have ⟨Sa, hSa, ha⟩ := ha
  have ⟨Sb, hSb, hb⟩ := hb
  have h' := h' Sa Sb hSa hSb
  cases h' with
  | inl h' =>
    have ha := h' a ha
    have h := h Sb hSb
    have ⟨c,hc⟩ := h a b ⟨ha, hb⟩
    exists c
    constructor
    · exact ⟨Sb, hSb, hc.left⟩
    · exact hc.right
  | inr h' =>
    have hb := h' b hb
    have h := h Sa hSa
    have ⟨c,hc⟩ := h b a ⟨hb, ha⟩
    exists c
    constructor
    · exact ⟨Sa, hSa, hc.left⟩
    · exact ⟨hc.right.right, hc.right.left⟩

theorem Union_Chain_Of_DDirected_Is_DDirected (h : subset F (DDirectedSet P))
  (h' : Chain (SetPOSET A) F) : DDirectedSet P (UnionF F) := by
  rw [DDirectedSet_Equal_DualUdirectedSet] at h
  have h := Union_Chain_Of_UDirected_Is_UDirected h h'
  exact Dual_UDirectedSet_Is_DDirectedSet P h

theorem Union_Chain_Of_Filter_Is_Filter (h : subset F (Filter P))
  (h' : Chain (SetPOSET A) F) : Filter P (UnionF F) := by
  constructor
  · have h := Family_Filter_Is_Family_UClosed h
    exact UnionUpwardClosed_Is_UpwardClosed h
  · have h := Family_Filter_Is_DDirected h
    exact Union_Chain_Of_DDirected_Is_DDirected h h'

theorem Union_Chain_Of_Ideal_Is_Ideal (h : subset F (Ideal P))
  (h' : Chain (SetPOSET A) F) : Ideal P (UnionF F) := by
  constructor
  · have h := Family_Ideal_Is_Family_DClosed h
    exact UnionDownwardClosed_Is_DownwardClosed h
  · have h := Family_Ideal_Is_UDirected h
    exact Union_Chain_Of_UDirected_Is_UDirected h h'
