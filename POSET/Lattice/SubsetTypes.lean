import POSET.Lattice.Dual
import POSET.SubsetTypes.ClosedSubsets.Dual
import POSET.SubsetTypes.ClosedSubsets.Subsets
import POSET.SubsetTypes.ClosedSubsets.Families
import POSET.Sets.Defs
import POSET.Sets.SetFamilies.Basic

variable {A : Type}

theorem UClosed_JoinSemilattice_Is_UDirected {D : A → Prop} {J : JoinSemilattice A} (h : UpwardClosed J.toPOSET D) :
  UDirectedSet J.toPOSET D := by
  intro a b h'
  have ha := J.up1 a b
  have hb := J.up2 a b
  have h' := h a (J.join a b) h'.left ha
  exact ⟨J.join a b, h', ha, hb⟩

theorem DClosed_MeetSemilattice_Is_DDirected {U : A → Prop} {M : MeetSemilattice A} (h : DownwardClosed M.toPOSET U) :
  DDirectedSet M.toPOSET U := by
  apply Dual_UDirectedSet_Is_DDirectedSet
  have h := DownwardClosed_Is_Dual_UpwardClosed M.toPOSET h
  rw [DualPOSET_Meet_Is_POSET_DualMeet] at h
  have h' := UClosed_JoinSemilattice_Is_UDirected h
  rw [← DualPOSET_Meet_Is_POSET_DualMeet] at h'
  exact h'

theorem Universe_JoinSemilattice_Is_UDirected (J : JoinSemilattice A) :
  UDirectedSet J.toPOSET (@universeSet A) := by
  have h := UniversIsUpward J.toPOSET
  exact UClosed_JoinSemilattice_Is_UDirected h

theorem Universe_MeetSemilattice_Is_DDirected (M : MeetSemilattice A) :
  DDirectedSet M.toPOSET (@universeSet A) := by
  have h := UniversIsDownward M.toPOSET
  exact DClosed_MeetSemilattice_Is_DDirected h

theorem Universe_Lattice_Is_UDirected (L : Lattice A) :
  UDirectedSet L.toPOSET (@universeSet A) :=
  Universe_JoinSemilattice_Is_UDirected L.toJoinSemilattice

theorem Universe_Lattice_Is_DDirected (L : Lattice A) :
  DDirectedSet L.toPOSET (@universeSet A) :=
  Universe_MeetSemilattice_Is_DDirected L.toMeetSemilattice

theorem Universe_JoinSemilattice_Is_Ideal (J : JoinSemilattice A) :
  Ideal J.toPOSET (@universeSet A) := ⟨UniversIsDownward J.toPOSET, Universe_JoinSemilattice_Is_UDirected J⟩

theorem Universe_MeetSemilattice_Is_Filter (M : MeetSemilattice A) :
  Filter M.toPOSET (@universeSet A) := ⟨UniversIsUpward M.toPOSET, Universe_MeetSemilattice_Is_DDirected M⟩

theorem Universe_Lattice_Is_Ideal (L : Lattice A) :
  Ideal L.toPOSET (@universeSet A) := Universe_JoinSemilattice_Is_Ideal L.toJoinSemilattice

theorem Universe_Lattice_Is_Filter (L : Lattice A) :
  Filter L.toPOSET (@universeSet A) := Universe_MeetSemilattice_Is_Filter L.toMeetSemilattice

theorem Intersection_Filters_Is_Filter_In_MeetSemilattice {M : MeetSemilattice A} {F : Family A} (h : subset F (Filter M.toPOSET)) :
  Filter M.toPOSET (InterseccionF F) := by
  constructor
  · have h := Family_Filter_Is_Family_UClosed h
    exact IntersectionUClosed_Is_UClosed h
  · intro a b ⟨ha, hb⟩
    exists M.meet a b
    constructor
    · intro S hS
      have ha := ha S hS
      have hb := hb S hS
      have hS := h S hS
      have ⟨cS, hcS, hcab⟩ := hS.right a b ⟨ha, hb⟩
      have hc := M.inf a b cS hcab
      exact hS.left cS (M.meet a b) hcS hc
    · exact ⟨M.down1 a b, M.down2 a b⟩

theorem Intersection_Ideals_Is_Ideal_In_JoinSemilattice (J : JoinSemilattice A) (F : Family A) (h : subset F (Ideal J.toPOSET)) :
  Ideal J.toPOSET (InterseccionF F) := by
  have h : subset F (Filter (DualPOSET J.toPOSET)) := h
  rw [DualPOSET_Join_Is_POSET_DualJoin] at h
  have h := Intersection_Filters_Is_Filter_In_MeetSemilattice h
  rw [← DualPOSET_Join_Is_POSET_DualJoin] at h
  exact Dual_Filter_Is_Ideal J.toPOSET h

section Prime

def PrimeIdeal (M : MeetSemilattice A) (I : A → Prop) : Prop :=
  (Ideal M.toPOSET I) ∧ (proper I) ∧ (∀ x y : A, (I (M.meet x y)) → ((I x) ∨ (I y)))

def PrimeFilter (J : JoinSemilattice A) (F : A → Prop) : Prop :=
  (Filter J.toPOSET F) ∧ (proper F) ∧ (∀ x y : A, (F (J.join x y)) → ((F x) ∨ (F y)))

theorem PrimeIdeal_Is_Dual_PrimeFilter_Meet_Join {M : MeetSemilattice A} {I : A → Prop} (h : PrimeIdeal M I) :
  PrimeFilter (Meet_Is_Dual_Join M) I := by
  have h' := Ideal_Is_Dual_Filter M.toPOSET h.left
  rw [DualPOSET_Meet_Is_POSET_DualMeet] at h'
  exact ⟨h', h.right.left, h.right.right⟩

theorem PrimeFilter_Is_Dual_PrimeIdeal_Meet_Join {J : JoinSemilattice A} {F : A → Prop} (h : PrimeFilter J F) :
  PrimeIdeal (Join_Is_Dual_Meet J) F := by
  have h' := Filter_Is_Dual_Ideal J.toPOSET h.left
  rw [DualPOSET_Join_Is_POSET_DualJoin] at h'
  exact ⟨h', h.right.left, h.right.right⟩

theorem PrimeIdeal_Is_Dual_PrimeFilter {L : Lattice A} {I : A → Prop} (h : PrimeIdeal L I) :
  PrimeFilter (Lattice_Is_Dual_Lattice L) I := PrimeIdeal_Is_Dual_PrimeFilter_Meet_Join h

theorem PrimeFilter_Is_Dual_PrimeIdeal {L : Lattice A} {F : A → Prop} (h : PrimeFilter L F) :
  PrimeIdeal (Lattice_Is_Dual_Lattice L) F := PrimeFilter_Is_Dual_PrimeIdeal_Meet_Join h




end Prime
