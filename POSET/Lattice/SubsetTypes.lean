import POSET.Lattice.Algebra
import POSET.SubsetTypes.ClosedSubsets.Dual
import POSET.SubsetTypes.ClosedSubsets.Subsets
import POSET.SubsetTypes.ClosedSubsets.Families
import POSET.Sets.Defs
import POSET.Sets.SetFamilies.Basic
import POSET.Sets.Algebra.Basic
import POSET.Logic

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

theorem UClosed_Contains_Joins_L {J : JoinSemilattice A} {S : A → Prop} {a b : A}
  (hU : UpwardClosed J S) (ha : S a) : S (J.join a b) := by
  have h := J.up1 a b
  exact hU a _ ha h

theorem DClosed_Contains_Meets_L {M : MeetSemilattice A} {S : A → Prop} {a b : A}
  (hD : DownwardClosed M S) (ha : S a) : S (M.meet a b) := by
  have h := M.down1 a b
  exact hD a _ ha h

theorem UClosed_Contains_Joins_R {L : Lattice A} {S : A → Prop} {a b : A}
  (hU : UpwardClosed L S) (hb : S b) : S (L.join a b) := by
  rw [Join_Is_Comm]
  exact UClosed_Contains_Joins_L hU hb

theorem DClosed_Contains_Meets_R {M : MeetSemilattice A} {S : A → Prop} {a b : A}
  (hD : DownwardClosed M S) (hb : S b) : S (M.meet a b) := by
  rw [Meet_Is_Comm]
  exact DClosed_Contains_Meets_L hD hb

theorem Filter_Contains_Meets {M : MeetSemilattice A} {F : A → Prop} {a b : A}
  (hF : Filter M F) (ha : F a) (hb : F b) : F (M.meet a b) := by
  have ⟨c,hcF, hcab⟩ := hF.right a b ⟨ha,hb⟩
  have hc := M.inf a b c hcab
  exact hF.left c _ hcF hc

theorem Ideal_Contains_Joins {J : JoinSemilattice A} {I : A → Prop} {a b : A}
  (hI : Ideal J I) (ha : I a) (hb : I b) : I (J.join a b) := by
  have ⟨c,hcF, hcab⟩ := hI.right a b ⟨ha,hb⟩
  have hc := J.sup a b c hcab
  exact hI.left c _ hcF hc

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



theorem PrimeIdeal_Is_Dual_PrimeFilter {M : MeetSemilattice A} {I : A → Prop} (h : PrimeIdeal M I) :
  PrimeFilter (Meet_Is_Dual_Join M) I := by
  have h' := Ideal_Is_Dual_Filter M.toPOSET h.left
  rw [DualPOSET_Meet_Is_POSET_DualMeet] at h'
  exact ⟨h', h.right.left, h.right.right⟩

theorem PrimeFilter_Is_Dual_PrimeIdeal {J : JoinSemilattice A} {F : A → Prop} (h : PrimeFilter J F) :
  PrimeIdeal (Join_Is_Dual_Meet J) F := by
  have h' := Filter_Is_Dual_Ideal J.toPOSET h.left
  rw [DualPOSET_Join_Is_POSET_DualJoin] at h'
  exact ⟨h', h.right.left, h.right.right⟩

theorem Dual_PrimeIdeal_Is_Filter {J : JoinSemilattice A} {F : A → Prop} (h : PrimeIdeal (Join_Is_Dual_Meet J) F) :
  PrimeFilter J F := by
  trivial

theorem Dual_PrimeFilter_Is_Ideal {M : MeetSemilattice A} {I : A → Prop} (h : PrimeFilter (Meet_Is_Dual_Join M) I) :
  PrimeIdeal M I := by
  trivial

theorem If_Complementary_Proper_Ideal_Is_Filter_Then_Is_PrimeFilter {M : MeetSemilattice A} {I : A → Prop}
  (h : Ideal M I) (h' : proper I) (hF : Filter M (Complementary I)) :
  PrimeIdeal M I := by
  refine ⟨?_, ?_, ?_⟩
  · exact h
  · exact h'
  · intro x y
    apply Classical.byContradiction
    intro h''
    have ⟨hI, hxy⟩ := neg_implication_elim h''
    have ⟨hx,hy⟩ := not_or_elim hxy
    have h := Filter_Contains_Meets hF hx hy
    exact h hI

theorem If_Complementary_Proper_Filter_Is_Ideal_Then_Is_PrimeIdeal {J : JoinSemilattice A} {F : A → Prop}
  (h : Filter J F) (h' : proper F) (hI : Ideal J (Complementary F)) :
  PrimeFilter J F := by
  apply Dual_PrimeIdeal_Is_Filter
  have hI := Ideal_Is_Dual_Filter J.toPOSET hI
  have h := Filter_Is_Dual_Ideal J.toPOSET h
  exact If_Complementary_Proper_Ideal_Is_Filter_Then_Is_PrimeFilter h h' hI

theorem Complementary_PrimeIdeal_Is_Filter {M : MeetSemilattice A} {I : A → Prop}
  (hI : PrimeIdeal M I) : Filter M (Complementary I) := by
  constructor
  · exact Complementart_DClosed_Is_UClosed hI.left.left
  · intro x y ⟨hx, hy⟩
    exists M.meet x y
    constructor
    · intro h
      have h := hI.right.right x y h
      cases h with
      | inl h =>
        exact hx h
      | inr h =>
        exact hy h
    · exact ⟨M.down1 x y, M.down2 x y⟩

theorem Complementary_PrimeFilter_Is_Ideal {J : JoinSemilattice A} {F : A → Prop}
  (hF : PrimeFilter J F) : Ideal J (Complementary F) := by
  apply Dual_Filter_Is_Ideal
  have hF := PrimeFilter_Is_Dual_PrimeIdeal hF
  exact Complementary_PrimeIdeal_Is_Filter hF

theorem Complementary_PrimeIdeal_Is_PrimeFilter {L : Lattice A} {I : A → Prop}
  (hI : PrimeIdeal L I) : PrimeFilter L (Complementary I) := by
  constructor
  · exact Complementary_PrimeIdeal_Is_Filter hI
  · constructor
    · exact Complementary_Proper_Is_Proper hI.right.left
    · intro x y h
      apply Classical.byContradiction
      intro h'
      have h' := not_or_elim h'
      have h' : (Complementary (Complementary I)) x ∧ (Complementary (Complementary I)) y := h'
      rw [← Double_Complement I] at h'
      have h' := Ideal_Contains_Joins hI.left h'.left h'.right
      exact h h'

theorem Complementary_PrimeFilter_Is_PrimeIdeal {L : Lattice A} {F : A → Prop}
  (hF : PrimeFilter L F) : PrimeIdeal L (Complementary F) := by
  apply Dual_PrimeFilter_Is_Ideal
  have hF := PrimeFilter_Is_Dual_PrimeIdeal hF
  rw [← Dual_Lattice_Meet_Is_Dual_Join] at hF
  exact Complementary_PrimeIdeal_Is_PrimeFilter hF

end Prime
