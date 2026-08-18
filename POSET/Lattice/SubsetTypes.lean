import POSET.Lattice.Dual
import POSET.SubsetTypes.ClosedSubsets.Dual
import POSET.SubsetTypes.ClosedSubsets.Subsets
import POSET.Sets.Defs

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
