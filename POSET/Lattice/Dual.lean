import POSET.Lattice.Defs
import POSET.DualOrder

variable {A : Type}

def Meet_Is_Dual_Join (M : MeetSemilattice A) : JoinSemilattice A where
  toPOSET := (DualPOSET M.toPOSET)
  join := M.meet
  up1 := M.down1
  up2 := M.down2
  sup := M.inf

def Join_Is_Dual_Meet (J : JoinSemilattice A) : MeetSemilattice A where
  toPOSET := (DualPOSET J.toPOSET)
  meet := J.join
  down1 := J.up1
  down2 := J.up2
  inf := J.sup

theorem DualPOSET_Join_Is_POSET_DualJoin (J : JoinSemilattice A) :
  (DualPOSET J.toPOSET) = (Join_Is_Dual_Meet J).toPOSET := rfl

theorem DualPOSET_Meet_Is_POSET_DualMeet (M : MeetSemilattice A) :
  (DualPOSET M.toPOSET) = (Meet_Is_Dual_Join M).toPOSET := rfl

theorem Dual_Meet_Is_Join (M : MeetSemilattice A) : ∃ J : JoinSemilattice A, M = Join_Is_Dual_Meet J := by
  refine ⟨Meet_Is_Dual_Join M, ?_⟩
  rcases M with ⟨P, meet, down1, down2, inf⟩
  dsimp [Join_Is_Dual_Meet, Meet_Is_Dual_Join]
  simp only [Dual_Dual_Is_OG P]


theorem Dual_Joint_Is_Meet (J : JoinSemilattice A) : ∃ M : MeetSemilattice A, J = Meet_Is_Dual_Join M := by
  refine ⟨Join_Is_Dual_Meet J, ?_⟩
  rcases J with ⟨P, join, up1, up2, sup⟩
  dsimp [Join_Is_Dual_Meet, Meet_Is_Dual_Join]
  simp only [Dual_Dual_Is_OG P]

def Lattice_Is_Dual_Lattice (L : Lattice A) : Lattice A where
  toJoinSemilattice := Meet_Is_Dual_Join L.toMeetSemilattice
  meet := L.join
  down1 := (Join_Is_Dual_Meet L.toJoinSemilattice).down1
  down2 := (Join_Is_Dual_Meet L.toJoinSemilattice).down2
  inf := (Join_Is_Dual_Meet L.toJoinSemilattice).inf

theorem Dual_Lattice_Meet_Is_Dual_Join (L : Lattice A) : (Lattice_Is_Dual_Lattice L).toMeetSemilattice = Join_Is_Dual_Meet L.toJoinSemilattice := by
  rfl

def DistLattice_Is_Dual_DistLattice (L : DistributiveLattice A) : DistributiveLattice A where
  toLattice := Lattice_Is_Dual_Lattice L.toLattice
  distJoin := L.distMeet
  distMeet := L.distJoin


theorem Disjoints_Is_Dual_CoDisjoints (M : MeetSemilattice A) :
  Disjoints M = CoDisjoints (Meet_Is_Dual_Join M) := rfl

theorem CoDisjoints_Is_Dual_Disjoints (J : JoinSemilattice A) :
  CoDisjoints J = Disjoints (Join_Is_Dual_Meet J) := rfl

theorem Complementaries_Is_Dual_Complementaries (L : Lattice A) :
  Complementaries L = Complementaries (Lattice_Is_Dual_Lattice L) := by
  ext a b
  constructor
  · intro h
    constructor
    · have h := h.right
      trivial
    · have h := h.left
      trivial
  · intro h
    constructor
    · have h := h.right
      trivial
    · have h := h.left
      trivial
