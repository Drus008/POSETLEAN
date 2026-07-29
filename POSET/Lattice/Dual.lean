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
