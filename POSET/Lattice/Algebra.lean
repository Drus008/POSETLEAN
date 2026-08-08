import POSET.Lattice.ExtremeElements
import POSET.Lattice.Dual
import POSET.ExtremeElements.BasicProp
import POSET.ExtremeElements.Subsets
import POSET.Sets.Basic

variable {A : Type}

theorem Join_Is_Comm (J : JoinSemilattice A) (a b : A) : J.join a b = J.join b a := by
  have h := Join_Is_Sup_Pair J a b
  have h' := Join_Is_Sup_Pair J b a
  rw [PairSet_Is_Comm a b] at h
  exact Sup_Unique h h'

theorem Meet_Is_Comm (M : MeetSemilattice A) (a b : A) : M.meet a b = M.meet b a := by
  let J := Meet_Is_Dual_Join M
  have h1 := Join_Is_Comm J a b
  exact h1

theorem Greater_Is_Join {J : JoinSemilattice A} {a b : A} (h : J.rel a b) : J.join a b = b := by
  have h := Greater_Is_Sup_Pair h
  exact (Sup_Pair_Is_Join h).symm

theorem Lower_Is_Meet {M : MeetSemilattice A} {a b : A} (h : M.rel a b) : M.meet a b = a := by
  have h : (Meet_Is_Dual_Join M).rel b a := h
  have h := Greater_Is_Join h
  rw [Meet_Is_Comm]
  exact h

theorem Join_Idempotent (J : JoinSemilattice A) (a : A) : J.join a a = a := by
  exact Greater_Is_Join (J.refl a)

theorem Meet_Idempotent (M : MeetSemilattice A) (a : A) : M.meet a a = a := by
  exact Lower_Is_Meet (M.refl a)

theorem Max_Is_Absorbent_Join {J : JoinSemilattice A} {M : A} (h : MaxElement J.toPOSET M) (a : A) : J.join M a = M := by
  have h := h a
  rw [Join_Is_Comm]
  exact Greater_Is_Join h

theorem Min_Is_Absorbent_Meet {M : MeetSemilattice A} {m : A} (h : MinElement M.toPOSET m) (a : A) : M.meet m a = m := by
  let J := Meet_Is_Dual_Join M
  have h := Min_Is_Dual_Max h
  have h := @Max_Is_Absorbent_Join A J m h a
  exact h

theorem Absorbent_Join_Is_Max {J : JoinSemilattice A} {M : A} (h : ∀ a : A, J.join a M = M) : MaxElement J.toPOSET M := by
  intro x
  have h' := J.up1 x M
  rw [h x] at h'
  exact h'

theorem Absorbent_Meet_Is_Min {M : MeetSemilattice A} {m : A} (h : ∀ a : A, M.meet a m = m) : MinElement M.toPOSET m := by
  apply Dual_Max_Is_Min
  have h : ∀ a : A, (Meet_Is_Dual_Join M).join a m = m := h
  exact Absorbent_Join_Is_Max h

theorem Max_Is_Identity_Meet {M : MeetSemilattice A} {m : A} (h : MaxElement M.toPOSET m) (a : A) : M.meet m a = a := by
  have h := h a
  rw [Meet_Is_Comm]
  exact Lower_Is_Meet h

theorem Min_Is_Identity_Join {J : JoinSemilattice A} {m : A} (h : MinElement J.toPOSET m) (a : A) : J.join m a = a := by
  let M := Join_Is_Dual_Meet J
  have h := Min_Is_Dual_Max h
  have h := @Max_Is_Identity_Meet A M m h a
  exact h

theorem Identity_Meet_Is_Max {M : MeetSemilattice A} {m : A} (h : ∀ a : A, M.meet m a = a) : MaxElement M.toPOSET m := by
  intro x
  have h' := M.down1 m x
  rw [h x] at h'
  exact h'

theorem Identity_Join_Is_Min {J : JoinSemilattice A} {m : A} (h : ∀ a : A, J.join m a = a) : MinElement J.toPOSET m := by
  apply Dual_Max_Is_Min
  have h : ∀ a : A, (Join_Is_Dual_Meet J).meet m a = a := h
  exact Identity_Meet_Is_Max h

theorem Absortion_Law1 (L : Lattice A) (a b : A) : L.meet a (L.join a b) = a := by
  have h := L.up1 a b
  exact Lower_Is_Meet (M := L.toMeetSemilattice) h

theorem Absortion_Law2 (L : Lattice A) (a b : A) : L.join a (L.meet a b) = a := by
  rw [Join_Is_Comm]
  exact Greater_Is_Join (J := L.toJoinSemilattice) (L.down1 a b)
