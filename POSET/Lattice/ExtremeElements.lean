import POSET.ExtremeElements.BasicProp
import POSET.Lattice.Basic

variable {A : Type}

theorem Max_Is_Absorbent_Join {J : JoinSemilattice A} {M : A} (h : MaxElement J.toPOSET M) (a : A) : J.join M a = M := by
  have h := h a
  rw [Join_Is_Comm]
  exact Greater_Is_Join h

theorem Min_Is_Absorbent_Meet {M : MeetSemilattice A} {m : A} (h : MinElement M.toPOSET m) (a : A) : M.meet m a = m := by
  let J := Meet_Is_Dual_Join M
  have h := Min_Is_Dual_Max h
  have h := @Max_Is_Absorbent_Join A J m h a
  exact h

theorem Max_Is_Identity_Meet {M : MeetSemilattice A} {m : A} (h : MaxElement M.toPOSET m) (a : A) : M.meet m a = a := by
  have h := h a
  rw [Meet_Is_Comm]
  exact Lower_Is_Meet h

theorem Min_Is_Identity_Meet {J : JoinSemilattice A} {m : A} (h : MinElement J.toPOSET m) (a : A) : J.join m a = a := by
  let M := Join_Is_Dual_Meet J
  have h := Min_Is_Dual_Max h
  have h := @Max_Is_Identity_Meet A M m h a
  exact h
