import POSET.Lattice.Defs
import POSET.Basic

variable {A : Type}

--def SubMeetSemilattice {M : MeetSemilattice A} {S : A → Prop}
--  (hM : ∀ x y : A, ((S x) ∧ (S y)) → (S (M.meet x y))) : MeetSemilattice {a : A // S a} where
--  toPOSET := SubPOSET S M.toPOSET
--  meet := λ a b => ⟨M.meet a.val b.val, hM a.val b.val ⟨a.property, b.property⟩⟩
--  down1 := by
--    intro a b
--    exact M.down1 a.val b.val
--  down2 := by
--    intro a b
--    exact M.down2 a.val b.val
--  inf := by
--    intro a b H h
