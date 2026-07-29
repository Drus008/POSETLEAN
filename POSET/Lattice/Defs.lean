import POSET.Basic


structure JoinSemilattice (A : Type) extends POSET A where
  join : A → A → A
  up1 : ∀ a b : A, rel a (join a b)
  up2 : ∀ a b : A, rel b (join a b)
  sup : ∀ a b h: A, (rel a h ∧ rel b h) → rel (join a b) h

structure MeetSemilattice (A : Type) extends POSET A where
  meet : A → A → A
  down1 : ∀ a b : A, rel (meet a b) a
  down2 : ∀ a b : A, rel (meet a b) b
  inf : ∀ a b h: A, (rel h a ∧ rel h b) → rel h (meet a b)

structure Lattice (A : Type) extends (JoinSemilattice A), (MeetSemilattice A)
