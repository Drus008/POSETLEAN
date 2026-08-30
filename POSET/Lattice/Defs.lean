import POSET.Basic

@[ext]
structure JoinSemilattice (A : Type) extends POSET A where
  join : A → A → A
  up1 : ∀ a b : A, rel a (join a b)
  up2 : ∀ a b : A, rel b (join a b)
  sup : ∀ a b h: A, (rel a h ∧ rel b h) → rel (join a b) h

@[ext]
structure MeetSemilattice (A : Type) extends POSET A where
  meet : A → A → A
  down1 : ∀ a b : A, rel (meet a b) a
  down2 : ∀ a b : A, rel (meet a b) b
  inf : ∀ a b h: A, (rel h a ∧ rel h b) → rel h (meet a b)

@[ext]
structure Lattice (A : Type) extends (JoinSemilattice A), (MeetSemilattice A)

instance : Coe (Lattice A) (MeetSemilattice A) := ⟨Lattice.toMeetSemilattice⟩
instance : Coe (Lattice A) (JoinSemilattice A) := ⟨Lattice.toJoinSemilattice⟩

@[ext]
structure DistributiveLattice (A : Type) extends (Lattice A) where
  distMeet : ∀ a b c : A, meet a (join b c) = join (meet a b) (meet a c)
  distJoin : ∀ a b c : A, join a (meet b c) = meet (join a b) (join a c)
