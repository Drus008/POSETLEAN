import POSET.Basic
import POSET.ExtremeElements.Defs

@[ext]
structure JoinSemilattice (A : Type) extends POSET A where
  join : A → A → A
  up1 : ∀ a b : A, rel a (join a b)
  up2 : ∀ a b : A, rel b (join a b)
  sup : ∀ a b h: A, (rel a h ∧ rel b h) → rel (join a b) h

instance {A : Type} : CoeOut (JoinSemilattice A) (POSET A) := ⟨JoinSemilattice.toPOSET⟩

@[ext]
structure MeetSemilattice (A : Type) extends POSET A where
  meet : A → A → A
  down1 : ∀ a b : A, rel (meet a b) a
  down2 : ∀ a b : A, rel (meet a b) b
  inf : ∀ a b h: A, (rel h a ∧ rel h b) → rel h (meet a b)

instance {A : Type} : CoeOut (MeetSemilattice A) (POSET A) := ⟨MeetSemilattice.toPOSET⟩

@[ext]
structure Lattice (A : Type) extends (JoinSemilattice A), (MeetSemilattice A)

instance {A : Type} : CoeOut (Lattice A) (MeetSemilattice A) := ⟨Lattice.toMeetSemilattice⟩
instance {A : Type} : CoeOut (Lattice A) (JoinSemilattice A) := ⟨Lattice.toJoinSemilattice⟩

theorem Lattice_POSET_Meet {A : Type} (L : Lattice A) : L.toPOSET = L.toMeetSemilattice.toPOSET := by trivial
theorem Lattice_POSET_Join {A : Type} (L : Lattice A) : L.toPOSET = L.toJoinSemilattice.toPOSET := by trivial


@[ext]
structure DistributiveLattice (A : Type) extends (Lattice A) where
  distMeet : ∀ a b c : A, meet a (join b c) = join (meet a b) (meet a c)
  distJoin : ∀ a b c : A, join a (meet b c) = meet (join a b) (join a c)

def Disjoints {A : Type} (M : MeetSemilattice A) (a b : A) := MinElement M (M.meet a b)

def CoDisjoints {A : Type} (J : JoinSemilattice A) (a b : A) := MaxElement J (J.join a b)

def Complementaries {A : Type} (L : Lattice A) (a b : A)  := (Disjoints L a b) ∧ (CoDisjoints L a b)
