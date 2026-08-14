import POSET.Morphisms.Defs
import POSET.Lattice.Defs
import POSET.Lattice.Algebra

variable {A B : Type} (L1 : Lattice A) (L2 : Lattice B)


structure LatticeHomo where
  app : A → B
  fMeet : ∀ x y : A, app (L1.meet x y) = L2.meet (app x) (app y)
  fJoin : ∀ x y : A, app (L1.join x y) = L2.join (app x) (app y)

instance : CoeFun (LatticeHomo L1 L2) (fun _ => A → B) where
  coe f := f.app

section basic

def LatticeHomo_Is_Monotone (f : LatticeHomo L1 L2) : Monotone L1.toPOSET L2.toPOSET where
  app := f.app
  mon := by
    intro x y h
    have h := Greater_Is_Join h
    have h' := f.fJoin x y
    rw [h] at h'
    have h'' := L2.up1 (f.app x) (f.app y)
    rw [← h'] at h''
    exact h''


end basic
