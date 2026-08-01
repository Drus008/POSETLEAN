import POSET.Basic

variable {A : Type}


structure LOSET (A : Type) extends POSET A where
  total : ∀ a b : A, (rel a b) ∨ rel b a
