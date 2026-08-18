import POSET.LOSET.Def
import POSET.SubsetTypes.Chain.Defs
import POSET.Lattice.Defs
import POSET.DualOrder
import POSET.Sets.Defs


variable {A : Type}

section dual

def DualLOSET (L : LOSET A) : LOSET A where
  toPOSET := DualPOSET L.toPOSET
  total := by
    intro a b
    exact L.total b a

end dual

section chain

theorem Universe_LOSET_Is_Chain (L : LOSET A) : Chain L.toPOSET (@universeSet A) := by
  unfold Chain
  intro x y h h'
  exact L.total x y

def If_Universe_Is_Chain_Then_Is_LOSET (P : POSET A) (h : Chain P (@universeSet A)) : LOSET A where
  toPOSET := P
  total := by
    intro a b
    exact h a b ⟨⟩ ⟨⟩


end chain

section lattice



end lattice
