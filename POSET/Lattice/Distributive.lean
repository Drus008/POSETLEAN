import POSET.Lattice.Algebra

variable {A : Type}


def SimpDistLattice (L : Lattice A)
  (h : ∀ a b c : A , L.meet a (L.join b c) = L.join (L.meet a b) (L.meet a c))
  : DistributiveLattice A where
  toLattice := L
  distMeet := h
  distJoin := by
    intro a b c
    rw [h _ a c]
    simp only [Meet_Lattice_Comm L _ a, Meet_Lattice_Comm L _ c]
    rw [h, h c _ _]
    rw [Join_Associativity L.toJoinSemilattice,← Join_Associativity L.toJoinSemilattice _ _ (L.meet c a)]
    rw [Meet_Lattice_Comm L c a]
    rw [← h, ← h, Absortion_Law1]

def SimpDistLattice2 (L : Lattice A)
  (h : ∀ a b c : A , L.join a (L.meet b c) = L.meet (L.join a b) (L.join a c))
  : DistributiveLattice A := DistLattice_Is_Dual_DistLattice (SimpDistLattice (Lattice_Is_Dual_Lattice L) h)
