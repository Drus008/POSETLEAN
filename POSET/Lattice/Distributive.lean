import POSET.Lattice.Algebra

variable {A : Type}

def DistJoin (J : JoinSemilattice A) : Prop := ∀ a b c : A, J.rel c (J.join a b) →
∃ a' b' : A, (J.rel a' a) ∧ (J.rel b' b) ∧ (c = J.join a' b')

def DistMeet (M : MeetSemilattice A) : Prop := ∀ a b c : A, M.rel (M.meet a b) c →
∃ a' b' : A, (M.rel a a') ∧ (M.rel b b') ∧ (c = M.meet a' b')

theorem DistJoin_Is_Dual_DistMeet {J : JoinSemilattice A} (h : DistJoin J) :
  DistMeet (Join_Is_Dual_Meet J) := by
  trivial

theorem DistMeet_Is_Dual_DistJoin {M : MeetSemilattice A} (h : DistMeet M) :
  DistJoin (Meet_Is_Dual_Join M) := by
  trivial


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

theorem DistLemaMeet (L : DistributiveLattice A) : DistMeet L.toMeetSemilattice := by
  intro a b c h
  exists (L.join a c)
  exists (L.join b c)
  simp []
  simp [] at h
  constructor
  · exact L.up1 a c
  · constructor
    · exact L.up1 b c
    · rw [Join_Is_Comm, Join_Is_Comm L.toJoinSemilattice b c]
      rw [← L.distJoin]
      have h' := L.up1 c (L.meet a b)
      have h := L.sup c (L.meet a b) c ⟨(L.refl c), h⟩
      exact L.antisym c _ h' h

theorem DistLemaJoin (L : DistributiveLattice A) : DistJoin L.toJoinSemilattice :=
  DistLemaMeet (DistLattice_Is_Dual_DistLattice L)
