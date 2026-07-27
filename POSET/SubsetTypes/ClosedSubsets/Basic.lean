import POSET.SubsetTypes.ClosedSubsets.Defs

variable {A : Type} (P : POSET A)
local infix:50 " ≤ " => P.rel


def emptySet (_ : A) : Prop := False

theorem EmptyIsUpward : UpwardClosed P emptySet := by
  unfold UpwardClosed
  intro a x
  rw [emptySet]
  simp

theorem EmptyIsDownward : DownwardClosed P emptySet := by
  unfold DownwardClosed
  intro a x
  rw [emptySet]
  simp

def universeSet (_ : A) : Prop := True

theorem UniversIsUpward : UpwardClosed P universeSet := by
  unfold UpwardClosed
  intro x a h
  rw [universeSet]
  trivial

theorem UniversIsDownward : DownwardClosed P universeSet := by
  unfold DownwardClosed
  intro x a h
  rw [universeSet]
  trivial
