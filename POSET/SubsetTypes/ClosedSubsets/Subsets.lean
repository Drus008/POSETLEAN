import POSET.Sets.Defs

import POSET.SubsetTypes.ClosedSubsets.Defs

variable {A : Type} (P : POSET A)
local infix:50 " ≤ " => P.rel

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
