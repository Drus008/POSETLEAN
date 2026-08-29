import POSET.Sets.Basic
import POSET.SubsetTypes.ClosedSubsets.Dual

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

theorem EmptyIsDDirected : DDirectedSet P (@emptySet A) := by
  intro a b ⟨ha, hb⟩
  contradiction

theorem EmptyIsUDirected : UDirectedSet P (@emptySet A) := by
  intro a b ⟨ha, hb⟩
  contradiction

theorem EmptyIsFilter : Filter P (@emptySet A) := ⟨EmptyIsUpward P, EmptyIsDDirected P⟩

theorem EmptyIsIdeal : Ideal P (@emptySet A) := ⟨EmptyIsDownward P, EmptyIsUDirected P⟩

theorem UniversIsUpward : UpwardClosed P universeSet := by
  unfold UpwardClosed
  intro x a h
  rw [universeSet]
  intro h
  trivial

theorem UniversIsDownward : DownwardClosed P universeSet := by
  unfold DownwardClosed
  intro x a h
  rw [universeSet]
  intro h
  trivial

theorem Unitary_Is_UDirected (a : A) : UDirectedSet P (unitarySet a) := by
  intro x y ⟨hx, hy⟩
  rw [hx, hy]
  have h := Unitary_Has_Element a
  exists a
  exact ⟨h, P.refl a, P.refl a⟩

theorem Unitary_Is_DDirected (a : A) : DDirectedSet P (unitarySet a) := by
  apply Dual_UDirectedSet_Is_DDirectedSet
  exact Unitary_Is_UDirected (DualPOSET P) a
