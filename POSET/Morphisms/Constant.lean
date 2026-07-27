import POSET.Morphisms.Defs

variable {A B : Type} (P1 : POSET A) (P2 : POSET B) (c : B)

local infix:50 " ≤1 " => P1.rel
local infix:50 " ≤2 " => P2.rel


def constMonotone : Monotone P1 P2 where
  app := λ x => c
  mon := by
    intro x y h
    exact P2.refl c

theorem const_Is_Increassing : Increasing P2 (λ _ : B => c) := by
  unfold Increasing
  intro x y h1
  simp
  exact P2.refl c

theorem const_Is_Decreasing : Decreasing P2 (λ _ : B => c) := by
  unfold Decreasing
  intro x y h1
  simp
  exact P2.refl c
