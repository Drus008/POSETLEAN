import POSET.Basic

variable (A : Type) (P : POSET A)

local infix:50 " ≤ " => P.rel

def MaxElement (M : A) : Prop := ∀ x : A, x ≤ M

def MinElement (m : A) : Prop := ∀ x : A, m ≤ x

def MaximalElement (M : A) : Prop := ∀ x : A, M ≤ x → x=M

def MinimalElement (m : A) : Prop := ∀ x : A, x ≤ m → x=m

theorem Max_unique (M1 M2 : A) (h1 : MaxElement A P M1) (h2 : MaxElement A P M2) : M1 = M2
  := by
  have P1 := h1 M2
  have P2 := h2 M1
  exact P.antisym M1 M2 P2 P1
