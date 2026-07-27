import POSET.Basic

variable {A : Type} (P : POSET A)
local infix:50 " ≤ " => P.rel

def UpwardClosed (S : A → Prop) : Prop :=
  ∀ a x : A, (S a) ∧ (a ≤ x) → (S x)

def DownwardClosed (S : A → Prop) : Prop :=
  ∀ a x : A, (S a) ∧ (x ≤ a) → (S x)

def ElementUpwardClausure (a : A) (x : A) : Prop := a ≤ x

def ElementDownwardClausure (a : A) (x : A) : Prop := x ≤ a

def UpwardClausure (S : A → Prop) (x : A) : Prop :=
  ∃ a : A, (S a) ∧ (a ≤ x)

def DownClausure (S : A → Prop) (x : A) : Prop :=
  ∃ a : A, (S a) ∧ (x ≤ a)
