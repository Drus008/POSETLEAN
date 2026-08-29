import POSET.Basic

variable {A : Type} (P : POSET A)
local infix:50 " ≤ " => P.rel

def UpwardClosed (S : A → Prop) : Prop :=
  ∀ a x : A, (S a) → (a ≤ x) → (S x)

def DownwardClosed (S : A → Prop) : Prop :=
  ∀ a x : A, (S a) → (x ≤ a) → (S x)

def ElementUpwardClosure (a : A) (x : A) : Prop := a ≤ x

def ElementDownwardClosure (a : A) (x : A) : Prop := x ≤ a

def UpwardClosure (S : A → Prop) (x : A) : Prop :=
  ∃ a : A, (S a) ∧ (a ≤ x)

def DownwardClosure (S : A → Prop) (x : A) : Prop :=
  ∃ a : A, (S a) ∧ (x ≤ a)

def UDirectedSet (S : A → Prop) : Prop :=
  ∀ a b : A, ((S a) ∧ (S b)) →  ∃ c : A, (S c) ∧ (a ≤ c) ∧ (b ≤ c)

def DDirectedSet (S : A → Prop) : Prop :=
  ∀ a b : A, ((S a) ∧ (S b)) → ∃ c : A, (S c) ∧ (c ≤ a) ∧ (c ≤ b)

-- Maybe It should be added that the set isn't empty
def Ideal (S : A → Prop) : Prop := (DownwardClosed P S) ∧ (UDirectedSet P S)

def Filter (S : A → Prop) : Prop := (UpwardClosed P S) ∧ (DDirectedSet P S)
