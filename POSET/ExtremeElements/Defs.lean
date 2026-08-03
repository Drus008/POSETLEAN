import POSET.Basic

variable {A : Type} (P : POSET A)

local infix:50 " ≤ " => P.rel

def MaxElement (M : A) : Prop := ∀ x : A, x ≤ M

def MinElement (m : A) : Prop := ∀ x : A, m ≤ x

def Coatom (c : A) : Prop := ∃ M : A, (MaxElement P M ∧ c ≠ M ∧ (∀ x : A, c ≤ x → (x = c ∨ x = M)))

def Atom (a : A) : Prop := ∃ m : A, (MinElement P m ∧ a ≠ m ∧ (∀ x : A, x ≤ a → (x = a ∨ x = m)))

def MaximalElement (M : A) : Prop := ∀ x : A, M ≤ x → x=M

def MinimalElement (m : A) : Prop := ∀ x : A, x ≤ m → x=m

def UpperBound (U : A) (S : A → Prop) : Prop := ∀ x : A, (S x) → x ≤ U

def LowerBound (L : A) (S : A → Prop) : Prop := ∀ x : A, (S x) → L ≤ x

def Supremum (s : A) (S : A → Prop) : Prop := UpperBound P s S ∧ ∀ U : A, UpperBound P U S → s ≤ U

def Infimum (i : A) (S : A → Prop) : Prop := LowerBound P i S ∧ ∀ L : A, LowerBound P L S → L ≤ i
