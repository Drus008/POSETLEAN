variable {A B C : Type}

def emptySet (_ : A) : Prop := False

def universeSet (_ : A) : Prop := True

def unitarySet (a : A) (x : A) : Prop := x = a

def pairSet (a b : A) (x : A) : Prop := x = a ∨ x = b

def subset (S1 S2 : A → Prop) : Prop := ∀ x : A, (S1 x) → (S2 x)

def proper (S : A → Prop) : Prop := ∃ x y : A, (S x) ∧ (¬ S y)

def SetOperation (op : A → B → C) (SA : A → Prop) (SB : B → Prop) (c : C) :=
  ∃ a : A, ∃ b : B, (SA a) ∧ (SB b) ∧ (c = op a b)
