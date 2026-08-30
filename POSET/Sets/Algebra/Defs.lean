
variable {A : Type}

def UnionS (S1 S2 : A → Prop) (x : A) := (S1 x) ∨ (S2 x)

def IntersectionS (S1 S2 : A → Prop) (x : A) := (S1 x) ∧ (S2 x)

def Complementary (S1 : A → Prop) (x : A) := ¬ (S1 x)

def Disjoint (S1 S2 : A → Prop) : Prop := ∀ x : A, ¬(S1 x ∧ S2 x)
