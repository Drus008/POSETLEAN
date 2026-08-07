
variable {A : Type}

def UnionS (S1 S2 : A → Prop) (x : A) := (S1 x) ∨ (S2 x)

def IntersectionS (S1 S2 : A → Prop) (x : A) := (S1 x) ∧ (S2 x)
