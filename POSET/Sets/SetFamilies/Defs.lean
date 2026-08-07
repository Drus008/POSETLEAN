

def Family (A : Type) := (A → Prop) → Prop

def UnionF {A : Type} (F : Family A) (x : A) := ∃ S : A → Prop, (F S) ∧ (S x)

def InterseccionF {A : Type} (F : Family A) (x : A) := ∀ S : A → Prop, (F S) → (S x)
