

def Family (A : Type) := (A → Prop) → Prop

def PowerSet {A : Type} (_ : A → Prop) := True

def UnionF {A : Type} (F : Family A) (x : A) := ∃ S : A → Prop, (F S) ∧ (S x)

def InterseccionF {A : Type} (F : Family A) (x : A) := ∀ S : A → Prop, (F S) → (S x)
