import POSET.Basic

variable {A : Type} (P : POSET A)

local infix:50 " ≤ " => P.rel

def Convex (C : A → Prop) : Prop := ∀ x a b : A, C a →  C b → a ≤ x → x ≤ b → C x
