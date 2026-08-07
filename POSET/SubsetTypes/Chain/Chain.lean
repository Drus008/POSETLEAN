import POSET.Basic

variable {A : Type} {P : POSET A}

local infix:50 " ≤ " => P.rel


def Chain (C : A → Prop) : Prop := ∀ x y : A, C x → C y → (x ≤ y ∨ y ≤ x)

def AntiChain (aC : A → Prop) : Prop := ∀ x y : A, x ≠ y → aC x → aC y → (¬ x ≤ y ∧ ¬ y ≤ x)
