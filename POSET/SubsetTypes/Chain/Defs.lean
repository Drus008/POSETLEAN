import POSET.Basic

variable {A : Type}


def Chain (P : POSET A) (C : A → Prop) : Prop := ∀ x y : A, C x → C y → (P.rel x y ∨ P.rel y x)

def AntiChain (P : POSET A) (aC : A → Prop) : Prop := ∀ x y : A, x ≠ y → aC x → aC y → (¬ P.rel x y ∧ ¬ P.rel y x)
