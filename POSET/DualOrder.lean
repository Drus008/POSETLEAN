import POSET.Basic

variable {A : Type} (P : POSET A)

def DualPOSET : POSET A where
  rel := fun (x y : A) => P.rel y x
  refl := by
    intro a
    exact P.refl a
  antisym := by
    intro a b
    have h := P.antisym b a
    intro h1 h2
    have h3 : b=a := h h1 h2
    exact h3.symm
  trans := by
    intro a b c
    have h := P.trans c b a
    intro h1 h2
    have h3 := h h2 h1
    exact h3

theorem Dual_Dual_Is_OG : DualPOSET (DualPOSET P) = P := by
  ext x y
  unfold DualPOSET
  dsimp
  rfl
