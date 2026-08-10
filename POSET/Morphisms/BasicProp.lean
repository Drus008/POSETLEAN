import POSET.Morphisms.Defs
import POSET.DualOrder
import POSET.Sets.Maps.Defs

variable {A : Type} {P : POSET A}

theorem InternalMonotone_Is_Increasing (f : Monotone P P) : Increasing P f := by
    unfold Increasing
    exact f.mon

def Increasing_Is_Monotone {f : A → A} (h : Increasing P f) : Monotone P P where
    app := f
    mon := h

theorem DualMonotone_Is_Decreasing (f : Monotone P (DualPOSET P)) : Decreasing P f := by
    unfold Decreasing
    have h := f.mon
    unfold DualPOSET at h
    dsimp at h
    exact h

def Decreasing_Is_DualMonotone {f : A → A} (h : Decreasing P f) : Monotone P (DualPOSET P) where
    app := f
    mon := h



section

variable {B : Type} {P' : POSET B}

def Monotone_Is_DualMonotone (f : Monotone P P') : Monotone (DualPOSET P) (DualPOSET P') where
    app := f
    mon := by
        have h := f.mon
        unfold DualPOSET
        dsimp
        intro x y
        exact h y x

def DualMonotone_Is_Monotone (f : Monotone (DualPOSET P) (DualPOSET P')) : Monotone P P' := by
    have h := Monotone_Is_DualMonotone f
    rw [Dual_Dual_Is_OG P, Dual_Dual_Is_OG P'] at h
    exact h

theorem Increasing_Is_Increasing_Dual {f : A → A} (h : Increasing P f) : Increasing (DualPOSET P) f := by
    let M1 := Increasing_Is_Monotone h
    let M2 := Monotone_Is_DualMonotone M1
    have h2 := InternalMonotone_Is_Increasing M2
    exact h2

theorem Decreasing_Is_Decreasing_Dual {f : A → A} (h : Decreasing P f) : Decreasing (DualPOSET P) f := by
    let M1 := Decreasing_Is_DualMonotone h
    let M2 := Monotone_Is_DualMonotone M1
    have h2 := DualMonotone_Is_Decreasing M2
    exact h2


theorem Reflecting_Is_Injective (f : Reflecting P P') : injective f := by
    intro x y h
    have h1 := P'.refl (f x)
    rw (config := { occs := .pos [2] }) [h] at h1
    have h1 := f.ref x y h1
    have h2 := P'.refl (f y)
    rw (config := { occs := .pos [2] }) [← h] at h2
    have h2 := f.ref y x h2
    exact P.antisym x y h1 h2


theorem Embedding_Is_Injective (f : Embedding P P') : injective f := by
    exact Reflecting_Is_Injective f.toReflecting

end
