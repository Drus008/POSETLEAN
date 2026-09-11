import POSET.ExtremeElements.Subsets
import POSET.ExtremeElements.BasicProp

structure Atomic (A : Type) extends POSET A where
  a : ∀ x : A, (¬ MinElement toPOSET x) → ∃ a : A, (Atom toPOSET a) ∧ (rel a x)

instance {A : Type} : CoeOut (Atomic A) (POSET A) := ⟨Atomic.toPOSET⟩

structure Atomistic (A : Type) extends POSET A where
  a : ∀ x : A, ∃ Sx : A → Prop, (subset Sx (Atom toPOSET)) ∧ (Supremum toPOSET x Sx)

instance {A : Type} : CoeOut (Atomistic A) (POSET A) := ⟨Atomistic.toPOSET⟩


def Atomistic_Is_Atomic {A : Type} (P : Atomistic A) : Atomic A where
  toPOSET := P.toPOSET
  a := by
    intro x h
    have ⟨Sx, hSxAtom, hSxSup⟩ := P.a x
    obtain h' | h' := Classical.em (Sx =emptySet)
    · rw [h'] at hSxSup
      have hx := Sup_EmptySet_Is_Min hSxSup
      have hx :=  h hx
      contradiction
    · have ⟨a,h'⟩ := NoEmpty_Has_Element h'
      exists a
      constructor
      · exact hSxAtom a h'
      · have hx := hSxSup.left
        exact hx a h'
