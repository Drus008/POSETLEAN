import POSET.Sets.SetPOSET.Defs
import POSET.ExtremeElements.Defs
import POSET.Sets.Basic

variable (A : Type)

theorem Universe_Is_Max : MaxElement (SetPOSET A) universeSet := by
  unfold MaxElement universeSet
  intro S
  change subset S (fun x => True)
  unfold subset
  intro x h
  trivial

theorem Empty_Is_Min : MinElement (SetPOSET A) emptySet := by
  unfold MinElement
  intro S
  change subset emptySet S
  unfold subset emptySet
  intro x
  intro h
  contradiction

-- This could be several usfull lemas
theorem Unitary_Is_Atom (a : A) : Atom (SetPOSET A) (unitarySet a) := by
  have h := Empty_Is_Min A
  unfold Atom
  apply Exists.intro emptySet
  refine ⟨h,?_⟩
  refine ⟨Unitary_Not_Empty a, ?_⟩
  intro S h
  change subset S (unitarySet a) at h
  by_cases h1 : ∃ x : A, S x
  · have ⟨x, h1⟩ := h1
    have h2 : S = unitarySet a := by
      have h3 : x = a := h x h1
      rw [h3] at h1
      have h4 := Unitary_Subset_Containing_Element a S h1
      exact SubsetAntisymetric h h4
    left
    exact h2
  · right
    exact defEmpty1 h1
