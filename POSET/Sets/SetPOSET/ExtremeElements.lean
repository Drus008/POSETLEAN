import POSET.Sets.SetFamilies.Defs
import POSET.Sets.SetPOSET.Defs
import POSET.ExtremeElements.BasicProp
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

theorem Universe_Is_Maximal : MaximalElement (SetPOSET A) universeSet := by
  exact Max_Is_Maximal (Universe_Is_Max A)

theorem Empty_Is_Minimal : MinimalElement (SetPOSET A) emptySet := by
  exact Min_Is_Minimal (Empty_Is_Min A)

-- This could contain several usfull lemas
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

theorem Union_Is_UpperBound (F : Family A) : UpperBound (SetPOSET A) (UnionF F) F := by
  intro S h
  change subset S (UnionF F)
  intro x hx
  unfold UnionF
  exact ⟨S, h, hx⟩

theorem Intersection_Is_LowerBound (F : Family A) : LowerBound (SetPOSET A) (InterseccionF F) F := by
  intro S h
  change subset (InterseccionF F) S
  intro x hx
  exact hx S h

theorem Union_Is_Sup (F : Family A) : Supremum (SetPOSET A) (UnionF F) F := by
  constructor
  · exact Union_Is_UpperBound A F
  · intro U h
    change subset _ U
    intro x hx
    have ⟨S, hx⟩ := hx
    have h := h S hx.left
    change subset S U at h
    exact h x hx.right

theorem Interseccion_Is_Inf (F : Family A) : Infimum (SetPOSET A) (InterseccionF F) F := by
  constructor
  · exact Intersection_Is_LowerBound A F
  · intro L h
    change subset L _
    intro x hx S hS
    unfold LowerBound at h
    have h := h S hS
    change subset L S at h
    exact h x hx
