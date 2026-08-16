import POSET.Sets.SetPOSET.ExtremeElements
import POSET.Sets.SetFamilies.Defs
import POSET.Sets.Defs

variable {A : Type}

theorem PowerSet_Contains_Universe (A : Type) :
  PowerSet (@universeSet A) := by
  trivial

theorem PowerSet_Contains_Empty (A : Type) :
  PowerSet (@emptySet A) := by
  trivial

theorem Union_Empty_Is_Empty (A : Type) :
  UnionF (@emptySet (A → Prop)) = @emptySet A := by
  funext x
  ext
  unfold UnionF
  unfold emptySet
  constructor
  · intro h
    have ⟨S,h⟩ := h
    exact h.left
  · intro h
    trivial

theorem Intersection_Empty_Is_Universe (A : Type) :
  InterseccionF (@emptySet (A → Prop)) = @universeSet A := by
  funext x
  ext
  constructor
  · intro h
    trivial
  · intro h S h
    contradiction


theorem Element_Family_Subset_Union {S : A → Prop} {F : Family A}
  (h : F S) : subset S (UnionF F) := by
  intro x hx
  exact ⟨S, h, hx⟩

theorem Intersection_Subset_Element_Family {S : A → Prop} {F : Family A}
  (h : F S) : subset (InterseccionF F) S := by
  intro x hx
  exact hx S h

theorem If_Family_Contains_Univers__Union_Is_Univers {F : Family A}
  (h : F (@universeSet A)) : UnionF F = @universeSet A := by
  have h := Element_Family_Subset_Union h
  exact (Universe_Is_Maximal A) _ h


theorem If_Family_Contains_Empty__Intersection_Is_Empty {F : Family A}
  (h : F (@emptySet A)) : InterseccionF F = @emptySet A := by
  have h := Intersection_Subset_Element_Family h
  exact (Empty_Is_Minimal A) _ h

theorem Union_PowerSet_Is_Universe (A : Type) :
  UnionF (@PowerSet A) = @universeSet A := by
  have h := PowerSet_Contains_Universe A
  exact If_Family_Contains_Univers__Union_Is_Univers  h

theorem Intersection_PowerSet_Is_Empty (A : Type) :
  InterseccionF (@PowerSet A) = @emptySet A := by
  have h := PowerSet_Contains_Empty A
  exact If_Family_Contains_Empty__Intersection_Is_Empty h
