import POSET.Sets.SetPOSET.Defs
import POSET.Sets.Algebra.Basic
import POSET.Lattice.Defs

variable (A : Type)

def SetMeet : MeetSemilattice (A → Prop) where
  toPOSET := SetPOSET A
  meet := IntersectionS
  down1 := I_Subset_L
  down2 := I_Subset_R
  inf := by
    intro S1 S2 H ⟨h1, h2⟩
    intro x hx
    have h1 := h1 x hx
    have h2 := h2 x hx
    exact ⟨h1, h2⟩

def SetJoin : JoinSemilattice (A → Prop) where
  toPOSET := SetPOSET A
  join := UnionS
  up1 := L_Subset_U
  up2 := R_Subset_U
  sup := by
    intro S1 S2 H ⟨h1, h2⟩ x hx
    cases hx with
    |inl hx =>
      exact h1 x hx
    |inr hx =>
      exact h2 x hx

def SetLattice : Lattice (A → Prop) where
  toPOSET := SetPOSET A

  meet := IntersectionS
  down1 := I_Subset_L
  down2 := I_Subset_R
  inf := (SetMeet A).inf

  join := UnionS
  up1 := L_Subset_U
  up2 := R_Subset_U
  sup := (SetJoin A).sup

theorem Meet_Lattice_Is_Meet_Set : (SetLattice A).toMeetSemilattice = SetMeet A := rfl

theorem Join_Lattice_Is_Join_Set : (SetLattice A).toJoinSemilattice = SetJoin A := rfl
