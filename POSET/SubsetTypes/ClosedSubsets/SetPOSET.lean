import POSET.Sets.SetPOSET.Defs
import POSET.SubsetTypes.ClosedSubsets.Basic
import POSET.Morphisms.Defs

def Down_Map_Monotone {A : Type} (P : POSET A) : Monotone P (SetPOSET A) where
  app := ElementDownwardClosure P
  mon := by
    intro a b h
    change subset (ElementDownwardClosure P a) (ElementDownwardClosure P b)
    unfold subset
    intro x hS
    unfold ElementDownwardClosure
    unfold ElementDownwardClosure at hS
    exact P.trans x a b hS h
