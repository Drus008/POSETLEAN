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


def Down_Map_Reflecting {A : Type} (P : POSET A) : Reflecting P (SetPOSET A) where
  app := ElementDownwardClosure P
  ref := by
    intro x y h
    change subset (ElementDownwardClosure P x) (ElementDownwardClosure P y) at h
    unfold subset at h
    have h := h x
    unfold ElementDownwardClosure at h
    exact h (P.refl x)


def Down_Map_Embedding {A : Type} (P : POSET A) : Embedding P (SetPOSET A) where
  app := ElementDownwardClosure P
  mon := (Down_Map_Monotone P).mon
  ref := (Down_Map_Reflecting P).ref
