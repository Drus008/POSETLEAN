import POSET.Basic
import POSET.Sets.Basic


variable (A : Type)

def SetPOSET : POSET (A → Prop) where
  rel := subset
  refl := SubsetReflexive
  trans := @SubsetTransitive A
  antisym := @SubsetAntisymetric A
