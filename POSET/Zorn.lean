import POSET.Basic
import POSET.ExtremeElements.BasicProp
import POSET.SubsetTypes.Chain.Defs


def ZornPOSET {A : Type} (P : POSET A) : Prop :=
  (∀ C : A → Prop, Chain P C → ∃ U : A, UpperBound P U C) → ∃ M : A, MaximalElement P M
