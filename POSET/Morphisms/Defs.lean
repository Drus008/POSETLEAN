import POSET.Basic

variable {A B : Type} (P1 : POSET A) (P2 : POSET B)

local infix:50 " ≤1 " => P1.rel
local infix:50 " ≤2 " => P2.rel

structure Monotone where
  app : A → B
  mon : ∀ x y : A, x ≤1 y → app x ≤2 app y

instance : CoeFun (Monotone P1 P2) (fun _ => A → B) where
  coe f := f.app

def Increasing (f : A → A) : Prop := ∀ x y : A, x ≤1 y → f x ≤1 f y

def Decreasing (f : A → A) : Prop := ∀ x y : A, x ≤1 y → f y ≤1 f x
