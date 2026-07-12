import POSET.Basic

variable (A : Type) (P : POSET A)

local infix:50 " ≤ " => P.rel

def MaxElement (M : A) : Prop := ∀ x : A, x ≤ M

def MinElement (m : A) : Prop := ∀ x : A, m ≤ x

def MaximalElement (M : A) : Prop := ∀ x : A, M ≤ x → x=M

def MinimalElement (m : A) : Prop := ∀ x : A, x ≤ m → x=m
