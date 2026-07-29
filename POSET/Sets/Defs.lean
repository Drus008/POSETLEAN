variable {A : Type}

def emptySet (_ : A) : Prop := False

def universeSet (_ : A) : Prop := True

def unitarySet (a : A) (x : A) : Prop := x = a

def pairSet (a b : A) (x : A) : Prop := x = a ∨ x = b
