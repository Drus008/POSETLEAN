variable (A : Type)

@[ext]
structure POSET where
  rel : A → A → Prop
  refl : ∀ a : A, rel a a
  antisym : ∀ a b : A, rel a b → rel b a → a = b
  trans : ∀ a b c : A, rel a b → rel b c → rel a c


def SubPOSET (P : A → Prop) (base : POSET A) : POSET {x : A // P x} where
  rel := fun x y => base.rel x.val y.val
  refl := fun x => base.refl x.val
  antisym := fun x y h1 h2 => Subtype.ext (base.antisym x.val y.val h1 h2)
  trans := fun x y z h1 h2 => base.trans x.val y.val z.val h1 h2
