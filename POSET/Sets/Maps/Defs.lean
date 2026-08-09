
variable {A B C : Type}

def injective (f : A → B) : Prop := ∀ x y : A, f x = f y → x = y

def surjective (f : A → B) : Prop := ∀ y : B, ∃ x : A, f x = y

def bijective (f : A → B) : Prop := injective f ∧ surjective f

def comp (g : B → C) (f : A → B) (x : A) : C := g (f x)

theorem Comp_Inj_Is_Inj {f : A → B} {g : B → C} (hf : injective f) (hg : injective g) :
  injective (comp g f) := by
  intro x y h
  have h := hg (f x) (f y) h
  exact hf x y h

theorem Comp_Sur_Is_Sur {f : A → B} {g : B → C} (hf : surjective f) (hg : surjective g) :
  surjective (comp g f) := by
  intro y
  have ⟨y',h⟩ := hg y
  have ⟨y'',h'⟩ := hf y'
  rw [← h'] at h
  exact ⟨y'',h⟩

theorem Comp_Bij_Is_Bij {f : A → B} {g : B → C} (hf : bijective f) (hg : bijective g) :
  bijective (comp g f) := by
  have hInj := Comp_Inj_Is_Inj hf.left hg.left
  have hSur := Comp_Sur_Is_Sur hf.right hg.right
  exact ⟨hInj, hSur⟩
