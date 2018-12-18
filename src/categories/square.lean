import categories.category

namespace categories

universe u
variable (C : Type (u+1))
variable [category C]

-- Commutative square in the category C
structure square : Type (u+1) :=
  {A B X Y : C}
  (f : A ⟶ B) (g : X ⟶ Y) (u : A ⟶ X) (v : B ⟶ Y)
  (H : f ≫ v = u ≫ g)

end categories
