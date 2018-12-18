import categories.category

namespace categories

universe u
variable {C : Type (u+1)}
variable [category C]

structure cospan : Type (u+1) :=
  {A B X : C}
  (f : A ⟶ B) (g : A ⟶ X)

end categories
