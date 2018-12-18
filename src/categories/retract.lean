/- Retract of a map, as arises frequently in model categories. -/

import categories.category

namespace categories

universe u
variable {C : Type (u+1)}
variable [category C]

structure retract {A B : C} (f : A ⟶ B) :=
  {A' B' : C}
  (f' : A' ⟶ B')
  (iA : A' ⟶ A) (rA : A ⟶ A')
  (iB : B' ⟶ B) (rB : B ⟶ B')
  (HA : iA ≫ rA = 𝟙 A')
  (HB : iB ≫ rB = 𝟙 B')
  (Hi : iA ≫ f = f' ≫ iB) (Hr : rA ≫ f' = f ≫ rB)

end categories
