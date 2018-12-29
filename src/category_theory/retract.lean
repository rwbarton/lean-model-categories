/- Retract of a map, as arises frequently in model categories. -/

import category_theory.category

namespace category_theory

universes u v
variables {C : Type u} [𝒞 : category.{u v} C]
include 𝒞

--- `retract f f'` is a diagram exhibiting f' as a retract of f.
structure retract {a b a' b' : C} (f : a ⟶ b) (f' : a' ⟶ b') : Type v :=
(ia : a' ⟶ a) (ra : a ⟶ a')
(ib : b' ⟶ b) (rb : b ⟶ b')
(ha : ia ≫ ra = 𝟙 a')
(hb : ib ≫ rb = 𝟙 b')
(hi : ia ≫ f = f' ≫ ib)
(hr : ra ≫ f' = f ≫ rb)

end category_theory

