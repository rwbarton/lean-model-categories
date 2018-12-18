import categories.category

import model.basic
import model.morphism_class

open categories

-- Fix a category C.
universe u
variable {C : Type (u+2)}
variable [category C]


namespace model

structure IsWeakEquivalences (is_weq : MorphismClass C) :=
  (id_is_weq : ∀ (X : C), is_weq (𝟙 X))
  -- Two out of three: If h = g . f and two of f, g, h are weak equivalences,
  -- then so is the third.
  (f_from_gh : ∀ {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z),
               is_weq g → is_weq (f ≫ g) → is_weq f)
  (g_from_fh : ∀ {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z),
               is_weq f → is_weq (f ≫ g) → is_weq g)
  (h_from_fg : ∀ {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z),
               is_weq f → is_weq g → is_weq (f ≫ g))

end model
