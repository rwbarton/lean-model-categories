/- Categories which are small relative to a cardinal κ.
   κ-filtered categories.
   Normally we care about these concepts for categories which are
   used to index (co)limits, so we work with small_categories. -/

import category_theory.limits.limits
import category_theory.size

universe v

namespace category_theory

class is_filtered_or_empty (C : Type v) [small_category C] : Prop :=
(cocone_objs : ∀ (X Y : C), ∃ Z, nonempty (X ⟶ Z) ∧ nonempty (Y ⟶ Z))
(cocone_maps : ∀ ⦃X Y : C⦄ (f g : X ⟶ Y), ∃ Z (h : Y ⟶ Z), f ≫ h = g ≫ h)

class is_filtered (C : Type v) [small_category C] extends is_filtered_or_empty C : Prop :=
(nonempty : nonempty C)

variables (κ : regular_cardinal.{v})

structure is_kappa_filtered (C : Type v) [small_category C] : Prop :=
(cocone_functor : ∀ {I : Type v} [small_category I] (hI : is_kappa_small κ I) (F : I ⥤ C),
  nonempty (limits.cocone F))

end category_theory
