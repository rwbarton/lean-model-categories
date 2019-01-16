import category_theory.limits.functor_category
import category_theory.limits.types

universe v

namespace category_theory

variables (C : Type v) [small_category C]

def presheaf : Type (v+1) := (Cᵒᵖ ⥤ Type v)

instance presheaf.category : category (presheaf C) := by dunfold presheaf; apply_instance
instance presheaf.has_colimits : limits.has_colimits.{v} (presheaf C) :=
by dunfold presheaf; apply_instance

end category_theory
