/- κ-compact objects. -/

import category_theory.filtered
import category_theory.limits.preserves
import category_theory.limits.functor_category
import category_theory.limits.types
import category_theory.stuff
import category_theory.yoneda_curry

universes v u

namespace category_theory

variables (κ : regular_cardinal.{v})
include κ

section

variables {C : Type u} [𝒞 : category.{v} C]
include 𝒞

def is_kappa_compact (A : C) : Prop :=
nonempty $ Π {J : Type v} {𝒥 : small_category J}, by exactI
  is_kappa_filtered κ J → limits.preserves_colimits_of_shape J (coyoneda.obj A)

end

section presheaf

lemma representable_is_compact {C : Type v} [small_category C] (c : C) :
  is_kappa_compact κ (yoneda.obj c) :=
⟨λ J 𝒥 hJ F,
 by exactI limits.preserves_colimits_of_iso (nat_iso.app (yoneda_lemma'' C) c).symm⟩

end presheaf

end category_theory
