import category_theory.compact
import category_theory.generator
import category_theory.induced2
import category_theory.limits.functor_category
import category_theory.limits.types
import category_theory.presheaf

universes u v

namespace category_theory
open category_theory.functor

variables (κ : regular_cardinal.{v})

section

variables (C : Type u) [𝒞 : category.{u v} C] [limits.has_colimits.{u v} C]
include 𝒞

include κ

/-- A cocomplete category C is locally κ-presentable if there exists
  a set of objects Aᵢ such that

  * each object Aᵢ is κ-compact, and
  * every object of C can be written as a κ-filtered colimit of the objects Aᵢ.

  The second condition requires a little trickery...
-/
def is_locally_kappa_presentable : Prop :=
∃ (ι : Type v) (A : ι → C),
(∀ i, is_kappa_compact κ (A i)) ∧
(∀ X, ∃ (J : Type v) [small_category J], by exactI is_kappa_filtered κ J ∧
  ∃ (F : J ⥤ induced_category A) (t : (F ⋙ induced_functor A) ⟹ (const _).obj X),
  nonempty (limits.is_colimit { X := X, ι := t }))

variables {C}

section of_strong_generator

/-- [AR94], 1.11 -/

variables {J : Type v} [small_category J]

inductive closure_under_J {ι : Type v} (A : ι → C) : Type v
| gen (i : ι) : closure_under_J
| colim (F_obj : J → closure_under_J) : closure_under_J

/-
lemma is_locally_kappa_presentable_of_strong_generator {ι : Type v} (A : ι → C)
  (h₁ : ∀ i, is_kappa_compact κ (A i)) (h₂ : is_strong_generator A) :
  is_locally_kappa_presentable κ C :=
sorry
-/

end of_strong_generator

/-
/-- A presheaf category is locally κ-presentable for any regular cardinal κ. -/
lemma presheaf_is_locally_kappa_presentable {J : Type v} [small_category J] :
  is_locally_kappa_presentable κ (presheaf J) :=
@is_locally_kappa_presentable_of_strong_generator κ (presheaf J) _ (@presheaf.has_colimits J _) _
  yoneda.obj (λ j, representable_is_compact κ j) yoneda_is_strong_generator
-/

end

end category_theory
