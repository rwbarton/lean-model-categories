import category_theory.limits.cones

universes v u u'

namespace category_theory.limits

open category_theory

variables {J : Type v} [small_category J]
variables {C : Type u} [𝒞 : category.{v} C]
include 𝒞
variables {D : Type u'} [𝒟 : category.{v} D]
include 𝒟

variables {K : Type v} [small_category K] (E : K ⥤ J)
variables {F : J ⥤ C} (G : C ⥤ D)

lemma whisker_thing {t : cocone F} : G.map_cocone (t.whisker E) = (G.map_cocone t).whisker E :=
rfl

/-
def whisker_fun {K : Type v} [small_category K] (E : K ⥤ J) : cocone F ⥤ cocone (E ⋙ F) :=
{ obj := λ t, t.whisker E,
  map := λ 
}
-/

end category_theory.limits

namespace category_theory

variables {J : Type v} [small_category J]
variables {C : Type u} [𝒞 : category.{v} C]
include 𝒞

def cocones.forget {F : J ⥤ C} : limits.cocone F ⥤ C :=
{ obj := λ t, t.X,
  map := λ s t f, f.hom }

def cones.forget {F : J ⥤ C} : limits.cone F ⥤ C :=
{ obj := λ t, t.X,
  map := λ s t f, f.hom }

end category_theory
