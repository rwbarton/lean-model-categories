import category_theory.functor_category
import category_theory.stuff
import category_theory.whiskering
import category_theory.equivalence

universes v₁ v₂ v₃ u₁ u₂ u₃

namespace category_theory

variables {C : Type u₁} [𝒞 : category.{v₁} C]
          {D : Type u₂} [𝒟 : category.{v₂} D]
include 𝒞 𝒟

@[simp] lemma left_unitor_hom_app (F : C ⥤ D) {X} :
  (functor.left_unitor F).hom.app X = 𝟙 _ :=
rfl

variables
          {E : Type u₃} [ℰ : category.{v₃} E]
include ℰ

def precompose : (C ⥤ D) ⥤ ((D ⥤ E) ⥤ (C ⥤ E)) :=
whiskering_left C D E

@[simp] lemma precompose_obj_map (F : C ⥤ D) {G H : D ⥤ E} (α : G ⟹ H) :
  (precompose.obj F).map α = whisker_left F α :=
rfl

omit 𝒞
def precompose_id : precompose.obj (functor.id D) ≅ functor.id (D ⥤ E) :=
nat_iso.of_components (λ F, functor.left_unitor _)
  (by tidy; erw [category.comp_id, category.id_comp]) -- help?

include 𝒞
def precompose_equivalence (F : C ≌ D) : (D ⥤ E) ≌ (C ⥤ E) :=
{ functor := precompose.obj F.functor,
  inverse := precompose.obj F.inverse,
  fun_inv_id' := (precompose.on_iso F.inv_fun_id).trans precompose_id,
  inv_fun_id' := (precompose.on_iso F.fun_inv_id).trans precompose_id }

end category_theory
