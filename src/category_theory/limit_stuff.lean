import category_theory.limits.limits
import category_theory.cone_stuff
import category_theory.stuff
import category_theory.equivalence
import category_theory.compose_functors
import category_theory.discrete_category

universes u v

namespace category_theory

open category_theory.functor
open category_theory.limits

variables {J K : Type v} [small_category J] [small_category K]
variables {C : Type u} [𝒞 : category.{u v} C]
include 𝒞

section

variables {E : K ⥤ J}
  (e : Π (F : J ⥤ C) (W : C), (F ⟹ (const J).obj W) ≃ ((E ⋙ F) ⟹ (const K).obj W))
  (he : ∀ F W t, e F W t = whisker_left E t)

include he
def whisker_left_preserves_colimits {F : J ⥤ C} {t : cocone F} :
  is_colimit t ≃ is_colimit (t.whisker E) :=
{ to_fun := λ h,
    is_colimit.of_hom_iso
      (λ W, ((h.hom_iso _).to_equiv.trans (e _ _)).to_iso)
      (λ W f, by dsimp; rw he; refl),
  inv_fun := λ h,
    is_colimit.of_hom_iso
      (λ W, ((h.hom_iso _).to_equiv.trans (e _ _).symm).to_iso)
      (λ W f, by dsimp; rw [equiv.symm_apply_eq, he]; refl),
  left_inv := λ h, subsingleton.elim _ _,
  right_inv := λ h, subsingleton.elim _ _ }

end

section whisker_equivalence

variables (E : K ≌ J)

def whisker_left_equivalence_preserves_colimits {F : J ⥤ C} {t : cocone F} :
  is_colimit t ≃ is_colimit (t.whisker E.functor) :=
whisker_left_preserves_colimits
  (λ F W, hom_equiv (precompose_equivalence E).functor) (λ F W t, rfl)

end whisker_equivalence

lemma is_colimit_of_iso {J : Type v} [small_category J] {F G : J ⥤ C} (α : F ≅ G)
  {t : limits.cocone G} (ht : limits.is_colimit t) : limits.is_colimit (t.precompose α.hom) :=
is_colimit.of_hom_iso
  (λ W, (ht.hom_iso W).trans ((yoneda.obj ((const J).obj W)).on_iso α.op.symm))
  (λ W f, by dsimp [cocone.precompose]; simp; refl) -- TODO: more simp lemmas

-- TODO: Clean up
@[simp] def cone.of_function {I : Type v} (X : C) {F : I → C} (f : Π i : I, X ⟶ F i) :
  limits.cone (functor.of_function F) :=
{ X := X,
  π := { app := λ i, f i,
    naturality' := λ X Y g,
    begin
      cases g, cases g, cases g,
      dsimp [functor.of_function],
      simp,
    end } }

@[simp] def cocone.of_function' {I : Type v} (X : C) {F : discrete I ⥤ C}
  (f : Π i : I, F.obj i ⟶ X) : limits.cocone F :=
{ X := X,
  ι := { app := λ i, f i,
    naturality' := λ X Y g,
    begin
      cases g, cases g, cases g,
      dsimp [functor.of_function],
      simp,
    end } }

@[simp] def cocone.of_function {I : Type v} (X : C) {F : I → C} (f : Π i : I, F i ⟶ X) :
  limits.cocone (functor.of_function F) :=
cocone.of_function' X f

end category_theory
