import category_theory.stuff
import category_theory.yoneda
import category_theory.whiskering

namespace category_theory

universes v₁ u₁ u₂

section

variables (C : Type u₁) [𝒞 : category.{v₁} C]
include 𝒞

--- The functor c ↦ (X ↦ ↑X(c)), where ↑ denotes ulift.
def yoneda_evaluation' : Cᵒᵖ ⥤ ((Cᵒᵖ ⥤ Type v₁) ⥤ Type (max u₁ v₁)) :=
evaluation (Cᵒᵖ) (Type v₁) ⋙ (whiskering_right _ _ _).obj (ulift_functor.{u₁ v₁})

--- The functor c ↦ (X ↦ Hom(yc, X)).
def yoneda_pairing' : Cᵒᵖ ⥤ ((Cᵒᵖ ⥤ Type v₁) ⥤ Type (max u₁ v₁)) :=
yoneda.op ⋙ coyoneda

def yoneda_lemma' : yoneda_pairing' C ≅ yoneda_evaluation' C :=
nat_iso.of_components
  (λ c,
    { hom := { app := λ X h, ulift.up (h.app c (𝟙 c)) },
      inv :=
      { app := λ X x,
        { app := λ c' f, X.map f x.down,
          naturality' := by intros c' c'' f; ext x; dsimp; erw X.map_comp x f; refl },
        naturality' := by intros X Y F; ext x c' f;
          exact (functor_to_types.naturality X Y F f _).symm },
      hom_inv_id' := begin
        ext X x c' f,
        convert (functor_to_types.naturality _ X x _ _).symm,
        dsimp, simp
      end,
      inv_hom_id' := by ext X x; exact functor_to_types.map_id X x.down })
  begin
    intros c c' f, ext X h,
    change h.app c' (𝟙 c' ≫ f) = X.map f (h.app c (𝟙 c)),
    convert functor_to_types.naturality _ X h f (𝟙 c) using 2,
    dsimp, simp
  end

end

section small

-- TODO: unify with large version somehow

variables (C : Type v₁) [small_category C]

def yoneda_lemma'' : (yoneda.op ⋙ coyoneda : Cᵒᵖ ⥤ _) ≅ evaluation (Cᵒᵖ) (Type v₁) :=
nat_iso.of_components
  (λ c,
    { hom := { app := λ X h, h.app c (𝟙 c) },
      inv :=
      { app := λ X x,
        { app := λ c' f, X.map f x,
          naturality' := by intros c' c'' f; ext x; dsimp; erw X.map_comp x f; refl },
        naturality' := by intros X Y F; ext x c' f;
          exact (functor_to_types.naturality X Y F f _).symm },
      hom_inv_id' := begin
        ext X x c' f,
        convert (functor_to_types.naturality _ X x _ _).symm,
        dsimp, simp
      end,
      inv_hom_id' := by ext X x; exact functor_to_types.map_id X x })
  begin
    intros c c' f, ext X h,
    change h.app c' (𝟙 c' ≫ f) = X.map f (h.app c (𝟙 c)),
    convert functor_to_types.naturality _ X h f (𝟙 c) using 2,
    dsimp, simp
  end

end small

end category_theory
