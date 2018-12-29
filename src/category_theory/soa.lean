import category_theory.transfinite.construction
import category_theory.limits.over

noncomputable theory

local attribute [instance] classical.dec

open category_theory category_theory.functor well_order_top

universes u v


-- TODO: move to limits.over
namespace category_theory.limits

variables {C : Type u} [𝒞 : category.{u v} C]
include 𝒞

instance over.has_colimits [limits.has_colimits C] {X : C} : limits.has_colimits (over X) :=
λ J 𝒥 F, by exactI { cocone := over.colimit F, is_colimit := over.is_colimit F }

instance over.forget_preserves_colimits [limits.has_colimits C] {X : C} :
  preserves_colimits (over.forget : over X ⥤ C) :=
λ J 𝒥 F, by exactI preserves_colimit_of_preserves_colimit_cocone (colimit.is_colimit _)
  (is_colimit.of_iso_colimit (colimit.is_colimit (F ⋙ over.forget))
     begin ext, swap, refl, simp, dsimp, simp, refl end)

end category_theory.limits


namespace category_theory.over

lemma of_eq {C : Type u} [category.{u v} C] {Z : C} {X Y : over Z} (h : X = Y) :
  X.hom = eq_to_hom (by cases h; refl) ≫ Y.hom :=
by cases h; simp

end category_theory.over

namespace category_theory.transfinite
section

parameters {C : Type u} [𝒞 : category.{u v} C] [limits.has_colimits C]
include 𝒞

parameters {I : morphism_class C}

parameters {γ : Type v} [well_order_top γ]

parameters (step : Π {X Y : C} (g : X ⟶ Y), Σ' X' (j : X ⟶ X') (g' : X' ⟶ Y), g = j ≫ g' ∧ I j)

-- Plan: use the existing argument in the over category C/Y.

def soa_factor {X Y : C} (g : X ⟶ Y) :
  Σ' (c : transfinite_composition I γ) (g' : c.F.obj ⊤ ⟶ Y) (h₀ : c.F.obj ⊥ = X),
  g = (eq_to_hom h₀.symm ≫ c.composition) ≫ g' :=
let ⟨c', hc'⟩ :=
  @build_transfinite_composition (over Y) _ _ (I.preimage over.forget) γ _
    (λ XY, over.mk (step XY.hom).2.2.1)
    (λ XY, over.hom_mk (step XY.hom).2.1 (step XY.hom).2.2.2.1.symm)
    (λ XY, (step XY.hom).2.2.2.2)
    (over.mk g) in
⟨c'.map over.forget, (c'.F.obj ⊤).hom,
 begin
   have := congr_arg (λ Z, over.forget.obj Z) hc',
   refine ⟨this, _⟩,
   dsimp [transfinite_composition.composition, transfinite_composition.map],
   rw [category.assoc, over.over_w],
   apply category_theory.over.of_eq hc'.symm
 end⟩

end
end category_theory.transfinite
