import category_theory.isomorphism
import category_theory.presheaf
import category_theory.yoneda
import category_theory.stuff

universes v u w

namespace category_theory

section

variables {C : Type u} [𝒞 : category.{v} C]
include 𝒞

variables {ι : Type w} (A : ι → C)

-- [AR94, 0.6]

/-- A family Aᵢ of objects of C is a generator if
  the functors Hom(Aᵢ, -) are jointly faithful. -/
def is_generator : Prop :=
∀ X Y (f g : X ⟶ Y), (∀ i (e : A i ⟶ X), e ≫ f = e ≫ g) → f = g

/-- A family Aᵢ of objects of C is a strong generator if it is a generator and
  whenever m : X → Y is a monic morphism such that every morphism Aᵢ → Y factors
  through m, m is an isomorphism. -/
def is_strong_generator {ι : Type w} (A : ι → C) : Prop :=
is_generator A ∧
∀ X Y (m : X ⟶ Y), mono m → (∀ i (y : A i ⟶ Y), ∃ f, y = f ≫ m) → nonempty (is_iso m)

end

section presheaf

variables {C : Type v} [small_category C]

lemma yoneda_is_generator : is_generator (yoneda.obj : C → presheaf C) :=
begin
  intros X Y f g h,
  ext c x,
  change C at c,
  convert congr_fun (nat_trans.congr_app (h c ((yoneda_sections_small c X).inv x)) c) (𝟙 c);
  exact (congr_fun (X.map_id c) x).symm
end

instance presheaf.mono {X Y : presheaf C} (m : X ⟶ Y) [mono m] (c : C) : mono (m.app c) :=
begin
  rw mono_iff_injective,
  intros x x' h,
  rw ←iso.inv_eq_iff_eq (yoneda_sections_small _ _),
  rw ←cancel_mono m,
  rw ←iso.hom_eq_iff_eq (yoneda_sections_small _ _),
  convert h; { dsimp [yoneda_lemma, ulift_trivial], erw X.map_id, refl }
end

/-- Representables form a strong generator of a presheaf category. -/
lemma yoneda_is_strong_generator : is_strong_generator (yoneda.obj : C → presheaf C) :=
begin
  refine ⟨yoneda_is_generator, _⟩,
  introsI X Y m hm₁ hm₂,
  refine ⟨_⟩,
  suffices : Π c, is_iso (m.app c), { apply nat_iso.is_iso_of_components },
  intro c,
  change C at c,
  choose f hf using hm₂ c,
  let f' : Y.obj c ⟶ X.obj c :=
    (yoneda_sections_small c Y).inv ≫ f ≫ (yoneda_sections_small c X).hom,
  have : f' ≫ m.app c = 𝟙 _,
  { ext y,
    convert (congr_fun (nat_trans.congr_app (hf ((yoneda_sections_small c Y).inv y)) c) (𝟙 c)).symm,
    exact (congr_fun (Y.map_id c) y).symm },
  refine ⟨f', _, this⟩,
  change _ = _,
  rw [←cancel_mono (m.app c), category.assoc, this], simp,
end

end presheaf

end category_theory
