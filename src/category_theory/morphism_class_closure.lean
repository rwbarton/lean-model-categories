import category_theory.transfinite.composition
import category_theory.colimits
import category_theory.colimit_lemmas

universes u v

namespace category_theory

variables {C : Type u} [𝒞 : category.{u v} C]
include 𝒞

variables (I : morphism_class C)

def closed_under_isos : Prop :=
∀ ⦃a b a' b' : C⦄ {f : a ⟶ b} {f' : a' ⟶ b'} (i : a ≅ a') (j : b ≅ b'), i.hom ≫ f' = f ≫ j.hom →
I f → I f'

def closed_under_pushouts : Prop :=
∀ ⦃a b a' b' : C⦄ {f : a ⟶ b} {f' : a' ⟶ b'} {i : a ⟶ a'} {j : b ⟶ b'} (po : Is_pushout f i j f'),
I f → I f'

include I
def closed_under_tcomp : Prop :=
∀ ⦃γ : Type v⦄ [well_order_top γ], by exactI ∀ (c : transfinite_composition I γ),
I c.composition
omit I

def closed_under_coproducts [∀ ι, limits.has_colimits_of_shape (discrete ι) C] : Prop :=
∀ ⦃ι : Type v⦄ {a b : ι → C} {f : Π i, a i ⟶ b i},
(∀ i, I (f i)) → I (limits.colim.map (nat_trans.of_function f))

lemma closed_under_pushouts_inter {I J : morphism_class C} :
  closed_under_pushouts I → closed_under_pushouts J → closed_under_pushouts (I ∩ J) :=
λ hI hJ a b a' b' f f' i j po ⟨hIf, hJf⟩, ⟨hI po hIf, hJ po hJf⟩

lemma closed_under_tcomp_inter {I J : morphism_class C} :
  closed_under_tcomp I → closed_under_tcomp J → closed_under_tcomp (I ∩ J) :=
λ hI hJ γ w c, by exactI
⟨hI (c.cast morphism_class.inter_subset_left), hJ (c.cast morphism_class.inter_subset_right)⟩

lemma closed_under_coproducts_inter [∀ ι, limits.has_colimits_of_shape (discrete ι) C]
  {I J : morphism_class C} :
  closed_under_coproducts I → closed_under_coproducts J → closed_under_coproducts (I ∩ J) :=
λ hI hJ ι a b f hf, ⟨hI (λ i, (hf i).1), hJ (λ i, (hf i).2)⟩

-- This seems too hard for now
/-
lemma coproduct_as_tcomp [limits.has_colimits C] (hI : closed_under_pushouts I)
  ⦃ι : Type v⦄ {a b : ι → C} {f : Π i, a i ⟶ b i} (hf : ∀ i, I (f i)) :
  ∃ (γ : Type v) (hγ : well_order_top γ), by exactI ∃ (c : transfinite_composition I γ),
  c.composition == limits.colim.map (nat_trans.of_function f) := -- FIXME
sorry

lemma closed_under_coproducts_of_pushouts_tcomp [limits.has_colimits C]
  (hpushouts : closed_under_pushouts I) (htcomp : closed_under_tcomp I) :
  closed_under_coproducts I :=
λ ι a b f hf, _
-/

variables {I}

lemma closed_under_isos_of_closed_under_pushouts :
  closed_under_pushouts I → closed_under_isos I :=
λ H a b a' b' f f' i j s hf,
have Is_pushout f i.hom (𝟙 b) _, begin
  convert Is_pushout_of_isomorphic
    (Is_pushout.refl f) f i.hom (iso.refl a) (iso.refl b) i.symm _ _; by simp
end,
have Is_pushout f i.hom j.hom f', begin
  convert Is_pushout_of_isomorphic' this j,
  { simp },
  { rw [category.assoc, ←s], simp }
end,
H this hf

lemma closed_under_coproducts_of_coproduct [∀ ι, limits.has_colimits_of_shape (discrete ι) C]
  (F : Π (ι : Type v), (discrete ι ⥤ C) ⥤ C) (hF : Π ι, F ι ≅ limits.colim)
  (hI₀ : closed_under_isos I)
  (hI : ∀ {ι} {a b : ι → C} {f : Π i, a i ⟶ b i}, (∀ i, I (f i)) →
   I ((F ι).map (nat_trans.of_function f))) : closed_under_coproducts I :=
λ ι a b f hf,
hI₀ (nat_iso.app (hF ι) _) (nat_iso.app (hF ι) _) (by symmetry; apply (hF ι).hom.naturality)
  (hI hf)

end category_theory
