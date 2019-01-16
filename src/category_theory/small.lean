import category_theory.transfinite.composition
import set_theory.cofinality

universes v u

namespace category_theory.transfinite
open category_theory
open well_order_top

section
variables {γ : Type v} [well_order_top γ]

open lattice

lemma upper_bound_of_cofinality {ι : Type v} (f : ι → {j : γ // j < ⊤})
  (h : cardinal.mk ι < cofinality γ) : ∃ j, j < ⊤ ∧ ∀ i, (f i).val < j :=
begin
  rcases ordinal.lt_cof_type (set.range f) (lt_of_le_of_lt (cardinal.mk_range_le _) h)
    with ⟨⟨j, hj⟩, h⟩,
  refine ⟨j, hj, λ i, h (f i) _⟩,
  apply set.mem_range_self
end

lemma is_limit_of_cofinality (h : cardinal.omega ≤ cofinality γ) : is_limit (⊤ : γ) :=
begin
  rcases is_bot_or_succ_or_limit (⊤ : γ) with ⟨_, H⟩|⟨i, _, H⟩|⟨_, H⟩,
  { rcases ordinal.lt_cof_type (∅ : set {j : γ // j < ⊤})
      (lt_of_lt_of_le (cardinal.lt_omega_iff_fintype.mpr ⟨infer_instance⟩) h)
      with ⟨⟨j, hj⟩, h⟩,
    exact absurd hj H.not_lt },
  { rcases upper_bound_of_cofinality (λ _, ⟨i, H.lt⟩ : punit → {j : γ // j < ⊤})
      (lt_of_lt_of_le (cardinal.lt_omega_iff_fintype.mpr ⟨infer_instance⟩) h)
      with ⟨j', h₁, h₂⟩,
    replace h₁ := H.le_of_lt_succ h₁,
    have : i < j', from h₂ punit.star,
    exact absurd h₁ (not_le_of_lt this) },
  { exact H }
end

lemma cofinality_of_is_limit (h : is_limit (⊤ : γ)) : cardinal.omega ≤ cofinality γ :=
begin
  -- TODO: split this proof into lemmas (bot ↔ 0, succ ↔ succ)
  dsimp [cofinality],
  rw ordinal.omega_le_cof,
  split,
  { intro H,
    have : (⊥ : γ) < ⊤, from bot_lt (λ h', not_bot_limit h' h),
    replace := (ordinal.typein_lt_typein (<)).mpr this,
    rw H at this,
    exact absurd this (not_lt_of_ge (ordinal.zero_le _)) },
  { intros o ho,
    have ho' := lt_trans ho (ordinal.typein_lt_type _ _),
    let j : γ := ordinal.enum (<) o ho',
    have : j < ⊤,
    { refine (ordinal.typein_lt_typein (<)).mp _,
      rwa ordinal.typein_enum },
    rcases has_succ_of_lt this with ⟨j', hj'⟩,
    have : ordinal.succ o ≤ ordinal.typein (<) j',
    { rw ordinal.succ_le,
      rw ←ordinal.typein_enum (<) ho',
      exact (ordinal.typein_lt_typein ((<) : γ → γ → Prop)).mpr hj'.lt },
    refine lt_of_le_of_lt this _,
    rw ordinal.typein_lt_typein,
    refine (eq_or_lt_of_le (well_order_top.le_top : j' ≤ ⊤)).resolve_left (λ H, _),
    subst j',
    exact not_succ_limit hj' h }
end

end

section

variables {C : Type u} [𝒞 : category.{v} C]
include 𝒞

-- X is κ-small with respect to I if any map from X to the end of a
-- transfinite composition of maps from I whose length has cofinality
-- at least κ factors through some earlier object in the composition.
def κ_small (I : morphism_class C) (κ : cardinal) (X : C) : Prop :=
∀ (γ : Type v) [well_order_top γ], by exactI κ ≤ cofinality γ →
∀ (c : transfinite_composition I γ) (f : X ⟶ c.F.obj ⊤),
∃ (j : γ) (hj : j < ⊤) (g : X ⟶ c.F.obj j),
  g ≫ c.F.map ⟨⟨lattice.le_top⟩⟩ = f

def small (I : morphism_class C) (X : C) : Prop := ∃ κ, κ_small I κ X

lemma κ_small_mono {I J : morphism_class C} {κ : cardinal} {X : C}
  (hIJ : ∀ {X Y} {f : X ⟶ Y}, I f → J f) (h : κ_small J κ X) : κ_small I κ X :=
λ γ I hγ c, by exactI h γ hγ (c.cast @hIJ)

end

section Set

lemma jointly_surjective {J : Type v} [small_category J] (F : J ⥤ Type v)
  {t : limits.cocone F} (h : limits.is_colimit t) (x : t.X) :
  ∃ j y, t.ι.app j y = x :=
begin
  suffices : (λ (x : t.X), ulift.up (∃ j y, t.ι.app j y = x)) = (λ _, ulift.up true),
  { have := congr_fun this x,
    have H := congr_arg ulift.down this,
    dsimp at H,
    rwa eq_true at H },
  refine h.hom_ext _,
  intro j, ext y,
  erw iff_true,
  exact ⟨j, y, rfl⟩
end

variables (I : morphism_class (Type v)) (X : Type v)

lemma is_small : small I X :=
begin
  have : ∃ κ, cardinal.mk X < κ ∧ κ.is_regular,
  { refine ⟨(max cardinal.omega (cardinal.mk X)).succ, _, cardinal.succ_is_regular (le_max_left _ _)⟩,
    exact lt_of_le_of_lt (le_max_right _ _) (cardinal.lt_succ_self _) },
  rcases this with ⟨κ, hκ₁, hκ₂⟩,
  refine ⟨κ, _⟩,
  intros γ I₁ hγ c f, resetI,
  have : ∀ x, ∃ j y, (c.F.map_cocone (cocone_at ⊤)).ι.app j y = f x,
  { intro x,
    cases c.limit ⊤ (is_limit_of_cofinality _) with hlim,
    refine jointly_surjective _ hlim _,
    exact le_trans hκ₂.1 hγ },
  choose jx yx hy using this,
  rcases upper_bound_of_cofinality jx (lt_of_lt_of_le hκ₁ hγ) with ⟨j, hj₁, hj₂⟩,
  refine ⟨j, hj₁, λ x, c.F.map ⟨⟨le_of_lt (hj₂ x)⟩⟩ (yx x), _⟩,
  ext x,
  rw ←hy,
  change (c.F.map _ ≫ c.F.map _) (yx x) = c.F.map _ (yx x),
  rw ←c.F.map_comp, refl,
end

end Set

end category_theory.transfinite
