import top_stuff
import closed_embedding

universes u v w

section sigma
-- TODO: Refactor everything here

variables {ι : Type w} {α : ι → Type u} [Π i, topological_space (α i)]

lemma is_open_sigma {s : set (sigma α)} : is_open s ↔ ∀ i, is_open (sigma.mk i ⁻¹' s) :=
by simp only [is_open_Inf, is_open_coinduced]

lemma is_closed_sigma {s : set (sigma α)} : is_closed s ↔ ∀ i, is_closed (sigma.mk i ⁻¹' s) :=
is_open_sigma

-- TODO: unify these
lemma is_open_sigma_mk {i : ι} : is_open (set.range (sigma.mk i : α i → sigma α)) :=
begin
  rw is_open_sigma,
  intro j,
  suffices : sigma.mk j ⁻¹' set.range (sigma.mk i) = {x | j = i},
  { convert is_open_const },
  ext x,
  change sigma.mk j x ∈ _ ↔ j = i,
  split,
  { rintro ⟨y, hy⟩, cc },
  { rintro rfl, exact ⟨x, rfl⟩ }
end

lemma is_closed_sigma_mk {i : ι} : is_closed (set.range (sigma.mk i : α i → sigma α)) :=
begin
  rw is_closed_sigma,
  intro j,
  change is_open _,
  suffices : -(sigma.mk j ⁻¹' set.range (sigma.mk i)) = {x | j ≠ i},
  { convert is_open_const, exact this },
  ext x,
  change sigma.mk j x ∉ _ ↔ j ≠ i,
  apply not_iff_not_of_iff,
  split,
  { rintro ⟨y, hy⟩, cc },
  { rintro rfl, exact ⟨x, rfl⟩ }
end

lemma injective_sigma_mk {i : ι} : function.injective (sigma.mk i : α i → sigma α) :=
λ a b h, by cc

lemma continuous_sigma_mk {i : ι} : continuous (λ a, (⟨i, a⟩ : sigma α)) :=
continuous_infi_rng continuous_coinduced_rng

lemma is_open_map_sigma_mk {i : ι} {s : set (α i)} :
  is_open s ↔ is_open (sigma.mk i '' s) :=
begin
  refine ⟨_, _⟩,
{ intro hs,
  rw is_open_sigma,
  intro j,
  classical,
  by_cases h : i = j,
  { subst j,
    convert hs,
    exact set.preimage_image_eq _ injective_sigma_mk },
  { convert is_open_empty,
    apply set.eq_empty_of_subset_empty,
    rintro x ⟨y, _, hy⟩,
    have : i = j, by cc,
    contradiction } },
{ intro hs,
  convert ←continuous_sigma_mk _ hs,
  exact set.preimage_image_eq _ injective_sigma_mk }
end

lemma is_closed_map_sigma_mk {i : ι} {s : set (α i)} :
  is_closed s ↔ is_closed (sigma.mk i '' s) :=
begin
  refine ⟨_, _⟩,
{ intro hs,
  rw is_closed_sigma,
  intro j,
  classical,
  by_cases h : i = j,
  { subst j,
    convert hs,
    exact set.preimage_image_eq _ injective_sigma_mk },
  { convert is_closed_empty,
    apply set.eq_empty_of_subset_empty,
    rintro x ⟨y, _, hy⟩,
    have : i = j, by cc,
    contradiction } },
{ intro hs,
  convert ←continuous_iff_is_closed.mp continuous_sigma_mk _ hs,
  exact set.preimage_image_eq _ injective_sigma_mk }
end

lemma embedding_sigma_mk {i : ι} : embedding (λ a, (⟨i, a⟩ : sigma α)) :=
have closed_embedding (λ a, (⟨i, a⟩ : sigma α)), from
  closed_embedding_of_injective_closed injective_sigma_mk (λ s, is_closed_map_sigma_mk),
this.1

variables {β : Type v} [topological_space β]

lemma continuous_sigma {f : sigma α → β} (h : ∀ i, continuous (λ a, f ⟨i, a⟩)) : continuous f :=
continuous_infi_dom (λ i, continuous_coinduced_dom (h i))

variables {γ : ι → Type v} [Π i, topological_space (γ i)]

-- TODO: Apply this somewhere
lemma continuous_sigma_map {f : Π i, α i → γ i} (hf : ∀ i, continuous (f i)) :
  continuous (sigma.map id f) :=
begin
  apply continuous_sigma,
  intro i,
  change continuous (λ a, sigma.mk i (f i a)),
  exact continuous.comp (hf i) continuous_sigma_mk
end

lemma embedding_sigma_map {f : Π i, α i → γ i} (hf : ∀ i, embedding (f i)) :
  embedding (sigma.map id f) :=
begin
  refine ⟨_, _⟩,
  { rintro ⟨i, x⟩ ⟨j, y⟩ h,
    dsimp [sigma.map, id] at h,
    have : i = j, by cc,
    subst j,
    have : x = y := (hf i).1 (by cc),
    cc },
  { apply le_antisymm,
    { intros s hs,
      replace hs := is_open_sigma.mp hs,
      have : ∀ i, ∃ (t : set (γ i)), is_open t ∧ f i ⁻¹' t = sigma.mk i ⁻¹' s,
      { intro i,
        apply is_open_induced_iff.mp,
        convert hs i,
        exact (hf i).2.symm },
      choose t ht using this,
      apply is_open_induced_iff.mpr,
      refine ⟨⋃ i, sigma.mk i '' t i, is_open_Union (λ i, _), _⟩,
      { rw ←is_open_map_sigma_mk, exact (ht i).1 },
      { ext p,
        rcases p with ⟨i, x⟩,
        change (sigma.mk i (f i x) ∈ ⋃ (i : ι), sigma.mk i '' t i) ↔ _,
        symmetry,
        split; intro H,
        { rw set.mem_Union,
          refine ⟨i, _⟩,
          change x ∈ sigma.mk i ⁻¹' s at H,
          rw ←(ht i).2 at H,
          exact ⟨f i x, H, rfl⟩ },
        { rw set.mem_Union at H,
          rcases H with ⟨j, y, h₁, h₂⟩,
          have : j = i, by cc,
          subst j,
          have : y = f i x, by cc,
          rw this at h₁,
          change x ∈ sigma.mk i ⁻¹' s,
          rw ←(ht i).2,
          exact h₁ } } },
    { rw ←continuous_iff_induced_le,
      apply continuous_sigma_map,
      exact λ i, (hf i).continuous } }
end

end sigma

section coproduct

open category_theory category_theory.limits
open homotopy_theory.topological_spaces

variables {ι : Type u}

def Top_coproduct : (discrete ι ⥤ Top.{u}) ⥤ Top.{u} :=
{ obj := λ F, Top.mk_ob (Σ i, F.obj i),
  map := λ F G t, Top.mk_hom (sigma.map id (λ i, t.app i))
    begin
      apply continuous_sigma,
      intro i,
      dsimp [sigma.map],
      exact continuous.comp ((t.app i).property) continuous_sigma_mk
    end }

def Top_coproduct_is_colimit : @Top_coproduct ι ≅ colim :=
nat_iso.of_components
  (λ F,
   { hom := Top.mk_hom (λ ⟨i, x⟩, (colimit.ι F i).val x)
       (continuous_sigma $ λ i, (colimit.ι F i).property),
     inv := colimit.desc F (cocone.of_function' (Top_coproduct.obj F)
       (λ i, Top.mk_hom (sigma.mk i) continuous_sigma_mk)) })
  (by tidy)

end coproduct

