import category_theory.examples.topological_spaces
import category_theory.cone_stuff
import category_theory.discrete_category
import homotopy_theory.topological_spaces.homeomorphism
import category_theory.limit_stuff

universes u v

lemma is_open_Inf {α : Type u} {ι : Type v} (t : ι → topological_space α) (s : set α) :
  @is_open _ (⨅ i, t i) s ↔ ∀ i, @is_open _ (t i) s :=
begin
  suffices : @continuous _ _ (⨅ i, t i) _ s ↔ ∀ i, @continuous _ _ (t i) _ s,
  { simpa [continuous_Prop] using this },
  simp [continuous_iff_induced_le]
end

open category_theory category_theory.examples category_theory.limits
open homotopy_theory.topological_spaces

lemma is_open_in_colimit {J : Type u} [small_category J] (F : J ⥤ Top.{u})
  {t : cocone F} (ht : is_colimit t) (s : set t.X) :
  is_open s ↔ ∀ j, is_open (t.ι.app j ⁻¹' s) :=
begin
  refine ⟨λ hs j, (t.ι.app j).property s hs, λ hs, _⟩,
  let t' := colimit.cocone F,
  let i : t' ≅ t := is_colimit.unique (colimit.is_colimit F) ht,
  let i' : Top.homeomorphism t'.X t.X := cocones.forget.on_iso i,
  rw [i'.is_open_iff, is_open_Inf],
  intro j,
  rw is_open_coinduced,
  exact hs j
end

lemma is_closed_in_colimit {J : Type u} [small_category J] (F : J ⥤ Top.{u})
  {t : cocone F} (ht : is_colimit t) (s : set t.X) :
  is_closed s ↔ ∀ j, is_closed (t.ι.app j ⁻¹' s) :=
is_open_in_colimit F ht (-s)

