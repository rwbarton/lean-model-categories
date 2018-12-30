import sigma_stuff

universes u v w

section

variables {ι : Type w} {α : ι → Type u} [Π i, topological_space (α i)]
variables {β : Type v} [topological_space β]

-- The nontrivial direction of the homeomorphism (Σ i, α i) × β → Σ i, (α i × β).
lemma continuous_distrib_sigma :
  continuous (λ p, ⟨p.1.1, ⟨p.1.2, p.2⟩⟩ : (Σ i, α i) × β → Σ i, (α i × β)) :=
begin
  let f : (Σ i, α i) × β → Σ i, (α i × β) := λ p, ⟨p.1.1, ⟨p.1.2, p.2⟩⟩,
  change continuous f,
  intros s hs,
  have : f ⁻¹' s = ⋃ i, (by exact λ p, (sigma.mk i p.1, p.2)) '' (sigma.mk i ⁻¹' s),
  { tidy },
  rw this,
  apply is_open_Union,
  intro i,
  apply embedding_open (embedding_prod_mk embedding_sigma_mk embedding_id),
  { convert is_open_prod is_open_sigma_mk is_open_univ,
    rw [←set.range_id, set.prod_range_range_eq] },
  exact continuous_sigma_mk s hs
end

end

open category_theory
open homotopy_theory.topological_spaces

def Top_distrib {ι : Type u} (F : discrete ι ⥤ Top.{u}) (Y : Top.{u}) :
  Top.prod (Top_coproduct.obj F) Y ⟶ Top_coproduct.obj (F ⋙ Top.product_by Y) :=
Top.mk_hom _ continuous_distrib_sigma
