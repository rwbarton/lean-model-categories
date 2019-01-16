import category_theory.small
import category_theory.transfinite.construction

noncomputable theory

universes v u

open well_order_top

namespace category_theory
namespace transfinite
section

parameters {C : Type u} [𝒞 : category.{v} C] [limits.has_colimits C]
include 𝒞

-- A set of "generating" maps
parameters {ι : Type v} (A : ι → C) (B : ι → C) (f : Π i, A i ⟶ B i)

-- Suppose the morphisms of I have this extension property
-- (we will guarantee this using the "attach all cells" construction)
parameters {I : morphism_class C}
parameters
  (hI : ∀ ⦃i X Y⦄ (g : X ⟶ Y) (Hg : I g) (h : A i ⟶ X), ∃ k : B i ⟶ Y, h ≫ g = f i ≫ k)

-- Domains of the generating maps are κ-small w.r.t. I, and γ has cofinality ≥ κ
parameters {κ : cardinal.{v}} (A_small : ∀ ⦃i⦄, κ_small I κ (A i))
parameters {γ : Type v} [well_order_top γ] [decidable_eq γ]
parameters (hκ : κ ≤ cofinality γ)

section

-- Suppose we've constructed a transfinite composition of maps from I of length γ
parameters (c : transfinite_composition I γ)

-- Then the end of the composition is injective w.r.t. the maps A i → B i
lemma replacement_injective {i} (h : A i ⟶ c.F.obj ⊤) :
  ∃ l : B i ⟶ c.F.obj ⊤, h = f i ≫ l :=
let ⟨j, hj, g, hg⟩ := A_small γ hκ c h,
    ⟨j', hj'⟩ := has_succ_of_lt hj,
    ⟨k, hk⟩ := hI _ (c.succ j j' hj') g in
⟨k ≫ c.F.map ⟨⟨lattice.le_top⟩⟩,
 by rw [←category.assoc, ←hk, ←hg, category.assoc, ←functor.map_comp]; refl⟩

end

section

parameters (F : C → C) (α : Π X, X ⟶ F X)
parameters (hα : ∀ X, I (α X))

def fibrant_replacement_cell_complex (X) :
  Σ' (c : transfinite_composition I γ), c.F.obj ⊥ = X :=
build_transfinite_composition F α hα X

def fibrant_replacement (X : C) : C :=
(fibrant_replacement_cell_complex X).fst.F.obj ⊤

def fibrant_unit (X : C) : X ⟶ fibrant_replacement X :=
eq_to_hom (fibrant_replacement_cell_complex X).snd.symm ≫
(fibrant_replacement_cell_complex X).fst.F.map ⟨⟨lattice.le_top⟩⟩

lemma fibrant_replacement_fibrant {X} {i} (h : A i ⟶ fibrant_replacement X) :
  ∃ l : B i ⟶ fibrant_replacement X, h = f i ≫ l :=
replacement_injective (fibrant_replacement_cell_complex X).fst h

end


end
end transfinite
end category_theory
