import topology.continuity
import category_theory.transfinite.composition
import category_theory.morphism_class_closure
import homotopy_theory.topological_spaces.category
import inj
import top_stuff

open set

universes u v

section

--- Two topologies on a type are equal if they have the same closed sets.
lemma topological_space_eq_closed {α : Type u} {f g : topological_space α}
  (h : ∀ s, @is_closed α f s ↔ @is_closed α g s) : f = g :=
by ext s; convert h (-s); simp

variables {α : Type u} [topological_space α] {β : Type v} [topological_space β]

def closed_embedding (f : α → β) : Prop :=
embedding f ∧ is_closed (range f)

-- In fact, this is a characterization of closed embeddings (among injections)
lemma closed_embedding.closed_iff_image_closed {f : α → β} (hf : closed_embedding f)
  {s : set α} : is_closed s ↔ is_closed (f '' s) :=
⟨embedding_is_closed hf.1 hf.2,
 λ h, begin
   convert ←continuous_iff_is_closed.mp hf.1.continuous _ h,
   apply preimage_image_eq _ hf.1.1
 end⟩

lemma closed_embedding.closed_iff_preimage_closed {f : α → β} (hf : closed_embedding f)
  {s : set β} (hs : s ⊆ range f) : is_closed s ↔ is_closed (f ⁻¹' s) :=
begin
  convert ←hf.closed_iff_image_closed.symm,
  rwa [image_preimage_eq_inter_range, inter_eq_self_of_subset_left]
end

lemma closed_embedding_of_injective_closed {f : α → β} (h : function.injective f)
  (hf : ∀ s, is_closed s ↔ is_closed (f '' s)) : closed_embedding f :=
begin
  refine ⟨⟨h, _⟩, by convert (hf univ).mp is_closed_univ; simp⟩,
  apply topological_space_eq_closed,
  intro s,
  rw [hf, is_closed_induced_iff],
  split; intro H,
  { refine ⟨f '' s, H, _⟩,
    rw preimage_image_eq _ h },
  { rcases H with ⟨t, tc, rfl⟩,
    rw image_preimage_eq_inter_range,
    apply is_closed_inter tc,
    convert (hf univ).mp is_closed_univ,
    simp }
end

end

section
open category_theory category_theory.limits
open homotopy_theory.topological_spaces

variables {J : Type u} [small_category J] [is_filtered_or_empty J]
variables (F : J ⥤ Top.{u})

-- Use facts about filtered colimits in Set
lemma filtered_colimit_closed_embedding
  (h : ∀ i j (f : i ⟶ j), closed_embedding (F.map f))
  {t : limits.cocone F} (ht : limits.is_colimit t) (i : J) :
  closed_embedding (t.ι.app i) :=
begin
  have inj : ∀ k, function.injective ⇑((t.ι).app k),
  { refine λ k, filtered_colimit_injective _ (preserves_colimit.preserves forget ht) _ k,
    intros i j hij, exact (h i j hij).1.1 },
  apply closed_embedding_of_injective_closed (inj i),
  { intro s,
    rw is_closed_in_colimit F ht,
    split; intro H,
    { intro j,
      rcases is_filtered_or_empty.cocone_objs i j with ⟨k, ⟨ik⟩, ⟨jk⟩⟩,
      rw [←t.w jk, ←t.w ik],
      erw [preimage_comp, image_comp, preimage_image_eq _ (inj k)],
      apply continuous_iff_is_closed.mp (F.map jk).property,
      exact (h i k ik).closed_iff_image_closed.mp H },
    { convert H i,
      symmetry,
      exact preimage_image_eq _ (inj i) } }
end

def closed_embedding_map {X Y : Top.{u}} (f : X ⟶ Y) : Prop := closed_embedding f

lemma closed_embedding_id {X : Top} : closed_embedding (𝟙 X) :=
⟨embedding_id, by convert is_closed_univ; apply range_id⟩

lemma closed_embedding_comp {X Y Z : Top} {f : X ⟶ Y} {g : Y ⟶ Z}
  (hf : closed_embedding f) (hg : closed_embedding g) : closed_embedding (f ≫ g) :=
⟨embedding_compose hf.1 hg.1, show is_closed (range (g ∘ f)),
 by rw [range_comp, ←hg.closed_iff_image_closed]; exact hf.2⟩

lemma closed_embedding_tcomp {γ : Type*} [well_order_top γ]
  (c : transfinite_composition @closed_embedding_map γ) {i j} (h : i ≤ j) :
  closed_embedding (c.F.map ⟨⟨h⟩⟩) :=
begin
  revert i,
  refine well_founded.induction (is_well_order.wf (<)) j _,
  clear j,
  intros j ih i h,
  rcases eq_or_lt_of_le h with rfl|h,
  { convert closed_embedding_id, apply c.F.map_id },
  { rcases well_order_top.is_bot_or_succ_or_limit j with ⟨_, hj⟩|⟨j', _, hj⟩|⟨_, hj⟩,
    { exact absurd h hj.not_lt },
    { convert closed_embedding_comp (ih j' hj.lt (hj.le_of_lt_succ h)) (c.succ j' j hj),
      apply c.F.map_comp },
    { rcases c.limit j hj with ⟨hlim⟩,
      haveI : is_filtered_or_empty {i // i < j} :=
      { cocone_objs := λ i i',
          ⟨⟨lattice.has_sup.sup i i', lattice.sup_lt_iff.mpr ⟨i.property, i'.property⟩⟩,
           ⟨⟨⟨lattice.le_sup_left⟩⟩⟩, ⟨⟨⟨lattice.le_sup_right⟩⟩⟩⟩,
        cocone_maps := λ i i' f f', ⟨i', ⟨⟨le_refl _⟩⟩, rfl⟩ },
      refine filtered_colimit_closed_embedding _ _ hlim ⟨i, h⟩,
      rintros i' i'' ⟨⟨h'⟩⟩,
      apply ih,
      exact i''.property } }
end

end
