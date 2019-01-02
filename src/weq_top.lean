import homotopy_theory.topological_spaces.weak_equivalences
import homotopy_theory.formal.cylinder.sdr
import homotopy_theory.formal.i_category.cylinder_object
import homotopy_theory.formal.i_category.dold
import wfs_top
import distrib_stuff
import weq_stuff

open category_theory category_theory.limits
open homotopy_theory.topological_spaces homotopy_theory.cylinder homotopy_theory.cofibrations

local notation `Top` := Top.{0}

namespace model_top

def ctiwe : morphism_class Top := @closed_t1_inclusion ∩ @is_weak_equivalence

lemma lifting_compact (D : gen_lifting_data) (hb : compact_space D.b)
  {γ : Type} [well_order_top γ] (hγ : cardinal.omega ≤ well_order_top.cofinality γ)
  (c : transfinite_composition @closed_t1_inclusion γ)
  (hc : ∀ (j < ⊤), gen_lifting_condition D (c.F.map ⟨⟨(lattice.bot_le : ⊥ ≤ j)⟩⟩)) :
  gen_lifting_condition D c.composition :=
begin
  intros h k s,
  rcases compact_small_closed_t1_inclusion γ hγ c k with ⟨j, hj, k', hk'⟩,
  rcases hc j hj h k' _ with ⟨l, m', hl, hm'₀, hm'₁⟩,
  refine ⟨l, m' ≫ c.F.map ⟨⟨(lattice.le_top : j ≤ ⊤)⟩⟩, hl, _, _⟩,
  { rw [←category.assoc, hm'₀, hk'] },
  { rw [←category.assoc, hm'₁, category.assoc, ←c.F.map_comp], refl },
  { haveI : mono (c.F.map ⟨⟨(lattice.le_top : j ≤ ⊤)⟩⟩) := begin
      rw Top.mono_iff_injective,
      exact (closed_embedding_tcomp (c.cast @closed_embedding_of_closed_t1_inclusion) _).1.1
    end,
    rw ←cancel_mono (c.F.map ⟨⟨(lattice.le_top : j ≤ ⊤)⟩⟩),
    rw [category.assoc, hk', category.assoc, ←c.F.map_comp, s], refl }
end

--- Hovey, 2.4.8
lemma ctiwe_tcomp : closed_under_tcomp ctiwe :=
begin
-- TODO: Induction principle for this style of argument, including restriction step?
  intros γ Iγ c, resetI,
  refine ⟨closed_t1_inclusion_tcomp (c.cast morphism_class.inter_subset_left), _⟩,
  suffices : ∀ j, is_weak_equivalence (c.F.map ⟨⟨(lattice.bot_le : ⊥ ≤ j)⟩⟩),
  { exact this ⊤ },
  refine well_founded.fix (well_order_top.wf_lt γ) _,
  intros j IH,
  rcases well_order_top.is_bot_or_succ_or_limit j with ⟨_, hj⟩|⟨i, j, hj⟩|⟨_, hj⟩,
  { change j = ⊥ at hj,
    subst j,
    convert is_weak_equivalence_iso (iso.refl _),
    exact c.F.map_id _ },
  { have := (c.succ i j hj).2,
    convert is_weak_equivalence_comp (IH i hj.lt) this,
    rw ←c.F.map_comp,
    refl },
  { let c' := c.below j,
    change is_weak_equivalence c'.composition,
    rw weq_iff,
    intro i,
    refine lifting_compact (weq_D i) (weq_compact i) _
      (c'.cast morphism_class.inter_subset_left) _,
    { apply transfinite.cofinality_of_is_limit,
      rw well_order_top.is_limit_iff,
      exact hj },
    { intros j' hj',
      have := IH j'.val hj',
      rw weq_iff at this,
      exact this i } }
end

def sdr : morphism_class Top := λ a b f, is_sdr_inclusion f

def ctisdr : morphism_class Top := @closed_t1_inclusion ∩ sdr

lemma ctisdr_ctiwe : ctisdr ⊆ ctiwe :=
λ a b f ⟨hf₁, ⟨⟨r, h, H⟩⟩⟩,
⟨hf₁,
 -- Compare heq_iff_sdr_inclusion.
 is_weak_equivalence_of_heq _ $ homotopy_equivalence_iff.mpr
   ⟨r, by convert homotopic.refl (𝟙 a), H.forget_rel⟩⟩

lemma sdr_pushouts : closed_under_pushouts sdr := λ a b a' b' f f' i j po hf,
pushout_of_sdr_inclusion po (preserves_pushouts.Is_pushout_of_Is_pushout _ po) hf

lemma ctisdr_pushouts : closed_under_pushouts ctisdr :=
closed_under_pushouts_inter @closed_t1_inclusion_pushout sdr_pushouts

lemma {u v} sigma.eq' {ι : Type u} {α : ι → Type v} {i : ι} {x y : α i} :
  sigma.mk i x = sigma.mk i y ↔ x = y :=
by split; cc

-- TODO: Prove this for any I-category (assuming I preserves coproducts)
lemma ctisdr_coproducts : closed_under_coproducts ctisdr :=
closed_under_coproducts_inter @closed_t1_inclusion_coproduct $
closed_under_coproducts_of_coproduct @Top_coproduct @Top_coproduct_is_colimit
  (closed_under_isos_of_closed_under_pushouts sdr_pushouts) $ λ ι a b f hf,
begin
  replace hf := λ i, classical.choice (hf i),
  refine ⟨⟨Top_coproduct.map (nat_trans.of_function (λ i, (hf i).r)), _, _⟩⟩,
  { ext p,
    rcases p with ⟨i, x⟩,
    change sigma.mk i _ = sigma.mk i x,
    congr,
    exact Top.hom_congr (hf i).h x },
  { have : ∀ i, ∃ H : homotopy _ _, H.is_rel _ := λ i, (hf i).H,
    choose H hH using this,
    let H' := Top_coproduct.map (nat_trans.of_function (λ i, (H i).H)),
    refine ⟨⟨Top_distrib _ _ ≫ H', _, _⟩, _⟩,
    { ext p,
      rcases p with ⟨i, x⟩,
      apply sigma.eq'.mpr,
      exact Top.hom_congr (H i).Hi₀ x },
    { ext p,
      rcases p with ⟨i, x⟩,
      apply sigma.eq'.mpr,
      exact Top.hom_congr (H i).Hi₁ x },
    { ext p,
      rcases p with ⟨⟨i, x⟩, t⟩,
      apply sigma.eq'.mpr,
      exact Top.hom_congr (hH i) ⟨x, t⟩ } }
end

-- TODO: Prove this for any I-category
-- TODO: Add extensionality lemma for I01?
lemma sdr_i {X : Top} : sdr ((i 0).app X) :=
begin
  refine ⟨⟨p.app X, pi_components 0, ⟨⟨_, _, _⟩, _⟩⟩⟩,
  { refine Top.mk_hom -- x = p.1.1, t = p.1.2, u = p.2
      (λ p, ⟨p.1.1, ⟨p.1.2.1 * p.2.1, mul_nonneg p.1.2.2.1 p.2.2.1, mul_le_one p.1.2.2.2 p.2.2.1 p.2.2.2⟩⟩) _,
    continuity },
  all_goals {
    ext x,
    refl,
    cases x with x t,
    apply subtype.eq,
    apply mul_zero <|> apply mul_one <|> apply zero_mul
  }
end

lemma ctisdr_J (n : ℕ) : ctisdr ((i 0).app (disk n)) :=
⟨closed_t1_inclusion_of_closed_embedding_t1 _ embedding_i closed_i, sdr_i⟩

lemma top_soa' {X Y : Top} (g : X ⟶ Y) :
  ∃ Z (j : X ⟶ Z) (q : Z ⟶ Y), ctiwe j ∧ rlp serre_J q ∧ j ≫ q = g :=
let ⟨Z, j, q, hg, hj, hq⟩ := soa_stmt Js ctisdr ctiwe
  (λ i, ctisdr_J i)
  (λ a b a' b' f i j f' po hf, ctisdr_pushouts po hf)
  (λ ι a b f hf, ctisdr_coproducts hf)
  (λ γ I₁ c, by exactI ctiwe_tcomp (c.cast ctisdr_ctiwe)) 
  (λ i, transfinite.κ_small_mono (λ a b f hf, hf.1)
     (@compact_small_closed_t1_inclusion _ (show compact_space (disk i), by apply_instance)))
  ((ordinal.omega + 1).out.α)
  (by convert le_refl _; convert ←out_cofinality; exact ordinal.cof_omega) g in
⟨Z, j, q, hj, begin rintros a b f ⟨i⟩, exact hq i end, hg.symm⟩

lemma π_induced_congr (n : ℕ) {X Y : Top} {f g : X ⟶ Y} {x : X} (e : f = g) :
  π_induced n x f ≫ eq_to_hom (by congr; exact Top.hom_congr e x) = π_induced n x g :=
by cases e; refl

lemma π_induced_congr' (n : ℕ) {X Y : Top} {f : X ⟶ Y} {x x' : X} (e : x = x') :
  eq_to_hom (by congr; exact e) ≫ π_induced n x' f =
  π_induced n x f ≫ eq_to_hom (by congr; exact congr_arg f e) :=
by cases e; refl

lemma W_retracts {a b a' b'} {f : a ⟶ b} {f' : a' ⟶ b'} (r : retract f f') :
  is_weak_equivalence f → is_weak_equivalence f' :=
begin
  rintro ⟨h0, hn⟩,
  refine ⟨_, λ n x, _⟩,
  { have : retract (π₀.map f) (π₀.map f') := π₀.on_retract r,
    rw h_is_iso at ⊢ h0,
    exact nonempty.map (retract_is_iso this) h0 },
  { have : retract (π_induced n (r.ia x) f) (π_induced n x f'),
    { -- Compare functor.on_retract
      refine ⟨π_induced n x r.ia, π_induced n (r.ia x) r.ra ≫ eq_to_hom _,
              π_induced n (f' x) r.ib ≫ eq_to_hom _, π_induced n _ r.rb ≫ eq_to_hom _,
              _, _, _, _⟩,
      { congr, exact Top.hom_congr r.ha x },
      { congr, exact (Top.hom_congr r.hi x).symm },
      { congr, convert (Top.hom_congr r.hr _).symm,
        change f' x = f' ((r.ia ≫ r.ra) x),
        rw Top.hom_congr r.ha x, refl },
      { rw [←category.assoc, ←π_induced_comp, π_induced_congr, π_induced_id], refl },
      { slice_lhs 2 3 { rw π_induced_congr' },
        slice_lhs 1 2 { rw [←π_induced_comp, ←π_induced_congr n r.hb.symm, π_induced_id] },
        simp, refl },
      { rw [←π_induced_comp, ←category.assoc, ←π_induced_comp, π_induced_congr],
        exact r.hi.symm },
      { rw [category.assoc, π_induced_congr'],
        rw [←category.assoc, ←π_induced_comp, ←category.assoc, ←π_induced_comp],
        rw [←π_induced_congr n r.hr],
        simp, refl } },
    replace hn := hn n (r.ia x),
    rw h_is_iso at ⊢ hn,
    exact nonempty.map (retract_is_iso this) hn }
end

lemma AC_sub_W : llp (rlp serre_J) ⊆ @is_weak_equivalence := λ a b f hf,
let ⟨a', b', f', r, hf'₁, hf'₂⟩ := retract_argument serre_acf @top_soa' f hf in
W_retracts r hf'₂

end model_top
