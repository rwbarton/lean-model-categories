import category_theory.limits.limits
import category_theory.model.wfs
import category_theory.model.weak_equivalences
import category_theory.retract

universes v u

namespace category_theory
open category_theory.limits

variables {M : Type u} [𝓜 : category.{v} M]
include 𝓜

structure is_model_category (W C F : morphism_class M) : Prop :=
(weq : is_weak_equivalences W)
(caf : is_wfs C (F ∩ W))
(acf : is_wfs (C ∩ W) F)

-- TODO: Show that it follows that W is closed under retracts. See
-- https://ncatlab.org/nlab/show/model+category#ClosureOfMorphisms

lemma is_model_category.weq_of_weq_retract_fib { W C F : morphism_class M } ( h : is_model_category W C F )
 {a b a' b'} {f : a ⟶ b} {f' : a' ⟶ b'} (r : retract f f') (hf : W f) (hf': F f') : W f' := begin
   rcases h.acf.fact f with ⟨ c, α, β, WCα, Fβ, f_fact ⟩,
   rw h.acf.llp at WCα,
   choose l hl using WCα hf' r.ra (β ≫ r.rb) (by { rw [← category.assoc, f_fact], exact r.hr }), 
   have rβf' : retract β f' := {
     ia := (r.ia) ≫ α,
     ra := l,
     ib := r.ib,
     rb := r.rb,
     ha := by { simp, rw hl.1, exact r.ha },
     hb := r.hb,
     hi := by { rw [category.assoc, f_fact], exact r.hi },
     hr := hl.2,
   },
   rw ← h.acf.llp at WCα,
   rw ← f_fact at hf,
   exact (is_wfs.retract_right h.caf rβf' ⟨ Fβ, h.weq.weq_cancel_left WCα.2 hf ⟩).2
end

#check @Is_pushout.uniqueness

lemma is_model_category.weq_of_weq_retract { W C F : morphism_class M } [ @has_pushouts M 𝓜] ( h : is_model_category W C F )
 {a b a' b'} {f : a ⟶ b} {f' : a' ⟶ b'} (r : retract f f') (hf : W f) : W f' := begin
   rcases h.acf.fact f' with ⟨ c, α, β, WCα, Fβ, f'_fact ⟩,
   cases has_pushouts.pushout α r.ia with z γ δ po,
   have WCδ : (C ∩ W) δ := by { rw h.acf.llp, rw h.acf.llp at WCα, exact llp_pushout F po WCα },
   have uq := @Is_pushout.uniqueness M 𝓜 a' c a z α r.ia γ δ po,
   have rεβ : retract (po.induced (β ≫ r.ib) f (by { rw [← category.assoc, f'_fact], exact r.hi.symm})) β := {
     ia := γ,
     ra := po.induced (𝟙 c) (r.ra ≫ α) (by { rw [category.comp_id, ← category.assoc, r.ha, category.id_comp] }),
     ib := r.ib,
     rb := r.rb,
     ha := by simp,
     hb := r.hb,
     hi := by simp,
     hr := by { 
      refine uq _ _, 
      rw [← category.assoc,
          Is_pushout.induced_commutes₀ po _ _ _,
          ← category.assoc, 
          Is_pushout.induced_commutes₀ po _ _ _, 
          category.assoc,
          category.id_comp,
          r.hb,
          category.comp_id],
      rw [← category.assoc,
          Is_pushout.induced_commutes₁ po _ _ _,
          ← category.assoc,
          Is_pushout.induced_commutes₁ po _ _ _,
          category.assoc,
          f'_fact,
          r.hr],
      }
    },
   rw ← f'_fact,
   apply h.weq.weq_comp a' c b' α β WCα.2,
   refine is_model_category.weq_of_weq_retract_fib h rεβ _ Fβ,
   apply h.weq.weq_cancel_left WCδ.2,
   rw Is_pushout.induced_commutes₁ po _ _ _,
   assumption,
end

omit 𝓜
class model_category (M : Type u) extends category.{v} M :=
(complete : has_limits M)
(cocomplete : has_colimits M)
(W C F : morphism_class M)
(h : is_model_category W C F)

-- variables { C: Type u } [mc: model_category C] {a b : C} { f: a ⟶ b }
-- lemma model_category.weq_of_weq_retract { C: Type u } [mc: model_category C]
--  {a b a' b' : C} {f : a ⟶ b} {f' : a' ⟶ b'} (r : retract f f') ( hf : W f ) : W f' := 
-- begin
  
-- end
include 𝓜

/-- We can skip checking the condition C ∩ W ⊆ AC. Compare Hirschhorn, Theorem 11.3.1. -/
-- TODO: we can also omit "AC ⊆ C" because it follows from AF ⊆ F, right?
lemma is_model_category.mk' {W C AF AC F : morphism_class M}
  (weq : is_weak_equivalences W)
  (caf : is_wfs C AF) (acf : is_wfs AC F)
  (hAF : AF = F ∩ W) (hAC : AC ⊆ W) :
  is_model_category W C F :=
suffices C ∩ W ⊆ AC, begin
  refine ⟨weq, _, _⟩,
  { convert ←caf },
  { convert ←acf,
    refine morphism_class.subset_antisymm _ this,
    intros a b f hf,
    refine ⟨_, hAC hf⟩,
    rw acf.llp at hf,
    rw caf.llp,
    revert a b,
    apply llp_anti,
    intros x y g hg,
    rw hAF at hg,
    exact hg.1 }
end,
begin
  rintros a b f ⟨f_c, f_w⟩,
  rcases acf.fact f with ⟨c, g, h, g_ac, h_f, gh⟩,
  have h_w : W h,
  { apply weq.weq_cancel_left (hAC g_ac),
    convert f_w },
  have h_af : AF h, by rw hAF; exact ⟨h_f, h_w⟩,
  -- TODO: use retract_argument
  rcases caf.lp f_c h_af g (𝟙 b) (by rw gh; simp) with ⟨l, hl₁, hl₂⟩,
  have : retract g f,
  { refine ⟨𝟙 a, 𝟙 a, l, h, _, _, _, _⟩,
    all_goals { tidy } },
  exact acf.retract_left this g_ac
end

def model_category.mk' [has_limits M] [has_colimits M] {W C AF AC F : morphism_class M}
  (weq : is_weak_equivalences W)
  (caf : is_wfs C AF) (acf : is_wfs AC F)
  (hAF : AF = F ∩ W) (hAC : AC ⊆ W) : model_category M :=
{ complete := by apply_instance,
  cocomplete := by apply_instance,
  W := W,
  C := C,
  F := F,
  h := by apply is_model_category.mk'; apply_assumption,
  to_category := (infer_instance : category M) }

end category_theory
