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
   --exact is_wfs.retract ⟨ Fβ, h.weq.weq_cancel_left WCα.2 hf ⟩,
end

omit 𝓜
class model_category (M : Type u) extends category.{v} M :=
(complete : has_limits M)
(cocomplete : has_colimits M)
(W C F : morphism_class M)
(h : is_model_category W C F)

variables {M}
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
  exact acf.retract this g_ac
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
