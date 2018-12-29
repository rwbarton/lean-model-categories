import category_theory.transfinite.extend2
import logic.crec

noncomputable theory

local attribute [instance] classical.dec

open category_theory category_theory.functor
open well_order_top

universes u v

namespace category_theory.transfinite
section

parameters {C : Type u} [𝒞 : category.{u v} C] [limits.has_colimits C]
include 𝒞

parameters {I : morphism_class C}

parameters {γ : Type v} [well_order_top γ]


variables (F : C → C) (α : Π X, X ⟶ F X) (hα : ∀ X, I (α X))
include hα

def build_transfinite_composition (X : C) :
  Σ' (c : transfinite_composition I γ), c.F.obj ⊥ = X :=
begin
  have ci : Π (i : γ), Σ' (c : transfinite_composition I (Ic i)),
    c.F.obj ⊥ = X,
  { refine crec (is_well_order.wf (<))
      (λ i i hii' c c', c.1.F = (Ic_initial_seg_Ic (le_of_lt hii')).to_functor ⋙ c'.1.F) _,
    rintros j ⟨Z, hZ⟩,
    let Z' := λ i hi, (Z i hi).1,
    rcases is_bot_or_succ_or_limit j with ⟨_,hj⟩|⟨i,_,hij⟩|⟨_,hj⟩;
    [refine ⟨⟨extend2.extend_tcomp_bot Z' hZ hj X, _⟩, _⟩,
     refine ⟨⟨extend2.extend_tcomp_succ Z' hZ hij (α _) (hα _), _⟩, _⟩,
     refine ⟨⟨extend2.extend_tcomp_limit Z' hZ hj, _⟩, _⟩],
    all_goals { try { apply extend1.extend_tcomp_F_extends } },
    apply extend2.extend_tcomp_bot_bot,
    all_goals
    { have : ⊥ < j,
      { apply bot_lt, intro h, apply not_bot_succ h hij <|> apply not_bot_limit h hj },
      have : (⊥ : Ic j) = (Ic_initial_seg_Ic (le_of_lt this)).to_functor.obj ⊥ := rfl,
      rw this,
      change (_ ⋙ extend1.extend_tcomp_F _ _ _).obj _ = _,
      rw ←extend1.extend_tcomp_F_extends,
      apply (Z ⊥ _).snd } },

  refine ⟨(ci ⊤).1.restrict, (ci ⊤).2⟩,
end

end
end category_theory.transfinite
