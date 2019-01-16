import category_theory.transfinite.extend1

noncomputable theory
local attribute [instance] classical.dec

universes v u

namespace category_theory.transfinite
namespace extend2
section

open category_theory category_theory.functor well_order_top

/- Note on building transfinite compositions

Suppose our aim is to construct a transfinite composition of some
particular "length" γ, γ being a well-ordered type with a greatest
element. This consists of a collection of objects X i for i : γ and
morphisms X i → X j for i j : γ, i ≤ j satisfying some conditions. We
want to construct these by transfinite recursion, forming a colimit at
limit stages and applying some other construction at successor stages.

This is tricky to do by a direct recursion because the objects and
morphisms depend on each other. Obviously the map we append at stage
i+1 must depend on the object X i, but at limit stages we need to form
the next object as a colimit and this construction depends on all the
previous maps. Moreover, in order to continue the construction and
form this colimit, we need to use the fact that the maps chosen so far
actually do define a functor.

In order to organize this construction, we apply the principle of
"consistent recursion". Namely, we will construct for each i : γ a
transfinite composition on the closed initial segment [⊥, i] of γ,
while requiring that for each i < j, the transfinite composition on
[⊥, i] is (strictly!) equal to the restriction of the transfinite
composition on [⊥, j]. (This condition relies on the ability to talk
about the *set* of objects of a category. If we wanted to use only
equivalence-invariant concepts, we'd need to instead construct
isomorphisms here which in turn satisfy some coherence conditions.)
At the end of the process, we have a transfinite composition on [⊥, ⊤]
which we transfer to the original type γ.

This section contains the building blocks for such a construction. For
each type of i (base case, successor case and limit case), we provide
a constructor for building a transfinite composition on [⊥, i] from
consistent transfinite compositions on the earlier segments, and a
lemma showing that the new transfinite composition is consistent with
the previous ones. We also provide a "finalizing" constructor which
transfers a transfinite composition on [⊥, ⊤] to γ.

(TODO: Probably want something more general for this last step, namely
restricting a transfinite composition along the inclusion of an
initial segment (ordinal.initial_seg). Then apply to γ → [⊥, ⊤].)

-/

-- General parameters for constructing a transfinite composition
parameters {C : Type u} [𝒞 : category.{v} C] [limits.has_colimits C]
include 𝒞
parameters {I : morphism_class C}
parameters {γ : Type v} [well_order_top γ]

parameters {k : γ} (Z : Π (i < k), transfinite_composition I (Ic i))
parameters (hZ : ∀ i i' (hik : i < k) (hi'k : i' < k) (hii' : i < i'),
  (Z i hik).F = (Ic_initial_seg_Ic (le_of_lt hii')).to_functor ⋙ (Z i' hi'k).F)

section bot
parameters (hk : is_bot k) (X : C)
include hk

lemma no (p : {p : Ic k // p < ⊤}) : false :=
hk.not_lt p.property

def extend_tcomp_bot_cone : limits.cocone (extend1.prev_F Z hZ) :=
{ X := X,
  ι :=
  { app := λ p, false.elim (no p),
    naturality' := λ p p' hpp', false.elim (no p) } }

def extend_tcomp_bot : transfinite_composition I (Ic k) :=
extend1.extend_tcomp Z hZ extend_tcomp_bot_cone
  (λ h hjk, false.elim $ not_bot_succ hk hjk)
  (λ hk', false.elim $ not_bot_limit hk hk')

lemma extend_tcomp_bot_bot : extend_tcomp_bot.F.obj ⊥ = X :=
begin
  convert ←(extend1.extend_tcomp_F_top Z hZ _),
  exact is_bot_iff_bot.mp (is_bot_iff.mpr hk)
end

end bot

section succ
parameters {j : γ} (hk : is_succ j k) {X : C} (f : (Z j hk.lt).F.obj ⊤ ⟶ X) (hf : I f)
include hf

def extend_tcomp_succ_cone : limits.cocone (extend1.prev_F Z hZ) :=
{ X := X,
  ι :=
  { app := λ p,
      (extend1.prev_F Z hZ).map (⟨⟨hk.le_of_lt_succ p.property⟩⟩ : p ⟶ ⟨⟨j, hk.le⟩, _⟩) ≫ f,
    naturality' := λ p p' hpp',
      by rw [←category.assoc, ←functor.map_comp]; exact (category.comp_id _ _).symm } }

def extend_tcomp_succ : transfinite_composition I (Ic k) :=
extend1.extend_tcomp Z hZ extend_tcomp_succ_cone
  (λ j' hj'k, begin
     have : j = j', from hk.uniq hj'k,
     subst j',
     change I (_ ≫ f),
     convert hf,
     convert category.id_comp _ _,
     apply category_theory.functor.map_id
   end)
  (λ hk', false.elim $ not_succ_limit hk hk')

end succ

section limit
parameters (hk : is_limit k)

def extend_tcomp_limit : transfinite_composition I (Ic k) :=
extend1.extend_tcomp Z hZ (limits.colimit.cocone _)
  (λ j hjk, false.elim $ not_succ_limit hjk hk)
  (λ _, limits.colimit.is_colimit _)

end limit

end
end extend2
end category_theory.transfinite
