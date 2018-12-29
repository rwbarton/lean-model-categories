import category_theory.cone_stuff
import category_theory.full_subcategory
import category_theory.morphism_class
import category_theory.limits.limits
import category_theory.preorder_hom
import order.well_order_top
import category_theory.stuff
import category_theory.limit_stuff

universes u u' v

namespace category_theory
open category_theory.limits
open well_order_top

section smooth_at
variables {γ : Type v} [well_order_top γ]

-- A functor F : γ → C is smooth at j : γ if F(j) is the colimit of F(i) over i < j.

def cocone_at (j : γ) : cocone (full_subcategory_inclusion (λ i, i < j)) :=
{ X := j, ι := { app := λ i, ⟨⟨le_of_lt i.property⟩⟩ } }

@[simp] lemma cocone_at_X (j : γ) : (cocone_at j).X = j := rfl

variables {C : Type u} [category.{u v} C]

def smooth_at (F : γ ⥤ C) (j : γ) : Prop :=
nonempty (is_colimit (F.map_cocone (cocone_at j)))

section

variables
  {α : Type v} [well_order_top α]
  {β : Type v} [well_order_top β]
  (f : initial_seg ((<) : α → α → Prop) ((<) : β → β → Prop))

lemma smooth_at_iff_restriction_smooth_at (F : β ⥤ C) (j : α) :
  smooth_at F (f.to_fun j) ↔ smooth_at (f.to_functor ⋙ F) j :=
equiv.nonempty_iff_nonempty $
  whisker_left_equivalence_preserves_colimits (preorder_equivalence (restrict_Io f j))

end

end smooth_at


variables {C : Type u} [𝒞 : category.{u v} C]
include 𝒞

variables (I : morphism_class C)

variables (γ : Type v) [well_order_top γ]
--local attribute [instance] well_order_top.has_bot

structure transfinite_composition :=
(F : γ ⥤ C)
(succ : ∀ (i j : γ) (h : is_succ i j), I (F.map ⟨⟨h.le⟩⟩))
(limit : ∀ (j : γ), is_limit j → smooth_at F j) -- maybe just inline `smooth_at`?

variables {I γ}

def transfinite_composition.composition
  (c : transfinite_composition.{u v} I γ) : c.F.obj ⊥ ⟶ c.F.obj ⊤ :=
c.F.map ⟨⟨lattice.le_top⟩⟩

section restrict

noncomputable def transfinite_composition.restrict (c : transfinite_composition I (Ic (⊤ : γ))) :
  transfinite_composition I γ :=
{ F := initial_seg.to_functor (initial_seg.of_iso iso_Ic_top) ⋙ c.F,
  succ := λ i j h, c.succ _ _ (is_succ_iff.mpr h),
  limit := λ j h,
    (smooth_at_iff_restriction_smooth_at _ _ j).mp (c.limit _ (is_limit_iff.mpr h)) }
end restrict

section

variables {J : morphism_class C}

def transfinite_composition.cast (h : ∀ a b (f : a ⟶ b), I f → J f)
  (c : transfinite_composition I γ) : transfinite_composition J γ :=
⟨c.F, λ i j hij, h _ _ _ (c.succ i j hij), c.limit⟩

end

section

variables {D : Type u'} [𝒟 : category.{u' v} D]
include 𝒟

variables {J : morphism_class D}
variables (F : C ⥤ D) [preserves_colimits F]

def transfinite_composition.map (c : transfinite_composition (J.preimage F) γ) :
  transfinite_composition J γ :=
{ F := c.F ⋙ F,
  succ := λ i j hij, c.succ i j hij,
  limit := λ j hj, (c.limit j hj).map (preserves_colimit.preserves F)  }

def transfinite_composition.map' (c : transfinite_composition I γ)
  (hIJ : ∀ {X Y} {f : X ⟶ Y}, I f → J (F.map f)) : transfinite_composition J γ :=
{ F := c.F ⋙ F,
  succ := λ i j hij, hIJ (c.succ i j hij),
  limit := λ j hj, (c.limit j hj).map (preserves_colimit.preserves F)  }

end

end category_theory
