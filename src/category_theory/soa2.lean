import category_theory.transfinite.construction
import category_theory.limits.over
import category_theory.colimits
import category_theory.small
import category_theory.model.wfs
import .soa

noncomputable theory

open category_theory category_theory.functor category_theory.limits category_theory.transfinite
open well_order_top

universes u v

namespace category_theory
section

parameters {C : Type u} [𝒞 : category.{u v} C] [has_colimits C] [has_pushouts.{u v} C]
include 𝒞

-- A set of "generating" maps
parameters {Iι : Type v} {IA IB : Iι → C} (If : Π i, IA i ⟶ IB i)

parameters (K K₁ : morphism_class C)

-- The generating morphisms belong to K
parameters (hIf : ∀ i, K (If i))

-- K is closed under pushouts ...
parameters (hK_pushout : ∀ {A B X Y} {i : A ⟶ X} {f : A ⟶ B} {g : X ⟶ Y} {j : B ⟶ Y}
  (po : Is_pushout i f g j), K i → K j)

-- ... and coproducts ...
parameters (hK_coprod : ∀ {ι : Type v} {A B : ι → C} (f : Π i, A i ⟶ B i),
  (∀ i, K (f i)) → K (colim.map (nat_trans.of_function f))) -- FIXME?

-- ... and transfinite compositions of maps of K belong to K₁
parameters (hK₁_tcomp : ∀ {γ : Type v} [well_order_top γ]
  (c : transfinite_composition K γ), K₁ c.composition)

-- Domains of the generating maps are κ-small w.r.t. K, and γ has cofinality ≥ κ
parameters {κ : cardinal.{v}} (A_small : ∀ ⦃i⦄, κ_small K κ (IA i))
parameters (γ : Type v) [well_order_top γ]
parameters (hκ : κ ≤ cofinality γ)

-- THEN, any map can be factored into a map from K₁ followed by a map
-- with the RLP w.r.t. the generating maps If.

def small_object_argument_step {X Y : C} (g : X ⟶ Y) :
  Σ' (X' : C) (j : X ⟶ X') (g' : X' ⟶ Y), g = j ≫ g' ∧ K j ∧
  ∀ ⦃i⦄ (h : IA i ⟶ X) (k : IB i ⟶ Y), If i ≫ k = h ≫ g →
  ∃ l : IB i ⟶ X', If i ≫ l = h ≫ j ∧ l ≫ g' = k :=
/- Form the collection S of all squares
        h
   IA i → X
If i ↓     ↓ g
   IB i → Y
        k      -/
let S : Type v := Σ' i h k, If i ≫ k = h ≫ g,
    A := colimit (functor.of_function (λ (s : S), IA s.1)),
    B := colimit (functor.of_function (λ (s : S), IB s.1)),
    f : A ⟶ B := colim.map (nat_trans.of_function (λ (s : S), If s.1)),
    h : A ⟶ X := colimit.desc (functor.of_function (λ (s : S), IA s.1))
      (cocone.of_function X (λ (s : S), s.2.1)),
    k : B ⟶ Y := colimit.desc (functor.of_function (λ (s : S), IB s.1))
      (cocone.of_function Y (λ (s : S), s.2.2.1)),
    po := has_pushouts.pushout f h,
    X' := po.ob in
have f ≫ k = h ≫ g, begin
  apply colimit.hom_ext,
  intro s,
  rw [colimit.map_desc, colimit.ι_desc],
  rw [←category.assoc, colimit.ι_desc],
  change If s.1 ≫ s.2.2.1 = s.2.1 ≫ g,
  exact s.2.2.2
end,
⟨X', po.map₁, po.is_pushout.induced k g this, by simp,
 hK_pushout po.is_pushout $ hK_coprod _ (λ (s : S), hIf s.1),
 begin
   intros i h' k' q,
   let s : S := ⟨i, h', k', q⟩,
   refine ⟨colimit.ι (functor.of_function (λ (s : S), IB s.1)) s ≫ po.map₀, _, _⟩,
   { have : If i ≫ colimit.ι (functor.of_function (λ (s : S), IB s.1)) s =
       colimit.ι (functor.of_function (λ (s : S), IA s.1)) s ≫ f, by rw colim.ι_map; refl,
     rw [←category.assoc, this, category.assoc, po.is_pushout.commutes, ←category.assoc],
     simp, refl },
   { simp, refl }
 end⟩

section
parameter (Y : C)  -- Fix Y, and work in the category C/Y.

/-- A map X → X' in C/Y belongs to K' if the underlying map X → X' of
  C belongs to K, and also any lifting problem from a generating map to X → Y
  admits a lift to X'. -/
def K' : morphism_class (over Y) :=
λ X X' g,
  K (by exact g.left) ∧
  ∀ ⦃i⦄ (h : IA i ⟶ X.left) (k : IB i ⟶ Y), If i ≫ k = h ≫ X.hom →
  ∃ l : IB i ⟶ X'.left, If i ≫ l = h ≫ g.left ∧ l ≫ X'.hom = k

def soa_F : over Y → over Y :=
λ XY, over.mk (small_object_argument_step XY.hom).2.2.1

def soa_α : Π XY, XY ⟶ soa_F XY :=
λ XY, over.hom_mk (small_object_argument_step XY.hom).2.1
  (small_object_argument_step XY.hom).2.2.2.1.symm

lemma soa_K' : Π XY, K' (soa_α XY) :=
λ XY, (small_object_argument_step XY.hom).2.2.2.2

end

set_option eqn_compiler.zeta true

def soa2_factor {X Y : C} (g : X ⟶ Y) :
  Σ' (c : transfinite_composition K γ) (g' : c.F.obj ⊤ ⟶ Y),
  (∃ (h₀ : c.F.obj ⊥ = X), g = (eq_to_hom h₀.symm ≫ c.composition) ≫ g') ∧
  ∀ i, lp (If i) g' :=
let ⟨c', hc'⟩ :=
  @build_transfinite_composition (over Y) _ _ (K' Y) γ _
    (soa_F Y)
    (soa_α Y)
    (soa_K' Y)
    (over.mk g),
    c := c'.map' over.forget (λ X Y f hf, hf.1) in
⟨c, (c'.F.obj ⊤).hom,
 begin
   have := congr_arg (λ Z, over.forget.obj Z) hc',
   refine ⟨this, _⟩,
   dsimp [c, transfinite_composition.composition, transfinite_composition.map'],
   rw [category.assoc, over.over_w],
   apply category_theory.over.of_eq hc'.symm
 end,
 λ i h k s,
 let ⟨j, hj, h', hh'⟩ := A_small γ hκ c h,
     ⟨j', hj'⟩ := has_succ_of_lt hj,
     ⟨l, hl₁, hl₂⟩ := (c'.succ j j' hj').2 h' k $ begin
       rw [←s, ←hh', category.assoc],
       congr, apply over.over_w
     end in
 ⟨l ≫ c.F.map ⟨⟨lattice.le_top⟩⟩,
  begin
    rw [←category.assoc, hl₁, category.assoc, ←hh'],
    congr, change c.F.map _ ≫ _ = _, rw ←functor.map_comp, refl
  end,
  begin
    rw category.assoc,
    convert hl₂,
    apply over.over_w
  end⟩⟩

-- Repackage the conclusions
def soa_stmt {X Y : C} (g : X ⟶ Y) :
  Σ' Z (j : X ⟶ Z) (q : Z ⟶ Y), g = j ≫ q ∧ K₁ j ∧ ∀ i, lp (If i) q :=
let ⟨c, g', H, l⟩ := soa2_factor g in
have K₁c : K₁ c.composition := hK₁_tcomp c,
⟨c.F.obj ⊤, eq_to_hom H.fst.symm ≫ c.composition, g', H.snd, by rwa of_eq_left K₁, l⟩

end
end category_theory
