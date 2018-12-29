import category_theory.discrete_category
import top_small

universe u

open category_theory category_theory.limits

namespace homotopy_theory.topological_spaces

section

parameters {Iι : Type u} {IA IB : Iι → Top.{u}} (If : Π i, IA i ⟶ IB i)
parameters (I : morphism_class Top.{u})

-- The generating morphisms belong to I
parameters (hIf : ∀ i, I (If i))

-- I is closed under pushouts ...
parameters (hI_pushout : ∀ {A B X Y : Top} {i : A ⟶ X} {f : A ⟶ B} {g : X ⟶ Y} {j : B ⟶ Y}
  (po : Is_pushout i f g j), I i → I j)

-- ... and coproducts ...
parameters (hI_coprod : ∀ {ι : Type u} {A B : ι → Top.{u}} (f : Π i, A i ⟶ B i),
  (∀ i, I (f i)) → I (colim.map (nat_trans.of_function f))) -- FIXME?

/- No, this is for later. (Also smallness of domains.)
-- ... and transfinite compositions:
parameters (hI_tcomp : ∀ {γ : Type u} [lattice.order_top γ] [is_well_order γ (<)]
  (c : transfinite_composition I γ), I c.composition)
-/

/-
def I' : morphism_class Top.{u} :=
λ X Y f, I f ∧
-/

-- One step of the small object argument.
def small_object_argument_step {X Y : Top.{u}} (g : X ⟶ Y) :
  Σ' (X' : Top.{u}) (j : X ⟶ X') (g' : X' ⟶ Y), g = j ≫ g' ∧ I j ∧
  ∀ ⦃i⦄ (h : IA i ⟶ X) (k : IB i ⟶ Y), If i ≫ k = h ≫ g →
  ∃ l : IB i ⟶ X', If i ≫ l = h ≫ j ∧ l ≫ g' = k :=
/- Form the collection S of all squares
        h
   IA i → X
If i ↓     ↓ g
   IB i → Y
        k      -/
let S : Type u := Σ' i h k, If i ≫ k = h ≫ g,
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
 hI_pushout po.is_pushout $ hI_coprod _ (λ (s : S), hIf s.1),
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

--def soa {X Y : Top.{u}} (g : X ⟶ Y) :

end

end homotopy_theory.topological_spaces
