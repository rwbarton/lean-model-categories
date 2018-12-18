import categories.category
import categories.isomorphism
import categories.retract
import categories.span

import model.basic
import model.morphism_class

open categories
open categories.isomorphism

-- Fix a category C.
universe u
variable {C : Type (u+2)}
variable [category C]


namespace model

-- XXX: Use "square" type?
-- XXX: how to mark notation ∙ as reducible?
-- XXX: Mark H ". obviously"? I guess that requires using a structure?
def square_admits_lift {A B X Y : C}
                       (f : A ⟶ B) (g : X ⟶ Y) (u : A ⟶ X) (v : B ⟶ Y)
                       (H : f ≫ v = u ≫ g) : Prop :=
  ∃ (h : B ⟶ X), u = f ≫ h ∧ v = h ≫ g-- u = h ∙ f ∧ v = g ∙ h

def LLP (right : MorphismClass C) : MorphismClass C :=
  λ {{A B}} (f : A ⟶ B),
  ∀ {X Y : C} (g : X ⟶ Y) (u : A ⟶ X) (v : B ⟶ Y) (H : f ≫ v = u ≫ g),
  right g → square_admits_lift f g u v H

def RLP (left : MorphismClass C) : MorphismClass C :=
  λ {{X Y}} (g : X ⟶ Y),
  ∀ {A B : C} (f : A ⟶ B) (u : A ⟶ X) (v : B ⟶ Y) (H : f ≫ v = u ≫ g),
  left g → square_admits_lift f g u v H


variable is_left : MorphismClass C
variable is_right : MorphismClass C

structure IsWFS : Prop :=
  -- Factorization.
  -- XXX We have a choice here: specify chosen factorization for each morphism?
  -- Let's try not for now, since it better matches the usual math concept,
  -- and see whether it is terrible
  (factor : ∀ {X Z : C} (f : X ⟶ Z), ∃ (Y : C) (fl : X ⟶ Y) (fr : Y ⟶ Z),
            is_left fl ∧ is_right fr ∧ f = fl ≫ fr)
  -- Lifting.
  (lift_left : is_left = LLP is_right)
  (lift_right : is_right = RLP is_left)

variable is_wfs : IsWFS is_left is_right
include is_wfs

def lift {A B X Y : C} (f : A ⟶ B) (g : X ⟶ Y) (u : A ⟶ X) (v : B ⟶ Y)
         (H : f ≫ v = u ≫ g) : is_left f → is_right g → square_admits_lift f g u v H :=
  λ lf rg, is_wfs.lift_left.subst lf g u v H rg

def id_is_left {A : C} : is_left (𝟙 A) := begin
  rw [is_wfs.lift_left, LLP], intros,
  rw square_admits_lift,
  existsi u,
  split, { simp }, { simp at H, assumption }
end

def iso_is_left {A B : C} (f : A ⟶ B) : is_Isomorphism f → is_left f := begin
  intros isof,
  rw [is_wfs.lift_left, LLP] at *, intros,
  rw square_admits_lift,
  existsi (isof.inverse ≫ u), split,
  { have := isof.witness_1, obviously },
  { have := isof.witness_2, obviously }
end

-- Should move C to a different letter (𝒞?)
def comp_is_left {A B B' : C} (f1 : A ⟶ B) (f2 : B ⟶ B') :
  is_left f1 → is_left f2 → is_left (f1 ≫ f2) := begin
  intros lf1 lf2,
  rw [is_wfs.lift_left, LLP] at *, intros,
  rw square_admits_lift,
  cases lf1 g u (f2 ≫ v) ♮ a with h1 _,
  cases lf2 g h1 v ♮ a with h2 _,
  existsi h2, split; { smt_eblast }
end

def pushout_is_left (c : cospan C) (s : square_on_cospan c) [IsPushout c s] :
  is_left c.f₁ → is_left s.i₂ := begin
  intro lf₁,
  rw [is_wfs.lift_left, LLP] at *, intros,
  rw square_admits_lift,
  have := s.H,
  -- Lift original map f₁ against g, producing h₁ : B₁ ⟶ X
  -- XXX: Marking the "H" field of square_on_cospan ". assumption" causes
  -- the ♮ below to fail, because it doesn't know how to consume auto_param
  -- (I guess). But ♯ works...
  cases lf₁ g (c.f₂ ≫ u) (s.i₁ ≫ v) ♮ a with h₁ _,

  -- Now, construct the induced map h : B₃ ⟶ X
  let s' : square_on_cospan c := ⟨h₁, u, ♮⟩,
  cases IsPushout.univ s s' with h _,

  -- Show it is a lift of i₂ against g
  existsi h, split,
  { smt_eblast },
  { -- In order to show that h ≫ g = v, we need to apply the universal
    -- property of the pushout B₃.
    let s'' : square_on_cospan c := ⟨s.i₁ ≫ v, u ≫ g, ♮⟩,
    apply equal_of_have_unique (IsPushout.univ s s''); { smt_eblast }
  }
end

def retract_is_left {A B : C} {f : A ⟶ B} (r : retract f) :
  is_left f → is_left r.f' := begin
  intro lf,
  rw [is_wfs.lift_left, LLP] at *, intros,
  rw square_admits_lift,

  have := r.Hr,
  cases lf g (r.rA ≫ u) (r.rB ≫ v) ♮ a with h₁ _,
  let h := r.iB ≫ h₁,
  existsi h, split,
  { have := r.Hi, have := r.HA, obviously },
  { have := r.HB, obviously }
end

-- Transfinite composition??

end model
