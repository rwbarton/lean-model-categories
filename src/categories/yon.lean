import categories.category
import categories.isomorphism
import categories.types

import .pullback

open categories
open categories.isomorphism

universe u
variable {C : Type (u+1)}
variable [category C]

variables {X Y : C}
def postcomposition_with (f : X ⟶ Y) : Π {Z : C}, (Z ⟶ X) → (Z ⟶ Y) := λ Z g, g ≫ f
def precomposition_with (f : X ⟶ Y) : Π {Z : C}, (Y ⟶ Z) → (X ⟶ Z) := λ Z g, f ≫ g
notation f`↓*` := postcomposition_with f
notation f`↑*` := precomposition_with f

def postcomposition_with_1 (f : X ⟶ Y) : Π Z : C, (Z ⟶ X) → (Z ⟶ Y) := λ Z g, g ≫ f
def precomposition_with_1 (f : X ⟶ Y) : Π Z : C, (Y ⟶ Z) → (X ⟶ Z) := λ Z g, f ≫ g
notation f `↓*[`:2 Z `]`:2 := postcomposition_with_1 f Z
notation f `↑*[`:2 Z `]`:2 := precomposition_with_1 f Z

open function

lemma yoneda {f : X ⟶ Y} : (Π Z, Is_equiv (f↓* : Hom Z X → Hom Z Y)) → is_Isomorphism f := begin
  intro E,
  let g : Y ⟶ X := (E Y).e.inv_fun (𝟙 Y),
  -- By definition, g ≫ f = 𝟙 Y.
  have : g ≫ f = 𝟙 Y := (E Y).right_inv (𝟙 Y),
  -- f ≫ g = 𝟙 X? True after applying _ ≫ f by the above, and (E X) says that we can conclude.
  have h : (f ≫ g) ≫ f = 𝟙 X ≫ f := ♯,
  have : f ≫ g = 𝟙 X := injective_of_left_inverse (E X).left_inv h,
  exact ⟨g⟩
end

lemma coyoneda {f : X ⟶ Y} : (Π Z, Is_equiv (f↑* : Hom Y Z → Hom X Z)) → is_Isomorphism f := begin
  intro E,
  let g : Y ⟶ X := (E X).e.inv_fun (𝟙 X),
  -- By definition, f ≫ g = 𝟙 X.
  have : f ≫ g = 𝟙 X := (E X).right_inv (𝟙 X),
  -- g ≫ f = 𝟙 Y? True after applying f ≫ _ by the above, and (E Y) says that we can conclude.
  have h : f ≫ (g ≫ f) = f ≫ 𝟙 Y := ♯,
  have : g ≫ f = 𝟙 Y := injective_of_left_inverse (E Y).left_inv h,
  exact ⟨g⟩
end

-- Why punit? because we defined Is_equiv to relate two types in the same universe (oops?)
-- and unit lives only in Type 0, while Hom A X lives in Type u
notation `!` := λ _, punit.star

variables (X Y)
-- def terminal := Π A, Hom A X ≃ unit
-- ^ This is fine, but in view of 'product' below:
def terminal := Π A, Is_equiv (! : Hom A X → punit)

-- def product (Z : C) := Π A, Hom A Z ≃ Hom A X × Hom A Y
-- ^ Actually, this definition is wrong! the isomorphism needs to be _natural_ in A.
-- Or, we fix maps Z ⟶ X and Z ⟶ Y and then ask that the induced map on Hom A _ is
-- an isomorphism for every A.

universe v
def prod.and {α β γ : Type v} (f : α → β) (g : α → γ) : α → β × γ := λ a, ⟨f a, g a⟩

/-
This is probably a bad idea:

instance {α β γ : Type*} : has_coe_to_fun ((α → β) × (α → γ)) :=
  ⟨λ _, α → β × γ,
   λ p, match p with | ⟨f, g⟩ := λ a, (f a, g a) end⟩

Similarly "instance : has_coe_to_fun ()"

-/

notation f `&`:1 g:1 := prod.and f g

def product (Z : C) (pX : Z ⟶ X) (pY : Z ⟶ Y) := Π (A : C), Is_equiv (pX↓*[A] & pY↓*[A])
