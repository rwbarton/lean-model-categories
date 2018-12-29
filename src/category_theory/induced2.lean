import category_theory.fully_faithful
import category_theory.full_subcategory

universes u₁ u₂ v

namespace category_theory

variables {C : Type u₁} {D : Type u₂} [𝒟 : category.{u₂ v} D] (f : C → D)
include 𝒟 f

def induced_category : Type u₁ := C

instance induced_category.category : category.{u₁ v} (induced_category f) :=
{ hom := λ x y, f x ⟶ f y,
  id := λ x, 𝟙 _,
  comp := λ _ _ _ f g, f ≫ g }

def induced_functor : induced_category f ⥤ D :=
{ obj := f, map := λ x y f, f }

instance induced_category.fully_faithful : fully_faithful (induced_functor f) :=
{ preimage := λ x y f, f }

section tmp
-- simp lemmas for full_subcategory_inclusion.
-- We should probably implement full_subcategory_inclusion in terms of induced_category,
-- though

@[simp] lemma full_subcategory_inclusion_obj (Z : D → Prop) (X) :
  (full_subcategory_inclusion Z).obj X = X.val :=
rfl

@[simp] lemma full_subcategory_inclusion_map (Z : D → Prop) {X Y} (f : X ⟶ Y) :
  (full_subcategory_inclusion Z).map f = f :=
rfl

end tmp

end category_theory
