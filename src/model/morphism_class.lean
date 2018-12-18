import categories.category

open categories

-- Fix a category C.
universe u
variable (C : Type (u+2))
variable [category C]


namespace model

-- A class of morphisms in a category (with no conditions).
-- Use as a predicate; e.g., is_weq : MorphismClass C, is_weq f : Prop
def MorphismClass : Type (u+2) :=
  Π {{X Y : C}}, set (Hom X Y)

/- This isn't really useful; I don't understand why.
   Attempting to use it results in 
failed to synthesize type class instance for [...]
⊢ has_mem (X ⟶ Y) (MorphismClass C)
-/
instance {X Y : C} : has_mem (Hom X Y) (MorphismClass C) :=
  ⟨λ f cl, cl f⟩

instance : has_inter (MorphismClass C) :=
  ⟨λ cl1 cl2, λ {{X Y}}, @cl1 X Y ∩ @cl2 X Y⟩

end model
