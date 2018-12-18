import categories.category

namespace categories

universe u

@[reducible] def lift (p : Prop) : Type u := ulift (plift p)
@[reducible] def up {p : Prop} (H : p) : lift p := ulift.up (plift.up H)

instance category_of_preorder {C : Type (u+1)} [preorder C] : category C :=
  { Hom := λ X Y, lift (X ≤ Y),
    identity := λ X, up (le_refl X),
    compose := λ X Y Z ⟨⟨XY⟩⟩ ⟨⟨YZ⟩⟩, up (le_trans XY YZ) }

end categories
