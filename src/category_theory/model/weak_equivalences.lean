import category_theory.morphism_class

universes v u

namespace category_theory

variables {M : Type u} [𝓜 : category.{v} M]
include 𝓜

structure is_weak_equivalences (W : morphism_class M) : Prop :=
(weq_of_iso : ∀ x y (i : x ≅ y), W i.hom)
(weq_comp : ∀ x y z (f : x ⟶ y) (g : y ⟶ z), W f → W g → W (f ≫ g))
(weq_cancel_left : ∀ {x y z} {f : x ⟶ y} {g : y ⟶ z}, W f → W (f ≫ g) → W g)
(weq_cancel_right : ∀ {x y z} {f : x ⟶ y} {g : y ⟶ z}, W g → W (f ≫ g) → W f)

end category_theory
