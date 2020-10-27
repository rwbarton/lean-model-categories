import category_theory.category
import category_theory.isomorphism
import category_theory.eq_to_hom
import category_theory.opposites

universes v v' u u'

namespace category_theory

variables (C : Type u) [𝒞 : category.{v} C]
include 𝒞

/-- A morphism class is any collection of the morphisms of C. -/
def morphism_class : Type (max u v) := Π ⦃X Y : C⦄, set (X ⟶ Y)

instance : has_inter (morphism_class C) := ⟨λ I J X Y f, I f ∧ J f⟩

instance : has_subset (morphism_class C) := ⟨λ I J, ∀ ⦃X Y⦄ ⦃f : X ⟶ Y⦄, I f → J f⟩

def morphism_class.op (I : morphism_class C) : morphism_class Cᵒᵖ := λ Y X f, I f

def morphism_class.univ : morphism_class C := λ X Y f, true

def morphism_class.isos : morphism_class C := λ X Y f, nonempty (is_iso f)

variables {C}

lemma morphism_class.inter_subset_left {I J : morphism_class C} : I ∩ J ⊆ I :=
λ X Y f hf, hf.1

lemma morphism_class.inter_subset_right {I J : morphism_class C} : I ∩ J ⊆ J :=
λ X Y f hf, hf.2

@[extensionality] def morphism_class.ext {I J : morphism_class C}
  (h : ∀ x y (f : x ⟶ y), I f ↔ J f) : I = J :=
by ext x y f; apply h

lemma morphism_class.subset_antisymm {I J : morphism_class C} (h : I ⊆ J) (h' : J ⊆ I) :
  I = J :=
by ext; tauto

variables (I : morphism_class C)

@[simp] lemma of_eq_left {X' X Y} (f : X ⟶ Y) (e : X' = X) : I (eq_to_hom e ≫ f) ↔ I f :=
by subst e; simp

@[simp] lemma of_eq_right {X Y Y'} (f : X ⟶ Y) (e : Y = Y') : I (f ≫ eq_to_hom e) ↔ I f :=
by subst e; simp

section
variables {D : Type u'} [𝒟 : category.{v'} D]
include 𝒟

def morphism_class.preimage (F : C ⥤ D) (I : morphism_class D) : morphism_class C :=
λ X Y f, I (F.map f)
end

end category_theory
