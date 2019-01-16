import category_theory.functor_category
import category_theory.isomorphism
import category_theory.eq_to_hom

-- TODO: Most of this is now redundant

universes v v' u u'

namespace category_theory
namespace functor

variables {C : Type u} [𝒞 : category.{v} C]
include 𝒞

@[simp] def change_hom (a b : C) {a' b' : C} (ea : a' = a) (eb : b' = b) (f : a ⟶ b) : a' ⟶ b' :=
eq_to_hom ea ≫ f ≫ eq_to_hom eb.symm

@[simp] lemma eq_to_hom_trans_assoc {X Y Z W : C} (p : X = Y) (q : Y = Z) (f : Z ⟶ W) :
  eq_to_hom p ≫ eq_to_hom q ≫ f = eq_to_hom (p.trans q) ≫ f :=
by cases p; cases q; simp


variables {D : Type u'} [𝒟 : category.{v'} D]
include 𝒟

lemma eq_obj {F G : C ⥤ D} (h : F = G) (X) : F.obj X = G.obj X :=
by subst h

lemma eq_hom {F G : C ⥤ D} (h : F = G) {X Y} (f : X ⟶ Y) :
  F.map f = eq_to_hom (category_theory.functor.eq_obj h X) ≫ G.map f ≫ eq_to_hom (category_theory.functor.eq_obj h Y).symm :=
by subst h; simp

@[simp] lemma category_theory.nat_trans.eq_to_hom_app {F G : C ⥤ D} (h : F = G) (X : C) :
  (eq_to_hom h : F ⟹ G).app X = eq_to_hom (category_theory.functor.eq_obj h X) :=
by subst h; refl

end functor
end category_theory
