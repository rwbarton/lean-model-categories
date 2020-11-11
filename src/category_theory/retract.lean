/- Retract of a map, as arises frequently in model categories. -/

import category_theory.category
import category_theory.functor
import category_theory.isomorphism
import category_theory.stuff

namespace category_theory

universes v v' u u'
variables {C : Type u} [𝒞 : category.{v} C]
include 𝒞

--- `retract f f'` is a diagram exhibiting f' as a retract of f.
structure retract {a b a' b' : C} (f : a ⟶ b) (f' : a' ⟶ b') : Type v :=
(ia : a' ⟶ a) (ra : a ⟶ a')
(ib : b' ⟶ b) (rb : b ⟶ b')
(ha : ia ≫ ra = 𝟙 a')
(hb : ib ≫ rb = 𝟙 b')
(hi : ia ≫ f = f' ≫ ib)
(hr : ra ≫ f' = f ≫ rb)

lemma retract_is_iso {a b a' b' : C} {f : a ⟶ b} {f' : a' ⟶ b'} (r : retract f f')
  (h : is_iso f) : is_iso f' :=
begin
  refine ⟨r.ib ≫ inv f ≫ r.ra, _, _⟩,
  { rw [←category.assoc, ←r.hi, category.assoc],
    simpa [is_iso.hom_inv_id_assoc] using r.ha },
  { rw [category.assoc, category.assoc, r.hr],
    simpa [is_iso.inv_hom_id_assoc] using r.hb }
end

variables {D : Type u'} [𝒟 : category.{v'} D]
include 𝒟

def functor.on_retract (F : C ⥤ D) {a b a' b' : C} {f : a ⟶ b} {f' : a' ⟶ b'} (r : retract f f') :
  retract (F.map f) (F.map f') :=
begin
  refine ⟨F.map r.ia, F.map r.ra, F.map r.ib, F.map r.rb, _, _, _, _⟩;
  { repeat {rw ←F.map_comp}, repeat {rw ←F.map_id},
    congr' 1,
    cases r,
    apply_assumption }
end

end category_theory

