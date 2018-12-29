import category_theory.limits.types
import category_theory.filtered
import category_theory.cone_stuff
import category_theory.stuff

universe u

section

variables {α : Type u} (r : α → α → Prop)

lemma quot.eq {a b : α} : quot.mk r a = quot.mk r b ↔ eqv_gen r a b :=
⟨quot.exact r, quot.eqv_gen_sound⟩

end

namespace category_theory
open category_theory.limits

variables {J : Type u} [small_category J] [is_filtered_or_empty J]
variables (F : J ⥤ Type u)

def filtered_colimit_r (x y : Σ j, F.obj j) : Prop :=
∃ k (f : x.1 ⟶ k) (g : y.1 ⟶ k), F.map f x.2 = F.map g y.2

lemma filtered_colimit_r_equiv : equivalence (filtered_colimit_r F) :=
⟨λ x, ⟨x.1, 𝟙 x.1, 𝟙 x.1, rfl⟩,
 λ x y ⟨k, f, g, h⟩, ⟨k, g, f, h.symm⟩,
 λ x y z ⟨k, f, g, h⟩ ⟨k', f', g', h'⟩,
   let ⟨l, ⟨fl⟩, ⟨gl⟩⟩ := is_filtered_or_empty.cocone_objs k k',
       ⟨m, n, hn⟩ := is_filtered_or_empty.cocone_maps (g ≫ fl) (f' ≫ gl) in
   ⟨m, f ≫ fl ≫ n, g' ≫ gl ≫ n, calc
      F.map (f ≫ fl ≫ n) x.2
          = F.map (fl ≫ n) (F.map f x.2)  : by simp
      ... = F.map (fl ≫ n) (F.map g y.2)  : by rw h
      ... = F.map ((g ≫ fl) ≫ n) y.2      : by simp
      ... = F.map ((f' ≫ gl) ≫ n) y.2     : by rw hn
      ... = F.map (gl ≫ n) (F.map f' y.2) : by simp
      ... = F.map (gl ≫ n) (F.map g' z.2) : by rw h'
      ... = F.map (g' ≫ gl ≫ n) z.2       : by simp⟩⟩

lemma filtered_colimit_r_le (x y : Σ j, F.obj j) :
  (∃ f : x.1 ⟶ y.1, y.2 = F.map f x.2) → filtered_colimit_r F x y :=
λ ⟨f, hf⟩, ⟨y.1, f, 𝟙 y.1, by simp [hf]⟩

lemma filtered_colimit_r_eq : filtered_colimit_r F = eqv_gen (λ x y, ∃ f : x.1 ⟶ y.1, y.2 = F.map f x.2) :=
begin
  apply le_antisymm,
  { rintros ⟨i, x⟩ ⟨j, y⟩ ⟨k, f, g, h⟩,
    exact eqv_gen.trans _ ⟨k, F.map f x⟩ _ (eqv_gen.rel _ _ ⟨f, rfl⟩)
      (eqv_gen.symm _ _ (eqv_gen.rel _ _ ⟨g, h⟩)) },
  { intros x y,
    convert relation.eqv_gen_mono (filtered_colimit_r_le F),
    apply propext,
    symmetry,
    exact relation.eqv_gen_iff_of_equivalence (filtered_colimit_r_equiv F) }
end

lemma equal_in_filtered_colimit_iff_aux {i j : J} {xi : F.obj i} {xj : F.obj j} :
  colimit.ι F i xi = colimit.ι F j xj ↔ ∃ k (f : i ⟶ k) (g : j ⟶ k), F.map f xi = F.map g xj :=
begin
  change quot.mk _ _ = quot.mk _ _ ↔ _,
  rw [quot.eq, ←filtered_colimit_r_eq],
  refl
end

variables {t : cocone F} (ht : is_colimit t)
include ht

local attribute [elab_simple] nat_trans.app
lemma equal_in_filtered_colimit_iff {i j : J} {xi : F.obj i} {xj : F.obj j} :
  t.ι.app i xi = t.ι.app j xj ↔ ∃ k (f : i ⟶ k) (g : j ⟶ k), F.map f xi = F.map g xj :=
let t' := colimit.cocone F,
    e : t' ≅ t := is_colimit.unique (colimit.is_colimit F) ht,
    e' : t'.X ≅ t.X := cocones.forget.on_iso e in
begin
  refine iff.trans _ (equal_in_filtered_colimit_iff_aux F),
  convert equiv.apply_eq_iff_eq e'.to_equiv _ _; rw ←e.hom.w; refl
end

lemma filtered_colimit_injective (h : ∀ i j (f : i ⟶ j), function.injective (F.map f))
  (i : J) : function.injective (t.ι.app i) :=
begin
  intros x y hxy,
  rcases (equal_in_filtered_colimit_iff F ht).mp hxy with ⟨k, f, g, H⟩,
  rcases is_filtered_or_empty.cocone_maps f g with ⟨Z, l, hl⟩,
  have : F.map (f ≫ l) x = F.map (g ≫ l) y,
  { rw [F.map_comp, F.map_comp],
    exact congr_arg (F.map l) H },
  rw hl at this,
  exact h _ _ (g ≫ l) this
end

end category_theory
