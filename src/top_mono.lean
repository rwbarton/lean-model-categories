import category_theory.examples.topological_spaces
import homotopy_theory.topological_spaces.category

universe u

open category_theory
namespace homotopy_theory.topological_spaces

lemma Top.mono_iff_injective {X Y : Top.{u}} {f : X ⟶ Y} : mono f ↔ function.injective f :=
begin
  split; intro H,
  { intros x x' h,
    let g : Top.point ⟶ X := Top.const x,
    let g' : Top.point ⟶ X := Top.const x',
    change g punit.star.{u+1} = g' punit.star.{u+1},
    apply Top.hom_congr,
    resetI,
    rw ←cancel_mono f,
    ext,
    exact h },
  { constructor,
    intros α g h hh,
    ext a,
    apply H,
    exact Top.hom_congr hh a }
end


end homotopy_theory.topological_spaces

