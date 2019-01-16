import category_theory.model.category
import homotopy_theory.topological_spaces.weak_equivalences
import wfs_top
import weq_top

namespace model_top

open category_theory
open homotopy_theory.topological_spaces

lemma W_is_weq : is_weak_equivalences @is_weak_equivalence :=
{ weq_of_iso := @is_weak_equivalence_iso,
  weq_comp := @is_weak_equivalence_comp,
  weq_cancel_left := Top_weak_equivalences.weq_of_comp_weq_left,
  weq_cancel_right := Top_weak_equivalences.weq_of_comp_weq_right }

/- Unfinished business. -/
axiom A₁ : rlp serre_I = rlp serre_J ∩ @is_weak_equivalence

def quillen_serre : model_category.{0} Top.{0} :=
model_category.mk' W_is_weq serre_caf serre_acf A₁ AC_sub_W

end model_top
