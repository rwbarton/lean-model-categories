import category_theory.category
import set_theory.cofinality

universe v

def regular_cardinal := {κ : cardinal.{v} // κ.is_regular}
instance : has_coe regular_cardinal.{v} cardinal.{v} :=
by dunfold regular_cardinal; apply_instance

namespace category_theory

variables (κ : regular_cardinal.{v})

def is_kappa_small (I : Type v) [small_category I] : Prop :=
cardinal.mk (Σ (X Y : I), X ⟶ Y) < κ

end category_theory
