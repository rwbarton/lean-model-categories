import homotopy_theory.topological_spaces.weak_equivalences
import top_small
import top_mono

open category_theory
open homotopy_theory.topological_spaces

namespace model_top

local notation `Top` := Top.{0}

structure gen_lifting_data :=
(a b c : Top)
(f : a ⟶ b)
(f₀ f₁ : b ⟶ c)
(h : f ≫ f₀ = f ≫ f₁)  -- Necessary?

def gen_lifting_condition (D : gen_lifting_data) {X Y : Top} (g : X ⟶ Y) :=
∀ (h : D.a ⟶ X) (k : D.b ⟶ Y), D.f ≫ k = h ≫ g →
∃ (l : D.b ⟶ X) (m : D.c ⟶ Y), D.f ≫ l = h ∧ D.f₀ ≫ m = k ∧ D.f₁ ≫ m = l ≫ g

/- The "gen_lifting_data" for weak equivalences are:

⬝ ∅ → * ⇉ I, which verifies surjectivity on π₀

⬝ * → Sⁿ ⇉ Sⁿ ∧ I₊, which verifies surjectivity on πₙ, n ≥ 1

⬝ * ⊔ * → I ⇉ (pushout), which verifies injectivity on π₀

⬝ Sⁿ ∨ Sⁿ → Sⁿ ∧ I₊ ⇉ (pushout), which verifies injectivity on πₙ, n ≥ 1

-/
axiom weq_iff : ∃ (ι : Type) (D : ι → gen_lifting_data), (∀ i, compact_space (D i).b) ∧
  (∀ {X Y : Top} (g : X ⟶ Y), is_weak_equivalence g ↔ ∀ i, gen_lifting_condition (D i) g)

end model_top
