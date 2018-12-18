import model.model

namespace model

open categories
open categories.universal

-- XXX fix precedence (higher than ⟶)
notation X ` ∐ ` Y := (binary_coproduct X Y).coproduct
notation X ` × ` Y := (binary_product X Y).product

section
universe u
variable {M : Type (u+1)}
variable [category M]
variables [has_BinaryCoproducts M] [has_BinaryProducts M]
variable {X : M}
def fold : (X ∐ X) ⟶ X := (binary_coproduct X X).map (𝟙 X) (𝟙 X)
def j₀ : X ⟶ (X ∐ X) := (binary_coproduct X X).left_inclusion
def j₁ : X ⟶ (X ∐ X) := (binary_coproduct X X).right_inclusion
@[simp]
lemma fold_of_j₀ : j₀ ≫ fold = 𝟙 X := (binary_coproduct X X).left_factorisation (𝟙 X) (𝟙 X)
@[simp]
lemma fold_of_j₁ : j₁ ≫ fold = 𝟙 X := (binary_coproduct X X).right_factorisation (𝟙 X) (𝟙 X)

def diag : X ⟶ X × X := (binary_product X X).map (𝟙 X) (𝟙 X)
def q₀ : X × X ⟶ X :=  (binary_product X X).left_projection
def q₁ : X × X ⟶ X :=  (binary_product X X).right_projection
@[simp]
lemma q₀_of_diag : diag ≫ q₀ = 𝟙 X := (binary_product X X).left_factorisation (𝟙 X) (𝟙 X)
@[simp]
lemma q₁_of_diag : diag ≫ q₁ = 𝟙 X := (binary_product X X).right_factorisation (𝟙 X) (𝟙 X)
end

/- Hirschhorn, §7.3.1 -/

universe u
variable {M : Type (u+2)}
-- XXX sort of weird we have to list all of these explicitly?
variables [category M] [Cocomplete M] [Complete M] [ModelCategory M]
-- XXX these should be redundant of course
variables [has_BinaryCoproducts M] [has_BinaryProducts M]

variables (X Y : M)
variables (f g : X ⟶ Y)

-- 7.3.2
structure cylinder :=
  (Cyl : M) (i : (X ∐ X) ⟶ Cyl) (p : Cyl ⟶ X)
  (H : fold = i ≫ p)
  (cof_i : cof i) (weq_p : weq p)

variable {X}
def cylinder.i₀ (cyl : cylinder X) : X ⟶ cyl.Cyl := j₀ ≫ cyl.i
def cylinder.i₁ (cyl : cylinder X) : X ⟶ cyl.Cyl := j₁ ≫ cyl.i

variables {X Y}
structure left_homotopy :=
  (cyl : cylinder X) (h : cyl.Cyl ⟶ Y)
  (Hf : cyl.i₀ ≫ h = f) (Hg : cyl.i₁ ≫ h = g)

def left_homotopic := nonempty (left_homotopy f g)


variable (X)
structure path :=
  (Path : M) (s : X ⟶ Path) (p : Path ⟶ X × X)
  (H : diag = s ≫ p)
  (weq_s : weq s) (fib_p : fib p)

variable {X}
def path.p₀ (pat : path X) : pat.Path ⟶ X := pat.p ≫ q₀
def path.p₁ (pat : path X) : pat.Path ⟶ X := pat.p ≫ q1

variables {X Y}
structure right_homotopy :=
  (pat : path Y) (h : X ⟶ pat.Path)
  (Hf : h ≫ pat.p₀ = f) (Hg : h ≫ pat.p₁ = g)

def right_homotopic := nonempty (left_homotopy f g)

def homotopic := left_homotopic f g ∧ right_homotopic f g

-- 7.3.3
variable (X)
-- XXX should this be "constructive"?
-- (But wait: we defined factorization non-constructively anyways.)
lemma exists_fibrant_cylinder : ∃ cyl : cylinder X, afib cyl.p :=
  match caf.factor (fold : (X ∐ X) ⟶ X) with
  | ⟨C, fl, fr, c_fl, af_fr, H⟩ := ⟨⟨C, fl, fr, H, c_fl, af_fr.1⟩, af_fr⟩
  end
lemma exists_cofibrant_path : ∃ pat : path X, acof pat.s :=
  match acf.factor (diag : X ⟶ X × X) with
  | ⟨P, fl, fr, ac_fl, f_fr, H⟩ := ⟨⟨P, fl, fr, H, ac_fl.1, f_fr⟩, ac_fl⟩
  end

-- skip 7.3.4
/-
variables {X Y} (f g)
lemma left_homotopy_from_fibrant_cylinder :
  left_homotopic f g → fibrant Y →
  ∃ h : left_homotopy f g, afib h.cyl.p := sorry
-/

-- 7.3.6
lemma cofibrant_j₀_is_cofibration : cofibrant X → cof (j₀ : X ⟶ (X ∐ X)) := λ cX,
  pushout_is_left _ _ caf (initial_cospan X X) (flipped_coproduct_square X X) cX
lemma cofibrant_j₁_is_cofibration : cofibrant X → cof (j₁ : X ⟶ (X ∐ X)) := λ cX,
  pushout_is_left _ _ caf (initial_cospan X X) (coproduct_square X X) cX

lemma fibrant_q₀_is_fibration : fibrant X → fib (q₀ : X × X ⟶ X) := sorry
lemma fibrant_q₁_is_fibration : fibrant X → fib (q₁ : X × X ⟶ X) := sorry

-- 7.3.7
-- XXX Don't know why this one was so difficult
lemma cylinder_i₀_is_weq (cyl : cylinder X) : weq cyl.i₀ := begin
  have : cyl.i₀ ≫ cyl.p = 𝟙 X := begin
    rw cylinder.i₀,
    simp,
    rw ←cyl.H,
    apply fold_of_j₀
  end,
  apply (ModelCategory.weq_ok M).f_from_gh cyl.i₀ cyl.p cyl.weq_p _,
  rw this,
  exact (ModelCategory.weq_ok M).id_is_weq X
end
lemma cylinder_i₁_is_weq (cyl : cylinder X) : weq cyl.i₁ := sorry
lemma path_p₀_is_weq (pat : path X) : weq pat.p₀ := sorry
lemma path_p₁_is_weq (pat : path X) : weq pat.p₁ := sorry

end model
