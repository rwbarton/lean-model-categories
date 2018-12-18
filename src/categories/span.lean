import categories.category
import categories.square
import categories.universal.complete

universe u

namespace categories

open categories.universal

variable {C : Type (u+1)}
variable [category C]

section not
variable [has_InitialObject C]

def morphism_from_initial_object_to (X : C) := (has_InitialObject.initial_object C).morphism_from_initial_object_to X

-- notation `∅` := initial_object
instance : has_emptyc C := ⟨initial_object C⟩
notation `∅!` := morphism_from_initial_object_to
end not

variable (C)
structure cospan : Type (u+1) :=
  {A B₁ B₂ : C}
  (f₁ : A ⟶ B₁) (f₂ : A ⟶ B₂)

variable {C}
-- def cospan_of_square (s : square C) : cospan C := ⟨s.f, s.u⟩

structure square_on_cospan (c : cospan C) :=
  {B₃ : C}
  (i₁ : c.B₁ ⟶ B₃) (i₂ : c.B₂ ⟶ B₃)
  (H : c.f₁ ≫ i₁ = c.f₂ ≫ i₂)
-- XXX: Some way to relate square_on_cospan to square?

structure have_unique {α : Sort u} (p : α → Prop) :=
  (x : α)
  (px : p x)
  (uniq : ∀ y, p y → y = x)
notation `∃∃` binders `, ` r:(scoped P, have_unique P) := r

def equal_of_have_unique {α : Sort u} {p : α → Prop} (hu : have_unique p)
                         {y z : α} : p y → p z → y = z := λ py pz,
  let x : α := hu.x in
  have yx : y = x, from hu.uniq y py,
  have zx : z = x, from hu.uniq z pz,
  yx.trans zx.symm

def universal_property (c : cospan C) (s s' : square_on_cospan c) : Type u :=
  ∃∃ h : s.B₃ ⟶ s'.B₃, s.i₁ ≫ h = s'.i₁ ∧ s.i₂ ≫ h = s'.i₂

class IsPushout (c : cospan C) (s : square_on_cospan c) :=
  (univ : ∀ s' : square_on_cospan c, universal_property c s s')

def map_from_pushout (c : cospan C) (s s' : square_on_cospan c) [IsPushout c s] : s.B₃ ⟶ s'.B₃ :=
  (IsPushout.univ s s').x

-- Rather than "the pushout of a cospan", we also often talk about
-- "a pushout f' of a morphism f" along another morphism.
-- But this is awkward to translate faithfully without introducing
-- a bunch of annoying propositional equalities.
  
variable C
class HasPushouts :=
  (pushout : Π (c : cospan C), Σ (s : square_on_cospan c), IsPushout c s)

section coproduct_square_is_pushout
variable {C}
variables (B₁ B₂ : C)
variables [has_InitialObject C]
variables [has_BinaryCoproducts C]

def initial_cospan : cospan C := ⟨∅! B₁, ∅! B₂⟩ 

def coproduct_square : square_on_cospan (initial_cospan B₁ B₂) :=
  let b := binary_coproduct B₁ B₂ in
  ⟨b.left_inclusion, b.right_inclusion,
  (has_InitialObject.initial_object C).uniqueness_of_morphisms_from_initial_object _ _ _⟩

def coproduct_square_is_universal (s' : square_on_cospan (initial_cospan B₁ B₂)) : universal_property (initial_cospan B₁ B₂) (coproduct_square B₁ B₂) s' := begin
  fapply have_unique.mk,
  exact (binary_coproduct B₁ B₂).map s'.i₁ s'.i₂,
  { obviously }, { obviously }
end

instance CoproductSquareIsPushout : IsPushout (initial_cospan B₁ B₂) (coproduct_square B₁ B₂) :=
  ⟨coproduct_square_is_universal B₁ B₂⟩

def flipped_coproduct_square : square_on_cospan (initial_cospan B₁ B₂) :=
  let b := binary_coproduct B₂ B₁ in
  ⟨b.right_inclusion, b.left_inclusion,
  (has_InitialObject.initial_object C).uniqueness_of_morphisms_from_initial_object _ _ _⟩

def flipped_coproduct_square_is_universal (s' : square_on_cospan (initial_cospan B₁ B₂)) : universal_property (initial_cospan B₁ B₂) (flipped_coproduct_square B₁ B₂) s' := begin
  fapply have_unique.mk,
  exact (binary_coproduct B₂ B₁).map s'.i₂ s'.i₁,
  { obviously }, { obviously }
end

instance FlippedCoproductSquareIsPushout : IsPushout (initial_cospan B₁ B₂) (flipped_coproduct_square B₁ B₂) :=
  ⟨flipped_coproduct_square_is_universal B₁ B₂⟩

end coproduct_square_is_pushout

end categories


namespace categories.universal

open categories

variable (C : Type (u+2))
variable [category C]

open categories 
-- XXX instance from Cocomplete(!)
-- instance [Cocomplete C] : HasPushouts C := sorry

end categories.universal
