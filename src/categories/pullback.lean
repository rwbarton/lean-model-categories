import data.equiv
import tidy.tidy

universe u
variables {α β γ : Type u}

@[class] structure Is_equiv (f : α → β) := (e : α ≃ β) (H : f = e.to_fun)

protected lemma Is_equiv.unique (f : α → β) (E1 E2 : Is_equiv f) : E1 = E2 :=
match E1, E2 with
| ⟨e1, H1⟩, ⟨e2, H2⟩ := by congr; exact equiv.eq_of_to_fun_eq (H1.symm.trans H2)
end

instance (f : α → β) : subsingleton (Is_equiv f) := ⟨Is_equiv.unique f⟩

def inv (f : α → β) [E : Is_equiv f] := E.e.inv_fun
notation f`⁻¹` := inv f
protected def Is_equiv.Hinv {f : α → β} (E : Is_equiv f) : f⁻¹ = E.e.inv_fun := rfl

lemma cancel_inv_left (f : α → β) [E : Is_equiv f] : f⁻¹ ∘ f = id := begin
  have t := funext E.e.left_inv, rwa [←E.H, ←E.Hinv] at t
end

lemma cancel_inv_right (f : α → β) [E : Is_equiv f] : f ∘ f⁻¹ = id := begin
  have t := funext E.e.right_inv, rwa [←E.H, ←E.Hinv] at t
end

open function
protected lemma Is_equiv.left_inv {f : α → β} (E : Is_equiv f) : left_inverse E.e.inv_fun f := 
  @eq.subst (α → β) (λ g, left_inverse E.e.inv_fun g) E.e.to_fun f E.H.symm E.e.left_inv
protected lemma Is_equiv.right_inv {f : α → β} (E : Is_equiv f) : right_inverse E.e.inv_fun f := 
  @eq.subst (α → β) (λ g, right_inverse E.e.inv_fun g) E.e.to_fun f E.H.symm E.e.right_inv

def Is_equiv.refl : Is_equiv (id : α → α) := ⟨equiv.refl α, rfl⟩
def Is_equiv.symm {f : α → β} (E : Is_equiv f) : Is_equiv f⁻¹ := ⟨equiv.symm E.e, rfl⟩
def Is_equiv.trans {f : α → β} {g : β → γ} : Is_equiv f → Is_equiv g → Is_equiv (g ∘ f) :=
  λ E1 E2, ⟨equiv.trans E1.e E2.e, begin have := E1.H, have := E2.H, obviously end⟩
def Is_equiv.trans1 (f : α → β) (g : β → γ) [E1 : Is_equiv f] [E3 : Is_equiv (g ∘ f)] : Is_equiv g :=
  have E2 : Is_equiv ((g ∘ f) ∘ f⁻¹) := Is_equiv.trans (Is_equiv.symm E1) E3,
  @eq.rec_on (β → β) (f ∘ f⁻¹) (λ h, Is_equiv (g ∘ h)) id (cancel_inv_right f) E2
-- XXX etc.

--- "Canonical" pullback of a span X₁ → Y ← X₂.
structure pullback {X₁ X₂ Y : Type u} (t₁ : X₁ → Y) (t₂ : X₂ → Y) : Type u :=
  (x₁ : X₁) (x₂ : X₂) (H : t₁ x₁ = t₂ x₂)

namespace pullback

section fixme

parameters {X₁ X₂ Y : Type u} {t₁ : X₁ → Y} {t₂ : X₂ → Y}

-- Projections from the canonical pullback.
-- (These are simply synonyms for x₁ and x₂.)
@[simp] def π₁ : pullback t₁ t₂ → X₁ := x₁
@[simp] def π₂ : pullback t₁ t₂ → X₂ := x₂

-- lemma eta {p : pullback t₁ t₂} : p = mk (p.x₁) (p.x₂) (p.H) := match p with | ⟨_, _, _⟩ := rfl end

-- Commutativity of the square formed by the canonical pullback.
protected lemma commutes : t₁ ∘ π₁ = t₂ ∘ π₂ := funext (λ ⟨_, _, H⟩, H)

--- Map to the canonical pullback induced by a commutative square.
def map_to_pullback {X₁ X₂ Y : Type u} {t₁ : X₁ → Y} {t₂ : X₂ → Y}
                    {A : Type u} (f₁ : A → X₁) (f₂ : A → X₂) (H : t₁ ∘ f₁ = t₂ ∘ f₂)
  : A → pullback t₁ t₂ := λ a, ⟨f₁ a, f₂ a, congr_fun H a⟩

end fixme

section gluing
/-

Gluing lemma, version for canonical pullbacks.

Given a diagram

𝟚 → 𝟙 → Z'
↓   ↓   ↓ p
X → Y → Z
  f   g

forming canonical pullbacks at 𝟙 and then 𝟚 yields an isomorphic
result to forming a single pullback at 𝟚, along f ∘ g.

-/
parameters {X Y Z Z' : Type u}
parameters (f : X → Y) (g : Y → Z) (pZ : Z' → Z)

open pullback

-- Iterated pullback
def Y' := pullback g pZ
def pY : Y' → Y := π₁
def g' : Y' → Z' := π₂
protected lemma Hg : g ∘ pY = pZ ∘ g' := pullback.commutes

def X' := pullback f (π₁ : Y' → Y)
def pX : X' → X := π₁
def f' : X' → Y' := π₂
protected lemma Hf : f ∘ pX = pY ∘ f' := pullback.commutes

-- Direct pullback
def X'' := pullback (g ∘ f) pZ
def qX : X'' → X := π₁
def gf' : X'' → Z' := π₂
@[applicable] protected lemma Hgf : (g ∘ f) ∘ qX = pZ ∘ gf' := pullback.commutes

def inv_funext {α β : Type u} {f g : α → β} (H : f = g) : ∀ a, f a = g a := congr_fun H

def iterated_to_direct : X' → X'' := map_to_pullback pX (g' ∘ f') $ begin
  have := congr_fun pullback.Hf,
  have := congr_fun pullback.Hg,
  obviously
end
/-
  calc (g ∘ f) ∘ pX = g ∘ (f ∘ pX)    : rfl
       ...          = g ∘ (pY ∘ f')   : by rw pullback.Hf
       ...          = (g ∘ pY) ∘ f'   : rfl
       ...          = (pZ ∘ g') ∘ f'  : by rw pullback.Hg
-/

def X''_to_Y' : X'' → Y' := map_to_pullback (f ∘ qX) gf' ♯
def direct_to_iterated : X'' → X' := map_to_pullback qX X''_to_Y' ♯

local attribute [simp] iterated_to_direct direct_to_iterated X''_to_Y' map_to_pullback pX qX

protected lemma idi_eq : direct_to_iterated ∘ iterated_to_direct = id := begin
  apply funext, intro a, induction a, simp,
  congr, induction a_x₂, congr, assumption
end

protected lemma did_eq : iterated_to_direct ∘ direct_to_iterated = id := begin
  apply funext, intro a, induction a, simp,
  congr
end

end gluing

section cartesian
--- (Non-canonical) pullbacks, i.e., cartesian squares.
structure a_pullback {X₁ X₂ Y : Type u} (t₁ : X₁ → Y) (t₂ : X₂ → Y) :=
  (T : Type u) (equiv : T ≃ pullback t₁ t₂)

section fixme
variables {X₁ X₂ Y : Type u}
variables {t₁ : X₁ → Y} {t₂ : X₂ → Y}
variable (X : a_pullback t₁ t₂)

def a_pullback.π₁ : X.T → X₁ := π₁ ∘ X.equiv
def a_pullback.π₂ : X.T → X₂ := π₂ ∘ X.equiv

end fixme

#check a_pullback.π₂

section gluing
parameters {X Y Z Z' : Type u} (f : X → Y) (g : Y → Z) (pZ : Z' → Z)

parameters (Y' : a_pullback g pZ) (X' : a_pullback f Y'.π₁)

def glue : a_pullback (g ∘ f) pZ := ⟨X'.T, sorry⟩
lemma glue_object : glue.T = X'.T := rfl
-- more lemmas?
#print equivalence

end gluing

end cartesian

end pullback
