import category_theory.natural_isomorphism
import category_theory.limits.limits
import category_theory.types
import category_theory.limits.preserves
import set_theory.cardinal

section
universes u v
lemma nonempty.map {α : Type u} {β : Type v} (f : α → β) : nonempty α → nonempty β
| ⟨a⟩ := ⟨f a⟩
end

section
universes u
lemma cardinal.mk_range_le {α β : Type u} (f : α → β) :
  cardinal.mk (set.range f) ≤ cardinal.mk α :=
begin
  refine ⟨⟨λ b, classical.some b.property, λ b b' H, subtype.eq _⟩⟩,
  rw [←classical.some_spec b.property, ←classical.some_spec b'.property],
  exact congr_arg f H
end
end

section

universe u

variables {X Y : Type u}

def equiv.to_iso (e : X ≃ Y) : X ≅ Y :=
{ hom := e.to_fun,
  inv := e.inv_fun,
  hom_inv_id' := funext e.left_inv,
  inv_hom_id' := funext e.right_inv }

@[simp] lemma equiv.to_iso_hom {e : X ≃ Y} : e.to_iso.hom = e :=
rfl

@[simp] lemma equiv.to_iso_inv {e : X ≃ Y} : e.to_iso.inv = e.symm :=
rfl

def category_theory.iso.to_equiv (i : X ≅ Y) : X ≃ Y :=
{ to_fun := i.hom,
  inv_fun := i.inv,
  left_inv := λ x, congr_fun i.hom_inv_id x,
  right_inv := λ y, congr_fun i.inv_hom_id y }

@[simp] lemma category_theory.iso.to_equiv_fun (i : X ≅ Y) : (i.to_equiv : X → Y) = i.hom :=
rfl

-- one more

end

namespace category_theory

section

universes u v

variables {C : Type u} [𝒞 : category.{u v} C] {X Y : C}
include 𝒞

def iso.of_is_iso (f : X ⟶ Y) [is_iso f] : X ≅ Y :=
{ hom := f, inv := inv f }

@[simp] lemma iso.of_is_iso.inv (f : X ⟶ Y) [is_iso f] :
  (iso.of_is_iso f).inv = inv f := rfl

def iso.op (i : X ≅ Y) : @iso (Cᵒᵖ) _ X Y :=
{ hom := i.inv,
  inv := i.hom,
  hom_inv_id' := i.hom_inv_id,
  inv_hom_id' := i.inv_hom_id }

end

section

universes u v

variables {C : Type u} [𝒞 : category.{u v} C] {X Y Z : C}
include 𝒞

-- Making these simp lemmas breaks extend1.lean??

lemma is_iso.hom_inv_id_assoc (f : X ⟶ Y) [is_iso f] (g : X ⟶ Z) : f ≫ inv f ≫ g = g :=
by rw [←category.assoc, is_iso.hom_inv_id, category.id_comp]

lemma is_iso.inv_hom_id_assoc (f : X ⟶ Y) [is_iso f] (g : Y ⟶ Z) : inv f ≫ f ≫ g = g :=
by rw [←category.assoc, is_iso.inv_hom_id, category.id_comp]

end

section

universe v

variables {X Y : Type v} (α : X ≅ Y)

lemma mono_iff_injective {f : X ⟶ Y} : mono f ↔ function.injective f :=
begin
  split; intro H,
  { intros x x' h,
    change (λ _, x) punit.star.{v+1} = (λ _, x') punit.star.{v+1},
    apply congr_fun,
    resetI,
    rw ←cancel_mono f,
    ext,
    exact h },
  { constructor,
    intros α g h hh,
    ext a,
    apply H,
    exact congr_fun hh a }
end

@[simp] lemma iso.hom_eq_iff_eq (x x' : X) : α.hom x = α.hom x' ↔ x = x' :=
(mono_iff_injective.mp (category_theory.mono_of_iso α.hom)).eq_iff

@[simp] lemma iso.inv_eq_iff_eq (y y' : Y) : α.inv y = α.inv y' ↔ y = y' :=
(mono_iff_injective.mp (category_theory.mono_of_iso α.inv)).eq_iff

@[simp] lemma iso.hom_inv_apply (y : Y) : α.hom (α.inv y) = y :=
show (α.inv ≫ α.hom) y = y, by rw α.inv_hom_id; refl

@[simp] lemma iso.inv_hom_apply (x : X) : α.inv (α.hom x) = x :=
show (α.hom ≫ α.inv) x = x, by rw α.hom_inv_id; refl

lemma iso.inv_apply_eq {x : X} {y : Y} : α.inv y = x ↔ y = α.hom x :=
by split; intro H; subst H; simp

lemma iso.eq_inv_apply {x : X} {y : Y} : x = α.inv y ↔ α.hom x = y :=
(eq_comm.trans α.inv_apply_eq).trans eq_comm

end

namespace nat_iso

universes u₁ u₂ v₁ v₂

variables {C : Type u₁} [𝒞 : category.{u₁ v₁} C] {D : Type u₂} [𝒟 : category.{u₂ v₂} D]
include 𝒞 𝒟

variables {F G : C ⥤ D}

def is_iso_of_components (α : F ⟶ G) [Π X, is_iso (α.app X)] : is_iso α :=
let i : F ≅ G := nat_iso.of_components (λ X, iso.of_is_iso (α.app X))
  (λ _ _ f, α.naturality f) in
{ inv := i.inv }

end nat_iso

section whisker

universes u₁ v₁ u₂ v₂ u₃ v₃ u₄ v₄

variables {C : Type u₁} [𝒞 : category.{u₁ v₁} C]
          {D : Type u₂} [𝒟 : category.{u₂ v₂} D]
          {E : Type u₃} [ℰ : category.{u₃ v₃} E]
include 𝒞 𝒟 ℰ

def whisker_left_iso (F : C ⥤ D) {G H : D ⥤ E} (α : G ≅ H) : (F ⋙ G) ≅ (F ⋙ H) :=
((whiskering_left C D E).obj F).on_iso α

def whisker_right_iso {G H : C ⥤ D} (α : G ≅ H) (F : D ⥤ E) : (G ⋙ F) ≅ (H ⋙ F) :=
((whiskering_right C D E).obj F).on_iso α


end whisker

namespace limits

universes u u' v

variables {J : Type v} [small_category J]
variables {C : Type u} [𝒞 : category.{u v} C]
include 𝒞

section
variables {F : J ⥤ C} {t : cocone F}

def is_colimit.of_hom_iso (i : Π (W : C), (t.X ⟶ W) ≅ (F ⟹ (functor.const J).obj W))
  (h : ∀ (W : C) f, (i W).hom f = t.ι ⊟ ((functor.const J).map f)) : is_colimit t :=
⟨λ s, (i s.X).inv s.ι,
 λ s j, by convert ←(nat_trans.congr_app (h s.X _) j).symm; apply (i s.X).hom_inv_apply,
 λ s m hm, by rw [(i s.X).eq_inv_apply, h]; ext j; apply hm⟩

end

/-
section
variables {F G : J ⥤ C} (α : G ⟹ F)

def precompose_functor : cocone F ⥤ cocone G :=
{ obj := cocone.precompose α,
  map := λ A B f,
  { hom := f.hom,
    w' := λ j, begin
      dsimp [cocone.precompose],
      rw [category.assoc, f.w']
    end } }

end
-/

variables {F F' : J ⥤ C} (α : F ≅ F')

def is_colimit.of_nat_iso {t : cocone F'} (h : is_colimit (t.precompose α.hom)) :
  is_colimit t :=
is_colimit.of_hom_iso
  (λ W, h.hom_iso W ≪≫ (yoneda.obj ((functor.const J).obj W)).on_iso α.op)
  (λ W f, begin
     ext X,
     dsimp [cocone.extend, cocone.precompose, iso.op],
     rw ←category.assoc, congr, apply (nat_iso.app α X).inv_hom_id_assoc,
   end)

variables {D : Type u'} [𝒟 : category.{u' v} D]
include 𝒟

variables (t : cocone F)

variables {G G' : C ⥤ D} (β : G ⟹ G')

-- TODO fix namespace. Should it be `nat_trans`?
def functor.map_cocone_hom :
  G.map_cocone t ⟶ (G'.map_cocone t).precompose (whisker_left F β) :=
{ hom := β.app t.X, w' := λ j, by apply β.naturality }

@[simp] lemma functor.map_cocone_hom_hom : (functor.map_cocone_hom t β).hom = β.app t.X :=
rfl

variables (γ : G ≅ G')
def functor.map_cocone_iso :
  G.map_cocone t ≅ (G'.map_cocone t).precompose (whisker_left F γ.hom) :=
{ hom := functor.map_cocone_hom t γ.hom,
  inv :=
  { hom := γ.inv.app _,
    w' := λ j, begin
      change _ ≫ (nat_iso.app γ t.X).inv = _,
      rw iso.comp_inv_eq,
      symmetry,
      apply γ.hom.naturality
    end } }

def is_colimit.of_map_nat_iso {t : cocone F} (h : is_colimit (G.map_cocone t)) :
  is_colimit (G'.map_cocone t) :=
have _ := is_colimit.of_iso_colimit h (functor.map_cocone_iso t γ),
is_colimit.of_nat_iso (whisker_left_iso F γ) this

def preserves_colimit_of_iso [preserves_colimit F G] : preserves_colimit F G' :=
⟨λ c hc, is_colimit.of_map_nat_iso γ (preserves_colimit.preserves G hc)⟩

def preserves_colimits_of_shape_of_iso [preserves_colimits_of_shape J G] :
  preserves_colimits_of_shape J G' :=
λ K, preserves_colimit_of_iso γ

def preserves_colimits_of_iso [preserves_colimits G] : preserves_colimits G' :=
λ J 𝒥, @preserves_colimits_of_shape_of_iso J 𝒥 _ _ _ _ _ _ γ (by resetI; apply_instance)

end limits

section ff

universes u₁ v₁ u₂ v₂

variables {C : Type u₁} [𝒞 : category.{u₁ v₁} C] {D : Type u₂} [𝒟 : category.{u₂ v₂} D]
include 𝒞 𝒟

/-
instance ff (F : C ⥤ D) [full F] [faithful F] : fully_faithful F :=
fully_faithful.mk F
-/

def hom_equiv (F : C ⥤ D) [full F] [faithful F] {X Y : C} : (X ⟶ Y) ≃ (F.obj X ⟶ F.obj Y) :=
{ to_fun := λ f, F.map f,
  inv_fun := λ g, F.preimage g,
  left_inv := λ f, F.injectivity (by simp),
  right_inv := λ g, by simp }

end ff

end category_theory

-- seriously miscellaneous
namespace equiv

universes u v
variables {α : Type u} {β : Type v}

def nonempty_iff_nonempty (e : equiv α β) : nonempty α ↔ nonempty β :=
⟨λ ⟨a⟩, ⟨e a⟩, λ ⟨b⟩, ⟨e.symm b⟩⟩

end equiv

