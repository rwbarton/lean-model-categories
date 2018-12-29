import order.order_iso
import set_theory.ordinal

universes u v w

section

variables {α : Type u} [preorder α] {β : Type v} [preorder β] {γ : Type w} [preorder γ]

structure is_preorder_hom (f : α → β) : Prop :=
(map_le : ∀ {x y}, x ≤ y → f x ≤ f y)

lemma is_preorder_hom.id : is_preorder_hom (@id α) :=
⟨λ x y h, h⟩

lemma is_preorder_hom.comp {f : α → β} (hf : is_preorder_hom f)
  {g : β → γ} (hg : is_preorder_hom g) : is_preorder_hom (g ∘ f) :=
⟨λ x y h, hg.map_le (hf.map_le h)⟩

variables (α β)

def preorder_iso : Type (max u v) :=
order_iso ((≤) : α → α → Prop) ((≤) : β → β → Prop)

instance preorder_iso_coe :
  has_coe (preorder_iso α β) (order_iso ((≤) : α → α → Prop) ((≤) : β → β → Prop)) :=
⟨λ f, f⟩

def preorder_iso.refl : preorder_iso α α :=
order_iso.refl _

variables {α β}

def preorder_iso.symm (f : preorder_iso α β) : preorder_iso β α := f.symm

def preorder_iso.trans (f : preorder_iso α β) (g : preorder_iso β γ) : preorder_iso α γ :=
f.trans g

lemma preorder_iso.is_hom (f : preorder_iso α β) : is_preorder_hom f :=
⟨λ x y h, f.ord'.mp h⟩

end

section of_strict

/- We want to relate homomorphisms and isomorphisms respecting (<) to
  ones respecting (≤), that is, preorder homomorphisms and
  isomorphisms as defined above. However, for a general preorder, the
  relation (<) does not contain enough information to reconstruct (≤).
  For example, any equivalence relation (~) induces a preorder in
  which x ≤ y ↔ x ~ y; the associated relation (<) is then empty
  regardless of the choice of (~). So even an `order_iso (<) (<)` need
  not be an `order_iso (≤) (≤)`.

  Therefore, we specialize here to partial_orders, for which (<) does
  determine (≤) via x ≤ y ↔ (x < y ∨ x = y). -/

variables {α : Type u} [partial_order α] {β : Type v} [partial_order β]

lemma is_preorder_hom.of_strict_hom (f : α → β) (hf : ∀ {x y}, x < y → f x < f y) :
  is_preorder_hom f :=
⟨λ x y h, (lt_or_eq_of_le h).rec (le_of_lt ∘ hf) (by rintro rfl; refl)⟩

variables (f : order_iso ((<) : α → α → Prop) ((<) : β → β → Prop))

lemma is_preorder_hom.of_strict_iso : is_preorder_hom f :=
is_preorder_hom.of_strict_hom f (λ x y h, f.ord'.mp h)

def preorder_iso.of_strict_iso : preorder_iso α β :=
{ ord := λ x y,
    ⟨λ h, (is_preorder_hom.of_strict_iso f).map_le h,
     λ h, begin
       convert ←(is_preorder_hom.of_strict_iso f.symm).map_le h;
       apply equiv.inverse_apply_apply
     end⟩,
  .. f }

@[simp] lemma preorder_iso.of_strict_iso_coe_fn :
  (preorder_iso.of_strict_iso f : α → β) = (f : α → β) :=
rfl  

-- TODO: Categorize the below

variables (g : order_embedding ((<) : α → α → Prop) ((<) : β → β → Prop))

def embed_le_of_embed_lt :
  order_embedding ((≤) : α → α → Prop) ((≤) : β → β → Prop) :=
{ ord := λ x y,
    ⟨λ h, (is_preorder_hom.of_strict_hom g (λ x y h, g.ord'.mp h)).map_le h,
     λ h, (lt_or_eq_of_le h).rec (λ h, le_of_lt (g.ord'.mpr h)) (λ h, le_of_eq (g.inj h))⟩,
  .. g }

end of_strict

section misc

variables {α : Type u} [partial_order α] {β : Type v} [partial_order β]
  (f : initial_seg ((<) : α → α → Prop) ((<) : β → β → Prop))

noncomputable def restrict_Io (j : α) : preorder_iso {i // i < j} {i // i < f j} :=
order_iso.of_surjective
  { to_fun := λ p, ⟨f p.1, f.to_order_embedding.ord'.mp p.2⟩,
    inj := λ p p' h, subtype.eq (f.inj (subtype.ext.mp h) ),
    ord := λ p p', (embed_le_of_embed_lt f.to_order_embedding).ord' }
  (λ ⟨i', h⟩,
     let ⟨i, hi⟩ := f.init' h in
     ⟨⟨i, f.to_order_embedding.ord'.mpr (by convert h)⟩, subtype.eq hi⟩)

end misc
