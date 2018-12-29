import category_theory.eq_to_iso
import category_theory.equivalence
import order.preorder_hom
import set_theory.ordinal

universes u v w

namespace category_theory

variables {α : Type u} [preorder α] {β : Type v} [preorder β] {γ : Type w} [preorder γ]

def preorder_functor (f : α → β) (hf : is_preorder_hom f) : α ⥤ β :=
{ obj := f, map := λ a a' h, ⟨⟨hf.map_le h.down.down⟩⟩ }

lemma preorder_functor.id : preorder_functor id is_preorder_hom.id = functor.id α :=
functor.ext (λ x, rfl) (λ x y h, rfl)

lemma preorder_functor.comp (f : α → β) (hf : is_preorder_hom f)
  (g : β → γ) (hg : is_preorder_hom g) :
  preorder_functor (g ∘ f) (hf.comp hg) = preorder_functor f hf ⋙ preorder_functor g hg :=
functor.ext (λ x, rfl) (λ x y h, rfl)

def preorder_equivalence (g : preorder_iso α β) : α ≌ β :=
by refine
  { functor := preorder_functor g g.is_hom,
    inverse := preorder_functor g.symm g.symm.is_hom,
    fun_inv_id' := _,
    inv_fun_id' := _ };
  { convert ←iso.refl _,
    rw ←preorder_functor.id,
    rw ←preorder_functor.comp,
    congr,
    ext x,
    apply equiv.inverse_apply_apply <|> apply equiv.apply_inverse_apply }

end category_theory

section

variables {α : Type v} [partial_order α] {β : Type v} [partial_order β]
  (f : initial_seg ((<) : α → α → Prop) ((<) : β → β → Prop))

def initial_seg.to_functor : α ⥤ β :=
category_theory.preorder_functor f $
  is_preorder_hom.of_strict_hom f (λ x y h, f.to_order_embedding.ord'.mp h)

@[simp] lemma initial_seg.to_functor_obj (j : α) : f.to_functor.obj j = f j :=
rfl

variables (g : order_iso ((<) : α → α → Prop) ((<) : β → β → Prop))

def order_iso.to_equivalence : α ≌ β :=
category_theory.preorder_equivalence (preorder_iso.of_strict_iso g)

end
