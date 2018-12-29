import set_theory.ordinal

namespace initial_seg

variables {α : Type*} {β : Type*}
  {r : α → α → Prop} {s : β → β → Prop}

theorem ord' (f : initial_seg r s) {a b} : r a b ↔ s (f a) (f b) :=
f.to_order_embedding.ord'

section
variables [partial_order α] [partial_order β]

lemma ord_le (f : initial_seg ((<) : α → α → Prop) ((<) : β → β → Prop)) {a a' : α} :
  a ≤ a' ↔ f a ≤ f a' :=
begin
  split; intro H,
  { rcases eq_or_lt_of_le H with rfl|H,
    { refl },
    { exact le_of_lt (f.ord'.mp H) } },
  { rcases eq_or_lt_of_le H with H|H,
    { exact le_of_eq (f.inj H) },
    { exact le_of_lt (f.ord'.mpr H) } }
end

end

end initial_seg
