import order.complete_lattice
import order.complete_lattice_stuff
import order.initial_seg_stuff
import set_theory.cofinality
import tactic.tidy

local attribute [instance] classical.dec

universes u v

open lattice

class well_order_top (α : Type u) extends complete_linear_order α :=
(wf_lt : well_founded ((<) : α → α → Prop))

instance well_order_top_is_well_order {α : Type u} [well_order_top α] : is_well_order α (<) :=
{ wf := well_order_top.wf_lt α }

namespace well_order_top

noncomputable def mk' {α : Type u} [lattice.order_top α] [is_well_order α (<)] :
  well_order_top α :=
have le_or_gt : ∀ (a b : α), a ≤ b ∨ a > b := λ a b, begin -- TODO: use `match`
    rcases trichotomous_of (<) a b with h|h|h,
    exact or.inl (le_of_lt h),
    exact or.inl (le_of_eq h),
    exact or.inr h,
  end,
{ wf_lt := is_well_order.wf (<),
  le_total := λ a b, (le_or_gt a b).imp_right le_of_lt,
  decidable_le := classical.dec_rel _,
  .. (infer_instance : lattice.order_top α),
  .. complete_lattice.mk_of_Inf α
  { Inf := λ s, if h : s = ∅ then ⊤ else well_founded.min (is_well_order.wf (<)) s h,
    le_Inf := λ s a ha, begin
      split_ifs,
      { exact le_top },
      { apply ha, apply well_founded.min_mem }
    end,
    Inf_le := λ s a ha, begin
      split_ifs,
      { subst s, exact false.elim ha },
      { refine (le_or_gt _ _).resolve_right _,
        exact well_founded.not_lt_min (is_well_order.wf (<)) _ _ ha }
    end } }

section

variables {α : Type u} [well_order_top α]

def le_top {j : α} : j ≤ ⊤ := lattice.le_top


def is_bot (j : α) : Prop := j = ⊥

lemma is_bot.not_lt {i j : α} (h : is_bot j) : ¬(i < j) :=
by convert not_lt_bot

lemma is_bot.le {i j : α} (h : is_bot i) : i ≤ j :=
by convert bot_le


lemma bot_is_bot : is_bot (⊥ : α) := refl _

lemma is_bot_iff_bot {j : α} : is_bot j ↔ j = ⊥ := iff.rfl

lemma bot_le {j : α} : ⊥ ≤ j := lattice.bot_le

lemma bot_lt {j : α} (h : ¬ is_bot j) : ⊥ < j :=
(eq_or_lt_of_le bot_le).resolve_left (ne.symm h)


def is_succ (i j : α) : Prop :=
i < j ∧ ∀ k, k < j → k ≤ i

lemma is_succ.lt {i j : α} (h : is_succ i j) : i < j :=
h.1

lemma is_succ.le {i j : α} (h : is_succ i j) : i ≤ j :=
le_of_lt h.1

lemma is_succ.le_of_lt_succ {k i j : α} (h : is_succ i j) : k < j → k ≤ i :=
h.2 k

-- unused
lemma is_succ.ge_of_gt_prec {k i j : α} (h : is_succ i j) : k > i → k ≥ j :=
le_of_not_lt ∘ mt h.le_of_lt_succ ∘ not_le_of_lt

lemma is_succ.bot_lt {i j : α} (hi : is_bot i) (hj : is_succ i j) : i < j :=
(eq_or_lt_of_le hi.le).resolve_left (λ H, by subst H; exact absurd hj.lt (lt_irrefl i))

lemma has_succ_of_lt {i k : α} (h : i < k) : ∃ j, is_succ i j :=
let s : set α := {j | i < j},
    ⟨j, js, hj⟩ := well_founded.has_min (well_order_top.wf_lt α) s (set.ne_empty_of_mem h) in
⟨j, js, λ l hl, le_of_not_gt $ λ hl', hj l hl' hl⟩


def is_limit (j : α) : Prop :=
¬(is_bot j) ∧ ¬(∃ i, is_succ i j)

lemma is_limit.bot_lt {i j : α} (hi : is_bot i) (hj : is_limit j) : i < j :=
(eq_or_lt_of_le hi.le).resolve_left (λ H, by subst H; exact hj.1 hi)


inductive bot_or_succ_or_limit : α → Type u
| is_bot (j : α) (h : is_bot j) : bot_or_succ_or_limit j
| is_succ (i j : α) (h : is_succ i j) : bot_or_succ_or_limit j
| is_limit (j : α) (h : is_limit j) : bot_or_succ_or_limit j

noncomputable lemma is_bot_or_succ_or_limit (j : α) : bot_or_succ_or_limit j :=
begin
  by_cases h : j = ⊥,
  { subst h, exact bot_or_succ_or_limit.is_bot ⊥ rfl },
  { let i₀ := Sup {i | i < j},
    have i₀j : i₀ ≤ j := Sup_le (λ i hi, le_of_lt hi),
    by_cases h' : i₀ = j,
    { refine bot_or_succ_or_limit.is_limit j ⟨h, _⟩,
      rintro ⟨i, hi⟩,
      have : i < i₀, by rw h'; exact hi.lt,
      refine absurd _ (not_le_of_gt this),
      apply Sup_le,
      intros i' hi',
      exact hi.le_of_lt_succ hi' },
    { refine bot_or_succ_or_limit.is_succ i₀ j ⟨(eq_or_lt_of_le i₀j).resolve_left h', _⟩,
      intros k hk,
      apply le_Sup,
      exact hk } }
end

lemma not_bot_succ {i j : α} (h : is_bot j) : ¬ is_succ i j :=
λ h', h.not_lt h'.lt

lemma not_bot_limit {j : α} (h : is_bot j) : ¬ is_limit j :=
λ h', h'.1 h

lemma not_succ_limit {i j : α} (h : is_succ i j) : ¬ is_limit j :=
λ h', h'.2 ⟨i, h⟩

lemma is_succ.uniq {i i' j : α} (h : is_succ i j) (h' : is_succ i' j) : i = i' :=
le_antisymm (h'.le_of_lt_succ h.lt) (h.le_of_lt_succ h'.lt)


section cofinality

variables (α)
include α
noncomputable def cofinality : cardinal.{u} :=
(ordinal.typein (<) (⊤ : α)).cof

end cofinality

section other

lemma supr_limit {s : ℕ → α} (h : ∀ n, s n < s (n+1)) : is_limit (supr s) :=
begin
  rcases is_bot_or_succ_or_limit (supr s) with ⟨j, hj⟩|⟨i, j, hj⟩|⟨j, hj⟩,
  { have : s 0 < supr s, from lt_of_lt_of_le (h 0) (le_supr _ _),
    exact absurd this hj.not_lt },
  { have : ¬ ∀ n, s n ≤ i := λ H, not_le_of_lt hj.lt (supr_le H),
    rcases not_forall.mp this with ⟨n, hn⟩,
    replace hn : supr s ≤ s n := le_of_not_gt (mt hj.le_of_lt_succ hn),
    have : supr s < s (n+1), from lt_of_le_of_lt hn (h n),
    exact absurd this (not_lt_of_le (le_supr _ _)) },
  { exact hj }
end


end other

end

-- TODO: ?
section interval

variables {α : Type u}

section
variable [partial_order α]

def Io (j : α) : Type u := {i // i < j}
def Ic (j : α) : Type u := {i // i ≤ j}

def Io.mk {i j : α} (hj : i < j) : Io j := subtype.mk i hj
def Ic.mk {i j : α} (hj : i ≤ j) : Ic j := subtype.mk i hj

variables {j : α}

instance Io.partial_order : partial_order (Io j) := by dunfold Io; apply_instance
instance Ic.partial_order : partial_order (Ic j) := by dunfold Ic; apply_instance

def Io_initial_seg : initial_seg ((<) : Io j → Io j → Prop) ((<) : α → α → Prop) :=
{ to_fun := λ i, i.val,
  ord := by intros; refl,
  inj := by intros i i' h; cases i; cases i'; cases h; refl,
  init := λ ⟨i, hi⟩ i' hii', ⟨⟨i', lt_trans hii' hi⟩, rfl⟩ }

def Ic_initial_seg : initial_seg ((<) : Ic j → Ic j → Prop) ((<) : α → α → Prop) :=
{ to_fun := λ i, i.val,
  ord := by intros; refl,
  inj := by intros i i' h; cases i; cases i'; cases h; refl,
  init := λ ⟨i, hi⟩ i' hii', ⟨⟨i', le_trans (le_of_lt hii') hi⟩, rfl⟩ }

def Io_initial_seg_Ic : initial_seg ((<) : Io j → Io j → Prop) ((<) : Ic j → Ic j → Prop) :=
{ to_fun := λ i, ⟨i.val, le_of_lt i.property⟩,
  ord := by tidy,
  inj := by tidy,
  init := λ ⟨i, hi⟩ ⟨i', hi'⟩ hii', ⟨⟨i', lt_trans hii' hi⟩, rfl⟩ }

variables {j' : α} (h : j ≤ j')

def Ic_initial_seg_Ic : initial_seg ((<) : Ic j → Ic j → Prop) ((<) : Ic j' → Ic j' → Prop) :=
{ to_fun := λ i, ⟨i.val, le_trans i.property h⟩,
  ord := by intros; refl,
  inj := by tidy,
  init := λ ⟨i, hi⟩ ⟨i', hi'⟩ hii', ⟨⟨i', le_trans (le_of_lt hii') hi⟩, rfl⟩ }

/-
instance Io.is_well_order [is_well_order α (<)] : is_well_order (Io j) (<) :=
Io_initial_seg.to_order_embedding.is_well_order
-/

instance Ic.is_well_order [is_well_order α (<)] : is_well_order (Ic j) (<) :=
Ic_initial_seg.to_order_embedding.is_well_order

end

instance Ic.order_top [partial_order α] {j : α} : lattice.order_top (Ic j) :=
{ top := ⟨j, le_refl j⟩,
  le_top := λ p, p.property,
  .. (infer_instance : partial_order (Ic j)) }

-- This could be made "computable", of course, at the cost of more work
-- (Inf s = Inf (subtype.val '' s ∪ {j}))
noncomputable instance Ic.well_order_top [well_order_top α] {j : α} : well_order_top (Ic j) :=
{ bot := ⟨⊥, bot_le⟩,
  bot_le := λ p, bot_le,
  .. well_order_top.mk' }

end interval


section Ic

variables {α : Type u} [well_order_top α] {k : α}

lemma is_bot_iff {j : Ic k} : is_bot j ↔ is_bot j.val :=
subtype.ext

lemma is_succ_iff {i j : Ic k} : is_succ i j ↔ is_succ i.val j.val :=
begin
  split; intro H; refine ⟨H.1, _⟩; intros l hl,
  { exact H.2 ⟨l, le_trans (le_of_lt hl) j.property⟩ hl },
  { exact H.2 l.val hl }
end

lemma is_limit_iff {j : Ic k} : is_limit j ↔ is_limit j.val :=
begin
  dsimp [is_limit],
  simp only [is_bot_iff, is_succ_iff],
  convert iff.rfl using 3,
  apply propext,
  split; rintros ⟨i, Hi⟩,
  { exact ⟨⟨i, le_trans Hi.le j.property⟩, Hi⟩ },
  { exact ⟨i.val, Hi⟩ }
end

end Ic


-- unused
section initial_seg

variables {α : Type u} [well_order_top α] {β : Type v} [well_order_top β]
variables (f : initial_seg ((<) : α → α → Prop) ((<) : β → β → Prop))

lemma is_bot_iff_seg {j : α} : is_bot j ↔ is_bot (f j) :=
begin
  split; intro H; apply eq_bot_iff.mpr; apply le_of_not_lt; intro h,
  { rcases f.init _ _ h with ⟨i, hi⟩,
    erw [←hi, ←f.ord] at h,
    exact H.not_lt h },
  { rw f.ord at h,
    exact H.not_lt h }
end

lemma is_succ_iff_seg {i j : α} : is_succ i j ↔ is_succ (f i) (f j) :=
begin
  split; intro H,
  { refine ⟨f.ord'.mp H.1, λ k hk, _⟩,
    rcases f.init _ k hk with ⟨k', hk'⟩,
    subst k,
    erw ←f.ord_le,
    erw ←f.ord' at hk,
    exact H.2 _ hk },
  { refine ⟨f.ord'.mpr H.1, λ k hk, _⟩,
    rw f.ord_le,
    rw f.ord' at hk,
    exact H.2 _ hk }
end

lemma is_limit_iff_seg {j : α} : is_limit j ↔ is_limit (f j) :=
begin
  dsimp [is_limit],
  simp only [is_bot_iff_seg f, is_succ_iff_seg f],
  convert iff.rfl using 3,
  apply propext,
  split; rintros ⟨i, Hi⟩,
  { rcases f.init _ i Hi.lt with ⟨i', hi'⟩,
    refine ⟨i', _⟩,
    convert Hi },
  { exact ⟨f i, Hi⟩ }
end

end initial_seg


variables {α : Type u} [well_order_top α]

def iso_Ic_top :
  order_iso ((<) : α → α → Prop) ((<) : Ic (⊤ : α) → Ic (⊤ : α) → Prop) :=
{ to_fun := λ a, ⟨a, le_top⟩,
  inv_fun := λ p, p.1,
  left_inv := λ a, rfl,
  right_inv := λ ⟨a, h⟩, rfl,
  ord := λ a b, iff.rfl }

end well_order_top
