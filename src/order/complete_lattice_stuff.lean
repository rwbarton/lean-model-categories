import order.complete_lattice

namespace lattice
universe u

variables (α : Type u) [partial_order α]

/-- Minimal data needed to define a complete lattice structure on a
  partially ordered set α in terms of the sup of any set. -/
structure complete_lattice.core_of_Sup :=
(Sup : set α → α)
(le_Sup : ∀s, ∀a∈s, a ≤ Sup s)
(Sup_le : ∀s a, (∀b∈s, b ≤ a) → Sup s ≤ a)

/-- Minimal data needed to define a complete lattice structure on a
  partially ordered set α in terms of the inf of any set. -/
structure complete_lattice.core_of_Inf :=
(Inf : set α → α)
(Inf_le : ∀s, ∀a∈s, Inf s ≤ a)
(le_Inf : ∀s a, (∀b∈s, a ≤ b) → a ≤ Inf s)

def semilattice_sup_bot.of_Sup (h : complete_lattice.core_of_Sup α) :
  semilattice_sup_bot α :=
{ bot := h.Sup ∅,
  bot_le := λ a, h.Sup_le _ _ (λ b hb, false.elim hb),

  sup := λ a b, h.Sup {a, b},
  le_sup_left := λ a b, h.le_Sup _ _ (by simp),
  le_sup_right := λ a b, h.le_Sup _ _ (by simp),
  sup_le := λ a b c hac hbc, h.Sup_le _ _ $ begin
    intros x hx,
    have : x = b ∨ x = a, by simpa using hx,
    cases this; subst x; apply_assumption
  end,

  .. (infer_instance : partial_order α) }

def semilattice_inf_top.of_Inf (h : complete_lattice.core_of_Inf α) :
  semilattice_inf_top α :=
{ top := h.Inf ∅,
  le_top := λ a, h.le_Inf _ _ (λ b hb, false.elim hb),

  inf := λ a b, h.Inf {a, b},
  inf_le_left := λ a b, h.Inf_le _ _ (by simp),
  inf_le_right := λ a b, h.Inf_le _ _ (by simp),
  le_inf := λ c a b hca hcb, h.le_Inf _ _ $ begin
    intros x hx,
    have : x = b ∨ x = a, by simpa using hx,
    cases this; subst x; apply_assumption
  end,

  .. (infer_instance : partial_order α) }

def Inf_of_Sup (h : complete_lattice.core_of_Sup α) :
  complete_lattice.core_of_Inf α :=
{ Inf := λ s, h.Sup {x | ∀ a ∈ s, x ≤ a},
  Inf_le := λ s a ha, h.Sup_le _ _ (λ b hb, hb a ha),
  le_Inf := λ s a ha, h.le_Sup _ _ ha }

def Sup_of_Inf (h : complete_lattice.core_of_Inf α) :
  complete_lattice.core_of_Sup α :=
{ Sup := λ s, h.Inf {x | ∀ a ∈ s, a ≤ x},
  le_Sup := λ s a ha, h.le_Inf _ _ (λ b hb, hb a ha),
  Sup_le := λ s a ha, h.Inf_le _ _ ha }

def complete_lattice.mk_of_Sup_Inf (hs : complete_lattice.core_of_Sup α)
  (hi : complete_lattice.core_of_Inf α) : complete_lattice α :=
{ .. semilattice_sup_bot.of_Sup α hs,
  .. semilattice_inf_top.of_Inf α hi,
  .. hs,
  .. hi }

def complete_lattice.mk_of_Sup (hs : complete_lattice.core_of_Sup α) :
  complete_lattice α :=
complete_lattice.mk_of_Sup_Inf α hs (Inf_of_Sup α hs)

def complete_lattice.mk_of_Inf (hi : complete_lattice.core_of_Inf α) :
  complete_lattice α :=
complete_lattice.mk_of_Sup_Inf α (Sup_of_Inf α hi) hi

end lattice
