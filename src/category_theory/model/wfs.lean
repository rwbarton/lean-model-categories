import category_theory.morphism_class
import category_theory.retract
import category_theory.colimits
import category_theory.transfinite.composition
import logic.crec

universes u v

namespace category_theory

variables {M : Type u} [𝓜 : category.{u v} M]
include 𝓜

def lp {a b x y : M} (f : a ⟶ b) (g : x ⟶ y) : Prop :=
∀ (h : a ⟶ x) (k : b ⟶ y), h ≫ g = f ≫ k →
∃ l : b ⟶ x, f ≫ l = h ∧ l ≫ g = k

def llp (R : morphism_class M) : morphism_class M :=
λ a b f, ∀ ⦃x y⦄ ⦃g : x ⟶ y⦄, R g → lp f g

def rlp (L : morphism_class M) : morphism_class M :=
λ x y g, ∀ ⦃a b⦄ ⦃f : a ⟶ b⦄, L f → lp f g

lemma llp_anti {R R' : morphism_class M} (h : R ⊆ R') : llp R' ⊆ llp R :=
λ a b f hf x y g hg, hf (h hg)

structure is_wfs (L R : morphism_class M) : Prop :=
(llp : L = llp R)
(rlp : R = rlp L)
(fact : ∀ {x y} (f : x ⟶ y), ∃ z (g : x ⟶ z) (h : z ⟶ y),
  L g ∧ R h ∧ g ≫ h = f)

lemma is_wfs.lp {L R : morphism_class M} (w : is_wfs L R)
  {a b x y} {f : a ⟶ b} {g : x ⟶ y} (hf : L f) (hg : R g) : lp f g :=
begin
  rw w.llp at hf,
  exact hf hg
end

lemma is_wfs.retract {L R : morphism_class M} (w : is_wfs L R)
  {a b a' b'} {f : a ⟶ b} {f' : a' ⟶ b'} (r : retract f f') (hf : L f) : L f' :=
begin
  rw w.llp,
  intros x y g hg h k s,
  rcases w.lp hf hg (r.ra ≫ h) (r.rb ≫ k)
    (by rw [category.assoc, s, ←category.assoc, ←category.assoc, r.hr]) with ⟨l, hl₁, hl₂⟩,
  refine ⟨r.ib ≫ l, _, _⟩,
  { rw [←category.assoc, ←r.hi, category.assoc, hl₁, ←category.assoc, r.ha, category.id_comp] },
  { rw [category.assoc, hl₂, ←category.assoc, r.hb, category.id_comp] }
end

lemma llp_rlp_self (L : morphism_class M) : L ⊆ llp (rlp L) :=
λ a b f hf x y g hg, hg hf

lemma wfs_of_factorization (I : morphism_class M)
  (h : ∀ {x y} (f : x ⟶ y), ∃ z (g : x ⟶ z) (h : z ⟶ y), llp (rlp I) g ∧ rlp I h ∧ g ≫ h = f) :
  is_wfs (llp (rlp I)) (rlp I) :=
{ llp := rfl,
  rlp := begin
    ext x y g,
    split; intro hg,
    { intros a b f hf, exact hf hg },
    { intros a b f hf, exact hg (llp_rlp_self _ hf) }
  end,
  fact := @h }

open morphism_class

lemma lp_isos_univ {a b x y} (f : a ⟶ b) (g : x ⟶ y) : isos M f → lp f g :=
begin
  rintro ⟨H⟩, resetI,
  intros h k s,
  refine ⟨inv f ≫ h, _, _⟩,
  { rw ←category.assoc, simp },
  { rw [category.assoc, s, ←category.assoc], simp }
end

lemma llp_univ : llp (univ M) = isos M :=
begin
  ext a b f,
  split; intro H,
  { rcases H trivial (𝟙 _) (𝟙 _) (by simp) with ⟨l, hl₁, hl₂⟩,
    exact ⟨⟨l, hl₁, hl₂⟩⟩ },
  { intros x y g _,
    exact lp_isos_univ f g H }
end

lemma rlp_isos : rlp (isos M) = univ M :=
begin
  ext x y g,
  suffices : rlp (isos M) g, from iff_true_intro this,
  rintros a b f H,
  exact lp_isos_univ f g H
end

lemma wfs_isos_univ : is_wfs (isos M) (univ M) :=
⟨llp_univ.symm, rlp_isos.symm,
 λ x y f, ⟨x, 𝟙 x, f, ⟨infer_instance⟩, trivial, category.id_comp _ f⟩⟩


-- TODO: phrase in terms of is_colimit?
section
open limits
lemma llp_coproduct (R : morphism_class M)
  {ι : Type v} {a b : ι → M} {f : Π i, a i ⟶ b i} (hf : ∀ i, llp R (f i))
  [limits.has_colimits_of_shape (discrete ι) M]
:
  llp R (limits.colim.map (nat_trans.of_function f)) :=
begin
  let A := functor.of_function a,
  let B := functor.of_function b,
  intros x y g hg h k s,
  have : ∀ i, ∃ li, f i ≫ li = colimit.ι A i ≫ h ∧ li ≫ g = colimit.ι B i ≫ k,
  { intro i,
    apply hf i hg,
    rw [category.assoc, s, ←category.assoc, ←category.assoc, colim.ι_map],
    refl },
  choose li hl using this,
  refine ⟨colimit.desc B (cocone.of_function x li), _, _⟩,
  { apply colimit.hom_ext, intro i,
    rw [←category.assoc, colim.ι_map, category.assoc, colimit.ι_desc],
    exact (hl i).1 },
  { apply colimit.hom_ext, intro i,
    rw [←category.assoc, colimit.ι_desc],
    exact (hl i).2 }
end
end

lemma llp_pushout (R : morphism_class M) {a b a' b' : M} {f : a ⟶ b} {f' : a' ⟶ b'}
  {i : a ⟶ a'} {j : b ⟶ b'} (po : Is_pushout f i j f') (hf : llp R f) : llp R f' :=
λ x y g hg h k s,
let ⟨l, hl₁, hl₂⟩ := hf hg (i ≫ h) (j ≫ k)
  (by rw [category.assoc, s, ←category.assoc, ←category.assoc, po.commutes]) in
⟨po.induced l h hl₁, by simp,
 begin
   apply po.uniqueness,
   { rw ←category.assoc,
     convert hl₂,
     simp },
   { rw ←category.assoc,
     convert s,
     simp }
 end⟩

open well_order_top
variables {γ : Type v} [well_order_top γ]
theorem llp_closed_under_transfinite_composition {R : morphism_class M}
  (c : transfinite_composition (llp R) γ) : llp R c.composition :=
begin
  intros x y g hg h k S,
  suffices : Π i, Σ' li : c.F.obj i ⟶ x,
    c.F.map ⟨⟨lattice.bot_le⟩⟩ ≫ li = h ∧ li ≫ g = c.F.map ⟨⟨lattice.le_top⟩⟩ ≫ k,
  { rcases this ⊤ with ⟨l, L⟩,
    refine ⟨l, _⟩,
    convert ←L using 2,
    convert category.id_comp _ _,
    apply c.F.map_id },
  refine crec (is_well_order.wf (<))
    (λ i i' hii' p p', c.F.map ⟨⟨le_of_lt hii'⟩⟩ ≫ p'.1 = p.1) _,
  rintros j ⟨l, hl⟩,

  -- The inductive consistency hypothesis only applies for i < i',
  -- but also holds automatically for i = i'.
  have hl' : ∀ i i' (hij : i < j) (hi'j : i' < j) (hii' : i ≤ i'),
    c.F.map ⟨⟨hii'⟩⟩ ≫ (l i' hi'j).fst = (l i hij).fst,
  { intros,
    cases eq_or_lt_of_le hii' with hii' hii',
    { subst hii', convert category.id_comp _ _, apply c.F.map_id },
    { exact hl i i' hij hi'j hii' } },

  apply classical.indefinite_description,
  rcases is_bot_or_succ_or_limit j with ⟨_,hj⟩|⟨i,_,hij⟩|⟨_,hj⟩,

  -- Base case
  { have := is_bot_iff_bot.mp hj,
    subst j,
    fsplit,
    { refine ⟨h, _, S⟩,
      convert category.id_comp _ _,
      apply c.F.map_id },
    { exact λ i ria, absurd ria hj.not_lt } },

  -- Successor case
  { -- We already constructed a lift up to `ix o`, and need to extend to `ix o.succ`.
    rcases classical.indefinite_description _
      (c.succ i j hij hg (l i _).1 (c.F.map ⟨⟨lattice.le_top⟩⟩ ≫ k) _) with ⟨l', hl'₁, hl'₂⟩,
    fsplit,
    { refine ⟨l', _, hl'₂⟩,
      -- New top triangle commutes
      { rw ←(l i _).snd.1,
        rw [←hl'₁, ←category.assoc, ←c.F.map_comp], refl } },
    -- New map extends the old ones
    { intros i' ria,
      -- By hl'₁, we extended the immediately preceding map, but we need to check all
      -- XXX: Need to handle the cases i = o, i < o separately
      rw ←hl' i' i ria hij.lt (hij.le_of_lt_succ ria),
      conv { to_rhs, rw [←hl'₁, ←category.assoc, ←c.F.map_comp] },
      refl },
    -- New bottom quadrilateral commutes
    { rw [←category.assoc, ←c.F.map_comp],
        apply (l _ _).snd.2 } },

  -- Limit case
  { -- Extend to the limit by gluing all the maps `l i` for `i < j`
    let t : limits.cocone (full_subcategory_inclusion (λ i, i < j) ⋙ c.F) :=
    { X := x, ι := { app := λ i, (l i.1 i.2).1, naturality' := begin
        rintros i i' ⟨⟨hii'⟩⟩,
        convert hl' i.1 i'.1 i.2 _ _,
        apply category.comp_id
      end } },
    rcases c.limit _ hj with ⟨hlim⟩,
    let l' := hlim.desc t,
    refine ⟨⟨l', _, _⟩, _⟩,
    -- New top triangle commutes
    { rw ←(l ⊥ (hj.bot_lt bot_is_bot)).snd.1,
      convert hlim.fac t ⟨⊥, _⟩,
      { convert category.id_comp _ _,
        apply c.F.map_id } },
    -- New bottom quadrilateral commutes
    { apply hlim.hom_ext,
      rintro ⟨i, io⟩,
      rw [←category.assoc, ←category.assoc],
      convert (l i io).snd.2,
      { apply hlim.fac },
      { erw ←c.F.map_comp, refl } },
    -- New map extends the old ones
    { exact λ i ria, hlim.fac t ⟨i, ria⟩ } }
end

end category_theory
