import category_theory.small
import homotopy_theory.topological_spaces.closed_t1_inclusion
import logic.crec
import tactic.norm_num
import closed_embedding

local attribute [instance] classical.prop_decidable

open category_theory category_theory.transfinite
open homotopy_theory.topological_spaces
open set

-- This seems too complicated, somehow.
lemma finite_of_discrete_subset_compact {α : Type*} [topological_space α] {s t : set α}
  (h : s ⊆ t) (hs : ∀ s' ⊆ s, is_closed s') (ht : compact t) : finite s :=
have compact s, from compact_of_is_closed_subset ht (hs _ (subset.refl s)) h,
have _ := compact_iff_compact_univ.mp this,
have opens : ∀ x ∈ (univ : set s), is_open ({x} : set s), begin
  intros x _,
  rw ←is_closed_compl_iff,
  convert ←continuous_iff_is_closed.mp continuous_subtype_val (subtype.val '' (- {x} : set s)) _,
  { exact preimage_image_eq _ subtype.val_injective },
  { apply hs, convert image_subset_range _ _, simp }
end,
let ⟨b, bs, bf, sb⟩ := compact_elim_finite_subcover_image this opens (by intro x; cases x; simpa) in -- make simp lemma?
begin
  rw (subset.antisymm bs (by simpa using sb)) at bf,
  convert ←finite_image subtype.val bf,
  simp
end

-- TODO: Convenient name for this c.F.map ... le_top stuff

open well_order_top

lemma tcomp_range_monotone {γ : Type*} [well_order_top γ]
  {I : morphism_class Top} (c : transfinite_composition I γ) {i j : γ} (h : i ≤ j) :
  range (c.F.map ⟨⟨(le_top : i ≤ ⊤)⟩⟩) ⊆ range (c.F.map ⟨⟨(le_top : j ≤ ⊤)⟩⟩) :=
begin
  rintros _ ⟨x, rfl⟩,
  refine ⟨c.F.map ⟨⟨h⟩⟩ x, _⟩,
  have := c.F.map_comp ⟨⟨h⟩⟩ ⟨⟨(le_top : j ≤ ⊤)⟩⟩,
  exact (Top.hom_congr this x).symm
end

lemma closed_embedding_of_closed_t1_inclusion {X Y : Top} {f : X ⟶ Y}
  (h : closed_t1_inclusion f) : closed_embedding f := ⟨h.1, h.2.1⟩

lemma closed_t1_inclusion_tcomp {γ : Type*} [well_order_top γ]
  (c : transfinite_composition @closed_t1_inclusion γ) : closed_t1_inclusion c.composition :=
have ce : ∀ j, closed_embedding (c.F.map ⟨⟨(le_top : j ≤ ⊤)⟩⟩), from
  λ j, closed_embedding_tcomp (c.cast @closed_embedding_of_closed_t1_inclusion) _,
⟨(ce ⊥).1, (ce ⊥).2, λ x hx, begin
   let s := {j | x ∈ range (c.F.map ⟨⟨(le_top : j ≤ ⊤)⟩⟩)},
   have : s ≠ ∅,
   { apply ne_empty_of_mem,
     change x ∈ range (c.F.map (𝟙 ⊤)),
     rw c.F.map_id,
     change x ∈ range id,       -- simp lemma?
     simp },
   let i := well_founded.min (is_well_order.wf (<)) s this,
   have is : i ∈ s, by apply well_founded.min_mem,
   have imin : ∀ i' < i, i' ∉ s, from
     λ i' hi' i's, well_founded.not_lt_min _ s this i's hi',
   change x ∈ range _ at is,
   -- i is the first stage at which x appears. It must be a successor stage.
   rcases is_bot_or_succ_or_limit i with ⟨_, hi⟩|⟨i', _, hi⟩|⟨_, hi⟩,
   { have : i = ⊥, from is_bot_iff_bot.mp hi,
     refine absurd _ hx,
     dsimp [transfinite_composition.composition],
     convert ←is },
   { rcases c.succ i' i hi with ⟨_, _, T₁⟩,
     rcases is with ⟨y, hy⟩,
     have : is_closed {y},
     { refine T₁ y _,
       rintro ⟨z, hz⟩,
       have : i' ∈ s,           -- TODO: Deduplicate with below
       { refine ⟨z, _⟩,
         rw [←hy, ←hz],
         have := c.F.map_comp ⟨⟨le_of_lt _⟩⟩ ⟨⟨le_top⟩⟩,
         exact (Top.hom_congr this z) },
       exact imin i' hi.lt this },
     convert (ce i).closed_iff_image_closed.mp this,
     simp [hy] },
   { rcases c.limit i hi with hlim,
     have := jointly_surjective (_ ⋙ forget) (limits.preserves_colimit.preserves forget hlim),
     rcases is with ⟨y, hy⟩,
     rcases this y with ⟨⟨i', hi'⟩, z, hz⟩,
     have : i' ∈ s,
     { refine ⟨z, _⟩,
       rw [←hy, ←hz],
       have := c.F.map_comp ⟨⟨le_of_lt hi'⟩⟩ ⟨⟨le_top⟩⟩,
       exact (Top.hom_congr this z) },
     exact absurd this (imin i' hi') }
 end⟩

-- TODO: Split off some simple parts of this into lemmas.
-- infinite_iff_unbounded?
-- sup over a cofinal subset is equal? unbounded subset cofinal in ℕ?
lemma compact_small_aux {X : Top} {k : set X} (hk : compact k)
  {γ : Type*} [well_order_top γ] (hγ : is_limit (⊤ : γ))
  (s : γ → set X) (h₁ : ∀ i j, i ≤ j → s i ⊆ s j) (h₂ : ∀ x, ∃ (j < ⊤), x ∈ s j)
  (h₃ : ∀ x, x ∉ s ⊥ → is_closed ({x} : set X))
  (h₄ : ∀ j, is_limit j → ∀ t ⊆ s j, (∀ i < j, is_closed (t ∩ s i)) → is_closed t) :
  ∃ j < ⊤, k ⊆ s j :=
begin
  by_contradiction H,
  simp only [not_exists, not_subset] at H,

  -- TODO: Tactic to make this more palatable?
  have r,
  { refine @crec' ℕ (<) nat.lt_wf
      (λ n, Σ' (j < ⊤), subtype ((k ∩ - s ⊥) ∩ s j : set X))
      (λ n n' h xn xn', xn'.2.2.val ∉ s xn.1) _,
    intros n x',
    apply classical.choice,
    cases n with n',
    { rcases H ⊥ (bot_lt (λ b, not_bot_limit b hγ)) with ⟨x, xk, xs⟩,
      rcases h₂ x with ⟨j, jt, xj⟩,
      refine ⟨⟨⟨j, jt, x, ⟨xk, xs⟩, xj⟩, λ i hi, _⟩⟩,
      cases hi },
    { rcases H (x'.val n' (nat.lt_succ_self _)).1 (x'.val n' (nat.lt_succ_self _)).2.1
        with ⟨x, xk, xs⟩,
      rcases h₂ x with ⟨j, jt, xj⟩,
      refine ⟨⟨⟨j, jt, x, ⟨xk, λ h, xs (h₁ _ _ bot_le h)⟩, xj⟩, λ i hi, _⟩⟩,
      { change x ∉ s (x'.val i hi).1,
        intro h,
        apply xs,
        rcases eq_or_lt_of_le (nat.le_of_lt_succ hi) with rfl|hi',
        { exact h },
        { have : (x'.val i hi).1 < (x'.val n' (nat.lt_succ_self _)).1,
          { refine (lt_or_ge _ _).resolve_right (λ h', _),
            apply x'.property i n' _ _ hi',
            apply h₁ _ _ h',
            apply (x'.val n' _).2.2.property.2 },
          exact h₁ _ _ (le_of_lt this) h } } } },
  rcases r with ⟨x, hx⟩, dsimp only [] at hx,

  have x_incr : ∀ i j (h : i < j), (x i).1 < (x j).1, from λ i j h,
    (lt_or_ge _ _).resolve_right (λ h', hx i j h (h₁ _ _ h' (x j).2.2.property.2)),

  have hx' : ∀ i j, (x j).2.2.val ∈ s (x i).1 → j ≤ i :=
   λ i j h, (lt_or_ge _ _).resolve_left (λ h', hx _ _ h' h),

  let m : γ := lattice.supr (λ n, (x n).1),
  have mlim : is_limit m,
  { apply supr_limit,
    intro n,
    apply x_incr,
    apply nat.lt_succ_self },

  let d : set X := range (λ n, (x n).2.2.val),
  have dk : d ⊆ k, { rintro _ ⟨n, rfl⟩, exact (x n).2.2.property.1.1 },
  have : ∀ d' ⊆ d, is_closed d',
  { intros d' hd',
    apply h₄ m mlim,
    { refine subset.trans hd' _,
      rintros _ ⟨n, rfl⟩,
      have : s (x n).1 ⊆ s m,
      { apply h₁, apply lattice.le_supr _ n },
      apply this,
      exact (x n).2.2.property.2 },
    { intros i hi,
      let I := {n | (x n).2.2.val ∈ d' ∩ s i},
      have : finite I,
      { by_contradiction inf,
        have : ∀ j, ∃ n ∈ I, n > j, -- lemma?
        { intro j,
          by_contradiction hj,
          have : I ⊆ {n | n ≤ j} := λ n nI, (lt_or_ge _ _).resolve_left (λ nj, hj ⟨n, nI, nj⟩),
          exact inf (finite_subset (finite_le_nat j) this) },
        have : i ≥ m,
        { apply lattice.supr_le,
          intro j,
          rcases this j with ⟨n, nI, nj⟩,
          refine le_of_lt ((lt_or_ge _ _).resolve_right (λ h, _)),
          exact not_lt_of_ge (hx' _ _ ((h₁ _ _ h) nI.2)) nj },
        exact not_lt_of_ge this hi },
      convert is_closed_Union this (λ n hn, h₃ _ (x n).2.2.property.1.2),
      ext z, simp only [mem_Union], split,
      { rintro ⟨zd', zsi⟩,
        rcases hd' zd' with ⟨zn, hzn⟩, subst z,
        refine ⟨zn, ⟨zd', zsi⟩, by apply mem_singleton⟩ },
      { rintro ⟨n, hn₁, hn₂⟩,
        rw mem_singleton_iff at hn₂, subst z, exact hn₁ } } },

  have : finite (range _) := finite_of_discrete_subset_compact dk this hk,

  have inj : function.injective (λ n, (x n).2.2.val),
  { intros i j xij, change (x i).2.2.val = (x j).2.2.val at xij,
    wlog hij : i ≤ j using [i j, j i], { apply le_total },
    refine (eq_or_lt_of_le hij).resolve_right (λ hij', _),
    have xi : (x i).2.2.val ∈ s (x i).1, from (x i).2.2.property.2,
    have xj : (x j).2.2.val ∉ s (x i).1, by apply hx _ _ hij',
    rw xij at xi, exact xj xi },
  rw ←image_univ at this,
  exact infinite_univ_nat (finite_of_finite_image inj this)
end

--- Hovey, Proposition 2.4.2
lemma compact_small_closed_t1_inclusion {X : Top} [compact_space X] :
  κ_small @closed_t1_inclusion cardinal.omega X :=
λ γ I₁ hγ c f, begin
  resetI,
  have ce : ∀ j, closed_embedding (c.F.map ⟨⟨(le_top : j ≤ ⊤)⟩⟩) :=
    λ j, closed_embedding_tcomp (c.cast @closed_embedding_of_closed_t1_inclusion) _,
  suffices : ∃ j < ⊤, range f ⊆ range (c.F.map ⟨⟨(le_top : j ≤ ⊤)⟩⟩),
  { rcases this with ⟨j, hj, hf⟩,
    exact ⟨j, hj, Top.factor_through_embedding hf (ce j).1, by simp⟩ },
  have : compact (range f), { rw ←image_univ, exact compact_image compact_univ f.property },
  apply compact_small_aux this (is_limit_of_cofinality hγ),
  { apply tcomp_range_monotone },
  { rcases c.limit ⊤ (is_limit_of_cofinality hγ) with hlim,
    have := jointly_surjective (_ ⋙ forget) (limits.preserves_colimit.preserves forget hlim),
    intro x,
    rcases this x with ⟨⟨j, jt⟩, y, hy⟩,
    refine ⟨j, jt, y, hy⟩ },
  { exact (closed_t1_inclusion_tcomp c).2.2 },
  { intros j hj t h₁ h₂,
    rw (ce j).closed_iff_preimage_closed h₁,
    rcases c.limit j hj with ⟨hlim⟩,
    rw is_closed_in_colimit _ hlim,
    rintro ⟨i, hi⟩,
    rw (ce i).closed_iff_image_closed,
    convert h₂ i hi,
    convert image_preimage_eq_inter_range using 2,
    rw ←preimage_comp,
    congr' 1,
    exact subtype.ext.mp (c.F.map_comp _ _).symm }
end

