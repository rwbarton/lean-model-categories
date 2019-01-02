import homotopy_theory.formal.i_category.cofibration_category
import homotopy_theory.topological_spaces.weak_equivalences
import top_small
import top_mono
import wfs_top -- for compact_space instances

noncomputable theory

open category_theory
open homotopy_theory.topological_spaces
open homotopy_theory.cofibrations

namespace model_top

local notation `Top` := Top.{0}

structure gen_lifting_data :=
(a b c : Top)
(f : a ⟶ b)
(f₀ f₁ : b ⟶ c)
--(h : f ≫ f₀ = f ≫ f₁)  -- Necessary?

def gen_lifting_condition (D : gen_lifting_data) {X Y : Top} (g : X ⟶ Y) :=
∀ (h : D.a ⟶ X) (k : D.b ⟶ Y), D.f ≫ k = h ≫ g →
∃ (l : D.b ⟶ X) (m : D.c ⟶ Y), D.f ≫ l = h ∧ D.f₀ ≫ m = k ∧ D.f₁ ≫ m = l ≫ g

/-- Lifting data for the condition: any square admits a lift in which
  the top triangle commutes and the bottom triangle commutes up to homotopy
  rel f. -/
def lifting_up_to_homotopy_data {a b : Top} {f : a ⟶ b} (hf : is_cof f) : gen_lifting_data :=
-- f doesn't really need to be a cofibration, but it makes things more convenient
-- because we defined the canonical_relative_cylinder for an I-category
{ a := a, b := b, f := f,
  c := (canonical_relative_cylinder hf).ob,
  f₀ := (canonical_relative_cylinder hf).i₀,
  f₁ := (canonical_relative_cylinder hf).i₁ }

lemma lifting_up_to_homotopy_condition {a b : Top} {f : a ⟶ b} (hf : is_cof f)
  {X Y : Top} (g : X ⟶ Y) : gen_lifting_condition (lifting_up_to_homotopy_data hf) g ↔
  ∀ (h : a ⟶ X) (k : b ⟶ Y), f ≫ k = h ≫ g →
  ∃ (l : b ⟶ X), f ≫ l = h ∧ homotopic_rel hf (l ≫ g) k :=
begin
  dsimp [gen_lifting_condition],
  apply forall_congr, intro h,
  apply forall_congr, intro k,
  apply imp_congr, refl,
  apply exists_congr, intro l,
  split,
  { rintro ⟨m, t, Hi₀, Hi₁⟩,
    refine ⟨t, _⟩,
    symmetry,
    refine ⟨_, ⟨⟨m, Hi₀, Hi₁⟩⟩⟩ },
  { rintro ⟨t, H⟩,
    rcases homotopic_rel' (canonical_relative_cylinder hf) (all_objects_fibrant _) _ _ H.symm
      with ⟨H, Hi₀, Hi₁⟩,
    exact ⟨H, t, Hi₀, Hi₁⟩ }
end

/-- Lifting data for the condition: any square admits a lift in which
  the top triangle commutes (no condition on the bottom triangle). -/
def half_lifting_data {a b : Top} (f : a ⟶ b) : gen_lifting_data :=
{ a := a, b := b, f := f,
  c := (has_pushouts.pushout f f).ob,
  f₀ := (has_pushouts.pushout f f).map₀,
  f₁ := (has_pushouts.pushout f f).map₁ }

lemma half_lifting_condition {a b : Top} (f : a ⟶ b) {X Y : Top} (g : X ⟶ Y) :
  gen_lifting_condition (half_lifting_data f) g ↔
  ∀ (h : a ⟶ X) (k : b ⟶ Y), f ≫ k = h ≫ g →
  ∃ (l : b ⟶ X), f ≫ l = h :=
begin
  dsimp [gen_lifting_condition],
  apply forall_congr, intro h,
  apply forall_congr, intro k,
  apply imp_congr_ctx, refl, intro s,
  apply exists_congr, intro l,
  split,
  { rintro ⟨_, t, _, _⟩, exact t },
  { intro t,
    refine ⟨(has_pushouts.pushout f f).is_pushout.induced k (l ≫ g) _, t, _, _⟩,
    { rw [←category.assoc, t, s] },
    all_goals { simp } }
end

/-- Lifting data for the condition: if two maps b ⟶ X agree on a and are
   homotopic rel a in Y, then they are also homotopic rel a in X. -/
def lift_homotopy_data {a b : Top} {j : a ⟶ b} (hj : is_cof j) : gen_lifting_data :=
half_lifting_data (canonical_relative_cylinder hj).ii

lemma lift_homotopy_condition {a b : Top} {j : a ⟶ b} (hj : is_cof j) {X Y : Top} (g : X ⟶ Y) :
  gen_lifting_condition (lift_homotopy_data hj) g ↔
  ∀ (f₀ f₁ : b ⟶ X), j ≫ f₀ = j ≫ f₁ →
  homotopic_rel hj (f₀ ≫ g) (f₁ ≫ g) → homotopic_rel hj f₀ f₁ :=
begin
  erw half_lifting_condition,
  let po := precofibration_category.pushout_by_cof j j hj,
  -- This could surely be made more succinct
  split,
  { intros H f₀ f₁ hf Hfg,
    rcases homotopic_rel' (canonical_relative_cylinder hj) (all_objects_fibrant _) _ _ Hfg
      with ⟨Hfg, Hi₀, Hi₁⟩,
    rcases H (po.is_pushout.induced f₀ f₁ hf) Hfg
        (by rw pushout_induced_comp; symmetry; apply pushout_induced_eq_iff; apply_assumption)
      with ⟨l, hl⟩,
    refine ⟨_, ⟨⟨l, _, _⟩⟩⟩;
    simp [relative_cylinder.i₀, relative_cylinder.i₁, canonical_relative_cylinder, hl] },
  { intros H h k s,
    have Hfg : homotopic_rel hj (po.map₀ ≫ h ≫ g) (po.map₁ ≫ h ≫ g),
    { refine ⟨_, ⟨⟨k, _, _⟩⟩⟩;
      rw ←s; simp [relative_cylinder.i₀, relative_cylinder.i₁, canonical_relative_cylinder] },
    have Hf : homotopic_rel hj (po.map₀ ≫ h) (po.map₁ ≫ h) := H (po.map₀ ≫ h) (po.map₁ ≫ h)
      (by rw [←category.assoc, ←category.assoc, po.is_pushout.commutes]) Hfg,
    rcases homotopic_rel' (canonical_relative_cylinder hj) (all_objects_fibrant _) _ _ Hf
      with ⟨Hf, Hi₀, Hi₁⟩,
    refine ⟨Hf, _⟩,
    apply po.is_pushout.uniqueness; rwa ←category.assoc }
end

local notation `is_iso'` := homotopy_theory.weak_equivalences.is_iso

lemma {u v} h_is_iso {C : Type u} [category.{u v} C] {a b : C} {f : a ⟶ b} :
  is_iso' f ↔ nonempty (is_iso f) :=
begin
  split,
  { rintro ⟨i, rfl⟩,
    exact ⟨infer_instance⟩ },
  { rintro ⟨i⟩,
    resetI,
    exact ⟨iso.of_is_iso f, rfl⟩ }
end

lemma {u} iso'_iff_bij {α β : Type u} {f : α ⟶ β} :
  is_iso' f ↔ function.bijective f :=
begin
  rw h_is_iso,
  split,
  { rintro ⟨e⟩,
    resetI,
    exact (iso.of_is_iso f).to_equiv.bijective },
  { intro H,
    let e := equiv.of_bijective H,
    exact ⟨is_iso.of_iso e.to_iso⟩ }
end

inductive weq_ι : Type
| inj₀  : weq_ι
| surj₀ : weq_ι
| injₙ  : ℕ → weq_ι
| surjₙ : ℕ → weq_ι

open weq_ι

/- The "gen_lifting_data" for weak equivalences are:

⬝ * ⊔ * → I ⇉ (pushout), which verifies injectivity on π₀

⬝ ∅ → * ⇉ I, which verifies surjectivity on π₀

⬝ Sⁿ ∨ Sⁿ → Sⁿ ∧ I₊ ⇉ (pushout), which verifies injectivity on πₙ, n ≥ 1

⬝ * → Sⁿ ⇉ Sⁿ ∧ I₊, which verifies surjectivity on πₙ, n ≥ 1

-/
def weq_D : weq_ι → gen_lifting_data
| inj₀      := lift_homotopy_data (all_objects_cofibrant.cofibrant Top.point)
| surj₀     := lifting_up_to_homotopy_data (all_objects_cofibrant.cofibrant Top.point)
| (injₙ n)  := lift_homotopy_data (based_sphere_well_pointed n)
| (surjₙ n) := lifting_up_to_homotopy_data (based_sphere_well_pointed n)

section compactness

universe u

lemma Top_pushout_ob.compact_space {a b₀ b₁ : Top} {f₀ : a ⟶ b₀} {f₁ : a ⟶ b₁}
  (h₀ : compact_space b₀) (h₁ : compact_space b₁) : compact_space (has_pushouts.pushout f₀ f₁).ob :=
begin
  let po := has_pushouts.pushout f₀ f₁,
  constructor,
  let g : b₀ ⊕ b₁ → po.ob := λ b, sum.rec_on b po.map₀ po.map₁,
  have : g '' set.univ = set.univ,
  { apply set.eq_univ_of_forall,
    -- We recall the definition of the pushout in Top as a quotient of the disjoint union
    rintro ⟨x⟩,
    refine ⟨x, trivial, _⟩,
    cases x; refl },
  rw ←this,
  exact compact_image compact_univ (continuous_sum_rec po.map₀.property po.map₁.property)
end

lemma Is_pushout_compact {a b₀ b₁ c : Top} {f₀ : a ⟶ b₀} {f₁ : a ⟶ b₁} {g₀ : b₀ ⟶ c} {g₁ : b₁ ⟶ c}
  (po : Is_pushout f₀ f₁ g₀ g₁) (hb₀ : compact_space b₀) (hb₁ : compact_space b₁) : compact_space c :=
let po' := has_pushouts.pushout f₀ f₁,
    e : po'.ob ≅ c := pushout.unique po'.is_pushout po in
begin
  haveI : compact_space po'.ob := Top_pushout_ob.compact_space hb₀ hb₁,
  constructor,
  have : e.hom '' set.univ = set.univ,
  { change Top.homeomorphism.equiv e '' set.univ = set.univ,
    rw [set.image_univ, set.range_iff_surjective],
    exact (Top.homeomorphism.equiv e).bijective.2 },
  rw ←this,
  exact compact_image compact_univ e.hom.property
end

lemma I.compact_space {a : Top} (h : compact_space a) :
  compact_space (show Top, from homotopy_theory.cylinder.I.obj a) := -- ??
show compact_space (a × I01), by apply_instance

lemma quotient.compact_space {A X : Top} (i : A ⟶ X) (h : compact_space X) :
  compact_space (quotient_space i) :=
Is_pushout_compact (quotient_space.is_pushout i) h (by apply_instance)

instance Top.empty.compact_space : compact_space Top.empty.{u} :=
begin
  constructor,
  haveI : fintype Top.empty.{u} := show fintype pempty, by apply_instance,
  exact compact_of_finite set.finite_univ
end

instance {n : ℕ} : compact_space (sphere_minus_one n) :=
begin
  constructor,
  rw ←compact_iff_compact_univ,
  change compact (_ : set (disk n)),
  apply compact_of_closed,
  apply sphere_disk_closed
end

lemma weq_compact (i : weq_ι) : compact_space (weq_D i).b :=
begin
  cases i with n n,
  { apply Top_pushout_ob.compact_space,
    { apply I.compact_space, apply_instance },
    { change compact_space Top.empty, apply_instance } },
  { change compact_space Top.point, apply_instance },
  { apply Top_pushout_ob.compact_space,
    { apply I.compact_space, apply quotient.compact_space, apply_instance },
    { change compact_space Top.point, apply_instance } },
  { apply quotient.compact_space, apply_instance }
end

end compactness

lemma π₀_iso_iff {X Y : Top} {g : X ⟶ Y} : is_iso' (π₀.map g) ↔
  (gen_lifting_condition (weq_D inj₀) g ∧ gen_lifting_condition (weq_D surj₀) g) :=
begin
  rw iso'_iff_bij,
  erw [lifting_up_to_homotopy_condition, lift_homotopy_condition],
  apply and_congr,
  { split,
    { intros H f₀ f₁ _ h,
      rw [homotopic_rel_iff_cylinder, homotopy_theory.cylinder.homotopic_rel_initial Ii_initial] at ⊢ h,
      suffices : ⟦f₀⟧ = ⟦f₁⟧, from quotient.exact this,
      apply H,
      exact quotient.sound h },
    { rintros H ⟨f₁⟩ ⟨f₂⟩ h,
      replace h : homotopy_theory.cylinder.homotopic (f₁ ≫ g) (f₂ ≫ g) := quotient.exact h,
      rw ←homotopy_theory.cylinder.homotopic_rel_initial.{1 0} Ii_initial (! *) at h,
      rw ←homotopic_rel_iff_cylinder (all_objects_cofibrant.cofibrant.{1 0} Top.point) at h,
      have h' := H f₁ f₂ (initial.uniqueness _ _) h,
      rw [homotopic_rel_iff_cylinder, homotopy_theory.cylinder.homotopic_rel_initial Ii_initial] at h',
      exact quotient.sound h' } },
  { split,
    { intros H _ k _,
      rcases H ⟦k⟧ with ⟨⟨l⟩, kl⟩,
      refine ⟨l, by apply initial.uniqueness, _⟩,
      rw [homotopic_rel_iff_cylinder, homotopy_theory.cylinder.homotopic_rel_initial Ii_initial],
      exact quotient.exact kl },
    { rintros H ⟨f⟩,
      rcases H (! X) f (by apply initial.uniqueness) with ⟨l, _, hl₂⟩,
      refine ⟨⟦l⟧, _⟩,
      rw [homotopic_rel_iff_cylinder, homotopy_theory.cylinder.homotopic_rel_initial Ii_initial] at hl₂,
      exact quotient.sound hl₂ } }
end

lemma π_iso_iff {n : ℕ} {X Y : Top} {g : X ⟶ Y} : (∀ (x : X), is_iso' (π_induced n x g)) ↔
  (gen_lifting_condition (weq_D (injₙ n)) g ∧ gen_lifting_condition (weq_D (surjₙ n)) g) :=
begin
  erw [lifting_up_to_homotopy_condition, lift_homotopy_condition],
  split,
  { intro H,
    split,
    { intros f₀ f₁ hf h,
      replace H := (iso'_iff_bij.mp (H (f₀ (based_sphere_basepoint n punit.star)))).1,
      let T := maps_extending (based_sphere_well_pointed n) (based_sphere_basepoint n ≫ f₀),
      let F₀ : T := ⟨f₀, rfl⟩,
      let F₁ : T := ⟨f₁, hf.symm⟩,
      rw homotopic_rel_iff_cylinder at ⊢ h,
      suffices : ⟦F₀⟧ = ⟦F₁⟧, from quotient.exact this,
      apply H,
      exact quotient.sound h },
    { intros h k s,
      replace H := (iso'_iff_bij.mp (H (h punit.star))).2,
      rcases H ⟦⟨k, by convert s; ext x; cases x; refl⟩⟧ with ⟨⟨l, hl⟩, kl⟩,
      refine ⟨l, _, _⟩,
      { convert hl, ext x, cases x, refl },
      rw homotopic_rel_iff_cylinder,
      exact quotient.exact kl } },
  { rintro ⟨Hi, Hs⟩ x,
    rw iso'_iff_bij,
    split,
    { rintro ⟨⟨f₁, hf₁⟩⟩ ⟨⟨f₂, hf₂⟩⟩ h,
      replace h : homotopy_theory.cylinder.homotopic_rel _ (f₁ ≫ g) (f₂ ≫ g) := quotient.exact h,
      rw ←homotopic_rel_iff_cylinder (based_sphere_well_pointed n) at h,
      have h' := Hi f₁ f₂ (hf₁.trans hf₂.symm) h,
      rw homotopic_rel_iff_cylinder at h',
      exact quotient.sound h' },
    { rintro ⟨⟨f, hf⟩⟩,
      rcases Hs (Top.const x) f hf with ⟨l, hl₁, hl₂⟩,
      refine ⟨⟦⟨l, hl₁⟩⟧, _⟩,
      rw homotopic_rel_iff_cylinder at hl₂,
      exact quotient.sound hl₂ } }
end

lemma weq_iff {X Y : Top} {g : X ⟶ Y} : is_weak_equivalence g ↔ ∀ i, gen_lifting_condition (weq_D i) g :=
begin
  split,
  { rintros ⟨h₀, hₙ⟩ i,
    rcases π₀_iso_iff.mp h₀,
    cases i with n n; { try { cases π_iso_iff.mp (hₙ n) }, assumption } },
  { intro H,
    exact ⟨π₀_iso_iff.mpr ⟨H inj₀, H surj₀⟩, λ n, π_iso_iff.mpr ⟨H (injₙ n), H (surjₙ n)⟩⟩ }
end

end model_top
