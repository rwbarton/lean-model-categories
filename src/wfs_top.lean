import category_theory.soa2
import homotopy_theory.topological_spaces.category
import homotopy_theory.topological_spaces.disk_sphere
import top_small
import sigma_stuff

universe u

open category_theory
open homotopy_theory.topological_spaces

-- Specialize small object argument to Top and closed T₁ inclusions.

section

-- C is Top.{u}
parameters {Iι : Type u} (IA : Iι → Top.{u}) (IB : Iι → Top.{u}) (If : Π i, IA i ⟶ IB i)

parameters (hIA : ∀ i, compact_space (IA i))
parameters (hIf : ∀ i, closed_t1_inclusion (If i))

inductive If_class : morphism_class Top.{u}
| I : ∀ i, If_class (If i)

def K : morphism_class Top.{u} :=
λ X Y f, llp (rlp If_class) f ∧ closed_t1_inclusion f

-- TODO: refactor out order_top part for successor ordinal?
-- TODO: move?
noncomputable instance ordinal.out.well_order_top (o : ordinal.{u}) :
  well_order_top (o + 1).out.α :=
begin
  let r := (o + 1).out.r,
  haveI := (o + 1).out.wo,
  have rt : ordinal.type r = o + 1,
  { rw ←ordinal.type_def,
    convert quotient.out_eq _,
    cases (o + 1).out, refl },

  letI : linear_order _ := linear_order_of_STO' r,
  letI : lattice.order_top ((o + 1).out.α) :=
    { top := ordinal.enum r o (by convert o.lt_succ_self),
      le_top := _,
      .. (infer_instance : partial_order _) },
  haveI : is_well_order ((o + 1).out.α) (<) := (o + 1).out.wo,
  exact well_order_top.mk',

  show ∀ i, i ≤ ordinal.enum r o _,
  { intro i,
    rw ←ordinal.enum_typein r i, swap, apply ordinal.typein_lt_type,
    have : ordinal.typein r i ≤ o,
    { rw ←ordinal.lt_succ,
      convert ←ordinal.typein_lt_type r _ },
    rcases eq_or_lt_of_le this with H|H,
    { convert ←le_refl _ },
    { exact le_of_lt ((ordinal.enum_lt _ _).mpr H) } }
end

lemma out_cofinality {o : ordinal.{u}} : well_order_top.cofinality ((o + 1).out.α) = o.cof :=
begin
  dsimp [well_order_top.cofinality],
  congr,
  haveI := (o + 1).out.wo,
  apply ordinal.typein_enum (o + 1).out.r
end

lemma closed_t1_inclusion_coproduct : closed_under_coproducts @closed_t1_inclusion :=
closed_under_coproducts_of_coproduct @Top_coproduct @Top_coproduct_is_colimit
  (@closed_under_isos_of_closed_under_pushouts _ _ @closed_t1_inclusion
     (λ a b a' b' f f' i j po hf, closed_t1_inclusion_of_pushout po hf)) $
begin
  intros ι a b f hf,
  refine ⟨embedding_sigma_map (λ i, (hf i).1), _, _⟩,
  { rw is_closed_sigma,
    intro i,
    convert (hf i).2.1 using 1,
    ext x,
    split,
    { rintro ⟨⟨j, y⟩, hy⟩,
      change sigma.mk j (f j y) = _ at hy,
      have : j = i, from congr_arg sigma.fst hy,
      subst j,
      use y,
      simp, cc },
    { rintro ⟨y, rfl⟩,
      exact ⟨⟨i, y⟩, rfl⟩ } },
  { rintro ⟨i, x⟩ h,
    have : x ∉ set.range (f i), by rintro ⟨y, rfl⟩; exact h ⟨⟨i, y⟩, rfl⟩,
    have : is_closed ({x} : set (b i)) := (hf i).2.2 _ this,
    convert embedding_is_closed _ _ this,
    swap,
    { exact sigma.mk i },
    { simp },
    { exact embedding_sigma_mk },
    { exact is_closed_sigma_mk } }
end

noncomputable def top_soa {X Y : Top.{u}} (g : X ⟶ Y) :
  Σ' Z (j : X ⟶ Z) (q : Z ⟶ Y), g = j ≫ q ∧ K j ∧ rlp If_class q :=
let ⟨Z, j, q, hg, hj, hq⟩ := soa_stmt If K
  (λ i, ⟨llp_rlp_self (If_class) (If_class.I i), hIf i⟩)
  (λ a b a' b' f i j f' po hf, ⟨llp_pushout _ po hf.1, closed_t1_inclusion_of_pushout po hf.2⟩)
  (λ ι a b f hf,
   ⟨llp_coproduct _ (λ i, (hf i).1),
    closed_t1_inclusion_coproduct (λ i, (hf i).2)⟩)
  (λ γ I₁ c, by exactI
    ⟨llp_closed_under_transfinite_composition (c.cast (λ a b f hf, hf.1)),
     closed_t1_inclusion_tcomp (c.cast (λ a b f hf, hf.2))⟩) 
  (λ i, transfinite.κ_small_mono (λ a b f hf, hf.2) (@compact_small_closed_t1_inclusion _ (hIA i)))
  ((ordinal.omega.{u} + 1).out.α)
  (by convert le_refl _; convert ←out_cofinality; exact ordinal.cof_omega) g in
⟨Z, j, q, hg, hj, begin rintros a b f ⟨i⟩, exact hq i end⟩

lemma top_wfs : is_wfs (llp (rlp If_class)) (rlp If_class) :=
wfs_of_factorization _ $
  λ X Y g, let ⟨Z, j, q, hg, hj, hq⟩ := top_soa g in
  ⟨Z, j, q, hj.1, hq, hg.symm⟩

end

section serre

instance : compact_space Top.point.{u} :=
begin
  constructor,
  haveI : fintype Top.point.{u} := show fintype punit, by apply_instance,
  exact compact_of_finite set.finite_univ
end

instance {n : ℕ} : compact_space (disk n) :=
begin
  induction n with n' ih,
  { change compact_space Top.point,
    apply_instance },
  { change compact_space (disk n' × I01),
    haveI := ih,
    apply_instance }
end

instance {n : ℕ} : t2_space (disk n) :=
begin
  induction n with n' ih,
  { change t2_space Top.point,
    apply_instance },
  { change t2_space (disk n' × I01),
    haveI := ih,
    apply_instance }
end

def serre_I : morphism_class Top.{0} :=
If_class sphere_minus_one disk sphere_disk_incl

lemma serre_caf : is_wfs (llp (rlp serre_I)) (rlp serre_I) :=
begin
  apply top_wfs,
  { intro n,
    constructor,
    refine (compact_iff_compact_image_of_embedding (Top.embedding_incl _)).mpr _,
    suffices : compact (disk_sphere_pair n).subset,
    { convert this,
      rw set.image_univ,
      apply set.subtype_val_range },
    change compact (_ : set (disk n)),
    exact compact_of_closed (sphere_disk_closed n) },
  { intro n,
    refine closed_t1_inclusion_of_closed_embedding_t1 _ (Top.embedding_incl _) _,
    convert sphere_disk_closed n,
    apply set.subtype_val_range }
end

open homotopy_theory.cylinder

instance I.t2_space {X : Top.{0}} [t2_space X] : t2_space (I.obj X : Top) :=
show t2_space (X × I01), by apply_instance

def serre_J : morphism_class Top.{0} :=
If_class disk (λ n, I.obj (disk n)) (λ n, (i 0).app _)

lemma serre_acf : is_wfs (llp (rlp serre_J)) (rlp serre_J) :=
begin
  apply top_wfs,
  { apply_instance },
  { intro n,
    exact closed_t1_inclusion_of_closed_embedding_t1 _ embedding_i closed_i }
end

end serre
