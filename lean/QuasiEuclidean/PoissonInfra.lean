-- SPDX-License-Identifier: MIT
-- Copyright 2026 Metere Industries, Inc. Author: Alfredo Metere.
-- Quasi-Euclidean Granular Geometry. Any derivative work must carry this notice:
--   This work is derivative of the Quasi-Euclidean Granular Geometry book
--   authored by Alfredo Metere. Copyright 2026 Metere Industries, Inc.
--   All rights reserved
-- See LICENSE.md and NOTICE.

import Mathlib
import QuasiEuclidean.OpenGeo


/-!
# Poisson point processes, Poisson sprinkling, and jittered sets

Shadow-type infrastructure (Lebesgue measure appears as the intensity), built here because
Mathlib has the Poisson *law* (`ProbabilityTheory.poissonMeasure`) but no Poisson *process*.

## The Poisson process
* `poissonProcess ν`: the Poisson process with finite intensity measure `ν`, as the law of a
  random finite configuration (`Config S = Σ n, Fin n → S`): the number of points is Poisson with
  mean `ν(S)`, and given `n` the points are i.i.d. with law `ν / ν(S)`.
* `poissonProcess_counts`: the counts in pairwise disjoint measurable sets have the product of
  Poisson laws (multinomial computation `sum_fiber_prod`); hence Poisson marginals
  (`hasLaw_count`) and independence (`iIndepFun_count`).
* `poissonProcess_map`, `measurePreserving_mapConfig`: the mapping theorem.
* Mean, variance and Chebyshev bounds of Poisson variables (`integral_of_hasLaw`,
  `variance_of_hasLaw`, `chebyshev_of_hasLaw`) and Chernoff bounds (`poisson_upper_tail`,
  `poisson_lower_tail`).
* `globalProcess μ Q`: the Poisson process with σ-finite intensity `μ`, built from independent
  window processes on the tiles of a tiling `Q` (`Measure.infinitePi`), with random counting
  measure `randomMeasure`.  Joint law of counts (`globalProcess_counts`, `gcount_counts`),
  uniqueness of the law of a random counting measure (`law_eq_of_counts`), and the mapping
  theorem for the law on the space of measures (`poissonLaw_map`).

## Poisson sets in `ℝ^d` and Poisson sprinkling of `ℝ^{1+n}`
* Isotropy in law under rigid motions (`poisson_rigid_law`, `poisson_rigid_invariant`), mean and
  variance of the content (`poisson_content_mean`, `poisson_content_variance`), uniform isotropy
  over the orthogonal group with probability tending to one (`poisson_uniform_isotropy`), the
  normal limit for `d = 2` (`poisson_clt_two`), and almost surely no repeated difference vectors
  (`poisson_distinct_differences`).
* Lorentz transformations preserve Lebesgue measure (`IsLorentz.measurePreserving`); the law of
  the sprinkling is Lorentz and translation invariant (`sprinkle_lorentz_invariant`,
  `sprinkle_translation_invariant`); there is no equivariant frame
  (`sprinkle_no_equivariant_frame`); mean, variance, Chebyshev, infinitesimal and strong-law
  forms of `μ_Π(A) ≈ leb(A)`; a translation-invariant point process with locally finite intensity
  charges no Lebesgue-null set (`ae_eq_zero_of_null`).

## Jittered sets
* Plane geometry of convex polygons: faces (`frontier_convexHull_subset`), rounding to a grid
  (`pplus_diff_subset`), thin strips (`volume_dset_le`), few boundary cells
  (`card_partial_le`).
* The random jittered set (`jlaw`), Hoeffding (`jcount_dev`) and Chernoff (`jcount_ge_le`)
  bounds, the probabilistic method (`exists_good_config`), and the classical existence theorem
  `jittered_exists`.
* The hyperfinite jittered set `jitSet` in the ultrapower: one point per cell (`jitSet_cell`), no
  repeated differences (`jitSet_distinct_diff`), the polygon bound (`jitSet_polygon`), vanishing
  retained terms (`jitSet_retained_zero`, `jitSet_retained_zero_standard`), faithfulness
  (`jitSet_faithful`) and Lebesgue shadow on Jordan sets (`jitSet_jordan`).
-/

open Finset

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
open scoped BigOperators

namespace QE.Poisson

theorem prod_comp_fiber {α : Type*} [Fintype α] [DecidableEq α] {n : ℕ} (q : α → ℝ)
    (c : Fin n → α) : ∏ i, q (c i) = ∏ a, q a ^ #{i | c i = a} := by
  rw [← Finset.prod_fiberwise (s := univ) (g := c) (f := fun i => q (c i))]
  refine Finset.prod_congr rfl fun a _ => ?_
  rw [Finset.prod_congr rfl (g := fun _ => q a) (fun i hi => by rw [(mem_filter.1 hi).2])]
  rw [prod_const]

theorem card_fiber_cons {α : Type*} [DecidableEq α] {n : ℕ} (a : α) (c : Fin n → α) (b : α) :
    #{i | (Fin.cons a c : Fin (n + 1) → α) i = b} = (if a = b then 1 else 0) + #{i | c i = b} := by
  rw [Fin.card_filter_univ_succ']
  simp

/-- The multinomial count, weighted: the sum over all words `c` of length `n` with letter counts
`K` of `∏ i, q (c i)`. -/
theorem sum_fiber_prod {α : Type*} [Fintype α] [DecidableEq α] (q : α → ℝ) (n : ℕ) (K : α → ℕ) :
    (∑ c ∈ (univ : Finset (Fin n → α)).filter (fun c => ∀ a, #{i | c i = a} = K a),
        ∏ i, q (c i)) * ∏ a, ((K a).factorial : ℝ)
      = if ∑ a, K a = n then (n.factorial : ℝ) * ∏ a, q a ^ K a else 0 := by
  induction n generalizing K with
  | zero =>
    by_cases hK : ∀ a, K a = 0
    · have h1 : (univ : Finset (Fin 0 → α)).filter (fun c => ∀ a, #{i | c i = a} = K a) = univ := by
        ext c; simp [hK]
      rw [h1]
      simp [hK]
    · push_neg at hK
      obtain ⟨a, ha⟩ := hK
      have h1 : (univ : Finset (Fin 0 → α)).filter (fun c => ∀ a, #{i | c i = a} = K a) = ∅ := by
        ext c; simp only [mem_filter, mem_univ, true_and, Finset.notMem_empty, iff_false]
        intro h; exact ha (by simpa using (h a).symm)
      have h2 : ∑ a, K a ≠ 0 := by
        intro h; exact ha ((Finset.sum_eq_zero_iff.1 h) a (mem_univ _))
      rw [h1, if_neg h2]; simp
  | succ n ih =>
    classical
    rw [Finset.sum_filter]
    rw [← (Fin.consEquiv (fun _ : Fin (n + 1) => α)).sum_comp, Fintype.sum_prod_type]
    simp only [Fin.consEquiv_apply, card_fiber_cons, Fin.prod_univ_succ, Fin.cons_zero,
      Fin.cons_succ]
    rw [Finset.sum_mul]
    -- each letter `a`
    have key : ∀ a, (∑ c' : Fin n → α, if ∀ b, (if a = b then 1 else 0) + #{i | c' i = b} = K b
        then q a * ∏ i, q (c' i) else 0) * ∏ b, ((K b).factorial : ℝ)
        = if ∑ b, K b = n + 1 then (K a : ℝ) * (n.factorial * ∏ b, q b ^ K b) else 0 := by
      intro a
      by_cases ha : K a = 0
      · have : ∀ c' : Fin n → α, ¬ ∀ b, (if a = b then 1 else 0) + #{i | c' i = b} = K b := by
          intro c' h; have := h a; simp [ha] at this
        simp [this, ha]
      · set K' := Function.update K a (K a - 1) with hK'
        have hcond : ∀ c' : Fin n → α, (∀ b, (if a = b then 1 else 0) + #{i | c' i = b} = K b) ↔
            ∀ b, #{i | c' i = b} = K' b := by
          intro c'
          refine forall_congr' fun b => ?_
          by_cases hb : a = b
          · subst hb; simp only [if_true, hK', Function.update_self]; omega
          · simp only [hb, if_false, zero_add, hK', Function.update_of_ne (Ne.symm hb)]
        simp_rw [hcond]
        rw [← Finset.sum_filter, ← Finset.mul_sum]
        have hfac : ∏ b, ((K b).factorial : ℝ) = (K a : ℝ) * ∏ b, ((K' b).factorial : ℝ) := by
          have e1 : ∏ b, ((K' b).factorial : ℝ) =
              ((K a - 1).factorial : ℝ) * ∏ b ∈ univ \ {a}, ((K b).factorial : ℝ) := by
            rw [show (fun b => ((K' b).factorial : ℝ)) =
                Function.update (fun b => ((K b).factorial : ℝ)) a ((K a - 1).factorial : ℝ) from by
                  ext b; by_cases hb : b = a
                  · subst hb; simp [hK']
                  · simp [hK', Function.update_of_ne hb]]
            rw [Finset.prod_update_of_mem (mem_univ a)]
          rw [e1, Finset.sdiff_singleton_eq_erase, ← Finset.mul_prod_erase univ _ (mem_univ a)]
          have : (K a).factorial = K a * (K a - 1).factorial := by
            conv_lhs => rw [show K a = (K a - 1) + 1 by omega]
            rw [Nat.factorial_succ]; congr 1; omega
          rw [this]; push_cast; ring
        have hsum : ∑ b, K b = ∑ b, K' b + 1 := by
          have e1 : ∑ b, K' b = (K a - 1) + ∑ b ∈ univ \ {a}, K b := by
            rw [hK', Finset.sum_update_of_mem (mem_univ a)]
          rw [e1, Finset.sdiff_singleton_eq_erase, ← Finset.add_sum_erase univ _ (mem_univ a)]; omega
        have hpow : q a * ∏ b, q b ^ K' b = ∏ b, q b ^ K b := by
          have e1 : ∏ b, q b ^ K' b = q a ^ (K a - 1) * ∏ b ∈ univ \ {a}, q b ^ K b := by
            rw [show (fun b => q b ^ K' b) =
                Function.update (fun b => q b ^ K b) a (q a ^ (K a - 1)) from by
                  ext b; by_cases hb : b = a
                  · subst hb; simp [hK']
                  · simp [hK', Function.update_of_ne hb]]
            rw [Finset.prod_update_of_mem (mem_univ a)]
          rw [e1, Finset.sdiff_singleton_eq_erase, ← Finset.mul_prod_erase univ (fun b => q b ^ K b) (mem_univ a)]
          rw [← mul_assoc, ← pow_succ']
          congr 2; omega
        rw [hfac, show ∀ x y z : ℝ, q a * x * (y * z) = y * q a * (x * z) from by intros; ring,
          ih K', hsum]
        by_cases hn : ∑ b, K' b = n
        · rw [if_pos hn, if_pos (by omega), ← hpow]; ring
        · rw [if_neg hn, if_neg (by omega)]; ring
    rw [Finset.sum_congr rfl (fun a _ => key a)]
    by_cases hn : ∑ b, K b = n + 1
    · simp only [hn, if_true]
      rw [← Finset.sum_mul, ← Nat.cast_sum, hn, Nat.factorial_succ]; push_cast; ring
    · simp [hn]


open MeasureTheory ProbabilityTheory Function Filter
open scoped Topology
open scoped ENNReal NNReal

noncomputable section

/-- A finite configuration in `S`: a number `n` of points and their positions. -/
abbrev Config (S : Type*) := Σ n : ℕ, (Fin n → S)

/-- The configuration of `n` points `x`. -/
abbrev cfg {S : Type*} (n : ℕ) (x : Fin n → S) : Config S := ⟨n, x⟩

variable {S : Type*} [MeasurableSpace S]

theorem measurable_mk (n : ℕ) : Measurable (cfg n : (Fin n → S) → Config S) := by
  rw [measurable_iff_comap_le]
  exact le_trans (MeasurableSpace.comap_mono (iInf_le _ n)) MeasurableSpace.comap_map_le

theorem measurableSet_config {s : Set (Config S)} :
    MeasurableSet s ↔ ∀ n, MeasurableSet (cfg n ⁻¹' s : Set (Fin n → S)) := by
  show MeasurableSet[⨅ a, _] s ↔ _
  rw [MeasurableSpace.measurableSet_iInf]; rfl

theorem cfg_injective (n : ℕ) : Function.Injective (cfg n : (Fin n → S) → Config S) :=
  fun _ _ h => eq_of_heq (Sigma.mk.inj h).2

theorem measurableEmbedding_mk (n : ℕ) :
    MeasurableEmbedding (cfg n : (Fin n → S) → Config S) where
  injective := cfg_injective n
  measurable := measurable_mk n
  measurableSet_image' := by
    intro t ht
    rw [measurableSet_config]
    intro m
    by_cases h : m = n
    · subst h
      rw [Set.preimage_image_eq _ (cfg_injective m)]; exact ht
    · convert MeasurableSet.empty
      ext x; simp only [Set.mem_preimage, Set.mem_image, Set.mem_empty_iff_false, iff_false]
      rintro ⟨y, hy⟩
      exact h (congrArg Sigma.fst hy.2).symm

open Classical in
/-- The number of points of a configuration in `B`. -/
def count (B : Set S) (ω : Config S) : ℕ := #{i | ω.2 i ∈ B}

/-- The Poisson weight `e^{-r} r^n / n!`. -/
def pw (r : ℝ) (n : ℕ) : ℝ := Real.exp (-r) * r ^ n / n.factorial

theorem pw_nonneg {r : ℝ} (hr : 0 ≤ r) (n : ℕ) : 0 ≤ pw r n := by
  unfold pw; positivity

/-- The uniform (normalised) law of a finite measure. -/
def unif (ν : Measure S) : Measure S := (ν Set.univ)⁻¹ • ν

/-- **The Poisson point process with finite intensity measure `ν`**, as the law of a random
finite configuration: the number of points is Poisson with mean `ν(S)`, and given that it is
`n`, the points are `n` independent samples of the normalised law `ν / ν(S)`. -/
def poissonProcess (ν : Measure S) : Measure (Config S) :=
  Measure.sum fun n : ℕ => ENNReal.ofReal (pw (ν Set.univ).toReal n) •
    (Measure.pi fun _ : Fin n => unif ν).map (cfg n)

theorem poissonProcess_apply (ν : Measure S) (s : Set (Config S)) :
    poissonProcess ν s = ∑' n : ℕ, ENNReal.ofReal (pw (ν Set.univ).toReal n) *
      (Measure.pi fun _ : Fin n => unif ν) (cfg n ⁻¹' s) := by
  rw [poissonProcess, Measure.sum_apply_of_countable]
  congr 1; ext n
  rw [Measure.smul_apply, (measurableEmbedding_mk n).map_apply, smul_eq_mul]

/-! ### Labels of a partition -/

section Fiber

variable {ι : Type*} [Fintype ι]

open Classical

/-- The label of a point with respect to a family of disjoint sets: `some j` on `B j`,
`none` off their union. -/
def label (B : ι → Set S) (s : S) : Option ι :=
  if h : ∃ j, s ∈ B j then some h.choose else none

/-- The cells of the partition generated by `B`: `B j`, and the complement of their union. -/
def cell (B : ι → Set S) : Option ι → Set S
  | some j => B j
  | none => (⋃ j, B j)ᶜ

theorem mem_cell_iff {B : ι → Set S} (hd : Pairwise (Disjoint on B)) (s : S) (a : Option ι) :
    s ∈ cell B a ↔ label B s = a := by
  classical
  cases a with
  | none =>
    simp only [cell, Set.mem_compl_iff, Set.mem_iUnion, not_exists, label]
    constructor
    · intro h; rw [dif_neg (by push_neg; exact h)]
    · intro h j hj
      rw [dif_pos ⟨j, hj⟩] at h; exact absurd h (by simp)
  | some j =>
    simp only [cell, label]
    constructor
    · intro hj
      have hex : ∃ j, s ∈ B j := ⟨j, hj⟩
      rw [dif_pos hex]
      congr 1
      by_contra hne
      exact Set.disjoint_left.1 (hd hne) hex.choose_spec hj
    · intro h
      by_cases hex : ∃ j, s ∈ B j
      · rw [dif_pos hex] at h
        have := Option.some_injective _ h
        rw [← this]; exact hex.choose_spec
      · rw [dif_neg hex] at h; exact absurd h (by simp)

theorem measurableSet_cell {B : ι → Set S} (hB : ∀ j, MeasurableSet (B j)) (a : Option ι) :
    MeasurableSet (cell B a) := by
  cases a with
  | none => exact (MeasurableSet.iUnion hB).compl
  | some j => exact hB j

theorem pairwise_disjoint_cell {B : ι → Set S} (hd : Pairwise (Disjoint on B)) :
    Pairwise (Disjoint on cell B) := by
  intro a b hab
  refine Set.disjoint_left.2 fun s ha hb => hab ?_
  rw [mem_cell_iff hd] at ha hb
  rw [← ha, ← hb]

theorem iUnion_cell {B : ι → Set S} (hd : Pairwise (Disjoint on B)) :
    (⋃ a, cell B a) = Set.univ := by
  ext s
  simp only [Set.mem_iUnion, Set.mem_univ, iff_true]
  exact ⟨label B s, (mem_cell_iff hd s _).2 rfl⟩

/-- The fibre set of a count vector is a disjoint union of boxes indexed by labellings. -/
theorem fiber_eq_iUnion {B : ι → Set S} (hd : Pairwise (Disjoint on B)) (n : ℕ) (k : ι → ℕ) :
    {x : Fin n → S | ∀ j, #{i | x i ∈ B j} = k j} =
      ⋃ c ∈ (univ : Finset (Fin n → Option ι)).filter (fun c => ∀ j, #{i | c i = some j} = k j),
        Set.univ.pi (fun i => cell B (c i)) := by
  classical
  ext x
  simp only [Set.mem_setOf_eq, Set.mem_iUnion, mem_filter, mem_univ, true_and, Set.mem_pi,
    Set.mem_univ, forall_const, exists_prop]
  have hlab : ∀ c : Fin n → Option ι, (∀ i, x i ∈ cell B (c i)) ↔ c = fun i => label B (x i) := by
    intro c
    simp_rw [mem_cell_iff hd]
    constructor
    · intro h; ext1 i; exact (h i).symm
    · rintro rfl i; rfl
  have hcnt : ∀ j, #{i | x i ∈ B j} = #{i | label B (x i) = some j} := by
    intro j
    congr 1; ext i
    simp only [mem_filter, mem_univ, true_and]
    exact mem_cell_iff hd (x i) (some j)
  constructor
  · intro h
    exact ⟨fun i => label B (x i), fun j => (hcnt j).symm.trans (h j), (hlab _).2 rfl⟩
  · rintro ⟨c, hc, hx⟩ j
    rw [(hlab c).1 hx] at hc
    rw [hcnt j]; exact hc j

theorem pi_fiber (μ : Measure S) [IsFiniteMeasure μ] {B : ι → Set S}
    (hB : ∀ j, MeasurableSet (B j)) (hd : Pairwise (Disjoint on B)) (n : ℕ) (k : ι → ℕ) :
    (Measure.pi fun _ : Fin n => μ) {x : Fin n → S | ∀ j, #{i | x i ∈ B j} = k j} =
      ENNReal.ofReal (∑ c ∈ (univ : Finset (Fin n → Option ι)).filter
        (fun c => ∀ j, #{i | c i = some j} = k j), ∏ i, (μ (cell B (c i))).toReal) := by
  rw [fiber_eq_iUnion hd, measure_biUnion_finset]
  · rw [ENNReal.ofReal_sum_of_nonneg (fun _ _ => by positivity)]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [Measure.pi_pi, ENNReal.ofReal_prod_of_nonneg (fun _ _ => by positivity)]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [ENNReal.ofReal_toReal (measure_ne_top _ _)]
  · intro c _ c' _ hcc'
    refine Set.disjoint_left.2 fun x hx hx' => hcc' ?_
    ext1 i
    have h1 := (mem_cell_iff hd (x i) (c i)).1 (hx i (Set.mem_univ _))
    have h2 := (mem_cell_iff hd (x i) (c' i)).1 (hx' i (Set.mem_univ _))
    rw [← h1, ← h2]
  · intro c _
    exact MeasurableSet.univ_pi fun i => measurableSet_cell hB (c i)

/-- Closed form of the labelling sum: multinomial coefficients. -/
theorem sum_label_prod (q : Option ι → ℝ) (n : ℕ) (k : ι → ℕ) :
    ∑ c ∈ (univ : Finset (Fin n → Option ι)).filter (fun c => ∀ j, #{i | c i = some j} = k j),
        ∏ i, q (c i) =
      if ∑ j, k j ≤ n then
        (n.factorial : ℝ) / ((n - ∑ j, k j).factorial * ∏ j, ((k j).factorial : ℝ)) *
          (q none ^ (n - ∑ j, k j) * ∏ j, q (some j) ^ k j)
      else 0 := by
  have hsum_fib : ∀ c : Fin n → Option ι,
      n = #{i | c i = none} + ∑ j, #{i | c i = some j} := by
    intro c
    have := Finset.card_eq_sum_card_fiberwise (s := (univ : Finset (Fin n))) (t := univ)
      (f := c) (fun _ _ => mem_univ _)
    rw [card_univ, Fintype.card_fin, Fintype.sum_option] at this
    exact this
  by_cases hs : ∑ j, k j ≤ n
  · rw [if_pos hs]
    set K : Option ι → ℕ := fun a => a.elim (n - ∑ j, k j) k with hK
    have hfilter : (univ : Finset (Fin n → Option ι)).filter
        (fun c => ∀ j, #{i | c i = some j} = k j) =
        (univ : Finset (Fin n → Option ι)).filter (fun c => ∀ a, #{i | c i = a} = K a) := by
      ext c
      simp only [mem_filter, mem_univ, true_and]
      constructor
      · intro h a
        cases a with
        | none =>
          have h1 := hsum_fib c
          have h2 : ∑ j, #{i | c i = some j} = ∑ j, k j := Finset.sum_congr rfl (fun j _ => h j)
          simp only [hK, Option.elim]
          omega
        | some j => exact h j
      · intro h j; exact h (some j)
    have hc := sum_fiber_prod q n K
    rw [← hfilter] at hc
    have hKsum : ∑ a, K a = n := by
      rw [Fintype.sum_option]; simp only [hK, Option.elim]; omega
    rw [if_pos hKsum, Fintype.prod_option, Fintype.prod_option] at hc
    simp only [hK, Option.elim] at hc
    have hpos : ((n - ∑ j, k j).factorial : ℝ) * ∏ j, ((k j).factorial : ℝ) ≠ 0 := by
      apply mul_ne_zero
      · exact_mod_cast Nat.factorial_ne_zero _
      · exact Finset.prod_ne_zero_iff.2 fun j _ => by exact_mod_cast Nat.factorial_ne_zero _
    field_simp
    linear_combination hc
  · rw [if_neg hs]
    apply Finset.sum_eq_zero
    intro c hc
    exfalso; apply hs
    simp only [mem_filter, mem_univ, true_and] at hc
    have h1 := hsum_fib c
    have h2 : ∑ j, #{i | c i = some j} = ∑ j, k j := Finset.sum_congr rfl (fun j _ => hc j)
    omega

end Fiber

theorem hasSum_pow_div_factorial (x : ℝ) :
    HasSum (fun n : ℕ => x ^ n / (n.factorial : ℝ)) (Real.exp x) := by
  rw [Real.exp_eq_exp_ℝ]
  exact NormedSpace.expSeries_div_hasSum_exp x

theorem isProbabilityMeasure_unif (ν : Measure S) [IsFiniteMeasure ν] (hν : ν Set.univ ≠ 0) :
    IsProbabilityMeasure (unif ν) :=
  ⟨by simp [unif, ENNReal.inv_mul_cancel hν (measure_ne_top _ _)]⟩

theorem toReal_unif (ν : Measure S) (s : Set S) :
    (unif ν s).toReal = (ν s).toReal / (ν Set.univ).toReal := by
  simp [unif, ENNReal.toReal_mul, div_eq_inv_mul]

section Joint

variable {ι : Type*} [Fintype ι]

open Classical

theorem sum_cell_measure (μ : Measure S) [IsFiniteMeasure μ] {B : ι → Set S}
    (hB : ∀ j, MeasurableSet (B j)) (hd : Pairwise (Disjoint on B)) :
    (μ Set.univ).toReal = ∑ a, (μ (cell B a)).toReal := by
  rw [← iUnion_cell hd, measure_iUnion (pairwise_disjoint_cell hd) (measurableSet_cell hB),
    tsum_fintype, ENNReal.toReal_sum (fun a _ => measure_ne_top _ _)]

/-- **Joint law of the counts.**  For pairwise disjoint measurable sets `B j`, the probability
that the Poisson process has exactly `k j` points in each `B j` is the product of the Poisson
weights `e^{-ν(B j)} ν(B j)^{k j} / (k j)!`.  This is at once the Poisson marginal law and the
independence of the counts. -/
theorem poissonProcess_counts (ν : Measure S) [IsFiniteMeasure ν] (hν : ν Set.univ ≠ 0)
    {B : ι → Set S} (hB : ∀ j, MeasurableSet (B j)) (hd : Pairwise (Disjoint on B)) (k : ι → ℕ) :
    poissonProcess ν {ω | ∀ j, count (B j) ω = k j} =
      ∏ j, ENNReal.ofReal (pw (ν (B j)).toReal (k j)) := by
  haveI := isProbabilityMeasure_unif ν hν
  rw [poissonProcess_apply]
  have hpre : ∀ n, (Measure.pi fun _ : Fin n => unif ν)
      (cfg n ⁻¹' {ω : Config S | ∀ j, count (B j) ω = k j}) =
      ENNReal.ofReal (∑ c ∈ (univ : Finset (Fin n → Option ι)).filter
        (fun c => ∀ j, #{i | c i = some j} = k j), ∏ i, (unif ν (cell B (c i))).toReal) :=
    fun n => pi_fiber (unif ν) hB hd n k
  simp_rw [hpre, sum_label_prod (fun a => (unif ν (cell B a)).toReal)]
  set Λ := (ν Set.univ).toReal with hΛ
  set m : Option ι → ℝ := fun a => (ν (cell B a)).toReal with hm
  set sk := ∑ j, k j with hsk
  have hΛpos : 0 < Λ := ENNReal.toReal_pos hν (measure_ne_top _ _)
  have hq : ∀ a, (unif ν (cell B a)).toReal = m a / Λ := fun a => toReal_unif ν _
  simp_rw [hq]
  have hΛsum : Λ = m none + ∑ j, m (some j) := by
    rw [hΛ, sum_cell_measure ν hB hd, Fintype.sum_option]
  -- the real series
  set F : ℕ → ℝ := fun n => if sk ≤ n then
        (n.factorial : ℝ) / ((n - sk).factorial * ∏ j, ((k j).factorial : ℝ)) *
          ((m none / Λ) ^ (n - sk) * ∏ j, (m (some j) / Λ) ^ k j) else 0 with hF
  have hF0 : ∀ n, 0 ≤ F n := by
    intro n; simp only [hF]; split_ifs
    · apply mul_nonneg (by positivity)
      apply mul_nonneg (pow_nonneg (div_nonneg ENNReal.toReal_nonneg hΛpos.le) _)
      exact Finset.prod_nonneg fun j _ => pow_nonneg (div_nonneg ENNReal.toReal_nonneg hΛpos.le) _
    · exact le_refl _
  set P : ℝ := ∏ j, pw (m (some j)) (k j) with hP
  have hterm : ∀ r, pw Λ (r + sk) * F (r + sk) =
      (Real.exp (-Λ) * ∏ j, (m (some j) ^ k j / ((k j).factorial : ℝ))) *
        (m none ^ r / (r.factorial : ℝ)) := by
    intro r
    simp only [hF, if_pos (Nat.le_add_left sk r), Nat.add_sub_cancel, pw]
    have hfac : ((r + sk).factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
    have hrf : (r.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
    have hkf : ∀ j, ((k j).factorial : ℝ) ≠ 0 := fun j => by exact_mod_cast Nat.factorial_ne_zero _
    have hΛ0 : Λ ≠ 0 := hΛpos.ne'
    have hkp : ∏ j, ((k j).factorial : ℝ) ≠ 0 := Finset.prod_ne_zero_iff.2 fun j _ => hkf j
    have e1 : ∏ j, (m (some j) / Λ) ^ k j = (∏ j, m (some j) ^ k j) / Λ ^ sk := by
      simp_rw [div_pow]; rw [Finset.prod_div_distrib, Finset.prod_pow_eq_pow_sum, ← hsk]
    have e2 : ∏ j, (m (some j) ^ k j / ((k j).factorial : ℝ)) =
        (∏ j, m (some j) ^ k j) / ∏ j, ((k j).factorial : ℝ) := Finset.prod_div_distrib ..
    rw [e1, e2, div_pow, pow_add]
    field_simp
  have hsumr : HasSum (fun r => pw Λ (r + sk) * F (r + sk))
      ((Real.exp (-Λ) * ∏ j, (m (some j) ^ k j / ((k j).factorial : ℝ))) * Real.exp (m none)) := by
    simp_rw [hterm]
    exact (hasSum_pow_div_factorial _).mul_left _
  have hlow : ∑ i ∈ range sk, pw Λ i * F i = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    simp only [hF, if_neg (by simpa using hi : ¬ sk ≤ i), mul_zero]
  have hsum : HasSum (fun n => pw Λ n * F n) P := by
    have := (hasSum_nat_add_iff (f := fun n => pw Λ n * F n) sk).1 hsumr
    rw [hlow, add_zero] at this
    convert this using 1
    rw [hP]
    have e3 : ∀ j, pw (m (some j)) (k j) =
        Real.exp (-m (some j)) * (m (some j) ^ k j / ((k j).factorial : ℝ)) := by
      intro j; simp only [pw]; ring
    rw [Finset.prod_congr rfl (fun j _ => e3 j), Finset.prod_mul_distrib, ← Real.exp_sum,
      show (∑ j, -m (some j)) = -Λ + m none by rw [hΛsum, Finset.sum_neg_distrib]; ring,
      Real.exp_add]
    ring
  -- back to `ℝ≥0∞`
  have hrw : ∀ n, ENNReal.ofReal (pw Λ n) * ENNReal.ofReal (F n) = ENNReal.ofReal (pw Λ n * F n) :=
    fun n => (ENNReal.ofReal_mul (pw_nonneg hΛpos.le n)).symm
  show ∑' n, ENNReal.ofReal (pw Λ n) * ENNReal.ofReal (F n) = _
  simp_rw [hrw]
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun n => mul_nonneg (pw_nonneg hΛpos.le n) (hF0 n))
    hsum.summable, hsum.tsum_eq, hP, ENNReal.ofReal_prod_of_nonneg
    (fun j _ => pw_nonneg ENNReal.toReal_nonneg _)]
  rfl

end Joint

/-! ### Consequences: probability measure, measurability, marginals, independence -/

theorem measurable_config_iff {β : Type*} [MeasurableSpace β] {f : Config S → β} :
    Measurable f ↔ ∀ n, Measurable (f ∘ cfg n) := by
  refine ⟨fun hf n => hf.comp (measurable_mk n), fun h => ?_⟩
  intro s hs
  rw [measurableSet_config]
  intro n
  exact h n hs

theorem measurable_count {B : Set S} (hB : MeasurableSet B) : Measurable (count B) := by
  classical
  rw [measurable_config_iff]
  intro n
  have : (count B ∘ cfg n : (Fin n → S) → ℕ) =
      fun x => ∑ i, if x i ∈ B then 1 else 0 := by
    ext x
    simp only [Function.comp_apply, count, cfg]
    rw [Finset.card_filter]
  rw [this]
  refine Finset.measurable_sum _ fun i _ => ?_
  exact Measurable.ite (measurableSet_preimage (measurable_pi_apply i) hB) measurable_const
    measurable_const

theorem isProbabilityMeasure_poissonProcess (ν : Measure S) [IsFiniteMeasure ν]
    (hν : ν Set.univ ≠ 0) : IsProbabilityMeasure (poissonProcess ν) := by
  constructor
  have h := poissonProcess_counts ν hν (ι := Empty) (B := fun _ => ∅) (fun _ => MeasurableSet.empty)
    (fun a => a.elim) (fun _ => 0)
  have e : {ω : Config S | ∀ j : Empty, count ((fun _ => (∅ : Set S)) j) ω = (fun _ => 0) j} =
      Set.univ := Set.eq_univ_of_forall fun ω j => j.elim
  rw [e, Finset.univ_eq_empty, Finset.prod_empty] at h
  exact h

/-- **Poisson marginals.**  The count in a measurable set `B` is Poisson with mean `ν(B)`. -/
theorem poissonProcess_count_eq (ν : Measure S) [IsFiniteMeasure ν] (hν : ν Set.univ ≠ 0)
    {B : Set S} (hB : MeasurableSet B) (k : ℕ) :
    poissonProcess ν {ω | count B ω = k} = ENNReal.ofReal (pw (ν B).toReal k) := by
  have h := poissonProcess_counts ν hν (ι := Unit) (B := fun _ => B) (fun _ => hB)
    (fun a b hab => absurd (Subsingleton.elim a b) hab) (fun _ => k)
  simpa using h

theorem hasLaw_count (ν : Measure S) [IsFiniteMeasure ν] (hν : ν Set.univ ≠ 0)
    {B : Set S} (hB : MeasurableSet B) :
    HasLaw (count B) (poissonMeasure (ν B).toNNReal) (poissonProcess ν) where
  aemeasurable := (measurable_count hB).aemeasurable
  map_eq := by
    apply Measure.ext_of_singleton
    intro k
    rw [Measure.map_apply (measurable_count hB) (measurableSet_singleton k), poissonMeasure_singleton]
    rw [show count B ⁻¹' {k} = {ω | count B ω = k} from rfl, poissonProcess_count_eq ν hν hB k]
    simp [pw, ENNReal.coe_toNNReal_eq_toReal]

/-- **Independence of counts on disjoint sets.** -/
theorem iIndepFun_count (ν : Measure S) [IsFiniteMeasure ν] (hν : ν Set.univ ≠ 0)
    {ι : Type*} [Fintype ι] {B : ι → Set S} (hB : ∀ j, MeasurableSet (B j))
    (hd : Pairwise (Disjoint on B)) :
    iIndepFun (fun j => count (B j)) (poissonProcess ν) := by
  haveI := isProbabilityMeasure_poissonProcess ν hν
  rw [iIndepFun_iff_map_fun_eq_pi_map (fun j => (measurable_count (hB j)).aemeasurable)]
  have hm : Measurable fun ω (j : ι) => count (B j) ω :=
    measurable_pi_iff.2 fun j => measurable_count (hB j)
  apply Measure.ext_of_singleton
  intro k
  rw [Measure.map_apply hm (measurableSet_singleton k), ← Set.univ_pi_singleton, Measure.pi_pi]
  have : (fun ω (j : ι) => count (B j) ω) ⁻¹' Set.univ.pi (fun j => {k j}) =
      {ω | ∀ j, count (B j) ω = k j} := by
    ext ω; simp
  rw [this, poissonProcess_counts ν hν hB hd]
  refine Finset.prod_congr rfl fun j _ => ?_
  rw [Measure.map_apply (measurable_count (hB j)) (measurableSet_singleton _)]
  exact (poissonProcess_count_eq ν hν (hB j) (k j)).symm

/-! ### The mapping theorem -/

variable {S' : Type*} [MeasurableSpace S']

/-- The image of a configuration under a map `T`. -/
def mapConfig (T : S → S') (ω : Config S) : Config S' := ⟨ω.1, fun i => T (ω.2 i)⟩

theorem count_mapConfig (T : S → S') (B : Set S') (ω : Config S) :
    count B (mapConfig T ω) = count (T ⁻¹' B) ω := rfl

theorem measurable_mapConfig {T : S → S'} (hT : Measurable T) : Measurable (mapConfig T) := by
  rw [measurable_config_iff]
  intro n
  have : (mapConfig T ∘ cfg n : (Fin n → S) → Config S') = cfg n ∘ fun x i => T (x i) := rfl
  rw [this]
  exact (measurable_mk n).comp (measurable_pi_iff.2 fun i => hT.comp (measurable_pi_apply i))

/-- **The mapping theorem.**  The image of the Poisson process with intensity `ν` under a
measurable map `T` is the Poisson process with the image intensity `T_* ν`. -/
theorem poissonProcess_map (ν : Measure S) [IsFiniteMeasure ν] (hν : ν Set.univ ≠ 0)
    {T : S → S'} (hT : Measurable T) :
    (poissonProcess ν).map (mapConfig T) = poissonProcess (ν.map T) := by
  haveI := isProbabilityMeasure_unif ν hν
  have huniv : (ν.map T) Set.univ = ν Set.univ := by
    rw [Measure.map_apply hT MeasurableSet.univ, Set.preimage_univ]
  rw [poissonProcess, Measure.map_sum (measurable_mapConfig hT).aemeasurable, poissonProcess]
  congr 1; ext1 n
  rw [Measure.map_smul, Measure.map_map (measurable_mapConfig hT) (measurable_mk n), huniv]
  congr 1
  have : (mapConfig T ∘ cfg n : (Fin n → S) → Config S') = cfg n ∘ fun x i => T (x i) := rfl
  have hmT : Measurable fun (x : Fin n → S) (i : Fin n) => T (x i) :=
    measurable_pi_iff.2 fun i => hT.comp (measurable_pi_apply i)
  rw [this, ← Measure.map_map (measurable_mk n) hmT]
  congr 1
  rw [Measure.pi_map_pi (fun _ => hT.aemeasurable)]
  · congr 1; ext1 i
    rw [unif, unif, Measure.map_smul, huniv]
    exact hT.aemeasurable
  · exact (measurable_mapConfig hT).aemeasurable

/-- The mapping theorem for measure-preserving maps: if `T` carries `ν` to `ν'`, it carries the
Poisson process of intensity `ν` to that of intensity `ν'`. -/
theorem measurePreserving_mapConfig (ν : Measure S) [IsFiniteMeasure ν] (hν : ν Set.univ ≠ 0)
    (ν' : Measure S') {T : S → S'} (hT : MeasurePreserving T ν ν') :
    MeasurePreserving (mapConfig T) (poissonProcess ν) (poissonProcess ν') :=
  ⟨measurable_mapConfig hT.measurable, by rw [poissonProcess_map ν hν hT.measurable, hT.map_eq]⟩

/-! ### Moments of the Poisson law -/

theorem hasSum_pw (r : ℝ) : HasSum (pw r) 1 := by
  have h := (hasSum_pow_div_factorial r).mul_left (Real.exp (-r))
  rw [← Real.exp_add, neg_add_cancel, Real.exp_zero] at h
  convert h using 1; ext n; simp only [pw]; ring

theorem pw_succ (r : ℝ) (n : ℕ) : pw r (n + 1) = r / (n + 1) * pw r n := by
  simp only [pw, Nat.factorial_succ, pow_succ]; push_cast
  have : (n.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
  field_simp

theorem hasSum_mul_pw (r : ℝ) : HasSum (fun n : ℕ => (n : ℝ) * pw r n) r := by
  rw [← hasSum_nat_add_iff' 1]
  simp only [Finset.range_one, Finset.sum_singleton, Nat.cast_zero, zero_mul, sub_zero]
  have : (fun n : ℕ => ((n + 1 : ℕ) : ℝ) * pw r (n + 1)) = fun n => r * pw r n := by
    ext n; rw [pw_succ]; push_cast; field_simp
  rw [this]; simpa using (hasSum_pw r).mul_left r

theorem hasSum_mul_pred_pw (r : ℝ) :
    HasSum (fun n : ℕ => (n : ℝ) * ((n : ℝ) - 1) * pw r n) (r ^ 2) := by
  rw [← hasSum_nat_add_iff' 2]
  simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, Nat.cast_zero,
    zero_mul, Nat.cast_one, sub_self, mul_zero, zero_add, add_zero, sub_zero]
  have : (fun n : ℕ => ((n + 2 : ℕ) : ℝ) * (((n + 2 : ℕ) : ℝ) - 1) * pw r (n + 2)) =
      fun n => r ^ 2 * pw r n := by
    ext n; rw [pw_succ, pw_succ]; push_cast; field_simp; ring
  rw [this]; simpa using (hasSum_pw r).mul_left (r ^ 2)

theorem hasSum_sq_pw (r : ℝ) : HasSum (fun n : ℕ => (n : ℝ) ^ 2 * pw r n) (r ^ 2 + r) := by
  convert (hasSum_mul_pred_pw r).add (hasSum_mul_pw r) using 1
  ext n; ring

theorem hasSum_sub_sq_pw (r : ℝ) : HasSum (fun n : ℕ => ((n : ℝ) - r) ^ 2 * pw r n) r := by
  have h := ((hasSum_sq_pw r).sub ((hasSum_mul_pw r).mul_left (2 * r))).add
    ((hasSum_pw r).mul_left (r ^ 2))
  convert h using 1
  · ext n; ring
  · ring

/-! ### Moments of a Poisson random variable -/

section PoissonRV

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X : Ω → ℕ} {r : ℝ≥0}

theorem hasLaw_of_pw (hX : Measurable X) (h : ∀ k, P {ω | X ω = k} = ENNReal.ofReal (pw r k)) :
    HasLaw X (poissonMeasure r) P where
  aemeasurable := hX.aemeasurable
  map_eq := by
    apply Measure.ext_of_singleton
    intro k
    rw [Measure.map_apply hX (measurableSet_singleton k), poissonMeasure_singleton]
    exact h k

theorem integral_comp_of_hasLaw (hX : HasLaw X (poissonMeasure r) P) (f : ℕ → ℝ) :
    ∫ ω, f (X ω) ∂P = ∑' n, pw r n * f n := by
  rw [← integral_map hX.aemeasurable .of_discrete, hX.map_eq, integral_poissonMeasure]
  simp [pw]

theorem integral_of_hasLaw (hX : HasLaw X (poissonMeasure r) P) :
    ∫ ω, (X ω : ℝ) ∂P = r := by
  rw [integral_comp_of_hasLaw hX (fun n => (n : ℝ))]
  simp_rw [mul_comm (pw _ _)]
  exact (hasSum_mul_pw _).tsum_eq

theorem memLp_of_hasLaw (hX : HasLaw X (poissonMeasure r) P) :
    MemLp (fun ω => (X ω : ℝ)) 2 P := by
  have hm : AEMeasurable (fun ω => (X ω : ℝ)) P := measurable_from_nat.comp_aemeasurable hX.aemeasurable
  rw [memLp_two_iff_integrable_sq hm.aestronglyMeasurable]
  have : (fun ω => (X ω : ℝ) ^ 2) = (fun n : ℕ => (n : ℝ) ^ 2) ∘ X := rfl
  rw [this, ← integrable_map_measure .of_discrete hX.aemeasurable, hX.map_eq,
    integrable_poissonMeasure_iff]
  refine (hasSum_sq_pw (r : ℝ)).summable.congr fun n => ?_
  simp [pw, mul_comm]

theorem variance_of_hasLaw (hX : HasLaw X (poissonMeasure r) P) :
    variance (fun ω => (X ω : ℝ)) P = r := by
  have hm : AEMeasurable (fun ω => (X ω : ℝ)) P := measurable_from_nat.comp_aemeasurable hX.aemeasurable
  rw [variance_eq_integral hm, integral_of_hasLaw hX,
    integral_comp_of_hasLaw hX (fun n => ((n : ℝ) - r) ^ 2)]
  simp_rw [mul_comm (pw _ _)]
  exact (hasSum_sub_sq_pw _).tsum_eq

theorem chebyshev_of_hasLaw [IsProbabilityMeasure P] (hX : HasLaw X (poissonMeasure r) P)
    {c : ℝ} (hc : 0 < c) :
    P {ω | c ≤ |(X ω : ℝ) - r|} ≤ ENNReal.ofReal (r / c ^ 2) := by
  have h := meas_ge_le_variance_div_sq (memLp_of_hasLaw hX) hc
  rwa [integral_of_hasLaw hX, variance_of_hasLaw hX] at h

/-! ### Chernoff bounds for a Poisson random variable -/

theorem exp_le_quad {θ : ℝ} (hθ : |θ| ≤ 1) : Real.exp θ ≤ 1 + θ + θ ^ 2 := by
  have h := Real.exp_bound hθ (n := 2) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, pow_zero, Nat.factorial_zero,
    Nat.cast_one, div_one, zero_add, pow_one, Nat.factorial_one] at h
  have h2 := (abs_le.1 h).2
  have : |θ| ^ 2 = θ ^ 2 := sq_abs θ
  rw [this] at h2
  norm_num at h2
  nlinarith [sq_nonneg θ]

theorem hasSum_pw_exp (r θ : ℝ) :
    HasSum (fun n : ℕ => pw r n * Real.exp (θ * n)) (Real.exp (r * (Real.exp θ - 1))) := by
  have h := (hasSum_pow_div_factorial (r * Real.exp θ)).mul_left (Real.exp (-r))
  convert h using 1
  · ext n
    simp only [pw]
    rw [mul_pow, ← Real.exp_nat_mul]
    ring_nf
  · rw [← Real.exp_add]; ring_nf

theorem poissonMeasure_le_tsum (r : ℝ≥0) (S : Set ℕ) (f : ℕ → ℝ) (hf0 : ∀ n, 0 ≤ f n)
    (hf : ∀ n ∈ S, 1 ≤ f n) (hs : Summable fun n => pw r n * f n) :
    poissonMeasure r S ≤ ENNReal.ofReal (∑' n, pw r n * f n) := by
  rw [poissonMeasure, Measure.sum_apply_of_countable]
  refine le_trans ?_ (le_of_eq (ENNReal.ofReal_tsum_of_nonneg
    (fun n => mul_nonneg (pw_nonneg r.2 n) (hf0 n)) hs).symm)
  refine ENNReal.tsum_le_tsum fun n => ?_
  rw [Measure.smul_apply, smul_eq_mul, Measure.dirac_apply]
  by_cases hn : n ∈ S
  · rw [Set.indicator_of_mem hn, Pi.one_apply, mul_one]
    exact ENNReal.ofReal_le_ofReal (le_mul_of_one_le_right (pw_nonneg r.2 n) (hf n hn))
  · rw [Set.indicator_of_notMem hn, mul_zero]; exact zero_le

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X : Ω → ℕ} {r : ℝ≥0}

/-- **Upper Chernoff bound**: `P(X ≥ r + x) ≤ exp(-x²/(4(r+x)))` for `X ~ Poisson(r)`. -/
theorem poisson_upper_tail (hX : HasLaw X (poissonMeasure r) P) {x : ℝ} (hx : 0 < x) :
    P {ω | (r : ℝ) + x ≤ X ω} ≤ ENNReal.ofReal (Real.exp (-x ^ 2 / (4 * (r + x)))) := by
  have hr := r.2
  set θ := x / (2 * (r + x)) with hθ
  have hθ0 : 0 ≤ θ := by positivity
  have hθ1 : θ ≤ 1 / 2 := by rw [hθ, div_le_iff₀ (by positivity)]; nlinarith
  have hmeas : MeasurableSet {n : ℕ | (r : ℝ) + x ≤ n} := (Set.to_countable _).measurableSet
  rw [show {ω | (r : ℝ) + x ≤ X ω} = X ⁻¹' {n : ℕ | (r : ℝ) + x ≤ n} from rfl,
    ← Measure.map_apply_of_aemeasurable hX.aemeasurable hmeas, hX.map_eq]
  have hsum := (hasSum_pw_exp r θ).mul_right (Real.exp (-θ * (r + x)))
  refine (poissonMeasure_le_tsum r _ (fun n => Real.exp (θ * n) * Real.exp (-θ * (r + x)))
    (fun n => by positivity) (fun n hn => ?_) ?_).trans ?_
  · rw [← Real.exp_add, Real.one_le_exp_iff]
    simp only [Set.mem_setOf_eq] at hn
    nlinarith
  · exact hsum.summable.congr fun n => by ring
  · rw [show (∑' n, pw r n * (Real.exp (θ * n) * Real.exp (-θ * (r + x)))) =
        ∑' n, pw r n * Real.exp (θ * n) * Real.exp (-θ * (r + x)) from tsum_congr fun n => by ring,
      hsum.tsum_eq, ← Real.exp_add]
    refine ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 ?_)
    have hq := exp_le_quad (θ := θ) (by rw [abs_of_nonneg hθ0]; linarith)
    have h1 : (r : ℝ) * (Real.exp θ - 1) ≤ r * (θ + θ ^ 2) :=
      mul_le_mul_of_nonneg_left (by linarith) hr
    have h2 : (r : ℝ) * θ ≤ x / 2 := by
      rw [hθ, mul_div_assoc', div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith
    have h3 : θ * x / 2 = x ^ 2 / (4 * (r + x)) := by
      rw [hθ]; field_simp; ring
    have h4 : (r : ℝ) * θ ^ 2 ≤ θ * (x / 2) := by
      have := mul_le_mul_of_nonneg_left h2 hθ0; nlinarith
    calc (r : ℝ) * (Real.exp θ - 1) + -θ * (r + x) ≤ r * (θ + θ ^ 2) + -θ * (r + x) := by linarith
      _ = r * θ ^ 2 - θ * x := by ring
      _ ≤ θ * (x / 2) - θ * x := by linarith
      _ = -(θ * x / 2) := by ring
      _ = -x ^ 2 / (4 * (r + x)) := by rw [h3]; ring

/-- **Lower Chernoff bound**: `P(X ≤ r - x) ≤ exp(-x²/(4(r+x)))` for `X ~ Poisson(r)`. -/
theorem poisson_lower_tail (hX : HasLaw X (poissonMeasure r) P) {x : ℝ} (hx : 0 < x) :
    P {ω | (X ω : ℝ) ≤ r - x} ≤ ENNReal.ofReal (Real.exp (-x ^ 2 / (4 * (r + x)))) := by
  have hr := r.2
  set θ := x / (2 * (r + x)) with hθ
  have hθ0 : 0 ≤ θ := by positivity
  have hθ1 : θ ≤ 1 / 2 := by rw [hθ, div_le_iff₀ (by positivity)]; nlinarith
  have hmeas : MeasurableSet {n : ℕ | (n : ℝ) ≤ r - x} := (Set.to_countable _).measurableSet
  rw [show {ω | (X ω : ℝ) ≤ r - x} = X ⁻¹' {n : ℕ | (n : ℝ) ≤ r - x} from rfl,
    ← Measure.map_apply_of_aemeasurable hX.aemeasurable hmeas, hX.map_eq]
  have hsum := (hasSum_pw_exp r (-θ)).mul_right (Real.exp (θ * (r - x)))
  refine (poissonMeasure_le_tsum r _ (fun n => Real.exp (-θ * n) * Real.exp (θ * (r - x)))
    (fun n => by positivity) (fun n hn => ?_) ?_).trans ?_
  · rw [← Real.exp_add, Real.one_le_exp_iff]
    simp only [Set.mem_setOf_eq] at hn
    nlinarith
  · exact hsum.summable.congr fun n => by ring
  · rw [show (∑' n, pw r n * (Real.exp (-θ * n) * Real.exp (θ * (r - x)))) =
        ∑' n, pw r n * Real.exp (-θ * n) * Real.exp (θ * (r - x)) from tsum_congr fun n => by ring,
      hsum.tsum_eq, ← Real.exp_add]
    refine ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 ?_)
    have hq := exp_le_quad (θ := -θ) (by rw [abs_neg, abs_of_nonneg hθ0]; linarith)
    have h1 : (r : ℝ) * (Real.exp (-θ) - 1) ≤ r * (-θ + θ ^ 2) :=
      mul_le_mul_of_nonneg_left (by nlinarith) hr
    have h2 : (r : ℝ) * θ ≤ x / 2 := by
      rw [hθ, mul_div_assoc', div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith
    have h3 : θ * x / 2 = x ^ 2 / (4 * (r + x)) := by
      rw [hθ]; field_simp; ring
    have h4 : (r : ℝ) * θ ^ 2 ≤ θ * (x / 2) := by
      have := mul_le_mul_of_nonneg_left h2 hθ0; nlinarith
    calc (r : ℝ) * (Real.exp (-θ) - 1) + θ * (r - x) ≤ r * (-θ + θ ^ 2) + θ * (r - x) := by
          linarith
      _ = r * θ ^ 2 - θ * x := by ring
      _ ≤ θ * (x / 2) - θ * x := by linarith
      _ = -(θ * x / 2) := by ring
      _ = -x ^ 2 / (4 * (r + x)) := by rw [h3]; ring

end PoissonRV

/-! ### Moments of the counts of the window process -/

/-- **Mean of the count**: `E N(B) = ν(B)`. -/
theorem integral_count (ν : Measure S) [IsFiniteMeasure ν] (hν : ν Set.univ ≠ 0)
    {B : Set S} (hB : MeasurableSet B) :
    ∫ ω, (count B ω : ℝ) ∂(poissonProcess ν) = (ν B).toReal := by
  rw [integral_of_hasLaw (hasLaw_count ν hν hB), ENNReal.coe_toNNReal_eq_toReal]

/-- **Variance of the count**: `Var N(B) = ν(B)`. -/
theorem variance_count (ν : Measure S) [IsFiniteMeasure ν] (hν : ν Set.univ ≠ 0)
    {B : Set S} (hB : MeasurableSet B) :
    variance (fun ω => (count B ω : ℝ)) (poissonProcess ν) = (ν B).toReal := by
  rw [variance_of_hasLaw (hasLaw_count ν hν hB), ENNReal.coe_toNNReal_eq_toReal]

/-! ## The Poisson convolution identity -/

theorem sum_piAntidiag_pw {Z : Type*} [DecidableEq Z] (F : Finset Z) (m : Z → ℝ) (K : ℕ) :
    ∑ y ∈ F.piAntidiag K, ∏ z ∈ F, pw (m z) (y z) = pw (∑ z ∈ F, m z) K := by
  have hmul := Finset.sum_pow_eq_sum_piAntidiag F m K
  have hterm : ∀ y ∈ F.piAntidiag K, ∏ z ∈ F, pw (m z) (y z) =
      Real.exp (-∑ z ∈ F, m z) / K.factorial *
        ((Nat.multinomial F y : ℝ) * ∏ z ∈ F, m z ^ y z) := by
    intro y hy
    rw [Finset.mem_piAntidiag] at hy
    have hspec := Nat.multinomial_spec F y
    rw [hy.1] at hspec
    have hspecR : (∏ z ∈ F, ((y z).factorial : ℝ)) * (Nat.multinomial F y : ℝ) =
        (K.factorial : ℝ) := by exact_mod_cast hspec
    have hK : (K.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero K
    have hP : (∏ z ∈ F, ((y z).factorial : ℝ)) ≠ 0 :=
      Finset.prod_ne_zero_iff.2 fun z _ => by exact_mod_cast Nat.factorial_ne_zero _
    simp only [pw]
    rw [Finset.prod_div_distrib, Finset.prod_mul_distrib, ← Real.exp_sum, Finset.sum_neg_distrib]
    have hM : (Nat.multinomial F y : ℝ) ≠ 0 := by exact_mod_cast (Nat.multinomial_pos F y).ne'
    rw [← hspecR]
    field_simp
  rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum, ← hmul, pw]
  ring

/-! ## The Poisson process with σ-finite intensity -/

section Global

variable {Z : Type*} [Countable Z]

/-- A tiling of `S` by countably many measurable tiles of finite positive `μ`-measure. -/
structure IsTiling (μ : Measure S) (Q : Z → Set S) : Prop where
  measurableSet : ∀ z, MeasurableSet (Q z)
  disjoint : Pairwise (Disjoint on Q)
  iUnion_eq : ⋃ z, Q z = Set.univ
  ne_top : ∀ z, μ (Q z) ≠ ⊤
  ne_zero : ∀ z, μ (Q z) ≠ 0

/-- A set is tile-bounded if it meets only finitely many tiles. -/
def TileBounded (Q : Z → Set S) (B : Set S) : Prop := {z | (B ∩ Q z).Nonempty}.Finite

open Classical in
/-- The Poisson process of a window, made a probability measure in all cases. -/
def safeProc (ν : Measure S) : Measure (Config S) :=
  if IsProbabilityMeasure (poissonProcess ν) then poissonProcess ν
  else Measure.dirac (cfg 0 Fin.elim0)

instance (ν : Measure S) : IsProbabilityMeasure (safeProc ν) := by
  unfold safeProc; split_ifs with h
  · exact h
  · infer_instance

theorem isFiniteMeasure_tile {μ : Measure S} {Q : Z → Set S} (h : IsTiling μ Q) (z : Z) :
    IsFiniteMeasure (μ.restrict (Q z)) := isFiniteMeasure_restrict.2 (h.ne_top z)

theorem restrict_tile_univ_ne_zero {μ : Measure S} {Q : Z → Set S} (h : IsTiling μ Q) (z : Z) :
    μ.restrict (Q z) Set.univ ≠ 0 := by
  rw [Measure.restrict_apply_univ]; exact h.ne_zero z

theorem safeProc_tile {μ : Measure S} {Q : Z → Set S} (h : IsTiling μ Q) (z : Z) :
    safeProc (μ.restrict (Q z)) = poissonProcess (μ.restrict (Q z)) := by
  haveI := isFiniteMeasure_tile h z
  have := isProbabilityMeasure_poissonProcess _ (restrict_tile_univ_ne_zero h z)
  unfold safeProc; rw [if_pos this]

/-- **The Poisson process with intensity `μ`**, on the space of tile-indexed families of window
configurations: independent Poisson processes on the tiles. -/
def globalProcess (μ : Measure S) (Q : Z → Set S) : Measure (Z → Config S) :=
  Measure.infinitePi fun z => safeProc (μ.restrict (Q z))

instance (μ : Measure S) (Q : Z → Set S) : IsProbabilityMeasure (globalProcess μ Q) := by
  unfold globalProcess; infer_instance

/-- The counting measure of a configuration. -/
def configMeasure (c : Config S) : Measure S := Measure.sum fun i : Fin c.1 => Measure.dirac (c.2 i)

theorem configMeasure_apply (c : Config S) {B : Set S} (hB : MeasurableSet B) :
    configMeasure c B = (count B c : ℝ≥0∞) := by
  classical
  rw [configMeasure, Measure.sum_apply _ hB, tsum_fintype]
  simp_rw [Measure.dirac_apply' _ hB, Set.indicator_apply]
  rw [count, Finset.card_filter]; push_cast
  simp

/-- **The random counting measure** of the global process: the points of the window
configuration of each tile that lie in that tile. -/
def randomMeasure (Q : Z → Set S) (ω : Z → Config S) : Measure S :=
  Measure.sum fun z => (configMeasure (ω z)).restrict (Q z)

theorem randomMeasure_apply {Q : Z → Set S} (hQ : ∀ z, MeasurableSet (Q z)) (ω : Z → Config S)
    {B : Set S} (hB : MeasurableSet B) :
    randomMeasure Q ω B = ∑' z, (count (B ∩ Q z) (ω z) : ℝ≥0∞) := by
  rw [randomMeasure, Measure.sum_apply _ hB]
  congr 1; ext z
  rw [Measure.restrict_apply hB, configMeasure_apply _ (hB.inter (hQ z))]

theorem measurable_randomMeasure {Q : Z → Set S} (hQ : ∀ z, MeasurableSet (Q z)) :
    Measurable (randomMeasure Q) := by
  refine Measure.measurable_of_measurable_coe _ fun B hB => ?_
  simp_rw [randomMeasure_apply hQ _ hB]
  refine Measurable.ennreal_tsum fun z => ?_
  exact measurable_from_nat.comp ((measurable_count (hB.inter (hQ z))).comp (measurable_pi_apply z))

/-- On a tile-bounded set the random measure is a finite sum of window counts. -/
theorem randomMeasure_eq_sum {Q : Z → Set S} (hQ : ∀ z, MeasurableSet (Q z)) (ω : Z → Config S)
    {B : Set S} (hB : MeasurableSet B) (F : Finset Z) (hF : ∀ z, (B ∩ Q z).Nonempty → z ∈ F) :
    randomMeasure Q ω B = ((∑ z ∈ F, count (B ∩ Q z) (ω z) : ℕ) : ℝ≥0∞) := by
  classical
  rw [randomMeasure_apply hQ ω hB, tsum_eq_sum (s := F)]
  · push_cast; rfl
  · intro z hz
    have : B ∩ Q z = ∅ := by
      by_contra hne; exact hz (hF z (Set.nonempty_iff_ne_empty.2 hne))
    simp [this, count]

theorem measurableSet_counts_eq {ι : Type*} [Fintype ι] {B : ι → Set S}
    (hB : ∀ j, MeasurableSet (B j)) (k : ι → ℕ) :
    MeasurableSet {c : Config S | ∀ j, count (B j) c = k j} := by
  have : {c : Config S | ∀ j, count (B j) c = k j} = ⋂ j, count (B j) ⁻¹' {k j} := by
    ext c; simp
  rw [this]
  exact MeasurableSet.iInter fun j => measurable_count (hB j) (measurableSet_singleton _)

/-- **Joint law of the counts of the Poisson process with σ-finite intensity**: for pairwise
disjoint measurable tile-bounded sets `B j`, the counts are independent and Poisson with means
`μ(B j)`. -/
theorem globalProcess_counts {μ : Measure S} {Q : Z → Set S} (h : IsTiling μ Q)
    {ι : Type*} [Fintype ι] {B : ι → Set S} (hB : ∀ j, MeasurableSet (B j))
    (hd : Pairwise (Disjoint on B)) (htb : ∀ j, TileBounded Q (B j)) (k : ι → ℕ) :
    globalProcess μ Q {ω | ∀ j, randomMeasure Q ω (B j) = k j} =
      ∏ j, ENNReal.ofReal (pw (μ (B j)).toReal (k j)) := by
  classical
  set F : Finset Z := Finset.univ.biUnion fun j => (htb j).toFinset with hFdef
  have hF : ∀ j z, (B j ∩ Q z).Nonempty → z ∈ F := by
    intro j z hz
    rw [hFdef, Finset.mem_biUnion]
    exact ⟨j, Finset.mem_univ _, (Set.Finite.mem_toFinset _).2 hz⟩
  set X : ι → Z → Config S → ℕ := fun j z c => count (B j ∩ Q z) c with hX
  set T : ι → Finset (Z → ℕ) := fun j => F.piAntidiag (k j) with hT
  set A : (ι → Z → ℕ) → Set (Z → Config S) :=
    fun x => Set.pi (F : Set Z) (fun z => {c | ∀ j, X j z c = x j z}) with hA
  have hE : {ω : Z → Config S | ∀ j, randomMeasure Q ω (B j) = k j} =
      ⋃ x ∈ Fintype.piFinset T, A x := by
    ext ω
    simp only [Set.mem_setOf_eq, Set.mem_iUnion, exists_prop, Fintype.mem_piFinset, hT,
      Finset.mem_piAntidiag, hA, Set.mem_pi, Finset.mem_coe]
    simp_rw [randomMeasure_eq_sum h.measurableSet ω (hB _) F (hF _), Nat.cast_inj]
    constructor
    · intro hω
      refine ⟨fun j z => if z ∈ F then X j z (ω z) else 0, fun j => ⟨?_, ?_⟩, ?_⟩
      · rw [← hω j]
        exact Finset.sum_congr rfl fun z hz => by simp [hz, hX]
      · intro z hz; by_contra hzF; exact hz (by simp [hzF])
      · intro z hz j; simp [hz]
    · rintro ⟨x, hx, hωx⟩ j
      rw [← (hx j).1]
      exact Finset.sum_congr rfl fun z hz => hωx z hz j
  have hdisj : Set.PairwiseDisjoint (↑(Fintype.piFinset T) : Set (ι → Z → ℕ)) A := by
    intro x hx x' hx' hxx'
    simp only [Finset.mem_coe, Fintype.mem_piFinset, hT, Finset.mem_piAntidiag] at hx hx'
    refine Set.disjoint_left.2 fun ω h1 h2 => hxx' ?_
    ext j z
    by_cases hz : z ∈ F
    · simp only [hA, Set.mem_pi, Finset.mem_coe, Set.mem_setOf_eq] at h1 h2
      rw [← h1 z hz j, h2 z hz j]
    · have e1 : x j z = 0 := by by_contra hne; exact hz ((hx j).2 z hne)
      have e2 : x' j z = 0 := by by_contra hne; exact hz ((hx' j).2 z hne)
      rw [e1, e2]
  have hmeasA : ∀ x ∈ Fintype.piFinset T, MeasurableSet (A x) := by
    intro x _
    refine MeasurableSet.pi (Finset.countable_toSet F) fun z _ => ?_
    exact measurableSet_counts_eq (fun j => (hB j).inter (h.measurableSet z)) _
  rw [hE, measure_biUnion_finset hdisj hmeasA]
  -- each cylinder
  have hcyl : ∀ x ∈ Fintype.piFinset T, globalProcess μ Q (A x) =
      ENNReal.ofReal (∏ z ∈ F, ∏ j, pw (μ (B j ∩ Q z)).toReal (x j z)) := by
    intro x _
    rw [hA, globalProcess, Measure.infinitePi_pi]
    · rw [ENNReal.ofReal_prod_of_nonneg (fun z _ => Finset.prod_nonneg fun j _ =>
        pw_nonneg ENNReal.toReal_nonneg _)]
      refine Finset.prod_congr rfl fun z _ => ?_
      haveI := isFiniteMeasure_tile h z
      rw [safeProc_tile h z]
      have hd' : Pairwise (Disjoint on fun j => B j ∩ Q z) :=
        fun i j hij => (hd hij).mono Set.inter_subset_left Set.inter_subset_left
      rw [poissonProcess_counts _ (restrict_tile_univ_ne_zero h z)
        (fun j => (hB j).inter (h.measurableSet z)) hd',
        ENNReal.ofReal_prod_of_nonneg (fun j _ => pw_nonneg ENNReal.toReal_nonneg _)]
      refine Finset.prod_congr rfl fun j _ => ?_
      rw [Measure.restrict_apply ((hB j).inter (h.measurableSet z)), Set.inter_assoc,
        Set.inter_self]
    · intro z _
      exact measurableSet_counts_eq (fun j => (hB j).inter (h.measurableSet z)) _
  rw [Finset.sum_congr rfl hcyl, ← ENNReal.ofReal_sum_of_nonneg (fun x _ =>
    Finset.prod_nonneg fun z _ => Finset.prod_nonneg fun j _ => pw_nonneg ENNReal.toReal_nonneg _)]
  rw [← ENNReal.ofReal_prod_of_nonneg (fun j _ => pw_nonneg ENNReal.toReal_nonneg _)]
  congr 1
  simp_rw [Finset.prod_comm (s := F) (t := Finset.univ)]
  rw [← Finset.prod_univ_sum (t := T)
    (f := fun j (y : Z → ℕ) => ∏ z ∈ F, pw (μ (B j ∩ Q z)).toReal (y z))]
  refine Finset.prod_congr rfl fun j _ => ?_
  rw [hT, sum_piAntidiag_pw]
  congr 1
  -- `μ (B j) = ∑ z ∈ F, μ (B j ∩ Q z)`
  have hcover : B j = ⋃ z ∈ F, (B j ∩ Q z) := by
    ext s
    simp only [Set.mem_iUnion, Set.mem_inter_iff, exists_prop]
    constructor
    · intro hs
      have : s ∈ ⋃ z, Q z := by rw [h.iUnion_eq]; trivial
      obtain ⟨z, hz⟩ := Set.mem_iUnion.1 this
      exact ⟨z, hF j z ⟨s, hs, hz⟩, hs, hz⟩
    · rintro ⟨z, _, hs, _⟩; exact hs
  have hμ : μ (B j) = ∑ z ∈ F, μ (B j ∩ Q z) := by
    conv_lhs => rw [hcover]
    rw [measure_biUnion_finset]
    · intro z _ z' _ hzz'
      exact (h.disjoint hzz').mono Set.inter_subset_right Set.inter_subset_right
    · intro z _; exact (hB j).inter (h.measurableSet z)
  rw [hμ, ENNReal.toReal_sum]
  intro z _
  exact ne_top_of_le_ne_top (h.ne_top z) (measure_mono Set.inter_subset_right)

/-! ### Uniqueness of the law of a random counting measure -/

theorem tileBounded_of_subset {Q : Z → Set S} {A B : Set S} (hB : TileBounded Q B) (h : A ⊆ B) :
    TileBounded Q A :=
  hB.subset fun z hz => hz.mono (Set.inter_subset_inter_left _ h)

theorem tileBounded_iUnion {Q : Z → Set S} {ι : Type*} [Finite ι] {B : ι → Set S}
    (hB : ∀ j, TileBounded Q (B j)) : TileBounded Q (⋃ j, B j) := by
  have : {z | ((⋃ j, B j) ∩ Q z).Nonempty} = ⋃ j, {z | (B j ∩ Q z).Nonempty} := by
    ext z; simp [Set.iUnion_inter, Set.nonempty_iUnion]
  unfold TileBounded; rw [this]
  exact Set.finite_iUnion hB

theorem measure_eq_tsum_tile {Q : Z → Set S} (hQm : ∀ z, MeasurableSet (Q z))
    (hQd : Pairwise (Disjoint on Q)) (hQu : ⋃ z, Q z = Set.univ) (ν : Measure S) {B : Set S}
    (hB : MeasurableSet B) : ν B = ∑' z, ν (B ∩ Q z) := by
  rw [← measure_iUnion]
  · congr 1; rw [← Set.inter_iUnion, hQu, Set.inter_univ]
  · intro z z' hzz'; exact (hQd hzz').mono Set.inter_subset_right Set.inter_subset_right
  · intro z; exact hB.inter (hQm z)

/-- The π-system of finite-dimensional events of tile-bounded sets. -/
def fdSets (Q : Z → Set S) : Set (Set (Measure S)) :=
  {s | ∃ (m : ℕ) (B : Fin m → Set S) (A : Fin m → Set ℝ≥0∞),
    (∀ j, MeasurableSet (B j) ∧ TileBounded Q (B j) ∧ MeasurableSet (A j)) ∧
      s = {ν | ∀ j, ν (B j) ∈ A j}}

theorem isPiSystem_fdSets (Q : Z → Set S) : IsPiSystem (fdSets Q) := by
  rintro s ⟨m, B, A, hBA, rfl⟩ t ⟨m', B', A', hBA', rfl⟩ _
  refine ⟨m + m', Fin.append B B', Fin.append A A', fun j => ?_, ?_⟩
  · refine Fin.addCases (fun j => ?_) (fun j => ?_) j
    · simp only [Fin.append_left]; exact hBA j
    · simp only [Fin.append_right]; exact hBA' j
  · ext ν
    simp only [Set.mem_inter_iff, Set.mem_setOf_eq]
    rw [Fin.forall_fin_add]
    simp only [Fin.append_left, Fin.append_right]

theorem generateFrom_fdSets {Q : Z → Set S} (hQm : ∀ z, MeasurableSet (Q z))
    (hQd : Pairwise (Disjoint on Q)) (hQu : ⋃ z, Q z = Set.univ) :
    (Measure.instMeasurableSpace : MeasurableSpace (Measure S)) =
      MeasurableSpace.generateFrom (fdSets Q) := by
  apply le_antisymm
  · have hTB : ∀ z, TileBounded Q (Q z) := by
      intro z
      refine (Set.finite_singleton z).subset fun z' hz' => ?_
      obtain ⟨x, hx1, hx2⟩ := hz'
      by_contra hne
      exact Set.disjoint_left.1 (hQd (Ne.symm hne)) hx1 hx2
    have hev : ∀ B, MeasurableSet B →
        @Measurable (Measure S) ℝ≥0∞ (MeasurableSpace.generateFrom (fdSets Q)) _
          fun ν => ν B := by
      intro B hB
      have h1 : ∀ z, @Measurable (Measure S) ℝ≥0∞ (MeasurableSpace.generateFrom (fdSets Q)) _
          fun ν => ν (B ∩ Q z) := by
        intro z A hA
        apply MeasurableSpace.measurableSet_generateFrom
        refine ⟨1, fun _ => B ∩ Q z, fun _ => A, fun _ => ⟨hB.inter (hQm z),
          tileBounded_of_subset (hTB z) Set.inter_subset_right, hA⟩, ?_⟩
        ext ν; simp
      have h2 : (fun ν : Measure S => ν B) = fun ν => ∑' z, ν (B ∩ Q z) := by
        ext ν; exact measure_eq_tsum_tile hQm hQd hQu ν hB
      rw [h2]
      exact @Measurable.ennreal_tsum _ (MeasurableSpace.generateFrom (fdSets Q)) _ _ _ h1
    have hid := @Measure.measurable_of_measurable_coe S (Measure S) _
      (MeasurableSpace.generateFrom (fdSets Q)) id hev
    exact fun s hs => hid hs
  · refine MeasurableSpace.generateFrom_le ?_
    rintro s ⟨m, B, A, hBA, rfl⟩
    have : {ν : Measure S | ∀ j, ν (B j) ∈ A j} = ⋂ j, (fun ν : Measure S => ν (B j)) ⁻¹' A j := by
      ext ν; simp
    rw [this]
    exact MeasurableSet.iInter fun j => Measure.measurable_coe (hBA j).1 (hBA j).2.2

/-- The atoms of the partition generated by finitely many sets `B j`, inside their union. -/
def atom {m : ℕ} (B : Fin m → Set S) (σ : Fin m → Bool) : Set S :=
  (⋂ j, if σ j then B j else (B j)ᶜ) ∩ ⋃ j, B j

theorem measurableSet_atom {m : ℕ} {B : Fin m → Set S} (hB : ∀ j, MeasurableSet (B j))
    (σ : Fin m → Bool) : MeasurableSet (atom B σ) := by
  refine MeasurableSet.inter (MeasurableSet.iInter fun j => ?_) (MeasurableSet.iUnion hB)
  split_ifs
  · exact hB j
  · exact (hB j).compl

theorem tileBounded_atom {Q : Z → Set S} {m : ℕ} {B : Fin m → Set S}
    (hB : ∀ j, TileBounded Q (B j)) (σ : Fin m → Bool) : TileBounded Q (atom B σ) :=
  tileBounded_of_subset (tileBounded_iUnion hB) Set.inter_subset_right

theorem pairwise_disjoint_atom {m : ℕ} (B : Fin m → Set S) : Pairwise (Disjoint on atom B) := by
  intro σ σ' hσ
  obtain ⟨j, hj⟩ : ∃ j, σ j ≠ σ' j := by
    by_contra hc; push_neg at hc; exact hσ (funext hc)
  refine Set.disjoint_left.2 fun x hx hx' => ?_
  have h1 := Set.mem_iInter.1 hx.1 j
  have h2 := Set.mem_iInter.1 hx'.1 j
  cases h : σ j <;> cases h' : σ' j <;> simp_all

theorem measure_eq_sum_atom {m : ℕ} {B : Fin m → Set S} (hB : ∀ j, MeasurableSet (B j))
    (ν : Measure S) (j : Fin m) :
    ν (B j) = ∑ σ ∈ Finset.univ.filter (fun σ => σ j = true), ν (atom B σ) := by
  classical
  rw [← measure_biUnion_finset]
  · congr 1
    ext x
    simp only [Set.mem_iUnion, Finset.mem_filter, Finset.mem_univ, true_and, exists_prop, atom,
      Set.mem_inter_iff, Set.mem_iInter]
    constructor
    · intro hx
      refine ⟨fun i => decide (x ∈ B i), by simpa using hx, fun i => ?_, ⟨j, hx⟩⟩
      by_cases hi : x ∈ B i <;> simp [hi]
    · rintro ⟨σ, hσ, hx, _⟩
      have := hx j; rw [hσ] at this; simpa using this
  · intro σ _ σ' _ hσ; exact pairwise_disjoint_atom B hσ
  · intro σ _; exact measurableSet_atom hB σ

/-- The atom-count decomposition of a finite-dimensional event. -/
theorem measure_fd_eq_tsum {Q : Z → Set S} {m : ℕ} {B : Fin m → Set S} {A : Fin m → Set ℝ≥0∞}
    (hB : ∀ j, MeasurableSet (B j)) (htb : ∀ j, TileBounded Q (B j))
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (Y : Ω → Measure S) (hY : Measurable Y)
    (hN : ∀ B, MeasurableSet B → TileBounded Q B → ∀ ω, ∃ n : ℕ, Y ω B = n) :
    P (Y ⁻¹' {ν : Measure S | ∀ j, ν (B j) ∈ A j}) =
      ∑' κ : {κ : (Fin m → Bool) → ℕ //
          ∀ j, (∑ σ ∈ Finset.univ.filter (fun σ => σ j = true), (κ σ : ℝ≥0∞)) ∈ A j},
        P {ω | ∀ σ, Y ω (atom B σ) = κ.1 σ} := by
  classical
  have hev : Y ⁻¹' {ν : Measure S | ∀ j, ν (B j) ∈ A j} =
      ⋃ κ : {κ : (Fin m → Bool) → ℕ //
          ∀ j, (∑ σ ∈ Finset.univ.filter (fun σ => σ j = true), (κ σ : ℝ≥0∞)) ∈ A j},
        {ω | ∀ σ, Y ω (atom B σ) = κ.1 σ} := by
    ext ω
    simp only [Set.mem_preimage, Set.mem_setOf_eq, Set.mem_iUnion]
    constructor
    · intro hω
      have hn := fun σ => hN (atom B σ) (measurableSet_atom hB σ) (tileBounded_atom htb σ) ω
      refine ⟨⟨fun σ => (hn σ).choose, fun j => ?_⟩, fun σ => (hn σ).choose_spec⟩
      have := hω j
      rw [measure_eq_sum_atom hB] at this
      convert this using 2 with σ
      exact (hn σ).choose_spec.symm
    · rintro ⟨κ, hκ⟩ j
      rw [measure_eq_sum_atom hB]
      convert κ.2 j using 2 with σ
      exact hκ σ
  rw [hev, measure_iUnion]
  · intro κ κ' hκ
    refine Set.disjoint_left.2 fun ω h1 h2 => hκ (Subtype.ext (funext fun σ => ?_))
    have := (h1 σ).symm.trans (h2 σ)
    exact_mod_cast this
  · intro κ
    have : {ω | ∀ σ, Y ω (atom B σ) = κ.1 σ} =
        ⋂ σ, (fun ω => Y ω (atom B σ)) ⁻¹' {(κ.1 σ : ℝ≥0∞)} := by ext; simp
    rw [this]
    exact MeasurableSet.iInter fun σ =>
      (Measure.measurable_coe (measurableSet_atom hB σ)).comp hY (measurableSet_singleton _)

/-- **Uniqueness of the law of a random counting measure.**  Two random measures whose values
on tile-bounded sets are natural numbers, and whose counts on every finite family of pairwise
disjoint tile-bounded sets have the same joint law, have the same law. -/
theorem law_eq_of_counts {Q : Z → Set S} (hQm : ∀ z, MeasurableSet (Q z))
    (hQd : Pairwise (Disjoint on Q)) (hQu : ⋃ z, Q z = Set.univ)
    {Ω₁ Ω₂ : Type*} [MeasurableSpace Ω₁] [MeasurableSpace Ω₂] (P₁ : Measure Ω₁) (P₂ : Measure Ω₂)
    [IsProbabilityMeasure P₁] [IsProbabilityMeasure P₂]
    (X₁ : Ω₁ → Measure S) (X₂ : Ω₂ → Measure S) (hX₁ : Measurable X₁) (hX₂ : Measurable X₂)
    (hN₁ : ∀ B, MeasurableSet B → TileBounded Q B → ∀ ω, ∃ n : ℕ, X₁ ω B = n)
    (hN₂ : ∀ B, MeasurableSet B → TileBounded Q B → ∀ ω, ∃ n : ℕ, X₂ ω B = n)
    (hlaw : ∀ (ι : Type) [Fintype ι] (B : ι → Set S), (∀ j, MeasurableSet (B j)) →
      Pairwise (Disjoint on B) → (∀ j, TileBounded Q (B j)) → ∀ k : ι → ℕ,
        P₁ {ω | ∀ j, X₁ ω (B j) = k j} = P₂ {ω | ∀ j, X₂ ω (B j) = k j}) :
    P₁.map X₁ = P₂.map X₂ := by
  refine ext_of_generate_finite (fdSets Q) (generateFrom_fdSets hQm hQd hQu)
    (isPiSystem_fdSets Q) ?_ ?_
  · rintro s ⟨m, B, A, hBA, rfl⟩
    have hsm : MeasurableSet {ν : Measure S | ∀ j, ν (B j) ∈ A j} := by
      rw [generateFrom_fdSets hQm hQd hQu]
      exact MeasurableSpace.measurableSet_generateFrom ⟨m, B, A, hBA, rfl⟩
    rw [Measure.map_apply hX₁ hsm, Measure.map_apply hX₂ hsm,
      measure_fd_eq_tsum (fun j => (hBA j).1) (fun j => (hBA j).2.1) P₁ X₁ hX₁ hN₁,
      measure_fd_eq_tsum (fun j => (hBA j).1) (fun j => (hBA j).2.1) P₂ X₂ hX₂ hN₂]
    congr 1; ext κ
    exact hlaw (Fin m → Bool) (atom B) (fun σ => measurableSet_atom (fun j => (hBA j).1) σ)
      (pairwise_disjoint_atom B) (fun σ => tileBounded_atom (fun j => (hBA j).2.1) σ) κ.1
  · simp [Measure.map_apply hX₁ MeasurableSet.univ, Measure.map_apply hX₂ MeasurableSet.univ]

/-! ### Counts, marginals and invariance in law of the global process -/

open Classical in
/-- The number of points of the global process in a set `B` (when `B` is tile-bounded). -/
def gcount (Q : Z → Set S) (B : Set S) (ω : Z → Config S) : ℕ :=
  if h : TileBounded Q B then ∑ z ∈ h.toFinset, count (B ∩ Q z) (ω z) else 0

theorem randomMeasure_eq_gcount {μ : Measure S} {Q : Z → Set S} (h : IsTiling μ Q) {B : Set S}
    (hB : MeasurableSet B) (htb : TileBounded Q B) (ω : Z → Config S) :
    randomMeasure Q ω B = gcount Q B ω := by
  rw [randomMeasure_eq_sum h.measurableSet ω hB htb.toFinset
    (fun z hz => (Set.Finite.mem_toFinset _).2 hz), gcount, dif_pos htb]

theorem measurable_gcount {Q : Z → Set S} (hQm : ∀ z, MeasurableSet (Q z)) {B : Set S}
    (hB : MeasurableSet B) : Measurable (gcount Q B) := by
  classical
  unfold gcount
  split_ifs with htb
  · exact Finset.measurable_sum _ fun z _ =>
      (measurable_count (hB.inter (hQm z))).comp (measurable_pi_apply z)
  · exact measurable_const

theorem gcount_counts {μ : Measure S} {Q : Z → Set S} (h : IsTiling μ Q)
    {ι : Type*} [Fintype ι] {B : ι → Set S} (hB : ∀ j, MeasurableSet (B j))
    (hd : Pairwise (Disjoint on B)) (htb : ∀ j, TileBounded Q (B j)) (k : ι → ℕ) :
    globalProcess μ Q {ω | ∀ j, gcount Q (B j) ω = k j} =
      ∏ j, ENNReal.ofReal (pw (μ (B j)).toReal (k j)) := by
  rw [← globalProcess_counts h hB hd htb k]
  congr 1; ext ω
  simp only [Set.mem_setOf_eq, randomMeasure_eq_gcount h (hB _) (htb _), Nat.cast_inj]

/-- **Poisson marginals of the global process.** -/
theorem hasLaw_gcount {μ : Measure S} {Q : Z → Set S} (h : IsTiling μ Q) {B : Set S}
    (hB : MeasurableSet B) (htb : TileBounded Q B) :
    HasLaw (gcount Q B) (poissonMeasure (μ B).toNNReal) (globalProcess μ Q) := by
  refine hasLaw_of_pw (measurable_gcount h.measurableSet hB) fun k => ?_
  have := gcount_counts h (ι := Unit) (B := fun _ => B) (fun _ => hB)
    (fun a b hab => absurd (Subsingleton.elim a b) hab) (fun _ => htb) (fun _ => k)
  simpa [ENNReal.coe_toNNReal_eq_toReal] using this

/-- **Independence of the counts of the global process on disjoint tile-bounded sets.** -/
theorem iIndepFun_gcount {μ : Measure S} {Q : Z → Set S} (h : IsTiling μ Q)
    {ι : Type*} [Fintype ι] {B : ι → Set S} (hB : ∀ j, MeasurableSet (B j))
    (hd : Pairwise (Disjoint on B)) (htb : ∀ j, TileBounded Q (B j)) :
    iIndepFun (fun j => gcount Q (B j)) (globalProcess μ Q) := by
  rw [iIndepFun_iff_map_fun_eq_pi_map
    (fun j => (measurable_gcount h.measurableSet (hB j)).aemeasurable)]
  have hm : Measurable fun ω (j : ι) => gcount Q (B j) ω :=
    measurable_pi_iff.2 fun j => measurable_gcount h.measurableSet (hB j)
  apply Measure.ext_of_singleton
  intro k
  rw [Measure.map_apply hm (measurableSet_singleton k), ← Set.univ_pi_singleton, Measure.pi_pi]
  have : (fun ω (j : ι) => gcount Q (B j) ω) ⁻¹' Set.univ.pi (fun j => {k j}) =
      {ω | ∀ j, gcount Q (B j) ω = k j} := by
    ext ω; simp
  rw [this, gcount_counts h hB hd htb]
  refine Finset.prod_congr rfl fun j _ => ?_
  rw [(hasLaw_gcount h (hB j) (htb j)).map_eq, poissonMeasure_singleton,
    ENNReal.coe_toNNReal_eq_toReal]
  rfl

/-- The law of the Poisson process with intensity `μ`, as a law on the space of measures. -/
def poissonLaw (μ : Measure S) (Q : Z → Set S) : Measure (Measure S) :=
  (globalProcess μ Q).map (randomMeasure Q)

instance {μ : Measure S} {Q : Z → Set S} [Fact (∀ z, MeasurableSet (Q z))] :
    IsProbabilityMeasure (poissonLaw μ Q) :=
  (Measure.isProbabilityMeasure_map_iff (measurable_randomMeasure Fact.out).aemeasurable).2 inferInstance

/-- **Invariance in law (the mapping theorem for the global process).**  If `T` preserves the
intensity `μ` and maps tile-bounded sets back to tile-bounded sets, the image `T_* Π` of the
Poisson process has the same law as `Π`. -/
theorem poissonLaw_map {μ : Measure S} {Q : Z → Set S} (h : IsTiling μ Q) {T : S → S}
    (hT : MeasurePreserving T μ μ)
    (hTB : ∀ B, MeasurableSet B → TileBounded Q B → TileBounded Q (T ⁻¹' B)) :
    (poissonLaw μ Q).map (fun ν => ν.map T) = poissonLaw μ Q := by
  have hX := measurable_randomMeasure h.measurableSet
  rw [poissonLaw, Measure.map_map (Measure.measurable_map T hT.measurable) hX]
  refine law_eq_of_counts h.measurableSet h.disjoint h.iUnion_eq _ _ _ _
    ((Measure.measurable_map T hT.measurable).comp hX) hX ?_ ?_ ?_
  · intro B hB htb ω
    simp only [Function.comp_apply]
    rw [Measure.map_apply hT.measurable hB]
    exact ⟨_, randomMeasure_eq_gcount h (hT.measurable hB) (hTB B hB htb) ω⟩
  · intro B hB htb ω
    exact ⟨_, randomMeasure_eq_gcount h hB htb ω⟩
  · intro ι _ B hB hd htb k
    have e : {ω | ∀ j, (randomMeasure Q ∘ id) ω (B j) = k j} = _ := rfl
    simp only [Function.comp_apply]
    simp_rw [Measure.map_apply hT.measurable (hB _)]
    rw [globalProcess_counts h (fun j => hT.measurable (hB j))
      (fun i j hij => (hd hij).preimage T) (fun j => hTB _ (hB j) (htb j)),
      globalProcess_counts h hB hd htb]
    refine Finset.prod_congr rfl fun j _ => ?_
    rw [hT.measure_preimage (hB j).nullMeasurableSet]

end Global

/-! ## Euclidean space: tiling by unit cubes -/

section Cubes

variable {d : ℕ}

/-- The unit cube with lower corner `z ∈ ℤ^d`. -/
def cube (z : Fin d → ℤ) : Set (Fin d → ℝ) := Set.univ.pi fun i => Set.Ico (z i : ℝ) (z i + 1)

theorem mem_cube_iff {z : Fin d → ℤ} {x : Fin d → ℝ} : x ∈ cube z ↔ ∀ i, ⌊x i⌋ = z i := by
  simp only [cube, Set.mem_pi, Set.mem_univ, Set.mem_Ico, true_implies, Int.floor_eq_iff]

theorem volume_cube (z : Fin d → ℤ) : volume (cube z) = 1 := by
  rw [cube, volume_pi_pi]
  simp

/-- The unit cubes tile `ℝ^d`, for every intensity `c • volume` with `0 < c < ∞`. -/
theorem isTiling_cube {c : ℝ≥0∞} (hc0 : c ≠ 0) (hct : c ≠ ⊤) :
    IsTiling (c • (volume : Measure (Fin d → ℝ))) (cube (d := d)) where
  measurableSet z := MeasurableSet.univ_pi fun _ => measurableSet_Ico
  disjoint := by
    intro z z' hzz'
    refine Set.disjoint_left.2 fun x hx hx' => hzz' (funext fun i => ?_)
    rw [mem_cube_iff] at hx hx'
    rw [← hx i, hx' i]
  iUnion_eq := by
    ext x
    simp only [Set.mem_iUnion, Set.mem_univ, iff_true]
    exact ⟨fun i => ⌊x i⌋, mem_cube_iff.2 fun i => rfl⟩
  ne_top z := by simp [volume_cube, hct]
  ne_zero z := by simp [volume_cube, hc0]

/-- Bounded sets meet only finitely many unit cubes. -/
theorem tileBounded_cube {B : Set (Fin d → ℝ)} (hB : Bornology.IsBounded B) :
    TileBounded (cube (d := d)) B := by
  obtain ⟨R, hR⟩ := hB.subset_closedBall 0
  refine (Set.Finite.subset (Fintype.piFinset fun _ : Fin d =>
    Finset.Icc (-⌈R⌉ - 1) ⌈R⌉).finite_toSet) ?_
  rintro z ⟨x, hxB, hxz⟩
  rw [mem_cube_iff] at hxz
  simp only [Finset.mem_coe, Fintype.mem_piFinset, Finset.mem_Icc]
  intro i
  have hx := hR hxB
  rw [Metric.mem_closedBall, dist_zero_right] at hx
  have hxi : |x i| ≤ R := (norm_le_pi_norm x i).trans hx
  rw [← hxz i]
  constructor
  · have : -R ≤ x i := by linarith [neg_abs_le (x i)]
    have h1 : (-⌈R⌉ - 1 : ℤ) < ⌊x i⌋ := by
      rw [Int.lt_floor_iff]; push_cast; linarith [Int.le_ceil R]
    omega
  · exact (Int.floor_mono ((le_abs_self _).trans hxi)).trans (Int.floor_le_ceil R)

end Cubes

/-! ## Minkowski space `ℝ^{1+n}`: Lorentz transformations preserve volume -/

section Minkowski

variable {n : ℕ}

/-- The Minkowski form `t² - |x|²` on `ℝ^{1+n}` (time coordinate `0`). -/
def minkowski (p : Fin (n + 1) → ℝ) : ℝ := p 0 ^ 2 - ∑ i : Fin n, p i.succ ^ 2

/-- A Lorentz transformation: a linear map of `ℝ^{1+n}` preserving the Minkowski form. -/
def IsLorentz (L : (Fin (n + 1) → ℝ) →ₗ[ℝ] (Fin (n + 1) → ℝ)) : Prop :=
  ∀ p, minkowski (L p) = minkowski p

/-- The signature vector `(1, -1, …, -1)`. -/
def etaVec : Fin (n + 1) → ℝ := Fin.cases 1 fun _ => -1

/-- The Minkowski bilinear form. -/
def mbil (p q : Fin (n + 1) → ℝ) : ℝ := ∑ i, etaVec i * p i * q i

theorem minkowski_eq_mbil (p : Fin (n + 1) → ℝ) : minkowski p = mbil p p := by
  simp only [minkowski, mbil, Fin.sum_univ_succ, etaVec, Fin.cases_zero, Fin.cases_succ]
  rw [sq]; simp only [sq, neg_mul, one_mul, Finset.sum_neg_distrib]; ring

theorem mbil_polar (p q : Fin (n + 1) → ℝ) :
    mbil p q = (minkowski (p + q) - minkowski (p - q)) / 4 := by
  simp only [minkowski_eq_mbil, mbil, Pi.add_apply, Pi.sub_apply]
  rw [← Finset.sum_sub_distrib, Finset.sum_div]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

theorem IsLorentz.mbil_map {L : (Fin (n + 1) → ℝ) →ₗ[ℝ] (Fin (n + 1) → ℝ)} (hL : IsLorentz L)
    (p q : Fin (n + 1) → ℝ) : mbil (L p) (L q) = mbil p q := by
  rw [mbil_polar, mbil_polar, ← map_add, ← map_sub, hL, hL]

theorem IsLorentz.det_sq {L : (Fin (n + 1) → ℝ) →ₗ[ℝ] (Fin (n + 1) → ℝ)} (hL : IsLorentz L) :
    LinearMap.det L ^ 2 = 1 := by
  classical
  set M := LinearMap.toMatrix' L with hM
  have key : M.transpose * Matrix.diagonal etaVec * M = Matrix.diagonal etaVec := by
    ext a b
    have h := hL.mbil_map (Pi.single a (1 : ℝ)) (Pi.single b 1)
    have hR : mbil (Pi.single a (1 : ℝ)) (Pi.single b 1) = if a = b then etaVec a else 0 := by
      unfold mbil
      rw [Finset.sum_eq_single a]
      · by_cases hab : a = b
        · subst hab; simp
        · simp [Pi.single_apply, hab, Ne.symm hab]
      · intro i _ hi; simp [Pi.single_apply, hi]
      · simp
    have hLft : mbil (L (Pi.single a 1)) (L (Pi.single b 1)) =
        ∑ x, M x a * etaVec x * M x b := by
      unfold mbil
      refine Finset.sum_congr rfl fun x _ => ?_
      simp only [hM, LinearMap.toMatrix'_apply]; ring
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.diagonal_apply, mul_ite,
      mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    rw [← hLft, h, hR]
  have hdet := congrArg Matrix.det key
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose] at hdet
  have hη : (Matrix.diagonal (etaVec (n := n))).det ≠ 0 := by
    rw [Matrix.det_diagonal]
    refine Finset.prod_ne_zero_iff.2 fun i _ => ?_
    refine Fin.cases ?_ (fun j => ?_) i <;> simp [etaVec]
  rw [← LinearMap.det_toMatrix', ← hM]
  have : M.det * M.det * (Matrix.diagonal (etaVec (n := n))).det =
      1 * (Matrix.diagonal (etaVec (n := n))).det := by
    linear_combination hdet
  have := mul_right_cancel₀ hη this
  rw [sq]; exact this

theorem IsLorentz.abs_det {L : (Fin (n + 1) → ℝ) →ₗ[ℝ] (Fin (n + 1) → ℝ)} (hL : IsLorentz L) :
    |LinearMap.det L| = 1 := by
  have h := hL.det_sq
  rw [← sq_abs] at h
  have h0 : 0 ≤ |LinearMap.det L| := abs_nonneg _
  nlinarith [sq_nonneg (|LinearMap.det L| - 1), sq_nonneg (|LinearMap.det L| + 1)]

/-- **Lorentz transformations preserve Lebesgue measure on `ℝ^{1+n}`** (`|det| = 1`), hence
every constant multiple of it. -/
theorem IsLorentz.measurePreserving {L : (Fin (n + 1) → ℝ) →ₗ[ℝ] (Fin (n + 1) → ℝ)}
    (hL : IsLorentz L) (c : ℝ≥0∞) :
    MeasurePreserving L (c • (volume : Measure (Fin (n + 1) → ℝ))) (c • volume) := by
  have hdet : LinearMap.det L ≠ 0 := by
    intro h; have := hL.abs_det; rw [h, abs_zero] at this; exact zero_ne_one this
  have hm : Measurable L := (LinearMap.continuous_of_finiteDimensional L).measurable
  refine ⟨hm, ?_⟩
  rw [Measure.map_smul, Measure.map_linearMap_addHaar_eq_smul_addHaar (μ := volume) hdet, abs_inv,
    hL.abs_det, inv_one, ENNReal.ofReal_one, one_smul]
  exact hm.aemeasurable

theorem IsLorentz.isBounded_preimage {L : (Fin (n + 1) → ℝ) →ₗ[ℝ] (Fin (n + 1) → ℝ)}
    (hL : IsLorentz L) {B : Set (Fin (n + 1) → ℝ)} (hB : Bornology.IsBounded B) :
    Bornology.IsBounded (L ⁻¹' B) := by
  classical
  set M := LinearMap.toMatrix' L with hM
  have hdet : IsUnit M.det := by
    rw [hM, LinearMap.det_toMatrix']
    refine isUnit_iff_ne_zero.2 fun h => ?_
    have := hL.abs_det; rw [h, abs_zero] at this; exact zero_ne_one this
  set G := Matrix.toLin' M⁻¹ with hG
  have hsub : L ⁻¹' B ⊆ G '' B := by
    intro p hp
    refine ⟨L p, hp, ?_⟩
    rw [hG, Matrix.toLin'_apply, ← LinearMap.toMatrix'_mulVec L, ← hM, Matrix.mulVec_mulVec,
      Matrix.nonsing_inv_mul _ hdet, Matrix.one_mulVec]
  exact ((LinearMap.toContinuousLinearMap G).lipschitzWith.isBounded_image hB).subset hsub

/-- The boost with Doppler factor `l` in the `(t, x₁)`-plane, as a linear map. -/
def boostL (n : ℕ) (l : ℝ) : (Fin (n + 2) → ℝ) →ₗ[ℝ] (Fin (n + 2) → ℝ) where
  toFun := QE.OpenGeo.boostAt 1 l
  map_add' p q := by
    ext i; simp only [QE.OpenGeo.boostAt, QE.OpenGeo.boost, Pi.add_apply]; split_ifs <;> ring
  map_smul' c p := by
    ext i; simp only [QE.OpenGeo.boostAt, QE.OpenGeo.boost, Pi.smul_apply, smul_eq_mul,
      RingHom.id_apply]; split_ifs <;> ring

theorem boostL_isLorentz (n : ℕ) {l : ℝ} (hl : l ≠ 0) : IsLorentz (boostL n l) := by
  intro p
  have h1 : (1 : Fin (n + 2)) ≠ 0 := by simp
  have hm := QE.OpenGeo.boost_minkowski l hl (p 0, p 1)
  have hp := QE.OpenGeo.boostAt_proj (1 : Fin (n + 2)) h1 l p
  simp only [minkowski, Fin.sum_univ_succ]
  have e0 : (boostL n l p) 0 = (QE.OpenGeo.boost l (p 0, p 1)).1 := congrArg Prod.fst hp
  have e1 : (boostL n l p) (Fin.succ 0) = (QE.OpenGeo.boost l (p 0, p 1)).2 := congrArg Prod.snd hp
  have erest : ∀ i : Fin n, (boostL n l p) i.succ.succ = p i.succ.succ := by
    intro i
    show QE.OpenGeo.boostAt 1 l p i.succ.succ = _
    simp only [QE.OpenGeo.boostAt]
    rw [if_neg (Fin.succ_ne_zero _), if_neg]
    intro h; have := congrArg Fin.val h; simp at this
  rw [e0, e1]
  simp_rw [erest]
  simp only at hm
  rw [show (Fin.succ (0 : Fin (n + 1)) : Fin (n + 2)) = 1 from rfl]
  linarith

theorem isBounded_preimage_add {d : ℕ} (a : Fin d → ℝ) {B : Set (Fin d → ℝ)}
    (hB : Bornology.IsBounded B) : Bornology.IsBounded ((· + a) ⁻¹' B) := by
  obtain ⟨R, hR⟩ := hB.subset_closedBall 0
  refine (Metric.isBounded_closedBall (x := 0) (r := R + ‖a‖)).subset fun p hp => ?_
  have := hR hp
  simp only [Metric.mem_closedBall, dist_zero_right] at this ⊢
  calc ‖p‖ = ‖(p + a) - a‖ := by rw [add_sub_cancel_right]
    _ ≤ ‖p + a‖ + ‖a‖ := norm_sub_le _ _
    _ ≤ R + ‖a‖ := by linarith

end Minkowski

/-! ## Poisson sprinkling of `ℝ^{1+n}` -/

section Sprinkling

variable {n : ℕ}

theorem isBounded_of_tileBounded_cube {d : ℕ} {B : Set (Fin d → ℝ)}
    (hB : TileBounded (cube (d := d)) B) : Bornology.IsBounded B := by
  have hsub : B ⊆ ⋃ z ∈ hB.toFinset, cube z := by
    intro x hx
    simp only [Set.mem_iUnion, exists_prop]
    exact ⟨fun i => ⌊x i⌋, (Set.Finite.mem_toFinset _).2 ⟨x, hx, mem_cube_iff.2 fun i => rfl⟩,
      mem_cube_iff.2 fun i => rfl⟩
  refine Bornology.IsBounded.subset ?_ hsub
  refine (Bornology.isBounded_biUnion_finset _).2 fun z _ => ?_
  refine (Metric.isBounded_Icc (fun i => (z i : ℝ)) (fun i => (z i : ℝ) + 1)).subset ?_
  intro x hx
  simp only [cube, Set.mem_pi, Set.mem_univ, Set.mem_Ico, true_implies] at hx
  exact ⟨fun i => (hx i).1, fun i => (hx i).2.le⟩

theorem tileBounded_cube_iff {d : ℕ} {B : Set (Fin d → ℝ)} :
    TileBounded (cube (d := d)) B ↔ Bornology.IsBounded B :=
  ⟨isBounded_of_tileBounded_cube, tileBounded_cube⟩

/-- The intensity measure `ℓ^{-(n+1)} · volume` of a sprinkling of `ℝ^{1+n}` at density one point
per Planck volume `ℓ^{n+1}`. -/
abbrev sprinkleIntensity (n : ℕ) (ℓ : ℝ) : Measure (Fin (n + 1) → ℝ) :=
  ENNReal.ofReal ((ℓ ^ (n + 1))⁻¹) • volume

theorem sprinkleIntensity_isTiling {ℓ : ℝ} (hℓ : 0 < ℓ) :
    IsTiling (sprinkleIntensity n ℓ) (cube (d := n + 1)) :=
  isTiling_cube (by simp [ENNReal.ofReal_eq_zero, hℓ]) ENNReal.ofReal_ne_top

/-- **Lorentz invariance in law of the Poisson sprinkling.** -/
theorem sprinkle_lorentz_invariant {ℓ : ℝ} (hℓ : 0 < ℓ)
    {L : (Fin (n + 1) → ℝ) →ₗ[ℝ] (Fin (n + 1) → ℝ)} (hL : IsLorentz L) :
    (poissonLaw (sprinkleIntensity n ℓ) cube).map (fun ν => ν.map L) =
      poissonLaw (sprinkleIntensity n ℓ) cube :=
  poissonLaw_map (sprinkleIntensity_isTiling hℓ) (hL.measurePreserving _) fun _ _ hB =>
    tileBounded_cube (hL.isBounded_preimage (isBounded_of_tileBounded_cube hB))

/-- **Translation invariance in law of the Poisson sprinkling.** -/
theorem sprinkle_translation_invariant {ℓ : ℝ} (hℓ : 0 < ℓ) (a : Fin (n + 1) → ℝ) :
    (poissonLaw (sprinkleIntensity n ℓ) cube).map (fun ν => ν.map (· + a)) =
      poissonLaw (sprinkleIntensity n ℓ) cube :=
  poissonLaw_map (sprinkleIntensity_isTiling hℓ)
    (measurePreserving_add_right (sprinkleIntensity n ℓ) a) fun _ _ hB =>
    tileBounded_cube (isBounded_preimage_add a (isBounded_of_tileBounded_cube hB))

/-- The unit future timelike hyperboloid `t² - |x|² = 1`, `t > 0`. -/
def hyperboloid (n : ℕ) : Set (Fin (n + 1) → ℝ) := {p | minkowski p = 1 ∧ 0 < p 0}

theorem measurableSet_hyperboloid : MeasurableSet (hyperboloid n) := by
  have hc : Continuous (minkowski (n := n)) := by unfold minkowski; fun_prop
  exact (measurableSet_eq_fun hc.measurable measurable_const).inter
    (measurableSet_lt measurable_const (measurable_pi_apply 0))

theorem lightcone_pos {p : Fin (n + 2) → ℝ} (hp : p ∈ hyperboloid (n + 1)) :
    0 < p 0 + p 1 ∧ 0 < p 0 - p 1 := by
  obtain ⟨h1, h0⟩ := hp
  simp only [minkowski, Fin.sum_univ_succ] at h1
  have hrest : 0 ≤ ∑ i : Fin n, p i.succ.succ ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
  have e : p (Fin.succ 0) = p 1 := rfl
  rw [e] at h1
  have : p 1 ^ 2 < p 0 ^ 2 := by nlinarith
  have := abs_lt_of_sq_lt_sq this h0.le
  constructor <;> linarith [neg_abs_le (p 1), le_abs_self (p 1)]

theorem boostL_apply_zero (l : ℝ) (p : Fin (n + 2) → ℝ) :
    boostL n l p 0 = (QE.OpenGeo.boost l (p 0, p 1)).1 :=
  congrArg Prod.fst (QE.OpenGeo.boostAt_proj (1 : Fin (n + 2)) (by simp) l p)

theorem boostL_apply_one (l : ℝ) (p : Fin (n + 2) → ℝ) :
    boostL n l p 1 = (QE.OpenGeo.boost l (p 0, p 1)).2 :=
  congrArg Prod.snd (QE.OpenGeo.boostAt_proj (1 : Fin (n + 2)) (by simp) l p)

/-- The boost by `2` maps the hyperboloid onto itself (as a preimage). -/
theorem boost_two_mem_hyperboloid_iff (p : Fin (n + 2) → ℝ) :
    boostL n 2 p ∈ hyperboloid (n + 1) ↔ p ∈ hyperboloid (n + 1) := by
  have hL := boostL_isLorentz n (l := 2) (by norm_num)
  have hlc := QE.OpenGeo.boost_lightcone (2 : ℝ) (p 0, p 1)
  rw [← boostL_apply_zero, ← boostL_apply_one] at hlc
  simp only at hlc
  constructor
  · intro h
    have hpos := lightcone_pos h
    refine ⟨by rw [← hL p]; exact h.1, ?_⟩
    rw [hlc.1] at hpos; rw [hlc.2] at hpos
    have h1 : 0 < p 0 + p 1 := by nlinarith [hpos.1]
    have h2 : 0 < p 0 - p 1 := by
      have := hpos.2; norm_num at this; linarith
    linarith
  · intro h
    have hpos := lightcone_pos h
    refine ⟨by rw [hL p]; exact h.1, ?_⟩
    have e1 := hlc.1; have e2 := hlc.2
    norm_num at e2
    nlinarith [hpos.1, hpos.2]

/-- **No Lorentz-equivariant frame** (Bombelli–Henson–Sorkin).  There is no measurable map `D`
from configurations (counting measures) of `ℝ^{1+(n+1)}` to the unit future hyperboloid that is
almost surely equivariant, `D(Λ Π) = Λ D(Π)`, for the Lorentz transformations `Λ` of the Poisson
sprinkling: the image law would be a probability measure on the hyperboloid invariant under
boosts, and there is none. -/
theorem sprinkle_no_equivariant_frame {ℓ : ℝ} (hℓ : 0 < ℓ)
    (D : Measure (Fin (n + 2) → ℝ) → (Fin (n + 2) → ℝ)) (hD : Measurable D)
    (hH : ∀ᵐ ν ∂(poissonLaw (sprinkleIntensity (n + 1) ℓ) cube), D ν ∈ hyperboloid (n + 1))
    (heq : ∀ L : (Fin (n + 2) → ℝ) →ₗ[ℝ] (Fin (n + 2) → ℝ), IsLorentz L →
      ∀ᵐ ν ∂(poissonLaw (sprinkleIntensity (n + 1) ℓ) cube), D (ν.map L) = L (D ν)) :
    False := by
  set 𝓛 := poissonLaw (sprinkleIntensity (n + 1) ℓ) cube with h𝓛
  haveI : Fact (∀ z, MeasurableSet (cube (d := n + 2) z)) :=
    ⟨(sprinkleIntensity_isTiling hℓ).measurableSet⟩
  set B := boostL n 2 with hBdef
  have hBL : IsLorentz B := boostL_isLorentz n (by norm_num)
  have hBm : Measurable B := (LinearMap.continuous_of_finiteDimensional B).measurable
  have hinv : 𝓛.map (fun ν => ν.map B) = 𝓛 := sprinkle_lorentz_invariant hℓ hBL
  set ρ := 𝓛.map D with hρ
  have hρB : ρ.map B = ρ := by
    rw [hρ, Measure.map_map hBm hD]
    have : 𝓛.map (B ∘ D) = 𝓛.map (D ∘ fun ν => ν.map B) := by
      refine Measure.map_congr ?_
      filter_upwards [heq B hBL] with ν hν
      exact hν.symm
    rw [this, ← Measure.map_map hD (Measure.measurable_map _ hBm), hinv]
  have hρH : ρ (hyperboloid (n + 1)) = 1 := by
    rw [hρ, Measure.map_apply hD measurableSet_hyperboloid]
    have := (ae_iff_measure_eq (μ := 𝓛) (p := fun ν => ν ∈ D ⁻¹' hyperboloid (n + 1))
      (hD measurableSet_hyperboloid).nullMeasurableSet).1 hH
    rw [Set.setOf_mem_eq] at this
    rw [this, measure_univ]
  -- the `log` of the light-cone coordinate `u = t + x₁`
  set g : (Fin (n + 2) → ℝ) → ℝ := fun p => Real.log (p 0 + p 1) with hg
  have hgm : Measurable g := by
    have : Continuous fun p : Fin (n + 2) → ℝ => p 0 + p 1 := by fun_prop
    exact Real.measurable_log.comp this.measurable
  set a := Real.log 2 with ha
  have hapos : 0 < a := Real.log_pos (by norm_num)
  set I : ℤ → Set (Fin (n + 2) → ℝ) :=
    fun k => hyperboloid (n + 1) ∩ g ⁻¹' Set.Ico (k * a) ((k + 1) * a) with hI
  have hIm : ∀ k, MeasurableSet (I k) := fun k =>
    measurableSet_hyperboloid.inter (hgm measurableSet_Ico)
  have hgB : ∀ p ∈ hyperboloid (n + 1), g (B p) = g p + a := by
    intro p hp
    have hlc := QE.OpenGeo.boost_lightcone (2 : ℝ) (p 0, p 1)
    rw [← boostL_apply_zero, ← boostL_apply_one] at hlc
    simp only [hg]
    rw [hlc.1, Real.log_mul (by norm_num) (lightcone_pos hp).1.ne', ha]; ring
  have hpre : ∀ k : ℤ, B ⁻¹' I (k + 1) = I k := by
    intro k
    ext p
    simp only [hI, Set.mem_preimage, Set.mem_inter_iff, Set.mem_Ico]
    rw [boost_two_mem_hyperboloid_iff]
    constructor
    · rintro ⟨hp, h1, h2⟩
      rw [hgB p hp] at h1 h2
      push_cast at h1 h2
      exact ⟨hp, by linarith, by linarith⟩
    · rintro ⟨hp, h1, h2⟩
      rw [hgB p hp]
      push_cast
      exact ⟨hp, by linarith, by linarith⟩
  have hstep : ∀ k : ℤ, ρ (I (k + 1)) = ρ (I k) := by
    intro k
    conv_lhs => rw [← hρB]
    rw [Measure.map_apply hBm (hIm _), hpre]
  have hconst : ∀ k : ℤ, ρ (I k) = ρ (I 0) := by
    intro k
    induction k using Int.induction_on with
    | zero => rfl
    | succ k ih => rw [hstep, ih]
    | pred k ih => rw [← ih, ← hstep]; congr 2; ring
  have hU : hyperboloid (n + 1) = ⋃ k : ℤ, I k := by
    ext p
    simp only [hI, Set.mem_iUnion, Set.mem_inter_iff, Set.mem_preimage, Set.mem_Ico]
    constructor
    · intro hp
      refine ⟨⌊g p / a⌋, hp, ?_, ?_⟩
      · have := Int.floor_le (g p / a); rw [le_div_iff₀ hapos] at this; exact this
      · have := Int.lt_floor_add_one (g p / a); rw [div_lt_iff₀ hapos] at this; exact this
    · rintro ⟨k, hp, _⟩; exact hp
  have hdisj : Pairwise (Disjoint on I) := by
    intro k k' hkk'
    refine Set.disjoint_left.2 fun p hp hp' => hkk' ?_
    simp only [hI, Set.mem_inter_iff, Set.mem_preimage, Set.mem_Ico] at hp hp'
    have h1 : (k : ℝ) < k' + 1 := by
      have := lt_of_le_of_lt hp.2.1 hp'.2.2; exact lt_of_mul_lt_mul_right this hapos.le
    have h2 : (k' : ℝ) < k + 1 := by
      have := lt_of_le_of_lt hp'.2.1 hp.2.2; exact lt_of_mul_lt_mul_right this hapos.le
    have h1' : k < k' + 1 := by exact_mod_cast h1
    have h2' : k' < k + 1 := by exact_mod_cast h2
    omega
  have hsum : ρ (hyperboloid (n + 1)) = ∑' k : ℤ, ρ (I 0) := by
    rw [hU, measure_iUnion hdisj hIm]
    exact tsum_congr hconst
  rw [hρH] at hsum
  by_cases h0 : ρ (I 0) = 0
  · rw [h0, tsum_zero] at hsum; exact one_ne_zero hsum
  · rw [ENNReal.tsum_const_eq_top_of_ne_zero h0] at hsum; exact ENNReal.one_ne_top hsum

/-- The content `μ_Π(A) = ℓ^{n+1} · #(A ∩ Π)` of a set under the sprinkling. -/
def sprinkleContent (n : ℕ) (ℓ : ℝ) (A : Set (Fin (n + 1) → ℝ)) (ω : (Fin (n + 1) → ℤ) → Config (Fin (n + 1) → ℝ)) : ℝ :=
  ℓ ^ (n + 1) * gcount cube A ω

/-- **Faithfulness**: a set containing a point of the sprinkling has content at least `ℓ^{n+1}`. -/
theorem sprinkle_faithful {ℓ : ℝ} (hℓ : 0 ≤ ℓ) (A : Set (Fin (n + 1) → ℝ))
    (ω : (Fin (n + 1) → ℤ) → Config (Fin (n + 1) → ℝ)) (h : gcount cube A ω ≠ 0) :
    ℓ ^ (n + 1) ≤ sprinkleContent n ℓ A ω := by
  unfold sprinkleContent
  have : (1 : ℝ) ≤ gcount cube A ω := by exact_mod_cast Nat.one_le_iff_ne_zero.2 h
  nlinarith [pow_nonneg hℓ (n + 1)]

theorem sprinkleIntensity_toReal {ℓ : ℝ} (hℓ : 0 < ℓ) (A : Set (Fin (n + 1) → ℝ)) :
    (sprinkleIntensity n ℓ A).toReal = (ℓ ^ (n + 1))⁻¹ * (volume A).toReal := by
  rw [sprinkleIntensity, Measure.smul_apply, smul_eq_mul, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (by positivity)]

theorem sprinkle_hasLaw {ℓ : ℝ} (hℓ : 0 < ℓ) {A : Set (Fin (n + 1) → ℝ)} (hA : MeasurableSet A)
    (hAb : Bornology.IsBounded A) :
    HasLaw (gcount cube A) (poissonMeasure (sprinkleIntensity n ℓ A).toNNReal)
      (globalProcess (sprinkleIntensity n ℓ) cube) :=
  hasLaw_gcount (sprinkleIntensity_isTiling hℓ) hA (tileBounded_cube hAb)

/-- **Mean content**: `E μ_Π(A) = leb(A)`. -/
theorem sprinkle_mean {ℓ : ℝ} (hℓ : 0 < ℓ) {A : Set (Fin (n + 1) → ℝ)} (hA : MeasurableSet A)
    (hAb : Bornology.IsBounded A) :
    ∫ ω, sprinkleContent n ℓ A ω ∂(globalProcess (sprinkleIntensity n ℓ) cube) =
      (volume A).toReal := by
  unfold sprinkleContent
  rw [integral_const_mul, integral_of_hasLaw (sprinkle_hasLaw hℓ hA hAb),
    ENNReal.coe_toNNReal_eq_toReal, sprinkleIntensity_toReal hℓ]
  field_simp

/-- **Variance of the content**: `Var μ_Π(A) = ℓ^{n+1} leb(A)`. -/
theorem sprinkle_variance {ℓ : ℝ} (hℓ : 0 < ℓ) {A : Set (Fin (n + 1) → ℝ)}
    (hA : MeasurableSet A) (hAb : Bornology.IsBounded A) :
    variance (sprinkleContent n ℓ A) (globalProcess (sprinkleIntensity n ℓ) cube) =
      ℓ ^ (n + 1) * (volume A).toReal := by
  unfold sprinkleContent
  rw [variance_const_mul, variance_of_hasLaw (sprinkle_hasLaw hℓ hA hAb),
    ENNReal.coe_toNNReal_eq_toReal, sprinkleIntensity_toReal hℓ]
  have : ℓ ^ (n + 1) ≠ 0 := by positivity
  field_simp

/-- **Chebyshev's bound for the content**:
`P(|μ_Π(A) - leb(A)| ≥ η) ≤ ℓ^{n+1} leb(A) / η²`. -/
theorem sprinkle_chebyshev {ℓ : ℝ} (hℓ : 0 < ℓ) {A : Set (Fin (n + 1) → ℝ)}
    (hA : MeasurableSet A) (hAb : Bornology.IsBounded A) {η : ℝ} (hη : 0 < η) :
    globalProcess (sprinkleIntensity n ℓ) cube
        {ω | η ≤ |sprinkleContent n ℓ A ω - (volume A).toReal|} ≤
      ENNReal.ofReal (ℓ ^ (n + 1) * (volume A).toReal / η ^ 2) := by
  have hc : 0 < ℓ ^ (n + 1) := by positivity
  have h := chebyshev_of_hasLaw (sprinkle_hasLaw hℓ hA hAb) (c := η / ℓ ^ (n + 1)) (by positivity)
  rw [ENNReal.coe_toNNReal_eq_toReal, sprinkleIntensity_toReal hℓ] at h
  have hset : {ω | η ≤ |sprinkleContent n ℓ A ω - (volume A).toReal|} =
      {ω | η / ℓ ^ (n + 1) ≤ |(gcount cube A ω : ℝ) - (ℓ ^ (n + 1))⁻¹ * (volume A).toReal|} := by
    ext ω
    simp only [Set.mem_setOf_eq, sprinkleContent]
    rw [div_le_iff₀ hc]
    have : |(gcount cube A ω : ℝ) - (ℓ ^ (n + 1))⁻¹ * (volume A).toReal| * ℓ ^ (n + 1) =
        |ℓ ^ (n + 1) * gcount cube A ω - (volume A).toReal| := by
      rw [← abs_of_pos hc, ← abs_mul, abs_of_pos hc]; congr 1; field_simp
    rw [this]
  rw [hset]
  refine h.trans (le_of_eq ?_)
  congr 1
  field_simp

/-- **The infinitesimal case**: if `ℓ = [ℓ_k]` is a positive infinitesimal, the probability
that `|μ_Π(A) - leb(A)| ≥ η` is infinitesimal for every standard `η > 0`. -/
theorem sprinkle_infinitesimal {ℓ : ℕ → ℝ} (hℓ : ∀ k, 0 < ℓ k)
    (hinf : QE.NSA.IsInfinitesimal (Hyperreal.ofSeq ℓ)) {A : Set (Fin (n + 1) → ℝ)}
    (hA : MeasurableSet A) (hAb : Bornology.IsBounded A) {η : ℝ} (hη : 0 < η) :
    QE.NSA.IsInfinitesimal (Hyperreal.ofSeq fun k =>
      (globalProcess (sprinkleIntensity n (ℓ k)) cube
        {ω | η ≤ |sprinkleContent n (ℓ k) A ω - (volume A).toReal|}).toReal) := by
  rw [QE.NSA.isInfinitesimal_ofSeq_iff]
  intro r hr
  set C := (volume A).toReal / η ^ 2 with hC
  have hC0 : 0 ≤ C := by positivity
  have h1 := (QE.NSA.isInfinitesimal_ofSeq_iff ℓ).1 hinf (min 1 (r / (C + 1))) (by positivity)
  filter_upwards [h1] with k hk
  have hk1 : ℓ k < 1 := by
    have := lt_of_le_of_lt (le_abs_self _) hk; exact lt_of_lt_of_le this (min_le_left _ _)
  have hk2 : ℓ k < r / (C + 1) := by
    have := lt_of_le_of_lt (le_abs_self _) hk; exact lt_of_lt_of_le this (min_le_right _ _)
  have hpow : ℓ k ^ (n + 1) ≤ ℓ k := pow_le_of_le_one (hℓ k).le hk1.le (by omega)
  have hb := sprinkle_chebyshev (n := n) (hℓ k) hA hAb hη
  have hb' := ENNReal.toReal_mono ENNReal.ofReal_ne_top hb
  rw [ENNReal.toReal_ofReal (by have := hℓ k; positivity)] at hb'
  rw [abs_of_nonneg ENNReal.toReal_nonneg]
  calc _ ≤ ℓ k ^ (n + 1) * (volume A).toReal / η ^ 2 := hb'
    _ = ℓ k ^ (n + 1) * C := by rw [hC]; ring
    _ ≤ ℓ k * C := mul_le_mul_of_nonneg_right hpow hC0
    _ ≤ r / (C + 1) * C := mul_le_mul_of_nonneg_right hk2.le hC0
    _ < r := by
      rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]; nlinarith

theorem measurable_sprinkleContent {ℓ : ℝ} {A : Set (Fin (n + 1) → ℝ)} (hA : MeasurableSet A) :
    Measurable (sprinkleContent n ℓ A) :=
  measurable_const.mul (measurable_from_nat.comp
    (measurable_gcount (fun z => MeasurableSet.univ_pi fun _ => measurableSet_Ico) hA))

/-- **Strong law along a sequence of Planck lengths.**  For independent sprinklings with Planck
lengths `ℓ_k`, `∑ ℓ_k^{n+1} < ∞`, almost surely `μ_{Π_k}(A_m) → leb(A_m)`, simultaneously for a
countable family of bounded Borel sets `A_m` (for instance all rational boxes). -/
theorem sprinkle_strong_law {ℓ : ℕ → ℝ} (hℓ : ∀ k, 0 < ℓ k)
    (hsum : Summable fun k => ℓ k ^ (n + 1)) {A : ℕ → Set (Fin (n + 1) → ℝ)}
    (hA : ∀ m, MeasurableSet (A m)) (hAb : ∀ m, Bornology.IsBounded (A m)) :
    ∀ᵐ ω ∂(Measure.infinitePi fun k => globalProcess (sprinkleIntensity n (ℓ k)) cube),
      ∀ m, Tendsto (fun k => sprinkleContent n (ℓ k) (A m) (ω k)) atTop
        (𝓝 (volume (A m)).toReal) := by
  rw [ae_all_iff]
  intro m
  set V := (volume (A m)).toReal with hV
  have hj : ∀ j : ℕ, ∀ᵐ ω ∂(Measure.infinitePi fun k => globalProcess (sprinkleIntensity n (ℓ k)) cube),
      ∀ᶠ k in atTop, ω ∉ {ω : ℕ → _ | 1 / ((j : ℝ) + 1) ≤
        |sprinkleContent n (ℓ k) (A m) (ω k) - V|} := by
    intro j
    apply ae_eventually_notMem
    have hη : (0 : ℝ) < 1 / ((j : ℝ) + 1) := by positivity
    have hle : ∀ k, (Measure.infinitePi fun k => globalProcess (sprinkleIntensity n (ℓ k)) cube)
        {ω : ℕ → _ | 1 / ((j : ℝ) + 1) ≤ |sprinkleContent n (ℓ k) (A m) (ω k) - V|} ≤
        ENNReal.ofReal (ℓ k ^ (n + 1) * V / (1 / ((j : ℝ) + 1)) ^ 2) := by
      intro k
      have hS : MeasurableSet {c : (Fin (n + 1) → ℤ) → Config (Fin (n + 1) → ℝ) |
          1 / ((j : ℝ) + 1) ≤ |sprinkleContent n (ℓ k) (A m) c - V|} :=
        measurableSet_le measurable_const
          (((measurable_sprinkleContent (hA m)).sub measurable_const).abs)
      have := (measurePreserving_eval_infinitePi
        (fun k => globalProcess (sprinkleIntensity n (ℓ k)) cube) k).measure_preimage
        hS.nullMeasurableSet
      rw [show {ω : ℕ → _ | 1 / ((j : ℝ) + 1) ≤ |sprinkleContent n (ℓ k) (A m) (ω k) - V|} =
        Function.eval k ⁻¹' {c | 1 / ((j : ℝ) + 1) ≤ |sprinkleContent n (ℓ k) (A m) c - V|}
        from rfl, this]
      exact sprinkle_chebyshev (hℓ k) (hA m) (hAb m) hη
    refine ne_top_of_le_ne_top ?_ (ENNReal.tsum_le_tsum hle)
    rw [← ENNReal.ofReal_tsum_of_nonneg]
    · exact ENNReal.ofReal_ne_top
    · intro k; have := hℓ k; positivity
    · exact (hsum.mul_right (V / (1 / ((j : ℝ) + 1)) ^ 2)).congr fun k => by ring
  rw [← ae_all_iff] at hj
  filter_upwards [hj] with ω hω
  rw [Metric.tendsto_atTop]
  intro r hr
  obtain ⟨j, hjr⟩ := exists_nat_one_div_lt hr
  obtain ⟨K, hK⟩ := (hω j).exists_forall_of_atTop
  refine ⟨K, fun k hk => ?_⟩
  have := hK k hk
  simp only [Set.mem_setOf_eq, not_le] at this
  rw [Real.dist_eq]
  exact this.trans hjr

end Sprinkling

/-! ## Euclidean space `ℝ^d` with its Euclidean structure -/

section Euclid

variable {d : ℕ}

/-- The unit cubes of `EuclideanSpace ℝ (Fin d)`. -/
def ecube (z : Fin d → ℤ) : Set (EuclideanSpace ℝ (Fin d)) := WithLp.ofLp ⁻¹' cube z

theorem isTiling_ecube {c : ℝ≥0∞} (hc0 : c ≠ 0) (hct : c ≠ ⊤) :
    IsTiling (c • (volume : Measure (EuclideanSpace ℝ (Fin d)))) (ecube (d := d)) := by
  have hp := PiLp.volume_preserving_ofLp (Fin d)
  have ht := isTiling_cube (d := d) hc0 hct
  refine ⟨fun z => hp.measurable (ht.measurableSet z), ?_, ?_, ?_, ?_⟩
  · intro z z' h; exact (ht.disjoint h).preimage _
  · show ⋃ z, WithLp.ofLp ⁻¹' cube z = _
    rw [← Set.preimage_iUnion, ht.iUnion_eq, Set.preimage_univ]
  · intro z
    rw [Measure.smul_apply, ecube, hp.measure_preimage (ht.measurableSet z).nullMeasurableSet]
    simpa [volume_cube] using hct
  · intro z
    rw [Measure.smul_apply, ecube, hp.measure_preimage (ht.measurableSet z).nullMeasurableSet]
    simpa [volume_cube] using hc0

theorem tileBounded_ecube {B : Set (EuclideanSpace ℝ (Fin d))} (hB : Bornology.IsBounded B) :
    TileBounded (ecube (d := d)) B := by
  have h := tileBounded_cube ((PiLp.lipschitzWith_ofLp 2 (fun _ : Fin d => ℝ)).isBounded_image hB)
  refine h.subset fun z hz => ?_
  obtain ⟨x, hxB, hxz⟩ := hz
  exact ⟨WithLp.ofLp x, ⟨x, hxB, rfl⟩, hxz⟩

theorem isBounded_of_tileBounded_ecube {B : Set (EuclideanSpace ℝ (Fin d))}
    (hB : TileBounded (ecube (d := d)) B) : Bornology.IsBounded B := by
  have h1 : Bornology.IsBounded (WithLp.ofLp '' B) := by
    refine isBounded_of_tileBounded_cube (hB.subset fun z hz => ?_)
    obtain ⟨y, ⟨x, hx, rfl⟩, hy⟩ := hz
    exact ⟨x, hx, hy⟩
  exact ((PiLp.antilipschitzWith_ofLp 2 (fun _ : Fin d => ℝ)).isBounded_preimage h1).subset
    (Set.subset_preimage_image _ _)

/-- Rigid motions of Euclidean space preserve Lebesgue measure. -/
theorem IsometryEquiv.measurePreserving_volume (g : EuclideanSpace ℝ (Fin d) ≃ᵢ
    EuclideanSpace ℝ (Fin d)) :
    MeasurePreserving g (volume : Measure (EuclideanSpace ℝ (Fin d))) volume := by
  set f := g.toRealAffineIsometryEquiv with hf
  set L := f.linearIsometryEquiv with hL
  have hdecomp : (g : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) =
      (· + g 0) ∘ L := by
    ext1 x
    simp only [Function.comp_apply, hL]
    have := f.map_vadd 0 x
    rw [vadd_eq_add, add_zero, hf, IsometryEquiv.coeFn_toRealAffineIsometryEquiv] at this
    rw [this, vadd_eq_add]
  rw [hdecomp]
  exact (measurePreserving_add_right volume (g 0)).comp L.measurePreserving

/-- The intensity `(2ε)^{-d} · volume`: on average one point per granular cell of volume
`(2ε)^d`. -/
abbrev granIntensity (d : ℕ) (ε : ℝ) : Measure (EuclideanSpace ℝ (Fin d)) :=
  ENNReal.ofReal (((2 * ε) ^ d)⁻¹) • volume

/-- The granular content `μ_Π(A) = (2ε)^d · #(A ∩ Π)` of the Poisson set. -/
def granContent (d : ℕ) (ε : ℝ) (A : Set (EuclideanSpace ℝ (Fin d)))
    (ω : (Fin d → ℤ) → Config (EuclideanSpace ℝ (Fin d))) : ℝ :=
  (2 * ε) ^ d * gcount ecube A ω

theorem granIntensity_isTiling {ε : ℝ} (hε : 0 < ε) :
    IsTiling (granIntensity d ε) (ecube (d := d)) :=
  isTiling_ecube (by simp [ENNReal.ofReal_eq_zero]; positivity) ENNReal.ofReal_ne_top

theorem granIntensity_toReal {ε : ℝ} (hε : 0 < ε) (A : Set (EuclideanSpace ℝ (Fin d))) :
    (granIntensity d ε A).toReal = ((2 * ε) ^ d)⁻¹ * (volume A).toReal := by
  rw [granIntensity, Measure.smul_apply, smul_eq_mul, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (by positivity)]

theorem measurable_granContent {ε : ℝ} {A : Set (EuclideanSpace ℝ (Fin d))}
    (hA : MeasurableSet A) : Measurable (granContent d ε A) :=
  measurable_const.mul (measurable_from_nat.comp
    (measurable_gcount (isTiling_ecube (c := 1) one_ne_zero ENNReal.one_ne_top).measurableSet hA))

/-- The law of the granular content of a bounded Borel set is the image of the Poisson law of
mean `(2ε)^{-d} leb(A)`. -/
theorem map_granContent {ε : ℝ} (hε : 0 < ε) {A : Set (EuclideanSpace ℝ (Fin d))}
    (hA : MeasurableSet A) (hAb : Bornology.IsBounded A) :
    (globalProcess (granIntensity d ε) ecube).map (granContent d ε A) =
      (poissonMeasure (granIntensity d ε A).toNNReal).map (fun k : ℕ => (2 * ε) ^ d * (k : ℝ)) := by
  have hl := hasLaw_gcount (granIntensity_isTiling (d := d) hε) hA (tileBounded_ecube hAb)
  rw [← hl.map_eq, Measure.map_map (by fun_prop) (measurable_gcount
    (granIntensity_isTiling hε).measurableSet hA)]
  rfl

theorem isometry_image_eq {X : Type*} [MetricSpace X] (g : X ≃ᵢ X) (C : Set X) :
    g '' C = g.symm ⁻¹' C := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩; simpa using hy
  · intro hx; exact ⟨g.symm x, hx, g.apply_symm_apply x⟩

theorem image_isometry_measurableSet (g : EuclideanSpace ℝ (Fin d) ≃ᵢ EuclideanSpace ℝ (Fin d))
    {C : Set (EuclideanSpace ℝ (Fin d))} (hC : MeasurableSet C) : MeasurableSet (g '' C) := by
  rw [isometry_image_eq]
  exact g.symm.continuous.measurable hC

theorem volume_image_isometry (g : EuclideanSpace ℝ (Fin d) ≃ᵢ EuclideanSpace ℝ (Fin d))
    {C : Set (EuclideanSpace ℝ (Fin d))} (hC : MeasurableSet C) : volume (g '' C) = volume C := by
  rw [isometry_image_eq]
  exact (IsometryEquiv.measurePreserving_volume g.symm).measure_preimage hC.nullMeasurableSet

/-- **Poisson sets, (i): isotropy in law.**  For every rigid motion `g` and bounded Borel `C`,
`μ_Π(gC)` has the same law as `μ_Π(C)`. -/
theorem poisson_rigid_law {ε : ℝ} (hε : 0 < ε) (g : EuclideanSpace ℝ (Fin d) ≃ᵢ
    EuclideanSpace ℝ (Fin d)) {C : Set (EuclideanSpace ℝ (Fin d))} (hC : MeasurableSet C)
    (hCb : Bornology.IsBounded C) :
    (globalProcess (granIntensity d ε) ecube).map (granContent d ε (g '' C)) =
      (globalProcess (granIntensity d ε) ecube).map (granContent d ε C) := by
  have hgb : Bornology.IsBounded (g '' C) := g.isometry.lipschitz.isBounded_image hCb
  rw [map_granContent hε (image_isometry_measurableSet g hC) hgb, map_granContent hε hC hCb,
    granIntensity, Measure.smul_apply, Measure.smul_apply, volume_image_isometry g hC]

/-- **Poisson sets, (i): mean.**  `E μ_Π(C) = leb(C)`. -/
theorem poisson_content_mean {ε : ℝ} (hε : 0 < ε) {C : Set (EuclideanSpace ℝ (Fin d))}
    (hC : MeasurableSet C) (hCb : Bornology.IsBounded C) :
    ∫ ω, granContent d ε C ω ∂(globalProcess (granIntensity d ε) ecube) = (volume C).toReal := by
  unfold granContent
  rw [integral_const_mul, integral_of_hasLaw (hasLaw_gcount (granIntensity_isTiling hε) hC
    (tileBounded_ecube hCb)), ENNReal.coe_toNNReal_eq_toReal, granIntensity_toReal hε]
  have : (2 * ε) ^ d ≠ 0 := by positivity
  field_simp

/-- **Poisson sets, (i): variance.**  `Var μ_Π(C) = (2ε)^d leb(C)`. -/
theorem poisson_content_variance {ε : ℝ} (hε : 0 < ε) {C : Set (EuclideanSpace ℝ (Fin d))}
    (hC : MeasurableSet C) (hCb : Bornology.IsBounded C) :
    variance (granContent d ε C) (globalProcess (granIntensity d ε) ecube) =
      (2 * ε) ^ d * (volume C).toReal := by
  unfold granContent
  rw [variance_const_mul, variance_of_hasLaw (hasLaw_gcount (granIntensity_isTiling hε) hC
    (tileBounded_ecube hCb)), ENNReal.coe_toNNReal_eq_toReal, granIntensity_toReal hε]
  have : (2 * ε) ^ d ≠ 0 := by positivity
  field_simp

/-- **Poisson sets: the law of the whole process is invariant under rigid motions** (the mapping
theorem, since rigid motions preserve Lebesgue measure). -/
theorem poisson_rigid_invariant {ε : ℝ} (hε : 0 < ε)
    (g : EuclideanSpace ℝ (Fin d) ≃ᵢ EuclideanSpace ℝ (Fin d)) :
    (poissonLaw (granIntensity d ε) ecube).map (fun ν => ν.map g) =
      poissonLaw (granIntensity d ε) ecube := by
  refine poissonLaw_map (granIntensity_isTiling hε) ?_ ?_
  · have h := IsometryEquiv.measurePreserving_volume g
    refine ⟨h.measurable, ?_⟩
    rw [Measure.map_smul, h.map_eq]
    exact h.measurable.aemeasurable
  · intro B _ hB
    refine tileBounded_ecube ?_
    have hb := isBounded_of_tileBounded_ecube hB
    rw [show (g : EuclideanSpace ℝ (Fin d) → _) ⁻¹' B = g.symm '' B by
      rw [isometry_image_eq, IsometryEquiv.symm_symm]]
    exact g.symm.isometry.lipschitz.isBounded_image hb

/-! ### Poisson sets: no repeated difference vectors -/

/-- The position of the `i`-th point of a configuration (`0` if there is none). -/
def posc (c : Config (EuclideanSpace ℝ (Fin d))) (i : ℕ) : EuclideanSpace ℝ (Fin d) :=
  if h : i < c.1 then c.2 ⟨i, h⟩ else 0

theorem measurable_posc (i : ℕ) :
    Measurable fun c : Config (EuclideanSpace ℝ (Fin d)) => posc c i := by
  rw [measurable_config_iff]
  intro n
  by_cases h : i < n
  · have : ((fun c : Config (EuclideanSpace ℝ (Fin d)) => posc c i) ∘ cfg n) =
        fun x => x ⟨i, h⟩ := by ext1 x; simp [posc, cfg, h]
    rw [this]; exact measurable_pi_apply _
  · have : ((fun c : Config (EuclideanSpace ℝ (Fin d)) => posc c i) ∘ cfg n) = fun _ => 0 := by
      ext1 x; simp [posc, cfg, h]
    rw [this]; exact measurable_const

/-- A coordinate of a product of atomless measures is a.s. not a function of the others. -/
theorem pi_coord_eq_null {n : ℕ} (μ : Measure (EuclideanSpace ℝ (Fin d))) [SigmaFinite μ]
    (hμ : ∀ p, μ {p} = 0) (i : Fin n) (G : (Fin n → EuclideanSpace ℝ (Fin d)) → EuclideanSpace ℝ (Fin d))
    (hG : Measurable G) (hinv : ∀ x e, G (Function.update x i e) = G x) :
    (Measure.pi fun _ : Fin n => μ) {x | x i = G x} = 0 := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by have := i.2; omega⟩
  have hmp := measurePreserving_piFinSuccAbove (fun _ : Fin (m + 1) => μ) i
  set G' : (Fin m → EuclideanSpace ℝ (Fin d)) → EuclideanSpace ℝ (Fin d) :=
    fun w => G (Fin.insertNth i 0 w) with hG'
  have hG'm : Measurable G' := hG.comp (by
    have : Measurable fun w : Fin m → EuclideanSpace ℝ (Fin d) => (Fin.insertNth i 0 w :
        Fin (m + 1) → EuclideanSpace ℝ (Fin d)) := by
      refine measurable_pi_iff.2 fun j => ?_
      refine Fin.succAboveCases i ?_ (fun k => ?_) j
      · simp only [Fin.insertNth_apply_same]; exact measurable_const
      · simp only [Fin.insertNth_apply_succAbove]; exact measurable_pi_apply k
    exact this)
  have hset : {x : Fin (m + 1) → EuclideanSpace ℝ (Fin d) | x i = G x} =
      (MeasurableEquiv.piFinSuccAbove (fun _ => EuclideanSpace ℝ (Fin d)) i) ⁻¹'
        {p | p.1 = G' p.2} := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_preimage, MeasurableEquiv.piFinSuccAbove_apply,
      Fin.insertNthEquiv_symm_apply, hG']
    rw [Fin.insertNth_removeNth, hinv]
  have hSm : MeasurableSet {p : EuclideanSpace ℝ (Fin d) × (Fin m → EuclideanSpace ℝ (Fin d)) |
      p.1 = G' p.2} := measurableSet_eq_fun measurable_fst (hG'm.comp measurable_snd)
  rw [hset, hmp.measure_preimage hSm.nullMeasurableSet, Measure.prod_apply_symm hSm]
  simp only [Set.preimage_setOf_eq]
  have : ∀ y, {x : EuclideanSpace ℝ (Fin d) | x = G' y} = {G' y} := fun y => rfl
  simp_rw [this, hμ, lintegral_zero]

theorem poissonProcess_posc_null (ν : Measure (EuclideanSpace ℝ (Fin d))) [IsFiniteMeasure ν]
    (hν0 : ν Set.univ ≠ 0) (hνa : ∀ p, ν {p} = 0) (i : ℕ)
    (F : Config (EuclideanSpace ℝ (Fin d)) → EuclideanSpace ℝ (Fin d)) (hF : Measurable F)
    (hinv : ∀ (n : ℕ) (x : Fin n → EuclideanSpace ℝ (Fin d)) (h : i < n) e,
      F (cfg n (Function.update x ⟨i, h⟩ e)) = F (cfg n x)) :
    poissonProcess ν {c | i < c.1 ∧ posc c i = F c} = 0 := by
  haveI := isProbabilityMeasure_unif ν hν0
  rw [poissonProcess_apply]
  refine ENNReal.tsum_eq_zero.2 fun n => ?_
  by_cases h : i < n
  · have : cfg n ⁻¹' {c : Config (EuclideanSpace ℝ (Fin d)) | i < c.1 ∧ posc c i = F c} =
        {x | x ⟨i, h⟩ = F (cfg n x)} := by
      ext x; simp [posc, cfg, h]
    rw [this, pi_coord_eq_null (unif ν) (fun p => by simp [unif, hνa]) ⟨i, h⟩
      (fun x => F (cfg n x)) (hF.comp (measurable_mk n)) (fun x e => hinv n x h e), mul_zero]
  · have : cfg n ⁻¹' {c : Config (EuclideanSpace ℝ (Fin d)) | i < c.1 ∧ posc c i = F c} = ∅ := by
      ext x; simp [cfg, h]
    rw [this, measure_empty, mul_zero]

/-- The points of the Poisson set: the points of each tile's configuration lying in the tile. -/
def points (ω : (Fin d → ℤ) → Config (EuclideanSpace ℝ (Fin d))) : Set (EuclideanSpace ℝ (Fin d)) :=
  {p | ∃ z, ∃ i : Fin (ω z).1, (ω z).2 i = p ∧ p ∈ ecube z}

/-- The position of the point with index `I = (tile, number)`. -/
def gpos (ω : (Fin d → ℤ) → Config (EuclideanSpace ℝ (Fin d))) (I : (Fin d → ℤ) × ℕ) :
    EuclideanSpace ℝ (Fin d) := posc (ω I.1) I.2

/-- The signs of `x₁ - x₂ - x₃ + x₄`. -/
def sgn4 : Fin 4 → ℝ := ![1, -1, -1, 1]

/-- The total coefficient of the index `J` in `x_{I₁} - x_{I₂} - x_{I₃} + x_{I₄}`. -/
def coef4 {ι : Type*} [DecidableEq ι] (I : Fin 4 → ι) (J : ι) : ℝ :=
  ∑ a, if I a = J then sgn4 a else 0

theorem exists_coef4_ne {ι : Type*} [DecidableEq ι] (I : Fin 4 → ι) (h01 : I 0 ≠ I 1)
    (h23 : I 2 ≠ I 3) (hp : (I 0, I 1) ≠ (I 2, I 3)) : ∃ a, coef4 I (I a) ≠ 0 := by
  by_cases h20 : I 2 = I 0
  · refine ⟨1, ?_⟩
    have h31 : I 3 ≠ I 1 := by
      intro h; apply hp; rw [h20, h]
    have h21 : I 2 ≠ I 1 := by rw [h20]; exact h01
    simp only [coef4, Fin.sum_univ_four, sgn4, if_pos rfl, if_neg h01, if_neg h21, if_neg h31]
    norm_num
  · refine ⟨0, ?_⟩
    simp only [coef4, Fin.sum_univ_four, sgn4, if_pos rfl, if_neg (Ne.symm h01), if_neg h20]
    by_cases h30 : I 3 = I 0
    · rw [if_pos h30]; norm_num
    · rw [if_neg h30]; norm_num

theorem sum_sgn4_split {ι E : Type*} [DecidableEq ι] [AddCommGroup E] [Module ℝ E]
    (I : Fin 4 → ι) (J : ι) (v : ι → E) :
    ∑ a, sgn4 a • v (I a) = coef4 I J • v J + ∑ a, (if I a = J then 0 else sgn4 a • v (I a)) := by
  rw [coef4, Finset.sum_smul, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun a _ => ?_
  by_cases h : I a = J
  · simp [h]
  · simp [h]

/-- **Poisson sets, (iii): no repeated difference vectors.**  Almost surely, for points
`p₁ ≠ p₂`, `p₃ ≠ p₄` of the Poisson set with `(p₁, p₂) ≠ (p₃, p₄)`, `p₁ - p₂ ≠ p₃ - p₄`. -/
theorem poisson_distinct_differences (hd : 1 ≤ d) {ε : ℝ} (hε : 0 < ε) :
    ∀ᵐ ω ∂(globalProcess (granIntensity d ε) ecube),
      ∀ p₁ ∈ points ω, ∀ p₂ ∈ points ω, ∀ p₃ ∈ points ω, ∀ p₄ ∈ points ω,
        p₁ ≠ p₂ → p₃ ≠ p₄ → (p₁, p₂) ≠ (p₃, p₄) → p₁ - p₂ ≠ p₃ - p₄ := by
  classical
  haveI : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
  set P := globalProcess (granIntensity d ε) ecube with hP
  have ht := granIntensity_isTiling (d := d) hε
  -- the events of an index quadruple
  set E : (Fin 4 → (Fin d → ℤ) × ℕ) → Set ((Fin d → ℤ) → Config (EuclideanSpace ℝ (Fin d))) :=
    fun I => {ω | (∀ a, (I a).2 < (ω (I a).1).1) ∧ ∑ a, sgn4 a • gpos ω (I a) = 0} with hE
  have key : ∀ I : Fin 4 → (Fin d → ℤ) × ℕ, I 0 ≠ I 1 → I 2 ≠ I 3 → (I 0, I 1) ≠ (I 2, I 3) →
      P (E I) = 0 := by
    intro I h01 h23 hp
    obtain ⟨a₀, ha₀⟩ := exists_coef4_ne I h01 h23 hp
    set J := I a₀ with hJ
    set κ := coef4 I J with hκ
    set zs := J.1 with hzs
    set is := J.2 with his
    set T4 : Finset (Fin d → ℤ) := Finset.univ.image fun b => (I b).1 with hT4
    set T4' := T4.erase zs with hT4'
    set X : ((Fin d → ℤ) → Config (EuclideanSpace ℝ (Fin d))) → Config (EuclideanSpace ℝ (Fin d)) :=
      fun ω => ω zs with hX
    set Y : ((Fin d → ℤ) → Config (EuclideanSpace ℝ (Fin d))) → (T4' → Config (EuclideanSpace ℝ (Fin d))) :=
      fun ω z => ω z with hY
    set posAt : Config (EuclideanSpace ℝ (Fin d)) × (T4' → Config (EuclideanSpace ℝ (Fin d))) →
        (Fin d → ℤ) × ℕ → EuclideanSpace ℝ (Fin d) :=
      fun q K => if h : K.1 ∈ T4' then posc (q.2 ⟨K.1, h⟩) K.2 else posc q.1 K.2 with hposAt
    set F : Config (EuclideanSpace ℝ (Fin d)) × (T4' → Config (EuclideanSpace ℝ (Fin d))) →
        EuclideanSpace ℝ (Fin d) :=
      fun q => -κ⁻¹ • ∑ b, (if I b = J then 0 else sgn4 b • posAt q (I b)) with hF
    have hposAtm : ∀ K, Measurable fun q : Config (EuclideanSpace ℝ (Fin d)) ×
        (T4' → Config (EuclideanSpace ℝ (Fin d))) => posAt q K := by
      intro K
      simp only [hposAt]
      split_ifs with h
      · exact (measurable_posc _).comp ((measurable_pi_apply _).comp measurable_snd)
      · exact (measurable_posc _).comp measurable_fst
    have hRm : Measurable fun q : Config (EuclideanSpace ℝ (Fin d)) ×
        (T4' → Config (EuclideanSpace ℝ (Fin d))) =>
          ∑ b, (if I b = J then (0 : EuclideanSpace ℝ (Fin d)) else sgn4 b • posAt q (I b)) := by
      refine Finset.measurable_sum (f := fun b q => if I b = J then (0 : EuclideanSpace ℝ (Fin d))
        else sgn4 b • posAt q (I b)) _ fun b _ => ?_
      by_cases hb : I b = J
      · simp only [hb, if_true]; exact measurable_const
      · simp only [hb, if_false]; exact (hposAtm (I b)).const_smul (sgn4 b)
    have hFm : Measurable F := (measurable_const (a := -κ⁻¹)).smul hRm
    set S : Set (Config (EuclideanSpace ℝ (Fin d)) × (T4' → Config (EuclideanSpace ℝ (Fin d)))) :=
      {q | is < q.1.1 ∧ posc q.1 is = F q} with hS
    have hlen : Measurable fun c : Config (EuclideanSpace ℝ (Fin d)) => c.1 := by
      rw [measurable_config_iff]; intro n; exact measurable_const
    have hSm : MeasurableSet S :=
      (measurableSet_lt measurable_const (hlen.comp measurable_fst)).inter
        (measurableSet_eq_fun ((measurable_posc _).comp measurable_fst) hFm)
    -- the event is contained in the preimage of `S`
    have hsub : E I ⊆ (fun ω => (X ω, Y ω)) ⁻¹' S := by
      rintro ω ⟨hlt, hsum⟩
      have hmatch : ∀ b, gpos ω (I b) = posAt (X ω, Y ω) (I b) := by
        intro b
        simp only [hposAt, gpos, hX, hY]
        split_ifs with h
        · rfl
        · have hb : (I b).1 ∈ T4 := Finset.mem_image.2 ⟨b, Finset.mem_univ _, rfl⟩
          have : (I b).1 = zs := by
            by_contra hne; exact h (Finset.mem_erase.2 ⟨hne, hb⟩)
          rw [this]
      refine ⟨hlt a₀, ?_⟩
      rw [sum_sgn4_split I J] at hsum
      simp_rw [hmatch] at hsum
      have hκ0 : κ ≠ 0 := ha₀
      simp only [hF]
      have : gpos ω J = -κ⁻¹ • ∑ b, (if I b = J then 0 else sgn4 b • posAt (X ω, Y ω) (I b)) := by
        have h2 := congrArg (fun v => κ⁻¹ • v) hsum
        simp only [smul_add, smul_zero, smul_smul] at h2
        rw [← hκ, inv_mul_cancel₀ hκ0, one_smul] at h2
        rw [neg_smul, eq_neg_iff_add_eq_zero]; exact h2
      exact this
    -- independence of the tile `zs` and the other tiles
    have hindep : ProbabilityTheory.IndepFun X Y P := by
      have h := ProbabilityTheory.iIndepFun_infinitePi
        (P := fun z => safeProc (granIntensity d ε |>.restrict (ecube z)))
        (X := fun _ c => c) (fun _ => measurable_id)
      have h2 := h.indepFun_finset {zs} T4' (by simp [hT4']) (fun _ => measurable_pi_apply _)
      have hev : Measurable fun f : ({zs} : Finset (Fin d → ℤ)) → Config (EuclideanSpace ℝ (Fin d)) =>
          f ⟨zs, Finset.mem_singleton_self _⟩ := measurable_pi_apply _
      exact h2.comp (φ := fun f => f ⟨zs, Finset.mem_singleton_self _⟩)
        (ψ := id) hev measurable_id
    have hXm : Measurable X := measurable_pi_apply _
    have hYm : Measurable Y := measurable_pi_iff.2 fun z => measurable_pi_apply _
    have hlawX : P.map X = poissonProcess ((granIntensity d ε).restrict (ecube zs)) := by
      rw [hP, globalProcess, hX]
      rw [show (fun ω : (Fin d → ℤ) → Config (EuclideanSpace ℝ (Fin d)) => ω zs) =
        Function.eval zs from rfl, Measure.infinitePi_map_eval, safeProc_tile ht]
    refine measure_mono_null hsub ?_
    rw [← Measure.map_apply (hXm.prodMk hYm) hSm,
      (ProbabilityTheory.indepFun_iff_map_prod_eq_prod_map_map hXm.aemeasurable
        hYm.aemeasurable).1 hindep, Measure.prod_apply_symm hSm]
    rw [hlawX]
    refine (lintegral_congr fun y => ?_).trans lintegral_zero
    haveI := isFiniteMeasure_tile ht zs
    have hsl : (fun x => (x, y)) ⁻¹' S =
        {c | is < c.1 ∧ posc c is = (fun c => F (c, y)) c} := rfl
    rw [hsl]
    refine poissonProcess_posc_null _ (restrict_tile_univ_ne_zero ht zs) (fun p => ?_) is
      (fun c => F (c, y)) (hFm.comp (measurable_id.prodMk measurable_const)) ?_
    · refine le_antisymm (le_trans (Measure.restrict_apply_le _ _) ?_) zero_le
      rw [Measure.smul_apply, measure_singleton, smul_zero]
    · intro n x h e
      have hpa : ∀ b, I b ≠ J → posAt (cfg n (Function.update x ⟨is, h⟩ e), y) (I b) =
          posAt (cfg n x, y) (I b) := by
        intro b hb
        by_cases hm : (I b).1 ∈ T4'
        · simp only [hposAt, dif_pos hm]
        · simp only [hposAt, dif_neg hm]
          have hbT : (I b).1 ∈ T4 := Finset.mem_image.2 ⟨b, Finset.mem_univ _, rfl⟩
          have h1 : (I b).1 = zs := by
            by_contra hne; exact hm (Finset.mem_erase.2 ⟨hne, hbT⟩)
          have h2 : (I b).2 ≠ is := by
            intro h2; exact hb (Prod.ext h1 h2)
          unfold posc
          by_cases h3 : (I b).2 < n
          · rw [dif_pos h3, dif_pos h3]
            show Function.update x ⟨is, h⟩ e ⟨(I b).2, h3⟩ = x ⟨(I b).2, h3⟩
            rw [Function.update_of_ne]
            intro h4; exact h2 (congrArg Fin.val h4)
          · rw [dif_neg h3, dif_neg h3]
      show -κ⁻¹ • ∑ b, (if I b = J then 0 else sgn4 b • posAt (cfg n (Function.update x ⟨is, h⟩ e), y) (I b)) =
        -κ⁻¹ • ∑ b, (if I b = J then 0 else sgn4 b • posAt (cfg n x, y) (I b))
      refine congrArg _ (Finset.sum_congr rfl fun b _ => ?_)
      by_cases hb : I b = J
      · rw [if_pos hb, if_pos hb]
      · rw [if_neg hb, if_neg hb, hpa b hb]
  -- the bad event is covered by the events of index quadruples
  have hcover : {ω | ¬ ∀ p₁ ∈ points ω, ∀ p₂ ∈ points ω, ∀ p₃ ∈ points ω, ∀ p₄ ∈ points ω,
      p₁ ≠ p₂ → p₃ ≠ p₄ → (p₁, p₂) ≠ (p₃, p₄) → p₁ - p₂ ≠ p₃ - p₄} ⊆
      ⋃ I : Fin 4 → (Fin d → ℤ) × ℕ,
        if I 0 ≠ I 1 ∧ I 2 ≠ I 3 ∧ (I 0, I 1) ≠ (I 2, I 3) then E I else ∅ := by
    intro ω hω
    simp only [Set.mem_setOf_eq, not_forall, exists_prop, not_not] at hω
    obtain ⟨p₁, ⟨z₁, i₁, rfl, -⟩, p₂, ⟨z₂, i₂, rfl, -⟩, p₃, ⟨z₃, i₃, rfl, -⟩, p₄,
      ⟨z₄, i₄, rfl, -⟩, h12, h34, hp, heq⟩ := hω
    set I : Fin 4 → (Fin d → ℤ) × ℕ := ![(z₁, i₁.1), (z₂, i₂.1), (z₃, i₃.1), (z₄, i₄.1)] with hI
    have hg : ∀ (z : Fin d → ℤ) (i : Fin (ω z).1), gpos ω (z, i.1) = (ω z).2 i := by
      intro z i; simp [gpos, posc, i.2]
    have hne : ∀ (z z' : Fin d → ℤ) (i : Fin (ω z).1) (i' : Fin (ω z').1),
        (ω z).2 i ≠ (ω z').2 i' → (z, i.1) ≠ (z', i'.1) := by
      intro z z' i i' h he
      apply h
      rw [← hg, ← hg, he]
    refine Set.mem_iUnion.2 ⟨I, ?_⟩
    have c1 : I 0 ≠ I 1 := hne _ _ _ _ h12
    have c2 : I 2 ≠ I 3 := hne _ _ _ _ h34
    have hI0 : I 0 = (z₁, i₁.1) := rfl
    have hI1 : I 1 = (z₂, i₂.1) := rfl
    have hI2 : I 2 = (z₃, i₃.1) := rfl
    have hI3 : I 3 = (z₄, i₄.1) := rfl
    have c3 : (I 0, I 1) ≠ (I 2, I 3) := by
      intro h
      apply hp
      have h0 : gpos ω (I 0) = gpos ω (I 2) := congrArg (gpos ω) (congrArg Prod.fst h)
      have h1 : gpos ω (I 1) = gpos ω (I 3) := congrArg (gpos ω) (congrArg Prod.snd h)
      rw [hI0, hI2, hg, hg] at h0
      rw [hI1, hI3, hg, hg] at h1
      rw [h0, h1]
    rw [if_pos ⟨c1, c2, c3⟩]
    refine ⟨fun a => ?_, ?_⟩
    · fin_cases a
      · exact i₁.2
      · exact i₂.2
      · exact i₃.2
      · exact i₄.2
    · rw [Fin.sum_univ_four, hI0, hI1, hI2, hI3, hg, hg, hg, hg]
      have s0 : sgn4 0 = 1 := rfl
      have s1 : sgn4 1 = -1 := rfl
      have s2 : sgn4 2 = -1 := rfl
      have s3 : sgn4 3 = 1 := rfl
      rw [s0, s1, s2, s3, one_smul, one_smul, neg_one_smul, neg_one_smul]
      have : (ω z₁).2 i₁ - (ω z₂).2 i₂ - ((ω z₃).2 i₃ - (ω z₄).2 i₄) = 0 := by
        rw [heq, sub_self]
      rw [← this]; abel
  rw [ae_iff]
  refine measure_mono_null hcover (measure_iUnion_null fun I => ?_)
  split_ifs with h
  · exact key I h.1 h.2.1 h.2.2
  · exact measure_empty

/-- **The uniform isotropy bound is `o(ε)` for `d ≥ 3`**: `ε^{d/2} √(log(1/ε)) / ε → 0`. -/
theorem isotropy_rate_littleO (hd : 3 ≤ d) :
    Tendsto (fun ε : ℝ => Real.sqrt (ε ^ d * Real.log (1 / ε)) / ε) (𝓝[>] 0) (𝓝 0) := by
  have h1 := (tendsto_log_mul_rpow_nhdsGT_zero (r := 1) one_pos).neg
  rw [neg_zero] at h1
  have h2 : Tendsto (fun ε : ℝ => Real.sqrt (-(Real.log ε * ε ^ (1 : ℝ)))) (𝓝[>] 0) (𝓝 0) := by
    have := (Real.continuous_sqrt.tendsto 0).comp h1
    rw [Real.sqrt_zero] at this; exact this
  refine squeeze_zero' ?_ ?_ h2
  · filter_upwards [self_mem_nhdsWithin] with ε hε
    exact div_nonneg (Real.sqrt_nonneg _) (le_of_lt hε)
  · filter_upwards [self_mem_nhdsWithin, Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)]
      with ε hε0 hε1
    have hε : 0 < ε := hε0
    have hL : 0 ≤ Real.log (1 / ε) := by
      rw [one_div, Real.log_inv, neg_nonneg]; exact Real.log_nonpos hε.le hε1.2.le
    rw [Real.rpow_one, show -(Real.log ε * ε) = ε * Real.log (1 / ε) by
      rw [one_div, Real.log_inv]; ring]
    rw [div_le_iff₀ hε]
    have e : ε ^ d * Real.log (1 / ε) = ε ^ 2 * (ε ^ (d - 2) * Real.log (1 / ε)) := by
      rw [← mul_assoc, ← pow_add]; congr 2; omega
    rw [e, Real.sqrt_mul (by positivity), Real.sqrt_sq hε.le, mul_comm]
    apply mul_le_mul_of_nonneg_right _ hε.le
    apply Real.sqrt_le_sqrt
    apply mul_le_mul_of_nonneg_right _ hL
    calc ε ^ (d - 2) ≤ ε ^ 1 := pow_le_pow_of_le_one hε.le hε1.2.le (by omega)
      _ = ε := pow_one ε

/-! ### Poisson sets in the plane: the normal limit of the retained term -/

theorem charFun_poisson_affine (r : ℝ≥0) (a b t : ℝ) :
    charFun ((poissonMeasure r).map fun n : ℕ => a * (n : ℝ) + b) t =
      Complex.exp (r * (Complex.exp ((a * t : ℝ) * Complex.I) - 1)) *
        Complex.exp ((b * t : ℝ) * Complex.I) := by
  have h1 : (poissonMeasure r).map (fun n : ℕ => a * (n : ℝ) + b) =
      (((poissonMeasure r).map (Nat.cast : ℕ → ℝ)).map (a * ·)).map (· + b) := by
    rw [Measure.map_map (by fun_prop) (by fun_prop), Measure.map_map (by fun_prop) (by fun_prop)]
    rfl
  rw [h1, charFun_map_add_const, charFun_map_mul, charFun_map_cast_poissonMeasure, Real.inner_apply]

/-- The cubic Taylor bound for `e^{is}`. -/
theorem exp_I_taylor (s : ℝ) (hs : |s| ≤ 1) :
    ‖Complex.exp ((s : ℂ) * Complex.I) - 1 - (s : ℂ) * Complex.I + (s : ℂ) ^ 2 / 2‖ ≤ |s| ^ 3 := by
  have hx : ‖(s : ℂ) * Complex.I‖ = |s| := by simp
  have h := Complex.exp_bound (x := (s : ℂ) * Complex.I) (by rw [hx]; exact hs) (n := 3) (by norm_num)
  rw [hx] at h
  have e : ∑ m ∈ Finset.range 3, ((s : ℂ) * Complex.I) ^ m / (m.factorial : ℂ) =
      1 + (s : ℂ) * Complex.I - (s : ℂ) ^ 2 / 2 := by
    simp [Finset.sum_range_succ, mul_pow, Complex.I_sq]; ring
  rw [e] at h
  have e2 : Complex.exp ((s : ℂ) * Complex.I) - 1 - (s : ℂ) * Complex.I + (s : ℂ) ^ 2 / 2 =
      Complex.exp ((s : ℂ) * Complex.I) - (1 + (s : ℂ) * Complex.I - (s : ℂ) ^ 2 / 2) := by ring
  rw [e2]
  refine h.trans ?_
  have : (Nat.succ 3 : ℝ) * ((Nat.factorial 3 : ℝ) * (3 : ℝ))⁻¹ ≤ 1 := by norm_num [Nat.factorial]
  calc |s| ^ 3 * ((Nat.succ 3 : ℝ) * ((Nat.factorial 3 : ℝ) * 3)⁻¹) ≤ |s| ^ 3 * 1 :=
        mul_le_mul_of_nonneg_left this (by positivity)
    _ = |s| ^ 3 := mul_one _

/-- **Poisson sets in the plane: the retained term has a normal limit.**  For `d = 2` and a
bounded Borel set `C`, as `ε → 0` (along any sequence `ε_k → 0⁺`),
`(μ_Π(C) - leb(C))/ε` converges in law to a centred normal variable with variance `4 leb(C)`. -/
theorem poisson_clt_two {ε : ℕ → ℝ} (hε : ∀ k, 0 < ε k) (hε0 : Tendsto ε atTop (𝓝 0))
    {C : Set (EuclideanSpace ℝ (Fin 2))} (hC : MeasurableSet C) (hCb : Bornology.IsBounded C)
    {Ω' : Type*} [MeasurableSpace Ω'] {P' : Measure Ω'} [IsProbabilityMeasure P'] {Y : Ω' → ℝ}
    (hY : HasLaw Y (gaussianReal 0 (4 * (volume C).toNNReal)) P') :
    TendstoInDistribution (fun k ω => (granContent 2 (ε k) C ω - (volume C).toReal) / ε k) atTop Y
      (fun k => globalProcess (granIntensity 2 (ε k)) ecube) P' := by
  set V := (volume C).toReal with hV
  have hV0 : 0 ≤ V := ENNReal.toReal_nonneg
  have hXm : ∀ k, Measurable fun ω => (granContent 2 (ε k) C ω - V) / ε k := fun k =>
    ((measurable_granContent hC).sub measurable_const).div_const _
  refine TendstoInDistribution.of_tendsto_charFun (fun k => (hXm k).aemeasurable)
    hY.aemeasurable fun t => ?_
  rw [hY.map_eq, charFun_gaussianReal]
  -- the law of the normalised content
  have hlaw : ∀ k, (globalProcess (granIntensity 2 (ε k)) ecube).map
      (fun ω => (granContent 2 (ε k) C ω - V) / ε k) =
      (poissonMeasure (granIntensity 2 (ε k) C).toNNReal).map
        (fun n : ℕ => (4 * ε k) * (n : ℝ) + (-V / ε k)) := by
    intro k
    have hl := hasLaw_gcount (granIntensity_isTiling (d := 2) (hε k)) hC (tileBounded_ecube hCb)
    rw [← hl.map_eq, Measure.map_map (by fun_prop)
      (measurable_gcount (granIntensity_isTiling (hε k)).measurableSet hC)]
    congr 1; ext1 ω
    simp only [Function.comp_apply, granContent]
    have := (hε k).ne'
    field_simp; ring
  simp_rw [hlaw, charFun_poisson_affine]
  set lam : ℕ → ℝ := fun k => (granIntensity 2 (ε k) C).toNNReal with hlam
  have hlamv : ∀ k, lam k = V / (4 * ε k ^ 2) := by
    intro k
    simp only [hlam, ENNReal.coe_toNNReal_eq_toReal, granIntensity_toReal (hε k), hV]
    rw [mul_pow]; ring
  -- combine the exponentials
  have hcomb : ∀ k, Complex.exp ((lam k : ℂ) * (Complex.exp ((4 * ε k * t : ℝ) * Complex.I) - 1)) *
      Complex.exp ((-V / ε k * t : ℝ) * Complex.I) =
      Complex.exp ((lam k : ℂ) * (Complex.exp ((4 * ε k * t : ℝ) * Complex.I) - 1 -
        ((4 * ε k * t : ℝ) : ℂ) * Complex.I)) := by
    intro k
    rw [← Complex.exp_add]
    congr 1
    have hl := hlamv k
    have hek := (hε k).ne'
    have : (lam k : ℂ) * (((4 * ε k * t : ℝ) : ℂ) * Complex.I) =
        -(((-V / ε k * t : ℝ) : ℂ) * Complex.I) := by
      rw [hl]; push_cast; field_simp
    linear_combination this
  have hcomb' : ∀ k, Complex.exp (↑↑(granIntensity 2 (ε k) C).toNNReal *
      (Complex.exp (↑(4 * ε k * t) * Complex.I) - 1)) * Complex.exp (↑(-V / ε k * t) * Complex.I) =
      Complex.exp ((lam k : ℂ) * (Complex.exp ((4 * ε k * t : ℝ) * Complex.I) - 1 -
        ((4 * ε k * t : ℝ) : ℂ) * Complex.I)) := fun k => hcomb k
  simp_rw [hcomb']
  refine Tendsto.cexp ?_
  -- the exponent tends to `-2 V t²`
  rw [show ((t : ℂ) * ((0 : ℝ) : ℂ) * Complex.I - (((4 * (volume C).toNNReal : ℝ≥0) : ℝ) : ℂ) *
      (t : ℂ) ^ 2 / 2) = ((-2 * V * t ^ 2 : ℝ) : ℂ) by
    push_cast; rw [hV]; ring]
  rw [tendsto_iff_norm_sub_tendsto_zero]
  -- the error is at most `16 V |t|³ ε_k` once `|4 ε_k t| ≤ 1`
  have hbound : ∀ᶠ k in atTop, ‖(lam k : ℂ) * (Complex.exp ((4 * ε k * t : ℝ) * Complex.I) - 1 -
      ((4 * ε k * t : ℝ) : ℂ) * Complex.I) - ((-2 * V * t ^ 2 : ℝ) : ℂ)‖ ≤
      16 * V * |t| ^ 3 * ε k := by
    have hev : ∀ᶠ k in atTop, |4 * ε k * t| ≤ 1 := by
      have : Tendsto (fun k => 4 * ε k * t) atTop (𝓝 0) := by
        simpa using (hε0.const_mul 4).mul_const t
      have := (this.abs).eventually (gt_mem_nhds (show |(0 : ℝ)| < 1 by norm_num))
      filter_upwards [this] with k hk; exact hk.le
    filter_upwards [hev] with k hk
    have htay := exp_I_taylor (4 * ε k * t) hk
    have hl := hlamv k
    have hek := hε k
    have e : (lam k : ℂ) * (Complex.exp ((4 * ε k * t : ℝ) * Complex.I) - 1 -
        ((4 * ε k * t : ℝ) : ℂ) * Complex.I) - ((-2 * V * t ^ 2 : ℝ) : ℂ) =
        (lam k : ℂ) * (Complex.exp (((4 * ε k * t : ℝ) : ℂ) * Complex.I) - 1 -
          ((4 * ε k * t : ℝ) : ℂ) * Complex.I + ((4 * ε k * t : ℝ) : ℂ) ^ 2 / 2) := by
      have hekC : (ε k : ℂ) ≠ 0 := by exact_mod_cast hek.ne'
      rw [hl]; push_cast; field_simp; ring
    rw [e, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by rw [hl]; positivity)]
    calc lam k * _ ≤ lam k * |4 * ε k * t| ^ 3 :=
          mul_le_mul_of_nonneg_left htay (by rw [hl]; positivity)
      _ = 16 * V * |t| ^ 3 * ε k := by
          rw [hl, abs_mul, abs_mul, abs_of_pos hek]; norm_num
          field_simp; ring
  have hlim : Tendsto (fun k => 16 * V * |t| ^ 3 * ε k) atTop (𝓝 0) := by
    simpa using hε0.const_mul (16 * V * |t| ^ 3)
  exact squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) hbound hlim

/-! ### Homotheties of convex bodies -/

/-- The homothety with centre `a` and ratio `s`. -/
def hom (a : EuclideanSpace ℝ (Fin d)) (s : ℝ) (x : EuclideanSpace ℝ (Fin d)) :
    EuclideanSpace ℝ (Fin d) := a + s • (x - a)

theorem hom_image_eq (a : EuclideanSpace ℝ (Fin d)) {s : ℝ} (hs : s ≠ 0)
    (D : Set (EuclideanSpace ℝ (Fin d))) : hom a s '' D = hom a s⁻¹ ⁻¹' D := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    simp only [Set.mem_preimage, hom, add_sub_cancel_left, smul_smul, inv_mul_cancel₀ hs, one_smul,
      add_sub_cancel]
    exact hx
  · intro hy
    refine ⟨hom a s⁻¹ y, hy, ?_⟩
    simp only [hom, add_sub_cancel_left, smul_smul, mul_inv_cancel₀ hs, one_smul, add_sub_cancel]

theorem measurable_hom (a : EuclideanSpace ℝ (Fin d)) (s : ℝ) : Measurable (hom a s) := by
  unfold hom; fun_prop

theorem measurableSet_hom_image (a : EuclideanSpace ℝ (Fin d)) {s : ℝ} (hs : s ≠ 0)
    {D : Set (EuclideanSpace ℝ (Fin d))} (hD : MeasurableSet D) : MeasurableSet (hom a s '' D) := by
  rw [hom_image_eq a hs]; exact measurable_hom a _ hD

theorem volume_hom_image (a : EuclideanSpace ℝ (Fin d)) {s : ℝ} (hs : 0 < s)
    (D : Set (EuclideanSpace ℝ (Fin d))) :
    volume (hom a s '' D) = ENNReal.ofReal (s ^ d) * volume D := by
  rw [hom_image_eq a hs.ne']
  have e : hom a s⁻¹ ⁻¹' D = (fun x => s⁻¹ • x) ⁻¹' ((· + (a - s⁻¹ • a)) ⁻¹' D) := by
    ext x; simp only [Set.mem_preimage, hom, smul_sub]; congr 1; abel
  rw [e, Measure.addHaar_preimage_smul volume (inv_ne_zero hs.ne'),
    measure_preimage_add_right, finrank_euclideanSpace_fin]
  congr 2
  rw [inv_pow, inv_inv, abs_of_pos (by positivity)]

theorem mem_hom_of_near {D : Set (EuclideanSpace ℝ (Fin d))} (hD : Convex ℝ D)
    {c : EuclideanSpace ℝ (Fin d)} {ρ t : ℝ} (hρ : 0 < ρ) (ht : 0 < t)
    (hball : Metric.closedBall c ρ ⊆ D) {x y : EuclideanSpace ℝ (Fin d)} (hx : x ∈ D)
    (hxy : ‖y - x‖ ≤ t * ρ) : y ∈ hom c (1 + t) '' D := by
  set w := t⁻¹ • (y - x) with hw
  have hwn : ‖w‖ ≤ ρ := by
    rw [hw, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos ht]
    rw [inv_mul_le_iff₀ ht]; exact hxy
  have hcw : c + w ∈ D := hball (by simpa [Metric.mem_closedBall, dist_eq_norm] using hwn)
  set x' := (1 + t)⁻¹ • x + (t / (1 + t)) • (c + w) with hx'
  have hx'D : x' ∈ D := hD hx hcw (by positivity) (by positivity) (by field_simp)
  refine ⟨x', hx'D, ?_⟩
  simp only [hom, hx', hw]
  have h1t : (1 + t) ≠ 0 := by positivity
  rw [smul_sub, smul_add, smul_smul, smul_smul, mul_inv_cancel₀ h1t, one_smul, smul_add,
    smul_smul]
  have : (1 + t) * (t / (1 + t)) = t := by field_simp
  rw [this, mul_inv_cancel₀ ht.ne', one_smul]
  module

theorem closedBall_subset_of_mem_hom {D : Set (EuclideanSpace ℝ (Fin d))} (hD : Convex ℝ D)
    {c : EuclideanSpace ℝ (Fin d)} {ρ t : ℝ} (ht : 0 < t) (ht1 : t ≤ 1)
    (hball : Metric.closedBall c ρ ⊆ D) {z : EuclideanSpace ℝ (Fin d)}
    (hz : z ∈ hom c (1 - t) '' D) : Metric.closedBall z (t * ρ) ⊆ D := by
  obtain ⟨x, hx, rfl⟩ := hz
  intro u hu
  rw [Metric.mem_closedBall, dist_eq_norm] at hu
  set w := t⁻¹ • (u - hom c (1 - t) x) with hw
  have hwn : ‖w‖ ≤ ρ := by
    rw [hw, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos ht, inv_mul_le_iff₀ ht]; exact hu
  have hcw : c + w ∈ D := hball (by simpa [Metric.mem_closedBall, dist_eq_norm] using hwn)
  have hu' : u = (1 - t) • x + t • (c + w) := by
    simp only [hw, hom, smul_add, smul_smul, mul_inv_cancel₀ ht.ne', one_smul]
    module
  rw [hu']
  exact hD hx hcw (by linarith) ht.le (by ring)

/-- **The sandwich.**  If two orthogonal maps are `η`-close, `C` is convex with
`B(a, ρ) ⊆ C ⊆ B(0, r₀)` and `t = η r₀ / ρ ∈ (0, 1]`, then `R C` lies between the homothetic
copies of `R' C` with ratios `1 - t` and `1 + t` about `R' a`. -/
theorem rot_sandwich {C : Set (EuclideanSpace ℝ (Fin d))} (hC : Convex ℝ C)
    {a : EuclideanSpace ℝ (Fin d)} {ρ r₀ η : ℝ} (hρ : 0 < ρ) (hball : Metric.closedBall a ρ ⊆ C)
    (hCr : C ⊆ Metric.closedBall 0 r₀) (R R' : EuclideanSpace ℝ (Fin d) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin d))
    (hRR : ∀ x, ‖R x - R' x‖ ≤ η * ‖x‖) (ht : 0 < η * r₀ / ρ) (ht1 : η * r₀ / ρ ≤ 1) :
    hom (R' a) (1 - η * r₀ / ρ) '' (R' '' C) ⊆ R '' C ∧
      R '' C ⊆ hom (R' a) (1 + η * r₀ / ρ) '' (R' '' C) := by
  set t := η * r₀ / ρ with htdef
  have htρ : t * ρ = η * r₀ := by rw [htdef]; field_simp
  have haC : a ∈ C := hball (Metric.mem_closedBall_self hρ.le)
  have hr₀ : 0 ≤ r₀ := by
    have := hCr haC; rw [Metric.mem_closedBall] at this; exact dist_nonneg.trans this
  have hηr : 0 < η * r₀ := by rw [← htρ]; positivity
  have hη : 0 ≤ η := by
    by_contra h; push_neg at h; nlinarith
  set D := R' '' C with hDdef
  have hDc : Convex ℝ D := by
    have := hC.linear_image (R'.toLinearEquiv.toLinearMap)
    simpa [hDdef] using this
  have hDball : Metric.closedBall (R' a) ρ ⊆ D := by
    intro y hy
    refine ⟨R'.symm y, hball ?_, R'.apply_symm_apply y⟩
    rw [Metric.mem_closedBall] at hy ⊢
    rw [show a = R'.symm (R' a) by simp, LinearIsometryEquiv.dist_map]; exact hy
  have hDr : ∀ z ∈ D, ‖z‖ ≤ r₀ := by
    rintro _ ⟨x, hx, rfl⟩
    have := hCr hx
    rw [Metric.mem_closedBall, dist_zero_right] at this
    rw [LinearIsometryEquiv.norm_map]; exact this
  constructor
  · intro z hz
    have hzD : z ∈ D := by
      obtain ⟨x, hx, rfl⟩ := hz
      have h := hDc hx (hDball (Metric.mem_closedBall_self hρ.le)) (a := 1 - t) (b := t)
        (by linarith) ht.le (by ring)
      convert h using 1
      simp only [hom]; module
    have hsub := closedBall_subset_of_mem_hom hDc ht ht1 hDball hz
    set u := R.symm z with hu
    have hw : R' u ∈ D := by
      apply hsub
      rw [Metric.mem_closedBall, dist_eq_norm]
      have h1 := hRR u
      rw [hu, LinearIsometryEquiv.apply_symm_apply] at h1
      rw [LinearIsometryEquiv.norm_map] at h1
      calc ‖R' u - z‖ = ‖z - R' u‖ := norm_sub_rev _ _
        _ ≤ η * ‖z‖ := by simpa [hu] using h1
        _ ≤ η * r₀ := mul_le_mul_of_nonneg_left (hDr z hzD) hη
        _ = t * ρ := htρ.symm
    obtain ⟨x, hx, hxu⟩ := hw
    have : x = u := R'.injective hxu
    refine ⟨u, this ▸ hx, ?_⟩
    rw [hu, LinearIsometryEquiv.apply_symm_apply]
  · rintro _ ⟨x, hx, rfl⟩
    refine mem_hom_of_near hDc hρ ht hDball ⟨x, hx, rfl⟩ ?_
    have := hCr hx
    rw [Metric.mem_closedBall, dist_zero_right] at this
    calc ‖R x - R' x‖ ≤ η * ‖x‖ := hRR x
      _ ≤ η * r₀ := mul_le_mul_of_nonneg_left this hη
      _ = t * ρ := htρ.symm

/-! ### A finite net of the orthogonal group -/

theorem euc_expand (x : EuclideanSpace ℝ (Fin d)) :
    x = ∑ j, x j • EuclideanSpace.single j (1 : ℝ) := by
  have := (EuclideanSpace.basisFun (Fin d) ℝ).sum_repr x
  simpa using this.symm

theorem euc_norm_le_sum_abs (v : EuclideanSpace ℝ (Fin d)) : ‖v‖ ≤ ∑ i, |v i| := by
  conv_lhs => rw [euc_expand v]
  refine (norm_sum_le _ _).trans (le_of_eq ?_)
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [norm_smul, Real.norm_eq_abs]; simp

/-- The matrix entries of a linear isometry. -/
def ent (R : EuclideanSpace ℝ (Fin d) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin d)) (i j : Fin d) : ℝ :=
  R (EuclideanSpace.single j 1) i

theorem abs_ent_le (R : EuclideanSpace ℝ (Fin d) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin d)) (i j : Fin d) :
    |ent R i j| ≤ 1 := by
  have h := PiLp.norm_apply_le (R (EuclideanSpace.single j (1 : ℝ))) i
  rw [LinearIsometryEquiv.norm_map] at h
  simpa [ent] using h

theorem norm_sub_le_of_ent (R R' : EuclideanSpace ℝ (Fin d) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin d))
    {δ : ℝ} (h : ∀ i j, |ent R i j - ent R' i j| ≤ δ) (x : EuclideanSpace ℝ (Fin d)) :
    ‖R x - R' x‖ ≤ d ^ 2 * δ * ‖x‖ := by
  have hx : R x - R' x = ∑ j, x j • (R (EuclideanSpace.single j 1) - R' (EuclideanSpace.single j 1)) := by
    conv_lhs => rw [euc_expand x]
    rw [map_sum, map_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_smul, map_smul, smul_sub]
  rw [hx]
  refine (norm_sum_le _ _).trans ?_
  have hcol : ∀ j, ‖R (EuclideanSpace.single j 1) - R' (EuclideanSpace.single j 1)‖ ≤ d * δ := by
    intro j
    refine (euc_norm_le_sum_abs _).trans ?_
    calc ∑ i, |(R (EuclideanSpace.single j 1) - R' (EuclideanSpace.single j 1)) i|
        ≤ ∑ _i : Fin d, δ := Finset.sum_le_sum fun i _ => by
          simpa [ent] using h i j
      _ = d * δ := by simp
  calc ∑ j, ‖x j • (R (EuclideanSpace.single j 1) - R' (EuclideanSpace.single j 1))‖
      ≤ ∑ _j : Fin d, ‖x‖ * (d * δ) := Finset.sum_le_sum fun j _ => by
        rw [norm_smul]
        exact mul_le_mul (PiLp.norm_apply_le x j) (hcol j) (norm_nonneg _) (norm_nonneg _)
    _ = d ^ 2 * δ * ‖x‖ := by simp; ring

open Classical in
/-- **A finite net of the orthogonal group**: for `0 < δ`, at most `(2/δ + 5)^{d²}` orthogonal maps
such that every orthogonal map is within `2 d² δ` of one of them in operator norm. -/
theorem rot_net {δ : ℝ} (hδ : 0 < δ) :
    ∃ N : Finset (EuclideanSpace ℝ (Fin d) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin d)),
      (N.card : ℝ) ≤ (2 / δ + 5) ^ (d * d) ∧
      ∀ R : EuclideanSpace ℝ (Fin d) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin d), ∃ R' ∈ N,
        ∀ x, ‖R x - R' x‖ ≤ 2 * d ^ 2 * δ * ‖x‖ := by
  set K : ℕ := ⌈1 / δ⌉₊ with hK
  set Gr : Finset (Fin d × Fin d → ℤ) :=
    Fintype.piFinset fun _ => Finset.Icc (-(K : ℤ) - 1) (K + 1) with hGr
  let good : (Fin d × Fin d → ℤ) → Prop :=
    fun g => ∃ R : EuclideanSpace ℝ (Fin d) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin d),
      ∀ i j, |ent R i j - g (i, j) * δ| ≤ δ
  let pick : (Fin d × Fin d → ℤ) → (EuclideanSpace ℝ (Fin d) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin d)) :=
    fun g => if h : good g then h.choose else LinearIsometryEquiv.refl ℝ _
  refine ⟨Gr.image pick, ?_, ?_⟩
  · refine (Nat.cast_le.2 Finset.card_image_le).trans ?_
    rw [hGr, Fintype.card_piFinset, Finset.prod_const, Finset.card_univ, Fintype.card_prod,
      Fintype.card_fin, Int.card_Icc]
    push_cast
    have hK1 : (K : ℝ) < 1 / δ + 1 := Nat.ceil_lt_add_one (by positivity)
    have : (((K : ℤ) + 1 + 1 - (-(K : ℤ) - 1)).toNat : ℝ) = 2 * K + 3 := by
      have : ((K : ℤ) + 1 + 1 - (-(K : ℤ) - 1)) = ((2 * K + 3 : ℕ) : ℤ) := by push_cast; ring
      rw [this, Int.toNat_natCast]; push_cast; ring
    rw [this]
    refine pow_le_pow_left₀ (by positivity) ?_ _
    rw [one_div] at hK1; rw [div_eq_mul_inv]; linarith
  · intro R
    set g : Fin d × Fin d → ℤ := fun p => ⌊ent R p.1 p.2 / δ⌋ with hg
    have hgood : good g := ⟨R, fun i j => by
      have h1 := Int.floor_le (ent R i j / δ)
      have h2 := Int.lt_floor_add_one (ent R i j / δ)
      rw [le_div_iff₀ hδ] at h1
      rw [div_lt_iff₀ hδ] at h2
      rw [abs_le]; simp only [hg]; constructor <;> nlinarith⟩
    have hgGr : g ∈ Gr := by
      rw [hGr, Fintype.mem_piFinset]
      intro p
      rw [Finset.mem_Icc]
      show -(K : ℤ) - 1 ≤ ⌊ent R p.1 p.2 / δ⌋ ∧ ⌊ent R p.1 p.2 / δ⌋ ≤ (K : ℤ) + 1
      have he := abs_le.1 (abs_ent_le R p.1 p.2)
      have hK1 : 1 / δ ≤ K := Nat.le_ceil _
      constructor
      · have : (-(K : ℤ) - 1 : ℤ) < ⌊ent R p.1 p.2 / δ⌋ := by
          rw [Int.lt_floor_iff]; push_cast
          have : -1 / δ ≤ ent R p.1 p.2 / δ := div_le_div_of_nonneg_right he.1 hδ.le
          rw [neg_div] at this; linarith
        exact this.le
      · have : ⌊ent R p.1 p.2 / δ⌋ ≤ (K : ℤ) := by
          rw [Int.floor_le_iff]; push_cast
          have : ent R p.1 p.2 / δ ≤ 1 / δ := div_le_div_of_nonneg_right he.2 hδ.le
          linarith
        omega
    refine ⟨pick g, Finset.mem_image_of_mem _ hgGr, fun x => ?_⟩
    have hpick : ∀ i j, |ent (pick g) i j - g (i, j) * δ| ≤ δ := by
      simp only [pick, dif_pos hgood]; exact hgood.choose_spec
    have hR := hgood
    have hRg : ∀ i j, |ent R i j - g (i, j) * δ| ≤ δ := by
      intro i j
      have h1 := Int.floor_le (ent R i j / δ)
      have h2 := Int.lt_floor_add_one (ent R i j / δ)
      rw [le_div_iff₀ hδ] at h1
      rw [div_lt_iff₀ hδ] at h2
      rw [abs_le]; simp only [hg]; constructor <;> nlinarith
    have := norm_sub_le_of_ent R (pick g) (δ := 2 * δ) (fun i j => by
      have := abs_sub_le (ent R i j) (g (i, j) * δ) (ent (pick g) i j)
      rw [abs_sub_comm (g (i, j) * δ)] at this
      linarith [hRg i j, hpick i j]) x
    linarith

/-! ### Poisson sets: uniform isotropy over the orthogonal group -/

theorem one_add_pow_sub_one_le {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (n : ℕ) :
    (1 + t) ^ n - 1 ≤ (2 ^ n - 1) * t := by
  induction n with
  | zero => simp
  | succ n ih =>
    have h2 : (1 + t) ^ n ≤ 2 ^ n := pow_le_pow_left₀ (by linarith) (by linarith) n
    rw [pow_succ, pow_succ]
    nlinarith

theorem one_sub_one_sub_pow_le {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (n : ℕ) :
    1 - (1 - t) ^ n ≤ (1 + t) ^ n - 1 := by
  have h1 := one_add_mul_le_pow (a := -t) (by linarith) n
  have h2 := one_add_mul_le_pow (a := t) (by linarith) n
  rw [show (1 : ℝ) + -t = 1 - t by ring] at h1
  nlinarith

theorem gcount_mono {Z : Type*} [Countable Z] {μ : Measure S} {Q : Z → Set S} (h : IsTiling μ Q) {A B : Set S}
    (hA : MeasurableSet A) (hB : MeasurableSet B) (htA : TileBounded Q A) (htB : TileBounded Q B)
    (hAB : A ⊆ B) (ω : Z → Config S) : gcount Q A ω ≤ gcount Q B ω := by
  have := measure_mono (μ := randomMeasure Q ω) hAB
  rw [randomMeasure_eq_gcount h hA htA, randomMeasure_eq_gcount h hB htB] at this
  exact_mod_cast this

/-- The constant of the uniform isotropy bound. -/
def isoConst (d : ℕ) (V r₀ ρ : ℝ) : ℝ :=
  8 * ((d : ℝ) ^ 3 + 1) * (2 ^ d * V + 1) * 2 ^ d + V * 2 ^ d * (2 * d ^ 2 * r₀ / ρ) + 1

theorem isoConst_pos {d : ℕ} {V r₀ ρ : ℝ} (hV : 0 ≤ V) (hr₀ : 0 < r₀) (hρ : 0 < ρ) :
    0 < isoConst d V r₀ ρ := by
  unfold isoConst; positivity

set_option maxHeartbeats 1600000 in
/-- **Uniform isotropy, at fixed `ε`.**  If `ε < 1`, `log(1/ε) ≥ 1`, `log(1/ε) ≤ (2ε)^{-d}` and
`2d²ε^d r₀/ρ ≤ 1/2`, then the probability that some orthogonal image of the convex body `C`
has `|μ_Π(RC) - leb(C)| > K √(ε^d log(1/ε))` is at most `2·7^{d²} ε`. -/
theorem poisson_uniform_bound (hd : 1 ≤ d) {C : Set (EuclideanSpace ℝ (Fin d))}
    (hCc : Convex ℝ C) (hCm : MeasurableSet C) {a : EuclideanSpace ℝ (Fin d)} {ρ r₀ : ℝ}
    (hρ : 0 < ρ) (hr₀ : 0 < r₀) (hball : Metric.closedBall a ρ ⊆ C)
    (hCr : C ⊆ Metric.closedBall 0 r₀) {ε : ℝ} (hε : 0 < ε) (hε1 : ε < 1)
    (hL1 : 1 ≤ Real.log (1 / ε)) (hLlam : Real.log (1 / ε) ≤ ((2 * ε) ^ d)⁻¹)
    (ht : 2 * d ^ 2 * ε ^ d * r₀ / ρ ≤ 1 / 2) :
    globalProcess (granIntensity d ε) ecube
        {ω | ∃ R : EuclideanSpace ℝ (Fin d) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin d),
          isoConst d (volume C).toReal r₀ ρ * Real.sqrt (ε ^ d * Real.log (1 / ε)) <
            |granContent d ε (R '' C) ω - (volume C).toReal|} ≤
      ENNReal.ofReal (2 * 7 ^ (d * d) * ε) := by
  classical
  set V := (volume C).toReal with hV
  have hV0 : 0 ≤ V := ENNReal.toReal_nonneg
  set L := Real.log (1 / ε) with hL
  set lam := ((2 * ε) ^ d)⁻¹ with hlam
  have hlam0 : 0 < lam := by positivity
  set δ := ε ^ d with hδ
  have hδ0 : 0 < δ := by positivity
  have hδ1 : δ ≤ 1 := pow_le_one₀ hε.le hε1.le
  obtain ⟨N, hNcard, hNnet⟩ := rot_net (d := d) hδ0
  set η := 2 * d ^ 2 * δ with hη
  set t := η * r₀ / ρ with htdef
  have ht' : t = 2 * d ^ 2 * ε ^ d * r₀ / ρ := by rw [htdef, hη, hδ]
  have ht0 : 0 < t := by rw [ht']; positivity
  have ht1 : t ≤ 1 / 2 := by rw [ht']; exact ht
  set K₁ := 8 * ((d : ℝ) ^ 3 + 1) * (2 ^ d * V + 1) with hK₁
  have hK₁0 : 0 < K₁ := by positivity
  set x := K₁ * Real.sqrt (lam * L) with hx
  have hx0 : 0 < x := by
    have : 0 < lam * L := mul_pos hlam0 (by linarith)
    positivity
  set P := globalProcess (granIntensity d ε) ecube with hP
  have htil := granIntensity_isTiling (d := d) hε
  -- the two homothetic bodies for each net element
  set Dp : (EuclideanSpace ℝ (Fin d) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin d)) → Set (EuclideanSpace ℝ (Fin d)) :=
    fun R' => hom (R' a) (1 + t) '' (R' '' C) with hDp
  set Dm : (EuclideanSpace ℝ (Fin d) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin d)) → Set (EuclideanSpace ℝ (Fin d)) :=
    fun R' => hom (R' a) (1 - t) '' (R' '' C) with hDm
  have himC : ∀ R' : EuclideanSpace ℝ (Fin d) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin d),
      R' '' C = R'.symm ⁻¹' C := fun R' => by
    ext y; constructor
    · rintro ⟨x, hx, rfl⟩; simpa using hx
    · intro hy; exact ⟨R'.symm y, hy, R'.apply_symm_apply y⟩
  have hmC : ∀ R' : EuclideanSpace ℝ (Fin d) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin d),
      MeasurableSet (R' '' C) := fun R' => by rw [himC]; exact R'.symm.continuous.measurable hCm
  have hvC : ∀ R' : EuclideanSpace ℝ (Fin d) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin d),
      volume (R' '' C) = volume C := fun R' => by
    rw [himC]; exact (R'.symm.measurePreserving).measure_preimage hCm.nullMeasurableSet
  have hCb : Bornology.IsBounded C := Metric.isBounded_closedBall.subset hCr
  have hbC : ∀ R' : EuclideanSpace ℝ (Fin d) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin d),
      Bornology.IsBounded (R' '' C) := fun R' => R'.lipschitzWith.isBounded_image hCb
  have hbhom : ∀ (c : EuclideanSpace ℝ (Fin d)) (s : ℝ) (D : Set (EuclideanSpace ℝ (Fin d))),
      Bornology.IsBounded D → Bornology.IsBounded (hom c s '' D) := by
    intro c s D hD
    have : LipschitzWith (‖s‖₊) (hom c s) := by
      refine LipschitzWith.of_dist_le_mul fun u v => ?_
      simp only [hom, dist_eq_norm]
      rw [show c + s • (u - c) - (c + s • (v - c)) = s • (u - v) by module, norm_smul]
      rfl
    exact this.isBounded_image hD
  have ht1' : t ≤ 1 := by linarith
  have h1mt : 0 < 1 - t := by linarith
  have hDpm : ∀ R', MeasurableSet (Dp R') := fun R' =>
    measurableSet_hom_image _ (by positivity : (1 + t) ≠ 0) (hmC R')
  have hDmm : ∀ R', MeasurableSet (Dm R') := fun R' =>
    measurableSet_hom_image _ h1mt.ne' (hmC R')
  have hDpb : ∀ R', Bornology.IsBounded (Dp R') := fun R' => hbhom _ _ _ (hbC R')
  have hDmb : ∀ R', Bornology.IsBounded (Dm R') := fun R' => hbhom _ _ _ (hbC R')
  have hint : ∀ D : Set (EuclideanSpace ℝ (Fin d)),
      ((granIntensity d ε D).toNNReal : ℝ) = lam * (volume D).toReal := by
    intro D; rw [ENNReal.coe_toNNReal_eq_toReal, granIntensity_toReal hε]
  have hmp : ∀ R', ((granIntensity d ε (Dp R')).toNNReal : ℝ) = lam * ((1 + t) ^ d * V) := by
    intro R'
    rw [hint, volume_hom_image _ (by positivity) _, hvC, ENNReal.toReal_mul,
      ENNReal.toReal_ofReal (by positivity)]
  have hmm : ∀ R', ((granIntensity d ε (Dm R')).toNNReal : ℝ) = lam * ((1 - t) ^ d * V) := by
    intro R'
    rw [hint, volume_hom_image _ h1mt _, hvC, ENNReal.toReal_mul,
      ENNReal.toReal_ofReal (by positivity)]
  -- the events of the net
  set Ep := fun R' : EuclideanSpace ℝ (Fin d) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin d) =>
    {ω | ((granIntensity d ε (Dp R')).toNNReal : ℝ) + x ≤ (gcount ecube (Dp R') ω : ℝ)} with hEp
  set Em := fun R' : EuclideanSpace ℝ (Fin d) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin d) =>
    {ω | (gcount ecube (Dm R') ω : ℝ) ≤ ((granIntensity d ε (Dm R')).toNNReal : ℝ) - x} with hEm
  -- the exponential bound
  have hexp : ∀ m : ℝ, 0 ≤ m → m ≤ lam * (2 ^ d * V) →
      Real.exp (-x ^ 2 / (4 * (m + x))) ≤ ε ^ (d * d * d + 1) := by
    intro m hm0 hm
    have hlamL : 0 ≤ lam * L := mul_nonneg hlam0.le (by linarith)
    have hx2 : x ^ 2 = K₁ ^ 2 * (lam * L) := by rw [hx, mul_pow, Real.sq_sqrt hlamL]
    have hsq : Real.sqrt (lam * L) ≤ lam := by
      rw [Real.sqrt_le_left hlam0.le]; nlinarith
    have hxle : x ≤ K₁ * lam := mul_le_mul_of_nonneg_left hsq hK₁0.le
    have hd3 : (1 : ℝ) ≤ 8 * ((d : ℝ) ^ 3 + 1) := by
      have := pow_nonneg (Nat.cast_nonneg d : (0 : ℝ) ≤ d) 3; linarith
    have hA0 : 0 ≤ 2 ^ d * V := by positivity
    have hVK : 2 ^ d * V ≤ K₁ := by
      rw [hK₁]
      calc 2 ^ d * V ≤ 2 ^ d * V + 1 := by linarith
        _ = 1 * (2 ^ d * V + 1) := by ring
        _ ≤ 8 * ((d : ℝ) ^ 3 + 1) * (2 ^ d * V + 1) :=
          mul_le_mul_of_nonneg_right hd3 (by linarith)
    have hmK : m ≤ lam * K₁ := hm.trans (mul_le_mul_of_nonneg_left hVK hlam0.le)
    have hden : 4 * (m + x) ≤ 8 * lam * K₁ := by linarith
    have hden0 : 0 < 4 * (m + x) := by positivity
    have hkey : ((d : ℝ) ^ 3 + 1) * L ≤ x ^ 2 / (4 * (m + x)) := by
      rw [le_div_iff₀ hden0, hx2]
      have h8 : ((d : ℝ) ^ 3 + 1) * 8 ≤ K₁ := by
        rw [hK₁]
        calc ((d : ℝ) ^ 3 + 1) * 8 = 8 * ((d : ℝ) ^ 3 + 1) * 1 := by ring
          _ ≤ 8 * ((d : ℝ) ^ 3 + 1) * (2 ^ d * V + 1) :=
            mul_le_mul_of_nonneg_left (by linarith) (by positivity)
      have hL0 : 0 ≤ L := by linarith
      calc ((d : ℝ) ^ 3 + 1) * L * (4 * (m + x)) ≤ ((d : ℝ) ^ 3 + 1) * L * (8 * lam * K₁) :=
            mul_le_mul_of_nonneg_left hden (by positivity)
        _ = (((d : ℝ) ^ 3 + 1) * 8) * K₁ * (lam * L) := by ring
        _ ≤ K₁ * K₁ * (lam * L) := by
            apply mul_le_mul_of_nonneg_right _ hlamL
            exact mul_le_mul_of_nonneg_right h8 hK₁0.le
        _ = K₁ ^ 2 * (lam * L) := by ring
    have hlog : L = -Real.log ε := by rw [hL, one_div, Real.log_inv]
    calc Real.exp (-x ^ 2 / (4 * (m + x))) ≤ Real.exp (-(((d : ℝ) ^ 3 + 1) * L)) := by
          apply Real.exp_le_exp.2; rw [neg_div]; linarith
      _ = ε ^ (d * d * d + 1) := by
          rw [hlog, show -(((d : ℝ) ^ 3 + 1) * -Real.log ε) =
            ((d * d * d + 1 : ℕ) : ℝ) * Real.log ε by push_cast; ring,
            Real.exp_nat_mul, Real.exp_log hε]
  have hpow2 : (1 + t) ^ d ≤ 2 ^ d := pow_le_pow_left₀ (by linarith) (by linarith) d
  have hpowm : (1 - t) ^ d ≤ 2 ^ d := pow_le_pow_left₀ h1mt.le (by linarith) d
  have hPp : ∀ R', P (Ep R') ≤ ENNReal.ofReal (ε ^ (d * d * d + 1)) := by
    intro R'
    refine (poisson_upper_tail (hasLaw_gcount htil (hDpm R') (tileBounded_ecube (hDpb R'))) hx0).trans
      (ENNReal.ofReal_le_ofReal (hexp _ (by positivity) ?_))
    rw [hmp]; exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hpow2 hV0) hlam0.le
  have hPm : ∀ R', P (Em R') ≤ ENNReal.ofReal (ε ^ (d * d * d + 1)) := by
    intro R'
    refine (poisson_lower_tail (hasLaw_gcount htil (hDmm R') (tileBounded_ecube (hDmb R'))) hx0).trans
      (ENNReal.ofReal_le_ofReal (hexp _ (by positivity) ?_))
    rw [hmm]; exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hpowm hV0) hlam0.le
  -- the bad event lies in the union of the events of the net
  have hsub : {ω | ∃ R : EuclideanSpace ℝ (Fin d) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin d),
      isoConst d V r₀ ρ * Real.sqrt (ε ^ d * L) < |granContent d ε (R '' C) ω - V|} ⊆
      ⋃ R' ∈ N, (Ep R' ∪ Em R') := by
    rintro ω ⟨R, hR⟩
    by_contra hω
    simp only [Set.mem_iUnion, Set.mem_union, exists_prop, not_exists, not_and, not_or] at hω
    obtain ⟨R', hR'N, hRR'⟩ := hNnet R
    have hRR : ∀ y, ‖R y - R' y‖ ≤ η * ‖y‖ := hRR'
    obtain ⟨hω1, hω2⟩ := hω R' hR'N
    simp only [hEp, hEm, Set.mem_setOf_eq, not_le] at hω1 hω2
    rw [hmp] at hω1; rw [hmm] at hω2
    obtain ⟨hin, hout⟩ := rot_sandwich hCc hρ hball hCr R R' hRR (by rw [← htdef]; exact ht0)
      (by rw [← htdef]; exact ht1')
    rw [← htdef] at hin hout
    have hRm : MeasurableSet (R '' C) := hmC R
    have hRb := hbC R
    have h1 := gcount_mono htil (hDmm R') hRm (tileBounded_ecube (hDmb R'))
      (tileBounded_ecube hRb) hin ω
    have h2 := gcount_mono htil hRm (hDpm R') (tileBounded_ecube hRb)
      (tileBounded_ecube (hDpb R')) hout ω
    set n := (gcount ecube (R '' C) ω : ℝ) with hn
    have h1' : (gcount ecube (Dm R') ω : ℝ) ≤ n := by rw [hn]; exact_mod_cast h1
    have h2' : n ≤ (gcount ecube (Dp R') ω : ℝ) := by rw [hn]; exact_mod_cast h2
    -- `|n - λV| ≤ x + λ V 2^d t`
    have hb1 := one_add_pow_sub_one_le ht0.le ht1' d
    have hb2 := one_sub_one_sub_pow_le ht0.le ht1' d
    have h2d : (2 : ℝ) ^ d - 1 ≤ 2 ^ d := by linarith
    have hgrow : (1 + t) ^ d - 1 ≤ 2 ^ d * t := hb1.trans (mul_le_mul_of_nonneg_right h2d ht0.le)
    have habs : |n - lam * V| ≤ x + lam * (V * (2 ^ d * t)) := by
      rw [abs_le]; constructor
      · have : lam * V - n < lam * V - lam * ((1 - t) ^ d * V) + x := by linarith
        have e : lam * V - lam * ((1 - t) ^ d * V) = lam * V * (1 - (1 - t) ^ d) := by ring
        have : lam * V * (1 - (1 - t) ^ d) ≤ lam * (V * (2 ^ d * t)) := by
          calc lam * V * (1 - (1 - t) ^ d) ≤ lam * V * ((1 + t) ^ d - 1) :=
                mul_le_mul_of_nonneg_left hb2 (by positivity)
            _ ≤ lam * V * (2 ^ d * t) := mul_le_mul_of_nonneg_left hgrow (by positivity)
            _ = lam * (V * (2 ^ d * t)) := by ring
        linarith
      · have : n - lam * V < lam * ((1 + t) ^ d * V) + x - lam * V := by linarith
        have : lam * ((1 + t) ^ d * V) - lam * V ≤ lam * (V * (2 ^ d * t)) := by
          have e : lam * ((1 + t) ^ d * V) - lam * V = lam * V * ((1 + t) ^ d - 1) := by ring
          rw [e]
          calc lam * V * ((1 + t) ^ d - 1) ≤ lam * V * (2 ^ d * t) :=
                mul_le_mul_of_nonneg_left hgrow (by positivity)
            _ = lam * (V * (2 ^ d * t)) := by ring
        linarith
    -- back to the content
    have hcont : granContent d ε (R '' C) ω - V = (n - lam * V) / lam := by
      simp only [granContent, hn, hlam]; field_simp
    rw [hcont, abs_div, abs_of_pos hlam0, lt_div_iff₀ hlam0] at hR
    -- the final estimate
    have hepsL : 0 ≤ ε ^ d * L := mul_nonneg (by positivity) (by linarith)
    have hsqrt1 : x / lam ≤ K₁ * 2 ^ d * Real.sqrt (ε ^ d * L) := by
      have hlamL : 0 ≤ lam * L := mul_nonneg hlam0.le (by linarith)
      have e : Real.sqrt (lam * L) / lam = Real.sqrt (2 ^ d) * Real.sqrt (ε ^ d * L) := by
        have e1 : lam * L = lam ^ 2 * (2 ^ d * (ε ^ d * L)) := by
          rw [hlam, mul_pow]; field_simp
        rw [e1, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hlam0.le, Real.sqrt_mul (by positivity)]
        field_simp
      have h2s : Real.sqrt (2 ^ d) ≤ 2 ^ d := by
        rw [Real.sqrt_le_left (by positivity)]
        have : (1 : ℝ) ≤ 2 ^ d := one_le_pow₀ (by norm_num)
        nlinarith
      calc x / lam = K₁ * (Real.sqrt (lam * L) / lam) := by rw [hx]; ring
        _ = K₁ * (Real.sqrt (2 ^ d) * Real.sqrt (ε ^ d * L)) := by rw [e]
        _ ≤ K₁ * (2 ^ d * Real.sqrt (ε ^ d * L)) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right h2s (Real.sqrt_nonneg _)) hK₁0.le
        _ = K₁ * 2 ^ d * Real.sqrt (ε ^ d * L) := by ring
    have hsqrt2 : V * (2 ^ d * t) ≤ V * 2 ^ d * (2 * d ^ 2 * r₀ / ρ) * Real.sqrt (ε ^ d * L) := by
      have hεd : ε ^ d ≤ Real.sqrt (ε ^ d * L) := by
        rw [Real.le_sqrt (by positivity) hepsL]
        have h1 : ε ^ d ≤ 1 := pow_le_one₀ hε.le hε1.le
        have h0 : 0 ≤ ε ^ d := by positivity
        calc (ε ^ d) ^ 2 = ε ^ d * ε ^ d := sq _
          _ ≤ ε ^ d * 1 := mul_le_mul_of_nonneg_left h1 h0
          _ ≤ ε ^ d * L := mul_le_mul_of_nonneg_left hL1 h0
      rw [ht']
      have : V * (2 ^ d * (2 * d ^ 2 * ε ^ d * r₀ / ρ)) =
          V * 2 ^ d * (2 * d ^ 2 * r₀ / ρ) * ε ^ d := by ring
      rw [this]
      exact mul_le_mul_of_nonneg_left hεd (by positivity)
    have hfin : |n - lam * V| ≤ lam * (isoConst d V r₀ ρ * Real.sqrt (ε ^ d * L)) := by
      have : x + lam * (V * (2 ^ d * t)) ≤ lam * (isoConst d V r₀ ρ * Real.sqrt (ε ^ d * L)) := by
        have hxl : x = lam * (x / lam) := by field_simp
        rw [hxl, ← mul_add]
        apply mul_le_mul_of_nonneg_left _ hlam0.le
        have : isoConst d V r₀ ρ * Real.sqrt (ε ^ d * L) =
            K₁ * 2 ^ d * Real.sqrt (ε ^ d * L) + V * 2 ^ d * (2 * d ^ 2 * r₀ / ρ) *
              Real.sqrt (ε ^ d * L) + Real.sqrt (ε ^ d * L) := by
          rw [isoConst, hK₁]; ring
        rw [this]
        linarith only [hsqrt1, hsqrt2, Real.sqrt_nonneg (ε ^ d * L)]
      exact habs.trans this
    have := lt_of_lt_of_le hR hfin
    rw [mul_comm lam] at this
    exact lt_irrefl _ this
  calc P _ ≤ P (⋃ R' ∈ N, (Ep R' ∪ Em R')) := measure_mono hsub
    _ ≤ ∑ R' ∈ N, P (Ep R' ∪ Em R') := measure_biUnion_finset_le _ _
    _ ≤ ∑ R' ∈ N, (ENNReal.ofReal (ε ^ (d * d * d + 1)) + ENNReal.ofReal (ε ^ (d * d * d + 1))) :=
        Finset.sum_le_sum fun R' _ => (measure_union_le _ _).trans (add_le_add (hPp R') (hPm R'))
    _ = ENNReal.ofReal (N.card * (2 * ε ^ (d * d * d + 1))) := by
        rw [Finset.sum_const, nsmul_eq_mul, ← ENNReal.ofReal_add (by positivity) (by positivity),
          ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_natCast]; congr 2; ring
    _ ≤ ENNReal.ofReal (2 * 7 ^ (d * d) * ε) := by
        apply ENNReal.ofReal_le_ofReal
        have hc : (N.card : ℝ) ≤ 7 ^ (d * d) / ε ^ (d * d * d) := by
          refine hNcard.trans ?_
          have h7 : 2 / δ + 5 ≤ 7 / δ := by
            rw [div_add' _ _ _ hδ0.ne', div_le_div_iff_of_pos_right hδ0]; nlinarith
          calc (2 / δ + 5) ^ (d * d) ≤ (7 / δ) ^ (d * d) := pow_le_pow_left₀ (by positivity) h7 _
            _ = 7 ^ (d * d) / ε ^ (d * d * d) := by
                rw [div_pow, hδ, ← pow_mul]; ring_nf
        calc (N.card : ℝ) * (2 * ε ^ (d * d * d + 1))
            ≤ 7 ^ (d * d) / ε ^ (d * d * d) * (2 * ε ^ (d * d * d + 1)) :=
              mul_le_mul_of_nonneg_right hc (by positivity)
          _ = 2 * 7 ^ (d * d) * ε := by
              have : ε ^ (d * d * d) ≠ 0 := by positivity
              field_simp; ring

/-- **Poisson sets, (ii): uniform isotropy.**  Let `C` be a convex body,
`B(a, ρ) ⊆ C ⊆ B(0, r₀)`.  With probability tending to `1` as `ε → 0`,
`sup_{R ∈ O(d)} |μ_Π(RC) - leb(C)| ≤ K ε^{d/2} √(log(1/ε))`, with `K` depending on `C` and `d`
only (here `K = isoConst d leb(C) r₀ ρ`).  Stated as: the probability of the complementary event
tends to `0`. -/
theorem poisson_uniform_isotropy (hd : 1 ≤ d) {C : Set (EuclideanSpace ℝ (Fin d))}
    (hCc : Convex ℝ C) (hCm : MeasurableSet C) {a : EuclideanSpace ℝ (Fin d)} {ρ r₀ : ℝ}
    (hρ : 0 < ρ) (hr₀ : 0 < r₀) (hball : Metric.closedBall a ρ ⊆ C)
    (hCr : C ⊆ Metric.closedBall 0 r₀) :
    Tendsto (fun ε : ℝ => globalProcess (granIntensity d ε) ecube
        {ω | ∃ R : EuclideanSpace ℝ (Fin d) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin d),
          isoConst d (volume C).toReal r₀ ρ * Real.sqrt (ε ^ d * Real.log (1 / ε)) <
            |granContent d ε (R '' C) ω - (volume C).toReal|}) (𝓝[>] 0) (𝓝 0) := by
  have h1 : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ε ∈ Set.Ioo 0 (Real.exp (-1)) :=
    Ioo_mem_nhdsGT (Real.exp_pos _)
  have h2 : ∀ᶠ ε in 𝓝[>] (0 : ℝ), Real.log (1 / ε) ≤ ((2 * ε) ^ d)⁻¹ := by
    have hlim := (tendsto_log_mul_rpow_nhdsGT_zero (r := (d : ℝ)) (by exact_mod_cast hd)).const_mul
      (-(2 : ℝ) ^ d)
    rw [mul_zero] at hlim
    have hev := hlim.eventually (gt_mem_nhds (show (0 : ℝ) < 1 by norm_num))
    filter_upwards [hev, self_mem_nhdsWithin] with ε hε hε0
    have hε0' : 0 < ε := hε0
    rw [Real.rpow_natCast] at hε
    rw [← one_div, le_div_iff₀ (by positivity), one_div, Real.log_inv, mul_pow]
    have : -Real.log ε * (2 ^ d * ε ^ d) = -2 ^ d * (Real.log ε * ε ^ d) := by ring
    linarith
  have h3 : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 2 * d ^ 2 * ε ^ d * r₀ / ρ ≤ 1 / 2 := by
    have hc : Continuous fun ε : ℝ => 2 * d ^ 2 * ε ^ d * r₀ / ρ := by fun_prop
    have hlim : Tendsto (fun ε : ℝ => 2 * d ^ 2 * ε ^ d * r₀ / ρ) (𝓝 0) (𝓝 0) := by
      have := hc.tendsto 0
      simpa [zero_pow (by omega : d ≠ 0)] using this
    exact (hlim.mono_left nhdsWithin_le_nhds).eventually
      (ge_mem_nhds (show (0 : ℝ) < 1 / 2 by norm_num))
  have hbound : ∀ᶠ ε in 𝓝[>] (0 : ℝ), globalProcess (granIntensity d ε) ecube
        {ω | ∃ R : EuclideanSpace ℝ (Fin d) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin d),
          isoConst d (volume C).toReal r₀ ρ * Real.sqrt (ε ^ d * Real.log (1 / ε)) <
            |granContent d ε (R '' C) ω - (volume C).toReal|} ≤
        ENNReal.ofReal (2 * 7 ^ (d * d) * ε) := by
    filter_upwards [h1, h2, h3] with ε hε1 hε2 hε3
    obtain ⟨hε0, hεe⟩ := hε1
    have hεlt1 : ε < 1 := hεe.trans (by
      rw [Real.exp_lt_one_iff]; norm_num)
    have hL : 1 ≤ Real.log (1 / ε) := by
      rw [one_div, Real.log_inv, le_neg]
      have := Real.log_lt_log hε0 hεe
      rw [Real.log_exp] at this; linarith
    exact poisson_uniform_bound hd hCc hCm hρ hr₀ hball hCr hε0 hεlt1 hL hε2 hε3
  have hlim : Tendsto (fun ε : ℝ => ENNReal.ofReal (2 * 7 ^ (d * d) * ε)) (𝓝[>] 0) (𝓝 0) := by
    have : Tendsto (fun ε : ℝ => 2 * 7 ^ (d * d) * ε) (𝓝[>] 0) (𝓝 0) := by
      have hc : Continuous fun ε : ℝ => 2 * 7 ^ (d * d) * ε := by fun_prop
      have := (hc.tendsto (0 : ℝ)).mono_left (nhdsWithin_le_nhds (s := Set.Ioi (0 : ℝ)))
      simpa using this
    simpa using (ENNReal.tendsto_ofReal this)
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim
    (Eventually.of_forall fun _ => zero_le) hbound

end Euclid

/-! ## A translation-invariant point process charges no null set -/

/-- **No points on null sets.**  Let `Π'` be a random measure on `ℝ^d` whose law is invariant
under all translations and whose intensity measure `Θ(A) = E Π'(A)` is locally finite.  Then
`Θ` is a multiple of Lebesgue measure (uniqueness of Haar measure), so almost surely `Π'`
charges no Lebesgue-null set. -/
theorem ae_eq_zero_of_null {d : ℕ} {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (X : Ω → Measure (Fin d → ℝ)) (hX : Measurable X)
    (hinv : ∀ a : Fin d → ℝ, (P.map X).map (fun ν => ν.map (a + ·)) = P.map X)
    (hfin : IsLocallyFiniteMeasure (P.bind X)) {F : Set (Fin d → ℝ)} (hF : volume F = 0) :
    ∀ᵐ ω ∂P, X ω F = 0 := by
  set Θ := P.bind X with hΘ
  have hΘapp : ∀ s, MeasurableSet s → Θ s = ∫⁻ ω, X ω s ∂P := fun s hs =>
    Measure.bind_apply hs hX.aemeasurable
  have hinvΘ : Θ.IsAddLeftInvariant := by
    constructor
    intro a
    have hm : Measurable (a + · : (Fin d → ℝ) → (Fin d → ℝ)) := measurable_const_add a
    ext s hs
    rw [Measure.map_apply hm hs, hΘapp _ (hm hs), hΘapp _ hs]
    have h1 : ∫⁻ ω, X ω ((a + ·) ⁻¹' s) ∂P = ∫⁻ ν, ν s ∂((P.map X).map (fun ν => ν.map (a + ·))) := by
      symm
      rw [lintegral_map (Measure.measurable_coe hs) (Measure.measurable_map _ hm)]
      rw [lintegral_map (f := fun ν : Measure (Fin d → ℝ) => (ν.map (a + ·)) s)
        ((Measure.measurable_coe hs).comp (Measure.measurable_map _ hm)) hX]
      congr 1; ext ω
      rw [Measure.map_apply hm hs]
    rw [h1, hinv a, lintegral_map (Measure.measurable_coe hs) hX]
  haveI := hinvΘ
  haveI := hfin
  have hsmul := MeasureTheory.Measure.isAddLeftInvariant_eq_smul Θ (volume : Measure (Fin d → ℝ))
  obtain ⟨F', hFF', hF'm, hF'0⟩ := exists_measurable_superset_of_null hF
  have hΘF : Θ F' = 0 := by rw [hsmul, Measure.smul_apply, hF'0, smul_zero]
  rw [hΘapp _ hF'm] at hΘF
  have hmeas : Measurable fun ω => X ω F' := (Measure.measurable_coe hF'm).comp hX
  have := (lintegral_eq_zero_iff hmeas).1 hΘF
  filter_upwards [this] with ω hω
  exact measure_mono_null hFF' hω

end

noncomputable section

open Set


/-! ## Jittered sets: plane geometry -/

section PlaneGeometry

/-- **Faces of a polygon.**  The frontier of the convex hull of a finite set `V` of the plane is
covered by the segments joining points of `V`. -/
theorem frontier_convexHull_subset (V : Finset (ℝ × ℝ)) :
    frontier (convexHull ℝ (V : Set (ℝ × ℝ))) ⊆ ⋃ a ∈ V, ⋃ b ∈ V, segment ℝ a b := by
  classical
  intro y hy
  have hK : IsClosed (convexHull ℝ (V : Set (ℝ × ℝ))) :=
    (V.finite_toSet.isCompact_convexHull ℝ).isClosed
  have hyK : y ∈ convexHull ℝ (V : Set (ℝ × ℝ)) := hK.frontier_subset hy
  have hyint : y ∉ interior (convexHull ℝ (V : Set (ℝ × ℝ))) := hy.2
  obtain ⟨ι, _, z, w, hzV, hind, hwpos, hw1, hwy⟩ := eq_pos_convex_span_of_mem_convexHull (𝕜 := ℝ) hyK
  have hcard : Fintype.card ι ≤ 3 := by
    have h1 := hind.card_le_finrank_succ
    have h2 := Submodule.finrank_le (vectorSpan ℝ (Set.range z))
    have h3 : Module.finrank ℝ (ℝ × ℝ) = 2 := by simp [Module.finrank_prod]
    omega
  simp only [Set.mem_iUnion, exists_prop]
  by_cases h3 : Fintype.card ι = 3
  · exfalso
    apply hyint
    have hspan : affineSpan ℝ (Set.range z) = ⊤ := by
      rw [hind.affineSpan_eq_top_iff_card_eq_finrank_add_one, h3]; simp [Module.finrank_prod]
    let b : AffineBasis ι ℝ (ℝ × ℝ) := ⟨z, hind, hspan⟩
    have hb : (b : ι → ℝ × ℝ) = z := rfl
    have hsub : interior (convexHull ℝ (Set.range b)) ⊆ interior (convexHull ℝ (V : Set (ℝ × ℝ))) :=
      interior_mono (convexHull_mono (by rw [hb]; exact hzV))
    apply hsub
    rw [b.interior_convexHull]
    intro i
    have hy' : y = Finset.univ.affineCombination ℝ b w := by
      rw [Finset.affineCombination_eq_linear_combination _ _ _ hw1, hb, hwy]
    rw [hy', b.coord_apply_combination_of_mem (Finset.mem_univ i) hw1]
    exact hwpos i
  · have hle2 : Fintype.card ι ≤ 2 := by omega
    have hne : Nonempty ι := by
      by_contra h
      rw [not_nonempty_iff] at h
      simp at hw1
    obtain ⟨i0⟩ := hne
    by_cases hall : ∀ k, k = i0
    · have hy0 : y = z i0 := by
        have hsum : ∑ i, w i • z i = w i0 • z i0 := by
          rw [Fintype.sum_eq_single i0 (fun k hk => absurd (hall k) hk)]
        have hw0 : w i0 = 1 := by
          rw [Fintype.sum_eq_single i0 (fun k hk => absurd (hall k) hk)] at hw1; exact hw1
        rw [← hwy, hsum, hw0, one_smul]
      have hzi : z i0 ∈ (V : Set (ℝ × ℝ)) := hzV ⟨i0, rfl⟩
      exact ⟨z i0, hzi, z i0, hzi, hy0 ▸ left_mem_segment ℝ (z i0) (z i0)⟩
    · push_neg at hall
      obtain ⟨j0, hj0⟩ := hall
      have hpair : ∀ k, k = i0 ∨ k = j0 := by
        intro k
        by_contra hk
        push_neg at hk
        have : ({i0, j0, k} : Finset ι).card = 3 := by
          rw [Finset.card_insert_of_notMem (by simp [Ne.symm hj0, Ne.symm hk.1]),
            Finset.card_pair (Ne.symm hk.2)]
        have := Finset.card_le_univ ({i0, j0, k} : Finset ι)
        omega
      have huniv : (Finset.univ : Finset ι) = {i0, j0} := by
        ext k; simp only [Finset.mem_univ, Finset.mem_insert, Finset.mem_singleton, true_iff]
        exact hpair k
      rw [huniv, Finset.sum_pair (Ne.symm hj0)] at hw1 hwy
      have hzi : z i0 ∈ (V : Set (ℝ × ℝ)) := hzV ⟨i0, rfl⟩
      have hzj : z j0 ∈ (V : Set (ℝ × ℝ)) := hzV ⟨j0, rfl⟩
      exact ⟨z i0, hzi, z j0, hzj, ⟨w i0, w j0, (hwpos i0).le, (hwpos j0).le, hw1, hwy⟩⟩

/-- A point outside the interior of a closed convex set `K` is as close to the frontier of `K`
as to any point of `K`. -/
theorem exists_frontier_near {K : Set (ℝ × ℝ)} (hKc : Convex ℝ K) (hK : IsClosed K)
    {y p : ℝ × ℝ} (hp : p ∈ K) (hy : y ∉ interior K) : ∃ f ∈ frontier K, ‖y - f‖ ≤ ‖y - p‖ := by
  by_cases hyK : y ∈ K
  · exact ⟨y, ⟨subset_closure hyK, hy⟩, by simp⟩
  · have hconn : IsPreconnected (segment ℝ p y) := (convex_segment p y).isPreconnected
    have hne : (segment ℝ p y ∩ frontier K).Nonempty := by
      by_contra hcon
      rw [Set.not_nonempty_iff_eq_empty] at hcon
      have hcov : segment ℝ p y ⊆ interior K ∪ (closure K)ᶜ := by
        intro q hq
        by_cases hqi : q ∈ interior K
        · exact Or.inl hqi
        · right
          intro hqc
          have : q ∈ segment ℝ p y ∩ frontier K := ⟨hq, hqc, hqi⟩
          rw [hcon] at this; exact this
      have hpi : p ∈ interior K := by
        rcases hcov (left_mem_segment ℝ p y) with h | h
        · exact h
        · exact absurd (subset_closure hp) h
      have hyc : y ∈ (closure K)ᶜ := by rw [hK.closure_eq]; exact hyK
      obtain ⟨q, _, hq1, hq2⟩ := hconn _ _ isOpen_interior isClosed_closure.isOpen_compl hcov
        ⟨p, left_mem_segment ℝ p y, hpi⟩ ⟨y, right_mem_segment ℝ p y, hyc⟩
      exact hq2 (interior_subset.trans subset_closure hq1)
    obtain ⟨f, hfseg, hfK⟩ := hne
    refine ⟨f, hfK, ?_⟩
    obtain ⟨a, b, ha, hb, hab, rfl⟩ := hfseg
    have : y - (a • p + b • y) = a • (y - p) := by
      rw [show a = 1 - b by linarith]; module
    rw [this, norm_smul, Real.norm_eq_abs, abs_of_nonneg ha]
    exact mul_le_of_le_one_left (norm_nonneg _) (by linarith)

/-- The closed grid box of side `δ` with lower corner `δ g`. -/
def gbox (δ : ℝ) (g : ℤ × ℤ) : Set (ℝ × ℝ) :=
  Set.Icc (g.1 * δ) ((g.1 + 1) * δ) ×ˢ Set.Icc (g.2 * δ) ((g.2 + 1) * δ)

/-- The `3 × 3` block of grid boxes around the box `g`. -/
def gbig (δ : ℝ) (g : ℤ × ℤ) : Set (ℝ × ℝ) :=
  Set.Icc ((g.1 - 1) * δ) ((g.1 + 2) * δ) ×ˢ Set.Icc ((g.2 - 1) * δ) ((g.2 + 2) * δ)

/-- The grid box containing a point. -/
def gidx (δ : ℝ) (v : ℝ × ℝ) : ℤ × ℤ := (⌊v.1 / δ⌋, ⌊v.2 / δ⌋)

theorem floor_bounds {δ : ℝ} (hδ : 0 < δ) (x : ℝ) :
    (⌊x / δ⌋ : ℝ) * δ ≤ x ∧ x < ((⌊x / δ⌋ : ℝ) + 1) * δ := by
  have h1 := Int.floor_le (x / δ)
  have h2 := Int.lt_floor_add_one (x / δ)
  rw [le_div_iff₀ hδ] at h1
  rw [div_lt_iff₀ hδ] at h2
  exact ⟨h1, h2⟩

theorem mem_gbox_gidx {δ : ℝ} (hδ : 0 < δ) (v : ℝ × ℝ) : v ∈ gbox δ (gidx δ v) := by
  obtain ⟨h1, h2⟩ := floor_bounds hδ v.1
  obtain ⟨h3, h4⟩ := floor_bounds hδ v.2
  exact ⟨⟨h1, h2.le⟩, ⟨h3, h4.le⟩⟩

theorem norm_sub_le_of_mem_gbox {δ : ℝ} (hδ : 0 < δ) (v : ℝ × ℝ) {u : ℝ × ℝ}
    (hu : u ∈ gbox δ (gidx δ v)) : ‖u - v‖ ≤ δ := by
  obtain ⟨h1, h2⟩ := floor_bounds hδ v.1
  obtain ⟨h3, h4⟩ := floor_bounds hδ v.2
  obtain ⟨⟨u1, u2⟩, ⟨u3, u4⟩⟩ := hu
  simp only [gidx] at u1 u2 u3 u4
  rw [Prod.norm_def, max_le_iff, Prod.fst_sub, Prod.snd_sub, Real.norm_eq_abs, Real.norm_eq_abs,
    abs_le, abs_le]
  refine ⟨⟨by nlinarith, by nlinarith⟩, ⟨by nlinarith, by nlinarith⟩⟩

theorem add_mem_gbig {δ : ℝ} (hδ : 0 < δ) (v : ℝ × ℝ) {w : ℝ × ℝ} (hw : ‖w‖ ≤ δ) :
    v + w ∈ gbig δ (gidx δ v) := by
  obtain ⟨h1, h2⟩ := floor_bounds hδ v.1
  obtain ⟨h3, h4⟩ := floor_bounds hδ v.2
  rw [Prod.norm_def, max_le_iff, Real.norm_eq_abs, Real.norm_eq_abs, abs_le, abs_le] at hw
  simp only [gbig, gidx, mem_prod, Set.mem_Icc, Prod.fst_add, Prod.snd_add]
  refine ⟨⟨by nlinarith, by nlinarith⟩, ⟨by nlinarith, by nlinarith⟩⟩

/-- The rounded outer polygon: the convex hull of the grid boxes of the points of `I`. -/
def pplus (δ : ℝ) (I : Finset (ℤ × ℤ)) : Set (ℝ × ℝ) := convexHull ℝ (⋃ g ∈ I, gbox δ g)

/-- The strip about the segment from box `g` to box `g'`. -/
def dset (δ : ℝ) (g g' : ℤ × ℤ) : Set (ℝ × ℝ) := convexHull ℝ (gbig δ g ∪ gbig δ g')

theorem convexHull_subset_pplus {δ : ℝ} (hδ : 0 < δ) (V : Finset (ℝ × ℝ)) :
    convexHull ℝ (V : Set (ℝ × ℝ)) ⊆ pplus δ (V.image (gidx δ)) := by
  refine convexHull_mono fun v hv => ?_
  simp only [Set.mem_iUnion, exists_prop]
  exact ⟨gidx δ v, Finset.mem_image_of_mem _ hv, mem_gbox_gidx hδ v⟩

theorem pplus_subset_thickening {δ : ℝ} (hδ : 0 < δ) (V : Finset (ℝ × ℝ)) :
    pplus δ (V.image (gidx δ)) ⊆
      {y | ∃ p ∈ convexHull ℝ (V : Set (ℝ × ℝ)), ‖y - p‖ ≤ δ} := by
  refine convexHull_min ?_ ?_
  · intro u hu
    simp only [Set.mem_iUnion, exists_prop, Finset.mem_image] at hu
    obtain ⟨_, ⟨v, hv, rfl⟩, hu⟩ := hu
    exact ⟨v, subset_convexHull ℝ _ hv, norm_sub_le_of_mem_gbox hδ v hu⟩
  · rintro y₁ ⟨p₁, hp₁, h₁⟩ y₂ ⟨p₂, hp₂, h₂⟩ a b ha hb hab
    refine ⟨a • p₁ + b • p₂, convex_convexHull ℝ _ hp₁ hp₂ ha hb hab, ?_⟩
    have : a • y₁ + b • y₂ - (a • p₁ + b • p₂) = a • (y₁ - p₁) + b • (y₂ - p₂) := by module
    rw [this]
    calc ‖a • (y₁ - p₁) + b • (y₂ - p₂)‖ ≤ ‖a • (y₁ - p₁)‖ + ‖b • (y₂ - p₂)‖ := norm_add_le _ _
      _ = a * ‖y₁ - p₁‖ + b * ‖y₂ - p₂‖ := by
          rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg ha,
            abs_of_nonneg hb]
      _ ≤ a * δ + b * δ := by gcongr
      _ = δ := by rw [← add_mul, hab, one_mul]

/-- **The remainder of the rounded polygon lies in the strips.**  A point of the rounded outer
polygon that is not interior to `conv V` lies in the strip of some pair of points of `V`. -/
theorem pplus_diff_subset {δ : ℝ} (hδ : 0 < δ) (V : Finset (ℝ × ℝ)) {y : ℝ × ℝ}
    (hy : y ∈ pplus δ (V.image (gidx δ))) (hyi : y ∉ interior (convexHull ℝ (V : Set (ℝ × ℝ)))) :
    ∃ a ∈ V, ∃ b ∈ V, y ∈ dset δ (gidx δ a) (gidx δ b) := by
  obtain ⟨p, hp, hyp⟩ := pplus_subset_thickening hδ V hy
  have hK : IsClosed (convexHull ℝ (V : Set (ℝ × ℝ))) :=
    (V.finite_toSet.isCompact_convexHull ℝ).isClosed
  obtain ⟨f, hf, hyf⟩ := exists_frontier_near (convex_convexHull ℝ _) hK hp hyi
  have hfseg := frontier_convexHull_subset V hf
  simp only [Set.mem_iUnion, exists_prop] at hfseg
  obtain ⟨a, ha, b, hb, s, t, hs, ht, hst, rfl⟩ := hfseg
  refine ⟨a, ha, b, hb, ?_⟩
  set w := y - (s • a + t • b) with hw
  have hwn : ‖w‖ ≤ δ := hyf.trans hyp
  have hya : a + w ∈ gbig δ (gidx δ a) := add_mem_gbig hδ a hwn
  have hyb : b + w ∈ gbig δ (gidx δ b) := add_mem_gbig hδ b hwn
  have : y = s • (a + w) + t • (b + w) := by
    have e : s • (a + w) + t • (b + w) = s • a + t • b + (s + t) • w := by module
    rw [e, hst, one_smul, hw]; abel
  rw [this]
  show _ ∈ convexHull ℝ (gbig δ (gidx δ a) ∪ gbig δ (gidx δ b))
  have h1 : a + w ∈ convexHull ℝ (gbig δ (gidx δ a) ∪ gbig δ (gidx δ b)) :=
    subset_convexHull ℝ _ (Set.mem_union_left _ hya)
  have h2 : b + w ∈ convexHull ℝ (gbig δ (gidx δ a) ∪ gbig δ (gidx δ b)) :=
    subset_convexHull ℝ _ (Set.mem_union_right _ hyb)
  exact convex_convexHull ℝ _ h1 h2 hs ht hst

theorem exists_weight {a b x : ℝ} (hab : a ≤ b) (hx : x ∈ Set.Icc a b) :
    ∃ s ∈ Set.Icc (0 : ℝ) 1, x = (1 - s) * a + s * b := by
  rcases eq_or_lt_of_le hab with h | h
  · subst h
    refine ⟨0, ⟨le_refl _, zero_le_one⟩, ?_⟩
    have : x = a := le_antisymm hx.2 hx.1
    rw [this]; ring
  · refine ⟨(x - a) / (b - a), ⟨div_nonneg (by linarith [hx.1]) (by linarith),
      (div_le_one (by linarith)).2 (by linarith [hx.2])⟩, ?_⟩
    field_simp; ring

/-- A box is the convex hull of its four corners. -/
theorem box_subset_convexHull {a₁ b₁ a₂ b₂ : ℝ} (h₁ : a₁ ≤ b₁) (h₂ : a₂ ≤ b₂) :
    Set.Icc a₁ b₁ ×ˢ Set.Icc a₂ b₂ ⊆
      convexHull ℝ ({(a₁, a₂), (b₁, a₂), (a₁, b₂), (b₁, b₂)} : Set (ℝ × ℝ)) := by
  rintro u ⟨hu1, hu2⟩
  obtain ⟨s, hs, hs'⟩ := exists_weight h₁ hu1
  obtain ⟨t, ht, ht'⟩ := exists_weight h₂ hu2
  set K := convexHull ℝ ({(a₁, a₂), (b₁, a₂), (a₁, b₂), (b₁, b₂)} : Set (ℝ × ℝ))
  have hK : Convex ℝ K := convex_convexHull ℝ _
  have m1 : ((a₁, a₂) : ℝ × ℝ) ∈ K := subset_convexHull ℝ _ (by simp)
  have m2 : ((b₁, a₂) : ℝ × ℝ) ∈ K := subset_convexHull ℝ _ (by simp)
  have m3 : ((a₁, b₂) : ℝ × ℝ) ∈ K := subset_convexHull ℝ _ (by simp)
  have m4 : ((b₁, b₂) : ℝ × ℝ) ∈ K := subset_convexHull ℝ _ (by simp)
  have hp := hK m1 m2 (by linarith [hs.2]) hs.1 (by ring : (1 - s) + s = 1)
  have hq := hK m3 m4 (by linarith [hs.2]) hs.1 (by ring : (1 - s) + s = 1)
  have hu := hK hp hq (by linarith [ht.2]) ht.1 (by ring : (1 - t) + t = 1)
  convert hu using 1
  ext
  · simp only [Prod.smul_mk, Prod.mk_add_mk, smul_eq_mul, Prod.fst_add, Prod.smul_fst]
    rw [hs']; ring
  · simp only [Prod.smul_mk, Prod.mk_add_mk, smul_eq_mul, Prod.snd_add, Prod.smul_snd]
    rw [ht']; ring

/-- The corners of the grid box `g`. -/
def gboxC (δ : ℝ) (g : ℤ × ℤ) : Set (ℝ × ℝ) :=
  {((g.1 : ℝ) * δ, (g.2 : ℝ) * δ), (((g.1 : ℝ) + 1) * δ, (g.2 : ℝ) * δ),
    ((g.1 : ℝ) * δ, ((g.2 : ℝ) + 1) * δ), (((g.1 : ℝ) + 1) * δ, ((g.2 : ℝ) + 1) * δ)}

/-- The corners of the `3 × 3` block around the box `g`. -/
def gbigC (δ : ℝ) (g : ℤ × ℤ) : Set (ℝ × ℝ) :=
  {(((g.1 : ℝ) - 1) * δ, ((g.2 : ℝ) - 1) * δ), (((g.1 : ℝ) + 2) * δ, ((g.2 : ℝ) - 1) * δ),
    (((g.1 : ℝ) - 1) * δ, ((g.2 : ℝ) + 2) * δ), (((g.1 : ℝ) + 2) * δ, ((g.2 : ℝ) + 2) * δ)}

theorem gbox_subset_convexHull {δ : ℝ} (hδ : 0 < δ) (g : ℤ × ℤ) :
    gbox δ g ⊆ convexHull ℝ (gboxC δ g) :=
  box_subset_convexHull (by nlinarith) (by nlinarith)

theorem gboxC_subset {δ : ℝ} (hδ : 0 < δ) (g : ℤ × ℤ) : gboxC δ g ⊆ gbox δ g := by
  intro u hu
  simp only [gboxC, Set.mem_insert_iff, Set.mem_singleton_iff] at hu
  rcases hu with rfl | rfl | rfl | rfl <;>
    exact ⟨⟨by nlinarith, by nlinarith⟩, ⟨by nlinarith, by nlinarith⟩⟩

theorem gbig_subset_convexHull {δ : ℝ} (hδ : 0 < δ) (g : ℤ × ℤ) :
    gbig δ g ⊆ convexHull ℝ (gbigC δ g) :=
  box_subset_convexHull (by nlinarith) (by nlinarith)

theorem gbigC_subset {δ : ℝ} (hδ : 0 < δ) (g : ℤ × ℤ) : gbigC δ g ⊆ gbig δ g := by
  intro u hu
  simp only [gbigC, Set.mem_insert_iff, Set.mem_singleton_iff] at hu
  rcases hu with rfl | rfl | rfl | rfl <;>
    exact ⟨⟨by nlinarith, by nlinarith⟩, ⟨by nlinarith, by nlinarith⟩⟩

theorem pplus_eq_corners {δ : ℝ} (hδ : 0 < δ) (I : Finset (ℤ × ℤ)) :
    pplus δ I = convexHull ℝ (⋃ g ∈ I, gboxC δ g) := by
  apply le_antisymm
  · refine convexHull_min ?_ (convex_convexHull ℝ _)
    intro u hu
    simp only [Set.mem_iUnion, exists_prop] at hu
    obtain ⟨g, hg, hu⟩ := hu
    exact convexHull_mono (Set.subset_biUnion_of_mem (u := fun g => gboxC δ g) hg)
      (gbox_subset_convexHull hδ g hu)
  · exact convexHull_mono (Set.biUnion_mono (fun _ h => h) fun g _ => gboxC_subset hδ g)

theorem dset_eq_corners {δ : ℝ} (hδ : 0 < δ) (g g' : ℤ × ℤ) :
    dset δ g g' = convexHull ℝ (gbigC δ g ∪ gbigC δ g') := by
  apply le_antisymm
  · refine convexHull_min ?_ (convex_convexHull ℝ _)
    rintro u (hu | hu)
    · exact convexHull_mono Set.subset_union_left (gbig_subset_convexHull hδ g hu)
    · exact convexHull_mono Set.subset_union_right (gbig_subset_convexHull hδ g' hu)
  · exact convexHull_mono (Set.union_subset_union (gbigC_subset hδ g) (gbigC_subset hδ g'))

theorem isCompact_pplus {δ : ℝ} (hδ : 0 < δ) (I : Finset (ℤ × ℤ)) : IsCompact (pplus δ I) := by
  rw [pplus_eq_corners hδ]
  refine Set.Finite.isCompact_convexHull ℝ ?_
  refine Set.Finite.biUnion I.finite_toSet fun g _ => ?_
  simp only [gboxC]; exact Set.toFinite _

theorem isCompact_dset {δ : ℝ} (hδ : 0 < δ) (g g' : ℤ × ℤ) : IsCompact (dset δ g g') := by
  rw [dset_eq_corners hδ]
  refine Set.Finite.isCompact_convexHull ℝ ?_
  refine Set.Finite.union ?_ ?_ <;> simp only [gbigC] <;> exact Set.toFinite _

theorem volume_closedBall_prod (q : ℝ × ℝ) (r : ℝ) (hr : 0 ≤ r) :
    volume (Metric.closedBall q r) = ENNReal.ofReal ((2 * r) ^ 2) := by
  obtain ⟨a, b⟩ := q
  rw [← closedBall_prod_same, Measure.volume_eq_prod, Measure.prod_prod, Real.volume_closedBall,
    Real.volume_closedBall, ← ENNReal.ofReal_mul (by positivity)]
  ring_nf

/-- The centre of the grid box `g`. -/
def gcen (δ : ℝ) (g : ℤ × ℤ) : ℝ × ℝ := (((g.1 : ℝ) + 1 / 2) * δ, ((g.2 : ℝ) + 1 / 2) * δ)

theorem gbig_subset_closedBall {δ : ℝ} (hδ : 0 < δ) (g : ℤ × ℤ) :
    gbig δ g ⊆ Metric.closedBall (gcen δ g) (3 * δ / 2) := by
  rintro u ⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩
  rw [Metric.mem_closedBall, dist_eq_norm, Prod.norm_def, max_le_iff, Prod.fst_sub, Prod.snd_sub,
    Real.norm_eq_abs, Real.norm_eq_abs, abs_le, abs_le]
  simp only [gcen]
  refine ⟨⟨by nlinarith, by nlinarith⟩, ⟨by nlinarith, by nlinarith⟩⟩

/-- **The strips are thin**: `vol(D) ≤ 25 δ |c - c'| + 75 δ²`. -/
theorem volume_dset_le {δ : ℝ} (hδ : 0 < δ) (g g' : ℤ × ℤ) :
    volume (dset δ g g') ≤
      ENNReal.ofReal (25 * δ * ‖gcen δ g' - gcen δ g‖ + 75 * δ ^ 2) := by
  set c := gcen δ g with hc
  set c' := gcen δ g' with hc'
  set S : Set (ℝ × ℝ) := {y | ∃ s ∈ Set.Icc (0 : ℝ) 1, ‖y - (c + s • (c' - c))‖ ≤ 3 * δ / 2} with hS
  have hSconv : Convex ℝ S := by
    rintro y₁ ⟨s₁, hs₁, h₁⟩ y₂ ⟨s₂, hs₂, h₂⟩ a b ha hb hab
    refine ⟨a * s₁ + b * s₂, ⟨by nlinarith [hs₁.1, hs₂.1], by nlinarith [hs₁.2, hs₂.2]⟩, ?_⟩
    have : a • y₁ + b • y₂ - (c + (a * s₁ + b * s₂) • (c' - c)) =
        a • (y₁ - (c + s₁ • (c' - c))) + b • (y₂ - (c + s₂ • (c' - c))) := by
      obtain rfl : b = 1 - a := by linarith
      module
    rw [this]
    calc _ ≤ ‖a • (y₁ - (c + s₁ • (c' - c)))‖ + ‖b • (y₂ - (c + s₂ • (c' - c)))‖ := norm_add_le _ _
      _ = a * ‖y₁ - (c + s₁ • (c' - c))‖ + b * ‖y₂ - (c + s₂ • (c' - c))‖ := by
          rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg ha,
            abs_of_nonneg hb]
      _ ≤ a * (3 * δ / 2) + b * (3 * δ / 2) := by gcongr
      _ = 3 * δ / 2 := by rw [← add_mul, hab, one_mul]
  have hsub : dset δ g g' ⊆ S := by
    refine convexHull_min ?_ hSconv
    rintro y (hy | hy)
    · refine ⟨0, ⟨le_refl _, zero_le_one⟩, ?_⟩
      have := gbig_subset_closedBall hδ g hy
      rw [Metric.mem_closedBall, dist_eq_norm] at this
      simpa using this
    · refine ⟨1, ⟨zero_le_one, le_refl _⟩, ?_⟩
      have := gbig_subset_closedBall hδ g' hy
      rw [Metric.mem_closedBall, dist_eq_norm] at this
      simpa using this
  set M : ℕ := ⌈‖c' - c‖ / δ⌉₊ + 1 with hM
  have hM0 : (0 : ℝ) < M := by rw [hM]; positivity
  have hMge : ‖c' - c‖ / δ ≤ M := by
    rw [hM]; push_cast; linarith [Nat.le_ceil (‖c' - c‖ / δ)]
  set q : ℕ → ℝ × ℝ := fun i => c + ((i : ℝ) / M) • (c' - c) with hq
  have hcover : S ⊆ ⋃ i ∈ Finset.range (M + 1), Metric.closedBall (q i) (5 * δ / 2) := by
    rintro y ⟨s, ⟨hs0, hs1⟩, hy⟩
    simp only [Set.mem_iUnion, exists_prop, Finset.mem_range]
    have hsM : 0 ≤ s * M := by positivity
    have hfl1 := Nat.floor_le hsM
    have hfl2 := Nat.lt_floor_add_one (s * M)
    refine ⟨⌊s * M⌋₊, ?_, ?_⟩
    · have : ⌊s * M⌋₊ ≤ M := by
        have := Nat.floor_mono (show s * M ≤ (M : ℝ) by nlinarith)
        simpa using this
      omega
    · rw [Metric.mem_closedBall, dist_eq_norm]
      have e : y - q ⌊s * M⌋₊ = (y - (c + s • (c' - c))) + (s - (⌊s * M⌋₊ : ℝ) / M) • (c' - c) := by
        simp only [hq]; module
      rw [e]
      have hd1 : 0 ≤ s - (⌊s * M⌋₊ : ℝ) / M := by
        rw [sub_nonneg, div_le_iff₀ hM0]; linarith
      have hd2 : s - (⌊s * M⌋₊ : ℝ) / M ≤ 1 / M := by
        rw [sub_le_iff_le_add, ← add_div, le_div_iff₀ hM0]; linarith
      have hcc : ‖c' - c‖ ≤ M * δ := by rwa [div_le_iff₀ hδ] at hMge
      calc ‖(y - (c + s • (c' - c))) + (s - (⌊s * M⌋₊ : ℝ) / M) • (c' - c)‖
          ≤ ‖y - (c + s • (c' - c))‖ + ‖(s - (⌊s * M⌋₊ : ℝ) / M) • (c' - c)‖ := norm_add_le _ _
        _ ≤ 3 * δ / 2 + 1 / M * (M * δ) := by
            rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hd1]
            gcongr
        _ = 5 * δ / 2 := by field_simp; ring
  calc volume (dset δ g g') ≤ volume S := measure_mono hsub
    _ ≤ volume (⋃ i ∈ Finset.range (M + 1), Metric.closedBall (q i) (5 * δ / 2)) :=
        measure_mono hcover
    _ ≤ ∑ i ∈ Finset.range (M + 1), volume (Metric.closedBall (q i) (5 * δ / 2)) :=
        measure_biUnion_finset_le _ _
    _ = ∑ i ∈ Finset.range (M + 1), ENNReal.ofReal ((5 * δ) ^ 2) := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [volume_closedBall_prod _ _ (by positivity)]; ring_nf
    _ = ENNReal.ofReal ((M + 1) * (5 * δ) ^ 2) := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, ENNReal.ofReal_mul (by positivity)]
        norm_cast
    _ ≤ ENNReal.ofReal (25 * δ * ‖c' - c‖ + 75 * δ ^ 2) := by
        apply ENNReal.ofReal_le_ofReal
        have hM2 : (M : ℝ) ≤ ‖c' - c‖ / δ + 2 := by
          rw [hM]; push_cast
          linarith [Nat.ceil_lt_add_one (show 0 ≤ ‖c' - c‖ / δ by positivity)]
        have : ((M : ℝ) + 1) * δ ≤ ‖c' - c‖ + 3 * δ := by
          have := mul_le_mul_of_nonneg_right hM2 hδ.le
          rw [add_mul, div_mul_cancel₀ _ hδ.ne'] at this; linarith
        nlinarith

/-! ### Cells meeting the boundary of a convex set -/

/-- The cell `c` of the jittered grid: side `h`, lower corner `(-R + c₁ h, -R + c₂ h)`. -/
def jcell {N : ℕ} (R h : ℝ) (c : Fin N × Fin N) : Set (ℝ × ℝ) :=
  Set.Ico (-R + (c.1 : ℝ) * h) (-R + ((c.1 : ℝ) + 1) * h) ×ˢ
    Set.Ico (-R + (c.2 : ℝ) * h) (-R + ((c.2 : ℝ) + 1) * h)

theorem lt_of_mem_jcell_lt {N : ℕ} {R h : ℝ} (hh : 0 < h) {i i' : Fin N} (hii : i < i')
    {x x' : ℝ} (hx : x ∈ Set.Ico (-R + (i : ℝ) * h) (-R + ((i : ℝ) + 1) * h))
    (hx' : x' ∈ Set.Ico (-R + (i' : ℝ) * h) (-R + ((i' : ℝ) + 1) * h)) : x < x' := by
  have : (i : ℝ) + 1 ≤ i' := by
    have : (i : ℕ) + 1 ≤ i' := hii; exact_mod_cast this
  have := mul_le_mul_of_nonneg_right this hh.le
  linarith [hx.2, hx'.1]

/-- The core of the antichain argument: a separating functional of a point `z` of the cell `c`
from `P` forbids points of `P` in cells `d` placed beyond `c` in the direction of the functional. -/
theorem no_bad_pair {N : ℕ} {R h : ℝ} (hh : 0 < h) {P : Set (ℝ × ℝ)} {α β : ℝ}
    {c d : Fin N × Fin N} {z q : ℝ × ℝ} (hz : z ∈ jcell R h c)
    (hsep : ∀ p ∈ P, α * z.1 + β * z.2 < α * p.1 + β * p.2) (hq : q ∈ jcell R h d) (hqP : q ∈ P)
    (h1 : (α ≤ 0 ∧ c.1 < d.1) ∨ (0 ≤ α ∧ d.1 < c.1))
    (h2 : (β ≤ 0 ∧ c.2 < d.2) ∨ (0 ≤ β ∧ d.2 < c.2)) : False := by
  have hs := hsep q hqP
  have e1 : α * (q.1 - z.1) ≤ 0 := by
    rcases h1 with ⟨ha, hcd⟩ | ⟨ha, hcd⟩
    · have := lt_of_mem_jcell_lt hh hcd hz.1 hq.1
      nlinarith
    · have := lt_of_mem_jcell_lt hh hcd hq.1 hz.1
      nlinarith
  have e2 : β * (q.2 - z.2) ≤ 0 := by
    rcases h2 with ⟨hb, hcd⟩ | ⟨hb, hcd⟩
    · have := lt_of_mem_jcell_lt hh hcd hz.2 hq.2
      nlinarith
    · have := lt_of_mem_jcell_lt hh hcd hq.2 hz.2
      nlinarith
  linarith

open Classical in
/-- **Few cells meet the boundary of a convex set.**  For a closed convex set `P`, at most
`12 N + 4` of the `N²` cells meet both `P` and its complement. -/
theorem card_partial_le {N : ℕ} {R h : ℝ} (hh : 0 < h) {P : Set (ℝ × ℝ)} (hPc : Convex ℝ P)
    (hPcl : IsClosed P) :
    (Finset.univ.filter (fun c : Fin N × Fin N =>
      (jcell R h c ∩ P).Nonempty ∧ ¬ jcell R h c ⊆ P)).card ≤ 12 * N + 4 := by
  set Par := Finset.univ.filter (fun c : Fin N × Fin N =>
      (jcell R h c ∩ P).Nonempty ∧ ¬ jcell R h c ⊆ P) with hPar
  have hex : ∀ c ∈ Par, ∃ ab : ℝ × ℝ, ∃ z ∈ jcell R h c,
      ∀ p ∈ P, ab.1 * z.1 + ab.2 * z.2 < ab.1 * p.1 + ab.2 * p.2 := by
    intro c hc
    rw [hPar, Finset.mem_filter] at hc
    obtain ⟨z, hzc, hzP⟩ := Set.not_subset.1 hc.2.2
    obtain ⟨f, u, hfz, hfP⟩ := geometric_hahn_banach_point_closed hPc hPcl hzP
    have hf : ∀ p : ℝ × ℝ, f p = f (1, 0) * p.1 + f (0, 1) * p.2 := by
      intro p
      have : p = p.1 • ((1 : ℝ), (0 : ℝ)) + p.2 • ((0 : ℝ), (1 : ℝ)) := by ext <;> simp
      conv_lhs => rw [this]
      rw [map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul]; ring
    refine ⟨(f (1, 0), f (0, 1)), z, hzc, fun p hp => ?_⟩
    have := hfP p hp
    rw [← hf, ← hf]; linarith
  let data : Fin N × Fin N → ℝ × ℝ := fun c => if hc : c ∈ Par then (hex c hc).choose else 0
  let typ : Fin N × Fin N → Bool × Bool := fun c => (decide ((data c).1 ≤ 0), decide ((data c).2 ≤ 0))
  have hdata : ∀ c ∈ Par, ∃ z ∈ jcell R h c,
      ∀ p ∈ P, (data c).1 * z.1 + (data c).2 * z.2 < (data c).1 * p.1 + (data c).2 * p.2 := by
    intro c hc
    simp only [data, dif_pos hc]
    exact (hex c hc).choose_spec
  -- the key of a cell for each type
  let key : Bool × Bool → Fin N × Fin N → ℤ := fun T c =>
    if T.1 = T.2 then (c.1 : ℤ) - c.2 else (c.1 : ℤ) + c.2
  have hcardT : ∀ T : Bool × Bool, (Par.filter (fun c => typ c = T)).card ≤ 3 * N + 1 := by
    intro T
    have hmaps : ∀ c ∈ Par.filter (fun c => typ c = T),
        key T c ∈ Finset.Icc (-(N : ℤ)) (2 * N) := by
      intro c _
      have h1 := c.1.2; have h2 := c.2.2
      simp only [key, Finset.mem_Icc]
      split_ifs <;> constructor <;> omega
    have hinj : Set.InjOn (key T) ↑(Par.filter (fun c => typ c = T)) := by
      intro c hc c' hc' hkey
      simp only [Finset.coe_filter, Set.mem_setOf_eq] at hc hc'
      by_contra hne
      obtain ⟨hcPar, hcT⟩ := hc
      obtain ⟨hc'Par, hc'T⟩ := hc'
      obtain ⟨z, hz, hsep⟩ := hdata c hcPar
      obtain ⟨z', hz', hsep'⟩ := hdata c' hc'Par
      have hqc := (Finset.mem_filter.1 hcPar).2.1
      have hqc' := (Finset.mem_filter.1 hc'Par).2.1
      obtain ⟨q, hq, hqP⟩ := hqc
      obtain ⟨q', hq', hq'P⟩ := hqc'
      have hne' : (c.1 : ℕ) ≠ c'.1 ∨ (c.2 : ℕ) ≠ c'.2 := by
        by_contra hh'
        push_neg at hh'
        exact hne (Prod.ext (Fin.ext hh'.1) (Fin.ext hh'.2))
      have hlt : ∀ {a b : Fin N}, (a : ℕ) < b → a < b := fun h => h
      simp only [typ, Prod.mk.injEq] at hcT hc'T
      obtain ⟨t1, t2⟩ := T
      simp only [key] at hkey
      have hc1 := c.1.2; have hc2 := c.2.2
      cases t1 <;> cases t2 <;> simp only [Prod.mk.injEq, decide_eq_true_eq, decide_eq_false_iff_not,
        not_le, Bool.false_eq_true, Bool.true_eq_false, if_true, if_false] at hcT hc'T hkey
      · -- α > 0, β > 0: key `i - j`
        rcases lt_or_gt_of_ne (show (c.1 : ℤ) ≠ c'.1 by omega) with h | h
        · exact no_bad_pair hh hz' hsep' hq hqP (Or.inr ⟨hc'T.1.le, hlt (by omega)⟩)
            (Or.inr ⟨hc'T.2.le, hlt (by omega)⟩)
        · exact no_bad_pair hh hz hsep hq' hq'P (Or.inr ⟨hcT.1.le, hlt (by omega)⟩)
            (Or.inr ⟨hcT.2.le, hlt (by omega)⟩)
      · -- α > 0, β ≤ 0: key `i + j`
        rcases lt_or_gt_of_ne (show (c.1 : ℤ) ≠ c'.1 by omega) with h | h
        · exact no_bad_pair hh hz' hsep' hq hqP (Or.inr ⟨hc'T.1.le, hlt (by omega)⟩)
            (Or.inl ⟨hc'T.2, hlt (by omega)⟩)
        · exact no_bad_pair hh hz hsep hq' hq'P (Or.inr ⟨hcT.1.le, hlt (by omega)⟩)
            (Or.inl ⟨hcT.2, hlt (by omega)⟩)
      · -- α ≤ 0, β > 0: key `i + j`
        rcases lt_or_gt_of_ne (show (c.1 : ℤ) ≠ c'.1 by omega) with h | h
        · exact no_bad_pair hh hz hsep hq' hq'P (Or.inl ⟨hcT.1, hlt (by omega)⟩)
            (Or.inr ⟨hcT.2.le, hlt (by omega)⟩)
        · exact no_bad_pair hh hz' hsep' hq hqP (Or.inl ⟨hc'T.1, hlt (by omega)⟩)
            (Or.inr ⟨hc'T.2.le, hlt (by omega)⟩)
      · -- α ≤ 0, β ≤ 0: key `i - j`
        rcases lt_or_gt_of_ne (show (c.1 : ℤ) ≠ c'.1 by omega) with h | h
        · exact no_bad_pair hh hz hsep hq' hq'P (Or.inl ⟨hcT.1, hlt (by omega)⟩)
            (Or.inl ⟨hcT.2, hlt (by omega)⟩)
        · exact no_bad_pair hh hz' hsep' hq hqP (Or.inl ⟨hc'T.1, hlt (by omega)⟩)
            (Or.inl ⟨hc'T.2, hlt (by omega)⟩)
    have := Finset.card_le_card_of_injOn (key T) hmaps hinj
    simp only [Int.card_Icc] at this
    omega
  calc Par.card = ∑ T ∈ (Finset.univ : Finset (Bool × Bool)), (Par.filter (fun c => typ c = T)).card :=
        Finset.card_eq_sum_card_fiberwise (fun _ _ => Finset.mem_univ _)
    _ ≤ ∑ _T ∈ (Finset.univ : Finset (Bool × Bool)), (3 * N + 1) := Finset.sum_le_sum fun T _ => hcardT T
    _ = 12 * N + 4 := by simp; ring

end PlaneGeometry

/-! ## Jittered sets: the random jittered set -/

section JitProb

variable {N : ℕ} {R h : ℝ}

theorem volume_jcell (hh : 0 < h) (c : Fin N × Fin N) :
    volume (jcell R h c) = ENNReal.ofReal (h ^ 2) := by
  rw [jcell, Measure.volume_eq_prod, Measure.prod_prod, Real.volume_Ico, Real.volume_Ico,
    ← ENNReal.ofReal_mul (by nlinarith)]
  ring_nf

theorem measurableSet_jcell (c : Fin N × Fin N) : MeasurableSet (jcell R h c) :=
  measurableSet_Ico.prod measurableSet_Ico

/-- The uniform law on a cell. -/
def unifCell (R h : ℝ) (c : Fin N × Fin N) : Measure (ℝ × ℝ) :=
  ENNReal.ofReal ((h ^ 2)⁻¹) • volume.restrict (jcell R h c)

theorem isProbabilityMeasure_unifCell (hh : 0 < h) (c : Fin N × Fin N) :
    IsProbabilityMeasure (unifCell R h c) := by
  constructor
  rw [unifCell, Measure.smul_apply, Measure.restrict_apply_univ, volume_jcell hh, smul_eq_mul,
    ← ENNReal.ofReal_mul (by positivity), inv_mul_cancel₀ (by positivity), ENNReal.ofReal_one]

theorem unifCell_apply {A : Set (ℝ × ℝ)} (hA : MeasurableSet A) (c : Fin N × Fin N) :
    unifCell R h c A = ENNReal.ofReal ((h ^ 2)⁻¹) * volume (A ∩ jcell R h c) := by
  rw [unifCell, Measure.smul_apply, Measure.restrict_apply hA, smul_eq_mul]

theorem unifCell_singleton (c : Fin N × Fin N) (p : ℝ × ℝ) : unifCell R h c {p} = 0 := by
  rw [unifCell_apply (measurableSet_singleton p)]
  refine mul_eq_zero_of_right _ (measure_mono_null Set.inter_subset_left ?_)
  exact measure_singleton p

/-- The law of the random jittered set: independent uniform points in the cells. -/
def jlaw (N : ℕ) (R h : ℝ) : Measure (Fin N × Fin N → ℝ × ℝ) := Measure.pi (unifCell R h)

theorem isProbabilityMeasure_jlaw (hh : 0 < h) : IsProbabilityMeasure (jlaw N R h) := by
  haveI := fun c => isProbabilityMeasure_unifCell (N := N) (R := R) hh c
  unfold jlaw; infer_instance

open Classical in
/-- The number of points of a configuration in `A`. -/
def jcount (A : Set (ℝ × ℝ)) (ω : Fin N × Fin N → ℝ × ℝ) : ℕ :=
  (Finset.univ.filter fun c => ω c ∈ A).card

theorem ae_mem_jcell (hh : 0 < h) :
    ∀ᵐ ω ∂(jlaw N R h), ∀ c, ω c ∈ jcell R h c := by
  haveI := fun c => isProbabilityMeasure_unifCell (N := N) (R := R) hh c
  rw [ae_all_iff]
  intro c
  have : (jlaw N R h) {ω | ω c ∉ jcell R h c} = 0 := by
    have hp := measurePreserving_eval (unifCell (N := N) R h) c
    rw [show {ω : Fin N × Fin N → ℝ × ℝ | ω c ∉ jcell R h c} =
      Function.eval c ⁻¹' (jcell R h c)ᶜ from rfl, jlaw,
      hp.measure_preimage (measurableSet_jcell c).compl.nullMeasurableSet, unifCell_apply
      (measurableSet_jcell c).compl, Set.compl_inter_self, measure_empty, mul_zero]
  rw [ae_iff]; simpa using this

/-- A sub-Gaussian tail bound with an upper bound on the variance proxy. -/
theorem subG_tail {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : Ω → ℝ} {c : ℝ≥0} (hX : HasSubgaussianMGF X c μ) {x : ℝ} (hx : 0 < x) {C : ℝ}
    (hC : (c : ℝ) ≤ C) (hC0 : 0 < C) :
    μ {ω | x ≤ X ω} ≤ ENNReal.ofReal (Real.exp (-x ^ 2 / (2 * C))) := by
  by_cases hc : c = 0
  · subst hc
    have h0 := hX.ae_eq_zero_of_hasSubgaussianMGF_zero
    have : μ {ω | x ≤ X ω} = 0 := by
      have h1 : μ {ω | ¬ X ω = (0 : Ω → ℝ) ω} = 0 := ae_iff.1 h0
      refine measure_mono_null (fun ω hω => ?_) h1
      simp only [Set.mem_setOf_eq, Pi.zero_apply] at hω ⊢
      linarith
    rw [this]; exact zero_le
  · have hcpos : (0 : ℝ) < c := by positivity
    have h := hX.measure_ge_le hx.le
    rw [← ofReal_measureReal]
    refine ENNReal.ofReal_le_ofReal (h.trans (Real.exp_le_exp.2 ?_))
    rw [neg_div, neg_div, neg_le_neg_iff]
    exact div_le_div_of_nonneg_left (sq_nonneg x) (by positivity) (by linarith)

open Classical in
/-- **Hoeffding's inequality for the jittered count of a convex set.**  For a closed convex `P`,
`P(|#(P ∩ Λ) - E #(P ∩ Λ)| ≥ x) ≤ 2 exp(-x²/(8N))`: only the at most `12N + 4` cells meeting
the boundary of `P` contribute fluctuations. -/
theorem jcount_dev (hN : 1 ≤ N) (hh : 0 < h) {P : Set (ℝ × ℝ)} (hPc : Convex ℝ P)
    (hPcl : IsClosed P) {x : ℝ} (hx : 0 < x) :
    jlaw N R h {ω | x ≤ |(jcount P ω : ℝ) - ∑ c : Fin N × Fin N, (unifCell R h c P).toReal|} ≤
      ENNReal.ofReal (2 * Real.exp (-x ^ 2 / (8 * N))) := by
  haveI := fun c => isProbabilityMeasure_unifCell (N := N) (R := R) hh c
  haveI := isProbabilityMeasure_jlaw (N := N) (R := R) hh
  have hPm : MeasurableSet P := hPcl.measurableSet
  set p : Fin N × Fin N → ℝ := fun c => (unifCell R h c P).toReal with hp
  set X : Fin N × Fin N → (ℝ × ℝ) → ℝ := fun _ y => P.indicator (fun _ => (1 : ℝ)) y with hX
  have hXm : ∀ c, Measurable (X c) := fun c => measurable_const.indicator hPm
  set Y : Fin N × Fin N → (Fin N × Fin N → ℝ × ℝ) → ℝ := fun c ω => X c (ω c) - p c with hY
  have hindep : iIndepFun Y (jlaw N R h) := by
    have := iIndepFun_pi (μ := unifCell (N := N) R h)
      (X := fun c y => X c y - p c) (fun c => ((hXm c).sub measurable_const).aemeasurable)
    exact this
  -- the variance proxies
  set ab : Fin N × Fin N → ℝ × ℝ := fun c =>
    if jcell R h c ⊆ P then (1, 1) else if jcell R h c ∩ P = ∅ then (0, 0) else (0, 1) with hab
  have hint : ∀ c, ∫ ω, X c (ω c) ∂(jlaw N R h) = p c := by
    intro c
    have h1 := integral_map (μ := jlaw N R h) (measurable_pi_apply c).aemeasurable
      (hXm c).aestronglyMeasurable
    rw [show (jlaw N R h).map (fun ω => ω c) = unifCell R h c from
      (measurePreserving_eval (unifCell (N := N) R h) c).map_eq] at h1
    rw [← h1]
    simp only [hX, hp]
    rw [integral_indicator_const _ hPm, smul_eq_mul, mul_one, measureReal_def]
  have hsub : ∀ c, HasSubgaussianMGF (Y c) ((‖(ab c).2 - (ab c).1‖₊ / 2) ^ 2) (jlaw N R h) := by
    intro c
    have hm : AEMeasurable (fun ω : Fin N × Fin N → ℝ × ℝ => X c (ω c)) (jlaw N R h) :=
      ((hXm c).comp (measurable_pi_apply c)).aemeasurable
    have hb : ∀ᵐ ω ∂(jlaw N R h), X c (ω c) ∈ Set.Icc (ab c).1 (ab c).2 := by
      filter_upwards [ae_mem_jcell (N := N) (R := R) hh] with ω hω
      have hc := hω c
      simp only [hab, hX]
      split_ifs with h1 h2
      · rw [Set.indicator_of_mem (h1 hc)]; simp
      · have : ω c ∉ P := fun h' => by
          have : ω c ∈ jcell R h c ∩ P := ⟨hc, h'⟩; rw [h2] at this; exact this
        rw [Set.indicator_of_notMem this]; simp
      · by_cases h3 : ω c ∈ P
        · rw [Set.indicator_of_mem h3]; simp
        · rw [Set.indicator_of_notMem h3]; simp
    have := hasSubgaussianMGF_of_mem_Icc hm hb
    rw [hint c] at this
    exact this
  set cpar : Fin N × Fin N → ℝ≥0 := fun c => (‖(ab c).2 - (ab c).1‖₊ / 2) ^ 2 with hcpar
  have hcpar_le : ∀ c, (cpar c : ℝ) ≤ if (jcell R h c ∩ P).Nonempty ∧ ¬ jcell R h c ⊆ P
      then 1 / 4 else 0 := by
    intro c
    simp only [hcpar, hab]
    split_ifs with h1 h2 h3 h4 h5 <;> simp_all [Set.nonempty_iff_ne_empty] <;> norm_num
  have hsum_le : (∑ c, (cpar c : ℝ)) ≤ 3 * N + 1 := by
    calc (∑ c, (cpar c : ℝ)) ≤ ∑ c, (if (jcell R h c ∩ P).Nonempty ∧ ¬ jcell R h c ⊆ P
          then (1 / 4 : ℝ) else 0) := Finset.sum_le_sum fun c _ => hcpar_le c
      _ = (1 / 4 : ℝ) * (Finset.univ.filter fun c : Fin N × Fin N =>
            (jcell R h c ∩ P).Nonempty ∧ ¬ jcell R h c ⊆ P).card := by
          rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul,
            mul_comm]
      _ ≤ (1 / 4 : ℝ) * (12 * N + 4) := by
          gcongr
          exact_mod_cast card_partial_le (R := R) hh hPc hPcl
      _ = 3 * N + 1 := by ring
  have hS := HasSubgaussianMGF.sum_of_iIndepFun hindep (s := Finset.univ) fun c _ => hsub c
  have hC : (((∑ c, cpar c : ℝ≥0)) : ℝ) ≤ 4 * N := by
    push_cast; have : (1 : ℝ) ≤ N := by exact_mod_cast hN
    linarith
  have hN0 : (0 : ℝ) < 4 * N := by have : (1 : ℝ) ≤ N := by exact_mod_cast hN
                                   linarith
  have hup := subG_tail hS hx hC hN0
  have hlo := subG_tail hS.neg hx hC hN0
  have heq : ∀ ω, (jcount P ω : ℝ) - ∑ c, p c = ∑ c, Y c ω := by
    intro ω
    simp only [hY, hX, Finset.sum_sub_distrib, jcount]
    congr 1
    rw [Finset.sum_indicator_eq_sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one]
  calc jlaw N R h {ω | x ≤ |(jcount P ω : ℝ) - ∑ c, p c|}
      ≤ jlaw N R h ({ω | x ≤ ∑ c, Y c ω} ∪ {ω | x ≤ (-(fun ω => ∑ c, Y c ω)) ω}) := by
        refine measure_mono fun ω hω => ?_
        simp only [Set.mem_setOf_eq, heq] at hω
        rcases le_abs'.1 hω with h1 | h1
        · right; simp only [Set.mem_setOf_eq, Pi.neg_apply]; linarith
        · left; exact h1
    _ ≤ jlaw N R h {ω | x ≤ ∑ c, Y c ω} + jlaw N R h {ω | x ≤ (-(fun ω => ∑ c, Y c ω)) ω} :=
        measure_union_le _ _
    _ ≤ ENNReal.ofReal (Real.exp (-x ^ 2 / (2 * (4 * N)))) +
          ENNReal.ofReal (Real.exp (-x ^ 2 / (2 * (4 * N)))) := add_le_add hup hlo
    _ = ENNReal.ofReal (2 * Real.exp (-x ^ 2 / (8 * N))) := by
        rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
        congr 1; ring_nf

/-- **Chernoff's bound for the jittered count**:
`P(#(D ∩ Λ) ≥ k) ≤ exp(-θ k + (e^θ - 1) E #(D ∩ Λ))` for `θ ≥ 0`. -/
theorem jcount_ge_le (hh : 0 < h) {D : Set (ℝ × ℝ)} (hD : MeasurableSet D) {θ : ℝ} (hθ : 0 ≤ θ)
    (k : ℝ) :
    jlaw N R h {ω | k ≤ (jcount D ω : ℝ)} ≤
      ENNReal.ofReal (Real.exp (-θ * k + (Real.exp θ - 1) *
        ∑ c : Fin N × Fin N, (unifCell R h c D).toReal)) := by
  classical
  haveI := fun c => isProbabilityMeasure_unifCell (N := N) (R := R) hh c
  haveI := isProbabilityMeasure_jlaw (N := N) (R := R) hh
  set p : Fin N × Fin N → ℝ := fun c => (unifCell R h c D).toReal with hp
  set X : Fin N × Fin N → (Fin N × Fin N → ℝ × ℝ) → ℝ :=
    fun c ω => D.indicator (fun _ => (1 : ℝ)) (ω c) with hX
  have hXm : ∀ c, Measurable (X c) := fun c =>
    (measurable_const.indicator hD).comp (measurable_pi_apply c)
  have hindep : iIndepFun X (jlaw N R h) :=
    iIndepFun_pi (μ := unifCell (N := N) R h) (X := fun c y => D.indicator (fun _ => (1 : ℝ)) y)
      (fun c => (measurable_const.indicator hD).aemeasurable)
  have hcount : (fun ω => (jcount D ω : ℝ)) = ∑ c, X c := by
    ext ω
    simp only [jcount, hX, Finset.sum_apply]
    rw [Finset.sum_indicator_eq_sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one]
  have hint : ∀ c, ∫ ω, X c ω ∂(jlaw N R h) = p c := by
    intro c
    have hm1 : Measurable (D.indicator fun _ : ℝ × ℝ => (1 : ℝ)) := measurable_const.indicator hD
    have h1 := integral_map (μ := jlaw N R h) (measurable_pi_apply c).aemeasurable
      (f := D.indicator fun _ : ℝ × ℝ => (1 : ℝ)) hm1.aestronglyMeasurable
    rw [show (jlaw N R h).map (fun ω => ω c) = unifCell R h c from
      (measurePreserving_eval (unifCell (N := N) R h) c).map_eq] at h1
    simp only [hX]
    rw [← h1, integral_indicator_const _ hD, smul_eq_mul, mul_one, measureReal_def]
  have hmgf : ∀ c, mgf (X c) (jlaw N R h) θ ≤ Real.exp ((Real.exp θ - 1) * p c) := by
    intro c
    have hpt : ∀ ω, Real.exp (θ * X c ω) = 1 + (Real.exp θ - 1) * X c ω := by
      intro ω
      simp only [hX]
      by_cases hω : ω c ∈ D
      · rw [Set.indicator_of_mem hω]; ring_nf
      · rw [Set.indicator_of_notMem hω]; simp
    have hXi : Integrable (X c) (jlaw N R h) := by
      refine Integrable.of_bound (C := 1) (hXm c).aestronglyMeasurable (Eventually.of_forall ?_)
      intro ω; simp only [hX]
      by_cases hω : ω c ∈ D
      · rw [Set.indicator_of_mem hω]; simp
      · rw [Set.indicator_of_notMem hω]; simp
    rw [mgf]
    simp_rw [hpt]
    rw [integral_add (integrable_const _) (hXi.const_mul _), integral_const, integral_const_mul,
      hint c]
    simp only [measureReal_def, measure_univ, ENNReal.toReal_one, smul_eq_mul, one_mul]
    have := Real.add_one_le_exp ((Real.exp θ - 1) * p c)
    linarith
  have hexpint : Integrable (fun ω => Real.exp (θ * (jcount D ω : ℝ))) (jlaw N R h) := by
    refine Integrable.of_bound (C := Real.exp (θ * (N * N : ℕ))) ?_ (Eventually.of_forall ?_)
    · have hcm : Measurable (fun ω : Fin N × Fin N → ℝ × ℝ => (jcount D ω : ℝ)) := by
        rw [hcount]
        have := Finset.measurable_sum (Finset.univ : Finset (Fin N × Fin N)) fun c _ => hXm c
        convert this using 1; ext ω; simp
      exact (Real.measurable_exp.comp (measurable_const.mul hcm)).aestronglyMeasurable
    · intro ω
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      apply Real.exp_le_exp.2
      apply mul_le_mul_of_nonneg_left _ hθ
      have : jcount D ω ≤ N * N := by
        unfold jcount
        exact (Finset.card_filter_le _ _).trans (by simp)
      exact_mod_cast this
  have hch := measure_ge_le_exp_mul_mgf (μ := jlaw N R h) (X := fun ω => (jcount D ω : ℝ)) k hθ
    hexpint
  rw [hcount, hindep.mgf_sum hXm] at hch
  rw [← ofReal_measureReal]
  refine ENNReal.ofReal_le_ofReal (hch.trans ?_)
  rw [hcount] at *
  calc Real.exp (-θ * k) * ∏ c, mgf (X c) (jlaw N R h) θ
      ≤ Real.exp (-θ * k) * ∏ c, Real.exp ((Real.exp θ - 1) * p c) := by
        gcongr with c
        · exact fun c _ => mgf_nonneg
        · exact hmgf c
    _ = Real.exp (-θ * k + (Real.exp θ - 1) * ∑ c, p c) := by
        rw [← Real.exp_sum, ← Real.exp_add, Finset.mul_sum]

/-- A coordinate of a product of measures, atomless in that coordinate, is a.s. not a function of
the other coordinates. -/
theorem pi_coord_eq_null' {ι : Type*} [Fintype ι] [DecidableEq ι] (μs : ι → Measure (ℝ × ℝ))
    [∀ i, SigmaFinite (μs i)] (i : ι) (hμ : ∀ p, μs i {p} = 0) (G : (ι → ℝ × ℝ) → ℝ × ℝ)
    (hG : Measurable G) (hinv : ∀ x e, G (Function.update x i e) = G x) :
    (Measure.pi μs) {x | x i = G x} = 0 := by
  have hmp := measurePreserving_piEquivPiSubtypeProd μs (fun j => j = i)
  set e := MeasurableEquiv.piEquivPiSubtypeProd (fun _ : ι => ℝ × ℝ) (fun j => j = i) with he
  set G' : ({j // ¬ j = i} → ℝ × ℝ) → ℝ × ℝ := fun v => G (e.symm (fun _ => 0, v)) with hG'
  have hG'm : Measurable G' := hG.comp (e.symm.measurable.comp (measurable_const.prodMk measurable_id))
  have hupd : ∀ x : ι → ℝ × ℝ, e.symm (fun _ => 0, (e x).2) = Function.update x i 0 := by
    intro x
    ext1 j
    by_cases hj : j = i
    · subst hj; simp [he, MeasurableEquiv.piEquivPiSubtypeProd, Equiv.piEquivPiSubtypeProd]
    · simp [he, MeasurableEquiv.piEquivPiSubtypeProd, Equiv.piEquivPiSubtypeProd, hj]
  have hset : {x : ι → ℝ × ℝ | x i = G x} = e ⁻¹' {q | q.1 ⟨i, rfl⟩ = G' q.2} := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_preimage, hG', hupd, hinv]
    rfl
  have hSm : MeasurableSet {q : ({j // j = i} → ℝ × ℝ) × ({j // ¬ j = i} → ℝ × ℝ) |
      q.1 ⟨i, rfl⟩ = G' q.2} :=
    measurableSet_eq_fun ((measurable_pi_apply _).comp measurable_fst) (hG'm.comp measurable_snd)
  rw [hset, hmp.measure_preimage hSm.nullMeasurableSet, Measure.prod_apply_symm hSm]
  refine (lintegral_congr fun v => ?_).trans lintegral_zero
  have : (fun u : {j // j = i} → ℝ × ℝ => (u, v)) ⁻¹'
      {q : ({j // j = i} → ℝ × ℝ) × ({j // ¬ j = i} → ℝ × ℝ) | q.1 ⟨i, rfl⟩ = G' q.2} =
      @Function.eval {j // j = i} (fun _ => ℝ × ℝ) ⟨i, rfl⟩ ⁻¹' ({G' v} : Set (ℝ × ℝ)) := by
    ext u; simp
  rw [this]
  convert Measure.pi_eval_preimage_null (μ := fun j : {j // j = i} => μs ↑j)
    (i := (⟨i, rfl⟩ : {j // j = i})) (s := ({G' v} : Set (ℝ × ℝ))) (hμ (G' v))

/-- **The random jittered set has no repeated difference vectors**, almost surely. -/
theorem jlaw_distinct_diff (hh : 0 < h) :
    ∀ᵐ ω ∂(jlaw N R h), ∀ c₁ c₂ c₃ c₄ : Fin N × Fin N, c₁ ≠ c₂ → c₃ ≠ c₄ →
      (c₁, c₂) ≠ (c₃, c₄) → ω c₁ - ω c₂ ≠ ω c₃ - ω c₄ := by
  classical
  haveI := fun c => isProbabilityMeasure_unifCell (N := N) (R := R) hh c
  simp only [ae_all_iff]
  intro c₁ c₂ c₃ c₄ h12 h34 hp
  set I : Fin 4 → Fin N × Fin N := ![c₁, c₂, c₃, c₄] with hI
  obtain ⟨a, ha⟩ := exists_coef4_ne I h12 h34 hp
  set J := I a with hJ
  set κ := coef4 I J with hκ
  set G : (Fin N × Fin N → ℝ × ℝ) → ℝ × ℝ :=
    fun ω => -κ⁻¹ • ∑ b, (if I b = J then 0 else sgn4 b • ω (I b)) with hG
  have hRm : Measurable fun ω : Fin N × Fin N → ℝ × ℝ =>
      ∑ b, (if I b = J then (0 : ℝ × ℝ) else sgn4 b • ω (I b)) := by
    refine Finset.measurable_sum (f := fun b (ω : Fin N × Fin N → ℝ × ℝ) =>
      if I b = J then (0 : ℝ × ℝ) else sgn4 b • ω (I b)) _ fun b _ => ?_
    by_cases hb : I b = J
    · simp only [hb, if_true]; exact measurable_const
    · simp only [hb, if_false]
      exact (measurable_pi_apply (X := fun _ : Fin N × Fin N => ℝ × ℝ) (I b)).const_smul (sgn4 b)
  have hGm : Measurable G := (measurable_const (a := -κ⁻¹)).smul hRm
  have hinv : ∀ x e, G (Function.update x J e) = G x := by
    intro x e
    simp only [hG]
    congr 1
    refine Finset.sum_congr rfl fun b _ => ?_
    by_cases hb : I b = J
    · simp [hb]
    · simp only [hb, if_false]
      rw [Function.update_of_ne hb]
  have hnull := pi_coord_eq_null' (unifCell (N := N) R h) J (unifCell_singleton J) G hGm hinv
  have hsub : {ω : Fin N × Fin N → ℝ × ℝ | ω c₁ - ω c₂ = ω c₃ - ω c₄} ⊆ {x | x J = G x} := by
    intro ω hω
    simp only [Set.mem_setOf_eq] at hω ⊢
    have hsum : ∑ b, sgn4 b • ω (I b) = 0 := by
      rw [Fin.sum_univ_four]
      have e0 : I 0 = c₁ := rfl
      have e1 : I 1 = c₂ := rfl
      have e2 : I 2 = c₃ := rfl
      have e3 : I 3 = c₄ := rfl
      have s0 : sgn4 0 = 1 := rfl
      have s1 : sgn4 1 = -1 := rfl
      have s2 : sgn4 2 = -1 := rfl
      have s3 : sgn4 3 = 1 := rfl
      rw [e0, e1, e2, e3, s0, s1, s2, s3, one_smul, one_smul, neg_one_smul, neg_one_smul]
      have : ω c₁ - ω c₂ - (ω c₃ - ω c₄) = 0 := by rw [hω, sub_self]
      rw [← this]; abel
    rw [sum_sgn4_split I J] at hsum
    have hκ0 : κ ≠ 0 := ha
    have h2 := congrArg (fun v => κ⁻¹ • v) hsum
    simp only [smul_add, smul_zero, smul_smul] at h2
    rw [← hκ, inv_mul_cancel₀ hκ0, one_smul] at h2
    simp only [hG]
    rw [neg_smul, eq_neg_iff_add_eq_zero]; exact h2
  rw [ae_iff]
  refine measure_mono_null (fun ω hω => ?_) hnull
  simp only [Set.mem_setOf_eq, not_not] at hω
  exact hsub hω

/-! ### The cells tile the window -/

/-- The closed window `[-R, R]²`. -/
def jwin (R : ℝ) : Set (ℝ × ℝ) := Set.Icc (-R) R ×ˢ Set.Icc (-R) R

/-- The half-open window `[-R, R)²`, the union of the cells. -/
def jwinh (R : ℝ) : Set (ℝ × ℝ) := Set.Ico (-R) R ×ˢ Set.Ico (-R) R

theorem jcell_disjoint (hh : 0 < h) : Pairwise (Disjoint on (jcell (N := N) R h)) := by
  intro c c' hcc'
  refine Set.disjoint_left.2 fun x hx hx' => hcc' ?_
  have key : ∀ (i i' : Fin N) (y : ℝ), y ∈ Set.Ico (-R + (i : ℝ) * h) (-R + ((i : ℝ) + 1) * h) →
      y ∈ Set.Ico (-R + (i' : ℝ) * h) (-R + ((i' : ℝ) + 1) * h) → i = i' := by
    intro i i' y hy hy'
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hlt
    · have := lt_of_mem_jcell_lt hh hlt hy hy'; linarith [hy.1, hy'.2, this]
    · have := lt_of_mem_jcell_lt hh hlt hy' hy; linarith
  exact Prod.ext (key _ _ _ hx.1 hx'.1) (key _ _ _ hx.2 hx'.2)

theorem iUnion_jcell (hh : 0 < h) (hNh : (N : ℝ) * h = 2 * R) :
    (⋃ c : Fin N × Fin N, jcell R h c) = jwinh R := by
  ext x
  simp only [Set.mem_iUnion, jwinh, jcell, Set.mem_prod, Set.mem_Ico]
  constructor
  · rintro ⟨c, ⟨h1, h2⟩, ⟨h3, h4⟩⟩
    have hc1 : ((c.1 : ℕ) : ℝ) + 1 ≤ N := by exact_mod_cast c.1.2
    have hc2 : ((c.2 : ℕ) : ℝ) + 1 ≤ N := by exact_mod_cast c.2.2
    have e1 := mul_le_mul_of_nonneg_right hc1 hh.le
    have e2 := mul_le_mul_of_nonneg_right hc2 hh.le
    refine ⟨⟨by nlinarith, by nlinarith⟩, ⟨by nlinarith, by nlinarith⟩⟩
  · rintro ⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩
    have idx : ∀ y : ℝ, -R ≤ y → y < R → ∃ i : Fin N,
        -R + (i : ℝ) * h ≤ y ∧ y < -R + ((i : ℝ) + 1) * h := by
      intro y hy1 hy2
      set t := (y + R) / h with ht
      have ht0 : 0 ≤ t := div_nonneg (by linarith) hh.le
      have htN : t < N := by rw [ht, div_lt_iff₀ hh]; linarith
      have hfl : ⌊t⌋₊ < N := by
        have := Nat.floor_lt ht0 |>.2 htN; exact_mod_cast this
      refine ⟨⟨⌊t⌋₊, hfl⟩, ?_, ?_⟩
      · have := Nat.floor_le ht0
        simp only
        have : (⌊t⌋₊ : ℝ) * h ≤ y + R := by rw [ht, le_div_iff₀ hh] at this; exact this
        linarith
      · have := Nat.lt_floor_add_one t
        simp only
        have : y + R < ((⌊t⌋₊ : ℝ) + 1) * h := by rw [ht, div_lt_iff₀ hh] at this; exact this
        linarith
    obtain ⟨i, hi1, hi2⟩ := idx x.1 h1 h2
    obtain ⟨j, hj1, hj2⟩ := idx x.2 h3 h4
    exact ⟨(i, j), ⟨hi1, hi2⟩, ⟨hj1, hj2⟩⟩

theorem volume_jwin_diff : volume (jwin R \ jwinh R) = 0 := by
  have hsub : jwin R \ jwinh R ⊆ ({R} ×ˢ Set.univ) ∪ (Set.univ ×ˢ {R}) := by
    rintro x ⟨⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩, hx⟩
    simp only [jwinh, Set.mem_prod, Set.mem_Ico, not_and_or, not_lt] at hx
    rcases hx with (hx | hx) | (hx | hx)
    · exact absurd h1 hx
    · left; exact ⟨le_antisymm h2 hx, Set.mem_univ _⟩
    · exact absurd h3 hx
    · right; exact ⟨Set.mem_univ _, le_antisymm h4 hx⟩
  refine measure_mono_null hsub (measure_union_null ?_ ?_)
  · rw [Measure.volume_eq_prod, Measure.prod_prod, Real.volume_singleton, zero_mul]
  · rw [Measure.volume_eq_prod, Measure.prod_prod, Real.volume_singleton, mul_zero]

theorem sum_unifCell (hh : 0 < h) (hNh : (N : ℝ) * h = 2 * R) {P : Set (ℝ × ℝ)}
    (hP : MeasurableSet P) :
    ∑ c : Fin N × Fin N, (unifCell R h c P).toReal = (h ^ 2)⁻¹ * (volume (P ∩ jwinh R)).toReal := by
  have hfin : ∀ c : Fin N × Fin N, volume (P ∩ jcell R h c) ≠ ⊤ := fun c =>
    ne_top_of_le_ne_top (by rw [volume_jcell hh]; exact ENNReal.ofReal_ne_top)
      (measure_mono Set.inter_subset_right)
  simp_rw [unifCell_apply hP, ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity : (0:ℝ) ≤ (h ^ 2)⁻¹)]
  rw [← Finset.mul_sum, ← ENNReal.toReal_sum (fun c _ => hfin c)]
  congr 2
  rw [← iUnion_jcell (N := N) hh hNh, Set.inter_iUnion, measure_iUnion]
  · rw [tsum_fintype]
  · intro c c' hcc'
    exact (jcell_disjoint hh hcc').mono Set.inter_subset_right Set.inter_subset_right
  · intro c; exact hP.inter (measurableSet_jcell c)

theorem jcount_mono {A B : Set (ℝ × ℝ)} (hAB : A ⊆ B) (ω : Fin N × Fin N → ℝ × ℝ) :
    jcount A ω ≤ jcount B ω := by
  classical
  unfold jcount
  apply Finset.card_le_card
  intro c hc
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hc ⊢
  exact hAB hc

theorem convex_jwin : Convex ℝ (jwin R) := (convex_Icc _ _).prod (convex_Icc _ _)

theorem volume_jwin_lt_top : volume (jwin R) < ⊤ := by
  rw [jwin, Measure.volume_eq_prod, Measure.prod_prod, Real.volume_Icc]
  exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top

open Classical in
/-- **The deterministic estimate for a good configuration.**  If the counts of the rounded
polygons deviate from their means by less than `x` and every strip holds fewer than `20` points,
then every convex polygon `A` with at most `k` vertices in the window, with any part of its
boundary, satisfies `|h² #(A ∩ Λ) - leb(A)| ≤ h² x + 19 h² k² + k² D_max`. -/
theorem jitter_bound_of_good (hh : 0 < h) (hNh : (N : ℝ) * h = 2 * R) {δ : ℝ} (hδ : 0 < δ)
    {G : Finset (ℤ × ℤ)} {k : ℕ} {x Dmax : ℝ} (hDmax : 0 ≤ Dmax) (ω : Fin N × Fin N → ℝ × ℝ)
    (hP : ∀ I ⊆ G, I.card ≤ k →
      |(jcount (pplus δ I) ω : ℝ) - ∑ c : Fin N × Fin N, (unifCell R h c (pplus δ I)).toReal| < x)
    (hD : ∀ g ∈ G, ∀ g' ∈ G, jcount (dset δ g g') ω < 20)
    (hGW : ∀ v ∈ jwin R, gidx δ v ∈ G)
    (hvolD : ∀ g ∈ G, ∀ g' ∈ G, (volume (dset δ g g')).toReal ≤ Dmax)
    (V : Finset (ℝ × ℝ)) (hVW : (V : Set (ℝ × ℝ)) ⊆ jwin R) (hVk : V.card ≤ k)
    (A : Set (ℝ × ℝ)) (hA1 : interior (convexHull ℝ (V : Set (ℝ × ℝ))) ⊆ A)
    (hA2 : A ⊆ convexHull ℝ (V : Set (ℝ × ℝ))) :
    |h ^ 2 * jcount A ω - (volume A).toReal| ≤ h ^ 2 * x + 19 * h ^ 2 * k ^ 2 + k ^ 2 * Dmax := by
  set I := V.image (gidx δ) with hI
  have hIG : I ⊆ G := by
    intro g hg
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.1 hg
    exact hGW v (hVW hv)
  have hIk : I.card ≤ k := Finset.card_image_le.trans hVk
  set Pp := pplus δ I with hPp
  have hPpm : MeasurableSet Pp := (isCompact_pplus hδ I).isClosed.measurableSet
  have hconvW : convexHull ℝ (V : Set (ℝ × ℝ)) ⊆ jwin R := convexHull_min hVW convex_jwin
  have hAW : A ⊆ jwin R := hA2.trans hconvW
  have hAPp : A ⊆ Pp := hA2.trans (convexHull_subset_pplus hδ V)
  set Ds := fun p : (ℝ × ℝ) × (ℝ × ℝ) => dset δ (gidx δ p.1) (gidx δ p.2) with hDs
  have hcover : Pp ⊆ A ∪ ⋃ p ∈ V ×ˢ V, Ds p := by
    intro y hy
    by_cases hyA : y ∈ A
    · exact Or.inl hyA
    · right
      have hyi : y ∉ interior (convexHull ℝ (V : Set (ℝ × ℝ))) := fun h' => hyA (hA1 h')
      obtain ⟨a, ha, b, hb, hyab⟩ := pplus_diff_subset hδ V hy hyi
      simp only [Set.mem_iUnion, exists_prop]
      exact ⟨(a, b), Finset.mem_product.2 ⟨ha, hb⟩, hyab⟩
  -- counts
  have hcA : jcount A ω ≤ jcount Pp ω := jcount_mono hAPp ω
  have hcP : jcount Pp ω ≤ jcount A ω + ∑ p ∈ V ×ˢ V, jcount (Ds p) ω := by
    unfold jcount
    calc (Finset.univ.filter fun c => ω c ∈ Pp).card
        ≤ ((Finset.univ.filter fun c => ω c ∈ A) ∪
            (V ×ˢ V).biUnion fun p => Finset.univ.filter fun c => ω c ∈ Ds p).card := by
          apply Finset.card_le_card
          intro c hc
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hc
          rcases hcover hc with h1 | h1
          · exact Finset.mem_union_left _ (by simpa using h1)
          · simp only [Set.mem_iUnion, exists_prop] at h1
            obtain ⟨p, hp, hcp⟩ := h1
            exact Finset.mem_union_right _ (Finset.mem_biUnion.2 ⟨p, hp, by simpa using hcp⟩)
      _ ≤ _ := (Finset.card_union_le _ _).trans (add_le_add le_rfl Finset.card_biUnion_le)
  have hsD : (∑ p ∈ V ×ˢ V, (jcount (Ds p) ω : ℝ)) ≤ 19 * k ^ 2 := by
    calc (∑ p ∈ V ×ˢ V, (jcount (Ds p) ω : ℝ)) ≤ ∑ _p ∈ V ×ˢ V, (19 : ℝ) := by
          refine Finset.sum_le_sum fun p hp => ?_
          obtain ⟨h1, h2⟩ := Finset.mem_product.1 hp
          have := hD _ (hGW _ (hVW h1)) _ (hGW _ (hVW h2))
          have : jcount (Ds p) ω ≤ 19 := by simp only [hDs]; omega
          exact_mod_cast this
      _ = 19 * ((V.card : ℝ) * V.card) := by
          rw [Finset.sum_const, Finset.card_product, nsmul_eq_mul]; push_cast; ring
      _ ≤ 19 * k ^ 2 := by
          have : (V.card : ℝ) ≤ k := by exact_mod_cast hVk
          nlinarith [Nat.cast_nonneg (α := ℝ) V.card]
  -- volumes
  have hfinA : volume A ≠ ⊤ := ne_top_of_le_ne_top volume_jwin_lt_top.ne (measure_mono hAW)
  have hfinPp : volume (Pp ∩ jwinh R) ≠ ⊤ := ne_top_of_le_ne_top volume_jwin_lt_top.ne
    (measure_mono (Set.inter_subset_right.trans (Set.prod_mono Set.Ico_subset_Icc_self
      Set.Ico_subset_Icc_self)))
  have hvol1 : (volume (Pp ∩ jwinh R)).toReal ≤ (volume A).toReal + k ^ 2 * Dmax := by
    have h1 : volume (Pp ∩ jwinh R) ≤ volume A + ∑ p ∈ V ×ˢ V, volume (Ds p) :=
      (measure_mono (Set.inter_subset_left.trans hcover)).trans
        ((measure_union_le _ _).trans (add_le_add le_rfl (measure_biUnion_finset_le _ _)))
    have hfinD : ∀ p ∈ V ×ˢ V, volume (Ds p) ≠ ⊤ := fun p _ =>
      (isCompact_dset hδ _ _).measure_lt_top.ne
    have h2 := ENNReal.toReal_mono (ENNReal.add_ne_top.2 ⟨hfinA,
      (ENNReal.sum_ne_top.2 hfinD)⟩) h1
    rw [ENNReal.toReal_add hfinA (ENNReal.sum_ne_top.2 hfinD), ENNReal.toReal_sum hfinD] at h2
    have h3 : (∑ p ∈ V ×ˢ V, (volume (Ds p)).toReal) ≤ k ^ 2 * Dmax := by
      calc (∑ p ∈ V ×ˢ V, (volume (Ds p)).toReal) ≤ ∑ _p ∈ V ×ˢ V, Dmax := by
            refine Finset.sum_le_sum fun p hp => ?_
            obtain ⟨h1, h2⟩ := Finset.mem_product.1 hp
            exact hvolD _ (hGW _ (hVW h1)) _ (hGW _ (hVW h2))
        _ = ((V.card : ℝ) * V.card) * Dmax := by
            rw [Finset.sum_const, Finset.card_product, nsmul_eq_mul]; push_cast; ring
        _ ≤ k ^ 2 * Dmax := by
            apply mul_le_mul_of_nonneg_right _ hDmax
            have : (V.card : ℝ) ≤ k := by exact_mod_cast hVk
            nlinarith [Nat.cast_nonneg (α := ℝ) V.card]
    linarith
  have hvol2 : (volume A).toReal ≤ (volume (Pp ∩ jwinh R)).toReal := by
    have h1 : volume A ≤ volume (Pp ∩ jwinh R) + volume (jwin R \ jwinh R) := by
      refine (measure_mono fun y hy => ?_).trans (measure_union_le _ _)
      by_cases hy' : y ∈ jwinh R
      · exact Or.inl ⟨hAPp hy, hy'⟩
      · exact Or.inr ⟨hAW hy, hy'⟩
    rw [volume_jwin_diff, add_zero] at h1
    exact ENNReal.toReal_mono hfinPp h1
  -- the mean of the rounded polygon
  have hm := sum_unifCell (N := N) hh hNh hPpm
  have hdev := hP I hIG hIk
  rw [hm] at hdev
  rw [abs_lt] at hdev
  have hh2 : 0 < h ^ 2 := by positivity
  have hcA' : (jcount A ω : ℝ) ≤ jcount Pp ω := by exact_mod_cast hcA
  have hcP' : (jcount Pp ω : ℝ) ≤ jcount A ω + ∑ p ∈ V ×ˢ V, (jcount (Ds p) ω : ℝ) := by
    exact_mod_cast hcP
  set m := (volume (Pp ∩ jwinh R)).toReal with hmdef
  have e1 : h ^ 2 * ((h ^ 2)⁻¹ * m) = m := by field_simp
  rw [abs_le]
  constructor
  · -- lower bound
    have : (jcount A ω : ℝ) ≥ (h ^ 2)⁻¹ * m - x - 19 * k ^ 2 := by linarith
    have := mul_le_mul_of_nonneg_left this hh2.le
    rw [mul_sub, mul_sub, e1] at this
    nlinarith
  · -- upper bound
    have : (jcount A ω : ℝ) ≤ (h ^ 2)⁻¹ * m + x := by linarith
    have := mul_le_mul_of_nonneg_left this hh2.le
    rw [mul_add, e1] at this
    nlinarith

/-- The subsets of `G` with at most `k` elements. -/
def smallSets (G : Finset (ℤ × ℤ)) (k : ℕ) : Finset (Finset (ℤ × ℤ)) :=
  (Finset.range (k + 1)).biUnion fun j => G.powersetCard j

theorem mem_smallSets {G I : Finset (ℤ × ℤ)} {k : ℕ} : I ∈ smallSets G k ↔ I ⊆ G ∧ I.card ≤ k := by
  simp only [smallSets, Finset.mem_biUnion, Finset.mem_range, Finset.mem_powersetCard]
  constructor
  · rintro ⟨j, hj, hIG, rfl⟩; exact ⟨hIG, by omega⟩
  · rintro ⟨hIG, hk⟩; exact ⟨I.card, by omega, hIG, rfl⟩

theorem card_smallSets_le (G : Finset (ℤ × ℤ)) (k : ℕ) (hG : 1 ≤ G.card) :
    ((smallSets G k).card : ℝ) ≤ (k + 1) * (G.card : ℝ) ^ k := by
  have h1 : (smallSets G k).card ≤ ∑ j ∈ Finset.range (k + 1), (G.powersetCard j).card :=
    Finset.card_biUnion_le
  have h2 : ∀ j ∈ Finset.range (k + 1), (G.powersetCard j).card ≤ G.card ^ k := by
    intro j hj
    rw [Finset.card_powersetCard]
    refine (Nat.choose_le_pow _ _).trans (Nat.pow_le_pow_right hG ?_)
    rw [Finset.mem_range] at hj; omega
  have h3 : (smallSets G k).card ≤ (k + 1) * G.card ^ k := by
    refine h1.trans ((Finset.sum_le_sum h2).trans ?_)
    rw [Finset.sum_const, Finset.card_range, smul_eq_mul]
  exact_mod_cast h3

open Classical in
/-- **The probabilistic method.**  If the union bound over the rounded polygons and the strips is
less than `1`, a good jittered configuration exists. -/
theorem exists_good_config (hN : 1 ≤ N) (hh : 0 < h) {δ : ℝ} (hδ : 0 < δ) {G : Finset (ℤ × ℤ)}
    {k : ℕ} {x θ S : ℝ} (hx : 0 < x) (hθ : 0 ≤ θ)
    (hS : ∀ g ∈ G, ∀ g' ∈ G, ∑ c : Fin N × Fin N, (unifCell R h c (dset δ g g')).toReal ≤ S)
    (hsmall : ((smallSets G k).card : ℝ) * (2 * Real.exp (-x ^ 2 / (8 * N))) +
      ((G ×ˢ G).card : ℝ) * Real.exp (-θ * 20 + (Real.exp θ - 1) * S) < 1) :
    ∃ ω : Fin N × Fin N → ℝ × ℝ, (∀ c, ω c ∈ jcell R h c) ∧
      (∀ c₁ c₂ c₃ c₄ : Fin N × Fin N, c₁ ≠ c₂ → c₃ ≠ c₄ → (c₁, c₂) ≠ (c₃, c₄) →
        ω c₁ - ω c₂ ≠ ω c₃ - ω c₄) ∧
      (∀ I ⊆ G, I.card ≤ k →
        |(jcount (pplus δ I) ω : ℝ) - ∑ c : Fin N × Fin N, (unifCell R h c (pplus δ I)).toReal| < x) ∧
      (∀ g ∈ G, ∀ g' ∈ G, jcount (dset δ g g') ω < 20) := by
  haveI := isProbabilityMeasure_jlaw (N := N) (R := R) hh
  set P := jlaw N R h with hP
  set B1 := ⋃ I ∈ smallSets G k, {ω : Fin N × Fin N → ℝ × ℝ |
    x ≤ |(jcount (pplus δ I) ω : ℝ) - ∑ c : Fin N × Fin N, (unifCell R h c (pplus δ I)).toReal|}
  set B2 := ⋃ p ∈ G ×ˢ G, {ω : Fin N × Fin N → ℝ × ℝ | (20 : ℝ) ≤ jcount (dset δ p.1 p.2) ω}
  set B3 := {ω : Fin N × Fin N → ℝ × ℝ | ¬ ∀ c, ω c ∈ jcell R h c}
  set B4 := {ω : Fin N × Fin N → ℝ × ℝ | ¬ ∀ c₁ c₂ c₃ c₄ : Fin N × Fin N, c₁ ≠ c₂ → c₃ ≠ c₄ →
    (c₁, c₂) ≠ (c₃, c₄) → ω c₁ - ω c₂ ≠ ω c₃ - ω c₄}
  have hB1 : P B1 ≤ ENNReal.ofReal (((smallSets G k).card : ℝ) * (2 * Real.exp (-x ^ 2 / (8 * N)))) := by
    refine (measure_biUnion_finset_le _ _).trans ?_
    calc ∑ I ∈ smallSets G k, P {ω : Fin N × Fin N → ℝ × ℝ |
          x ≤ |(jcount (pplus δ I) ω : ℝ) - ∑ c : Fin N × Fin N, (unifCell R h c (pplus δ I)).toReal|}
        ≤ ∑ _I ∈ smallSets G k, ENNReal.ofReal (2 * Real.exp (-x ^ 2 / (8 * N))) :=
          Finset.sum_le_sum fun I _ => jcount_dev hN hh (convex_convexHull ℝ _)
            (isCompact_pplus hδ I).isClosed hx
      _ = _ := by
          rw [Finset.sum_const, nsmul_eq_mul, ← ENNReal.ofReal_natCast,
            ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
  have hB2 : P B2 ≤ ENNReal.ofReal (((G ×ˢ G).card : ℝ) *
      Real.exp (-θ * 20 + (Real.exp θ - 1) * S)) := by
    refine (measure_biUnion_finset_le _ _).trans ?_
    calc ∑ p ∈ G ×ˢ G, P {ω : Fin N × Fin N → ℝ × ℝ | (20 : ℝ) ≤ jcount (dset δ p.1 p.2) ω}
        ≤ ∑ _p ∈ G ×ˢ G, ENNReal.ofReal (Real.exp (-θ * 20 + (Real.exp θ - 1) * S)) := by
          refine Finset.sum_le_sum fun p hp => ?_
          obtain ⟨h1, h2⟩ := Finset.mem_product.1 hp
          refine (jcount_ge_le hh (isCompact_dset hδ _ _).isClosed.measurableSet hθ 20).trans ?_
          apply ENNReal.ofReal_le_ofReal
          apply Real.exp_le_exp.2
          have : 0 ≤ Real.exp θ - 1 := by linarith [Real.add_one_le_exp θ]
          have := mul_le_mul_of_nonneg_left (hS _ h1 _ h2) this
          linarith
      _ = _ := by
          rw [Finset.sum_const, nsmul_eq_mul, ← ENNReal.ofReal_natCast,
            ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
  have hB3 : P B3 = 0 := by
    have := ae_mem_jcell (N := N) (R := R) hh; rw [ae_iff] at this; exact this
  have hB4 : P B4 = 0 := by
    have := jlaw_distinct_diff (N := N) (R := R) hh; rw [ae_iff] at this; exact this
  have htot : P (B1 ∪ B2 ∪ B3 ∪ B4) < 1 := by
    calc P (B1 ∪ B2 ∪ B3 ∪ B4) ≤ P B1 + P B2 + P B3 + P B4 :=
          (measure_union_le _ _).trans (add_le_add ((measure_union_le _ _).trans
            (add_le_add (measure_union_le _ _) le_rfl)) le_rfl)
      _ ≤ ENNReal.ofReal (((smallSets G k).card : ℝ) * (2 * Real.exp (-x ^ 2 / (8 * N)))) +
          ENNReal.ofReal (((G ×ˢ G).card : ℝ) * Real.exp (-θ * 20 + (Real.exp θ - 1) * S)) + 0 + 0 := by
          rw [hB3, hB4]; exact add_le_add (add_le_add (add_le_add hB1 hB2) le_rfl) le_rfl
      _ < 1 := by
          rw [add_zero, add_zero, ← ENNReal.ofReal_add (by positivity) (by positivity),
            ← ENNReal.ofReal_one]
          exact (ENNReal.ofReal_lt_ofReal_iff one_pos).2 hsmall
  obtain ⟨ω, hω⟩ : ∃ ω, ω ∉ B1 ∪ B2 ∪ B3 ∪ B4 := by
    by_contra hcon
    push_neg at hcon
    have : P (B1 ∪ B2 ∪ B3 ∪ B4) = 1 := by
      rw [Set.eq_univ_of_forall hcon, measure_univ]
    rw [this] at htot; exact lt_irrefl _ htot
  simp only [Set.mem_union, not_or] at hω
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := hω
  refine ⟨ω, not_not.1 h3, not_not.1 h4, fun I hIG hIk => ?_, fun g hg g' hg' => ?_⟩
  · have hI : I ∈ smallSets G k := mem_smallSets.2 ⟨hIG, hIk⟩
    by_contra hcon
    push_neg at hcon
    exact h1 (Set.mem_biUnion hI hcon)
  · by_contra hcon
    push_neg at hcon
    have h20 : (20 : ℝ) ≤ jcount (dset δ g g') ω := by exact_mod_cast hcon
    exact h2 (Set.mem_biUnion (x := (g, g')) (Finset.mem_product.2 ⟨hg, hg'⟩) h20)

/-- The grid of boxes of side `δ` covering the window `[-R, R]²`. -/
def jgrid (R δ : ℝ) : Finset (ℤ × ℤ) :=
  let M : ℤ := ⌈R / δ⌉₊ + 1
  Finset.Icc (-M) M ×ˢ Finset.Icc (-M) M

theorem gidx_mem_jgrid {R δ : ℝ} (hR : 0 < R) (hδ : 0 < δ) {v : ℝ × ℝ} (hv : v ∈ jwin R) :
    gidx δ v ∈ jgrid R δ := by
  obtain ⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩ := hv
  have hc : R / δ ≤ ⌈R / δ⌉₊ := Nat.le_ceil _
  have key : ∀ y : ℝ, -R ≤ y → y ≤ R → (-((⌈R / δ⌉₊ : ℤ) + 1) ≤ ⌊y / δ⌋ ∧ ⌊y / δ⌋ ≤ (⌈R / δ⌉₊ : ℤ) + 1) := by
    intro y hy1 hy2
    constructor
    · have : -(R / δ) - 1 < (⌊y / δ⌋ : ℝ) := by
        have := Int.lt_floor_add_one (y / δ)
        have : -(R / δ) ≤ y / δ := by rw [← neg_div]; exact div_le_div_of_nonneg_right hy1 hδ.le
        linarith
      have : (-((⌈R / δ⌉₊ : ℤ) + 1) : ℝ) < ⌊y / δ⌋ + 1 := by push_cast; linarith
      have := this
      exact_mod_cast (show (-((⌈R / δ⌉₊ : ℤ) + 1) : ℤ) ≤ ⌊y / δ⌋ by
        have h' : ((-((⌈R / δ⌉₊ : ℤ) + 1) : ℤ) : ℝ) < ((⌊y / δ⌋ + 1 : ℤ) : ℝ) := by push_cast; linarith
        have := Int.cast_lt.1 h'; omega)
    · have : (⌊y / δ⌋ : ℝ) ≤ R / δ := (Int.floor_le _).trans (div_le_div_of_nonneg_right hy2 hδ.le)
      have h' : ((⌊y / δ⌋ : ℤ) : ℝ) ≤ (((⌈R / δ⌉₊ : ℤ) + 1 : ℤ) : ℝ) := by push_cast; linarith
      exact_mod_cast h'
  simp only [jgrid, gidx, Finset.mem_product, Finset.mem_Icc]
  exact ⟨key v.1 h1 h2, key v.2 h3 h4⟩

theorem card_jgrid_le {R δ : ℝ} (hR : 0 < R) (hδ : 0 < δ) :
    ((jgrid R δ).card : ℝ) ≤ (2 * R / δ + 5) ^ 2 := by
  simp only [jgrid, Finset.card_product, Int.card_Icc]
  have hc := Nat.ceil_lt_add_one (show 0 ≤ R / δ by positivity)
  have e : (((⌈R / δ⌉₊ : ℤ) + 1 + 1 - -((⌈R / δ⌉₊ : ℤ) + 1)).toNat : ℝ) = 2 * ⌈R / δ⌉₊ + 3 := by
    have : ((⌈R / δ⌉₊ : ℤ) + 1 + 1 - -((⌈R / δ⌉₊ : ℤ) + 1)) = ((2 * ⌈R / δ⌉₊ + 3 : ℕ) : ℤ) := by
      push_cast; ring
    rw [this, Int.toNat_natCast]; push_cast; ring
  push_cast
  rw [e, ← sq]
  apply pow_le_pow_left₀ (by positivity)
  have : (2 : ℝ) * R / δ = 2 * (R / δ) := by ring
  linarith

theorem jgrid_cen_dist {R δ : ℝ} (hR : 0 < R) (hδ : 0 < δ) {g g' : ℤ × ℤ} (hg : g ∈ jgrid R δ)
    (hg' : g' ∈ jgrid R δ) : ‖gcen δ g' - gcen δ g‖ ≤ 2 * R + 4 * δ := by
  simp only [jgrid, Finset.mem_product, Finset.mem_Icc] at hg hg'
  have hc := Nat.ceil_lt_add_one (show 0 ≤ R / δ by positivity)
  have hM : (((⌈R / δ⌉₊ : ℤ) + 1 : ℤ) : ℝ) * δ ≤ R + 2 * δ := by
    push_cast
    have : (⌈R / δ⌉₊ : ℝ) * δ ≤ (R / δ + 1) * δ := mul_le_mul_of_nonneg_right hc.le hδ.le
    rw [add_mul, div_mul_cancel₀ _ hδ.ne'] at this; linarith
  have bound : ∀ a b : ℤ, -((⌈R / δ⌉₊ : ℤ) + 1) ≤ a → a ≤ (⌈R / δ⌉₊ : ℤ) + 1 →
      -((⌈R / δ⌉₊ : ℤ) + 1) ≤ b → b ≤ (⌈R / δ⌉₊ : ℤ) + 1 →
      |(((b : ℝ) + 1 / 2) * δ - ((a : ℝ) + 1 / 2) * δ)| ≤ 2 * R + 4 * δ := by
    intro a b ha1 ha2 hb1 hb2
    have e : (((b : ℝ) + 1 / 2) * δ - ((a : ℝ) + 1 / 2) * δ) = ((b - a : ℤ) : ℝ) * δ := by
      push_cast; ring
    rw [e, abs_mul, abs_of_pos hδ]
    have : |((b - a : ℤ) : ℝ)| ≤ 2 * (((⌈R / δ⌉₊ : ℤ) + 1 : ℤ) : ℝ) := by
      rw [← Int.cast_abs]
      have : |b - a| ≤ 2 * ((⌈R / δ⌉₊ : ℤ) + 1) := by rw [abs_le]; constructor <;> omega
      exact_mod_cast this
    nlinarith
  rw [Prod.norm_def, max_le_iff]
  simp only [gcen, Prod.fst_sub, Prod.snd_sub, Real.norm_eq_abs]
  exact ⟨bound _ _ hg.1.1 hg.1.2 hg'.1.1 hg'.1.2, bound _ _ hg.2.1 hg.2.2 hg'.2.1 hg'.2.2⟩

/-- The constant of the jittered bound. -/
def jitConst (R : ℝ) : ℝ := 4 * Real.sqrt (80 * R) + 1

set_option maxHeartbeats 1600000 in
/-- **Jittered sets at a fixed resolution.**  Let `ε = R/N` satisfy the smallness conditions
below.  There is a jittered set `Λ` (one point in each cell of side `2ε` of `[-R, R)²`) with no
repeated difference vectors such that every convex polygon `A` with at most `log(1/ε)` vertices
in `[-R, R]²`, with any part of its boundary, satisfies
`|(2ε)² #(A ∩ Λ) - leb(A)| ≤ K ε^{3/2} log(1/ε)`. -/
theorem jittered_exists_eps {R : ℝ} (hR : 0 < R) {N : ℕ} (hN : 1 ≤ N)
    (hε1 : R / N ≤ Real.exp (-1))
    (hε2 : 2 * R * (R / N) + 5 * (R / N) ^ 4 ≤ 1)
    (hε3 : 2 * (R / N) + (R / N) ^ 4 * Real.exp (25 / 2 * R + 44) < 1)
    (hε4 : Real.sqrt (R / N) * Real.log (N / R) * (251 + 50 * R) ≤ 1) :
    ∃ Λ : Fin N × Fin N → ℝ × ℝ, (∀ c, Λ c ∈ jcell R (2 * (R / N)) c) ∧
      (∀ c₁ c₂ c₃ c₄ : Fin N × Fin N, c₁ ≠ c₂ → c₃ ≠ c₄ → (c₁, c₂) ≠ (c₃, c₄) →
        Λ c₁ - Λ c₂ ≠ Λ c₃ - Λ c₄) ∧
      ∀ V : Finset (ℝ × ℝ), (V : Set (ℝ × ℝ)) ⊆ jwin R → V.card ≤ ⌊Real.log (N / R)⌋₊ →
        ∀ A : Set (ℝ × ℝ), interior (convexHull ℝ (V : Set (ℝ × ℝ))) ⊆ A →
          A ⊆ convexHull ℝ (V : Set (ℝ × ℝ)) →
            |(2 * (R / N)) ^ 2 * jcount A Λ - (volume A).toReal| ≤
              jitConst R * ((R / N) * Real.sqrt (R / N)) * Real.log (N / R) := by
  set ε := R / N with hεdef
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hε : 0 < ε := div_pos hR hNpos
  have hεe1 : ε < 1 := hε1.trans_lt (by rw [Real.exp_lt_one_iff]; norm_num)
  set L := Real.log (N / R) with hL
  have hL1 : 1 ≤ L := by
    rw [hL, show (N : ℝ) / R = ε⁻¹ by rw [hεdef, inv_div], Real.log_inv, le_neg]
    have := Real.log_le_log hε hε1
    rwa [Real.log_exp] at this
  have hLε : Real.exp L = ε⁻¹ := by
    rw [hL, show (N : ℝ) / R = ε⁻¹ by rw [hεdef, inv_div], Real.exp_log (by positivity)]
  set h := 2 * ε with hhdef
  have hh : 0 < h := by positivity
  have hNh : (N : ℝ) * h = 2 * R := by rw [hhdef, hεdef]; field_simp
  set δ := ε ^ 3 with hδdef
  have hδ : 0 < δ := by positivity
  set k := ⌊L⌋₊ with hk
  have hkL : (k : ℝ) ≤ L := Nat.floor_le (by linarith)
  set K₁ := Real.sqrt (80 * R) with hK₁
  have hK₁sq : K₁ ^ 2 = 80 * R := Real.sq_sqrt (by positivity)
  set x := K₁ * L / Real.sqrt ε with hxdef
  have hsε : 0 < Real.sqrt ε := Real.sqrt_pos.2 hε
  have hx : 0 < x := by
    have : 0 < K₁ := Real.sqrt_pos.2 (by positivity)
    positivity
  set G := jgrid R δ with hG
  set Dmax := 50 * R * δ + 175 * δ ^ 2 with hDmax
  have hvolD : ∀ g ∈ G, ∀ g' ∈ G, (volume (dset δ g g')).toReal ≤ Dmax := by
    intro g hg g' hg'
    have h1 := volume_dset_le hδ g g'
    have h2 := jgrid_cen_dist hR hδ hg hg'
    refine (ENNReal.toReal_mono ENNReal.ofReal_ne_top h1).trans ?_
    rw [ENNReal.toReal_ofReal (by positivity)]
    nlinarith
  set S := (h ^ 2)⁻¹ * Dmax with hS
  have hSD : ∀ g ∈ G, ∀ g' ∈ G,
      ∑ c : Fin N × Fin N, (unifCell R h c (dset δ g g')).toReal ≤ S := by
    intro g hg g' hg'
    rw [sum_unifCell (N := N) hh hNh (isCompact_dset hδ g g').isClosed.measurableSet]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    refine (ENNReal.toReal_mono (isCompact_dset hδ g g').measure_lt_top.ne
      (measure_mono Set.inter_subset_left)).trans (hvolD g hg g' hg')
  -- the union bound is small
  have hΓ : ((G.card : ℝ)) ≤ (ε ^ 4)⁻¹ ^ 2 := by
    refine (card_jgrid_le hR hδ).trans (pow_le_pow_left₀ (by positivity) ?_ 2)
    rw [hδdef, ← one_div, le_div_iff₀ (by positivity)]
    have : (2 * R / ε ^ 3 + 5) * ε ^ 4 = 2 * R * ε + 5 * ε ^ 4 := by field_simp
    linarith
  have hG1 : 1 ≤ G.card := by
    have : (0 : ℤ × ℤ) ∈ G := by
      simp only [hG, jgrid, Finset.mem_product, Finset.mem_Icc, Prod.fst_zero, Prod.snd_zero]
      omega
    exact Finset.card_pos.2 ⟨_, this⟩
  have hterm1 : ((smallSets G k).card : ℝ) * (2 * Real.exp (-x ^ 2 / (8 * N))) ≤ 2 * ε := by
    have hc := card_smallSets_le G k hG1
    have hx2 : x ^ 2 / (8 * N) = 10 * L ^ 2 := by
      rw [hxdef, div_pow, mul_pow, hK₁sq, Real.sq_sqrt hε.le, hεdef]; field_simp; ring
    rw [neg_div, hx2]
    have hkexp : (k : ℝ) + 1 ≤ Real.exp L := by linarith [Real.add_one_le_exp L]
    have hGexp : (G.card : ℝ) ≤ Real.exp (8 * L) := by
      refine hΓ.trans (le_of_eq ?_)
      rw [← Real.exp_log (show (0 : ℝ) < (ε ^ 4)⁻¹ ^ 2 by positivity)]
      congr 1
      rw [Real.log_pow, Real.log_inv, Real.log_pow, hL, show (N : ℝ) / R = ε⁻¹ by
        rw [hεdef, inv_div], Real.log_inv]; push_cast; ring
    have hpow : (G.card : ℝ) ^ k ≤ Real.exp (8 * L ^ 2) := by
      calc (G.card : ℝ) ^ k ≤ Real.exp (8 * L) ^ k := pow_le_pow_left₀ (by positivity) hGexp k
        _ = Real.exp (8 * L * k) := by rw [← Real.exp_nat_mul]; ring_nf
        _ ≤ Real.exp (8 * L ^ 2) := Real.exp_le_exp.2 (by nlinarith)
    calc ((smallSets G k).card : ℝ) * (2 * Real.exp (-(10 * L ^ 2)))
        ≤ ((k + 1) * (G.card : ℝ) ^ k) * (2 * Real.exp (-(10 * L ^ 2))) :=
          mul_le_mul_of_nonneg_right hc (by positivity)
      _ ≤ (Real.exp L * Real.exp (8 * L ^ 2)) * (2 * Real.exp (-(10 * L ^ 2))) := by
          gcongr
      _ = 2 * Real.exp (L - 2 * L ^ 2) := by
          rw [← Real.exp_add]; rw [mul_comm 2, ← mul_assoc, ← Real.exp_add]; ring_nf
      _ ≤ 2 * Real.exp (-L) := by gcongr; nlinarith
      _ = 2 * ε := by rw [Real.exp_neg, hLε, inv_inv]
  have hterm2 : ((G ×ˢ G).card : ℝ) * Real.exp (-L * 20 + (Real.exp L - 1) * S) ≤
      ε ^ 4 * Real.exp (25 / 2 * R + 44) := by
    rw [Finset.card_product]
    push_cast
    have hS' : (Real.exp L - 1) * S ≤ 25 / 2 * R + 44 := by
      rw [hLε, hS, hDmax, hhdef, hδdef]
      have : (ε⁻¹ - 1) * ((2 * ε) ^ 2)⁻¹ * (50 * R * ε ^ 3 + 175 * (ε ^ 3) ^ 2) ≤
          ε⁻¹ * ((2 * ε) ^ 2)⁻¹ * (50 * R * ε ^ 3 + 175 * (ε ^ 3) ^ 2) := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        apply mul_le_mul_of_nonneg_right _ (by positivity); linarith
      have e : ε⁻¹ * ((2 * ε) ^ 2)⁻¹ * (50 * R * ε ^ 3 + 175 * (ε ^ 3) ^ 2) =
          25 / 2 * R + 175 / 4 * ε ^ 3 := by field_simp; ring
      have : ε ^ 3 ≤ 1 := pow_le_one₀ hε.le hεe1.le
      nlinarith
    have hexpL : Real.exp (-L * 20) = ε ^ 20 := by
      rw [show -L * 20 = ((20 : ℕ) : ℝ) * (-L) by push_cast; ring, Real.exp_nat_mul,
        Real.exp_neg, hLε, inv_inv]
    calc (G.card : ℝ) * G.card * Real.exp (-L * 20 + (Real.exp L - 1) * S)
        ≤ ((ε ^ 4)⁻¹ ^ 2 * (ε ^ 4)⁻¹ ^ 2) * (ε ^ 20 * Real.exp (25 / 2 * R + 44)) := by
          rw [Real.exp_add, hexpL]
          gcongr
      _ = ε ^ 4 * Real.exp (25 / 2 * R + 44) := by field_simp
  have hsmall : ((smallSets G k).card : ℝ) * (2 * Real.exp (-x ^ 2 / (8 * N))) +
      ((G ×ˢ G).card : ℝ) * Real.exp (-L * 20 + (Real.exp L - 1) * S) < 1 := by
    linarith
  obtain ⟨Λ, hcell, hdiff, hP, hD⟩ := exists_good_config (R := R) hN hh hδ hx (by linarith) hSD hsmall
  refine ⟨Λ, hcell, hdiff, fun V hVW hVk A hA1 hA2 => ?_⟩
  have hb := jitter_bound_of_good (N := N) hh hNh hδ (by positivity : 0 ≤ Dmax) Λ hP hD
    (fun v hv => gidx_mem_jgrid hR hδ hv) hvolD V hVW hVk A hA1 hA2
  refine hb.trans ?_
  -- the numerical estimate
  have hh2x : h ^ 2 * x = 4 * K₁ * (ε * Real.sqrt ε) * L := by
    rw [hhdef, hxdef]
    have hd : ε / Real.sqrt ε = Real.sqrt ε := Real.div_sqrt
    calc (2 * ε) ^ 2 * (K₁ * L / Real.sqrt ε) = 4 * K₁ * (ε * (ε / Real.sqrt ε)) * L := by ring
      _ = 4 * K₁ * (ε * Real.sqrt ε) * L := by rw [hd]
  have hk2 : (k : ℝ) ^ 2 ≤ L ^ 2 := pow_le_pow_left₀ (Nat.cast_nonneg _) hkL 2
  have hrest : 19 * h ^ 2 * (k : ℝ) ^ 2 + (k : ℝ) ^ 2 * Dmax ≤ ε * Real.sqrt ε * L := by
    have hD' : Dmax ≤ ε ^ 2 * (50 * R + 175) := by
      rw [hDmax, hδdef]
      have h1 : ε ^ 3 ≤ ε ^ 2 := pow_le_pow_of_le_one hε.le hεe1.le (by norm_num)
      have h2 : (ε ^ 3) ^ 2 ≤ ε ^ 2 := by
        rw [← pow_mul]; exact pow_le_pow_of_le_one hε.le hεe1.le (by norm_num)
      nlinarith
    have hstep : 19 * h ^ 2 * (k : ℝ) ^ 2 + (k : ℝ) ^ 2 * Dmax ≤ ε ^ 2 * L ^ 2 * (251 + 50 * R) := by
      rw [hhdef]
      have : 19 * (2 * ε) ^ 2 * (k : ℝ) ^ 2 ≤ 76 * ε ^ 2 * L ^ 2 := by nlinarith
      have : (k : ℝ) ^ 2 * Dmax ≤ L ^ 2 * (ε ^ 2 * (50 * R + 175)) :=
        mul_le_mul hk2 hD' (by positivity) (by positivity)
      nlinarith
    refine hstep.trans ?_
    have e : ε ^ 2 * L ^ 2 * (251 + 50 * R) =
        (ε * Real.sqrt ε * L) * (Real.sqrt ε * L * (251 + 50 * R)) := by
      calc ε ^ 2 * L ^ 2 * (251 + 50 * R) = ε * ε * L ^ 2 * (251 + 50 * R) := by ring
        _ = ε * (Real.sqrt ε * Real.sqrt ε) * L ^ 2 * (251 + 50 * R) := by
            rw [Real.mul_self_sqrt hε.le]
        _ = _ := by ring
    rw [e]
    calc (ε * Real.sqrt ε * L) * (Real.sqrt ε * L * (251 + 50 * R))
        ≤ (ε * Real.sqrt ε * L) * 1 := mul_le_mul_of_nonneg_left hε4 (by positivity)
      _ = ε * Real.sqrt ε * L := mul_one _
  rw [jitConst]
  nlinarith

/-- **Jittered sets are isotropic for polygons (classical form).**  For every `R > 0` and every
large enough `N`, with `ε = R/N`, there is a jittered set `Λ` in `[-R, R]²` (one point in each cell
of side `2ε`) with no repeated difference vectors, such that every convex polygon `A ⊆ [-R, R]²`
with at most `log(1/ε)` vertices, with any part of its boundary included, satisfies
`|(2ε)² #(A ∩ Λ) - leb(A)| ≤ K ε^{3/2} log(1/ε)`, `K = jitConst R`. -/
theorem jittered_exists {R : ℝ} (hR : 0 < R) :
    ∀ᶠ N : ℕ in atTop, ∃ Λ : Fin N × Fin N → ℝ × ℝ, (∀ c, Λ c ∈ jcell R (2 * (R / N)) c) ∧
      (∀ c₁ c₂ c₃ c₄ : Fin N × Fin N, c₁ ≠ c₂ → c₃ ≠ c₄ → (c₁, c₂) ≠ (c₃, c₄) →
        Λ c₁ - Λ c₂ ≠ Λ c₃ - Λ c₄) ∧
      ∀ V : Finset (ℝ × ℝ), (V : Set (ℝ × ℝ)) ⊆ jwin R → V.card ≤ ⌊Real.log (N / R)⌋₊ →
        ∀ A : Set (ℝ × ℝ), interior (convexHull ℝ (V : Set (ℝ × ℝ))) ⊆ A →
          A ⊆ convexHull ℝ (V : Set (ℝ × ℝ)) →
            |(2 * (R / N)) ^ 2 * jcount A Λ - (volume A).toReal| ≤
              jitConst R * ((R / N) * Real.sqrt (R / N)) * Real.log (N / R) := by
  have hlim : Tendsto (fun N : ℕ => R / (N : ℝ)) atTop (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_iff.2 ⟨tendsto_const_div_atTop_nhds_zero_nat R, ?_⟩
    filter_upwards [eventually_ge_atTop 1] with N hN
    exact div_pos hR (by exact_mod_cast hN)
  have hcont : ∀ f : ℝ → ℝ, Continuous f → f 0 < 1 → ∀ᶠ N : ℕ in atTop, f (R / N) < 1 := by
    intro f hf h0
    exact (hlim.mono_right nhdsWithin_le_nhds).eventually
      ((hf.tendsto 0).eventually (gt_mem_nhds h0)) |>.mono fun N h => h
  have e1 : ∀ᶠ N : ℕ in atTop, R / N ≤ Real.exp (-1) :=
    (hlim.mono_right nhdsWithin_le_nhds).eventually (ge_mem_nhds (Real.exp_pos _))
  have e2 : ∀ᶠ N : ℕ in atTop, 2 * R * (R / N) + 5 * (R / N) ^ 4 < 1 :=
    hcont (fun e => 2 * R * e + 5 * e ^ 4) (by fun_prop) (by norm_num)
  have e3 : ∀ᶠ N : ℕ in atTop, 2 * (R / N) + (R / N) ^ 4 * Real.exp (25 / 2 * R + 44) < 1 :=
    hcont (fun e => 2 * e + e ^ 4 * Real.exp (25 / 2 * R + 44)) (by fun_prop) (by norm_num)
  have e4 : ∀ᶠ N : ℕ in atTop,
      Real.sqrt (R / N) * Real.log (N / R) * (251 + 50 * R) ≤ 1 := by
    have h1 := (tendsto_log_mul_rpow_nhdsGT_zero (r := 1 / 2) (by norm_num)).const_mul
      (-(251 + 50 * R))
    rw [mul_zero] at h1
    have h2 := (h1.comp hlim).eventually (ge_mem_nhds (show (0 : ℝ) < 1 by norm_num))
    filter_upwards [h2, eventually_ge_atTop 1] with N hN hN1
    have hpos : 0 < R / (N : ℝ) := div_pos hR (by exact_mod_cast hN1)
    simp only [Function.comp_apply] at hN
    rw [← Real.sqrt_eq_rpow] at hN
    have : Real.log (N / R) = -Real.log (R / N) := by
      rw [show (N : ℝ) / R = (R / N)⁻¹ by rw [inv_div], Real.log_inv]
    rw [this]
    linarith
  filter_upwards [e1, e2, e3, e4, eventually_ge_atTop 1] with N h1 h2 h3 h4 hN
  exact jittered_exists_eps hR hN h1 h2.le h3 h4

end JitProb

/-! ## The hyperfinite jittered set -/

section JitHyper

/-- The property of a jittered set at resolution `N` (see `jittered_exists`). -/
def JitGood (R : ℝ) (N : ℕ) (Λ : Fin N × Fin N → ℝ × ℝ) : Prop :=
  (∀ c, Λ c ∈ jcell R (2 * (R / N)) c) ∧
    (∀ c₁ c₂ c₃ c₄ : Fin N × Fin N, c₁ ≠ c₂ → c₃ ≠ c₄ → (c₁, c₂) ≠ (c₃, c₄) →
      Λ c₁ - Λ c₂ ≠ Λ c₃ - Λ c₄) ∧
    ∀ V : Finset (ℝ × ℝ), (V : Set (ℝ × ℝ)) ⊆ jwin R → V.card ≤ ⌊Real.log (N / R)⌋₊ →
      ∀ A : Set (ℝ × ℝ), interior (convexHull ℝ (V : Set (ℝ × ℝ))) ⊆ A →
        A ⊆ convexHull ℝ (V : Set (ℝ × ℝ)) →
          |(2 * (R / N)) ^ 2 * jcount A Λ - (volume A).toReal| ≤
            jitConst R * ((R / N) * Real.sqrt (R / N)) * Real.log (N / R)

open Classical in
/-- A choice of jittered set at each resolution `N m` (good for `U`-almost every `m`). -/
def jitSeq (R : ℝ) (N : ℕ → ℕ) (m : ℕ) : Fin (N m) × Fin (N m) → ℝ × ℝ :=
  if h : ∃ Λ, JitGood R (N m) Λ then h.choose else fun _ => 0

/-- The hyperfinite jittered set `Λ = [Λ_m]`, as a sequence of finite sets. -/
def jitSet (R : ℝ) (N : ℕ → ℕ) (m : ℕ) : Finset (ℝ × ℝ) := Finset.univ.image (jitSeq R N m)

theorem jitSeq_good {R : ℝ} (hR : 0 < R) {N : ℕ → ℕ} (hN : Tendsto N (hyperfilter ℕ) atTop) :
    ∀ᶠ m in hyperfilter ℕ, JitGood R (N m) (jitSeq R N m) := by
  have h := hN.eventually (jittered_exists hR)
  filter_upwards [h] with m hm
  have e : jitSeq R N m = hm.choose := by
    classical
    unfold jitSeq; exact dif_pos hm
  rw [e]; exact hm.choose_spec

theorem jcount_eq_card {N : ℕ} {R h : ℝ} (hh : 0 < h) {Λ : Fin N × Fin N → ℝ × ℝ}
    (hcell : ∀ c, Λ c ∈ jcell R h c) (A : Set (ℝ × ℝ)) [DecidablePred (· ∈ A)] :
    jcount A Λ = ((Finset.univ.image Λ).filter (· ∈ A)).card := by
  classical
  have hinj : Function.Injective Λ := by
    intro c c' hcc'
    by_contra hne
    exact Set.disjoint_left.1 (jcell_disjoint hh hne) (hcell c) (hcc' ▸ hcell c')
  rw [jcount, Finset.filter_image, Finset.card_image_of_injective _ hinj]
  congr 1; ext c; simp

/-- The content `μ_Λ(A) = (2ε)² #(A ∩ Λ)` of an internal set `A = [A_m]`. -/
noncomputable def jitMu (R : ℝ) (N : ℕ → ℕ) (A : ℕ → Set (ℝ × ℝ)) : ℝ* := by
  classical
  exact Hyperreal.ofSeq fun m => (2 * (R / N m)) ^ 2 * ((jitSet R N m).filter (· ∈ A m)).card

/-- The (nonstandard) Lebesgue measure `*leb(A) = [leb(A_m)]` of an internal set. -/
noncomputable def jitLeb (A : ℕ → Set (ℝ × ℝ)) : ℝ* :=
  Hyperreal.ofSeq fun m => (volume (A m)).toReal

/-- The infinitesimal `ε = R/N`. -/
noncomputable def jitEps (R : ℝ) (N : ℕ → ℕ) : ℝ* := Hyperreal.ofSeq fun m => R / N m

theorem jitEps_infinitesimal {R : ℝ} (hR : 0 < R) {N : ℕ → ℕ}
    (hN : Tendsto N (hyperfilter ℕ) atTop) :
    0 < jitEps R N ∧ QE.NSA.IsInfinitesimal (jitEps R N) := by
  have hNr : Tendsto (fun m => (N m : ℝ)) (hyperfilter ℕ) atTop :=
    tendsto_natCast_atTop_atTop.comp hN
  constructor
  · rw [jitEps, show (0 : ℝ*) = Hyperreal.ofSeq fun _ => 0 from rfl, Hyperreal.ofSeq_lt_ofSeq]
    filter_upwards [hN.eventually (eventually_ge_atTop 1)] with m hm
    exact div_pos hR (by exact_mod_cast hm)
  · rw [jitEps, QE.NSA.isInfinitesimal_ofSeq_iff]
    intro r hr
    have := (hNr.const_div_atTop R).eventually (gt_mem_nhds hr) |>.and
      (hN.eventually (eventually_ge_atTop 1))
    filter_upwards [this] with m ⟨hm, hm1⟩
    rw [abs_of_pos (div_pos hR (by exact_mod_cast hm1))]; exact hm

open Classical in
/-- **The hyperfinite jittered set has exactly one point in each cell.** -/
theorem jitSet_cell {R : ℝ} (hR : 0 < R) {N : ℕ → ℕ} (hN : Tendsto N (hyperfilter ℕ) atTop) :
    ∀ᶠ m in hyperfilter ℕ, ∀ c : Fin (N m) × Fin (N m),
      ((jitSet R N m).filter (· ∈ jcell R (2 * (R / N m)) c)).card = 1 := by
  classical
  filter_upwards [jitSeq_good hR hN, hN.eventually (eventually_ge_atTop 1)] with m hm hm1
  intro c
  have hh : 0 < 2 * (R / N m) := by
    have : (0 : ℝ) < N m := by exact_mod_cast hm1
    positivity
  rw [Finset.card_eq_one]
  refine ⟨jitSeq R N m c, ?_⟩
  ext p
  simp only [jitSet, Finset.mem_filter, Finset.mem_image, Finset.mem_univ, true_and,
    Finset.mem_singleton]
  constructor
  · rintro ⟨⟨c', rfl⟩, hp⟩
    by_contra hne
    have hcc : c' ≠ c := fun h' => hne (by rw [h'])
    exact Set.disjoint_left.1 (jcell_disjoint hh hcc) (hm.1 c') hp
  · rintro rfl; exact ⟨⟨c, rfl⟩, hm.1 c⟩

/-- **No two pairs of points of the hyperfinite jittered set have the same difference.** -/
theorem jitSet_distinct_diff {R : ℝ} (hR : 0 < R) {N : ℕ → ℕ}
    (hN : Tendsto N (hyperfilter ℕ) atTop) :
    ∀ u₁ ∈ QE.NSA.hfin (jitSet R N), ∀ u₂ ∈ QE.NSA.hfin (jitSet R N),
    ∀ u₃ ∈ QE.NSA.hfin (jitSet R N), ∀ u₄ ∈ QE.NSA.hfin (jitSet R N),
      u₁ ≠ u₂ → u₃ ≠ u₄ → (u₁, u₂) ≠ (u₃, u₄) → u₁ - u₂ ≠ u₃ - u₄ := by
  intro u₁ hu₁ u₂ hu₂ u₃ hu₃ u₄ hu₄ h12 h34 hp heq
  obtain ⟨w₁, rfl⟩ := QE.NSA.exists_rep u₁
  obtain ⟨w₂, rfl⟩ := QE.NSA.exists_rep u₂
  obtain ⟨w₃, rfl⟩ := QE.NSA.exists_rep u₃
  obtain ⟨w₄, rfl⟩ := QE.NSA.exists_rep u₄
  unfold QE.NSA.hfin at hu₁ hu₂ hu₃ hu₄
  rw [QE.NSA.mem_internal] at hu₁ hu₂ hu₃ hu₄
  have ne_ev : ∀ a b : ℕ → ℝ × ℝ, ((a : QE.NSA.Ult (ℝ × ℝ)) ≠ b) →
      ∀ᶠ m in hyperfilter ℕ, a m ≠ b m := by
    intro a b hab
    by_contra hc
    apply hab
    apply Filter.Germ.coe_eq.2
    have := (Ultrafilter.eventually_not (f := hyperfilter ℕ)).2 hc
    filter_upwards [this] with m hm
    simpa using hm
  have e12 := ne_ev _ _ h12
  have e34 := ne_ev _ _ h34
  have epair : ∀ᶠ m in hyperfilter ℕ, w₁ m ≠ w₃ m ∨ w₂ m ≠ w₄ m := by
    by_contra hc
    apply hp
    have := (Ultrafilter.eventually_not (f := hyperfilter ℕ)).2 hc
    have h13 : (w₁ : QE.NSA.Ult (ℝ × ℝ)) = w₃ := Filter.Germ.coe_eq.2 (this.mono fun m hm => by
      push_neg at hm; exact hm.1)
    have h24 : (w₂ : QE.NSA.Ult (ℝ × ℝ)) = w₄ := Filter.Germ.coe_eq.2 (this.mono fun m hm => by
      push_neg at hm; exact hm.2)
    rw [h13, h24]
  have edif : ∀ᶠ m in hyperfilter ℕ, w₁ m - w₂ m = w₃ m - w₄ m := by
    have : ((fun m => w₁ m - w₂ m : ℕ → ℝ × ℝ) : QE.NSA.Ult (ℝ × ℝ)) =
        ((fun m => w₃ m - w₄ m : ℕ → ℝ × ℝ) : QE.NSA.Ult (ℝ × ℝ)) := heq
    exact Filter.Germ.coe_eq.1 this
  obtain ⟨m, hm, h1, h2, h3, h4, n12, n34, np, nd⟩ :=
    ((jitSeq_good hR hN).and (hu₁.and (hu₂.and (hu₃.and (hu₄.and (e12.and (e34.and
      (epair.and edif)))))))).exists
  simp only [jitSet, Finset.coe_image, Finset.coe_univ, Set.image_univ, Set.mem_range] at h1 h2 h3 h4
  obtain ⟨c₁, hc₁⟩ := h1
  obtain ⟨c₂, hc₂⟩ := h2
  obtain ⟨c₃, hc₃⟩ := h3
  obtain ⟨c₄, hc₄⟩ := h4
  refine hm.2.1 c₁ c₂ c₃ c₄ ?_ ?_ ?_ ?_
  · rintro rfl; exact n12 (hc₁.symm.trans hc₂)
  · rintro rfl; exact n34 (hc₃.symm.trans hc₄)
  · intro hcc
    simp only [Prod.mk.injEq] at hcc
    obtain ⟨rfl, rfl⟩ := hcc
    rcases np with h | h
    · exact h (hc₁.symm.trans hc₃)
    · exact h (hc₂.symm.trans hc₄)
  · rw [hc₁, hc₂, hc₃, hc₄]; exact nd

theorem tendsto_ratio_hyper {R : ℝ} (hR : 0 < R) {N : ℕ → ℕ}
    (hN : Tendsto N (hyperfilter ℕ) atTop) :
    Tendsto (fun m => R / (N m : ℝ)) (hyperfilter ℕ) (𝓝[>] 0) := by
  have hNr : Tendsto (fun m => (N m : ℝ)) (hyperfilter ℕ) atTop :=
    tendsto_natCast_atTop_atTop.comp hN
  refine tendsto_nhdsWithin_iff.2 ⟨hNr.const_div_atTop R, ?_⟩
  filter_upwards [hN.eventually (eventually_ge_atTop 1)] with m hm
  exact div_pos hR (by exact_mod_cast hm)

theorem tendsto_sqrt_log_hyper {R : ℝ} (hR : 0 < R) {N : ℕ → ℕ}
    (hN : Tendsto N (hyperfilter ℕ) atTop) (C : ℝ) :
    Tendsto (fun m => C * Real.sqrt (R / N m) * Real.log (N m / R)) (hyperfilter ℕ) (𝓝 0) := by
  have h1 := ((tendsto_log_mul_rpow_nhdsGT_zero (r := 1 / 2) (by norm_num)).const_mul (-C)).comp
    (tendsto_ratio_hyper hR hN)
  rw [mul_zero] at h1
  refine h1.congr' ?_
  filter_upwards [hN.eventually (eventually_ge_atTop 1)] with m hm
  have hpos : 0 < R / (N m : ℝ) := div_pos hR (by exact_mod_cast hm)
  simp only [Function.comp_apply]
  rw [← Real.sqrt_eq_rpow,
    show (N m : ℝ) / R = (R / N m)⁻¹ by rw [inv_div], Real.log_inv]
  ring

open Classical in
/-- **Jittered sets are isotropic for polygons (hyperfinite form).**  For every internal convex
polygon `A ⊆ [-R, R]²` with at most `log(1/ε)` vertices, with any part of its boundary,
`|μ_Λ(A) - leb(A)| ≤ K ε^{3/2} log(1/ε)`. -/
theorem jitSet_polygon {R : ℝ} (hR : 0 < R) {N : ℕ → ℕ} (hN : Tendsto N (hyperfilter ℕ) atTop)
    (V : ℕ → Finset (ℝ × ℝ)) (A : ℕ → Set (ℝ × ℝ))
    (hVA : ∀ᶠ m in hyperfilter ℕ, (V m : Set (ℝ × ℝ)) ⊆ jwin R ∧
      (V m).card ≤ ⌊Real.log (N m / R)⌋₊ ∧ interior (convexHull ℝ (V m : Set (ℝ × ℝ))) ⊆ A m ∧
      A m ⊆ convexHull ℝ (V m : Set (ℝ × ℝ))) :
    |jitMu R N A - jitLeb A| ≤
      Hyperreal.ofSeq fun m => jitConst R * ((R / N m) * Real.sqrt (R / N m)) * Real.log (N m / R) := by
  rw [jitMu, jitLeb, show ∀ f g : ℕ → ℝ, |Hyperreal.ofSeq f - Hyperreal.ofSeq g| =
    Hyperreal.ofSeq fun m => |f m - g m| from fun f g => rfl, Hyperreal.ofSeq_le_ofSeq]
  filter_upwards [jitSeq_good hR hN, hVA, hN.eventually (eventually_ge_atTop 1)] with m hm hv hm1
  have hh : 0 < 2 * (R / N m) := by
    have : (0 : ℝ) < N m := by exact_mod_cast hm1
    positivity
  have := hm.2.2 (V m) hv.1 hv.2.1 (A m) hv.2.2.1 hv.2.2.2
  rw [jcount_eq_card hh hm.1] at this
  convert this using 3
  simp only [jitSet]

/-- **Vanishing retained term.**  For every internal convex polygon as above,
`(μ_Λ(A) - leb(A))/ε` is infinitesimal: `ρ(A) = 0`. -/
theorem jitSet_retained_zero {R : ℝ} (hR : 0 < R) {N : ℕ → ℕ}
    (hN : Tendsto N (hyperfilter ℕ) atTop) (V : ℕ → Finset (ℝ × ℝ)) (A : ℕ → Set (ℝ × ℝ))
    (hVA : ∀ᶠ m in hyperfilter ℕ, (V m : Set (ℝ × ℝ)) ⊆ jwin R ∧
      (V m).card ≤ ⌊Real.log (N m / R)⌋₊ ∧ interior (convexHull ℝ (V m : Set (ℝ × ℝ))) ⊆ A m ∧
      A m ⊆ convexHull ℝ (V m : Set (ℝ × ℝ))) :
    QE.NSA.IsInfinitesimal ((jitMu R N A - jitLeb A) / jitEps R N) := by
  classical
  have hb := jitSet_polygon hR hN V A hVA
  rw [jitMu, jitLeb] at hb
  rw [jitMu, jitLeb, jitEps]
  rw [show ∀ f g : ℕ → ℝ, |Hyperreal.ofSeq f - Hyperreal.ofSeq g| =
    Hyperreal.ofSeq fun m => |f m - g m| from fun f g => rfl, Hyperreal.ofSeq_le_ofSeq] at hb
  rw [show ∀ f g e : ℕ → ℝ, (Hyperreal.ofSeq f - Hyperreal.ofSeq g) / Hyperreal.ofSeq e =
    Hyperreal.ofSeq fun m => (f m - g m) / e m from fun f g e => rfl,
    QE.NSA.isInfinitesimal_ofSeq_iff]
  intro r hr
  have hlim := (tendsto_sqrt_log_hyper hR hN (jitConst R)).eventually (gt_mem_nhds hr)
  filter_upwards [hb, hlim, hN.eventually (eventually_ge_atTop 1)] with m h1 h2 h3
  have hpos : 0 < R / (N m : ℝ) := div_pos hR (by exact_mod_cast h3)
  rw [abs_div, abs_of_pos hpos, div_lt_iff₀ hpos]
  calc _ ≤ jitConst R * ((R / N m) * Real.sqrt (R / N m)) * Real.log (N m / R) := h1
    _ = (jitConst R * Real.sqrt (R / N m) * Real.log (N m / R)) * (R / N m) := by ring
    _ < r * (R / N m) := mul_lt_mul_of_pos_right h2 hpos

/-- **Standard polygons have zero retained term.**  For a standard convex polygon `A` in the
window, with any part of its boundary, `ρ(A) = st((μ_Λ(A) - leb(A))/ε) = 0`. -/
theorem jitSet_retained_zero_standard {R : ℝ} (hR : 0 < R) {N : ℕ → ℕ}
    (hN : Tendsto N (hyperfilter ℕ) atTop) (V : Finset (ℝ × ℝ)) (hV : (V : Set (ℝ × ℝ)) ⊆ jwin R)
    (A : Set (ℝ × ℝ)) (hA1 : interior (convexHull ℝ (V : Set (ℝ × ℝ))) ⊆ A)
    (hA2 : A ⊆ convexHull ℝ (V : Set (ℝ × ℝ))) :
    QE.NSA.IsInfinitesimal ((jitMu R N (fun _ => A) - jitLeb (fun _ => A)) / jitEps R N) := by
  refine jitSet_retained_zero hR hN (fun _ => V) (fun _ => A) ?_
  have hlog : Tendsto (fun m => Real.log (N m / R)) (hyperfilter ℕ) atTop := by
    have := (tendsto_ratio_hyper hR hN)
    refine (tendsto_neg_atBot_atTop.comp (Real.tendsto_log_nhdsGT_zero.comp this)).congr' ?_
    filter_upwards [hN.eventually (eventually_ge_atTop 1)] with m hm
    simp only [Function.comp_apply]
    rw [show (N m : ℝ) / R = (R / N m)⁻¹ by rw [inv_div], Real.log_inv]
  have hev := (tendsto_nat_floor_atTop.comp hlog).eventually (eventually_ge_atTop V.card)
  filter_upwards [hev] with m hm
  exact ⟨hV, hm, hA1, hA2⟩

open Classical in
/-- **Faithfulness**: an internal set containing a point of `Λ` has content at least `(2ε)²`. -/
theorem jitSet_faithful {R : ℝ} {N : ℕ → ℕ} (A : ℕ → Set (ℝ × ℝ))
    (hA : ∀ᶠ m in hyperfilter ℕ, ((jitSet R N m).filter (· ∈ A m)).Nonempty) :
    (2 * jitEps R N) ^ 2 ≤ jitMu R N A := by
  rw [jitMu, jitEps, show ∀ f : ℕ → ℝ, (2 * Hyperreal.ofSeq f) ^ 2 =
    Hyperreal.ofSeq fun m => (2 * f m) ^ 2 from fun f => rfl, Hyperreal.ofSeq_le_ofSeq]
  filter_upwards [hA] with m hm
  have : (1 : ℝ) ≤ ((jitSet R N m).filter (· ∈ A m)).card := by
    exact_mod_cast Finset.card_pos.2 hm
  nlinarith [sq_nonneg (2 * (R / N m))]

/-! ### The shadow of the jittered content on Jordan sets -/

theorem convexHull_corners_eq {a₁ b₁ a₂ b₂ : ℝ} (h₁ : a₁ ≤ b₁) (h₂ : a₂ ≤ b₂) :
    convexHull ℝ ({(a₁, a₂), (b₁, a₂), (a₁, b₂), (b₁, b₂)} : Set (ℝ × ℝ)) =
      Set.Icc a₁ b₁ ×ˢ Set.Icc a₂ b₂ := by
  apply le_antisymm
  · refine convexHull_min ?_ ((convex_Icc _ _).prod (convex_Icc _ _))
    intro u hu
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hu
    rcases hu with rfl | rfl | rfl | rfl <;> exact ⟨⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩⟩
  · exact box_subset_convexHull h₁ h₂

/-- Every grid cell is a convex polygon with four vertices in the window. -/
theorem jcell_polygon {R : ℝ} (hR : 0 < R) {M : ℕ} (hM : 1 ≤ M) (c : Fin M × Fin M) :
    ∃ V : Finset (ℝ × ℝ), V.card ≤ 4 ∧ (V : Set (ℝ × ℝ)) ⊆ jwin R ∧
      interior (convexHull ℝ (V : Set (ℝ × ℝ))) ⊆ jcell R (2 * R / M) c ∧
      jcell R (2 * R / M) c ⊆ convexHull ℝ (V : Set (ℝ × ℝ)) := by
  classical
  set s := 2 * R / M with hs
  have hMpos : (0 : ℝ) < M := by exact_mod_cast hM
  have hs0 : 0 < s := by positivity
  set a₁ := -R + (c.1 : ℝ) * s
  set b₁ := -R + ((c.1 : ℝ) + 1) * s
  set a₂ := -R + (c.2 : ℝ) * s
  set b₂ := -R + ((c.2 : ℝ) + 1) * s
  have h₁ : a₁ ≤ b₁ := by simp only [a₁, b₁]; nlinarith
  have h₂ : a₂ ≤ b₂ := by simp only [a₂, b₂]; nlinarith
  have hMs : (M : ℝ) * s = 2 * R := by rw [hs]; field_simp
  have hc1 : (c.1 : ℝ) + 1 ≤ M := by exact_mod_cast c.1.2
  have hc2 : (c.2 : ℝ) + 1 ≤ M := by exact_mod_cast c.2.2
  have hb₁ : b₁ ≤ R := by
    have := mul_le_mul_of_nonneg_right hc1 hs0.le; simp only [b₁]; linarith
  have hb₂ : b₂ ≤ R := by
    have := mul_le_mul_of_nonneg_right hc2 hs0.le; simp only [b₂]; linarith
  have ha₁ : -R ≤ a₁ := by simp only [a₁]; have : (0 : ℝ) ≤ (c.1 : ℝ) * s := by positivity
                           linarith
  have ha₂ : -R ≤ a₂ := by simp only [a₂]; have : (0 : ℝ) ≤ (c.2 : ℝ) * s := by positivity
                           linarith
  refine ⟨{(a₁, a₂), (b₁, a₂), (a₁, b₂), (b₁, b₂)}, ?_, ?_, ?_, ?_⟩
  · exact (Finset.card_insert_le _ _).trans (Nat.succ_le_succ ((Finset.card_insert_le _ _).trans
      (Nat.succ_le_succ ((Finset.card_insert_le _ _).trans (by simp)))))
  · intro u hu
    simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
      Set.mem_singleton_iff] at hu
    rcases hu with rfl | rfl | rfl | rfl <;>
      exact ⟨⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩⟩
  · simp only [Finset.coe_insert, Finset.coe_singleton]
    rw [convexHull_corners_eq h₁ h₂, interior_prod_eq, interior_Icc, interior_Icc]
    rintro u ⟨⟨u1, u2⟩, ⟨u3, u4⟩⟩
    exact ⟨⟨u1.le, u2⟩, ⟨u3.le, u4⟩⟩
  · simp only [Finset.coe_insert, Finset.coe_singleton]
    rw [convexHull_corners_eq h₁ h₂]
    rintro u ⟨⟨u1, u2⟩, ⟨u3, u4⟩⟩
    exact ⟨⟨u1, u2.le⟩, ⟨u3, u4.le⟩⟩

theorem jcell_meets_frontier {N : ℕ} {R h : ℝ} (c : Fin N × Fin N) {E : Set (ℝ × ℝ)}
    (h1 : (jcell R h c ∩ E).Nonempty) (h2 : ¬ jcell R h c ⊆ E) :
    (jcell R h c ∩ frontier E).Nonempty := by
  by_contra hcon
  rw [Set.not_nonempty_iff_eq_empty] at hcon
  have hconn : IsPreconnected (jcell R h c) :=
    ((convex_Ico _ _).prod (convex_Ico _ _)).isPreconnected
  have hcov : jcell R h c ⊆ interior E ∪ (closure E)ᶜ := by
    intro q hq
    by_cases hqi : q ∈ interior E
    · exact Or.inl hqi
    · right; intro hqc
      have : q ∈ jcell R h c ∩ frontier E := ⟨hq, hqc, hqi⟩
      rw [hcon] at this; exact this
  obtain ⟨p, hp, hpE⟩ := h1
  obtain ⟨q, hq, hqE⟩ := Set.not_subset.1 h2
  have hpi : p ∈ interior E := by
    rcases hcov hp with h' | h'
    · exact h'
    · exact absurd (subset_closure hpE) h'
  have hqc : q ∈ (closure E)ᶜ := by
    rcases hcov hq with h' | h'
    · exact absurd (interior_subset h') hqE
    · exact h'
  obtain ⟨y, _, hy1, hy2⟩ := hconn _ _ isOpen_interior isClosed_closure.isOpen_compl hcov
    ⟨p, hp, hpi⟩ ⟨q, hq, hqc⟩
  exact hy2 (interior_subset.trans subset_closure hy1)

theorem jcell_subset_cthickening {N : ℕ} {R h : ℝ} (hh : 0 < h) (c : Fin N × Fin N)
    {F : Set (ℝ × ℝ)} (hc : (jcell R h c ∩ F).Nonempty) :
    jcell R h c ⊆ Metric.cthickening h F := by
  obtain ⟨f, hf, hfF⟩ := hc
  intro x hx
  refine Metric.mem_cthickening_of_dist_le x f h F hfF ?_
  rw [dist_eq_norm, Prod.norm_def, max_le_iff, Prod.fst_sub, Prod.snd_sub, Real.norm_eq_abs,
    Real.norm_eq_abs, abs_le, abs_le]
  obtain ⟨⟨x1, x2⟩, ⟨x3, x4⟩⟩ := hx
  obtain ⟨⟨f1, f2⟩, ⟨f3, f4⟩⟩ := hf
  refine ⟨⟨by nlinarith, by nlinarith⟩, ⟨by nlinarith, by nlinarith⟩⟩

theorem jitSet_subset_jwinh {R : ℝ} (hR : 0 < R) {N : ℕ → ℕ} {m : ℕ}
    (hm : JitGood R (N m) (jitSeq R N m)) (hm1 : 1 ≤ N m) {p : ℝ × ℝ} (hp : p ∈ jitSet R N m) :
    p ∈ jwinh R := by
  simp only [jitSet, Finset.mem_image, Finset.mem_univ, true_and] at hp
  obtain ⟨c, rfl⟩ := hp
  have hNm : (0 : ℝ) < N m := by exact_mod_cast hm1
  have hh : 0 < 2 * (R / N m) := by positivity
  rw [← iUnion_jcell (N := N m) hh (by field_simp)]
  exact Set.mem_iUnion.2 ⟨c, hm.1 c⟩

set_option maxHeartbeats 1600000 in
open Classical in
/-- **The shadow of the jittered content on Jordan sets is Lebesgue measure.**  For a standard set
`E` of the window whose frontier is Lebesgue-null (a Jordan-measurable set),
`μ_Λ(*E) ≈ leb(E)`, i.e. `st μ_Λ(*E) = leb(E)`. -/
theorem jitSet_jordan {R : ℝ} (hR : 0 < R) {N : ℕ → ℕ} (hN : Tendsto N (hyperfilter ℕ) atTop)
    {E : Set (ℝ × ℝ)} (hEW : E ⊆ jwin R) (hE : volume (frontier E) = 0) :
    QE.NSA.IsInfinitesimal (jitMu R N (fun _ => E) - ((volume E).toReal : ℝ*)) := by
  rw [jitMu, show ∀ (f : ℕ → ℝ) (r : ℝ), Hyperreal.ofSeq f - (r : ℝ*) =
    Hyperreal.ofSeq fun m => f m - r from fun f r => rfl, QE.NSA.isInfinitesimal_ofSeq_iff]
  intro r hr
  set F := frontier E with hF
  have hWc : IsClosed (jwin R) := isClosed_Icc.prod isClosed_Icc
  have hFc : IsCompact F := by
    refine Metric.isCompact_of_isClosed_isBounded isClosed_frontier ?_
    refine (Metric.isBounded_Icc ((-R, -R) : ℝ × ℝ) (R, R)).subset ?_
    refine frontier_subset_closure.trans ((closure_minimal hEW hWc).trans ?_)
    rintro u ⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩; exact ⟨⟨h1, h3⟩, ⟨h2, h4⟩⟩
  -- Step A: a standard grid whose boundary cells have total area `< r/2`
  have htend := tendsto_measure_cthickening_of_isCompact (μ := (volume : Measure (ℝ × ℝ))) hFc
  rw [hE] at htend
  have hs : Tendsto (fun M : ℕ => 2 * R / (M : ℝ)) atTop (𝓝 0) :=
    tendsto_const_div_atTop_nhds_zero_nat (2 * R)
  obtain ⟨M, hM1, hMth⟩ := ((eventually_ge_atTop 1).and ((htend.comp hs).eventually
    (gt_mem_nhds (show (0 : ℝ≥0∞) < ENNReal.ofReal (r / 2) by
      rw [ENNReal.ofReal_pos]; linarith)))).exists
  simp only [Function.comp_apply] at hMth
  set s := 2 * R / (M : ℝ) with hsdef
  have hMpos : (0 : ℝ) < M := by exact_mod_cast hM1
  have hs0 : 0 < s := by positivity
  set Q : Fin M × Fin M → Set (ℝ × ℝ) := jcell R s with hQ
  set Im := Finset.univ.filter fun c : Fin M × Fin M => Q c ⊆ E with hIm
  set Ip := Finset.univ.filter fun c : Fin M × Fin M => (Q c ∩ E).Nonempty with hIp
  have hQfin : ∀ c, volume (Q c) ≠ ⊤ := fun c => by rw [hQ, volume_jcell hs0]; exact ENNReal.ofReal_ne_top
  have hQvol : ∀ c, (volume (Q c)).toReal = s ^ 2 := fun c => by
    rw [hQ, volume_jcell hs0, ENNReal.toReal_ofReal (by positivity)]
  set Sm := ∑ c ∈ Im, (volume (Q c)).toReal with hSm
  set Sp := ∑ c ∈ Ip, (volume (Q c)).toReal with hSp
  have hdisj : Set.PairwiseDisjoint (↑(Finset.univ : Finset (Fin M × Fin M))) Q :=
    fun c _ c' _ hcc' => jcell_disjoint hs0 hcc'
  have hvolU : ∀ I : Finset (Fin M × Fin M),
      (volume (⋃ c ∈ I, Q c)).toReal = ∑ c ∈ I, (volume (Q c)).toReal := by
    intro I
    rw [measure_biUnion_finset (fun c _ c' _ h => jcell_disjoint hs0 h)
      (fun c _ => measurableSet_jcell c), ENNReal.toReal_sum (fun c _ => hQfin c)]
  have hfinE : volume E ≠ ⊤ := ne_top_of_le_ne_top volume_jwin_lt_top.ne (measure_mono hEW)
  have hB1 : Sm ≤ (volume E).toReal := by
    rw [hSm, ← hvolU]
    refine ENNReal.toReal_mono hfinE (measure_mono ?_)
    intro x hx
    simp only [Set.mem_iUnion, exists_prop, hIm, Finset.mem_filter, Finset.mem_univ, true_and] at hx
    obtain ⟨c, hc, hxc⟩ := hx; exact hc hxc
  have hB2 : (volume E).toReal ≤ Sp := by
    rw [hSp, ← hvolU]
    have h1 : volume E ≤ volume (⋃ c ∈ Ip, Q c) + volume (jwin R \ jwinh R) := by
      refine (measure_mono fun x hx => ?_).trans (measure_union_le _ _)
      by_cases hxW : x ∈ jwinh R
      · left
        rw [← iUnion_jcell (N := M) hs0 (by rw [hsdef]; field_simp)] at hxW
        obtain ⟨c, hc⟩ := Set.mem_iUnion.1 hxW
        simp only [Set.mem_iUnion, exists_prop, hIp, Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨c, ⟨x, hc, hx⟩, hc⟩
      · exact Or.inr ⟨hEW hx, hxW⟩
    rw [volume_jwin_diff, add_zero] at h1
    have hfinU : volume (⋃ c ∈ Ip, Q c) ≠ ⊤ := by
      rw [measure_biUnion_finset (fun c _ c' _ h => jcell_disjoint hs0 h)
        (fun c _ => measurableSet_jcell c)]
      exact ENNReal.sum_ne_top.2 fun c _ => hQfin c
    exact ENNReal.toReal_mono hfinU h1
  have hImIp : Im ⊆ Ip := by
    intro c hc
    simp only [hIm, hIp, Finset.mem_filter, Finset.mem_univ, true_and] at hc ⊢
    refine ⟨(-R + ((c.1 : ℕ) : ℝ) * s, -R + ((c.2 : ℕ) : ℝ) * s), ?_, hc ?_⟩ <;>
      exact ⟨⟨le_refl _, by nlinarith⟩, ⟨le_refl _, by nlinarith⟩⟩
  have hB3 : Sp - Sm ≤ (volume (Metric.cthickening s F)).toReal := by
    have hsd := Finset.sum_sdiff hImIp (f := fun c => (volume (Q c)).toReal)
    have e : Sp - Sm = ∑ c ∈ Ip \ Im, (volume (Q c)).toReal := by
      rw [hSp, hSm, ← hsd]; ring
    rw [e, ← hvolU]
    refine ENNReal.toReal_mono (hFc.cthickening.measure_lt_top).ne (measure_mono ?_)
    intro x hx
    simp only [Set.mem_iUnion, exists_prop, Finset.mem_sdiff, hIp, hIm, Finset.mem_filter,
      Finset.mem_univ, true_and] at hx
    obtain ⟨c, ⟨hc1, hc2⟩, hxc⟩ := hx
    exact jcell_subset_cthickening hs0 c (jcell_meets_frontier c hc1 hc2) hxc
  have hB4 : (volume (Metric.cthickening s F)).toReal < r / 2 :=
    ENNReal.toReal_lt_of_lt_ofReal hMth
  -- Step C: the jittered counts of the grid cells
  have hεlim : Tendsto (fun m => (M : ℝ) ^ 2 * (jitConst R * ((R / N m) * Real.sqrt (R / N m)) *
      Real.log (N m / R))) (hyperfilter ℕ) (𝓝 0) := by
    have h1 := (tendsto_ratio_hyper hR hN).mono_right nhdsWithin_le_nhds
    have h2 := tendsto_sqrt_log_hyper hR hN ((M : ℝ) ^ 2 * jitConst R)
    have := h1.mul h2
    rw [zero_mul] at this
    refine this.congr fun m => ?_
    ring
  have hlog4 : ∀ᶠ m in hyperfilter ℕ, 4 ≤ ⌊Real.log (N m / R)⌋₊ := by
    have hlog : Tendsto (fun m => Real.log (N m / R)) (hyperfilter ℕ) atTop := by
      refine (tendsto_neg_atBot_atTop.comp
        (Real.tendsto_log_nhdsGT_zero.comp (tendsto_ratio_hyper hR hN))).congr' ?_
      filter_upwards [hN.eventually (eventually_ge_atTop 1)] with m hm
      simp only [Function.comp_apply]
      rw [show (N m : ℝ) / R = (R / N m)⁻¹ by rw [inv_div], Real.log_inv]
    exact (tendsto_nat_floor_atTop.comp hlog).eventually (eventually_ge_atTop 4)
  filter_upwards [jitSeq_good hR hN, hN.eventually (eventually_ge_atTop 1), hlog4,
    hεlim.eventually (gt_mem_nhds (show (0 : ℝ) < r / 2 by linarith))] with m hm hm1 h4 hb
  set Λ := jitSet R N m with hΛ
  set hm2 := (2 * (R / N m)) ^ 2 with hhm2
  set b := jitConst R * ((R / N m) * Real.sqrt (R / N m)) * Real.log (N m / R) with hbdef
  have hNm : (0 : ℝ) < N m := by exact_mod_cast hm1
  have hh : 0 < 2 * (R / N m) := by positivity
  have hcell : ∀ c : Fin M × Fin M,
      |hm2 * ((Λ.filter (· ∈ Q c)).card : ℝ) - (volume (Q c)).toReal| ≤ b := by
    intro c
    obtain ⟨V, hV4, hVW, hV1, hV2⟩ := jcell_polygon hR hM1 c
    have := hm.2.2 V hVW (hV4.trans h4) (Q c) hV1 hV2
    rw [jcount_eq_card hh hm.1] at this
    convert this using 4
    simp only [hΛ, jitSet]
  have hb0 : 0 ≤ b := (abs_nonneg _).trans (hcell (⟨0, by omega⟩, ⟨0, by omega⟩))
  have hcard : ∀ I : Finset (Fin M × Fin M), (I.card : ℝ) ≤ (M : ℝ) ^ 2 := by
    intro I
    have : I.card ≤ M * M := by
      have := Finset.card_le_univ I
      simpa [Fintype.card_prod, Fintype.card_fin] using this
    have : (I.card : ℝ) ≤ (M : ℝ) * M := by exact_mod_cast this
    nlinarith
  -- lower count
  have hcL : (∑ c ∈ Im, ((Λ.filter (· ∈ Q c)).card : ℝ)) ≤ (Λ.filter (· ∈ E)).card := by
    have : ∑ c ∈ Im, (Λ.filter (· ∈ Q c)).card = (Im.biUnion fun c => Λ.filter (· ∈ Q c)).card := by
      rw [Finset.card_biUnion]
      intro c _ c' _ hcc'
      refine Finset.disjoint_left.2 fun p hp hp' => ?_
      simp only [Finset.mem_filter] at hp hp'
      exact Set.disjoint_left.1 (jcell_disjoint hs0 hcc') hp.2 hp'.2
    have h2 : (Im.biUnion fun c => Λ.filter (· ∈ Q c)).card ≤ (Λ.filter (· ∈ E)).card := by
      apply Finset.card_le_card
      intro p hp
      simp only [Finset.mem_biUnion, Finset.mem_filter, hIm, Finset.mem_univ, true_and] at hp ⊢
      obtain ⟨c, hc, hpΛ, hpc⟩ := hp
      exact ⟨hpΛ, hc hpc⟩
    exact_mod_cast this ▸ h2
  -- upper count
  have hcU : ((Λ.filter (· ∈ E)).card : ℝ) ≤ ∑ c ∈ Ip, ((Λ.filter (· ∈ Q c)).card : ℝ) := by
    have h1 : (Λ.filter (· ∈ E)).card ≤ (Ip.biUnion fun c => Λ.filter (· ∈ Q c)).card := by
      apply Finset.card_le_card
      intro p hp
      simp only [Finset.mem_filter] at hp
      have hpW := jitSet_subset_jwinh hR hm hm1 hp.1
      rw [← iUnion_jcell (N := M) hs0 (by rw [hsdef]; field_simp)] at hpW
      obtain ⟨c, hc⟩ := Set.mem_iUnion.1 hpW
      simp only [Finset.mem_biUnion, Finset.mem_filter, hIp, Finset.mem_univ, true_and]
      exact ⟨c, ⟨p, hc, hp.2⟩, hp.1, hc⟩
    have h2 := (Nat.cast_le (α := ℝ)).2 (h1.trans Finset.card_biUnion_le)
    push_cast at h2
    exact h2
  -- combine
  have hlow : Sm - (M : ℝ) ^ 2 * b ≤ hm2 * (Λ.filter (· ∈ E)).card := by
    calc Sm - (M : ℝ) ^ 2 * b ≤ Sm - Im.card * b :=
          sub_le_sub_left (mul_le_mul_of_nonneg_right (hcard Im) hb0) _
      _ = ∑ c ∈ Im, ((volume (Q c)).toReal - b) := by
          rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul]
      _ ≤ ∑ c ∈ Im, hm2 * ((Λ.filter (· ∈ Q c)).card : ℝ) :=
          Finset.sum_le_sum fun c _ => by linarith [(abs_le.1 (hcell c)).1]
      _ = hm2 * ∑ c ∈ Im, ((Λ.filter (· ∈ Q c)).card : ℝ) := by rw [Finset.mul_sum]
      _ ≤ hm2 * (Λ.filter (· ∈ E)).card := mul_le_mul_of_nonneg_left hcL (by positivity)
  have hup : hm2 * (Λ.filter (· ∈ E)).card ≤ Sp + (M : ℝ) ^ 2 * b := by
    calc hm2 * ((Λ.filter (· ∈ E)).card : ℝ)
        ≤ hm2 * ∑ c ∈ Ip, ((Λ.filter (· ∈ Q c)).card : ℝ) :=
          mul_le_mul_of_nonneg_left hcU (by positivity)
      _ = ∑ c ∈ Ip, hm2 * ((Λ.filter (· ∈ Q c)).card : ℝ) := by rw [Finset.mul_sum]
      _ ≤ ∑ c ∈ Ip, ((volume (Q c)).toReal + b) :=
          Finset.sum_le_sum fun c _ => by linarith [(abs_le.1 (hcell c)).2]
      _ = Sp + Ip.card * b := by rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul]
      _ ≤ Sp + (M : ℝ) ^ 2 * b := add_le_add le_rfl (mul_le_mul_of_nonneg_right (hcard Ip) hb0)
  rw [abs_lt]
  constructor <;> linarith

end JitHyper


end

end QE.Poisson
