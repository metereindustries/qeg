-- SPDX-License-Identifier: MIT
-- Copyright 2026 Metere Industries, Inc. Author: Alfredo Metere.
-- Quasi-Euclidean Granular Geometry. Any derivative work must carry this notice:
--   This work is derivative of the Quasi-Euclidean Granular Geometry book
--   authored by Alfredo Metere. Copyright 2026 Metere Industries, Inc.
--   All rights reserved
-- See LICENSE.md and NOTICE.

import QuasiEuclidean.Ch03_Measure
import QuasiEuclidean.Ch04_Diff
import QuasiEuclidean.Ch05_Integral
import QuasiEuclidean.NSA_Internal

/-!
# Review infrastructure B: chapters 3, 4 and 5

Lean statements closing the gaps between the printed statements of chapters 3–5
and their earlier Lean constants:

* `QE.Diff`: linearity, constants and identity for `D⁻` and `D°`
  (`prop:differential-linear`); lattice chords of a granularly convex function
  have non-decreasing slopes (`thm:differential-convex`); the lattice form of
  the boundedness of `D⁺`, `D⁻`, with the norm `1/ε` attained
  (`thm:differential-bounded`).
* `QE.Measure`: boxes with mixed closed/open sides (`thm:measure-box`); the
  Lebesgue comparison for a finite union of closed intervals
  (`prop:measure-elementary-error`, a shadow statement); the snapped image of a
  countably infinite standard set is external, every hyperfinite superset has
  unlimited cardinality, and the Farey example (`thm:countable-positive`); the
  lattice trace of the classical Cantor set at triadic depth `K`
  (`prop:measure-cantor`).
* `QE.Integral`: the explicit two-sided horizon bound for the granular Gamma
  integral (`thm:integral-gamma-limit`) and the second-order expansion of the
  granular `∫₀¹ dx/x` (`thm:integral-harmonic`).
-/

open Finset Filter Topology

set_option linter.unusedSectionVars false

namespace QE.Diff

section Algebra

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

theorem Dm_smul (ε c : K) (f : K → K) (x : K) :
    QE.Dm ε (fun y => c * f y) x = c * QE.Dm ε f x := by
  unfold QE.Dm; ring

theorem Dm_const (ε c : K) (x : K) : QE.Dm ε (fun _ => c) x = 0 := by
  unfold QE.Dm; simp

theorem Dm_id (ε : K) (hε : ε ≠ 0) (x : K) : QE.Dm ε (fun y => y) x = 1 := by
  unfold QE.Dm; field_simp; ring

theorem Dc_smul (ε c : K) (f : K → K) (x : K) :
    QE.Dc ε (fun y => c * f y) x = c * QE.Dc ε f x := by
  unfold QE.Dc; ring

theorem Dc_const (ε c : K) (x : K) : QE.Dc ε (fun _ => c) x = 0 := by
  unfold QE.Dc; simp

theorem Dc_id (ε : K) (hε : ε ≠ 0) (x : K) : QE.Dc ε (fun y => y) x = 1 := by
  unfold QE.Dc; field_simp; ring

/-- `prop:differential-linear` in one statement: `D⁺, D⁻, D°` are linear, kill
constants and send the identity to `1`. -/
theorem linear_all (ε : K) (hε : ε ≠ 0) (c : K) (f g : K → K) (x : K) :
    (QE.Dp ε (fun y => f y + g y) x = QE.Dp ε f x + QE.Dp ε g x ∧
      QE.Dp ε (fun y => c * f y) x = c * QE.Dp ε f x ∧
      QE.Dp ε (fun _ => c) x = 0 ∧ QE.Dp ε (fun y => y) x = 1) ∧
    (QE.Dm ε (fun y => f y + g y) x = QE.Dm ε f x + QE.Dm ε g x ∧
      QE.Dm ε (fun y => c * f y) x = c * QE.Dm ε f x ∧
      QE.Dm ε (fun _ => c) x = 0 ∧ QE.Dm ε (fun y => y) x = 1) ∧
    (QE.Dc ε (fun y => f y + g y) x = QE.Dc ε f x + QE.Dc ε g x ∧
      QE.Dc ε (fun y => c * f y) x = c * QE.Dc ε f x ∧
      QE.Dc ε (fun _ => c) x = 0 ∧ QE.Dc ε (fun y => y) x = 1) :=
  ⟨⟨Dp_add ε f g x, Dp_smul ε c f x, Dp_const ε c x, Dp_id ε hε x⟩,
    ⟨Dm_add ε f g x, Dm_smul ε c f x, Dm_const ε c x, Dm_id ε hε x⟩,
    ⟨Dc_add ε f g x, Dc_smul ε c f x, Dc_const ε c x, Dc_id ε hε x⟩⟩

/-! ### Convexity: chord slopes -/

/-- Telescoping: the chord increment over `[x_i, x_j]` is `2ε` times the sum of
`D⁺f` over `[x_i, x_j)`. -/
theorem chord_eq_sum_Dp (ε : K) (hε : ε ≠ 0) (f : K → K) (a : K) (i j : ℕ) (hij : i ≤ j) :
    f (a + 2 * ε * j) - f (a + 2 * ε * i)
      = 2 * ε * ∑ k ∈ Ico i j, QE.Dp ε f (a + 2 * ε * k) := by
  induction j, hij using Nat.le_induction with
  | base => simp
  | succ j hij ih =>
    rw [sum_Ico_succ_top hij, mul_add, ← ih]
    unfold QE.Dp
    have h2 : (2 * ε) ≠ 0 := mul_ne_zero two_ne_zero hε
    have e : a + 2 * ε * ((j + 1 : ℕ) : K) = a + 2 * ε * j + 2 * ε := by push_cast; ring
    rw [e]; field_simp; ring

/-- Window means of a sequence that is non-decreasing on `[0, n]` grow when the
window moves right: extending to the right. -/
private lemma mean_extend_right (d : ℕ → K) (n : ℕ)
    (hd : ∀ p q, p ≤ q → q ≤ n → d p ≤ d q) (i j : ℕ) (hij : i < j) (hj : j < n + 1)
    (_hj1 : j + 1 ≤ n + 1) :
    (∑ k ∈ Ico i j, d k) / ((j : K) - i) ≤ (∑ k ∈ Ico i (j + 1), d k) / (((j + 1 : ℕ) : K) - i) := by
  rw [sum_Ico_succ_top hij.le]
  have hm : (0 : K) < (j : K) - i := by
    have : (i : K) < j := by exact_mod_cast hij
    linarith
  have hm1 : (0 : K) < ((j + 1 : ℕ) : K) - i := by push_cast; linarith
  have hS : ∑ k ∈ Ico i j, d k ≤ ((j : K) - i) * d j := by
    have : ∑ k ∈ Ico i j, d k ≤ ∑ _k ∈ Ico i j, d j :=
      sum_le_sum fun k hk => hd k j (le_of_lt (mem_Ico.1 hk).2) (by omega)
    rw [sum_const, Nat.card_Ico, nsmul_eq_mul] at this
    have e : ((j - i : ℕ) : K) = (j : K) - i := by rw [Nat.cast_sub hij.le]
    rwa [e] at this
  rw [div_le_div_iff₀ hm hm1]
  push_cast
  nlinarith

/-- Window means grow when the left end moves right. -/
private lemma mean_shrink_left (d : ℕ → K) (n : ℕ)
    (hd : ∀ p q, p ≤ q → q ≤ n → d p ≤ d q) (i j : ℕ) (hij : i + 1 < j) (hj : j ≤ n + 1) :
    (∑ k ∈ Ico i j, d k) / ((j : K) - i) ≤ (∑ k ∈ Ico (i + 1) j, d k) / ((j : K) - (i + 1 : ℕ)) := by
  rw [← sum_Ico_consecutive _ (Nat.le_succ i) (by omega : i + 1 ≤ j), Nat.Ico_succ_singleton,
    sum_singleton]
  have hm : (0 : K) < (j : K) - i := by
    have : (i : K) + 1 < j := by exact_mod_cast hij
    linarith
  have hm1 : (0 : K) < (j : K) - (i + 1 : ℕ) := by
    have : (i : K) + 1 < j := by exact_mod_cast hij
    push_cast; linarith
  have hS : ((j : K) - (i + 1 : ℕ)) * d i ≤ ∑ k ∈ Ico (i + 1) j, d k := by
    have : ∑ _k ∈ Ico (i + 1) j, d i ≤ ∑ k ∈ Ico (i + 1) j, d k :=
      sum_le_sum fun k hk => hd i k (by have := (mem_Ico.1 hk).1; omega)
        (by have := (mem_Ico.1 hk).2; omega)
    rw [sum_const, Nat.card_Ico, nsmul_eq_mul] at this
    have e : ((j - (i + 1) : ℕ) : K) = (j : K) - (i + 1 : ℕ) := by
      rw [Nat.cast_sub (by omega : i + 1 ≤ j)]
    rwa [e] at this
  rw [div_le_div_iff₀ hm hm1]
  push_cast at hS ⊢
  nlinarith

/-- Means of a sequence non-decreasing on `[0, n]` over windows `[i, j)` ⊆ `[0, n+1)`
are monotone in both ends. -/
theorem window_mean_mono (d : ℕ → K) (n : ℕ) (hd : ∀ p q, p ≤ q → q ≤ n → d p ≤ d q)
    (i j i' j' : ℕ) (hij : i < j) (hij' : i' < j') (hii : i ≤ i') (hjj : j ≤ j')
    (hj' : j' ≤ n + 1) :
    (∑ k ∈ Ico i j, d k) / ((j : K) - i) ≤ (∑ k ∈ Ico i' j', d k) / ((j' : K) - i') := by
  -- first extend the right end from `j` to `j'`
  have hR : ∀ m, j ≤ m → m ≤ j' →
      (∑ k ∈ Ico i j, d k) / ((j : K) - i) ≤ (∑ k ∈ Ico i m, d k) / ((m : K) - i) := by
    intro m hjm hmj
    induction m, hjm using Nat.le_induction with
    | base => exact le_rfl
    | succ m hjm ih =>
      exact (ih (by omega)).trans (mean_extend_right d n hd i m (by omega) (by omega) (by omega))
  -- then move the left end from `i` to `i'`
  have hL : ∀ m, i ≤ m → m ≤ i' →
      (∑ k ∈ Ico i j', d k) / ((j' : K) - i) ≤ (∑ k ∈ Ico m j', d k) / ((j' : K) - m) := by
    intro m him hmi
    induction m, him using Nat.le_induction with
    | base => exact le_rfl
    | succ m him ih =>
      exact (ih (by omega)).trans (mean_shrink_left d n hd m j' (by omega) hj')
  exact (hR j' hjj le_rfl).trans (hL i' hii le_rfl)

/-- **Convexity criterion, chord form** (`thm:differential-convex`): if
`D⁺D⁻f(x_{k+1}) ≥ 0` for `k < n`, `x_k = a + 2εk`, then the lattice chords of `f`
over `[x_i, x_j]` (`i < j ≤ n+1`) have slopes that are non-decreasing in both
endpoints: `f` is convex on the lattice points of the run. -/
theorem chord_slope_mono (ε : K) (hε : 0 < ε) (f : K → K) (a : K) (n : ℕ)
    (h : ∀ k < n, 0 ≤ QE.Dp ε (QE.Dm ε f) (a + 2 * ε * (k + 1)))
    (i j i' j' : ℕ) (hij : i < j) (hij' : i' < j') (hii : i ≤ i') (hjj : j ≤ j')
    (hj' : j' ≤ n + 1) :
    (f (a + 2 * ε * j) - f (a + 2 * ε * i)) / ((a + 2 * ε * j) - (a + 2 * ε * i)) ≤
      (f (a + 2 * ε * j') - f (a + 2 * ε * i')) / ((a + 2 * ε * j') - (a + 2 * ε * i')) := by
  have hmono := Dp_mono_of_second_nonneg ε hε f a n h
  have h2 : (0 : K) < 2 * ε := by positivity
  have key : ∀ p q : ℕ, p < q →
      (f (a + 2 * ε * q) - f (a + 2 * ε * p)) / ((a + 2 * ε * q) - (a + 2 * ε * p))
        = (∑ k ∈ Ico p q, QE.Dp ε f (a + 2 * ε * k)) / ((q : K) - p) := by
    intro p q hpq
    rw [chord_eq_sum_Dp ε hε.ne' f a p q hpq.le]
    have : (a + 2 * ε * q) - (a + 2 * ε * p) = 2 * ε * ((q : K) - p) := by ring
    rw [this, mul_div_mul_left _ _ h2.ne']
  rw [key i j hij, key i' j' hij']
  exact window_mean_mono (fun k => QE.Dp ε f (a + 2 * ε * k)) n
    (fun p q hpq hqn => hmono p q hpq hqn) i j i' j' hij hij' hii hjj hj'

/-! ### Boundedness on the lattice -/

/-- **Boundedness of `D⁺`, `D⁻` on the lattice** (`thm:differential-bounded`):
if `|f| ≤ B` at the lattice points `2εk`, then `|D⁺f| ≤ B/ε` and `|D⁻f| ≤ B/ε`
at the lattice points; and the bound is attained by a function with `|f| ≤ 1`
on the lattice, so the operator norm on bounded lattice functions is exactly
`1/ε`. -/
theorem Dp_Dm_bounded_lattice (ε : K) (hε : 0 < ε) :
    (∀ (f : K → K) (B : K), (∀ k : ℤ, |f (2 * ε * k)| ≤ B) →
      ∀ k : ℤ, |QE.Dp ε f (2 * ε * k)| ≤ B / ε ∧ |QE.Dm ε f (2 * ε * k)| ≤ B / ε) ∧
    (∃ f : K → K, (∀ k : ℤ, |f (2 * ε * k)| ≤ 1) ∧
      |QE.Dp ε f (2 * ε * (0 : ℤ))| = 1 / ε ∧ |QE.Dm ε f (2 * ε * (0 : ℤ))| = 1 / ε) := by
  have h2 : (0 : K) < 2 * ε := by positivity
  have core : ∀ (f : K → K) (B : K) (x y : K), |f x| ≤ B → |f y| ≤ B →
      |(f x - f y) / (2 * ε)| ≤ B / ε := by
    intro f B x y hx hy
    rw [abs_div, abs_of_pos h2, div_le_div_iff₀ h2 hε]
    have := abs_sub (f x) (f y)
    nlinarith
  refine ⟨fun f B hB k => ⟨?_, ?_⟩, ?_⟩
  · unfold QE.Dp
    have e : 2 * ε * (k : K) + 2 * ε = 2 * ε * ((k + 1 : ℤ) : K) := by push_cast; ring
    rw [e]; exact core f B _ _ (hB (k + 1)) (hB k)
  · unfold QE.Dm
    have e : 2 * ε * (k : K) - 2 * ε = 2 * ε * ((k - 1 : ℤ) : K) := by push_cast; ring
    rw [e]; exact core f B _ _ (hB k) (hB (k - 1))
  · classical
    -- `f = 1` at the lattice point `0`, `-1` elsewhere
    refine ⟨fun y => if y = 0 then 1 else -1, fun k => ?_, ?_, ?_⟩
    · beta_reduce; split_ifs <;> simp
    · unfold QE.Dp
      have hne : (2 * ε : K) ≠ 0 := by positivity
      simp only [Int.cast_zero, mul_zero, zero_add, hne, ite_true, ite_false]
      rw [show ((-1 : K) - 1) / (2 * ε) = -(1 / ε) by field_simp; ring, abs_neg,
        abs_of_pos (by positivity)]
    · unfold QE.Dm
      have hne : (-(2 * ε) : K) ≠ 0 := by simp; exact hε.ne'
      simp only [Int.cast_zero, mul_zero, zero_sub, hne, ite_true, ite_false]
      rw [show ((1 : K) - -1) / (2 * ε) = 1 / ε by field_simp; ring,
        abs_of_pos (by positivity)]

end Algebra

end QE.Diff

namespace QE.Measure

section Boxes

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-- **Boxes with mixed sides** (`thm:measure-box`, general case): a product of
lattice intervals with `cᵢ = nClosed lᵢ rᵢ` closed endpoints in the `i`-th factor
(`aᵢ < bᵢ`) has granular measure `∏ (Lᵢ + (cᵢ - 1)·2ε)`. -/
theorem muN_box_mixed (n : ℕ) (ε : K) (l r : Fin n → Bool) (a b : Fin n → ℤ)
    (h : ∀ i, a i < b i) :
    muN n ε (Fintype.piFinset fun i => itv (l i) (r i) (a i) (b i)) =
      ∏ i, ((centre ε (b i) - centre ε (a i)) + ((nClosed (l i) (r i) : K) - 1) * (2 * ε)) := by
  unfold muN
  rw [Fintype.card_piFinset]; push_cast
  rw [← Fin.prod_const, ← prod_mul_distrib]
  refine prod_congr rfl fun i _ => ?_
  rw [← mu_itv ε (l i) (r i) (h i)]
  unfold mu; ring

end Boxes

end QE.Measure

namespace QE.Integral

/-! ### Granular Gamma: the explicit horizon bound (`thm:integral-gamma-limit`) -/

theorem fall_horizon_nonneg (ε : ℝ) (hε : 0 < ε) (N j : ℕ) :
    0 ≤ QE.fall ε (2 * ε * N) j := by
  unfold QE.fall
  by_cases hj : j ≤ N
  · refine prod_nonneg fun i hi => ?_
    have : (i : ℝ) ≤ N := by exact_mod_cast (by have := mem_range.1 hi; omega : i ≤ N)
    nlinarith
  · rw [prod_eq_zero (i := N) (mem_range.2 (by omega)) (by ring)]

theorem fall_horizon_le (ε : ℝ) (hε : 0 < ε) (N j : ℕ) :
    QE.fall ε (2 * ε * N) j ≤ (2 * ε * N) ^ j := by
  unfold QE.fall
  by_cases hj : j ≤ N
  · rw [← Fin.prod_const, ← prod_range (fun _ => 2 * ε * (N : ℝ))]
    refine Finset.prod_le_prod₀ (fun i hi => ?_) (fun i _ => ?_)
    · have : (i : ℝ) ≤ N := by exact_mod_cast (by have := mem_range.1 hi; omega : i ≤ N)
      nlinarith
    · have : (0 : ℝ) ≤ i := Nat.cast_nonneg i
      nlinarith
  · rw [prod_eq_zero (i := N) (mem_range.2 (by omega)) (by ring)]
    positivity

/-- The defect `k! - Γ_ε^Ω(k+1)` lies in `[0, (k+1)! Ω^k (1+2ε)^{-N}]` for `Ω = 2εN ≥ 1`. -/
theorem gamma_defect_bounds (ε : ℝ) (hε : 0 < ε) (k N : ℕ) (hΩ : 1 ≤ 2 * ε * N) :
    0 ≤ (k.factorial : ℝ) - gammaG ε k N ∧
      (k.factorial : ℝ) - gammaG ε k N ≤
        ((k + 1).factorial : ℝ) * (2 * ε * N) ^ k * (1 + 2 * ε)⁻¹ ^ N := by
  rw [gammaG_closed ε hε k N]
  have hq : 0 ≤ (1 + 2 * ε : ℝ)⁻¹ ^ N := by positivity
  set S := ∑ j ∈ range (k + 1), (k.factorial : ℝ) / (j.factorial : ℝ) * QE.fall ε (2 * ε * N) j
  have hS0 : 0 ≤ S := sum_nonneg fun j _ =>
    mul_nonneg (by positivity) (fall_horizon_nonneg ε hε N j)
  have hS1 : S ≤ ((k + 1).factorial : ℝ) * (2 * ε * N) ^ k := by
    have : S ≤ ∑ _j ∈ range (k + 1), (k.factorial : ℝ) * (2 * ε * N) ^ k := by
      refine sum_le_sum fun j hj => ?_
      have hjk : j ≤ k := by have := mem_range.1 hj; omega
      have h1 : (k.factorial : ℝ) / (j.factorial : ℝ) ≤ k.factorial := by
        refine div_le_self (by positivity) ?_
        exact_mod_cast Nat.one_le_iff_ne_zero.2 (Nat.factorial_ne_zero j)
      have h2 : QE.fall ε (2 * ε * N) j ≤ (2 * ε * N) ^ k :=
        (fall_horizon_le ε hε N j).trans (pow_le_pow_right₀ hΩ hjk)
      exact mul_le_mul h1 h2 (fall_horizon_nonneg ε hε N j) (by positivity)
    rw [sum_const, card_range, nsmul_eq_mul] at this
    have e : ((k + 1).factorial : ℝ) = ((k + 1 : ℕ) : ℝ) * k.factorial := by
      push_cast [Nat.factorial_succ]; ring
    rw [e]; linarith
  constructor
  · nlinarith
  · nlinarith

/-- **Explicit horizon bound** (`thm:integral-gamma-limit`, last assertion, for real
`ε`): for `0 < ε ≤ 1/2` and `Ω = 2εN ≥ 1`,
`0 ≤ k! - Γ_ε^Ω(k+1) ≤ (k+1)! Ω^k e^{-Ω/2}`. -/
theorem gamma_horizon_bound (ε : ℝ) (hε : 0 < ε) (hε2 : ε ≤ 1 / 2) (k N : ℕ)
    (hΩ : 1 ≤ 2 * ε * N) :
    0 ≤ (k.factorial : ℝ) - gammaG ε k N ∧
      (k.factorial : ℝ) - gammaG ε k N ≤
        ((k + 1).factorial : ℝ) * (2 * ε * N) ^ k * Real.exp (-(2 * ε * N) / 2) := by
  obtain ⟨h0, h1⟩ := gamma_defect_bounds ε hε k N hΩ
  refine ⟨h0, h1.trans ?_⟩
  have hexp : (1 + 2 * ε)⁻¹ ^ N ≤ Real.exp (-(2 * ε * N) / 2) := by
    refine (pow_inv_le_exp ε hε N).trans (Real.exp_le_exp.2 ?_)
    have hN : 0 ≤ 2 * ε * (N : ℝ) := by positivity
    rw [div_le_div_iff₀ (by linarith) (by norm_num)]
    nlinarith
  exact mul_le_mul_of_nonneg_left hexp (by positivity)

/-- `t^k e^{-t/2} → 0` as `t → ∞`. -/
theorem tendsto_pow_mul_exp_neg_half (k : ℕ) :
    Tendsto (fun t : ℝ => t ^ k * Real.exp (-t / 2)) atTop (𝓝 0) := by
  have h := (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero k).comp
    (tendsto_id.atTop_div_const (by norm_num : (0 : ℝ) < 2))
  have h2 := h.const_mul ((2 : ℝ) ^ k)
  rw [mul_zero] at h2
  refine h2.congr fun t => ?_
  simp only [Function.comp, id]
  rw [show -t / 2 = -(t / 2) by ring, div_pow]
  field_simp

/-- **Explicit horizon bound at an infinite horizon** (`thm:integral-gamma-limit`, the
hyperreal form): let `ε = [e_m]` with `0 < e_m ≤ 1/2` and let the horizon
`Ω = [2 e_m N_m]` be positive unlimited.  Then the hyperreal defect
`k! - Γ_ε^Ω(k+1)` lies between `0` and `(k+1)! Ω^k e^{-Ω/2}`, and this bound is
infinitesimal. -/
theorem gamma_horizon_bound_hyper (e : ℕ → ℝ) (N : ℕ → ℕ)
    (he : ∀ᶠ m in (hyperfilter ℕ : Filter ℕ), 0 < e m ∧ e m ≤ 1 / 2)
    (hΩ : ∀ r : ℝ, ∀ᶠ m in (hyperfilter ℕ : Filter ℕ), r < 2 * e m * N m) (k : ℕ) :
    0 ≤ Hyperreal.ofSeq (fun m => (k.factorial : ℝ) - gammaG (e m) k (N m)) ∧
      Hyperreal.ofSeq (fun m => (k.factorial : ℝ) - gammaG (e m) k (N m)) ≤
        Hyperreal.ofSeq (fun m => ((k + 1).factorial : ℝ) * (2 * e m * N m) ^ k *
          Real.exp (-(2 * e m * N m) / 2)) ∧
      QE.NSA.IsInfinitesimal (Hyperreal.ofSeq (fun m =>
        ((k + 1).factorial : ℝ) * (2 * e m * N m) ^ k * Real.exp (-(2 * e m * N m) / 2))) := by
  have hb : ∀ᶠ m in (hyperfilter ℕ : Filter ℕ),
      0 ≤ (k.factorial : ℝ) - gammaG (e m) k (N m) ∧
      (k.factorial : ℝ) - gammaG (e m) k (N m) ≤ ((k + 1).factorial : ℝ) * (2 * e m * N m) ^ k *
          Real.exp (-(2 * e m * N m) / 2) := by
    filter_upwards [he, hΩ 1] with m hm h1
    exact gamma_horizon_bound (e m) hm.1 hm.2 k (N m) h1.le
  refine ⟨?_, ?_, ?_⟩
  · exact Hyperreal.ofSeq_le_ofSeq.2 (by filter_upwards [hb] with m hm using hm.1)
  · exact Hyperreal.ofSeq_le_ofSeq.2 (by filter_upwards [hb] with m hm using hm.2)
  · have hT : Tendsto (fun m => 2 * e m * (N m : ℝ)) (hyperfilter ℕ : Filter ℕ) atTop :=
      tendsto_atTop.2 fun r => by filter_upwards [hΩ r] with m hm using hm.le
    have := ((tendsto_pow_mul_exp_neg_half k).comp hT).const_mul ((k + 1).factorial : ℝ)
    rw [mul_zero] at this
    rw [QE.NSA.isInfinitesimal_ofSeq_iff]
    intro r hr
    have h := (Metric.tendsto_nhds.1 this) r hr
    filter_upwards [h] with m hm
    simpa [Real.dist_eq, mul_assoc] using hm

end QE.Integral

namespace QE.Measure

/-! ### One-dimensional elementary sets against Lebesgue measure
(`prop:measure-elementary-error`, shadow statement) -/

theorem mem_Icc_lattice_iff {ε : ℝ} (hε : 0 < ε) (a b : ℝ) (k : ℤ) :
    2 * ε * (k : ℝ) ∈ Set.Icc a b ↔ k ∈ Icc ⌈a / (2 * ε)⌉ ⌊b / (2 * ε)⌋ := by
  have h2 : 0 < 2 * ε := by positivity
  rw [Set.mem_Icc, mem_Icc, Int.ceil_le, Int.le_floor, div_le_iff₀ h2, le_div_iff₀ h2]
  constructor <;> rintro ⟨h1, h3⟩ <;> constructor <;> linarith

/-- The lattice indices of a finite union of closed intervals form the union of
the index runs. -/
theorem lattice_biUnion_eq {ε : ℝ} (hε : 0 < ε) (s : Finset (ℝ × ℝ)) :
    {k : ℤ | 2 * ε * (k : ℝ) ∈ ⋃ p ∈ s, Set.Icc p.1 p.2} =
      ↑(s.biUnion fun p => Icc ⌈p.1 / (2 * ε)⌉ ⌊p.2 / (2 * ε)⌋) := by
  ext k
  simp only [Set.mem_ofPred_eq, Set.mem_iUnion, coe_biUnion, mem_coe, exists_prop]
  exact exists_congr fun p => and_congr_right fun _ => mem_Icc_lattice_iff hε _ _ k

/-- **Elementary sets in one dimension, against Lebesgue measure**: for any finite
family of `m` closed real intervals (overlaps allowed) with union `E`,
`|μ(E ∩ 2εℤ) - λ(E)| ≤ m · 2ε`, where `μ(E ∩ 2εℤ) = 2ε · #{k : 2εk ∈ E}`.
Overlapping intervals are merged (`E` is unchanged and `m` drops); for pairwise
disjoint intervals, additivity of both sides and `latCount_bound`. -/
theorem elementary_error_leb {ε : ℝ} (hε : 0 < ε) (s : Finset (ℝ × ℝ))
    (hs : ∀ p ∈ s, p.1 ≤ p.2) :
    |2 * ε * ({k : ℤ | 2 * ε * (k : ℝ) ∈ ⋃ p ∈ s, Set.Icc p.1 p.2}.ncard : ℝ) -
        (MeasureTheory.volume (⋃ p ∈ s, Set.Icc p.1 p.2)).toReal| ≤ 2 * ε * s.card := by
  classical
  induction h : s.card using Nat.strong_induction_on generalizing s with
  | _ m ih =>
  by_cases hov : ∃ p ∈ s, ∃ q ∈ s, p ≠ q ∧ (Set.Icc p.1 p.2 ∩ Set.Icc q.1 q.2).Nonempty
  · obtain ⟨p, hp, q, hq, hpq, x, hx1, hx2⟩ := hov
    set s' := insert (min p.1 q.1, max p.2 q.2) ((s.erase p).erase q) with hs'
    have hq' : q ∈ s.erase p := mem_erase.2 ⟨hpq.symm, hq⟩
    have hcard : s'.card < m := by
      have h1 : s'.card ≤ ((s.erase p).erase q).card + 1 := card_insert_le _ _
      have h2 : ((s.erase p).erase q).card + 1 = (s.erase p).card := card_erase_add_one hq'
      have h3 : (s.erase p).card + 1 = s.card := card_erase_add_one hp
      omega
    have hU : (⋃ r ∈ s', Set.Icc r.1 r.2) = ⋃ r ∈ s, Set.Icc r.1 r.2 := by
      have hpq_union : Set.Icc p.1 p.2 ∪ Set.Icc q.1 q.2 =
          Set.Icc (min p.1 q.1) (max p.2 q.2) :=
        Set.Icc_union_Icc' (le_trans hx2.1 hx1.2) (le_trans hx1.1 hx2.2)
      have hsplit : (⋃ r ∈ s, Set.Icc r.1 r.2) = Set.Icc p.1 p.2 ∪ (Set.Icc q.1 q.2 ∪
          ⋃ r ∈ (s.erase p).erase q, Set.Icc r.1 r.2) := by
        conv_lhs => rw [← insert_erase hp, ← insert_erase hq']
        simp only [set_biUnion_insert]
      rw [hsplit, hs', set_biUnion_insert, ← Set.union_assoc, hpq_union]
    have hs'le : ∀ r ∈ s', r.1 ≤ r.2 := by
      intro r hr
      rcases mem_insert.1 hr with rfl | hr
      · exact le_trans (min_le_left _ _) ((hs p hp).trans (le_max_left _ _))
      · exact hs r (mem_of_mem_erase (mem_of_mem_erase hr))
    have := ih s'.card (h ▸ hcard) s' hs'le rfl
    rw [hU] at this
    refine this.trans ?_
    have : (s'.card : ℝ) ≤ m := by exact_mod_cast hcard.le
    rw [← h] at this ⊢
    nlinarith
  · push Not at hov
    have hdisj : (s : Set (ℝ × ℝ)).PairwiseDisjoint fun r => Set.Icc r.1 r.2 := by
      intro p hp q hq hpq
      rw [Function.onFun, Set.disjoint_iff_inter_eq_empty]
      exact hov p hp q hq hpq
    have hdisjI : (s : Set (ℝ × ℝ)).PairwiseDisjoint
        fun r => Icc ⌈r.1 / (2 * ε)⌉ ⌊r.2 / (2 * ε)⌋ := by
      intro p hp q hq hpq
      rw [Function.onFun, Finset.disjoint_left]
      intro k hk1 hk2
      exact Set.disjoint_left.1 (hdisj hp hq hpq) ((mem_Icc_lattice_iff hε _ _ k).2 hk1)
        ((mem_Icc_lattice_iff hε _ _ k).2 hk2)
    rw [lattice_biUnion_eq hε, Set.ncard_coe_finset]
    rw [MeasureTheory.measure_biUnion_finset hdisj (fun r _ => measurableSet_Icc)]
    rw [ENNReal.toReal_sum (fun r _ => by simp)]
    have hv : ∀ r ∈ s, (MeasureTheory.volume (Set.Icc r.1 r.2)).toReal = r.2 - r.1 := by
      intro r hr
      rw [Real.volume_Icc, ENNReal.toReal_ofReal (by linarith [hs r hr])]
    rw [sum_congr rfl hv, ← h]
    exact elementary_error hε s Prod.fst Prod.snd hs hdisjI

end QE.Measure

namespace QE.Measure

open QE.NSA

/-! ### Countable sets: externality, unlimited supersets, Farey (`thm:countable-positive`) -/

section Countable

variable {α : Type*}

theorem isInternal_singleton (x : Ult α) : IsInternal ({x} : Set (Ult α)) := by
  obtain ⟨u, rfl⟩ := exists_rep x
  refine ⟨fun n => {u n}, ?_⟩
  ext y; obtain ⟨v, rfl⟩ := exists_rep y
  rw [mem_internal, Set.mem_singleton_iff]
  exact Germ.coe_eq

/-- Every finite set of the ultrapower is internal. -/
theorem isInternal_of_finite {t : Set (Ult α)} (ht : t.Finite) : IsInternal t := by
  induction t, ht using Set.Finite.induction_on with
  | empty => exact isInternal_empty
  | @insert a s _ _ ih =>
    rw [Set.insert_eq]; exact (isInternal_singleton a).union ih

/-- **A countably infinite set of the ultrapower is external** (by countable
saturation: removing the first `k` elements leaves nonempty internal sets with
empty intersection). -/
theorem not_isInternal_of_countable_infinite {S : Set (Ult α)} (hc : S.Countable)
    (hi : S.Infinite) : ¬ IsInternal S := by
  intro hS
  obtain ⟨f, hf⟩ := hc.exists_eq_range hi.nonempty
  set T : ℕ → Set (Ult α) := fun k => S \ (f '' Set.Iic k) with hT
  have hTi : ∀ k, IsInternal (T k) := fun k =>
    hS.diff (isInternal_of_finite ((Set.finite_Iic k).image f))
  have hTne : ∀ k, (T k).Nonempty := fun k =>
    (hi.sdiff ((Set.finite_Iic k).image f)).nonempty
  have hanti : Antitone T := by
    intro k l hkl x hx
    exact ⟨hx.1, fun h => hx.2 (Set.image_mono (Set.Iic_subset_Iic.2 hkl) h)⟩
  obtain ⟨x, hx⟩ := saturation_decreasing T hTi hTne hanti
  have hxS : x ∈ S := (Set.mem_iInter.1 hx 0).1
  rw [hf] at hxS
  obtain ⟨j, rfl⟩ := hxS
  exact (Set.mem_iInter.1 hx j).2 ⟨j, Set.mem_Iic.2 le_rfl, rfl⟩

end Countable

variable {n : ℕ}

/-- The snap `⌊x⌉ = 2ε⌊x/(2ε) + 1/2⌋` (coordinatewise) of a standard point
`a ∈ ℝⁿ`, for `ε = [e_m]`, as an element of the ultrapower. -/
noncomputable def snapG (e : ℕ → ℝ) (a : Fin n → ℝ) : Ult (Fin n → ℝ) :=
  ((fun m i => 2 * e m * (⌊(a i + e m) / (2 * e m)⌋ : ℝ) : ℕ → Fin n → ℝ) : Ult (Fin n → ℝ))

theorem snap_close {e : ℝ} (he : 0 < e) (t : ℝ) : |2 * e * (⌊(t + e) / (2 * e)⌋ : ℝ) - t| ≤ e := by
  obtain ⟨h1, h2⟩ := QE.NSA.snap_bounds he t
  rw [abs_le]; constructor <;> linarith

/-- Distinct standard points have eventually distinct snaps. -/
theorem snap_eventually_ne {e : ℕ → ℝ} (he0 : 0 < Hyperreal.ofSeq e)
    (hinf : IsInfinitesimal (Hyperreal.ofSeq e)) {a a' : Fin n → ℝ} (h : a ≠ a') :
    ∀ᶠ m in (hyperfilter ℕ : Filter ℕ),
      (fun i => 2 * e m * (⌊(a i + e m) / (2 * e m)⌋ : ℝ)) ≠
        (fun i => 2 * e m * (⌊(a' i + e m) / (2 * e m)⌋ : ℝ)) := by
  obtain ⟨i, hi⟩ := Function.ne_iff.1 h
  have hd : 0 < |a i - a' i| := abs_pos.2 (sub_ne_zero.2 hi)
  filter_upwards [Hyperreal.ofSeq_lt_ofSeq.1 he0, eventually_small hinf (by positivity :
    0 < |a i - a' i| / 4)] with m hm hsm
  intro heq
  have := congrFun heq i
  have c1 := snap_close hm (a i)
  have c2 := snap_close hm (a' i)
  rw [this] at c1
  have : |a i - a' i| ≤ 2 * e m := by
    calc |a i - a' i| = |(2 * e m * (⌊(a' i + e m) / (2 * e m)⌋ : ℝ) - a' i) -
          (2 * e m * (⌊(a' i + e m) / (2 * e m)⌋ : ℝ) - a i)| := by ring_nf
      _ ≤ _ := abs_sub _ _
      _ ≤ e m + e m := by linarith
      _ = 2 * e m := by ring
  linarith

theorem snapG_injective {e : ℕ → ℝ} (he0 : 0 < Hyperreal.ofSeq e)
    (hinf : IsInfinitesimal (Hyperreal.ofSeq e)) :
    Function.Injective (snapG (n := n) e) := by
  intro a a' h
  by_contra hne
  have h1 := snap_eventually_ne he0 hinf hne
  have h2 := Germ.coe_eq.1 h
  obtain ⟨m, hm1, hm2⟩ := (h1.and h2).exists
  exact hm1 hm2

/-- **`thm:countable-positive` (ii)**: for a positive infinitesimal `ε`, the snapped
image `⌊A⌉ = {⌊a⌉ : a ∈ A}` of a countably infinite standard set `A ⊆ ℝⁿ` is
external. -/
theorem snap_image_external {e : ℕ → ℝ} (he0 : 0 < Hyperreal.ofSeq e)
    (hinf : IsInfinitesimal (Hyperreal.ofSeq e)) {A : Set (Fin n → ℝ)} (hc : A.Countable)
    (hi : A.Infinite) : ¬ IsInternal (snapG e '' A) :=
  not_isInternal_of_countable_infinite (hc.image _)
    (hi.image (snapG_injective he0 hinf).injOn)

/-- **`thm:countable-positive` (iii)**: every hyperfinite set `B = [B_m]` of lattice
points containing the snapped image of an infinite standard set `A` has, for
every standard `k`, at least `k` elements; its internal cardinality is unlimited
and its granular measure `(2ε)ⁿ #B` is at least `k (2ε)ⁿ`. -/
theorem superset_snap_unlimited {e : ℕ → ℝ} (he0 : 0 < Hyperreal.ofSeq e)
    (hinf : IsInfinitesimal (Hyperreal.ofSeq e)) {A : Set (Fin n → ℝ)} (hi : A.Infinite)
    (Bs : ℕ → Finset (Fin n → ℝ)) (hB : snapG e '' A ⊆ hfin Bs) :
    (∀ k : ℕ, ∀ᶠ m in (hyperfilter ℕ : Filter ℕ), k ≤ (Bs m).card) ∧
    IsUnlimited (hcard (hfin Bs)) ∧
    (∀ k : ℕ, (k : ℝ*) * (2 * Hyperreal.ofSeq e) ^ n ≤
      Hyperreal.ofSeq (fun m => (2 * e m) ^ n * ((Bs m).card : ℝ))) := by
  classical
  have key : ∀ k : ℕ, ∀ᶠ m in (hyperfilter ℕ : Filter ℕ), k ≤ (Bs m).card := by
    intro k
    obtain ⟨t, htA, htc⟩ := hi.exists_subset_card_eq k
    let s : ℕ → (Fin n → ℝ) → (Fin n → ℝ) :=
      fun m a i => 2 * e m * (⌊(a i + e m) / (2 * e m)⌋ : ℝ)
    have hmem : ∀ᶠ m in (hyperfilter ℕ : Filter ℕ), ∀ a ∈ t, s m a ∈ Bs m := by
      refine (Filter.eventually_all_finset t).2 fun a ha => ?_
      have := hB ⟨a, htA ha, rfl⟩
      exact (mem_internal _ _).1 this
    have hinj : ∀ᶠ m in (hyperfilter ℕ : Filter ℕ), ∀ p ∈ t ×ˢ t, p.1 ≠ p.2 → s m p.1 ≠ s m p.2 := by
      refine (Filter.eventually_all_finset (t ×ˢ t)).2 fun p _ => ?_
      by_cases hp : p.1 = p.2
      · exact Filter.Eventually.of_forall fun _ h => absurd hp h
      · filter_upwards [snap_eventually_ne he0 hinf hp] with m hm _ using hm
    filter_upwards [hmem, hinj] with m hm1 hm2
    have hI : Set.InjOn (s m) t := by
      intro a ha a' ha' heq
      by_contra hne
      exact hm2 (a, a') (mem_product.2 ⟨ha, ha'⟩) hne heq
    rw [← htc, ← card_image_of_injOn hI]
    exact card_le_card fun x hx => by
      obtain ⟨a, ha, rfl⟩ := mem_image.1 hx; exact hm1 a ha
  refine ⟨key, fun k => ?_, fun k => ?_⟩
  · rw [hcard_hfin]
    exact Germ.coe_lt.2 (by filter_upwards [key (k + 1)] with m hm using hm)
  · have h1 : ((k : ℝ) : ℝ*) * (2 * Hyperreal.ofSeq e) ^ n =
        Hyperreal.ofSeq (fun m => (k : ℝ) * (2 * e m) ^ n) := rfl
    rw [show ((k : ℝ*)) = ((k : ℝ) : ℝ*) by norm_cast, h1]
    refine Hyperreal.ofSeq_le_ofSeq.2 ?_
    filter_upwards [key k, Hyperreal.ofSeq_lt_ofSeq.1 he0] with m hm hem
    have : (k : ℝ) ≤ (Bs m).card := by exact_mod_cast hm
    have : 0 ≤ (2 * e m) ^ n := by have : (0:ℝ) < e m := hem; positivity
    nlinarith

/-- **`thm:countable-positive` (iv)**, finitary content in dimension `n`: the image of
`H` indices has granular measure at most `H (2ε)ⁿ`, with equality iff the
labelling is injective on them. -/
theorem muN_image_range {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    {ε : K} (hε : 0 < ε) (H : ℕ) (f : ℕ → Fin n → ℤ) :
    muN n ε ((range H).image f) ≤ (2 * ε) ^ n * H ∧
      (muN n ε ((range H).image f) = (2 * ε) ^ n * H ↔ Set.InjOn f (range H)) := by
  classical
  unfold muN
  have hp : (0 : K) < (2 * ε) ^ n := by positivity
  refine ⟨mul_le_mul_of_nonneg_left (by exact_mod_cast card_image_le.trans (card_range H).le)
    hp.le, ?_⟩
  rw [mul_right_inj' hp.ne']
  constructor
  · intro h
    have : ((range H).image f).card = (range H).card := by
      rw [card_range]; exact_mod_cast h
    exact card_image_iff.1 this
  · intro h; rw [card_image_of_injOn h, card_range]

/-- **`thm:countable-positive` (iv)**, containment: for an enumeration `a` of `A` and an
unlimited `H = [H_m]`, the internal set `A_H = {⌊a_j⌉ : j < H}` contains the snap of
every `a_j` with standard `j`, hence `⌊A⌉ ⊆ A_H` when `a` enumerates `A`. -/
theorem snap_subset_AH {e : ℕ → ℝ} (a : ℕ → Fin n → ℝ) (H : ℕ → ℕ)
    (hH : IsUnlimited (H : Ult ℕ)) :
    snapG e '' Set.range a ⊆
      hfin (fun m => (range (H m)).image fun j i =>
        2 * e m * (⌊(a j i + e m) / (2 * e m)⌋ : ℝ)) := by
  classical
  rintro _ ⟨_, ⟨j, rfl⟩, rfl⟩
  refine (mem_internal _ _).2 ?_
  have := Germ.coe_lt.1 (hH j)
  filter_upwards [this] with m hm
  exact mem_coe.2 (mem_image.2 ⟨j, mem_range.2 hm, rfl⟩)

/-! #### The Farey example (`thm:countable-positive` (v)) -/

/-- The Farey set `F_M = {p/q : 0 ≤ p ≤ q, 1 ≤ q ≤ M}`. -/
noncomputable def fareyFin (M : ℕ) : Finset ℝ :=
  ((range (M + 1) ×ˢ range (M + 1)).filter (fun pq => 1 ≤ pq.2 ∧ pq.1 ≤ pq.2)).image
    fun pq => (pq.1 : ℝ) / pq.2

theorem fareyFin_card_le (M : ℕ) : (fareyFin M).card ≤ (M + 1) ^ 2 := by
  unfold fareyFin
  refine card_image_le.trans ((card_filter_le _ _).trans ?_)
  rw [card_product, card_range]; ring_nf; exact le_rfl

theorem zero_mem_fareyFin (M : ℕ) (hM : 1 ≤ M) : (0 : ℝ) ∈ fareyFin M := by
  unfold fareyFin
  refine mem_image.2 ⟨(0, 1), mem_filter.2 ⟨mem_product.2 ⟨by simp, by simp; omega⟩, by simp⟩, ?_⟩
  simp

/-- For `2ε = 1/M!`, every point of `F_M` is a lattice point. -/
theorem fareyFin_lattice (M : ℕ) {x : ℝ} (hx : x ∈ fareyFin M) :
    ∃ k : ℤ, x = 2 * (1 / (2 * (M.factorial : ℝ))) * k := by
  unfold fareyFin at hx
  obtain ⟨⟨p, q⟩, hpq, rfl⟩ := mem_image.1 hx
  simp only [mem_filter, mem_product, mem_range] at hpq
  obtain ⟨⟨-, hq⟩, hq1, -⟩ := hpq
  obtain ⟨c, hc⟩ := Nat.dvd_factorial hq1 (by omega : q ≤ M)
  refine ⟨(p * c : ℕ), ?_⟩
  have hq0 : (q : ℝ) ≠ 0 := by exact_mod_cast (by omega : q ≠ 0)
  have hf : (M.factorial : ℝ) = q * c := by exact_mod_cast hc
  have hc0 : (c : ℝ) ≠ 0 := by
    intro h; rw [h, mul_zero] at hf; exact (Nat.cast_ne_zero.2 (Nat.factorial_ne_zero M)) hf
  simp only
  push_cast
  rw [hf]; field_simp

/-- Every rational of `[0,1]` with denominator `q ≤ M` lies in `F_M`. -/
theorem rat_mem_fareyFin (r : ℚ) (hr0 : 0 ≤ r) (hr1 : r ≤ 1) (M : ℕ) (hM : r.den ≤ M) :
    (r : ℝ) ∈ fareyFin M := by
  unfold fareyFin
  have hnum : 0 ≤ r.num := Rat.num_nonneg.2 hr0
  have hle : r.num ≤ r.den := by
    have hd : (0 : ℚ) < r.den := by exact_mod_cast r.den_pos
    have h := r.num_div_den
    have : (r.num : ℚ) ≤ r.den := by
      rw [← h] at hr1; exact (div_le_one hd).1 hr1
    exact_mod_cast this
  refine mem_image.2 ⟨(r.num.toNat, r.den), mem_filter.2 ⟨mem_product.2 ⟨mem_range.2 ?_,
    mem_range.2 (by omega)⟩, ⟨r.den_pos, ?_⟩⟩, ?_⟩
  · have : r.num.toNat ≤ r.den := by omega
    omega
  · omega
  · simp only
    have : ((r.num.toNat : ℕ) : ℝ) = (r.num : ℝ) := by
      rw [← Int.cast_natCast, Int.toNat_of_nonneg hnum]
    rw [this]
    exact_mod_cast (Rat.num_div_den r)

theorem tendsto_sq_div_factorial :
    Tendsto (fun M : ℕ => ((M : ℝ) + 1) ^ 2 / (M.factorial : ℝ)) atTop (𝓝 0) := by
  have hlim : Tendsto (fun M : ℕ => (16 : ℝ) / M) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  refine squeeze_zero' (Eventually.of_forall fun M => by positivity) ?_ hlim
  filter_upwards [eventually_ge_atTop 4] with M hM
  have hM' : (4 : ℝ) ≤ M := by exact_mod_cast hM
  -- `M! ≥ M (M-1) (M-2) ≥ M³/4`
  have hfac : (M : ℝ) * (M - 1) * (M - 2) ≤ M.factorial := by
    obtain ⟨k, rfl⟩ : ∃ k, M = k + 2 := ⟨M - 2, by omega⟩
    rw [Nat.factorial_succ, Nat.factorial_succ]
    have hk : (k : ℝ) ≤ k.factorial := by exact_mod_cast Nat.self_le_factorial k
    push_cast
    have : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    have h1 : (0:ℝ) ≤ ((k:ℝ) + 1 + 1) * (k + 1) := by positivity
    nlinarith [mul_le_mul_of_nonneg_left hk h1]
  have hpos : (0 : ℝ) < M.factorial := by exact_mod_cast Nat.factorial_pos M
  rw [div_le_div_iff₀ hpos (by linarith)]
  nlinarith [mul_le_mul_of_nonneg_left hfac (by norm_num : (0:ℝ) ≤ 16)]

/-- **The Farey example** (`thm:countable-positive` (v)): let `M = [M_m]` be an
unlimited hypernatural and `2ε = 1/M!`.  The internal (hyperfinite) Farey set
`F_M = [F_{M_m}]` lies in the lattice, contains every standard rational of
`[0,1]`, and has granular measure `0 < 2ε #F_M ≤ 2ε (M+1)²`, an infinitesimal. -/
theorem farey_hyper (Ms : ℕ → ℕ) (hM : IsUnlimited (Ms : Ult ℕ)) :
    let e : ℕ → ℝ := fun m => 1 / (2 * ((Ms m).factorial : ℝ))
    hfin (fun m => fareyFin (Ms m)) ⊆ lattice (Hyperreal.ofSeq e) ∧
    (∀ r : ℚ, 0 ≤ r → r ≤ 1 → ((r : ℝ) : ℝ*) ∈ hfin (fun m => fareyFin (Ms m))) ∧
    0 < Hyperreal.ofSeq (fun m => 2 * e m * ((fareyFin (Ms m)).card : ℝ)) ∧
    Hyperreal.ofSeq (fun m => 2 * e m * ((fareyFin (Ms m)).card : ℝ)) ≤
      Hyperreal.ofSeq (fun m => 2 * e m * (((Ms m : ℝ) + 1) ^ 2)) ∧
    IsInfinitesimal (Hyperreal.ofSeq (fun m => 2 * e m * ((fareyFin (Ms m)).card : ℝ))) := by
  intro e
  have hge : ∀ q : ℕ, ∀ᶠ m in (hyperfilter ℕ : Filter ℕ), q ≤ Ms m := fun q => by
    filter_upwards [Germ.coe_lt.1 (hM q)] with m hm using hm.le
  have hT : Tendsto Ms (hyperfilter ℕ : Filter ℕ) atTop := tendsto_atTop.2 hge
  have hpos : ∀ m, 0 < 2 * e m := fun m => by simp only [e]; positivity
  have hbd : ∀ m, 2 * e m * ((fareyFin (Ms m)).card : ℝ) ≤ 2 * e m * (((Ms m : ℝ) + 1) ^ 2) :=
    fun m => mul_le_mul_of_nonneg_left (by exact_mod_cast fareyFin_card_le (Ms m)) (hpos m).le
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro x hx
    obtain ⟨u, rfl⟩ := exists_rep x
    refine (mem_lattice_ofSeq e u).2 ?_
    filter_upwards [(mem_internal _ u).1 hx] with m hm
    exact fareyFin_lattice (Ms m) hm
  · intro r h0 h1
    refine (mem_internal _ _).2 ?_
    filter_upwards [hge r.den] with m hm
    exact rat_mem_fareyFin r h0 h1 (Ms m) hm
  · refine Germ.coe_pos.2 ?_
    filter_upwards [hge 1] with m hm
    have : (0 : ℝ) < (fareyFin (Ms m)).card := by
      exact_mod_cast card_pos.2 ⟨0, zero_mem_fareyFin _ hm⟩
    exact mul_pos (hpos m) this
  · exact Hyperreal.ofSeq_le_ofSeq.2 (Eventually.of_forall hbd)
  · rw [isInfinitesimal_ofSeq_iff]
    intro t ht
    have hlim := (tendsto_sq_div_factorial.comp hT)
    filter_upwards [(Metric.tendsto_nhds.1 hlim) t ht] with m hm
    simp only [Function.comp, Real.dist_eq, sub_zero] at hm
    have h0 : 0 ≤ 2 * e m * ((fareyFin (Ms m)).card : ℝ) := by
      have := hpos m; positivity
    rw [abs_of_nonneg h0]
    have he : 2 * e m * (((Ms m : ℝ) + 1) ^ 2) = ((Ms m : ℝ) + 1) ^ 2 / ((Ms m).factorial : ℝ) := by
      simp only [e]; field_simp
    rw [abs_of_nonneg (by positivity)] at hm
    linarith [hbd m]

/-- A lattice of rational spacing consists of hyperrational points: with `2ε = [1/N_m]`,
`𝕃 ∩ [0,1] ⊆ *ℚ`, so `*ℚ ∩ [0,1] ∩ 𝕃 = [0,1] ∩ 𝕃`. -/
theorem lattice_rational (Ns : ℕ → ℕ) :
    latIcc (Hyperreal.ofSeq fun m => 1 / (2 * (Ns m : ℝ))) 0 1 ⊆
      starSet (Set.range ((↑) : ℚ → ℝ)) := by
  intro x hx
  obtain ⟨⟨Kseq, hK⟩, -, -⟩ := hx
  obtain ⟨u, rfl⟩ := exists_rep x
  refine (mem_starSet _ u).2 ?_
  have h := Germ.coe_eq.1 hK
  filter_upwards [h] with m hm
  refine ⟨(Kseq m : ℚ) / (Ns m : ℚ), ?_⟩
  rw [hm]; push_cast
  by_cases hN : (Ns m : ℝ) = 0
  · rw [hN]; simp
  · field_simp; rfl

end QE.Measure

namespace QE.Measure

open QE.NSA

/-! ### The lattice trace of the classical Cantor set (`prop:measure-cantor` (iii), (iv)) -/

/-- `x ∈ C_n` iff `x` lies in one of the construction intervals `[c/3ⁿ, (c+1)/3ⁿ]`,
`c ∈ 𝒞_n`. -/
theorem mem_preCantorSet_iff (n : ℕ) (x : ℝ) :
    x ∈ preCantorSet n ↔
      ∃ c ∈ cantorIdx n, (c : ℝ) / 3 ^ n ≤ x ∧ x ≤ ((c : ℝ) + 1) / 3 ^ n := by
  induction n generalizing x with
  | zero => simp [cantorIdx]
  | succ n ih =>
    have h3 : (0 : ℝ) < 3 ^ n := by positivity
    rw [preCantorSet_succ, Set.mem_union, Set.mem_image, Set.mem_image]
    have e1 : (∃ y, y ∈ preCantorSet n ∧ y / 3 = x) ↔ 3 * x ∈ preCantorSet n :=
      ⟨fun ⟨y, hy, hyx⟩ => by rw [← hyx]; convert hy using 1; ring,
        fun h => ⟨3 * x, h, by ring⟩⟩
    have e2 : (∃ y, y ∈ preCantorSet n ∧ (2 + y) / 3 = x) ↔ 3 * x - 2 ∈ preCantorSet n :=
      ⟨fun ⟨y, hy, hyx⟩ => by rw [← hyx]; convert hy using 1; ring,
        fun h => ⟨3 * x - 2, h, by ring⟩⟩
    rw [e1, e2, ih, ih]
    simp only [cantorIdx, mem_union, mem_image]
    have hp : (3 : ℝ) ^ (n + 1) = 3 * 3 ^ n := by ring
    constructor
    · rintro (⟨c, hc, h1, h2⟩ | ⟨c, hc, h1, h2⟩)
      · refine ⟨c, Or.inl hc, ?_, ?_⟩
        · rw [hp, div_le_iff₀ (by positivity)]; rw [div_le_iff₀ h3] at h1; linarith
        · rw [hp, le_div_iff₀ (by positivity)]; rw [le_div_iff₀ h3] at h2; linarith
      · refine ⟨c + 2 * 3 ^ n, Or.inr ⟨c, hc, rfl⟩, ?_, ?_⟩
        · push_cast; rw [hp, div_le_iff₀ (by positivity)]; rw [div_le_iff₀ h3] at h1; linarith
        · push_cast; rw [hp, le_div_iff₀ (by positivity)]; rw [le_div_iff₀ h3] at h2; linarith
    · rintro ⟨c', hc', h1, h2⟩
      rw [hp] at h1 h2
      rcases hc' with hc | ⟨c, hc, rfl⟩
      · refine Or.inl ⟨c', hc, ?_, ?_⟩
        · rw [div_le_iff₀ h3]; rw [div_le_iff₀ (by positivity)] at h1; linarith
        · rw [le_div_iff₀ h3]; rw [le_div_iff₀ (by positivity)] at h2; linarith
      · refine Or.inr ⟨c, hc, ?_, ?_⟩
        · push_cast at h1
          rw [div_le_iff₀ h3]; rw [div_le_iff₀ (by positivity)] at h1; linarith
        · push_cast at h2
          rw [le_div_iff₀ h3]; rw [le_div_iff₀ (by positivity)] at h2; linarith

/-- Endpoints of the construction intervals at stage `n`. -/
noncomputable def cantorEnds : ℕ → Set ℝ
  | 0 => {0, 1}
  | n + 1 => (· / 3) '' cantorEnds n ∪ (fun x ↦ (2 + x) / 3) '' cantorEnds n

theorem mem_cantorEnds_iff (n : ℕ) (x : ℝ) :
    x ∈ cantorEnds n ↔ ∃ c ∈ cantorIdx n, x = (c : ℝ) / 3 ^ n ∨ x = ((c : ℝ) + 1) / 3 ^ n := by
  induction n generalizing x with
  | zero => simp [cantorEnds, cantorIdx]
  | succ n ih =>
    have h3 : (0 : ℝ) < 3 ^ n := by positivity
    show x ∈ (· / 3) '' cantorEnds n ∪ (fun x ↦ (2 + x) / 3) '' cantorEnds n ↔ _
    rw [Set.mem_union, Set.mem_image, Set.mem_image]
    have e1 : (∃ y, y ∈ cantorEnds n ∧ y / 3 = x) ↔ 3 * x ∈ cantorEnds n :=
      ⟨fun ⟨y, hy, hyx⟩ => by rw [← hyx]; convert hy using 1; ring,
        fun h => ⟨3 * x, h, by ring⟩⟩
    have e2 : (∃ y, y ∈ cantorEnds n ∧ (2 + y) / 3 = x) ↔ 3 * x - 2 ∈ cantorEnds n :=
      ⟨fun ⟨y, hy, hyx⟩ => by rw [← hyx]; convert hy using 1; ring,
        fun h => ⟨3 * x - 2, h, by ring⟩⟩
    rw [e1, e2, ih, ih]
    simp only [cantorIdx, mem_union, mem_image]
    have hp : (3 : ℝ) ^ (n + 1) = 3 * 3 ^ n := by ring
    have h3' : (3 : ℝ) ^ n ≠ 0 := h3.ne'
    constructor
    · rintro (⟨c, hc, h⟩ | ⟨c, hc, h⟩)
      · refine ⟨c, Or.inl hc, ?_⟩
        rw [hp]
        rcases h with h | h
        · left; field_simp; field_simp at h; linarith
        · right; field_simp; field_simp at h; linarith
      · refine ⟨c + 2 * 3 ^ n, Or.inr ⟨c, hc, rfl⟩, ?_⟩
        push_cast; rw [hp]
        rcases h with h | h
        · left; field_simp; field_simp at h; linarith
        · right; field_simp; field_simp at h; linarith
    · rintro ⟨c', hc', h⟩
      rw [hp] at h
      rcases hc' with hc | ⟨c, hc, rfl⟩
      · refine Or.inl ⟨c', hc, ?_⟩
        rcases h with h | h
        · left; field_simp at h ⊢; linarith
        · right; field_simp at h ⊢; linarith
      · refine Or.inr ⟨c, hc, ?_⟩
        push_cast at h
        rcases h with h | h
        · left; field_simp at h ⊢; linarith
        · right; field_simp at h ⊢; linarith

theorem cantorEnds_subset_succ (n : ℕ) : cantorEnds n ⊆ cantorEnds (n + 1) := by
  induction n with
  | zero =>
    intro x hx
    show x ∈ (· / 3) '' cantorEnds 0 ∪ (fun x ↦ (2 + x) / 3) '' cantorEnds 0
    rcases hx with rfl | rfl
    · exact Or.inl ⟨0, Or.inl rfl, by norm_num⟩
    · exact Or.inr ⟨1, Or.inr rfl, by norm_num⟩
  | succ n ih =>
    show (· / 3) '' cantorEnds n ∪ (fun x ↦ (2 + x) / 3) '' cantorEnds n ⊆
      (· / 3) '' cantorEnds (n + 1) ∪ (fun x ↦ (2 + x) / 3) '' cantorEnds (n + 1)
    exact Set.union_subset_union (Set.image_mono ih) (Set.image_mono ih)

theorem cantorEnds_subset_pre (n : ℕ) : cantorEnds n ⊆ preCantorSet n := by
  induction n with
  | zero =>
    intro x hx; rcases hx with rfl | rfl <;> simp
  | succ n ih =>
    show (· / 3) '' cantorEnds n ∪ (fun x ↦ (2 + x) / 3) '' cantorEnds n ⊆ _
    rw [preCantorSet_succ]
    exact Set.union_subset_union (Set.image_mono ih) (Set.image_mono ih)

/-- Endpoints of construction intervals belong to the Cantor set. -/
theorem cantorEnds_subset_cantorSet (K : ℕ) : cantorEnds K ⊆ cantorSet := by
  intro x hx
  have hmono : Monotone cantorEnds := monotone_nat_of_le_succ cantorEnds_subset_succ
  refine Set.mem_iInter.2 fun n => ?_
  rcases le_total n K with h | h
  · exact preCantorSet_antitone h (cantorEnds_subset_pre K hx)
  · exact cantorEnds_subset_pre n (hmono h hx)

/-- The lattice indices of the stage-`K` endpoints: `{c, c+1 : c ∈ 𝒞_K}`. -/
def cantorTrace (K : ℕ) : Finset ℤ := (cantorIdx K).biUnion fun c => {(c : ℤ), (c : ℤ) + 1}

theorem cantorTrace_card (K : ℕ) : (cantorTrace K).card = 2 ^ (K + 1) := by
  unfold cantorTrace
  rw [card_biUnion]
  · rw [sum_congr rfl (fun (c : ℕ) _ => card_pair (by omega : (c : ℤ) ≠ (c : ℤ) + 1)),
      sum_const, cantorIdx_card]
    simp [pow_succ]
  · intro c hc c' hc' hne
    rw [Function.onFun, Finset.disjoint_left]
    have e1 := cantorIdx_even K c hc
    have e2 := cantorIdx_even K c' hc'
    intro x hx hx'
    simp only [mem_insert, mem_singleton] at hx hx'
    omega

/-- **The lattice trace of the Cantor set** (`prop:measure-cantor` (iii)): on the
triadic lattice `2ε = 3^{-K}`, the lattice points of the Cantor set `C` are exactly
those of its stage-`K` approximant `C_K`, namely the `2^{K+1}` endpoints of the
construction intervals, and `μ(C ∩ 𝕃) = 2 (2/3)^K`. -/
theorem cantor_lattice_trace (K : ℕ) :
    {j : ℤ | 2 * (1 / (2 * 3 ^ K) : ℝ) * j ∈ cantorSet} = ↑(cantorTrace K) ∧
    {j : ℤ | 2 * (1 / (2 * 3 ^ K) : ℝ) * j ∈ preCantorSet K} = ↑(cantorTrace K) ∧
    (cantorTrace K).card = 2 ^ (K + 1) ∧
    mu (1 / (2 * 3 ^ K) : ℝ) (cantorTrace K) = 2 * (2 / 3) ^ K := by
  have h3 : (0 : ℝ) < 3 ^ K := by positivity
  have hx : ∀ j : ℤ, 2 * (1 / (2 * 3 ^ K) : ℝ) * j = (j : ℝ) / 3 ^ K := fun j => by
    field_simp
  have pre_iff : ∀ j : ℤ, (j : ℝ) / 3 ^ K ∈ preCantorSet K ↔ j ∈ cantorTrace K := by
    intro j
    rw [mem_preCantorSet_iff]
    simp only [cantorTrace, mem_biUnion, mem_insert, mem_singleton]
    constructor
    · rintro ⟨c, hc, h1, h2⟩
      rw [div_le_div_iff_of_pos_right h3] at h1 h2
      have h1' : (c : ℤ) ≤ j := by exact_mod_cast h1
      have h2' : j ≤ (c : ℤ) + 1 := by exact_mod_cast h2
      exact ⟨c, hc, by omega⟩
    · rintro ⟨c, hc, h | h⟩ <;> subst h <;> refine ⟨c, hc, ?_, ?_⟩ <;>
        (rw [div_le_div_iff_of_pos_right h3]; push_cast; linarith)
  have ends : ∀ j ∈ cantorTrace K, (j : ℝ) / 3 ^ K ∈ cantorEnds K := by
    intro j hj
    simp only [cantorTrace, mem_biUnion, mem_insert, mem_singleton] at hj
    obtain ⟨c, hc, h⟩ := hj
    rw [mem_cantorEnds_iff]
    refine ⟨c, hc, ?_⟩
    rcases h with rfl | rfl
    · left; push_cast; rfl
    · right; push_cast; rfl
  refine ⟨?_, ?_, cantorTrace_card K, ?_⟩
  · ext j
    simp only [Set.mem_ofPred_eq, mem_coe, hx]
    constructor
    · intro h; exact (pre_iff j).1 (Set.mem_iInter.1 h K)
    · intro h; exact cantorEnds_subset_cantorSet K (ends j h)
  · ext j; simp only [Set.mem_ofPred_eq, mem_coe, hx]; exact pre_iff j
  · unfold mu; rw [cantorTrace_card]; push_cast
    rw [div_pow]; field_simp; ring

/-- **Granular dimension of the Cantor set** (`prop:measure-cantor` (iv)), finite depth:
`log #(C ∩ 𝕃) / log(1/(2ε)) = ((K+1)/K) · log 2 / log 3` on the lattice `2ε = 3^{-K}`. -/
theorem cantor_dim_trace (K : ℕ) (hK : 0 < K) :
    Real.log ((cantorTrace K).card) / Real.log (1 / (2 * (1 / (2 * 3 ^ K) : ℝ))) =
      ((K + 1 : ℝ) / K) * (Real.log 2 / Real.log 3) := by
  rw [cantorTrace_card]
  have e : (1 / (2 * (1 / (2 * 3 ^ K) : ℝ))) = 3 ^ K := by field_simp
  rw [e]; push_cast
  rw [Real.log_pow, Real.log_pow]
  have : (K : ℝ) ≠ 0 := by exact_mod_cast hK.ne'
  have h3 : Real.log 3 ≠ 0 := by
    have := Real.log_pos (by norm_num : (1 : ℝ) < 3); linarith
  field_simp
  push_cast; ring

/-- **Shadow form** (`prop:measure-cantor` (iii), (iv)) at an unlimited triadic depth
`K = [K_m]`: `μ(C ∩ 𝕃) = 2(2/3)^K` is a positive infinitesimal, and the standard part
of `log #(C ∩ 𝕃) / log(1/(2ε))` is `log 2 / log 3`. -/
theorem cantor_shadow (Ks : ℕ → ℕ) (hK : IsUnlimited (Ks : Ult ℕ)) :
    0 < Hyperreal.ofSeq (fun m => 2 * (2 / 3 : ℝ) ^ (Ks m)) ∧
    IsInfinitesimal (Hyperreal.ofSeq (fun m => 2 * (2 / 3 : ℝ) ^ (Ks m))) ∧
    ArchimedeanClass.stdPart (Hyperreal.ofSeq (fun m =>
      Real.log ((cantorTrace (Ks m)).card) / Real.log (1 / (2 * (1 / (2 * 3 ^ (Ks m)) : ℝ)))))
      = Real.log 2 / Real.log 3 := by
  have hT : Tendsto Ks (hyperfilter ℕ : Filter ℕ) atTop :=
    tendsto_atTop.2 fun q => by filter_upwards [Germ.coe_lt.1 (hK q)] with m hm using hm.le
  refine ⟨Germ.coe_pos.2 (Eventually.of_forall fun m => by positivity), ?_, ?_⟩
  · rw [isInfinitesimal_ofSeq_iff]
    intro t ht
    have h := ((tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 2 / 3)
      (by norm_num)).comp hT).const_mul 2
    rw [mul_zero] at h
    filter_upwards [(Metric.tendsto_nhds.1 h) t ht] with m hm
    rw [Real.dist_eq, sub_zero] at hm
    exact hm
  · apply Hyperreal.stdPart_of_tendsto
    rw [Hyperreal.tendsto_ofSeq]
    have hlim : Tendsto (fun K : ℕ => ((K + 1 : ℝ) / K) * (Real.log 2 / Real.log 3)) atTop
        (𝓝 (Real.log 2 / Real.log 3)) := by
      have h1 : Tendsto (fun K : ℕ => ((K + 1 : ℝ) / K)) atTop (𝓝 1) := by
        have := (tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ)).const_add 1
        rw [add_zero] at this
        refine this.congr' ?_
        filter_upwards [eventually_gt_atTop 0] with K hK
        have : (K : ℝ) ≠ 0 := by exact_mod_cast hK.ne'
        field_simp
      simpa using h1.mul_const (Real.log 2 / Real.log 3)
    refine (hlim.comp hT).congr' ?_
    filter_upwards [Germ.coe_lt.1 (hK 0)] with m hm
    exact (cantor_dim_trace (Ks m) hm).symm

end QE.Measure

namespace QE.Integral

/-! ### `∫_{(0,1)} dx/x`: the second-order expansion (`thm:integral-harmonic`) -/

/-- `log(1+x) ≥ x - x²/2 + x³/3 - x⁴/4` for `x ≥ 0`. -/
theorem log_one_add_ge_quartic {x : ℝ} (hx : 0 ≤ x) :
    x - x ^ 2 / 2 + x ^ 3 / 3 - x ^ 4 / 4 ≤ Real.log (1 + x) := by
  let F : ℝ → ℝ := fun y => Real.log (1 + y) - (y - y ^ 2 / 2 + y ^ 3 / 3 - y ^ 4 / 4)
  have hD : ∀ y, 0 ≤ y → HasDerivAt F (y ^ 4 / (1 + y)) y := by
    intro y hy
    have h1 : (1 + y) ≠ 0 := by positivity
    have hl : HasDerivAt (fun y => Real.log (1 + y)) (1 / (1 + y)) y := by
      have := ((hasDerivAt_id y).const_add 1).log h1
      simpa using this
    have hp : HasDerivAt (fun y : ℝ => y - y ^ 2 / 2 + y ^ 3 / 3 - y ^ 4 / 4)
        (1 - y + y ^ 2 - y ^ 3) y := by
      have := ((((hasDerivAt_id y).sub ((hasDerivAt_pow 2 y).div_const 2)).add
        ((hasDerivAt_pow 3 y).div_const 3)).sub ((hasDerivAt_pow 4 y).div_const 4))
      convert this using 1
      · funext z; simp only [Pi.sub_apply, Pi.add_apply, id]
      · norm_num
    convert hl.sub hp using 1
    field_simp; ring
  have hmono : MonotoneOn F (Set.Ici 0) := by
    refine monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ici 0)
      (fun y hy => (hD y hy).continuousAt.continuousWithinAt)
      (fun y hy => (hD y (interior_subset hy)).hasDerivWithinAt) ?_
    intro y hy
    rw [interior_Ici, Set.mem_Ioi] at hy
    positivity
  have := hmono (Set.mem_Ici.2 le_rfl) (Set.mem_Ici.2 hx) hx
  simp only [F, add_zero, Real.log_one] at this
  norm_num at this
  linarith

/-- `log(1+x) ≤ x - x²/2 + x³/3` for `x ≥ 0`. -/
theorem log_one_add_le_cubic {x : ℝ} (hx : 0 ≤ x) :
    Real.log (1 + x) ≤ x - x ^ 2 / 2 + x ^ 3 / 3 := by
  let F : ℝ → ℝ := fun y => (y - y ^ 2 / 2 + y ^ 3 / 3) - Real.log (1 + y)
  have hD : ∀ y, 0 ≤ y → HasDerivAt F (y ^ 3 / (1 + y)) y := by
    intro y hy
    have h1 : (1 + y) ≠ 0 := by positivity
    have hl : HasDerivAt (fun y => Real.log (1 + y)) (1 / (1 + y)) y := by
      have := ((hasDerivAt_id y).const_add 1).log h1
      simpa using this
    have hp : HasDerivAt (fun y : ℝ => y - y ^ 2 / 2 + y ^ 3 / 3) (1 - y + y ^ 2) y := by
      have := (((hasDerivAt_id y).sub ((hasDerivAt_pow 2 y).div_const 2)).add
        ((hasDerivAt_pow 3 y).div_const 3))
      convert this using 1
      · funext z; simp only [Pi.sub_apply, Pi.add_apply, id]
      · norm_num
    convert hp.sub hl using 1
    field_simp; ring
  have hmono : MonotoneOn F (Set.Ici 0) := by
    refine monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ici 0)
      (fun y hy => (hD y hy).continuousAt.continuousWithinAt)
      (fun y hy => (hD y (interior_subset hy)).hasDerivWithinAt) ?_
    intro y hy
    rw [interior_Ici, Set.mem_Ioi] at hy
    positivity
  have := hmono (Set.mem_Ici.2 le_rfl) (Set.mem_Ici.2 hx) hx
  simp only [F, add_zero, Real.log_one] at this
  norm_num at this
  linarith

/-- The corrected harmonic sequence `d_n = H_n - ln n - 1/(2n)`. -/
noncomputable def harmD (n : ℕ) : ℝ := (harmonic n : ℝ) - Real.log n - 1 / (2 * n)

/-- One step of `d`: `d_{n+1} - d_n = x/2 + x/(2(1+x)) - ln(1+x)` with `x = 1/n`. -/
theorem harmD_step (n : ℕ) (hn : 1 ≤ n) :
    harmD (n + 1) - harmD n =
      (1 / (n : ℝ)) / 2 + (1 / (n : ℝ)) / (2 * (1 + 1 / (n : ℝ))) - Real.log (1 + 1 / (n : ℝ)) := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  unfold harmD
  rw [harmonic_succ]; push_cast
  have e : (1 + 1 / (n : ℝ)) = ((n : ℝ) + 1) / n := by field_simp
  rw [e, Real.log_div (by positivity) hn'.ne']
  field_simp
  ring

theorem harmD_step_nonneg (n : ℕ) (hn : 1 ≤ n) : 0 ≤ harmD (n + 1) - harmD n := by
  rw [harmD_step n hn]
  set x : ℝ := 1 / (n : ℝ) with hxdef
  have hx0 : 0 < x := by positivity
  have hx1 : x ≤ 1 := by
    rw [hxdef, div_le_one (by exact_mod_cast hn)]; exact_mod_cast hn
  rcases eq_or_lt_of_le hx1 with h1 | h1
  · rw [h1]; norm_num
    have := Real.log_two_lt_d9; norm_num at this ⊢; linarith
  · rcases le_or_gt x (1 / 2) with h2 | h2
    · have hl := log_one_add_le_cubic hx0.le
      have : x ^ 3 / 3 ≤ x ^ 3 / (2 * (1 + x)) := by
        rw [div_le_div_iff₀ (by norm_num) (by positivity)]; nlinarith [pow_pos hx0 3]
      have e : x / 2 + x / (2 * (1 + x)) = x - x ^ 2 / 2 + x ^ 3 / (2 * (1 + x)) := by
        field_simp; ring
      linarith
    · -- `1/2 < x < 1` forces `n = 1`, impossible
      exfalso
      have hn2 : 2 ≤ n := by
        by_contra h; have : n = 1 := by omega
        subst this; norm_num at h1
      have : x ≤ 1 / 2 := by
        rw [hxdef, div_le_div_iff₀ (by positivity) (by norm_num)]
        have : (2 : ℝ) ≤ n := by exact_mod_cast hn2
        linarith
      linarith

theorem harmD_step_le (n : ℕ) (hn : 1 ≤ n) :
    harmD (n + 1) - harmD n ≤ 1 / (4 * (n : ℝ) ^ 2) - 1 / (4 * ((n : ℝ) + 1) ^ 2) := by
  rw [harmD_step n hn]
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  set x : ℝ := 1 / (n : ℝ) with hxdef
  have hx0 : 0 < x := by positivity
  have hx1 : x ≤ 1 := by rw [hxdef, div_le_one (by linarith)]; exact hn'
  have hl := log_one_add_ge_quartic hx0.le
  -- `x/2 + x/(2(1+x)) - ln(1+x) ≤ x³/6`
  have h6 : x / 2 + x / (2 * (1 + x)) - Real.log (1 + x) ≤ x ^ 3 / 6 := by
    have e : x / 2 + x / (2 * (1 + x)) = x - x ^ 2 / 2 + x ^ 3 / (2 * (1 + x)) := by
      field_simp; ring
    have h : x ^ 3 / (2 * (1 + x)) ≤ x ^ 3 / 2 - x ^ 4 / 4 := by
      rw [div_le_iff₀ (by positivity)]
      have : 0 ≤ x ^ 3 * (x - x ^ 2) := mul_nonneg (by positivity) (by nlinarith)
      nlinarith
    linarith
  refine h6.trans ?_
  have hn0 : (0 : ℝ) < n := by linarith
  have hx3 : x ^ 3 / 6 = 1 / (6 * (n : ℝ) ^ 3) := by rw [hxdef]; field_simp
  rw [hx3, show (1 : ℝ) / (4 * (n : ℝ) ^ 2) - 1 / (4 * ((n : ℝ) + 1) ^ 2) =
    (2 * n + 1) / (4 * (n : ℝ) ^ 2 * ((n : ℝ) + 1) ^ 2) by field_simp; ring]
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  have h8 : (2 : ℝ) ≤ 8 * (n : ℝ) ^ 2 - 2 * n - 4 := by nlinarith
  have : 0 ≤ (n : ℝ) ^ 2 * (8 * (n : ℝ) ^ 2 - 2 * n - 4) := by positivity
  nlinarith

theorem tendsto_harmD : Tendsto harmD atTop (𝓝 Real.eulerMascheroniConstant) := by
  have h := Real.tendsto_harmonic_sub_log.sub
    ((tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ)).div_const 2)
  rw [zero_div, sub_zero] at h
  refine h.congr fun n => ?_
  unfold harmD; rw [div_div]; ring

/-- `0 ≤ γ - d_n ≤ 1/(4n²)` for `n ≥ 1`. -/
theorem harmD_bounds (n : ℕ) (hn : 1 ≤ n) :
    harmD n ≤ Real.eulerMascheroniConstant ∧
      Real.eulerMascheroniConstant ≤ harmD n + 1 / (4 * (n : ℝ) ^ 2) := by
  have hu : Monotone fun k : ℕ => harmD (k + 1) := monotone_nat_of_le_succ fun k => by
    have := harmD_step_nonneg (k + 1) (by omega)
    linarith
  have hv : Antitone fun k : ℕ => harmD (k + 1) + 1 / (4 * ((k + 1 : ℕ) : ℝ) ^ 2) :=
    antitone_nat_of_succ_le fun k => by
      have := harmD_step_le (k + 1) (by omega)
      push_cast at this ⊢
      linarith
  have hT1 : Tendsto (fun k : ℕ => harmD (k + 1)) atTop (𝓝 Real.eulerMascheroniConstant) :=
    tendsto_harmD.comp (tendsto_add_atTop_nat 1)
  have hg : Tendsto (fun k : ℕ => 1 / (4 * ((k + 1 : ℕ) : ℝ) ^ 2)) atTop (𝓝 0) := by
    have : Tendsto (fun k : ℕ => (4 * ((k + 1 : ℕ) : ℝ) ^ 2)) atTop atTop := by
      refine Tendsto.const_mul_atTop (by norm_num) ?_
      exact (tendsto_pow_atTop (by norm_num)).comp
        (tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1))
    refine this.inv_tendsto_atTop.congr fun k => ?_
    simp only [Pi.inv_apply, one_div]
  have hT2 := hT1.add hg
  rw [add_zero] at hT2
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  refine ⟨hu.ge_of_tendsto hT1 k, ?_⟩
  have := hv.le_of_tendsto hT2 k
  simpa using this

/-- **Second-order expansion of `∫_{(0,1)} dx/x`** (`thm:integral-harmonic`): with
`2ε = 1/n`, the granular integral `H_{n-1}` satisfies
`ln(1/(2ε)) + γ - ε - ε² ≤ ∫_{(0,1)} dx/x ≤ ln(1/(2ε)) + γ - ε`,
i.e. `∫_{(0,1)} dx/x = ln(1/(2ε)) + γ - ε + O(ε²)` with `|O(ε²)| ≤ ε²`, for every
`n ≥ 1`. -/
theorem gint_inv_expansion (n : ℕ) (hn : 1 ≤ n) :
    let ε : ℝ := 1 / (2 * n)
    Real.log (1 / (2 * ε)) + Real.eulerMascheroniConstant - ε - ε ^ 2 ≤
        ∑ k ∈ Ico 1 n, (2 * ε * k)⁻¹ * (2 * ε) ∧
      ∑ k ∈ Ico 1 n, (2 * ε * k)⁻¹ * (2 * ε) ≤
        Real.log (1 / (2 * ε)) + Real.eulerMascheroniConstant - ε := by
  intro ε
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  rw [gint_inv_harmonic ε (by positivity) n]
  have e1 : (1 / (2 * ε)) = (n : ℝ) := by simp only [ε]; field_simp
  have e2 : ((harmonic (n - 1) : ℚ) : ℝ) = harmD n + Real.log n - 1 / (2 * n) := by
    have : harmonic n = harmonic (n - 1) + (n : ℚ)⁻¹ := by
      conv_lhs => rw [show n = (n - 1) + 1 by omega]
      rw [harmonic_succ, Nat.sub_add_cancel hn]
    unfold harmD; rw [this]; push_cast; field_simp; ring
  rw [e1, e2]
  obtain ⟨h1, h2⟩ := harmD_bounds n hn
  have e3 : ε ^ 2 = 1 / (4 * (n : ℝ) ^ 2) := by simp only [ε]; field_simp; ring
  have e4 : ε = 1 / (2 * n) := rfl
  rw [e3, e4]
  constructor <;> linarith

end QE.Integral

namespace QE.Integral

open QE.NSA

/-- **`thm:integral-harmonic` at an infinitesimal granule**: for an unlimited
hypernatural `n = [n_m]` and `2ε = 1/n`, the error of
`∫_{(0,1)} dx/x ≈ ln(1/(2ε)) + γ - ε` lies in `[-ε², 0]`, and
`st(∫_{(0,1)} dx/x - ln(1/(2ε))) = γ`. -/
theorem gint_inv_expansion_hyper (ns : ℕ → ℕ) (hn : IsUnlimited (ns : Ult ℕ)) :
    -(Hyperreal.ofSeq fun m => (1 / (2 * (ns m : ℝ))) ^ 2) ≤
        Hyperreal.ofSeq (fun m => ((harmonic (ns m - 1) : ℚ) : ℝ) -
          (Real.log (ns m) + Real.eulerMascheroniConstant - 1 / (2 * (ns m : ℝ)))) ∧
      Hyperreal.ofSeq (fun m => ((harmonic (ns m - 1) : ℚ) : ℝ) -
          (Real.log (ns m) + Real.eulerMascheroniConstant - 1 / (2 * (ns m : ℝ)))) ≤ 0 ∧
      ArchimedeanClass.stdPart (Hyperreal.ofSeq fun m =>
        ((harmonic (ns m - 1) : ℚ) : ℝ) - Real.log (ns m)) = Real.eulerMascheroniConstant := by
  have hge : ∀ q : ℕ, ∀ᶠ m in (hyperfilter ℕ : Filter ℕ), q ≤ ns m := fun q => by
    filter_upwards [Germ.coe_lt.1 (hn q)] with m hm using hm.le
  have hb : ∀ᶠ m in (hyperfilter ℕ : Filter ℕ),
      -((1 / (2 * (ns m : ℝ))) ^ 2) ≤ ((harmonic (ns m - 1) : ℚ) : ℝ) -
          (Real.log (ns m) + Real.eulerMascheroniConstant - 1 / (2 * (ns m : ℝ))) ∧
      ((harmonic (ns m - 1) : ℚ) : ℝ) -
          (Real.log (ns m) + Real.eulerMascheroniConstant - 1 / (2 * (ns m : ℝ))) ≤ 0 := by
    filter_upwards [hge 1] with m hm
    obtain ⟨h1, h2⟩ := gint_inv_expansion (ns m) hm
    have hn0 : (0 : ℝ) < ns m := by exact_mod_cast hm
    rw [gint_inv_harmonic _ (by positivity)] at h1 h2
    have e : Real.log (1 / (2 * (1 / (2 * (ns m : ℝ))))) = Real.log (ns m) := by
      congr 1; field_simp
    rw [e] at h1 h2
    constructor <;> linarith
  refine ⟨?_, ?_, ?_⟩
  · exact Hyperreal.ofSeq_le_ofSeq.2 (by filter_upwards [hb] with m hm using hm.1)
  · exact Hyperreal.ofSeq_le_ofSeq.2 (by filter_upwards [hb] with m hm using hm.2)
  · apply Hyperreal.stdPart_of_tendsto
    rw [Hyperreal.tendsto_ofSeq]
    have hT : Tendsto ns (hyperfilter ℕ : Filter ℕ) atTop := tendsto_atTop.2 hge
    have h := gint_inv_sub_log.comp hT
    refine h.congr' ?_
    filter_upwards [hge 1] with m hm
    simp only [Function.comp]
    have h0 : (0 : ℝ) < ns m := by exact_mod_cast hm
    rw [gint_inv_harmonic _ (by positivity)]

end QE.Integral

namespace QE.Measure

/-- **`prop:measure-cantor` (ii) for the classical approximants**: on the triadic lattice
`2ε = 3^{-K}` and for `n ≤ K`, the lattice trace of the stage-`n` approximant `C_n` is the
union of the closed runs `[c s, c s + s]`, `c ∈ 𝒞_n`, `s = 3^{K-n}`; hence
`μ(C_n ∩ 𝕃) = 2ⁿ(3^{-n} + 2ε) = (2/3)ⁿ + 2ⁿ·2ε`. -/
theorem cantor_stage_trace (K n : ℕ) (hn : n ≤ K) :
    {j : ℤ | 2 * (1 / (2 * 3 ^ K) : ℝ) * j ∈ preCantorSet n} =
      ↑((cantorIdx n).biUnion fun c =>
        Icc ((c * 3 ^ (K - n) : ℕ) : ℤ) ((c * 3 ^ (K - n) + 3 ^ (K - n) : ℕ) : ℤ)) ∧
    mu (1 / (2 * 3 ^ K) : ℝ) ((cantorIdx n).biUnion fun c =>
        Icc ((c * 3 ^ (K - n) : ℕ) : ℤ) ((c * 3 ^ (K - n) + 3 ^ (K - n) : ℕ) : ℤ)) =
      (2 / 3 : ℝ) ^ n + 2 ^ n * (2 * (1 / (2 * 3 ^ K))) := by
  set s : ℕ := 3 ^ (K - n) with hsdef
  have hK : (3 : ℝ) ^ K = 3 ^ n * s := by
    rw [hsdef]; push_cast; rw [← pow_add]; congr 1; omega
  have h3n : (0 : ℝ) < 3 ^ n := by positivity
  have hs : (0 : ℝ) < s := by rw [hsdef]; positivity
  refine ⟨?_, ?_⟩
  · ext j
    simp only [Set.mem_ofPred_eq, coe_biUnion, mem_coe, Set.mem_iUnion, mem_Icc, exists_prop]
    have hx : 2 * (1 / (2 * 3 ^ K) : ℝ) * j = (j : ℝ) / (3 ^ n * s) := by
      rw [← hK]; field_simp
    rw [hx, mem_preCantorSet_iff]
    refine exists_congr fun c => and_congr_right fun _ => ?_
    rw [div_le_div_iff₀ h3n (by positivity), div_le_div_iff₀ (by positivity) h3n]
    constructor
    · rintro ⟨h1, h2⟩
      have h1' : (c : ℝ) * s ≤ j := by nlinarith
      have h2' : (j : ℝ) ≤ (c + 1) * s := by nlinarith
      constructor
      · exact_mod_cast (by push_cast; exact h1' : (((c * s : ℕ) : ℤ) : ℝ) ≤ j)
      · exact_mod_cast (by push_cast; linarith : (j : ℝ) ≤ (((c * s + s : ℕ) : ℤ) : ℝ))
    · rintro ⟨h1, h2⟩
      have h1' : (c : ℝ) * s ≤ j := by exact_mod_cast h1
      have h2' : (j : ℝ) ≤ c * s + s := by exact_mod_cast h2
      constructor <;> nlinarith
  · rw [mu_cantor _ n s (by positivity)]
    have : (2 : ℝ) * (1 / (2 * 3 ^ K)) * s = 1 / 3 ^ n := by
      rw [hK]; field_simp
    rw [show (2 : ℝ) ^ n * (2 * (1 / (2 * 3 ^ K)) * s + 2 * (1 / (2 * 3 ^ K))) =
      2 ^ n * (2 * (1 / (2 * 3 ^ K)) * s) + 2 ^ n * (2 * (1 / (2 * 3 ^ K))) by ring, this,
      div_pow]
    field_simp

/-- Shadow comparison in `thm:countable-positive` (v): the Farey measure is infinitesimal
and its standard part is Lebesgue's value `λ(ℚ ∩ [0,1]) = 0`. -/
theorem farey_shadow_leb (Ms : ℕ → ℕ) (hM : QE.NSA.IsUnlimited (Ms : QE.NSA.Ult ℕ)) :
    ArchimedeanClass.stdPart (Hyperreal.ofSeq fun m =>
        2 * (1 / (2 * ((Ms m).factorial : ℝ))) * ((fareyFin (Ms m)).card : ℝ)) =
      (MeasureTheory.volume (Set.range ((↑) : ℚ → ℝ) ∩ Set.Icc 0 1)).toReal := by
  have h0 : MeasureTheory.volume (Set.range ((↑) : ℚ → ℝ) ∩ Set.Icc 0 1) = 0 :=
    ((Set.countable_range _).mono Set.inter_subset_left).measure_zero _
  rw [h0, ENNReal.toReal_zero]
  exact QE.NSA.stdPart_of_infinitesimal (farey_hyper Ms hM).2.2.2.2

end QE.Measure
