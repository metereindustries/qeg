-- SPDX-License-Identifier: MIT
-- Copyright 2026 Metere Industries, Inc. Author: Alfredo Metere.
-- Quasi-Euclidean Granular Geometry. Any derivative work must carry this notice:
--   This work is derivative of the Quasi-Euclidean Granular Geometry book
--   authored by Alfredo Metere. Copyright 2026 Metere Industries, Inc.
--   All rights reserved
-- See LICENSE.md and NOTICE.

import QuasiEuclidean.Ch11_Prob
import QuasiEuclidean.Ch02_Hyper

/-!
# Central limit theorem with error term for the fair-coin walk (`thm:prob-clt`)

The book's theorem is the Berry–Esseen bound specialised to fair signs:
`sup_x |P(S_n ≤ x√n) - Φ(x)| ≤ C/√n`.  Mathlib has no Berry–Esseen theorem; for
the symmetric Bernoulli walk we prove the bound directly, with `C = 2000`:

1. *Exact law* (granular, Lebesgue-free): `∑_ω f(S_n ω) = ∑_j C(n,j) f(2j-n)`,
   and the exact moments `E S_n^2 = n`, `E S_n^4 = 3n^2 - 2n`.
2. *Local de Moivre–Laplace*: Stirling with Robbins' error
   (`0 ≤ log s_m - log √π ≤ 1/(12m)`) and a third-order log expansion give
   `|q_j - p_j| ≤ 55 p_j (1/n + k²/n² + 3k⁴/n³)` in the range `k⁴ ≤ n³`
   (`k = 2j-n`, `p_j = C(n,j)/2^n`, `q_j = 2hφ(kh)`, `h = 1/√n`); hence
   `∑_j |p_j - q_j| ≤ 640/√n`.
3. *Cells*: the midpoint rule `|∫_{c-h}^{c+h} φ - 2hφ(c)| ≤ 2h³` on the `n+1`
   cells tiling `[-(n+1)h, (n+1)h]`; the Gaussian tails are controlled by the
   total masses `∑ p_j = 1 = ∫ φ`.
4. *Assembly*, then the hyperfinite reading via `Hyperreal.ofSeq`.

`Φ` is a Lebesgue integral, so the final theorems are shadow results
(`\leanshadowref`).  (Mathlib's identification of the Stirling constant `√π`
goes through the Wallis integrals, so `local_est` is not Lebesgue-free either.)
-/

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace QE.Prob.BE

open Finset Real

/-! ## Part 1 (granular, Lebesgue-free): the exact law of `S_n` -/

/-- The law of the walk: summing any function of `S_n` over all `2^n` sign
sequences is the binomial sum `∑_j C(n,j) f(2j - n)`. -/
theorem sum_fun_S (n : ℕ) (f : ℝ → ℝ) :
    ∑ ω : Fin n → Bool, f (S ω) = ∑ j ∈ range (n + 1), (n.choose j : ℝ) * f (2 * j - n) := by
  induction n generalizing f with
  | zero => simp [S]
  | succ n ih =>
    rw [sum_cons, Fintype.sum_bool]
    simp only [S_cons, sgn, ite_true]
    have h1 := ih (fun s => f (1 + s))
    have h2 := ih (fun s => f (-1 + s))
    simp only [Bool.false_eq_true, ite_false] at h1 h2 ⊢
    rw [h1, h2]
    rw [sum_range_succ' (fun j => ((n + 1).choose j : ℝ) * f (2 * j - (n + 1 : ℕ)))]
    simp only [Nat.choose_succ_succ', Nat.cast_add, add_mul, sum_add_distrib,
      Nat.choose_zero_right, Nat.cast_one, one_mul]
    have e1 : ∑ j ∈ range (n + 1), (n.choose (j + 1) : ℝ) * f (2 * ((j + 1 : ℕ) : ℝ) - (n + 1 : ℕ))
        + f (2 * ((0 : ℕ) : ℝ) - (n + 1 : ℕ))
        = ∑ j ∈ range (n + 1), (n.choose j : ℝ) * f (-1 + (2 * j - n)) := by
      have := sum_range_succ' (fun j => (n.choose j : ℝ) * f (2 * (j : ℝ) - (n + 1 : ℕ))) (n + 1)
      rw [Nat.choose_zero_right, Nat.cast_one, one_mul] at this
      rw [← this, sum_range_succ, Nat.choose_succ_self, Nat.cast_zero, zero_mul, add_zero]
      refine sum_congr rfl (fun j _ => ?_)
      congr 2; push_cast; ring
    have e2 : ∑ j ∈ range (n + 1), (n.choose j : ℝ) * f (2 * ((j + 1 : ℕ) : ℝ) - (n + 1 : ℕ))
        = ∑ j ∈ range (n + 1), (n.choose j : ℝ) * f (1 + (2 * j - n)) := by
      refine sum_congr rfl (fun j _ => ?_)
      congr 2; push_cast; ring
    push_cast at e1 e2 ⊢
    linarith [e1, e2]

theorem sum_S_cube (n : ℕ) : ∑ ω : Fin n → Bool, (S ω : ℝ) ^ 3 = 0 := by
  induction n with
  | zero => simp [S]
  | succ n ih =>
    rw [sum_cons, Fintype.sum_bool]
    simp only [S_cons, sgn, ite_true, Bool.false_eq_true, ite_false]
    rw [← sum_add_distrib]
    have e : ∀ s : ℝ, (1 + s) ^ 3 + (-1 + s) ^ 3 = 2 * s ^ 3 + 6 * s := by intro s; ring
    simp only [e, sum_add_distrib, ← mul_sum, ih, sum_S (K := ℝ)]
    ring

theorem sum_S_four (n : ℕ) :
    ∑ ω : Fin n → Bool, (S ω : ℝ) ^ 4 = (3 * (n : ℝ) ^ 2 - 2 * n) * 2 ^ n := by
  induction n with
  | zero => simp [S]
  | succ n ih =>
    rw [sum_cons, Fintype.sum_bool]
    simp only [S_cons, sgn, ite_true, Bool.false_eq_true, ite_false]
    rw [← sum_add_distrib]
    have e : ∀ s : ℝ, (1 + s) ^ 4 + (-1 + s) ^ 4 = 2 * s ^ 4 + 12 * s ^ 2 + 2 := by
      intro s; ring
    simp only [e, sum_add_distrib, ← mul_sum, ih, sum_S_sq (K := ℝ), sum_const, card_univ,
      Fintype.card_fun, Fintype.card_bool, Fintype.card_fin, nsmul_eq_mul]
    push_cast; ring

/-- Binomial form of the moments. -/
theorem binom_moment (n r : ℕ) :
    ∑ j ∈ range (n + 1), (n.choose j : ℝ) * (2 * j - n) ^ r
      = ∑ ω : Fin n → Bool, (S ω : ℝ) ^ r :=
  (sum_fun_S n (fun s => s ^ r)).symm


/-- A down-closed predicate cuts an initial segment out of `range N`. -/
theorem filter_range_downset (P : ℕ → Prop) [DecidablePred P]
    (hP : ∀ i j, i ≤ j → P j → P i) (N : ℕ) :
    ∃ m ≤ N, (range N).filter P = range m := by
  induction N with
  | zero => exact ⟨0, le_rfl, by simp⟩
  | succ N ih =>
    by_cases hN : P N
    · refine ⟨N + 1, le_rfl, ?_⟩
      ext i
      simp only [mem_filter, mem_range]
      constructor
      · exact fun h => h.1
      · exact fun h => ⟨h, hP i N (by omega) hN⟩
    · obtain ⟨m, hm, e⟩ := ih
      refine ⟨m, by omega, ?_⟩
      rw [range_add_one, filter_insert]; simp only [hN, ↓reduceIte, e]

/-! ## Part 2: Stirling's formula with an explicit error -/

open Stirling in
/-- `0 ≤ log s_m - log √π ≤ 1/(12 m)` for the Stirling sequence `s_m = m!/(√(2m)(m/e)^m)`. -/
theorem log_stirling_err (m : ℕ) (hm : 1 ≤ m) :
    0 ≤ log (stirlingSeq m) - log √π ∧ log (stirlingSeq m) - log √π ≤ 1 / (12 * m) := by
  have hm0 : m ≠ 0 := by omega
  constructor
  · have := sqrt_pi_le_stirlingSeq hm0
    have : log √π ≤ log (stirlingSeq m) := log_le_log (by positivity) this
    linarith
  · have tele : ∀ N : ℕ, log (stirlingSeq m) - log (stirlingSeq (m + N))
        ≤ 1 / (12 * m) - 1 / (12 * ((m + N : ℕ) : ℝ)) := by
      intro N
      induction N with
      | zero => simp
      | succ N ih =>
        have h := log_stirlingSeq_sdiff_le (m + N)
        have hmN : (0 : ℝ) < ((m + N : ℕ) : ℝ) := by
          have : 0 < m + N := by omega
          exact_mod_cast this
        have e : (1 : ℝ) / (12 * ((m + N : ℕ) : ℝ) * (((m + N : ℕ) : ℝ) + 1))
            = 1 / (12 * ((m + N : ℕ) : ℝ)) - 1 / (12 * ((m + N + 1 : ℕ) : ℝ)) := by
          push_cast; field_simp; ring
        rw [e] at h
        rw [show m + (N + 1) = m + N + 1 from rfl]
        linarith
    have hlim : Filter.Tendsto (fun N : ℕ => log (stirlingSeq m) - log (stirlingSeq (m + N)))
        Filter.atTop (nhds (log (stirlingSeq m) - log √π)) := by
      refine tendsto_const_nhds.sub ?_
      have h1 : Filter.Tendsto (fun N : ℕ => stirlingSeq (m + N)) Filter.atTop (nhds √π) := by
        have := tendsto_stirlingSeq_sqrt_pi.comp (Filter.tendsto_add_atTop_nat m)
        refine this.congr (fun N => ?_)
        simp [Function.comp_def, add_comm]
      exact h1.log (by positivity)
    refine le_of_tendsto' hlim (fun N => ?_)
    have := tele N
    have : (0 : ℝ) ≤ 1 / (12 * ((m + N : ℕ) : ℝ)) := by positivity
    linarith

open Stirling in
/-- `log m! = log s_m + log(2m)/2 + m (log m - 1)` for `m ≥ 1`. -/
theorem log_factorial_eq (m : ℕ) (hm : 1 ≤ m) :
    log (m.factorial : ℝ) = log (stirlingSeq m) + (log 2 + log m) / 2 + m * (log m - 1) := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  rw [log_stirlingSeq_formula, log_mul (by norm_num) hm0.ne', log_div hm0.ne' (exp_pos 1).ne',
    log_exp]
  ring

/-- Logarithm series with third-order remainder. -/
theorem log_one_sub_expand (x : ℝ) (hx : |x| ≤ 1 / 2) :
    |log (1 - x) + x + x ^ 2 / 2 + x ^ 3 / 3| ≤ 2 * x ^ 4 := by
  have h := abs_log_sub_add_sum_range_le (x := x) (by linarith) 3
  simp only [sum_range_succ, sum_range_zero] at h
  norm_num at h
  have e4 : |x| ^ 4 = x ^ 4 := by rw [pow_abs]; exact abs_of_nonneg (by positivity)
  rw [e4] at h
  have hpos : 0 < 1 - |x| := by linarith
  have : x ^ 4 / (1 - |x|) ≤ 2 * x ^ 4 := by
    rw [div_le_iff₀ hpos]; nlinarith [pow_two_nonneg (x ^ 2), abs_nonneg x]
  calc _ = |x + x ^ 2 / 2 + x ^ 3 / 3 + log (1 - x)| := by ring_nf
    _ ≤ _ := h.trans this

theorem abs_log_one_sub_le (u : ℝ) (hu0 : 0 ≤ u) (hu : u ≤ 1 / 2) : |log (1 - u)| ≤ 2 * u := by
  have h := abs_log_sub_add_sum_range_le (x := u) (by rw [abs_of_nonneg hu0]; linarith) 0
  simp only [sum_range_zero, zero_add, pow_one, abs_of_nonneg hu0] at h
  have : u / (1 - u) ≤ 2 * u := by
    rw [div_le_iff₀ (by linarith)]; nlinarith
  exact h.trans this

/-- The entropy expansion: with `a = n(1+t)/2`, `b = n(1-t)/2`,
`|a log(1+t) + b log(1-t) - n t²/2| ≤ 3 n t⁴` for `|t| ≤ 1/2`. -/
theorem entropy_expand (n t : ℝ) (hn : 0 ≤ n) (ht : |t| ≤ 1 / 2) :
    |n * (1 + t) / 2 * log (1 + t) + n * (1 - t) / 2 * log (1 - t) - n * t ^ 2 / 2|
      ≤ 3 * n * t ^ 4 := by
  have h1 := log_one_sub_expand (-t) (by rwa [abs_neg])
  have h2 := log_one_sub_expand t ht
  simp only [sub_neg_eq_add] at h1
  set E1 := log (1 + t) + -t + (-t) ^ 2 / 2 + (-t) ^ 3 / 3
  set E2 := log (1 - t) + t + t ^ 2 / 2 + t ^ 3 / 3
  have ht1 : 0 ≤ 1 + t := by linarith [neg_abs_le t]
  have ht2 : 0 ≤ 1 - t := by linarith [le_abs_self t]
  have ha : 0 ≤ n * (1 + t) / 2 := by positivity
  have hb : 0 ≤ n * (1 - t) / 2 := by positivity
  have e : n * (1 + t) / 2 * log (1 + t) + n * (1 - t) / 2 * log (1 - t) - n * t ^ 2 / 2
      = n * t ^ 4 / 3 + n * (1 + t) / 2 * E1 + n * (1 - t) / 2 * E2 := by
    simp only [E1, E2]; ring
  rw [e]
  have h4 : (-t) ^ 4 = t ^ 4 := by ring
  rw [h4] at h1
  calc _ ≤ |n * t ^ 4 / 3| + |n * (1 + t) / 2 * E1| + |n * (1 - t) / 2 * E2| :=
        abs_add_three _ _ _
    _ = n * t ^ 4 / 3 + n * (1 + t) / 2 * |E1| + n * (1 - t) / 2 * |E2| := by
        rw [abs_of_nonneg (by positivity), abs_mul, abs_mul, abs_of_nonneg ha, abs_of_nonneg hb]
    _ ≤ n * t ^ 4 / 3 + n * (1 + t) / 2 * (2 * t ^ 4) + n * (1 - t) / 2 * (2 * t ^ 4) := by
        gcongr
    _ = n * t ^ 4 * (7 / 3) := by ring
    _ ≤ 3 * n * t ^ 4 := by nlinarith [pow_two_nonneg (t ^ 2)]

theorem abs_exp_sub_one_le' (D : ℝ) : |exp D - 1| ≤ |D| * exp |D| := by
  rcases le_total 0 D with h | h
  · rw [abs_of_nonneg h, abs_of_nonneg (by linarith [add_one_le_exp D])]
    have := add_one_le_exp (-D)
    rw [exp_neg] at this
    have hp := exp_pos D
    have h2 := mul_le_mul_of_nonneg_left this hp.le
    rw [mul_inv_cancel₀ hp.ne'] at h2
    nlinarith
  · rw [abs_of_nonpos h, abs_of_nonpos (by
      have := exp_le_exp.2 h; rw [exp_zero] at this; linarith)]
    have := add_one_le_exp D
    have : 1 ≤ exp (-D) := one_le_exp (by linarith)
    nlinarith


/-! ## Part 3: the local de Moivre–Laplace estimate with relative error -/

/-- Binomial weight `P(S_n = 2j - n) = C(n,j) / 2^n`. -/
noncomputable def pj (n j : ℕ) : ℝ := (n.choose j : ℝ) / 2 ^ n

/-- Gaussian lattice weight `2 h φ((2j-n) h)` with `h = 1/√n`. -/
noncomputable def qj (n j : ℕ) : ℝ :=
  2 / √(2 * π * n) * exp (-((2 : ℝ) * j - n) ^ 2 / (2 * n))

theorem pj_pos (n j : ℕ) (hj : j ≤ n) : 0 < pj n j := by
  unfold pj; have := Nat.choose_pos hj; positivity

theorem pj_nonneg (n j : ℕ) : 0 ≤ pj n j := by unfold pj; positivity

theorem qj_nonneg (n j : ℕ) : 0 ≤ qj n j := by unfold qj; positivity

theorem exp_four_le : exp 4 ≤ 55 := by
  have h := exp_one_lt_d9
  have e : exp 4 = exp 1 ^ 4 := by rw [← exp_nat_mul]; norm_num
  rw [e]
  have h0 : 0 ≤ exp 1 := (exp_pos 1).le
  calc exp 1 ^ 4 ≤ (2.7182818286 : ℝ) ^ 4 := by gcongr
    _ ≤ 55 := by norm_num

/-- **Local de Moivre–Laplace with relative error.**  In the central range
`(2j-n)^4 ≤ n^3`, `n ≥ 16`, the binomial weight and the Gaussian weight agree up to
a relative error `O(1/n + k²/n² + k⁴/n³)`, `k = 2j - n`. -/
theorem local_est (n j : ℕ) (hn : 16 ≤ n) (hj : j ≤ n)
    (hc : ((2 : ℝ) * j - n) ^ 4 ≤ (n : ℝ) ^ 3) :
    |qj n j - pj n j| ≤ 55 * pj n j *
      (1 / n + ((2 : ℝ) * j - n) ^ 2 / (n : ℝ) ^ 2 + 3 * ((2 : ℝ) * j - n) ^ 4 / (n : ℝ) ^ 3) := by
  set nr : ℝ := (n : ℝ) with hnr_def
  set a : ℝ := (j : ℝ) with ha_def
  set b : ℝ := ((n - j : ℕ) : ℝ) with hb_def
  have hab : a + b = nr := by simp only [ha_def, hb_def, hnr_def]; push_cast [hj]; ring
  set k : ℝ := 2 * a - nr with hk_def
  have hnr : (16 : ℝ) ≤ nr := by rw [hnr_def]; exact_mod_cast hn
  have hnr0 : 0 < nr := by linarith
  set t : ℝ := k / nr with ht_def
  have ht4 : t ^ 4 ≤ 1 / nr := by
    rw [ht_def, div_pow, div_le_div_iff₀ (by positivity) hnr0]
    nlinarith
  have ht4' : t ^ 4 ≤ 1 / 16 := ht4.trans (by
    rw [div_le_div_iff₀ hnr0 (by norm_num)]; linarith)
  have ht2 : t ^ 2 ≤ 1 / 4 := by nlinarith [sq_nonneg (t ^ 2)]
  have ht : |t| ≤ 1 / 2 := by
    by_contra hcon; have hcon := lt_of_not_ge hcon
    nlinarith [sq_abs t, abs_nonneg t]
  have ha : a = nr * (1 + t) / 2 := by rw [ht_def, hk_def]; field_simp; ring
  have hb : b = nr * (1 - t) / 2 := by rw [ht_def, hk_def]; field_simp; linarith
  have htl : -(1 / 2) ≤ t := (abs_le.1 ht).1
  have htu : t ≤ 1 / 2 := (abs_le.1 ht).2
  have ha4 : nr / 4 ≤ a := by rw [ha]; nlinarith
  have hb4 : nr / 4 ≤ b := by rw [hb]; nlinarith
  have ha0 : 0 < a := by linarith
  have hb0 : 0 < b := by linarith
  have hj1 : 1 ≤ j := by
    have : (0 : ℝ) < j := ha0
    exact_mod_cast this
  have hnj1 : 1 ≤ n - j := by
    have : (0 : ℝ) < ((n - j : ℕ) : ℝ) := hb0
    exact_mod_cast this
  -- Stirling errors
  obtain ⟨hsn0, hsn1⟩ := log_stirling_err n (by omega)
  obtain ⟨hsa0, hsa1⟩ := log_stirling_err j hj1
  obtain ⟨hsb0, hsb1⟩ := log_stirling_err (n - j) hnj1
  set ln := log (Stirling.stirlingSeq n) - log √π
  set la := log (Stirling.stirlingSeq j) - log √π
  set lb := log (Stirling.stirlingSeq (n - j)) - log √π
  have hlogsqrt : log √π = log π / 2 := by rw [log_sqrt pi_pos.le]
  -- logarithm of the binomial weight
  have hp : log (pj n j) = log (n.factorial : ℝ) - log (j.factorial : ℝ)
      - log ((n - j).factorial : ℝ) - nr * log 2 := by
    unfold pj
    rw [Nat.cast_choose ℝ hj, log_div (by positivity) (by positivity),
      log_div (by positivity) (by positivity), log_mul (by positivity) (by positivity),
      log_pow]
    ring
  rw [log_factorial_eq n (by omega), log_factorial_eq j hj1, log_factorial_eq (n - j) hnj1]
    at hp
  have hq : log (qj n j) = log 2 - (log 2 + log π + log nr) / 2 - k ^ 2 / (2 * nr) := by
    unfold qj
    rw [log_mul (by positivity) (exp_pos _).ne', log_exp, log_div (by norm_num) (by positivity),
      log_sqrt (by positivity), log_mul (by positivity) (by positivity),
      log_mul (by norm_num) pi_pos.ne']
    simp only [hk_def, ha_def, hnr_def]
    ring
  have hL1 : log (1 + t) = log 2 + log a - log nr := by
    rw [show 1 + t = 2 * a / nr by rw [ha]; field_simp, log_div (by positivity) hnr0.ne',
      log_mul (by norm_num) ha0.ne']
  have hL2 : log (1 - t) = log 2 + log b - log nr := by
    rw [show 1 - t = 2 * b / nr by rw [hb]; field_simp, log_div (by positivity) hnr0.ne',
      log_mul (by norm_num) hb0.ne']
  have hL : log (1 - t ^ 2) = log (1 + t) + log (1 - t) := by
    rw [← log_mul (by linarith) (by linarith)]; ring_nf
  have htk : nr * t ^ 2 / 2 = k ^ 2 / (2 * nr) := by rw [ht_def]; field_simp
  set D := (-ln + la + lb) + log (1 - t ^ 2) / 2
    + (nr * (1 + t) / 2 * log (1 + t) + nr * (1 - t) / 2 * log (1 - t) - nr * t ^ 2 / 2) with hD
  have hDeq : log (qj n j) = log (pj n j) + D := by
    rw [hq, hp, hD, ← ha, ← hb, hL, hL1, hL2, htk]
    simp only [ln, la, lb, hlogsqrt]
    linear_combination (log nr - log 2 - 1) * hab
  -- bound on D
  have hD1 : |-ln + la + lb| ≤ 1 / nr := by
    have e1 : 1 / (12 * (j : ℝ)) ≤ 1 / (3 * nr) := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]; linarith
    have e2 : 1 / (12 * ((n - j : ℕ) : ℝ)) ≤ 1 / (3 * nr) := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]; linarith
    have e3 : 1 / (3 * nr) = (1 / nr) / 3 := by field_simp
    have e4 : 1 / (12 * nr) = (1 / nr) / 12 := by field_simp
    have : 0 < 1 / nr := by positivity
    rw [abs_le]; constructor <;> linarith
  have hD2 : |log (1 - t ^ 2) / 2| ≤ t ^ 2 := by
    rw [abs_div, abs_two, div_le_iff₀ (by norm_num)]
    have := abs_log_one_sub_le (t ^ 2) (sq_nonneg t) (by linarith)
    linarith
  have hD3 := entropy_expand nr t hnr0.le ht
  have hDb : |D| ≤ 1 / nr + t ^ 2 + 3 * nr * t ^ 4 := by
    rw [hD]
    calc _ ≤ |-ln + la + lb| + |log (1 - t ^ 2) / 2| + |nr * (1 + t) / 2 * log (1 + t)
          + nr * (1 - t) / 2 * log (1 - t) - nr * t ^ 2 / 2| := abs_add_three _ _ _
      _ ≤ _ := by linarith
  have hconv1 : t ^ 2 = k ^ 2 / nr ^ 2 := by rw [ht_def, div_pow]
  have hconv2 : nr * t ^ 4 = k ^ 4 / nr ^ 3 := by rw [ht_def]; field_simp
  have hDb' : |D| ≤ 1 / nr + k ^ 2 / nr ^ 2 + 3 * k ^ 4 / nr ^ 3 := by
    have : 3 * nr * t ^ 4 = 3 * k ^ 4 / nr ^ 3 := by rw [mul_assoc, hconv2]; ring
    rw [← hconv1]; linarith
  have hD4 : |D| ≤ 4 := by
    have : nr * t ^ 4 ≤ 1 := by
      calc nr * t ^ 4 ≤ nr * (1 / nr) := by gcongr
        _ = 1 := by field_simp
    have : 1 / nr ≤ 1 / 16 := by rw [div_le_div_iff₀ hnr0 (by norm_num)]; linarith
    linarith
  -- conclude
  have hppos := pj_pos n j hj
  have hqpos : 0 < qj n j := by unfold qj; positivity
  have hqe : qj n j = pj n j * exp D := by
    rw [← exp_log hqpos, hDeq, exp_add, exp_log hppos]
  rw [hqe, show pj n j * exp D - pj n j = pj n j * (exp D - 1) by ring, abs_mul,
    abs_of_pos hppos]
  have h1 := abs_exp_sub_one_le' D
  have h2 : exp |D| ≤ 55 := (exp_le_exp.2 hD4).trans exp_four_le
  calc pj n j * |exp D - 1| ≤ pj n j * (|D| * 55) := by
        gcongr; exact h1.trans (by gcongr)
    _ = 55 * pj n j * |D| := by ring
    _ ≤ _ := by gcongr


/-! ## Part 4 (shadow side): the normal law -/

open MeasureTheory Set

/-- The standard normal density `φ(u) = e^{-u²/2}/√(2π)`. -/
noncomputable def gd (u : ℝ) : ℝ := exp (-u ^ 2 / 2) / √(2 * π)

/-- The standard normal distribution function, as printed in the book:
`Φ(x) = (2π)^{-1/2} ∫_{-∞}^x e^{-u²/2} du`. -/
noncomputable def Phi (x : ℝ) : ℝ := 1 / √(2 * π) * ∫ u in Iic x, exp (-u ^ 2 / 2)

theorem gd_eq (u : ℝ) : gd u = 1 / √(2 * π) * exp (-(1 / 2) * u ^ 2) := by
  unfold gd; rw [show -(1 / 2) * u ^ 2 = -u ^ 2 / 2 by ring]; ring

theorem gd_nonneg (u : ℝ) : 0 ≤ gd u := by unfold gd; positivity

theorem sqrt_two_pi_ge_one : 1 ≤ √(2 * π) := by
  rw [show (1 : ℝ) = √1 by simp]
  exact sqrt_le_sqrt (by nlinarith [pi_gt_three])

theorem gd_le_one (u : ℝ) : gd u ≤ 1 := by
  unfold gd
  rw [div_le_one (by positivity)]
  have : exp (-u ^ 2 / 2) ≤ 1 := by
    rw [exp_le_one_iff]; nlinarith [sq_nonneg u]
  linarith [sqrt_two_pi_ge_one]

theorem gd_continuous : Continuous gd := by unfold gd; fun_prop

theorem gd_integrable : Integrable gd := by
  have h := (integrable_exp_neg_mul_sq (b := 1 / 2) (by norm_num)).const_mul (1 / √(2 * π))
  refine h.congr (Filter.Eventually.of_forall (fun u => ?_))
  simp only [gd_eq]

theorem Phi_eq (x : ℝ) : Phi x = ∫ u in Iic x, gd u := by
  unfold Phi gd
  rw [← integral_const_mul]
  congr 1; ext u; ring

theorem integral_gd : ∫ u, gd u = 1 := by
  simp only [gd_eq]
  rw [integral_const_mul, integral_gaussian]
  rw [show π / (1 / 2) = 2 * π by ring]
  have : 0 < √(2 * π) := by positivity
  field_simp

theorem Phi_sub (x y : ℝ) : Phi y - Phi x = ∫ u in x..y, gd u := by
  rw [Phi_eq, Phi_eq]
  exact intervalIntegral.integral_Iic_sub_Iic gd_integrable.integrableOn
    gd_integrable.integrableOn

theorem Phi_add_Ioi (x : ℝ) : Phi x + ∫ u in Ioi x, gd u = 1 := by
  rw [Phi_eq, intervalIntegral.integral_Iic_add_Ioi gd_integrable.integrableOn
    gd_integrable.integrableOn, integral_gd]

theorem Phi_nonneg (x : ℝ) : 0 ≤ Phi x := by
  rw [Phi_eq]; exact setIntegral_nonneg measurableSet_Iic (fun u _ => gd_nonneg u)

theorem Ioi_nonneg (x : ℝ) : 0 ≤ ∫ u in Ioi x, gd u :=
  setIntegral_nonneg measurableSet_Ioi (fun u _ => gd_nonneg u)

theorem Phi_le_one (x : ℝ) : Phi x ≤ 1 := by
  have := Phi_add_Ioi x; have := Ioi_nonneg x; linarith

theorem Phi_mono {x y : ℝ} (h : x ≤ y) : Phi x ≤ Phi y := by
  have := Phi_sub x y
  have : 0 ≤ ∫ u in x..y, gd u :=
    intervalIntegral.integral_nonneg h (fun u _ => gd_nonneg u)
  linarith

theorem Phi_lipschitz (x y : ℝ) : |Phi y - Phi x| ≤ |y - x| := by
  rw [Phi_sub, ← Real.norm_eq_abs]
  have := intervalIntegral.norm_integral_le_of_norm_le_const (a := x) (b := y) (C := 1)
    (f := gd) (fun u _ => by rw [Real.norm_eq_abs, abs_of_nonneg (gd_nonneg u)]; exact gd_le_one u)
  simpa using this

/-- Derivative of the density: `φ' = -u φ`. -/
noncomputable def dgd (u : ℝ) : ℝ := -u * gd u

theorem hasDerivAt_gd (u : ℝ) : HasDerivAt gd (dgd u) u := by
  unfold dgd gd
  have h : HasDerivAt (fun u : ℝ => -u ^ 2 / 2) (-u) u := by
    have := ((hasDerivAt_pow 2 u).neg).div_const 2
    convert this using 1; push_cast; ring
  have := (h.exp).div_const (√(2 * π))
  convert this using 1; ring

theorem hasDerivAt_dgd (u : ℝ) : HasDerivAt dgd ((u ^ 2 - 1) * gd u) u := by
  have h := ((hasDerivAt_id u).neg).mul (hasDerivAt_gd u)
  have e : dgd = fun x => -id x * gd x := by ext x; simp [dgd]
  rw [e]; convert h using 1; simp [dgd]; ring

theorem abs_ddgd_le (u : ℝ) : |(u ^ 2 - 1) * gd u| ≤ 1 := by
  unfold gd
  rw [abs_mul, abs_div, abs_of_pos (exp_pos _), abs_of_pos (by positivity : 0 < √(2 * π))]
  have hy : 0 ≤ u ^ 2 / 2 := by positivity
  have hq := quadratic_le_exp_of_nonneg hy
  have h1 : |u ^ 2 - 1| ≤ exp (u ^ 2 / 2) := by
    rw [abs_le]; constructor
    · nlinarith [sq_nonneg u]
    · nlinarith [sq_nonneg (u ^ 2 / 2 - 1)]
  have h2 : |u ^ 2 - 1| * exp (-u ^ 2 / 2) ≤ 1 := by
    have e : exp (-u ^ 2 / 2) = (exp (u ^ 2 / 2))⁻¹ := by rw [← exp_neg]; ring_nf
    rw [e, ← div_eq_mul_inv, div_le_one (exp_pos _)]; exact h1
  rw [mul_div_assoc']
  rw [div_le_one (by positivity)]
  linarith [sqrt_two_pi_ge_one]

theorem dgd_lipschitz (u c : ℝ) : |dgd u - dgd c| ≤ |u - c| := by
  have := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le (s := univ) (f := dgd)
    (fun x _ => (hasDerivAt_dgd x).hasDerivWithinAt) (fun x _ => abs_ddgd_le x) convex_univ
    (mem_univ c) (mem_univ u)
  simpa using this

/-- Second-order Taylor bound for the density. -/
theorem gd_taylor (u c : ℝ) : |gd u - gd c - (u - c) * dgd c| ≤ (u - c) ^ 2 := by
  have hder : ∀ w ∈ uIcc c u, HasDerivWithinAt (fun w => gd w - w * dgd c)
      (dgd w - dgd c) (uIcc c u) w := by
    intro w _
    have := (hasDerivAt_gd w).sub ((hasDerivAt_id w).mul_const (dgd c))
    exact (this.congr_deriv (by simp)).hasDerivWithinAt
  have hb : ∀ w ∈ uIcc c u, ‖dgd w - dgd c‖ ≤ |u - c| := by
    intro w hw
    rw [Real.norm_eq_abs]
    exact (dgd_lipschitz w c).trans (abs_sub_left_of_mem_uIcc hw)
  have := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le hder hb (convex_uIcc c u)
    left_mem_uIcc right_mem_uIcc
  simp only [Real.norm_eq_abs] at this
  calc |gd u - gd c - (u - c) * dgd c| = |gd u - u * dgd c - (gd c - c * dgd c)| := by ring_nf
    _ ≤ |u - c| * |u - c| := this
    _ = (u - c) ^ 2 := by rw [← abs_mul, ← sq, abs_sq]

/-- Midpoint rule on one cell: `|∫_{c-h}^{c+h} φ - 2hφ(c)| ≤ 2h³`. -/
theorem cell_est (c h : ℝ) (hh : 0 ≤ h) :
    |(∫ u in (c - h)..(c + h), gd u) - 2 * h * gd c| ≤ 2 * h ^ 3 := by
  have hint : IntervalIntegrable gd volume (c - h) (c + h) :=
    gd_continuous.intervalIntegrable _ _
  have e : (∫ u in (c - h)..(c + h), gd u) - 2 * h * gd c
      = ∫ u in (c - h)..(c + h), (gd u - gd c - (u - c) * dgd c) := by
    rw [intervalIntegral.integral_sub, intervalIntegral.integral_sub hint,
      intervalIntegral.integral_mul_const, intervalIntegral.integral_sub, integral_id]
    · simp; ring
    all_goals first
      | exact intervalIntegrable_const
      | exact ((continuous_id.sub continuous_const).mul continuous_const).intervalIntegrable _ _
      | exact continuous_id.intervalIntegrable _ _
      | exact (gd_continuous.sub continuous_const).intervalIntegrable _ _
  rw [e, ← Real.norm_eq_abs]
  have := intervalIntegral.norm_integral_le_of_norm_le_const (a := c - h) (b := c + h)
    (C := h ^ 2) (f := fun u => gd u - gd c - (u - c) * dgd c) (fun u hu => by
      rw [Real.norm_eq_abs]
      refine (gd_taylor u c).trans ?_
      have hu' := uIoc_subset_uIcc hu
      rw [Set.uIcc_of_le (by linarith)] at hu'
      have : |u - c| ≤ h := by rw [abs_le]; constructor <;> linarith [hu'.1, hu'.2]
      calc (u - c) ^ 2 = |u - c| ^ 2 := (sq_abs _).symm
        _ ≤ h ^ 2 := by gcongr)
  refine this.trans (le_of_eq ?_)
  rw [show c + h - (c - h) = 2 * h by ring, abs_of_nonneg (by linarith)]; ring


/-! ## Part 5: assembling the uniform bound -/

theorem sum_pj_moment (n r : ℕ) :
    ∑ j ∈ range (n + 1), pj n j * ((2 : ℝ) * j - n) ^ r
      = (∑ ω : Fin n → Bool, (S ω : ℝ) ^ r) / 2 ^ n := by
  rw [← binom_moment, sum_div]
  refine sum_congr rfl (fun j _ => ?_)
  unfold pj; ring

theorem sum_pj (n : ℕ) : ∑ j ∈ range (n + 1), pj n j = 1 := by
  have := sum_pj_moment n 0
  simp only [pow_zero, mul_one, sum_const, card_univ, Fintype.card_fun, Fintype.card_bool,
    Fintype.card_fin, nsmul_eq_mul] at this
  rw [this]; push_cast; field_simp

theorem sum_pj_sq (n : ℕ) : ∑ j ∈ range (n + 1), pj n j * ((2 : ℝ) * j - n) ^ 2 = n := by
  rw [sum_pj_moment, sum_S_sq (K := ℝ)]; field_simp

theorem sum_pj_four (n : ℕ) :
    ∑ j ∈ range (n + 1), pj n j * ((2 : ℝ) * j - n) ^ 4 ≤ 3 * (n : ℝ) ^ 2 := by
  rw [sum_pj_moment, sum_S_four]
  rw [mul_div_assoc, div_self (by positivity), mul_one]
  have : (0 : ℝ) ≤ n := by positivity
  linarith

/-- Gaussian weight bound off the central range. -/
theorem qj_tail (n j : ℕ) (hn : 1 ≤ n) (hc : (n : ℝ) ^ 3 < ((2 : ℝ) * j - n) ^ 4) :
    qj n j ≤ 16 / (n * √n) := by
  set k : ℝ := (2 : ℝ) * j - n
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  set z : ℝ := k ^ 2 / (2 * n) with hz_def
  have hz0 : 0 ≤ z := by positivity
  have hz : (n : ℝ) / 8 ≤ exp z := by
    have h1 := quadratic_le_exp_of_nonneg hz0
    have h2 : z ^ 2 / 2 = k ^ 4 / (8 * (n : ℝ) ^ 2) := by rw [hz_def]; field_simp; ring
    have h3 : (n : ℝ) / 8 ≤ k ^ 4 / (8 * (n : ℝ) ^ 2) := by
      rw [div_le_div_iff₀ (by norm_num) (by positivity)]; nlinarith
    nlinarith
  have he : exp (-k ^ 2 / (2 * n)) ≤ 8 / n := by
    rw [show -k ^ 2 / (2 * n) = -z by rw [hz_def]; ring, exp_neg]
    calc (exp z)⁻¹ ≤ ((n : ℝ) / 8)⁻¹ := inv_anti₀ (by positivity) hz
      _ = 8 / n := by rw [inv_div]
  have hs : √(n : ℝ) ≤ √(2 * π * n) := sqrt_le_sqrt (by nlinarith [pi_gt_three])
  have hsn : 0 < √(n : ℝ) := sqrt_pos.2 hn0
  unfold qj
  calc 2 / √(2 * π * n) * exp (-k ^ 2 / (2 * n)) ≤ 2 / √(n : ℝ) * (8 / n) := by
        gcongr
    _ = 16 / (n * √n) := by field_simp; ring

/-- Total-variation distance between the binomial and the Gaussian lattice weights. -/
theorem tv_bound (n : ℕ) (hn : 16 ≤ n) :
    ∑ j ∈ range (n + 1), |pj n j - qj n j| ≤ 640 / √n := by
  have hn1 : 1 ≤ n := by omega
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
  have hsn : 0 < √(n : ℝ) := sqrt_pos.2 hn0
  have hpt : ∀ j ∈ range (n + 1), |pj n j - qj n j| ≤
      55 / n * pj n j + 55 / (n : ℝ) ^ 2 * (pj n j * ((2 : ℝ) * j - n) ^ 2)
      + 166 / (n : ℝ) ^ 3 * (pj n j * ((2 : ℝ) * j - n) ^ 4) + 16 / (n * √n) := by
    intro j hj
    have hj' : j ≤ n := Nat.lt_succ_iff.1 (mem_range.1 hj)
    have hp := pj_nonneg n j
    have hq := qj_nonneg n j
    set k : ℝ := (2 : ℝ) * j - n
    have hk2 : 0 ≤ pj n j * k ^ 2 := by positivity
    have hk4 : 0 ≤ pj n j * k ^ 4 := by positivity
    have h16 : 0 ≤ 16 / ((n : ℝ) * √n) := by positivity
    by_cases hc : k ^ 4 ≤ (n : ℝ) ^ 3
    · have := local_est n j hn hj' hc
      rw [abs_sub_comm]
      refine this.trans ?_
      have e : 55 * pj n j * (1 / n + k ^ 2 / (n : ℝ) ^ 2 + 3 * k ^ 4 / (n : ℝ) ^ 3)
          = 55 / n * pj n j + 55 / (n : ℝ) ^ 2 * (pj n j * k ^ 2)
            + 165 / (n : ℝ) ^ 3 * (pj n j * k ^ 4) := by ring
      rw [e]
      have : 165 / (n : ℝ) ^ 3 * (pj n j * k ^ 4) ≤ 166 / (n : ℝ) ^ 3 * (pj n j * k ^ 4) := by
        gcongr; norm_num
      have : 0 ≤ 55 / n * pj n j := by positivity
      linarith
    · have hc' : (n : ℝ) ^ 3 < k ^ 4 := lt_of_not_ge hc
      have hqt := qj_tail n j hn1 hc'
      have hpk : pj n j ≤ 1 / (n : ℝ) ^ 3 * (pj n j * k ^ 4) := by
        rw [div_mul_eq_mul_div, one_mul, le_div_iff₀ (by positivity)]
        nlinarith
      have habs : |pj n j - qj n j| ≤ pj n j + qj n j := by
        rw [abs_le]; constructor <;> linarith
      have : 0 ≤ 55 / n * pj n j := by positivity
      have : 0 ≤ 55 / (n : ℝ) ^ 2 * (pj n j * k ^ 2) := by positivity
      have : 1 / (n : ℝ) ^ 3 * (pj n j * k ^ 4) ≤ 166 / (n : ℝ) ^ 3 * (pj n j * k ^ 4) := by
        gcongr; norm_num
      linarith
  refine (sum_le_sum hpt).trans ?_
  simp only [sum_add_distrib, ← mul_sum, sum_const, card_range, nsmul_eq_mul]
  rw [sum_pj, sum_pj_sq]
  have h4 := sum_pj_four n
  have h4' : 166 / (n : ℝ) ^ 3 * ∑ j ∈ range (n + 1), pj n j * ((2 : ℝ) * j - n) ^ 4
      ≤ 166 / (n : ℝ) ^ 3 * (3 * (n : ℝ) ^ 2) := by gcongr
  set s := √(n : ℝ) with hs_def
  have hss : s ^ 2 = n := sq_sqrt hn0.le
  have hs1 : 1 ≤ s := by rw [hs_def, show (1 : ℝ) = √1 by simp]; exact sqrt_le_sqrt (by
    exact_mod_cast hn1)
  have hfin : 55 / (n : ℝ) * 1 + 55 / (n : ℝ) ^ 2 * n + 166 / (n : ℝ) ^ 3 * (3 * (n : ℝ) ^ 2)
      + ((n + 1 : ℕ) : ℝ) * (16 / (n * s)) ≤ 640 / s := by
    rw [← hss]; push_cast; rw [← hss]
    have hs0 : 0 < s := by linarith
    have e : 55 / s ^ 2 * 1 + 55 / (s ^ 2) ^ 2 * s ^ 2 + 166 / (s ^ 2) ^ 3 * (3 * (s ^ 2) ^ 2)
        + (s ^ 2 + 1) * (16 / (s ^ 2 * s)) = 608 / s ^ 2 + 16 * (s ^ 2 + 1) / s ^ 3 := by
      field_simp; ring
    rw [e]
    have : 608 / s ^ 2 ≤ 608 / s := div_le_div_of_nonneg_left (by norm_num) hs0 (by nlinarith)
    have : 16 * (s ^ 2 + 1) / s ^ 3 ≤ 32 / s := by
      rw [div_le_div_iff₀ (by positivity) hs0]; nlinarith [pow_pos hs0 3]
    have : (640 : ℝ) / s = 608 / s + 32 / s := by ring
    linarith
  linarith


theorem qj_eq (n : ℕ) (hn : 1 ≤ n) (j : ℕ) :
    qj n j = 2 * (1 / √n) * gd (((2 : ℝ) * j - n) * (1 / √n)) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hs : 0 < √(n : ℝ) := sqrt_pos.2 hn0
  have hsq : √(n : ℝ) ^ 2 = n := sq_sqrt hn0.le
  unfold qj gd
  have e1 : (((2 : ℝ) * j - n) * (1 / √n)) ^ 2 = ((2 : ℝ) * j - n) ^ 2 / n := by
    rw [mul_pow, one_div, inv_pow, hsq]; ring
  rw [e1, sqrt_mul (by positivity) (n : ℝ)]
  rw [show -(((2 : ℝ) * j - n) ^ 2 / n) / 2 = -((2 : ℝ) * j - n) ^ 2 / (2 * n) by ring]
  field_simp

/-- Left endpoints of the cells: cell `j` is `[a_j, a_{j+1}]`, centred at `(2j-n)/√n`. -/
noncomputable def cellEnd (n j : ℕ) : ℝ := ((2 : ℝ) * j - n - 1) * (1 / √n)

/-- The Gaussian lattice weights reproduce the normal law cell by cell. -/
theorem cells_est (n : ℕ) (hn : 1 ≤ n) (m : ℕ) (hm : m ≤ n + 1) :
    |∑ j ∈ range m, qj n j - (Phi (cellEnd n m) - Phi (cellEnd n 0))|
      ≤ 2 * (n + 1) * (1 / √n) ^ 3 := by
  set h : ℝ := 1 / √n with hh
  have hh0 : 0 ≤ h := by positivity
  rw [Phi_sub, ← intervalIntegral.sum_integral_adjacent_intervals
    (fun k _ => gd_continuous.intervalIntegrable _ _), ← sum_sub_distrib]
  refine (abs_sum_le_sum_abs _ _).trans ?_
  have hpt : ∀ j ∈ range m, |qj n j - ∫ u in cellEnd n j..cellEnd n (j + 1), gd u|
      ≤ 2 * h ^ 3 := by
    intro j _
    have e1 : cellEnd n j = ((2 : ℝ) * j - n) * h - h := by unfold cellEnd; rw [← hh]; ring
    have e2 : cellEnd n (j + 1) = ((2 : ℝ) * j - n) * h + h := by
      unfold cellEnd; rw [← hh]; push_cast; ring
    rw [e1, e2, qj_eq n hn j, ← hh, abs_sub_comm]
    exact cell_est _ h hh0
  refine (sum_le_sum hpt).trans ?_
  rw [sum_const, card_range, nsmul_eq_mul]
  have : (m : ℝ) ≤ n + 1 := by exact_mod_cast hm
  have : 0 ≤ 2 * h ^ 3 := by positivity
  nlinarith

/-- The distribution function of the normalised walk, `P(S_n ≤ x√n)`. -/
noncomputable def Fn (n : ℕ) (x : ℝ) : ℝ :=
  prob (univ : Finset (Fin n → Bool)) (unif univ) (fun ω => (S ω : ℝ) ≤ x * √n)

theorem Fn_eq (n : ℕ) (x : ℝ) :
    Fn n x = ∑ j ∈ (range (n + 1)).filter (fun j : ℕ => (2 : ℝ) * j - n ≤ x * √n), pj n j := by
  unfold Fn prob unif
  rw [sum_filter, sum_filter, card_univ, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]
  have := sum_fun_S n (fun s => if s ≤ x * √n then 1 else 0)
  calc ∑ ω : Fin n → Bool, (if (S ω : ℝ) ≤ x * √n then 1 / (((2 ^ n : ℕ)) : ℝ) else 0)
      = (1 / 2 ^ n) * ∑ ω : Fin n → Bool, (if (S ω : ℝ) ≤ x * √n then (1 : ℝ) else 0) := by
        rw [mul_sum]; refine sum_congr rfl (fun ω _ => ?_); split_ifs <;> push_cast <;> ring
    _ = (1 / 2 ^ n) * ∑ j ∈ range (n + 1),
          (n.choose j : ℝ) * (if (2 : ℝ) * j - n ≤ x * √n then 1 else 0) := by rw [this]
    _ = _ := by
        rw [mul_sum]; refine sum_congr rfl (fun j _ => ?_); unfold pj
        split_ifs <;> ring

/-- **CLT with error term, large `n`.** -/
theorem clt_bound_large (n : ℕ) (hn : 16 ≤ n) (x : ℝ) : |Fn n x - Phi x| ≤ 2000 / √n := by
  have hn1 : 1 ≤ n := by omega
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
  set s : ℝ := √n with hs_def
  have hs0 : 0 < s := sqrt_pos.2 hn0
  have hss : s ^ 2 = n := sq_sqrt hn0.le
  have hs1 : 1 ≤ s := by
    rw [hs_def, show (1 : ℝ) = √1 by simp]; exact sqrt_le_sqrt (by exact_mod_cast hn1)
  set h : ℝ := 1 / s with hh
  have hh0 : 0 < h := by positivity
  set E := ∑ j ∈ range (n + 1), |pj n j - qj n j| with hE
  have hEb : E ≤ 640 / s := tv_bound n hn
  set W : ℝ := 2 * (n + 1) * h ^ 3 with hW
  have hWb : W ≤ 4 / s := by
    rw [hW, hh, ← hss, div_pow, one_pow]
    rw [show 2 * (s ^ 2 + 1) * (1 / s ^ 3) = 2 * (s ^ 2 + 1) / s ^ 3 by ring,
      div_le_div_iff₀ (by positivity) hs0]
    nlinarith [pow_pos hs0 3]
  set A := Phi (cellEnd n 0) with hA
  set B := 1 - Phi (cellEnd n (n + 1)) with hB
  have hA0 : 0 ≤ A := Phi_nonneg _
  have hB0 : 0 ≤ B := by have := Phi_le_one (cellEnd n (n + 1)); linarith
  -- the total mass of the cells
  have hAB : A + B ≤ E + W := by
    have hc := cells_est n hn1 (n + 1) le_rfl
    have hpq : 1 - ∑ j ∈ range (n + 1), qj n j ≤ E := by
      rw [← sum_pj n, ← sum_sub_distrib]
      exact (le_abs_self _).trans (abs_sum_le_sum_abs _ _)
    rw [abs_le] at hc
    linarith [hc.1]
  -- the event as an initial segment of indices
  obtain ⟨m, hm, hfilt⟩ := filter_range_downset (fun j : ℕ => (2 : ℝ) * j - n ≤ x * s)
    (fun i j hij hj => by
      have : (i : ℝ) ≤ j := by exact_mod_cast hij
      linarith) (n + 1)
  have hF : Fn n x = ∑ j ∈ range m, pj n j := by rw [Fn_eq, hfilt]
  have hmem : ∀ j, j ∈ range m ↔ (j < n + 1 ∧ (2 : ℝ) * j - n ≤ x * s) := by
    intro j; rw [← hfilt, mem_filter, Finset.mem_range]
  have hFq : |∑ j ∈ range m, pj n j - ∑ j ∈ range m, qj n j| ≤ E := by
    rw [← sum_sub_distrib]
    refine (abs_sum_le_sum_abs _ _).trans ?_
    exact sum_le_sum_of_subset_of_nonneg (range_subset_range.2 hm)
      (fun _ _ _ => abs_nonneg _)
  have hcm := cells_est n hn1 m hm
  rw [← hs_def, ← hh] at hcm
  -- position of `x` relative to the cell boundary `a_m`
  have hconv : ∀ y : ℝ, (y ≤ x * s ↔ y * h ≤ x) := by
    intro y; rw [hh, mul_one_div, div_le_iff₀ hs0]
  have hPhi : |Phi (cellEnd n m) - Phi x| ≤ h + A + B := by
    have lip : ∀ y, |y - x| ≤ h → |Phi y - Phi x| ≤ h + A + B := fun y hy => by
      have := Phi_lipschitz x y; linarith
    have hce : ∀ j : ℕ, cellEnd n j = ((2 : ℝ) * j - n - 1) * h := by
      intro j; unfold cellEnd; rw [hh, hs_def]
    rcases Nat.eq_zero_or_pos m with h0 | hpos
    · -- `x` lies left of every lattice point
      have hnot : ¬ ((2 : ℝ) * (0 : ℕ) - n ≤ x * s) := by
        intro hc; have := (hmem 0).2 ⟨by omega, hc⟩; rw [h0] at this; simp at this
      rw [hconv] at hnot
      have hlt : x < (-(n : ℝ)) * h := by push_cast at hnot; linarith
      rw [h0]
      by_cases hx : cellEnd n 0 ≤ x
      · apply lip; rw [abs_le]; rw [hce] at hx ⊢; push_cast at hx ⊢; constructor <;> nlinarith
      · have h1 := Phi_mono (lt_of_not_ge hx).le
        have h2 := Phi_nonneg x
        rw [abs_le]; constructor <;> linarith
    · rcases Nat.lt_or_ge m (n + 1) with hlt | hge
      · have hP1 : (2 : ℝ) * ((m - 1 : ℕ) : ℝ) - n ≤ x * s := ((hmem (m - 1)).1
          (by rw [Finset.mem_range]; omega)).2
        have hP2 : ¬ ((2 : ℝ) * (m : ℝ) - n ≤ x * s) := by
          intro hc; have := (hmem m).2 ⟨hlt, hc⟩; simp at this
        rw [hconv] at hP1 hP2
        have hc1 : ((m - 1 : ℕ) : ℝ) = (m : ℝ) - 1 := by
          rw [Nat.cast_sub (by omega)]; simp
        rw [hc1] at hP1
        apply lip; rw [hce, abs_le]; constructor <;> nlinarith
      · have hmn : m = n + 1 := by omega
        have hPn : (2 : ℝ) * (n : ℝ) - n ≤ x * s := ((hmem n).1 (by rw [hmn, Finset.mem_range]; omega)).2
        rw [hconv] at hPn
        rw [hmn]
        by_cases hx : x ≤ cellEnd n (n + 1)
        · apply lip; rw [abs_le]; rw [hce] at hx ⊢; push_cast at hx ⊢
          constructor <;> nlinarith
        · have h1 := Phi_mono (lt_of_not_ge hx).le
          have h2 := Phi_le_one x
          rw [abs_le]; constructor <;> linarith
  rw [hF]
  rw [abs_le] at hFq hcm hPhi ⊢
  rw [← hW] at hcm
  have : (2000 : ℝ) / s = 3 * (640 / s) + 3 * (4 / s) + 1 / s + 67 / s := by ring
  have : 0 ≤ 67 / s := by positivity
  constructor <;> linarith


theorem Fn_nonneg (n : ℕ) (x : ℝ) : 0 ≤ Fn n x := by
  rw [Fn_eq]; exact sum_nonneg (fun j _ => pj_nonneg n j)

theorem Fn_le_one (n : ℕ) (x : ℝ) : Fn n x ≤ 1 := by
  rw [Fn_eq, ← sum_pj n]
  exact sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun j _ _ => pj_nonneg n j)

/-- **Central limit theorem with error term** (explicit constant `C = 2000`):
for every `n ≥ 1` and every real `x`, `|P(S_n ≤ x√n) - Φ(x)| ≤ 2000/√n`. -/
theorem clt_error_explicit (n : ℕ) (hn : 1 ≤ n) (x : ℝ) : |Fn n x - Phi x| ≤ 2000 / √n := by
  rcases Nat.lt_or_ge n 16 with hlt | hge
  · have h1 : |Fn n x - Phi x| ≤ 1 := by
      rw [abs_le]
      constructor <;> linarith [Fn_nonneg n x, Fn_le_one n x, Phi_nonneg x, Phi_le_one x]
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
    have hs : √(n : ℝ) ≤ 4 := by
      rw [show (4 : ℝ) = √16 by rw [show (16 : ℝ) = 4 ^ 2 by norm_num, sqrt_sq (by norm_num)]]
      exact sqrt_le_sqrt (by exact_mod_cast hlt.le)
    have hs0 : 0 < √(n : ℝ) := sqrt_pos.2 hn0
    have : 1 ≤ 2000 / √(n : ℝ) := by rw [le_div_iff₀ hs0]; linarith
    linarith
  · exact clt_bound_large n hge x

/-- **Central limit theorem with error term** (the book's statement,
`thm:prob-clt`): there is an absolute constant `C` such that for every `n ≥ 1`,
`sup_x |P(S_n ≤ x√n) - Φ(x)| ≤ C/√n`, where `P` is the uniform law on the coin
space `{±1}^n` and `Φ(x) = (2π)^{-1/2} ∫_{-∞}^x e^{-u²/2} du`. -/
theorem clt_error : ∃ C : ℝ, ∀ n : ℕ, 1 ≤ n → ∀ x : ℝ,
    |prob (univ : Finset (Fin n → Bool)) (unif univ) (fun ω => (S ω : ℝ) ≤ x * √n)
      - 1 / √(2 * π) * ∫ u in Iic x, exp (-u ^ 2 / 2)| ≤ C / √n :=
  ⟨2000, fun n hn x => clt_error_explicit n hn x⟩

/-- Qualitative consequence: for every fixed `x`, `P(S_n ≤ x√n) → Φ(x)`. -/
theorem clt_tendsto (x : ℝ) :
    Filter.Tendsto (fun n : ℕ => Fn n x) Filter.atTop (nhds (Phi x)) := by
  rw [Metric.tendsto_atTop]
  intro δ hδ
  obtain ⟨N, hN⟩ := exists_nat_gt ((2000 / δ) ^ 2)
  refine ⟨N + 1, fun n hn => ?_⟩
  have hn1 : 1 ≤ n := by omega
  have hnN : ((2000 / δ) ^ 2 : ℝ) < n := by
    have : (N : ℝ) ≤ n := by exact_mod_cast (by omega : N ≤ n)
    linarith
  have hsq : 2000 / δ < √(n : ℝ) := by
    rw [show 2000 / δ = √((2000 / δ) ^ 2) by rw [sqrt_sq (by positivity)]]
    exact sqrt_lt_sqrt (by positivity) hnN
  have hs0 : 0 < √(n : ℝ) := lt_trans (by positivity) hsq
  rw [Real.dist_eq]
  refine (clt_error_explicit n hn1 x).trans_lt ?_
  rw [div_lt_iff₀ hs0]
  rw [div_lt_iff₀ hδ] at hsq
  linarith


/-! ## Part 6: the hyperfinite reading -/

theorem Phi_continuous : Continuous Phi :=
  (LipschitzWith.of_dist_le_mul (K := 1) (fun x y => by
    rw [Real.dist_eq, Real.dist_eq, NNReal.coe_one, one_mul]
    exact Phi_lipschitz y x)).continuous

open Hyperreal QE.Hyper in
/-- **Hyperfinite form of the error bound.**  For a hypernatural `n = [n_k] ≥ 1` and
a hyperreal `x = [x_k]`, the internal distribution function satisfies
`|*P(S_n ≤ x√n) - *Φ(x)| ≤ 2000/√n` (the transfer of `clt_error_explicit`). -/
theorem clt_error_hyper (nseq : ℕ → ℕ) (hn : ∀ k, 1 ≤ nseq k) (xseq : ℕ → ℝ) :
    ofSeq (fun k => |Fn (nseq k) (xseq k) - Phi (xseq k)|)
      ≤ ofSeq (fun k => 2000 / √(nseq k : ℝ)) :=
  ofSeq_le_ofSeq.2 (Filter.Eventually.of_forall (fun k => clt_error_explicit _ (hn k) _))

open Hyperreal QE.Hyper in
/-- **Consequence for infinite `n`.**  If `n = [n_k]` is an infinite hypernatural and
`x = [x_k]` is a finite hyperreal, then `*P(S_n ≤ x√n) ≈ Φ(st x)`. -/
theorem clt_infinite (nseq : ℕ → ℕ) (xseq : ℕ → ℝ)
    (hN : ∀ r : ℝ, (r : ℝ*) < ofSeq (fun k => (nseq k : ℝ)))
    (hx : IsFinite (ofSeq xseq)) :
    Icl (ofSeq (fun k => Fn (nseq k) (xseq k)))
      (Phi (ArchimedeanClass.stdPart (ofSeq xseq)) : ℝ*) := by
  apply icl_of_tendsto
  set r := ArchimedeanClass.stdPart (ofSeq xseq)
  have hxr : Filter.Tendsto xseq (Filter.hyperfilter ℕ) (nhds r) := tendsto_ofSeq.1 (tendsto_stdPart hx)
  have hev : ∀ b : ℝ, ∀ᶠ k in (Filter.hyperfilter ℕ : Filter ℕ), b < (nseq k : ℝ) := fun b =>
    ofSeq_lt_ofSeq.1 (hN b)
  have hNt : Filter.Tendsto (fun k => (nseq k : ℝ)) (Filter.hyperfilter ℕ) Filter.atTop :=
    Filter.tendsto_atTop.2 (fun b => (hev b).mono (fun _ h => h.le))
  have hsq : Filter.Tendsto (fun k => 2000 / √(nseq k : ℝ)) (Filter.hyperfilter ℕ) (nhds 0) := by
    have : Filter.Tendsto (fun t : ℝ => 2000 / √t) Filter.atTop (nhds 0) :=
      tendsto_const_nhds.div_atTop (tendsto_sqrt_atTop)
    exact this.comp hNt
  have hPhi : Filter.Tendsto (fun k => Phi (xseq k)) (Filter.hyperfilter ℕ) (nhds (Phi r)) :=
    (Phi_continuous.tendsto r).comp hxr
  have hdiff : Filter.Tendsto (fun k => Fn (nseq k) (xseq k) - Phi (xseq k)) (Filter.hyperfilter ℕ)
      (nhds 0) := by
    refine squeeze_zero_norm' ?_ hsq
    filter_upwards [hev 0] with k hk
    have : 1 ≤ nseq k := by
      have : (0 : ℝ) < nseq k := hk
      exact_mod_cast this
    rw [Real.norm_eq_abs]
    exact clt_error_explicit _ this _
  rw [tendsto_ofSeq]
  have := hdiff.add hPhi
  simpa using this

end QE.Prob.BE
