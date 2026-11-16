-- SPDX-License-Identifier: MIT
-- Copyright 2026 Metere Industries, Inc. Author: Alfredo Metere.
-- Quasi-Euclidean Granular Geometry. Any derivative work must carry this notice:
--   This work is derivative of the Quasi-Euclidean Granular Geometry book
--   authored by Alfredo Metere. Copyright 2026 Metere Industries, Inc.
--   All rights reserved
-- See LICENSE.md and NOTICE.

import QuasiEuclidean.Basic

/-!
# Chapter 5: Granular integral calculus

`QE.gint ε f a n = ∑_{k<n} f(a + 2εk) · 2ε` is the granular integral over the
half-open run `[a, b)` of lattice points, `b = a + 2εn`.  All identities are
exact for every `ε` in every linearly ordered field; shadow statements are
proved over `ℝ` as limits.
-/

open Finset

set_option linter.unusedSectionVars false

namespace QE.Integral

section Algebra

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-- Granular integral over the closed run `[a, b]` (`n + 1` points). -/
def gintCC (ε : K) (f : K → K) (a : K) (n : ℕ) : K :=
  ∑ k ∈ range (n + 1), f (a + 2 * ε * k) * (2 * ε)

/-- Granular integral over the open run `(a, b)` (`n - 1` points). -/
def gintOO (ε : K) (f : K → K) (a : K) (n : ℕ) : K :=
  ∑ k ∈ Ico 1 n, f (a + 2 * ε * k) * (2 * ε)

/-- Granular integral over the run `(a, b]` (`n` points). -/
def gintOC (ε : K) (f : K → K) (a : K) (n : ℕ) : K :=
  ∑ k ∈ Ico 1 (n + 1), f (a + 2 * ε * k) * (2 * ε)

/-- Additivity over adjacent half-open runs: `[a,c) = [a,b) ⊔ [b,c)`. -/
theorem gint_add_runs (ε : K) (f : K → K) (a : K) (m n : ℕ) :
    QE.gint ε f a (m + n) = QE.gint ε f a m + QE.gint ε f (a + 2 * ε * m) n := by
  unfold QE.gint
  rw [sum_range_add]
  congr 1
  apply sum_congr rfl
  intro k _
  push_cast; ring_nf

theorem gint_add (ε : K) (f g : K → K) (a : K) (n : ℕ) :
    QE.gint ε (fun x => f x + g x) a n = QE.gint ε f a n + QE.gint ε g a n := by
  unfold QE.gint; rw [← sum_add_distrib]; apply sum_congr rfl; intro k _; ring

theorem gint_smul (ε c : K) (f : K → K) (a : K) (n : ℕ) :
    QE.gint ε (fun x => c * f x) a n = c * QE.gint ε f a n := by
  unfold QE.gint; rw [mul_sum]; apply sum_congr rfl; intro k _; ring

/-- The integral of a constant over `[a, b)` is `c (b - a)`: the measure of
`[a,b)` is exactly `b - a`. -/
theorem gint_const (ε c : K) (a : K) (n : ℕ) :
    QE.gint ε (fun _ => c) a n = c * (2 * ε * n) := by
  unfold QE.gint; rw [sum_const, card_range, nsmul_eq_mul]; ring

/-- Monotonicity of the granular integral. -/
theorem gint_mono (ε : K) (hε : 0 < ε) (f g : K → K) (a : K) (n : ℕ)
    (h : ∀ k < n, f (a + 2 * ε * k) ≤ g (a + 2 * ε * k)) :
    QE.gint ε f a n ≤ QE.gint ε g a n := by
  unfold QE.gint
  apply sum_le_sum
  intro k hk
  exact mul_le_mul_of_nonneg_right (h k (mem_range.mp hk)) (by positivity)

/-- Triangle inequality. -/
theorem abs_gint_le (ε : K) (hε : 0 < ε) (f : K → K) (a : K) (n : ℕ) :
    |QE.gint ε f a n| ≤ QE.gint ε (fun x => |f x|) a n := by
  unfold QE.gint
  refine (abs_sum_le_sum_abs _ _).trans (le_of_eq ?_)
  apply sum_congr rfl; intro k _
  rw [abs_mul, abs_of_pos (by positivity : (0 : K) < 2 * ε)]

/-- **Exact fundamental theorem of granular calculus** (first form). -/
theorem granular_ftc (ε : K) (hε : ε ≠ 0) (f : K → K) (a : K) (n : ℕ) :
    QE.gint ε (QE.Dp ε f) a n = f (a + 2 * ε * n) - f a := by
  unfold QE.gint QE.Dp
  induction n with
  | zero => simp
  | succ n ih =>
    rw [sum_range_succ, ih]
    have : a + 2 * ε * ((n : K)) + 2 * ε = a + 2 * ε * ((n + 1 : ℕ) : K) := by push_cast; ring
    rw [this]; field_simp; ring

/-- **Second fundamental theorem**: the forward difference quotient of the running
integral `F(a + 2εn) = ∫_{[a, a+2εn)} f` is the integrand, exactly. -/
theorem granular_ftc2 (ε : K) (hε : ε ≠ 0) (f : K → K) (a : K) (n : ℕ) :
    (QE.gint ε f a (n + 1) - QE.gint ε f a n) / (2 * ε) = f (a + 2 * ε * n) := by
  unfold QE.gint; rw [sum_range_succ]; field_simp; ring

/-- **Summation by parts** (shifted form). -/
theorem sum_by_parts (ε : K) (hε : ε ≠ 0) (f g : K → K) (a : K) (n : ℕ) :
    QE.gint ε (fun x => f x * QE.Dp ε g x) a n
      = f (a + 2 * ε * n) * g (a + 2 * ε * n) - f a * g a
        - QE.gint ε (fun x => QE.Dp ε f x * g (x + 2 * ε)) a n := by
  have h := granular_ftc ε hε (fun x => f x * g x) a n
  have e : QE.gint ε (QE.Dp ε (fun x => f x * g x)) a n
      = QE.gint ε (fun x => f x * QE.Dp ε g x) a n
        + QE.gint ε (fun x => QE.Dp ε f x * g (x + 2 * ε)) a n := by
    rw [← gint_add]
    unfold QE.gint
    apply sum_congr rfl; intro k _
    unfold QE.Dp; field_simp; ring
  rw [e] at h
  linarith

/-- **Summation by parts with the explicit `2ε` correction** (symmetric form):
`∫ f D⁺g = [fg] - ∫ g D⁺f - 2ε ∫ D⁺f D⁺g`. -/
theorem sum_by_parts_sym (ε : K) (hε : ε ≠ 0) (f g : K → K) (a : K) (n : ℕ) :
    QE.gint ε (fun x => f x * QE.Dp ε g x) a n
      = f (a + 2 * ε * n) * g (a + 2 * ε * n) - f a * g a
        - QE.gint ε (fun x => QE.Dp ε f x * g x) a n
        - 2 * ε * QE.gint ε (fun x => QE.Dp ε f x * QE.Dp ε g x) a n := by
  rw [sum_by_parts ε hε]
  have : QE.gint ε (fun x => QE.Dp ε f x * g (x + 2 * ε)) a n
      = QE.gint ε (fun x => QE.Dp ε f x * g x) a n
        + 2 * ε * QE.gint ε (fun x => QE.Dp ε f x * QE.Dp ε g x) a n := by
    rw [← gint_smul, ← gint_add]
    unfold QE.gint
    apply sum_congr rfl; intro k _
    unfold QE.Dp; field_simp; ring
  rw [this]; ring

/-- **Mean value theorem for granular integrals**: the mean value of `f` over a
run lies between two values of `f` at lattice points of the run. -/
theorem gint_mean_value (ε : K) (hε : 0 < ε) (f : K → K) (a : K) (n : ℕ) (hn : 0 < n) :
    (∃ k < n, f (a + 2 * ε * k) ≤ QE.gint ε f a n / (2 * ε * n)) ∧
    (∃ k < n, QE.gint ε f a n / (2 * ε * n) ≤ f (a + 2 * ε * k)) := by
  have hne : (range n).Nonempty := nonempty_range_iff.mpr (by omega)
  have hnK : (0 : K) < n := by exact_mod_cast hn
  have hpos : (0 : K) < 2 * ε * n := by positivity
  have hsum : ∑ k ∈ range n, f (a + 2 * ε * k)
      = ∑ _k ∈ range n, QE.gint ε f a n / (2 * ε * n) := by
    rw [sum_const, card_range, nsmul_eq_mul]
    unfold QE.gint; rw [← sum_mul]; field_simp
  constructor
  · obtain ⟨k, hk, h⟩ := exists_le_of_sum_le hne hsum.le
    exact ⟨k, mem_range.mp hk, h⟩
  · obtain ⟨k, hk, h⟩ := exists_le_of_sum_le hne hsum.ge
    exact ⟨k, mem_range.mp hk, h⟩

/-- **Cauchy–Schwarz inequality** for granular integrals. -/
theorem gint_cauchy_schwarz (ε : K) (hε : 0 < ε) (f g : K → K) (a : K) (n : ℕ) :
    QE.gint ε (fun x => f x * g x) a n ^ 2
      ≤ QE.gint ε (fun x => f x ^ 2) a n * QE.gint ε (fun x => g x ^ 2) a n := by
  unfold QE.gint
  beta_reduce
  have := sum_mul_sq_le_sq_mul_sq (range n) (fun k => f (a + 2 * ε * k)) (fun k => g (a + 2 * ε * k))
  have h2 : (0 : K) ≤ (2 * ε) ^ 2 := by positivity
  rw [← sum_mul, ← sum_mul, ← sum_mul]
  calc ((∑ k ∈ range n, f (a + 2 * ε * k) * g (a + 2 * ε * k)) * (2 * ε)) ^ 2
      = (∑ k ∈ range n, f (a + 2 * ε * k) * g (a + 2 * ε * k)) ^ 2 * (2 * ε) ^ 2 := by ring
    _ ≤ ((∑ k ∈ range n, f (a + 2 * ε * k) ^ 2) * ∑ k ∈ range n, g (a + 2 * ε * k) ^ 2)
          * (2 * ε) ^ 2 := mul_le_mul_of_nonneg_right this h2
    _ = _ := by ring

/-- The lattice exponential integrates exactly:
`∑_{k<n} (1+2ε)^k · 2ε = (1+2ε)^n - 1`, i.e. `∫_{[0,b)} e_ε = e_ε(b) - 1`. -/
theorem gint_exp_lattice (ε : K) (n : ℕ) :
    ∑ k ∈ range n, (1 + 2 * ε) ^ k * (2 * ε) = (1 + 2 * ε) ^ n - 1 := by
  induction n with
  | zero => simp
  | succ n ih => rw [sum_range_succ, ih, pow_succ]; ring

/-! ### Endpoint conventions -/

/-- Closed run: `∫_{[a,b]} = ∫_{[a,b)} + 2ε f(b)`. -/
theorem gintCC_eq (ε : K) (f : K → K) (a : K) (n : ℕ) :
    gintCC ε f a n = QE.gint ε f a n + f (a + 2 * ε * n) * (2 * ε) := by
  unfold gintCC QE.gint; rw [sum_range_succ]

/-- Open run: `∫_{(a,b)} = ∫_{[a,b)} - 2ε f(a)`. -/
theorem gintOO_eq (ε : K) (f : K → K) (a : K) (n : ℕ) (hn : 1 ≤ n) :
    gintOO ε f a n = QE.gint ε f a n - f a * (2 * ε) := by
  unfold gintOO QE.gint
  rw [range_eq_Ico, ← sum_Ico_consecutive _ (Nat.zero_le 1) hn]
  simp

/-- Left-open run: `∫_{(a,b]} = ∫_{[a,b)} + 2ε (f(b) - f(a))`. -/
theorem gintOC_eq (ε : K) (f : K → K) (a : K) (n : ℕ) :
    gintOC ε f a n = QE.gint ε f a n + (f (a + 2 * ε * n) - f a) * (2 * ε) := by
  have h := gintOO_eq ε f a (n + 1) (by omega)
  unfold gintOO at h; unfold gintOC
  rw [h]
  unfold QE.gint; rw [sum_range_succ]; ring

/-- The right Riemann sum is the granular integral over the shifted run. -/
theorem gintOC_shift (ε : K) (f : K → K) (a : K) (n : ℕ) :
    gintOC ε f a n = QE.gint ε f (a + 2 * ε) n := by
  unfold gintOC QE.gint
  rw [sum_Ico_eq_sum_range]
  rw [show n + 1 - 1 = n by omega]
  apply sum_congr rfl; intro k _; push_cast; ring_nf

/-- The four interval measures, recovered from integrating `1`. -/
theorem interval_measures (ε : K) (a : K) (n : ℕ) (hn : 1 ≤ n) :
    gintCC ε (fun _ => 1) a n = 2 * ε * n + 2 * ε ∧
    QE.gint ε (fun _ => 1) a n = 2 * ε * n ∧
    gintOC ε (fun _ => 1) a n = 2 * ε * n ∧
    gintOO ε (fun _ => 1) a n = 2 * ε * n - 2 * ε := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [gintCC_eq, gint_const]; ring
  · rw [gint_const]; ring
  · rw [gintOC_eq, gint_const]; ring
  · rw [gintOO_eq ε _ a n hn, gint_const]; ring

/-- **The trapezoid rule is the mean of the closed and open granular integrals**
(and of the two half-open ones). -/
theorem trapezoid (ε : K) (f : K → K) (a : K) (n : ℕ) (hn : 1 ≤ n) :
    QE.gint ε f a n + ε * (f (a + 2 * ε * n) - f a)
      = (gintCC ε f a n + gintOO ε f a n) / 2 ∧
    QE.gint ε f a n + ε * (f (a + 2 * ε * n) - f a)
      = (QE.gint ε f a n + gintOC ε f a n) / 2 := by
  rw [gintCC_eq, gintOO_eq ε f a n hn, gintOC_eq]
  constructor <;> ring_nf

/-- The midpoint rule is the granular integral on the dual lattice `a + ε + 2εℤ`. -/
theorem midpoint_rule (ε : K) (f : K → K) (a : K) (n : ℕ) :
    ∑ k ∈ range n, f ((a + 2 * ε * k + (a + 2 * ε * (k + 1))) / 2) * (2 * ε)
      = QE.gint ε f (a + ε) n := by
  unfold QE.gint; apply sum_congr rfl; intro k _; congr 2; field_simp; ring

/-! ### Changes of variables -/

/-- Translation by a lattice vector. -/
theorem gint_translate (ε : K) (f : K → K) (a : K) (j : ℤ) (n : ℕ) :
    QE.gint ε (fun x => f (x + 2 * ε * j)) a n = QE.gint ε f (a + 2 * ε * j) n := by
  unfold QE.gint; apply sum_congr rfl; intro k _; beta_reduce; congr 2; ring

/-- Reflection maps `[a, b)` onto `(-b, -a]`: openness is transported to the other end. -/
theorem gint_reflect (ε : K) (f : K → K) (a : K) (n : ℕ) :
    QE.gint ε (fun x => f (-x)) a n = gintOC ε f (-(a + 2 * ε * n)) n := by
  rw [gintOC_shift]
  unfold QE.gint
  rw [← sum_range_reflect]
  apply sum_congr rfl
  intro k hk
  have hk' : k < n := mem_range.mp hk
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  rw [Nat.cast_sub (by omega : k ≤ m)]
  push_cast; ring_nf

/-- Integer dilation `u = m x`: an exact change of granule `ε ↦ m ε`. -/
theorem gint_dilate (ε : K) (f : K → K) (a : K) (m n : ℕ) :
    QE.gint ε (fun x => f (m * x)) a n * m = QE.gint (m * ε) f (m * a) n := by
  unfold QE.gint; rw [sum_mul]; apply sum_congr rfl; intro k _; ring_nf

/-- **Exact change of variables** for an arbitrary map `φ`: with the divided
difference `[F; φ(x), φ(x+2ε)]` in place of `F' ∘ φ`. -/
theorem change_of_variables (ε : K) (hε : ε ≠ 0) (F φ : K → K) (a : K) (n : ℕ) :
    QE.gint ε (fun x => (F (φ (x + 2 * ε)) - F (φ x)) / (φ (x + 2 * ε) - φ x)
        * QE.Dp ε φ x) a n
      = F (φ (a + 2 * ε * n)) - F (φ a) := by
  have h := granular_ftc ε hε (fun x => F (φ x)) a n
  rw [← h]
  unfold QE.gint
  apply sum_congr rfl; intro k _
  congr 1
  unfold QE.Dp
  beta_reduce
  by_cases huv : φ (a + 2 * ε * k + 2 * ε) - φ (a + 2 * ε * k) = 0
  · have : φ (a + 2 * ε * k + 2 * ε) = φ (a + 2 * ε * k) := sub_eq_zero.mp huv
    rw [this]; simp
  · field_simp

/-! ### Falling powers and the granular power rule -/

lemma fall_succ (ε x : K) (k : ℕ) :
    QE.fall ε (x + 2 * ε) (k + 1) = QE.fall ε x (k + 1) + 2 * ε * (k + 1) * QE.fall ε x k := by
  unfold QE.fall
  rw [prod_range_succ' (fun j => x + 2 * ε - 2 * ε * j), prod_range_succ]
  simp only [Nat.cast_add, Nat.cast_one, Nat.cast_zero, mul_zero, sub_zero]
  have : ∏ j ∈ range k, (x + 2 * ε - 2 * ε * ((j : K) + 1)) = ∏ j ∈ range k, (x - 2 * ε * j) := by
    apply prod_congr rfl; intro j _; ring
  rw [this]; ring

lemma fall_zero_succ (ε : K) (k : ℕ) : QE.fall ε 0 (k + 1) = 0 := by
  unfold QE.fall; rw [prod_range_succ']; simp

/-- The granular power rule for falling powers: `∫_{[0,b)} x^{(k)} = b^{(k+1)}/(k+1)`. -/
theorem gint_fall (ε : K) (hε : ε ≠ 0) (k n : ℕ) :
    QE.gint ε (fun x => QE.fall ε x k) 0 n = QE.fall ε (2 * ε * n) (k + 1) / (k + 1) := by
  have hk : (k + 1 : K) ≠ 0 := by positivity
  have h := granular_ftc ε hε (fun x => QE.fall ε x (k + 1) / (k + 1)) 0 n
  have e : QE.Dp ε (fun x => QE.fall ε x (k + 1) / (k + 1)) = fun x => QE.fall ε x k := by
    funext x; unfold QE.Dp; beta_reduce; rw [fall_succ]; field_simp; ring
  rw [e] at h
  rw [h, fall_zero_succ, zero_add]; simp

lemma fall_centre (ε : K) (n k : ℕ) :
    QE.fall ε (2 * ε * n) k = (2 * ε) ^ k * (n.descFactorial k : K) := by
  induction k with
  | zero => simp [QE.fall]
  | succ k ih =>
    unfold QE.fall at *
    rw [prod_range_succ, ih, Nat.descFactorial_succ]
    rcases le_or_gt k n with h | h
    · push_cast [h]; ring
    · have : n - k = 0 := by omega
      rw [this]
      have h0 : n.descFactorial k = 0 := Nat.descFactorial_eq_zero_iff_lt.mpr h
      simp [h0]

/-- **Euler–Maclaurin for monomials, exactly** (Faulhaber with Bernoulli numbers):
`∫_{[0,b)} x^p = ∑_{i ≤ p} B_i C(p+1,i) (2ε)^i b^{p+1-i} / (p+1)`, `b = 2εn`. -/
theorem gint_pow (ε : K) (p n : ℕ) :
    QE.gint ε (fun x => x ^ p) 0 n
      = ∑ i ∈ range (p + 1), (bernoulli i : K) * ((p + 1).choose i : K)
          * (2 * ε) ^ i * (2 * ε * n) ^ (p + 1 - i) / (p + 1) := by
  have h := congrArg (fun q : ℚ => (q : K)) (sum_range_pow n p)
  push_cast at h
  have lhs : QE.gint ε (fun x => x ^ p) 0 n = (2 * ε) ^ (p + 1) * ∑ k ∈ range n, (k : K) ^ p := by
    unfold QE.gint; rw [mul_sum]; apply sum_congr rfl; intro k _; ring
  rw [lhs, h, mul_sum]
  apply sum_congr rfl
  intro i hi
  have hi' : i ≤ p + 1 := by have := mem_range.mp hi; omega
  have e : (2 * ε) ^ (p + 1) = (2 * ε) ^ i * (2 * ε) ^ (p + 1 - i) := by
    rw [← pow_add, Nat.add_sub_cancel' hi']
  rw [e, mul_pow]; ring

/-- **Euler–Maclaurin is exact for cubics**:
`∫_{[a,b)} f = ∫_a^b f - ε (f(b) - f(a)) + (ε²/3) (f'(b) - f'(a))`. -/
theorem euler_maclaurin_cubic (ε : K) (c₀ c₁ c₂ c₃ a : K) (n : ℕ) :
    let f : K → K := fun x => c₀ + c₁ * x + c₂ * x ^ 2 + c₃ * x ^ 3
    let f' : K → K := fun x => c₁ + 2 * c₂ * x + 3 * c₃ * x ^ 2
    let F : K → K := fun x => c₀ * x + c₁ * x ^ 2 / 2 + c₂ * x ^ 3 / 3 + c₃ * x ^ 4 / 4
    QE.gint ε f a n = (F (a + 2 * ε * n) - F a) - ε * (f (a + 2 * ε * n) - f a)
        + ε ^ 2 / 3 * (f' (a + 2 * ε * n) - f' a) := by
  intro f f' F
  induction n with
  | zero => simp [QE.gint]
  | succ n ih =>
    unfold QE.gint at *
    rw [sum_range_succ, ih]
    simp only [f, f', F]
    push_cast; ring

/-- **Richardson extrapolation across two granules** (Simpson's rule): for cubic `f`,
combining the trapezoid sums at granules `ε` and `2ε` gives the classical integral
exactly. -/
theorem simpson_cubic (ε : K) (c₀ c₁ c₂ c₃ a : K) (m : ℕ) :
    let f : K → K := fun x => c₀ + c₁ * x + c₂ * x ^ 2 + c₃ * x ^ 3
    let F : K → K := fun x => c₀ * x + c₁ * x ^ 2 / 2 + c₂ * x ^ 3 / 3 + c₃ * x ^ 4 / 4
    let b : K := a + 4 * ε * m
    (4 * (QE.gint ε f a (2 * m) + ε * (f b - f a))
      - (QE.gint (2 * ε) f a m + 2 * ε * (f b - f a))) / 3 = F b - F a := by
  intro f F b
  have h1 := euler_maclaurin_cubic ε c₀ c₁ c₂ c₃ a (2 * m)
  have h2 := euler_maclaurin_cubic (2 * ε) c₀ c₁ c₂ c₃ a m
  simp only [] at h1 h2
  simp only [f, F, b]
  rw [h1, h2]
  push_cast
  ring

/-! ### Granular Gamma function -/

/-- The truncated granular Gamma integral
`Γ_ε^{(N)}(k+1) = ∑_{j<N} (2εj)^{(k)} (1+2ε)^{-(j+1)} · 2ε`, i.e. the granular
integral of `x^{(k)} / e_ε(x + 2ε)` over `[0, 2εN)`. -/
def gammaG (ε : K) (k N : ℕ) : K :=
  ∑ j ∈ range N, QE.fall ε (2 * ε * j) k * (1 + 2 * ε)⁻¹ ^ (j + 1) * (2 * ε)

theorem gammaG_zero (ε : K) (hε : 0 < ε) (N : ℕ) :
    gammaG ε 0 N = 1 - (1 + 2 * ε)⁻¹ ^ N := by
  have h1 : (1 + 2 * ε) ≠ 0 := by positivity
  induction N with
  | zero => simp [gammaG]
  | succ N ih =>
    unfold gammaG at *
    rw [sum_range_succ, ih]
    simp only [QE.fall, prod_range_zero, one_mul]
    rw [pow_succ]; field_simp; ring

/-- **Exact recursion with boundary term** (granular integration by parts):
`Γ_ε^{(N)}(k+2) = (k+1) Γ_ε^{(N)}(k+1) - (2εN)^{(k+1)} (1+2ε)^{-N}`. -/
theorem gammaG_succ (ε : K) (hε : 0 < ε) (k N : ℕ) :
    gammaG ε (k + 1) N
      = (k + 1) * gammaG ε k N - QE.fall ε (2 * ε * N) (k + 1) * (1 + 2 * ε)⁻¹ ^ N := by
  have h1 : (1 + 2 * ε) ≠ 0 := by positivity
  induction N with
  | zero => simp [gammaG, fall_zero_succ]
  | succ N ih =>
    unfold gammaG at *
    rw [sum_range_succ, sum_range_succ, ih]
    have e : 2 * ε * ((N + 1 : ℕ) : K) = 2 * ε * N + 2 * ε := by push_cast; ring
    rw [e, fall_succ]
    rw [pow_succ]
    field_simp
    ring

/-- **Closed form at finite horizon** `Ω = 2εN`:
`Γ_ε^{(N)}(k+1) = k! - (1+2ε)^{-N} ∑_{j ≤ k} (k!/j!) Ω^{(j)}`. -/
theorem gammaG_closed (ε : K) (hε : 0 < ε) (k N : ℕ) :
    gammaG ε k N = (k.factorial : K) - (1 + 2 * ε)⁻¹ ^ N *
      ∑ j ∈ range (k + 1), (k.factorial : K) / (j.factorial : K) * QE.fall ε (2 * ε * N) j := by
  induction k with
  | zero => rw [gammaG_zero ε hε]; simp [QE.fall]
  | succ k ih =>
    rw [gammaG_succ ε hε, ih, sum_range_succ (n := k + 1)]
    have hf : ((k + 1).factorial : K) = (k + 1) * (k.factorial : K) := by
      push_cast [Nat.factorial_succ]; ring
    have hf0 : ((k + 1).factorial : K) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
    rw [div_self hf0, hf]
    have e1 : ∑ x ∈ range (k + 1), (k + 1 : K) * (k.factorial : K) / (x.factorial : K)
          * QE.fall ε (2 * ε * N) x
        = (k + 1) * ∑ x ∈ range (k + 1), (k.factorial : K) / (x.factorial : K)
          * QE.fall ε (2 * ε * N) x := by
      rw [mul_sum]; apply sum_congr rfl; intro x _; ring
    rw [e1]; ring

end Algebra

/-- The horizon factor is exponentially small: `(1+2ε)^{-N} ≤ exp(-2εN/(1+2ε))`. -/
theorem pow_inv_le_exp (ε : ℝ) (hε : 0 < ε) (N : ℕ) :
    (1 + 2 * ε)⁻¹ ^ N ≤ Real.exp (-(2 * ε * N) / (1 + 2 * ε)) := by
  have h1 : (0 : ℝ) < 1 + 2 * ε := by linarith
  have hq : (1 + 2 * ε)⁻¹ ≤ Real.exp (-(2 * ε) / (1 + 2 * ε)) := by
    have := Real.add_one_le_exp (-(2 * ε) / (1 + 2 * ε))
    have e : -(2 * ε) / (1 + 2 * ε) + 1 = (1 + 2 * ε)⁻¹ := by field_simp; ring
    linarith
  calc (1 + 2 * ε)⁻¹ ^ N ≤ Real.exp (-(2 * ε) / (1 + 2 * ε)) ^ N :=
        pow_le_pow_left₀ (by positivity) hq N
    _ = Real.exp (-(2 * ε * N) / (1 + 2 * ε)) := by
        rw [← Real.exp_nat_mul]; congr 1; ring

section Algebra2

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-! ### Principal values -/

/-- An odd function sums to `0` over a symmetric run of lattice points. -/
theorem sum_odd_symm (ε : K) (g : K → K) (hg : ∀ x, g (-x) = -g x) (n : ℕ) :
    ∑ k ∈ Icc (-(n : ℤ)) n, g (2 * ε * k) * (2 * ε) = 0 := by
  set S := ∑ k ∈ Icc (-(n : ℤ)) n, g (2 * ε * k) * (2 * ε)
  have hS : S = -S := by
    have : S = ∑ k ∈ Icc (-(n : ℤ)) n, g (2 * ε * ((-k : ℤ) : K)) * (2 * ε) := by
      apply sum_nbij' (fun k => -k) (fun k => -k)
      · intro k hk; simp only [mem_Icc] at hk ⊢; omega
      · intro k hk; simp only [mem_Icc] at hk ⊢; omega
      · intro k _; simp
      · intro k _; simp
      · intro k _; simp
    conv_lhs => rw [this]
    rw [← sum_neg_distrib]
    apply sum_congr rfl; intro k _
    push_cast
    rw [show 2 * ε * -(k : K) = -(2 * ε * k) by ring, hg]; ring
  linarith

/-- **Cauchy principal value, automatically**: `∫ dx/x` over a symmetric run is
exactly `0` (the point `0` contributes nothing since its value is taken as `0`;
equivalently, it is excluded). -/
theorem pv_inv (ε : K) (n : ℕ) :
    ∑ k ∈ Icc (-(n : ℤ)) n, (2 * ε * k)⁻¹ * (2 * ε) = 0 :=
  sum_odd_symm ε (fun x => x⁻¹) (fun x => by simp [inv_neg]) n

/-- The same integral over the half-open run `[-A, A)`, `A = 2εn`: the missing
endpoint carries exactly `-1/n`. -/
theorem pv_inv_halfopen (ε : K) (hε : ε ≠ 0) (n : ℕ) (hn : 0 < n) :
    ∑ k ∈ Ico (-(n : ℤ)) n, (2 * ε * k)⁻¹ * (2 * ε) = -1 / n := by
  have h := pv_inv ε n
  have hsplit : Icc (-(n : ℤ)) n = insert (n : ℤ) (Ico (-(n : ℤ)) n) := by
    ext k; simp only [mem_Icc, mem_insert, mem_Ico]; omega
  rw [hsplit, sum_insert (by simp)] at h
  have hnK : (n : K) ≠ 0 := by exact_mod_cast hn.ne'
  have : ((n : ℤ) : K) = (n : K) := by norm_cast
  rw [this] at h
  have e : (2 * ε * n)⁻¹ * (2 * ε) = 1 / n := by field_simp
  rw [e] at h
  rw [neg_div]; linarith

/-! ### Dirichlet's function on a lattice -/

/-- If the integrand equals `1` at every lattice point of the run, its granular
integral is the length of the run. -/
theorem gint_eq_length (ε : K) (f : K → K) (a : K) (n : ℕ)
    (h : ∀ k < n, f (a + 2 * ε * k) = 1) : QE.gint ε f a n = 2 * ε * n := by
  rw [show 2 * ε * (n : K) = 1 * (2 * ε * n) by ring, ← gint_const ε 1 a n]
  unfold QE.gint
  apply sum_congr rfl; intro k hk; rw [h k (mem_range.mp hk)]

/-- If the integrand vanishes at every lattice point of the run, its granular
integral is `0`. -/
theorem gint_eq_zero (ε : K) (f : K → K) (a : K) (n : ℕ)
    (h : ∀ k < n, f (a + 2 * ε * k) = 0) : QE.gint ε f a n = 0 := by
  unfold QE.gint
  apply sum_eq_zero; intro k hk; rw [h k (mem_range.mp hk)]; simp

/-! ### Taylor's theorem with granular integral remainder -/

/-- Iterated forward granular derivative (local copy). -/
def Dpk (ε : K) (k : ℕ) (f : K → K) : K → K := (QE.Dp ε)^[k] f

lemma Dpk_succ_shift (ε : K) (hε : ε ≠ 0) (k : ℕ) (f : K → K) (x : K) :
    Dpk ε k f (x + 2 * ε) = Dpk ε k f x + 2 * ε * Dpk ε (k + 1) f x := by
  have : Dpk ε (k + 1) f = QE.Dp ε (Dpk ε k f) := by
    simp only [Dpk]; rw [Function.iterate_succ_apply']
  rw [this]; unfold QE.Dp; field_simp; ring

/-- One step of the Taylor telescope. -/
lemma taylor_step (ε : K) (hε : ε ≠ 0) (f : K → K) (x : K) (M : ℕ) :
    ∀ m : ℕ,
    (∑ k ∈ range (m + 1), (M.choose k : K) * (2 * ε) ^ k * Dpk ε k f (x + 2 * ε))
      - ∑ k ∈ range (m + 1), ((M + 1).choose k : K) * (2 * ε) ^ k * Dpk ε k f x
      = (M.choose m : K) * (2 * ε) ^ (m + 1) * Dpk ε (m + 1) f x := by
  intro m
  induction m with
  | zero =>
    simp only [zero_add, range_one, sum_singleton, Nat.choose_zero_right, Nat.cast_one,
      pow_zero, one_mul, pow_one]
    rw [Dpk_succ_shift ε hε]; ring
  | succ m ih =>
    rw [sum_range_succ, sum_range_succ (n := m + 1)]
    have hpas : ((M + 1).choose (m + 1) : K) = (M.choose m : K) + (M.choose (m + 1) : K) := by
      rw [Nat.choose_succ_succ]; push_cast; ring
    rw [hpas, Dpk_succ_shift ε hε (m + 1)]
    have := ih
    linear_combination this

/-- **Taylor's theorem with granular integral remainder** (exact, for every `f`):
`f(a + 2εn) = ∑_{k<m} C(n,k)(2ε)^k D^k f(a) + ∑_{j<n} C(n-1-j, m-1) (2ε)^m D^m f(a+2εj)`. -/
theorem taylor_remainder (ε : K) (hε : ε ≠ 0) (f : K → K) (a : K) (m n : ℕ) :
    f (a + 2 * ε * n)
      = ∑ k ∈ range (m + 1), (n.choose k : K) * (2 * ε) ^ k * Dpk ε k f a
        + ∑ j ∈ range n, ((n - 1 - j).choose m : K) * (2 * ε) ^ (m + 1)
            * Dpk ε (m + 1) f (a + 2 * ε * j) := by
  set R : ℕ → K := fun j =>
    ∑ k ∈ range (m + 1), ((n - j).choose k : K) * (2 * ε) ^ k * Dpk ε k f (a + 2 * ε * j)
    with hR
  have htel := sum_range_sub R n
  have hRn : R n = f (a + 2 * ε * n) := by
    simp only [hR, Nat.sub_self]
    rw [sum_eq_single 0]
    · simp [Dpk]
    · intro k _ hk; rw [Nat.choose_eq_zero_of_lt (by omega)]; simp
    · intro h; simp at h
  have hR0 : R 0 = ∑ k ∈ range (m + 1), (n.choose k : K) * (2 * ε) ^ k * Dpk ε k f a := by
    simp [hR]
  have hstep : ∀ j ∈ range n, R (j + 1) - R j
      = ((n - 1 - j).choose m : K) * (2 * ε) ^ (m + 1) * Dpk ε (m + 1) f (a + 2 * ε * j) := by
    intro j hj
    have hj' := mem_range.mp hj
    obtain ⟨M, hM⟩ : ∃ M, n - j = M + 1 := ⟨n - j - 1, by omega⟩
    have h1 : n - (j + 1) = M := by omega
    have h2 : n - 1 - j = M := by omega
    simp only [hR, h1, hM, h2]
    have e : a + 2 * ε * ((j + 1 : ℕ) : K) = a + 2 * ε * j + 2 * ε := by push_cast; ring
    rw [e]
    exact taylor_step ε hε f (a + 2 * ε * j) M m
  rw [sum_congr rfl hstep] at htel
  rw [htel, hRn, hR0]; ring

/-! ### Granular Stieltjes integrals and quadratic covariation -/

/-- Left-point (Itô) granular Stieltjes integral `∑_{k<n} f(x_k) (g(x_{k+1}) - g(x_k))`. -/
def stL (ε : K) (f g : K → K) (a : K) (n : ℕ) : K :=
  ∑ k ∈ range n, f (a + 2 * ε * k) * (g (a + 2 * ε * (k + 1)) - g (a + 2 * ε * k))

/-- Right-point granular Stieltjes integral. -/
def stR (ε : K) (f g : K → K) (a : K) (n : ℕ) : K :=
  ∑ k ∈ range n, f (a + 2 * ε * (k + 1)) * (g (a + 2 * ε * (k + 1)) - g (a + 2 * ε * k))

/-- Quadratic covariation `[f, g] = ∑ Δf Δg` over the run. -/
def qcov (ε : K) (f g : K → K) (a : K) (n : ℕ) : K :=
  ∑ k ∈ range n, (f (a + 2 * ε * (k + 1)) - f (a + 2 * ε * k))
    * (g (a + 2 * ε * (k + 1)) - g (a + 2 * ε * k))

/-- Right minus left is the quadratic covariation, exactly. -/
theorem stR_sub_stL (ε : K) (f g : K → K) (a : K) (n : ℕ) :
    stR ε f g a n - stL ε f g a n = qcov ε f g a n := by
  unfold stR stL qcov; rw [← sum_sub_distrib]; apply sum_congr rfl; intro k _; ring

/-- Integration by parts for granular Stieltjes integrals. -/
theorem stL_add_stR (ε : K) (f g : K → K) (a : K) (n : ℕ) :
    stL ε f g a n + stR ε g f a n
      = f (a + 2 * ε * n) * g (a + 2 * ε * n) - f a * g a := by
  unfold stL stR
  induction n with
  | zero => simp
  | succ n ih =>
    rw [sum_range_succ, sum_range_succ]
    have e : ((n + 1 : ℕ) : K) = (n : K) + 1 := by push_cast; ring
    rw [e]
    linear_combination ih

/-- **Exact Itô formula for squares**: `∫ f df (left point) = ½(f(b)² - f(a)²) - ½[f,f]`. -/
theorem ito_square (ε : K) (f : K → K) (a : K) (n : ℕ) :
    stL ε f f a n = (f (a + 2 * ε * n) ^ 2 - f a ^ 2) / 2 - qcov ε f f a n / 2 := by
  have h1 := stL_add_stR ε f f a n
  have h2 := stR_sub_stL ε f f a n
  linear_combination h1 / 2 - h2 / 2

/-! ### `∫ H dH`: three conventions, three exact answers -/

/-- The Heaviside step, closed at `0`. -/
def heav (x : K) : K := if 0 ≤ x then 1 else 0

lemma Dp_heav (ε : K) (hε : 0 < ε) (k : ℤ) :
    QE.Dp ε heav (2 * ε * k) = if k = -1 then 1 / (2 * ε) else 0 := by
  unfold QE.Dp heav
  have h2 : (0 : K) < 2 * ε := by positivity
  have e1 : 2 * ε * (k : K) + 2 * ε = 2 * ε * ((k + 1 : ℤ) : K) := by push_cast; ring
  rw [e1]
  have p1 : (0 ≤ 2 * ε * (k : K)) ↔ 0 ≤ k := by
    rw [mul_nonneg_iff_of_pos_left h2]; exact_mod_cast Iff.rfl
  have p2 : (0 ≤ 2 * ε * ((k + 1 : ℤ) : K)) ↔ 0 ≤ k + 1 := by
    rw [mul_nonneg_iff_of_pos_left h2]; exact_mod_cast Iff.rfl
  simp only [p1, p2]
  rcases lt_trichotomy k (-1) with hk | hk | hk
  · have a : ¬ 0 ≤ k := by omega
    have b : ¬ 0 ≤ k + 1 := by omega
    have c : k ≠ -1 := by omega
    simp only [a, b, c, ite_false]; simp
  · subst hk; norm_num
  · have a : 0 ≤ k := by omega
    have b : 0 ≤ k + 1 := by omega
    have c : k ≠ -1 := by omega
    simp only [a, b, c, ite_true, ite_false]; simp

/-- Left-point (Itô) evaluation: `∫ H dH = 0`. -/
theorem int_H_dH_left (ε : K) (hε : 0 < ε) (n : ℕ) (hn : 1 ≤ n) :
    ∑ k ∈ Icc (-(n : ℤ)) n, heav (2 * ε * k) * QE.Dp ε heav (2 * ε * k) * (2 * ε) = 0 := by
  rw [sum_eq_single (-1 : ℤ)]
  · have h0 : heav (2 * ε * ((-1 : ℤ) : K)) = 0 := by
      unfold heav; push_cast
      split_ifs with h
      · nlinarith
      · rfl
    rw [h0]; ring
  · intro k _ hk; rw [Dp_heav ε hε]; simp [hk]
  · intro h; exfalso; apply h; simp only [mem_Icc]; omega

/-- Right-point (anticipating) evaluation: `∫ H dH = 1`. -/
theorem int_H_dH_right (ε : K) (hε : 0 < ε) (n : ℕ) (hn : 1 ≤ n) :
    ∑ k ∈ Icc (-(n : ℤ)) n, heav (2 * ε * k + 2 * ε) * QE.Dp ε heav (2 * ε * k) * (2 * ε) = 1 := by
  have h2 : (0 : K) < 2 * ε := by positivity
  rw [sum_eq_single (-1 : ℤ)]
  · rw [Dp_heav ε hε]; simp only [↓reduceIte]
    have : (0 : K) ≤ 2 * ε * ((-1 : ℤ) : K) + 2 * ε := by push_cast; linarith
    simp only [heav, this, ite_true]; field_simp
  · intro k _ hk; rw [Dp_heav ε hε]; simp [hk]
  · intro h; exfalso; apply h; simp only [mem_Icc]; omega

/-- Midpoint (Stratonovich) evaluation: `∫ ½(H + S H) dH = ½`. -/
theorem int_H_dH_mid (ε : K) (hε : 0 < ε) (n : ℕ) (hn : 1 ≤ n) :
    ∑ k ∈ Icc (-(n : ℤ)) n, (heav (2 * ε * k) + heav (2 * ε * k + 2 * ε)) / 2
      * QE.Dp ε heav (2 * ε * k) * (2 * ε) = 1 / 2 := by
  have hl := int_H_dH_left ε hε n hn
  have hr := int_H_dH_right ε hε n hn
  have : ∑ k ∈ Icc (-(n : ℤ)) n, (heav (2 * ε * k) + heav (2 * ε * k + 2 * ε)) / 2
      * QE.Dp ε heav (2 * ε * k) * (2 * ε)
      = (∑ k ∈ Icc (-(n : ℤ)) n, heav (2 * ε * k) * QE.Dp ε heav (2 * ε * k) * (2 * ε)
        + ∑ k ∈ Icc (-(n : ℤ)) n, heav (2 * ε * k + 2 * ε) * QE.Dp ε heav (2 * ε * k) * (2 * ε))
        / 2 := by
    rw [← sum_add_distrib, sum_div]; apply sum_congr rfl; intro k _; ring
  rw [this, hl, hr]; ring

/-! ### Two granulations compared (Lebesgue-free Cauchy estimates) -/

/-- **Refinement estimate** (granular, Lebesgue-free).  Compare the granular
integral over `m n` cells of the granule `ε` with the one over `n` cells of the
coarser granule `m ε` (same run `[a, a + 2εmn)`).  If on every coarse cell the
fine samples differ from the coarse sample by at most `η`, the two integrals
differ by at most `η (b - a)`. -/
theorem gint_refine (ε : K) (hε : 0 ≤ ε) (f : K → K) (a : K) (m n : ℕ) (η : K)
    (hb : ∀ k < n, ∀ j < m,
      |f (a + 2 * ε * ((m : K) * k + j)) - f (a + 2 * ε * ((m : K) * k))| ≤ η) :
    |QE.gint ε f a (m * n) - QE.gint ((m : K) * ε) f a n| ≤ η * (2 * ε * ((m : K) * n)) := by
  induction n with
  | zero => simp [QE.gint]
  | succ n ih =>
    have hblock : QE.gint ε f a (m * (n + 1)) = QE.gint ε f a (m * n)
        + ∑ j ∈ range m, f (a + 2 * ε * ((m : K) * n + j)) * (2 * ε) := by
      rw [show m * (n + 1) = m * n + m by ring, gint_add_runs]
      congr 1; unfold QE.gint; apply sum_congr rfl; intro j _
      congr 2; push_cast; ring
    have hc : QE.gint ((m : K) * ε) f a (n + 1) = QE.gint ((m : K) * ε) f a n
        + ∑ _j ∈ range m, f (a + 2 * ε * ((m : K) * n)) * (2 * ε) := by
      unfold QE.gint
      rw [sum_range_succ, sum_const, card_range, nsmul_eq_mul]
      congr 1
      rw [show (2 * ((m : K) * ε) * (n : K)) = 2 * ε * ((m : K) * n) by ring]; ring
    rw [hblock, hc]
    have hd : |∑ j ∈ range m, f (a + 2 * ε * ((m : K) * n + j)) * (2 * ε)
        - ∑ _j ∈ range m, f (a + 2 * ε * ((m : K) * n)) * (2 * ε)| ≤ m * (η * (2 * ε)) := by
      rw [← sum_sub_distrib]
      refine (abs_sum_le_sum_abs _ _).trans ?_
      calc _ ≤ ∑ _j ∈ range m, η * (2 * ε) := sum_le_sum (fun j hj => by
              rw [← sub_mul, abs_mul, abs_of_nonneg (by linarith : (0 : K) ≤ 2 * ε)]
              exact mul_le_mul_of_nonneg_right (hb n (by omega) j (mem_range.mp hj)) (by linarith))
        _ = _ := by rw [sum_const, card_range, nsmul_eq_mul]
    have ih' := ih (fun k hk j hj => hb k (by omega) j hj)
    have e : QE.gint ε f a (m * n) + ∑ j ∈ range m, f (a + 2 * ε * ((m : K) * n + j)) * (2 * ε)
        - (QE.gint ((m : K) * ε) f a n + ∑ _j ∈ range m, f (a + 2 * ε * ((m : K) * n)) * (2 * ε))
        = (QE.gint ε f a (m * n) - QE.gint ((m : K) * ε) f a n)
          + (∑ j ∈ range m, f (a + 2 * ε * ((m : K) * n + j)) * (2 * ε)
            - ∑ _j ∈ range m, f (a + 2 * ε * ((m : K) * n)) * (2 * ε)) := by ring
    rw [e]
    calc _ ≤ _ := abs_add_le _ _
      _ ≤ η * (2 * ε * ((m : K) * n)) + m * (η * (2 * ε)) := add_le_add ih' hd
      _ = _ := by push_cast; ring

lemma sum_range_cast_two (m : ℕ) : (∑ j ∈ range m, (j : K)) * 2 = m * ((m : K) - 1) := by
  induction m with
  | zero => simp
  | succ m ih => rw [sum_range_succ, add_mul, ih]; push_cast; ring

/-- **Refinement estimate for Lipschitz integrands** (granular, Lebesgue-free):
`|∫_{[a,b)} f dₑx - ∫_{[a,b)} f d_{mε}x| ≤ L (m - 1) ε (b - a)`.  For `m = 2`
(one halving of the granule) the two granulations differ by at most
`L ε (b - a)`; summing the geometric series over successive halvings is the
granular Cauchy criterion behind the Riemann shadow. -/
theorem gint_refine_lipschitz (ε : K) (hε : 0 ≤ ε) (f : K → K) (L : K)
    (hL : ∀ x y, |f x - f y| ≤ L * |x - y|) (a : K) (m n : ℕ) :
    |QE.gint ε f a (m * n) - QE.gint ((m : K) * ε) f a n|
      ≤ L * ((m : K) - 1) * ε * (2 * ε * ((m : K) * n)) := by
  induction n with
  | zero => simp [QE.gint]
  | succ n ih =>
    have hblock : QE.gint ε f a (m * (n + 1)) = QE.gint ε f a (m * n)
        + ∑ j ∈ range m, f (a + 2 * ε * ((m : K) * n + j)) * (2 * ε) := by
      rw [show m * (n + 1) = m * n + m by ring, gint_add_runs]
      congr 1; unfold QE.gint; apply sum_congr rfl; intro j _
      congr 2; push_cast; ring
    have hc : QE.gint ((m : K) * ε) f a (n + 1) = QE.gint ((m : K) * ε) f a n
        + ∑ _j ∈ range m, f (a + 2 * ε * ((m : K) * n)) * (2 * ε) := by
      unfold QE.gint
      rw [sum_range_succ, sum_const, card_range, nsmul_eq_mul]
      congr 1
      rw [show (2 * ((m : K) * ε) * (n : K)) = 2 * ε * ((m : K) * n) by ring]; ring
    rw [hblock, hc]
    have hd : |∑ j ∈ range m, f (a + 2 * ε * ((m : K) * n + j)) * (2 * ε)
        - ∑ _j ∈ range m, f (a + 2 * ε * ((m : K) * n)) * (2 * ε)|
          ≤ L * (2 * ε) ^ 2 * ∑ j ∈ range m, (j : K) := by
      rw [← sum_sub_distrib]
      refine (abs_sum_le_sum_abs _ _).trans ?_
      rw [mul_sum]
      refine sum_le_sum (fun j _ => ?_)
      rw [← sub_mul, abs_mul, abs_of_nonneg (by linarith : (0 : K) ≤ 2 * ε)]
      have h1 := hL (a + 2 * ε * ((m : K) * n + j)) (a + 2 * ε * ((m : K) * n))
      have h2 : |a + 2 * ε * ((m : K) * n + j) - (a + 2 * ε * ((m : K) * n))| = 2 * ε * j := by
        rw [show a + 2 * ε * ((m : K) * n + j) - (a + 2 * ε * ((m : K) * n)) = 2 * ε * j by ring]
        exact abs_of_nonneg (by positivity)
      rw [h2] at h1
      calc _ ≤ L * (2 * ε * j) * (2 * ε) :=
            mul_le_mul_of_nonneg_right h1 (by linarith)
        _ = _ := by ring
    have ih' := ih
    have hs := sum_range_cast_two (K := K) m
    have e : QE.gint ε f a (m * n) + ∑ j ∈ range m, f (a + 2 * ε * ((m : K) * n + j)) * (2 * ε)
        - (QE.gint ((m : K) * ε) f a n + ∑ _j ∈ range m, f (a + 2 * ε * ((m : K) * n)) * (2 * ε))
        = (QE.gint ε f a (m * n) - QE.gint ((m : K) * ε) f a n)
          + (∑ j ∈ range m, f (a + 2 * ε * ((m : K) * n + j)) * (2 * ε)
            - ∑ _j ∈ range m, f (a + 2 * ε * ((m : K) * n)) * (2 * ε)) := by ring
    rw [e]
    calc _ ≤ _ := abs_add_le _ _
      _ ≤ L * ((m : K) - 1) * ε * (2 * ε * ((m : K) * n))
            + L * (2 * ε) ^ 2 * ∑ j ∈ range m, (j : K) := add_le_add ih' hd
      _ = L * ((m : K) - 1) * ε * (2 * ε * ((m : K) * n))
            + L * (2 * ε ^ 2) * ((∑ j ∈ range m, (j : K)) * 2) := by ring
      _ = _ := by rw [hs]; push_cast; ring

/-- **Partial sums of the power divergence** (granular, Lebesgue-free): for the
run `(0, 2εN]`, `(3/2 - 1/(N+1))/(2ε) ≤ ∑_{k=1}^{N} (2εk)⁻² 2ε ≤ (2 - 1/N)/(2ε)`.
The `1/ε` divergence and its coefficient window `[1, 2]` follow by
telescoping, without any value of `ζ(2)`. -/
theorem inv_sq_partial_bounds (N : ℕ) (hN : 1 ≤ N) :
    (3 : K) / 2 - 1 / ((N : K) + 1) ≤ ∑ k ∈ Ico 1 (N + 1), 1 / ((k : K)) ^ 2 ∧
    ∑ k ∈ Ico 1 (N + 1), 1 / ((k : K)) ^ 2 ≤ 2 - 1 / (N : K) := by
  induction N, hN using Nat.le_induction with
  | base => norm_num
  | succ N hN ih =>
    rw [sum_Ico_succ_top (by omega)]
    obtain ⟨h1, h2⟩ := ih
    have hN' : (1 : K) ≤ N := by exact_mod_cast hN
    push_cast
    have hp : (0 : K) < N := by linarith
    constructor
    · have : 1 / ((N : K) + 1) - 1 / ((N : K) + 1 + 1) ≤ 1 / ((N : K) + 1) ^ 2 := by
        rw [div_sub_div _ _ (by positivity) (by positivity),
          div_le_div_iff₀ (by positivity) (by positivity)]
        nlinarith
      linarith
    · have : 1 / ((N : K) + 1) ^ 2 ≤ 1 / (N : K) - 1 / ((N : K) + 1) := by
        rw [div_sub_div _ _ (by positivity) (by positivity),
          div_le_div_iff₀ (by positivity) (by positivity)]
        nlinarith
      linarith

theorem gint_inv_sq_partial (ε : K) (hε : 0 < ε) (N : ℕ) (hN : 1 ≤ N) :
    ((3 : K) / 2 - 1 / ((N : K) + 1)) / (2 * ε)
        ≤ ∑ k ∈ Ico 1 (N + 1), (1 / (2 * ε * k) ^ 2) * (2 * ε) ∧
    ∑ k ∈ Ico 1 (N + 1), (1 / (2 * ε * k) ^ 2) * (2 * ε) ≤ (2 - 1 / (N : K)) / (2 * ε) := by
  have e : ∑ k ∈ Ico 1 (N + 1), (1 / (2 * ε * k) ^ 2) * (2 * ε)
      = (∑ k ∈ Ico 1 (N + 1), 1 / ((k : K)) ^ 2) / (2 * ε) := by
    rw [sum_div]; apply sum_congr rfl; intro k hk
    have hk0 : (k : K) ≠ 0 := by
      have := (mem_Ico.mp hk).1; exact_mod_cast (by omega : k ≠ 0)
    field_simp
  obtain ⟨h1, h2⟩ := inv_sq_partial_bounds (K := K) N hN
  have h2e : (0 : K) < 2 * ε := by linarith
  rw [e]
  exact ⟨div_le_div_of_nonneg_right h1 h2e.le, div_le_div_of_nonneg_right h2 h2e.le⟩

end Algebra2

/-! ## Real-variable results -/

section RealAnalysis

open Real Filter Topology Set intervalIntegral MeasureTheory

/-- Dirichlet's function: `1` on the rationals, `0` elsewhere. -/
noncomputable def dirichlet (x : ℝ) : ℝ := by
  classical exact if ∃ q : ℚ, (q : ℝ) = x then 1 else 0

/-- On a rational lattice (rational base point and granule) the granular integral of
Dirichlet's function over `[a, b)` is `b - a`. -/
theorem gint_dirichlet_rat (ε a : ℚ) (n : ℕ) :
    QE.gint (ε : ℝ) dirichlet (a : ℝ) n = 2 * (ε : ℝ) * n := by
  apply gint_eq_length
  intro k _
  unfold dirichlet
  split_ifs with h
  · rfl
  · exact absurd ⟨a + 2 * ε * k, by push_cast; ring⟩ h

/-- On an irrationally shifted lattice the same integral is `0`: the granular
integral of a nowhere-continuous function depends on the lattice. -/
theorem gint_dirichlet_irrat (ε : ℚ) (a : ℝ) (ha : Irrational a) (n : ℕ) :
    QE.gint (ε : ℝ) dirichlet a n = 0 := by
  apply gint_eq_zero
  intro k _
  unfold dirichlet
  split_ifs with h
  · exfalso
    obtain ⟨q, hq⟩ := h
    apply ha
    refine ⟨q - 2 * ε * k, ?_⟩
    push_cast; rw [hq]; ring
  · rfl

/-- **Shadow (classical comparison).** The cell estimate behind all
Riemann-sum shadows (uses the interval integral as the lossy target). -/
lemma cell_bound (f g : ℝ → ℝ) (x h : ℝ) (hh : 0 ≤ h) (hf : Continuous f)
    (hg : IntervalIntegrable g volume x (x + h))
    (hb : ∀ t ∈ Ioc x (x + h), |f t - f x| ≤ g t) :
    |(∫ t in x..x + h, f t) - f x * h| ≤ ∫ t in x..x + h, g t := by
  have e : (∫ t in x..x + h, f t) - f x * h = ∫ t in x..x + h, (f t - f x) := by
    rw [integral_sub (hf.intervalIntegrable _ _) intervalIntegrable_const]
    rw [intervalIntegral.integral_const]; simp; ring
  rw [e]
  have := norm_integral_le_of_norm_le (μ := volume) (f := fun t => f t - f x)
    (by linarith : x ≤ x + h) (Eventually.of_forall (fun t ht => by
      simpa [Real.norm_eq_abs] using hb t ht)) hg
  simpa [Real.norm_eq_abs] using this

/-- **Shadow (classical comparison).** Uniform cell bound summed over a run. -/
theorem gint_sub_integral_le (ε : ℝ) (hε : 0 < ε) (f : ℝ → ℝ) (hf : Continuous f)
    (a : ℝ) (n : ℕ) (η : ℝ)
    (hb : ∀ k < n, ∀ t ∈ Ioc (a + 2 * ε * k) (a + 2 * ε * k + 2 * ε),
      |f t - f (a + 2 * ε * k)| ≤ η) :
    |QE.gint ε f a n - ∫ t in a..a + 2 * ε * n, f t| ≤ η * (2 * ε * n) := by
  set x : ℕ → ℝ := fun k => a + 2 * ε * k with hx
  have hsum := sum_integral_adjacent_intervals (μ := volume) (f := f) (a := x) (n := n)
    (fun k _ => hf.intervalIntegrable _ _)
  have hx0 : x 0 = a := by simp [hx]
  rw [hx0] at hsum
  rw [← hsum]
  unfold QE.gint
  rw [← sum_sub_distrib]
  refine (abs_sum_le_sum_abs _ _).trans ?_
  have : η * (2 * ε * n) = ∑ k ∈ range n, η * (2 * ε) := by
    rw [sum_const, card_range, nsmul_eq_mul]; ring
  rw [this]
  apply sum_le_sum
  intro k hk
  have hk' := mem_range.mp hk
  have hxk : x (k + 1) = x k + 2 * ε := by simp [hx]; ring
  rw [hxk, abs_sub_comm]
  show |(∫ t in x k..x k + 2 * ε, f t) - f (x k) * (2 * ε)| ≤ η * (2 * ε)
  have := cell_bound f (fun _ => η) (x k) (2 * ε) (by positivity) hf intervalIntegrable_const
    (fun t ht => hb k hk' t ht)
  refine this.trans (le_of_eq ?_)
  rw [intervalIntegral.integral_const, smul_eq_mul]; ring

/-- **Shadow (classical comparison): explicit bound for Lipschitz integrands**:
`|∫_{[a,b)} f - ∫_a^b f| ≤ L ε (b - a)`. -/
theorem gint_lipschitz (ε : ℝ) (hε : 0 < ε) (f : ℝ → ℝ) (L : ℝ)
    (hL : ∀ x y, |f x - f y| ≤ L * |x - y|) (a : ℝ) (n : ℕ) :
    |QE.gint ε f a n - ∫ t in a..a + 2 * ε * n, f t| ≤ L * ε * (2 * ε * n) := by
  have hL0 : 0 ≤ L := by
    have := hL 1 0; simp at this; linarith [abs_nonneg (f 1 - f 0)]
  have hf : Continuous f := by
    apply continuous_iff_continuousAt.mpr
    intro x
    rw [Metric.continuousAt_iff]
    intro η hη
    refine ⟨η / (L + 1), by positivity, fun y hy => ?_⟩
    rw [Real.dist_eq] at hy ⊢
    calc |f y - f x| ≤ L * |y - x| := hL y x
      _ ≤ L * (η / (L + 1)) := by gcongr
      _ < η := by rw [mul_div_assoc', div_lt_iff₀ (by positivity)]; nlinarith
  set x : ℕ → ℝ := fun k => a + 2 * ε * k with hx
  have hsum := sum_integral_adjacent_intervals (μ := volume) (f := f) (a := x) (n := n)
    (fun k _ => hf.intervalIntegrable _ _)
  have hx0 : x 0 = a := by simp [hx]
  rw [hx0] at hsum
  rw [← hsum]
  unfold QE.gint
  rw [← sum_sub_distrib]
  refine (abs_sum_le_sum_abs _ _).trans ?_
  have : L * ε * (2 * ε * n) = ∑ k ∈ range n, L * (2 * ε) ^ 2 / 2 := by
    rw [sum_const, card_range, nsmul_eq_mul]; ring
  rw [this]
  apply sum_le_sum
  intro k _
  have hxk : x (k + 1) = x k + 2 * ε := by simp [hx]; ring
  rw [hxk, abs_sub_comm]
  show |(∫ t in x k..x k + 2 * ε, f t) - f (x k) * (2 * ε)| ≤ L * (2 * ε) ^ 2 / 2
  have hg : IntervalIntegrable (fun t => L * (t - x k)) volume (x k) (x k + 2 * ε) :=
    (continuous_const.mul (continuous_id.sub continuous_const)).intervalIntegrable _ _
  have := cell_bound f (fun t => L * (t - x k)) (x k) (2 * ε) (by positivity) hf hg
    (fun t ht => by
      have := hL t (x k)
      rwa [abs_of_nonneg (by linarith [ht.1] : 0 ≤ t - x k)] at this)
  have hint : ∫ t in x k..x k + 2 * ε, L * (t - x k) = L * (2 * ε) ^ 2 / 2 := by
    rw [intervalIntegral.integral_const_mul, integral_comp_sub_right (fun t => t), integral_id]
    ring
  rw [hint] at this
  exact this

/-- **Shadow theorem for continuous integrands**: with `n` cells of length
`(b - a)/n` (granule `ε_n = (b-a)/(2n)`), the granular integrals converge to the
Riemann integral. -/
theorem gint_shadow (f : ℝ → ℝ) (hf : Continuous f) (a b : ℝ) (hab : a < b) :
    Tendsto (fun n : ℕ => QE.gint ((b - a) / (2 * n)) f a n) atTop
      (𝓝 (∫ t in a..b, f t)) := by
  rw [Metric.tendsto_atTop]
  intro η hη
  have huc := (isCompact_Icc (a := a) (b := b)).uniformContinuousOn_of_continuous
    hf.continuousOn
  rw [Metric.uniformContinuousOn_iff] at huc
  obtain ⟨δ, hδ, hδf⟩ := huc (η / (2 * (b - a))) (div_pos hη (by linarith))
  obtain ⟨N, hN⟩ := exists_nat_gt ((b - a) / δ)
  refine ⟨N + 1, fun n hn => ?_⟩
  have hn0 : (0 : ℝ) < n := by
    have : 0 < n := by omega
    exact_mod_cast this
  set ε := (b - a) / (2 * n) with hεdef
  have hε : 0 < ε := by rw [hεdef]; apply div_pos (by linarith) (by positivity)
  have hbn : a + 2 * ε * n = b := by rw [hεdef]; field_simp; ring
  have hcell : 2 * ε < δ := by
    have h1 : (b - a) / δ < n := by
      have : (N : ℝ) + 1 ≤ n := by exact_mod_cast hn
      linarith
    rw [div_lt_iff₀ hδ] at h1
    rw [hεdef, show 2 * ((b - a) / (2 * n)) = (b - a) / n by field_simp]
    rw [div_lt_iff₀ hn0]; linarith
  have key := gint_sub_integral_le ε hε f hf a n (η / (2 * (b - a))) (by
    intro k hk t ht
    have hk' : (k : ℝ) + 1 ≤ n := by exact_mod_cast hk
    have hxk : a + 2 * ε * k ∈ Icc a b := by
      constructor
      · have : (0 : ℝ) ≤ k := Nat.cast_nonneg k; nlinarith
      · rw [← hbn]; nlinarith
    have ht' : t ∈ Icc a b := by
      constructor
      · linarith [ht.1, hxk.1]
      · rw [← hbn]
        have : t ≤ a + 2 * ε * k + 2 * ε := ht.2
        nlinarith
    have hd : dist t (a + 2 * ε * k) < δ := by
      rw [Real.dist_eq, abs_of_pos (by linarith [ht.1])]; linarith [ht.2]
    have := hδf t ht' (a + 2 * ε * k) hxk hd
    rw [Real.dist_eq] at this
    exact this.le)
  rw [hbn] at key
  rw [Real.dist_eq]
  calc |QE.gint ε f a n - ∫ t in a..b, f t| ≤ η / (2 * (b - a)) * (2 * ε * n) := key
    _ = η / 2 := by rw [show 2 * ε * n = b - a by linarith]; field_simp
    _ < η := by linarith

/-! ### Divergent integrals become explicit: `∫_0^1 dx/x` -/

/-- The granular integral of `1/x` over the open run `(0, 1)`, `1 = 2εn`, is the
harmonic number `H_{n-1}`. -/
theorem gint_inv_harmonic (ε : ℝ) (hε : 0 < ε) (n : ℕ) :
    ∑ k ∈ Ico 1 n, (2 * ε * k)⁻¹ * (2 * ε) = (harmonic (n - 1) : ℝ) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rcases Nat.eq_zero_or_pos n with h | h
    · subst h; simp
    · rw [sum_Ico_succ_top (by omega), ih]
      rw [show n + 1 - 1 = (n - 1) + 1 by omega, harmonic_succ, Nat.sub_add_cancel h]
      have : (n : ℝ) ≠ 0 := by exact_mod_cast h.ne'
      push_cast
      field_simp

/-- **Intrinsic regularisation**: with `2ε = 1/n`,
`∫_{(0,1)} dx/x - ln(1/(2ε)) → γ` (Euler–Mascheroni). -/
theorem gint_inv_sub_log :
    Tendsto (fun n : ℕ => (∑ k ∈ Ico 1 n, (2 * (1 / (2 * (n : ℝ))) * k)⁻¹ * (2 * (1 / (2 * n))))
      - log n) atTop (𝓝 eulerMascheroniConstant) := by
  have h1 := tendsto_harmonic_sub_log.sub (tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ))
  rw [sub_zero] at h1
  refine h1.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with n hn
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  rw [gint_inv_harmonic _ (by positivity) n]
  have e : harmonic n = harmonic (n - 1) + (n : ℚ)⁻¹ := by
    conv_lhs => rw [show n = (n - 1) + 1 by omega]
    rw [harmonic_succ, Nat.sub_add_cancel hn]
  rw [e]; push_cast; ring

/-- The truncated granular Gamma integral tends to `k!` as the horizon grows:
`Γ_ε(k+1) = k!` exactly, for every granule `ε > 0`. -/
theorem gammaG_tendsto (ε : ℝ) (hε : 0 < ε) (k : ℕ) :
    Tendsto (fun N => gammaG ε k N) atTop (𝓝 (k.factorial : ℝ)) := by
  have hq0 : (0 : ℝ) ≤ (1 + 2 * ε)⁻¹ := by positivity
  have hq1 : (1 + 2 * ε)⁻¹ < 1 := inv_lt_one_of_one_lt₀ (by linarith)
  have hqN := tendsto_pow_atTop_nhds_zero_of_lt_one hq0 hq1
  induction k with
  | zero =>
    have : Tendsto (fun N => 1 - (1 + 2 * ε)⁻¹ ^ N) atTop (𝓝 (1 - 0)) :=
      tendsto_const_nhds.sub hqN
    simp only [sub_zero] at this
    simpa [gammaG_zero ε hε] using this
  | succ k ih =>
    have hb : Tendsto (fun N : ℕ => QE.fall ε (2 * ε * N) (k + 1) * (1 + 2 * ε)⁻¹ ^ N)
        atTop (𝓝 0) := by
      have hup : Tendsto (fun N : ℕ => (2 * ε) ^ (k + 1) * ((N : ℝ) ^ (k + 1) * (1 + 2 * ε)⁻¹ ^ N))
          atTop (𝓝 ((2 * ε) ^ (k + 1) * 0)) :=
        tendsto_const_nhds.mul (tendsto_pow_const_mul_const_pow_of_abs_lt_one (k + 1)
          (by rw [abs_of_nonneg hq0]; exact hq1))
      rw [mul_zero] at hup
      apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hup
      · intro N; simp only [fall_centre]; positivity
      · intro N
        simp only [fall_centre]
        have : ((N.descFactorial (k + 1) : ℕ) : ℝ) ≤ (N : ℝ) ^ (k + 1) := by
          exact_mod_cast Nat.descFactorial_le_pow N (k + 1)
        have h2 : (0 : ℝ) ≤ (2 * ε) ^ (k + 1) := by positivity
        have h3 : (0 : ℝ) ≤ (1 + 2 * ε)⁻¹ ^ N := by positivity
        calc (2 * ε) ^ (k + 1) * ((N.descFactorial (k + 1) : ℕ) : ℝ) * (1 + 2 * ε)⁻¹ ^ N
            ≤ (2 * ε) ^ (k + 1) * (N : ℝ) ^ (k + 1) * (1 + 2 * ε)⁻¹ ^ N := by gcongr
          _ = _ := by ring
    have := (tendsto_const_nhds (x := ((k : ℝ) + 1))).mul ih |>.sub hb
    rw [sub_zero] at this
    have e : ((k + 1).factorial : ℝ) = ((k : ℝ) + 1) * (k.factorial : ℝ) := by
      push_cast [Nat.factorial_succ]; ring
    rw [e]
    refine this.congr' ?_
    filter_upwards with N
    rw [gammaG_succ ε hε k N]

/-- **Shadow (classical comparison): granular Gaussian sum vs `√π`**
(Poisson summation; the proof goes through the continuum Fourier transform):
`∑_{x ∈ 2εℤ} e^{-x²} 2ε = √π ∑_{k ∈ ℤ} e^{-π² k² / (4ε²)}`; the granular value
exceeds `√π` only by terms of order `e^{-π²/(4ε²)}`. -/
theorem gauss_sum (ε : ℝ) (hε : 0 < ε) :
    (∑' k : ℤ, exp (-(2 * ε * k) ^ 2) * (2 * ε))
      = √π * ∑' k : ℤ, exp (-(π ^ 2 / (4 * ε ^ 2)) * (k : ℝ) ^ 2) := by
  have ha : 0 < 4 * ε ^ 2 / π := by positivity
  have h := Real.tsum_exp_neg_mul_int_sq ha
  have e1 : ∀ k : ℤ, -π * (4 * ε ^ 2 / π) * (k : ℝ) ^ 2 = -(2 * ε * k) ^ 2 := by
    intro k; field_simp; ring
  have e2 : ∀ k : ℤ, -π / (4 * ε ^ 2 / π) * (k : ℝ) ^ 2 = -(π ^ 2 / (4 * ε ^ 2)) * (k : ℝ) ^ 2 := by
    intro k; field_simp
  simp only [e1, e2] at h
  rw [tsum_mul_right, h]
  have hs : (4 * ε ^ 2 / π) ^ (1 / 2 : ℝ) = 2 * ε / √π := by
    rw [← sqrt_eq_rpow, sqrt_div' _ pi_pos.le, sqrt_mul' _ (sq_nonneg _), sqrt_sq hε.le]
    rw [show √(4 : ℝ) = 2 by rw [show (4 : ℝ) = 2 ^ 2 by norm_num, sqrt_sq (by norm_num)]]
  rw [hs]
  have hpi : 0 < √π := sqrt_pos.mpr pi_pos
  field_simp

/-- **Shadow (classical value of the constant)**: over the infinite lattice `(0, ∞)`,
`∑_{x ∈ 2εℕ, x > 0} x⁻² · 2ε = π²/(12 ε)`. -/
theorem gint_inv_sq (ε : ℝ) (hε : 0 < ε) :
    HasSum (fun k : ℕ => (1 / (2 * ε * k) ^ 2) * (2 * ε)) (π ^ 2 / (12 * ε)) := by
  have h := hasSum_zeta_two.mul_right (1 / (2 * ε))
  convert h using 1
  · funext k
    rcases Nat.eq_zero_or_pos k with hk | hk
    · subst hk; simp
    · have : (k : ℝ) ≠ 0 := by exact_mod_cast hk.ne'
      field_simp
  · field_simp; ring

end RealAnalysis

end QE.Integral
