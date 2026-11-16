-- SPDX-License-Identifier: MIT
-- Copyright 2026 Metere Industries, Inc. Author: Alfredo Metere.
-- Quasi-Euclidean Granular Geometry. Any derivative work must carry this notice:
--   This work is derivative of the Quasi-Euclidean Granular Geometry book
--   authored by Alfredo Metere. Copyright 2026 Metere Industries, Inc.
--   All rights reserved
-- See LICENSE.md and NOTICE.

import QuasiEuclidean.Basic

/-!
# Chapter 4: Granular differential calculus

All results are exact identities or inequalities valid for every `ε > 0`
(or `ε ≠ 0`) in an arbitrary linearly ordered field `K`; the book's
infinitesimal setting is the instance `K := Hyperreal`, and the physical
setting is `K := ℝ`, `ε = ℓ_P`.  Shadow (standard-part) statements are proved
over `ℝ` as limit statements `ε → 0⁺`.
-/

open Finset

set_option linter.unusedSectionVars false

namespace QE.Diff

section Algebra

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-- The shift operator `S f (x) = f (x + 2ε)`. -/
def Sh (ε : K) (f : K → K) (x : K) : K := f (x + 2 * ε)

/-- Two-point average across the poles of the point-sphere at `x`. -/
def Av (ε : K) (f : K → K) (x : K) : K := (f (x + ε) + f (x - ε)) / 2

/-- The shift is `1 + 2ε D⁺`. -/
theorem Sh_eq (ε : K) (hε : ε ≠ 0) (f : K → K) (x : K) :
    Sh ε f x = f x + 2 * ε * QE.Dp ε f x := by
  unfold Sh QE.Dp; field_simp; ring

/-- Linearity of `D⁺`. -/
theorem Dp_add (ε : K) (f g : K → K) (x : K) :
    QE.Dp ε (fun y => f y + g y) x = QE.Dp ε f x + QE.Dp ε g x := by
  unfold QE.Dp; ring

theorem Dp_smul (ε c : K) (f : K → K) (x : K) :
    QE.Dp ε (fun y => c * f y) x = c * QE.Dp ε f x := by
  unfold QE.Dp; ring

theorem Dp_const (ε c : K) (x : K) : QE.Dp ε (fun _ => c) x = 0 := by
  unfold QE.Dp; simp

theorem Dp_id (ε : K) (hε : ε ≠ 0) (x : K) : QE.Dp ε (fun y => y) x = 1 := by
  unfold QE.Dp; field_simp; ring

theorem Dm_add (ε : K) (f g : K → K) (x : K) :
    QE.Dm ε (fun y => f y + g y) x = QE.Dm ε f x + QE.Dm ε g x := by
  unfold QE.Dm; ring

theorem Dc_add (ε : K) (f g : K → K) (x : K) :
    QE.Dc ε (fun y => f y + g y) x = QE.Dc ε f x + QE.Dc ε g x := by
  unfold QE.Dc; ring

/-- `D⁻` at `x` is `D⁺` at `x - 2ε`. -/
theorem Dm_eq_Dp (ε : K) (f : K → K) (x : K) :
    QE.Dm ε f x = QE.Dp ε f (x - 2 * ε) := by
  unfold QE.Dm QE.Dp; ring_nf

/-- The arithmetic mean of `D⁺` and `D⁻` is the central difference of step `2ε`. -/
theorem Dp_add_Dm (ε : K) (hε : ε ≠ 0) (f : K → K) (x : K) :
    (QE.Dp ε f x + QE.Dm ε f x) / 2 = (f (x + 2 * ε) - f (x - 2 * ε)) / (4 * ε) := by
  unfold QE.Dp QE.Dm; field_simp; ring

/-- `D⁺ - D⁻` is `2ε` times the second difference quotient. -/
theorem Dp_sub_Dm (ε : K) (hε : ε ≠ 0) (f : K → K) (x : K) :
    QE.Dp ε f x - QE.Dm ε f x
      = 2 * ε * ((f (x + 2 * ε) - 2 * f x + f (x - 2 * ε)) / (2 * ε) ^ 2) := by
  unfold QE.Dp QE.Dm; field_simp; ring

/-- Granular Leibniz rule (exact, with its `2ε` cross term). -/
theorem Dp_mul (ε : K) (hε : ε ≠ 0) (f g : K → K) (x : K) :
    QE.Dp ε (fun y => f y * g y) x
      = QE.Dp ε f x * g x + f x * QE.Dp ε g x + 2 * ε * (QE.Dp ε f x * QE.Dp ε g x) := by
  unfold QE.Dp; field_simp; ring

/-- Leibniz rule in shifted (two-term) form. -/
theorem Dp_mul_shift (ε : K) (hε : ε ≠ 0) (f g : K → K) (x : K) :
    QE.Dp ε (fun y => f y * g y) x = QE.Dp ε f x * Sh ε g x + f x * QE.Dp ε g x := by
  unfold QE.Dp Sh; field_simp; ring

/-- Backward Leibniz rule: the cross term enters with a minus sign. -/
theorem Dm_mul (ε : K) (hε : ε ≠ 0) (f g : K → K) (x : K) :
    QE.Dm ε (fun y => f y * g y) x
      = QE.Dm ε f x * g x + f x * QE.Dm ε g x - 2 * ε * (QE.Dm ε f x * QE.Dm ε g x) := by
  unfold QE.Dm; field_simp; ring

/-- Central Leibniz rule: exact with pole averages, no cross term. -/
theorem Dc_mul (ε : K) (hε : ε ≠ 0) (f g : K → K) (x : K) :
    QE.Dc ε (fun y => f y * g y) x = QE.Dc ε f x * Av ε g x + Av ε f x * QE.Dc ε g x := by
  unfold QE.Dc Av; field_simp; ring

/-- Central Leibniz rule in point-value form: the cross term is of second order. -/
theorem Dc_mul' (ε : K) (hε : ε ≠ 0) (f g : K → K) (x : K) :
    QE.Dc ε (fun y => f y * g y) x
      = QE.Dc ε f x * g x + f x * QE.Dc ε g x
        + QE.Dc ε f x * (Av ε g x - g x) + (Av ε f x - f x) * QE.Dc ε g x := by
  rw [Dc_mul ε hε]; ring

/-- The `2ε` correction for squares: `D⁺(f²) = 2 f D⁺f + 2ε (D⁺f)²`. -/
theorem Dp_sq (ε : K) (hε : ε ≠ 0) (f : K → K) (x : K) :
    QE.Dp ε (fun y => f y ^ 2) x = 2 * f x * QE.Dp ε f x + 2 * ε * QE.Dp ε f x ^ 2 := by
  unfold QE.Dp; field_simp; ring

/-- Granular quotient rule. -/
theorem Dp_div (ε : K) (hε : ε ≠ 0) (f g : K → K) (x : K)
    (hg : g x ≠ 0) (hg' : g (x + 2 * ε) ≠ 0) :
    QE.Dp ε (fun y => f y / g y) x
      = (QE.Dp ε f x * g x - f x * QE.Dp ε g x) / (g x * Sh ε g x) := by
  unfold QE.Dp Sh; field_simp; ring

/-- Divided difference `[f; u, v]` (Mathlib's `slope`, which is `0` when `u = v`). -/
def ddiff (f : K → K) (u v : K) : K := (f v - f u) / (v - u)

lemma ddiff_mul (f : K → K) (u v : K) : ddiff f u v * (v - u) = f v - f u := by
  unfold ddiff
  by_cases h : v - u = 0
  · have : v = u := sub_eq_zero.mp h
    subst this; simp
  · field_simp

/-- Exact granular chain rule: the outer derivative is the divided difference of
`f` over the image of the cell. -/
theorem Dp_comp (ε : K) (f g : K → K) (x : K) :
    QE.Dp ε (fun y => f (g y)) x = ddiff f (g x) (g (x + 2 * ε)) * QE.Dp ε g x := by
  unfold QE.Dp
  rw [← mul_div_assoc, ddiff_mul]

/-- **Granular inverse function rule**: if `g ∘ f = id`, the divided difference of
`g` over the image of a cell is the reciprocal of `D⁺ f`. -/
theorem inverse_rule (ε : K) (hε : ε ≠ 0) (f g : K → K) (hgf : ∀ x, g (f x) = x) (x : K) :
    ddiff g (f x) (f (x + 2 * ε)) * QE.Dp ε f x = 1 := by
  rw [← Dp_comp]
  have : (fun y => g (f y)) = fun y => y := funext hgf
  rw [this, Dp_id ε hε]

/-- Falling power at the next lattice point. -/
lemma fall_shift (ε x : K) (k : ℕ) :
    QE.fall ε (x + 2 * ε) (k + 1) = (x + 2 * ε) * QE.fall ε x k := by
  unfold QE.fall
  rw [prod_range_succ']
  simp only [Nat.cast_add, Nat.cast_one, Nat.cast_zero, mul_zero, sub_zero]
  rw [mul_comm]
  congr 1
  apply prod_congr rfl
  intro j _; ring

/-- Newton's rule for granular falling powers: `D⁺ x^{(k+1)} = (k+1) x^{(k)}`. -/
theorem Dp_fall (ε : K) (hε : ε ≠ 0) (k : ℕ) (x : K) :
    QE.Dp ε (fun y => QE.fall ε y (k + 1)) x = (k + 1) * QE.fall ε x k := by
  unfold QE.Dp
  beta_reduce
  rw [fall_shift]
  have : QE.fall ε x (k + 1) = QE.fall ε x k * (x - 2 * ε * k) := by
    unfold QE.fall; rw [prod_range_succ]
  rw [this]; field_simp; ring

/-- Falling powers evaluated at lattice points: `(2εn)^{(k)} = (2ε)^k n(n-1)⋯(n-k+1)`. -/
theorem fall_centre (ε : K) (n k : ℕ) :
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

/-- Iterated forward granular derivative. -/
def Dpk (ε : K) (k : ℕ) (f : K → K) : K → K := (QE.Dp ε)^[k] f

lemma Dpk_eq_fwdDiff (ε : K) (hε : ε ≠ 0) (k : ℕ) (f : K → K) (x : K) :
    Dpk ε k f x = (fwdDiff (2 * ε))^[k] f x / (2 * ε) ^ k := by
  induction k generalizing x with
  | zero => simp [Dpk]
  | succ k ih =>
    have h1 : Dpk ε (k + 1) f = QE.Dp ε (Dpk ε k f) := by
      simp only [Dpk]; rw [Function.iterate_succ_apply']
    rw [h1, Function.iterate_succ_apply']
    unfold QE.Dp
    rw [ih, ih]
    simp only [fwdDiff]
    field_simp
    ring

/-- **Newton's forward-difference formula** (the exact granular Taylor theorem):
`f(x + 2εn) = ∑_{k ≤ n} C(n,k) (2ε)^k (D⁺)^k f(x)`. -/
theorem newton_series (ε : K) (hε : ε ≠ 0) (f : K → K) (x : K) (n : ℕ) :
    f (x + 2 * ε * n) = ∑ k ∈ range (n + 1), (n.choose k : K) * (2 * ε) ^ k * Dpk ε k f x := by
  have h := shift_eq_sum_fwdDiff_iter (2 * ε) f n x
  have e : x + 2 * ε * n = x + n • (2 * ε) := by rw [nsmul_eq_mul]; ring
  rw [e, h]
  apply sum_congr rfl
  intro k _
  rw [Dpk_eq_fwdDiff ε hε, nsmul_eq_mul]
  have : (2 * ε) ^ k ≠ 0 := pow_ne_zero _ (mul_ne_zero two_ne_zero hε)
  field_simp

/-- Newton's series in falling-power (Taylor) form:
`f(x + t) = ∑_{k ≤ n} (D⁺)^k f(x) · t^{(k)} / k!` for `t = 2εn`. -/
theorem newton_taylor (ε : K) (hε : ε ≠ 0) (f : K → K) (x : K) (n : ℕ) :
    f (x + 2 * ε * n)
      = ∑ k ∈ range (n + 1), Dpk ε k f x * QE.fall ε (2 * ε * n) k / (k.factorial : K) := by
  rw [newton_series ε hε f x n]
  apply sum_congr rfl
  intro k _
  rw [fall_centre, Nat.descFactorial_eq_factorial_mul_choose]
  have : (k.factorial : K) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero k
  push_cast
  field_simp

/-- Exact discrete fundamental identity used throughout: the sum of `D⁺ f · 2ε`
over `n` consecutive cells telescopes. -/
lemma sum_Dp (ε : K) (hε : ε ≠ 0) (f : K → K) (a : K) (n : ℕ) :
    ∑ k ∈ range n, QE.Dp ε f (a + 2 * ε * k) * (2 * ε) = f (a + 2 * ε * n) - f a := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [sum_range_succ, ih]
    unfold QE.Dp
    have : a + 2 * ε * ((n : K)) + 2 * ε = a + 2 * ε * ((n + 1 : ℕ) : K) := by push_cast; ring
    rw [this]; field_simp; ring

/-- **Granular mean value theorem**: on a run of `n ≥ 1` cells there is a lattice
point where `D⁺ f` is at least the mean slope, and one where it is at most. -/
theorem mvt (ε : K) (hε : 0 < ε) (f : K → K) (a : K) (n : ℕ) (hn : 0 < n) :
    (∃ k ∈ range n, (f (a + 2 * ε * n) - f a) / (2 * ε * n) ≤ QE.Dp ε f (a + 2 * ε * k)) ∧
    (∃ k ∈ range n, QE.Dp ε f (a + 2 * ε * k) ≤ (f (a + 2 * ε * n) - f a) / (2 * ε * n)) := by
  have hne : (range n).Nonempty := nonempty_range_iff.mpr (by omega)
  have h2 : (2 * ε) ≠ 0 := by positivity
  have hnK : (n : K) ≠ 0 := by exact_mod_cast hn.ne'
  have hsum : ∑ k ∈ range n, QE.Dp ε f (a + 2 * ε * k)
      = ∑ _k ∈ range n, (f (a + 2 * ε * n) - f a) / (2 * ε * n) := by
    rw [sum_const, card_range, nsmul_eq_mul, ← sum_Dp ε hε.ne' f a n, ← sum_mul]
    field_simp
  constructor
  · exact exists_le_of_sum_le hne hsum.ge
  · exact exists_le_of_sum_le hne hsum.le

/-- **Monotonicity criterion**: if `D⁺ f ≥ 0` on the cells of a run, `f` is
nondecreasing along the lattice points of the run. -/
theorem mono_of_Dp_nonneg (ε : K) (hε : 0 < ε) (f : K → K) (a : K) (n : ℕ)
    (h : ∀ k < n, 0 ≤ QE.Dp ε f (a + 2 * ε * k)) :
    ∀ i j, i ≤ j → j ≤ n → f (a + 2 * ε * i) ≤ f (a + 2 * ε * j) := by
  intro i j hij hjn
  have key : f (a + 2 * ε * j) - f (a + 2 * ε * i)
      = ∑ k ∈ Finset.Ico i j, QE.Dp ε f (a + 2 * ε * k) * (2 * ε) := by
    rw [Finset.sum_Ico_eq_sub _ hij, sum_Dp ε hε.ne', sum_Dp ε hε.ne']; ring
  have : 0 ≤ ∑ k ∈ Finset.Ico i j, QE.Dp ε f (a + 2 * ε * k) * (2 * ε) := by
    apply sum_nonneg
    intro k hk
    have hk' : k < n := by simp at hk; omega
    exact mul_nonneg (h k hk') (by positivity)
  linarith

/-- Strict monotonicity criterion. -/
theorem strictMono_of_Dp_pos (ε : K) (hε : 0 < ε) (f : K → K) (a : K) (n : ℕ)
    (h : ∀ k < n, 0 < QE.Dp ε f (a + 2 * ε * k)) :
    ∀ i j, i < j → j ≤ n → f (a + 2 * ε * i) < f (a + 2 * ε * j) := by
  intro i j hij hjn
  have key : f (a + 2 * ε * j) - f (a + 2 * ε * i)
      = ∑ k ∈ Finset.Ico i j, QE.Dp ε f (a + 2 * ε * k) * (2 * ε) := by
    rw [Finset.sum_Ico_eq_sub _ hij.le, sum_Dp ε hε.ne', sum_Dp ε hε.ne']; ring
  have : 0 < ∑ k ∈ Finset.Ico i j, QE.Dp ε f (a + 2 * ε * k) * (2 * ε) := by
    apply sum_pos
    · intro k hk
      have hk' : k < n := by simp at hk; omega
      exact mul_pos (h k hk') (by positivity)
    · exact ⟨i, by simp [hij]⟩
  linarith

/-- Converse: nondecreasing on the lattice implies `D⁺ f ≥ 0`. -/
theorem Dp_nonneg_of_le (ε : K) (hε : 0 < ε) (f : K → K) (x : K)
    (h : f x ≤ f (x + 2 * ε)) : 0 ≤ QE.Dp ε f x := by
  unfold QE.Dp; apply div_nonneg <;> linarith

/-- **Granular Fermat rule**: at a lattice local maximum, `D⁺ f ≤ 0 ≤ D⁻ f`. -/
theorem fermat_max (ε : K) (hε : 0 < ε) (f : K → K) (x : K)
    (h1 : f (x + 2 * ε) ≤ f x) (h2 : f (x - 2 * ε) ≤ f x) :
    QE.Dp ε f x ≤ 0 ∧ 0 ≤ QE.Dm ε f x := by
  unfold QE.Dp QE.Dm
  constructor
  · apply div_nonpos_of_nonpos_of_nonneg <;> linarith
  · apply div_nonneg <;> linarith

/-- Granular Fermat rule at a minimum. -/
theorem fermat_min (ε : K) (hε : 0 < ε) (f : K → K) (x : K)
    (h1 : f x ≤ f (x + 2 * ε)) (h2 : f x ≤ f (x - 2 * ε)) :
    QE.Dm ε f x ≤ 0 ∧ 0 ≤ QE.Dp ε f x := by
  unfold QE.Dp QE.Dm
  constructor
  · apply div_nonpos_of_nonpos_of_nonneg <;> linarith
  · apply div_nonneg <;> linarith

/-- Second-difference test: `D⁺ D⁻ f (x) < 0` together with `D⁺ f (x) ≤ 0 ≤ D⁻ f(x)`
characterises nothing more than the lattice local maximum; we record the exact
identity `D⁺ f - D⁻ f = 2ε D⁺D⁻ f`. -/
theorem Dp_sub_Dm_eq (ε : K) (hε : ε ≠ 0) (f : K → K) (x : K) :
    QE.Dp ε f x - QE.Dm ε f x = 2 * ε * QE.Dp ε (QE.Dm ε f) x := by
  unfold QE.Dp QE.Dm; field_simp; ring_nf

/-! ### The kink of `|x|` and the Heaviside step -/

/-- `|x|` at `0`: `D⁺ = 1`. -/
theorem Dp_abs_zero (ε : K) (hε : 0 < ε) : QE.Dp ε (fun x => |x|) 0 = 1 := by
  unfold QE.Dp; beta_reduce
  rw [zero_add, abs_of_pos (by positivity), abs_zero, sub_zero, div_self (by positivity)]

/-- `|x|` at `0`: `D⁻ = -1`. -/
theorem Dm_abs_zero (ε : K) (hε : 0 < ε) : QE.Dm ε (fun x => |x|) 0 = -1 := by
  unfold QE.Dm; beta_reduce
  have h : |2 * ε| = 2 * ε := abs_of_pos (by positivity)
  have h2 : (2 * ε) ≠ 0 := by positivity
  simp only [zero_sub, abs_neg, abs_zero, h]
  field_simp

/-- `|x|` at `0`: `D° = 0`. -/
theorem Dc_abs_zero (ε : K) : QE.Dc ε (fun x => |x|) 0 = 0 := by
  unfold QE.Dc; simp

/-- Away from the kink `|x|` has the classical derivative exactly. -/
theorem Dp_abs_pos (ε : K) (hε : 0 < ε) (x : K) (hx : 0 ≤ x) :
    QE.Dp ε (fun x => |x|) x = 1 := by
  unfold QE.Dp; beta_reduce
  rw [abs_of_nonneg (by positivity), abs_of_nonneg hx]
  field_simp; ring

/-- The Heaviside step (closed at `0`). -/
def heaviside (x : K) : K := if 0 ≤ x then 1 else 0

/-- The granular Dirac delta: the indicator of the point `0` divided by its length. -/
def delta (ε : K) (x : K) : K := if x = 0 then 1 / (2 * ε) else 0

/-- `D⁻ H` on the lattice is exactly the granular delta at the point `0`. -/
theorem Dm_heaviside (ε : K) (hε : 0 < ε) (k : ℤ) :
    QE.Dm ε heaviside (2 * ε * k) = delta ε (2 * ε * k) := by
  unfold QE.Dm heaviside delta
  have h2 : (0 : K) < 2 * ε := by positivity
  have e1 : 2 * ε * (k : K) - 2 * ε = 2 * ε * ((k - 1 : ℤ) : K) := by push_cast; ring
  rw [e1]
  have p1 : (0 ≤ 2 * ε * (k : K)) ↔ 0 ≤ k := by
    rw [mul_nonneg_iff_of_pos_left h2]; exact_mod_cast Iff.rfl
  have p2 : (0 ≤ 2 * ε * ((k - 1 : ℤ) : K)) ↔ 0 ≤ k - 1 := by
    rw [mul_nonneg_iff_of_pos_left h2]; exact_mod_cast Iff.rfl
  have p3 : (2 * ε * (k : K) = 0) ↔ k = 0 := by
    rw [mul_eq_zero, or_iff_right h2.ne']; exact_mod_cast Iff.rfl
  simp only [p1, p2, p3]
  rcases lt_trichotomy k 0 with hk | hk | hk
  · have a : ¬ 0 ≤ k := by omega
    have b : ¬ 0 ≤ k - 1 := by omega
    have c : k ≠ 0 := by omega
    simp only [a, b, c, ite_false]; simp
  · subst hk; norm_num
  · have a : 0 ≤ k := by omega
    have b : 0 ≤ k - 1 := by omega
    have c : k ≠ 0 := by omega
    simp only [a, b, c, ite_true, ite_false]; simp

/-- `D⁺ H` on the lattice is the granular delta carried by the point `-2ε`. -/
theorem Dp_heaviside (ε : K) (hε : 0 < ε) (k : ℤ) :
    QE.Dp ε heaviside (2 * ε * k) = delta ε (2 * ε * (k + 1)) := by
  have := Dm_heaviside ε hε (k + 1)
  rw [Dm_eq_Dp] at this
  push_cast at this
  rw [← this]; congr 1; ring

/-- `D° H` on the lattice is the granular delta at `0`, whatever value is assigned
to `H(0)`: the poles `x ± ε` of a lattice point never sit on the jump. -/
theorem Dc_heaviside (ε : K) (hε : 0 < ε) (c : K) (k : ℤ) :
    QE.Dc ε (fun x => if x = 0 then c else heaviside x) (2 * ε * k) = delta ε (2 * ε * k) := by
  unfold QE.Dc heaviside delta
  beta_reduce
  have h2 : (0 : K) < 2 * ε := by positivity
  have hne1 : 2 * ε * (k : K) + ε ≠ 0 := by
    intro h
    have : (2 * (k : K) + 1) * ε = 0 := by linarith
    rcases mul_eq_zero.mp this with h' | h'
    · have : (2 * k + 1 : ℤ) = 0 := by exact_mod_cast h'
      omega
    · linarith
  have hne2 : 2 * ε * (k : K) - ε ≠ 0 := by
    intro h
    have : (2 * (k : K) - 1) * ε = 0 := by linarith
    rcases mul_eq_zero.mp this with h' | h'
    · have : (2 * k - 1 : ℤ) = 0 := by exact_mod_cast h'
      omega
    · linarith
  have p3 : (2 * ε * (k : K) = 0) ↔ k = 0 := by
    rw [mul_eq_zero, or_iff_right h2.ne']; exact_mod_cast Iff.rfl
  simp only [hne1, hne2, p3, ite_false]
  rcases lt_trichotomy k 0 with hk | hk | hk
  · have hk' : (k : K) ≤ -1 := by exact_mod_cast (show k ≤ -1 by omega)
    have a : ¬ (0 ≤ 2 * ε * (k : K) + ε) := by nlinarith
    have b : ¬ (0 ≤ 2 * ε * (k : K) - ε) := by nlinarith
    have c : k ≠ 0 := by omega
    simp only [a, b, c, ite_false]; simp
  · subst hk
    have b : ¬ (ε ≤ 0) := by linarith
    have b' : (0 : K) ≤ ε := hε.le
    simp [b, b']
  · have hk' : (1 : K) ≤ k := by exact_mod_cast (show 1 ≤ k by omega)
    have a : (0 ≤ 2 * ε * (k : K) + ε) := by nlinarith
    have b : (0 ≤ 2 * ε * (k : K) - ε) := by nlinarith
    have c : k ≠ 0 := by omega
    simp only [a, b, c, ite_true, ite_false]; simp

/-- The `2ε` correction for the square of the identity: `D⁺ x² = 2x + 2ε`. -/
theorem Dp_sq_id (ε : K) (hε : ε ≠ 0) (x : K) :
    QE.Dp ε (fun y => y ^ 2) x = 2 * x + 2 * ε := by
  unfold QE.Dp; field_simp; ring

/-- The granular delta has total mass exactly `1` on any symmetric run of lattice
points containing `0`. -/
theorem delta_sum (ε : K) (hε : 0 < ε) (n : ℕ) :
    ∑ k ∈ Finset.Icc (-(n : ℤ)) n, delta ε (2 * ε * k) * (2 * ε) = 1 := by
  have h2 : (0 : K) < 2 * ε := by positivity
  rw [Finset.sum_eq_single (0 : ℤ)]
  · simp [delta]; field_simp
  · intro k _ hk
    have : (2 * ε * (k : K)) ≠ 0 := mul_ne_zero h2.ne' (by exact_mod_cast hk)
    simp [delta, this]
  · intro h; exfalso; apply h; simp

/-- Sifting property of the granular delta (exact). -/
theorem delta_sift (ε : K) (hε : 0 < ε) (n : ℕ) (φ : K → K) :
    ∑ k ∈ Finset.Icc (-(n : ℤ)) n, delta ε (2 * ε * k) * φ (2 * ε * k) * (2 * ε) = φ 0 := by
  have h2 : (0 : K) < 2 * ε := by positivity
  rw [Finset.sum_eq_single (0 : ℤ)]
  · simp [delta]; field_simp
  · intro k _ hk
    have : (2 * ε * (k : K)) ≠ 0 := mul_ne_zero h2.ne' (by exact_mod_cast hk)
    simp [delta, this]
  · intro h; exfalso; apply h; simp

/-- The granular delta squared is an honest function, with total mass `1/(2ε)`:
the product `δ·δ` that has no distributional meaning is here a number. -/
theorem delta_sq_sum (ε : K) (hε : 0 < ε) (n : ℕ) :
    ∑ k ∈ Finset.Icc (-(n : ℤ)) n, delta ε (2 * ε * k) ^ 2 * (2 * ε) = 1 / (2 * ε) := by
  have h2 : (0 : K) < 2 * ε := by positivity
  rw [Finset.sum_eq_single (0 : ℤ)]
  · simp [delta]; field_simp
  · intro k _ hk
    have : (2 * ε * (k : K)) ≠ 0 := mul_ne_zero h2.ne' (by exact_mod_cast hk)
    simp [delta, this]
  · intro h; exfalso; apply h; simp

/-! ### Time reversal, l'Hôpital, convexity, boundedness -/

/-- Time reversal exchanges `D⁺` and `D⁻`: `D⁻ (f ∘ neg) (x) = - D⁺ f (-x)`. -/
theorem Dm_comp_neg (ε : K) (f : K → K) (x : K) :
    QE.Dm ε (fun y => f (-y)) x = - QE.Dp ε f (-x) := by
  unfold QE.Dm QE.Dp; beta_reduce
  rw [show -(x - 2 * ε) = -x + 2 * ε by ring]; ring

/-- **Exact granular l'Hôpital rule**: if `f(a) = g(a) = 0` and `g(a+2ε) ≠ 0`, then
`f(a+2ε)/g(a+2ε) = D⁺f(a)/D⁺g(a)`. -/
theorem lhopital (ε : K) (hε : ε ≠ 0) (f g : K → K) (a : K) (hf : f a = 0) (hg : g a = 0) :
    f (a + 2 * ε) / g (a + 2 * ε) = QE.Dp ε f a / QE.Dp ε g a := by
  unfold QE.Dp; rw [hf, hg, sub_zero, sub_zero]
  have : (2 * ε) ≠ 0 := mul_ne_zero two_ne_zero hε
  rw [div_div_div_cancel_right₀ this]

/-- **Convexity criterion**: if the granular second derivative `D⁺D⁻f` is
non-negative at the interior lattice points of a run, `D⁺ f` is non-decreasing
along the run. -/
theorem Dp_mono_of_second_nonneg (ε : K) (hε : 0 < ε) (f : K → K) (a : K) (n : ℕ)
    (h : ∀ k < n, 0 ≤ QE.Dp ε (QE.Dm ε f) (a + 2 * ε * (k + 1))) :
    ∀ i j, i ≤ j → j ≤ n → QE.Dp ε f (a + 2 * ε * i) ≤ QE.Dp ε f (a + 2 * ε * j) := by
  have step : ∀ k < n, QE.Dp ε f (a + 2 * ε * k) ≤ QE.Dp ε f (a + 2 * ε * (k + 1)) := by
    intro k hk
    have h1 := Dp_sub_Dm_eq ε hε.ne' f (a + 2 * ε * (k + 1))
    have h2 : QE.Dm ε f (a + 2 * ε * (k + 1)) = QE.Dp ε f (a + 2 * ε * k) := by
      rw [Dm_eq_Dp]; congr 1; ring
    rw [h2] at h1
    have := h k hk
    have : 0 ≤ 2 * ε * QE.Dp ε (QE.Dm ε f) (a + 2 * ε * (k + 1)) := by positivity
    linarith
  intro i j hij hjn
  induction j with
  | zero => have : i = 0 := by omega
            subst this; exact le_refl _
  | succ j ih =>
    rcases Nat.eq_or_lt_of_le hij with h' | h'
    · rw [h']
    · have := ih (by omega) (by omega)
      have := step j (by omega)
      push_cast at this ⊢
      linarith

/-- **The granular derivative is a bounded operator**: `|f| ≤ B` implies
`|D⁺ f| ≤ B/ε`. -/
theorem Dp_bounded (ε : K) (hε : 0 < ε) (f : K → K) (B : K) (hB : ∀ y, |f y| ≤ B) (x : K) :
    |QE.Dp ε f x| ≤ B / ε := by
  unfold QE.Dp
  have h2 : (0 : K) < 2 * ε := by positivity
  rw [abs_div, abs_of_pos h2, div_le_div_iff₀ h2 hε]
  have := abs_sub (f (x + 2 * ε)) (f x)
  have h3 := hB (x + 2 * ε)
  have h4 := hB x
  nlinarith

/-- The bound is attained by the alternating lattice function `(-1)^k`: the
norm of `D⁺` on bounded lattice functions is exactly `1/ε`. -/
theorem Dp_alternating (ε : K) (hε : ε ≠ 0) (k : ℕ) :
    ((-1 : K) ^ (k + 1) - (-1) ^ k) / (2 * ε) = -((-1) ^ k / ε) := by
  rw [pow_succ]; field_simp; ring

end Algebra

/-! ## Real-variable results: exponential, trigonometry, shadows -/

section RealAnalysis

open Real Filter Topology Set

/-- The granular exponential `e_ε(x) = (1+2ε)^{x/(2ε)}`. -/
noncomputable def eg (ε x : ℝ) : ℝ := (1 + 2 * ε) ^ (x / (2 * ε))

/-- `D⁺ e_ε = e_ε` exactly, at every real `x` (not only on the lattice). -/
theorem Dp_eg (ε : ℝ) (hε : 0 < ε) (x : ℝ) : QE.Dp ε (eg ε) x = eg ε x := by
  unfold QE.Dp eg
  have h1 : (0 : ℝ) < 1 + 2 * ε := by linarith
  have e : (x + 2 * ε) / (2 * ε) = x / (2 * ε) + 1 := by field_simp
  rw [e, rpow_add_one h1.ne']
  field_simp; ring

/-- Functional equation of the granular exponential. -/
theorem eg_add (ε : ℝ) (hε : 0 < ε) (x y : ℝ) : eg ε (x + y) = eg ε x * eg ε y := by
  unfold eg
  rw [add_div, rpow_add (by linarith)]

theorem eg_zero (ε : ℝ) : eg ε 0 = 1 := by simp [eg]

/-- On the lattice the granular exponential is the integer power `(1+2ε)^k`. -/
theorem eg_centre (ε : ℝ) (hε : 0 < ε) (k : ℤ) : eg ε (2 * ε * k) = (1 + 2 * ε) ^ k := by
  unfold eg
  have : 2 * ε * (k : ℝ) / (2 * ε) = (k : ℝ) := by field_simp
  rw [this, rpow_intCast]

lemma tendsto_two_mul_right : Tendsto (fun ε : ℝ => 2 * ε) (𝓝[>] 0) (𝓝[>] 0) := by
  apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
  · have : Tendsto (fun ε : ℝ => 2 * ε) (𝓝 0) (𝓝 (2 * 0)) :=
      (continuous_const.mul continuous_id).tendsto 0
    simpa using this.mono_left nhdsWithin_le_nhds
  · filter_upwards [self_mem_nhdsWithin] with ε hε
    exact mul_pos two_pos (Set.mem_Ioi.mp hε)

lemma tendsto_log_ratio :
    Tendsto (fun ε : ℝ => log (1 + 2 * ε) / (2 * ε)) (𝓝[>] 0) (𝓝 1) := by
  have h := (hasDerivAt_log (one_ne_zero (α := ℝ))).tendsto_slope_zero_right
  simp only [log_one, sub_zero, smul_eq_mul, inv_one] at h
  have := h.comp tendsto_two_mul_right
  refine this.congr' ?_
  filter_upwards with ε
  simp [Function.comp, div_eq_inv_mul]

/-- **Shadow of the granular exponential**: if `x_ε → x₀` then
`e_ε(x_ε) → exp x₀` as `ε → 0⁺` (i.e. `st e_ε(x) = e^{st x}` for finite `x`). -/
theorem eg_shadow (x : ℝ → ℝ) (x₀ : ℝ) (hx : Tendsto x (𝓝[>] 0) (𝓝 x₀)) :
    Tendsto (fun ε => eg ε (x ε)) (𝓝[>] 0) (𝓝 (exp x₀)) := by
  have h : Tendsto (fun ε => exp (log (1 + 2 * ε) / (2 * ε) * x ε)) (𝓝[>] 0) (𝓝 (exp x₀)) := by
    have := (tendsto_log_ratio.mul hx)
    rw [one_mul] at this
    exact (continuous_exp.tendsto _).comp this
  refine h.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with ε hε
  have hε' : (0 : ℝ) < ε := hε
  unfold eg
  rw [rpow_def_of_pos (by linarith)]
  congr 1; ring

/-- Exponentials are eigenfunctions of `D⁺`, with eigenvalue `(e^{2ελ}-1)/(2ε)`. -/
theorem Dp_exp (ε : ℝ) (lam x : ℝ) :
    QE.Dp ε (fun y => exp (lam * y)) x = (exp (2 * ε * lam) - 1) / (2 * ε) * exp (lam * x) := by
  unfold QE.Dp; beta_reduce
  rw [show lam * (x + 2 * ε) = lam * x + 2 * ε * lam by ring, exp_add]
  ring

/-- The operator identity `D = log(S)/(2ε)` on exponentials: the classical exponent
is recovered exactly from the granular eigenvalue `μ`. -/
theorem log_shift_exp (ε : ℝ) (hε : 0 < ε) (lam : ℝ) :
    log (1 + 2 * ε * ((exp (2 * ε * lam) - 1) / (2 * ε))) / (2 * ε) = lam := by
  have h2 : (2 * ε) ≠ 0 := by positivity
  rw [show 1 + 2 * ε * ((exp (2 * ε * lam) - 1) / (2 * ε)) = exp (2 * ε * lam) by
    field_simp; ring, log_exp]
  field_simp

/-! ### Granular trigonometry -/

/-- Granular complex exponential on the lattice: `E(n) = (1 + 2iε)^n`. -/
noncomputable def cexpg (ε : ℝ) (n : ℕ) : ℂ := (1 + 2 * ε * Complex.I) ^ n

/-- Granular cosine. -/
noncomputable def cosg (ε : ℝ) (n : ℕ) : ℝ := (cexpg ε n).re
/-- Granular sine. -/
noncomputable def sing (ε : ℝ) (n : ℕ) : ℝ := (cexpg ε n).im

/-- `D⁺ E = i E` exactly. -/
theorem Dp_cexpg (ε : ℝ) (hε : ε ≠ 0) (n : ℕ) :
    (cexpg ε (n + 1) - cexpg ε n) / (2 * ε) = Complex.I * cexpg ε n := by
  unfold cexpg
  have : (ε : ℂ) ≠ 0 := by exact_mod_cast hε
  rw [pow_succ]
  field_simp
  ring

theorem cosg_succ (ε : ℝ) (n : ℕ) : cosg ε (n + 1) = cosg ε n - 2 * ε * sing ε n := by
  unfold cosg sing cexpg
  rw [pow_succ, Complex.mul_re]; simp; exact mul_comm _ _

theorem sing_succ (ε : ℝ) (n : ℕ) : sing ε (n + 1) = sing ε n + 2 * ε * cosg ε n := by
  unfold cosg sing cexpg
  rw [pow_succ, Complex.mul_im]; simp [mul_comm]; exact add_comm _ _

/-- `D⁺ cos_ε = - sin_ε` on the lattice. -/
theorem Dp_cosg (ε : ℝ) (hε : ε ≠ 0) (n : ℕ) :
    (cosg ε (n + 1) - cosg ε n) / (2 * ε) = - sing ε n := by
  rw [cosg_succ]; field_simp; ring

/-- `D⁺ sin_ε = cos_ε` on the lattice. -/
theorem Dp_sing (ε : ℝ) (hε : ε ≠ 0) (n : ℕ) :
    (sing ε (n + 1) - sing ε n) / (2 * ε) = cosg ε n := by
  rw [sing_succ]; field_simp; ring

/-- Exact addition theorem for the granular cosine. -/
theorem cosg_add (ε : ℝ) (m n : ℕ) :
    cosg ε (m + n) = cosg ε m * cosg ε n - sing ε m * sing ε n := by
  unfold cosg sing cexpg; rw [pow_add, Complex.mul_re]

/-- Exact addition theorem for the granular sine. -/
theorem sing_add (ε : ℝ) (m n : ℕ) :
    sing ε (m + n) = sing ε m * cosg ε n + cosg ε m * sing ε n := by
  unfold cosg sing cexpg; rw [pow_add, Complex.mul_im]; ring

/-- The granular Pythagorean identity, exactly: `cos² + sin² = (1+4ε²)^n`. -/
theorem cosg_sq_add_sing_sq (ε : ℝ) (n : ℕ) :
    cosg ε n ^ 2 + sing ε n ^ 2 = (1 + 4 * ε ^ 2) ^ n := by
  unfold cosg sing
  have h : (cexpg ε n).re ^ 2 + (cexpg ε n).im ^ 2 = Complex.normSq (cexpg ε n) := by
    rw [Complex.normSq_apply]; ring
  rw [h]; unfold cexpg
  rw [map_pow, Complex.normSq_apply]
  simp; ring

/-- The defect of the Pythagorean identity is controlled: at `x = 2εn`,
`1 ≤ cos² + sin² ≤ exp(2ε x)`. -/
theorem pythag_defect (ε : ℝ) (n : ℕ) :
    1 ≤ cosg ε n ^ 2 + sing ε n ^ 2 ∧
      cosg ε n ^ 2 + sing ε n ^ 2 ≤ exp (2 * ε * (2 * ε * n)) := by
  rw [cosg_sq_add_sing_sq]
  constructor
  · exact one_le_pow₀ (by nlinarith)
  · have h1 : 1 + 4 * ε ^ 2 ≤ exp (4 * ε ^ 2) := by linarith [add_one_le_exp (4 * ε ^ 2)]
    calc (1 + 4 * ε ^ 2) ^ n ≤ exp (4 * ε ^ 2) ^ n :=
          pow_le_pow_left₀ (by nlinarith) h1 n
      _ = exp (2 * ε * (2 * ε * n)) := by rw [← exp_nat_mul]; ring_nf

/-! ### Shadow theorems -/

/-- **Pointwise shadow theorem**: if `f` is differentiable at `x`,
`D⁺ f(x) → f'(x)` as `ε → 0⁺`. -/
theorem Dp_shadow (f : ℝ → ℝ) (f' x : ℝ) (hf : HasDerivAt f f' x) :
    Tendsto (fun ε => QE.Dp ε f x) (𝓝[>] 0) (𝓝 f') := by
  have := hf.tendsto_slope_zero_right.comp tendsto_two_mul_right
  refine this.congr' ?_
  filter_upwards with ε
  simp [QE.Dp, Function.comp, div_eq_inv_mul]

/-- **Shadow theorem for `C¹` functions at a moving point**: if `f` is `C¹` and
`x_ε → x₀`, then `D⁺ f(x_ε) → f'(x₀)`; this is the statement
`st D⁺ *f(x) = f'(st x)` for every finite `x`. -/
theorem Dp_shadow_C1 (f f' : ℝ → ℝ) (hf : ∀ y, HasDerivAt f (f' y) y) (hc : Continuous f')
    (x : ℝ → ℝ) (x₀ : ℝ) (hx : Tendsto x (𝓝[>] 0) (𝓝 x₀)) :
    Tendsto (fun ε => QE.Dp ε f (x ε)) (𝓝[>] 0) (𝓝 (f' x₀)) := by
  have hmvt : ∀ ε : ℝ, 0 < ε → ∃ ξ ∈ Ioo (x ε) (x ε + 2 * ε), f' ξ = QE.Dp ε f (x ε) := by
    intro ε hε
    obtain ⟨ξ, hξ, h⟩ := exists_hasDerivAt_eq_slope f f' (by linarith : x ε < x ε + 2 * ε)
      (fun y _ => (hf y).continuousAt.continuousWithinAt) (fun y _ => hf y)
    refine ⟨ξ, hξ, ?_⟩
    rw [h, QE.Dp]; congr 1; ring
  choose! ξ hξ heq using hmvt
  have hξt : Tendsto ξ (𝓝[>] 0) (𝓝 x₀) := by
    have hup : Tendsto (fun ε => x ε + 2 * ε) (𝓝[>] 0) (𝓝 x₀) := by
      have h2 : Tendsto (fun ε : ℝ => 2 * ε) (𝓝[>] 0) (𝓝 0) :=
        tendsto_two_mul_right.mono_right nhdsWithin_le_nhds
      simpa using hx.add h2
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hx hup
    · filter_upwards [self_mem_nhdsWithin] with ε hε using (hξ ε hε).1.le
    · filter_upwards [self_mem_nhdsWithin] with ε hε using (hξ ε hε).2.le
  have := (hc.tendsto x₀).comp hξt
  refine this.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with ε hε using heq ε hε

/-- First-order Taylor bound for `f` with `M`-Lipschitz derivative. -/
lemma taylor1_nonneg (f f' : ℝ → ℝ) (M : ℝ) (hf : ∀ y, HasDerivAt f (f' y) y)
    (hL : ∀ y z, |f' y - f' z| ≤ M * |y - z|) (x h : ℝ) (hh : 0 ≤ h) :
    |f (x + h) - f x - h * f' x| ≤ M * h ^ 2 / 2 := by
  have key : ∀ s : ℝ, s = 1 ∨ s = -1 →
      s * (f (x + h) - f x - h * f' x) - M * h ^ 2 / 2 ≤ 0 := by
    intro s hs
    set ψ : ℝ → ℝ := fun t => s * (f (x + t) - f x - t * f' x) - M * t ^ 2 / 2 with hψ
    have hder : ∀ t, HasDerivAt ψ (s * (f' (x + t) - f' x) - M * t) t := by
      intro t
      have h1 : HasDerivAt (fun t => f (x + t)) (f' (x + t)) t := by
        exact (hf (x + t)).comp_const_add x t
      have h2 := ((h1.sub_const (f x)).sub ((hasDerivAt_id t).mul_const (f' x))).const_mul s
      have h3 := ((hasDerivAt_pow 2 t).const_mul M).div_const 2
      exact (h2.sub h3).congr_deriv (by simp; ring)
    have hanti : AntitoneOn ψ (Ici 0) := by
      apply antitoneOn_of_deriv_nonpos (convex_Ici 0)
      · exact fun t _ => (hder t).continuousAt.continuousWithinAt
      · exact fun t _ => (hder t).differentiableAt.differentiableWithinAt
      · intro t ht
        rw [interior_Ici] at ht
        rw [(hder t).deriv]
        have ht' : 0 < t := ht
        have hl := hL (x + t) x
        rw [show x + t - x = t by ring, abs_of_pos ht'] at hl
        rcases hs with rfl | rfl
        · have := le_abs_self (f' (x + t) - f' x); linarith
        · have := neg_abs_le (f' (x + t) - f' x); linarith
    have := hanti (self_mem_Ici) (show (0 : ℝ) ≤ h from hh) hh
    simpa [hψ] using this
  rw [abs_le]
  constructor
  · have := key (-1) (Or.inr rfl); linarith
  · have := key 1 (Or.inl rfl); linarith

/-- First-order Taylor bound, both directions. -/
theorem taylor1 (f f' : ℝ → ℝ) (M : ℝ) (hf : ∀ y, HasDerivAt f (f' y) y)
    (hL : ∀ y z, |f' y - f' z| ≤ M * |y - z|) (x h : ℝ) :
    |f (x + h) - f x - h * f' x| ≤ M * h ^ 2 / 2 := by
  rcases le_total 0 h with hh | hh
  · exact taylor1_nonneg f f' M hf hL x h hh
  · have hg : ∀ y, HasDerivAt (fun y => f (-y)) (-f' (-y)) y := by
      intro y
      simpa using (hf (0 - y)).comp_const_sub 0 y
    have hgL : ∀ y z, |-f' (-y) - -f' (-z)| ≤ M * |y - z| := by
      intro y z
      have := hL (-y) (-z)
      rw [show -f' (-y) - -f' (-z) = -(f' (-y) - f' (-z)) by ring, abs_neg]
      rwa [show -y - -z = -(y - z) by ring, abs_neg] at this
    have := taylor1_nonneg (fun y => f (-y)) (fun y => -f' (-y)) M hg hgL (-x) (-h) (by linarith)
    simp only [neg_add, neg_neg] at this
    rw [show f (x + h) - f x - h * f' x = f (-(-x) + -(-h)) - f (-(-x)) - -h * -f' (-(-x)) by
      simp]
    simpa [neg_sq] using this

/-- **Uniform shadow bound**: if `f'` is `M`-Lipschitz (e.g. `f ∈ C²`, `|f''| ≤ M`),
then `|D⁺ f(x) - f'(x)| ≤ M ε` for every `x` and every `ε > 0`. -/
theorem Dp_sub_deriv_le (f f' : ℝ → ℝ) (M : ℝ) (hf : ∀ y, HasDerivAt f (f' y) y)
    (hL : ∀ y z, |f' y - f' z| ≤ M * |y - z|) (ε : ℝ) (hε : 0 < ε) (x : ℝ) :
    |QE.Dp ε f x - f' x| ≤ M * ε := by
  have h := taylor1 f f' M hf hL x (2 * ε)
  have h2 : (0 : ℝ) < 2 * ε := by positivity
  have e : QE.Dp ε f x - f' x = (f (x + 2 * ε) - f x - 2 * ε * f' x) / (2 * ε) := by
    unfold QE.Dp; field_simp
  rw [e, abs_div, abs_of_pos h2, div_le_iff₀ h2]
  nlinarith

/-- Uniform bound for the central difference: `|D° f(x) - f'(x)| ≤ M ε / 2`. -/
theorem Dc_sub_deriv_le (f f' : ℝ → ℝ) (M : ℝ) (hf : ∀ y, HasDerivAt f (f' y) y)
    (hL : ∀ y z, |f' y - f' z| ≤ M * |y - z|) (ε : ℝ) (hε : 0 < ε) (x : ℝ) :
    |QE.Dc ε f x - f' x| ≤ M * ε / 2 := by
  have h1 := taylor1 f f' M hf hL x ε
  have h2 := taylor1 f f' M hf hL x (-ε)
  have hp : (0 : ℝ) < 2 * ε := by positivity
  have e : QE.Dc ε f x - f' x
      = ((f (x + ε) - f x - ε * f' x) - (f (x + -ε) - f x - -ε * f' x)) / (2 * ε) := by
    unfold QE.Dc; field_simp; ring_nf
  rw [e, abs_div, abs_of_pos hp, div_le_iff₀ hp]
  have := abs_sub (f (x + ε) - f x - ε * f' x) (f (x + -ε) - f x - -ε * f' x)
  rw [neg_sq] at h2
  nlinarith

/-- **Hölder functions** (e.g. Weierstrass's nowhere-differentiable function) have
granular derivatives everywhere, with the explicit growth `C (2ε)^{α-1}`. -/
theorem Dp_holder (f : ℝ → ℝ) (C α : ℝ) (hC : ∀ x y, |f x - f y| ≤ C * |x - y| ^ α)
    (ε : ℝ) (hε : 0 < ε) (x : ℝ) : |QE.Dp ε f x| ≤ C * (2 * ε) ^ (α - 1) := by
  have h2 : (0 : ℝ) < 2 * ε := by positivity
  unfold QE.Dp
  rw [abs_div, abs_of_pos h2, div_le_iff₀ h2, rpow_sub_one h2.ne', mul_assoc, div_mul_cancel₀ _ h2.ne']
  have := hC (x + 2 * ε) x
  rwa [show x + 2 * ε - x = 2 * ε by ring, abs_of_pos h2] at this

/-! ### Higher differences and derivatives -/

/-- **Mean-value bounds for higher differences** (positivity of the Peano/B-spline
kernel): if `F 0, F 1, …, F k` is a chain of successive derivatives and
`m ≤ F k ≤ M` on `[x, x + 2kε]`, then `m ≤ (D⁺)^k F₀ (x) ≤ M`. -/
theorem Dpk_bounds (ε : ℝ) (hε : 0 < ε) (k : ℕ) :
    ∀ (F : ℕ → ℝ → ℝ) (m M x : ℝ), (∀ j < k, ∀ y, HasDerivAt (F j) (F (j + 1) y) y) →
      (∀ y ∈ Icc x (x + 2 * ε * k), m ≤ F k y ∧ F k y ≤ M) →
      m ≤ Dpk ε k (F 0) x ∧ Dpk ε k (F 0) x ≤ M := by
  induction k with
  | zero =>
    intro F m M x _ hb
    simpa [Dpk] using hb x (by simp)
  | succ k ih =>
    intro F m M x hF hb
    set G : ℕ → ℝ → ℝ := fun j => QE.Dp ε (F j) with hG
    have hGd : ∀ j < k, ∀ y, HasDerivAt (G j) (G (j + 1) y) y := by
      intro j hj y
      have h1 := hF j (by omega) (y + 2 * ε)
      have h1' : HasDerivAt (fun y => F j (y + 2 * ε)) (F (j + 1) (y + 2 * ε)) y := by
        exact h1.comp_add_const y (2 * ε)
      have h2 := hF j (by omega) y
      have := (h1'.sub h2).div_const (2 * ε)
      exact this
    have hGb : ∀ y ∈ Icc x (x + 2 * ε * k), m ≤ G k y ∧ G k y ≤ M := by
      intro y hy
      obtain ⟨ξ, hξ, h⟩ := exists_hasDerivAt_eq_slope (F k) (F (k + 1))
        (by linarith : y < y + 2 * ε)
        (fun z _ => (hF k (by omega) z).continuousAt.continuousWithinAt)
        (fun z _ => hF k (by omega) z)
      have hmem : ξ ∈ Icc x (x + 2 * ε * ((k + 1 : ℕ) : ℝ)) := by
        push_cast
        constructor <;> nlinarith [hy.1, hy.2, hξ.1, hξ.2]
      have hGk : G k y = F (k + 1) ξ := by
        rw [h, hG]; simp only [QE.Dp]; congr 1; ring
      rw [hGk]; exact hb ξ hmem
    have := ih G m M x hGd hGb
    have e : Dpk ε (k + 1) (F 0) = Dpk ε k (G 0) := by
      simp only [Dpk, hG]; rw [Function.iterate_succ_apply]
    rw [e]; exact this

/-- **Mean value theorem for higher differences**: if `F k` is continuous, then
`(D⁺)^k F₀(x) = F_k(ξ)` for some `ξ ∈ [x, x + 2kε]`. -/
theorem Dpk_mvt (ε : ℝ) (hε : 0 < ε) (k : ℕ) (F : ℕ → ℝ → ℝ)
    (hF : ∀ j < k, ∀ y, HasDerivAt (F j) (F (j + 1) y) y) (hc : Continuous (F k)) (x : ℝ) :
    ∃ ξ ∈ Icc x (x + 2 * ε * k), Dpk ε k (F 0) x = F k ξ := by
  have hxle : x ≤ x + 2 * ε * k := by have : (0 : ℝ) ≤ k := Nat.cast_nonneg k; nlinarith
  have hcpt : IsCompact (Icc x (x + 2 * ε * k)) := isCompact_Icc
  have hne : (Icc x (x + 2 * ε * k)).Nonempty := nonempty_Icc.mpr hxle
  obtain ⟨a, ha, hamin⟩ := hcpt.exists_isMinOn hne hc.continuousOn
  obtain ⟨b, hb, hbmax⟩ := hcpt.exists_isMaxOn hne hc.continuousOn
  have hbd := Dpk_bounds ε hε k F (F k a) (F k b) x hF
    (fun y hy => ⟨hamin hy, hbmax hy⟩)
  -- intermediate value theorem on the segment between `a` and `b`
  rcases le_total a b with hab | hab
  · have hsub : Icc a b ⊆ Icc x (x + 2 * ε * k) := Icc_subset_Icc ha.1 hb.2
    obtain ⟨ξ, hξ, h⟩ := intermediate_value_Icc hab hc.continuousOn
      (show Dpk ε k (F 0) x ∈ Icc (F k a) (F k b) from hbd)
    exact ⟨ξ, hsub hξ, h.symm⟩
  · have hsub : Icc b a ⊆ Icc x (x + 2 * ε * k) := Icc_subset_Icc hb.1 ha.2
    obtain ⟨ξ, hξ, h⟩ := intermediate_value_Icc' hab hc.continuousOn
      (show Dpk ε k (F 0) x ∈ Icc (F k a) (F k b) from hbd)
    exact ⟨ξ, hsub hξ, h.symm⟩

/-- **Shadow theorem for higher differences**: `(D⁺)^k f(x) → f^{(k)}(x)`. -/
theorem Dpk_shadow (k : ℕ) (F : ℕ → ℝ → ℝ)
    (hF : ∀ j < k, ∀ y, HasDerivAt (F j) (F (j + 1) y) y) (x : ℝ)
    (hc : ContinuousAt (F k) x) :
    Tendsto (fun ε => Dpk ε k (F 0) x) (𝓝[>] 0) (𝓝 (F k x)) := by
  rw [Metric.tendsto_nhdsWithin_nhds]
  intro η hη
  obtain ⟨δ, hδ, hcont⟩ := Metric.continuousAt_iff.mp hc (η / 2) (by positivity)
  refine ⟨δ / (2 * k + 2), by positivity, ?_⟩
  intro ε hε hεd
  have hε' : (0 : ℝ) < ε := hε
  rw [Real.dist_eq, sub_zero, abs_of_pos hε'] at hεd
  have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have hb := Dpk_bounds ε hε' k F (F k x - η / 2) (F k x + η / 2) x hF (by
    intro y hy
    have hyx : dist y x < δ := by
      rw [Real.dist_eq, abs_of_nonneg (by linarith [hy.1])]
      have h1 : 2 * ε * k < δ := by
        rw [lt_div_iff₀ (by positivity)] at hεd; nlinarith
      linarith [hy.2]
    have := hcont hyx
    rw [Real.dist_eq, abs_lt] at this
    constructor <;> linarith)
  rw [Real.dist_eq, abs_lt]
  constructor <;> linarith [hb.1, hb.2]

/-! ### Symbols: the granular dispersion relation -/

/-- The central derivative of a sine wave: `D° sin(ωx) = (sin(ωε)/ε) cos(ωx)`. -/
theorem Dc_sin (ε ω x : ℝ) (hε : ε ≠ 0) :
    QE.Dc ε (fun y => sin (ω * y)) x = sin (ω * ε) / ε * cos (ω * x) := by
  unfold QE.Dc; beta_reduce
  rw [show ω * (x + ε) = ω * x + ω * ε by ring, show ω * (x - ε) = ω * x - ω * ε by ring,
    sin_add, sin_sub]
  field_simp; ring

/-- The central derivative of a cosine wave. -/
theorem Dc_cos (ε ω x : ℝ) (hε : ε ≠ 0) :
    QE.Dc ε (fun y => cos (ω * y)) x = -(sin (ω * ε) / ε * sin (ω * x)) := by
  unfold QE.Dc; beta_reduce
  rw [show ω * (x + ε) = ω * x + ω * ε by ring, show ω * (x - ε) = ω * x - ω * ε by ring,
    cos_add, cos_sub]
  field_simp; ring

/-- The granular Laplacian of a plane wave: `-D⁺D⁻ cos(ωx) = (sin(ωε)/ε)² cos(ωx)`;
its spectrum is `[0, 1/ε²]`. -/
theorem neg_DpDm_cos (ε ω x : ℝ) (hε : ε ≠ 0) :
    -QE.Dp ε (QE.Dm ε (fun y => cos (ω * y))) x = (sin (ω * ε) / ε) ^ 2 * cos (ω * x) := by
  unfold QE.Dp QE.Dm; beta_reduce
  rw [show x + 2 * ε - 2 * ε = x by ring,
    show ω * (x + 2 * ε) = ω * x + 2 * (ω * ε) by ring,
    show ω * (x - 2 * ε) = ω * x - 2 * (ω * ε) by ring, cos_add, cos_sub,
    cos_two_mul, sin_two_mul]
  have hc : cos (ω * ε) ^ 2 = 1 - sin (ω * ε) ^ 2 := by rw [← sin_sq_add_cos_sq (ω * ε)]; ring
  field_simp
  rw [hc]; ring

/-- Time reversal of the granular exponential: `D⁻ e_ε(-x) = -e_ε(-x)`, whereas
`D⁺ e_ε(-x) = -e_ε(-x)/(1+2ε)`. -/
theorem Dm_eg_neg (ε : ℝ) (hε : 0 < ε) (x : ℝ) :
    QE.Dm ε (fun y => eg ε (-y)) x = - eg ε (-x) := by
  rw [Dm_comp_neg, Dp_eg ε hε]

theorem Dp_eg_neg (ε : ℝ) (hε : 0 < ε) (x : ℝ) :
    QE.Dp ε (fun y => eg ε (-y)) x = - eg ε (-x) / (1 + 2 * ε) := by
  unfold QE.Dp; beta_reduce
  have h1 : (0 : ℝ) < 1 + 2 * ε := by linarith
  have e : eg ε (-x) = eg ε (-(x + 2 * ε)) * (1 + 2 * ε) := by
    rw [show -x = -(x + 2 * ε) + 2 * ε by ring, eg_add ε hε]
    congr 1
    unfold eg; rw [show 2 * ε / (2 * ε) = (1 : ℝ) by field_simp, rpow_one]
  rw [e]; field_simp; ring

/-! ### A table of exact granular derivatives -/

theorem Dp_inv (ε x : ℝ) (hε : ε ≠ 0) (hx : x ≠ 0) (hx' : x + 2 * ε ≠ 0) :
    QE.Dp ε (fun y => 1 / y) x = -1 / (x * (x + 2 * ε)) := by
  unfold QE.Dp; beta_reduce; field_simp; ring

theorem Dp_sqrt (ε x : ℝ) (hε : 0 < ε) (hx : 0 ≤ x) :
    QE.Dp ε (fun y => √y) x = 1 / (√(x + 2 * ε) + √x) := by
  unfold QE.Dp; beta_reduce
  have h1 : 0 < √(x + 2 * ε) := sqrt_pos.mpr (by linarith)
  have h2 : 0 ≤ √x := sqrt_nonneg x
  have hs : √(x + 2 * ε) ^ 2 = x + 2 * ε := sq_sqrt (by linarith)
  have hs' : √x ^ 2 = x := sq_sqrt hx
  have hpos : 0 < √(x + 2 * ε) + √x := by linarith
  rw [div_eq_div_iff (by positivity) hpos.ne']
  nlinarith [hs, hs']

theorem Dp_log (ε x : ℝ) (hε : 0 < ε) (hx : 0 < x) :
    QE.Dp ε (fun y => log y) x = log (1 + 2 * ε / x) / (2 * ε) := by
  unfold QE.Dp; beta_reduce
  rw [← log_div (by positivity) hx.ne']
  congr 2; field_simp

end RealAnalysis

end QE.Diff
