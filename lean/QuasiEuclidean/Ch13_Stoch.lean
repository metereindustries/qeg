-- SPDX-License-Identifier: MIT
-- Copyright 2026 Metere Industries, Inc. Author: Alfredo Metere.
-- Quasi-Euclidean Granular Geometry. Any derivative work must carry this notice:
--   This work is derivative of the Quasi-Euclidean Granular Geometry book
--   authored by Alfredo Metere. Copyright 2026 Metere Industries, Inc.
--   All rights reserved
-- See LICENSE.md and NOTICE.

import QuasiEuclidean.Basic

/-!
# Chapter 13: Granular stochastic processes

The Anderson walk on the hyperfinite time lattice, formalised as exact
finitary statements about the finite coin space `Fin n → Bool` with the
uniform (counting) measure.  A coin `b : Bool` has sign `sgn b = ±1`, the
increment of the walk on the `k`-th time cell `[kτ,(k+1)τ)` is
`ΔW_k = sgn (ω k) · s`, with space step `s = √τ` (we never take a square
root: we work with `s` and put `τ := s ^ 2`).  In the book `s = 2ε`,
`τ = (2ε)^2`.

Everything holds over every linearly ordered field `K` and every `n`; in
particular for `K := Hyperreal` and `n` an (internal) hypernatural, by
transfer of these finite statements.
-/

set_option linter.unusedSectionVars false

namespace QE.Stoch

open Finset

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-! ## Coins, paths, the uniform measure -/

/-- The sign of a coin: `+1` for heads (`true`), `-1` for tails. -/
def sgn (b : Bool) : K := if b then 1 else -1

@[simp] theorem sgn_true : (sgn true : K) = 1 := rfl
@[simp] theorem sgn_false : (sgn false : K) = -1 := rfl

theorem sgn_sq (b : Bool) : (sgn b : K) ^ 2 = 1 := by
  cases b <;> simp [sgn]

theorem sgn_not (b : Bool) : (sgn (!b) : K) = - sgn b := by
  cases b <;> simp [sgn]

/-- The number of paths of length `n` is `2^n`; each has probability `2^{-n} > 0`. -/
theorem card_paths (n : ℕ) : Fintype.card (Fin n → Bool) = 2 ^ n := by
  simp

theorem path_prob_pos (n : ℕ) : (0 : K) < 1 / (2 : K) ^ n := by
  positivity

/-- Expectation under the uniform measure on paths of length `n`. -/
noncomputable def E {n : ℕ} (X : (Fin n → Bool) → K) : K :=
  (∑ ω, X ω) / (2 : K) ^ n

theorem E_const {n : ℕ} (c : K) : E (fun _ : Fin n → Bool => c) = c := by
  unfold E
  rw [Finset.sum_const, Finset.card_univ, card_paths]
  simp [nsmul_eq_mul]

/-- Flip the `l`-th coin. -/
def flip {n : ℕ} (l : Fin n) : Equiv.Perm (Fin n → Bool) where
  toFun ω := Function.update ω l (!ω l)
  invFun ω := Function.update ω l (!ω l)
  left_inv ω := by
    funext j
    by_cases h : j = l
    · subst h; simp
    · simp [Function.update_of_ne h]
  right_inv ω := by
    funext j
    by_cases h : j = l
    · subst h; simp
    · simp [Function.update_of_ne h]

theorem flip_self {n : ℕ} (l : Fin n) (ω : Fin n → Bool) : flip l ω l = !ω l := by
  simp [flip]

theorem flip_ne {n : ℕ} {l j : Fin n} (h : j ≠ l) (ω : Fin n → Bool) :
    flip l ω j = ω j := by
  simp [flip, Function.update_of_ne h]

/-- **Fundamental cancellation.**  If `g` does not depend on the `l`-th coin,
then `∑_ω g(ω) ξ_l(ω) = 0`.  (Martingale-increment property.) -/
theorem sum_mul_sgn_eq_zero {n : ℕ} (l : Fin n) (g : (Fin n → Bool) → K)
    (hg : ∀ ω, g (flip l ω) = g ω) : ∑ ω, g ω * sgn (ω l) = 0 := by
  have h := Equiv.sum_comp (flip l) (fun ω => g ω * sgn (ω l))
  simp only [hg, flip_self, sgn_not] at h
  have h2 : ∑ ω, g ω * -sgn (ω l) = - ∑ ω, g ω * sgn (ω l) := by
    rw [← Finset.sum_neg_distrib]; congr 1; funext ω; ring
  rw [h2] at h
  linarith

/-- Coins have mean zero. -/
theorem sum_sgn {n : ℕ} (l : Fin n) : ∑ ω : Fin n → Bool, (sgn (ω l) : K) = 0 := by
  have := sum_mul_sgn_eq_zero (K := K) l (fun _ => 1) (fun _ => rfl)
  simpa using this

/-- **White-noise covariance.** `∑_ω ξ_j ξ_k = 2^n δ_{jk}`; dividing by
`2^n τ` gives `E[η_j η_k] = δ_{jk}/τ` for the white noise `η = ξ/√τ`. -/
theorem sum_sgn_mul_sgn {n : ℕ} (j k : Fin n) :
    ∑ ω : Fin n → Bool, (sgn (ω j) : K) * sgn (ω k) =
      if j = k then (2 : K) ^ n else 0 := by
  split_ifs with h
  · subst h
    simp_rw [← sq, sgn_sq]
    simp
  · exact sum_mul_sgn_eq_zero k (fun ω => sgn (ω j))
      (fun ω => by simp [flip_ne h])

theorem E_white_noise {n : ℕ} (s : K) (hs : s ≠ 0) (j k : Fin n) :
    E (fun ω : Fin n → Bool => (sgn (ω j) / s) * (sgn (ω k) / s)) =
      if j = k then 1 / s ^ 2 else 0 := by
  unfold E
  have : ∀ ω : Fin n → Bool, (sgn (ω j) / s) * (sgn (ω k) / s)
      = ((sgn (ω j) : K) * sgn (ω k)) / s ^ 2 := fun ω => by field_simp
  simp_rw [this, ← Finset.sum_div, sum_sgn_mul_sgn]
  split_ifs
  · field_simp
  · simp

/-! ## The Anderson walk and `(ΔW)^2 = τ` -/

/-- Anderson walk at time index `k`: `W_k = ∑_{j<k} ξ_j s`. -/
def W {n : ℕ} (s : K) (ω : Fin n → Bool) (k : ℕ) : K :=
  ∑ j ∈ Finset.univ.filter (fun j : Fin n => (j : ℕ) < k), sgn (ω j) * s

/-- **`thm:ito-exact`.**  `(ΔW)^2 = τ` exactly, on every path and every cell. -/
theorem ito_exact (s : K) (b : Bool) : (sgn b * s) ^ 2 = s ^ 2 := by
  rw [mul_pow, sgn_sq, one_mul]

/-- **Lévy's identity** `∑ (ΔW)^2 = nτ = t`, for every path: an identity,
not a limit in probability. -/
theorem quadratic_variation {n : ℕ} (s : K) (ω : Fin n → Bool) :
    ∑ k : Fin n, (sgn (ω k) * s) ^ 2 = n * s ^ 2 := by
  simp [ito_exact]

/-! ## Exact Itô formula -/

/-- Exact Itô formula for `W^2`. -/
theorem ito_sq (w d τ : K) (hd : d ^ 2 = τ) : (w + d) ^ 2 - w ^ 2 = 2 * w * d + τ := by
  rw [← hd]; ring

/-- Exact Itô formula for `W^3`. -/
theorem ito_cube (w d τ : K) (hd : d ^ 2 = τ) :
    (w + d) ^ 3 - w ^ 3 = 3 * w ^ 2 * d + 3 * w * τ + τ * d := by
  rw [← hd]; ring

/-- Exact Itô formula for `W^4`. -/
theorem ito_quartic (w d τ : K) (hd : d ^ 2 = τ) :
    (w + d) ^ 4 - w ^ 4 = 4 * w ^ 3 * d + 6 * w ^ 2 * τ + 4 * w * τ * d + τ ^ 2 := by
  rw [← hd]; ring

/-- **Exact Itô formula (`thm:stoch-ito-formula`).**  For any `f` and a step
`d = ±2ε`, `f(x+d) - f(x) = ½(D⁺f + D⁻f)(x)·d + ½ D⁺D⁻f(x)·(2ε)^2`, with no
remainder: the Itô correction is the granular second derivative times `τ`. -/
theorem ito_formula (ε : K) (hε : ε ≠ 0) (f : K → K) (x : K) (b : Bool) :
    f (x + sgn b * (2 * ε)) - f x
      = (QE.Dp ε f x + QE.Dm ε f x) / 2 * (sgn b * (2 * ε))
        + (QE.Dp ε (QE.Dm ε f) x) / 2 * (2 * ε) ^ 2 := by
  unfold QE.Dp QE.Dm
  have h1 : x + 2 * ε - 2 * ε = x := by ring
  rw [h1]
  cases b
  · simp only [sgn_false]
    have h2 : x + -1 * (2 * ε) = x - 2 * ε := by ring
    rw [h2]; field_simp; ring
  · simp only [sgn_true]
    have h2 : x + 1 * (2 * ε) = x + 2 * ε := by ring
    rw [h2]; field_simp; ring

/-- Summed exact Itô formula along any path of a `±2ε` walk. -/
theorem ito_formula_sum (ε : K) (hε : ε ≠ 0) (f : K → K) (w : ℕ → K)
    (b : ℕ → Bool) (hw : ∀ k, w (k + 1) = w k + sgn (b k) * (2 * ε)) (n : ℕ) :
    f (w n) - f (w 0)
      = ∑ k ∈ range n, (QE.Dp ε f (w k) + QE.Dm ε f (w k)) / 2 * (w (k + 1) - w k)
        + ∑ k ∈ range n, (QE.Dp ε (QE.Dm ε f) (w k)) / 2 * (2 * ε) ^ 2 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, Finset.sum_range_succ]
    have hi := ito_formula ε hε f (w n) (b n)
    rw [hw n, add_sub_cancel_left]
    linarith [ih, hi]

/-! ## Itô, Stratonovich and the λ-family -/

/-- **Itô–Stratonovich difference (`thm:stoch-ito-strat`).**  Evaluating the
integrand at `(1-λ) H_k + λ H_{k+1}` changes the sum by exactly
`λ ∑ ΔH ΔW`; `λ = 0` is Itô (`[t_k,t_{k+1})`), `λ = 1/2` Stratonovich. -/
theorem lambda_sum (lam : K) (H W : ℕ → K) (n : ℕ) :
    ∑ k ∈ range n, ((1 - lam) * H k + lam * H (k + 1)) * (W (k + 1) - W k)
      = ∑ k ∈ range n, H k * (W (k + 1) - W k)
        + lam * ∑ k ∈ range n, (H (k + 1) - H k) * (W (k + 1) - W k) := by
  induction n with
  | zero => simp
  | succ n ih => simp only [Finset.sum_range_succ, ih]; ring

/-- Itô integral `∫ W dW`, exactly: `½(W_n² − W_0²) − ½ nτ`. -/
theorem ito_W_dW (τ : K) (W : ℕ → K) (hW : ∀ k, (W (k + 1) - W k) ^ 2 = τ) (n : ℕ) :
    ∑ k ∈ range n, W k * (W (k + 1) - W k) = (W n ^ 2 - W 0 ^ 2) / 2 - n * τ / 2 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih]
    have := hW n
    push_cast
    nlinarith [this]

/-- Stratonovich integral `∫ W ∘ dW = ½(W_n² − W_0²)` exactly (no hypothesis). -/
theorem strat_W_dW (W : ℕ → K) (n : ℕ) :
    ∑ k ∈ range n, (W k + W (k + 1)) / 2 * (W (k + 1) - W k) = (W n ^ 2 - W 0 ^ 2) / 2 := by
  induction n with
  | zero => simp
  | succ n ih => rw [Finset.sum_range_succ, ih]; ring

/-- The λ-integral of `W dW` is `½(W_n² − W_0²) + (λ − ½) nτ`. -/
theorem lambda_W_dW (lam τ : K) (W : ℕ → K) (hW : ∀ k, (W (k + 1) - W k) ^ 2 = τ)
    (n : ℕ) :
    ∑ k ∈ range n, ((1 - lam) * W k + lam * W (k + 1)) * (W (k + 1) - W k)
      = (W n ^ 2 - W 0 ^ 2) / 2 + (lam - 1 / 2) * (n * τ) := by
  rw [lambda_sum, ito_W_dW τ W hW]
  have : ∑ k ∈ range n, (W (k + 1) - W k) * (W (k + 1) - W k) = n * τ := by
    simp_rw [← sq, hW]; simp
  rw [this]; ring

/-! ## Adapted integrands, Itô isometry, stopping -/

/-- `H` is adapted (non-anticipating): `H k` depends only on coins `j < k`. -/
def Adapted {n : ℕ} (H : Fin n → (Fin n → Bool) → K) : Prop :=
  ∀ k ω ω', (∀ j : Fin n, j < k → ω j = ω' j) → H k ω = H k ω'

theorem Adapted.flip_eq {n : ℕ} {H : Fin n → (Fin n → Bool) → K} (hH : Adapted H)
    {k l : Fin n} (hkl : k ≤ l) (ω : Fin n → Bool) : H k (flip l ω) = H k ω := by
  apply hH
  intro j hj
  exact flip_ne (ne_of_lt (lt_of_lt_of_le hj hkl)) ω

/-- Stochastic (Itô) sum `∑_k H_k ξ_k` (multiply by `s` for `∑ H ΔW`). -/
def stochSum {n : ℕ} (H : Fin n → (Fin n → Bool) → K) (ω : Fin n → Bool) : K :=
  ∑ k, H k ω * sgn (ω k)

/-- The Itô sum of an adapted integrand has mean zero. -/
theorem sum_stochSum_eq_zero {n : ℕ} (H : Fin n → (Fin n → Bool) → K) (hH : Adapted H) :
    ∑ ω, stochSum H ω = 0 := by
  unfold stochSum
  rw [Finset.sum_comm]
  apply Finset.sum_eq_zero
  intro k _
  exact sum_mul_sgn_eq_zero k (H k) (fun ω => hH.flip_eq le_rfl ω)

/-- **Itô isometry (`thm:stoch-isometry`)**, exact on `{±1}^n`:
`∑_ω (∑_k H_k ξ_k)^2 = ∑_ω ∑_k H_k^2` for adapted `H`. -/
theorem ito_isometry {n : ℕ} (H : Fin n → (Fin n → Bool) → K) (hH : Adapted H) :
    ∑ ω, (stochSum H ω) ^ 2 = ∑ ω, ∑ k, (H k ω) ^ 2 := by
  have key : ∀ k l : Fin n,
      ∑ ω, (H k ω * sgn (ω k)) * (H l ω * sgn (ω l))
        = if k = l then ∑ ω, (H k ω) ^ 2 else 0 := by
    intro k l
    split_ifs with hkl
    · subst hkl
      apply Finset.sum_congr rfl
      intro ω _
      have := sgn_sq (K := K) (ω k)
      calc H k ω * sgn (ω k) * (H k ω * sgn (ω k))
          = (H k ω) ^ 2 * (sgn (ω k)) ^ 2 := by ring
        _ = (H k ω) ^ 2 := by rw [this, mul_one]
    · rcases lt_or_gt_of_ne hkl with h | h
      · have := sum_mul_sgn_eq_zero l (fun ω => H k ω * sgn (ω k) * H l ω)
          (fun ω => by
            rw [hH.flip_eq h.le, hH.flip_eq le_rfl, flip_ne (ne_of_lt h)])
        rw [← this]
        apply Finset.sum_congr rfl; intro ω _; ring
      · have := sum_mul_sgn_eq_zero k (fun ω => H l ω * sgn (ω l) * H k ω)
          (fun ω => by
            rw [hH.flip_eq h.le, hH.flip_eq le_rfl, flip_ne (ne_of_lt h)])
        rw [← this]
        apply Finset.sum_congr rfl; intro ω _; ring
  unfold stochSum
  simp_rw [sq, Finset.sum_mul_sum]
  rw [Finset.sum_comm]
  rw [Finset.sum_congr rfl (fun k _ => Finset.sum_comm)]
  simp_rw [key]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  rw [Finset.sum_comm]
  simp_rw [sq]

/-- Itô isometry in expectation form with the physical step:
`E[(∑ H ΔW)^2] = E[∑ H^2 τ]`, `ΔW = ξ s`, `τ = s^2`. -/
theorem ito_isometry_E {n : ℕ} (s : K) (H : Fin n → (Fin n → Bool) → K) (hH : Adapted H) :
    E (fun ω => (∑ k, H k ω * (sgn (ω k) * s)) ^ 2)
      = E (fun ω => ∑ k, (H k ω) ^ 2 * s ^ 2) := by
  unfold E
  congr 1
  have h1 : ∀ ω : Fin n → Bool, (∑ k, H k ω * (sgn (ω k) * s)) ^ 2
      = (stochSum H ω) ^ 2 * s ^ 2 := by
    intro ω; unfold stochSum
    rw [← mul_pow, Finset.sum_mul]; congr 1
    apply Finset.sum_congr rfl; intro k _; ring
  have h2 : ∀ ω : Fin n → Bool, ∑ k, (H k ω) ^ 2 * s ^ 2 = (∑ k, (H k ω) ^ 2) * s ^ 2 := by
    intro ω; rw [Finset.sum_mul]
  simp_rw [h1, h2, ← Finset.sum_mul, ito_isometry H hH]

/-- Itô sum up to time index `k`: `M_k = ∑_{l<k} H_l ξ_l`. -/
def stochSumTo {n : ℕ} (H : Fin n → (Fin n → Bool) → K) (k : ℕ) (ω : Fin n → Bool) : K :=
  ∑ l ∈ Finset.univ.filter (fun l : Fin n => (l : ℕ) < k), H l ω * sgn (ω l)

/-- **Martingale property**, exact: for every `Y` determined by the coins
before time `k`, `E[Y (M_n − M_k)] = 0`, i.e. `E[M_n | 𝓕_k] = M_k`. -/
theorem martingale_property {n : ℕ} (H : Fin n → (Fin n → Bool) → K) (hH : Adapted H)
    (k : ℕ) (Y : (Fin n → Bool) → K)
    (hY : ∀ ω ω', (∀ j : Fin n, (j : ℕ) < k → ω j = ω' j) → Y ω = Y ω') :
    ∑ ω, Y ω * (stochSum H ω - stochSumTo H k ω) = 0 := by
  have hsplit : ∀ ω, stochSum H ω - stochSumTo H k ω
      = ∑ l ∈ Finset.univ.filter (fun l : Fin n => ¬ (l : ℕ) < k), H l ω * sgn (ω l) := by
    intro ω
    unfold stochSum stochSumTo
    rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun l : Fin n => (l : ℕ) < k)]
    ring
  simp_rw [hsplit, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_eq_zero
  intro l hl
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_lt] at hl
  have := sum_mul_sgn_eq_zero l (fun ω => Y ω * H l ω) (fun ω => by
    rw [hH.flip_eq le_rfl]
    congr 1
    apply hY
    intro j hj
    exact flip_ne (fun h => by rw [h] at hj; omega) ω)
  rw [← this]
  apply Finset.sum_congr rfl; intro ω _; ring

/-- A stopping time: whether `k < T` is decided by the coins `j < k`. -/
def IsStoppingTime {n : ℕ} (T : (Fin n → Bool) → ℕ) : Prop :=
  ∀ (k : Fin n) ω ω', (∀ j : Fin n, j < k → ω j = ω' j) → ((k : ℕ) < T ω ↔ (k : ℕ) < T ω')

/-- The indicator integrand `1_{k < T}` of a stopping time. -/
def stopInd {n : ℕ} (T : (Fin n → Bool) → ℕ) : Fin n → (Fin n → Bool) → K :=
  fun k ω => if (k : ℕ) < T ω then 1 else 0

theorem stopInd_adapted {n : ℕ} (T : (Fin n → Bool) → ℕ) (hT : IsStoppingTime T) :
    Adapted (stopInd (K := K) T) := by
  intro k ω ω' h
  unfold stopInd
  rw [if_congr (hT k ω ω' h) rfl rfl]

/-- The stopped walk `W_{T∧n}/s = ∑_{k < T} ξ_k`. -/
theorem stopped_walk {n : ℕ} (s : K) (T : (Fin n → Bool) → ℕ) (ω : Fin n → Bool) :
    stochSum (stopInd T) ω * s = W s ω (T ω) := by
  unfold stochSum stopInd W
  rw [Finset.sum_mul, Finset.sum_filter]
  apply Finset.sum_congr rfl; intro k _
  split_ifs <;> ring

/-- **Optional stopping** (exact, hyperfinite horizon): `E[W_{T∧n}] = 0`. -/
theorem optional_stopping {n : ℕ} (s : K) (T : (Fin n → Bool) → ℕ) (hT : IsStoppingTime T) :
    E (fun ω => W s ω (T ω)) = 0 := by
  unfold E
  simp_rw [← stopped_walk s T, ← Finset.sum_mul,
    sum_stochSum_eq_zero _ (stopInd_adapted (K := K) T hT)]
  simp

/-- **Wald's second identity** (exact): `E[W_{T∧n}^2] = τ E[T ∧ n]`. -/
theorem wald_second {n : ℕ} (s : K) (T : (Fin n → Bool) → ℕ) (hT : IsStoppingTime T) :
    E (fun ω => (W s ω (T ω)) ^ 2) = s ^ 2 * E (fun ω => ((min n (T ω) : ℕ) : K)) := by
  unfold E
  simp_rw [← stopped_walk s T, mul_pow, ← Finset.sum_mul,
    ito_isometry _ (stopInd_adapted (K := K) T hT)]
  have : ∀ ω : Fin n → Bool, ∑ k, (stopInd (K := K) T k ω) ^ 2 = ((min n (T ω) : ℕ) : K) := by
    intro ω
    unfold stopInd
    have h' : ∀ k : Fin n, ((if (k : ℕ) < T ω then (1 : K) else 0) ^ 2)
        = if (k : ℕ) < T ω then 1 else 0 := fun k => by split_ifs <;> simp
    simp_rw [h']
    rw [Finset.sum_boole, Fin.card_filter_val_lt]
  simp_rw [this]
  ring

/-- Gambler's ruin, exact finite-horizon form: if the stopped walk takes
the value `a` with probability `p`, `-b` with probability `q`, and on the
remaining event (probability `r`) has mean value `m` with `|m| ≤ c`,
then `|a p - b q| ≤ c r`.  (`E[W_{T∧n}] = 0` gives `a p - b q + m r = 0`.) -/
theorem ruin_bound (a b p q r m c : K) (h0 : a * p - b * q + m * r = 0)
    (hr : 0 ≤ r) (hm : |m| ≤ c) : |a * p - b * q| ≤ c * r := by
  have : a * p - b * q = -(m * r) := by linarith
  rw [this, abs_neg, abs_mul, abs_of_nonneg hr]
  exact mul_le_mul_of_nonneg_right hm hr

/-! ## The binomial heat kernel and exact moments -/

/-- The unscaled walk `S = ∑ ξ_j` on paths of length `k`. -/
def S {k : ℕ} (ω : Fin k → Bool) : K := ∑ j, sgn (ω j)

/-- One-step decomposition of a path sum (first coin vs the rest). -/
theorem sum_succ (k : ℕ) (g : K → K) :
    ∑ ω : Fin (k + 1) → Bool, g (S ω) = ∑ ω : Fin k → Bool, (g (S ω + 1) + g (S ω - 1)) := by
  rw [← (Fin.consEquiv (fun _ => Bool)).sum_comp]
  rw [Fintype.sum_prod_type]
  simp only [Fin.consEquiv_apply, S, Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ]
  rw [Fintype.sum_bool, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl; intro ω _
  simp [sgn]; ring_nf

/-- Value function `u(k,x) = E[f(x + W_k)]` of the walk. -/
noncomputable def u (s : K) (f : K → K) (k : ℕ) (x : K) : K :=
  (∑ ω : Fin k → Bool, f (x + S ω * s)) / (2 : K) ^ k

/-- **Exact granular heat equation (backward Kolmogorov / Feynman–Kac with
zero potential)**: `u(k+1,x) = ½(u(k,x+s) + u(k,x-s))`. -/
theorem heat_step (s : K) (f : K → K) (k : ℕ) (x : K) :
    u s f (k + 1) x = (u s f k (x + s) + u s f k (x - s)) / 2 := by
  unfold u
  rw [sum_succ k (fun y => f (x + y * s))]
  have h1 : ∀ ω : Fin k → Bool, f (x + (S ω + 1) * s) = f (x + s + S ω * s) :=
    fun ω => by congr 1; ring
  have h2 : ∀ ω : Fin k → Bool, f (x + (S ω - 1) * s) = f (x - s + S ω * s) :=
    fun ω => by congr 1; ring
  simp_rw [h1, h2, Finset.sum_add_distrib]
  rw [pow_succ]
  field_simp

/-- Heat equation in granular-derivative form, `s = 2ε`, `τ = (2ε)^2`:
`(u(k+1,x) − u(k,x))/τ = ½ D⁺D⁻ u(k,·)(x)`. -/
theorem heat_equation (ε : K) (hε : ε ≠ 0) (f : K → K) (k : ℕ) (x : K) :
    (u (2 * ε) f (k + 1) x - u (2 * ε) f k x) / (2 * ε) ^ 2
      = QE.Dp ε (QE.Dm ε (u (2 * ε) f k)) x / 2 := by
  rw [heat_step]
  unfold QE.Dp QE.Dm
  have h1 : x + 2 * ε - 2 * ε = x := by ring
  rw [h1]
  field_simp
  ring

theorem sum_S_pow (k : ℕ) (p : ℕ) : ∑ ω : Fin (k + 1) → Bool, (S ω : K) ^ p
    = ∑ ω : Fin k → Bool, ((S ω + 1) ^ p + (S ω - 1) ^ p) :=
  sum_succ k (fun y => y ^ p)

theorem sum_S_one (k : ℕ) : ∑ ω : Fin k → Bool, (S ω : K) = 0 := by
  induction k with
  | zero => simp [S]
  | succ k ih =>
    have := sum_S_pow (K := K) k 1
    simp only [pow_one] at this
    rw [this]
    have : ∀ ω : Fin k → Bool, (S ω + 1 + (S ω - 1) : K) = 2 * S ω := fun ω => by ring
    simp_rw [this, ← Finset.mul_sum, ih, mul_zero]

theorem sum_S_two (k : ℕ) : ∑ ω : Fin k → Bool, (S ω : K) ^ 2 = k * 2 ^ k := by
  induction k with
  | zero => simp [S]
  | succ k ih =>
    rw [sum_S_pow]
    have : ∀ ω : Fin k → Bool, ((S ω + 1) ^ 2 + (S ω - 1) ^ 2 : K) = 2 * S ω ^ 2 + 2 :=
      fun ω => by ring
    simp_rw [this, Finset.sum_add_distrib, ← Finset.mul_sum, ih]
    simp only [Finset.sum_const, Finset.card_univ, card_paths, nsmul_eq_mul]
    push_cast; ring

theorem sum_S_three (k : ℕ) : ∑ ω : Fin k → Bool, (S ω : K) ^ 3 = 0 := by
  induction k with
  | zero => simp [S]
  | succ k ih =>
    rw [sum_S_pow]
    have : ∀ ω : Fin k → Bool, ((S ω + 1) ^ 3 + (S ω - 1) ^ 3 : K) = 2 * S ω ^ 3 + 6 * S ω :=
      fun ω => by ring
    simp_rw [this, Finset.sum_add_distrib, ← Finset.mul_sum, ih, sum_S_one]
    ring

/-- **Exact fourth moment**: `∑ S^4 = (3k² − 2k) 2^k`, i.e.
`E[W_t^4] = 3t² − 2tτ` with `t = kτ`, `τ = s²`. -/
theorem sum_S_four (k : ℕ) : ∑ ω : Fin k → Bool, (S ω : K) ^ 4 = (3 * k ^ 2 - 2 * k) * 2 ^ k := by
  induction k with
  | zero => simp [S]
  | succ k ih =>
    rw [sum_S_pow]
    have : ∀ ω : Fin k → Bool, ((S ω + 1) ^ 4 + (S ω - 1) ^ 4 : K)
        = 2 * S ω ^ 4 + 12 * S ω ^ 2 + 2 := fun ω => by ring
    simp_rw [this, Finset.sum_add_distrib, ← Finset.mul_sum, ih, sum_S_two]
    simp only [Finset.sum_const, Finset.card_univ, card_paths, nsmul_eq_mul]
    push_cast; ring

theorem E_W_four (s : K) (k : ℕ) :
    (∑ ω : Fin k → Bool, (S ω * s : K) ^ 4) / 2 ^ k
      = 3 * (k * s ^ 2) ^ 2 - 2 * (k * s ^ 2) * s ^ 2 := by
  simp_rw [mul_pow, ← Finset.sum_mul, sum_S_four]
  field_simp

theorem E_W_two (s : K) (k : ℕ) :
    (∑ ω : Fin k → Bool, (S ω * s : K) ^ 2) / 2 ^ k = k * s ^ 2 := by
  simp_rw [mul_pow, ← Finset.sum_mul, sum_S_two]
  field_simp

/-! ## Feynman–Kac as a hyperfinite path sum -/

/-- Path functional `f(x + W_k) ∏_{j<k} g(x + W_j)` along a path, written
recursively (first step, then the rest of the path). -/
def pathFK (s : K) (f g : K → K) : (k : ℕ) → (Fin k → Bool) → K → K
  | 0, _, x => f x
  | k + 1, ω, x => g x * pathFK s f g k (Fin.tail ω) (x + sgn (ω 0) * s)

/-- The Feynman–Kac value `v(k,x) = E[f(x+W_k) ∏_{j<k} g(x+W_j)]`, a finite
sum over the `2^k` paths. -/
noncomputable def vFK (s : K) (f g : K → K) (k : ℕ) (x : K) : K :=
  (∑ ω : Fin k → Bool, pathFK s f g k ω x) / (2 : K) ^ k

/-- **Exact Feynman–Kac recursion**: `v(k+1,x) = g(x) · ½(v(k,x+s) + v(k,x−s))`.
With `g = 1 − Vτ` this is the granular equation
`(v(k+1) − v(k))/τ = ½ D⁺D⁻ v − V v(k+1-step average)`. -/
theorem fk_step (s : K) (f g : K → K) (k : ℕ) (x : K) :
    vFK s f g (k + 1) x = g x * ((vFK s f g k (x + s) + vFK s f g k (x - s)) / 2) := by
  unfold vFK
  rw [← (Fin.consEquiv (fun _ => Bool)).sum_comp, Fintype.sum_prod_type]
  simp only [Fin.consEquiv_apply, pathFK, Fin.cons_zero, Fintype.sum_bool,
    sgn_true, sgn_false]
  rw [← Finset.mul_sum, ← Finset.mul_sum]
  have h1 : x + 1 * s = x + s := by ring
  have h2 : x + -1 * s = x - s := by ring
  rw [h1, h2, pow_succ]
  field_simp
  rfl

/-- With `g ≡ 1` the Feynman–Kac path functional is just `f(x + W_k)`. -/
theorem pathFK_one (s : K) (f : K → K) (k : ℕ) (ω : Fin k → Bool) (x : K) :
    pathFK s f (fun _ => 1) k ω x = f (x + S ω * s) := by
  induction k generalizing x with
  | zero => simp [pathFK, S]
  | succ k ih =>
    simp only [pathFK, one_mul, ih]
    congr 1
    simp only [S, Fin.sum_univ_succ, Fin.tail]
    ring

/-! ## Granular SDEs: two-point decomposition, generator, Dynkin -/

/-- **Two-point decomposition.**  Every function of one coin is
`mean + ξ · half-difference`: the basis `{1, ξ}` spans all of them. -/
theorem two_point (φ : Bool → K) (b : Bool) :
    φ b = (φ true + φ false) / 2 + sgn b * ((φ true - φ false) / 2) := by
  cases b <;> simp [sgn] <;> ring

/-- **Exact Itô formula for an Itô recursion** `X' = X + aτ + b ΔW`,
`ΔW = ξ s`: `f(X') − f(X) = A ΔW + B τ` with explicit `A` (granular
diffusion coefficient) and `B` (granular generator applied to `f`). -/
theorem ito_formula_sde (f : K → K) (x a b τ s : K) (hs : s ≠ 0) (hτ : τ ≠ 0) (c : Bool) :
    f (x + a * τ + b * (sgn c * s)) - f x
      = ((f (x + a * τ + b * s) - f (x + a * τ - b * s)) / (2 * s)) * (sgn c * s)
        + (((f (x + a * τ + b * s) + f (x + a * τ - b * s)) / 2 - f x) / τ) * τ := by
  cases c
  · simp only [sgn_false]
    have : x + a * τ + b * (-1 * s) = x + a * τ - b * s := by ring
    rw [this]; field_simp; ring
  · simp only [sgn_true]
    have : x + a * τ + b * (1 * s) = x + a * τ + b * s := by ring
    rw [this]; field_simp; ring

/-- **Exact Dynkin formula.**  If each increment is `A_k ξ_k + B_k` with `A`
adapted, the expected total increment is the expected sum of the drifts. -/
theorem dynkin {n : ℕ} (A B : Fin n → (Fin n → Bool) → K) (hA : Adapted A) :
    ∑ ω, ∑ k, (A k ω * sgn (ω k) + B k ω) = ∑ ω, ∑ k, B k ω := by
  simp_rw [Finset.sum_add_distrib]
  have := sum_stochSum_eq_zero A hA
  unfold stochSum at this
  rw [this, zero_add]

/-! ## Exact Girsanov (change of drift) -/

/-- Splitting a path sum at the first coin. -/
theorem sum_cons (k : ℕ) (g : (Fin (k + 1) → Bool) → K) :
    ∑ ω, g ω = ∑ ω : Fin k → Bool, (g (Fin.cons true ω) + g (Fin.cons false ω)) := by
  rw [← (Fin.consEquiv (fun _ => Bool)).sum_comp, Fintype.sum_prod_type, Fintype.sum_bool,
    ← Finset.sum_add_distrib]
  rfl

/-- Girsanov density for a constant tilt `θ`: `Z = ∏ (1 + θ ξ_k)`. -/
def Z (θ : K) {k : ℕ} (ω : Fin k → Bool) : K := ∏ j, (1 + θ * sgn (ω j))

theorem Z_cons (θ : K) {k : ℕ} (b : Bool) (ω : Fin k → Bool) :
    Z θ (Fin.cons b ω : Fin (k + 1) → Bool) = (1 + θ * sgn b) * Z θ ω := by
  simp [Z, Fin.prod_univ_succ]

theorem S_cons {k : ℕ} (b : Bool) (ω : Fin k → Bool) :
    (S (Fin.cons b ω : Fin (k + 1) → Bool) : K) = sgn b + S ω := by
  simp [S, Fin.sum_univ_succ]

/-- The tilted weights are positive when `|θ| < 1`. -/
theorem Z_pos (θ : K) (hθ : |θ| < 1) {k : ℕ} (ω : Fin k → Bool) : 0 < Z θ ω := by
  unfold Z
  apply Finset.prod_pos
  intro j _
  rcases abs_lt.mp hθ with ⟨h1, h2⟩
  cases ω j <;> simp [sgn] <;> linarith

/-- The tilted measure `Q(ω) = Z(ω)/2^k` is a probability: `∑ Z = 2^k`. -/
theorem sum_Z (θ : K) (k : ℕ) : ∑ ω : Fin k → Bool, Z θ ω = 2 ^ k := by
  induction k with
  | zero => simp [Z]
  | succ k ih =>
    rw [sum_cons]
    simp_rw [Z_cons, sgn_true, sgn_false]
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, ih, pow_succ]
    ring

/-- **Exact Girsanov drift**: under `Q`, `E_Q[S_k] = kθ`; with `θ = μ s`
this is `E_Q[W_t] = μ t` exactly. -/
theorem sum_Z_S (θ : K) (k : ℕ) :
    ∑ ω : Fin k → Bool, Z θ ω * S ω = k * θ * 2 ^ k := by
  induction k with
  | zero => simp [S]
  | succ k ih =>
    rw [sum_cons]
    simp_rw [Z_cons, S_cons, sgn_true, sgn_false]
    have : ∀ ω : Fin k → Bool,
        (1 + θ * 1) * Z θ ω * (1 + S ω) + (1 + θ * -1) * Z θ ω * (-1 + S ω)
          = 2 * θ * Z θ ω + 2 * (Z θ ω * S ω) := fun ω => by ring
    simp_rw [this, Finset.sum_add_distrib, ← Finset.mul_sum, sum_Z, ih]
    push_cast; ring

/-! ## Tanaka's formula and local time at the point 0 -/

/-- Integer sign as an element of `K`. -/
def isgn (m : ℤ) : K := if 0 < m then 1 else if m < 0 then -1 else 0

/-- Symmetric granular derivative of `|x|` at the lattice point `2εm`. -/
theorem Dsym_abs (ε : K) (hε : 0 < ε) (m : ℤ) :
    (QE.Dp ε (fun x => |x|) (2 * ε * m) + QE.Dm ε (fun x => |x|) (2 * ε * m)) / 2
      = isgn m := by
  unfold QE.Dp QE.Dm isgn
  beta_reduce
  have hne : (2 * ε) ≠ 0 := by positivity
  rcases lt_trichotomy m 0 with h | h | h
  · have hm : (m : K) ≤ -1 := by exact_mod_cast (by omega : m ≤ -1)
    have hk : 2 * ε * (m : K) ≤ -(2 * ε) := by nlinarith
    rw [if_neg (by omega), if_pos h]
    rw [abs_of_nonpos (by linarith : 2 * ε * (m : K) + 2 * ε ≤ 0),
      abs_of_nonpos (by linarith : 2 * ε * (m : K) ≤ 0),
      abs_of_nonpos (by linarith : 2 * ε * (m : K) - 2 * ε ≤ 0)]
    field_simp; ring
  · subst h
    simp only [Int.cast_zero, mul_zero, zero_add, zero_sub, abs_zero, sub_zero, abs_neg,
      lt_irrefl, ite_false]
    rw [abs_of_pos (by linarith : (0 : K) < 2 * ε)]
    field_simp; ring
  · have hm : (1 : K) ≤ m := by exact_mod_cast (by omega : 1 ≤ m)
    have hk : 2 * ε ≤ 2 * ε * (m : K) := by nlinarith
    rw [if_pos h]
    rw [abs_of_nonneg (by linarith : 0 ≤ 2 * ε * (m : K) + 2 * ε),
      abs_of_nonneg (by linarith : 0 ≤ 2 * ε * (m : K)),
      abs_of_nonneg (by linarith : 0 ≤ 2 * ε * (m : K) - 2 * ε)]
    field_simp; ring

/-- Second granular derivative of `|x|` at `2εm`: `2 δ_ε`, i.e. `1/ε` at the
point `0` and `0` elsewhere.  The point 0 has size, and `|x|` has a genuine
granular second derivative there. -/
theorem Dsec_abs (ε : K) (hε : 0 < ε) (m : ℤ) :
    QE.Dp ε (QE.Dm ε (fun x => |x|)) (2 * ε * m) = if m = 0 then 1 / ε else 0 := by
  unfold QE.Dp QE.Dm
  beta_reduce
  have h1 : 2 * ε * (m : K) + 2 * ε - 2 * ε = 2 * ε * m := by ring
  rw [h1]
  rcases lt_trichotomy m 0 with h | h | h
  · have hm : (m : K) ≤ -1 := by exact_mod_cast (by omega : m ≤ -1)
    have hk : 2 * ε * (m : K) ≤ -(2 * ε) := by nlinarith
    rw [if_neg (by omega)]
    rw [abs_of_nonpos (by linarith : 2 * ε * (m : K) + 2 * ε ≤ 0),
      abs_of_nonpos (by linarith : 2 * ε * (m : K) ≤ 0),
      abs_of_nonpos (by linarith : 2 * ε * (m : K) - 2 * ε ≤ 0)]
    field_simp; ring
  · subst h
    simp only [Int.cast_zero, mul_zero, zero_add, zero_sub, abs_zero, sub_zero, abs_neg,
      ite_true]
    rw [abs_of_pos (by linarith : (0 : K) < 2 * ε)]
    field_simp; ring
  · have hm : (1 : K) ≤ m := by exact_mod_cast (by omega : 1 ≤ m)
    have hk : 2 * ε ≤ 2 * ε * (m : K) := by nlinarith
    rw [if_neg (by omega)]
    rw [abs_of_nonneg (by linarith : 0 ≤ 2 * ε * (m : K) + 2 * ε),
      abs_of_nonneg (by linarith : 0 ≤ 2 * ε * (m : K)),
      abs_of_nonneg (by linarith : 0 ≤ 2 * ε * (m : K) - 2 * ε)]
    field_simp; ring

/-- **Exact Tanaka formula.**  For a `±2ε` lattice walk `w_k = 2ε m_k`,
`|w_n| − |w_0| = ∑ sgn(w_k) Δw_k + 2ε · #{k < n : w_k = 0}`:
the local time at `0` is the number of visits to the point `0` times its
diameter. -/
theorem tanaka (ε : K) (hε : 0 < ε) (m : ℕ → ℤ) (b : ℕ → Bool)
    (hw : ∀ k, 2 * ε * (m (k + 1) : K) = 2 * ε * m k + sgn (b k) * (2 * ε)) (n : ℕ) :
    |2 * ε * (m n : K)| - |2 * ε * (m 0 : K)|
      = ∑ k ∈ range n, isgn (m k) * (2 * ε * (m (k + 1) : K) - 2 * ε * m k)
        + 2 * ε * ((range n).filter (fun k => m k = 0)).card := by
  have h := ito_formula_sum ε hε.ne' (fun x => |x|) (fun k => 2 * ε * (m k : K)) b hw n
  rw [h]
  congr 1
  · apply Finset.sum_congr rfl; intro k _
    rw [Dsym_abs ε hε]
  · rw [Finset.card_filter, Nat.cast_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl; intro k _
    rw [Dsec_abs ε hε]
    split_ifs <;> field_simp <;> ring

/-! ## Two-dimensional exact Itô formula -/

/-- **Four-point decomposition** of a function of two coins in the basis
`{1, ξ, ξ', ξξ'}`. -/
theorem four_point (φ : Bool → Bool → K) (b c : Bool) :
    φ b c = (φ true true + φ true false + φ false true + φ false false) / 4
      + sgn b * ((φ true true + φ true false - φ false true - φ false false) / 4)
      + sgn c * ((φ true true - φ true false + φ false true - φ false false) / 4)
      + sgn b * sgn c * ((φ true true - φ true false - φ false true + φ false false) / 4) := by
  cases b <;> cases c <;> simp [sgn] <;> ring

/-- **Exact two-dimensional Itô formula** for independent increments
`d₁ = ξ s`, `d₂ = ξ' s`, `τ = s²`: the increment of `f` is a combination of
`d₁`, `d₂`, the cross term `d₁ d₂` (mixed granular derivative) and `τ`
(diagonal granular Laplacian). -/
theorem ito_formula_2d (f : K → K → K) (x y s : K) (hs : s ≠ 0) (b c : Bool) :
    f (x + sgn b * s) (y + sgn c * s) - f x y
      = ((f (x + s) (y + s) + f (x + s) (y - s) - f (x - s) (y + s) - f (x - s) (y - s))
            / (4 * s)) * (sgn b * s)
        + ((f (x + s) (y + s) - f (x + s) (y - s) + f (x - s) (y + s) - f (x - s) (y - s))
            / (4 * s)) * (sgn c * s)
        + ((f (x + s) (y + s) - f (x + s) (y - s) - f (x - s) (y + s) + f (x - s) (y - s))
            / (4 * s ^ 2)) * ((sgn b * s) * (sgn c * s))
        + (((f (x + s) (y + s) + f (x + s) (y - s) + f (x - s) (y + s) + f (x - s) (y - s)) / 4
            - f x y) / s ^ 2) * s ^ 2 := by
  have e1 : x + -1 * s = x - s := by ring
  have e2 : y + -1 * s = y - s := by ring
  have e3 : x + 1 * s = x + s := by ring
  have e4 : y + 1 * s = y + s := by ring
  cases b <;> cases c <;> simp only [sgn_true, sgn_false, e1, e2, e3, e4] <;> field_simp <;> ring

/-! ## The exponential martingale is a Girsanov density (over ℝ) -/

/-- `e^{θ ξ s} / cosh(θ s) = 1 + tanh(θ s) ξ` for a coin `ξ = ±1`. -/
theorem exp_tilt (θ s : ℝ) (b : Bool) :
    Real.exp (θ * (sgn b * s)) / Real.cosh (θ * s) = 1 + Real.tanh (θ * s) * sgn b := by
  have hc : Real.cosh (θ * s) ≠ 0 := (Real.cosh_pos _).ne'
  rw [Real.tanh_eq_sinh_div_cosh]
  cases b
  · simp only [sgn_false]
    rw [div_eq_iff hc, Real.cosh_eq, Real.sinh_eq]
    have : θ * (-1 * s) = -(θ * s) := by ring
    rw [this]; field_simp; ring
  · simp only [sgn_true]
    rw [div_eq_iff hc, Real.cosh_eq, Real.sinh_eq]
    have : θ * (1 * s) = θ * s := by ring
    rw [this]; field_simp; ring

/-- **Exact moment generating function** of the Anderson walk:
`E[e^{θ W_k}] = cosh(θ s)^k` (shadow: `e^{θ² t/2}`). -/
theorem mgf_walk (θ s : ℝ) (k : ℕ) :
    (∑ ω : Fin k → Bool, Real.exp (θ * (S ω * s))) / 2 ^ k = Real.cosh (θ * s) ^ k := by
  have hc : Real.cosh (θ * s) ≠ 0 := (Real.cosh_pos _).ne'
  have h : ∀ ω : Fin k → Bool, Real.exp (θ * (S ω * s))
      = Real.cosh (θ * s) ^ k * Z (Real.tanh (θ * s)) ω := by
    intro ω
    unfold S Z
    rw [Finset.sum_mul, Finset.mul_sum, Real.exp_sum]
    have hp : Real.cosh (θ * s) ^ k = ∏ _j : Fin k, Real.cosh (θ * s) := by
      simp [Finset.prod_const]
    rw [hp, ← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl; intro j _
    rw [← exp_tilt θ s (ω j)]
    field_simp
  simp_rw [h, ← Finset.mul_sum, sum_Z]
  field_simp

/-! ## Worked examples -/

/-- Granular "Lebesgue measure" on lattice path space `𝕃^n` (the `n`-cell
granular measure of Chapter 3) is invariant under every lattice translation
of paths: it exists, unlike Lebesgue measure on an infinite-dimensional space. -/
theorem path_measure_translation_invariant (n : ℕ) (ε : K) (A : Finset (Fin n → ℤ))
    (v : Fin n → ℤ) :
    QE.muN n ε (A.map (Equiv.addRight v).toEmbedding) = QE.muN n ε A := by
  unfold QE.muN; rw [Finset.card_map]

/-- Exact stationary variance of the granular Ornstein–Uhlenbeck (Langevin)
recursion `X_{k+1} = (1-γτ) X_k + σ η_k τ`, `Var(σ η τ) = σ² τ`:
`V = σ² / (γ (2 - γτ))` is the fixed point of `V ↦ (1-γτ)² V + σ² τ`. -/
theorem ou_stationary (γ σ τ : K) (hγ : γ ≠ 0) (h2 : 2 - γ * τ ≠ 0) :
    (1 - γ * τ) ^ 2 * (σ ^ 2 / (γ * (2 - γ * τ))) + σ ^ 2 * τ
      = σ ^ 2 / (γ * (2 - γ * τ)) := by
  field_simp; ring

/-- The Stratonovich (symmetric-cell) step for `dX = X ∘ dZ` is the Cayley
map: `X' = X (2 + z)/(2 - z)` solves `X' - X = z (X + X')/2` exactly. -/
theorem cayley_step (X z : K) (hz : 2 - z ≠ 0) :
    X * (2 + z) / (2 - z) - X = z * (X + X * (2 + z) / (2 - z)) / 2 := by
  field_simp; ring

end QE.Stoch
