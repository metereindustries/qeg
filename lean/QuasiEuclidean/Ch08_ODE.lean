-- SPDX-License-Identifier: MIT
-- Copyright 2026 Metere Industries, Inc. Author: Alfredo Metere.
-- Quasi-Euclidean Granular Geometry. Any derivative work must carry this notice:
--   This work is derivative of the Quasi-Euclidean Granular Geometry book
--   authored by Alfredo Metere. Copyright 2026 Metere Industries, Inc.
--   All rights reserved
-- See LICENSE.md and NOTICE.

import QuasiEuclidean.Basic

/-!
# Chapter 8: differential equations as exact difference equations

An ordinary differential equation `ẋ = F(x)` is read, on the granular time
lattice of spacing `2ε`, as the exact difference equation
`x(t + 2ε) = x(t) + 2ε F(x(t))`.  All results below are exact finitary
identities or inequalities valid for every `ε` in every linearly ordered
field (or in `ℝ` when square roots or `exp` are needed); the infinitesimal
case is the instance `K := Hyperreal`.
-/

set_option linter.unusedSectionVars false

namespace QE.ODE

open Finset

section Field
variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-! ## The granular initial value problem -/

/-- The granular (forward) orbit of `ẋ = F(x)` from `x₀`: `x_{k+1} = x_k + 2ε F(x_k)`. -/
def euler (ε : K) (F : K → K) (x₀ : K) : ℕ → K
  | 0 => x₀
  | k + 1 => euler ε F x₀ k + 2 * ε * F (euler ε F x₀ k)

@[simp] theorem euler_zero (ε : K) (F : K → K) (x₀ : K) : euler ε F x₀ 0 = x₀ := rfl

@[simp] theorem euler_succ (ε : K) (F : K → K) (x₀ : K) (k : ℕ) :
    euler ε F x₀ (k + 1) = euler ε F x₀ k + 2 * ε * F (euler ε F x₀ k) := rfl

/-- A function on `K` whose step relation is the granular ODE has granular derivative `F`. -/
theorem Dp_of_step (ε : K) (hε : ε ≠ 0) (F f : K → K) (x : K)
    (h : f (x + 2 * ε) = f x + 2 * ε * F (f x)) : QE.Dp ε f x = F (f x) := by
  unfold QE.Dp; rw [h]; field_simp; ring

/-- The exact discrete integral equation (granular Volterra form). -/
theorem euler_sum (ε : K) (F : K → K) (x₀ : K) (k : ℕ) :
    euler ε F x₀ k = x₀ + ∑ j ∈ range k, F (euler ε F x₀ j) * (2 * ε) := by
  induction k with
  | zero => simp
  | succ k ih => rw [sum_range_succ, ← add_assoc, ← ih, euler_succ]; ring

/-- Equi-Lipschitz bound in time for the granular orbit (the core of Peano's theorem). -/
theorem euler_increment_bound (ε : K) (hε : 0 ≤ ε) (F : K → K) (M : K)
    (hF : ∀ y, |F y| ≤ M) (x₀ : K) (i k : ℕ) :
    |euler ε F x₀ (i + k) - euler ε F x₀ i| ≤ M * (2 * ε * k) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [← add_assoc, euler_succ]
    have h1 : |2 * ε * F (euler ε F x₀ (i + k))| ≤ 2 * ε * M := by
      rw [abs_mul, abs_of_nonneg (by linarith : (0:K) ≤ 2 * ε)]
      exact mul_le_mul_of_nonneg_left (hF _) (by linarith)
    calc |euler ε F x₀ (i + k) + 2 * ε * F (euler ε F x₀ (i + k)) - euler ε F x₀ i|
        = |(euler ε F x₀ (i + k) - euler ε F x₀ i) + 2 * ε * F (euler ε F x₀ (i + k))| := by
          ring_nf
      _ ≤ |euler ε F x₀ (i + k) - euler ε F x₀ i| + |2 * ε * F (euler ε F x₀ (i + k))| :=
          abs_add_le _ _
      _ ≤ M * (2 * ε * k) + 2 * ε * M := add_le_add ih h1
      _ = M * (2 * ε * ((k + 1 : ℕ) : K)) := by push_cast; ring

/-! ## Discrete Grönwall inequality -/

/-- Discrete Grönwall inequality (exact form). -/
theorem gronwall (u : ℕ → K) (a d : K) (ha : 0 ≤ a) (h : ∀ k, u (k + 1) ≤ a * u k + d)
    (k : ℕ) : u k ≤ a ^ k * u 0 + d * ∑ j ∈ range k, a ^ j := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hs : ∑ j ∈ range (k + 1), a ^ j = a * ∑ j ∈ range k, a ^ j + 1 := by
      rw [sum_range_succ', mul_sum]; simp [pow_succ, mul_comm]
    calc u (k + 1) ≤ a * u k + d := h k
      _ ≤ a * (a ^ k * u 0 + d * ∑ j ∈ range k, a ^ j) + d := by
          have := mul_le_mul_of_nonneg_left ih ha; linarith
      _ = a ^ (k + 1) * u 0 + d * ∑ j ∈ range (k + 1), a ^ j := by rw [hs]; ring

/-- Granular Grönwall with closed-form geometric sum:
`u_{k+1} ≤ (1+2εL) u_k + 2εβ ⇒ u_k ≤ (1+2εL)^k u_0 + β((1+2εL)^k - 1)/L`. -/
theorem gronwall_granular (u : ℕ → K) (ε L β : K) (hε : 0 < ε) (hL : 0 < L)
    (h : ∀ k, u (k + 1) ≤ (1 + 2 * ε * L) * u k + 2 * ε * β) (k : ℕ) :
    u k ≤ (1 + 2 * ε * L) ^ k * u 0 + β * ((1 + 2 * ε * L) ^ k - 1) / L := by
  have h1 := gronwall u (1 + 2 * ε * L) (2 * ε * β) (by positivity) h k
  have hne : (1 + 2 * ε * L) ≠ 1 := by
    intro h'; have : 2 * ε * L = 0 := by linarith
    have : 0 < 2 * ε * L := by positivity
    linarith
  rw [geom_sum_eq hne] at h1
  have e : 2 * ε * β * (((1 + 2 * ε * L) ^ k - 1) / (1 + 2 * ε * L - 1))
      = β * ((1 + 2 * ε * L) ^ k - 1) / L := by
    field_simp; ring
  linarith

/-! ## Stability and uniqueness under a Lipschitz condition -/

/-- Exact stability estimate: a perturbed orbit with defect `r` stays within the Grönwall
envelope of the granular orbit. -/
theorem euler_stability (ε : K) (hε : 0 ≤ ε) (F : K → K) (L : K) (hL : 0 ≤ L)
    (hF : ∀ x y, |F x - F y| ≤ L * |x - y|) (x₀ : K) (y r : ℕ → K) (ρ : K)
    (hy : ∀ k, y (k + 1) = y k + 2 * ε * F (y k) + 2 * ε * r k) (hr : ∀ k, |r k| ≤ ρ)
    (k : ℕ) :
    |euler ε F x₀ k - y k| ≤ (1 + 2 * ε * L) ^ k * |x₀ - y 0|
        + 2 * ε * ρ * ∑ j ∈ range k, (1 + 2 * ε * L) ^ j := by
  have := gronwall (fun k => |euler ε F x₀ k - y k|) (1 + 2 * ε * L) (2 * ε * ρ)
    (by positivity) ?_ k
  · simpa using this
  intro k
  simp only [euler_succ, hy]
  have h2 : (0:K) ≤ 2 * ε := by linarith
  set a := euler ε F x₀ k
  calc |a + 2 * ε * F a - (y k + 2 * ε * F (y k) + 2 * ε * r k)|
      = |(a - y k) + 2 * ε * (F a - F (y k)) - 2 * ε * r k| := by ring_nf
    _ ≤ |a - y k| + |2 * ε * (F a - F (y k))| + |2 * ε * r k| := by
        refine (abs_sub _ _).trans ?_
        exact add_le_add_left (abs_add_le _ _) _
    _ ≤ |a - y k| + 2 * ε * (L * |a - y k|) + 2 * ε * ρ := by
        rw [abs_mul (2 * ε), abs_mul (2 * ε) (r k), abs_of_nonneg h2]
        have := mul_le_mul_of_nonneg_left (hF a (y k)) h2
        have := mul_le_mul_of_nonneg_left (hr k) h2
        linarith
    _ = (1 + 2 * ε * L) * |a - y k| + 2 * ε * ρ := by ring

/-- Continuous dependence on the initial datum (granular uniqueness). -/
theorem euler_lipschitz_dependence (ε : K) (hε : 0 ≤ ε) (F : K → K) (L : K) (hL : 0 ≤ L)
    (hF : ∀ x y, |F x - F y| ≤ L * |x - y|) (x₀ y₀ : K) (k : ℕ) :
    |euler ε F x₀ k - euler ε F y₀ k| ≤ (1 + 2 * ε * L) ^ k * |x₀ - y₀| := by
  have := euler_stability ε hε F L hL hF x₀ (euler ε F y₀) (fun _ => 0) 0
    (fun k => by simp) (fun k => by simp) k
  simpa using this

/-! ## Linear equations: the granular exponential -/

/-- `ẋ = a x` is solved exactly by the granular exponential `(1 + 2εa)^k x₀`. -/
theorem euler_linear (ε a x₀ : K) (k : ℕ) :
    euler ε (fun x => a * x) x₀ k = (1 + 2 * ε * a) ^ k * x₀ := by
  induction k with
  | zero => simp
  | succ k ih => rw [euler_succ, ih, pow_succ]; ring

/-- Exact granular Duhamel formula for `ẋ = a x + b(t)`. -/
theorem duhamel (ε a : K) (b x : ℕ → K)
    (hx : ∀ k, x (k + 1) = x k + 2 * ε * (a * x k + b k)) (k : ℕ) :
    x k = (1 + 2 * ε * a) ^ k * x 0
      + ∑ j ∈ range k, (1 + 2 * ε * a) ^ (k - 1 - j) * (2 * ε * b j) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [hx k, ih, sum_range_succ]
    have hs : ∑ j ∈ range k, (1 + 2 * ε * a) ^ (k + 1 - 1 - j) * (2 * ε * b j)
        = (1 + 2 * ε * a) * ∑ j ∈ range k, (1 + 2 * ε * a) ^ (k - 1 - j) * (2 * ε * b j) := by
      rw [mul_sum]; refine sum_congr rfl (fun j hj => ?_)
      have hj' : j < k := mem_range.mp hj
      have : k + 1 - 1 - j = (k - 1 - j) + 1 := by omega
      rw [this, pow_succ]; ring
    rw [hs]; simp only [Nat.add_sub_cancel, Nat.sub_self, pow_zero, pow_succ]; ring

/-! ## The harmonic oscillator -/

/-- Energy `p² + ω² q²` of a phase point `z = (q, p)`. -/
def energy (ω : K) (z : K × K) : K := z.2 ^ 2 + ω ^ 2 * z.1 ^ 2

/-- Explicit (forward) Euler for `q̇ = p, ṗ = -ω² q` with step `2ε`. -/
def explicitOsc (ε ω : K) (z₀ : K × K) : ℕ → K × K
  | 0 => z₀
  | k + 1 =>
    let z := explicitOsc ε ω z₀ k
    (z.1 + 2 * ε * z.2, z.2 - 2 * ε * ω ^ 2 * z.1)

/-- Explicit Euler multiplies the energy by exactly `1 + 4ε²ω²` per step. -/
theorem explicitOsc_energy_step (ε ω : K) (z₀ : K × K) (k : ℕ) :
    energy ω (explicitOsc ε ω z₀ (k + 1)) = (1 + 4 * ε ^ 2 * ω ^ 2) * energy ω (explicitOsc ε ω z₀ k) := by
  simp only [explicitOsc, energy]; ring

theorem explicitOsc_energy (ε ω : K) (z₀ : K × K) (k : ℕ) :
    energy ω (explicitOsc ε ω z₀ k) = (1 + 4 * ε ^ 2 * ω ^ 2) ^ k * energy ω z₀ := by
  induction k with
  | zero => simp [explicitOsc]
  | succ k ih => rw [explicitOsc_energy_step, ih, pow_succ]; ring

/-- Implicit (backward) Euler divides the energy by exactly `1 + 4ε²ω²` per step. -/
theorem implicit_energy_step (ε ω q p q' p' : K) (hq : q' - 2 * ε * p' = q)
    (hp : p' + 2 * ε * ω ^ 2 * q' = p) :
    energy ω (q, p) = (1 + 4 * ε ^ 2 * ω ^ 2) * energy ω (q', p') := by
  subst hq hp; simp only [energy]; ring

/-- Symplectic Euler: kick `p` first, then drift `q` with the new momentum. -/
def sympOsc (ε ω : K) (z₀ : K × K) : ℕ → K × K
  | 0 => z₀
  | k + 1 =>
    let z := sympOsc ε ω z₀ k
    let p' := z.2 - 2 * ε * ω ^ 2 * z.1
    (z.1 + 2 * ε * p', p')

/-- The modified energy `p² + ω² q² − 2εω² q p`. -/
def modEnergy (ε ω : K) (z : K × K) : K := z.2 ^ 2 + ω ^ 2 * z.1 ^ 2 - 2 * ε * ω ^ 2 * z.1 * z.2

/-- Symplectic Euler conserves the modified energy exactly. -/
theorem sympOsc_modEnergy_step (ε ω : K) (z₀ : K × K) (k : ℕ) :
    modEnergy ε ω (sympOsc ε ω z₀ (k + 1)) = modEnergy ε ω (sympOsc ε ω z₀ k) := by
  simp only [sympOsc, modEnergy]; ring

theorem sympOsc_modEnergy (ε ω : K) (z₀ : K × K) (k : ℕ) :
    modEnergy ε ω (sympOsc ε ω z₀ k) = modEnergy ε ω z₀ := by
  induction k with
  | zero => rfl
  | succ k ih => rw [sympOsc_modEnergy_step, ih]

/-- Two-sided comparison of the modified and the true energy. -/
theorem modEnergy_bounds (ε ω : K) (hε : 0 ≤ ε) (hω : 0 ≤ ω) (z : K × K) :
    (1 - ε * ω) * energy ω z ≤ modEnergy ε ω z ∧ modEnergy ε ω z ≤ (1 + ε * ω) * energy ω z := by
  obtain ⟨q, p⟩ := z
  simp only [energy, modEnergy]
  have hεω : 0 ≤ ε * ω := mul_nonneg hε hω
  constructor
  · nlinarith [mul_nonneg hεω (sq_nonneg (p - ω * q))]
  · nlinarith [mul_nonneg hεω (sq_nonneg (p + ω * q))]

/-- Under `εω < 1` the true energy along symplectic Euler is bounded for all time. -/
theorem sympOsc_energy_bounded (ε ω : K) (hε : 0 ≤ ε) (hω : 0 ≤ ω) (z₀ : K × K) (k : ℕ) :
    (1 - ε * ω) * energy ω (sympOsc ε ω z₀ k) ≤ (1 + ε * ω) * energy ω z₀ := by
  have h1 := (modEnergy_bounds ε ω hε hω (sympOsc ε ω z₀ k)).1
  have h2 := (modEnergy_bounds ε ω hε hω z₀).2
  rw [sympOsc_modEnergy] at h1
  linarith

/-- The implicit midpoint (Crank–Nicolson) rule conserves the true energy exactly. -/
theorem midpoint_energy (ε ω q p q' p' : K) (hq : q' - q = ε * (p + p'))
    (hp : p' - p = -(ε * ω ^ 2 * (q + q'))) : energy ω (q', p') = energy ω (q, p) := by
  simp only [energy]
  linear_combination (p' + p) * hp + ω ^ 2 * (q' + q) * hq

/-- Symplectic Euler is the leapfrog scheme: `q_{k+2} − 2q_{k+1} + q_k = −(2ε)²ω² q_{k+1}`. -/
theorem sympOsc_leapfrog (ε ω : K) (z₀ : K × K) (k : ℕ) :
    (sympOsc ε ω z₀ (k + 2)).1 - 2 * (sympOsc ε ω z₀ (k + 1)).1 + (sympOsc ε ω z₀ k).1
      = -(2 * ε) ^ 2 * ω ^ 2 * (sympOsc ε ω z₀ (k + 1)).1 := by
  simp only [sympOsc]; ring

/-- Phase-volume factors: symplectic Euler has Jacobian determinant `1`. -/
theorem symp_det (ε ω : K) :
    (!![1 - 4 * ε ^ 2 * ω ^ 2, 2 * ε; -(2 * ε * ω ^ 2), 1] : Matrix (Fin 2) (Fin 2) K).det = 1 := by
  rw [Matrix.det_fin_two_of]; ring

/-- Explicit Euler has Jacobian determinant `1 + 4ε²ω²`. -/
theorem explicit_det (ε ω : K) :
    (!![1, 2 * ε; -(2 * ε * ω ^ 2), 1] : Matrix (Fin 2) (Fin 2) K).det = 1 + 4 * ε ^ 2 * ω ^ 2 := by
  rw [Matrix.det_fin_two_of]; ring

/-! ## Blow-up of `ẋ = x²` -/

/-- Reciprocal identity behind the blow-up analysis. -/
theorem recip_step (ε x : K) (hx : 0 < x) (hd : 0 < 1 + 2 * ε * x) :
    1 / (x + 2 * ε * x ^ 2) = 1 / x - 2 * ε / (1 + 2 * ε * x) := by
  have : x + 2 * ε * x ^ 2 = x * (1 + 2 * ε * x) := by ring
  have h1 := hx.ne'; have h2 := hd.ne'
  rw [this, div_sub_div _ _ h1 h2, div_eq_div_iff (mul_ne_zero h1 h2) (mul_ne_zero h1 h2)]; ring

theorem blowup_pos (ε : K) (hε : 0 ≤ ε) (x₀ : K) (hx : 0 < x₀) (k : ℕ) :
    0 < euler ε (fun x => x ^ 2) x₀ k ∧
      euler ε (fun x => x ^ 2) x₀ k ≤ euler ε (fun x => x ^ 2) x₀ (k + 1) := by
  induction k with
  | zero => exact ⟨hx, by simp; positivity⟩
  | succ k ih =>
    have h0 := ih.1.trans_le ih.2
    exact ⟨h0, by rw [euler_succ (k := k + 1)]; nlinarith [sq_nonneg (euler ε (fun x => x ^ 2) x₀ (k + 1))]⟩

/-- The reciprocal decreases by at most `2ε` per step: `1/x_k ≥ 1/x₀ − 2εk`. -/
theorem blowup_upper (ε : K) (hε : 0 ≤ ε) (x₀ : K) (hx : 0 < x₀) (k : ℕ) :
    1 / x₀ - 2 * ε * k ≤ 1 / euler ε (fun x => x ^ 2) x₀ k := by
  induction k with
  | zero => simp
  | succ k ih =>
    set x := euler ε (fun x => x ^ 2) x₀ k
    have hxp : 0 < x := (blowup_pos ε hε x₀ hx k).1
    have hd : 0 < 1 + 2 * ε * x := by positivity
    have key : 1 / euler ε (fun x => x ^ 2) x₀ (k + 1) = 1 / x - 2 * ε / (1 + 2 * ε * x) :=
      recip_step ε x hxp hd
    have hle : 2 * ε / (1 + 2 * ε * x) ≤ 2 * ε :=
      div_le_self (by linarith) (by nlinarith [mul_nonneg hε hxp.le])
    rw [key]; push_cast; linarith

/-- While the orbit stays below `M`, lattice time is bounded: `2εk < (1 + 2εM)/x₀`. -/
theorem blowup_reach (ε : K) (hε : 0 < ε) (x₀ : K) (hx : 0 < x₀) (M : K) (hM : 0 < M)
    (k : ℕ) (hk : ∀ j < k, euler ε (fun x => x ^ 2) x₀ j ≤ M) :
    2 * ε * k < (1 + 2 * ε * M) / x₀ := by
  have hc : 0 < 1 + 2 * ε * M := by positivity
  have claim : ∀ m ≤ k, 1 / euler ε (fun x => x ^ 2) x₀ m ≤ 1 / x₀ - m * (2 * ε / (1 + 2 * ε * M)) := by
    intro m
    induction m with
    | zero => intro; simp
    | succ m ih =>
      intro hm
      have ih := ih (by omega)
      set x := euler ε (fun x => x ^ 2) x₀ m
      have hxp : 0 < x := (blowup_pos ε hε.le x₀ hx m).1
      have hxM : x ≤ M := hk m (by omega)
      have key : 1 / euler ε (fun x => x ^ 2) x₀ (m + 1) = 1 / x - 2 * ε / (1 + 2 * ε * x) :=
        recip_step ε x hxp (by positivity)
      have hge : 2 * ε / (1 + 2 * ε * M) ≤ 2 * ε / (1 + 2 * ε * x) :=
        div_le_div_of_nonneg_left (by linarith) (by positivity) (by nlinarith)
      rw [key]; push_cast; linarith
  have h1 := claim k le_rfl
  have hpos : 0 < 1 / euler ε (fun x => x ^ 2) x₀ k := by
    have := (blowup_pos ε hε.le x₀ hx k).1; positivity
  have h2 : (k : K) * (2 * ε / (1 + 2 * ε * M)) < 1 / x₀ := by linarith
  rw [mul_div_assoc', div_lt_iff₀ hc] at h2
  rw [lt_div_iff₀ hx]
  calc 2 * ε * k * x₀ = (k * (2 * ε)) * x₀ := by ring
    _ < (1 / x₀ * (1 + 2 * ε * M)) * x₀ := by
        exact mul_lt_mul_of_pos_right h2 hx
    _ = 1 + 2 * ε * M := by field_simp

/-- In an Archimedean field the orbit of `ẋ = x²` exceeds every bound. -/
theorem blowup_exists [Archimedean K] (ε : K) (hε : 0 < ε) (x₀ : K) (hx : 0 < x₀) (M : K)
    (hM : 0 < M) : ∃ k, M < euler ε (fun x => x ^ 2) x₀ k := by
  by_contra hcon
  push Not at hcon
  obtain ⟨n, hn⟩ := exists_nat_gt ((1 + 2 * ε * M) / x₀ / (2 * ε))
  have := blowup_reach ε hε x₀ hx M hM n (fun j _ => hcon j)
  rw [div_lt_iff₀ (by positivity)] at hn
  linarith

/-- Super-exponential growth after the blow-up time: `x_{k+1} ≥ 2ε x_k²`. -/
theorem blowup_superexp (ε : K) (hε : 0 ≤ ε) (x₀ : K) (hx : 0 < x₀) (k : ℕ) :
    2 * ε * (euler ε (fun x => x ^ 2) x₀ k) ^ 2 ≤ euler ε (fun x => x ^ 2) x₀ (k + 1) := by
  rw [euler_succ]; have := (blowup_pos ε hε x₀ hx k).1; linarith

/-! ## Heat equation: explicit scheme -/

section Heat
variable {G : Type*} [AddCommGroup G]

/-- One step of the explicit heat scheme with mesh ratio `r = τ/(2ε)²`. -/
def heatStep (r : K) (e : G) (u : G → K) : G → K :=
  fun j => u j + r * (u (j + e) - 2 * u j + u (j - e))

def heatIter (r : K) (e : G) (u : G → K) : ℕ → G → K
  | 0 => u
  | n + 1 => heatStep r e (heatIter r e u n)

/-- The mesh ratio condition `τ ≤ (2ε)²/2`. -/
theorem rate_mem (τ ε : K) (hτ : 0 ≤ τ) (hε : 0 < ε) (hst : τ ≤ (2 * ε) ^ 2 / 2) :
    0 ≤ τ / (2 * ε) ^ 2 ∧ τ / (2 * ε) ^ 2 ≤ 1 / 2 := by
  have h : 0 < (2 * ε) ^ 2 := by positivity
  refine ⟨div_nonneg hτ h.le, ?_⟩
  rw [div_le_iff₀ h]; linarith

/-- Discrete maximum principle for one step. -/
theorem heatStep_bounds (r : K) (h0 : 0 ≤ r) (h1 : r ≤ 1 / 2) (e : G) (u : G → K) (m M : K)
    (hu : ∀ j, m ≤ u j ∧ u j ≤ M) (j : G) : m ≤ heatStep r e u j ∧ heatStep r e u j ≤ M := by
  simp only [heatStep]
  obtain ⟨a1, a2⟩ := hu (j + e); obtain ⟨b1, b2⟩ := hu j; obtain ⟨c1, c2⟩ := hu (j - e)
  have hr : 0 ≤ 1 - 2 * r := by linarith
  constructor
  · nlinarith [mul_le_mul_of_nonneg_left b1 hr, mul_le_mul_of_nonneg_left a1 h0,
      mul_le_mul_of_nonneg_left c1 h0]
  · nlinarith [mul_le_mul_of_nonneg_left b2 hr, mul_le_mul_of_nonneg_left a2 h0,
      mul_le_mul_of_nonneg_left c2 h0]

/-- Discrete maximum principle for all time. -/
theorem heat_max (r : K) (h0 : 0 ≤ r) (h1 : r ≤ 1 / 2) (e : G) (u : G → K) (m M : K)
    (hu : ∀ j, m ≤ u j ∧ u j ≤ M) (n : ℕ) (j : G) :
    m ≤ heatIter r e u n j ∧ heatIter r e u n j ≤ M := by
  induction n generalizing j with
  | zero => exact hu j
  | succ n ih => exact heatStep_bounds r h0 h1 e _ m M ih j

/-- Monotonicity (comparison principle). -/
theorem heatStep_mono (r : K) (h0 : 0 ≤ r) (h1 : r ≤ 1 / 2) (e : G) (u v : G → K)
    (huv : ∀ j, u j ≤ v j) (j : G) : heatStep r e u j ≤ heatStep r e v j := by
  simp only [heatStep]
  have hr : 0 ≤ 1 - 2 * r := by linarith
  nlinarith [mul_le_mul_of_nonneg_left (huv j) hr, mul_le_mul_of_nonneg_left (huv (j + e)) h0,
    mul_le_mul_of_nonneg_left (huv (j - e)) h0]

/-- Exact conservation of heat on a finite (periodic) lattice. -/
theorem heatStep_mass [Fintype G] (r : K) (e : G) (u : G → K) :
    ∑ j, heatStep r e u j = ∑ j, u j := by
  simp only [heatStep, sum_add_distrib, ← mul_sum, sum_sub_distrib]
  have h1 : ∑ j, u (j + e) = ∑ j, u j := Fintype.sum_equiv (Equiv.addRight e) _ _ (fun _ => rfl)
  have h2 : ∑ j, u (j - e) = ∑ j, u j := Fintype.sum_equiv (Equiv.subRight e) _ _ (fun _ => rfl)
  rw [h1, h2]; ring

/-- Explicit heat step on a lattice with `d` axis directions `e i`
(the `d`-dimensional scheme with mesh ratio `r = τ/(2ε)²`). -/
def heatStepN (r : K) {d : ℕ} (e : Fin d → G) (u : G → K) : G → K :=
  fun j => u j + r * ∑ i, (u (j + e i) - 2 * u j + u (j - e i))

def heatIterN (r : K) {d : ℕ} (e : Fin d → G) (u : G → K) : ℕ → G → K
  | 0 => u
  | n + 1 => heatStepN r e (heatIterN r e u n)

/-- Discrete maximum principle in `d` directions under `2 d r ≤ 1`. -/
theorem heatStepN_bounds (r : K) (h0 : 0 ≤ r) {d : ℕ} (h1 : 2 * d * r ≤ 1) (e : Fin d → G)
    (u : G → K) (m M : K) (hu : ∀ j, m ≤ u j ∧ u j ≤ M) (j : G) :
    m ≤ heatStepN r e u j ∧ heatStepN r e u j ≤ M := by
  simp only [heatStepN]
  have hs : ∑ i, (u (j + e i) - 2 * u j + u (j - e i))
      = ∑ i, (u (j + e i) + u (j - e i)) - 2 * d * u j := by
    simp only [sum_sub_distrib, sum_add_distrib, sum_const, card_univ, Fintype.card_fin,
      nsmul_eq_mul]; ring
  have lo : (d : K) * m + d * m ≤ ∑ i, (u (j + e i) + u (j - e i)) := by
    have := Finset.sum_le_sum (s := (univ : Finset (Fin d)))
      (fun i _ => add_le_add (hu (j + e i)).1 (hu (j - e i)).1)
    simpa using this
  have hi : ∑ i, (u (j + e i) + u (j - e i)) ≤ (d : K) * M + d * M := by
    have := Finset.sum_le_sum (s := (univ : Finset (Fin d)))
      (fun i _ => add_le_add (hu (j + e i)).2 (hu (j - e i)).2)
    simpa using this
  rw [hs]
  have hr : 0 ≤ 1 - 2 * d * r := by linarith
  obtain ⟨b1, b2⟩ := hu j
  constructor
  · nlinarith [mul_le_mul_of_nonneg_left b1 hr, mul_le_mul_of_nonneg_left lo h0]
  · nlinarith [mul_le_mul_of_nonneg_left b2 hr, mul_le_mul_of_nonneg_left hi h0]

theorem heatN_max (r : K) (h0 : 0 ≤ r) {d : ℕ} (h1 : 2 * d * r ≤ 1) (e : Fin d → G)
    (u : G → K) (m M : K) (hu : ∀ j, m ≤ u j ∧ u j ≤ M) (n : ℕ) (j : G) :
    m ≤ heatIterN r e u n j ∧ heatIterN r e u n j ≤ M := by
  induction n generalizing j with
  | zero => exact hu j
  | succ n ih => exact heatStepN_bounds r h0 h1 e _ m M ih j

/-- Linearity of the heat step. -/
theorem heatStep_sub (r : K) (e : G) (u v : G → K) (j : G) :
    heatStep r e (fun i => u i - v i) j = heatStep r e u j - heatStep r e v j := by
  simp only [heatStep]; ring

/-- Backward stability of one heat step for `r < 1/4`:
`(1 − 4r)‖u‖∞ ≤ ‖Su‖∞` on a finite lattice. -/
theorem heat_backward_step [Fintype G] [Nonempty G] (r : K) (h0 : 0 ≤ r) (h1 : r ≤ 1 / 4)
    (e : G) (u : G → K) (M : K) (hM : ∀ j, |heatStep r e u j| ≤ M) (j : G) :
    (1 - 4 * r) * |u j| ≤ M := by
  obtain ⟨j0, -, hj0⟩ := Finset.exists_max_image (univ : Finset G) (fun i => |u i|) univ_nonempty
  have hmax : ∀ i, |u i| ≤ |u j0| := fun i => hj0 i (mem_univ i)
  have key : (1 - 4 * r) * |u j0| ≤ |heatStep r e u j0| := by
    simp only [heatStep]
    have e1 : u j0 + r * (u (j0 + e) - 2 * u j0 + u (j0 - e))
        = (1 - 2 * r) * u j0 + r * (u (j0 + e) + u (j0 - e)) := by ring
    rw [e1]
    have hA : |r * (u (j0 + e) + u (j0 - e))| ≤ 2 * r * |u j0| := by
      rw [abs_mul, abs_of_nonneg h0]
      have := abs_add_le (u (j0 + e)) (u (j0 - e))
      nlinarith [hmax (j0 + e), hmax (j0 - e)]
    have hB : |(1 - 2 * r) * u j0| = (1 - 2 * r) * |u j0| := by
      rw [abs_mul, abs_of_nonneg (by linarith)]
    have := abs_sub_abs_le_abs_sub ((1 - 2 * r) * u j0) (-(r * (u (j0 + e) + u (j0 - e))))
    rw [abs_neg, sub_neg_eq_add] at this
    linarith
  have h4 : 0 ≤ 1 - 4 * r := by linarith
  calc (1 - 4 * r) * |u j| ≤ (1 - 4 * r) * |u j0| := mul_le_mul_of_nonneg_left (hmax j) h4
    _ ≤ |heatStep r e u j0| := key
    _ ≤ M := hM j0

/-- Backward stability of `n` heat steps: `(1 − 4r)ⁿ‖u‖∞ ≤ ‖Sⁿu‖∞` for `r < 1/4`. -/
theorem heat_backward [Fintype G] [Nonempty G] (r : K) (h0 : 0 ≤ r) (h1 : r < 1 / 4)
    (e : G) (n : ℕ) : ∀ (u : G → K) (M : K), (∀ j, |heatIter r e u n j| ≤ M) →
      ∀ j, (1 - 4 * r) ^ n * |u j| ≤ M := by
  have hc : 0 < 1 - 4 * r := by linarith
  induction n with
  | zero => intro u M hM j; simpa [heatIter] using hM j
  | succ n ih =>
    intro u M hM j
    have h1' := heat_backward_step r h0 h1.le e (heatIter r e u n) M hM
    have h2 : ∀ i, |heatIter r e u n i| ≤ M / (1 - 4 * r) := fun i => by
      rw [le_div_iff₀ hc]; linarith [h1' i]
    have := ih u (M / (1 - 4 * r)) h2 j
    rw [le_div_iff₀ hc] at this
    rw [pow_succ]; linarith

/-- Hence `n` heat steps are injective for `r < 1/4`: no information is lost. -/
theorem heat_injective [Fintype G] [Nonempty G] (r : K) (h0 : 0 ≤ r) (h1 : r < 1 / 4)
    (e : G) (n : ℕ) (u v : G → K) (h : heatIter r e u n = heatIter r e v n) : u = v := by
  have lin : ∀ m j, heatIter r e (fun i => u i - v i) m j = heatIter r e u m j - heatIter r e v m j := by
    intro m
    induction m with
    | zero => intro j; rfl
    | succ m ih =>
      intro j
      show heatStep r e (heatIter r e (fun i => u i - v i) m) j = _
      rw [show heatIter r e (fun i => u i - v i) m = fun i => heatIter r e u m i - heatIter r e v m i
        from funext ih, heatStep_sub]; rfl
  have hb := heat_backward r h0 h1 e n (fun i => u i - v i) 0 (fun j => by rw [lin, h]; simp)
  funext j
  have hpos : 0 < (1 - 4 * r) ^ n := pow_pos (by linarith) n
  have := hb j
  have : |u j - v j| ≤ 0 := by nlinarith [abs_nonneg (u j - v j)]
  have := abs_nonpos_iff.mp this
  linarith

end Heat

/-- The checkerboard mode is multiplied by exactly `1 − 4r` per step. -/
theorem heat_checkerboard (r c : K) (n : ℕ) (j : ℤ) :
    heatIter r (1 : ℤ) (fun i => (-1 : K) ^ i * c) n j = (1 - 4 * r) ^ n * ((-1 : K) ^ j * c) := by
  induction n generalizing j with
  | zero => simp [heatIter]
  | succ n ih =>
    simp only [heatIter, heatStep, ih]
    have hm : (-1 : K) ≠ 0 := by norm_num
    rw [zpow_add_one₀ hm, zpow_sub_one₀ hm]
    have : (-1 : K)⁻¹ = -1 := by norm_num
    rw [this, pow_succ]; ring

/-- Beyond the stability threshold the checkerboard mode grows geometrically. -/
theorem heat_unstable (r : K) (h : 1 / 2 < r) : 1 < |1 - 4 * r| := by
  rw [abs_of_neg (by linarith)]; linarith

/-! ## Wave equation: exact discrete energy -/

section Wave
variable {N : ℕ} [NeZero N]

/-- Discrete energy between time levels `x = uⁿ` and `y = uⁿ⁺¹` (Courant number `μ`). -/
def waveEnergy (μ : K) (x y : ZMod N → K) : K :=
  ∑ j, (y j - x j) ^ 2 + μ ^ 2 * ∑ j, (y (j + 1) - y j) * (x (j + 1) - x j)

/-- Leapfrog for the wave equation conserves the discrete energy exactly. -/
theorem wave_energy_conserved (μ : K) (a b c : ZMod N → K)
    (h : ∀ j, c j - 2 * b j + a j = μ ^ 2 * (b (j + 1) - 2 * b j + b (j - 1))) :
    waveEnergy μ b c = waveEnergy μ a b := by
  have hs : ∑ j, (b (j + 1) - b j) * (c (j + 1) - a (j + 1))
      = ∑ j, (b j - b (j - 1)) * (c j - a j) := by
    exact Fintype.sum_equiv (Equiv.addRight (1 : ZMod N)) _ _ (fun j => by simp)
  have key : waveEnergy μ b c - waveEnergy μ a b
      = μ ^ 2 * (∑ j, ((b (j + 1) - 2 * b j + b (j - 1)) * (c j - a j)
          - (b (j + 1) - b j) * (c j - a j))
        + ∑ j, (b (j + 1) - b j) * (c (j + 1) - a (j + 1))) := by
    unfold waveEnergy
    simp only [mul_sum, ← sum_add_distrib, ← sum_sub_distrib]
    refine sum_congr rfl (fun j _ => ?_)
    linear_combination (c j - a j) * h j
  rw [hs, ← sum_add_distrib] at key
  have hz : ∑ j, ((b (j + 1) - 2 * b j + b (j - 1)) * (c j - a j) - (b (j + 1) - b j) * (c j - a j)
      + (b j - b (j - 1)) * (c j - a j)) = 0 := by
    refine sum_eq_zero (fun j _ => ?_); ring
  rw [hz, mul_zero] at key
  linarith

/-- Under the Courant–Friedrichs–Lewy condition the energy controls the kinetic part:
`E ≥ (1 − μ²) ∑ (y − x)²`. -/
theorem wave_energy_lower (μ : K) (x y : ZMod N → K) :
    (1 - μ ^ 2) * ∑ j, (y j - x j) ^ 2 ≤ waveEnergy μ x y := by
  unfold waveEnergy
  have hs : ∑ j, (y (j + 1) - x (j + 1)) ^ 2 = ∑ j, (y j - x j) ^ 2 :=
    Fintype.sum_equiv (Equiv.addRight (1 : ZMod N)) _ (fun j => (y j - x j) ^ 2) (fun _ => rfl)
  have hterm : 0 ≤ ∑ j, ((y (j + 1) - y j) * (x (j + 1) - x j)
      + ((y (j + 1) - x (j + 1)) ^ 2 + (y j - x j) ^ 2) / 2) := by
    refine sum_nonneg (fun j _ => ?_)
    nlinarith [sq_nonneg ((y (j + 1) - y j) + (x (j + 1) - x j)),
      sq_nonneg ((y (j + 1) - x (j + 1)) + (y j - x j))]
  rw [sum_add_distrib, ← sum_div, sum_add_distrib, hs] at hterm
  nlinarith [sq_nonneg μ]

end Wave

/-- Granular comparison principle: for `2εL ≤ 1` the time-one map is monotone, so
ordered initial data give ordered orbits. -/
theorem euler_order (ε : K) (hε : 0 ≤ ε) (F : K → K) (L : K)
    (hF : ∀ x y, |F x - F y| ≤ L * |x - y|) (hstep : 2 * ε * L ≤ 1) (x₀ y₀ : K)
    (h : x₀ ≤ y₀) (k : ℕ) : euler ε F x₀ k ≤ euler ε F y₀ k := by
  induction k with
  | zero => exact h
  | succ k ih =>
    rw [euler_succ, euler_succ]
    set a := euler ε F x₀ k; set b := euler ε F y₀ k
    have h1 := hF b a
    rw [abs_of_nonneg (by linarith : (0:K) ≤ b - a)] at h1
    have h2 : -(L * (b - a)) ≤ F b - F a := by linarith [neg_abs_le (F b - F a)]
    have h3 : 0 ≤ 2 * ε := by linarith
    nlinarith [mul_le_mul_of_nonneg_left h2 h3]

/-! ## Granular Liouville formula, gradient flows, discontinuous right-hand sides -/

/-- Granular Liouville formula in dimension two:
`det(I + 2εA) = 1 + 2ε tr A + 4ε² det A`. -/
theorem det_granular_flow (ε a b c d : K) :
    (!![1 + 2 * ε * a, 2 * ε * b; 2 * ε * c, 1 + 2 * ε * d] : Matrix (Fin 2) (Fin 2) K).det
      = 1 + 2 * ε * (a + d) + 4 * ε ^ 2 * (a * d - b * c) := by
  rw [Matrix.det_fin_two_of]; ring

/-- One step of the granular gradient flow `ẋ = −V'(x)` decreases `V` by at least
`2ε(1 − εL)V'(x)²` under the descent inequality with constant `L`. -/
theorem gradient_step (V V' : K → K) (L ε : K)
    (hdesc : ∀ x y, V y ≤ V x + V' x * (y - x) + L / 2 * (y - x) ^ 2) (x : K) :
    V (x + 2 * ε * (-V' x)) ≤ V x - 2 * ε * (1 - ε * L) * V' x ^ 2 := by
  have := hdesc x (x + 2 * ε * (-V' x))
  have e : x + 2 * ε * -V' x - x = -(2 * ε * V' x) := by ring
  rw [e] at this
  nlinarith [this]

/-- Exact discrete energy-dissipation inequality for the granular gradient flow. -/
theorem gradient_dissipation (V V' : K → K) (L ε : K)
    (hdesc : ∀ x y, V y ≤ V x + V' x * (y - x) + L / 2 * (y - x) ^ 2) (x₀ : K) (k : ℕ) :
    V (euler ε (fun x => -V' x) x₀ k)
      + ∑ j ∈ range k, 2 * ε * (1 - ε * L) * V' (euler ε (fun x => -V' x) x₀ j) ^ 2 ≤ V x₀ := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [sum_range_succ, euler_succ]
    have := gradient_step V V' L ε hdesc (euler ε (fun x => -V' x) x₀ k)
    linarith

/-- The right-hand side `−sgn x`, with the value `0` at the point `0`. -/
def negSgn (x : K) : K := if 0 < x then -1 else if x < 0 then 1 else 0

/-- From a lattice point `2εm` the granular solution of `ẋ = −sgn x` is exactly `(2εm − t)₊`. -/
theorem sgn_lattice_descent (ε : K) (hε : 0 < ε) (m k : ℕ) (hk : k ≤ m) :
    euler ε negSgn (2 * ε * m) k = 2 * ε * ((m : K) - k) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [euler_succ, ih (by omega)]
    have hpos : 0 < 2 * ε * ((m : K) - k) := by
      have : (k : K) + 1 ≤ m := by exact_mod_cast hk
      have : 0 < (m : K) - k := by linarith
      positivity
    simp only [negSgn, hpos, ite_true]; push_cast; ring

theorem sgn_lattice_rest (ε : K) (hε : 0 < ε) (m i : ℕ) :
    euler ε negSgn (2 * ε * m) (m + i) = 0 := by
  induction i with
  | zero => simpa using sgn_lattice_descent ε hε m m le_rfl
  | succ i ih => rw [← add_assoc, euler_succ, ih]; simp [negSgn]

/-- Off the lattice, the granular solution chatters with period two and amplitude `< 2ε`. -/
theorem sgn_chatter (ε x₀ : K) (hx : 0 < x₀) (hx2 : x₀ < 2 * ε) (j : ℕ) :
    euler ε negSgn x₀ (2 * j) = x₀ ∧ euler ε negSgn x₀ (2 * j + 1) = x₀ - 2 * ε := by
  induction j with
  | zero => simp [negSgn, hx]; ring
  | succ j ih =>
    have h1 : 2 * (j + 1) = 2 * j + 1 + 1 := by ring
    have hneg : x₀ - 2 * ε < 0 := by linarith
    have hA : euler ε negSgn x₀ (2 * (j + 1)) = x₀ := by
      rw [h1, euler_succ, ih.2]
      simp only [negSgn, not_lt.mpr hneg.le, hneg, ite_true, ite_false]; ring
    refine ⟨hA, ?_⟩
    rw [euler_succ, hA]; simp [negSgn, hx]; ring

end Field

/-! ## Fourier modes and exact discrete oscillations (real case) -/

/-- A cosine mode of frequency `θ` is multiplied by exactly `1 − 2r(1 − cos θ)` per heat step. -/
theorem heat_cos_mode (r θ : ℝ) (n : ℕ) (j : ℤ) :
    heatIter r (1 : ℤ) (fun i => Real.cos (θ * i)) n j
      = (1 - 2 * r * (1 - Real.cos θ)) ^ n * Real.cos (θ * j) := by
  induction n generalizing j with
  | zero => simp [heatIter]
  | succ n ih =>
    simp only [heatIter, heatStep, ih]
    push_cast
    rw [show θ * (j + 1) = θ * j + θ by ring, show θ * (j - 1) = θ * j - θ by ring,
      Real.cos_add, Real.cos_sub, pow_succ]
    ring

/-- Exact discrete oscillation: if `cos θ = 1 − 2ε²ω²` then `A cos(θk + φ)` solves the
leapfrog (symplectic Euler) recursion exactly. -/
theorem leapfrog_cos_solution (ε ω θ A φ : ℝ) (hθ : Real.cos θ = 1 - 2 * ε ^ 2 * ω ^ 2) (k : ℕ) :
    A * Real.cos (θ * (k + 2) + φ) - 2 * (A * Real.cos (θ * (k + 1) + φ)) + A * Real.cos (θ * k + φ)
      = -(2 * ε) ^ 2 * ω ^ 2 * (A * Real.cos (θ * (k + 1) + φ)) := by
  have e1 : θ * (k + 2) + φ = (θ * (k + 1) + φ) + θ := by ring
  have e2 : θ * k + φ = (θ * (k + 1) + φ) - θ := by ring
  rw [e1, e2, Real.cos_add, Real.cos_sub, hθ]; ring

/-! ## The equation `ẋ = √|x|`: both branches -/

section Sqrt

/-- From the exact point `0` the granular dynamics stays at `0` forever. -/
theorem sqrt_zero_branch (ε : ℝ) (k : ℕ) : euler ε (fun x => Real.sqrt |x|) 0 k = 0 := by
  induction k with
  | zero => rfl
  | succ k ih => simp [ih]

theorem sqrt_branch_mono (ε : ℝ) (hε : 0 ≤ ε) (x₀ : ℝ) (hx : 0 ≤ x₀) (k : ℕ) :
    0 ≤ euler ε (fun x => Real.sqrt |x|) x₀ k ∧
      euler ε (fun x => Real.sqrt |x|) x₀ k ≤ euler ε (fun x => Real.sqrt |x|) x₀ (k + 1) := by
  induction k with
  | zero => exact ⟨hx, by simp; positivity⟩
  | succ k ih =>
    have h0 := ih.1.trans ih.2
    exact ⟨h0, by rw [euler_succ (k := k + 1)]; have := Real.sqrt_nonneg |euler ε (fun x => Real.sqrt |x|) x₀ (k + 1)|; nlinarith⟩

/-- Upper envelope: `√x_k ≤ √x₀ + εk`. -/
theorem sqrt_branch_upper (ε : ℝ) (hε : 0 ≤ ε) (x₀ : ℝ) (hx : 0 ≤ x₀) (k : ℕ) :
    Real.sqrt (euler ε (fun x => Real.sqrt |x|) x₀ k) ≤ Real.sqrt x₀ + ε * k := by
  induction k with
  | zero => simp
  | succ k ih =>
    set x := euler ε (fun x => Real.sqrt |x|) x₀ k
    have hx0 : 0 ≤ x := (sqrt_branch_mono ε hε x₀ hx k).1
    rw [euler_succ, abs_of_nonneg hx0]
    have hu := Real.sq_sqrt hx0
    have hun := Real.sqrt_nonneg x
    rw [Real.sqrt_le_left (by positivity)]
    push_cast
    nlinarith [Real.sqrt_nonneg x₀]

/-- Lower envelope: for `x₀ > 0`, `ε ≤ 2√x₀` and `δ = ε²/(2√x₀)`,
`√x_k ≥ √x₀ + k(ε − δ)`. -/
theorem sqrt_branch_lower (ε : ℝ) (hε : 0 ≤ ε) (x₀ : ℝ) (hx : 0 < x₀)
    (hsmall : ε ≤ 2 * Real.sqrt x₀) (k : ℕ) :
    Real.sqrt x₀ + k * (ε - ε ^ 2 / (2 * Real.sqrt x₀))
      ≤ Real.sqrt (euler ε (fun x => Real.sqrt |x|) x₀ k) := by
  set s := Real.sqrt x₀
  have hs : 0 < s := Real.sqrt_pos.mpr hx
  set δ := ε ^ 2 / (2 * s)
  have hδ : 2 * s * δ = ε ^ 2 := by simp only [δ]; field_simp
  have hδ0 : 0 ≤ δ := by positivity
  have hδε : δ ≤ ε := by nlinarith
  induction k with
  | zero => simp [s]
  | succ k ih =>
    set x := euler ε (fun x => Real.sqrt |x|) x₀ k
    have hx0 : 0 ≤ x := (sqrt_branch_mono ε hε x₀ hx.le k).1
    set u := Real.sqrt x
    have hu2 : u ^ 2 = x := Real.sq_sqrt hx0
    have hk0 : (0:ℝ) ≤ k * (ε - δ) := mul_nonneg (Nat.cast_nonneg k) (by linarith)
    have hus : s ≤ u := by linarith
    rw [euler_succ, abs_of_nonneg hx0]
    apply Real.le_sqrt_of_sq_le
    push_cast
    have : (u + ε - δ) ^ 2 ≤ x + 2 * ε * u := by
      rw [← hu2]
      nlinarith [mul_le_mul_of_nonneg_right hus hδ0]
    nlinarith

/-- The implicit (backward) step from `0` has exactly two solutions: the granular
dichotomy behind Peano non-uniqueness. -/
theorem sqrt_implicit_dichotomy (ε x : ℝ) (hε : 0 ≤ ε) (hx : 0 ≤ x) :
    x = 0 + 2 * ε * Real.sqrt |x| ↔ x = 0 ∨ x = 4 * ε ^ 2 := by
  rw [abs_of_nonneg hx]
  have h2 := Real.sq_sqrt hx
  constructor
  · intro h
    have : Real.sqrt x * (Real.sqrt x - 2 * ε) = 0 := by nlinarith
    rcases mul_eq_zero.mp this with h0 | h0
    · left; nlinarith
    · right; have : Real.sqrt x = 2 * ε := by linarith
      nlinarith
  · rintro (h | h)
    · subst h; simp
    · subst h
      have : Real.sqrt (4 * ε ^ 2) = 2 * ε := by
        rw [show 4 * ε ^ 2 = (2 * ε) ^ 2 by ring]; exact Real.sqrt_sq (by linarith)
      rw [this]; ring

/-- The positive implicit successor `(ε + √(ε² + a))²`. -/
noncomputable def implicitRoot (ε a : ℝ) : ℝ := (ε + Real.sqrt (ε ^ 2 + a)) ^ 2

theorem implicitRoot_spec (ε a : ℝ) (hε : 0 ≤ ε) (ha : 0 ≤ a) :
    implicitRoot ε a = a + 2 * ε * Real.sqrt |implicitRoot ε a| := by
  unfold implicitRoot
  have hs : 0 ≤ Real.sqrt (ε ^ 2 + a) := Real.sqrt_nonneg _
  rw [abs_of_nonneg (sq_nonneg _), Real.sqrt_sq (by linarith)]
  have := Real.sq_sqrt (by positivity : 0 ≤ ε ^ 2 + a)
  nlinarith

theorem implicitRoot_pos (ε a : ℝ) (hε : 0 < ε) (ha : 0 ≤ a) : 0 < implicitRoot ε a := by
  unfold implicitRoot; have := Real.sqrt_nonneg (ε ^ 2 + a); positivity

/-- From a positive state the implicit step has exactly one admissible successor. -/
theorem implicit_pos_unique (ε a y z : ℝ) (_hε : 0 ≤ ε) (ha : 0 < a) (hy : 0 ≤ y) (hz : 0 ≤ z)
    (hy' : y = a + 2 * ε * Real.sqrt |y|) (hz' : z = a + 2 * ε * Real.sqrt |z|) : y = z := by
  rw [abs_of_nonneg hy] at hy'; rw [abs_of_nonneg hz] at hz'
  have hv := Real.sq_sqrt hy; have hw := Real.sq_sqrt hz
  have v0 := Real.sqrt_nonneg y; have w0 := Real.sqrt_nonneg z
  have hfac : (Real.sqrt y - Real.sqrt z) * (Real.sqrt y + Real.sqrt z - 2 * ε) = 0 := by nlinarith
  rcases mul_eq_zero.mp hfac with h | h
  · have : Real.sqrt y = Real.sqrt z := by linarith
    rw [← hv, ← hw, this]
  · exfalso
    have : Real.sqrt y * (Real.sqrt y - 2 * ε) = -(Real.sqrt y * Real.sqrt z) := by nlinarith
    nlinarith [mul_nonneg v0 w0]

/-- An implicit orbit of `ẋ = √|x|`. -/
def IsImplicitOrbit (ε : ℝ) (x : ℕ → ℝ) : Prop :=
  x 0 = 0 ∧ ∀ k, 0 ≤ x k ∧ x (k + 1) = x k + 2 * ε * Real.sqrt |x (k + 1)|

theorem implicitOrbit_mono (ε : ℝ) (hε : 0 ≤ ε) (x : ℕ → ℝ) (hx : IsImplicitOrbit ε x) (k : ℕ) :
    x k ≤ x (k + 1) := by
  rw [(hx.2 k).2]; have := Real.sqrt_nonneg |x (k + 1)|; nlinarith

/-- Implicit orbits from `0` are determined by their departure step `m`
(the last step at which the orbit is still `0`). -/
theorem implicit_orbit_eq (ε : ℝ) (hε : 0 < ε) (x y : ℕ → ℝ) (hx : IsImplicitOrbit ε x)
    (hy : IsImplicitOrbit ε y) (m : ℕ) (hxm : ∀ j ≤ m, x j = 0) (hym : ∀ j ≤ m, y j = 0)
    (hx1 : 0 < x (m + 1)) (hy1 : 0 < y (m + 1)) : ∀ j, x j = y j := by
  have hpos : ∀ (z : ℕ → ℝ), IsImplicitOrbit ε z → 0 < z (m + 1) → ∀ i, 0 < z (m + 1 + i) := by
    intro z hz h0 i
    induction i with
    | zero => simpa using h0
    | succ i ih => exact ih.trans_le (implicitOrbit_mono ε hε.le z hz _)
  have base : x (m + 1) = y (m + 1) := by
    have ex := (hx.2 m).2; have ey := (hy.2 m).2
    rw [hxm m le_rfl] at ex; rw [hym m le_rfl] at ey
    have a := (sqrt_implicit_dichotomy ε _ hε.le (hx.2 (m + 1)).1).mp ex
    have b := (sqrt_implicit_dichotomy ε _ hε.le (hy.2 (m + 1)).1).mp ey
    rcases a with a | a
    · linarith
    rcases b with b | b
    · linarith
    rw [a, b]
  have tail : ∀ i, x (m + 1 + i) = y (m + 1 + i) := by
    intro i
    induction i with
    | zero => simpa using base
    | succ i ih =>
      have ex := (hx.2 (m + 1 + i)).2; have ey := (hy.2 (m + 1 + i)).2
      rw [ih] at ex
      exact implicit_pos_unique ε _ _ _ hε.le (by rw [← ih]; exact hpos x hx hx1 i)
        (hx.2 _).1 (hy.2 _).1 ex ey
  intro j
  by_cases hj : j ≤ m
  · rw [hxm j hj, hym j hj]
  · obtain ⟨i, rfl⟩ : ∃ i, j = m + 1 + i := ⟨j - (m + 1), by omega⟩
    exact tail i

/-- Orbits that never depart coincide with the zero orbit. -/
theorem implicit_orbit_zero (ε : ℝ) (x : ℕ → ℝ) (hx : ∀ j, x j = 0) : IsImplicitOrbit ε x :=
  ⟨hx 0, fun k => by simp [hx]⟩

end Sqrt

/-- `(1 + x)^k ≤ e^{kx}` for `x ≥ 0`: the granular Grönwall factor is below the classical one. -/
theorem one_add_pow_le_exp (x : ℝ) (hx : 0 ≤ x) (k : ℕ) : (1 + x) ^ k ≤ Real.exp (k * x) := by
  rw [Real.exp_nat_mul]
  exact pow_le_pow_left₀ (by linarith) (by linarith [Real.add_one_le_exp x]) k

end QE.ODE
