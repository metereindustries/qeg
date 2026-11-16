-- SPDX-License-Identifier: MIT
-- Copyright 2026 Metere Industries, Inc. Author: Alfredo Metere.
-- Quasi-Euclidean Granular Geometry. Any derivative work must carry this notice:
--   This work is derivative of the Quasi-Euclidean Granular Geometry book
--   authored by Alfredo Metere. Copyright 2026 Metere Industries, Inc.
--   All rights reserved
-- See LICENSE.md and NOTICE.

import QuasiEuclidean.Basic

/-!
# Chapter 6: Real analysis on the granular line (`QE.Analysis`)

Machine-checked content of Chapter 6 of *Quasi-Euclidean Granular Geometry*.

* Granular distributions on lattice indices: `δ_ε`, the closed Heaviside function, the exact
  identities `δ_ε² = δ_ε/(2ε)`, `D⁻H = δ_ε`, `x · pv(1/x) = 1 - 2εδ_ε`, and the algebraic
  obstructions (Schwartz type) that the granular calculus escapes.
* Exact discrete Dirichlet kernel; exact granular Hölder and Minkowski inequalities.
* The hyperfinite torus `ℤ/Nℤ`: exact Fourier inversion, Parseval, convolution, shift,
  finite Poisson summation, and the Donoho–Stark uncertainty principle.
* Shadows (Mathlib `Hyperreal`): Robinson's compactness criterion, continuity and uniform
  continuity as S-continuity, nonstandard Heine–Cantor, Cauchy's criterion, completeness via
  the standard part, uniform convergence as S-convergence.
* Pathological functions on the lattice: Dirichlet and Thomae.

All finitary identities hold for every `ε` in every linearly ordered field (or for every `N`),
so the infinitesimal and the physical instantiations are special cases.
-/

set_option linter.unusedSectionVars false

namespace QE.Analysis

open Finset

section Distributions
variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-- Granular delta on lattice indices: `1/(2ε)` at the index `0`, zero elsewhere. -/
def delta (ε : K) (k : ℤ) : K := if k = 0 then 1 / (2 * ε) else 0

/-- Heaviside function with the closed convention `H(0) = 1`. -/
def heaviside (k : ℤ) : K := if 0 ≤ k then 1 else 0

/-- Symmetric (midpoint) Heaviside, `H(0) = 1/2`. -/
def heavisideHalf (k : ℤ) : K := if 0 < k then 1 else if k = 0 then 1 / 2 else 0

/-- Forward granular difference quotient on lattice indices. -/
def dp (ε : K) (u : ℤ → K) (k : ℤ) : K := (u (k + 1) - u k) / (2 * ε)

/-- Backward granular difference quotient on lattice indices. -/
def dm (ε : K) (u : ℤ → K) (k : ℤ) : K := (u k - u (k - 1)) / (2 * ε)

/-- Granular pairing over the window of indices `[-M, M]`. -/
def pair (ε : K) (M : ℕ) (u φ : ℤ → K) : K :=
  ∑ k ∈ Icc (-(M : ℤ)) M, u k * φ k * (2 * ε)

theorem pair_delta (ε : K) (hε : ε ≠ 0) (M : ℕ) (φ : ℤ → K) :
    pair ε M (delta ε) φ = φ 0 := by
  unfold pair delta
  rw [Finset.sum_eq_single (0 : ℤ)]
  · simp; field_simp
  · intro b _ hb; simp [hb]
  · intro h; exfalso; apply h; simp

/-- `δ_ε² = δ_ε / (2ε)` exactly. -/
theorem delta_sq (ε : K) (k : ℤ) : delta ε k * delta ε k = delta ε k / (2 * ε) := by
  unfold delta; split_ifs <;> simp; ring

/-- Powers: `δ_ε^(m+1) = δ_ε / (2ε)^m`. -/
theorem delta_pow (ε : K) (hε : ε ≠ 0) (m : ℕ) (k : ℤ) :
    delta ε k ^ (m + 1) = delta ε k / (2 * ε) ^ m := by
  unfold delta; split_ifs
  · rw [pow_succ, div_pow, one_pow]; field_simp
  · simp

theorem pair_delta_sq (ε : K) (hε : ε ≠ 0) (M : ℕ) (φ : ℤ → K) :
    pair ε M (fun k => delta ε k * delta ε k) φ = φ 0 / (2 * ε) := by
  have : (fun k => delta ε k * delta ε k) = fun k => delta ε k * (1 / (2 * ε)) := by
    funext k; rw [delta_sq]; ring
  rw [this]
  have h2 : pair ε M (fun k => delta ε k * (1 / (2 * ε))) φ
      = pair ε M (delta ε) (fun k => φ k * (1 / (2 * ε))) := by
    unfold pair; apply Finset.sum_congr rfl; intro k _; ring
  rw [h2, pair_delta ε hε]; ring

/-- The backward granular derivative of the closed Heaviside function is `δ_ε`. -/
theorem dm_heaviside (ε : K) (k : ℤ) : dm ε heaviside k = delta ε k := by
  unfold dm heaviside delta
  by_cases h0 : k = 0
  · subst h0; simp
  · by_cases hk : 0 < k
    · have h1 : 0 ≤ k - 1 := by omega
      rw [ite_eq_left hk.le, ite_eq_left h1, ite_eq_right h0]; simp
    · have h2 : ¬ 0 ≤ k := by omega
      have h1 : ¬ 0 ≤ k - 1 := by omega
      rw [ite_eq_right h2, ite_eq_right h1, ite_eq_right h0]; simp

/-- The forward granular derivative of `H` is the delta shifted by one granule. -/
theorem dp_heaviside (ε : K) (k : ℤ) : dp ε heaviside k = delta ε (k + 1) := by
  unfold dp heaviside delta
  by_cases h0 : k + 1 = 0
  · have : ¬ 0 ≤ k := by omega
    simp [h0, this]
  · by_cases hk : 0 ≤ k
    · have : 0 ≤ k + 1 := by omega
      simp [h0, hk, this]
    · have : ¬ 0 ≤ k + 1 := by omega
      simp [*]

theorem heaviside_sq (k : ℤ) : (heaviside k : K) * heaviside k = heaviside k := by
  unfold heaviside; split_ifs <;> simp

theorem heaviside_mul_delta (ε : K) (k : ℤ) : heaviside k * delta ε k = delta ε k := by
  unfold heaviside delta; split_ifs <;> simp_all

theorem heavisideHalf_mul_delta (ε : K) (k : ℤ) :
    heavisideHalf k * delta ε k = delta ε k / 2 := by
  unfold heavisideHalf delta; split_ifs <;> simp_all; ring

theorem heavisideHalf_sq_ne : (heavisideHalf 0 : K) * heavisideHalf 0 ≠ heavisideHalf 0 := by
  unfold heavisideHalf; norm_num

/-- Heaviside function with an arbitrary value `θ` at the origin. -/
def heavisideTheta (θ : K) (k : ℤ) : K := if 0 < k then 1 else if k = 0 then θ else 0

/-- `H_θ^n δ_ε = θ^n δ_ε` exactly: the value of `H` on the point-sphere at `0` is all that
the product sees. For `θ = 1` (closed half-line) this is `δ_ε`; Colombeau's association
`Hⁿδ ≈ δ/(n+1)` is the average `∫₀¹ θⁿ dθ` of this over an unresolved profile. -/
theorem heavisideTheta_pow_mul_delta (ε θ : K) (n : ℕ) (k : ℤ) :
    heavisideTheta θ k ^ n * delta ε k = θ ^ n * delta ε k := by
  unfold heavisideTheta delta
  by_cases h : k = 0
  · subst h; simp
  · simp [h]

/-- `D⁻(H^{n+1}) = δ_ε` for the closed Heaviside function, for every `n`. -/
theorem dm_heaviside_pow (ε : K) (n : ℕ) (k : ℤ) :
    dm ε (fun j => (heaviside j : K) ^ (n + 1)) k = delta ε k := by
  have : (fun j => (heaviside j : K) ^ (n + 1)) = heaviside := by
    funext j; unfold heaviside; split_ifs <;> simp
  rw [this, dm_heaviside]

/-- Backward granular Leibniz rule with its exact cross term. -/
theorem dm_mul (ε : K) (hε : ε ≠ 0) (u v : ℤ → K) (k : ℤ) :
    dm ε (fun j => u j * v j) k
      = u k * dm ε v k + v k * dm ε u k - 2 * ε * (dm ε u k * dm ε v k) := by
  unfold dm; field_simp; ring

/-- Differentiating `H² = H` granularly: `δ = 2Hδ - 2ε δ²`, exactly. The term `2εδ²`
equals `δ`; the classical computation drops it and concludes `Hδ = δ/2`. -/
theorem delta_from_heaviside_sq (ε : K) (hε : ε ≠ 0) (k : ℤ) :
    delta ε k = 2 * (heaviside k * delta ε k) - 2 * ε * (delta ε k * delta ε k) := by
  have h := dm_mul ε hε heaviside heaviside k
  have hH : (fun j => (heaviside j : K) * heaviside j) = heaviside := by
    funext j; exact heaviside_sq j
  rw [hH, dm_heaviside] at h
  linear_combination h

theorem two_eps_delta_sq (ε : K) (hε : ε ≠ 0) (k : ℤ) :
    2 * ε * (delta ε k * delta ε k) = delta ε k := by
  rw [delta_sq]; field_simp

/-- With the forward derivative the product reads the other side of the jump:
`H · D⁺H = 0` exactly, while `H · D⁻H = D⁻H = δ_ε` (`heaviside_mul_delta`). -/
theorem heaviside_mul_dp_heaviside (ε : K) (k : ℤ) :
    heaviside k * dp ε heaviside k = 0 := by
  rw [dp_heaviside]; unfold heaviside delta
  by_cases h : k + 1 = 0
  · have : ¬ 0 ≤ k := by omega
    simp [this]
  · simp [h]

/-- Twisted forward Leibniz rule applied to `H² = H`: `D⁺H = 2H D⁺H + 2ε (D⁺H)²`, i.e.
`D⁺H = 2ε (D⁺H)²` exactly. -/
theorem dp_heaviside_eq_sq (ε : K) (hε : ε ≠ 0) (k : ℤ) :
    dp ε heaviside k = 2 * ε * (dp ε heaviside k * dp ε heaviside k) := by
  rw [dp_heaviside, two_eps_delta_sq ε hε]

/-- Abstract obstruction: in a commutative ring, an additive map obeying the exact
Leibniz rule kills every idempotent. -/
theorem leibniz_kills_idempotent {R : Type*} [CommRing R] (D : R → R)
    (hD : ∀ a b, D (a * b) = a * D b + b * D a) (e : R) (he : e * e = e) : D e = 0 := by
  have h1 : D e = 2 * (e * D e) := by
    have := hD e e; rw [he] at this; linear_combination this
  have h2 : e * D e = 0 := by
    have : e * D e = 2 * (e * D e) := by
      calc e * D e = e * (2 * (e * D e)) := by rw [← h1]
        _ = 2 * ((e * e) * D e) := by ring
        _ = 2 * (e * D e) := by rw [he]
    linear_combination -this
  rw [h1, h2]; ring

/-- Schwartz-type associativity obstruction: in any ring, `x δ = 0` and `x v = 1`
force `δ = 0`. -/
theorem assoc_obstruction {R : Type*} [Ring R] (x d v : R) (hxd : d * x = 0)
    (hxv : x * v = 1) : d = 0 := by
  calc d = d * (x * v) := by rw [hxv, mul_one]
    _ = (d * x) * v := by rw [mul_assoc]
    _ = 0 := by rw [hxd, zero_mul]

/-- Schwartz's impossibility argument, in abstract form. Let `A` be any (associative, not
necessarily commutative) ring with an additive map `D` obeying the exact Leibniz rule. Suppose
`x, H, g ∈ A` satisfy the three classical facts `x' = 1`, `(Hx)' = H` (i.e. `(x₊)' = H`) and
`(x g)'' = 2 g' + 1` (for `g = x ln|x| - x`). Then `δ := D H` vanishes. -/
theorem schwartz_abstract {A : Type*} [Ring A] (D : A →+ A)
    (hD : ∀ a b, D (a * b) = D a * b + a * D b) (x H g : A)
    (hx : D x = 1) (hHx : D (H * x) = H) (hxg : D (D (x * g)) = 2 * D g + 1) :
    D H = 0 := by
  have hδx : D H * x = 0 := by
    have h := hD H x
    rw [hx, mul_one, hHx] at h
    exact add_eq_right.mp h.symm
  have hxv : x * D (D g) = 1 := by
    have h1 := hD x g
    rw [hx, one_mul] at h1
    have h2 : D (D (x * g)) = D g + (D x * D g + x * D (D g)) := by
      rw [h1, map_add, hD]
    rw [hx, one_mul, hxg, two_mul] at h2
    have h3 : (D g + D g) + 1 = (D g + D g) + x * D (D g) := by rw [h2]; abel
    exact (add_left_cancel h3).symm
  exact assoc_obstruction x (D H) (D (D g)) hδx hxv

/-- The position function `x = 2εk` on lattice indices. -/
def pos (ε : K) (k : ℤ) : K := 2 * ε * k

/-- Granular principal value of `1/x`: `1/x` off the origin, `0` at the origin. -/
def pv (ε : K) (k : ℤ) : K := if k = 0 then 0 else 1 / (2 * ε * k)

theorem pos_mul_delta (ε : K) (k : ℤ) : pos ε k * delta ε k = 0 := by
  unfold pos delta; split_ifs with h <;> simp [h]

/-- `x · pv(1/x) = 1 - 2ε δ_ε` exactly. -/
theorem pos_mul_pv (ε : K) (hε : ε ≠ 0) (k : ℤ) :
    pos ε k * pv ε k = 1 - 2 * ε * delta ε k := by
  unfold pos pv delta
  split_ifs with h
  · subst h; field_simp; ring
  · have : (k : K) ≠ 0 := by exact_mod_cast h
    simp; field_simp

/-- Associativity is consistent granularly: `δ (x v) = (δ x) v = 0`, because
`δ (1 - 2εδ) = δ - 2εδ² = 0`. -/
theorem delta_mul_pos_mul_pv (ε : K) (hε : ε ≠ 0) (k : ℤ) :
    delta ε k * (pos ε k * pv ε k) = 0 ∧ (delta ε k * pos ε k) * pv ε k = 0 := by
  constructor
  · rw [pos_mul_pv ε hε, mul_sub, mul_one]
    have := two_eps_delta_sq ε hε k
    linear_combination -this
  · rw [mul_comm (delta ε k), pos_mul_delta]; simp

/-- Pairing of the granular derivative of `δ`: summation by parts with explicit
boundary data (`φ` evaluated at the two indices adjacent to `0`). -/
theorem pair_dp_delta (ε : K) (hε : ε ≠ 0) (M : ℕ) (hM : 1 ≤ M) (φ : ℤ → K) :
    pair ε M (dp ε (delta ε)) φ = -(φ 0 - φ (-1)) / (2 * ε) := by
  unfold pair dp delta
  have hmem0 : (0 : ℤ) ∈ Icc (-(M : ℤ)) M := by simp
  have hmem1 : (-1 : ℤ) ∈ Icc (-(M : ℤ)) M := by simp; omega
  rw [← Finset.add_sum_erase _ _ hmem0, ← Finset.add_sum_erase _ _
    (Finset.mem_erase.mpr ⟨by norm_num, hmem1⟩)]
  rw [Finset.sum_eq_zero]
  · simp; field_simp; ring
  · intro b hb
    simp only [Finset.mem_erase] at hb
    have h1 : b + 1 ≠ 0 := by omega
    simp [hb.2.1, h1]

/-- The lattice function `|x| = |2εk|`. -/
def absL (ε : K) (k : ℤ) : K := |2 * ε * k|

theorem dm_absL (ε : K) (hε : 0 < ε) (k : ℤ) :
    dm ε (absL ε) k = if 1 ≤ k then 1 else -1 := by
  unfold dm absL
  have h2 : (0 : K) < 2 * ε := by linarith
  rw [abs_mul (2 * ε) (k : K), abs_mul (2 * ε) ((k - 1 : ℤ) : K), abs_of_pos h2]
  split_ifs with h
  · have h1 : (0 : K) ≤ (k : K) := by exact_mod_cast (by omega : (0 : ℤ) ≤ k)
    have h3 : (0 : K) ≤ ((k - 1 : ℤ) : K) := by exact_mod_cast (by omega : (0 : ℤ) ≤ k - 1)
    rw [abs_of_nonneg h1, abs_of_nonneg h3]; push_cast; field_simp; ring
  · have h1 : (k : K) ≤ 0 := by exact_mod_cast (by omega : k ≤ (0 : ℤ))
    have h3 : ((k - 1 : ℤ) : K) ≤ 0 := by exact_mod_cast (by omega : k - 1 ≤ (0 : ℤ))
    rw [abs_of_nonpos h1, abs_of_nonpos h3]; push_cast; field_simp; ring

/-- `D⁺D⁻|x| = 2δ_ε` exactly: the classical identity `|x|'' = 2δ` holds on the nose. -/
theorem dpdm_absL (ε : K) (hε : 0 < ε) (k : ℤ) :
    dp ε (dm ε (absL ε)) k = 2 * delta ε k := by
  unfold dp
  rw [dm_absL ε hε, dm_absL ε hε]
  unfold delta
  by_cases h0 : k = 0
  · subst h0; norm_num; field_simp
  · rw [ite_eq_right h0]
    by_cases hk : 1 ≤ k
    · rw [ite_eq_left (by omega : 1 ≤ k + 1), ite_eq_left hk]; simp
    · rw [ite_eq_right (by omega : ¬ 1 ≤ k + 1), ite_eq_right hk]; simp

/-- The lattice function `x₊ = max(x,0)`. -/
def xplus (ε : K) (k : ℤ) : K := if 0 ≤ k then 2 * ε * k else 0

/-- `D⁺D⁻x₊ = δ_ε` and `D⁻x₊ = H - 2εδ_ε` (the open Heaviside function). -/
theorem dm_xplus (ε : K) (hε : ε ≠ 0) (k : ℤ) :
    dm ε (xplus ε) k = heaviside k - 2 * ε * delta ε k := by
  unfold dm xplus heaviside delta
  by_cases h0 : k = 0
  · subst h0; simp; field_simp; ring
  · by_cases hk : 1 ≤ k
    · rw [ite_eq_left (by omega : (0 : ℤ) ≤ k), ite_eq_left (by omega : (0 : ℤ) ≤ k - 1),
        ite_eq_left (by omega : (0 : ℤ) ≤ k), ite_eq_right h0]
      push_cast; field_simp; ring
    · rw [ite_eq_right (by omega : ¬ (0 : ℤ) ≤ k), ite_eq_right (by omega : ¬ (0 : ℤ) ≤ k - 1),
        ite_eq_right (by omega : ¬ (0 : ℤ) ≤ k), ite_eq_right h0]
      simp

theorem dpdm_xplus (ε : K) (hε : ε ≠ 0) (k : ℤ) :
    dp ε (dm ε (xplus ε)) k = delta ε k := by
  unfold dp
  rw [dm_xplus ε hε, dm_xplus ε hε]
  unfold heaviside delta
  by_cases h0 : k = 0
  · subst h0; simp; field_simp
  · by_cases hk : 0 ≤ k
    · have h1 : k + 1 ≠ 0 := by omega
      rw [ite_eq_left (by omega : (0 : ℤ) ≤ k + 1), ite_eq_left hk, ite_eq_right h1, ite_eq_right h0]; simp
    · rw [ite_eq_right hk, ite_eq_right h0]
      by_cases h1 : k + 1 = 0
      · rw [ite_eq_left (by omega : (0 : ℤ) ≤ k + 1), ite_eq_left h1]; field_simp; ring
      · rw [ite_eq_right (by omega : ¬ (0 : ℤ) ≤ k + 1), ite_eq_right h1]; simp

end Distributions

section Kernel

/-- Discrete Dirichlet kernel identity:
`2 sin(θ/2) (1 + 2 ∑_{k=1}^{M} cos kθ) = 2 sin((M+1/2)θ)`. -/
theorem dirichlet_kernel (θ : ℝ) (M : ℕ) :
    2 * Real.sin (θ / 2) * (1 + 2 * ∑ k ∈ Finset.range M, Real.cos ((k + 1 : ℕ) * θ))
      = 2 * Real.sin ((M + 1 / 2) * θ) := by
  induction M with
  | zero => simp; ring_nf
  | succ n ih =>
    rw [Finset.sum_range_succ]
    have key : Real.sin ((((n + 1 : ℕ) : ℝ) + 1 / 2) * θ) - Real.sin ((n + 1 / 2) * θ)
        = 2 * Real.sin (θ / 2) * Real.cos (((n + 1 : ℕ) : ℝ) * θ) := by
      rw [Real.sin_sub_sin]; push_cast; ring_nf
    push_cast at key ih ⊢
    linear_combination ih - 2 * key

end Kernel

section Lp

/-- Granular `L^p` integral `∑ |f|^p 2ε` over a finite set of indices. -/
noncomputable def lpSum (ε : ℝ) (p : ℝ) (s : Finset ℤ) (f : ℤ → ℝ) : ℝ :=
  ∑ k ∈ s, |f k| ^ p * (2 * ε)

/-- Exact granular Hölder inequality. -/
theorem holder (ε : ℝ) (hε : 0 < ε) {p q : ℝ} (hpq : p.HolderConjugate q)
    (s : Finset ℤ) (f g : ℤ → ℝ) :
    ∑ k ∈ s, f k * g k * (2 * ε) ≤ lpSum ε p s f ^ (1 / p) * lpSum ε q s g ^ (1 / q) := by
  have hw : 0 ≤ 2 * ε := by linarith
  have H := Real.inner_le_Lp_mul_Lq s f g hpq
  unfold lpSum
  rw [← Finset.sum_mul, ← Finset.sum_mul, ← Finset.sum_mul]
  have hA : 0 ≤ ∑ k ∈ s, |f k| ^ p := Finset.sum_nonneg fun _ _ => by positivity
  have hB : 0 ≤ ∑ k ∈ s, |g k| ^ q := Finset.sum_nonneg fun _ _ => by positivity
  rw [Real.mul_rpow hA hw, Real.mul_rpow hB hw]
  have hw1 : (2 * ε) ^ (1 / p) * (2 * ε) ^ (1 / q) = 2 * ε := by
    rw [← Real.rpow_add (by linarith)]
    have : 1 / p + 1 / q = 1 := by
      have := hpq.inv_add_inv_eq_one; simpa [one_div] using this
    rw [this, Real.rpow_one]
  calc (∑ k ∈ s, f k * g k) * (2 * ε)
      ≤ ((∑ k ∈ s, |f k| ^ p) ^ (1 / p) * (∑ k ∈ s, |g k| ^ q) ^ (1 / q)) * (2 * ε) :=
        mul_le_mul_of_nonneg_right H hw
    _ = (∑ k ∈ s, |f k| ^ p) ^ (1 / p) * (2 * ε) ^ (1 / p) *
        ((∑ k ∈ s, |g k| ^ q) ^ (1 / q) * (2 * ε) ^ (1 / q)) := by
          linear_combination (-((∑ k ∈ s, |f k| ^ p) ^ (1 / p) *
            (∑ k ∈ s, |g k| ^ q) ^ (1 / q))) * hw1

/-- Exact granular Minkowski inequality. -/
theorem minkowski (ε : ℝ) (hε : 0 < ε) {p : ℝ} (hp : 1 ≤ p) (s : Finset ℤ) (f g : ℤ → ℝ) :
    lpSum ε p s (fun k => f k + g k) ^ (1 / p)
      ≤ lpSum ε p s f ^ (1 / p) + lpSum ε p s g ^ (1 / p) := by
  have hw : 0 ≤ 2 * ε := by linarith
  have H := Real.Lp_add_le s f g hp
  unfold lpSum
  rw [← Finset.sum_mul, ← Finset.sum_mul, ← Finset.sum_mul]
  have hA : 0 ≤ ∑ k ∈ s, |f k + g k| ^ p := Finset.sum_nonneg fun _ _ => by positivity
  have hB : 0 ≤ ∑ k ∈ s, |f k| ^ p := Finset.sum_nonneg fun _ _ => by positivity
  have hC : 0 ≤ ∑ k ∈ s, |g k| ^ p := Finset.sum_nonneg fun _ _ => by positivity
  rw [Real.mul_rpow hA hw, Real.mul_rpow hB hw, Real.mul_rpow hC hw, ← add_mul]
  exact mul_le_mul_of_nonneg_right H (by positivity)

/-- Sup bound with the explicit (infinite, if `ε` is infinitesimal) constant `(2ε)^{-1}`:
`|f k|^p ≤ (2ε)⁻¹ ∑ |f|^p 2ε`. -/
theorem pointwise_le_lpSum (ε : ℝ) (hε : 0 < ε) (p : ℝ) (s : Finset ℤ) (f : ℤ → ℝ)
    {k : ℤ} (hk : k ∈ s) : |f k| ^ p ≤ (2 * ε)⁻¹ * lpSum ε p s f := by
  unfold lpSum
  rw [← Finset.sum_mul]
  have : |f k| ^ p ≤ ∑ j ∈ s, |f j| ^ p :=
    Finset.single_le_sum (f := fun j => |f j| ^ p) (fun _ _ => by positivity) hk
  have h2 : (2 * ε)⁻¹ * ((∑ j ∈ s, |f j| ^ p) * (2 * ε)) = ∑ j ∈ s, |f j| ^ p := by
    field_simp
  linarith

/-- The `L^2` norm of `δ_ε`: `∑ δ² 2ε = 1/(2ε)` (finite for each `ε`, infinite when `ε`
is infinitesimal). -/
theorem delta_L2 (ε : ℝ) (hε : 0 < ε) (M : ℕ) :
    ∑ k ∈ Icc (-(M : ℤ)) M, delta ε k * delta ε k * (2 * ε) = 1 / (2 * ε) := by
  have := pair_delta_sq ε hε.ne' M (fun _ => 1)
  unfold pair at this; simpa using this

end Lp

end QE.Analysis

namespace QE.Analysis

open Filter Topology

noncomputable section

section Shadow
open Hyperreal

/-- `x ≃ r`: the hyperreal `x` is infinitely close to the standard real `r`
(equivalently `st x = r`). -/
def NearSt (x : ℝ*) (r : ℝ) : Prop := Filter.Germ.Tendsto x (𝓝 r)

/-- `x` is infinitesimal. -/
def Infinitesimal (x : ℝ*) : Prop := NearSt x 0

/-- The nonstandard extension `*f` of a standard function. -/
def starF (f : ℝ → ℝ) (x : ℝ*) : ℝ* := Filter.Germ.map f x

/-- Membership in the nonstandard extension `*S` of a standard set. -/
def InStar (S : Set ℝ) (x : ℝ*) : Prop := Filter.Germ.LiftPred (· ∈ S) x

theorem nearSt_ofSeq (s : ℕ → ℝ) (r : ℝ) :
    NearSt (ofSeq s) r ↔ Tendsto s (hyperfilter ℕ) (𝓝 r) := Iff.rfl

theorem starF_ofSeq (f : ℝ → ℝ) (s : ℕ → ℝ) : starF f (ofSeq s) = ofSeq (f ∘ s) := rfl

theorem inStar_ofSeq (S : Set ℝ) (s : ℕ → ℝ) :
    InStar S (ofSeq s) ↔ ∀ᶠ n in hyperfilter ℕ, s n ∈ S := Filter.Germ.liftPred_coe

theorem ofSeq_sub (a b : ℕ → ℝ) : ofSeq a - ofSeq b = ofSeq (a - b) := rfl

/-- Robinson's characterisation of compactness: `S` is compact iff every point of `*S`
is infinitely close to a (standard) point of `S`. -/
theorem robinson_compact (S : Set ℝ) :
    IsCompact S ↔ ∀ x : ℝ*, InStar S x → ∃ r ∈ S, NearSt x r := by
  constructor
  · intro hS x hx
    obtain ⟨s, rfl⟩ := ofSeq_surjective x
    rw [inStar_ofSeq] at hx
    obtain ⟨r, hr, hle⟩ := hS.ultrafilter_le_nhds (Ultrafilter.map s (hyperfilter ℕ))
      (by rw [Ultrafilter.coe_map, Filter.le_principal_iff]; exact hx)
    exact ⟨r, hr, by rw [nearSt_ofSeq]; rw [Ultrafilter.coe_map] at hle; exact hle⟩
  · intro H
    rw [isCompact_iff_isSeqCompact]
    intro u hu
    obtain ⟨r, hr, hnear⟩ := H (ofSeq u) (by
      rw [inStar_ofSeq]; exact Filter.Eventually.of_forall hu)
    rw [nearSt_ofSeq] at hnear
    refine ⟨r, hr, MapClusterPt.tendsto_subseq ?_⟩
    have h1 : Filter.map u (hyperfilter ℕ) ≤ 𝓝 r := hnear
    have h2 : Filter.map u (hyperfilter ℕ) ≤ Filter.map u atTop :=
      Filter.map_mono Nat.hyperfilter_le_atTop
    exact Filter.NeBot.mono (by infer_instance) (le_inf h1 h2)

/-- Compactness of `[a,b]`: every hyperreal in `*[a,b]` has a shadow in `[a,b]`. -/
theorem shadow_Icc {a b : ℝ} (x : ℝ*) (hx : InStar (Set.Icc a b) x) :
    ∃ r ∈ Set.Icc a b, NearSt x r :=
  (robinson_compact _).1 isCompact_Icc x hx

/-- Continuity is S-continuity: `f` is continuous at `r` iff `x ≃ r ⇒ *f(x) ≃ f(r)`. -/
theorem continuousAt_iff_S (f : ℝ → ℝ) (r : ℝ) :
    ContinuousAt f r ↔ ∀ x : ℝ*, NearSt x r → NearSt (starF f x) (f r) := by
  constructor
  · intro hf x hx
    obtain ⟨s, rfl⟩ := ofSeq_surjective x
    exact hf.tendsto.comp hx
  · intro H
    rw [Metric.continuousAt_iff]
    by_contra hcon
    push Not at hcon
    obtain ⟨η, hη, hbad⟩ := hcon
    have hδ : ∀ n : ℕ, (0 : ℝ) < 1 / ((n : ℝ) + 1) := fun n => by positivity
    choose s hs1 hs2 using fun n => hbad _ (hδ n)
    have hs : Tendsto s atTop (𝓝 r) := by
      rw [tendsto_iff_dist_tendsto_zero]
      exact squeeze_zero (fun n => dist_nonneg) (fun n => (hs1 n).le)
        tendsto_one_div_add_atTop_nhds_zero_nat
    have h := H (ofSeq s) ((nearSt_ofSeq s r).2 (hs.mono_left Nat.hyperfilter_le_atTop))
    rw [starF_ofSeq, nearSt_ofSeq] at h
    have hev := (Metric.tendsto_nhds.1 h) η hη
    obtain ⟨n, hn⟩ := hev.exists
    exact absurd (hs2 n) (not_le.2 hn)

/-- Uniform continuity is S-continuity at every pair of infinitely close hyperreals. -/
theorem uniformContinuous_iff_S (f : ℝ → ℝ) :
    UniformContinuous f ↔
      ∀ x y : ℝ*, Infinitesimal (x - y) → Infinitesimal (starF f x - starF f y) := by
  constructor
  · intro hf x y hxy
    obtain ⟨a, rfl⟩ := ofSeq_surjective x
    obtain ⟨b, rfl⟩ := ofSeq_surjective y
    unfold Infinitesimal at *
    rw [starF_ofSeq, starF_ofSeq, ofSeq_sub, nearSt_ofSeq]
    rw [ofSeq_sub, nearSt_ofSeq] at hxy
    rw [Metric.uniformContinuous_iff] at hf
    rw [Metric.tendsto_nhds] at hxy ⊢
    intro η hη
    obtain ⟨δ, hδ, hfδ⟩ := hf η hη
    filter_upwards [hxy δ hδ] with n hn
    simp only [Pi.sub_apply, Function.comp, Real.dist_eq, sub_zero] at hn ⊢
    exact hfδ (by rw [Real.dist_eq]; exact hn)
  · intro H
    rw [Metric.uniformContinuous_iff]
    by_contra hcon
    push Not at hcon
    obtain ⟨η, hη, hbad⟩ := hcon
    have hδ : ∀ n : ℕ, (0 : ℝ) < 1 / ((n : ℝ) + 1) := fun n => by positivity
    choose a b hab1 hab2 using fun n => hbad _ (hδ n)
    have hab : Tendsto (a - b) atTop (𝓝 0) := by
      rw [tendsto_iff_dist_tendsto_zero]
      refine squeeze_zero (fun n => dist_nonneg) (fun n => ?_)
        tendsto_one_div_add_atTop_nhds_zero_nat
      simp only [Pi.sub_apply, dist_zero_right, Real.norm_eq_abs]
      rw [← Real.dist_eq]; exact (hab1 n).le
    have h := H (ofSeq a) (ofSeq b) (by
      unfold Infinitesimal; rw [ofSeq_sub, nearSt_ofSeq]
      exact hab.mono_left Nat.hyperfilter_le_atTop)
    unfold Infinitesimal at h
    rw [starF_ofSeq, starF_ofSeq, ofSeq_sub, nearSt_ofSeq] at h
    obtain ⟨n, hn⟩ := ((Metric.tendsto_nhds.1 h) η hη).exists
    simp only [Pi.sub_apply, Function.comp, dist_zero_right, Real.norm_eq_abs] at hn
    rw [← Real.dist_eq] at hn
    exact absurd (hab2 n) (not_le.2 hn)

/-- Nonstandard Heine–Cantor: a function continuous on `[a,b]` is S-continuous at every
pair of infinitely close points of `*[a,b]`. -/
theorem S_continuous_on_Icc {a b : ℝ} (f : ℝ → ℝ) (hf : ContinuousOn f (Set.Icc a b))
    (x y : ℝ*) (hx : InStar (Set.Icc a b) x) (hy : InStar (Set.Icc a b) y)
    (hxy : Infinitesimal (x - y)) : Infinitesimal (starF f x - starF f y) := by
  obtain ⟨r, hr, hxr⟩ := shadow_Icc x hx
  obtain ⟨u, rfl⟩ := ofSeq_surjective x
  obtain ⟨v, rfl⟩ := ofSeq_surjective y
  unfold Infinitesimal at *
  rw [ofSeq_sub, nearSt_ofSeq] at hxy
  rw [nearSt_ofSeq] at hxr
  rw [inStar_ofSeq] at hx hy
  have hyr : Tendsto v (hyperfilter ℕ) (𝓝 r) := by
    have := hxr.sub hxy
    simp only [sub_zero] at this
    convert this using 1; funext n; simp
  have hu' : Tendsto u (hyperfilter ℕ) (𝓝[Set.Icc a b] r) :=
    tendsto_nhdsWithin_iff.2 ⟨hxr, hx⟩
  have hv' : Tendsto v (hyperfilter ℕ) (𝓝[Set.Icc a b] r) :=
    tendsto_nhdsWithin_iff.2 ⟨hyr, hy⟩
  have h1 := ((hf r hr).tendsto.comp hu').sub ((hf r hr).tendsto.comp hv')
  rw [sub_self] at h1
  rw [starF_ofSeq, starF_ofSeq, ofSeq_sub, nearSt_ofSeq]
  exact h1

/-- A hypernatural, represented by a sequence `ν`, is infinite. -/
def InfiniteNat (ν : ℕ → ℕ) : Prop := Tendsto ν (hyperfilter ℕ) atTop

/-- Cauchy's criterion as Robinson's: `(a_n)` is Cauchy iff `a_ν ≃ a_μ` for all infinite
hypernaturals `ν, μ`. -/
theorem cauchySeq_iff_S (a : ℕ → ℝ) :
    CauchySeq a ↔ ∀ ν μ : ℕ → ℕ, InfiniteNat ν → InfiniteNat μ →
      Infinitesimal (ofSeq (a ∘ ν) - ofSeq (a ∘ μ)) := by
  constructor
  · intro ha ν μ hν hμ
    unfold Infinitesimal
    rw [ofSeq_sub, nearSt_ofSeq, Metric.tendsto_nhds]
    intro η hη
    obtain ⟨N0, hN0⟩ := Metric.cauchySeq_iff.1 ha η hη
    filter_upwards [tendsto_atTop.1 hν N0, tendsto_atTop.1 hμ N0] with n h1 h2
    have := hN0 _ h1 _ h2
    simpa [Real.dist_eq] using this
  · intro H
    rw [Metric.cauchySeq_iff]
    by_contra hcon
    push Not at hcon
    obtain ⟨η, hη, hbad⟩ := hcon
    choose m hm n hn hmn using hbad
    have hmT : InfiniteNat m :=
      (tendsto_atTop_mono hm tendsto_id).mono_left Nat.hyperfilter_le_atTop
    have hnT : InfiniteNat n :=
      (tendsto_atTop_mono hn tendsto_id).mono_left Nat.hyperfilter_le_atTop
    have h := H m n hmT hnT
    unfold Infinitesimal at h
    rw [ofSeq_sub, nearSt_ofSeq] at h
    obtain ⟨k, hk⟩ := ((Metric.tendsto_nhds.1 h) η hη).exists
    have := hmn k
    simp only [Pi.sub_apply, Function.comp, Real.dist_eq, sub_zero] at hk this
    exact absurd this (not_le.2 hk)

/-- Completeness via the standard part: a Cauchy sequence converges to the shadow of its
value at the infinite hypernatural `ω`. -/
theorem cauchy_tendsto_stdPart (a : ℕ → ℝ) (ha : CauchySeq a) :
    Tendsto a atTop (𝓝 (ArchimedeanClass.stdPart (ofSeq a))) := by
  obtain ⟨B, hB⟩ : ∃ B, ∀ n, |a n| ≤ B := by
    obtain ⟨R, hR⟩ := (Metric.isBounded_range_iff.1 ha.isBounded_range) |>.imp
      fun R h => h
    refine ⟨|a 0| + R, fun n => ?_⟩
    have := hR n 0
    rw [Real.dist_eq] at this
    have := abs_sub_abs_le_abs_sub (a n) (a 0)
    linarith
  have hfin : 0 ≤ ArchimedeanClass.mk (ofSeq a) := by
    refine ArchimedeanClass.mk_nonneg_of_le_of_le_of_archimedean coeRingHom
      (r := -B) (s := B) ?_ ?_
    · show ((-B : ℝ) : ℝ*) ≤ ofSeq a
      exact ofSeq_le_ofSeq.2 (Filter.Eventually.of_forall fun n => by
        have := hB n; linarith [abs_le.1 this])
    · show ofSeq a ≤ ((B : ℝ) : ℝ*)
      exact ofSeq_le_ofSeq.2 (Filter.Eventually.of_forall fun n => by
        have := hB n; linarith [abs_le.1 this])
  rw [Metric.tendsto_atTop]
  intro η hη
  obtain ⟨N0, hN0⟩ := Metric.cauchySeq_iff.1 ha (η / 2) (by linarith)
  refine ⟨N0, fun m hm => ?_⟩
  have hev : ∀ᶠ n in hyperfilter ℕ, N0 ≤ n := Nat.hyperfilter_le_atTop (Filter.eventually_ge_atTop N0)
  have hup : ofSeq a ≤ coeRingHom (a m + η / 2) := by
    show ofSeq a ≤ ((a m + η / 2 : ℝ) : ℝ*)
    refine ofSeq_le_ofSeq.2 ?_
    filter_upwards [hev] with n hn
    have := hN0 n hn m hm; rw [Real.dist_eq] at this
    linarith [abs_lt.1 this]
  have hlo : coeRingHom (a m - η / 2) ≤ ofSeq a := by
    show ((a m - η / 2 : ℝ) : ℝ*) ≤ ofSeq a
    refine ofSeq_le_ofSeq.2 ?_
    filter_upwards [hev] with n hn
    have := hN0 n hn m hm; rw [Real.dist_eq] at this
    linarith [abs_lt.1 this]
  have h1 := ArchimedeanClass.stdPart_le_of_le coeRingHom hfin hup
  have h2 := ArchimedeanClass.le_stdPart_of_le coeRingHom hfin hlo
  rw [Real.dist_eq, abs_lt]; constructor <;> linarith

/-- Uniform convergence as S-convergence: `F_n → f` uniformly iff `*F_ν(x) ≃ *f(x)` for
every infinite hypernatural `ν` and every hyperreal `x = [s]`. -/
theorem tendstoUniformly_iff_S (F : ℕ → ℝ → ℝ) (f : ℝ → ℝ) :
    TendstoUniformly F f atTop ↔ ∀ (ν : ℕ → ℕ) (s : ℕ → ℝ), InfiniteNat ν →
      Infinitesimal (ofSeq (fun n => F (ν n) (s n)) - starF f (ofSeq s)) := by
  constructor
  · intro hF ν s hν
    unfold Infinitesimal
    rw [starF_ofSeq, ofSeq_sub, nearSt_ofSeq, Metric.tendsto_nhds]
    intro η hη
    have h := (Metric.tendstoUniformly_iff.1 hF) η hη
    filter_upwards [hν.eventually h] with n hn
    have := hn (s n)
    simp only [Pi.sub_apply, Function.comp, Real.dist_eq, sub_zero] at this ⊢
    rw [abs_sub_comm]; exact this
  · intro H
    rw [Metric.tendstoUniformly_iff]
    by_contra hcon
    push Not at hcon
    obtain ⟨η, hη, hbad⟩ := hcon
    rw [Filter.frequently_atTop] at hbad
    choose ν hν x hx using hbad
    have hνT : InfiniteNat ν :=
      (tendsto_atTop_mono hν tendsto_id).mono_left Nat.hyperfilter_le_atTop
    have h := H ν x hνT
    unfold Infinitesimal at h
    rw [starF_ofSeq, ofSeq_sub, nearSt_ofSeq] at h
    obtain ⟨k, hk⟩ := ((Metric.tendsto_nhds.1 h) η hη).exists
    have := hx k
    simp only [Pi.sub_apply, Function.comp, Real.dist_eq, sub_zero] at hk this
    rw [abs_sub_comm] at this
    exact absurd this (not_le.2 hk)

end Shadow

end

section Lattice
variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-- Discrete Lipschitz propagation: a one-granule bound `|u(k+1) - u(k)| ≤ L·2ε`
propagates exactly to `|u(k+m) - u(k)| ≤ L·2ε·m`. -/
theorem lipschitz_propagate (ε L : K) (u : ℤ → K) (h : ∀ k, |u (k + 1) - u k| ≤ L * (2 * ε))
    (k : ℤ) (m : ℕ) : |u (k + m) - u k| ≤ L * (2 * ε) * m := by
  induction m with
  | zero => simp
  | succ n ih =>
    have h1 := h (k + n)
    have : u (k + ((n + 1 : ℕ) : ℤ)) - u k = (u (k + n + 1) - u (k + n)) + (u (k + n) - u k) := by
      push_cast; ring_nf
    rw [this]
    calc |(u (k + n + 1) - u (k + n)) + (u (k + n) - u k)|
        ≤ |u (k + n + 1) - u (k + n)| + |u (k + n) - u k| := abs_add_le _ _
      _ ≤ L * (2 * ε) + L * (2 * ε) * n := add_le_add h1 ih
      _ = L * (2 * ε) * ((n + 1 : ℕ) : K) := by push_cast; ring

end Lattice

end QE.Analysis

namespace QE.Analysis

open Finset ZMod ComplexConjugate

section DFT
variable {N : ℕ} [NeZero N]

/-- The character `e(x) = exp(2πi x/N)` on the hyperfinite torus `ℤ/Nℤ`. -/
noncomputable abbrev e (x : ZMod N) : ℂ := ZMod.stdAddChar x

theorem norm_e (x : ZMod N) : ‖e x‖ = 1 := by
  unfold e; rw [ZMod.stdAddChar_apply]; exact Circle.norm_coe _

theorem conj_e (x : ZMod N) : conj (e x) = e (-x) := by
  have h := norm_e x
  unfold e at h ⊢
  rw [AddChar.map_neg_eq_inv, Complex.inv_eq_conj h]

theorem e_mul_conj (x : ZMod N) : e x * conj (e x) = 1 := by
  rw [conj_e]; unfold e; rw [← AddChar.map_add_eq_mul]; simp

/-- Orthogonality of characters on the torus. -/
theorem sum_e_mul (b : ZMod N) :
    ∑ x : ZMod N, e (x * b) = if b = 0 then (N : ℂ) else 0 := by
  have := AddChar.sum_mulShift (ψ := (ZMod.stdAddChar : AddChar (ZMod N) ℂ)) b
    (ZMod.isPrimitive_stdAddChar N)
  rw [this, ZMod.card]; split_ifs <;> simp

/-- Exact Fourier inversion on the hyperfinite torus. -/
theorem dft_inversion (Φ : ZMod N → ℂ) (j : ZMod N) :
    Φ j = (N : ℂ)⁻¹ * ∑ k : ZMod N, e (j * k) * ZMod.dft Φ k := by
  have h := congrFun (ZMod.dft.symm_apply_apply Φ) j
  rw [ZMod.invDFT_apply] at h
  calc Φ j = _ := h.symm
    _ = _ := by
      simp only [smul_eq_mul]; congr 1; apply Finset.sum_congr rfl; intro k _
      rw [mul_comm j k]

/-- Exact Parseval–Plancherel identity (complex form). -/
theorem parseval_complex (Φ : ZMod N → ℂ) :
    ∑ k : ZMod N, ZMod.dft Φ k * conj (ZMod.dft Φ k)
      = (N : ℂ) * ∑ j : ZMod N, Φ j * conj (Φ j) := by
  simp only [ZMod.dft_apply, smul_eq_mul, map_sum, map_mul, conj_e]
  simp_rw [Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro j _
  rw [Finset.sum_comm]
  have hk : ∀ l : ZMod N, ∑ k : ZMod N, e (-(j * k)) * Φ j * (e (-(-(l * k))) * conj (Φ l))
      = (Φ j * conj (Φ l)) * ∑ k : ZMod N, e (k * (l - j)) := by
    intro l; rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro k _
    have : e (k * (l - j)) = e (-(j * k)) * e (-(-(l * k))) := by
      unfold e; rw [← AddChar.map_add_eq_mul]; congr 1; ring
    rw [this]; ring
  simp_rw [hk, sum_e_mul, sub_eq_zero]
  simp [Finset.sum_ite_eq', mul_comm]

/-- Exact Parseval identity in norms: `∑ |Φ̂|² = N ∑ |Φ|²`. -/
theorem parseval (Φ : ZMod N → ℂ) :
    ∑ k : ZMod N, ‖ZMod.dft Φ k‖ ^ 2 = (N : ℝ) * ∑ j : ZMod N, ‖Φ j‖ ^ 2 := by
  have h := parseval_complex Φ
  simp_rw [Complex.mul_conj', ← Complex.ofReal_pow] at h
  rw [← Complex.ofReal_sum, ← Complex.ofReal_sum] at h
  exact_mod_cast h

/-- Cyclic convolution on the torus. -/
def conv (f g : ZMod N → ℂ) (m : ZMod N) : ℂ := ∑ j : ZMod N, f j * g (m - j)

/-- Exact convolution theorem. -/
theorem dft_conv (f g : ZMod N → ℂ) (k : ZMod N) :
    ZMod.dft (conv f g) k = ZMod.dft f k * ZMod.dft g k := by
  simp only [ZMod.dft_apply, smul_eq_mul, conv, Finset.mul_sum, Finset.sum_mul]
  conv_lhs => rw [Finset.sum_comm]
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro j _
  rw [Fintype.sum_equiv (Equiv.addLeft j).symm _
    (fun n => stdAddChar (-((j + n) * k)) * (f j * g n)) (fun m => by simp [sub_eq_neg_add])]
  apply Finset.sum_congr rfl; intro n _
  have : e (-((j + n) * k)) = e (-(j * k)) * e (-(n * k)) := by
    unfold e; rw [← AddChar.map_add_eq_mul]; congr 1; ring
  unfold e at this; rw [this]; ring

/-- Shift theorem: translation by one granule multiplies the spectrum by `e(k)`. -/
theorem dft_shift (Φ : ZMod N → ℂ) (k : ZMod N) :
    ZMod.dft (fun j => Φ (j + 1)) k = e k * ZMod.dft Φ k := by
  simp only [ZMod.dft_apply, smul_eq_mul, Finset.mul_sum]
  rw [Fintype.sum_equiv (Equiv.addRight 1) _
    (fun m => stdAddChar (-((m - 1) * k)) * Φ m) (fun j => by simp)]
  apply Finset.sum_congr rfl; intro m _
  have : e (-((m - 1) * k)) = e k * e (-(m * k)) := by
    unfold e; rw [← AddChar.map_add_eq_mul]; congr 1; ring
  unfold e at this; rw [this]; ring

/-- The forward granular difference is an exact Fourier multiplier:
`𝓕(Φ(·+1) - Φ)(k) = (e(k) - 1) 𝓕Φ(k)`; dividing by `2ε` gives the symbol of `D⁺_ε`. -/
theorem dft_forward_diff (Φ : ZMod N → ℂ) (k : ZMod N) :
    ZMod.dft (fun j => Φ (j + 1) - Φ j) k = (e k - 1) * ZMod.dft Φ k := by
  have h : (fun j => Φ (j + 1) - Φ j) = (fun j => Φ (j + 1)) - Φ := rfl
  rw [h, map_sub, Pi.sub_apply, dft_shift]; ring

theorem norm_dft_le (Φ : ZMod N → ℂ) (k : ZMod N) :
    ‖ZMod.dft Φ k‖ ≤ ∑ j : ZMod N, ‖Φ j‖ := by
  rw [ZMod.dft_apply]
  calc ‖∑ j : ZMod N, ZMod.stdAddChar (-(j * k)) • Φ j‖
      ≤ ∑ j : ZMod N, ‖ZMod.stdAddChar (-(j * k)) • Φ j‖ := norm_sum_le _ _
    _ = ∑ j : ZMod N, ‖Φ j‖ := by
        apply Finset.sum_congr rfl; intro j _
        rw [norm_smul]; have := norm_e (N := N) (-(j * k)); unfold e at this
        rw [this, one_mul]

/-- Exact decay bound ("integration by parts"): `|e(k) - 1| · |Φ̂(k)| ≤ ∑ |Φ(j+1) - Φ(j)|`,
the total variation of `Φ`. -/
theorem dft_decay (Φ : ZMod N → ℂ) (k : ZMod N) :
    ‖e k - 1‖ * ‖ZMod.dft Φ k‖ ≤ ∑ j : ZMod N, ‖Φ (j + 1) - Φ j‖ := by
  rw [← norm_mul, ← dft_forward_diff]
  exact norm_dft_le _ k

/-- Exact aliasing: sampling the trigonometric polynomial `∑_{n∈F} c_n e^{iξ_n x}` on the
torus gives the transform `N ∑_{n ≡ k (mod N)} c_n`. -/
theorem aliasing (F : Finset ℤ) (c : ℤ → ℂ) (k : ZMod N) :
    ZMod.dft (fun j : ZMod N => ∑ n ∈ F, c n * e (j * (n : ZMod N))) k
      = (N : ℂ) * ∑ n ∈ F.filter (fun n : ℤ => (n : ZMod N) = k), c n := by
  simp only [ZMod.dft_apply, smul_eq_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  have : ∀ n ∈ F, ∑ j : ZMod N, stdAddChar (-(j * k)) * (c n * e (j * (n : ZMod N)))
      = c n * (if (n : ZMod N) - k = 0 then (N : ℂ) else 0) := by
    intro n _
    rw [← sum_e_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl; intro j _
    have : e (j * ((n : ZMod N) - k)) = e (-(j * k)) * e (j * (n : ZMod N)) := by
      unfold e; rw [← AddChar.map_add_eq_mul]; congr 1; ring
    unfold e at this ⊢; rw [this]; ring
  rw [Finset.sum_congr rfl this, Finset.sum_filter]
  apply Finset.sum_congr rfl; intro n _
  simp only [sub_eq_zero]
  split_ifs <;> ring

/-- Geometric sum of the character along the multiples of `L`. -/
theorem sum_e_multiples (L M : ℕ) (hN : N = L * M) (j : ZMod N) :
    ∑ s ∈ Finset.range M, e (-(j * ((L * s : ℕ) : ZMod N)))
      = if (L : ZMod N) * j = 0 then (M : ℂ) else 0 := by
  set ζ : ℂ := e (-(j * (L : ZMod N))) with hζ
  have hpow : ∀ s : ℕ, e (-(j * ((L * s : ℕ) : ZMod N))) = ζ ^ s := by
    intro s
    rw [hζ]; unfold e; rw [← AddChar.map_nsmul_eq_pow]; congr 1
    push_cast; rw [nsmul_eq_mul]; ring
  simp_rw [hpow]
  split_ifs with h
  · have : ζ = 1 := by
      rw [hζ]; unfold e
      have : -(j * (L : ZMod N)) = 0 := by rw [mul_comm, h, neg_zero]
      rw [this, AddChar.map_zero_eq_one]
    simp [this]
  · have hne : ζ ≠ 1 := by
      rw [hζ]; unfold e
      intro h1
      rw [← AddChar.map_zero_eq_one (ZMod.stdAddChar (N := N))] at h1
      have := ZMod.injective_stdAddChar h1
      apply h; rw [mul_comm]; exact neg_eq_zero.mp this
    have hM : ζ ^ M = 1 := by
      rw [hζ]; unfold e; rw [← AddChar.map_nsmul_eq_pow, nsmul_eq_mul]
      have : (M : ZMod N) * -(j * (L : ZMod N)) = -(j * ((L * M : ℕ) : ZMod N)) := by
        push_cast; ring
      rw [this, ← hN, ZMod.natCast_self]; simp
    rw [geom_sum_eq hne, hM]; simp

/-- Exact finite Poisson summation: for `N = L M`, the sum of `Φ` over the `L`-torsion
subgroup (the multiples of `M`) equals `1/M` times the sum of `Φ̂` over the multiples
of `L`. -/
theorem poisson (L M : ℕ) (hN : N = L * M) (hM : M ≠ 0) (Φ : ZMod N → ℂ) :
    ∑ j ∈ Finset.univ.filter (fun j : ZMod N => (L : ZMod N) * j = 0), Φ j
      = (M : ℂ)⁻¹ * ∑ s ∈ Finset.range M, ZMod.dft Φ ((L * s : ℕ) : ZMod N) := by
  simp only [ZMod.dft_apply, smul_eq_mul]
  rw [Finset.sum_comm]
  have : ∀ j : ZMod N, ∑ s ∈ Finset.range M, e (-(j * ((L * s : ℕ) : ZMod N))) * Φ j
      = (if (L : ZMod N) * j = 0 then (M : ℂ) else 0) * Φ j := by
    intro j; rw [← Finset.sum_mul, sum_e_multiples L M hN j]
  unfold e at this
  simp_rw [this, ite_mul, zero_mul]
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, ← Finset.mul_sum, ← mul_assoc,
    inv_mul_cancel₀ (by exact_mod_cast hM), one_mul]

/-- Support of a function on the torus. -/
noncomputable def supp (Φ : ZMod N → ℂ) : Finset (ZMod N) :=
  Finset.univ.filter (fun j => Φ j ≠ 0)

theorem norm_dft_sq_le (Φ : ZMod N → ℂ) (k : ZMod N) :
    ‖ZMod.dft Φ k‖ ^ 2 ≤ (supp Φ).card * ∑ j : ZMod N, ‖Φ j‖ ^ 2 := by
  have h1 : ‖ZMod.dft Φ k‖ ≤ ∑ j ∈ supp Φ, ‖Φ j‖ := by
    rw [ZMod.dft_apply]
    calc ‖∑ j : ZMod N, ZMod.stdAddChar (-(j * k)) • Φ j‖
        ≤ ∑ j : ZMod N, ‖ZMod.stdAddChar (-(j * k)) • Φ j‖ := norm_sum_le _ _
      _ = ∑ j : ZMod N, ‖Φ j‖ := by
          apply Finset.sum_congr rfl; intro j _
          rw [norm_smul]; have := norm_e (N := N) (-(j * k)); unfold e at this
          rw [this, one_mul]
      _ = ∑ j ∈ supp Φ, ‖Φ j‖ := by
          unfold supp; rw [Finset.sum_filter]; apply Finset.sum_congr rfl; intro j _
          split_ifs with h
          · rfl
          · push Not at h; simp [h]
  have h2 : (∑ j ∈ supp Φ, ‖Φ j‖) ^ 2 ≤ (supp Φ).card * ∑ j ∈ supp Φ, ‖Φ j‖ ^ 2 :=
    sq_sum_le_card_mul_sum_sq
  have h3 : ∑ j ∈ supp Φ, ‖Φ j‖ ^ 2 ≤ ∑ j : ZMod N, ‖Φ j‖ ^ 2 :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun _ _ _ => by positivity)
  calc ‖ZMod.dft Φ k‖ ^ 2 ≤ (∑ j ∈ supp Φ, ‖Φ j‖) ^ 2 := by
        exact pow_le_pow_left₀ (norm_nonneg _) h1 2
    _ ≤ _ := h2
    _ ≤ _ := by gcongr

/-- Donoho–Stark uncertainty principle on the hyperfinite torus:
`|supp Φ| · |supp Φ̂| ≥ N` for every nonzero `Φ`. -/
theorem uncertainty (Φ : ZMod N → ℂ) (hΦ : Φ ≠ 0) :
    (N : ℝ) ≤ (supp Φ).card * (supp (ZMod.dft Φ)).card := by
  set E := ∑ j : ZMod N, ‖Φ j‖ ^ 2 with hE
  have hEpos : 0 < E := by
    obtain ⟨j, hj⟩ : ∃ j, Φ j ≠ 0 := by
      by_contra h; push Not at h; exact hΦ (funext h)
    have : 0 < ‖Φ j‖ ^ 2 := by positivity
    exact lt_of_lt_of_le this
      (Finset.single_le_sum (f := fun j => ‖Φ j‖ ^ 2) (fun _ _ => by positivity)
        (Finset.mem_univ j))
  have hpar := parseval Φ
  have hsum : ∑ k : ZMod N, ‖ZMod.dft Φ k‖ ^ 2
      = ∑ k ∈ supp (ZMod.dft Φ), ‖ZMod.dft Φ k‖ ^ 2 := by
    unfold supp; rw [Finset.sum_filter]; apply Finset.sum_congr rfl; intro k _
    split_ifs with h
    · rfl
    · push Not at h; simp [h]
  have hbound : ∑ k ∈ supp (ZMod.dft Φ), ‖ZMod.dft Φ k‖ ^ 2
      ≤ (supp (ZMod.dft Φ)).card * ((supp Φ).card * E) := by
    have := Finset.sum_le_card_nsmul (supp (ZMod.dft Φ)) (fun k => ‖ZMod.dft Φ k‖ ^ 2)
      ((supp Φ).card * E) (fun k _ => norm_dft_sq_le Φ k)
    simpa [nsmul_eq_mul] using this
  have : (N : ℝ) * E ≤ ((supp Φ).card * (supp (ZMod.dft Φ)).card) * E := by
    rw [← hpar, hsum]; nlinarith [hbound]
  exact le_of_mul_le_mul_right this hEpos

/-- The granular Fourier coefficient of `δ` is flat: `𝓕 δ_0 ≡ 1`. -/
theorem dft_delta (k : ZMod N) :
    ZMod.dft (fun j : ZMod N => if j = 0 then (1 : ℂ) else 0) k = 1 := by
  rw [ZMod.dft_apply]; simp

end DFT

end QE.Analysis

namespace QE.Analysis

open Finset

noncomputable section Pathological
open Classical

/-- Dirichlet's function: `1` on the rationals, `0` elsewhere. -/
def dirichletF (x : ℝ) : ℝ := if ∃ q : ℚ, (q : ℝ) = x then 1 else 0

/-- On the lattice `{k/N}` (all of whose points are rational) the granular integral of
Dirichlet's function over `[0,1)` is exactly `1`. -/
theorem dirichlet_lattice (N : ℕ) (hN : 0 < N) :
    ∑ k ∈ range N, dirichletF ((k : ℝ) / N) * (1 / N) = 1 := by
  have : ∀ k ∈ range N, dirichletF ((k : ℝ) / N) * (1 / N) = 1 / N := by
    intro k _
    unfold dirichletF
    rw [ite_eq_left ⟨(k : ℚ) / N, by push_cast; rfl⟩, one_mul]
  rw [Finset.sum_congr rfl this, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  field_simp

/-- On a lattice shifted by an irrational offset the same integral is exactly `0`. -/
theorem dirichlet_shifted (N : ℕ) (α : ℝ) (hα : Irrational α) :
    ∑ k ∈ range N, dirichletF (α + (k : ℝ) / N) * (1 / N) = 0 := by
  apply Finset.sum_eq_zero
  intro k _
  unfold dirichletF
  rw [ite_eq_right, zero_mul]
  rintro ⟨q, hq⟩
  apply hα
  refine ⟨q - (k : ℚ) / N, ?_⟩
  push_cast; rw [hq]; ring

/-- Thomae's function: `1/q` at `p/q` in lowest terms, `0` at irrationals. -/
def thomae (x : ℝ) : ℝ :=
  if h : ∃ q : ℚ, (q : ℝ) = x then 1 / (Classical.choose h).den else 0

theorem thomae_rat (q : ℚ) : thomae q = 1 / q.den := by
  unfold thomae
  have h : ∃ r : ℚ, (r : ℝ) = q := ⟨q, rfl⟩
  rw [dite_eq_left h]
  have := Classical.choose_spec h
  rw [Rat.cast_injective this]

/-- Thomae's function at the lattice point `k/N` equals `gcd(k,N)/N`. -/
theorem thomae_lattice (N k : ℕ) (hN : 0 < N) :
    thomae ((k : ℝ) / N) = (Nat.gcd k N : ℝ) / N := by
  have hq : ((k : ℝ) / N) = (((mkRat (k : ℤ) N : ℚ)) : ℝ) := by
    rw [Rat.mkRat_eq_div]; push_cast; rfl
  rw [hq, thomae_rat, Rat.den_mkRat, ite_eq_right (by omega)]
  simp only [Int.natAbs_natCast]
  have hg : Nat.gcd N k ∣ N := Nat.gcd_dvd_left N k
  have hgpos : 0 < Nat.gcd N k := Nat.gcd_pos_of_pos_left _ hN
  rw [Nat.cast_div hg (by exact_mod_cast hgpos.ne'), Nat.gcd_comm]
  have : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  have : (Nat.gcd k N : ℝ) ≠ 0 := by
    rw [Nat.gcd_comm]; exact_mod_cast hgpos.ne'
  field_simp

/-- Exact value: the granular integral of Thomae's function over `[0,1)` is
`(1/N²) ∑_{k<N} gcd(k,N)` (Pillai's arithmetical function over `N²`). -/
theorem thomae_integral (N : ℕ) (hN : 0 < N) :
    ∑ k ∈ range N, thomae ((k : ℝ) / N) * (1 / N)
      = (∑ k ∈ range N, (Nat.gcd k N : ℝ)) / (N : ℝ) ^ 2 := by
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl; intro k _
  rw [thomae_lattice N k hN]; ring

theorem sum_gcd_le (N : ℕ) (hN : 0 < N) :
    ∑ k ∈ range N, Nat.gcd k N ≤ N * #N.divisors := by
  -- shift the summation index: the terms `k = 0` and `k = N` coincide
  have hshift : ∑ k ∈ range N, Nat.gcd k N = ∑ k ∈ range N, Nat.gcd (k + 1) N := by
    have h1 := Finset.sum_range_succ (fun k => Nat.gcd k N) N
    have h2 := Finset.sum_range_succ' (fun k => Nat.gcd k N) N
    simp only [Nat.gcd_self, Nat.gcd_zero_left] at h1 h2
    omega
  rw [hshift]
  have hle : ∀ k ∈ range N, Nat.gcd (k + 1) N ≤ ∑ d ∈ N.divisors, if d ∣ k + 1 then d else 0 := by
    intro k _
    have hmem : Nat.gcd (k + 1) N ∈ N.divisors :=
      Nat.mem_divisors.2 ⟨Nat.gcd_dvd_right _ _, hN.ne'⟩
    have := Finset.single_le_sum (f := fun d => if d ∣ k + 1 then d else 0)
      (fun _ _ => Nat.zero_le _) hmem
    simpa [Nat.gcd_dvd_left] using this
  calc ∑ k ∈ range N, Nat.gcd (k + 1) N
      ≤ ∑ k ∈ range N, ∑ d ∈ N.divisors, (if d ∣ k + 1 then d else 0) := Finset.sum_le_sum hle
    _ = ∑ d ∈ N.divisors, ∑ k ∈ range N, (if d ∣ k + 1 then d else 0) := Finset.sum_comm
    _ = ∑ d ∈ N.divisors, d * (N / d) := by
        apply Finset.sum_congr rfl; intro d _
        rw [← Finset.sum_filter, Finset.sum_const, Nat.card_multiples, smul_eq_mul, mul_comm]
    _ = ∑ d ∈ N.divisors, N := by
        apply Finset.sum_congr rfl; intro d hd
        exact Nat.mul_div_cancel' (Nat.dvd_of_mem_divisors hd)
    _ = N * #N.divisors := by rw [Finset.sum_const, smul_eq_mul, mul_comm]

/-- The divisor bound `τ(N) ≤ 2 ⌊√N⌋`. -/
theorem card_divisors_le_two_sqrt (N : ℕ) : #N.divisors ≤ 2 * Nat.sqrt N := by
  set A := N.divisors.filter (fun d => d * d ≤ N)
  set B := N.divisors.filter (fun d => ¬ d * d ≤ N)
  have hsplit : #N.divisors = #A + #B := (Finset.card_filter_add_card_filter_not _).symm
  have hA : #A ≤ Nat.sqrt N := by
    have : A ⊆ Finset.Icc 1 (Nat.sqrt N) := by
      intro d hd
      simp only [A, Finset.mem_filter, Nat.mem_divisors] at hd
      simp only [Finset.mem_Icc]
      exact ⟨Nat.pos_of_dvd_of_pos hd.1.1 (Nat.pos_of_ne_zero hd.1.2), Nat.le_sqrt.2 hd.2⟩
    have := Finset.card_le_card this
    simpa using this
  have hB : #B ≤ #A := by
    refine Finset.card_le_card_of_injOn (fun d => N / d) ?_ ?_
    · intro d hd
      simp only [B, Finset.coe_filter, Set.mem_ofPred_eq, Nat.mem_divisors] at hd
      simp only [A, Finset.coe_filter, Set.mem_ofPred_eq, Nat.mem_divisors]
      obtain ⟨⟨hdN, hN0⟩, hdd⟩ := hd
      refine ⟨⟨Nat.div_dvd_of_dvd hdN, hN0⟩, ?_⟩
      have hdpos : 0 < d := Nat.pos_of_dvd_of_pos hdN (Nat.pos_of_ne_zero hN0)
      have hed : N / d * d = N := Nat.div_mul_cancel hdN
      have hlt : N / d < d := by
        by_contra h; push Not at h
        have := Nat.mul_le_mul_right d h
        rw [hed] at this; exact hdd this
      calc N / d * (N / d) ≤ N / d * d := Nat.mul_le_mul_left _ hlt.le
        _ = N := hed
    · intro d1 hd1 d2 hd2 heq
      simp only [B, Finset.coe_filter, Set.mem_ofPred_eq, Nat.mem_divisors] at hd1 hd2
      simp only at heq
      have h1 := Nat.div_div_self hd1.1.1 hd1.1.2
      have h2 := Nat.div_div_self hd2.1.1 hd2.1.2
      rw [← h1, ← h2, heq]
  omega

/-- The granular integral of Thomae's function is at most `2⌊√N⌋/N`; hence it is
infinitesimal when `N` is infinite, and its shadow is the Riemann value `0`. -/
theorem thomae_integral_le (N : ℕ) (hN : 0 < N) :
    ∑ k ∈ range N, thomae ((k : ℝ) / N) * (1 / N) ≤ 2 * (Nat.sqrt N : ℝ) / N := by
  rw [thomae_integral N hN]
  have h1 : (∑ k ∈ range N, (Nat.gcd k N : ℝ)) ≤ (N : ℝ) * (2 * Nat.sqrt N) := by
    have := sum_gcd_le N hN
    have h2 := card_divisors_le_two_sqrt N
    have : ∑ k ∈ range N, Nat.gcd k N ≤ N * (2 * Nat.sqrt N) :=
      this.trans (Nat.mul_le_mul_left _ h2)
    exact_mod_cast this
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  rw [div_le_div_iff₀ (by positivity) hNpos]
  nlinarith

end Pathological

end QE.Analysis
