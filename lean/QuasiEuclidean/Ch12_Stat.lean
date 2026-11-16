-- SPDX-License-Identifier: MIT
-- Copyright 2026 Metere Industries, Inc. Author: Alfredo Metere.
-- Quasi-Euclidean Granular Geometry. Any derivative work must carry this notice:
--   This work is derivative of the Quasi-Euclidean Granular Geometry book
--   authored by Alfredo Metere. Copyright 2026 Metere Industries, Inc.
--   All rights reserved
-- See LICENSE.md and NOTICE.

import QuasiEuclidean.Basic

/-!
# Chapter 12: Granular statistics

Exact finitary statements behind Chapter 12 of the book.  Everything is
stated over an arbitrary linearly ordered field `K` and an arbitrary `ε`
(usually `ε > 0`); the book's infinitesimal setting is `K := Hyperreal`
and the physical setting is `K := ℝ` with `ε` the instrument resolution.

* granular likelihood of a sample is a genuine probability (sums to one
  over the sample space, bounded by one);
* likelihood ratios and maximum-likelihood estimators do not depend on `ε`;
* factorisation theorem: conditional law given a sufficient statistic;
* Bayes' theorem on a hyperfinite parameter lattice, proper uniform priors,
  the Jeffreys–Lindley spike identity and the Bayes-factor cap;
* the granular Cramér–Rao (Hammersley–Chapman–Robbins) inequality;
* exact Sheppard identities for a uniform granular rounding offset;
* exponential families: mean = derivative of the log-partition function,
  which is shifted by `n log (2ε)` in the granular normalisation.
-/

set_option linter.unusedSectionVars false

namespace QE.Stat

open Finset

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-! ## Likelihood is a probability -/

/-- Granular likelihood of a sample `x : Fin m → ι` of size `m` drawn from a
granular density `f` in dimension `n`: `∏ᵢ f(xᵢ) (2ε)ⁿ`. -/
def likelihood {ι : Type*} {m : ℕ} (n : ℕ) (ε : K) (f : ι → K) (x : Fin m → ι) : K :=
  ∏ i, f (x i) * (2 * ε) ^ n

/-- The granular likelihoods of all samples of size `m` add up to one: the
likelihood is the probability of the observed sample. -/
theorem likelihood_sum_one {ι : Type*} (m n : ℕ) (ε : K) (f : ι → K) (s : Finset ι)
    (hf : ∑ x ∈ s, f x * (2 * ε) ^ n = 1) :
    ∑ x ∈ Fintype.piFinset (fun _ : Fin m => s), likelihood n ε f x = 1 := by
  unfold likelihood
  rw [← Finset.prod_univ_sum (fun _ : Fin m => s) (fun _ y => f y * (2 * ε) ^ n)]
  simp [hf]

/-- A single grain has probability at most one. -/
theorem grain_prob_le_one {ι : Type*} (n : ℕ) (ε : K) (f : ι → K) (s : Finset ι)
    (hf0 : ∀ x ∈ s, 0 ≤ f x) (hε : 0 ≤ ε) (hf : ∑ x ∈ s, f x * (2 * ε) ^ n = 1)
    {x : ι} (hx : x ∈ s) : f x * (2 * ε) ^ n ≤ 1 := by
  rw [← hf]
  exact Finset.single_le_sum (f := fun y => f y * (2 * ε) ^ n)
    (fun y hy => mul_nonneg (hf0 y hy) (pow_nonneg (by linarith) n)) hx

/-- A granular density is bounded by `1/(2ε)ⁿ`. -/
theorem density_le_inv {ι : Type*} (n : ℕ) (ε : K) (f : ι → K) (s : Finset ι)
    (hf0 : ∀ x ∈ s, 0 ≤ f x) (hε : 0 < ε) (hf : ∑ x ∈ s, f x * (2 * ε) ^ n = 1)
    {x : ι} (hx : x ∈ s) : f x ≤ 1 / (2 * ε) ^ n := by
  have h := grain_prob_le_one n ε f s hf0 hε.le hf hx
  have hp : 0 < (2 * ε) ^ n := pow_pos (by linarith) n
  rw [le_div_iff₀ hp]; exact h

/-- No versions: a granular density is determined at every grain by the
probabilities it assigns (contrast: a Lebesgue density is only an a.e. class). -/
theorem density_unique {ι : Type*} [DecidableEq ι] (n : ℕ) (ε : K) (hε : 0 < ε)
    (f g : ι → K) (s : Finset ι)
    (h : ∀ A ⊆ s, ∑ x ∈ A, f x * (2 * ε) ^ n = ∑ x ∈ A, g x * (2 * ε) ^ n) :
    ∀ x ∈ s, f x = g x := by
  intro x hx
  have := h {x} (Finset.singleton_subset_iff.mpr hx)
  simp only [Finset.sum_singleton] at this
  have hp : (2 * ε) ^ n ≠ 0 := pow_ne_zero _ (by linarith)
  exact mul_right_cancel₀ hp this

/-- The granular likelihood of a sample is at most one. -/
theorem likelihood_le_one {ι : Type*} (m n : ℕ) (ε : K) (f : ι → K) (s : Finset ι)
    (hf0 : ∀ x ∈ s, 0 ≤ f x) (hε : 0 ≤ ε) (hf : ∑ x ∈ s, f x * (2 * ε) ^ n = 1)
    (x : Fin m → ι) (hx : ∀ i, x i ∈ s) : likelihood n ε f x ≤ 1 := by
  unfold likelihood
  apply Finset.prod_le_one₀
  · intro i _; exact mul_nonneg (hf0 _ (hx i)) (pow_nonneg (by linarith) n)
  · intro i _; exact grain_prob_le_one n ε f s hf0 hε hf (hx i)

/-- The granular likelihood is the classical density product times `(2ε)^{nm}`. -/
theorem likelihood_eq {ι : Type*} (m n : ℕ) (ε : K) (f : ι → K) (x : Fin m → ι) :
    likelihood n ε f x = (2 * ε) ^ (n * m) * ∏ i, f (x i) := by
  unfold likelihood
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
    ← pow_mul, mul_comm]

/-- Likelihood ratios are free of `ε`. -/
theorem likelihood_ratio {ι : Type*} (m n : ℕ) (ε : K) (hε : ε ≠ 0) (f g : ι → K)
    (x : Fin m → ι) :
    likelihood n ε f x / likelihood n ε g x = (∏ i, f (x i)) / ∏ i, g (x i) := by
  rw [likelihood_eq, likelihood_eq]
  have h : (2 * ε) ^ (n * m) ≠ 0 := pow_ne_zero _ (mul_ne_zero two_ne_zero hε)
  rw [mul_div_mul_left _ _ h]

/-- On a hyperfinite (finite) parameter lattice the maximum-likelihood estimator
always exists. -/
theorem mle_exists {Θ : Type*} (P : Finset Θ) (hP : P.Nonempty) (L : Θ → K) :
    ∃ θ ∈ P, ∀ θ' ∈ P, L θ' ≤ L θ :=
  Finset.exists_max_image P L hP

/-- Maximisers are unchanged by a positive factor such as `(2ε)^{nm}`: the
granular MLE coincides with the density-product MLE. -/
theorem argmax_scale {Θ : Type*} (P : Finset Θ) (L : Θ → K) (c : K) (hc : 0 < c) (θ : Θ) :
    (∀ θ' ∈ P, c * L θ' ≤ c * L θ) ↔ (∀ θ' ∈ P, L θ' ≤ L θ) := by
  constructor
  · intro h θ' h'; exact le_of_mul_le_mul_left (h θ' h') hc
  · intro h θ' h'; exact mul_le_mul_of_nonneg_left (h θ' h') hc.le

/-! ## Testing -/

/-- Neyman–Pearson lemma on a finite (hyperfinite) sample space: a likelihood
ratio test `φs` (reject when `p₁ > k p₀`, accept when `p₁ < k p₀`, anything on
the boundary) is at least as powerful as any test `φ` of no larger size. -/
theorem neyman_pearson {ι : Type*} (s : Finset ι) (p0 p1 φ φs : ι → K) (k : K) (hk : 0 ≤ k)
    (hφ : ∀ i ∈ s, 0 ≤ φ i ∧ φ i ≤ 1)
    (h1 : ∀ i ∈ s, k * p0 i < p1 i → φs i = 1) (h0 : ∀ i ∈ s, p1 i < k * p0 i → φs i = 0)
    (hsize : ∑ i ∈ s, φ i * p0 i ≤ ∑ i ∈ s, φs i * p0 i) :
    ∑ i ∈ s, φ i * p1 i ≤ ∑ i ∈ s, φs i * p1 i := by
  have key : 0 ≤ ∑ i ∈ s, (φs i - φ i) * (p1 i - k * p0 i) := by
    apply Finset.sum_nonneg
    intro i hi
    obtain ⟨ha, hb⟩ := hφ i hi
    rcases lt_trichotomy (k * p0 i) (p1 i) with h | h | h
    · rw [h1 i hi h]; exact mul_nonneg (by linarith) (by linarith)
    · rw [h, sub_self, mul_zero]
    · rw [h0 i hi h]; exact mul_nonneg_of_nonpos_of_nonpos (by linarith) (by linarith)
  have e : ∑ i ∈ s, (φs i - φ i) * (p1 i - k * p0 i)
      = (∑ i ∈ s, φs i * p1 i - ∑ i ∈ s, φ i * p1 i)
        - k * (∑ i ∈ s, φs i * p0 i - ∑ i ∈ s, φ i * p0 i) := by
    rw [mul_sub, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib,
      ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl; intro i _; ring
  rw [e] at key
  have : 0 ≤ k * (∑ i ∈ s, φs i * p0 i - ∑ i ∈ s, φ i * p0 i) :=
    mul_nonneg hk (by linarith)
  linarith

/-- Closed and open tails differ by the mass of the observed grain:
`P(T ≥ t) = P(T > t) + P(T = t)`. -/
theorem tail_split {α : Type*} [LinearOrder α] (s : Finset α) (p : α → K) (t : α) :
    ∑ u ∈ s.filter (fun u => t ≤ u), p u
      = ∑ u ∈ s.filter (fun u => t < u), p u + ∑ u ∈ s.filter (fun u => u = t), p u := by
  rw [← Finset.sum_union]
  · apply Finset.sum_congr
    · ext u; simp only [Finset.mem_filter, Finset.mem_union]
      constructor
      · rintro ⟨hu, h⟩
        rcases lt_or_eq_of_le h with h | h
        · exact Or.inl ⟨hu, h⟩
        · exact Or.inr ⟨hu, h.symm⟩
      · rintro (⟨hu, h⟩ | ⟨hu, h⟩)
        · exact ⟨hu, h.le⟩
        · exact ⟨hu, h.ge⟩
    · intro _ _; rfl
  · rw [Finset.disjoint_filter]
    intro u _ h h'; rw [h'] at h; exact lt_irrefl _ h

/-- The mid-`p`-value `P(T > t) + P(T = t)/2` has mean exactly `1/2` (times the
squared total mass), for every law on a finite ordered set. -/
theorem midp_mean {α : Type*} [LinearOrder α] (s : Finset α) (p : α → K) :
    ∑ t ∈ s, p t * (∑ u ∈ s.filter (fun u => t < u), p u + p t / 2)
      = (∑ t ∈ s, p t) ^ 2 / 2 := by
  set A := ∑ t ∈ s, ∑ u ∈ s, p t * (if t < u then p u else 0) with hA
  have hB : ∑ t ∈ s, ∑ u ∈ s, p t * (if u < t then p u else 0) = A := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro t _
    apply Finset.sum_congr rfl; intro u _
    split_ifs <;> ring
  have hsq : (∑ t ∈ s, p t) ^ 2
      = A + ∑ t ∈ s, ∑ u ∈ s, p t * (if u < t then p u else 0) + ∑ t ∈ s, p t * p t := by
    rw [hA, sq, Finset.sum_mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl; intro t ht
    have : ∀ u ∈ s, p t * p u = p t * (if t < u then p u else 0)
        + p t * (if u < t then p u else 0) + (if t = u then p t * p u else 0) := by
      intro u _
      rcases lt_trichotomy t u with h | h | h
      · simp [h, not_lt_of_gt h, ne_of_lt h]
      · simp [h]
      · simp [h, not_lt_of_gt h, ne_of_gt h]
    rw [Finset.sum_congr rfl this, Finset.sum_add_distrib, Finset.sum_add_distrib,
      Finset.sum_ite_eq s t (fun u => p t * p u), ite_eq_left_iff.mpr (fun h => absurd ht h)]
  rw [hB] at hsq
  have hL : ∑ t ∈ s, p t * (∑ u ∈ s.filter (fun u => t < u), p u + p t / 2)
      = A + (∑ t ∈ s, p t * p t) / 2 := by
    rw [hA, Finset.sum_div, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl; intro t _
    rw [Finset.sum_filter, mul_add, Finset.mul_sum]
    ring
  rw [hL, hsq]; ring

/-! ## Sufficiency -/

/-- Fisher–Neyman factorisation, granular form: if `p_θ(x) = g_θ(T x) h(x)`,
the conditional probability of `x` given `T = t` (a non-null event) does not
depend on `θ`. -/
theorem factorization_conditional {ι τ : Type*} [DecidableEq τ] (s : Finset ι) (T : ι → τ)
    (g : τ → K) (h : ι → K) (x : ι) (t : τ) (hx : T x = t) (hg : g t ≠ 0) :
    (g (T x) * h x) / ∑ y ∈ s.filter (fun y => T y = t), g (T y) * h y
      = h x / ∑ y ∈ s.filter (fun y => T y = t), h y := by
  have hs : ∑ y ∈ s.filter (fun y => T y = t), g (T y) * h y
      = g t * ∑ y ∈ s.filter (fun y => T y = t), h y := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro y hy
    rw [(Finset.mem_filter.mp hy).2]
  rw [hs, hx, mul_div_mul_left _ _ hg]

/-! ## Bayes on the lattice -/

/-- Posterior probability of `θ` for prior `π` and likelihood `L` on the
parameter lattice `P`. -/
def posterior {Θ : Type*} (P : Finset Θ) (π L : Θ → K) (θ : Θ) : K :=
  π θ * L θ / ∑ θ' ∈ P, π θ' * L θ'

theorem posterior_sum_one {Θ : Type*} (P : Finset Θ) (π L : Θ → K)
    (h : ∑ θ' ∈ P, π θ' * L θ' ≠ 0) : ∑ θ ∈ P, posterior P π L θ = 1 := by
  unfold posterior
  rw [← Finset.sum_div, div_self h]

/-- A constant prior on a hyperfinite lattice is proper, and its posterior is the
normalised likelihood, whatever the constant. -/
theorem posterior_uniform {Θ : Type*} (P : Finset Θ) (L : Θ → K) (c : K) (hc : c ≠ 0)
    (θ : Θ) : posterior P (fun _ => c) L θ = L θ / ∑ θ' ∈ P, L θ' := by
  unfold posterior
  rw [← Finset.mul_sum, mul_div_mul_left _ _ hc]

/-- The uniform prior on a finite lattice sums to one. -/
theorem uniform_prior_sum_one {Θ : Type*} (P : Finset Θ) (hP : P.Nonempty) :
    ∑ _θ ∈ P, (1 : K) / P.card = 1 := by
  rw [Finset.sum_const, nsmul_eq_mul]
  have : (P.card : K) ≠ 0 := by exact_mod_cast (Finset.card_pos.mpr hP).ne'
  field_simp

/-- Mass of one grain under the uniform prior on `[-Ω, Ω] ∩ 2εℤ`, `Ω = 2εN`:
it is `2ε/(2Ω+2ε)`, the granular measure of the point over that of the box. -/
theorem uniform_point_mass (ε : K) (hε : 0 < ε) (N : ℕ) :
    (1 : K) / ((Finset.Icc (-(N : ℤ)) N).card : K) = 2 * ε / (2 * (2 * ε * N) + 2 * ε) := by
  rw [Int.card_Icc]
  have hc : (((N + 1 - -(N : ℤ)).toNat : ℕ) : K) = 2 * N + 1 := by
    rw [← Int.cast_natCast, Int.toNat_of_nonneg (by omega)]; push_cast; ring
  rw [hc]
  have h1 : (2 * (N : K) + 1) ≠ 0 := by positivity
  field_simp

/-- Posterior odds = prior odds × likelihood ratio, exactly. -/
theorem posterior_odds {Θ : Type*} (P : Finset Θ) (π L : Θ → K) (a b : Θ)
    (h : ∑ θ' ∈ P, π θ' * L θ' ≠ 0) :
    posterior P π L a / posterior P π L b = (π a / π b) * (L a / L b) := by
  unfold posterior
  rw [div_div_div_cancel_right₀ h, mul_div_mul_comm]

/-- Jeffreys–Lindley spike identity.  `L0` is the likelihood of the null grain,
`S` the summed likelihood of the `M` alternative grains.  The spike-and-slab
Bayes factor `L0 / (S/M)` equals `M` times the posterior odds of the single
null grain under the uniform (diffuse) prior on all `M + 1` grains. -/
theorem spike_identity (L0 S M : K) (hS : S ≠ 0) (hT : L0 + S ≠ 0) (hM : M ≠ 0) :
    L0 / (S / M) = M * ((L0 / (L0 + S)) / (1 - L0 / (L0 + S))) := by
  have h1 : 1 - L0 / (L0 + S) = S / (L0 + S) := by field_simp; ring
  rw [h1]
  field_simp

/-- The Bayes factor of a point null against a uniform alternative on `M` grains
is capped by `M` times the likelihood ratio against any single alternative grain. -/
theorem bayes_factor_le {Θ : Type*} (A : Finset Θ) (L : Θ → K) (L0 M : K)
    (hL : ∀ θ ∈ A, 0 ≤ L θ) (hL0 : 0 ≤ L0) (hM : 0 < M) {j : Θ} (hj : j ∈ A)
    (hLj : 0 < L j) :
    L0 / ((∑ θ ∈ A, L θ) / M) ≤ M * L0 / L j := by
  have hS : L j ≤ ∑ θ ∈ A, L θ := Finset.single_le_sum hL hj
  have hSpos : 0 < ∑ θ ∈ A, L θ := lt_of_lt_of_le hLj hS
  rw [div_div_eq_mul_div, mul_comm L0 M]
  exact div_le_div_of_nonneg_left (mul_nonneg hM.le hL0) hLj hS

/-! ## Granular Cramér–Rao -/

/-- Hammersley–Chapman–Robbins inequality on a finite space: `p` and `q` are
the laws at `θ` and at the neighbouring grain `θ + 2ε`, `T` any statistic. -/
theorem hcr_bound {ι : Type*} (s : Finset ι) (p q T : ι → K) (hp : ∀ i ∈ s, 0 < p i)
    (hps : ∑ i ∈ s, p i = 1) (hqs : ∑ i ∈ s, q i = 1) :
    (∑ i ∈ s, q i * T i - ∑ i ∈ s, p i * T i) ^ 2 ≤
      (∑ i ∈ s, p i * (T i - ∑ j ∈ s, p j * T j) ^ 2) *
      (∑ i ∈ s, p i * (q i / p i - 1) ^ 2) := by
  set m := ∑ j ∈ s, p j * T j with hm
  have key : ∑ i ∈ s, q i * T i - m
      = ∑ i ∈ s, p i * (T i - m) * (q i / p i - 1) := by
    have e : ∀ i ∈ s, p i * (T i - m) * (q i / p i - 1)
        = q i * T i - p i * T i - (m * q i - m * p i) := by
      intro i hi
      have := (hp i hi).ne'
      field_simp
    rw [Finset.sum_congr rfl e, Finset.sum_sub_distrib, Finset.sum_sub_distrib,
      Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum, hps, hqs]
    ring
  rw [key]
  set A := ∑ i ∈ s, p i * (T i - m) ^ 2
  set B := ∑ i ∈ s, p i * (q i / p i - 1) ^ 2
  set C := ∑ i ∈ s, p i * (T i - m) * (q i / p i - 1)
  have hq : ∀ t : K, 0 ≤ A * (t * t) + (-2 * C) * t + B := by
    intro t
    have e : A * (t * t) + (-2 * C) * t + B
        = ∑ i ∈ s, p i * ((T i - m) * t - (q i / p i - 1)) ^ 2 := by
      simp only [A, B, C, Finset.sum_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl; intro i _; ring
    rw [e]
    exact Finset.sum_nonneg (fun i hi => mul_nonneg (hp i hi).le (sq_nonneg _))
  have hd := discrim_le_zero hq
  unfold discrim at hd
  nlinarith [hd]

/-- Granular Fisher information at `θ` in the direction of the next grain. -/
def fisherG {ι : Type*} (s : Finset ι) (ε : K) (p q : ι → K) : K :=
  ∑ i ∈ s, p i * ((q i / p i - 1) / (2 * ε)) ^ 2

/-- The granular score `(p_{θ+2ε}/p_θ - 1)/(2ε)` has mean exactly zero. -/
theorem score_mean_zero {ι : Type*} (s : Finset ι) (ε : K) (p q : ι → K)
    (hp : ∀ i ∈ s, 0 < p i) (hps : ∑ i ∈ s, p i = 1) (hqs : ∑ i ∈ s, q i = 1) :
    ∑ i ∈ s, p i * ((q i / p i - 1) / (2 * ε)) = 0 := by
  have e : ∀ i ∈ s, p i * ((q i / p i - 1) / (2 * ε)) = (q i - p i) / (2 * ε) := by
    intro i hi
    have := (hp i hi).ne'
    field_simp
  rw [Finset.sum_congr rfl e, ← Finset.sum_div, Finset.sum_sub_distrib, hps, hqs, sub_self,
    zero_div]

/-- Tensorisation of the chi-square: for `m` independent observations,
`E[(q^{⊗m}/p^{⊗m})²] = (E[(q/p)²])^m`; equivalently
`1 + (2ε)² I_ε^{(m)} = (1 + (2ε)² I_ε)^m`. -/
theorem chi2_tensor {ι : Type*} (s : Finset ι) (p q : ι → K) (m : ℕ) :
    ∑ x ∈ Fintype.piFinset (fun _ : Fin m => s),
        (∏ i, p (x i)) * ((∏ i, q (x i)) / ∏ i, p (x i)) ^ 2
      = (∑ y ∈ s, p y * (q y / p y) ^ 2) ^ m := by
  have e : ∀ x ∈ Fintype.piFinset (fun _ : Fin m => s),
      (∏ i, p (x i)) * ((∏ i, q (x i)) / ∏ i, p (x i)) ^ 2
        = ∏ i, (p (x i) * (q (x i) / p (x i)) ^ 2) := by
    intro x _
    rw [← Finset.prod_div_distrib, ← Finset.prod_pow, ← Finset.prod_mul_distrib]
  rw [Finset.sum_congr rfl e, ← Finset.prod_univ_sum (fun _ : Fin m => s)
    (fun _ y => p y * (q y / p y) ^ 2)]
  simp

/-- Granular Cramér–Rao inequality: `(D⁺ E_θ T)² ≤ Var_θ T · I_ε(θ)`. -/
theorem granular_cramer_rao {ι : Type*} (s : Finset ι) (ε : K) (hε : 0 < ε)
    (p q T : ι → K) (hp : ∀ i ∈ s, 0 < p i)
    (hps : ∑ i ∈ s, p i = 1) (hqs : ∑ i ∈ s, q i = 1) :
    ((∑ i ∈ s, q i * T i - ∑ i ∈ s, p i * T i) / (2 * ε)) ^ 2 ≤
      (∑ i ∈ s, p i * (T i - ∑ j ∈ s, p j * T j) ^ 2) * fisherG s ε p q := by
  have h := hcr_bound s p q T hp hps hqs
  have hpos : 0 < (2 * ε) ^ 2 := by positivity
  have hF : fisherG s ε p q = (∑ i ∈ s, p i * (q i / p i - 1) ^ 2) / (2 * ε) ^ 2 := by
    unfold fisherG
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl; intro i _; rw [div_pow]; ring
  rw [hF, div_pow, mul_div_assoc']
  exact div_le_div_of_nonneg_right h hpos.le

/-- Unbiased version: if `E_{θ+2ε} T - E_θ T = 2ε` then `Var_θ T · I_ε(θ) ≥ 1`. -/
theorem granular_cramer_rao_unbiased {ι : Type*} (s : Finset ι) (ε : K) (hε : 0 < ε)
    (p q T : ι → K) (hp : ∀ i ∈ s, 0 < p i)
    (hps : ∑ i ∈ s, p i = 1) (hqs : ∑ i ∈ s, q i = 1)
    (hub : ∑ i ∈ s, q i * T i - ∑ i ∈ s, p i * T i = 2 * ε) :
    1 ≤ (∑ i ∈ s, p i * (T i - ∑ j ∈ s, p j * T j) ^ 2) * fisherG s ε p q := by
  have h := granular_cramer_rao s ε hε p q T hp hps hqs
  rw [hub, div_self (by positivity), one_pow] at h
  exact h

/-- Two-sided exact bound for the granular Fisher information of the lattice
Gaussian location family, `I_ε = (exp(h²/σ²) - 1)/h²` with `h = 2ε`:
`1/σ² ≤ I_ε ≤ exp(h²/σ²)/σ²`.  Its shadow is the classical `1/σ²`. -/
theorem gaussian_fisher_bounds (h σ : ℝ) (hh : 0 < h) (hσ : 0 < σ) :
    1 / σ ^ 2 ≤ (Real.exp (h ^ 2 / σ ^ 2) - 1) / h ^ 2 ∧
      (Real.exp (h ^ 2 / σ ^ 2) - 1) / h ^ 2 ≤ Real.exp (h ^ 2 / σ ^ 2) / σ ^ 2 := by
  set u := h ^ 2 / σ ^ 2 with hu
  have hh2 : 0 < h ^ 2 := by positivity
  have hσ2 : 0 < σ ^ 2 := by positivity
  have hlow : u + 1 ≤ Real.exp u := Real.add_one_le_exp u
  have hup : Real.exp u - 1 ≤ u * Real.exp u := by
    have h1 : -u + 1 ≤ Real.exp (-u) := Real.add_one_le_exp (-u)
    have h2 : Real.exp (-u) * Real.exp u = 1 := by rw [← Real.exp_add]; simp
    have h3 : 0 < Real.exp u := Real.exp_pos u
    nlinarith
  have hus : u * σ ^ 2 = h ^ 2 := by rw [hu]; field_simp
  constructor
  · rw [div_le_div_iff₀ hσ2 hh2]; nlinarith
  · rw [div_le_div_iff₀ hh2 hσ2]
    have := mul_le_mul_of_nonneg_right hup hσ2.le
    have e : u * Real.exp u * σ ^ 2 = Real.exp u * h ^ 2 := by rw [← hus]; ring
    linarith

/-! ## Sheppard's corrections, exactly -/

lemma pow1_gen (c : K) (m : ℕ) :
    ∑ j ∈ range m, (2 * (j : K) - c) = m * ((m : K) - 1) - m * c := by
  induction m with
  | zero => simp
  | succ n ih => rw [sum_range_succ, ih]; push_cast; ring

lemma pow2_gen (c : K) (m : ℕ) :
    ∑ j ∈ range m, (2 * (j : K) - c) ^ 2
      = 2 / 3 * m * ((m : K) - 1) * (2 * m - 1) - 2 * c * m * ((m : K) - 1) + m * c ^ 2 := by
  induction m with
  | zero => simp
  | succ n ih => rw [sum_range_succ, ih]; push_cast; ring

lemma pow3_gen (c : K) (m : ℕ) :
    ∑ j ∈ range m, (2 * (j : K) - c) ^ 3
      = 2 * (m : K) ^ 2 * ((m : K) - 1) ^ 2 - 2 * c * m * ((m : K) - 1) * (2 * m - 1)
        + 3 * c ^ 2 * m * ((m : K) - 1) - m * c ^ 3 := by
  induction m with
  | zero => simp
  | succ n ih => rw [sum_range_succ, ih]; push_cast; ring

lemma pow4_gen (c : K) (m : ℕ) :
    ∑ j ∈ range m, (2 * (j : K) - c) ^ 4
      = 8 / 15 * m * ((m : K) - 1) * (2 * m - 1) * (3 * (m : K) ^ 2 - 3 * m - 1)
        - 8 * c * (m : K) ^ 2 * ((m : K) - 1) ^ 2
        + 4 * c ^ 2 * m * ((m : K) - 1) * (2 * m - 1)
        - 4 * c ^ 3 * m * ((m : K) - 1) + m * c ^ 4 := by
  induction m with
  | zero => simp
  | succ n ih => rw [sum_range_succ, ih]; push_cast; ring

/-- Offset of the `j`-th grain from the centre of a coarse cell of `m` grains,
in units of `ε`: `2j - (m - 1)`. -/
def off (m j : ℕ) : K := 2 * (j : K) - ((m : K) - 1)

lemma off_sum (m : ℕ) : ∑ j ∈ range m, (off m j : K) = 0 := by
  unfold off; rw [pow1_gen]; ring

lemma off_sum_sq (m : ℕ) :
    ∑ j ∈ range m, (off m j : K) ^ 2 = m * ((m : K) ^ 2 - 1) / 3 := by
  unfold off; rw [pow2_gen]; ring

lemma off_sum_cube (m : ℕ) : ∑ j ∈ range m, (off m j : K) ^ 3 = 0 := by
  unfold off; rw [pow3_gen]; ring

lemma off_sum_four (m : ℕ) :
    ∑ j ∈ range m, (off m j : K) ^ 4
      = m * ((m : K) ^ 2 - 1) * (3 * (m : K) ^ 2 - 7) / 15 := by
  unfold off; rw [pow4_gen]; ring

/-- Expectation of `g(Y + U)` where `Y` has law `p` on `s` and, independently,
`U = ε·off(m,j)` is uniform on the `m` grains of a coarse cell of width `2εm`. -/
def dither {ι : Type*} (s : Finset ι) (p : ι → K) (y : ι → K) (ε : K) (m : ℕ)
    (g : K → K) : K :=
  ∑ x ∈ s, p x * ((1 / (m : K)) * ∑ j ∈ range m, g (y x + ε * off m j))

/-- Sheppard, first moment: the uniform granular offset does not move the mean. -/
theorem sheppard_mean {ι : Type*} (s : Finset ι) (p y : ι → K) (ε : K) (m : ℕ) (hm : 0 < m) :
    dither s p y ε m (fun z => z) = ∑ x ∈ s, p x * y x := by
  unfold dither
  apply sum_congr rfl; intro x _
  have hm' : (m : K) ≠ 0 := by exact_mod_cast hm.ne'
  rw [sum_add_distrib, ← mul_sum, off_sum, sum_const, card_range, nsmul_eq_mul, mul_zero,
    add_zero]
  field_simp

/-- Granular Sheppard correction for the second moment: the uniform offset adds
exactly `(h² - (2ε)²)/12`, `h = 2εm` the coarse cell width. -/
theorem sheppard_second {ι : Type*} (s : Finset ι) (p y : ι → K) (ε : K) (m : ℕ) (hm : 0 < m)
    (hp : ∑ x ∈ s, p x = 1) :
    dither s p y ε m (fun z => z ^ 2)
      = ∑ x ∈ s, p x * y x ^ 2 + ((2 * ε * m) ^ 2 - (2 * ε) ^ 2) / 12 := by
  unfold dither
  have hm' : (m : K) ≠ 0 := by exact_mod_cast hm.ne'
  have inner : ∀ x ∈ s, p x * ((1 / (m : K)) * ∑ j ∈ range m, (y x + ε * off m j) ^ 2)
      = p x * y x ^ 2 + p x * (((2 * ε * m) ^ 2 - (2 * ε) ^ 2) / 12) := by
    intro x _
    have e : ∀ j ∈ range m, (y x + ε * off m j) ^ 2
        = y x ^ 2 + (2 * y x * ε) * off m j + ε ^ 2 * (off m j) ^ 2 := by
      intro j _; ring
    rw [sum_congr rfl e, sum_add_distrib, sum_add_distrib, ← mul_sum, ← mul_sum, off_sum,
      off_sum_sq, sum_const, card_range, nsmul_eq_mul]
    field_simp
    ring
  rw [sum_congr rfl inner, sum_add_distrib, ← sum_mul, hp, one_mul]

/-- Granular Sheppard identity for the fourth moment:
`E(Y+U)⁴ = EY⁴ + 6 EY² σ₂ + σ₄` (given `E U = E U³ = 0`, and `EY`-free), with the
exact granular offset moments `σ₂ = ε²(m²-1)/3`, `σ₄ = ε⁴(m²-1)(3m²-7)/15`. -/
theorem sheppard_fourth {ι : Type*} (s : Finset ι) (p y : ι → K) (ε : K) (m : ℕ) (hm : 0 < m)
    (hp : ∑ x ∈ s, p x = 1) :
    dither s p y ε m (fun z => z ^ 4)
      = ∑ x ∈ s, p x * y x ^ 4
        + 6 * (∑ x ∈ s, p x * y x ^ 2) * (ε ^ 2 * ((m : K) ^ 2 - 1) / 3)
        + ε ^ 4 * ((m : K) ^ 2 - 1) * (3 * (m : K) ^ 2 - 7) / 15 := by
  unfold dither
  have hm' : (m : K) ≠ 0 := by exact_mod_cast hm.ne'
  have inner : ∀ x ∈ s, p x * ((1 / (m : K)) * ∑ j ∈ range m, (y x + ε * off m j) ^ 4)
      = p x * y x ^ 4 + 6 * (p x * y x ^ 2) * (ε ^ 2 * ((m : K) ^ 2 - 1) / 3)
        + p x * (ε ^ 4 * ((m : K) ^ 2 - 1) * (3 * (m : K) ^ 2 - 7) / 15) := by
    intro x _
    have e : ∀ j ∈ range m, (y x + ε * off m j) ^ 4
        = y x ^ 4 + (4 * y x ^ 3 * ε) * off m j + (6 * y x ^ 2 * ε ^ 2) * (off m j) ^ 2
          + (4 * y x * ε ^ 3) * (off m j) ^ 3 + ε ^ 4 * (off m j) ^ 4 := by
      intro j _; ring
    rw [sum_congr rfl e, sum_add_distrib, sum_add_distrib, sum_add_distrib, sum_add_distrib,
      ← mul_sum, ← mul_sum, ← mul_sum, ← mul_sum, off_sum, off_sum_sq, off_sum_cube,
      off_sum_four, sum_const, card_range, nsmul_eq_mul]
    field_simp
    ring
  have h2 : ∑ x ∈ s, p x * (ε ^ 4 * ((m : K) ^ 2 - 1) * (3 * (m : K) ^ 2 - 7) / 15)
      = ε ^ 4 * ((m : K) ^ 2 - 1) * (3 * (m : K) ^ 2 - 7) / 15 := by
    rw [← sum_mul, hp, one_mul]
  have h3 : ∑ x ∈ s, 6 * (p x * y x ^ 2) * (ε ^ 2 * ((m : K) ^ 2 - 1) / 3)
      = 6 * (∑ x ∈ s, p x * y x ^ 2) * (ε ^ 2 * ((m : K) ^ 2 - 1) / 3) := by
    rw [← sum_mul, ← mul_sum]
  rw [sum_congr rfl inner, sum_add_distrib, sum_add_distrib, h2, h3]

/-- Granular Sheppard correction for the variance. -/
theorem sheppard_variance {ι : Type*} (s : Finset ι) (p y : ι → K) (ε : K) (m : ℕ)
    (hm : 0 < m) (hp : ∑ x ∈ s, p x = 1) :
    dither s p y ε m (fun z => z ^ 2) - (dither s p y ε m (fun z => z)) ^ 2
      = (∑ x ∈ s, p x * y x ^ 2 - (∑ x ∈ s, p x * y x) ^ 2)
        + ((2 * ε * m) ^ 2 - (2 * ε) ^ 2) / 12 := by
  rw [sheppard_second s p y ε m hm hp, sheppard_mean s p y ε m hm]; ring

/-! ## Exponential families -/

/-- Mean of the sufficient statistic = derivative of the log-partition function
`A(θ) = log ∑ h(x) e^{θ T(x)}`. -/
theorem expfam_mean {ι : Type*} (s : Finset ι) (h T : ι → ℝ) (hh : ∀ x ∈ s, 0 < h x)
    (hs : s.Nonempty) (θ : ℝ) :
    HasDerivAt (fun θ => Real.log (∑ x ∈ s, h x * Real.exp (θ * T x)))
      ((∑ x ∈ s, h x * (Real.exp (θ * T x) * T x)) / ∑ x ∈ s, h x * Real.exp (θ * T x)) θ := by
  have hZ : HasDerivAt (fun θ => ∑ x ∈ s, h x * Real.exp (θ * T x))
      (∑ x ∈ s, h x * (Real.exp (θ * T x) * T x)) θ :=
    HasDerivAt.fun_sum (fun x _ => ((hasDerivAt_mul_const (T x)).exp).const_mul (h x))
  have hpos : 0 < ∑ x ∈ s, h x * Real.exp (θ * T x) :=
    Finset.sum_pos (fun x hx => mul_pos (hh x hx) (Real.exp_pos _)) hs
  exact hZ.log hpos.ne'

/-- Exact granular score of an exponential family: the forward difference of the
log-partition function over one parameter step `δ` is the log of the moment
generating function `E_θ e^{δT}`. -/
theorem expfam_step {ι : Type*} (s : Finset ι) (h T : ι → ℝ) (hh : ∀ x ∈ s, 0 < h x)
    (hs : s.Nonempty) (θ δ : ℝ) :
    Real.log (∑ x ∈ s, h x * Real.exp ((θ + δ) * T x))
        - Real.log (∑ x ∈ s, h x * Real.exp (θ * T x))
      = Real.log (∑ x ∈ s, (h x * Real.exp (θ * T x) / ∑ y ∈ s, h y * Real.exp (θ * T y))
          * Real.exp (δ * T x)) := by
  have hZ : 0 < ∑ y ∈ s, h y * Real.exp (θ * T y) :=
    Finset.sum_pos (fun x hx => mul_pos (hh x hx) (Real.exp_pos _)) hs
  have e : ∑ x ∈ s, (h x * Real.exp (θ * T x) / ∑ y ∈ s, h y * Real.exp (θ * T y))
          * Real.exp (δ * T x)
      = (∑ x ∈ s, h x * Real.exp ((θ + δ) * T x)) / ∑ y ∈ s, h y * Real.exp (θ * T y) := by
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl; intro x _
    rw [add_mul, Real.exp_add]; ring
  have hZ' : 0 < ∑ x ∈ s, h x * Real.exp ((θ + δ) * T x) :=
    Finset.sum_pos (fun x hx => mul_pos (hh x hx) (Real.exp_pos _)) hs
  rw [e, Real.log_div hZ'.ne' hZ.ne']

/-- Exact chi-square between neighbouring members of an exponential family:
`E_θ[(p_{θ+δ}/p_θ)²] = Z(θ+2δ) Z(θ) / Z(θ+δ)²`, i.e. `exp` of the second
difference of the log-partition function. -/
theorem expfam_chi2 {ι : Type*} (s : Finset ι) (h T : ι → ℝ) (hh : ∀ x ∈ s, 0 < h x)
    (hs : s.Nonempty) (θ δ : ℝ) :
    let Z := fun t : ℝ => ∑ x ∈ s, h x * Real.exp (t * T x)
    ∑ x ∈ s, (h x * Real.exp (θ * T x) / Z θ) *
        ((h x * Real.exp ((θ + δ) * T x) / Z (θ + δ)) / (h x * Real.exp (θ * T x) / Z θ)) ^ 2
      = Z (θ + 2 * δ) * Z θ / Z (θ + δ) ^ 2 := by
  intro Z
  have hZ : ∀ t, 0 < Z t := fun t =>
    Finset.sum_pos (fun x hx => mul_pos (hh x hx) (Real.exp_pos _)) hs
  have e : ∀ x ∈ s, (h x * Real.exp (θ * T x) / Z θ) *
        ((h x * Real.exp ((θ + δ) * T x) / Z (θ + δ)) / (h x * Real.exp (θ * T x) / Z θ)) ^ 2
      = h x * Real.exp ((θ + 2 * δ) * T x) * (Z θ / Z (θ + δ) ^ 2) := by
    intro x hx
    have h1 := (hh x hx).ne'
    have h2 := (Real.exp_pos (θ * T x)).ne'
    have h3 := (hZ θ).ne'
    have h4 := (hZ (θ + δ)).ne'
    rw [show (θ + δ) * T x = θ * T x + δ * T x by ring,
      show (θ + 2 * δ) * T x = θ * T x + δ * T x + δ * T x by ring,
      Real.exp_add, Real.exp_add, Real.exp_add]
    field_simp
  rw [Finset.sum_congr rfl e, ← Finset.sum_mul]
  show Z (θ + 2 * δ) * (Z θ / Z (θ + δ) ^ 2) = _
  ring

/-- The granular normalisation `(2ε)ⁿ` shifts the log-partition function by the
constant `n log(2ε)` and so leaves all its derivatives (cumulants) unchanged. -/
theorem expfam_logpartition_shift (Z ε : ℝ) (n : ℕ) (hZ : 0 < Z) (hε : 0 < ε) :
    Real.log ((2 * ε) ^ n * Z) = n * Real.log (2 * ε) + Real.log Z := by
  rw [Real.log_mul (by positivity) hZ.ne', Real.log_pow]

end QE.Stat
