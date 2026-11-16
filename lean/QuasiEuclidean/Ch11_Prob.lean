-- SPDX-License-Identifier: MIT
-- Copyright 2026 Metere Industries, Inc. Author: Alfredo Metere.
-- Quasi-Euclidean Granular Geometry. Any derivative work must carry this notice:
--   This work is derivative of the Quasi-Euclidean Granular Geometry book
--   authored by Alfredo Metere. Copyright 2026 Metere Industries, Inc.
--   All rights reserved
-- See LICENSE.md and NOTICE.

import QuasiEuclidean.Basic

/-!
# Chapter 11: Hyperfinite probability

A (hyper)finite probability space is a finite set of outcomes `s` with
weights `p`.  All statements are exact finite identities or inequalities,
valid in every linearly ordered field `K`; with `K := Hyperreal` and a
hyperfinite `s` they are the internal statements of the book.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace QE.Prob

open Finset

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-! ## Probability and expectation on a finite outcome set -/

/-- Probability of the event `A` (a decidable predicate on outcomes). -/
def prob {α : Type*} (s : Finset α) (p : α → K) (A : α → Prop) [DecidablePred A] : K :=
  ∑ ω ∈ s.filter A, p ω

/-- Expectation of the random variable `X`. -/
def expect {α : Type*} (s : Finset α) (p : α → K) (X : α → K) : K :=
  ∑ ω ∈ s, p ω * X ω

/-- The uniform weight on `s`. -/
def unif {α : Type*} (s : Finset α) : α → K := fun _ => 1 / (s.card : K)

/-- Every outcome of a uniform (hyper)finite space has strictly positive
probability. -/
theorem unif_pos {α : Type*} (s : Finset α) (hs : s.Nonempty) (ω : α) :
    0 < (unif s ω : K) := by
  unfold unif
  have : (0 : K) < s.card := by exact_mod_cast hs.card_pos
  positivity

/-- The uniform weights sum to one. -/
theorem unif_sum {α : Type*} (s : Finset α) (hs : s.Nonempty) :
    ∑ ω ∈ s, (unif s ω : K) = 1 := by
  unfold unif
  have : (s.card : K) ≠ 0 := by exact_mod_cast hs.card_pos.ne'
  rw [sum_const, nsmul_eq_mul]; field_simp

/-- Probability of an event under the uniform weights is a ratio of counts. -/
theorem prob_unif {α : Type*} (s : Finset α) (A : α → Prop) [DecidablePred A] :
    prob s (unif s) A = ((s.filter A).card : K) / s.card := by
  unfold prob unif
  rw [sum_const, nsmul_eq_mul]; ring

/-- A nonempty event has positive probability when every outcome has positive
weight: there are no null events. -/
theorem prob_pos {α : Type*} (s : Finset α) (p : α → K) (hp : ∀ ω ∈ s, 0 < p ω)
    (A : α → Prop) [DecidablePred A] (hA : (s.filter A).Nonempty) :
    0 < prob s p A := by
  unfold prob
  exact sum_pos (fun ω hω => hp ω (mem_filter.1 hω).1) hA

/-- Uniform probability on a lattice box is the ratio of granular measures,
whatever the granule `ε ≠ 0`. -/
theorem unif_eq_mu_ratio (n : ℕ) (ε : K) (hε : ε ≠ 0) (A : Finset (Fin n → ℤ))
    (B : (Fin n → ℤ) → Prop) [DecidablePred B] :
    prob A (unif A) B = muN n ε (A.filter B) / muN n ε A := by
  rw [prob_unif]; unfold muN
  have : (2 * ε) ^ n ≠ 0 := pow_ne_zero _ (mul_ne_zero two_ne_zero hε)
  rw [mul_div_mul_left _ _ this]

/-- Granular density: if `P(X = x) = f(x) (2ε)^n`, then the probability of an
event is the granular integral of `f` over it, and a point where `f > 0`
carries strictly positive probability. -/
theorem density_prob (n : ℕ) (ε : K) (s : Finset (Fin n → ℤ)) (f : (Fin n → ℤ) → K)
    (A : (Fin n → ℤ) → Prop) [DecidablePred A] :
    prob s (fun k => f k * (2 * ε) ^ n) A = (∑ k ∈ s.filter A, f k) * (2 * ε) ^ n := by
  unfold prob; rw [sum_mul]

theorem density_point_pos (n : ℕ) (ε : K) (hε : 0 < ε) (f : (Fin n → ℤ) → K)
    (k : Fin n → ℤ) (hf : 0 < f k) : 0 < f k * (2 * ε) ^ n := by
  positivity

/-! ## Markov and Chebyshev, exactly -/

/-- Markov's inequality on a finite space. -/
theorem markov {α : Type*} (s : Finset α) (p : α → K) (hp : ∀ ω ∈ s, 0 ≤ p ω)
    (X : α → K) (hX : ∀ ω ∈ s, 0 ≤ X ω) (a : K) (ha : 0 < a) :
    prob s p (fun ω => a ≤ X ω) ≤ expect s p X / a := by
  rw [le_div_iff₀ ha]
  unfold prob expect
  calc (∑ ω ∈ s.filter (fun ω => a ≤ X ω), p ω) * a
      = ∑ ω ∈ s.filter (fun ω => a ≤ X ω), p ω * a := by rw [sum_mul]
    _ ≤ ∑ ω ∈ s.filter (fun ω => a ≤ X ω), p ω * X ω := by
        apply sum_le_sum
        intro ω hω
        rw [mem_filter] at hω
        exact mul_le_mul_of_nonneg_left hω.2 (hp ω hω.1)
    _ ≤ ∑ ω ∈ s, p ω * X ω := by
        apply sum_le_sum_of_subset_of_nonneg (filter_subset _ _)
        intro ω hω _
        exact mul_nonneg (hp ω hω) (hX ω hω)

/-- Chebyshev's inequality on a finite space (about an arbitrary centre `m`). -/
theorem chebyshev {α : Type*} (s : Finset α) (p : α → K) (hp : ∀ ω ∈ s, 0 ≤ p ω)
    (X : α → K) (m a : K) (ha : 0 < a) :
    prob s p (fun ω => a ≤ |X ω - m|) ≤ expect s p (fun ω => (X ω - m) ^ 2) / a ^ 2 := by
  have h := markov s p hp (fun ω => (X ω - m) ^ 2) (fun ω _ => sq_nonneg _) (a ^ 2)
    (by positivity)
  have hfe : s.filter (fun ω => a ≤ |X ω - m|) = s.filter (fun ω => a ^ 2 ≤ (X ω - m) ^ 2) := by
    apply filter_congr
    intro ω _
    rw [sq_le_sq, abs_of_pos ha]
  unfold prob at h ⊢
  rw [hfe]; exact h

/-! ## Coin tossing: exact second moment and the weak law -/

/-- The sign of a coin. -/
def sgn (b : Bool) : K := if b then 1 else -1

/-- Partial sum of `n` signs. -/
def S {n : ℕ} (ω : Fin n → Bool) : K := ∑ i, sgn (ω i)

theorem sgn_sq (b : Bool) : (sgn b : K) ^ 2 = 1 := by
  cases b <;> simp [sgn]

theorem sum_cons {M : Type*} [AddCommMonoid M] (n : ℕ) (F : (Fin (n + 1) → Bool) → M) :
    ∑ ω, F ω = ∑ b : Bool, ∑ ω' : Fin n → Bool, F (Fin.cons b ω') := by
  rw [← Fintype.sum_prod_type']
  exact (Fintype.sum_equiv (Fin.consEquiv (fun _ => Bool)) _ _ (fun _ => rfl)).symm

theorem S_cons (n : ℕ) (b : Bool) (ω' : Fin n → Bool) :
    (S (Fin.cons b ω' : Fin (n + 1) → Bool) : K) = sgn b + S ω' := by
  unfold S; rw [Fin.sum_univ_succ]; simp

/-- The sum of the walk over all `2^n` sign sequences vanishes. -/
theorem sum_S (n : ℕ) : ∑ ω : Fin n → Bool, (S ω : K) = 0 := by
  induction n with
  | zero => simp [S]
  | succ n ih =>
    rw [sum_cons]
    simp only [S_cons, sum_add_distrib, ih, sum_const, card_univ]
    simp [sgn, Fintype.card_fun]

/-- Exact second moment: `∑_ω S(ω)^2 = n · 2^n`, i.e. `E S_n^2 = n`. -/
theorem sum_S_sq (n : ℕ) : ∑ ω : Fin n → Bool, (S ω : K) ^ 2 = n * 2 ^ n := by
  induction n with
  | zero => simp [S]
  | succ n ih =>
    rw [sum_cons]
    have : ∀ b : Bool, ∑ ω' : Fin n → Bool, (S (Fin.cons b ω' : Fin (n+1) → Bool) : K) ^ 2
        = 2 ^ n + 2 * sgn b * ∑ ω' : Fin n → Bool, (S ω' : K)
          + ∑ ω' : Fin n → Bool, (S ω' : K) ^ 2 := by
      intro b
      simp only [S_cons]
      have e : ∀ ω' : Fin n → Bool, (sgn b + S ω' : K) ^ 2
          = 1 + 2 * sgn b * S ω' + S ω' ^ 2 := by
        intro ω'; rw [add_sq, sgn_sq]
      simp only [e, sum_add_distrib, ← mul_sum, sum_const, card_univ, Fintype.card_fun,
        Fintype.card_bool, Fintype.card_fin]
      simp only [nsmul_eq_mul, mul_one, Nat.cast_pow, Nat.cast_ofNat]
    rw [Fintype.sum_bool, this, this, sum_S, ih]
    push_cast; ring

/-- Expectation of `S_n^2` under the uniform (fair-coin) measure is exactly `n`. -/
theorem expect_S_sq (n : ℕ) :
    expect (univ : Finset (Fin n → Bool)) (unif univ) (fun ω => (S ω : K) ^ 2) = n := by
  unfold expect unif
  rw [← mul_sum, sum_S_sq, card_univ, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]
  push_cast
  have : (2 : K) ^ n ≠ 0 := pow_ne_zero _ two_ne_zero
  field_simp

/-- Weak law of large numbers in exact finite form:
`P(|S_n| ≥ n a) ≤ 1 / (n a^2)` for every `n ≥ 1` and `a > 0`. -/
theorem wlln (n : ℕ) (hn : 0 < n) (a : K) (ha : 0 < a) :
    prob (univ : Finset (Fin n → Bool)) (unif univ) (fun ω => n * a ≤ |(S ω : K) - 0|)
      ≤ 1 / (n * a ^ 2) := by
  have hn' : (0 : K) < n := by exact_mod_cast hn
  have h := chebyshev (univ : Finset (Fin n → Bool)) (unif univ)
    (fun ω _ => (unif_pos _ univ_nonempty ω).le) (fun ω => (S ω : K)) 0 (n * a)
    (by positivity)
  simp only [sub_zero] at h ⊢
  have e := expect_S_sq (K := K) n
  rw [e] at h
  calc _ ≤ (n : K) / (n * a) ^ 2 := h
    _ = 1 / (n * a ^ 2) := by field_simp

/-! ## Conditional probability on any event -/

/-- Conditional probability `P(A | B)`. -/
def cond {α : Type*} (s : Finset α) (p : α → K) (A B : α → Prop) [DecidablePred A]
    [DecidablePred B] : K :=
  prob s p (fun ω => A ω ∧ B ω) / prob s p B

/-- Bayes' formula, valid for every nonempty conditioning event (which has
positive probability). -/
theorem bayes {α : Type*} (s : Finset α) (p : α → K) (hp : ∀ ω ∈ s, 0 < p ω)
    (A B : α → Prop) [DecidablePred A] [DecidablePred B]
    (hA : (s.filter A).Nonempty) (hB : (s.filter B).Nonempty) :
    cond s p A B = cond s p B A * prob s p A / prob s p B := by
  have hpA := prob_pos s p hp A hA
  have hpB := prob_pos s p hp B hB
  unfold cond
  have : prob s p (fun ω => B ω ∧ A ω) = prob s p (fun ω => A ω ∧ B ω) := by
    unfold prob; congr 1; apply filter_congr; intro ω _; exact and_comm
  rw [this]; field_simp

/-- Conditioning a uniform product space on a fibre `{x} × T` gives the uniform
law on `T` exactly. -/
theorem cond_fibre {α β : Type*} [DecidableEq α] [DecidableEq β]
    (S : Finset α) (T : Finset β) (x : α) (hx : x ∈ S) (y : β) (hy : y ∈ T) :
    cond (S ×ˢ T) (unif (S ×ˢ T)) (fun ω => ω.2 = y) (fun ω => ω.1 = x)
      = 1 / (T.card : K) := by
  unfold cond
  rw [prob_unif, prob_unif]
  have h1 : (S ×ˢ T).filter (fun ω : α × β => ω.2 = y ∧ ω.1 = x) = {(x, y)} := by
    ext ⟨a, b⟩; simp only [mem_filter, mem_product, mem_singleton, Prod.mk.injEq]
    constructor
    · rintro ⟨_, h2, h1⟩; exact ⟨h1, h2⟩
    · rintro ⟨rfl, rfl⟩; exact ⟨⟨hx, hy⟩, rfl, rfl⟩
  have h2 : ((S ×ˢ T).filter (fun ω : α × β => ω.1 = x)).card = T.card := by
    have : (S ×ˢ T).filter (fun ω : α × β => ω.1 = x) = ({x} : Finset α) ×ˢ T := by
      ext ⟨a, b⟩; simp only [mem_filter, mem_product, mem_singleton]
      constructor
      · rintro ⟨⟨_, hb⟩, rfl⟩; exact ⟨rfl, hb⟩
      · rintro ⟨rfl, hb⟩; exact ⟨⟨hx, hb⟩, rfl⟩
    rw [this, card_product, card_singleton, one_mul]
  rw [h1, h2, card_singleton]
  push_cast
  have hS : (0 : K) < (S ×ˢ T).card := by
    exact_mod_cast (Finset.Nonempty.card_pos ⟨(x, y), mem_product.2 ⟨hx, hy⟩⟩)
  have hT : (0 : K) < T.card := by exact_mod_cast (Finset.Nonempty.card_pos ⟨y, hy⟩)
  field_simp

/-- Conditioning on a general event `T` of a uniform space: the conditional law
of an outcome is uniform on `T` (so the conditional law of any statistic is
its push-forward from `T`: the shape of `T` is the whole answer). -/
theorem cond_unif {α : Type*} (s : Finset α) (T : α → Prop) [DecidablePred T]
    (A : α → Prop) [DecidablePred A] (hT : (s.filter T).Nonempty) :
    cond s (unif s) A T = (((s.filter T).filter A).card : K) / (s.filter T).card := by
  unfold cond; rw [prob_unif, prob_unif]
  have hs : (0 : K) < s.card := by
    obtain ⟨ω, hω⟩ := hT
    exact_mod_cast Finset.Nonempty.card_pos ⟨ω, (mem_filter.1 hω).1⟩
  have hT' : (0 : K) < (s.filter T).card := by exact_mod_cast hT.card_pos
  have : s.filter (fun ω => A ω ∧ T ω) = (s.filter T).filter A := by
    rw [filter_filter]; apply filter_congr; intro ω _; exact and_comm
  rw [this]; field_simp

/-- Conditional law on a coordinate fibre of a product space with arbitrary
weights: `P(Y = y | X = x) = w(x,y) / ∑_{y'} w(x,y')`.  This is the granular
regular conditional density, defined at every `x`. -/
theorem cond_fibre_weights {α β : Type*} [DecidableEq α] [DecidableEq β]
    (S : Finset α) (T : Finset β) (w : α × β → K) (x : α) (hx : x ∈ S) (y : β) (hy : y ∈ T) :
    cond (S ×ˢ T) w (fun ω => ω.2 = y) (fun ω => ω.1 = x)
      = w (x, y) / ∑ y' ∈ T, w (x, y') := by
  unfold cond prob
  have h1 : (S ×ˢ T).filter (fun ω : α × β => ω.2 = y ∧ ω.1 = x) = {(x, y)} := by
    ext ⟨a, b⟩; simp only [mem_filter, mem_product, mem_singleton, Prod.mk.injEq]
    constructor
    · rintro ⟨_, h2, h1⟩; exact ⟨h1, h2⟩
    · rintro ⟨rfl, rfl⟩; exact ⟨⟨hx, hy⟩, rfl, rfl⟩
  have h2 : (S ×ˢ T).filter (fun ω : α × β => ω.1 = x) = ({x} : Finset α) ×ˢ T := by
    ext ⟨a, b⟩; simp only [mem_filter, mem_product, mem_singleton]
    constructor
    · rintro ⟨⟨_, hb⟩, rfl⟩; exact ⟨rfl, hb⟩
    · rintro ⟨rfl, hb⟩; exact ⟨⟨hx, hb⟩, rfl⟩
  rw [h1, h2, sum_singleton, sum_product, sum_singleton]

/-! ## Independence and product spaces -/

/-- Under the uniform law on a product, rectangles factorise exactly. -/
theorem unif_product {α β : Type*} (S : Finset α) (T : Finset β)
    (A : α → Prop) (B : β → Prop) [DecidablePred A] [DecidablePred B] :
    prob (S ×ˢ T) (unif (S ×ˢ T) : α × β → K) (fun ω => A ω.1 ∧ B ω.2)
      = prob S (unif S) A * prob T (unif T) B := by
  rw [prob_unif, prob_unif, prob_unif]
  have : (S ×ˢ T).filter (fun ω : α × β => A ω.1 ∧ B ω.2) = S.filter A ×ˢ T.filter B := by
    ext ⟨a, b⟩; simp only [mem_filter, mem_product]; tauto
  rw [this, card_product, card_product]; push_cast
  rw [mul_div_mul_comm]

/-! ## Uniform probability on `{1, …, H}` and natural density -/

/-- Each integer of `{1,…,H}` has probability `1/H > 0`. -/
theorem unif_Icc_point (H : ℕ) (hH : 0 < H) (k : ℕ) :
    (unif (Icc 1 H) k : K) = 1 / H := by
  unfold unif; simp

/-- The probability that a uniformly chosen integer of `{1,…,H}` is divisible
by `m` is exactly `⌊H/m⌋/H`. -/
theorem prob_dvd (H m : ℕ) :
    prob (Icc 1 H) (unif (Icc 1 H)) (fun x => m ∣ x) = ((H / m : ℕ) : K) / H := by
  rw [prob_unif]
  have : Icc 1 H = Ioc 0 H := by ext x; simp [Nat.lt_iff_add_one_le]
  rw [this, Nat.Ioc_filter_dvd_card_eq_div]; simp

/-- ...and differs from `1/m` by at most `1/H`: the natural density `1/m` is the
shadow of the hyperfinite probability when `H` is infinite. -/
theorem prob_dvd_close (H m : ℕ) (hH : 0 < H) (hm : 0 < m) :
    |((H / m : ℕ) : K) / H - 1 / m| ≤ 1 / H := by
  have hH' : (0 : K) < H := by exact_mod_cast hH
  have hm' : (0 : K) < m := by exact_mod_cast hm
  have hdiv := Nat.div_add_mod H m
  have hr := Nat.mod_lt H hm
  set q := H / m
  set r := H % m
  have hHq : (H : K) = m * q + r := by exact_mod_cast hdiv.symm
  have hrK : (r : K) < m := by exact_mod_cast hr
  have hr0 : (0 : K) ≤ r := by positivity
  have e : (q : K) / H - 1 / m = -(r / (m * H)) := by
    have h3 : (q : K) * m - H * 1 = -r := by rw [hHq]; ring
    rw [div_sub_div _ _ hH'.ne' hm'.ne', h3, neg_div, mul_comm (H : K)]
  rw [e, abs_neg, abs_of_nonneg (by positivity)]
  rw [div_le_div_iff₀ (by positivity) hH']
  nlinarith

/-- Exact shift defect of the uniform law on `{0,…,H-1}`: for every set `A ⊆ ℕ`,
`P(X + 1 ∈ A) - P(X ∈ A) = (1_A(H) - 1_A(0))/H`. Translation invariance fails
only by a boundary term of size at most `1/H`. -/
theorem shift_defect (H : ℕ) (A : ℕ → Prop) [DecidablePred A] :
    prob (range H) (unif (range H)) (fun k => A (k + 1)) - prob (range H) (unif (range H)) A
      = ((if A H then (1 : K) else 0) - (if A 0 then 1 else 0)) / H := by
  unfold prob unif
  rw [sum_filter, sum_filter, ← sum_sub_distrib, card_range]
  have := sum_range_sub (fun k => if A k then (1 : K) / H else 0) H
  rw [this]
  split_ifs <;> ring

theorem shift_defect_abs (H : ℕ) (hH : 0 < H) (A : ℕ → Prop) [DecidablePred A] :
    |prob (range H) (unif (range H)) (fun k => A (k + 1)) - prob (range H) (unif (range H)) A|
      ≤ (1 : K) / H := by
  rw [shift_defect]
  have hH' : (0 : K) < H := by exact_mod_cast hH
  rw [abs_div, abs_of_pos hH']
  apply div_le_div_of_nonneg_right _ hH'.le
  split_ifs <;> norm_num

/-- Natural density is the shadow of the hyperfinite uniform probability:
if `#(A ∩ [1,n])/n → d`, then at the infinite hypernatural `ω` (the class of
`n ↦ n`) the internal probability `#(*A ∩ [1,ω])/ω` has standard part `d`. -/
theorem density_shadow (A : ℕ → Prop) [DecidablePred A] (d : ℝ)
    (h : Filter.Tendsto (fun n : ℕ => (((Icc 1 n).filter A).card : ℝ) / n)
      Filter.atTop (nhds d)) :
    (Hyperreal.ofSeq (fun n : ℕ => (((Icc 1 n).filter A).card : ℝ) / n)).Tendsto (nhds d) :=
  Hyperreal.tendsto_ofSeq.2 (h.mono_left Nat.hyperfilter_le_atTop)

/-! ## Bertrand's chord: two granulations, two exact answers -/

/-- "Random radial distance" granulation: `2M` equally spaced distances in
`[0,1)`, of which exactly `M` lie in `[0,1/2)`; the probability is exactly `1/2`. -/
theorem bertrand_radial (M : ℕ) (hM : 0 < M) :
    prob (range (2 * M)) (unif (range (2 * M))) (fun k => k < M) = (1 / 2 : K) := by
  rw [prob_unif]
  have : (range (2 * M)).filter (fun k => k < M) = range M := by
    ext k; simp only [mem_filter, mem_range]; omega
  rw [this, card_range, card_range]
  have : (0 : K) < M := by exact_mod_cast hM
  push_cast; field_simp

/-- "Random endpoints" granulation with `N = 3M` angular cells: the chord is
strictly longer than the side of the inscribed triangle iff the angular index
difference lies in `(M, 2M)`; there are exactly `M - 1` such indices, so the
probability is exactly `1/3 - 1/(3M)`, and the boundary event (chord exactly
equal to the side) has probability `2/(3M) > 0`. -/
theorem bertrand_endpoints (M : ℕ) (hM : 0 < M) :
    prob (range (3 * M)) (unif (range (3 * M))) (fun k => M < k ∧ k < 2 * M)
      = (1 / 3 : K) - 1 / (3 * M) := by
  rw [prob_unif]
  have : (range (3 * M)).filter (fun k => M < k ∧ k < 2 * M) = Ioo M (2 * M) := by
    ext k; simp only [mem_filter, mem_range, mem_Ioo]; omega
  rw [this, Nat.card_Ioo, card_range]
  have hM' : (0 : K) < M := by exact_mod_cast hM
  have : ((2 * M - M - 1 : ℕ) : K) = M - 1 := by
    rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]; push_cast; ring
  rw [this]; push_cast; field_simp

theorem bertrand_boundary (M : ℕ) (hM : 0 < M) :
    prob (range (3 * M)) (unif (range (3 * M))) (fun k => k = M ∨ k = 2 * M)
      = (2 : K) / (3 * M) := by
  rw [prob_unif]
  have : (range (3 * M)).filter (fun k => k = M ∨ k = 2 * M) = {M, 2 * M} := by
    ext k; simp only [mem_filter, mem_range, mem_insert, mem_singleton]; omega
  rw [this, card_pair (by omega), card_range]; push_cast; ring

/-! ## Ties: the birthday bound with `N` cells -/

/-- The number of tie-free samples of size `n` from `N` cells. -/
theorem card_injective (n N : ℕ) :
    ((univ : Finset (Fin n → Fin N)).filter Function.Injective).card = N.descFactorial n := by
  rw [← Fintype.card_subtype, Fintype.card_congr (Equiv.subtypeInjectiveEquivEmbedding _ _),
    Fintype.card_embedding_eq, Fintype.card_fin, Fintype.card_fin]

/-- Descending factorial as a product. -/
theorem descFactorial_eq_prod (N n : ℕ) (h : n ≤ N) :
    (N.descFactorial n : K) = ∏ k ∈ range n, ((N : K) - k) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Nat.descFactorial_succ, prod_range_succ, ← ih (by omega), Nat.cast_mul,
      Nat.cast_sub (by omega), mul_comm]

/-- Union bound for products: `1 - ∏ (1 - a_k) ≤ ∑ a_k` for `a_k ∈ [0,1]`. -/
theorem one_sub_prod_le_sum (n : ℕ) (a : ℕ → K) (h0 : ∀ k, 0 ≤ a k) (h1 : ∀ k, a k ≤ 1) :
    1 - ∏ k ∈ range n, (1 - a k) ≤ ∑ k ∈ range n, a k := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [prod_range_succ, sum_range_succ]
    have hP0 : 0 ≤ ∏ k ∈ range n, (1 - a k) :=
      prod_nonneg (fun k _ => sub_nonneg.2 (h1 k))
    have hP1 : ∏ k ∈ range n, (1 - a k) ≤ 1 :=
      prod_le_one₀ (fun k _ => sub_nonneg.2 (h1 k)) (fun k _ => by linarith [h0 k])
    nlinarith [h0 n]

/-- Probability of no tie among `n` samples from `N` equiprobable cells. -/
theorem prob_no_tie (n N : ℕ) (hN : 0 < N) (h : n ≤ N) :
    prob (univ : Finset (Fin n → Fin N)) (unif univ) Function.Injective
      = ∏ k ∈ range n, (1 - (k : K) / N) := by
  rw [prob_unif, card_injective, card_univ, Fintype.card_fun, Fintype.card_fin,
    Fintype.card_fin, descFactorial_eq_prod N n h]
  have hN' : (N : K) ≠ 0 := by exact_mod_cast hN.ne'
  push_cast
  rw [show (N : K) ^ n = ∏ _k ∈ range n, (N : K) by simp, ← prod_div_distrib]
  apply prod_congr rfl; intro k _; field_simp

/-- Birthday bound: the probability of at least one tie is at most
`n(n-1)/(2N)`. With `N = 1/(2ε)` cells this is `n(n-1)ε`. -/
theorem tie_le (n N : ℕ) (hN : 0 < N) (h : n ≤ N) :
    1 - prob (univ : Finset (Fin n → Fin N)) (unif univ) Function.Injective
      ≤ (n : K) * (n - 1) / (2 * N) := by
  rw [prob_no_tie n N hN h]
  have hN' : (0 : K) < N := by exact_mod_cast hN
  have := one_sub_prod_le_sum (K := K) n (fun k => (k : K) / N)
    (fun k => by positivity)
  calc _ ≤ ∑ k ∈ range n, (k : K) / N := by
        apply le_trans _ (le_refl _)
        -- only indices `k < n ≤ N` occur; restrict the bound accordingly
        have key : ∀ m ≤ n, 1 - ∏ k ∈ range m, (1 - (k : K) / N) ≤ ∑ k ∈ range m, (k : K) / N := by
          intro m hm
          induction m with
          | zero => simp
          | succ m ih =>
            rw [prod_range_succ, sum_range_succ]
            have ih := ih (by omega)
            have hm1 : (m : K) / N ≤ 1 := by
              rw [div_le_one hN']; exact_mod_cast (by omega : m ≤ N)
            have hP0 : 0 ≤ ∏ k ∈ range m, (1 - (k : K) / N) := by
              apply prod_nonneg; intro k hk
              rw [mem_range] at hk
              have : (k : K) / N ≤ 1 := by
                rw [div_le_one hN']; exact_mod_cast (by omega : k ≤ N)
              linarith
            have hP1 : ∏ k ∈ range m, (1 - (k : K) / N) ≤ 1 := by
              apply prod_le_one₀
              · intro k hk; rw [mem_range] at hk
                have : (k : K) / N ≤ 1 := by
                  rw [div_le_one hN']; exact_mod_cast (by omega : k ≤ N)
                linarith
              · intro k _; have : (0 : K) ≤ k / N := by positivity
                linarith
            have : (0 : K) ≤ m / N := by positivity
            nlinarith
        exact key n le_rfl
    _ = (n : K) * (n - 1) / (2 * N) := by
        rw [← sum_div]
        have hs : ∀ m : ℕ, ∑ k ∈ range m, (k : K) = m * (m - 1) / 2 := by
          intro m; induction m with
          | zero => simp
          | succ m ih => rw [sum_range_succ, ih]; push_cast; ring
        rw [hs]; field_simp

/-- Lower bound: the probability of no tie is at most `exp(-n(n-1)/(2N))`. -/
theorem no_tie_le_exp (n N : ℕ) (hN : 0 < N) (h : n ≤ N) :
    prob (univ : Finset (Fin n → Fin N)) (unif univ) Function.Injective
      ≤ Real.exp (-((n : ℝ) * (n - 1) / (2 * N))) := by
  rw [prob_no_tie n N hN h]
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have hs : ∑ k ∈ range n, (k : ℝ) / N = n * (n - 1) / (2 * N) := by
    rw [← sum_div]
    have : ∀ m : ℕ, ∑ k ∈ range m, (k : ℝ) = m * (m - 1) / 2 := by
      intro m; induction m with
      | zero => simp
      | succ m ih => rw [sum_range_succ, ih]; push_cast; ring
    rw [this]; field_simp
  rw [← hs, ← sum_neg_distrib, Real.exp_sum]
  apply prod_le_prod₀
  · intro k hk; rw [mem_range] at hk
    have : (k : ℝ) / N ≤ 1 := by rw [div_le_one hN']; exact_mod_cast (by omega : k ≤ N)
    linarith
  · intro k _
    have := Real.add_one_le_exp (-((k : ℝ) / N))
    linarith

/-- Probability of a tie between two independent draws with weights `w`:
`P(X = Y) = ∑_x w(x)^2`. -/
theorem prob_tie_two {α : Type*} [DecidableEq α] (s : Finset α) (w : α → K) :
    prob (s ×ˢ s) (fun ω => w ω.1 * w ω.2) (fun ω => ω.1 = ω.2) = ∑ x ∈ s, w x ^ 2 := by
  unfold prob
  rw [← diag_eq_filter, diag, sum_map]
  apply sum_congr rfl; intro x _; simp [sq]

/-- With a granular density, `P(X = Y) = 2ε · ∑ f(x)^2 · 2ε`: the collision
probability is exactly `2ε` times the granular integral of `f^2`. -/
theorem prob_tie_density {α : Type*} [DecidableEq α] (s : Finset α) (f : α → K) (ε : K) :
    prob (s ×ˢ s) (fun ω => (f ω.1 * (2 * ε)) * (f ω.2 * (2 * ε))) (fun ω => ω.1 = ω.2)
      = 2 * ε * ∑ x ∈ s, f x ^ 2 * (2 * ε) := by
  rw [prob_tie_two s (fun x => f x * (2 * ε)), mul_sum]; apply sum_congr rfl; intro x _; ring

/-! ## Uniform law on a lattice interval: the openness of the interval is in
the variance -/

theorem sum_range_cast (N : ℕ) : ∑ k ∈ range N, (k : K) = N * (N - 1) / 2 := by
  induction N with
  | zero => simp
  | succ m ih => rw [sum_range_succ, ih]; push_cast; ring

theorem sum_range_cast_sq (N : ℕ) :
    ∑ k ∈ range N, (k : K) ^ 2 = N * (N - 1) * (2 * N - 1) / 6 := by
  induction N with
  | zero => simp
  | succ m ih => rw [sum_range_succ, ih]; push_cast; ring

/-- Uniform law on the half-open lattice interval `[0,1) ∩ 2εℤ` (`2εN = 1`):
mean `1/2 - ε`, variance `(1 - 4ε²)/12`, exactly. -/
theorem unif_halfopen_moments (ε : K) (N : ℕ) (hN : 0 < N) (h : 2 * ε * N = 1) :
    (∑ k ∈ range N, (1 / (N : K)) * (2 * ε * k)) = 1 / 2 - ε ∧
    (∑ k ∈ range N, (1 / (N : K)) * (2 * ε * k) ^ 2) - (1 / 2 - ε) ^ 2
      = (1 - 4 * ε ^ 2) / 12 := by
  have hN' : (N : K) ≠ 0 := by exact_mod_cast hN.ne'
  have hε : ε = 1 / (2 * N) := by field_simp; linarith
  subst hε
  constructor
  · simp only [← mul_sum, mul_pow]
    rw [sum_range_cast]; field_simp
  · simp only [mul_pow, ← mul_sum]
    rw [sum_range_cast_sq]; field_simp; ring

/-- Uniform law on the closed lattice interval `[0,1] ∩ 2εℤ` (`2εN = 1`,
`N+1` points): mean `1/2`, variance `(1 + 4ε)/12`, exactly. -/
theorem unif_closed_moments (ε : K) (N : ℕ) (hN : 0 < N) (h : 2 * ε * N = 1) :
    (∑ k ∈ range (N + 1), (1 / ((N + 1 : ℕ) : K)) * (2 * ε * k)) = 1 / 2 ∧
    (∑ k ∈ range (N + 1), (1 / ((N + 1 : ℕ) : K)) * (2 * ε * k) ^ 2) - (1 / 2) ^ 2
      = (1 + 4 * ε) / 12 := by
  have hN' : (N : K) ≠ 0 := by exact_mod_cast hN.ne'
  have hN1 : ((N : K) + 1) ≠ 0 := by positivity
  have hε : ε = 1 / (2 * N) := by field_simp; linarith
  subst hε
  constructor
  · simp only [← mul_sum]
    rw [sum_range_cast]; push_cast; field_simp; ring
  · simp only [mul_pow, ← mul_sum]
    rw [sum_range_cast_sq]; push_cast; field_simp; ring

/-! ## Characteristic functions on the hyperfinite torus -/

open ZMod in
/-- Characteristic function of a law `p` on the torus `ℤ/Nℤ` (lattice of `N`
cells): `φ(t) = ∑_j p(j) e(j t / N)`. -/
noncomputable def charFn {N : ℕ} [NeZero N] (p : ZMod N → ℂ) (t : ZMod N) : ℂ :=
  ∑ j : ZMod N, stdAddChar (j * t) * p j

open ZMod in
/-- Exact inversion: `p(k) = (1/N) ∑_t e(-t k / N) φ(t)`. -/
theorem charFn_inversion {N : ℕ} [NeZero N] (p : ZMod N → ℂ) (k : ZMod N) :
    p k = (N : ℂ)⁻¹ * ∑ t : ZMod N, stdAddChar (-(t * k)) * charFn p t := by
  have h1 : charFn p = fun t => (N : ℂ) * (𝓕⁻ p) t := by
    funext t
    rw [invDFT_apply, smul_eq_mul, ← mul_assoc, mul_inv_cancel₀ (NeZero.ne _), one_mul]
    rfl
  have h2 : p = 𝓕 (𝓕⁻ p) := by simp
  conv_lhs => rw [h2]
  rw [dft_apply, h1, mul_sum]
  apply sum_congr rfl; intro t _
  rw [smul_eq_mul]
  have hN : (N : ℂ) ≠ 0 := NeZero.ne _
  field_simp

open ZMod in
/-- `φ(0) = 1` for a probability law. -/
theorem charFn_zero {N : ℕ} [NeZero N] (p : ZMod N → ℂ) (hp : ∑ j, p j = 1) :
    charFn p 0 = 1 := by
  simp [charFn, hp]

open ZMod in
/-- Convolution of two laws on the torus (law of the sum of independent
variables). -/
noncomputable def conv {N : ℕ} [NeZero N] (p q : ZMod N → ℂ) (k : ZMod N) : ℂ :=
  ∑ j : ZMod N, p j * q (k - j)

open ZMod in
/-- The characteristic function of an independent sum is the product. -/
theorem charFn_conv {N : ℕ} [NeZero N] (p q : ZMod N → ℂ) (t : ZMod N) :
    charFn (conv p q) t = charFn p t * charFn q t := by
  unfold charFn conv
  rw [sum_mul_sum]
  simp_rw [mul_sum]
  rw [sum_comm]
  apply sum_congr rfl; intro j _
  rw [← Fintype.sum_equiv (Equiv.addLeft j) (fun m => stdAddChar ((j + m) * t) * (p j * q (j + m - j)))
    (fun k => stdAddChar (k * t) * (p j * q (k - j))) (fun _ => rfl)]
  apply sum_congr rfl; intro m _
  rw [add_sub_cancel_left, add_mul, AddChar.map_add_eq_mul]; ring

/-! ## Granulating a classical law: snapping -/

/-- Rounding to the nearest lattice centre, `⌊y⌉_ε = 2ε ⌊y/(2ε) + 1/2⌋`. -/
noncomputable def snap {L : Type*} [Field L] [LinearOrder L] [IsStrictOrderedRing L]
    [FloorRing L] (ε y : L) : L :=
  2 * ε * ⌊y / (2 * ε) + 1 / 2⌋

/-- Snapping moves a point by at most the granule `ε`. -/
theorem snap_err {L : Type*} [Field L] [LinearOrder L] [IsStrictOrderedRing L] [FloorRing L]
    (ε : L) (hε : 0 < ε) (y : L) : |snap ε y - y| ≤ ε := by
  unfold snap
  set t := y / (2 * ε) + 1 / 2
  have h1 := Int.floor_le t
  have h2 := Int.lt_floor_add_one t
  have hy : y = 2 * ε * (t - 1 / 2) := by simp only [t]; field_simp; ring
  rw [hy, abs_le]
  constructor <;> nlinarith

/-- If two random variables differ by at most `δ` at every outcome, their
expectations differ by at most `δ`. -/
theorem expect_close {α : Type*} (s : Finset α) (p : α → K) (hp : ∀ ω ∈ s, 0 ≤ p ω)
    (hs : ∑ ω ∈ s, p ω = 1) (g h : α → K) (δ : K) (hgh : ∀ ω ∈ s, |g ω - h ω| ≤ δ) :
    |expect s p g - expect s p h| ≤ δ := by
  unfold expect
  rw [← sum_sub_distrib]
  calc |∑ ω ∈ s, (p ω * g ω - p ω * h ω)| ≤ ∑ ω ∈ s, |p ω * g ω - p ω * h ω| :=
        abs_sum_le_sum_abs _ _
    _ = ∑ ω ∈ s, p ω * |g ω - h ω| := by
        apply sum_congr rfl; intro ω hω
        rw [← mul_sub, abs_mul, abs_of_nonneg (hp ω hω)]
    _ ≤ ∑ ω ∈ s, p ω * δ := by
        apply sum_le_sum; intro ω hω
        exact mul_le_mul_of_nonneg_left (hgh ω hω) (hp ω hω)
    _ = δ := by rw [← sum_mul, hs, one_mul]

/-- Snapping a (finitely supported) classical law shifts its mean by at most `ε`. -/
theorem expect_snap {α : Type*} {L : Type*} [Field L] [LinearOrder L] [IsStrictOrderedRing L]
    [FloorRing L] (s : Finset α) (p : α → L) (hp : ∀ ω ∈ s, 0 ≤ p ω)
    (hs : ∑ ω ∈ s, p ω = 1) (Y : α → L) (ε : L) (hε : 0 < ε) :
    |expect s p (fun ω => snap ε (Y ω)) - expect s p Y| ≤ ε :=
  expect_close s p hp hs _ _ ε (fun ω _ => snap_err ε hε (Y ω))

/-- A random point of the lattice `{k/N : 1 ≤ k ≤ N}` with `N = d m` has
denominator dividing `m` (i.e. `d ∣ k`) with probability exactly `m/N`. -/
theorem prob_den_dvd (d m : ℕ) (hd : 0 < d) :
    prob (Icc 1 (d * m)) (unif (Icc 1 (d * m))) (fun k => d ∣ k)
      = (m : K) / ((d * m : ℕ) : K) := by
  rw [prob_dvd, Nat.mul_div_cancel_left _ hd]

/-- Every lattice point `k/N` is rational. -/
theorem lattice_rational (N : ℕ) (k : ℤ) : ∃ q : ℚ, ((k : ℝ) / N) = q :=
  ⟨(k : ℚ) / N, by push_cast; rfl⟩

/-! ## The granular exponential law -/

/-- Waiting time on the time lattice: `P(T = 2εk) = q (1 - q)^k`. -/
theorem geom_tail (q : K) (n : ℕ) :
    ∑ k ∈ range n, q * (1 - q) ^ k = 1 - (1 - q) ^ n := by
  induction n with
  | zero => simp
  | succ n ih => rw [sum_range_succ, ih, pow_succ]; ring

/-- Exact memorylessness: `P(T ≥ s + t | T ≥ s) = P(T ≥ t)`. -/
theorem geom_memoryless (q : K) (hq : q < 1) (s t : ℕ) :
    (1 - q) ^ (s + t) / (1 - q) ^ s = (1 - q) ^ t := by
  have : (1 - q) ^ s ≠ 0 := pow_ne_zero _ (by linarith)
  rw [pow_add]; field_simp

/-- With hazard `q = 2ελ`, the waiting-time law has granular density
`f(2εk) = λ (1 - 2ελ)^k`. -/
theorem geom_density (ε lam : K) (k : ℕ) :
    (2 * ε * lam) * (1 - 2 * ε * lam) ^ k = (lam * (1 - 2 * ε * lam) ^ k) * (2 * ε) := by
  ring

end QE.Prob
