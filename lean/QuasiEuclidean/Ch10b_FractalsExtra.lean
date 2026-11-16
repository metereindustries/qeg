-- SPDX-License-Identifier: MIT
-- Copyright 2026 Metere Industries, Inc. Author: Alfredo Metere.
-- Quasi-Euclidean Granular Geometry. Any derivative work must carry this notice:
--   This work is derivative of the Quasi-Euclidean Granular Geometry book
--   authored by Alfredo Metere. Copyright 2026 Metere Industries, Inc.
--   All rights reserved
-- See LICENSE.md and NOTICE.

import QuasiEuclidean.Ch10b_Fractals

/-!
# Chapter 10b (continued): staircase, level-dependent digits, snapping shadows

Contents (namespace `QE.Fractal`):
* **I. Digit sets with level-dependent digits** `digitSeqSet b D K` (level `i`
  uses the digits `D i`): exact count `∏_{i<K} |D i|`, exact boxes, and the
  alternating-blocks set of `prop:fr-alt` with its exact granular dimension.
* **J. The b-adic lattice inside the factorial lattice**: `b^K ∣ (bK)!`.
* **K. The snapped set `{1/n}`**: exact two-sided count.
* **L. The granular devil's staircase** and the digit formula of the Cantor
  function at triadic rationals; exact agreement, jumps, derivative, FTC.
* **M. Dragon curves**: no rounding up to depth `2K`.
* **N. Shadow of the segment-wise snapped curve**: the granule-depth estimate,
  the infinitesimal step, Hausdorff distances, Hutchinson contraction, and the
  standard parts of the vertex sets.

All sections except **N** are exact and finitary (no limits, no measure).
Section **N** is a shadow section; it uses the Hausdorff distance and limits
along the hyperfilter, but no Lebesgue measure.
-/

namespace QE.Fractal

open Finset

/-! ## I. Digit sets with level-dependent digits -/

/-- The level-`K` digit set with level-dependent digits: level `0` is `{0}`, and
level `K+1` consists of `b x + d` with `x` at level `K` and `d ∈ D K`.
Levels are added coarsest first: `D 0` is the most significant digit. -/
def digitSeqSet (b : ℕ) (D : ℕ → Finset ℕ) : ℕ → Finset ℕ
  | 0 => {0}
  | K + 1 => ((digitSeqSet b D K) ×ˢ D K).image (fun p => b * p.1 + p.2)

theorem digitSeqSet_succ (b : ℕ) (D : ℕ → Finset ℕ) (K : ℕ) :
    digitSeqSet b D (K + 1) = ((digitSeqSet b D K) ×ˢ D K).image (fun p => b * p.1 + p.2) :=
  rfl

/-- With a constant digit sequence, `digitSeqSet` is the digit set `digitSet`. -/
theorem digitSeqSet_const (b : ℕ) (D : Finset ℕ) (K : ℕ) :
    digitSeqSet b (fun _ => D) K = digitSet b D K := by
  induction K with
  | zero => rfl
  | succ K ih => rw [digitSeqSet_succ, digitSet_succ, ih]

/-- Exact count: if every digit of every level is `< b`, then
`#(digitSeqSet b D K) = ∏_{i<K} |D i|`. -/
theorem card_digitSeqSet {b : ℕ} {D : ℕ → Finset ℕ} (hD : ∀ i, ∀ d ∈ D i, d < b) (K : ℕ) :
    (digitSeqSet b D K).card = ∏ i ∈ range K, (D i).card := by
  induction K with
  | zero => simp [digitSeqSet]
  | succ K ih =>
    rw [digitSeqSet_succ, card_image_of_injOn, card_product, ih, prod_range_succ]
    rintro ⟨x, d⟩ hp ⟨x', d'⟩ hp' h
    simp only [coe_product, Set.mem_prod, mem_coe] at hp hp'
    obtain ⟨h1, h2⟩ := digit_inj (hD K d hp.2) (hD K d' hp'.2) h
    exact Prod.ext h1 h2

/-- Exact coarse-graining: floor division by `b` deletes the finest level. -/
theorem digitSeqSet_coarse {b : ℕ} {D : ℕ → Finset ℕ} (hD : ∀ i, ∀ d ∈ D i, d < b)
    (hne : ∀ i, (D i).Nonempty) (K : ℕ) :
    (digitSeqSet b D (K + 1)).image (· / b) = digitSeqSet b D K := by
  rw [digitSeqSet_succ, image_image]
  ext x
  simp only [mem_image, mem_product, Function.comp_apply, Prod.exists]
  constructor
  · rintro ⟨y, d, ⟨hy, hd⟩, rfl⟩
    rw [digit_div (hD K d hd)]; exact hy
  · intro hx
    obtain ⟨d, hd⟩ := hne K
    exact ⟨x, d, ⟨hx, hd⟩, digit_div (hD K d hd)⟩

/-- Exact boxes: for `j ≤ K`, the boxes of side `b^j` met by level `K` are
exactly level `K - j` (the `j` finest levels are deleted). -/
theorem digitSeqSet_boxes {b : ℕ} {D : ℕ → Finset ℕ} (hD : ∀ i, ∀ d ∈ D i, d < b)
    (hne : ∀ i, (D i).Nonempty) {j K : ℕ} (hj : j ≤ K) :
    (digitSeqSet b D K).image (· / b ^ j) = digitSeqSet b D (K - j) := by
  induction j with
  | zero => simp
  | succ j ih =>
    have hK : K - j = (K - (j + 1)) + 1 := by omega
    have : (fun x : ℕ => x / b ^ (j + 1)) = (fun x => x / b) ∘ (fun x => x / b ^ j) := by
      funext x; simp [pow_succ, Nat.div_div_eq_div_mul]
    rw [this, ← image_image, ih (by omega), hK, digitSeqSet_coarse hD hne]

/-- Exact box counts: for `j ≤ K`, `NN (b^j) (digitSeqSet b D K) = ∏_{i<K-j} |D i|`. -/
theorem NN_digitSeqSet {b : ℕ} {D : ℕ → Finset ℕ} (hD : ∀ i, ∀ d ∈ D i, d < b)
    (hne : ∀ i, (D i).Nonempty) {j K : ℕ} (hj : j ≤ K) :
    NN (b ^ j) (digitSeqSet b D K) = ∏ i ∈ range (K - j), (D i).card := by
  rw [NN, digitSeqSet_boxes hD hne hj, card_digitSeqSet hD]

/-! ### The alternating-blocks set of `prop:fr-alt` -/

/-- Block index of level `n` (`0`-based): block `k` has `2^k` levels, so level
`n` lies in block `Nat.log 2 (n+1)`. -/
def altBlock (n : ℕ) : ℕ := Nat.log 2 (n + 1)

/-- The digits of level `n`: `{0,2}` in even blocks, `{0,1,2}` in odd blocks. -/
def altDigits (n : ℕ) : Finset ℕ := if Even (altBlock n) then {0, 2} else {0, 1, 2}

/-- The alternating set `A_K` (triadic, level-dependent digits). -/
def altSet (K : ℕ) : Finset ℕ := digitSeqSet 3 altDigits K

/-- `c K`: the number of `{0,1,2}` levels among the first `K` levels. -/
def altC (K : ℕ) : ℕ := ((range K).filter fun n => ¬ Even (altBlock n)).card

theorem altDigits_lt : ∀ i, ∀ d ∈ altDigits i, d < 3 := by
  intro i d hd
  unfold altDigits at hd
  split_ifs at hd <;> simp at hd <;> omega

theorem altDigits_nonempty : ∀ i, (altDigits i).Nonempty := by
  intro i; unfold altDigits; split_ifs <;> simp

theorem altC_le (K : ℕ) : altC K ≤ K := by
  unfold altC
  exact (card_filter_le _ _).trans (card_range K).le

theorem altC_succ (K : ℕ) :
    altC (K + 1) = altC K + if Even (altBlock K) then 0 else 1 := by
  unfold altC
  rw [range_add_one, filter_insert]
  split_ifs with h
  · simp
  · rw [card_insert_of_notMem (by simp)]

/-- The product of the digit counts: `∏_{i<K} |D_i| = 2^(K - c_K) · 3^(c_K)`. -/
theorem prod_altDigits (K : ℕ) :
    ∏ i ∈ range K, (altDigits i).card = 2 ^ (K - altC K) * 3 ^ altC K := by
  induction K with
  | zero => simp [altC]
  | succ K ih =>
    rw [prod_range_succ, ih, altC_succ]
    have hle := altC_le K
    unfold altDigits
    split_ifs with h
    · simp only [add_zero]
      rw [show K + 1 - altC K = (K - altC K) + 1 by omega, pow_succ]
      simp; ring
    · rw [show K + 1 - (altC K + 1) = K - altC K by omega, pow_succ 3]
      simp; ring

/-- `prop:fr-alt`(i), count: `#A_K = 2^(a_K) 3^(c_K)` with `a_K = K - c_K`. -/
theorem card_altSet (K : ℕ) : (altSet K).card = 2 ^ (K - altC K) * 3 ^ altC K := by
  rw [altSet, card_digitSeqSet altDigits_lt, prod_altDigits]

/-- `prop:fr-alt`(i), box counts: for `j ≤ K`,
`NN (3^j) A_K = 2^(a_{K-j}) 3^(c_{K-j})`. -/
theorem NN_altSet {j K : ℕ} (hj : j ≤ K) :
    NN (3 ^ j) (altSet K) = 2 ^ ((K - j) - altC (K - j)) * 3 ^ altC (K - j) := by
  rw [altSet, NN_digitSeqSet altDigits_lt altDigits_nonempty hj, prod_altDigits]

/-- `prop:fr-alt`(ii): `dimGranule A_K (3^K) = (1 - c_K/K) λ + c_K/K` with
`λ = log 2 / log 3`, for `K ≥ 1`. -/
theorem dimGranule_altSet {K : ℕ} (hK : 0 < K) :
    dimGranule (altSet K) ((3 : ℝ) ^ K) =
      (1 - (altC K : ℝ) / K) * (Real.log 2 / Real.log 3) + (altC K : ℝ) / K := by
  have hle := altC_le K
  have hKr : (K : ℝ) ≠ 0 := by exact_mod_cast hK.ne'
  have hl3 : Real.log 3 ≠ 0 := by
    have := Real.log_pos (by norm_num : (1 : ℝ) < 3); exact this.ne'
  rw [dimGranule, card_altSet]
  push_cast
  rw [Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow, Real.log_pow,
    Nat.cast_sub hle]
  field_simp

/-- Inside block `k`, level `2^k - 1 + m` (`m < 2^k`) has block index `k`. -/
theorem altBlock_in_block (k m : ℕ) (hm : m < 2 ^ k) : altBlock (2 ^ k - 1 + m) = k := by
  unfold altBlock
  have h1 : 1 ≤ 2 ^ k := Nat.one_le_two_pow
  rw [show 2 ^ k - 1 + m + 1 = 2 ^ k + m by omega]
  refine Nat.log_eq_of_pow_le_of_lt_pow (by omega) ?_
  rw [pow_succ]; omega

/-- Counting along block `k`: `c_{2^k - 1 + m} = c_{2^k - 1} + [k odd] m` for `m ≤ 2^k`. -/
theorem altC_block (k m : ℕ) (hm : m ≤ 2 ^ k) :
    altC (2 ^ k - 1 + m) = altC (2 ^ k - 1) + if Even k then 0 else m := by
  induction m with
  | zero => split_ifs <;> simp
  | succ m ih =>
    rw [← add_assoc, altC_succ, ih (by omega), altBlock_in_block k m (by omega)]
    split_ifs <;> omega

/-- The count at block ends: with `K = 2^(k+1) - 1` (end of block `k`),
`3 c_K = 2 K` if `k` is odd and `3 c_K = K - 1` if `k` is even. -/
theorem altC_block_end (k : ℕ) :
    (¬ Even k → 3 * altC (2 ^ (k + 1) - 1) = 2 * (2 ^ (k + 1) - 1)) ∧
    (Even k → 3 * altC (2 ^ (k + 1) - 1) = 2 ^ (k + 1) - 1 - 1) := by
  induction k with
  | zero =>
    refine ⟨fun h => absurd (by decide) h, fun _ => ?_⟩
    decide
  | succ k ih =>
    have hp : 1 ≤ 2 ^ (k + 1) := Nat.one_le_two_pow
    have e : 2 ^ (k + 1 + 1) - 1 = 2 ^ (k + 1) - 1 + 2 ^ (k + 1) := by
      rw [pow_succ 2 (k + 1)]; omega
    rw [e, altC_block (k + 1) _ le_rfl]
    rcases Nat.even_or_odd k with hk | hk
    · have hk1 : ¬ Even (k + 1) := by rw [Nat.even_add_one]; exact not_not.2 hk
      have h2 := ih.2 hk
      refine ⟨fun _ => ?_, fun h => absurd h hk1⟩
      simp only [hk1, ↓reduceIte]
      omega
    · have hk' : ¬ Even k := Nat.not_even_iff_odd.2 hk
      have hk1 : Even (k + 1) := by rw [Nat.even_add_one]; exact hk'
      have h2 := ih.1 hk'
      refine ⟨fun h => absurd hk1 h, fun _ => ?_⟩
      simp only [hk1, ↓reduceIte, add_zero]
      omega

/-- `prop:fr-alt`(iii): at the end of a `{0,1,2}` block (`K = 2^(k+1) - 1`,
`k` odd), `c_K / K = 2/3` exactly and `dimGranule A_K (3^K) = λ/3 + 2/3`. -/
theorem altSet_dim_odd_block {k : ℕ} (hk : ¬ Even k) :
    let K := 2 ^ (k + 1) - 1
    (altC K : ℝ) / K = 2 / 3 ∧
      dimGranule (altSet K) ((3 : ℝ) ^ K) = (1 / 3) * (Real.log 2 / Real.log 3) + 2 / 3 := by
  intro K
  have hK : 0 < K := by
    have : 2 ≤ 2 ^ (k + 1) := by
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ (k + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    show 0 < 2 ^ (k + 1) - 1; omega
  have h3 : (3 : ℝ) * altC K = 2 * K := by exact_mod_cast (altC_block_end k).1 hk
  have hKr : (K : ℝ) ≠ 0 := by exact_mod_cast hK.ne'
  have hc : (altC K : ℝ) / K = 2 / 3 := by
    rw [div_eq_iff hKr]; linarith
  refine ⟨hc, ?_⟩
  rw [dimGranule_altSet hK, hc]; ring

/-- `prop:fr-alt`(iv): at the end of a `{0,2}` block (`K = 2^(k+1) - 1`, `k`
even), `c_K / K = 1/3 - η_K` with `η_K = 1/(3K)`, and
`dimGranule A_K (3^K) = (2/3) λ + 1/3 - η_K (1 - λ)`. -/
theorem altSet_dim_even_block {k : ℕ} (hk : Even k) :
    let K := 2 ^ (k + 1) - 1
    (altC K : ℝ) / K = 1 / 3 - 1 / (3 * K) ∧
      dimGranule (altSet K) ((3 : ℝ) ^ K) =
        (2 / 3) * (Real.log 2 / Real.log 3) + 1 / 3 -
          1 / (3 * K) * (1 - Real.log 2 / Real.log 3) := by
  intro K
  have hK : 0 < K := by
    have : 2 ≤ 2 ^ (k + 1) := by
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ (k + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    show 0 < 2 ^ (k + 1) - 1; omega
  have h3n : 3 * altC K = K - 1 := (altC_block_end k).2 hk
  have h3 : (3 : ℝ) * altC K = K - 1 := by
    have : (((K - 1 : ℕ)) : ℝ) = K - 1 := by rw [Nat.cast_sub (by omega)]; simp
    rw [← this]; exact_mod_cast h3n
  have hKr : (K : ℝ) ≠ 0 := by exact_mod_cast hK.ne'
  have hc : (altC K : ℝ) / K = 1 / 3 - 1 / (3 * K) := by
    field_simp; linarith
  refine ⟨hc, ?_⟩
  rw [dimGranule_altSet hK, hc]; ring

/-! ## J. The `b`-adic lattice is a sublattice of the factorial lattice -/

/-- `b^K` divides `(b K)!` for `b ≥ 1`. -/
theorem pow_dvd_factorial_mul (b K : ℕ) (hb : 1 ≤ b) : b ^ K ∣ (b * K).factorial := by
  induction K with
  | zero => simp
  | succ K ih =>
    have e : b * (K + 1) = (b * (K + 1) - 1) + 1 := by
      have : 1 ≤ b * (K + 1) := Nat.one_le_iff_ne_zero.2 (by positivity)
      omega
    have h1 : (b * K).factorial ∣ (b * (K + 1) - 1).factorial :=
      Nat.factorial_dvd_factorial (by rw [mul_add, mul_one]; omega)
    rw [pow_succ, e, Nat.factorial_succ, ← e, mul_comm (b * (K + 1))]
    exact mul_dvd_mul (ih.trans h1) (Dvd.intro (K + 1) rfl)

/-- If `M ≥ b K` then `b^K ∣ M!`. -/
theorem pow_dvd_factorial_of_le {b K M : ℕ} (hb : 1 ≤ b) (hM : b * K ≤ M) :
    b ^ K ∣ M.factorial :=
  (pow_dvd_factorial_mul b K hb).trans (Nat.factorial_dvd_factorial hM)

/-- The `b`-adic lattice is a sublattice of the `1/M!` lattice when `M ≥ b K`:
every `k / b^K` equals `m / M!` for the integer `m = k · (M! / b^K)`. -/
theorem badic_sub_factorial {b K M : ℕ} (hb : 1 ≤ b) (hM : b * K ≤ M) (k : ℤ) :
    ∃ m : ℤ, (k : ℚ) / (b : ℚ) ^ K = m / (M.factorial : ℚ) := by
  obtain ⟨q, hq⟩ := pow_dvd_factorial_of_le hb hM
  refine ⟨k * q, ?_⟩
  have hbK : (b : ℚ) ^ K ≠ 0 := pow_ne_zero _ (by exact_mod_cast (show b ≠ 0 by omega))
  have hq0 : (q : ℚ) ≠ 0 := by
    intro h
    have : q = 0 := by exact_mod_cast h
    rw [this, mul_zero] at hq; exact Nat.factorial_ne_zero M hq
  rw [hq]; push_cast
  field_simp

/-! ## K. The snapped set `{1/n}` (`ex:fr-inverse`) -/

/-- The lattice index of `1/n` snapped to the lattice of spacing `1/N` (nearest
point, ties up): `⌊N/n + 1/2⌋ = (2N + n) / (2n)`. -/
def snapInv (N n : ℕ) : ℕ := (2 * N + n) / (2 * n)

/-- `snapInv N n` is a nearest lattice index of `N/n`:
`N/n - 1/2 < snapInv N n ≤ N/n + 1/2`. -/
theorem snapInv_spec (N : ℕ) {n : ℕ} (hn : 0 < n) :
    (N : ℚ) / n - 1 / 2 < snapInv N n ∧ (snapInv N n : ℚ) ≤ N / n + 1 / 2 := by
  have h1 : 2 * n * snapInv N n ≤ 2 * N + n := by
    rw [mul_comm]; exact Nat.div_mul_le_self _ _
  have h2 : 2 * N + n < 2 * n * (snapInv N n + 1) := by
    exact Nat.lt_mul_div_succ _ (by omega)
  have hn' : (0 : ℚ) < n := by exact_mod_cast hn
  have h1' : (2 * n * snapInv N n : ℚ) ≤ 2 * N + n := by exact_mod_cast h1
  have h2' : (2 * N + n : ℚ) < 2 * n * (snapInv N n + 1) := by exact_mod_cast h2
  constructor
  · rw [div_sub' (by positivity), div_lt_iff₀ hn']; nlinarith
  · rw [div_add' _ _ _ (by positivity), le_div_iff₀ hn']; nlinarith

/-- The internal set `A` of `ex:fr-inverse`: `0` together with the snapped
points `⌊1/n⌉`, `1 ≤ n ≤ N`, as lattice indices. -/
def invSet (N : ℕ) : Finset ℕ := insert 0 ((Icc 1 N).image (snapInv N))

theorem snapInv_step {N n : ℕ} (hn : 1 ≤ n) (hN : n * (n + 1) ≤ N) :
    snapInv N (n + 1) < snapInv N n := by
  unfold snapInv
  set a := (2 * N + (n + 1)) / (2 * (n + 1))
  have ha : 2 * (n + 1) * a ≤ 2 * N + (n + 1) := by
    rw [mul_comm]; exact Nat.div_mul_le_self _ _
  rw [Nat.lt_iff_add_one_le, Nat.le_div_iff_mul_le (by omega)]
  by_contra hc
  replace hc := lt_of_not_ge hc
  have : (2 * N + n) * (n + 1) < (a + 1) * (2 * n) * (n + 1) :=
    Nat.mul_lt_mul_of_pos_right hc (by omega)
  nlinarith

theorem snapInv_strictAnti {N n m : ℕ} (hn : 1 ≤ n) (hnm : n < m)
    (hm : m ≤ Nat.sqrt N) : snapInv N m < snapInv N n := by
  induction m, hnm using Nat.le_induction with
  | base =>
    apply snapInv_step hn
    have := Nat.sqrt_le N
    nlinarith
  | succ m hm' ih =>
    refine lt_trans ?_ (ih (by omega))
    apply snapInv_step (by omega)
    have := Nat.sqrt_le N
    nlinarith

theorem snapInv_le {N n : ℕ} (hn : Nat.sqrt N + 1 ≤ n) : snapInv N n < Nat.sqrt N + 2 := by
  unfold snapInv
  rw [Nat.div_lt_iff_lt_mul (by omega)]
  have := Nat.lt_succ_sqrt N
  have h2 : (Nat.sqrt N + 1) * (Nat.sqrt N + 1) ≤ n * (Nat.sqrt N + 1) :=
    Nat.mul_le_mul_right _ hn
  nlinarith

theorem snapInv_pos {N n : ℕ} (hn : 1 ≤ n) (hnN : n ≤ N) : 1 ≤ snapInv N n := by
  unfold snapInv
  rw [Nat.le_div_iff_mul_le (by omega)]; omega

/-- `ex:fr-inverse`, exact count: for every `N`, with `s = ⌊√N⌋`,
`s + 1 ≤ #A ≤ 2 s + 2`. -/
theorem card_invSet (N : ℕ) :
    Nat.sqrt N + 1 ≤ (invSet N).card ∧ (invSet N).card ≤ 2 * Nat.sqrt N + 2 := by
  set s := Nat.sqrt N
  have hsN : s ≤ N := Nat.sqrt_le_self N
  constructor
  · have hsub : insert 0 ((Icc 1 s).image (snapInv N)) ⊆ invSet N :=
      insert_subset_insert _ (image_subset_image (Icc_subset_Icc le_rfl hsN))
    refine le_trans ?_ (card_le_card hsub)
    rw [card_insert_of_notMem, card_image_of_injOn, Nat.card_Icc, Nat.add_sub_cancel]
    · intro x hx y hy hxy
      simp only [coe_Icc, Set.mem_Icc] at hx hy
      by_contra hne
      rcases Nat.lt_or_gt_of_ne hne with h | h
      · exact (snapInv_strictAnti hx.1 h hy.2).ne' hxy
      · exact (snapInv_strictAnti hy.1 h hx.2).ne hxy
    · simp only [mem_image, mem_Icc, not_exists, not_and]
      intro x hx h
      have := snapInv_pos hx.1 (hx.2.trans hsN); omega
  · have hsub : invSet N ⊆ (Icc 1 s).image (snapInv N) ∪ range (s + 2) := by
      intro x hx
      simp only [invSet, mem_insert, mem_image, mem_Icc] at hx
      simp only [mem_union, mem_image, mem_Icc, mem_range]
      rcases hx with rfl | ⟨n, ⟨hn1, hnN⟩, rfl⟩
      · right; omega
      · by_cases hns : n ≤ s
        · left; exact ⟨n, ⟨hn1, hns⟩, rfl⟩
        · right; exact snapInv_le (by omega)
    refine (card_le_card hsub).trans ((card_union_le _ _).trans ?_)
    rw [card_range]
    have := card_image_le (s := Icc 1 s) (f := snapInv N)
    rw [Nat.card_Icc, Nat.add_sub_cancel] at this
    omega

/-- `ex:fr-inverse`, real form: `√N ≤ #A ≤ 2√N + 2`, hence `#A ≤ 3√N` for `N ≥ 4`. -/
theorem card_invSet_real (N : ℕ) :
    Real.sqrt N ≤ (invSet N).card ∧ ((invSet N).card : ℝ) ≤ 2 * Real.sqrt N + 2 ∧
      (4 ≤ N → ((invSet N).card : ℝ) ≤ 3 * Real.sqrt N) := by
  obtain ⟨h1, h2⟩ := card_invSet N
  have hlo : Real.sqrt N < (Nat.sqrt N : ℝ) + 1 := Real.real_sqrt_lt_nat_sqrt_succ
  have hhi : (Nat.sqrt N : ℝ) ≤ Real.sqrt N := Real.nat_sqrt_le_real_sqrt
  have h1' : ((Nat.sqrt N + 1 : ℕ) : ℝ) ≤ (invSet N).card := by exact_mod_cast h1
  have h2' : ((invSet N).card : ℝ) ≤ ((2 * Nat.sqrt N + 2 : ℕ) : ℝ) := by exact_mod_cast h2
  push_cast at h1' h2'
  refine ⟨by linarith, by linarith, fun h4 => ?_⟩
  have : (2 : ℝ) ≤ Real.sqrt N := by
    rw [show (2 : ℝ) = Real.sqrt 4 by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt (by exact_mod_cast h4)
  linarith

/-! ## L. The granular devil's staircase (`def:fr-staircase`, `prop:fr-staircase`) -/

/-- Every element of a digit set of level `K` is `< b^K` (digits `< b`). -/
theorem digitSet_lt {b : ℕ} {D : Finset ℕ} (hD : ∀ d ∈ D, d < b) (K : ℕ) :
    ∀ x ∈ digitSet b D K, x < b ^ K := by
  induction K with
  | zero => simp
  | succ K ih =>
    intro x hx
    rw [digitSet_succ] at hx
    simp only [mem_image, mem_product, Prod.exists] at hx
    obtain ⟨y, d, ⟨hy, hd⟩, rfl⟩ := hx
    have h1 := ih y hy
    have h2 := hD d hd
    rw [pow_succ]
    calc b * y + d < b * y + b := by omega
      _ = b * (y + 1) := by ring
      _ ≤ b * b ^ K := Nat.mul_le_mul_left _ h1
      _ = b ^ K * b := by ring

theorem cantor_lt (K : ℕ) : ∀ x ∈ cantor K, x < 3 ^ K :=
  digitSet_lt (by decide) K

theorem mem_digitSet_succ {b : ℕ} {D : Finset ℕ} {K x : ℕ} :
    x ∈ digitSet b D (K + 1) ↔ ∃ y ∈ digitSet b D K, ∃ d ∈ D, x = b * y + d := by
  rw [digitSet_succ]
  simp only [mem_image, mem_product, Prod.exists]
  constructor
  · rintro ⟨y, d, ⟨hy, hd⟩, rfl⟩; exact ⟨y, hy, d, hd, rfl⟩
  · rintro ⟨y, hy, d, hd, rfl⟩; exact ⟨y, d, ⟨hy, hd⟩, rfl⟩

/-- Top-digit decomposition of a digit set: the elements of level `K+1` are the
`e b^K + y` with `e ∈ D` (the most significant digit) and `y` at level `K`. -/
theorem mem_digitSet_succ_top {b : ℕ} {D : Finset ℕ} :
    ∀ {K x : ℕ}, x ∈ digitSet b D (K + 1) ↔ ∃ e ∈ D, ∃ y ∈ digitSet b D K, x = e * b ^ K + y
  | 0, x => by
    rw [mem_digitSet_succ]
    simp only [digitSet_zero, mem_singleton, pow_zero, mul_one]
    constructor
    · rintro ⟨y, rfl, d, hd, rfl⟩; exact ⟨d, hd, 0, rfl, by ring⟩
    · rintro ⟨e, he, y, rfl, hx⟩; exact ⟨0, rfl, e, he, by rw [hx]; ring⟩
  | K + 1, x => by
    rw [mem_digitSet_succ]
    constructor
    · rintro ⟨z, hz, d, hd, rfl⟩
      obtain ⟨e, he, y, hy, rfl⟩ := mem_digitSet_succ_top.1 hz
      exact ⟨e, he, b * y + d, mem_digitSet_succ.2 ⟨y, hy, d, hd, rfl⟩, by ring⟩
    · rintro ⟨e, he, w, hw, rfl⟩
      obtain ⟨y, hy, d, hd, rfl⟩ := mem_digitSet_succ.1 hw
      exact ⟨e * b ^ K + y, mem_digitSet_succ_top.2 ⟨e, he, y, hy, rfl⟩, d, hd, by ring⟩

/-- Top-digit decomposition of the Cantor set:
`C_{K+1} = C_K ∪ (2·3^K + C_K)`. -/
theorem cantor_succ_eq (K : ℕ) :
    cantor (K + 1) = cantor K ∪ (cantor K).image (2 * 3 ^ K + ·) := by
  ext x
  simp only [cantor, mem_union, mem_image]
  rw [mem_digitSet_succ_top]
  simp only [mem_insert, mem_singleton]
  constructor
  · rintro ⟨e, he | he, y, hy, rfl⟩
    · left; simpa [he] using hy
    · right; exact ⟨y, hy, by rw [he]⟩
  · rintro (h | ⟨y, hy, rfl⟩)
    · exact ⟨0, Or.inl rfl, x, h, by ring⟩
    · exact ⟨2, Or.inr rfl, y, hy, rfl⟩

/-- The number of points of `C_K` below `k`. -/
def cantorCount (K k : ℕ) : ℕ := ((cantor K).filter (· < k)).card

/-- The granular devil's staircase `F_K(k) = #{c ∈ C_K : c < k} / 2^K`. -/
def stair (K k : ℕ) : ℚ := (cantorCount K k : ℚ) / 2 ^ K

theorem cantorCount_zero (K : ℕ) : cantorCount K 0 = 0 := by
  simp [cantorCount]

theorem cantorCount_of_le {K k : ℕ} (hk : 3 ^ K ≤ k) : cantorCount K k = 2 ^ K := by
  unfold cantorCount
  rw [filter_true_of_mem (fun x hx => (cantor_lt K x hx).trans_le hk), card_cantorSet]

/-- Recursion of the count: `#{c ∈ C_{K+1}, c < k} = #{c ∈ C_K, c < k} + #{c ∈ C_K, c < k - 2·3^K}`. -/
theorem cantorCount_succ (K k : ℕ) :
    cantorCount (K + 1) k = cantorCount K k + cantorCount K (k - 2 * 3 ^ K) := by
  unfold cantorCount
  rw [cantor_succ_eq, filter_union, card_union_of_disjoint]
  · congr 1
    rw [filter_image, card_image_of_injective _ (fun a b h => by simpa using h)]
    congr 1
    apply filter_congr
    intro x _
    show 2 * 3 ^ K + x < k ↔ x < k - 2 * 3 ^ K
    omega
  · rw [disjoint_left]
    intro x hx hx'
    simp only [mem_filter, mem_image] at hx hx'
    obtain ⟨y, _, rfl⟩ := hx'.1
    have := cantor_lt K _ hx.1
    omega

/-- `prop:fr-staircase`(i): `F_K(0) = 0`, `F_K(3^K) = 1`, and `2^K F_K(k)` is a
natural number. -/
theorem stair_zero (K : ℕ) : stair K 0 = 0 := by simp [stair, cantorCount_zero]

theorem stair_top (K : ℕ) : stair K (3 ^ K) = 1 := by
  rw [stair, cantorCount_of_le le_rfl]; simp

theorem stair_denom (K k : ℕ) : ∃ n : ℕ, stair K k = n / 2 ^ K := ⟨_, rfl⟩

/-- The staircase is monotone. -/
theorem stair_mono (K : ℕ) : Monotone (stair K) := by
  intro k k' h
  unfold stair cantorCount
  gcongr

/-- `prop:fr-staircase`(ii): `F_K(k+1) - F_K(k) = 2^{-K}` if `k ∈ C_K`, else `0`. -/
theorem stair_jump (K k : ℕ) :
    stair K (k + 1) - stair K k = if k ∈ cantor K then 1 / 2 ^ K else 0 := by
  unfold stair cantorCount
  have e : (cantor K).filter (· < k + 1) =
      (cantor K).filter (· < k) ∪ (cantor K).filter (· = k) := by
    rw [← filter_or]; apply filter_congr; intro x _; omega
  have hd : Disjoint ((cantor K).filter (· < k)) ((cantor K).filter (· = k)) := by
    rw [disjoint_filter]; intro x _ h; omega
  rw [e, card_union_of_disjoint hd]
  have : ((cantor K).filter (· = k)).card = if k ∈ cantor K then 1 else 0 := by
    split_ifs with h
    · rw [card_eq_one]
      exact ⟨k, by
        ext x; simp only [mem_filter, mem_singleton]
        exact ⟨fun h' => h'.2, fun h' => ⟨h' ▸ h, h'⟩⟩⟩
    · rw [card_eq_zero, filter_eq_empty_iff]; intro x hx hxk; exact h (hxk ▸ hx)
  rw [this]
  split_ifs <;> push_cast <;> ring

/-- There are exactly `2^K` jumps: `#{k < 3^K : k ∈ C_K} = 2^K`. -/
theorem stair_card_jumps (K : ℕ) : ((range (3 ^ K)).filter (· ∈ cantor K)).card = 2 ^ K := by
  rw [← card_cantorSet K]
  congr 1
  ext x; simp only [mem_filter, mem_range]
  exact ⟨fun h => h.2, fun h => ⟨cantor_lt K x h, h⟩⟩

/-- Self-similarity: `F_{K+1}(k) = F_K(k)/2 + F_K(k - 2·3^K)/2`. -/
theorem stair_succ (K k : ℕ) :
    stair (K + 1) k = stair K k / 2 + stair K (k - 2 * 3 ^ K) / 2 := by
  unfold stair; rw [cantorCount_succ]; push_cast; rw [pow_succ]; ring

/-- `prop:fr-staircase`(iii): `F_K(k) = 1/2` for `3^{K-1} ≤ k ≤ 2·3^{K-1}` (`K ≥ 1`). -/
theorem stair_middle {K k : ℕ} (hK : 1 ≤ K) (h1 : 3 ^ (K - 1) ≤ k) (h2 : k ≤ 2 * 3 ^ (K - 1)) :
    stair K k = 1 / 2 := by
  obtain ⟨K, rfl⟩ : ∃ K', K = K' + 1 := ⟨K - 1, by omega⟩
  simp only [Nat.add_sub_cancel] at h1 h2
  rw [stair_succ, show k - 2 * 3 ^ K = 0 by omega, stair_zero, stair, cantorCount_of_le h1]
  push_cast; field_simp; norm_num

/-- The `i`-th ternary digit (most significant first, `0`-based) of `k` written
with `K` digits: `d_{i+1} = ⌊k / 3^{K-1-i}⌋ mod 3`. -/
def tdigit (K k i : ℕ) : ℕ := k / 3 ^ (K - 1 - i) % 3

/-- The term of digit `i` in the Cantor function's digit formula:
`2^{-(i+1)}` if `d_{i+1} = 1`, else `(d_{i+1}/2) 2^{-(i+1)}`. -/
def cantorTerm (K k i : ℕ) : ℚ :=
  if tdigit K k i = 1 then (1 / 2) ^ (i + 1) else (tdigit K k i : ℚ) / 2 * (1 / 2) ^ (i + 1)

/-- The classical Cantor function at the triadic rational `k / 3^K`, by its digit
formula: with `m` the first index with `d_m = 1`,
`Φ = ∑_{i<m} (d_i/2) 2^{-i} + 2^{-m}`, or `∑_{i≤K} (d_i/2) 2^{-i}` if there is no
such `m`; and `Φ(1) = 1`.  The sum keeps the terms whose earlier digits are all
`≠ 1`. -/
def cantorFn (K k : ℕ) : ℚ :=
  if 3 ^ K ≤ k then 1 else
    ∑ i ∈ range K, if (∀ j ∈ range i, tdigit K k j ≠ 1) then cantorTerm K k i else 0

theorem tdigit_succ_zero {K k : ℕ} (hk : k < 3 ^ (K + 1)) : tdigit (K + 1) k 0 = k / 3 ^ K := by
  unfold tdigit
  simp only [Nat.add_sub_cancel, Nat.sub_zero]
  apply Nat.mod_eq_of_lt
  rw [Nat.div_lt_iff_lt_mul (by positivity)]; rw [pow_succ] at hk; omega

theorem tdigit_succ_succ {K k i : ℕ} (hi : i < K) :
    tdigit (K + 1) k (i + 1) = tdigit K (k % 3 ^ K) i := by
  unfold tdigit
  have e : K + 1 - 1 - (i + 1) = K - 1 - i := by omega
  rw [e]
  set m := K - 1 - i
  have hp : 3 ^ K = 3 ^ m * 3 ^ (i + 1) := by rw [← pow_add]; congr 1; omega
  conv_lhs => rw [← Nat.div_add_mod k (3 ^ K)]
  rw [hp, show 3 ^ m * 3 ^ (i + 1) * (k / (3 ^ m * 3 ^ (i + 1))) + k % (3 ^ m * 3 ^ (i + 1)) =
      k % (3 ^ m * 3 ^ (i + 1)) + 3 ^ m * (3 ^ (i + 1) * (k / (3 ^ m * 3 ^ (i + 1)))) by ring,
    Nat.add_mul_div_left _ _ (by positivity), pow_succ]
  rw [show 3 ^ i * 3 * (k / (3 ^ m * (3 ^ i * 3))) = 3 * (3 ^ i * (k / (3 ^ m * (3 ^ i * 3))))
    by ring, Nat.add_mul_mod_self_left]

/-- Top-digit recursion of the digit formula: for `k < 3^{K+1}` with top digit
`d = ⌊k/3^K⌋` and rest `s = k mod 3^K`: `Φ_{K+1}(k) = 1/2` if `d = 1`, and
`Φ_{K+1}(k) = d/4 + Φ_K(s)/2` otherwise. -/
theorem cantorFn_succ {K k : ℕ} (hk : k < 3 ^ (K + 1)) :
    cantorFn (K + 1) k =
      if k / 3 ^ K = 1 then 1 / 2 else (k / 3 ^ K : ℕ) / 4 + cantorFn K (k % 3 ^ K) / 2 := by
  have hs : ¬ 3 ^ K ≤ k % 3 ^ K := not_le.2 (Nat.mod_lt _ (by positivity))
  unfold cantorFn
  simp only [not_le.2 hk, hs, ↓reduceIte]
  rw [sum_range_succ']
  have h0 := tdigit_succ_zero hk
  have hd : k / 3 ^ K < 3 := by
    rw [Nat.div_lt_iff_lt_mul (by positivity)]; rw [pow_succ] at hk; omega
  simp only [range_zero, notMem_empty, IsEmpty.forall_iff, forall_const, ↓reduceIte]
  have hcond : ∀ i ∈ range K, ((∀ j ∈ range (i + 1), tdigit (K + 1) k j ≠ 1) ↔
      (k / 3 ^ K ≠ 1 ∧ ∀ j ∈ range i, tdigit K (k % 3 ^ K) j ≠ 1)) := by
    intro i hi
    rw [mem_range] at hi
    constructor
    · intro h
      refine ⟨h0 ▸ h 0 (by simp), fun j hj => ?_⟩
      rw [mem_range] at hj
      rw [← tdigit_succ_succ (by omega)]; exact h (j + 1) (by simp; omega)
    · rintro ⟨h1, h2⟩ j hj
      rw [mem_range] at hj
      rcases j with _ | j
      · rw [h0]; exact h1
      · rw [tdigit_succ_succ (by omega)]; exact h2 j (by simp; omega)
  have hterm : ∀ i ∈ range K, cantorTerm (K + 1) k (i + 1) = cantorTerm K (k % 3 ^ K) i / 2 := by
    intro i hi
    rw [mem_range] at hi
    unfold cantorTerm
    rw [tdigit_succ_succ hi]
    split_ifs <;> ring
  rw [sum_congr rfl (fun i hi => by rw [if_congr (hcond i hi) rfl rfl, hterm i hi])]
  unfold cantorTerm
  rw [h0]
  split_ifs with h1
  · simp [h1]
  · simp only [h1, ne_eq, not_false_eq_true, true_and]
    rw [sum_div, add_comm]
    congr 1
    · ring
    · apply sum_congr rfl; intro i _; split_ifs <;> ring

/-- `prop:fr-staircase`(iv): the granular staircase equals the classical Cantor
function (digit formula) at every triadic lattice point:
`F_K(k) = Φ(k 3^{-K})` for `0 ≤ k ≤ 3^K`. -/
theorem stair_eq_cantorFn (K : ℕ) : ∀ k ≤ 3 ^ K, stair K k = cantorFn K k := by
  induction K with
  | zero =>
    intro k hk
    rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hk with rfl | rfl
    · simp [stair_zero, cantorFn]
    · rw [show (1 : ℕ) = 3 ^ 0 by rfl, stair_top]; simp [cantorFn]
  | succ K ih =>
    intro k hk
    rcases hk.lt_or_eq with hk | rfl
    · rw [cantorFn_succ hk, stair_succ]
      have hd : k / 3 ^ K < 3 := by
        rw [Nat.div_lt_iff_lt_mul (by positivity)]; rw [pow_succ] at hk; omega
      have hdm := Nat.div_add_mod k (3 ^ K)
      have hs : k % 3 ^ K < 3 ^ K := Nat.mod_lt _ (by positivity)
      have hP : (0 : ℚ) < 2 ^ K := by positivity
      interval_cases hq : k / 3 ^ K
      · -- top digit 0: k < 3^K
        have hk' : k = k % 3 ^ K := by omega
        rw [show k - 2 * 3 ^ K = 0 by omega, stair_zero, ← ih _ hs.le, ← hk']
        simp
      · -- top digit 1
        rw [show k - 2 * 3 ^ K = 0 by omega, stair_zero, stair, cantorCount_of_le (by omega)]
        simp only [↓reduceIte]; push_cast; field_simp; norm_num
      · -- top digit 2
        rw [show k - 2 * 3 ^ K = k % 3 ^ K by omega, ih _ hs.le, stair, cantorCount_of_le (by omega)]
        simp only [show (2 : ℕ) ≠ 1 by decide, ↓reduceIte]; push_cast; field_simp; ring
    · rw [stair_top]; simp [cantorFn]

/-- `prop:fr-staircase`(v), derivative: on the lattice `gh = 3^{-K}`, the granular
derivative `(F_K(k+1) - F_K(k)) / 3^{-K}` is `(3/2)^K` on `C_K` and `0` elsewhere. -/
theorem stair_Dp (K k : ℕ) :
    (stair K (k + 1) - stair K k) / (1 / 3 ^ K) = if k ∈ cantor K then (3 / 2) ^ K else 0 := by
  rw [stair_jump]
  split_ifs
  · rw [div_pow]; field_simp
  · simp

/-- `prop:fr-staircase`(v), exact FTC: `∑_{k<3^K} D⁺F_K(k) · 3^{-K} = 1 = F_K(3^K) - F_K(0)`. -/
theorem stair_ftc (K : ℕ) :
    ∑ k ∈ range (3 ^ K), (stair K (k + 1) - stair K k) / (1 / 3 ^ K) * (1 / 3 ^ K) = 1 ∧
      stair K (3 ^ K) - stair K 0 = 1 := by
  have h3 : (1 / 3 ^ K : ℚ) ≠ 0 := by positivity
  have e : ∑ k ∈ range (3 ^ K), (stair K (k + 1) - stair K k) / (1 / 3 ^ K) * (1 / 3 ^ K) =
      stair K (3 ^ K) - stair K 0 := by
    rw [← sum_range_sub (stair K)]
    exact sum_congr rfl fun k _ => div_mul_cancel₀ _ h3
  rw [e, stair_top, stair_zero]; norm_num

/-- `prop:fr-staircase`(v), as a sum of the derivative values: the derivative
`(3/2)^K` on the `2^K` points of `C_K`, each of content `3^{-K}`, sums to `1`. -/
theorem stair_Dp_sum (K : ℕ) :
    ∑ k ∈ range (3 ^ K), (if k ∈ cantor K then ((3 : ℚ) / 2) ^ K else 0) * (1 / 3 ^ K) = 1 := by
  refine Eq.trans (sum_congr rfl fun k _ => ?_) (stair_ftc K).1
  rw [stair_Dp]

/-! ## M. Dragon curves are exact up to depth `2K` (`ex:fr-dragon`) -/

section Dragon

open Complex

/-- A Gaussian integer, i.e. a vector of the square lattice `ℤ + ℤ i ⊆ ℂ`. -/
def IsGauss (z : ℂ) : Prop := ∃ a b : ℤ, z = a + b * I

theorem IsGauss.mul {z w : ℂ} (hz : IsGauss z) (hw : IsGauss w) : IsGauss (z * w) := by
  obtain ⟨a, b, rfl⟩ := hz
  obtain ⟨c, d, rfl⟩ := hw
  exact ⟨a * c - b * d, a * d + b * c, by push_cast; linear_combination ((b : ℂ) * d) * I_sq⟩

theorem isGauss_two_pow (n : ℕ) : IsGauss ((2 : ℂ) ^ n) :=
  ⟨2 ^ n, 0, by push_cast; ring⟩

/-- The dragon generator factor: `(1 + i)/2` for `true`, `(1 - i)/2` for `false`. -/
noncomputable def dt (s : Bool) : ℂ := if s then (1 + I) / 2 else (1 - I) / 2

theorem one_sub_dt (s : Bool) : 1 - dt s = dt (!s) := by
  cases s <;> simp [dt] <;> ring

theorem isGauss_two_dt (a : Bool) : IsGauss (2 * dt a) := by
  cases a
  · exact ⟨1, -1, by simp [dt]; ring⟩
  · exact ⟨1, 1, by simp [dt]; ring⟩

/-- Two steps multiply by `(1 ± i)(1 ± i)/4 ∈ {1/2, ± i/2}`: `2 · dt a · dt b`
is a Gaussian unit. -/
theorem isGauss_two_dt_dt (a b : Bool) : IsGauss (2 * (dt a * dt b)) := by
  cases a <;> cases b
  · exact ⟨0, -1, by simp [dt]; linear_combination ((1 : ℂ) / 2) * I_sq⟩
  · exact ⟨1, 0, by simp [dt]; linear_combination (-(1 : ℂ) / 2) * I_sq⟩
  · exact ⟨1, 0, by simp [dt]; linear_combination (-(1 : ℂ) / 2) * I_sq⟩
  · exact ⟨0, 1, by simp [dt]; linear_combination ((1 : ℂ) / 2) * I_sq⟩

theorem isGauss_prod_dt : ∀ l : List Bool, IsGauss (2 ^ ((l.length + 1) / 2) * (l.map dt).prod)
  | [] => ⟨1, 0, by simp⟩
  | [a] => by simpa using isGauss_two_dt a
  | a :: b :: l => by
    have h := (isGauss_two_dt_dt a b).mul (isGauss_prod_dt l)
    have e : (l.length + 1 + 1 + 1) / 2 = (l.length + 1) / 2 + 1 := by omega
    simp only [List.length_cons, List.map_cons, List.prod_cons, e, pow_succ]
    convert h using 1; ring

/-- Every product of at most `2K` dragon factors, times `2^K`, is a lattice vector. -/
theorem isGauss_letter (K : ℕ) (l : List Bool) (hl : l.length ≤ 2 * K) :
    IsGauss ((2 : ℂ) ^ K * (l.map dt).prod) := by
  have h := (isGauss_two_pow (K - (l.length + 1) / 2)).mul (isGauss_prod_dt l)
  convert h using 1
  rw [← mul_assoc, ← pow_add, show K - (l.length + 1) / 2 + (l.length + 1) / 2 = K by omega]

/-- One step of the segment-wise snapped dragon D0L: a letter `v` of type `s`
becomes `snap (t_s v)` and `v - snap (t_s v)`, of types `(g s).1` and `(g s).2`
(`g` codes the orientations: constant for the Lévy C curve, alternating for the
Heighway dragon). -/
noncomputable def dStep (sn : ℂ → ℂ) (g : Bool → Bool × Bool) (w : List (ℂ × Bool)) :
    List (ℂ × Bool) :=
  w.flatMap fun p => [(sn (dt p.2 * p.1), (g p.2).1), (p.1 - sn (dt p.2 * p.1), (g p.2).2)]

/-- The depth-`k` word, from the base letter `e` of type `s₀`. -/
noncomputable def dWord (sn : ℂ → ℂ) (g : Bool → Bool × Bool) (e : ℂ) (s₀ : Bool) (k : ℕ) :
    List (ℂ × Bool) :=
  (dStep sn g)^[k] [(e, s₀)]

theorem dStep_congr (sn : ℂ → ℂ) (g : Bool → Bool × Bool) (w : List (ℂ × Bool))
    (h : ∀ p ∈ w, sn (dt p.2 * p.1) = dt p.2 * p.1) : dStep sn g w = dStep id g w := by
  induction w with
  | nil => rfl
  | cons p w ih =>
    simp only [dStep, List.flatMap_cons] at ih ⊢
    rw [h p (by simp), ih (fun q hq => h q (by simp [hq]))]
    rfl

/-- The classical (unsnapped) depth-`k` letters are `e · ∏ (k dragon factors)`. -/
theorem dWord_classical (g : Bool → Bool × Bool) (e : ℂ) (s₀ : Bool) (k : ℕ) :
    ∀ p ∈ dWord id g e s₀ k, ∃ l : List Bool, l.length = k ∧ p.1 = e * (l.map dt).prod := by
  induction k with
  | zero => intro p hp; simp [dWord] at hp; exact ⟨[], rfl, by simp [hp]⟩
  | succ k ih =>
    intro p hp
    simp only [dWord, Function.iterate_succ_apply', dStep, List.mem_flatMap] at hp
    obtain ⟨q, hq, hpq⟩ := hp
    obtain ⟨l, hl, hql⟩ := ih q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false, id] at hpq
    rcases hpq with rfl | rfl
    · exact ⟨q.2 :: l, by simp [hl], by simp [hql]; ring⟩
    · refine ⟨(!q.2) :: l, by simp [hl], ?_⟩
      simp only [List.map_cons, List.prod_cons, ← one_sub_dt, hql]; ring

/-- `ex:fr-dragon`: with base `e = 2^K` and any snap map fixing the lattice
vectors, the segment-wise snapped dragon word equals the classical word at every
depth `k ≤ 2K` (both orientations, any orientation coding `g`): no rounding
occurs, and the granular vertices (partial sums) are the classical vertices. -/
theorem dragon_exact (K : ℕ) (sn : ℂ → ℂ) (hsn : ∀ z, IsGauss z → sn z = z)
    (g : Bool → Bool × Bool) (s₀ : Bool) {k : ℕ} (hk : k ≤ 2 * K) :
    dWord sn g ((2 : ℂ) ^ K) s₀ k = dWord id g ((2 : ℂ) ^ K) s₀ k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    simp only [dWord, Function.iterate_succ_apply'] at ih ⊢
    rw [ih (by omega)]
    apply dStep_congr
    intro p hp
    obtain ⟨l, hl, hpl⟩ := dWord_classical g _ s₀ k p hp
    apply hsn
    have := isGauss_letter K (p.2 :: l) (by simp [hl]; omega)
    convert this using 1
    simp [hpl]; ring

/-- `ex:fr-dragon`: every letter of the depth-`k` dragon word, `k ≤ 2K`, is a
lattice vector. -/
theorem dragon_letters_lattice (K : ℕ) (g : Bool → Bool × Bool) (s₀ : Bool) {k : ℕ}
    (hk : k ≤ 2 * K) : ∀ p ∈ dWord id g ((2 : ℂ) ^ K) s₀ k, IsGauss p.1 := by
  intro p hp
  obtain ⟨l, hl, hpl⟩ := dWord_classical g _ s₀ k p hp
  rw [hpl]; exact isGauss_letter K l (by omega)

end Dragon

/-! ## N. Shadow of the segment-wise snapped curve (`thm:fr-segment-shadow`) -/

section SegmentShadow

open Filter Topology Metric Bornology

/-- The exponent `α = log c / log (1/r)` of `thm:fr-segment-shadow`. -/
noncomputable def snapAlpha (c r : ℝ) : ℝ := Real.log c / Real.log (1 / r)

theorem snapAlpha_pos {c r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) (hc : 1 < c) : 0 < snapAlpha c r :=
  div_pos (Real.log_pos hc) (Real.log_pos (by rw [lt_div_iff₀ hr0]; linarith))

/-- `c r < 1` means `α < 1`. -/
theorem snapAlpha_lt_one {c r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) (hc : 0 < c) (hcr : c * r < 1) :
    snapAlpha c r < 1 := by
  have h1r : c < 1 / r := by rw [lt_div_iff₀ hr0]; exact hcr
  have hl : 0 < Real.log (1 / r) := Real.log_pos (by rw [lt_div_iff₀ hr0]; linarith)
  rw [snapAlpha, div_lt_one hl]
  exact Real.log_lt_log hc h1r

/-- `r^{-α} = c`. -/
theorem rpow_neg_snapAlpha {c r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) (hc : 0 < c) :
    r ^ (-snapAlpha c r) = c := by
  have hl : Real.log (1 / r) ≠ 0 := (Real.log_pos (by rw [lt_div_iff₀ hr0]; linarith)).ne'
  rw [Real.rpow_def_of_pos hr0, snapAlpha, one_div, Real.log_inv] at *
  rw [show Real.log r * -(Real.log c / -Real.log r) = Real.log c by
      have : Real.log r ≠ 0 := fun h => hl (by rw [h, neg_zero])
      field_simp,
    Real.exp_log hc]

/-- The granule-depth estimate: if `K ≥ 1` and `gh < r^{K-1}` (minimality of the
granule depth `K`), then `c^K < (r gh)^{-α}` (`0 < r < 1 < c`). -/
theorem pow_lt_granule {r c ε : ℝ} (hr0 : 0 < r) (hr1 : r < 1) (hc : 1 < c) (hε : 0 < ε)
    {K : ℕ} (hK1 : 1 ≤ K) (hK : ε < r ^ (K - 1)) :
    c ^ K < (r * ε) ^ (-snapAlpha c r) := by
  have hα := snapAlpha_pos hr0 hr1 hc
  have hc' := rpow_neg_snapAlpha hr0 hr1 (by linarith : 0 < c)
  set α := snapAlpha c r
  have e : c ^ K = (r ^ K) ^ (-α) := by
    calc c ^ K = (r ^ (-α)) ^ K := by rw [hc']
      _ = r ^ (-α * K) := (Real.rpow_mul_natCast hr0.le _ _).symm
      _ = (r ^ K) ^ (-α) := by rw [← Real.rpow_natCast, ← Real.rpow_mul hr0.le, mul_comm]
  have hlt : r * ε < r ^ K := by
    calc r * ε < r * r ^ (K - 1) := mul_lt_mul_of_pos_left hK hr0
      _ = r ^ K := by rw [← pow_succ']; congr 1; omega
  rw [e]
  exact Real.rpow_lt_rpow_of_neg (by positivity) hlt (by linarith)

/-- The vertex error at the granule depth: under the error recursion
`e 0 = 0`, `e (k+1) ≤ c e k + δ` with `δ ≥ 0`, `1 < c`, and the granule depth
`K` (`K ≥ 1`, `gh < r^{K-1}`): `e K ≤ δ (r gh)^{-α} / (c - 1)`. -/
theorem snap_error_granule {r c δ ε : ℝ} (hr0 : 0 < r) (hr1 : r < 1) (hc : 1 < c)
    (hδ : 0 ≤ δ) (hε : 0 < ε) {K : ℕ} (hK1 : 1 ≤ K) (hK : ε < r ^ (K - 1))
    (e : ℕ → ℝ) (h0 : e 0 = 0) (hrec : ∀ k, e (k + 1) ≤ c * e k + δ) :
    e K ≤ δ * (r * ε) ^ (-snapAlpha c r) / (c - 1) := by
  have h := error_recursion_closed e h0 (by linarith) hc.ne' hrec K
  have hc1 : 0 < c - 1 := by linarith
  refine h.trans ?_
  rw [div_le_div_iff_of_pos_right hc1]
  have := pow_lt_granule hr0 hr1 hc hε hK1 hK
  nlinarith

/-- `thm:fr-segment-shadow`, finitary form with `δ = √2 gr = gh/√2`:
`E_K < r^{-α} / (√2 (c - 1)) · gh^{1-α}`. -/
theorem snap_error_granule_rpow {r c ε : ℝ} (hr0 : 0 < r) (hr1 : r < 1) (hc : 1 < c)
    (hε : 0 < ε) {K : ℕ} (hK1 : 1 ≤ K) (hK : ε < r ^ (K - 1))
    (e : ℕ → ℝ) (h0 : e 0 = 0) (hrec : ∀ k, e (k + 1) ≤ c * e k + ε / Real.sqrt 2) :
    e K < r ^ (-snapAlpha c r) / (Real.sqrt 2 * (c - 1)) * ε ^ (1 - snapAlpha c r) := by
  have h := error_recursion_closed e h0 (by linarith) hc.ne' hrec K
  have hc1 : 0 < c - 1 := by linarith
  have hs : 0 < Real.sqrt 2 := by positivity
  have hpow := pow_lt_granule hr0 hr1 hc hε hK1 hK
  have e1 : r ^ (-snapAlpha c r) / (Real.sqrt 2 * (c - 1)) * ε ^ (1 - snapAlpha c r) =
      ε / Real.sqrt 2 * (r * ε) ^ (-snapAlpha c r) / (c - 1) := by
    rw [Real.mul_rpow hr0.le hε.le, Real.rpow_sub hε, Real.rpow_one, Real.rpow_neg hε.le,
      Real.rpow_neg hr0.le]
    field_simp
  rw [e1]
  refine h.trans_lt ?_
  rw [div_lt_div_iff_of_pos_right hc1]
  have : 0 < ε / Real.sqrt 2 := by positivity
  nlinarith

/-- An infinitesimal `Hyperreal.ofSeq f` (positive Archimedean class) is a sequence tending
to `0` along the hyperfilter. -/
theorem tendsto_of_infinitesimal {f : ℕ → ℝ} (h : 0 < ArchimedeanClass.mk (Hyperreal.ofSeq f)) :
    Tendsto f (hyperfilter ℕ : Filter ℕ) (𝓝 0) := by
  rw [Metric.tendsto_nhds]
  intro η hη
  have hη0 : ArchimedeanClass.mk ((η : ℝ) : Hyperreal) = 0 := Hyperreal.archimedeanClassMk_coe hη.ne'
  have h1 := (ArchimedeanClass.mk_lt_mk.1 (hη0 ▸ h)) 1
  rw [one_smul, ← Hyperreal.coe_abs, abs_of_pos hη] at h1
  have h2 := abs_lt.1 h1
  have hlo : ∀ᶠ n in (hyperfilter ℕ : Filter ℕ), -η < f n := by
    have : ((-η : ℝ) : Hyperreal) < Hyperreal.ofSeq f := by rw [Hyperreal.coe_neg]; exact h2.1
    exact Germ.coe_lt.1 this
  have hhi : ∀ᶠ n in (hyperfilter ℕ : Filter ℕ), f n < η := Germ.coe_lt.1 h2.2
  filter_upwards [hlo, hhi] with n h3 h4
  rw [Real.dist_eq, sub_zero, abs_lt]; exact ⟨h3, h4⟩

/-- `thm:fr-segment-shadow`, infinitesimal step: let `gh = [ε_n]` be a positive
infinitesimal, `K = [K_n]` with `K_n ≥ 1` and `ε_n < r^{K_n - 1}` (the granule
depth), and let the vertex errors satisfy `e_n 0 = 0`, `e_n k ≥ 0`,
`e_n (k+1) ≤ c e_n k + δ_n` with `0 ≤ δ_n ≤ C ε_n`.  If `0 < r < 1` and
`c r < 1` (all standard), then `E_K = [e_n (K_n)]` tends to `0` along the
hyperfilter, i.e. is infinitesimal. -/
theorem snap_error_tendsto {r c C : ℝ} (hr0 : 0 < r) (hr1 : r < 1)
    (hcr : c * r < 1) (ε δ : ℕ → ℝ) (hε : ∀ n, 0 < ε n)
    (hinf : Tendsto ε (hyperfilter ℕ : Filter ℕ) (𝓝 0))
    (hδ : ∀ n, 0 ≤ δ n ∧ δ n ≤ C * ε n)
    (K : ℕ → ℕ) (hK1 : ∀ n, 1 ≤ K n) (hK : ∀ n, ε n < r ^ (K n - 1))
    (e : ℕ → ℕ → ℝ) (he0 : ∀ n, e n 0 = 0) (hnn : ∀ n k, 0 ≤ e n k)
    (hrec : ∀ n k, e n (k + 1) ≤ c * e n k + δ n) :
    Tendsto (fun n => e n (K n)) (hyperfilter ℕ : Filter ℕ) (𝓝 0) := by
  -- enlarge `c` to `c' > 1` with `c' r < 1`
  set m := max c 1
  have h1r : 1 < 1 / r := by rw [lt_div_iff₀ hr0]; linarith
  have hm1 : m < 1 / r := max_lt (by rw [lt_div_iff₀ hr0]; exact hcr) h1r
  set c' := (m + 1 / r) / 2
  have hc'1 : 1 < c' := by
    have : (1 : ℝ) ≤ m := le_max_right c 1
    show 1 < (m + 1 / r) / 2; linarith
  have hcc' : c ≤ c' := by
    have : c ≤ m := le_max_left c 1
    show c ≤ (m + 1 / r) / 2; linarith
  have hc'r : c' * r < 1 := by
    have : c' < 1 / r := by show (m + 1 / r) / 2 < 1 / r; linarith
    rwa [lt_div_iff₀ hr0] at this
  set α := snapAlpha c' r
  have hα1 : α < 1 := snapAlpha_lt_one hr0 hr1 (by linarith) hc'r
  have hc1 : 0 < c' - 1 := by linarith
  -- the pointwise bound
  have hb : ∀ n, e n (K n) ≤ C * r ^ (-α) / (c' - 1) * ε n ^ (1 - α) := by
    intro n
    have hrec' : ∀ k, e n (k + 1) ≤ c' * e n k + δ n := fun k =>
      (hrec n k).trans (by nlinarith [hnn n k])
    have h := snap_error_granule hr0 hr1 hc'1 (hδ n).1 (hε n) (hK1 n) (hK n) (e n) (he0 n) hrec'
    refine h.trans ?_
    have e1 : C * r ^ (-α) / (c' - 1) * ε n ^ (1 - α) =
        C * ε n * (r * ε n) ^ (-α) / (c' - 1) := by
      rw [Real.mul_rpow hr0.le (hε n).le, Real.rpow_sub (hε n), Real.rpow_one,
        Real.rpow_neg (hε n).le, Real.rpow_neg hr0.le]
      field_simp
    rw [e1, div_le_div_iff_of_pos_right hc1]
    exact mul_le_mul_of_nonneg_right (hδ n).2 (Real.rpow_nonneg (mul_pos hr0 (hε n)).le _)
  -- the bound tends to `0`
  have hlim : Tendsto (fun n => C * r ^ (-α) / (c' - 1) * ε n ^ (1 - α))
      (hyperfilter ℕ : Filter ℕ) (𝓝 0) := by
    have h1 : Tendsto (fun n => ε n ^ (1 - α)) (hyperfilter ℕ : Filter ℕ) (𝓝 0) := by
      have := ((Real.continuousAt_rpow_const 0 (1 - α) (Or.inr (by linarith))).tendsto).comp hinf
      rwa [Real.zero_rpow (by linarith)] at this
    simpa using h1.const_mul (C * r ^ (-α) / (c' - 1))
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim
    (fun n => hnn n (K n)) hb

/-- `thm:fr-segment-shadow`, hyperreal form: under the hypotheses of
`snap_error_tendsto`, if `gh = Hyperreal.ofSeq ε` is infinitesimal (`0 < mk gh`), then
the vertex error `E_K = Hyperreal.ofSeq (n ↦ e_n (K_n))` is infinitesimal. -/
theorem snap_error_infinitesimal {r c C : ℝ} (hr0 : 0 < r) (hr1 : r < 1)
    (hcr : c * r < 1) (ε δ : ℕ → ℝ) (hε : ∀ n, 0 < ε n)
    (hinf : 0 < ArchimedeanClass.mk (Hyperreal.ofSeq ε))
    (hδ : ∀ n, 0 ≤ δ n ∧ δ n ≤ C * ε n)
    (K : ℕ → ℕ) (hK1 : ∀ n, 1 ≤ K n) (hK : ∀ n, ε n < r ^ (K n - 1))
    (e : ℕ → ℕ → ℝ) (he0 : ∀ n, e n 0 = 0) (hnn : ∀ n k, 0 ≤ e n k)
    (hrec : ∀ n k, e n (k + 1) ≤ c * e n k + δ n) :
    0 < ArchimedeanClass.mk (Hyperreal.ofSeq fun n => e n (K n)) :=
  Hyperreal.archimedeanClassMk_pos_of_tendsto (Hyperreal.tendsto_ofSeq.2 (snap_error_tendsto hr0 hr1 hcr
    ε δ hε (tendsto_of_infinitesimal hinf) hδ K hK1 hK e he0 hnn hrec))

variable {X : Type*} [PseudoMetricSpace X]

/-- Hausdorff distance between vertex sets matched by index: if
`dist (v j) (p j) ≤ E` for `j ≤ m`, then `d_H({v_j}, {p_j}) ≤ E`. -/
theorem hausdorffDist_matched (v p : ℕ → X) (m : ℕ) {E : ℝ} (hE : 0 ≤ E)
    (h : ∀ j ≤ m, dist (v j) (p j) ≤ E) :
    hausdorffDist (v '' Set.Iic m) (p '' Set.Iic m) ≤ E := by
  refine hausdorffDist_le_of_mem_dist hE ?_ ?_
  · rintro _ ⟨j, hj, rfl⟩; exact ⟨p j, ⟨j, hj, rfl⟩, h j hj⟩
  · rintro _ ⟨j, hj, rfl⟩; exact ⟨v j, ⟨j, hj, rfl⟩, by rw [dist_comm]; exact h j hj⟩

/-- The Hutchinson operator `S ↦ ⋃ i, f_i(S)`. -/
def hutch {ι : Type*} (f : ι → X → X) (S : Set X) : Set X := ⋃ i, f i '' S

omit [PseudoMetricSpace X] in
theorem hutch_nonempty {ι : Type*} [Nonempty ι] (f : ι → X → X) {S : Set X}
    (hS : S.Nonempty) : (hutch f S).Nonempty := by
  obtain ⟨i⟩ := ‹Nonempty ι›
  obtain ⟨x, hx⟩ := hS
  exact ⟨f i x, Set.mem_iUnion.2 ⟨i, x, hx, rfl⟩⟩

theorem hutch_isBounded {ι : Type*} [Finite ι] (f : ι → X → X) {r : NNReal}
    (hf : ∀ i, LipschitzWith r (f i)) {S : Set X} (hS : IsBounded S) :
    IsBounded (hutch f S) :=
  isBounded_iUnion.2 fun i => (hf i).isBounded_image hS

/-- Hutchinson: the operator of `r`-Lipschitz maps is an `r`-contraction for the
Hausdorff distance (nonempty bounded sets, finitely many maps). -/
theorem hausdorffDist_hutch_le {ι : Type*} [Finite ι] (f : ι → X → X) {r : NNReal}
    (hf : ∀ i, LipschitzWith r (f i)) {S T : Set X} (hS : S.Nonempty) (hT : T.Nonempty)
    (hSb : IsBounded S) (hTb : IsBounded T) :
    hausdorffDist (hutch f S) (hutch f T) ≤ r * hausdorffDist S T := by
  have fin := hausdorffEDist_ne_top_of_nonempty_of_bounded hS hT hSb hTb
  have key : ∀ η > 0, hausdorffDist (hutch f S) (hutch f T) ≤ r * (hausdorffDist S T + η) := by
    intro η hη
    have hlt : hausdorffDist S T < hausdorffDist S T + η := by linarith
    refine hausdorffDist_le_of_mem_dist
      (mul_nonneg r.2 (by linarith [hausdorffDist_nonneg (s := S) (t := T)])) ?_ ?_
    · rintro _ ⟨_, ⟨i, rfl⟩, x, hx, rfl⟩
      obtain ⟨y, hy, hxy⟩ := exists_dist_lt_of_hausdorffDist_lt hx hlt fin
      exact ⟨f i y, Set.mem_iUnion.2 ⟨i, y, hy, rfl⟩,
        ((hf i).dist_le_mul x y).trans (mul_le_mul_of_nonneg_left hxy.le r.2)⟩
    · rintro _ ⟨_, ⟨i, rfl⟩, y, hy, rfl⟩
      obtain ⟨x, hx, hxy⟩ := exists_dist_lt_of_hausdorffDist_lt' hy hlt fin
      exact ⟨f i x, Set.mem_iUnion.2 ⟨i, x, hx, rfl⟩, by
        rw [dist_comm]
        exact ((hf i).dist_le_mul x y).trans (mul_le_mul_of_nonneg_left hxy.le r.2)⟩
  refine le_of_forall_pos_le_add fun η hη => ?_
  have h := key (η / (r + 1)) (by positivity)
  have : (r : ℝ) * (η / (r + 1)) ≤ η := by
    rw [mul_div_assoc', div_le_iff₀ (by positivity)]; nlinarith [r.2]
  nlinarith

/-- Iterated Hutchinson bound: if `A` is a fixed point of the Hutchinson
operator (the attractor), then `d_H(F^K(S), A) ≤ r^K d_H(S, A)`. -/
theorem hausdorffDist_hutch_iterate {ι : Type*} [Finite ι] [Nonempty ι] (f : ι → X → X)
    {r : NNReal} (hf : ∀ i, LipschitzWith r (f i)) {S A : Set X} (hS : S.Nonempty)
    (hA : A.Nonempty) (hSb : IsBounded S) (hAb : IsBounded A) (hfix : hutch f A = A) (K : ℕ) :
    hausdorffDist ((hutch f)^[K] S) A ≤ (r : ℝ) ^ K * hausdorffDist S A := by
  have hne : ∀ K, ((hutch f)^[K] S).Nonempty ∧ IsBounded ((hutch f)^[K] S) := by
    intro K
    induction K with
    | zero => exact ⟨hS, hSb⟩
    | succ K ih =>
      rw [Function.iterate_succ_apply']
      exact ⟨hutch_nonempty f ih.1, hutch_isBounded f hf ih.2⟩
  induction K with
  | zero => simp
  | succ K ih =>
    rw [Function.iterate_succ_apply']
    conv_lhs => rw [← hfix]
    refine (hausdorffDist_hutch_le f hf (hne K).1 hA (hne K).2 hAb).trans ?_
    rw [pow_succ]
    nlinarith [r.2, hausdorffDist_nonneg (s := S) (t := A)]

/-- Every point of a polygon with sides of length `≤ L` is within `L/2` of a
vertex, and the vertices lie on the polygon:
`d_H({p_0, …, p_m}, ⋃_{j<m} [p_j, p_{j+1}]) ≤ L/2` (`m ≥ 1`). -/
theorem hausdorffDist_vertices_polygon {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (p : ℕ → E) {m : ℕ} (hm : 1 ≤ m) {L : ℝ} (hL : 0 ≤ L)
    (h : ∀ j < m, dist (p j) (p (j + 1)) ≤ L) :
    hausdorffDist (p '' Set.Iic m) (⋃ j ∈ Set.Iio m, segment ℝ (p j) (p (j + 1))) ≤ L / 2 := by
  refine hausdorffDist_le_of_mem_dist (by linarith) ?_ ?_
  · rintro _ ⟨j, hj, rfl⟩
    rcases (Set.mem_Iic.1 hj).lt_or_eq with hj' | rfl
    · exact ⟨p j, Set.mem_biUnion (Set.mem_Iio.2 hj') (left_mem_segment ℝ _ _),
        by rw [dist_self]; linarith⟩
    · refine ⟨p j, Set.mem_biUnion (Set.mem_Iio.2 (show j - 1 < j by omega)) ?_,
        by rw [dist_self]; linarith⟩
      rw [show j - 1 + 1 = j by omega]; exact right_mem_segment ℝ _ _
  · intro x hx
    simp only [Set.mem_iUnion, Set.mem_Iio] at hx
    obtain ⟨j, hj, hx⟩ := hx
    have hsum := dist_add_dist_of_mem_segment hx
    have hjL := h j hj
    by_cases h1 : dist (p j) x ≤ L / 2
    · exact ⟨p j, ⟨j, Set.mem_Iic.2 hj.le, rfl⟩, by rw [dist_comm]; exact h1⟩
    · exact ⟨p (j + 1), ⟨j + 1, Set.mem_Iic.2 hj, rfl⟩, by linarith⟩

/-- The triangle step of `thm:fr-segment-shadow`: from
`d_H(V, V^cl) ≤ E`, `d_H(V^cl, P) ≤ ρ/2` and `d_H(P, A) ≤ ρ D` (nonempty bounded
sets `V, W, P`) follows `d_H(V, A) ≤ E + ρ (1/2 + D)`. -/
theorem hausdorffDist_shadow_triangle {V W P A : Set X} (hV : V.Nonempty) (hW : W.Nonempty)
    (hP : P.Nonempty) (hVb : IsBounded V) (hWb : IsBounded W)
    (hPb : IsBounded P) {E ρ D : ℝ}
    (h1 : hausdorffDist V W ≤ E) (h2 : hausdorffDist W P ≤ ρ / 2)
    (h3 : hausdorffDist P A ≤ ρ * D) :
    hausdorffDist V A ≤ E + ρ * (1 / 2 + D) := by
  have t1 := hausdorffDist_triangle (s := V) (t := W) (u := A)
    (hausdorffEDist_ne_top_of_nonempty_of_bounded hV hW hVb hWb)
  have t2 := hausdorffDist_triangle (s := W) (t := P) (u := A)
    (hausdorffEDist_ne_top_of_nonempty_of_bounded hW hP hWb hPb)
  nlinarith

/-- `thm:fr-segment-shadow`, standard parts.  Let `V_n` be nonempty bounded sets
(the internal vertex set `V_K = [V_n]`) with `d_H(V_n, A) → 0` along the
hyperfilter (`d_H(V_K, A)` infinitesimal), and `A` compact and nonempty.  Then
(i) every internal point `v = [v_n]` of `V_K` has a standard part in `A`:
`v_n → a ∈ A` along the hyperfilter; (ii) every `a ∈ A` is the standard part of
some internal point of `V_K`. -/
theorem shadow_of_hausdorff {A : Set X} (hA : IsCompact A) (hAne : A.Nonempty)
    (V : ℕ → Set X) (hV : ∀ n, (V n).Nonempty) (hVb : ∀ n, IsBounded (V n))
    (hd : Tendsto (fun n => hausdorffDist (V n) A) (hyperfilter ℕ : Filter ℕ) (𝓝 0)) :
    (∀ v : ℕ → X, (∀ n, v n ∈ V n) →
        ∃ a ∈ A, Tendsto v (hyperfilter ℕ : Filter ℕ) (𝓝 a)) ∧
      (∀ a ∈ A, ∃ v : ℕ → X, (∀ n, v n ∈ V n) ∧
        Tendsto v (hyperfilter ℕ : Filter ℕ) (𝓝 a)) := by
  have fin : ∀ n, hausdorffEDist (V n) A ≠ ⊤ := fun n =>
    hausdorffEDist_ne_top_of_nonempty_of_bounded (hV n) hAne (hVb n) hA.isBounded
  constructor
  · intro v hv
    choose a ha hda using fun n => hA.exists_infDist_eq_dist hAne (v n)
    obtain ⟨x, hx, hux⟩ := hA.ultrafilter_le_nhds (Ultrafilter.map a (hyperfilter ℕ))
      (by rw [Ultrafilter.coe_map]; exact tendsto_principal.2 (Filter.Eventually.of_forall ha))
    have hax : Tendsto a (hyperfilter ℕ : Filter ℕ) (𝓝 x) := hux
    refine ⟨x, hx, hax.congr_dist ?_⟩
    refine squeeze_zero (fun n => dist_nonneg) (fun n => ?_) hd
    rw [dist_comm, ← hda n]
    exact infDist_le_hausdorffDist_of_mem (hv n) (fin n)
  · intro a ha
    have hlt : ∀ n, hausdorffDist (V n) A < hausdorffDist (V n) A + 1 / ((n : ℝ) + 1) :=
      fun n => by have : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
                  linarith
    choose v hv hdv using fun n => exists_dist_lt_of_hausdorffDist_lt' ha (hlt n) (fin n)
    refine ⟨v, hv, tendsto_iff_dist_tendsto_zero.2 ?_⟩
    have h1 : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) (hyperfilter ℕ : Filter ℕ) (𝓝 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat.mono_left
        (hyperfilter_le_cofinite.trans Nat.cofinite_eq_atTop.le)
    have h2 := hd.add h1
    rw [add_zero] at h2
    exact squeeze_zero (fun n => dist_nonneg) (fun n => (hdv n).le) h2

/-- `thm:fr-segment-shadow`, assembled.  Data for each index `n` of the
ultrapower: the granular vertex set `V n`, the classical vertex set `W n`, the
classical polygon `P n = F^{K_n}(P₀)` (Hutchinson iterate of the base `P₀`,
`r`-Lipschitz maps `f`), its attractor `A` (a compact nonempty fixed point of
the Hutchinson operator), and `ρ_n = r^{K_n} ≤ ε_n`.  If
`d_H(V n, W n) ≤ E_n` with `E_n → 0` (the vertex error, `snap_error_tendsto`),
`d_H(W n, P n) ≤ ρ_n/2` (`hausdorffDist_vertices_polygon`), and `ε_n → 0` along
the hyperfilter, then `d_H(V_K, A)` is infinitesimal and the standard parts of
the points of `V_K` are exactly `A`. -/
theorem segment_shadow {ι : Type*} [Finite ι] [Nonempty ι] (f : ι → X → X) {r : NNReal}
    (hf : ∀ i, LipschitzWith r (f i)) {A P₀ : Set X} (hA : IsCompact A) (hAne : A.Nonempty)
    (hfix : hutch f A = A) (hP₀ : P₀.Nonempty) (hP₀b : IsBounded P₀)
    (K : ℕ → ℕ) (ε E : ℕ → ℝ) (hrε : ∀ n, (r : ℝ) ^ K n ≤ ε n)
    (hε : Tendsto ε (hyperfilter ℕ : Filter ℕ) (𝓝 0))
    (hE : Tendsto E (hyperfilter ℕ : Filter ℕ) (𝓝 0))
    (V W : ℕ → Set X) (hV : ∀ n, (V n).Nonempty) (hVb : ∀ n, IsBounded (V n))
    (hW : ∀ n, (W n).Nonempty) (hWb : ∀ n, IsBounded (W n))
    (hVW : ∀ n, hausdorffDist (V n) (W n) ≤ E n)
    (hWP : ∀ n, hausdorffDist (W n) ((hutch f)^[K n] P₀) ≤ (r : ℝ) ^ K n / 2) :
    Tendsto (fun n => hausdorffDist (V n) A) (hyperfilter ℕ : Filter ℕ) (𝓝 0) ∧
    (∀ v : ℕ → X, (∀ n, v n ∈ V n) →
        ∃ a ∈ A, Tendsto v (hyperfilter ℕ : Filter ℕ) (𝓝 a)) ∧
      (∀ a ∈ A, ∃ v : ℕ → X, (∀ n, v n ∈ V n) ∧
        Tendsto v (hyperfilter ℕ : Filter ℕ) (𝓝 a)) := by
  have hPit : ∀ k, ((hutch f)^[k] P₀).Nonempty ∧ IsBounded ((hutch f)^[k] P₀) := by
    intro k
    induction k with
    | zero => exact ⟨hP₀, hP₀b⟩
    | succ k ih =>
      rw [Function.iterate_succ_apply']
      exact ⟨hutch_nonempty f ih.1, hutch_isBounded f hf ih.2⟩
  set D := hausdorffDist P₀ A
  have hbound : ∀ n, hausdorffDist (V n) A ≤ E n + ε n * (1 / 2 + D) := by
    intro n
    have h3 := hausdorffDist_hutch_iterate f hf hP₀ hAne hP₀b hA.isBounded hfix (K n)
    have h := hausdorffDist_shadow_triangle (hV n) (hW n) (hPit (K n)).1 (hVb n) (hWb n)
      (hPit (K n)).2 (hVW n) (hWP n) h3
    refine h.trans ?_
    have : 0 ≤ 1 / 2 + D := by have := hausdorffDist_nonneg (s := P₀) (t := A); linarith
    nlinarith [hrε n]
  have hlim : Tendsto (fun n => E n + ε n * (1 / 2 + D)) (hyperfilter ℕ : Filter ℕ) (𝓝 0) := by
    simpa using hE.add (hε.mul_const (1 / 2 + D))
  have hd : Tendsto (fun n => hausdorffDist (V n) A) (hyperfilter ℕ : Filter ℕ) (𝓝 0) :=
    squeeze_zero (fun n => hausdorffDist_nonneg) hbound hlim
  exact ⟨hd, shadow_of_hausdorff hA hAne V hV hVb hd⟩

end SegmentShadow

end QE.Fractal
