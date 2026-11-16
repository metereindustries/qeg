-- SPDX-License-Identifier: MIT
-- Copyright 2026 Metere Industries, Inc. Author: Alfredo Metere.
-- Quasi-Euclidean Granular Geometry. Any derivative work must carry this notice:
--   This work is derivative of the Quasi-Euclidean Granular Geometry book
--   authored by Alfredo Metere. Copyright 2026 Metere Industries, Inc.
--   All rights reserved
-- See LICENSE.md and NOTICE.

import QuasiEuclidean.Basic

/-!
# Chapter 3: the granular measure

All statements are exact finitary identities, valid for every `ε` in every
linearly ordered field `K` (hence for `K := ℝ*` with `ε` infinitesimal, and
for `K := ℝ` with `ε` the Planck length).  Lattice points are indexed by
integers (`k ↦ 2εk`), configurations are finite sets of indices.
-/

set_option linter.unusedSectionVars false

namespace QE.Measure

open Finset

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-! ## Basic values -/

theorem mu_empty (ε : K) : mu ε (∅ : Finset ℤ) = 0 := by
  simp [mu]

theorem mu_singleton (ε : K) (a : ℤ) : mu ε {a} = 2 * ε := by
  simp [mu]

private lemma card_cast (a b : ℤ) (c : ℤ) (h : 0 ≤ b + c - a) :
    (((b + c - a).toNat : ℕ) : K) = ((b + c - a : ℤ) : K) := by
  rw [← Int.cast_natCast, Int.toNat_of_nonneg h]

/-- `μ[a,b] = (b-a) + 2ε`. -/
theorem mu_Icc (ε : K) {a b : ℤ} (h : a ≤ b) :
    mu ε (Icc a b) = (centre ε b - centre ε a) + 2 * ε := by
  unfold mu centre
  rw [Int.card_Icc, card_cast a b 1 (by omega)]; push_cast; ring

/-- `μ[a,b) = b-a`. -/
theorem mu_Ico (ε : K) {a b : ℤ} (h : a ≤ b) :
    mu ε (Ico a b) = centre ε b - centre ε a := by
  unfold mu centre
  rw [Int.card_Ico]
  have : (((b - a).toNat : ℕ) : K) = ((b - a : ℤ) : K) := by
    rw [← Int.cast_natCast, Int.toNat_of_nonneg (by omega)]
  rw [this]; push_cast; ring

/-- `μ(a,b] = b-a`. -/
theorem mu_Ioc (ε : K) {a b : ℤ} (h : a ≤ b) :
    mu ε (Ioc a b) = centre ε b - centre ε a := by
  unfold mu centre
  rw [Int.card_Ioc]
  have : (((b - a).toNat : ℕ) : K) = ((b - a : ℤ) : K) := by
    rw [← Int.cast_natCast, Int.toNat_of_nonneg (by omega)]
  rw [this]; push_cast; ring

/-- `μ(a,b) = (b-a) - 2ε` for `a < b`. -/
theorem mu_Ioo (ε : K) {a b : ℤ} (h : a < b) :
    mu ε (Ioo a b) = (centre ε b - centre ε a) - 2 * ε := by
  unfold mu centre
  rw [Int.card_Ioo]
  have : (((b - a - 1).toNat : ℕ) : K) = ((b - a - 1 : ℤ) : K) := by
    rw [← Int.cast_natCast, Int.toNat_of_nonneg (by omega)]
  rw [this]; push_cast; ring

/-! ## Faithfulness: no null sets but the empty set -/

theorem mu_nonneg {ε : K} (hε : 0 ≤ ε) (A : Finset ℤ) : 0 ≤ mu ε A := by
  unfold mu; positivity

theorem mu_eq_zero_iff {ε : K} (hε : ε ≠ 0) (A : Finset ℤ) : mu ε A = 0 ↔ A = ∅ := by
  unfold mu
  constructor
  · intro h
    have h2 : (2 * ε) ≠ 0 := mul_ne_zero two_ne_zero hε
    have : (A.card : K) = 0 := by
      rcases mul_eq_zero.1 h with h' | h'
      · exact absurd h' h2
      · exact h'
    exact Finset.card_eq_zero.1 (by exact_mod_cast this)
  · rintro rfl; simp

theorem mu_pos_iff {ε : K} (hε : 0 < ε) (A : Finset ℤ) : 0 < mu ε A ↔ A.Nonempty := by
  constructor
  · intro h
    rw [Finset.nonempty_iff_ne_empty]
    intro hA; rw [hA, mu_empty] at h; exact lt_irrefl _ h
  · intro h
    unfold mu
    have : (0 : K) < A.card := by exact_mod_cast h.card_pos
    positivity

/-- Lossless: the granular measure separates sets. -/
theorem mu_symmDiff_eq_zero_iff {ε : K} (hε : ε ≠ 0) (A B : Finset ℤ) :
    mu ε (symmDiff A B) = 0 ↔ A = B := by
  rw [mu_eq_zero_iff hε, Finset.symmDiff_eq_empty]

/-- Every nonempty configuration has measure at least one granule `2ε`. -/
theorem mu_ge_of_nonempty {ε : K} (hε : 0 ≤ ε) {A : Finset ℤ} (hA : A.Nonempty) :
    2 * ε ≤ mu ε A := by
  unfold mu
  have : (1 : K) ≤ A.card := by exact_mod_cast hA.card_pos
  nlinarith

/-- `n`-dimensional faithfulness. -/
theorem muN_eq_zero_iff (n : ℕ) {ε : K} (hε : ε ≠ 0) (A : Finset (Fin n → ℤ)) :
    muN n ε A = 0 ↔ A = ∅ := by
  unfold muN
  have h2 : (2 * ε) ^ n ≠ 0 := pow_ne_zero _ (mul_ne_zero two_ne_zero hε)
  constructor
  · intro h
    rcases mul_eq_zero.1 h with h' | h'
    · exact absurd h' h2
    · exact Finset.card_eq_zero.1 (by exact_mod_cast h')
  · rintro rfl; simp

theorem muN_ge_of_nonempty (n : ℕ) {ε : K} (hε : 0 ≤ ε) {A : Finset (Fin n → ℤ)}
    (hA : A.Nonempty) : (2 * ε) ^ n ≤ muN n ε A := by
  unfold muN
  have : (1 : K) ≤ A.card := by exact_mod_cast hA.card_pos
  have h0 : 0 ≤ (2 * ε) ^ n := by positivity
  nlinarith

/-! ## Interval information: the two bits of openness -/

/-- The four lattice intervals with endpoints `a, b`; `l` (resp. `r`) records
whether the left (resp. right) endpoint is included. -/
def itv (l r : Bool) (a b : ℤ) : Finset ℤ :=
  match l, r with
  | true, true => Icc a b
  | true, false => Ico a b
  | false, true => Ioc a b
  | false, false => Ioo a b

/-- Number of closed endpoints. -/
def nClosed (l r : Bool) : ℕ := l.toNat + r.toNat

/-- Unified interval formula: `μ(I) = (b-a) + (#closed endpoints - 1)·2ε`. -/
theorem mu_itv (ε : K) (l r : Bool) {a b : ℤ} (h : a < b) :
    mu ε (itv l r a b) = (centre ε b - centre ε a) + ((nClosed l r : K) - 1) * (2 * ε) := by
  cases l <;> cases r <;> simp only [itv, nClosed, Bool.toNat_true, Bool.toNat_false] <;> push_cast
  · rw [mu_Ioo ε h]; ring
  · rw [mu_Ioc ε h.le]; ring
  · rw [mu_Ico ε h.le]; ring
  · rw [mu_Icc ε h.le]; ring

/-- The measure determines the number of closed endpoints. -/
theorem nClosed_eq_of_mu_eq {ε : K} (hε : ε ≠ 0) (l r l' r' : Bool) {a b : ℤ} (h : a < b)
    (hμ : mu ε (itv l r a b) = mu ε (itv l' r' a b)) : nClosed l r = nClosed l' r' := by
  rw [mu_itv ε l r h, mu_itv ε l' r' h] at hμ
  have h2 : (2 * ε) ≠ 0 := mul_ne_zero two_ne_zero hε
  have : ((nClosed l r : K) - 1) = ((nClosed l' r' : K) - 1) :=
    mul_right_cancel₀ h2 (by linarith)
  exact_mod_cast (sub_left_inj.1 this)

/-- First moment `∑_{x∈A} x · 2ε` of a configuration. -/
def moment (ε : K) (A : Finset ℤ) : K := ∑ k ∈ A, centre ε k * (2 * ε)

/-- The first moments of `(a,b]` and `[a,b)` differ by `(b - a)·2ε`. -/
theorem moment_Ioc_sub_Ico (ε : K) {a b : ℤ} (h : a < b) :
    moment ε (Ioc a b) - moment ε (Ico a b) = (centre ε b - centre ε a) * (2 * ε) := by
  unfold moment
  have h1 : Icc a b = insert a (Ioc a b) := by
    ext x; simp only [mem_Icc, mem_insert, mem_Ioc]; omega
  have h2 : Icc a b = insert b (Ico a b) := by
    ext x; simp only [mem_Icc, mem_insert, mem_Ico]; omega
  have ha : a ∉ Ioc a b := by simp
  have hb : b ∉ Ico a b := by simp
  have e1 : ∑ k ∈ Icc a b, centre ε k * (2 * ε)
      = centre ε a * (2 * ε) + ∑ k ∈ Ioc a b, centre ε k * (2 * ε) := by
    rw [h1, sum_insert ha]
  have e2 : ∑ k ∈ Icc a b, centre ε k * (2 * ε)
      = centre ε b * (2 * ε) + ∑ k ∈ Ico a b, centre ε k * (2 * ε) := by
    rw [h2, sum_insert hb]
  linarith

/-- **Interval information.** For fixed lattice endpoints `a < b` and `ε ≠ 0`,
the pair (measure, first moment) determines which of the four intervals we
have: both bits of openness are retained. -/
theorem itv_determined {ε : K} (hε : ε ≠ 0) (l r l' r' : Bool) {a b : ℤ} (h : a < b)
    (hμ : mu ε (itv l r a b) = mu ε (itv l' r' a b))
    (hm : moment ε (itv l r a b) = moment ε (itv l' r' a b)) : l = l' ∧ r = r' := by
  have hn := nClosed_eq_of_mu_eq hε l r l' r' h hμ
  have hne : (centre ε b - centre ε a) * (2 * ε) ≠ 0 := by
    unfold centre
    have : ((b : K) - a) ≠ 0 := sub_ne_zero.2 (by exact_mod_cast h.ne')
    have : (2 * ε * b - 2 * ε * a) = 2 * ε * (b - a) := by ring
    rw [this]
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero two_ne_zero hε) (by assumption))
      (mul_ne_zero two_ne_zero hε)
  have hd := moment_Ioc_sub_Ico ε h
  cases l <;> cases r <;> cases l' <;> cases r' <;>
    simp_all [nClosed, itv]

/-- Runs of consecutive lattice points `{m, …, m+n-1}`: index sum. -/
theorem sum_Ico_run (m : ℤ) (n : ℕ) :
    2 * ∑ k ∈ Ico m (m + n), k = n * (2 * m + n - 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have : Ico m (m + ((n + 1 : ℕ) : ℤ)) = insert (m + n) (Ico m (m + n)) := by
      ext x; simp only [mem_Ico, mem_insert]; push_cast; omega
    rw [this, sum_insert (by simp), mul_add, ih]; push_cast; ring

/-- A run of consecutive lattice points is determined by its measure and its
first moment (here: its cardinality and index sum). -/
theorem run_determined (m m' : ℤ) (n n' : ℕ)
    (hc : (Ico m (m + n)).card = (Ico m' (m' + n')).card)
    (hs : ∑ k ∈ Ico m (m + n), k = ∑ k ∈ Ico m' (m' + n'), k) (hn : 0 < n) :
    m = m' ∧ n = n' := by
  simp only [Int.card_Ico] at hc
  have hnn : n = n' := by omega
  subst hnn
  refine ⟨?_, rfl⟩
  have h1 := sum_Ico_run m n
  have h2 := sum_Ico_run m' n
  rw [hs] at h1
  have : (n : ℤ) * (2 * m + n - 1) = n * (2 * m' + n - 1) := by linarith
  have hn' : (n : ℤ) ≠ 0 := by exact_mod_cast hn.ne'
  have := mul_left_cancel₀ hn' this
  linarith

/-! ## Additivity -/

theorem mu_union_disjoint (ε : K) {A B : Finset ℤ} (h : Disjoint A B) :
    mu ε (A ∪ B) = mu ε A + mu ε B := by
  unfold mu; rw [card_union_of_disjoint h]; push_cast; ring

/-- Inclusion–exclusion, exact. -/
theorem mu_union_add_inter (ε : K) (A B : Finset ℤ) :
    mu ε (A ∪ B) + mu ε (A ∩ B) = mu ε A + mu ε B := by
  unfold mu
  have := card_union_add_card_inter A B
  have : ((A ∪ B).card : K) + (A ∩ B).card = A.card + B.card := by exact_mod_cast this
  linear_combination (2 * ε) * this

theorem mu_mono {ε : K} (hε : 0 ≤ ε) {A B : Finset ℤ} (h : A ⊆ B) : mu ε A ≤ mu ε B := by
  unfold mu
  have : (A.card : K) ≤ B.card := by exact_mod_cast card_le_card h
  nlinarith

theorem mu_sdiff (ε : K) {A B : Finset ℤ} (h : B ⊆ A) : mu ε (A \ B) = mu ε A - mu ε B := by
  unfold mu; rw [card_sdiff_of_subset h]; push_cast [card_le_card h]; ring

/-- Finite (indeed hyperfinite, by transfer) additivity over a pairwise
disjoint family. -/
theorem mu_biUnion {ι : Type*} (ε : K) (s : Finset ι) (A : ι → Finset ℤ)
    (h : (s : Set ι).PairwiseDisjoint A) : mu ε (s.biUnion A) = ∑ i ∈ s, mu ε (A i) := by
  unfold mu; rw [card_biUnion h]; push_cast; rw [mul_sum]

/-! ## Invariance -/

/-- Granular measure is invariant under every injective relabelling of points. -/
theorem mu_image_of_injOn (ε : K) (A : Finset ℤ) (f : ℤ → ℤ) (hf : Set.InjOn f A) :
    mu ε (A.image f) = mu ε A := by
  unfold mu; rw [card_image_of_injOn hf]

/-- Translation invariance under lattice shifts. -/
theorem mu_shift (ε : K) (A : Finset ℤ) (t : ℤ) : mu ε (A.image (· + t)) = mu ε A :=
  mu_image_of_injOn ε A _ (fun _ _ _ _ h => by simpa using h)

/-- Reflection invariance. -/
theorem mu_neg (ε : K) (A : Finset ℤ) : mu ε (A.image (fun k => -k)) = mu ε A :=
  mu_image_of_injOn ε A _ (fun _ _ _ _ h => by simpa using h)

theorem muN_image_of_injOn (n : ℕ) (ε : K) (A : Finset (Fin n → ℤ)) (f : (Fin n → ℤ) → (Fin n → ℤ))
    (hf : Set.InjOn f A) : muN n ε (A.image f) = muN n ε A := by
  unfold muN; rw [card_image_of_injOn hf]

theorem muN_shift (n : ℕ) (ε : K) (A : Finset (Fin n → ℤ)) (t : Fin n → ℤ) :
    muN n ε (A.image (· + t)) = muN n ε A :=
  muN_image_of_injOn n ε A _ (fun _ _ _ _ h => by simpa using h)

/-- Action of the hyperoctahedral group `(ℤˣ)^n ⋊ Sₙ` on lattice indices:
permute coordinates by `σ` and flip signs by `s`. -/
def hyperoct {n : ℕ} (σ : Equiv.Perm (Fin n)) (s : Fin n → ℤˣ) (k : Fin n → ℤ) : Fin n → ℤ :=
  fun i => (s i : ℤ) * k (σ i)

theorem hyperoct_injective {n : ℕ} (σ : Equiv.Perm (Fin n)) (s : Fin n → ℤˣ) :
    Function.Injective (hyperoct σ s) := by
  intro k k' h
  funext j
  have := congrFun h (σ.symm j)
  simp only [hyperoct, Equiv.apply_symm_apply] at this
  have hu : IsUnit ((s (σ.symm j) : ℤ)) := (s (σ.symm j)).isUnit
  exact hu.mul_left_cancel this

/-- Invariance under the full symmetry group of the cubic lattice. -/
theorem muN_hyperoct (n : ℕ) (ε : K) (A : Finset (Fin n → ℤ)) (σ : Equiv.Perm (Fin n))
    (s : Fin n → ℤˣ) : muN n ε (A.image (hyperoct σ s)) = muN n ε A :=
  muN_image_of_injOn n ε A _ (hyperoct_injective σ s).injOn

/-- On the hyperfinite torus `ℤ/Nℤ`: the measure of a configuration. -/
def muT (N : ℕ) (ε : K) (A : Finset (ZMod N)) : K := 2 * ε * A.card

theorem muT_shift (N : ℕ) (ε : K) (A : Finset (ZMod N)) (t : ZMod N) :
    muT N ε (A.image (· + t)) = muT N ε A := by
  unfold muT; rw [card_image_of_injective _ (add_left_injective t)]

theorem muT_univ (N : ℕ) [NeZero N] (ε : K) : muT N ε (univ : Finset (ZMod N)) = 2 * ε * N := by
  unfold muT; simp [ZMod.card]

/-! ## Boxes and the Steiner-type expansion -/

/-- Closed box `∏ [aᵢ,bᵢ]`: `μ = ∏ (bᵢ - aᵢ + 2ε)`. -/
theorem muN_box (n : ℕ) (ε : K) (a b : Fin n → ℤ) (h : ∀ i, a i ≤ b i) :
    muN n ε (Fintype.piFinset fun i => Icc (a i) (b i)) =
      ∏ i, (centre ε (b i) - centre ε (a i) + 2 * ε) := by
  unfold muN
  rw [Fintype.card_piFinset]; push_cast
  have : (2 * ε) ^ n = ∏ _i : Fin n, (2 * ε) := by simp
  rw [this, ← prod_mul_distrib]
  refine prod_congr rfl fun i _ => ?_
  have := mu_Icc ε (h i)
  unfold mu at this; exact this

/-- Half-open box `∏ [aᵢ,bᵢ)`: `μ = ∏ (bᵢ - aᵢ)`, the exact Euclidean volume. -/
theorem muN_box_Ico (n : ℕ) (ε : K) (a b : Fin n → ℤ) (h : ∀ i, a i ≤ b i) :
    muN n ε (Fintype.piFinset fun i => Ico (a i) (b i)) =
      ∏ i, (centre ε (b i) - centre ε (a i)) := by
  unfold muN
  rw [Fintype.card_piFinset]; push_cast
  have : (2 * ε) ^ n = ∏ _i : Fin n, (2 * ε) := by simp
  rw [this, ← prod_mul_distrib]
  refine prod_congr rfl fun i _ => ?_
  have := mu_Ico ε (h i)
  unfold mu at this; exact this

/-- **Steiner-type expansion.** `∏ (Lᵢ + 2ε) = ∑_S (∏_{i∈S} Lᵢ) (2ε)^{n-|S|}`:
the coefficient of `(2ε)^j` is the `(n-j)`-th elementary symmetric function
of the side lengths (volume, half the surface area, …). -/
theorem steiner (n : ℕ) (ε : K) (L : Fin n → K) :
    ∏ i, (L i + 2 * ε) = ∑ S ∈ (univ : Finset (Fin n)).powerset,
      (∏ i ∈ S, L i) * (2 * ε) ^ (n - S.card) := by
  rw [prod_add]
  refine sum_congr rfl fun S _ => ?_
  rw [prod_const, card_sdiff_of_subset (subset_univ S), card_univ, Fintype.card_fin]

theorem steiner_two (ε L₁ L₂ : K) :
    (L₁ + 2 * ε) * (L₂ + 2 * ε) = L₁ * L₂ + ε * (2 * (L₁ + L₂)) + 4 * ε ^ 2 := by ring

theorem steiner_three (ε L₁ L₂ L₃ : K) :
    (L₁ + 2 * ε) * (L₂ + 2 * ε) * (L₃ + 2 * ε)
      = L₁ * L₂ * L₃ + ε * (2 * (L₁ * L₂ + L₂ * L₃ + L₃ * L₁))
        + ε ^ 2 * (4 * (L₁ + L₂ + L₃)) + 8 * ε ^ 3 := by ring

/-! ## No Banach–Tarski paradox -/

/-- A finite set cannot be split into two parts each in bijection with the whole,
unless it is empty. -/
theorem no_doubling {α : Type*} [DecidableEq α] (A B C : Finset α) (hBC : Disjoint B C)
    (hU : B ∪ C = A) (eB : B ≃ A) (eC : C ≃ A) : A = ∅ := by
  have h1 := Fintype.card_congr eB
  have h2 := Fintype.card_congr eC
  simp only [Fintype.card_coe] at h1 h2
  have := card_union_of_disjoint hBC
  rw [hU] at this
  exact card_eq_zero.1 (by omega)

/-- **No paradoxical decomposition.** If a finite configuration `A` is
partitioned into pieces `R i` (`i ∈ s`), and the pieces with `i ∈ T` can be
moved by injective maps `g i` to a partition of `A`, and so can the remaining
pieces, then `A = ∅`. -/
theorem no_paradoxical {α ι : Type*} [DecidableEq α] [DecidableEq ι]
    (A : Finset α) (s T : Finset ι) (R : ι → Finset α) (g : ι → α → α)
    (hR : (s : Set ι).PairwiseDisjoint R) (hRA : s.biUnion R = A)
    (hg : ∀ i ∈ s, Set.InjOn (g i) (R i))
    (hT : ((s.filter (· ∈ T)) : Set ι).PairwiseDisjoint (fun i => (R i).image (g i)))
    (hTA : (s.filter (· ∈ T)).biUnion (fun i => (R i).image (g i)) = A)
    (hT' : ((s.filter (· ∉ T)) : Set ι).PairwiseDisjoint (fun i => (R i).image (g i)))
    (hTA' : (s.filter (· ∉ T)).biUnion (fun i => (R i).image (g i)) = A) : A = ∅ := by
  have e0 : A.card = ∑ i ∈ s, (R i).card := by rw [← hRA, card_biUnion hR]
  have e1 : A.card = ∑ i ∈ s.filter (· ∈ T), (R i).card := by
    rw [← hTA, card_biUnion hT]
    refine sum_congr rfl fun i hi => card_image_of_injOn (hg i (mem_filter.1 hi).1)
  have e2 : A.card = ∑ i ∈ s.filter (· ∉ T), (R i).card := by
    rw [← hTA', card_biUnion hT']
    refine sum_congr rfl fun i hi => card_image_of_injOn (hg i (mem_filter.1 hi).1)
  have := sum_filter_add_sum_filter_not s (· ∈ T) (fun i => (R i).card)
  exact card_eq_zero.1 (by omega)

/-- Measure form: every injective map preserves `μ`, so a doubling would give
`μ(A) = 2 μ(A)`. -/
theorem mu_no_doubling {ε : K} (hε : ε ≠ 0) (A B C : Finset ℤ) (hBC : Disjoint B C)
    (hU : B ∪ C = A) (hB : mu ε B = mu ε A) (hC : mu ε C = mu ε A) : A = ∅ := by
  have := mu_union_disjoint ε hBC
  rw [hU, hB, hC] at this
  exact (mu_eq_zero_iff hε A).1 (by linarith)

/-! ## Countable sets: granular positivity -/

/-- `H` sample values snapped to the lattice occupy at most `H` granules. -/
theorem mu_image_range_le {ε : K} (hε : 0 ≤ ε) (H : ℕ) (f : ℕ → ℤ) :
    mu ε ((range H).image f) ≤ 2 * ε * H := by
  unfold mu
  have : (((range H).image f).card : K) ≤ H := by
    exact_mod_cast (card_image_le.trans (card_range H).le)
  nlinarith

/-- … with equality iff the snapped values are distinct. -/
theorem mu_image_range_eq_iff {ε : K} (hε : ε ≠ 0) (H : ℕ) (f : ℕ → ℤ) :
    mu ε ((range H).image f) = 2 * ε * H ↔ Set.InjOn f (range H) := by
  unfold mu
  have h2 : (2 * ε) ≠ 0 := mul_ne_zero two_ne_zero hε
  rw [mul_right_inj' h2, ← card_range H, Nat.cast_inj, card_range]
  constructor
  · intro h; exact card_image_iff.1 (h.trans (card_range H).symm)
  · intro h; rw [card_image_of_injOn h, card_range]

/-- Any configuration containing `k` distinct points has measure at least `2εk`. -/
theorem mu_ge_of_card_le {ε : K} (hε : 0 ≤ ε) {A S : Finset ℤ} (hS : S ⊆ A) :
    2 * ε * S.card ≤ mu ε A := by
  have := mu_mono hε hS; unfold mu at this ⊢; exact this

/-! ## Almost everywhere becomes "everywhere except counted points" -/

/-- If `f = g` off an exceptional set `S ⊆ A`, the granular integrals over `A`
differ by exactly the contribution of `S`. -/
theorem sum_diff_exceptional (ε : K) (A S : Finset ℤ) (hS : S ⊆ A) (f g : ℤ → K)
    (hfg : ∀ k ∈ A, k ∉ S → f k = g k) :
    ∑ k ∈ A, f k * (2 * ε) - ∑ k ∈ A, g k * (2 * ε) = ∑ k ∈ S, (f k - g k) * (2 * ε) := by
  rw [← sum_sub_distrib]
  simp_rw [← sub_mul]
  rw [← sum_subset hS]
  intro k hk hkS; rw [hfg k hk hkS]; ring

theorem mu_exceptional (ε : K) (S : Finset ℤ) : mu ε S = 2 * ε * S.card := rfl

/-! ## Vitali: hyperfinitely many translates -/

/-- If the translates `V + g` (`g ∈ G`) are pairwise disjoint, their union has
cardinality `|G|·|V|`; in the hyperfinite setting this is what replaces the
contradiction of Vitali's construction. -/
theorem card_translates (V G : Finset ℤ)
    (h : (G : Set ℤ).PairwiseDisjoint (fun g => V.image (· + g))) :
    (G.biUnion fun g => V.image (· + g)).card = G.card * V.card := by
  rw [card_biUnion h]
  rw [sum_congr rfl fun g _ => card_image_of_injective V (add_left_injective g)]
  simp

theorem mu_translates (ε : K) (V G : Finset ℤ)
    (h : (G : Set ℤ).PairwiseDisjoint (fun g => V.image (· + g))) :
    mu ε (G.biUnion fun g => V.image (· + g)) = G.card * mu ε V := by
  unfold mu; rw [card_translates V G h]; push_cast; ring

/-! ## Cantor set -/

/-- Left-endpoint indices (in units of `3^{-n}`) of the depth-`n` Cantor intervals. -/
def cantorIdx : ℕ → Finset ℕ
  | 0 => {0}
  | n + 1 => cantorIdx n ∪ (cantorIdx n).image (· + 2 * 3 ^ n)

theorem cantorIdx_lt (n : ℕ) : ∀ x ∈ cantorIdx n, x < 3 ^ n := by
  induction n with
  | zero => simp [cantorIdx]
  | succ n ih =>
    intro x hx
    simp only [cantorIdx, mem_union, mem_image] at hx
    rcases hx with hx | ⟨y, hy, rfl⟩
    · have := ih x hx; rw [pow_succ]; omega
    · have := ih y hy; rw [pow_succ]; omega

theorem cantorIdx_even (n : ℕ) : ∀ x ∈ cantorIdx n, 2 ∣ x := by
  induction n with
  | zero => simp [cantorIdx]
  | succ n ih =>
    intro x hx
    simp only [cantorIdx, mem_union, mem_image] at hx
    rcases hx with hx | ⟨y, hy, rfl⟩
    · exact ih x hx
    · exact dvd_add (ih y hy) (dvd_mul_right 2 _)

/-- There are exactly `2^n` intervals at depth `n`. -/
theorem cantorIdx_card (n : ℕ) : (cantorIdx n).card = 2 ^ n := by
  induction n with
  | zero => simp [cantorIdx]
  | succ n ih =>
    simp only [cantorIdx]
    rw [card_union_of_disjoint, card_image_of_injective _ (add_left_injective _), ih, pow_succ]
    · ring
    · rw [disjoint_left]
      intro x hx hx'
      obtain ⟨y, _, rfl⟩ := mem_image.1 hx'
      have := cantorIdx_lt n _ hx
      omega

/-- Closed intervals of `s+1` lattice points (lattice length `2εs`) starting at
`c·s` for indices `c` in a set of pairwise-distant (even) indices: the measure
is the total length plus one granule `2ε` per component. -/
theorem mu_closed_components (ε : K) (T : Finset ℕ) (hT : ∀ c ∈ T, 2 ∣ c) (s : ℕ) (hs : 0 < s) :
    mu ε (T.biUnion fun c => Icc ((c * s : ℕ) : ℤ) ((c * s + s : ℕ) : ℤ))
      = T.card * (2 * ε * s + 2 * ε) := by
  rw [mu_biUnion]
  · rw [sum_congr rfl fun c _ => mu_Icc ε (by push_cast; omega)]
    simp only [centre]; push_cast
    trans ∑ _x ∈ T, (2 * ε * s + 2 * ε)
    · exact sum_congr rfl fun x _ => by ring
    · rw [sum_const, nsmul_eq_mul]
  · intro c hc c' hc' hne
    simp only [Function.onFun]
    rw [disjoint_left]
    intro x hx hx'
    simp only [mem_Icc] at hx hx'
    have h1 : c * s ≤ c' * s + s := by omega
    have h2 : c' * s ≤ c * s + s := by omega
    obtain ⟨u, rfl⟩ := hT c hc
    obtain ⟨v, rfl⟩ := hT c' hc'
    have huv : u ≠ v := fun h => hne (by rw [h])
    rcases Nat.lt_or_gt_of_ne huv with h | h
    · have : (2 * u + 2) * s ≤ 2 * v * s := Nat.mul_le_mul_right _ (by omega)
      nlinarith
    · have : (2 * v + 2) * s ≤ 2 * u * s := Nat.mul_le_mul_right _ (by omega)
      nlinarith

/-- Granular measure of the depth-`n` Cantor approximant on a lattice of
`s` granules per depth-`n` interval: `2^n (2εs + 2ε)`.  With `2εs = 3^{-n}`
this is `(2/3)^n + 2^n · 2ε`. -/
theorem mu_cantor (ε : K) (n s : ℕ) (hs : 0 < s) :
    mu ε ((cantorIdx n).biUnion fun c => Icc ((c * s : ℕ) : ℤ) ((c * s + s : ℕ) : ℤ))
      = 2 ^ n * (2 * ε * s + 2 * ε) := by
  rw [mu_closed_components ε _ (cantorIdx_even n) s hs, cantorIdx_card]; push_cast; ring

/-- Box-counting ratio of the Cantor approximants: `log 2^n / log 3^n = log 2 / log 3`. -/
theorem cantor_dim (n : ℕ) (hn : 0 < n) :
    Real.log ((cantorIdx n).card) / Real.log ((3 : ℝ) ^ n) = Real.log 2 / Real.log 3 := by
  rw [cantorIdx_card]; push_cast
  rw [Real.log_pow, Real.log_pow]
  have : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  field_simp

/-! ## Shadow theorem: intervals and boxes (Jordan case) -/

/-- Number of lattice points of `2εℤ` in `[a,b]`. -/
noncomputable def latCount (ε a b : ℝ) : ℕ := (Icc ⌈a / (2 * ε)⌉ ⌊b / (2 * ε)⌋).card

theorem latCount_bound {ε : ℝ} (hε : 0 < ε) {a b : ℝ} (hab : a ≤ b) :
    |2 * ε * latCount ε a b - (b - a)| ≤ 2 * ε := by
  unfold latCount
  rw [Int.card_Icc]
  set x := a / (2 * ε)
  set y := b / (2 * ε)
  have h2 : 0 < 2 * ε := by linarith
  have hxy : x ≤ y := div_le_div_of_nonneg_right hab h2.le
  have f1 := Int.floor_le y
  have f2 := Int.lt_floor_add_one y
  have c1 := Int.le_ceil x
  have c2 := Int.ceil_lt_add_one x
  have hnn : (0 : ℤ) ≤ ⌊y⌋ + 1 - ⌈x⌉ := by
    have : ((⌈x⌉ : ℤ) : ℝ) < ⌊y⌋ + 2 := by linarith
    have : ⌈x⌉ < ⌊y⌋ + 2 := by exact_mod_cast this
    omega
  have hc : (((⌊y⌋ + 1 - ⌈x⌉).toNat : ℕ) : ℝ) = ((⌊y⌋ : ℝ) + 1 - ⌈x⌉) := by
    rw [← Int.cast_natCast, Int.toNat_of_nonneg hnn]; push_cast; ring
  rw [hc]
  have ha : a = 2 * ε * x := by simp only [x]; field_simp
  have hb : b = 2 * ε * y := by simp only [y]; field_simp
  rw [abs_le]
  constructor
  · rw [ha, hb]; nlinarith
  · rw [ha, hb]; nlinarith

/-- **Shadow of the interval measure.** `2ε · #([a,b] ∩ 2εℤ) → b - a` as `ε → 0⁺`. -/
theorem shadow_interval {a b : ℝ} (hab : a ≤ b) :
    Filter.Tendsto (fun ε => 2 * ε * (latCount ε a b : ℝ)) (nhdsWithin 0 (Set.Ioi 0))
      (nhds (b - a)) := by
  rw [Metric.tendsto_nhdsWithin_nhds]
  intro δ hδ
  refine ⟨δ / 4, by positivity, fun ε hε hd => ?_⟩
  have hε' : 0 < ε := hε
  rw [Real.dist_eq] at hd ⊢
  rw [sub_zero, abs_of_pos hε'] at hd
  have := latCount_bound hε' hab
  linarith

/-- **Shadow for boxes.** `(2ε)^n · #(∏[aᵢ,bᵢ] ∩ (2εℤ)^n) → ∏ (bᵢ - aᵢ)`. -/
theorem shadow_box (n : ℕ) {a b : Fin n → ℝ} (hab : ∀ i, a i ≤ b i) :
    Filter.Tendsto (fun ε => ∏ i, 2 * ε * (latCount ε (a i) (b i) : ℝ))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (∏ i, (b i - a i))) :=
  tendsto_finsetProd _ fun i _ => shadow_interval (hab i)

/-- The box count factorises, so the previous limit is the shadow of `muN`. -/
theorem box_count_eq (n : ℕ) (ε : ℝ) (a b : Fin n → ℝ) :
    (2 * ε) ^ n * ((Fintype.piFinset fun i => Icc ⌈a i / (2 * ε)⌉ ⌊b i / (2 * ε)⌋).card : ℝ)
      = ∏ i, 2 * ε * (latCount ε (a i) (b i) : ℝ) := by
  rw [Fintype.card_piFinset]; push_cast
  rw [prod_mul_distrib]; simp [latCount]

/-- The image of any finite index set `S` under any labelling `f` occupies at
most `|S|` granules (used for the Farey representative of `ℚ ∩ [0,1]`). -/
theorem mu_image_le {α : Type*} [DecidableEq α] {ε : K} (hε : 0 ≤ ε) (S : Finset α)
    (f : α → ℤ) : mu ε (S.image f) ≤ 2 * ε * S.card := by
  unfold mu
  have : ((S.image f).card : K) ≤ S.card := by exact_mod_cast card_image_le
  nlinarith

/-- Farey bound: the rationals `p/q` with `0 ≤ p ≤ q ≤ M`, placed on any lattice,
have granular measure at most `2ε (M+1)^2`. -/
theorem mu_farey_le {ε : K} (hε : 0 ≤ ε) (M : ℕ) (f : ℕ × ℕ → ℤ) :
    mu ε ((range (M + 1) ×ˢ range (M + 1)).image f) ≤ 2 * ε * ((M : K) + 1) ^ 2 := by
  have := mu_image_le hε (range (M + 1) ×ˢ range (M + 1)) f
  rw [card_product, card_range] at this
  push_cast at this; nlinarith

/-! ## Combined statements (one constant per book theorem) -/

/-- `thm:interval-measure` in one statement. -/
theorem interval_measure (ε : K) {a b : ℤ} (h : a < b) :
    mu ε (Icc a b) = (centre ε b - centre ε a) + 2 * ε ∧
    mu ε (Ico a b) = centre ε b - centre ε a ∧
    mu ε (Ioc a b) = centre ε b - centre ε a ∧
    mu ε (Ioo a b) = (centre ε b - centre ε a) - 2 * ε ∧
    mu ε {a} = 2 * ε ∧ mu ε (∅ : Finset ℤ) = 0 :=
  ⟨mu_Icc ε h.le, mu_Ico ε h.le, mu_Ioc ε h.le, mu_Ioo ε h, mu_singleton ε a, mu_empty ε⟩

/-- `thm:faithful` in one statement. -/
theorem faithful {ε : K} (hε : ε ≠ 0) (A B : Finset ℤ) :
    (mu ε A = 0 ↔ A = ∅) ∧ (mu ε (symmDiff A B) = 0 ↔ A = B) :=
  ⟨mu_eq_zero_iff hε A, mu_symmDiff_eq_zero_iff hε A B⟩

/-- `thm:measure-additivity` in one statement (families indexed by finite sets of naturals). -/
theorem additivity {ε : K} (hε : 0 ≤ ε) :
    (∀ A B : Finset ℤ, Disjoint A B → mu ε (A ∪ B) = mu ε A + mu ε B) ∧
    (∀ (s : Finset ℕ) (A : ℕ → Finset ℤ), (s : Set ℕ).PairwiseDisjoint A →
      mu ε (s.biUnion A) = ∑ i ∈ s, mu ε (A i)) ∧
    (∀ A B : Finset ℤ, A ⊆ B → mu ε A ≤ mu ε B ∧ mu ε (B \ A) = mu ε B - mu ε A) :=
  ⟨fun _ _ h => mu_union_disjoint ε h, fun s A h => mu_biUnion ε s A h,
    fun _ _ h => ⟨mu_mono hε h, mu_sdiff ε h⟩⟩

/-- `thm:interval-information` in one statement. -/
theorem interval_information {ε : K} (hε : ε ≠ 0) {a b : ℤ} (h : a < b) :
    (∀ l r l' r' : Bool, mu ε (itv l r a b) = mu ε (itv l' r' a b) → nClosed l r = nClosed l' r') ∧
    moment ε (Ioc a b) - moment ε (Ico a b) = (centre ε b - centre ε a) * (2 * ε) ∧
    (∀ l r l' r' : Bool, mu ε (itv l r a b) = mu ε (itv l' r' a b) →
      moment ε (itv l r a b) = moment ε (itv l' r' a b) → l = l' ∧ r = r') ∧
    (∀ (m m' : ℤ) (n n' : ℕ), 0 < n → (Ico m (m + n)).card = (Ico m' (m' + n')).card →
      ∑ k ∈ Ico m (m + n), k = ∑ k ∈ Ico m' (m' + n'), k → m = m' ∧ n = n') :=
  ⟨fun l r l' r' => nClosed_eq_of_mu_eq hε l r l' r' h, moment_Ioc_sub_Ico ε h,
    fun l r l' r' => itv_determined hε l r l' r' h,
    fun m m' n n' hn hc hs => run_determined m m' n n' hc hs hn⟩

/-- Translation and injective-map invariance (`thm:measure-shift`) in one statement. -/
theorem shift_invariance (ε : K) :
    (∀ (A : Finset ℤ) (t : ℤ), mu ε (A.image (· + t)) = mu ε A) ∧
    (∀ (n : ℕ) (A : Finset (Fin n → ℤ)) (t : Fin n → ℤ), muN n ε (A.image (· + t)) = muN n ε A) ∧
    (∀ (N : ℕ) (A : Finset (ZMod N)) (t : ZMod N), muT N ε (A.image (· + t)) = muT N ε A) ∧
    (∀ (A : Finset ℤ) (f : ℤ → ℤ), Set.InjOn f A → mu ε (A.image f) = mu ε A) :=
  ⟨mu_shift ε, fun n => muN_shift n ε, fun N => muT_shift N ε,
    fun A f hf => mu_image_of_injOn ε A f hf⟩

/-- `thm:countable-positive` (finitary content) in one statement. -/
theorem countable_positive {ε : K} (hε : 0 < ε) :
    (∀ (n : ℕ) (A : Finset (Fin n → ℤ)), A.Nonempty → (2 * ε) ^ n ≤ muN n ε A) ∧
    (∀ A S : Finset ℤ, S ⊆ A → 2 * ε * S.card ≤ mu ε A) ∧
    (∀ (H : ℕ) (f : ℕ → ℤ), mu ε ((range H).image f) ≤ 2 * ε * H ∧
      (mu ε ((range H).image f) = 2 * ε * H ↔ Set.InjOn f (range H))) ∧
    (∀ (M : ℕ) (f : ℕ × ℕ → ℤ),
      mu ε ((range (M + 1) ×ˢ range (M + 1)).image f) ≤ 2 * ε * ((M : K) + 1) ^ 2) :=
  ⟨fun n _ hA => muN_ge_of_nonempty n hε.le hA, fun _ _ h => mu_ge_of_card_le hε.le h,
    fun H f => ⟨mu_image_range_le hε.le H f, mu_image_range_eq_iff hε.ne' H f⟩,
    fun M f => mu_farey_le hε.le M f⟩

/-- Granular Cantor sets (`prop:measure-cantor`) in one statement. -/
theorem cantor (ε : K) :
    (∀ n, (cantorIdx n).card = 2 ^ n ∧ ∀ x ∈ cantorIdx n, 2 ∣ x ∧ x < 3 ^ n) ∧
    (∀ n s : ℕ, 0 < s → mu ε ((cantorIdx n).biUnion
        fun c => Icc ((c * s : ℕ) : ℤ) ((c * s + s : ℕ) : ℤ)) = 2 ^ n * (2 * ε * s + 2 * ε)) ∧
    (∀ n : ℕ, 0 < n →
      Real.log ((cantorIdx n).card) / Real.log ((3 : ℝ) ^ n) = Real.log 2 / Real.log 3) :=
  ⟨fun n => ⟨cantorIdx_card n, fun x hx => ⟨cantorIdx_even n x hx, cantorIdx_lt n x hx⟩⟩,
    fun n s hs => mu_cantor ε n s hs, fun n hn => cantor_dim n hn⟩

/-- Shadow theorem, box case (`thm:shadow`) in one statement. -/
theorem shadow_boxes :
    (∀ {ε a b : ℝ}, 0 < ε → a ≤ b → |2 * ε * latCount ε a b - (b - a)| ≤ 2 * ε) ∧
    (∀ (n : ℕ) {a b : Fin n → ℝ}, (∀ i, a i ≤ b i) →
      Filter.Tendsto (fun ε => (2 * ε) ^ n *
        ((Fintype.piFinset fun i => Icc ⌈a i / (2 * ε)⌉ ⌊b i / (2 * ε)⌋).card : ℝ))
        (nhdsWithin 0 (Set.Ioi 0)) (nhds (∏ i, (b i - a i)))) := by
  refine ⟨fun hε hab => latCount_bound hε hab, fun n a b hab => ?_⟩
  simp_rw [box_count_eq]
  exact shadow_box n hab

/-! ## Exact Fubini, and lower-dimensional sets -/

/-- **Exact Fubini–Cavalieri.** The planar granular measure of a finite
configuration is the sum over occupied columns of `2ε` times the linear
granular measure of the column. -/
theorem fubini (ε : K) (A : Finset (ℤ × ℤ)) :
    (2 * ε) ^ 2 * A.card =
      ∑ x ∈ A.image Prod.fst, 2 * ε * mu ε ((A.filter (·.1 = x)).image Prod.snd) := by
  unfold mu
  have h : A.card = ∑ x ∈ A.image Prod.fst, (A.filter (·.1 = x)).card :=
    card_eq_sum_card_fiberwise (fun p hp => mem_image_of_mem Prod.fst hp)
  have h2 : ∀ x, ((A.filter (·.1 = x)).image Prod.snd).card = (A.filter (·.1 = x)).card := by
    intro x
    refine card_image_of_injOn ?_
    intro p hp q hq hpq
    have hp' := (mem_filter.1 hp).2
    have hq' := (mem_filter.1 hq).2
    exact Prod.ext (hp'.trans hq'.symm) hpq
  simp_rw [h2]
  rw [h]; push_cast; rw [mul_sum]
  refine sum_congr rfl fun x _ => by ring

/-- The lattice diagonal of the closed square `[0, 2εn]²` has `n+1` points:
granular measure `2ε · (2εn + 2ε)` — thickness `2ε` times the ℓ^∞-length
`2εn` of the segment plus one granule, not its Euclidean length `√2 · 2εn`. -/
theorem muN_diagonal (ε : K) (n : ℕ) :
    muN 2 ε ((Icc (0 : ℤ) n).image fun k => ![k, k]) = 2 * ε * (2 * ε * n + 2 * ε) := by
  unfold muN
  rw [card_image_of_injective _ (fun k k' h => by simpa using congrFun h 0), Int.card_Icc]
  have : (((n + 1 - 0 : ℤ)).toNat : K) = (n : K) + 1 := by
    rw [sub_zero]
    have : ((n : ℤ) + 1).toNat = n + 1 := by omega
    rw [this]; push_cast; ring
  rw [this]; ring

/-- A degenerate (flat) closed box: `k` free sides of lengths `Lᵢ` and `n-k`
sides of length zero has measure `(2ε)^{n-k} ∏ (Lᵢ + 2ε)`. Stated as: a closed
box with all sides zero is a single point of measure `(2ε)^n`. -/
theorem muN_box_point (n : ℕ) (ε : K) (a : Fin n → ℤ) :
    muN n ε (Fintype.piFinset fun i => Icc (a i) (a i)) = (2 * ε) ^ n := by
  rw [muN_box n ε a a (fun _ => le_rfl)]; simp

/-! ## Quantitative shadow for one-dimensional elementary sets -/

/-- For a finite family of real intervals `[aᵢ, bᵢ]` whose lattice traces are
pairwise disjoint, the granular measure of the union differs from the total
length by at most one granule `2ε` per component. -/
theorem elementary_error {ι : Type*} {ε : ℝ} (hε : 0 < ε) (s : Finset ι) (a b : ι → ℝ)
    (hab : ∀ i ∈ s, a i ≤ b i)
    (hd : (s : Set ι).PairwiseDisjoint fun i => Icc ⌈a i / (2 * ε)⌉ ⌊b i / (2 * ε)⌋) :
    |2 * ε * ((s.biUnion fun i => Icc ⌈a i / (2 * ε)⌉ ⌊b i / (2 * ε)⌋).card : ℝ)
        - ∑ i ∈ s, (b i - a i)| ≤ 2 * ε * s.card := by
  rw [card_biUnion hd]; push_cast
  rw [mul_sum, ← sum_sub_distrib]
  calc |∑ i ∈ s, (2 * ε * ((Icc ⌈a i / (2 * ε)⌉ ⌊b i / (2 * ε)⌋).card : ℝ) - (b i - a i))|
      ≤ ∑ i ∈ s, |2 * ε * ((Icc ⌈a i / (2 * ε)⌉ ⌊b i / (2 * ε)⌋).card : ℝ) - (b i - a i)| :=
        abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i ∈ s, 2 * ε := sum_le_sum fun i hi => latCount_bound hε (hab i hi)
    _ = 2 * ε * s.card := by rw [sum_const, nsmul_eq_mul]; ring

/-! ## Hilbert's hotel on a hyperfinite set -/

/-- Among `2H` consecutive lattice indices exactly `H` are even: halving the
evens of `[0, 2H)` fills only `[0, H)`, never the whole. -/
theorem card_evens (H : ℕ) : ((range (2 * H)).filter Even).card = H := by
  have : (range (2 * H)).filter Even = (range H).image (2 * ·) := by
    ext x
    simp only [mem_filter, mem_range, mem_image]
    constructor
    · rintro ⟨hx, ⟨r, rfl⟩⟩; exact ⟨r, by omega, by ring⟩
    · rintro ⟨r, hr, rfl⟩; exact ⟨by omega, ⟨r, by ring⟩⟩
  rw [this, card_image_of_injective _ (fun x y h => by simpa using h), card_range]

end QE.Measure
