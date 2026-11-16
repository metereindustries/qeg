-- SPDX-License-Identifier: MIT
-- Copyright 2026 Metere Industries, Inc. Author: Alfredo Metere.
-- Quasi-Euclidean Granular Geometry. Any derivative work must carry this notice:
--   This work is derivative of the Quasi-Euclidean Granular Geometry book
--   authored by Alfredo Metere. Copyright 2026 Metere Industries, Inc.
--   All rights reserved
-- See LICENSE.md and NOTICE.

import QuasiEuclidean.Basic

/-!
# Chapter 10b: Fractal geometry — exact box counts and exact dimensions

Everything here is an exact finitary statement.  A lattice point is its
integer index `k` (standing for the centre `k·2ε`), a set is a `Finset` of
indices, and the content of a set is its number of points.  No Lebesgue
measure and no integral is used anywhere: box counts are cardinalities of
images under floor division, dimensions are ratios of logarithms of counts.

Contents (namespace `QE.Fractal`):
* **A. Box counts.**  `boxes s A` (floor division by the box side `s`),
  `N s A`; monotonicity, subadditivity, positivity, nesting of scales; the
  planar product law `N2 s (A ×ˢ B) = N s A * N s B`; the dimension between
  two scales and its exact additivity on products; the granule-scale
  dimension `log #A / log L` and its additivity.
* **B. Digit (b-adic self-similar) sets.**  `digitSet b D K` (one and `n`
  dimensions); exact cardinality `|D|^K`, exact coarse-graining, exact box
  counts `|D|^(K-j)` at scale `b^j`, and the exact dimension
  `log |D| / log b` between any two scales and at the granule scale.
  Instances: the Cantor set (`b = 3`, `D = {0,2}`) and the Sierpiński carpet
  (`n = 2`, `b = 3`, `|D| = 8`).
* **C. Exact L-systems.**  Substitutions preserving the vector sum, generator
  words, the closure theorem for snapped generators, turtle endpoints, the
  snap error bound, and the error of a snapped iterated function system.
* **D. Shadow.**  The standard part of the hyperreal sequence of granule
  dimensions is its classical limit; bounds and liminf/limsup version.
-/

namespace QE.Fractal

open Finset

/-! ## A. Box counts -/

/-- The boxes of side `s` met by `A ⊆ ℤ`: the floor quotients `k / s`
(Lean's `/` on `ℤ` is floor division when `s > 0`). -/
def boxes (s : ℤ) (A : Finset ℤ) : Finset ℤ := A.image (· / s)

/-- The box count of `A` at box side `s`. -/
def N (s : ℤ) (A : Finset ℤ) : ℕ := (boxes s A).card

/-- At box side `1` (the granule scale) the box count is the number of points. -/
theorem N_one (A : Finset ℤ) : N 1 A = A.card := by
  simp [N, boxes]

/-- A set never meets more boxes than it has points. -/
theorem N_le_card (s : ℤ) (A : Finset ℤ) : N s A ≤ A.card :=
  card_image_le

/-- Box counts are monotone: `A ⊆ B` implies `N s A ≤ N s B`. -/
theorem N_mono (s : ℤ) {A B : Finset ℤ} (h : A ⊆ B) : N s A ≤ N s B :=
  card_le_card (image_subset_image h)

/-- The boxes met by a union are the union of the boxes met. -/
theorem boxes_union (s : ℤ) (A B : Finset ℤ) :
    boxes s (A ∪ B) = boxes s A ∪ boxes s B :=
  image_union _ _

/-- Box counts are subadditive: `N s (A ∪ B) ≤ N s A + N s B`. -/
theorem N_union_le (s : ℤ) (A B : Finset ℤ) : N s (A ∪ B) ≤ N s A + N s B := by
  rw [N, boxes_union]; exact card_union_le _ _

/-- A nonempty set meets at least one box: `0 < N s A`. -/
theorem N_pos (s : ℤ) {A : Finset ℤ} (h : A.Nonempty) : 0 < N s A :=
  card_pos.2 (h.image _)

/-- Nested scales: for `0 < s` and `0 < t`, the boxes of side `s*t` are the
boxes of side `t` of the boxes of side `s`. -/
theorem boxes_mul {s t : ℤ} (hs : 0 < s) (_ht : 0 < t) (A : Finset ℤ) :
    boxes (s * t) A = boxes t (boxes s A) := by
  simp only [boxes, image_image, Function.comp_def, Int.ediv_ediv_of_nonneg hs.le]

/-- Coarser boxes are fewer: for `0 < s`, `0 < t`, `N (s*t) A ≤ N s A`. -/
theorem N_mul_le {s t : ℤ} (hs : 0 < s) (ht : 0 < t) (A : Finset ℤ) :
    N (s * t) A ≤ N s A := by
  rw [N, boxes_mul hs ht]; exact card_image_le

/-- Planar boxes of side `s`: componentwise floor division. -/
def boxes2 (s : ℤ) (P : Finset (ℤ × ℤ)) : Finset (ℤ × ℤ) :=
  P.image (fun p => (p.1 / s, p.2 / s))

/-- The planar box count at box side `s`. -/
def N2 (s : ℤ) (P : Finset (ℤ × ℤ)) : ℕ := (boxes2 s P).card

/-- Product law for boxes: the planar boxes of `A × B` are the products of the
boxes of `A` and of `B`. -/
theorem boxes2_prod (s : ℤ) (A B : Finset ℤ) :
    boxes2 s (A ×ˢ B) = boxes s A ×ˢ boxes s B := by
  ext ⟨x, y⟩
  simp only [boxes2, boxes, mem_image, mem_product, Prod.exists, Prod.mk.injEq]
  constructor
  · rintro ⟨a, b, ⟨ha, hb⟩, rfl, rfl⟩
    exact ⟨⟨a, ha, rfl⟩, ⟨b, hb, rfl⟩⟩
  · rintro ⟨⟨a, ha, rfl⟩, ⟨b, hb, rfl⟩⟩
    exact ⟨a, b, ⟨ha, hb⟩, rfl, rfl⟩

/-- Product law for box counts: `N2 s (A ×ˢ B) = N s A * N s B`, exactly. -/
theorem N2_prod (s : ℤ) (A B : Finset ℤ) : N2 s (A ×ˢ B) = N s A * N s B := by
  rw [N2, boxes2_prod, card_product, N, N]

/-- Product law at the granule scale: `#(A × B) = #A · #B`. -/
theorem card_prod (A B : Finset ℤ) : (A ×ˢ B).card = A.card * B.card :=
  card_product _ _

/-- At box side `1` the planar box count is the number of points. -/
theorem N2_one (P : Finset (ℤ × ℤ)) : N2 1 P = P.card := by
  simp [N2, boxes2]

/-- The box-counting dimension of `A` between box sides `s₁ < s₂`:
`log (N s₁ A / N s₂ A) / log (s₂ / s₁)`. -/
noncomputable def dimBetween (s₁ s₂ : ℤ) (A : Finset ℤ) : ℝ :=
  Real.log ((N s₁ A : ℝ) / N s₂ A) / Real.log ((s₂ : ℝ) / s₁)

/-- The planar box-counting dimension between box sides `s₁` and `s₂`. -/
noncomputable def dimBetween2 (s₁ s₂ : ℤ) (P : Finset (ℤ × ℤ)) : ℝ :=
  Real.log ((N2 s₁ P : ℝ) / N2 s₂ P) / Real.log ((s₂ : ℝ) / s₁)

/-- Exact additivity of the dimension between two scales on products: for
nonempty `A`, `B`, `dimBetween2 s₁ s₂ (A ×ˢ B) = dimBetween s₁ s₂ A +
dimBetween s₁ s₂ B` (no limit is taken). -/
theorem dimBetween2_prod (s₁ s₂ : ℤ) {A B : Finset ℤ} (hA : A.Nonempty)
    (hB : B.Nonempty) :
    dimBetween2 s₁ s₂ (A ×ˢ B) = dimBetween s₁ s₂ A + dimBetween s₁ s₂ B := by
  have h1 : (N s₁ A : ℝ) ≠ 0 := by exact_mod_cast (N_pos s₁ hA).ne'
  have h2 : (N s₂ A : ℝ) ≠ 0 := by exact_mod_cast (N_pos s₂ hA).ne'
  have h3 : (N s₁ B : ℝ) ≠ 0 := by exact_mod_cast (N_pos s₁ hB).ne'
  have h4 : (N s₂ B : ℝ) ≠ 0 := by exact_mod_cast (N_pos s₂ hB).ne'
  unfold dimBetween2 dimBetween
  rw [N2_prod, N2_prod, Nat.cast_mul, Nat.cast_mul, mul_div_mul_comm,
    Real.log_mul (div_ne_zero h1 h2) (div_ne_zero h3 h4), add_div]

/-- The granule-scale dimension `log #A / log L`, where `L` is the number of
granules per unit length (a real number for every finite set). -/
noncomputable def dimGranule {α : Type*} (A : Finset α) (L : ℝ) : ℝ :=
  Real.log A.card / Real.log L

/-- The granule-scale dimension of a planar set. -/
noncomputable def dimGranule2 (P : Finset (ℤ × ℤ)) (L : ℝ) : ℝ :=
  Real.log P.card / Real.log L

/-- The granule-scale dimension is always defined and exactly encodes the
count: for nonempty `A` and `1 < L`, `L ^ dimGranule A L = #A`. -/
theorem rpow_dimGranule {α : Type*} {A : Finset α} (hA : A.Nonempty) {L : ℝ}
    (hL : 1 < L) : L ^ dimGranule A L = A.card := by
  have hc : (0 : ℝ) < A.card := by exact_mod_cast card_pos.2 hA
  have hl : Real.log L ≠ 0 := (Real.log_pos hL).ne'
  rw [Real.rpow_def_of_pos (by linarith), dimGranule, mul_div_cancel₀ _ hl,
    Real.exp_log hc]

/-- The granule-scale dimension is nonnegative when `1 < L`. -/
theorem dimGranule_nonneg {α : Type*} (A : Finset α) {L : ℝ} (hL : 1 < L) :
    0 ≤ dimGranule A L :=
  div_nonneg (Real.log_natCast_nonneg _) (Real.log_pos hL).le

/-- Additivity of the granule-scale dimension on products of nonempty sets,
for any types: `dimGranule (A ×ˢ B) L = dimGranule A L + dimGranule B L`. -/
theorem dimGranule_prod {α β : Type*} {A : Finset α} {B : Finset β}
    (hA : A.Nonempty) (hB : B.Nonempty) (L : ℝ) :
    dimGranule (A ×ˢ B) L = dimGranule A L + dimGranule B L := by
  have h1 : (A.card : ℝ) ≠ 0 := by exact_mod_cast (card_pos.2 hA).ne'
  have h2 : (B.card : ℝ) ≠ 0 := by exact_mod_cast (card_pos.2 hB).ne'
  unfold dimGranule
  rw [card_product, Nat.cast_mul, Real.log_mul h1 h2, add_div]

/-- Additivity of the planar granule-scale dimension: for nonempty
`A B : Finset ℤ`, `dimGranule2 (A ×ˢ B) L = dimGranule A L + dimGranule B L`. -/
theorem dimGranule2_prod {A B : Finset ℤ} (hA : A.Nonempty) (hB : B.Nonempty)
    (L : ℝ) : dimGranule2 (A ×ˢ B) L = dimGranule A L + dimGranule B L :=
  dimGranule_prod hA hB L

/-! ## B. Digit (b-adic self-similar) sets -/

/-- The level-`K` digit set: `digitSet b D 0 = {0}` and level `K+1` consists of
the numbers `b x + d` with `x` at level `K` and `d ∈ D`.  (Indices in `ℕ`.) -/
def digitSet (b : ℕ) (D : Finset ℕ) : ℕ → Finset ℕ
  | 0 => {0}
  | K + 1 => ((digitSet b D K) ×ˢ D).image (fun p => b * p.1 + p.2)

@[simp] theorem digitSet_zero (b : ℕ) (D : Finset ℕ) : digitSet b D 0 = {0} := rfl

theorem digitSet_succ (b : ℕ) (D : Finset ℕ) (K : ℕ) :
    digitSet b D (K + 1) = ((digitSet b D K) ×ˢ D).image (fun p => b * p.1 + p.2) :=
  rfl

/-- Division by `b` strips the last digit: for `d < b`, `(b x + d) / b = x`. -/
theorem digit_div {b x d : ℕ} (hd : d < b) : (b * x + d) / b = x := by
  have hb : 0 < b := lt_of_le_of_lt (Nat.zero_le _) hd
  rw [Nat.mul_add_div hb, Nat.div_eq_of_lt hd, add_zero]

/-- The remainder mod `b` is the last digit: for `d < b`, `(b x + d) % b = d`. -/
theorem digit_mod {b x d : ℕ} (hd : d < b) : (b * x + d) % b = d := by
  rw [Nat.mul_add_mod, Nat.mod_eq_of_lt hd]

/-- Base-`b` expansion is unique: `(x, d) ↦ b x + d` is injective on pairs with
`d < b`. -/
theorem digit_inj {b x d x' d' : ℕ} (hd : d < b) (hd' : d' < b)
    (h : b * x + d = b * x' + d') : x = x' ∧ d = d' := by
  refine ⟨?_, ?_⟩
  · rw [← digit_div (x := x) hd, h, digit_div hd']
  · rw [← digit_mod (x := x) hd, h, digit_mod hd']

/-- The exact count of a digit set: if every digit is `< b`, then
`#(digitSet b D K) = |D|^K`. -/
theorem card_digitSet {b : ℕ} {D : Finset ℕ} (hD : ∀ d ∈ D, d < b) (K : ℕ) :
    (digitSet b D K).card = D.card ^ K := by
  induction K with
  | zero => simp
  | succ K ih =>
    rw [digitSet_succ, card_image_of_injOn, card_product, ih, pow_succ]
    rintro ⟨x, d⟩ hp ⟨x', d'⟩ hp' h
    simp only [coe_product, Set.mem_prod, mem_coe] at hp hp'
    obtain ⟨h1, h2⟩ := digit_inj (hD d hp.2) (hD d' hp'.2) h
    exact Prod.ext h1 h2

/-- Exact coarse-graining: if `D` is nonempty and every digit is `< b`, the
floor quotients by `b` of level `K+1` are exactly level `K` (`ℕ` division). -/
theorem digitSet_coarse {b : ℕ} {D : Finset ℕ} (hD : ∀ d ∈ D, d < b)
    (hne : D.Nonempty) (K : ℕ) :
    (digitSet b D (K + 1)).image (· / b) = digitSet b D K := by
  rw [digitSet_succ, image_image]
  ext x
  simp only [mem_image, mem_product, Function.comp_apply, Prod.exists]
  constructor
  · rintro ⟨y, d, ⟨hy, hd⟩, rfl⟩
    rw [digit_div (hD d hd)]; exact hy
  · intro hx
    obtain ⟨d, hd⟩ := hne
    exact ⟨x, d, ⟨hx, hd⟩, digit_div (hD d hd)⟩

/-- Exact box sets of a digit set: for `j ≤ K`, the boxes of side `b^j`
(floor division in `ℕ`) met by level `K` are exactly level `K - j`
(`D` nonempty, digits `< b`). -/
theorem digitSet_boxes {b : ℕ} {D : Finset ℕ} (hD : ∀ d ∈ D, d < b)
    (hne : D.Nonempty) {j K : ℕ} (hj : j ≤ K) :
    (digitSet b D K).image (· / b ^ j) = digitSet b D (K - j) := by
  induction j with
  | zero => simp
  | succ j ih =>
    have hK : K - j = (K - (j + 1)) + 1 := by omega
    have : (fun x : ℕ => x / b ^ (j + 1)) = (fun x => x / b) ∘ (fun x => x / b ^ j) := by
      funext x; simp [pow_succ, Nat.div_div_eq_div_mul]
    rw [this, ← image_image, ih (by omega), hK, digitSet_coarse hD hne]

/-- Exact box counts of a digit set: for `j ≤ K`, level `K` meets exactly
`|D|^(K-j)` boxes of side `b^j` (floor division in `ℕ`; `D` nonempty,
digits `< b`). -/
theorem card_digitSet_boxes {b : ℕ} {D : Finset ℕ} (hD : ∀ d ∈ D, d < b)
    (hne : D.Nonempty) {j K : ℕ} (hj : j ≤ K) :
    ((digitSet b D K).image (· / b ^ j)).card = D.card ^ (K - j) := by
  rw [digitSet_boxes hD hne hj, card_digitSet hD]

/-- Box count in `ℕ`: the number of boxes of side `s` (floor division) met by
`A : Finset ℕ`. -/
def NN (s : ℕ) (A : Finset ℕ) : ℕ := (A.image (· / s)).card

/-- The dimension between box sides `s₁` and `s₂` for sets of natural indices:
`log (NN s₁ A / NN s₂ A) / log (s₂ / s₁)`. -/
noncomputable def dimBetweenN (s₁ s₂ : ℕ) (A : Finset ℕ) : ℝ :=
  Real.log ((NN s₁ A : ℝ) / NN s₂ A) / Real.log ((s₂ : ℝ) / s₁)

/-- Real-number identity used for exact dimensions: if `i < j ≤ K` and `c ≠ 0`,
`log (c^(K-i) / c^(K-j)) / log (β^j / β^i) = log c / log β` for `β ≠ 0`. -/
theorem log_ratio_pow {c β : ℝ} (hc : c ≠ 0) (hβ : β ≠ 0) {i j K : ℕ}
    (hij : i < j) (hjK : j ≤ K) :
    Real.log (c ^ (K - i) / c ^ (K - j)) / Real.log (β ^ j / β ^ i) =
      Real.log c / Real.log β := by
  have e1 : c ^ (K - i) / c ^ (K - j) = c ^ (j - i) := by
    rw [show K - i = (K - j) + (j - i) by omega, pow_add,
      mul_div_cancel_left₀ _ (pow_ne_zero _ hc)]
  have e2 : β ^ j / β ^ i = β ^ (j - i) := by
    rw [show j = i + (j - i) by omega, pow_add, mul_div_cancel_left₀ _ (pow_ne_zero _ hβ),
      show i + (j - i) - i = j - i by omega]
  have hn : ((j - i : ℕ) : ℝ) ≠ 0 := by exact_mod_cast (show j - i ≠ 0 by omega)
  rw [e1, e2, Real.log_pow, Real.log_pow, mul_div_mul_left _ _ hn]

/-- Exact dimension of a digit set between two scales: for `i < j ≤ K`, the
dimension of level `K` between box sides `b^i` and `b^j` is exactly
`log |D| / log b` (`2 ≤ b`, `D` nonempty, digits `< b`, `ℕ` division). -/
theorem dim_digitSet {b : ℕ} {D : Finset ℕ} (hb : 2 ≤ b) (hD : ∀ d ∈ D, d < b)
    (hne : D.Nonempty) {i j K : ℕ} (hij : i < j) (hjK : j ≤ K) :
    dimBetweenN (b ^ i) (b ^ j) (digitSet b D K) = Real.log D.card / Real.log b := by
  unfold dimBetweenN NN
  rw [card_digitSet_boxes hD hne (by omega), card_digitSet_boxes hD hne hjK]
  push_cast
  exact log_ratio_pow (by exact_mod_cast (card_pos.2 hne).ne')
    (by exact_mod_cast (show b ≠ 0 by omega)) hij hjK

/-- Exact granule-scale dimension of a digit set: for `K ≥ 1`,
`log #(digitSet b D K) / log (b^K) = log |D| / log b` (digits `< b`). -/
theorem dimGranule_digitSet {b : ℕ} {D : Finset ℕ} (hD : ∀ d ∈ D, d < b)
    {K : ℕ} (hK : 0 < K) :
    dimGranule (digitSet b D K) ((b : ℝ) ^ K) = Real.log D.card / Real.log b := by
  have hn : (K : ℝ) ≠ 0 := by exact_mod_cast hK.ne'
  rw [dimGranule, card_digitSet hD, Nat.cast_pow, Real.log_pow, Real.log_pow,
    mul_div_mul_left _ _ hn]

/-- The middle-thirds Cantor digit set has exactly `2^K` points at level `K`. -/
theorem card_cantor (K : ℕ) : (digitSet 3 {0, 2} K).card = 2 ^ K := by
  rw [card_digitSet (by decide)]; rfl

/-- The Cantor set has granule-scale dimension exactly `log 2 / log 3` at every
level `K ≥ 1`. -/
theorem dimGranule_cantor {K : ℕ} (hK : 0 < K) :
    dimGranule (digitSet 3 {0, 2} K) ((3 : ℝ) ^ K) = Real.log 2 / Real.log 3 := by
  have := dimGranule_digitSet (b := 3) (D := {0, 2}) (by decide) hK
  push_cast at this
  rw [this]; norm_num

/-! ### `n`-dimensional digit sets -/

/-- The level-`K` digit set in `ℕⁿ`: level `0` is `{0}` and level `K+1` consists
of the points `b • x + d` (componentwise) with `x` at level `K`, `d ∈ D`. -/
def digitSetN {n : ℕ} (b : ℕ) (D : Finset (Fin n → ℕ)) : ℕ → Finset (Fin n → ℕ)
  | 0 => {0}
  | K + 1 => ((digitSetN b D K) ×ˢ D).image (fun p => b • p.1 + p.2)

theorem digitSetN_succ {n : ℕ} (b : ℕ) (D : Finset (Fin n → ℕ)) (K : ℕ) :
    digitSetN b D (K + 1) = ((digitSetN b D K) ×ˢ D).image (fun p => b • p.1 + p.2) :=
  rfl

/-- The exact count of an `n`-dimensional digit set: if every coordinate of
every digit is `< b`, then `#(digitSetN b D K) = |D|^K`. -/
theorem card_digitSetN {n b : ℕ} {D : Finset (Fin n → ℕ)}
    (hD : ∀ d ∈ D, ∀ i, d i < b) (K : ℕ) :
    (digitSetN b D K).card = D.card ^ K := by
  induction K with
  | zero => simp [digitSetN]
  | succ K ih =>
    rw [digitSetN_succ, card_image_of_injOn, card_product, ih, pow_succ]
    rintro ⟨x, d⟩ hp ⟨x', d'⟩ hp' h
    simp only [coe_product, Set.mem_prod, mem_coe] at hp hp'
    have hc : ∀ i, x i = x' i ∧ d i = d' i := fun i =>
      digit_inj (hD d hp.2 i) (hD d' hp'.2 i) (by simpa using congrFun h i)
    simp only [Prod.mk.injEq]
    exact ⟨funext fun i => (hc i).1, funext fun i => (hc i).2⟩

/-- Componentwise floor division of a point of `ℕⁿ` by `s`. -/
def cdiv {n : ℕ} (s : ℕ) (x : Fin n → ℕ) : Fin n → ℕ := fun i => x i / s

/-- Exact coarse-graining in `n` dimensions: componentwise division by `b`
maps level `K+1` onto level `K` (`D` nonempty, coordinates `< b`). -/
theorem digitSetN_coarse {n b : ℕ} {D : Finset (Fin n → ℕ)}
    (hD : ∀ d ∈ D, ∀ i, d i < b) (hne : D.Nonempty) (K : ℕ) :
    (digitSetN b D (K + 1)).image (cdiv b) = digitSetN b D K := by
  have key : ∀ x d, d ∈ D → cdiv b (b • x + d) = x := fun x d hd =>
    funext fun i => by simp [cdiv, digit_div (hD d hd i)]
  rw [digitSetN_succ, image_image]
  ext x
  simp only [mem_image, mem_product, Function.comp_apply, Prod.exists]
  constructor
  · rintro ⟨y, d, ⟨hy, hd⟩, rfl⟩
    rw [key y d hd]; exact hy
  · intro hx
    obtain ⟨d, hd⟩ := hne
    exact ⟨x, d, ⟨hx, hd⟩, key x d hd⟩

/-- Exact box sets in `n` dimensions: for `j ≤ K`, the boxes of side `b^j`
(componentwise `ℕ` floor division) met by level `K` are exactly level `K - j`. -/
theorem digitSetN_boxes {n b : ℕ} {D : Finset (Fin n → ℕ)}
    (hD : ∀ d ∈ D, ∀ i, d i < b) (hne : D.Nonempty) {j K : ℕ} (hj : j ≤ K) :
    (digitSetN b D K).image (cdiv (b ^ j)) = digitSetN b D (K - j) := by
  induction j with
  | zero =>
    have : cdiv (n := n) (b ^ 0) = id := by funext x i; simp [cdiv]
    rw [this, image_id]; rfl
  | succ j ih =>
    have hK : K - j = (K - (j + 1)) + 1 := by omega
    have : cdiv (n := n) (b ^ (j + 1)) = cdiv b ∘ cdiv (b ^ j) := by
      funext x i; simp [cdiv, pow_succ, Nat.div_div_eq_div_mul]
    rw [this, ← image_image, ih (by omega), hK, digitSetN_coarse hD hne]

/-- Exact box counts in `n` dimensions: for `j ≤ K`, level `K` meets exactly
`|D|^(K-j)` boxes of side `b^j` (`D` nonempty, coordinates `< b`). -/
theorem card_digitSetN_boxes {n b : ℕ} {D : Finset (Fin n → ℕ)}
    (hD : ∀ d ∈ D, ∀ i, d i < b) (hne : D.Nonempty) {j K : ℕ} (hj : j ≤ K) :
    ((digitSetN b D K).image (cdiv (b ^ j))).card = D.card ^ (K - j) := by
  rw [digitSetN_boxes hD hne hj, card_digitSetN hD]

/-- The dimension between box sides `s₁` and `s₂` for sets in `ℕⁿ`. -/
noncomputable def dimBetweenNn {n : ℕ} (s₁ s₂ : ℕ) (A : Finset (Fin n → ℕ)) : ℝ :=
  Real.log (((A.image (cdiv s₁)).card : ℝ) / (A.image (cdiv s₂)).card) /
    Real.log ((s₂ : ℝ) / s₁)

/-- Exact dimension of an `n`-dimensional digit set between two scales: for
`i < j ≤ K` it equals `log |D| / log b` (`2 ≤ b`, `D` nonempty, coordinates
`< b`). -/
theorem dim_digitSetN {n b : ℕ} {D : Finset (Fin n → ℕ)} (hb : 2 ≤ b)
    (hD : ∀ d ∈ D, ∀ i, d i < b) (hne : D.Nonempty) {i j K : ℕ} (hij : i < j)
    (hjK : j ≤ K) :
    dimBetweenNn (b ^ i) (b ^ j) (digitSetN b D K) = Real.log D.card / Real.log b := by
  unfold dimBetweenNn
  rw [card_digitSetN_boxes hD hne (by omega), card_digitSetN_boxes hD hne hjK]
  push_cast
  exact log_ratio_pow (by exact_mod_cast (card_pos.2 hne).ne')
    (by exact_mod_cast (show b ≠ 0 by omega)) hij hjK

/-- Exact granule-scale dimension of an `n`-dimensional digit set: for `K ≥ 1`,
`log #(digitSetN b D K) / log (b^K) = log |D| / log b` (coordinates `< b`). -/
theorem dimGranule_digitSetN {n b : ℕ} {D : Finset (Fin n → ℕ)}
    (hD : ∀ d ∈ D, ∀ i, d i < b) {K : ℕ} (hK : 0 < K) :
    dimGranule (digitSetN b D K) ((b : ℝ) ^ K) = Real.log D.card / Real.log b := by
  have hn : (K : ℝ) ≠ 0 := by exact_mod_cast hK.ne'
  rw [dimGranule, card_digitSetN hD, Nat.cast_pow, Real.log_pow, Real.log_pow,
    mul_div_mul_left _ _ hn]

/-- The Sierpiński-carpet digits: the eight points of `{0,1,2}²` other than the
centre `(1,1)`. -/
def carpetDigits : Finset (Fin 2 → ℕ) :=
  ((Finset.univ : Finset (Fin 2 → Fin 3)).filter (fun f => f ≠ fun _ => 1)).image
    (fun f i => (f i : ℕ))

/-- Every coordinate of a carpet digit is `< 3`. -/
theorem carpetDigits_lt : ∀ d ∈ carpetDigits, ∀ i, d i < 3 := by
  intro d hd i
  simp only [carpetDigits, mem_image] at hd
  obtain ⟨f, -, rfl⟩ := hd
  exact (f i).isLt

/-- There are exactly eight carpet digits. -/
theorem card_carpetDigits : carpetDigits.card = 8 := by decide

/-- The Sierpiński carpet has exactly `8^K` points at level `K`. -/
theorem card_carpet (K : ℕ) : (digitSetN 3 carpetDigits K).card = 8 ^ K := by
  rw [card_digitSetN carpetDigits_lt, card_carpetDigits]

/-- The Sierpiński carpet has granule-scale dimension exactly `log 8 / log 3`
at every level `K ≥ 1`. -/
theorem dimGranule_carpet {K : ℕ} (hK : 0 < K) :
    dimGranule (digitSetN 3 carpetDigits K) ((3 : ℝ) ^ K) = Real.log 8 / Real.log 3 := by
  have := dimGranule_digitSetN (b := 3) carpetDigits_lt hK
  rw [card_carpetDigits] at this
  push_cast at this
  exact this

/-! ## C. Exact L-systems -/

section Lsystem

variable {G : Type*}

/-- One substitution step preserves the vector sum: if every letter's image
sums to the letter (`(σ v).sum = v`), then `(w.flatMap σ).sum = w.sum`. -/
theorem subst_sum [AddCommMonoid G] (σ : G → List G) (hσ : ∀ v, (σ v).sum = v)
    (w : List G) : (w.flatMap σ).sum = w.sum := by
  induction w with
  | nil => simp
  | cons a w ih => rw [List.flatMap_cons, List.sum_append, ih, hσ, List.sum_cons]

/-- Every iterate of a sum-preserving substitution preserves the vector sum:
`((fun w => w.flatMap σ)^[k] w).sum = w.sum` for all `k`. -/
theorem iterate_sum [AddCommMonoid G] (σ : G → List G) (hσ : ∀ v, (σ v).sum = v)
    (k : ℕ) (w : List G) : ((fun w => w.flatMap σ)^[k] w).sum = w.sum := by
  induction k with
  | zero => rfl
  | succ k ih => rw [Function.iterate_succ_apply', subst_sum σ hσ, ih]

/-- Deleting the zero letters of a word does not change its sum. -/
theorem filter_ne_zero_sum [AddCommMonoid G] [DecidableEq G] (w : List G) :
    (w.filter (fun g => g ≠ 0)).sum = w.sum := by
  induction w with
  | nil => simp
  | cons a w ih =>
    rw [List.filter_cons]
    split_ifs with h
    · rw [List.sum_cons, List.sum_cons, ih]
    · have h0 : a = 0 := by simpa using h
      rw [List.sum_cons, h0, zero_add, ih]

/-- The generator word of a polygonal path `q 0, q 1, …, q m`: its letters are
the steps `q (j+1) - q j`. -/
def genWord [AddCommGroup G] (q : ℕ → G) (m : ℕ) : List G :=
  (List.range m).map (fun j => q (j + 1) - q j)

/-- The steps of a polygonal path telescope: `(genWord q m).sum = q m - q 0`. -/
theorem genWord_sum [AddCommGroup G] (q : ℕ → G) (m : ℕ) :
    (genWord q m).sum = q m - q 0 := by
  induction m with
  | zero => simp [genWord]
  | succ m ih =>
    rw [genWord, List.range_succ, List.map_append, List.sum_append, ← genWord, ih]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
    abel

/-- Closure theorem for snapped generators: for any `snap : E → G`, any map
`T : E → E` and any points `p 0, …, p m`, if `snap (T (p 0)) = 0` and
`snap (T (p m)) = v`, the generator word of the snapped path
`q j = snap (T (p j))` sums exactly to `v`. -/
theorem snap_generator_closes {E : Type*} [AddCommGroup G] (snap : E → G)
    (T : E → E) (p : ℕ → E) (m : ℕ) {v : G} (h0 : snap (T (p 0)) = 0)
    (hm : snap (T (p m)) = v) :
    (genWord (fun j => snap (T (p j))) m).sum = v := by
  rw [genWord_sum, h0, hm, sub_zero]

/-- The turtle positions of a word: the partial sums `(w.take i).sum` for
`i = 0, …, w.length`. -/
def turtle [AddCommMonoid G] (w : List G) : List G :=
  (List.range (w.length + 1)).map (fun i => (w.take i).sum)

theorem turtle_ne_nil [AddCommMonoid G] (w : List G) : turtle w ≠ [] := by
  simp [turtle]

/-- The last turtle position of a word is the sum of the word. -/
theorem turtle_getLast [AddCommMonoid G] (w : List G) :
    (turtle w).getLast (turtle_ne_nil w) = w.sum := by
  simp [turtle]

/-- The turtle endpoint is exact at every depth: after `k` substitution steps
the last turtle position is still the sum of the axiom word. -/
theorem turtle_endpoint_iterate [AddCommMonoid G] (σ : G → List G)
    (hσ : ∀ v, (σ v).sum = v) (k : ℕ) (w : List G) :
    (turtle ((fun w => w.flatMap σ)^[k] w)).getLast (turtle_ne_nil _) = w.sum := by
  rw [turtle_getLast, iterate_sum σ hσ]

end Lsystem

section Snap

variable {E : Type*} [SeminormedAddCommGroup E]

/-- Snap error bound: if `‖snap x - x‖ ≤ δ` for all `x`, then
`‖snap a - snap b‖ ≤ ‖a - b‖ + 2δ`. -/
theorem snap_dist_le (snap : E → E) {δ : ℝ} (h : ∀ x, ‖snap x - x‖ ≤ δ) (a b : E) :
    ‖snap a - snap b‖ ≤ ‖a - b‖ + 2 * δ := by
  have e : snap a - snap b = (snap a - a) + (a - b) + (b - snap b) := by abel
  have hb : ‖b - snap b‖ ≤ δ := by rw [norm_sub_rev]; exact h b
  rw [e]
  calc ‖(snap a - a) + (a - b) + (b - snap b)‖
      ≤ ‖snap a - a‖ + ‖a - b‖ + ‖b - snap b‖ := norm_add₃_le
    _ ≤ δ + ‖a - b‖ + δ := by linarith [h a]
    _ = ‖a - b‖ + 2 * δ := by ring

/-- Composition of the maps of a word: `comp f [] = id` and
`comp f (i :: w) x = f i (comp f w x)`, i.e. `comp f [i₁, …, iₙ] = f i₁ ∘ ⋯ ∘ f iₙ`
(the last letter is applied first). -/
def comp {ι : Type*} (f : ι → E → E) : List ι → E → E
  | [] => id
  | i :: w => f i ∘ comp f w

/-- Error of a snapped iterated function system: if each `f i` is
`r`-Lipschitz (`r ≥ 0`) and `‖fhat i x - f i x‖ ≤ δ`, then for every word `w`
and point `x`, `‖comp fhat w x - comp f w x‖ ≤ δ * ∑_{j < |w|} r^j`. -/
theorem comp_snap_error {ι : Type*} (f fhat : ι → E → E) {r δ : ℝ} (hr : 0 ≤ r)
    (hf : ∀ i x y, ‖f i x - f i y‖ ≤ r * ‖x - y‖)
    (hfhat : ∀ i x, ‖fhat i x - f i x‖ ≤ δ) (w : List ι) (x : E) :
    ‖comp fhat w x - comp f w x‖ ≤ δ * ∑ j ∈ range w.length, r ^ j := by
  induction w with
  | nil => simp [comp]
  | cons i w ih =>
    simp only [comp, Function.comp_apply, List.length_cons]
    set y := comp fhat w x
    set z := comp f w x
    have e : fhat i y - f i z = (fhat i y - f i y) + (f i y - f i z) := by abel
    have hsum : δ * ∑ j ∈ range (w.length + 1), r ^ j =
        δ + r * (δ * ∑ j ∈ range w.length, r ^ j) := by
      have hs : ∑ j ∈ range w.length, r ^ (j + 1) = r * ∑ j ∈ range w.length, r ^ j := by
        rw [mul_sum]; exact sum_congr rfl fun j _ => by ring
      rw [sum_range_succ', hs]; ring
    rw [e, hsum]
    calc ‖(fhat i y - f i y) + (f i y - f i z)‖
        ≤ ‖fhat i y - f i y‖ + ‖f i y - f i z‖ := norm_add_le _ _
      _ ≤ δ + r * ‖y - z‖ := add_le_add (hfhat i y) (hf i y z)
      _ ≤ δ + r * (δ * ∑ j ∈ range w.length, r ^ j) := by
        gcongr

/-- Uniform error of a snapped contracting IFS: if each `f i` is `r`-Lipschitz
with `0 ≤ r < 1`, `‖fhat i x - f i x‖ ≤ δ` and `0 ≤ δ`, then for every word
`w` (of any length) `‖comp fhat w x - comp f w x‖ ≤ δ / (1 - r)`. -/
theorem comp_snap_error_le {ι : Type*} (f fhat : ι → E → E) {r δ : ℝ} (hr : 0 ≤ r)
    (hr1 : r < 1) (hδ : 0 ≤ δ) (hf : ∀ i x y, ‖f i x - f i y‖ ≤ r * ‖x - y‖)
    (hfhat : ∀ i x, ‖fhat i x - f i x‖ ≤ δ) (w : List ι) (x : E) :
    ‖comp fhat w x - comp f w x‖ ≤ δ / (1 - r) := by
  refine (comp_snap_error f fhat hr hf hfhat w x).trans ?_
  have h1r : 0 < 1 - r := by linarith
  have hg : ∑ j ∈ range w.length, r ^ j ≤ 1 / (1 - r) := by
    rw [geom_sum_eq hr1.ne, show r ^ w.length - 1 = -(1 - r ^ w.length) by ring,
      show r - 1 = -(1 - r) by ring, neg_div_neg_eq]
    exact div_le_div_of_nonneg_right (by linarith [pow_nonneg hr w.length]) h1r.le
  calc δ * ∑ j ∈ range w.length, r ^ j ≤ δ * (1 / (1 - r)) :=
        mul_le_mul_of_nonneg_left hg hδ
    _ = δ / (1 - r) := by ring

end Snap

/-! ## D. Shadow: comparison with the classical limit -/

open Filter Topology Hyperreal ArchimedeanClass

/-- Shadow of the granule dimension: if the sequence `dim K` of granule
dimensions (at scales `b^{-K}`) tends to `L`, then the hyperreal
`Hyperreal.ofSeq dim` has standard part `L`. -/
theorem granule_dim_shadow (dim : ℕ → ℝ) {L : ℝ} (h : Tendsto dim atTop (𝓝 L)) :
    stdPart (ofSeq dim) = L :=
  stdPart_of_tendsto (tendsto_ofSeq.2
    (h.mono_left (hyperfilter_le_cofinite.trans Nat.cofinite_eq_atTop.le)))

/-- Shadow of a digit set's dimension: the hyperreal of granule dimensions
`K ↦ dimGranule (digitSet b D K) (b^K)` has standard part exactly
`log |D| / log b` (digits `< b`). -/
theorem digitSet_dim_shadow {b : ℕ} {D : Finset ℕ} (hD : ∀ d ∈ D, d < b) :
    stdPart (ofSeq fun K => dimGranule (digitSet b D K) ((b : ℝ) ^ K)) =
      Real.log D.card / Real.log b := by
  apply granule_dim_shadow
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with K hK
  exact (dimGranule_digitSet hD hK).symm

/-- Bounds pass to the shadow: if eventually `a ≤ dim K ≤ c`, then
`a ≤ st (ofSeq dim) ≤ c`. -/
theorem granule_dim_shadow_bounds (dim : ℕ → ℝ) {a c : ℝ}
    (h : ∀ᶠ K in atTop, a ≤ dim K ∧ dim K ≤ c) :
    a ≤ stdPart (ofSeq dim) ∧ stdPart (ofSeq dim) ≤ c := by
  have h' : ∀ᶠ K in (hyperfilter ℕ : Filter ℕ), a ≤ dim K ∧ dim K ≤ c :=
    h.filter_mono (hyperfilter_le_cofinite.trans Nat.cofinite_eq_atTop.le)
  have ha : ((a : ℝ*)) ≤ ofSeq dim := Germ.coe_le.2 (h'.mono fun _ hK => hK.1)
  have hc : ofSeq dim ≤ ((c : ℝ*)) := Germ.coe_le.2 (h'.mono fun _ hK => hK.2)
  have hmk : 0 ≤ ArchimedeanClass.mk (ofSeq dim) :=
    ArchimedeanClass.mk_nonneg_of_le_of_le_of_archimedean coeRingHom ha hc
  exact ⟨ArchimedeanClass.le_stdPart_of_le coeRingHom hmk ha,
    ArchimedeanClass.stdPart_le_of_le coeRingHom hmk hc⟩

/-- The shadow lies between liminf and limsup: for a bounded sequence `dim`
(`a ≤ dim K ≤ c` for all `K`),
`liminf dim ≤ st (ofSeq dim) ≤ limsup dim`. -/
theorem granule_dim_shadow_liminf_limsup (dim : ℕ → ℝ) {a c : ℝ}
    (h : ∀ K, a ≤ dim K ∧ dim K ≤ c) :
    liminf dim atTop ≤ stdPart (ofSeq dim) ∧ stdPart (ofSeq dim) ≤ limsup dim atTop := by
  have hbu : IsBoundedUnder (· ≤ ·) atTop dim :=
    isBoundedUnder_of ⟨c, fun K => (h K).2⟩
  have hbl : IsBoundedUnder (· ≥ ·) atTop dim :=
    isBoundedUnder_of ⟨a, fun K => (h K).1⟩
  constructor
  · refine le_of_forall_lt_imp_le_of_dense fun s hs => ?_
    have hev : ∀ᶠ K in atTop, s < dim K :=
      eventually_lt_of_lt_liminf hs hbl
    exact (granule_dim_shadow_bounds dim (a := s) (c := c)
      (hev.mono fun K hK => ⟨hK.le, (h K).2⟩)).1
  · refine le_of_forall_gt_imp_ge_of_dense fun s hs => ?_
    have hev : ∀ᶠ K in atTop, dim K < s :=
      eventually_lt_of_limsup_lt hs hbu
    exact (granule_dim_shadow_bounds dim (a := a) (c := s)
      (hev.mono fun K hK => ⟨(h K).1, hK.le⟩)).2

/-! ## E. The Cantor set and Cantor dust, granularly -/

/-- The level-`K` Cantor set: the triadic digit set with digits `{0, 2}`. -/
def cantor (K : ℕ) : Finset ℕ := digitSet 3 {0, 2} K

/-- The level-`K` Cantor set has exactly `2^K` points. -/
theorem card_cantorSet (K : ℕ) : (cantor K).card = 2 ^ K := card_cantor K

section CantorField

variable {F : Type*} [Field F] [LinearOrder F] [IsStrictOrderedRing F]

set_option linter.unusedSectionVars false in
/-- Granular measure of the Cantor set on the triadic lattice of spacing
`h = 3^{-K}`, over any linearly ordered field: `#C_K · h = (2/3)^K`, exactly. -/
theorem cantor_measure (K : ℕ) :
    ((cantor K).card : F) * ((3 : F) ^ K)⁻¹ = (2 / 3) ^ K := by
  rw [card_cantorSet, Nat.cast_pow, div_pow, div_eq_mul_inv]; norm_num

/-- The same in the book's notation: with `2ε = 3^{-K}` and the Cantor points
as integer indices, `QE.mu ε C_K = (2/3)^K`, over any linearly ordered field. -/
theorem cantor_mu (K : ℕ) :
    QE.mu (((3 : F) ^ K)⁻¹ / 2) ((cantor K).image (Nat.cast : ℕ → ℤ)) = (2 / 3) ^ K := by
  rw [QE.mu, card_image_of_injective _ Nat.cast_injective, ← cantor_measure K]
  ring

/-- The granular measure of the Cantor set is strictly positive at every
level: `0 < (2/3)^K` (over any linearly ordered field). -/
theorem cantor_measure_pos (K : ℕ) : (0 : F) < (2 / 3) ^ K :=
  pow_pos (by norm_num) K

/-- The granular measure of the Cantor set strictly decreases with the level:
`(2/3)^(K+1) < (2/3)^K`. -/
theorem cantor_measure_strictAnti (K : ℕ) : (2 / 3 : F) ^ (K + 1) < (2 / 3) ^ K := by
  rw [pow_succ]
  have := cantor_measure_pos (F := F) K
  nlinarith

/-- The granular measure is bounded by its value at any coarser level:
for `K ≤ K'`, `(2/3)^K' ≤ (2/3)^K`. -/
theorem cantor_measure_le {K K' : ℕ} (h : K ≤ K') : (2 / 3 : F) ^ K' ≤ (2 / 3) ^ K :=
  pow_le_pow_of_le_one (by norm_num) (by norm_num) h

end CantorField

/-- Shadow: the granular measure `(2/3)^K` of the Cantor set tends to `0`
(the classical Lebesgue value is the shadow; no measure theory is used). -/
theorem cantor_measure_tendsto_zero :
    Tendsto (fun K : ℕ => ((2 : ℝ) / 3) ^ K) atTop (𝓝 0) :=
  tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)

/-- The level-`K` Cantor set has granule-scale dimension exactly
`log 2 / log 3` for `K ≥ 1`. -/
theorem dimGranule_cantorSet {K : ℕ} (hK : 0 < K) :
    dimGranule (cantor K) ((3 : ℝ) ^ K) = Real.log 2 / Real.log 3 :=
  dimGranule_cantor hK

/-- The level-`K` Cantor dust `C_K × C_K` has exactly `4^K = (2^K)^2` points. -/
theorem card_cantorDust (K : ℕ) :
    (cantor K ×ˢ cantor K).card = 4 ^ K ∧ (cantor K ×ˢ cantor K).card = (2 ^ K) ^ 2 := by
  rw [card_product, card_cantorSet]
  constructor
  · rw [← mul_pow]; norm_num
  · ring

/-- The Cantor dust has granule-scale dimension exactly `2 · log 2 / log 3`
at every level `K ≥ 1`, by additivity of the granule dimension on products. -/
theorem dimGranule_cantorDust {K : ℕ} (hK : 0 < K) :
    dimGranule (cantor K ×ˢ cantor K) ((3 : ℝ) ^ K) = 2 * Real.log 2 / Real.log 3 := by
  have hne : (cantor K).Nonempty := by
    rw [← card_pos, card_cantorSet]; exact pow_pos (by norm_num) K
  rw [dimGranule_prod hne hne, dimGranule_cantorSet hK]
  ring

/-! ## F. The finite diagonal argument -/

/-- Finite diagonal argument: for any list `f : Fin K → (Fin K → Bool)` of `K`
bit strings of length `K`, the diagonal `fun i => !(f i i)` differs from every
`f j`. -/
theorem diagonal_not_in_list {K : ℕ} (f : Fin K → (Fin K → Bool)) :
    ∀ j, (fun i => !(f i i)) ≠ f j := by
  intro j h
  have := congrFun h j
  simp at this

/-- The diagonal of a short list: for `f : Fin M → (Fin K → Bool)` with
`M ≤ K`, the string that flips `f i` at coordinate `i` for `i < M` (and is
`false` elsewhere) differs from every `f j`. -/
theorem diagonal_not_in_short_list {M K : ℕ} (hMK : M ≤ K) (f : Fin M → (Fin K → Bool)) :
    ∀ j, (fun i : Fin K => if h : i.val < M then !(f ⟨i.val, h⟩ i) else false) ≠ f j := by
  intro j h
  have := congrFun h ⟨j.val, lt_of_lt_of_le j.isLt hMK⟩
  simp [j.isLt] at this

/-- A list of `K` bit strings of length `K` contains at most `K` distinct
strings: `(univ.image f).card ≤ K`. -/
theorem card_image_list_le {K : ℕ} (f : Fin K → (Fin K → Bool)) :
    (univ.image f).card ≤ K :=
  card_image_le.trans (by simp)

/-- There are exactly `2^K` bit strings of length `K`. -/
theorem card_bitStrings (K : ℕ) : (univ : Finset (Fin K → Bool)).card = 2 ^ K := by
  simp

/-- Exact counting form of the diagonal argument: at least `2^K - K` bit
strings of length `K` are missed by any list of `K` of them. -/
theorem card_missed_ge {K : ℕ} (f : Fin K → (Fin K → Bool)) :
    2 ^ K - K ≤ (univ \ univ.image f).card := by
  rw [card_sdiff_of_subset (subset_univ _), card_bitStrings]
  exact Nat.sub_le_sub_left (card_image_list_le f) _

/-- `K < 2^K` for every `K`. -/
theorem lt_two_pow (K : ℕ) : K < 2 ^ K := Nat.lt_two_pow_self

/-- No list of `K` bit strings of length `K` covers all `2^K` strings: the
list is not surjective, and its image is not all of `Fin K → Bool`. -/
theorem list_not_covers {K : ℕ} (f : Fin K → (Fin K → Bool)) :
    ¬ Function.Surjective f ∧ univ.image f ≠ univ := by
  refine ⟨fun hs => ?_, fun he => ?_⟩
  · obtain ⟨j, hj⟩ := hs (fun i => !(f i i))
    exact diagonal_not_in_list f j hj.symm
  · have h1 := card_image_list_le f
    rw [he, card_bitStrings] at h1
    exact absurd h1 (not_le.2 (lt_two_pow K))

/-- Shadow (classical comparison): Cantor's theorem, `f : α → Set α` is never
surjective (Mathlib's `Function.cantor_surjective`). -/
theorem cantor_shadow {α : Type*} (f : α → Set α) : ¬ Function.Surjective f :=
  Function.cantor_surjective f

/-! ## G. Error of segment-wise snapping (the D0L construction) -/

section SegmentSnap

variable {𝕜 : Type*} [NormedField 𝕜] {E : Type*} [SeminormedAddCommGroup E]
  [NormedSpace 𝕜 E]

/-- Error of one snapped affine vertex: if `‖snap x - x‖ ≤ δ` for all `x`, then
for any scalar `t` (e.g. `t : ℂ` for vertices off the base line),
`‖snap (a + t • (b - a)) - (A + t • (B - A))‖ ≤ δ + ‖1 - t‖ ‖a - A‖ + ‖t‖ ‖b - B‖`. -/
theorem affine_snap_error (snap : E → E) {δ : ℝ} (h : ∀ x, ‖snap x - x‖ ≤ δ)
    (t : 𝕜) (a b A B : E) :
    ‖snap (a + t • (b - a)) - (A + t • (B - A))‖ ≤
      δ + ‖1 - t‖ * ‖a - A‖ + ‖t‖ * ‖b - B‖ := by
  set y := a + t • (b - a)
  have e : snap y - (A + t • (B - A)) =
      (snap y - y) + ((1 - t) • (a - A) + t • (b - B)) := by
    simp only [y, sub_smul, one_smul, smul_sub]; abel
  rw [e]
  calc ‖(snap y - y) + ((1 - t) • (a - A) + t • (b - B))‖
      ≤ ‖snap y - y‖ + (‖(1 - t) • (a - A)‖ + ‖t • (b - B)‖) :=
        (norm_add_le _ _).trans (by gcongr; exact norm_add_le _ _)
    _ ≤ δ + (‖1 - t‖ * ‖a - A‖ + ‖t‖ * ‖b - B‖) := by
        rw [norm_smul, norm_smul]; linarith [h y]
    _ = δ + ‖1 - t‖ * ‖a - A‖ + ‖t‖ * ‖b - B‖ := by ring

/-- Error of one snapped affine vertex, max form: with `c = ‖1 - t‖ + ‖t‖` and
`e = max ‖a - A‖ ‖b - B‖`, `‖snap (a + t • (b - a)) - (A + t • (B - A))‖ ≤ δ + c * e`. -/
theorem affine_snap_error_max (snap : E → E) {δ : ℝ} (h : ∀ x, ‖snap x - x‖ ≤ δ)
    (t : 𝕜) (a b A B : E) :
    ‖snap (a + t • (b - a)) - (A + t • (B - A))‖ ≤
      δ + (‖1 - t‖ + ‖t‖) * max ‖a - A‖ ‖b - B‖ := by
  refine (affine_snap_error snap h t a b A B).trans ?_
  have h1 : ‖1 - t‖ * ‖a - A‖ ≤ ‖1 - t‖ * max ‖a - A‖ ‖b - B‖ :=
    mul_le_mul_of_nonneg_left (le_max_left _ _) (norm_nonneg _)
  have h2 : ‖t‖ * ‖b - B‖ ≤ ‖t‖ * max ‖a - A‖ ‖b - B‖ :=
    mul_le_mul_of_nonneg_left (le_max_right _ _) (norm_nonneg _)
  nlinarith

/-- The affine error constant is at least one: `1 ≤ ‖1 - t‖ + ‖t‖` for every
scalar `t` (triangle inequality). -/
theorem one_le_affine_const (t : 𝕜) : 1 ≤ ‖1 - t‖ + ‖t‖ := by
  calc (1 : ℝ) = ‖(1 - t) + t‖ := by rw [sub_add_cancel, norm_one]
    _ ≤ ‖1 - t‖ + ‖t‖ := norm_add_le _ _

end SegmentSnap

/-- Error recursion: if `e 0 = 0`, `0 ≤ c` and `e (k+1) ≤ c * e k + δ` for all
`k`, then `e k ≤ δ * ∑_{j < k} c^j` for all `k`.  (`δ` may have any sign.) -/
theorem error_recursion (e : ℕ → ℝ) {c δ : ℝ} (h0 : e 0 = 0) (hc : 0 ≤ c)
    (hrec : ∀ k, e (k + 1) ≤ c * e k + δ) (k : ℕ) :
    e k ≤ δ * ∑ j ∈ range k, c ^ j := by
  induction k with
  | zero => simp [h0]
  | succ k ih =>
    have hs : ∑ j ∈ range k, c ^ (j + 1) = c * ∑ j ∈ range k, c ^ j := by
      rw [mul_sum]; exact sum_congr rfl fun j _ => by ring
    have : δ * ∑ j ∈ range (k + 1), c ^ j = c * (δ * ∑ j ∈ range k, c ^ j) + δ := by
      rw [sum_range_succ', hs]; ring
    rw [this]
    exact (hrec k).trans (by nlinarith)

/-- Error recursion, closed form: under the hypotheses of `error_recursion` and
`c ≠ 1`, `e k ≤ δ * (c^k - 1) / (c - 1)`. -/
theorem error_recursion_closed (e : ℕ → ℝ) {c δ : ℝ} (h0 : e 0 = 0) (hc : 0 ≤ c)
    (hc1 : c ≠ 1) (hrec : ∀ k, e (k + 1) ≤ c * e k + δ) (k : ℕ) :
    e k ≤ δ * (c ^ k - 1) / (c - 1) := by
  have := error_recursion e h0 hc hrec k
  rwa [geom_sum_eq hc1, ← mul_div_assoc] at this

/-! ## H. Point-wise snapping -/

/-- Point-wise snapping: if every vertex is `snap x` of the exact classical
vertex `x` and `‖snap x - x‖ ≤ δ` for all `x`, then every vertex is within `δ`
of its classical position. -/
theorem point_snap_error {E : Type*} [SeminormedAddCommGroup E] (snap : E → E) {δ : ℝ}
    (h : ∀ x, ‖snap x - x‖ ≤ δ) (p : ℕ → E) (j : ℕ) : ‖snap (p j) - p j‖ ≤ δ :=
  h (p j)

/-- The telescoped word of point-wise snapped vertices sums to the snapped
endpoint difference: `(genWord (fun j => snap (p j)) m).sum = snap (p m) - snap (p 0)`. -/
theorem point_snap_word_sum {E : Type*} [AddCommGroup E] (snap : E → E) (p : ℕ → E)
    (m : ℕ) : (genWord (fun j => snap (p j)) m).sum = snap (p m) - snap (p 0) :=
  genWord_sum _ m

end QE.Fractal
