-- SPDX-License-Identifier: MIT
-- Copyright 2026 Metere Industries, Inc. Author: Alfredo Metere.
-- Quasi-Euclidean Granular Geometry. Any derivative work must carry this notice:
--   This work is derivative of the Quasi-Euclidean Granular Geometry book
--   authored by Alfredo Metere. Copyright 2026 Metere Industries, Inc.
--   All rights reserved
-- See LICENSE.md and NOTICE.

import QuasiEuclidean.Basic

/-!
# Chapter 15b: Learning machines — the solution space of a model

Everything here is an exact finitary statement about lattice points, finite
sums and finite products.  No Lebesgue measure and no integral is used: the
content of a set of parameters is its number of lattice points, probabilities
are weighted counts on finite sample spaces, and expectations are finite sums.

Contents (namespace `QE.Learn`):
* parameter boxes and their counts `(2M+1)^N`;
* the snap (round-half-up) and the quantisation algebra: idempotence, odd
  ratios nest, even ratios have an exact double-rounding defect, the carry of
  `snap (a+b)`, error cosets, cell counts `r^N`, rescaling;
* stagnation of rounded gradient descent, stochastic rounding (exact
  unbiasedness, also with finitely many random bits);
* eventual periodicity of deterministic training;
* granular charts, solution counts, faithfulness, connectivity and barriers;
* hidden-unit, head and residual symmetries and the orders of the groups;
* fixed-point rescaling rigidity, dyadic rescaling of floating point;
* softmax: positivity, shift invariance, masking identity, saturation;
* zero weights versus pruned weights;
* a finite Chernoff–Hoeffding-type bound (constant `1` instead of `2`),
  the union bound, and the finite-class (Occam) bound;
* transformer parameter counts (GPT-2 small, LLaMA-7B);
* single-bit faults in two's complement.
-/

namespace QE.Learn

open Finset

/-! ## Parameter boxes -/

/-- The index box `{-M,…,M}^N` of a fixed-point parameter lattice. -/
def box (N : ℕ) (M : ℤ) : Finset (Fin N → ℤ) :=
  Fintype.piFinset fun _ => Icc (-M) M

theorem card_box (N : ℕ) (M : ℕ) : (box N M).card = (2 * M + 1) ^ N := by
  simp only [box, Fintype.card_piFinset, Int.card_Icc, prod_const, card_univ,
    Fintype.card_fin]
  congr 1
  omega

theorem mem_box {N : ℕ} {M : ℤ} {k : Fin N → ℤ} :
    k ∈ box N M ↔ ∀ i, -M ≤ k i ∧ k i ≤ M := by
  simp [box, Fintype.mem_piFinset]

/-- Granular content of the full parameter box. -/
theorem muN_box {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    (N M : ℕ) (ε : K) :
    QE.muN N ε (box N M) = (2 * ε) ^ N * ((2 * M + 1 : ℕ) : K) ^ N := by
  simp [QE.muN, card_box]

/-- Faithfulness on parameter space: a set of parameters has zero content iff
it is empty. -/
theorem muN_pos_iff {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    (N : ℕ) (ε : K) (hε : 0 < ε) (A : Finset (Fin N → ℤ)) :
    0 < QE.muN N ε A ↔ A.Nonempty := by
  unfold QE.muN
  constructor
  · intro h
    by_contra hA
    rw [not_nonempty_iff_eq_empty] at hA
    simp [hA] at h
  · intro h
    have : (0 : K) < A.card := by exact_mod_cast h.card_pos
    positivity

/-! ## The snap and the quantisation algebra -/

section Snap

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K] [FloorRing K]

/-- Cell index of `x` for the granule `e` (round half up). -/
noncomputable def idx (e x : K) : ℤ := ⌊x / (2 * e) + 1 / 2⌋

/-- The snap `⌊x⌉_e = 2e ⌊x/(2e) + 1/2⌋`. -/
noncomputable def snap (e x : K) : K := 2 * e * idx e x

theorem idx_lattice (e : K) (he : 0 < e) (n : ℤ) : idx e (2 * e * n) = n := by
  unfold idx
  rw [Int.floor_eq_iff]
  have : 2 * e * (n : K) / (2 * e) = n := by field_simp
  rw [this]; constructor <;> linarith

/-- Snapping a lattice point does nothing. -/
theorem snap_lattice (e : K) (he : 0 < e) (n : ℤ) : snap e (2 * e * n) = 2 * e * n := by
  rw [snap, idx_lattice e he]

/-- **Idempotence**: `snap ∘ snap = snap`. -/
theorem snap_snap (e : K) (he : 0 < e) (x : K) : snap e (snap e x) = snap e x :=
  snap_lattice e he _

/-- The cell of a centre: `snap e (c + u) = c` iff `-e ≤ u < e`. -/
theorem snap_add_iff (e : K) (he : 0 < e) (n : ℤ) (u : K) :
    snap e (2 * e * n + u) = 2 * e * n ↔ -e ≤ u ∧ u < e := by
  have h2 : (0 : K) < 2 * e := by linarith
  unfold snap idx
  constructor
  · intro h
    have h' : (⌊(2 * e * n + u) / (2 * e) + 1 / 2⌋ : K) = n := by
      have := mul_left_cancel₀ (ne_of_gt h2) h
      exact this
    have hfl : ⌊(2 * e * n + u) / (2 * e) + 1 / 2⌋ = n := by exact_mod_cast h'
    rw [Int.floor_eq_iff] at hfl
    have hx : (2 * e * n + u) / (2 * e) = n + u / (2 * e) := by field_simp
    rw [hx] at hfl
    obtain ⟨h1, h3⟩ := hfl
    have a1 : -(1 / 2 : K) ≤ u / (2 * e) := by linarith
    have a2 : u / (2 * e) < 1 / 2 := by linarith
    rw [le_div_iff₀ h2] at a1
    rw [div_lt_iff₀ h2] at a2
    constructor <;> linarith
  · rintro ⟨h1, h3⟩
    congr 1
    have hfl : ⌊(2 * e * n + u) / (2 * e) + 1 / 2⌋ = n := by
      rw [Int.floor_eq_iff]
      have hx : (2 * e * n + u) / (2 * e) = n + u / (2 * e) := by field_simp
      rw [hx]
      have a1 : -(1 / 2 : K) ≤ u / (2 * e) := by rw [le_div_iff₀ h2]; linarith
      have a2 : u / (2 * e) < 1 / 2 := by rw [div_lt_iff₀ h2]; linarith
      constructor <;> linarith
    rw [hfl]

/-- Snapping error: `-e ≤ x - snap e x < e`. -/
theorem snap_err (e : K) (he : 0 < e) (x : K) : -e ≤ x - snap e x ∧ x - snap e x < e := by
  have h2 : (0 : K) < 2 * e := by linarith
  have h := Int.floor_le (x / (2 * e) + 1 / 2)
  have h' := Int.lt_floor_add_one (x / (2 * e) + 1 / 2)
  unfold snap idx
  set m := ⌊x / (2 * e) + 1 / 2⌋
  have hx : x = 2 * e * (x / (2 * e)) := by field_simp
  constructor <;> nlinarith

/-- Snap commutes with translation by lattice vectors. -/
theorem snap_add_lattice (e : K) (he : 0 < e) (n : ℤ) (x : K) :
    snap e (2 * e * n + x) = 2 * e * n + snap e x := by
  unfold snap idx
  have h2 : (2 * e) ≠ 0 := by positivity
  have hx : (2 * e * n + x) / (2 * e) + 1 / 2 = (x / (2 * e) + 1 / 2) + n := by
    field_simp; ring
  rw [hx, Int.floor_add_intCast]; push_cast; ring

/-- **Carry of a sum**: `snap (a+b) - snap a - snap b ∈ {-2e, 0, 2e}`. -/
theorem snap_add_carry (e : K) (he : 0 < e) (a b : K) :
    ∃ c : ℤ, (c = -1 ∨ c = 0 ∨ c = 1) ∧ snap e (a + b) = snap e a + snap e b + 2 * e * c := by
  obtain ⟨ha1, ha2⟩ := snap_err e he a
  obtain ⟨hb1, hb2⟩ := snap_err e he b
  obtain ⟨hs1, hs2⟩ := snap_err e he (a + b)
  have h2 : (0 : K) < 2 * e := by linarith
  refine ⟨idx e (a + b) - idx e a - idx e b, ?_, ?_⟩
  · have key : (2 * e) * ((idx e (a + b) - idx e a - idx e b : ℤ) : K)
        = snap e (a + b) - snap e a - snap e b := by
      unfold snap; push_cast; ring
    have up : (2 * e) * ((idx e (a + b) - idx e a - idx e b : ℤ) : K) < 2 * e * 2 := by
      rw [key]; linarith
    have lo : 2 * e * (-2) < (2 * e) * ((idx e (a + b) - idx e a - idx e b : ℤ) : K) := by
      rw [key]; linarith
    have u : ((idx e (a + b) - idx e a - idx e b : ℤ) : K) < 2 := by
      by_contra hc; rw [not_lt] at hc; nlinarith
    have l : (-2 : K) < ((idx e (a + b) - idx e a - idx e b : ℤ) : K) := by
      by_contra hc; rw [not_lt] at hc; nlinarith
    have u' : idx e (a + b) - idx e a - idx e b < 2 := by exact_mod_cast u
    have l' : -2 < idx e (a + b) - idx e a - idx e b := by exact_mod_cast l
    omega
  · unfold snap; push_cast; ring

/-- Rescaling: `snap e (c x) = c · snap (e/c) x` for `c > 0`.  Multiplying by
`c` commutes with quantisation exactly when the granule is rescaled with it. -/
theorem snap_smul (e c x : K) (hc : 0 < c) : snap e (c * x) = c * snap (e / c) x := by
  unfold snap idx
  have hc' : c ≠ 0 := ne_of_gt hc
  by_cases he : e = 0
  · subst he; simp
  have h1 : c * x / (2 * e) = x / (2 * (e / c)) := by field_simp
  rw [h1]; field_simp

/-- Snapping a fine lattice point `2e·n` to the granule `s·e` (ratio `s`). -/
theorem idx_ratio (e : K) (he : 0 < e) (s : ℕ) (hs : 0 < s) (n : ℤ) :
    idx ((s : K) * e) (2 * e * n) = ⌊(n : K) / s + 1 / 2⌋ := by
  unfold idx
  have hs' : (0 : K) < s := by exact_mod_cast hs
  congr 2
  field_simp

/-- **Odd ratios nest**: if the coarse granule is an odd multiple `s e` of the
fine granule `e`, rounding first to `e` and then to `s e` is the same as
rounding directly to `s e` (round half up). -/
theorem double_round_odd (e : K) (he : 0 < e) (j : ℕ) (x : K) :
    idx (((2 * j + 1 : ℕ) : K) * e) (snap e x) = idx (((2 * j + 1 : ℕ) : K) * e) x := by
  set s : ℕ := 2 * j + 1 with hsdef
  have hs : 0 < s := by omega
  have hsK : (0 : K) < s := by exact_mod_cast hs
  have h2e : (0 : K) < 2 * e := by linarith
  unfold snap
  rw [idx_ratio e he s hs]
  set n := idx e x with hn
  set m := idx ((s : K) * e) x with hm
  -- floor facts
  have hn1 : (n : K) ≤ x / (2 * e) + 1 / 2 := Int.floor_le _
  have hn2 : x / (2 * e) + 1 / 2 < n + 1 := Int.lt_floor_add_one _
  have hm1 : (m : K) ≤ x / (2 * (s * e)) + 1 / 2 := Int.floor_le _
  have hm2 : x / (2 * (s * e)) + 1 / 2 < m + 1 := Int.lt_floor_add_one _
  have hy : x / (2 * e) = s * (x / (2 * (s * e))) := by field_simp
  set y := x / (2 * (s * e))
  have hsj : (s : K) = 2 * j + 1 := by rw [hsdef]; push_cast; ring
  -- integer bounds on n
  rw [hy] at hn1 hn2
  rw [hsj] at hn1 hn2 hsK ⊢
  have lo : 2 * (j : ℤ) * m + m - j ≤ n := by
    rw [hn]; unfold idx; apply Int.le_floor.mpr; push_cast
    rw [hy, hsj]; nlinarith
  have hi : n ≤ 2 * (j : ℤ) * m + m + j := by
    have : (n : K) < 2 * j * m + m + j + 1 := by nlinarith
    have : n < 2 * (j : ℤ) * m + m + j + 1 := by exact_mod_cast this
    omega
  have loK : 2 * (j : K) * m + m - j ≤ n := by exact_mod_cast lo
  have hiK : (n : K) ≤ 2 * j * m + m + j := by exact_mod_cast hi
  rw [Int.floor_eq_iff]
  constructor
  · rw [div_add' _ _ _ (ne_of_gt hsK), le_div_iff₀ hsK]; nlinarith
  · rw [div_add' _ _ _ (ne_of_gt hsK), div_lt_iff₀ hsK]; nlinarith

/-- **Even ratios: the double-rounding defect.**  If the coarse granule is
`2j·e` (`j ≥ 1`), rounding through the fine granule `e` gives the direct
result or one coarse step more, and it gives one step more exactly when the
fine snapped index lands on a coarse tie, `n = s m + j`. -/
theorem double_round_even (e : K) (he : 0 < e) (j : ℕ) (hj : 0 < j) (x : K) :
    let s : ℕ := 2 * j
    let n := idx e x
    let m := idx ((s : K) * e) x
    (idx ((s : K) * e) (snap e x) = m ∧ n ≠ s * m + j) ∨
    (idx ((s : K) * e) (snap e x) = m + 1 ∧ n = s * m + j) := by
  intro s n m
  have hs : 0 < s := by omega
  have hsK : (0 : K) < s := by exact_mod_cast hs
  have h2e : (0 : K) < 2 * e := by linarith
  unfold snap
  rw [idx_ratio e he s hs]
  have hn1 : (n : K) ≤ x / (2 * e) + 1 / 2 := Int.floor_le _
  have hn2 : x / (2 * e) + 1 / 2 < n + 1 := Int.lt_floor_add_one _
  have hm1 : (m : K) ≤ x / (2 * (s * e)) + 1 / 2 := Int.floor_le _
  have hm2 : x / (2 * (s * e)) + 1 / 2 < m + 1 := Int.lt_floor_add_one _
  have hy : x / (2 * e) = s * (x / (2 * (s * e))) := by field_simp
  have hsj : (s : K) = 2 * j := by push_cast [s]; ring
  have hjK : (0 : K) < j := by exact_mod_cast hj
  rw [hy] at hn1 hn2
  set y := x / (2 * (s * e))
  rw [hsj] at hn1 hn2 hsK ⊢
  have lo : 2 * (j : ℤ) * m - j ≤ n := by
    show 2 * (j : ℤ) * m - j ≤ idx e x
    unfold idx; apply Int.le_floor.mpr; push_cast
    rw [hy, hsj]; nlinarith
  have hi : n ≤ 2 * (j : ℤ) * m + j := by
    have : (n : K) < 2 * j * m + j + 1 := by nlinarith
    have : n < 2 * (j : ℤ) * m + j + 1 := by exact_mod_cast this
    omega
  have hsZ : ((s : ℕ) : ℤ) = 2 * j := by push_cast [s]; ring
  by_cases hc : n = 2 * j * m + j
  · right
    refine ⟨?_, by rw [hsZ]; exact hc⟩
    rw [Int.floor_eq_iff, show idx e x = n from rfl, hc]; push_cast
    constructor
    · rw [div_add' _ _ _ (by positivity), le_div_iff₀ (by positivity)]; nlinarith
    · rw [div_add' _ _ _ (by positivity), div_lt_iff₀ (by positivity)]; nlinarith
  · left
    refine ⟨?_, by rw [hsZ]; exact hc⟩
    have hi' : n ≤ 2 * (j : ℤ) * m + j - 1 := by omega
    have loK : 2 * (j : K) * m - j ≤ n := by exact_mod_cast lo
    have hiK : (n : K) ≤ 2 * j * m + j - 1 := by exact_mod_cast hi'
    rw [Int.floor_eq_iff]
    constructor
    · rw [div_add' _ _ _ (ne_of_gt hsK), le_div_iff₀ hsK]; nlinarith
    · rw [div_add' _ _ _ (ne_of_gt hsK), div_lt_iff₀ hsK]; nlinarith

end Snap

/-! ## Quantisation on the lattice: integer form, error cosets, cells -/

/-- Integer quantiser of ratio `r`: the coarse index of the fine index `k`
(fine granule `ε`, coarse granule `r ε`, round half up). -/
def qz (r : ℕ) (k : ℤ) : ℤ := (2 * k + r) / (2 * r)

/-- The quantisation residual (error, in fine units). -/
def res (r : ℕ) (k : ℤ) : ℤ := k - r * qz r k

theorem qz_eq_idx {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K] [FloorRing K]
    (e : K) (he : 0 < e) (r : ℕ) (hr : 0 < r) (k : ℤ) :
    idx ((r : K) * e) (2 * e * k) = qz r k := by
  rw [idx_ratio e he r hr]
  have hrK : (0 : K) < r := by exact_mod_cast hr
  have : (k : K) / r + 1 / 2 = ((2 * k + r : ℤ) : K) / ((2 * r : ℕ) : K) := by
    push_cast; field_simp
  rw [this, Int.floor_div_natCast, Int.floor_intCast]
  simp [qz]

/-- The residual is a centred representative: `-r ≤ 2·res < r`, and
`k = r·qz + res`. -/
theorem res_bounds (r : ℕ) (hr : 0 < r) (k : ℤ) :
    k = r * qz r k + res r k ∧ -(r : ℤ) ≤ 2 * res r k ∧ 2 * res r k < r := by
  have h2r : (0 : ℤ) < 2 * r := by omega
  have hd := Int.mul_ediv_add_emod (2 * k + r) (2 * r)
  have h0 := Int.emod_nonneg (2 * k + r) (ne_of_gt h2r)
  have h1 := Int.emod_lt_of_pos (2 * k + r) h2r
  unfold res qz
  refine ⟨by ring, ?_, ?_⟩ <;> nlinarith

/-- Uniqueness: a decomposition `k = r q + e` with `-r ≤ 2e < r` is the
quantisation. -/
theorem qz_unique (r : ℕ) (hr : 0 < r) (k q e : ℤ) (hk : k = r * q + e)
    (h1 : -(r : ℤ) ≤ 2 * e) (h2 : 2 * e < r) : qz r k = q := by
  unfold qz
  have h2r : (0 : ℤ) < 2 * r := by omega
  have := (Int.ediv_emod_unique h2r (a := 2 * k + r) (r := 2 * e + r) (q := q)).mpr
    ⟨by subst hk; ring, by omega, by omega⟩
  exact this.1

/-- **Sign symmetry and ties.**  For an odd ratio the half-up quantiser is odd,
`q_r(-k) = -q_r(k)`; for an even ratio it is not (ties are broken upward):
`q_2(1) = 1` but `q_2(-1) = 0`. -/
theorem qz_neg_odd (j : ℕ) (k : ℤ) : qz (2 * j + 1) (-k) = -qz (2 * j + 1) k := by
  have hr : 0 < 2 * j + 1 := by omega
  obtain ⟨hk, h1, h2⟩ := res_bounds (2 * j + 1) hr k
  apply qz_unique (2 * j + 1) hr (-k) (-qz (2 * j + 1) k) (-res (2 * j + 1) k)
  · linarith
  · push_cast at h1 h2 ⊢; omega
  · push_cast at h1 h2 ⊢; omega

theorem qz_tie_even : qz 2 1 = 1 ∧ qz 2 (-1) = 0 := by decide

/-- **Invariance of a profile count.**  A bijection `g` that maps the cell
`C` onto the cell `C'` and preserves the solution predicate preserves the
number of solutions in the cell. -/
theorem profile_invariant {α : Type*} [DecidableEq α] (g : α ≃ α) (C C' : Finset α)
    (hC : C.map g.toEmbedding = C') (S : α → Prop) [DecidablePred S] (hS : ∀ x, S (g x) ↔ S x) :
    (C'.filter S).card = (C.filter S).card ∧ C'.card = C.card := by
  subst hC
  refine ⟨?_, card_map _⟩
  rw [filter_map, card_map]
  congr 1
  ext x; simp [hS]

/-- Coarse cell in index form: the `r` fine indices with coarse index `q`. -/
def cellZ (r : ℕ) (q : ℤ) : Finset ℤ :=
  (Ico (-((r : ℤ) / 2)) ((r : ℤ) - (r : ℤ) / 2)).image fun e => (r : ℤ) * q + e

theorem mem_cellZ (r : ℕ) (hr : 0 < r) (q k : ℤ) : k ∈ cellZ r q ↔ qz r k = q := by
  unfold cellZ
  simp only [mem_image, mem_Ico]
  constructor
  · rintro ⟨e, ⟨h1, h2⟩, rfl⟩
    exact qz_unique r hr _ q e rfl (by omega) (by omega)
  · intro h
    obtain ⟨hk, h1, h2⟩ := res_bounds r hr k
    refine ⟨res r k, ⟨by omega, by omega⟩, ?_⟩
    rw [h] at hk; omega

theorem card_cellZ (r : ℕ) (q : ℤ) : (cellZ r q).card = r := by
  unfold cellZ
  rw [card_image_of_injective _ (fun a b h => by simpa using h), Int.card_Ico]
  omega

/-- The `N`-dimensional coarse cell: fine lattice points quantising to `q`. -/
def cellN {N : ℕ} (r : ℕ) (q : Fin N → ℤ) : Finset (Fin N → ℤ) :=
  Fintype.piFinset fun i => cellZ r (q i)

theorem mem_cellN {N : ℕ} (r : ℕ) (hr : 0 < r) (q k : Fin N → ℤ) :
    k ∈ cellN r q ↔ ∀ i, qz r (k i) = q i := by
  simp [cellN, Fintype.mem_piFinset, mem_cellZ r hr]

/-- **Cell count**: a coarse cell contains exactly `r^N` fine lattice points. -/
theorem card_cellN {N : ℕ} (r : ℕ) (q : Fin N → ℤ) : (cellN r q).card = r ^ N := by
  simp [cellN, Fintype.card_piFinset, card_cellZ]

/-- Bits saved by quantising `N` parameters with ratio `r`: `N log₂ r`. -/
theorem bits_saved (N r : ℕ) (hr : 0 < r) :
    Real.logb 2 ((r : ℝ) ^ N) = N * Real.logb 2 r := by
  rw [Real.logb_pow]

/-! ## Accumulation and dot products -/

section Accum

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K] [FloorRing K]

/-- Granular accumulator: `s₀ = 0`, `s_{t+1} = snap (s_t + p_t)`. -/
noncomputable def accum (e : K) (p : ℕ → K) : ℕ → K
  | 0 => 0
  | t + 1 => snap e (accum e p t + p t)

/-- Exact error bound for an accumulator of granule `e`: after `n` additions
the accumulated value differs from the exact sum by at most `n e`. -/
theorem accum_err (e : K) (he : 0 < e) (p : ℕ → K) (n : ℕ) :
    |accum e p n - ∑ t ∈ range n, p t| ≤ n * e := by
  induction n with
  | zero => simp [accum]
  | succ n ih =>
    rw [sum_range_succ]
    simp only [accum]
    obtain ⟨h1, h2⟩ := snap_err e he (accum e p n + p n)
    have : |snap e (accum e p n + p n) - (accum e p n + p n)| ≤ e := by
      rw [abs_le]; constructor <;> linarith
    calc |snap e (accum e p n + p n) - (∑ t ∈ range n, p t + p n)|
        = |(snap e (accum e p n + p n) - (accum e p n + p n)) +
            (accum e p n - ∑ t ∈ range n, p t)| := by ring_nf
      _ ≤ e + n * e := (abs_add_le _ _).trans (add_le_add this ih)
      _ = ((n + 1 : ℕ) : K) * e := by push_cast; ring

/-- An accumulator whose summands are lattice points is exact. -/
theorem accum_exact (e : K) (he : 0 < e) (p : ℕ → ℤ) (n : ℕ) :
    accum e (fun t => 2 * e * p t) n = 2 * e * ((∑ t ∈ range n, p t : ℤ) : K) := by
  induction n with
  | zero => simp [accum]
  | succ n ih =>
    simp only [accum, ih, sum_range_succ]
    rw [show 2 * e * ((∑ t ∈ range n, p t : ℤ) : K) + 2 * e * p n
        = 2 * e * ((∑ t ∈ range n, p t + p n : ℤ) : K) by push_cast; ring]
    exact snap_lattice e he _

/-- **Dot-product error decomposition**: quantising the weights changes a dot
product by exactly `∑ (w - snap w) x`, of size at most `e ∑ |x|`. -/
theorem dot_quant_err {n : ℕ} (e : K) (he : 0 < e) (w x : Fin n → K) :
    ∑ i, w i * x i - ∑ i, snap e (w i) * x i = ∑ i, (w i - snap e (w i)) * x i ∧
    |∑ i, w i * x i - ∑ i, snap e (w i) * x i| ≤ e * ∑ i, |x i| := by
  have hdec : ∑ i, w i * x i - ∑ i, snap e (w i) * x i = ∑ i, (w i - snap e (w i)) * x i := by
    rw [← sum_sub_distrib]; congr 1; ext i; ring
  refine ⟨hdec, ?_⟩
  rw [hdec, mul_sum]
  refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun i _ => ?_)
  rw [abs_mul]
  obtain ⟨h1, h2⟩ := snap_err e he (w i)
  have : |w i - snap e (w i)| ≤ e := by rw [abs_le]; constructor <;> linarith
  exact mul_le_mul_of_nonneg_right this (abs_nonneg _)

end Accum

/-! ## Training on the lattice -/

section Training

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K] [FloorRing K]

/-- One step of rounded gradient descent, coordinatewise. -/
noncomputable def gdStep {N : ℕ} (e η : K) (g : (Fin N → K) → Fin N → K)
    (θ : Fin N → K) : Fin N → K :=
  fun i => snap e (θ i - η * g θ i)

/-- **Stagnation, exact form.**  At a lattice coordinate `θᵢ = 2e n`, the
rounded update leaves `θᵢ` unchanged iff `-e < η gᵢ ≤ e`. -/
theorem stagnation_iff (e : K) (he : 0 < e) (n : ℤ) (η g : K) :
    snap e (2 * e * n - η * g) = 2 * e * n ↔ -e < η * g ∧ η * g ≤ e := by
  rw [sub_eq_add_neg, snap_add_iff e he]
  constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith

/-- **Stagnation.**  If `|η gᵢ| < e` for every coordinate at a lattice point,
rounded gradient descent does not move: the point is a fixed point. -/
theorem stagnation {N : ℕ} (e η : K) (he : 0 < e) (g : (Fin N → K) → Fin N → K)
    (n : Fin N → ℤ) (h : ∀ i, |η * g (fun j => 2 * e * n j) i| < e) :
    gdStep e η g (fun j => 2 * e * n j) = fun j => 2 * e * n j := by
  funext i
  unfold gdStep
  have := h i
  rw [abs_lt] at this
  exact (stagnation_iff e he (n i) η _).mpr ⟨this.1, this.2.le⟩

/-- **Stochastic rounding is unbiased**: rounding `x = 2e(k + p)` up with
probability `p` and down with probability `1-p` has mean `x`. -/
theorem sr_unbiased (e : K) (k : ℤ) (p : K) :
    (1 - p) * (2 * e * k) + p * (2 * e * (k + 1)) = 2 * e * (k + p) := by ring

/-- Variance of stochastic rounding: `(2e)² p (1-p) ≤ e²`. -/
theorem sr_variance (e : K) (k : ℤ) (p : K) :
    (1 - p) * (2 * e * k - 2 * e * (k + p)) ^ 2 + p * (2 * e * (k + 1) - 2 * e * (k + p)) ^ 2
      = (2 * e) ^ 2 * (p * (1 - p)) ∧ (2 * e) ^ 2 * (p * (1 - p)) ≤ e ^ 2 := by
  constructor
  · ring
  · nlinarith [sq_nonneg (2 * e * p - e), sq_nonneg e]

/-- **Stochastic rounding with `b` random bits** is exactly unbiased when the
fractional part is a multiple of `2^{-b}`: averaging over the `2^b` equally
likely bit strings `u`, rounding up iff `u < j`. -/
theorem sr_bits (e : K) (k : ℤ) (b j : ℕ) (hj : j ≤ 2 ^ b) :
    (∑ u ∈ range (2 ^ b), (if u < j then 2 * e * (k + 1) else 2 * e * k)) / (2 ^ b : ℕ)
      = 2 * e * (k + (j : K) / (2 ^ b : ℕ)) := by
  have hcard : ((range (2 ^ b)).filter (fun u => u < j)).card = j := by
    have : (range (2 ^ b)).filter (fun u => u < j) = range j := by
      ext u; simp only [mem_filter, mem_range]; omega
    rw [this, card_range]
  have hcard' : ((range (2 ^ b)).filter (fun u => ¬ u < j)).card = 2 ^ b - j := by
    rw [filter_not, card_sdiff_of_subset (filter_subset _ _), hcard, card_range]
  rw [sum_ite, sum_const, sum_const, hcard, hcard', nsmul_eq_mul, nsmul_eq_mul]
  have hpos : (0 : K) < (2 ^ b : ℕ) := by positivity
  rw [Nat.cast_sub hj]
  field_simp
  ring

/-- **Eventual periodicity** of any deterministic training map on a finite
set of states (pigeonhole). -/
theorem eventually_periodic {X : Type*} [Fintype X] (f : X → X) (x : X) :
    ∃ m n : ℕ, 0 < n ∧ m + n ≤ Fintype.card X ∧ f^[m + n] x = f^[m] x := by
  have hc : Fintype.card X < Fintype.card (Fin (Fintype.card X + 1)) := by simp
  obtain ⟨i, j, hij, h⟩ :=
    Fintype.exists_ne_map_eq_of_card_lt (fun i : Fin (Fintype.card X + 1) => f^[i] x) hc
  rcases lt_or_gt_of_ne (Fin.val_injective.ne hij) with hlt | hlt
  · refine ⟨i, j - i, by omega, by have := j.isLt; omega, ?_⟩
    rw [Nat.add_sub_cancel' hlt.le]; exact h.symm
  · refine ⟨j, i - j, by omega, by have := i.isLt; omega, ?_⟩
    rw [Nat.add_sub_cancel' hlt.le]; exact h

/-- Once periodic, always periodic. -/
theorem periodic_forever {X : Type*} (f : X → X) {x : X} {m n : ℕ}
    (h : f^[m + n] x = f^[m] x) (t : ℕ) : f^[m + t + n] x = f^[m + t] x := by
  have e1 : m + t + n = t + (m + n) := by omega
  have e2 : m + t = t + m := by omega
  rw [e1, e2, Function.iterate_add_apply, h, ← Function.iterate_add_apply]

/-- **Training with a cyclic data schedule** (`B` mini-batches visited in a
fixed order, step maps `T b`) is eventually periodic: the state
`(parameters, batch index)` lives in a finite set. -/
theorem schedule_eventually_periodic {X : Type*} [Fintype X] (B : ℕ) [NeZero B]
    (T : Fin B → X → X) (x : X) (b : Fin B) :
    let F : X × Fin B → X × Fin B := fun s => (T s.2 s.1, s.2 + 1)
    ∃ m n : ℕ, 0 < n ∧ m + n ≤ Fintype.card X * B ∧ F^[m + n] (x, b) = F^[m] (x, b) := by
  intro F
  obtain ⟨m, n, hn, hle, h⟩ := eventually_periodic F (x, b)
  refine ⟨m, n, hn, ?_, h⟩
  simpa [Fintype.card_prod, Fintype.card_fin] using hle

/-- The granular gradient of a quadratic is biased by exactly `a ε`
(forward difference) and exact for the central difference. -/
theorem Dp_quadratic (ε a x : K) (hε : ε ≠ 0) :
    QE.Dp ε (fun y => a / 2 * y ^ 2) x = a * x + a * ε ∧
    QE.Dc ε (fun y => a / 2 * y ^ 2) x = a * x := by
  unfold QE.Dp QE.Dc
  constructor <;> field_simp <;> ring

end Training

/-! ## Solution sets, charts, dimension, connectivity -/

/-- A granular chart: the graph of a map `φ` over a window `W` has exactly as
many lattice points as the window. -/
theorem graph_card {α β : Type*} [DecidableEq α] [DecidableEq β] (W : Finset α) (φ : α → β) :
    (W.image fun u => (u, φ u)).card = W.card :=
  card_image_of_injective _ (fun a b h => by simpa using congrArg Prod.fst h)

/-- Local content of a granular `k`-manifold at window radius `r`. -/
theorem chart_card {k : ℕ} {β : Type*} [DecidableEq β] (r : ℕ) (φ : (Fin k → ℤ) → β) :
    ((box k r).image fun u => (u, φ u)).card = (2 * r + 1) ^ k := by
  rw [graph_card, card_box]

/-- Dimension read off a count: `log_{2r+1} #(chart) = k`. -/
theorem chart_dim (k r : ℕ) (hr : 0 < r) :
    Real.logb (2 * r + 1) (((2 * r + 1 : ℕ) : ℝ) ^ k) = k := by
  have hb : (1 : ℝ) < 2 * r + 1 := by
    have : (1 : ℝ) ≤ r := by exact_mod_cast hr
    linarith
  rw [Real.logb_pow]; push_cast
  rw [Real.logb_self_eq_one hb, mul_one]

/-- Exact-constraint solution set `{c} × box`: `m` coordinates pinned, `n`
free.  It has `(2M+1)^n` lattice points. -/
theorem pinned_card (m n M : ℕ) (c : Fin m → ℤ) :
    (({c} : Finset (Fin m → ℤ)) ×ˢ box n M).card = (2 * M + 1) ^ n := by
  rw [card_product, card_singleton, one_mul, card_box]

/-- Probability that a uniformly random lattice initialisation satisfies the
`m` pinned constraints: exactly `(2M+1)^{-m}`, positive. -/
theorem pinned_prob (m n M : ℕ) (c : Fin m → ℤ) :
    ((({c} : Finset (Fin m → ℤ)) ×ˢ box n M).card : ℝ) / ((box m M ×ˢ box n M).card : ℝ)
      = 1 / ((2 * M + 1 : ℕ) : ℝ) ^ m ∧
    0 < 1 / ((2 * M + 1 : ℕ) : ℝ) ^ m := by
  rw [pinned_card, card_product, card_box, card_box]
  constructor
  · push_cast
    have : ((2 * M + 1 : ℝ)) ^ n ≠ 0 := by positivity
    field_simp
  · positivity

/-- Description length of a solution set `S ⊆ Λ` (bits needed to locate it by
uniform guessing): `log₂(#Λ/#S) = log₂ #Λ - log₂ #S`. -/
theorem desc_length (Λ S : ℕ) (hΛ : 0 < Λ) (hS : 0 < S) :
    Real.logb 2 ((Λ : ℝ) / S) = Real.logb 2 Λ - Real.logb 2 S :=
  Real.logb_div (by positivity) (by positivity)

/-- Flatter (larger) solution sets cost fewer bits. -/
theorem desc_length_anti (Λ S S' : ℕ) (hS : 0 < S) (h : S ≤ S') (hΛ : 0 < Λ) :
    Real.logb 2 ((Λ : ℝ) / S') ≤ Real.logb 2 ((Λ : ℝ) / S) := by
  apply Real.logb_le_logb_of_le (by norm_num)
  · have : (0 : ℝ) < S' := by exact_mod_cast lt_of_lt_of_le hS h
    positivity
  · apply div_le_div_of_nonneg_left (by positivity) (by exact_mod_cast hS) (by exact_mod_cast h)

/-- Lattice bijections preserve the count of a basin exactly. -/
theorem count_invariant {α β : Type*} [DecidableEq β] (f : α → β) (hf : Function.Injective f)
    (B : Finset α) : (B.image f).card = B.card :=
  card_image_of_injective _ hf

/-- `2N`-adjacency on `ℤ^N`: one coordinate changes by `±1`. -/
def adj {N : ℕ} (a b : Fin N → ℤ) : Prop :=
  ∃ i, |a i - b i| = 1 ∧ ∀ j, j ≠ i → a j = b j

/-- Paths inside a set `S`. -/
def pathIn {N : ℕ} (S : Set (Fin N → ℤ)) : (Fin N → ℤ) → (Fin N → ℤ) → Prop :=
  Relation.ReflTransGen fun a b => a ∈ S ∧ b ∈ S ∧ adj a b

/-- **Boxes are connected**: any two points of a lattice box are joined by a
path of unit steps inside the box. -/
theorem box_connected {N : ℕ} (lo hi : Fin N → ℤ) (a b : Fin N → ℤ)
    (ha : ∀ i, lo i ≤ a i ∧ a i ≤ hi i) (hb : ∀ i, lo i ≤ b i ∧ b i ≤ hi i) :
    pathIn {x | ∀ i, lo i ≤ x i ∧ x i ≤ hi i} a b := by
  classical
  suffices H : ∀ n : ℕ, ∀ a : Fin N → ℤ, (∀ i, lo i ≤ a i ∧ a i ≤ hi i) →
      (∑ i, |a i - b i|).toNat = n → pathIn {x | ∀ i, lo i ≤ x i ∧ x i ≤ hi i} a b from
    H _ a ha rfl
  intro n
  induction n with
  | zero =>
    intro a ha hn
    have h0 : ∑ i, |a i - b i| = 0 := by
      have := Finset.sum_nonneg (s := univ) fun i _ => abs_nonneg (a i - b i)
      omega
    have : a = b := by
      funext i
      have := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => abs_nonneg (a i - b i))).mp h0 i
        (mem_univ _)
      rw [abs_eq_zero] at this; omega
    rw [this]; exact Relation.ReflTransGen.refl
  | succ n ih =>
    intro a ha hn
    have hne : ∃ i, a i ≠ b i := by
      by_contra hc
      push Not at hc
      have : ∑ i, |a i - b i| = 0 := by simp [hc]
      omega
    obtain ⟨i, hi'⟩ := hne
    let v : ℤ := if a i < b i then a i + 1 else a i - 1
    let a' := Function.update a i v
    have hv : |v - b i| = |a i - b i| - 1 := by
      simp only [v]; split_ifs with h
      · rw [abs_of_nonpos (by omega), abs_of_neg (by omega)]; ring
      · rw [abs_of_nonneg (by omega), abs_of_pos (by omega)]; ring
    have hsum : ∑ j, |a' j - b j| = ∑ j, |a j - b j| - 1 := by
      have hfun : (fun j => |a' j - b j|) =
          Function.update (fun j => |a j - b j|) i (|v - b i|) := by
        funext j; by_cases hj : j = i
        · subst hj; simp [a']
        · simp [a', hj]
      rw [hfun, Finset.sum_update_of_mem (mem_univ i), hv]
      rw [← Finset.add_sum_erase _ _ (mem_univ i)]
      ring_nf
      simp [Finset.sdiff_singleton_eq_erase]
    have ha' : ∀ j, lo j ≤ a' j ∧ a' j ≤ hi j := by
      intro j; by_cases hj : j = i
      · subst hj; simp only [a', Function.update_self, v]
        have := ha j; have := hb j
        split_ifs <;> constructor <;> omega
      · simp only [a', Function.update_of_ne hj]; exact ha j
    have hstep : adj a a' := by
      refine ⟨i, ?_, fun j hj => by simp [a', hj]⟩
      simp only [a', Function.update_self, v]; split_ifs <;> simp
    apply Relation.ReflTransGen.head ⟨ha, ha', hstep⟩
    apply ih a' ha'
    rw [hsum]; omega

/-- **Barriers disconnect**: if no point of `S` has `i`-th coordinate `c`,
then a path in `S` starting below `c` stays below `c`. -/
theorem barrier {N : ℕ} (S : Set (Fin N → ℤ)) (i : Fin N) (c : ℤ)
    (hS : ∀ x ∈ S, x i ≠ c) {a b : Fin N → ℤ} (hab : pathIn S a b) (ha : a i < c) :
    b i < c := by
  induction hab with
  | refl => exact ha
  | tail _ hst ih =>
    obtain ⟨-, hc, j, h1, h2⟩ := hst
    by_cases hj : i = j
    · subst hj
      have := hS _ hc
      rw [abs_eq (by norm_num)] at h1
      omega
    · rw [← h2 i hj]; exact ih

/-- An isolated point of `S` is its own component. -/
theorem isolated {N : ℕ} (S : Set (Fin N → ℤ)) (a : Fin N → ℤ)
    (h : ∀ b ∈ S, ¬ adj a b) {b : Fin N → ℤ} (hab : pathIn S a b) : b = a := by
  induction hab with
  | refl => rfl
  | tail _ hst ih => subst ih; exact absurd hst.2.2 (h _ hst.2.1)

/-- Precision-dependent connectivity, worked case.  The fine staircase
`(0,0),(1,0),(1,1),(2,1),(2,2)` is a path; its coarse points (ratio `2`) are
`(0,0)` and `(1,1)` in coarse indices, which are not adjacent. -/
theorem staircase_fine :
    adj ![0, 0] ![1, 0] ∧ adj ![1, 0] ![1, 1] ∧ adj ![1, 1] ![2, 1] ∧ adj ![2, 1] ![2, 2] := by
  refine ⟨⟨0, by decide, ?_⟩, ⟨1, by decide, ?_⟩, ⟨0, by decide, ?_⟩, ⟨1, by decide, ?_⟩⟩ <;>
    intro j hj <;> fin_cases j <;> simp_all

theorem staircase_coarse : ¬ adj (![0, 0] : Fin 2 → ℤ) ![1, 1] := by
  rintro ⟨i, h1, h2⟩
  fin_cases i
  · have := h2 1 (by decide); simp at this
  · have := h2 0 (by decide); simp at this

/-! ## Symmetries -/

open scoped Matrix

/-- **Hidden-unit permutation symmetry** (any layer of the form
`∑_j a_j σ(⟨w_j, x⟩ + b_j)`, and any sum of heads): permuting units does not
change the function. -/
theorem units_perm {K : Type*} [AddCommMonoid K] {h : ℕ} (F : Fin h → K) (σ : Equiv.Perm (Fin h)) :
    ∑ j, F (σ j) = ∑ j, F j :=
  Equiv.sum_comp σ F

theorem mlp_perm {K : Type*} [CommRing K] {h d : ℕ} (act : K → K) (a : Fin h → K)
    (W : Fin h → Fin d → K) (b : Fin h → K) (x : Fin d → K) (σ : Equiv.Perm (Fin h)) :
    ∑ j, a (σ j) * act (∑ i, W (σ j) i * x i + b (σ j)) =
    ∑ j, a j * act (∑ i, W j i * x i + b j) :=
  Equiv.sum_comp σ (fun j => a j * act (∑ i, W j i * x i + b j))

/-- **Query–key gauge**: `(W_Q A)(W_K A^{-T})^T = W_Q W_Kᵀ` for invertible `A`. -/
theorem qk_gauge {K : Type*} [Field K] {n dh : ℕ} (WQ WK : Matrix (Fin n) (Fin dh) K)
    (A : Matrix (Fin dh) (Fin dh) K) (hA : IsUnit A.det) :
    (WQ * A) * (WK * (A⁻¹)ᵀ)ᵀ = WQ * WKᵀ := by
  rw [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc, ← Matrix.mul_assoc A,
    Matrix.mul_nonsing_inv A hA, Matrix.one_mul]

/-- **Value–output gauge**: `(W_V B)(B^{-1} W_O) = W_V W_O`. -/
theorem vo_gauge {K : Type*} [Field K] {n dh m : ℕ} (WV : Matrix (Fin n) (Fin dh) K)
    (WO : Matrix (Fin dh) (Fin m) K) (B : Matrix (Fin dh) (Fin dh) K) (hB : IsUnit B.det) :
    (WV * B) * (B⁻¹ * WO) = WV * WO := by
  rw [Matrix.mul_assoc, ← Matrix.mul_assoc B, Matrix.mul_nonsing_inv B hB, Matrix.one_mul]

/-- **Cube rigidity, column bound.**  If `x ↦ xA` maps the integer cube
`{-M,…,M}^k` (`M ≥ 1`) into itself, every column of `A` has `ℓ¹` norm `≤ 1`. -/
theorem cube_col_l1 {k : ℕ} (A : Fin k → Fin k → ℤ) (M : ℤ) (hM : 1 ≤ M)
    (h : ∀ x : Fin k → ℤ, (∀ i, |x i| ≤ M) → ∀ j, |∑ i, x i * A i j| ≤ M) (j : Fin k) :
    ∑ i, |A i j| ≤ 1 := by
  have hsgn : ∀ a : ℤ, |Int.sign a| ≤ 1 := by
    intro a; rcases Int.sign_trichotomy a with h | h | h <;> rw [h] <;> norm_num
  have hx := h (fun i => M * Int.sign (A i j)) (fun i => by
    rw [abs_mul, abs_of_pos (by omega : 0 < M)]
    have := hsgn (A i j); nlinarith) j
  have hs : ∑ i, M * Int.sign (A i j) * A i j = M * ∑ i, |A i j| := by
    rw [mul_sum]; congr 1; ext i
    rw [mul_assoc, Int.sign_mul_self, Int.natCast_natAbs]
  rw [hs, abs_of_nonneg (by positivity)] at hx
  by_contra hc; push Not at hc
  nlinarith

/-- **Cube rigidity, support.**  An integer column with `ℓ¹` norm `≤ 1` has at
most one nonzero entry, and that entry is `±1`. -/
theorem col_support {k : ℕ} (a : Fin k → ℤ) (h : ∑ i, |a i| ≤ 1) :
    (∀ i, |a i| ≤ 1) ∧ ∀ i i', a i ≠ 0 → a i' ≠ 0 → i = i' := by
  constructor
  · intro i
    exact (Finset.single_le_sum (fun j _ => abs_nonneg (a j)) (mem_univ i)).trans h
  · intro i i' hi hi'
    by_contra hne
    have h2 : |a i| + |a i'| ≤ ∑ j, |a j| := by
      calc |a i| + |a i'| = ∑ j ∈ {i, i'}, |a j| := (Finset.sum_pair (f := fun j => |a j|) hne).symm
        _ ≤ ∑ j, |a j| :=
          Finset.sum_le_sum_of_subset_of_nonneg (subset_univ _) (fun j _ _ => abs_nonneg _)
    have := abs_pos.mpr hi; have := abs_pos.mpr hi'
    omega

/-- Order of the hyperoctahedral group `B_k` (signed permutations). -/
theorem card_signed_perm (k : ℕ) :
    Fintype.card ((Fin k → Bool) × Equiv.Perm (Fin k)) = 2 ^ k * k.factorial := by
  simp [Fintype.card_prod, Fintype.card_perm]

/-- The discrete, lattice-preserving symmetry group of one transformer block
with `H` heads of width `dh` and MLP width `f`: head permutations, a signed
permutation in each head's query–key and value–output gauges, and MLP
hidden-unit permutations. -/
abbrev BlockSym (H dh f : ℕ) :=
  Equiv.Perm (Fin H) × (Fin H → ((Fin dh → Bool) × Equiv.Perm (Fin dh)) ×
    ((Fin dh → Bool) × Equiv.Perm (Fin dh))) × Equiv.Perm (Fin f)

instance (H dh f : ℕ) : Fintype (BlockSym H dh f) := by unfold BlockSym; infer_instance

theorem card_BlockSym (H dh f : ℕ) :
    Fintype.card (BlockSym H dh f) =
      H.factorial * (2 ^ dh * dh.factorial) ^ (2 * H) * f.factorial := by
  simp [BlockSym, Fintype.card_prod, Fintype.card_perm, Fintype.card_pi, pow_mul]
  ring

/-- The network symmetry group: a residual-stream permutation (LayerNorm
networks: `Perm (Fin d)`) and one block group per layer. -/
theorem card_NetSym (d L H dh f : ℕ) :
    Fintype.card (Equiv.Perm (Fin d) × (Fin L → BlockSym H dh f)) =
      d.factorial * (H.factorial * (2 ^ dh * dh.factorial) ^ (2 * H) * f.factorial) ^ L := by
  rw [Fintype.card_prod, Fintype.card_perm, Fintype.card_fin, Fintype.card_pi, card_BlockSym]
  simp

/-- Counting modulo symmetry: if every orbit (fibre of `π`) inside `S` has at
most `g` elements, then `#S ≤ g · #orbits`. -/
theorem orbits_lower {α β : Type*} [DecidableEq β] (S : Finset α) (π : α → β) (g : ℕ)
    (h : ∀ y ∈ S.image π, (S.filter fun x => π x = y).card ≤ g) :
    S.card ≤ g * (S.image π).card := by
  exact card_le_mul_card_image S g h

/-! ## Rescaling -/

/-- ReLU is positively homogeneous: rescaling the incoming weight by `c > 0`
and the outgoing weight by `1/c` leaves the unit unchanged. -/
theorem relu_rescale (a z c : ℝ) (hc : 0 < c) : (a / c) * max (c * z) 0 = a * max z 0 := by
  rw [show max (c * z) 0 = c * max z 0 by
    rcases le_total z 0 with h | h
    · rw [max_eq_right (by nlinarith), max_eq_right h, mul_zero]
    · rw [max_eq_left (by nlinarith), max_eq_left h]]
  field_simp

/-- **Fixed-point rigidity**: a positive scale `c` such that both `c` and
`1/c` map the integer lattice into itself is `1`. -/
theorem fixed_point_rigid (c : ℝ) (hc : 0 < c) (h1 : ∃ m : ℤ, c = m) (h2 : ∃ n : ℤ, c⁻¹ = n) :
    c = 1 := by
  obtain ⟨m, rfl⟩ := h1
  obtain ⟨n, hn⟩ := h2
  have hm : (0 : ℤ) < m := by exact_mod_cast hc
  have hmn : (m : ℝ) * n = 1 := by rw [← hn]; field_simp
  have hmn' : m * n = 1 := by exact_mod_cast hmn
  have : m = 1 := by
    rcases Int.eq_one_or_neg_one_of_mul_eq_one hmn' with h | h <;> omega
  simp [this]

/-- Normal binary floating-point numbers of precision `p` with exponents in
`[emin, emax]`. -/
def IsFloat (p : ℕ) (emin emax : ℤ) (x : ℝ) : Prop :=
  ∃ m e : ℤ, 2 ^ (p - 1) ≤ |m| ∧ |m| < 2 ^ p ∧ emin ≤ e ∧ e ≤ emax ∧ x = m * (2 : ℝ) ^ e

/-- **Dyadic rescaling** maps floats to floats (with the exponent window
shifted): the float grid is invariant under powers of two. -/
theorem float_dyadic (p : ℕ) (emin emax j : ℤ) (x : ℝ) (hx : IsFloat p emin emax x) :
    IsFloat p (emin + j) (emax + j) ((2 : ℝ) ^ j * x) := by
  obtain ⟨m, e, h1, h2, h3, h4, rfl⟩ := hx
  refine ⟨m, e + j, h1, h2, by omega, by omega, ?_⟩
  rw [zpow_add₀ (by norm_num)]; ring

/-- **Spacing is proportional to magnitude**: for a positive normal float
`x = m 2^e`, the local spacing `2^e` satisfies `2^{-p} < 2^e/x ≤ 2^{1-p}`. -/
theorem float_rel_spacing (p : ℕ) (hp : 0 < p) (m e : ℤ) (h1 : 2 ^ (p - 1) ≤ m) (h2 : m < 2 ^ p) :
    (2 : ℝ) ^ e / (m * 2 ^ e) ≤ 1 / 2 ^ (p - 1) ∧ 1 / 2 ^ p < (2 : ℝ) ^ e / (m * 2 ^ e) := by
  have he : (0 : ℝ) < 2 ^ e := by positivity
  have hm1 : (2 : ℝ) ^ (p - 1) ≤ m := by exact_mod_cast h1
  have hm2 : (m : ℝ) < 2 ^ p := by exact_mod_cast h2
  have hmpos : (0 : ℝ) < m := lt_of_lt_of_le (by positivity) hm1
  rw [div_mul_cancel_right₀ (ne_of_gt he)]
  constructor
  · simp only [one_div]; exact inv_anti₀ (by positivity) hm1
  · simp only [one_div]; exact inv_strictAnti₀ hmpos hm2

/-! ## Softmax -/

/-- Softmax over a finite set of keys `T`. -/
noncomputable def softmax {ι : Type*} (T : Finset ι) (z : ι → ℝ) (i : ι) : ℝ :=
  Real.exp (z i) / ∑ j ∈ T, Real.exp (z j)

theorem softmax_pos {ι : Type*} (T : Finset ι) (hT : T.Nonempty) (z : ι → ℝ) (i : ι) :
    0 < softmax T z i := by
  unfold softmax
  have : 0 < ∑ j ∈ T, Real.exp (z j) := sum_pos (fun j _ => Real.exp_pos _) hT
  positivity

theorem softmax_shift {ι : Type*} (T : Finset ι) (z : ι → ℝ) (c : ℝ) (i : ι) :
    softmax T (fun j => z j + c) i = softmax T z i := by
  unfold softmax
  simp only [Real.exp_add]
  rw [← sum_mul]
  have : Real.exp c ≠ 0 := (Real.exp_pos c).ne'
  by_cases h : ∑ j ∈ T, Real.exp (z j) = 0
  · simp [h]
  · field_simp

/-- **Saturation**: equal (snapped) logits give exactly uniform attention. -/
theorem softmax_uniform {ι : Type*} (T : Finset ι) (z : ι → ℝ) (c : ℝ)
    (h : ∀ j ∈ T, z j = c) (i : ι) (hi : i ∈ T) : softmax T z i = 1 / T.card := by
  unfold softmax
  rw [sum_congr rfl (fun j hj => by rw [h j hj]), sum_const, h i hi, nsmul_eq_mul]
  have : Real.exp c ≠ 0 := (Real.exp_pos c).ne'
  field_simp

/-- **Masking is not a zero weight.**  Removing key `j` from the support
rescales every other weight by `Z/(Z + e^{z_j}) < 1`, where `Z` is the
partition function without `j`. -/
theorem softmax_mask {ι : Type*} [DecidableEq ι] (T : Finset ι) (z : ι → ℝ) (j : ι) (hj : j ∈ T)
    (hne : (T.erase j).Nonempty) (i : ι) :
    softmax T z i = softmax (T.erase j) z i *
      ((∑ l ∈ T.erase j, Real.exp (z l)) / (∑ l ∈ T.erase j, Real.exp (z l) + Real.exp (z j))) ∧
    (∑ l ∈ T.erase j, Real.exp (z l)) / (∑ l ∈ T.erase j, Real.exp (z l) + Real.exp (z j)) < 1 := by
  have hZ : 0 < ∑ l ∈ T.erase j, Real.exp (z l) := sum_pos (fun l _ => Real.exp_pos _) hne
  have hT : ∑ l ∈ T, Real.exp (z l) = ∑ l ∈ T.erase j, Real.exp (z l) + Real.exp (z j) := by
    rw [← add_sum_erase T _ hj, add_comm]
  have hej := Real.exp_pos (z j)
  constructor
  · unfold softmax; rw [hT]; field_simp
  · rw [div_lt_one (by linarith)]; linarith

/-- Ties between two independent uniform logits on `K` levels have probability
exactly `1/K`. -/
theorem tie_prob (K : ℕ) (hK : 0 < K) :
    ((univ.filter fun p : Fin K × Fin K => p.1 = p.2).card : ℝ) / (Fintype.card (Fin K × Fin K))
      = 1 / K := by
  have : (univ.filter fun p : Fin K × Fin K => p.1 = p.2) = univ.image fun i => (i, i) := by
    ext ⟨a, b⟩; simp [eq_comm]
  rw [this, card_image_of_injective _ (fun a b h => by simpa using h)]
  have : (K : ℝ) ≠ 0 := by exact_mod_cast hK.ne'
  simp [Fintype.card_prod]

/-- **Bounded logits give bounded cross-entropy**: if every logit lies in
`[-B, B]`, every softmax weight is at least `e^{-2B}/#T`, so the token loss
`-ln p` is at most `ln #T + 2B`. -/
theorem softmax_lower {ι : Type*} (T : Finset ι) (hT : T.Nonempty) (z : ι → ℝ) (B : ℝ)
    (hz : ∀ j, -B ≤ z j ∧ z j ≤ B) (i : ι) :
    Real.exp (-(2 * B)) / T.card ≤ softmax T z i := by
  unfold softmax
  have hc : (0 : ℝ) < T.card := by exact_mod_cast hT.card_pos
  have hsum : ∑ j ∈ T, Real.exp (z j) ≤ T.card * Real.exp B := by
    calc ∑ j ∈ T, Real.exp (z j) ≤ ∑ j ∈ T, Real.exp B :=
          sum_le_sum fun j _ => Real.exp_le_exp.mpr (hz j).2
      _ = T.card * Real.exp B := by rw [sum_const, nsmul_eq_mul]
  have hpos : 0 < ∑ j ∈ T, Real.exp (z j) := sum_pos (fun j _ => Real.exp_pos _) hT
  rw [div_le_div_iff₀ hc hpos]
  calc Real.exp (-(2 * B)) * ∑ j ∈ T, Real.exp (z j)
      ≤ Real.exp (-(2 * B)) * (T.card * Real.exp B) :=
        mul_le_mul_of_nonneg_left hsum (Real.exp_pos _).le
    _ = Real.exp (-B) * T.card := by
        rw [show -B = -(2 * B) + B by ring, Real.exp_add]; ring
    _ ≤ Real.exp (z i) * T.card :=
        mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (hz i).1) hc.le

/-! ## Zero weights and pruning -/

/-- A parameter that may be pruned has `V + 1` states: absent, or one of `V`
stored values (one of which may be the value `0`). -/
theorem card_prunable (V : ℕ) : Fintype.card (Option (Fin V)) = V + 1 := by simp

/-- An absent weight is not a learned zero. -/
theorem absent_ne_zero (V : ℕ) [NeZero V] : (none : Option (Fin V)) ≠ some 0 := by simp

/-- The pruning mask of `N` parameters has `2^N` states: exactly `N` bits. -/
theorem mask_bits (N : ℕ) :
    Fintype.card (Fin N → Bool) = 2 ^ N ∧ Real.logb 2 ((2 : ℝ) ^ N) = N := by
  refine ⟨by simp, ?_⟩
  rw [Real.logb_pow, Real.logb_self_eq_one (by norm_num), mul_one]

/-- Sparse configurations: `(V+1)^N = ∑_k C(N,k) V^k` (choose the support,
then the values). -/
theorem sparse_count (N V : ℕ) :
    Fintype.card (Fin N → Option (Fin V)) = ∑ k ∈ range (N + 1), N.choose k * V ^ k := by
  rw [Fintype.card_pi]
  simp only [Fintype.card_option, Fintype.card_fin, prod_const, card_univ]
  rw [add_pow]
  apply sum_congr rfl; intro k _; simp [mul_comm]

/-- Zero is one bit (granular measure form): the empty configuration and the
configuration "the point 0" have contents `0 < 2ε`. -/
theorem zero_vs_absent {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    (ε : K) (hε : 0 < ε) : QE.mu ε (∅ : Finset ℤ) = 0 ∧ QE.mu ε {0} = 2 * ε ∧ (0 : K) < 2 * ε := by
  refine ⟨by simp [QE.mu], by simp [QE.mu], by linarith⟩

/-! ## Finite sampling: a Chernoff–Hoeffding-type bound, union bound, Occam -/

section Sampling

variable {Z : Type*} [Fintype Z]

/-- Weight of a sample `ω ∈ Z^n` drawn i.i.d. from the finite law `q`. -/
def wt {n : ℕ} (q : Z → ℝ) (ω : Fin n → Z) : ℝ := ∏ i, q (ω i)

/-- Probability of an event on the finite sample space `Z^n`. -/
noncomputable def probS (n : ℕ) (q : Z → ℝ) (A : (Fin n → Z) → Prop) : ℝ := by
  classical exact ∑ ω, if A ω then wt q ω else 0

theorem wt_nonneg {n : ℕ} (q : Z → ℝ) (hq : ∀ z, 0 ≤ q z) (ω : Fin n → Z) : 0 ≤ wt q ω :=
  prod_nonneg fun i _ => hq _

/-- Product structure: `∑_ω ∏_i g(ω_i) = (∑_z g z)^n`. -/
theorem sum_prod_eq_pow (n : ℕ) (g : Z → ℝ) :
    ∑ ω : Fin n → Z, ∏ i, g (ω i) = (∑ z, g z) ^ n := by
  rw [sum_pow', Fintype.piFinset_univ]

/-- Moment generating bound (finite Hoeffding lemma, weak constant): for a
`[0,1]`-valued `f` with mean `μ` and `0 ≤ s ≤ 1`,
`∑_z q z e^{s(f z - μ)} ≤ e^{s²/4}`. -/
theorem mgf_le (q : Z → ℝ) (hq : ∀ z, 0 ≤ q z) (hq1 : ∑ z, q z = 1) (f : Z → ℝ)
    (hf : ∀ z, 0 ≤ f z ∧ f z ≤ 1) (s : ℝ) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    ∑ z, q z * Real.exp (s * (f z - ∑ y, q y * f y)) ≤ Real.exp (s ^ 2 / 4) := by
  set μ := ∑ y, q y * f y with hμ
  have hμ0 : 0 ≤ μ := sum_nonneg fun y _ => mul_nonneg (hq y) (hf y).1
  have hμ1 : μ ≤ 1 := by
    calc μ ≤ ∑ y, q y * 1 := sum_le_sum fun y _ => mul_le_mul_of_nonneg_left (hf y).2 (hq y)
      _ = 1 := by simp [hq1]
  -- pointwise: e^y ≤ 1 + y + y²
  have hpt : ∀ z, Real.exp (s * (f z - μ)) ≤ 1 + s * (f z - μ) + s ^ 2 * (f z - μ) ^ 2 := by
    intro z
    have hy : |s * (f z - μ)| ≤ 1 := by
      rw [abs_mul, abs_of_nonneg hs0]
      have : |f z - μ| ≤ 1 := by rw [abs_le]; constructor <;> linarith [(hf z).1, (hf z).2]
      nlinarith [abs_nonneg (f z - μ)]
    have := Real.abs_exp_sub_one_sub_id_le hy
    rw [abs_le] at this
    nlinarith [this.2]
  have hvar : ∑ z, q z * (f z - μ) ^ 2 ≤ 1 / 4 := by
    have e1 : ∑ z, q z * (f z - μ) ^ 2 = ∑ z, q z * f z ^ 2 - μ ^ 2 := by
      have : ∀ z, q z * (f z - μ) ^ 2 = q z * f z ^ 2 - 2 * μ * (q z * f z) + μ ^ 2 * q z := by
        intro z; ring
      simp only [this, sum_add_distrib, sum_sub_distrib, ← mul_sum, hq1, ← hμ]; ring
    have e2 : ∑ z, q z * f z ^ 2 ≤ μ :=
      sum_le_sum fun z _ => mul_le_mul_of_nonneg_left (by nlinarith [(hf z).1, (hf z).2]) (hq z)
    rw [e1]; nlinarith [sq_nonneg (μ - 1 / 2)]
  calc ∑ z, q z * Real.exp (s * (f z - μ))
      ≤ ∑ z, q z * (1 + s * (f z - μ) + s ^ 2 * (f z - μ) ^ 2) :=
        sum_le_sum fun z _ => mul_le_mul_of_nonneg_left (hpt z) (hq z)
    _ = 1 + s * (μ - μ) + s ^ 2 * ∑ z, q z * (f z - μ) ^ 2 := by
        have : ∀ z, q z * (1 + s * (f z - μ) + s ^ 2 * (f z - μ) ^ 2)
            = q z + s * (q z * f z) - s * μ * q z + s ^ 2 * (q z * (f z - μ) ^ 2) := by
          intro z; ring
        simp only [this, sum_add_distrib, sum_sub_distrib, ← mul_sum, hq1, ← hμ]; ring
    _ ≤ 1 + s ^ 2 / 4 := by nlinarith [sq_nonneg s]
    _ ≤ Real.exp (s ^ 2 / 4) := by linarith [Real.add_one_le_exp (s ^ 2 / 4)]

/-- **Chernoff–Hoeffding-type upper tail on a finite product space.**  For
i.i.d. `[0,1]`-valued observations and `0 ≤ t ≤ 1/2`,
`P(∑ᵢ (f(ωᵢ) - μ) ≥ n t) ≤ e^{-n t²}`.  (Hoeffding's constant is `2` in place
of `1`; this weaker bound is proved here from scratch, by finite sums only.) -/
theorem chernoff_upper (q : Z → ℝ) (hq : ∀ z, 0 ≤ q z) (hq1 : ∑ z, q z = 1) (f : Z → ℝ)
    (hf : ∀ z, 0 ≤ f z ∧ f z ≤ 1) (n : ℕ) (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1 / 2) :
    probS n q (fun ω => (n : ℝ) * t ≤ ∑ i, (f (ω i) - ∑ y, q y * f y)) ≤
      Real.exp (-(n * t ^ 2)) := by
  classical
  set μ := ∑ y, q y * f y
  set s := 2 * t
  have hs0 : 0 ≤ s := by positivity
  have hs1 : s ≤ 1 := by linarith
  unfold probS
  calc (∑ ω : Fin n → Z, if (n : ℝ) * t ≤ ∑ i, (f (ω i) - μ) then wt q ω else 0)
      ≤ ∑ ω : Fin n → Z, wt q ω * Real.exp (s * (∑ i, (f (ω i) - μ) - n * t)) := by
        apply sum_le_sum; intro ω _
        have hw := wt_nonneg q hq ω
        split_ifs with h
        · have : 1 ≤ Real.exp (s * (∑ i, (f (ω i) - μ) - n * t)) :=
            Real.one_le_exp (mul_nonneg hs0 (by linarith))
          nlinarith
        · positivity
    _ = Real.exp (-(s * n * t)) * ∑ ω : Fin n → Z, ∏ i, (q (ω i) * Real.exp (s * (f (ω i) - μ))) := by
        rw [mul_sum]; apply sum_congr rfl; intro ω _
        unfold wt
        rw [prod_mul_distrib, ← Real.exp_sum]
        rw [show s * (∑ i, (f (ω i) - μ) - n * t) = -(s * n * t) + ∑ i, s * (f (ω i) - μ) by
          rw [← mul_sum]; ring, Real.exp_add]
        ring
    _ = Real.exp (-(s * n * t)) * (∑ z, q z * Real.exp (s * (f z - μ))) ^ n := by
        rw [sum_prod_eq_pow n (fun z => q z * Real.exp (s * (f z - μ)))]
    _ ≤ Real.exp (-(s * n * t)) * Real.exp (s ^ 2 / 4) ^ n := by
        apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
        apply pow_le_pow_left₀ (sum_nonneg fun z _ => mul_nonneg (hq z) (Real.exp_pos _).le)
        exact mgf_le q hq hq1 f hf s hs0 hs1
    _ = Real.exp (-(n * t ^ 2)) := by
        rw [← Real.exp_nat_mul, ← Real.exp_add]; congr 1; simp only [s]; ring

/-- Lower tail, from the upper tail applied to `1 - f`. -/
theorem chernoff_lower (q : Z → ℝ) (hq : ∀ z, 0 ≤ q z) (hq1 : ∑ z, q z = 1) (f : Z → ℝ)
    (hf : ∀ z, 0 ≤ f z ∧ f z ≤ 1) (n : ℕ) (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1 / 2) :
    probS n q (fun ω => ∑ i, (f (ω i) - ∑ y, q y * f y) ≤ -((n : ℝ) * t)) ≤
      Real.exp (-(n * t ^ 2)) := by
  classical
  have h := chernoff_upper q hq hq1 (fun z => 1 - f z)
    (fun z => ⟨by linarith [(hf z).2], by linarith [(hf z).1]⟩) n t ht0 ht1
  have hmean : ∑ y, q y * (1 - f y) = 1 - ∑ y, q y * f y := by
    simp only [mul_sub, mul_one, sum_sub_distrib, hq1]
  refine le_trans (le_of_eq ?_) h
  unfold probS
  apply sum_congr rfl; intro ω _
  beta_reduce
  rw [hmean]
  have : ∑ i, (1 - f (ω i) - (1 - ∑ y, q y * f y)) = -∑ i, (f (ω i) - ∑ y, q y * f y) := by
    rw [← sum_neg_distrib]; congr 1; ext i; ring
  rw [this]
  congr 1; apply propext; constructor <;> intro h <;> linarith

/-- Two-sided, dimension-free sampling bound:
`P(|∑ᵢ (f(ωᵢ) - μ)| ≥ n t) ≤ 2 e^{-n t²}`. -/
theorem chernoff_two_sided (q : Z → ℝ) (hq : ∀ z, 0 ≤ q z) (hq1 : ∑ z, q z = 1) (f : Z → ℝ)
    (hf : ∀ z, 0 ≤ f z ∧ f z ≤ 1) (n : ℕ) (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1 / 2) :
    probS n q (fun ω => (n : ℝ) * t ≤ |∑ i, (f (ω i) - ∑ y, q y * f y)|) ≤
      2 * Real.exp (-(n * t ^ 2)) := by
  classical
  have hu := chernoff_upper q hq hq1 f hf n t ht0 ht1
  have hl := chernoff_lower q hq hq1 f hf n t ht0 ht1
  unfold probS at *
  have : ∀ ω : Fin n → Z,
      (if (n : ℝ) * t ≤ |∑ i, (f (ω i) - ∑ y, q y * f y)| then wt q ω else 0) ≤
      (if (n : ℝ) * t ≤ ∑ i, (f (ω i) - ∑ y, q y * f y) then wt q ω else 0) +
      (if ∑ i, (f (ω i) - ∑ y, q y * f y) ≤ -((n : ℝ) * t) then wt q ω else 0) := by
    intro ω
    have hw := wt_nonneg q hq ω
    have key : (n : ℝ) * t ≤ |∑ i, (f (ω i) - ∑ y, q y * f y)| →
        ((n : ℝ) * t ≤ ∑ i, (f (ω i) - ∑ y, q y * f y) ∨
          ∑ i, (f (ω i) - ∑ y, q y * f y) ≤ -((n : ℝ) * t)) := fun h => by
      rcases le_abs.mp h with h | h
      · left; exact h
      · right; linarith
    split_ifs with h1 h2 h3 h3 <;> try linarith
    rcases key h1 with h | h <;> contradiction
  calc _ ≤ ∑ ω : Fin n → Z, ((if (n : ℝ) * t ≤ ∑ i, (f (ω i) - ∑ y, q y * f y) then wt q ω else 0) +
      (if ∑ i, (f (ω i) - ∑ y, q y * f y) ≤ -((n : ℝ) * t) then wt q ω else 0)) :=
        sum_le_sum fun ω _ => this ω
    _ ≤ _ := by rw [sum_add_distrib]; linarith

/-- **Finite union bound.** -/
theorem union_bound {ι : Type*} (n : ℕ) (q : Z → ℝ) (hq : ∀ z, 0 ≤ q z) (H : Finset ι)
    (B : ι → (Fin n → Z) → Prop) :
    probS n q (fun ω => ∃ h ∈ H, B h ω) ≤ ∑ h ∈ H, probS n q (B h) := by
  classical
  unfold probS
  rw [sum_comm]
  apply sum_le_sum; intro ω _
  have hw := wt_nonneg q hq ω
  split_ifs with hex
  · obtain ⟨h, hh, hb⟩ := hex
    calc wt q ω = (if B h ω then wt q ω else 0) := by rw [if_pos hb]
      _ ≤ ∑ h' ∈ H, (if B h' ω then wt q ω else 0) :=
        single_le_sum (f := fun h' => if B h' ω then wt q ω else 0)
          (fun h' _ => by split_ifs <;> linarith) hh
  · exact sum_nonneg fun h' _ => by split_ifs <;> linarith

/-- **Finite-class (Occam) bound.**  For a finite class `H` of hypotheses with
`[0,1]`-valued losses `ℓ h z`, risk `R h = ∑ q ℓ h` and `m` i.i.d. samples,
`P(∃ h ∈ H, R h - R̂ h ≥ t) ≤ #H · e^{-m t²}` for `0 ≤ t ≤ 1/2`. -/
theorem occam {ι : Type*} (q : Z → ℝ) (hq : ∀ z, 0 ≤ q z) (hq1 : ∑ z, q z = 1)
    (H : Finset ι) (ℓ : ι → Z → ℝ) (hℓ : ∀ h z, 0 ≤ ℓ h z ∧ ℓ h z ≤ 1) (m : ℕ) (hm : 0 < m)
    (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1 / 2) :
    probS m q (fun ω => ∃ h ∈ H,
        t ≤ (∑ z, q z * ℓ h z) - (∑ i, ℓ h (ω i)) / m) ≤ H.card * Real.exp (-(m * t ^ 2)) := by
  classical
  refine (union_bound m q hq H _).trans ?_
  rw [← nsmul_eq_mul, ← sum_const]
  apply sum_le_sum; intro h _
  refine le_trans (le_of_eq ?_) (chernoff_lower q hq hq1 (ℓ h) (hℓ h) m t ht0 ht1)
  unfold probS
  apply sum_congr rfl; intro ω _
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have e : ∑ i, (ℓ h (ω i) - ∑ y, q y * ℓ h y) = ∑ i, ℓ h (ω i) - m * ∑ y, q y * ℓ h y := by
    rw [sum_sub_distrib]; simp
  beta_reduce
  rw [e]
  congr 1; apply propext
  rw [le_sub_iff_add_le, ← le_sub_iff_add_le', div_le_iff₀ hmR]
  constructor <;> intro h <;> nlinarith

/-- Solving `#H e^{-m t²} = δ` for `t`. -/
theorem occam_radius (Hc : ℕ) (hH : 0 < Hc) (δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) (m : ℕ)
    (hm : 0 < m) :
    let t := Real.sqrt ((Real.log Hc + Real.log (1 / δ)) / m)
    (Hc : ℝ) * Real.exp (-(m * t ^ 2)) = δ := by
  intro t
  have hHR : (0 : ℝ) < Hc := by exact_mod_cast hH
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have h1 : 0 ≤ Real.log Hc := Real.log_nonneg (by exact_mod_cast hH)
  have h2 : 0 ≤ Real.log (1 / δ) := Real.log_nonneg (by rw [le_div_iff₀ hδ0]; linarith)
  have ht : (m : ℝ) * t ^ 2 = Real.log Hc + Real.log (1 / δ) := by
    simp only [t]
    rw [Real.sq_sqrt (by positivity)]; field_simp
  rw [ht, neg_add, Real.exp_add, Real.exp_neg, Real.exp_neg, Real.exp_log hHR,
    Real.exp_log (by positivity)]
  field_simp

/-- **Occam bound for a granular network**: the parameter box `{-M..M}^N`
indexes the hypotheses, `#H = (2M+1)^N`, and with
`t = √((N ln(2M+1) + ln(1/δ))/m) ≤ 1/2`, with probability at least `1-δ`
every lattice network has `R - R̂ < t`. -/
theorem occam_lattice (q : Z → ℝ) (hq : ∀ z, 0 ≤ q z) (hq1 : ∑ z, q z = 1) (N M : ℕ)
    (ℓ : (Fin N → ℤ) → Z → ℝ) (hℓ : ∀ h z, 0 ≤ ℓ h z ∧ ℓ h z ≤ 1) (m : ℕ) (hm : 0 < m)
    (δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1)
    (ht : Real.sqrt ((Real.log (((2 * M + 1) ^ N : ℕ) : ℝ) + Real.log (1 / δ)) / m) ≤ 1 / 2) :
    probS m q (fun ω => ∃ θ ∈ box N M,
        Real.sqrt ((Real.log (((2 * M + 1) ^ N : ℕ) : ℝ) + Real.log (1 / δ)) / m) ≤
          (∑ z, q z * ℓ θ z) - (∑ i, ℓ θ (ω i)) / m) ≤ δ := by
  have h := occam q hq hq1 (box N M) ℓ hℓ m hm _ (Real.sqrt_nonneg _) ht
  rw [card_box] at h
  refine h.trans (le_of_eq ?_)
  exact occam_radius _ (by positivity) δ hδ0 hδ1 m hm

/-- `ln (2M+1)^N = N ln(2M+1)`: the complexity term is linear in `N`. -/
theorem log_box (N M : ℕ) : Real.log (((2 * M + 1) ^ N : ℕ) : ℝ) = N * Real.log (2 * M + 1) := by
  push_cast; rw [Real.log_pow]

end Sampling

/-! ## Transformer parameter counts -/

/-- One GPT-2 block (pre-LayerNorm, biased projections, MLP width `4d`):
LN₁ (`2d`), fused QKV (`3d² + 3d`), output projection (`d² + d`),
LN₂ (`2d`), MLP up (`4d² + 4d`), MLP down (`4d² + d`). -/
def gpt2Block (d : ℕ) : ℕ :=
  2 * d + (3 * d * d + 3 * d) + (d * d + d) + 2 * d + (4 * d * d + 4 * d) + (4 * d * d + d)

/-- GPT-2: token embedding `V d` (tied with the unembedding), learned positions
`T d`, `L` blocks, final LayerNorm `2d`. -/
def gpt2Params (V T d L : ℕ) : ℕ := V * d + T * d + L * gpt2Block d + 2 * d

theorem gpt2_closed (V T d L : ℕ) :
    gpt2Params V T d L = 12 * L * d ^ 2 + 13 * L * d + V * d + T * d + 2 * d := by
  unfold gpt2Params gpt2Block; ring

theorem gpt2_small : gpt2Params 50257 1024 768 12 = 124439808 := by
  unfold gpt2Params gpt2Block; norm_num

/-- Splitting into `H` heads of width `d/H` does not change the count. -/
theorem heads_count (H dh : ℕ) : H * ((H * dh) * dh) = (H * dh) * (H * dh) := by ring

/-- One LLaMA block: RMSNorm gains (`2d`), `W_Q,W_K,W_V,W_O` (`4d²`, no bias),
SwiGLU MLP with three `d × f` matrices. -/
def llamaBlock (d f : ℕ) : ℕ := 2 * d + 4 * d * d + 3 * d * f

/-- LLaMA: untied embedding and unembedding (`2 V d`), `L` blocks, final norm. -/
def llamaParams (V d f L : ℕ) : ℕ := 2 * V * d + L * llamaBlock d f + d

theorem llama7b : llamaParams 32000 4096 11008 32 = 6738415616 := by
  unfold llamaParams llamaBlock; norm_num

/-! ## Single-bit faults in two's complement -/

/-- Bit weights of a `(b+1)`-bit two's-complement integer: `2^j` for the
low bits and `-2^b` for the sign bit. -/
def bitWeight (b : ℕ) (j : Fin (b + 1)) : ℤ :=
  if (j : ℕ) = b then -(2 : ℤ) ^ b else 2 ^ (j : ℕ)

/-- Value of a two's-complement bit pattern. -/
def tcVal (b : ℕ) (β : Fin (b + 1) → Bool) : ℤ :=
  ∑ j, bitWeight b j * (if β j then 1 else 0)

theorem abs_bitWeight (b : ℕ) (j : Fin (b + 1)) : |bitWeight b j| = 2 ^ (j : ℕ) := by
  unfold bitWeight; split_ifs with h
  · rw [abs_neg, h, abs_of_pos (by positivity)]
  · rw [abs_of_pos (by positivity)]

/-- **A single bit flip moves the lattice index by exactly `±2^j`**, hence
the parameter by exactly `2ε·2^j`. -/
theorem bitflip_jump (b : ℕ) (β : Fin (b + 1) → Bool) (j : Fin (b + 1)) :
    |tcVal b (Function.update β j (!β j)) - tcVal b β| = 2 ^ (j : ℕ) := by
  unfold tcVal
  have hfun : (fun i => bitWeight b i * (if Function.update β j (!β j) i then 1 else 0)) =
      Function.update (fun i => bitWeight b i * (if β i then 1 else 0)) j
        (bitWeight b j * (if !β j then 1 else 0)) := by
    funext i; by_cases hi : i = j
    · subst hi; simp
    · simp [hi]
  rw [hfun, Finset.sum_update_of_mem (mem_univ j), ← Finset.add_sum_erase _ _ (mem_univ j)]
  rw [Finset.sdiff_singleton_eq_erase]
  have : bitWeight b j * (if (!β j) = true then 1 else 0) + ∑ x ∈ univ.erase j,
      bitWeight b x * (if β x = true then 1 else 0) -
      (bitWeight b j * (if β j = true then 1 else 0) + ∑ x ∈ univ.erase j,
      bitWeight b x * (if β x = true then 1 else 0)) =
      bitWeight b j * ((if (!β j) = true then 1 else 0) - (if β j = true then 1 else 0)) := by ring
  rw [this, abs_mul, abs_bitWeight]
  cases β j <;> simp

/-- The single-fault profile of `N` parameters of `b+1` bits has exactly
`N (b+1)` entries. -/
theorem card_faults (N b : ℕ) : Fintype.card (Fin N × Fin (b + 1)) = N * (b + 1) := by simp

/-! ## The enumerable toy: a one-dimensional query–key logit -/

/-- Toy solution predicate on int8 indices (`θ = k/64`):
`(ab - 1)² ≤ 2^{-8}` iff `|k l - 4096| ≤ 256`. -/
def toySol (k l : ℤ) : Bool := decide (|k * l - 4096| ≤ 256)

theorem toy_reference : toySol 93 44 = true := by decide

/-- Quantisation of the reference solution `(93, 44)` along the dyadic ladder:
ratios `2` and `4` succeed, ratio `8` fails. -/
theorem toy_ladder :
    (2 * qz 2 93, 2 * qz 2 44) = (94, 44) ∧ toySol 94 44 = true ∧
    (4 * qz 4 93, 4 * qz 4 44) = (92, 44) ∧ toySol 92 44 = true ∧
    (8 * qz 8 93, 8 * qz 8 44) = (96, 48) ∧ toySol 96 48 = false := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

/-- Quantisability profile at ratio `4`: `14` of the `16` fine points of the
coarse cell are solutions. -/
theorem toy_profile_4 :
    ((cellZ 4 (qz 4 93) ×ˢ cellZ 4 (qz 4 44)).filter fun p => toySol p.1 p.2 = true).card = 14 := by
  decide

/-- At ratio `8`: `16` of `64`. -/
theorem toy_profile_8 :
    ((cellZ 8 (qz 8 93) ×ˢ cellZ 8 (qz 8 44)).filter fun p => toySol p.1 p.2 = true).card = 16 := by
  decide

/-- Single-bit faults of the reference point: flipping bits `0,1,2` of `93`
(giving `92, 95, 89`) or bits `0,1` of `44` (giving `45, 46`) keeps a solution;
bit `3` of `93` (`85`) and bit `2` of `44` (`40`) do not. -/
theorem toy_faults :
    toySol 92 44 = true ∧ toySol 95 44 = true ∧ toySol 89 44 = true ∧ toySol 85 44 = false ∧
    toySol 93 45 = true ∧ toySol 93 46 = true ∧ toySol 93 40 = false := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

/-! ## Normalisation layers and the residual stream -/

section Norms

variable {d : ℕ}

/-- LayerNorm with gain `γ`, bias `β` and stabiliser `κ`. -/
noncomputable def layerNorm (κ : ℝ) (γ β x : Fin d → ℝ) (i : Fin d) : ℝ :=
  γ i * ((x i - (∑ j, x j) / d) / Real.sqrt ((∑ j, (x j - (∑ l, x l) / d) ^ 2) / d + κ)) + β i

/-- **LayerNorm is permutation-equivariant**: permuting the residual stream and
the gains/biases commutes with LayerNorm. -/
theorem layerNorm_perm (κ : ℝ) (γ β x : Fin d → ℝ) (σ : Equiv.Perm (Fin d)) (i : Fin d) :
    layerNorm κ (γ ∘ σ) (β ∘ σ) (x ∘ σ) i = layerNorm κ γ β x (σ i) := by
  unfold layerNorm
  simp only [Function.comp]
  rw [Equiv.sum_comp σ x, Equiv.sum_comp σ (fun j => (x j - (∑ l, x l) / d) ^ 2)]

/-- RMSNorm with gain `γ`. -/
noncomputable def rmsNorm (κ : ℝ) (γ x : Fin d → ℝ) (i : Fin d) : ℝ :=
  γ i * x i / Real.sqrt ((∑ j, x j ^ 2) / d + κ)

/-- **RMSNorm is equivariant under signed permutations**
`x ↦ (sᵢ x_{σ i})` with `sᵢ = ±1`. -/
theorem rmsNorm_signed_perm (κ : ℝ) (γ x s : Fin d → ℝ) (hs : ∀ i, s i = 1 ∨ s i = -1)
    (σ : Equiv.Perm (Fin d)) (i : Fin d) :
    rmsNorm κ (γ ∘ σ) (fun j => s j * x (σ j)) i = s i * rmsNorm κ γ x (σ i) := by
  unfold rmsNorm
  have hsq : ∀ j, (s j * x (σ j)) ^ 2 = x (σ j) ^ 2 := by
    intro j; rcases hs j with h | h <;> rw [h] <;> ring
  simp only [Function.comp, hsq]
  rw [Equiv.sum_comp σ (fun j => x j ^ 2)]
  ring

end Norms

/-- **Sharpness is not reparametrisation invariant** (Dinh et al.): for the
loss `(ab - c)²` the Hessian trace at `(a,b)` is `2(a² + b²)`; the rescaled
solution `(αa, b/α)` has trace `2(α²a² + b²/α²)`, unbounded in `α`, while the
function `ab` is unchanged. -/
theorem sharpness_rescale (a b α : ℝ) (hα : α ≠ 0) :
    (α * a) * (b / α) = a * b ∧
    2 * ((α * a) ^ 2 + (b / α) ^ 2) = 2 * (α ^ 2 * a ^ 2 + b ^ 2 / α ^ 2) := by
  constructor <;> field_simp

theorem sharpness_unbounded (a b : ℝ) (ha : a ≠ 0) (K : ℝ) :
    ∃ α : ℝ, 0 < α ∧ K < 2 * ((α * a) ^ 2 + (b / α) ^ 2) := by
  have ha2 : 0 < a ^ 2 := by positivity
  refine ⟨|K| / a ^ 2 + 1, by positivity, ?_⟩
  set α := |K| / a ^ 2 + 1
  have hα1 : 1 ≤ α := by simp only [α]; have := div_nonneg (abs_nonneg K) ha2.le; linarith
  have h1 : α * a ^ 2 ≥ |K| + a ^ 2 := by
    simp only [α]; rw [add_mul, div_mul_cancel₀ _ (ne_of_gt ha2), one_mul]
  have h2 : (α * a) ^ 2 ≥ α * a ^ 2 := by nlinarith
  nlinarith [sq_nonneg (b / α), le_abs_self K]

end QE.Learn
