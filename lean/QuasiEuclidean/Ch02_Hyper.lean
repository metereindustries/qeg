-- SPDX-License-Identifier: MIT
-- Copyright 2026 Metere Industries, Inc. Author: Alfredo Metere.
-- Quasi-Euclidean Granular Geometry. Any derivative work must carry this notice:
--   This work is derivative of the Quasi-Euclidean Granular Geometry book
--   authored by Alfredo Metere. Copyright 2026 Metere Industries, Inc.
--   All rights reserved
-- See LICENSE.md and NOTICE.

import QuasiEuclidean.Basic

/-!
# Chapter 2: the hyperfinite continuum

Formal companion of `chapters/02-hyperfinite-continuum.tex`.

* Snapping to the nearest centre over an arbitrary floor ring (covers `ℝ`, `ℚ`,
  and the physical instantiation `ε = ℓ_P`), uniqueness of the nearest centre
  over an arbitrary ordered field.
* Infinitesimals in Mathlib's `Hyperreal` (via `ArchimedeanClass.mk`: `x` is
  infinitesimal iff `0 < mk x`, finite iff `0 ≤ mk x`), monads, standard part.
* Hyperintegers as ultrapower classes of integer sequences, the factorial
  lattice `N = M!`, the dyadic lattice, and the hyper-snap defined
  sequence-wise (a hand-made instance of Łoś's theorem).
* Transfer for the ultrapower of `ℝ` in an arbitrary first-order language,
  as a corollary of Mathlib's Łoś theorem.
-/

namespace QE.Hyper

open ArchimedeanClass Filter

section Snap

set_option linter.unusedSectionVars false

variable {K' : Type*} [Field K']

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-- Distance between lattice centres is `2ε` times the index distance. -/
theorem centre_sub (ε : K) (k j : ℤ) :
    QE.centre ε k - QE.centre ε j = 2 * ε * ((k - j : ℤ) : K) := by
  unfold QE.centre; push_cast; ring

/-- Uniqueness of the nearest centre: a point lies in at most one Voronoi cell
`2εk + [-ε, ε)`.  Valid in every ordered field. -/
theorem cell_unique {ε : K} (hε : 0 < ε) {x : K} {k j : ℤ}
    (hk : QE.centre ε k - ε ≤ x ∧ x < QE.centre ε k + ε)
    (hj : QE.centre ε j - ε ≤ x ∧ x < QE.centre ε j + ε) : k = j := by
  unfold QE.centre at hk hj
  have h1 : 2 * ε * ((k : K) - j) < 2 * ε * 1 := by nlinarith
  have h2 : 2 * ε * (-1) < 2 * ε * ((k : K) - j) := by nlinarith
  have hpos : (0 : K) < 2 * ε := by linarith
  have a1 : ((k - j : ℤ) : K) < ((1 : ℤ) : K) := by
    push_cast; exact lt_of_mul_lt_mul_left h1 hpos.le
  have a2 : ((-1 : ℤ) : K) < ((k - j : ℤ) : K) := by
    push_cast; exact lt_of_mul_lt_mul_left h2 hpos.le
  have b1 := Int.cast_lt.mp a1
  have b2 := Int.cast_lt.mp a2
  omega

/-- Distinct lattice centres are at distance at least `2ε`. -/
theorem centre_sep {ε : K} (hε : 0 < ε) {k j : ℤ} (h : k ≠ j) :
    2 * ε ≤ |QE.centre ε k - QE.centre ε j| := by
  rw [centre_sub, abs_mul, abs_of_pos (by linarith : (0:K) < 2 * ε)]
  have : (1 : K) ≤ |((k - j : ℤ) : K)| := by
    rw [← Int.cast_abs]
    exact_mod_cast Int.one_le_abs (sub_ne_zero.mpr h)
  nlinarith

/-- Robinson's sum bound in granular form: if every term is at most `η · 2ε`
in absolute value, the sum over `A` is at most `η · μ_ε(A)`. -/
theorem abs_sum_le_mu {ε : K} (A : Finset ℤ) (a : ℤ → K) (η : K)
    (h : ∀ k ∈ A, |a k| ≤ η * (2 * ε)) : |∑ k ∈ A, a k| ≤ η * QE.mu ε A := by
  calc |∑ k ∈ A, a k| ≤ ∑ k ∈ A, |a k| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _k ∈ A, η * (2 * ε) := Finset.sum_le_sum h
    _ = η * QE.mu ε A := by rw [Finset.sum_const, nsmul_eq_mul]; unfold QE.mu; ring

/-- Lattice oscillation of a Lipschitz function: neighbouring values differ by at
most `L · 2ε`. -/
theorem lipschitz_step {ε L : K} (f : K → K) (hf : ∀ x y, |f x - f y| ≤ L * |x - y|)
    (hε : 0 < ε) (x : K) : |f (x + 2 * ε) - f x| ≤ L * (2 * ε) := by
  have := hf (x + 2 * ε) x
  rwa [add_sub_cancel_left, abs_of_pos (by linarith : (0 : K) < 2 * ε)] at this

/-- Consecutive points of the granular graph `{(x, f x)}` of an `L`-Lipschitz
function are at squared distance at most `(2ε)² (1 + L²)`. -/
theorem lipschitz_graph_step {ε L : K} (f : K → K) (hf : ∀ x y, |f x - f y| ≤ L * |x - y|)
    (hε : 0 < ε) (x : K) :
    (2 * ε) ^ 2 + (f (x + 2 * ε) - f x) ^ 2 ≤ (2 * ε) ^ 2 * (1 + L ^ 2) := by
  have h := lipschitz_step f hf hε x
  have h2 : (f (x + 2 * ε) - f x) ^ 2 ≤ (L * (2 * ε)) ^ 2 := by
    rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) h 2
  nlinarith

/-- Cardinality of the hyperfinite line (`ax:QE3`): with horizon `Ω = 2εM`, the
lattice `{2εk : |k| ≤ M}` has `2M + 1 = Ω/ε + 1` points. -/
theorem card_lattice {ε : K} (hε : 0 < ε) (M : ℕ) :
    (((Finset.Icc (-(M : ℤ)) M).card : ℕ) : K) = QE.centre ε M / ε + 1 := by
  rw [Int.card_Icc]
  have : ((M : ℤ) + 1 - -(M : ℤ)).toNat = 2 * M + 1 := by omega
  rw [this]; unfold QE.centre; push_cast
  field_simp

/-- **Zeno's paradox of extension, resolved.**  If `2εN = 1`, the unit interval
`[0,1]` contains exactly `N + 1` points, each of length `2ε`, and their total
granular length is `1 + 2ε` (not `0`, not undefined). -/
theorem zeno_unit_interval {ε : K} (N : ℕ) (hN : 2 * ε * N = 1) :
    QE.mu ε (Finset.Icc (0 : ℤ) N) = 1 + 2 * ε ∧ (Finset.Icc (0 : ℤ) N).card = N + 1 := by
  have hc : (Finset.Icc (0 : ℤ) N).card = N + 1 := by
    rw [Int.card_Icc]; omega
  refine ⟨?_, hc⟩
  unfold QE.mu; rw [hc]; push_cast; linarith

variable [FloorRing K]

/-- Snapping (rounding to the nearest centre, ties upward):
`⌊x⌉_ε = 2ε ⌊x/(2ε) + 1/2⌋`. -/
noncomputable def snap (ε x : K) : K := 2 * ε * ⌊x / (2 * ε) + 1 / 2⌋

/-- The lattice index of the snapped point. -/
noncomputable def snapIdx (ε x : K) : ℤ := ⌊x / (2 * ε) + 1 / 2⌋

theorem snap_eq_centre (ε x : K) : snap ε x = QE.centre ε (snapIdx ε x) := rfl

/-- Every point lies in the Voronoi cell of its snap: `-ε ≤ x - ⌊x⌉_ε < ε`. -/
theorem snap_mem_cell {ε : K} (hε : 0 < ε) (x : K) :
    -ε ≤ x - snap ε x ∧ x - snap ε x < ε := by
  unfold snap
  have hpos : (0 : K) < 2 * ε := by linarith
  set t := x / (2 * ε) + 1 / 2 with ht
  have hx : x = 2 * ε * (t - 1 / 2) := by rw [ht]; field_simp; ring
  have f1 := Int.floor_le t
  have f2 := Int.lt_floor_add_one t
  constructor
  · rw [hx]; nlinarith
  · rw [hx]; nlinarith

/-- **Snapping error** (`thm:hyper-snap-error`): `|x - ⌊x⌉_ε| ≤ ε`. -/
theorem abs_sub_snap_le {ε : K} (hε : 0 < ε) (x : K) : |x - snap ε x| ≤ ε := by
  obtain ⟨h1, h2⟩ := snap_mem_cell hε x
  exact abs_le.mpr ⟨h1, h2.le⟩

/-- The lattice is `ε`-dense: every point is within `ε` of a centre. -/
theorem exists_centre_near {ε : K} (hε : 0 < ε) (x : K) :
    ∃ k : ℤ, |x - QE.centre ε k| ≤ ε :=
  ⟨snapIdx ε x, abs_sub_snap_le hε x⟩

/-- Characterisation of the fibres of `snap`: they are exactly the cells. -/
theorem snap_eq_iff {ε : K} (hε : 0 < ε) (x : K) (k : ℤ) :
    snap ε x = QE.centre ε k ↔ QE.centre ε k - ε ≤ x ∧ x < QE.centre ε k + ε := by
  constructor
  · intro h
    have := snap_mem_cell hε x
    rw [h] at this
    constructor <;> linarith [this.1, this.2]
  · intro h
    have hc := snap_mem_cell hε x
    have hc' : QE.centre ε (snapIdx ε x) - ε ≤ x ∧ x < QE.centre ε (snapIdx ε x) + ε := by
      rw [← snap_eq_centre]; constructor <;> linarith [hc.1, hc.2]
    rw [snap_eq_centre, cell_unique hε hc' h]

/-- Sub-granular numbers snap to `0`: if `-ε ≤ x < ε` then `⌊x⌉_ε = 0`. -/
theorem snap_eq_zero {ε : K} (hε : 0 < ε) {x : K} (h1 : -ε ≤ x) (h2 : x < ε) :
    snap ε x = 0 := by
  have := (snap_eq_iff hε x 0).mpr (by simp [QE.centre]; exact ⟨h1, h2⟩)
  simpa [QE.centre] using this

/-- Lattice centres are fixed by `snap`. -/
theorem snap_centre {ε : K} (hε : 0 < ε) (k : ℤ) : snap ε (QE.centre ε k) = QE.centre ε k :=
  (snap_eq_iff hε _ k).mpr ⟨by linarith, by linarith⟩

/-- `snap` is idempotent. -/
theorem snap_snap {ε : K} (hε : 0 < ε) (x : K) : snap ε (snap ε x) = snap ε x := by
  have := snap_centre hε (snapIdx ε x)
  rwa [← snap_eq_centre] at this

/-- `snap` is monotone. -/
theorem snap_mono {ε : K} (hε : 0 < ε) : Monotone (snap ε) := by
  intro x y hxy
  unfold snap
  have hpos : (0 : K) < 2 * ε := by linarith
  have : ⌊x / (2 * ε) + 1 / 2⌋ ≤ ⌊y / (2 * ε) + 1 / 2⌋ := by
    apply Int.floor_mono
    have := div_le_div_of_nonneg_right hxy hpos.le
    linarith
  have : ((⌊x / (2 * ε) + 1 / 2⌋ : ℤ) : K) ≤ ⌊y / (2 * ε) + 1 / 2⌋ := by exact_mod_cast this
  exact mul_le_mul_of_nonneg_left this hpos.le

/-- `snap` commutes with lattice translations. -/
theorem snap_add_centre {ε : K} (hε : 0 < ε) (x : K) (k : ℤ) :
    snap ε (x + QE.centre ε k) = snap ε x + QE.centre ε k := by
  unfold snap QE.centre
  have hne : (2 * ε) ≠ 0 := by positivity
  have : (x + 2 * ε * k) / (2 * ε) + 1 / 2 = (x / (2 * ε) + 1 / 2) + (k : K) := by
    field_simp; ring
  rw [this, Int.floor_add_intCast]; push_cast; ring

/-- Snapping moves points by less than one lattice spacing: `|⌊x⌉ - ⌊y⌉| < |x - y| + 2ε`. -/
theorem abs_snap_sub_snap_lt {ε : K} (hε : 0 < ε) (x y : K) :
    |snap ε x - snap ε y| < |x - y| + 2 * ε := by
  have hx := snap_mem_cell hε x
  have hy := snap_mem_cell hε y
  have : |snap ε x - snap ε y| < 2 * ε + |x - y| := by
    rw [abs_lt]
    constructor
    · have := neg_abs_le (x - y); linarith [hx.1, hx.2, hy.1, hy.2]
    · have := le_abs_self (x - y); linarith [hx.1, hx.2, hy.1, hy.2]
  linarith

/-- Successor structure: snapping commutes with the step `x ↦ x + 2ε`. -/
theorem snap_succ {ε : K} (hε : 0 < ε) (x : K) :
    snap ε (x + 2 * ε) = snap ε x + 2 * ε := by
  have := snap_add_centre hε x 1
  simpa [QE.centre] using this

/-- A hyperfinite binary expansion `0.11…1` (`K` ones) equals `1 - 2^{-K}`:
it is a lattice point distinct from `1`, one spacing below it. -/
theorem sum_ones_dyadic (h2 : (2 : K') ≠ 0) (K : ℕ) :
    ∑ i ∈ Finset.range K, ((1 : K') / 2) ^ (i + 1) = 1 - (1 / 2) ^ K := by
  induction K with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_range_succ, ih]
    have h : ((1 : K') / 2) ^ (m + 1) * 2 = (1 / 2) ^ m := by
      rw [pow_succ, mul_assoc, one_div, inv_mul_cancel₀ h2, mul_one]
    linear_combination h

/-- Snapping is additive up to one carry: `⌊x+y⌉ = ⌊x⌉ + ⌊y⌉ + 2εd` with `d ∈ {-1,0,1}`. -/
theorem snap_add_carry {ε : K} (hε : 0 < ε) (x y : K) :
    ∃ d : ℤ, |d| ≤ 1 ∧ snap ε (x + y) = snap ε x + snap ε y + 2 * ε * d := by
  refine ⟨snapIdx ε (x + y) - snapIdx ε x - snapIdx ε y, ?_, ?_⟩
  · have h1 := snap_mem_cell hε (x + y)
    have h2 := snap_mem_cell hε x
    have h3 := snap_mem_cell hε y
    simp only [snap_eq_centre, QE.centre] at h1 h2 h3
    set d : ℤ := snapIdx ε (x + y) - snapIdx ε x - snapIdx ε y with hd
    have hdK : (d : K) = snapIdx ε (x + y) - snapIdx ε x - snapIdx ε y := by
      rw [hd]; push_cast; ring
    have u : 2 * ε * (d : K) < 2 * ε * 2 := by rw [hdK]; nlinarith
    have l : 2 * ε * (-2) < 2 * ε * (d : K) := by rw [hdK]; nlinarith
    have hpos : (0 : K) < 2 * ε := by linarith
    have u' : ((d : ℤ) : K) < ((2 : ℤ) : K) := by
      push_cast; exact lt_of_mul_lt_mul_left u hpos.le
    have l' : ((-2 : ℤ) : K) < ((d : ℤ) : K) := by
      push_cast; exact lt_of_mul_lt_mul_left l hpos.le
    have := Int.cast_lt.mp u'
    have := Int.cast_lt.mp l'
    rw [abs_le]; constructor <;> omega
  · simp only [snap_eq_centre, QE.centre]; push_cast; ring

/-- Counting lattice centres in a closed interval `[a,b]` (`a ≤ b` arbitrary,
not necessarily lattice points): the index set is `⌈a/2ε⌉ … ⌊b/2ε⌋` and
`|2ε · #(centres in [a,b]) - (b - a)| ≤ 2ε`. -/
theorem count_interval {ε : K} (hε : 0 < ε) {a b : K} (hab : a ≤ b) :
    (∀ k : ℤ, k ∈ Finset.Icc ⌈a / (2 * ε)⌉ ⌊b / (2 * ε)⌋ ↔
        a ≤ QE.centre ε k ∧ QE.centre ε k ≤ b) ∧
    |2 * ε * ((Finset.Icc ⌈a / (2 * ε)⌉ ⌊b / (2 * ε)⌋).card : K) - (b - a)| ≤ 2 * ε := by
  have hpos : (0 : K) < 2 * ε := by linarith
  constructor
  · intro k
    rw [Finset.mem_Icc, Int.ceil_le, Int.le_floor, div_le_iff₀ hpos, le_div_iff₀ hpos]
    unfold QE.centre
    constructor <;> rintro ⟨h1, h2⟩ <;> exact ⟨by linarith, by linarith⟩
  · set a' := a / (2 * ε)
    set b' := b / (2 * ε)
    have ha : a = 2 * ε * a' := by simp only [a']; field_simp
    have hb : b = 2 * ε * b' := by simp only [b']; field_simp
    have hab' : a' ≤ b' := div_le_div_of_nonneg_right hab hpos.le
    have c1 := Int.le_ceil a'
    have c2 := Int.ceil_lt_add_one a'
    have f1 := Int.floor_le b'
    have f2 := Int.lt_floor_add_one b'
    have hle : ⌈a'⌉ ≤ ⌊b'⌋ + 1 := by
      have : ((⌈a'⌉ : ℤ) : K) < ((⌊b'⌋ + 2 : ℤ) : K) := by push_cast; linarith
      have := Int.cast_lt.mp this; omega
    rw [Int.card_Icc]
    have hc : (((⌊b'⌋ + 1 - ⌈a'⌉).toNat : ℕ) : K) = ((⌊b'⌋ + 1 - ⌈a'⌉ : ℤ) : K) := by
      rw [← Int.cast_natCast, Int.toNat_of_nonneg (by omega)]
    rw [hc, abs_le, ha, hb]; push_cast
    constructor <;> nlinarith

/-- `n`-dimensional snapping, coordinatewise. -/
noncomputable def snapN {n : ℕ} (ε : K) (x : Fin n → K) : Fin n → K := fun i => snap ε (x i)

/-- Coordinatewise (sup-norm) error bound in `n` dimensions. -/
theorem snapN_sup_le {n : ℕ} {ε : K} (hε : 0 < ε) (x : Fin n → K) (i : Fin n) :
    |x i - snapN ε x i| ≤ ε := abs_sub_snap_le hε (x i)

/-- Euclidean error bound: `‖x - ⌊x⌉‖² ≤ n ε²`, i.e. `‖x - ⌊x⌉‖ ≤ √n ε`. -/
theorem snapN_sq_le {n : ℕ} {ε : K} (hε : 0 < ε) (x : Fin n → K) :
    ∑ i, (x i - snapN ε x i) ^ 2 ≤ n * ε ^ 2 := by
  have h : ∀ i ∈ (Finset.univ : Finset (Fin n)), (x i - snapN ε x i) ^ 2 ≤ ε ^ 2 := by
    intro i _
    have := snapN_sup_le hε x i
    rw [← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) this 2
  calc ∑ i, (x i - snapN ε x i) ^ 2 ≤ ∑ _i : Fin n, ε ^ 2 := Finset.sum_le_sum h
    _ = n * ε ^ 2 := by simp

/-- The Heaviside step `H(x) = 1` for `x ≥ 0`, `0` otherwise. -/
def heaviside (x : K) : K := if 0 ≤ x then 1 else 0

/-- The point-sphere at the jump: the average of `H` over the two poles `±ε` of the
point `0` is exactly `1/2`. -/
theorem heaviside_pole_average {ε : K} (hε : 0 < ε) :
    (heaviside ε + heaviside (-ε)) / 2 = 1 / 2 := by
  unfold heaviside
  rw [ite_eq_left hε.le, ite_eq_right (by linarith)]; ring

/-- The central granular derivative of `H` at `0` is `1/(2ε)`: one over the
point diameter. -/
theorem Dc_heaviside_zero {ε : K} (hε : 0 < ε) : QE.Dc ε heaviside 0 = 1 / (2 * ε) := by
  unfold QE.Dc heaviside
  rw [zero_add, zero_sub, ite_eq_left hε.le, ite_eq_right (by linarith)]; ring

/-- Away from the jump the central derivative of `H` vanishes at every centre. -/
theorem Dc_heaviside_centre {ε : K} (hε : 0 < ε) {k : ℤ} (hk : k ≠ 0) :
    QE.Dc ε heaviside (QE.centre ε k) = 0 := by
  unfold QE.Dc heaviside QE.centre
  rcases lt_or_gt_of_ne hk with h | h
  · have h' : (k : K) ≤ -1 := by exact_mod_cast Int.le_sub_one_of_lt h
    rw [ite_eq_right (by nlinarith), ite_eq_right (by nlinarith)]; ring
  · have h' : (1 : K) ≤ k := by exact_mod_cast h
    rw [ite_eq_left (by nlinarith), ite_eq_left (by nlinarith)]; ring

/-- Hence the granular delta `D_c H` has total mass exactly `1` on any window of
centres containing `0`. -/
theorem sum_Dc_heaviside {ε : K} (hε : 0 < ε) (A : Finset ℤ) (h0 : 0 ∈ A) :
    ∑ k ∈ A, QE.Dc ε heaviside (QE.centre ε k) * (2 * ε) = 1 := by
  rw [Finset.sum_eq_single_of_mem 0 h0]
  · have : QE.centre ε 0 = 0 := by simp [QE.centre]
    rw [this, Dc_heaviside_zero hε]; field_simp
  · intro k _ hk; rw [Dc_heaviside_centre hε hk, zero_mul]

end Snap

section Third

/-- Snapping `1/3` to the dyadic lattice of spacing `2ε = 4^{-n}` (even exponent):
the residual is `+2ε/3`. -/
theorem snap_third_even (n : ℕ) (k : ℤ) (hk : 3 * k + 1 = 4 ^ n) :
    snap (1 / (2 * 4 ^ n) : ℝ) (1 / 3) = QE.centre (1 / (2 * 4 ^ n) : ℝ) k ∧
    (1 : ℝ) / 3 - QE.centre (1 / (2 * 4 ^ n) : ℝ) k = 2 * (1 / (2 * 4 ^ n)) / 3 := by
  have hA : (0 : ℝ) < 4 ^ n := by positivity
  have hk' : (k : ℝ) = ((4 : ℝ) ^ n - 1) / 3 := by
    have : ((3 * k + 1 : ℤ) : ℝ) = ((4 ^ n : ℤ) : ℝ) := by rw [hk]
    push_cast at this; linarith
  have hε : (0 : ℝ) < 1 / (2 * 4 ^ n) := by positivity
  have hc : QE.centre (1 / (2 * 4 ^ n) : ℝ) k = 1 / 3 - 1 / (3 * 4 ^ n) := by
    unfold QE.centre; rw [hk']; field_simp
  refine ⟨(snap_eq_iff hε _ k).mpr ?_, ?_⟩
  · rw [hc]
    constructor
    · have : (0 : ℝ) ≤ 1 / (3 * 4 ^ n) + 1 / (2 * 4 ^ n) := by positivity
      linarith
    · have : 1 / (3 * (4 : ℝ) ^ n) < 1 / (2 * 4 ^ n) := by
        apply one_div_lt_one_div_of_lt (by positivity); linarith
      linarith
  · rw [hc]; field_simp; ring

/-- Odd exponent, spacing `2ε = 2^{-(2n+1)}`: the residual is `-2ε/3`.  The sign of
the sub-granular residual records the parity of the exponent. -/
theorem snap_third_odd (n : ℕ) (k : ℤ) (hk : 3 * k = 2 * 4 ^ n + 1) :
    snap (1 / (4 * 4 ^ n) : ℝ) (1 / 3) = QE.centre (1 / (4 * 4 ^ n) : ℝ) k ∧
    (1 : ℝ) / 3 - QE.centre (1 / (4 * 4 ^ n) : ℝ) k = -(2 * (1 / (4 * 4 ^ n)) / 3) := by
  have hA : (0 : ℝ) < 4 ^ n := by positivity
  have hk' : (k : ℝ) = (2 * (4 : ℝ) ^ n + 1) / 3 := by
    have : ((3 * k : ℤ) : ℝ) = ((2 * 4 ^ n + 1 : ℤ) : ℝ) := by rw [hk]
    push_cast at this; linarith
  have hε : (0 : ℝ) < 1 / (4 * 4 ^ n) := by positivity
  have hc : QE.centre (1 / (4 * 4 ^ n) : ℝ) k = 1 / 3 + 1 / (6 * 4 ^ n) := by
    unfold QE.centre; rw [hk']; field_simp; ring
  refine ⟨(snap_eq_iff hε _ k).mpr ?_, ?_⟩
  · rw [hc]
    constructor
    · have : 1 / (6 * (4 : ℝ) ^ n) ≤ 1 / (4 * 4 ^ n) := by
        apply one_div_le_one_div_of_le (by positivity); linarith
      linarith
    · have : (0 : ℝ) < 1 / (6 * 4 ^ n) + 1 / (4 * 4 ^ n) := by positivity
      linarith
  · rw [hc]; field_simp; ring

end Third

/-! ## Hyperreals -/

open Hyperreal

/-- `x` is infinitesimal. -/
def Infinitesimal (x : ℝ*) : Prop := 0 < ArchimedeanClass.mk x

/-- `x` is finite (limited). -/
def IsFinite (x : ℝ*) : Prop := 0 ≤ ArchimedeanClass.mk x

/-- Infinitely close. -/
def Icl (x y : ℝ*) : Prop := Infinitesimal (x - y)

/-- The monad (halo) of `x`. -/
def monad (x : ℝ*) : Set ℝ* := {y | Icl y x}

/-- Mathlib's `ε = ω⁻¹` is a positive infinitesimal. -/
theorem epsilon_infinitesimal : Infinitesimal Hyperreal.epsilon :=
  archimedeanClassMk_epsilon_pos

/-- A positive infinitesimal is below every positive real. -/
theorem epsilon_lt_real {r : ℝ} (hr : 0 < r) : Hyperreal.epsilon < (r : ℝ*) :=
  epsilon_lt_of_pos hr

/-- Failure of the Archimedean property: `ω` exceeds every natural number. -/
theorem nat_lt_omega (n : ℕ) : (n : ℝ*) < Hyperreal.omega := by
  have := coe_lt_omega (n : ℝ)
  rwa [show ((n : ℝ) : ℝ*) = (n : ℝ*) from rfl] at this

/-- Equivalently, `n · ε < 1` for every natural number `n`. -/
theorem nat_mul_epsilon_lt_one (n : ℕ) : (n : ℝ*) * Hyperreal.epsilon < 1 := by
  have h := nat_lt_omega n
  have hε := epsilon_pos
  calc (n : ℝ*) * Hyperreal.epsilon < Hyperreal.omega * Hyperreal.epsilon :=
        mul_lt_mul_of_pos_right h hε
    _ = 1 := by rw [mul_comm]; exact epsilon_mul_omega

/-- If `|x| ≤ |y|` and `y` is infinitesimal, so is `x`. -/
theorem Infinitesimal.of_abs_le {x y : ℝ*} (hy : Infinitesimal y) (h : |x| ≤ |y|) :
    Infinitesimal x :=
  lt_of_lt_of_le hy (ArchimedeanClass.mk_le_mk_of_abs h)

/-- Sums of infinitesimals are infinitesimal. -/
theorem Infinitesimal.add {x y : ℝ*} (hx : Infinitesimal x) (hy : Infinitesimal y) :
    Infinitesimal (x + y) :=
  lt_of_lt_of_le (lt_min hx hy) (ArchimedeanClass.min_le_mk_add x y)

/-- Finite times infinitesimal is infinitesimal. -/
theorem Infinitesimal.mul_finite {x y : ℝ*} (hx : Infinitesimal x) (hy : IsFinite y) :
    Infinitesimal (x * y) := by
  unfold Infinitesimal IsFinite at *
  rw [ArchimedeanClass.mk_mul]
  exact lt_of_lt_of_le hx (le_add_of_nonneg_right hy)

/-- Standard integers are finite. -/
theorem isFinite_intCast (k : ℤ) : IsFinite (k : ℝ*) := mk_intCast_nonneg k

/-- `2εk` is infinitesimal for every standard integer `k`: the standard-indexed
centres all lie in the monad of `0`. -/
theorem infinitesimal_centre {e : ℝ*} (he : Infinitesimal e) (k : ℤ) :
    Infinitesimal (QE.centre e k) := by
  unfold QE.centre
  have h2 : Infinitesimal (2 * e) := by
    have : (2 : ℝ*) * e = e + e := by ring
    rw [this]; exact he.add he
  exact h2.mul_finite (isFinite_intCast k)

/-- Orders of magnitude: `ε^(k+1) < r ε^k` for every standard `r > 0`, so each
power of `ε` is ultrasmall relative to the previous one. -/
theorem epsilon_pow_succ_lt (k : ℕ) {r : ℝ} (hr : 0 < r) :
    Hyperreal.epsilon ^ (k + 1) < (r : ℝ*) * Hyperreal.epsilon ^ k := by
  rw [pow_succ, mul_comm (r : ℝ*)]
  exact mul_lt_mul_of_pos_left (epsilon_lt_real hr) (pow_pos epsilon_pos k)

/-- The Archimedean class (valuation) of `ε^k` is `k` times that of `ε`. -/
theorem mk_epsilon_pow (k : ℕ) :
    ArchimedeanClass.mk (Hyperreal.epsilon ^ k) = k • ArchimedeanClass.mk Hyperreal.epsilon :=
  ArchimedeanClass.mk_pow k _

/-- `ε²` is ultrasmall relative to `ε`: `ε² < r ε` for every positive real `r`. -/
theorem epsilon_sq_lt (r : ℝ) (hr : 0 < r) :
    Hyperreal.epsilon ^ 2 < (r : ℝ*) * Hyperreal.epsilon := by
  rw [sq]
  exact mul_lt_mul_of_pos_right (epsilon_lt_real hr) epsilon_pos

/-- Distinct reals have disjoint monads. -/
theorem monad_disjoint {r s : ℝ} (h : r ≠ s) :
    Disjoint (monad (r : ℝ*)) (monad (s : ℝ*)) := by
  rw [Set.disjoint_left]
  intro y hr hs
  have hrs : Infinitesimal ((r : ℝ*) - s) := by
    have e1 : Infinitesimal ((r : ℝ*) - y) := by
      unfold Infinitesimal; rw [ArchimedeanClass.mk_sub_comm]; exact hr
    have := e1.add hs
    simpa using this
  have : ((r : ℝ*) - s) = ((r - s : ℝ) : ℝ*) := by rw [coe_sub]
  rw [Infinitesimal, this, archimedeanClassMk_coe (sub_ne_zero.mpr h)] at hrs
  exact lt_irrefl _ hrs

/-- Every finite hyperreal lies in the monad of its standard part. -/
theorem mem_monad_stdPart {x : ℝ*} (hx : IsFinite x) :
    x ∈ monad ((ArchimedeanClass.stdPart x : ℝ) : ℝ*) :=
  mk_sub_stdPart_pos Hyperreal.coeRingHom hx

/-- Infinitely close finite hyperreals have the same standard part. -/
theorem stdPart_eq_of_icl {x y : ℝ*} (h : Icl y x) :
    ArchimedeanClass.stdPart y = ArchimedeanClass.stdPart x := by
  have : y = x + (y - x) := by ring
  rw [this, stdPart_add_eq_left h]

/-- The standard part is additive on finite hyperreals. -/
theorem st_add {x y : ℝ*} (hx : IsFinite x) (hy : IsFinite y) :
    ArchimedeanClass.stdPart (x + y) = ArchimedeanClass.stdPart x + ArchimedeanClass.stdPart y :=
  stdPart_add hx hy

/-- The standard part is multiplicative on finite hyperreals. -/
theorem st_mul {x y : ℝ*} (hx : IsFinite x) (hy : IsFinite y) :
    ArchimedeanClass.stdPart (x * y) = ArchimedeanClass.stdPart x * ArchimedeanClass.stdPart y :=
  stdPart_mul hx hy

/-- The standard part fixes standard reals. -/
theorem st_real (r : ℝ) : ArchimedeanClass.stdPart (r : ℝ*) = r := stdPart_coe r

/-- Continuity as commutation with the standard part: if `f` is continuous at
`r` and `x = [xₙ]` with `xₙ → r` along the ultrafilter, then
`st (*f x) = f r = f (st x)`. -/
theorem st_map_of_continuousAt {x : ℝ*} {r : ℝ} {f : ℝ → ℝ} (hf : ContinuousAt f r)
    (hxr : x.Tendsto (nhds r)) :
    ArchimedeanClass.stdPart (x.map f) = f r ∧ ArchimedeanClass.stdPart x = r :=
  ⟨stdPart_of_tendsto (Hyperreal.stdPart_map hf hxr), stdPart_of_tendsto hxr⟩

/-- A finite hyperreal converges (along the ultrafilter) to its standard part. -/
theorem tendsto_stdPart {x : ℝ*} (hx : IsFinite x) :
    x.Tendsto (nhds (ArchimedeanClass.stdPart x)) :=
  tendsto_iff_forall.mpr
    ⟨fun _s hs => (lt_of_lt_stdPart Hyperreal.coeRingHom hx hs).le,
     fun _s hs => (lt_of_stdPart_lt Hyperreal.coeRingHom hx hs).le⟩

theorem icl_of_tendsto {x : ℝ*} {r : ℝ} (h : x.Tendsto (nhds r)) : Icl x r := by
  have hf : IsFinite x := archimedeanClassMk_nonneg_of_tendsto h
  have := mem_monad_stdPart hf
  rwa [stdPart_of_tendsto h] at this

theorem Icl.symm {x y : ℝ*} (h : Icl x y) : Icl y x := by
  unfold Icl Infinitesimal at *; rwa [ArchimedeanClass.mk_sub_comm]

theorem Icl.trans {x y z : ℝ*} (h1 : Icl x y) (h2 : Icl y z) : Icl x z := by
  have := Infinitesimal.add h1 h2
  unfold Icl; simpa using this

/-- **S-continuity** (Robinson): the natural extension of a continuous `f : ℝ → ℝ`
maps infinitely close finite hyperreals to infinitely close values. -/
theorem s_continuous {f : ℝ → ℝ} (hf : Continuous f) {x y : ℝ*} (hx : IsFinite x)
    (hxy : Icl y x) : Icl (y.map f) (x.map f) := by
  have hy : IsFinite y := by
    have : y = x + (y - x) := by ring
    unfold IsFinite
    rw [this]
    exact le_trans (le_min hx (le_of_lt hxy)) (ArchimedeanClass.min_le_mk_add _ _)
  have ex := tendsto_stdPart hx
  have ey := tendsto_stdPart hy
  rw [stdPart_eq_of_icl hxy] at ey
  have a := icl_of_tendsto (Hyperreal.stdPart_map hf.continuousAt ex)
  have b := icl_of_tendsto (Hyperreal.stdPart_map hf.continuousAt ey)
  exact b.trans a.symm

/-! ### Hyperintegers and the factorial and dyadic lattices -/

/-- A hyperinteger: the class of an integer-valued sequence. -/
def IsHyperint (x : ℝ*) : Prop := ∃ f : ℕ → ℤ, x = ofSeq (fun n => (f n : ℝ))

theorem isHyperint_intCast (k : ℤ) : IsHyperint (k : ℝ*) :=
  ⟨fun _ => k, rfl⟩

theorem IsHyperint.add {x y : ℝ*} (hx : IsHyperint x) (hy : IsHyperint y) :
    IsHyperint (x + y) := by
  obtain ⟨f, rfl⟩ := hx; obtain ⟨g, rfl⟩ := hy
  exact ⟨f + g, by simp [ofSeq]; rfl⟩

theorem IsHyperint.mul {x y : ℝ*} (hx : IsHyperint x) (hy : IsHyperint y) :
    IsHyperint (x * y) := by
  obtain ⟨f, rfl⟩ := hx; obtain ⟨g, rfl⟩ := hy
  exact ⟨f * g, by simp [ofSeq]; rfl⟩

theorem IsHyperint.neg {x : ℝ*} (hx : IsHyperint x) : IsHyperint (-x) := by
  obtain ⟨f, rfl⟩ := hx
  exact ⟨-f, by simp [ofSeq]; rfl⟩

theorem ofSeq_mul_ofSeq (f g : ℕ → ℝ) : ofSeq f * ofSeq g = ofSeq (fun n => f n * g n) := rfl

theorem ofSeq_eq_of_eventually {f g : ℕ → ℝ}
    (h : ∀ᶠ n in (hyperfilter ℕ : Filter ℕ), f n = g n) : ofSeq f = ofSeq g :=
  Germ.coe_eq.mpr h

/-- The factorial hypernatural `N = M!` with `M = [n ↦ n]`. -/
noncomputable def factN : ℝ* := ofSeq (fun n => (n.factorial : ℝ))

theorem eventually_hyper {p : ℕ → Prop} (m : ℕ) (h : ∀ n ≥ m, p n) :
    ∀ᶠ n in (hyperfilter ℕ : Filter ℕ), p n := by
  apply Filter.Eventually.filter_mono hyperfilter_le_cofinite
  rw [Nat.cofinite_eq_atTop, Filter.eventually_atTop]
  exact ⟨m, h⟩

theorem isHyperint_factN : IsHyperint factN :=
  ⟨fun n => (n.factorial : ℤ), by simp [factN]⟩

/-- `N = M!` is infinite. -/
theorem real_lt_factN (r : ℝ) : (r : ℝ*) < factN := by
  obtain ⟨m, hm⟩ := exists_nat_gt r
  apply ofSeq_lt_ofSeq.mpr
  apply eventually_hyper m
  intro n hn
  have h1 : (m : ℝ) ≤ n := by exact_mod_cast hn
  have h2 : (n : ℝ) ≤ n.factorial := by exact_mod_cast Nat.self_le_factorial n
  show r < n.factorial
  linarith

theorem factN_pos : 0 < factN := by
  have := real_lt_factN 0; simpa using this

/-- **Factorial lattice** (`thm:hyper-factorial-lattice`): for every standard
rational `q`, `q · N` is a hyperinteger, hence `q = z / N` lies on the lattice
`(1/N)·*ℤ` of spacing `2ε = 1/N`. -/
theorem rat_mul_factN_isHyperint (q : ℚ) : IsHyperint (((q : ℝ) : ℝ*) * factN) := by
  refine ⟨fun n => if q.den ∣ n.factorial then q.num * ((n.factorial / q.den : ℕ) : ℤ) else 0, ?_⟩
  have hq : ((q : ℝ) : ℝ*) = ofSeq (fun _ => (q : ℝ)) := rfl
  rw [hq, factN, ofSeq_mul_ofSeq]
  apply ofSeq_eq_of_eventually
  apply eventually_hyper q.den
  intro n hn
  have hd : q.den ∣ n.factorial := Nat.dvd_factorial q.den_pos hn
  simp only [hd, ite_true]
  have hden : (q.den : ℝ) ≠ 0 := by exact_mod_cast q.den_nz
  rw [Int.cast_mul, Int.cast_natCast, Nat.cast_div hd hden, Rat.cast_def]
  field_simp

theorem rat_on_factorial_lattice (q : ℚ) :
    ∃ z : ℝ*, IsHyperint z ∧ ((q : ℝ) : ℝ*) = z / factN :=
  ⟨_, rat_mul_factN_isHyperint q, by
    rw [mul_div_assoc, div_self factN_pos.ne', mul_one]⟩

/-- The dyadic hypernatural `2^K` with `K = [n ↦ n]`. -/
noncomputable def dyadN : ℝ* := ofSeq (fun n => (2 : ℝ) ^ n)

/-- Every standard dyadic rational `m / 2^j` lies on the dyadic lattice
`2^{-K}·*ℤ`. -/
theorem dyadic_on_dyadic_lattice (m : ℤ) (j : ℕ) :
    IsHyperint ((((m : ℝ) / 2 ^ j : ℝ) : ℝ*) * dyadN) := by
  refine ⟨fun n => m * 2 ^ (n - j), ?_⟩
  have hq : ((((m : ℝ) / 2 ^ j : ℝ)) : ℝ*) = ofSeq (fun _ => ((m : ℝ) / 2 ^ j)) := rfl
  rw [hq, dyadN, ofSeq_mul_ofSeq]
  apply ofSeq_eq_of_eventually
  apply eventually_hyper j
  intro n hn
  push_cast
  have : (2 : ℝ) ^ n = 2 ^ (n - j) * 2 ^ j := by
    rw [← pow_add, Nat.sub_add_cancel hn]
  rw [this]; field_simp

/-- No standard irrational lies on the factorial lattice: `r · N` is not a
hyperinteger.  (All lattice points `z/N` are hyperrational.) -/
theorem irrational_not_on_factorial_lattice {r : ℝ} (hr : Irrational r) :
    ¬ IsHyperint ((r : ℝ*) * factN) := by
  rintro ⟨f, hf⟩
  have hq : ((r : ℝ) : ℝ*) = ofSeq (fun _ => r) := rfl
  rw [hq, factN, ofSeq_mul_ofSeq] at hf
  have hev : ∀ᶠ n in (hyperfilter ℕ : Filter ℕ), r * (n.factorial : ℝ) = f n :=
    Germ.coe_eq.mp hf
  obtain ⟨n, hn⟩ := hev.exists
  exact (hr.mul_natCast (Nat.factorial_ne_zero n)).ne_int (f n) hn

/-- `1/3` is not on the dyadic lattice `2^{-K}·*ℤ`: the lattice choice matters. -/
theorem third_not_on_dyadic_lattice : ¬ IsHyperint ((((1 : ℝ) / 3 : ℝ) : ℝ*) * dyadN) := by
  rintro ⟨f, hf⟩
  have hq : ((((1 : ℝ) / 3 : ℝ)) : ℝ*) = ofSeq (fun _ => (1 : ℝ) / 3) := rfl
  rw [hq, dyadN, ofSeq_mul_ofSeq] at hf
  have hev : ∀ᶠ n in (hyperfilter ℕ : Filter ℕ), (1 : ℝ) / 3 * 2 ^ n = f n :=
    Germ.coe_eq.mp hf
  obtain ⟨n, hn⟩ := hev.exists
  have h1 : (2 : ℝ) ^ n = 3 * f n := by linarith
  have h2 : (2 : ℤ) ^ n = 3 * f n := by exact_mod_cast h1
  have h3 : (3 : ℤ) ∣ 2 ^ n := ⟨f n, h2⟩
  have h4 : (3 : ℤ) ∣ 2 := Int.prime_three.dvd_of_dvd_pow h3
  omega

/-- A hyperrational: the class of a rational-valued sequence. -/
def IsHyperrat (x : ℝ*) : Prop := ∃ f : ℕ → ℚ, x = ofSeq (fun n => (f n : ℝ))

/-- Every lattice point `z / N` (with `z, N` hyperintegers) is hyperrational. -/
theorem hyperint_div_isHyperrat {z N : ℝ*} (hz : IsHyperint z) (hN : IsHyperint N) :
    IsHyperrat (z / N) := by
  obtain ⟨f, rfl⟩ := hz; obtain ⟨g, rfl⟩ := hN
  refine ⟨fun n => (f n : ℚ) / (g n : ℚ), ?_⟩
  show ofSeq (fun n => (f n : ℝ) / (g n : ℝ)) = _
  congr 1; funext n; push_cast; rfl

/-- An irrational translate of a hyperrational is not hyperrational. -/
theorem irrational_add_not_hyperrat {r : ℝ} (hr : Irrational r) {x : ℝ*}
    (hx : IsHyperrat x) : ¬ IsHyperrat ((r : ℝ*) + x) := by
  obtain ⟨f, rfl⟩ := hx
  rintro ⟨g, hg⟩
  have hq : ((r : ℝ) : ℝ*) = ofSeq (fun _ => r) := rfl
  rw [hq] at hg
  have hev : ∀ᶠ n in (hyperfilter ℕ : Filter ℕ), r + (f n : ℝ) = g n := Germ.coe_eq.mp hg
  obtain ⟨n, hn⟩ := hev.exists
  exact hr.ne_rat (g n - f n) (by push_cast; linarith)

/-- The rational indicator (Dirichlet function) on `ℝ`. -/
noncomputable def dirichlet : ℝ → ℝ := Set.indicator (Set.range ((↑) : ℚ → ℝ)) (fun _ => 1)

/-- Its natural extension to `ℝ*`, sequence-wise. -/
noncomputable def starDirichlet (x : ℝ*) : ℝ* := Germ.map dirichlet x

/-- `*1_ℚ` equals `1` at every hyperrational, in particular at every point of the
factorial (or dyadic) lattice. -/
theorem starDirichlet_hyperrat {x : ℝ*} (hx : IsHyperrat x) : starDirichlet x = 1 := by
  obtain ⟨f, rfl⟩ := hx
  show ofSeq (fun n => dirichlet (f n)) = ofSeq (fun _ => 1)
  congr 1; funext n
  simp [dirichlet]

/-- `*1_ℚ` vanishes on an irrationally shifted lattice. -/
theorem starDirichlet_shift {r : ℝ} (hr : Irrational r) {x : ℝ*} (hx : IsHyperrat x) :
    starDirichlet ((r : ℝ*) + x) = 0 := by
  obtain ⟨f, rfl⟩ := hx
  show ofSeq (fun n => dirichlet (r + f n)) = ofSeq (fun _ => 0)
  congr 1; funext n
  simp only [dirichlet, Set.indicator_apply_eq_zero, Set.mem_range]
  rintro ⟨q, hq⟩
  exact (hr.ne_rat (q - f n) (by push_cast; linarith)).elim

/-! ### The hyper-snap -/

/-- Snapping in `ℝ*`, defined sequence-wise in the ultrapower. -/
noncomputable def hsnap (e x : ℝ*) : ℝ* := Germ.map₂ (fun a b : ℝ => snap a b) e x

/-- The hyper-snap of `x` is a hyperinteger multiple of `2e`. -/
theorem hsnap_on_lattice (e x : ℝ*) : ∃ z : ℝ*, IsHyperint z ∧ hsnap e x = 2 * e * z := by
  obtain ⟨f, rfl⟩ := ofSeq_surjective e
  obtain ⟨g, rfl⟩ := ofSeq_surjective x
  refine ⟨_, ⟨fun n => snapIdx (f n) (g n), rfl⟩, ?_⟩
  rfl

/-- Snapping error in `ℝ*`: `-e ≤ x - ⌊x⌉_e < e` (Łoś applied by hand). -/
theorem hsnap_mem_cell {e : ℝ*} (he : 0 < e) (x : ℝ*) :
    -e ≤ x - hsnap e x ∧ x - hsnap e x < e := by
  obtain ⟨f, rfl⟩ := ofSeq_surjective e
  obtain ⟨g, rfl⟩ := ofSeq_surjective x
  have hf : ∀ᶠ n in (hyperfilter ℕ : Filter ℕ), 0 < f n := by
    have : ofSeq (fun _ => (0 : ℝ)) < ofSeq f := he
    exact ofSeq_lt_ofSeq.mp this
  constructor
  · show ofSeq (fun n => -f n) ≤ ofSeq (fun n => g n - snap (f n) (g n))
    apply ofSeq_le_ofSeq.mpr
    exact hf.mono fun n hn => (snap_mem_cell hn (g n)).1
  · show ofSeq (fun n => g n - snap (f n) (g n)) < ofSeq f
    apply ofSeq_lt_ofSeq.mpr
    exact hf.mono fun n hn => (snap_mem_cell hn (g n)).2

/-- `|x - ⌊x⌉_e| ≤ e` in `ℝ*`. -/
theorem abs_sub_hsnap_le {e : ℝ*} (he : 0 < e) (x : ℝ*) : |x - hsnap e x| ≤ e := by
  obtain ⟨h1, h2⟩ := hsnap_mem_cell he x
  exact abs_le.mpr ⟨h1, h2.le⟩

/-- Every hyperreal is infinitely close to a lattice point if `e` is a positive
infinitesimal. -/
theorem hsnap_icl {e : ℝ*} (he : 0 < e) (hi : Infinitesimal e) (x : ℝ*) :
    Icl (hsnap e x) x := by
  apply hi.of_abs_le
  rw [abs_sub_comm, abs_of_pos he]
  exact abs_sub_hsnap_le he x

/-- **Shadow of the snap** (`thm:hyper-st-snap`): `st ⌊x⌉_ε = st x`. -/
theorem stdPart_hsnap {e : ℝ*} (he : 0 < e) (hi : Infinitesimal e) (x : ℝ*) :
    ArchimedeanClass.stdPart (hsnap e x) = ArchimedeanClass.stdPart x :=
  stdPart_eq_of_icl (hsnap_icl he hi x)

/-! ### Transfer -/

/-- **Transfer** for the ultrapower of `ℝ` (corollary of Łoś's theorem): for any
first-order language `L` and any `L`-structure on `ℝ`, a sentence holds in the
ultrapower `ℝ^ℕ/U` (with `U` Mathlib's hyperfilter, the ultrafilter used to
build `ℝ*`) iff it holds in `ℝ`. -/
theorem transfer {L : FirstOrder.Language} [L.Structure ℝ] (φ : L.Sentence) :
    ((hyperfilter ℕ : Ultrafilter ℕ) : Filter ℕ).Product (fun _ : ℕ => ℝ) ⊨ φ ↔ ℝ ⊨ φ := by
  rw [FirstOrder.Language.Ultraproduct.sentence_realize]
  exact Filter.eventually_const

end QE.Hyper
