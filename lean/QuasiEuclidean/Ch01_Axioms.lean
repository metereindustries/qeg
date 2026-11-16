-- SPDX-License-Identifier: MIT
-- Copyright 2026 Metere Industries, Inc. Author: Alfredo Metere.
-- Quasi-Euclidean Granular Geometry. Any derivative work must carry this notice:
--   This work is derivative of the Quasi-Euclidean Granular Geometry book
--   authored by Alfredo Metere. Copyright 2026 Metere Industries, Inc.
--   All rights reserved
-- See LICENSE.md and NOTICE.

import QuasiEuclidean.Basic

/-!
# Chapter 1: The axiom that a point is a sphere

Formal counterparts of the results of Chapter 1 (`ch:axiom`).

* Existence of granules: absolute (an infinitesimal in `ℝ*`) and relative
  (below every quantity of a finite context, in any ordered field).
* A concrete model of the axioms QE1–QE3 in Mathlib's `Hyperreal`.
* First consequences: separation of distinct centres, disjoint interiors,
  touching neighbours, overlap criterion, diameter and volume of a point,
  packing density, cell decomposition, lines as tubes.
-/

open Metric

set_option linter.unusedSectionVars false

namespace QE.Axioms

/-! ## Existence of granules -/

/-- **Absolute granule.** There is a positive hyperreal smaller than every
positive real number (Mathlib's `Hyperreal.epsilon`). -/
theorem exists_absolute_granule :
    ∃ ε : ℝ*, 0 < ε ∧ ∀ r : ℝ, 0 < r → ε < (r : ℝ*) :=
  ⟨Hyperreal.epsilon, Hyperreal.epsilon_pos, fun _ hr => Hyperreal.epsilon_lt_of_pos hr⟩

/-- The absolute granule is infinitesimal in the sense of Archimedean
classes (`0 < mk ε`). -/
theorem absolute_granule_infinitesimal :
    0 < ArchimedeanClass.mk (Hyperreal.epsilon) :=
  Hyperreal.archimedeanClassMk_epsilon_pos

/-- The absolute granule has standard part `0`. -/
theorem absolute_granule_stdPart :
    ArchimedeanClass.stdPart (Hyperreal.epsilon) = 0 :=
  Hyperreal.stdPart_epsilon

/-- No standard multiple of the absolute granule reaches `1`: the granule
violates the Archimedean property. -/
theorem absolute_granule_nonarchimedean (n : ℕ) :
    (n : ℝ*) * Hyperreal.epsilon < 1 := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · have hn' : (0 : ℝ) < 1 / n := by positivity
    have h := Hyperreal.epsilon_lt_of_pos hn'
    have hpos : (0 : ℝ*) < n := by exact_mod_cast hn
    rw [Hyperreal.coe_div, Hyperreal.coe_one] at h
    have : (n : ℝ*) = ((n : ℝ) : ℝ*) := by norm_cast
    rw [← this] at h
    calc (n : ℝ*) * Hyperreal.epsilon < n * (1 / n) := mul_lt_mul_of_pos_left h hpos
      _ = 1 := by field_simp

section Field
variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-- **Relative granule.** For every finite context of positive quantities
and every standard safety factor `m`, there is `ε > 0` with `m ε` below every
quantity of the context.  This is the finitary content of Hrbacek's
relative ultrasmallness. -/
theorem exists_relative_granule (s : Finset K) (hs : ∀ x ∈ s, 0 < x) (m : ℕ) :
    ∃ ε : K, 0 < ε ∧ ∀ x ∈ s, (m : K) * ε < x := by
  classical
  by_cases hne : s.Nonempty
  · set μ := s.inf' hne id with hμ
    have hμpos : 0 < μ := by
      rw [hμ, Finset.lt_inf'_iff]; exact fun x hx => hs x hx
    have hM : (0 : K) < (m : K) + 1 := by positivity
    refine ⟨μ / ((m : K) + 1), div_pos hμpos hM, fun x hx => ?_⟩
    have hle : μ ≤ x := Finset.inf'_le _ hx
    have : (m : K) * (μ / ((m : K) + 1)) < μ := by
      rw [mul_div_assoc', div_lt_iff₀ hM]; nlinarith
    linarith
  · refine ⟨1, one_pos, fun x hx => absurd ⟨x, hx⟩ hne⟩

/-! ## Lattice centres -/

theorem centre_sub (ε : K) (k j : ℤ) :
    QE.centre ε k - QE.centre ε j = 2 * ε * ((k - j : ℤ) : K) := by
  unfold QE.centre; push_cast; ring

/-- Distinct lattice centres are at distance at least `2ε` (one point
diameter). -/
theorem centre_dist_ge {ε : K} (hε : 0 < ε) {k j : ℤ} (h : k ≠ j) :
    2 * ε ≤ |QE.centre ε k - QE.centre ε j| := by
  rw [centre_sub, abs_mul, abs_of_pos (by linarith : (0 : K) < 2 * ε)]
  have h1 : (1 : K) ≤ |((k - j : ℤ) : K)| := by
    rw [← Int.cast_abs]
    exact_mod_cast Int.one_le_abs (sub_ne_zero.mpr h)
  nlinarith

theorem centre_injective {ε : K} (hε : ε ≠ 0) : Function.Injective (QE.centre ε) := by
  intro k j h
  unfold QE.centre at h
  have h2 : (2 * ε) ≠ 0 := mul_ne_zero two_ne_zero hε
  exact_mod_cast mul_left_cancel₀ h2 h

/-- Neighbouring centres are exactly one diameter apart. -/
theorem centre_succ (ε : K) (k : ℤ) : QE.centre ε (k + 1) - QE.centre ε k = 2 * ε := by
  unfold QE.centre; push_cast; ring

/-- **QE2 in one dimension.** The open interiors of the point-spheres around
distinct centres are disjoint. -/
theorem interiors_disjoint {ε : K} (hε : 0 < ε) {k j : ℤ} (h : k ≠ j) :
    Disjoint (Set.Ioo (QE.centre ε k - ε) (QE.centre ε k + ε))
      (Set.Ioo (QE.centre ε j - ε) (QE.centre ε j + ε)) := by
  rw [Set.disjoint_left]
  rintro x ⟨h1, h2⟩ ⟨h3, h4⟩
  have := centre_dist_ge hε h
  rcases abs_cases (QE.centre ε k - QE.centre ε j) with ⟨hc, _⟩ | ⟨hc, _⟩ <;> linarith

/-- Neighbouring point-spheres touch in exactly one point. -/
theorem neighbours_touch {ε : K} (hε : 0 ≤ ε) (k : ℤ) :
    Set.Icc (QE.centre ε k - ε) (QE.centre ε k + ε) ∩
      Set.Icc (QE.centre ε (k + 1) - ε) (QE.centre ε (k + 1) + ε)
      = {QE.centre ε k + ε} := by
  have hs := centre_succ ε k
  ext x
  simp only [Set.mem_inter_iff, Set.mem_Icc, Set.mem_singleton_iff]
  constructor
  · rintro ⟨⟨_, h2⟩, ⟨h3, _⟩⟩; linarith
  · rintro rfl
    exact ⟨⟨by linarith, le_rfl⟩, ⟨by linarith, by linarith⟩⟩

/-! ## Voronoi cells and the cell decomposition -/

/-- The Voronoi cell `[c - ε, c + ε)` of the lattice site with index `k`. -/
def cell (ε : K) (k : ℤ) : Set K := Set.Ico (QE.centre ε k - ε) (QE.centre ε k + ε)

/-- Distinct cells are disjoint. -/
theorem cell_disjoint {ε : K} (hε : 0 < ε) {k j : ℤ} (h : k ≠ j) :
    Disjoint (cell ε k) (cell ε j) := by
  rw [Set.disjoint_left]
  rintro x ⟨h1, h2⟩ ⟨h3, h4⟩
  rcases lt_or_gt_of_ne h with hkj | hkj
  · have : (k : K) + 1 ≤ j := by exact_mod_cast hkj
    unfold QE.centre at *; nlinarith
  · have : (j : K) + 1 ≤ k := by exact_mod_cast hkj
    unfold QE.centre at *; nlinarith

/-- Each cell has length `2ε`, the diameter of a point. -/
theorem cell_length (ε : K) (k : ℤ) : (QE.centre ε k + ε) - (QE.centre ε k - ε) = 2 * ε := by
  ring

/-- The cell index of `x`: the index of the nearest lattice centre. -/
noncomputable def cellIndex [FloorRing K] (ε : K) (x : K) : ℤ := ⌊x / (2 * ε) + 1 / 2⌋

theorem mem_cell_cellIndex [FloorRing K] {ε : K} (hε : 0 < ε) (x : K) :
    x ∈ cell ε (cellIndex ε x) := by
  have h2 : (0 : K) < 2 * ε := by linarith
  have hf := Int.floor_le (x / (2 * ε) + 1 / 2)
  have hl := Int.lt_floor_add_one (x / (2 * ε) + 1 / 2)
  unfold cell cellIndex QE.centre
  set n := ⌊x / (2 * ε) + 1 / 2⌋
  have e : x = 2 * ε * (x / (2 * ε)) := by field_simp
  constructor
  · have : 2 * ε * (n : K) ≤ 2 * ε * (x / (2 * ε) + 1 / 2) := mul_le_mul_of_nonneg_left hf h2.le
    nlinarith
  · have : 2 * ε * (x / (2 * ε) + 1 / 2) < 2 * ε * ((n : K) + 1) :=
      mul_lt_mul_of_pos_left hl h2
    nlinarith

/-- **Cell decomposition.** Every element of the field lies in exactly one
cell. -/
theorem existsUnique_cell [FloorRing K] {ε : K} (hε : 0 < ε) (x : K) :
    ∃! k : ℤ, x ∈ cell ε k := by
  refine ⟨cellIndex ε x, mem_cell_cellIndex hε x, fun j hj => ?_⟩
  by_contra hne
  exact Set.disjoint_left.mp (cell_disjoint hε hne) hj (mem_cell_cellIndex hε x)

/-- The cells with indices in `[a, b]` tile the half-open interval
`[2εa - ε, 2εb + ε)`. -/
theorem cells_cover_interval [FloorRing K] {ε : K} (hε : 0 < ε) (a b : ℤ) :
    (⋃ k ∈ Finset.Icc a b, cell ε k) =
      Set.Ico (QE.centre ε a - ε) (QE.centre ε b + ε) := by
  ext x
  simp only [Set.mem_iUnion, Finset.mem_Icc, exists_prop, Set.mem_Ico]
  constructor
  · rintro ⟨k, ⟨hak, hkb⟩, h1, h2⟩
    have ha : (a : K) ≤ k := by exact_mod_cast hak
    have hb : (k : K) ≤ b := by exact_mod_cast hkb
    unfold QE.centre at *
    constructor <;> nlinarith
  · rintro ⟨h1, h2⟩
    obtain ⟨hc1, hc2⟩ := mem_cell_cellIndex hε x
    refine ⟨cellIndex ε x, ⟨?_, ?_⟩, hc1, hc2⟩
    · by_contra hlt; push Not at hlt
      have : ((cellIndex ε x : ℤ) : K) + 1 ≤ a := by exact_mod_cast hlt
      unfold QE.centre at *; nlinarith
    · by_contra hlt; push Not at hlt
      have : (b : K) + 1 ≤ ((cellIndex ε x : ℤ) : K) := by exact_mod_cast hlt
      unfold QE.centre at *; nlinarith

/-- The total length of the cells indexed by `[a, b]` equals the length of
the interval they tile, which is the granular measure `μ_ε [a, b]`. -/
theorem cells_total_length (ε : K) {a b : ℤ} (h : a ≤ b) :
    ((QE.centre ε b + ε) - (QE.centre ε a - ε)) = QE.mu ε (Finset.Icc a b) := by
  unfold QE.mu QE.centre
  rw [Int.card_Icc]
  have hc : (((b + 1 - a).toNat : ℕ) : K) = ((b + 1 - a : ℤ) : K) := by
    rw [← Int.cast_natCast, Int.toNat_of_nonneg (by omega)]
  rw [hc]; push_cast; ring

/-! ## Lines are tubes -/

/-- A point-sphere with centre index `m` meets the horizontal line at height
`y` iff `|2εm - y| ≤ ε`.  Any two lattice rows meeting the same line are
equal or adjacent. -/
theorem line_rows_adjacent {ε : K} (hε : 0 < ε) {y : K} {m m' : ℤ}
    (hm : |QE.centre ε m - y| ≤ ε) (hm' : |QE.centre ε m' - y| ≤ ε) :
    |m - m'| ≤ 1 := by
  by_contra hc; push Not at hc
  have hne : m ≠ m' := by intro h; subst h; simp at hc
  have h2 : (2 : ℤ) ≤ |m - m'| := hc
  have hK : (2 : K) ≤ |((m - m' : ℤ) : K)| := by rw [← Int.cast_abs]; exact_mod_cast h2
  have hd : |QE.centre ε m - QE.centre ε m'| ≤ 2 * ε := by
    calc |QE.centre ε m - QE.centre ε m'|
        = |(QE.centre ε m - y) - (QE.centre ε m' - y)| := by ring_nf
      _ ≤ |QE.centre ε m - y| + |QE.centre ε m' - y| := abs_sub _ _
      _ ≤ 2 * ε := by linarith
  rw [centre_sub, abs_mul, abs_of_pos (by linarith : (0 : K) < 2 * ε)] at hd
  nlinarith

/-- Every horizontal line meets at least one row of point-spheres. -/
theorem line_meets_row [FloorRing K] {ε : K} (hε : 0 < ε) (y : K) :
    ∃ m : ℤ, |QE.centre ε m - y| ≤ ε := by
  obtain ⟨h1, h2⟩ := mem_cell_cellIndex hε y
  exact ⟨cellIndex ε y, abs_le.mpr ⟨by linarith, by linarith⟩⟩

/-- **Packing density** of the cubic lattice of touching balls: the ratio of
ball volume `ω ε^n` to cell volume `(2ε)^n` does not depend on `ε`. -/
theorem packing_density (ω : K) {ε : K} (hε : ε ≠ 0) (n : ℕ) :
    ω * ε ^ n / (2 * ε) ^ n = ω / 2 ^ n := by
  rw [mul_pow]; field_simp

/-- **The point `0` is not nothing.** The configuration consisting of the
single point at the origin has granular measure `2ε > 0`, while the empty
configuration has measure `0`. -/
theorem mu_origin_ne_empty {ε : K} (hε : 0 < ε) :
    QE.mu ε ∅ = 0 ∧ QE.mu ε {0} = 2 * ε ∧ QE.mu ε ∅ < QE.mu ε {0} := by
  unfold QE.mu; simp; linarith

/-- **Shared endpoints are counted.** Two closed lattice segments sharing an
endpoint: `μ[a,b] + μ[b,c] = μ[a,c] + 2ε`; the excess is exactly the
measure of the shared point. -/
theorem mu_shared_endpoint (ε : K) {a b c : ℤ} (hab : a ≤ b) (hbc : b ≤ c) :
    QE.mu ε (Finset.Icc a b) + QE.mu ε (Finset.Icc b c)
      = QE.mu ε (Finset.Icc a c) + 2 * ε := by
  unfold QE.mu
  rw [Int.card_Icc, Int.card_Icc, Int.card_Icc]
  have h1 : (((b + 1 - a).toNat : ℕ) : K) = ((b + 1 - a : ℤ) : K) := by
    rw [← Int.cast_natCast, Int.toNat_of_nonneg (by omega)]
  have h2 : (((c + 1 - b).toNat : ℕ) : K) = ((c + 1 - b : ℤ) : K) := by
    rw [← Int.cast_natCast, Int.toNat_of_nonneg (by omega)]
  have h3 : (((c + 1 - a).toNat : ℕ) : K) = ((c + 1 - a : ℤ) : K) := by
    rw [← Int.cast_natCast, Int.toNat_of_nonneg (by omega)]
  rw [h1, h2, h3]; push_cast; ring

/-- **Zeno's dichotomy terminates at the granule.** After `K` halvings the
runner has covered `1 - 2^{-K}`; on the dyadic lattice `2ε = 2^{-K}` the
remaining distance is exactly one point diameter. -/
theorem zeno_dyadic (K' : ℕ) :
    ∑ k ∈ Finset.range K', ((1 : K) / 2) ^ (k + 1) = 1 - ((1 : K) / 2) ^ K' := by
  induction K' with
  | zero => simp
  | succ n ih => rw [Finset.sum_range_succ, ih, pow_succ]; ring

/-- **The granular line is discretely ordered.** No lattice centre lies
strictly between two neighbouring centres. -/
theorem no_centre_between {ε : K} (hε : 0 < ε) (k m : ℤ) :
    ¬ (QE.centre ε k < QE.centre ε m ∧ QE.centre ε m < QE.centre ε (k + 1)) := by
  rintro ⟨h1, h2⟩
  unfold QE.centre at h1 h2
  have h2ε : (0 : K) < 2 * ε := by linarith
  have a1 : (k : K) < m := lt_of_mul_lt_mul_left h1 h2ε.le
  have a2 : (m : K) < ((k + 1 : ℤ) : K) := lt_of_mul_lt_mul_left h2 h2ε.le
  have b1 : k < m := by exact_mod_cast a1
  have b2 : m < k + 1 := by exact_mod_cast a2
  omega

end Field

/-! ## Points in `ℝⁿ` -/

/-- Lattice point with index `k : Fin n → ℤ` in `ℝⁿ` (sup-metric model). -/
def latticePt {n : ℕ} (ε : ℝ) (k : Fin n → ℤ) : Fin n → ℝ := fun i => 2 * ε * k i

/-- Distinct lattice points in `ℝⁿ` are at sup-distance `≥ 2ε`. -/
theorem latticePt_dist_ge {n : ℕ} {ε : ℝ} (hε : 0 < ε) {k j : Fin n → ℤ} (h : k ≠ j) :
    2 * ε ≤ dist (latticePt ε k) (latticePt ε j) := by
  obtain ⟨i, hi⟩ := Function.ne_iff.mp h
  calc 2 * ε ≤ |QE.centre ε (k i) - QE.centre ε (j i)| := centre_dist_ge hε hi
    _ = dist (latticePt ε k i) (latticePt ε j i) := by
        rw [Real.dist_eq]; rfl
    _ ≤ dist (latticePt ε k) (latticePt ε j) := dist_le_pi_dist _ _ i

/-- **QE2 in `ℝⁿ`.** Open balls of radius `ε` around distinct lattice points
are disjoint. -/
theorem latticePt_balls_disjoint {n : ℕ} {ε : ℝ} (hε : 0 < ε) {k j : Fin n → ℤ}
    (h : k ≠ j) : Disjoint (ball (latticePt ε k) ε) (ball (latticePt ε j) ε) := by
  rw [Set.disjoint_left]
  intro x hx hy
  have h1 := latticePt_dist_ge hε h
  have h2 := dist_triangle_right (latticePt ε k) (latticePt ε j) x
  rw [mem_ball] at hx hy
  rw [dist_comm] at hx hy
  linarith

/-- Lattice point in Euclidean space. -/
noncomputable def latticePtE {n : ℕ} (ε : ℝ) (k : Fin n → ℤ) : EuclideanSpace ℝ (Fin n) :=
  WithLp.toLp 2 (latticePt ε k)

/-- Distinct lattice points are at Euclidean distance `≥ 2ε`. -/
theorem latticePtE_dist_ge {n : ℕ} {ε : ℝ} (hε : 0 < ε) {k j : Fin n → ℤ} (h : k ≠ j) :
    2 * ε ≤ dist (latticePtE ε k) (latticePtE ε j) := by
  obtain ⟨i, hi⟩ := Function.ne_iff.mp h
  have h1 := centre_dist_ge hε hi
  rw [EuclideanSpace.dist_eq]
  have hterm : dist (latticePt ε k i) (latticePt ε j i) ^ 2 ≤
      ∑ l, dist ((latticePtE ε k) l) ((latticePtE ε j) l) ^ 2 := by
    have := Finset.single_le_sum (f := fun l => dist ((latticePtE ε k) l) ((latticePtE ε j) l) ^ 2)
      (fun l _ => sq_nonneg _) (Finset.mem_univ i)
    simpa [latticePtE] using this
  have hd : dist (latticePt ε k i) (latticePt ε j i) = |QE.centre ε (k i) - QE.centre ε (j i)| := by
    rw [Real.dist_eq]; rfl
  rw [hd] at hterm
  calc 2 * ε ≤ |QE.centre ε (k i) - QE.centre ε (j i)| := h1
    _ = Real.sqrt (|QE.centre ε (k i) - QE.centre ε (j i)| ^ 2) := by
        rw [Real.sqrt_sq (abs_nonneg _)]
    _ ≤ _ := Real.sqrt_le_sqrt hterm

/-- **QE2 in Euclidean `ℝⁿ`.** Open Euclidean balls of radius `ε` around
distinct lattice points are disjoint. -/
theorem latticePtE_balls_disjoint {n : ℕ} {ε : ℝ} (hε : 0 < ε) {k j : Fin n → ℤ}
    (h : k ≠ j) : Disjoint (ball (latticePtE ε k) ε) (ball (latticePtE ε j) ε) := by
  rw [Set.disjoint_left]
  intro x hx hy
  have h1 := latticePtE_dist_ge hε h
  have h2 := dist_triangle_right (latticePtE ε k) (latticePtE ε j) x
  rw [mem_ball] at hx hy
  rw [dist_comm] at hx hy
  linarith

/-- **Incidence is overlap.** In a real normed space, two point-spheres
(closed balls of radius `ε`) meet iff their centres are at most `2ε` apart. -/
theorem points_meet_iff {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {ε : ℝ} (x y : E) :
    (closedBall x ε ∩ closedBall y ε).Nonempty ↔ dist x y ≤ 2 * ε := by
  constructor
  · rintro ⟨z, hx, hy⟩
    rw [mem_closedBall, dist_comm] at hx hy
    have := dist_triangle_right x y z
    linarith
  · intro h
    refine ⟨midpoint ℝ x y, ?_, ?_⟩
    · rw [mem_closedBall, dist_comm, dist_left_midpoint (𝕜 := ℝ)]
      simp only [Real.norm_ofNat]; linarith
    · rw [mem_closedBall, dist_comm, dist_right_midpoint (𝕜 := ℝ)]
      simp only [Real.norm_ofNat]; linarith

/-- **A point has diameter `2ε`** (in any nontrivial real normed space). -/
theorem point_diam {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [Nontrivial E]
    (c : E) {ε : ℝ} (hε : 0 ≤ ε) : diam (closedBall c ε) = 2 * ε :=
  Metric.diam_closedBall_eq c hε

open MeasureTheory in
/-- **Shadow (classical comparison).** The Lebesgue volume of the ball
`closedBall c ε` is `ω_n ε^n`, with
`ω_n = π^{n/2} / Γ(n/2 + 1)` the volume of the unit ball of `ℝⁿ`. -/
theorem point_volume (n : ℕ) [NeZero n] (c : EuclideanSpace ℝ (Fin n)) (ε : ℝ) :
    volume (closedBall c ε) = ENNReal.ofReal ε ^ n *
      ENNReal.ofReal (Real.sqrt Real.pi ^ n / Real.Gamma (n / 2 + 1)) := by
  rw [EuclideanSpace.volume_closedBall, Fintype.card_fin]

/-! ## Cells, slabs and Cavalieri in `n` dimensions -/

/-- The `n`-dimensional Voronoi cell `c + [-ε, ε)ⁿ` of the lattice point with
index `k`. -/
def cellN {n : ℕ} (ε : ℝ) (k : Fin n → ℤ) : Set (Fin n → ℝ) :=
  Set.pi Set.univ fun i => cell ε (k i)

/-- **Cell decomposition of `ℝⁿ`.** Every point of `ℝⁿ` lies in exactly one
`n`-dimensional cell. -/
theorem existsUnique_cellN {n : ℕ} {ε : ℝ} (hε : 0 < ε) (x : Fin n → ℝ) :
    ∃! k : Fin n → ℤ, x ∈ cellN ε k := by
  refine ⟨fun i => cellIndex ε (x i), ?_, ?_⟩
  · intro i _; exact mem_cell_cellIndex hε (x i)
  · intro j hj
    funext i
    have hji : x i ∈ cell ε (j i) := hj i (Set.mem_univ i)
    by_contra hne
    exact Set.disjoint_left.mp (cell_disjoint hε hne) hji (mem_cell_cellIndex hε (x i))

open MeasureTheory in
/-- **Shadow (classical comparison).** Each `n`-dimensional cell has Lebesgue
volume `(2ε)ⁿ`, equal to the content that QE4 assigns to a point by counting. -/
theorem volume_cellN {n : ℕ} {ε : ℝ} (hε : 0 ≤ ε) (k : Fin n → ℤ) :
    volume (cellN ε k) = ENNReal.ofReal ((2 * ε) ^ n) := by
  unfold cellN cell
  rw [Real.volume_pi_Ico]
  have h : ∀ i : Fin n, ENNReal.ofReal (QE.centre ε (k i) + ε - (QE.centre ε (k i) - ε))
      = ENNReal.ofReal (2 * ε) := fun i => by congr 1; ring
  simp only [h, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [← ENNReal.ofReal_pow (by linarith)]

/-- **A hyperplane piece is a slab one point thick.** The granular content of
the box `{0} × ∏ tᵢ` in dimension `n+1` equals the point diameter `2ε`
times the `n`-dimensional content of `∏ tᵢ`. -/
theorem muN_slab {n : ℕ} (ε : ℝ) (t : Fin n → Finset ℤ) :
    QE.muN (n + 1) ε (Fintype.piFinset (Fin.cons ({0} : Finset ℤ) t))
      = 2 * ε * QE.muN n ε (Fintype.piFinset t) := by
  unfold QE.muN
  rw [Fintype.card_piFinset, Fintype.card_piFinset, Fin.prod_univ_succ]
  simp
  ring

/-- **A segment has breadth one point.** A horizontal granular segment
`[a,b] × {0}` in the plane has area `2ε · μ_ε[a,b]`. -/
theorem muN_segment (ε : ℝ) (a b : ℤ) :
    QE.muN 2 ε (Fintype.piFinset ![({0} : Finset ℤ), Finset.Icc a b])
      = 2 * ε * QE.mu ε (Finset.Icc a b) := by
  unfold QE.muN QE.mu
  rw [Fintype.card_piFinset, Fin.prod_univ_two]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Finset.card_singleton, one_mul]
  ring

/-- **Cavalieri's principle is exact.** The granular square `[a,b]²` is the
disjoint union of its `b - a + 1` rows; its content is the number of rows
times the area of a row, which equals `μ_ε[a,b]²`. -/
theorem cavalieri_square (ε : ℝ) (a b : ℤ) :
    QE.muN 2 ε (Fintype.piFinset fun _ : Fin 2 => Finset.Icc a b)
      = ((Finset.Icc a b).card : ℝ) * (2 * ε * QE.mu ε (Finset.Icc a b)) ∧
    QE.muN 2 ε (Fintype.piFinset fun _ : Fin 2 => Finset.Icc a b)
      = QE.mu ε (Finset.Icc a b) ^ 2 := by
  unfold QE.muN QE.mu
  rw [Fintype.card_piFinset, Fin.prod_univ_two]
  constructor <;> (push_cast; ring)

/-! ## A model of QE1–QE3 in `ℝ*` -/

/-- A hyperreal is a *hyperinteger* if it is represented by an integer
sequence. -/
def IsHyperint (x : ℝ*) : Prop := ∃ f : ℕ → ℤ, x = Hyperreal.ofSeq (fun n => (f n : ℝ))

/-- The data of a model of the axioms QE1–QE3: a granule `ε > 0` smaller
than every positive real, an infinite hyperinteger `N` with `2εN = 1`, and an
infinite horizon `Ω = 2ε·M` with `M` a hyperinteger. -/
structure GranularModel where
  ε : ℝ*
  N : ℝ*
  M : ℝ*
  ε_pos : 0 < ε
  ε_small : ∀ r : ℝ, 0 < r → ε < (r : ℝ*)
  N_hyperint : IsHyperint N
  spacing_inv : 2 * ε * N = 1
  M_hyperint : IsHyperint M
  horizon_infinite : ∀ r : ℝ, (r : ℝ*) < 2 * ε * M

/-- **Consistency of QE1–QE3**: the hyperreal ultrapower carries a model,
with `N = ω`, `ε = 1/(2ω)` and horizon `Ω = ω`. -/
noncomputable def hyperrealModel : GranularModel where
  ε := Hyperreal.epsilon / 2
  N := Hyperreal.omega
  M := Hyperreal.omega * Hyperreal.omega
  ε_pos := by have := Hyperreal.epsilon_pos; positivity
  ε_small r hr := by
    have h1 := Hyperreal.epsilon_lt_of_pos hr
    have h2 := Hyperreal.epsilon_pos
    linarith
  N_hyperint := ⟨fun n => n, by simp [Hyperreal.omega]⟩
  spacing_inv := by
    have := Hyperreal.epsilon_mul_omega
    linear_combination this
  M_hyperint := ⟨fun n => (n : ℤ) * n, by
    simp only [Hyperreal.omega, Int.cast_mul, Int.cast_natCast]; rfl⟩
  horizon_infinite r := by
    have h : 2 * (Hyperreal.epsilon / 2) * (Hyperreal.omega * Hyperreal.omega) =
        Hyperreal.omega := by
      have := Hyperreal.epsilon_mul_omega
      linear_combination Hyperreal.omega * this
    rw [h]; exact Hyperreal.coe_lt_omega r

theorem consistent : Nonempty GranularModel := ⟨hyperrealModel⟩


/-! ## Combined statements (one Lean name per book statement) -/

/-- Book: Proposition "Granules exist". -/
theorem granules_exist :
    (∃ ε : ℝ*, 0 < ε ∧ ∀ r : ℝ, 0 < r → ε < (r : ℝ*)) ∧
    0 < ArchimedeanClass.mk (Hyperreal.epsilon) ∧
    (∀ n : ℕ, (n : ℝ*) * Hyperreal.epsilon < 1) ∧
    (∀ (K : Type) [Field K] [LinearOrder K] [IsStrictOrderedRing K]
      (s : Finset K), (∀ x ∈ s, 0 < x) → ∀ m : ℕ, ∃ ε : K, 0 < ε ∧ ∀ x ∈ s, (m : K) * ε < x) :=
  ⟨exists_absolute_granule, absolute_granule_infinitesimal, absolute_granule_nonarchimedean,
    fun _ _ _ _ s hs m => exists_relative_granule s hs m⟩

/-- Book: Proposition "Separation of centres". -/
theorem separation :
    (∀ (K : Type) [Field K] [LinearOrder K] [IsStrictOrderedRing K] (ε : K), 0 < ε →
      (∀ k j : ℤ, k ≠ j → 2 * ε ≤ |QE.centre ε k - QE.centre ε j|) ∧
      Function.Injective (QE.centre ε) ∧
      (∀ k : ℤ, QE.centre ε (k + 1) - QE.centre ε k = 2 * ε)) ∧
    (∀ (n : ℕ) (ε : ℝ), 0 < ε → ∀ k j : Fin n → ℤ, k ≠ j →
      2 * ε ≤ dist (latticePt ε k) (latticePt ε j) ∧
      2 * ε ≤ dist (latticePtE ε k) (latticePtE ε j)) :=
  ⟨fun _ _ _ _ _ hε => ⟨fun _ _ h => centre_dist_ge hε h, centre_injective hε.ne',
      fun k => centre_succ _ k⟩,
   fun _ _ hε _ _ h => ⟨latticePt_dist_ge hε h, latticePtE_dist_ge hε h⟩⟩

/-- Book: Theorem "Impenetrability". -/
theorem impenetrability :
    (∀ (K : Type) [Field K] [LinearOrder K] [IsStrictOrderedRing K] (ε : K), 0 < ε →
      (∀ k j : ℤ, k ≠ j → Disjoint (Set.Ioo (QE.centre ε k - ε) (QE.centre ε k + ε))
        (Set.Ioo (QE.centre ε j - ε) (QE.centre ε j + ε))) ∧
      (∀ k : ℤ, Set.Icc (QE.centre ε k - ε) (QE.centre ε k + ε) ∩
        Set.Icc (QE.centre ε (k + 1) - ε) (QE.centre ε (k + 1) + ε) = {QE.centre ε k + ε})) ∧
    (∀ (n : ℕ) (ε : ℝ), 0 < ε → ∀ k j : Fin n → ℤ, k ≠ j →
      Disjoint (ball (latticePt ε k) ε) (ball (latticePt ε j) ε) ∧
      Disjoint (ball (latticePtE ε k) ε) (ball (latticePtE ε j) ε)) :=
  ⟨fun _ _ _ _ _ hε => ⟨fun _ _ h => interiors_disjoint hε h, fun k => neighbours_touch hε.le k⟩,
   fun _ _ hε _ _ h => ⟨latticePt_balls_disjoint hε h, latticePtE_balls_disjoint hε h⟩⟩

/-- Book: Theorem "Cell decomposition" (one dimension). -/
theorem cell_decomposition {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    [FloorRing K] {ε : K} (hε : 0 < ε) :
    (∀ k j : ℤ, k ≠ j → Disjoint (cell ε k) (cell ε j)) ∧
    (∀ k : ℤ, (QE.centre ε k + ε) - (QE.centre ε k - ε) = 2 * ε) ∧
    (∀ x : K, ∃! k : ℤ, x ∈ cell ε k) ∧
    (∀ a b : ℤ, (⋃ k ∈ Finset.Icc a b, cell ε k) =
      Set.Ico (QE.centre ε a - ε) (QE.centre ε b + ε)) ∧
    (∀ a b : ℤ, a ≤ b →
      ((QE.centre ε b + ε) - (QE.centre ε a - ε)) = QE.mu ε (Finset.Icc a b)) :=
  ⟨fun _ _ h => cell_disjoint hε h, cell_length ε, existsUnique_cell hε,
    cells_cover_interval hε, fun _ _ h => cells_total_length ε h⟩

/-- **The content of a point is one atom** (Lebesgue-free).  A single lattice
point has granular content `(2ε)ⁿ`, and the content of every finite
configuration is the sum of the contents of its points. -/
theorem muN_singleton_atom {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K] (n : ℕ) (ε : K) (k : Fin n → ℤ) :
    QE.muN n ε {k} = (2 * ε) ^ n := by
  unfold QE.muN; simp

theorem muN_eq_sum_atoms {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K] (n : ℕ) (ε : K) (A : Finset (Fin n → ℤ)) :
    QE.muN n ε A = ∑ k ∈ A, QE.muN n ε {k} := by
  simp only [muN_singleton_atom, Finset.sum_const, nsmul_eq_mul]
  unfold QE.muN; ring

/-- Book: Proposition "Diameter and content of a point" (granular, Lebesgue-free):
the point-sphere has diameter `2ε`, a single point has content `(2ε)ⁿ`, and
content is additive over points.  The Lebesgue volume `ω_n εⁿ` of the ball is
the separate shadow statement `point_volume`. -/
theorem point_size (n : ℕ) [NeZero n] (c : EuclideanSpace ℝ (Fin n)) {ε : ℝ} (hε : 0 ≤ ε) :
    diam (closedBall c ε) = 2 * ε ∧
    (∀ k : Fin n → ℤ, QE.muN n ε {k} = (2 * ε) ^ n) ∧
    (∀ A : Finset (Fin n → ℤ), QE.muN n ε A = ∑ k ∈ A, QE.muN n ε {k}) := by
  have : Nontrivial (EuclideanSpace ℝ (Fin n)) := by
    refine ⟨⟨EuclideanSpace.single 0 1, 0, fun h => ?_⟩⟩
    have := congrArg (fun v : EuclideanSpace ℝ (Fin n) => v 0) h
    simp at this
  exact ⟨point_diam c hε, muN_singleton_atom n ε, muN_eq_sum_atoms n ε⟩

/-- Book: Proposition "A line is a tube one or two points thick". -/
theorem line_tube {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K] [FloorRing K]
    {ε : K} (hε : 0 < ε) (y : K) :
    (∃ m : ℤ, |QE.centre ε m - y| ≤ ε) ∧
    (∀ m m' : ℤ, |QE.centre ε m - y| ≤ ε → |QE.centre ε m' - y| ≤ ε → |m - m'| ≤ 1) :=
  ⟨line_meets_row hε y, fun _ _ h h' => line_rows_adjacent hε h h'⟩

/-- Book: Theorem "Cell decomposition of n-space" (granular, Lebesgue-free).
Every `x ∈ ℝⁿ` lies in exactly one cell; its owner is given coordinatewise by
the floor map `cellIndex`; each cell is the product of `n` half-open
intervals of length `2ε`; and the content of a finite set of lattice points
is `(2ε)ⁿ` per owned cell.  (The Lebesgue volume of a cell is the shadow
statement `volume_cellN`.) -/
theorem cell_decomposition_n {n : ℕ} {ε : ℝ} (hε : 0 < ε) :
    (∀ x : Fin n → ℝ, ∃! k : Fin n → ℤ, x ∈ cellN ε k) ∧
    (∀ (x : Fin n → ℝ) (k : Fin n → ℤ), x ∈ cellN ε k ↔ k = fun i => cellIndex ε (x i)) ∧
    (∀ k : Fin n → ℤ, cellN ε k =
      Set.pi Set.univ (fun i => Set.Ico (QE.centre ε (k i) - ε) (QE.centre ε (k i) + ε)) ∧
      ∀ i, (QE.centre ε (k i) + ε) - (QE.centre ε (k i) - ε) = 2 * ε) ∧
    (∀ A : Finset (Fin n → ℤ), QE.muN n ε A = ∑ _k ∈ A, (2 * ε) ^ n) := by
  refine ⟨existsUnique_cellN hε, fun x k => ⟨fun hk => ?_, fun hk => ?_⟩,
    fun k => ⟨rfl, fun i => cell_length ε (k i)⟩, fun A => ?_⟩
  · obtain ⟨k0, -, hu⟩ := existsUnique_cellN (n := n) hε x
    have h1 := hu k hk
    have h2 := hu (fun i => cellIndex ε (x i)) (fun i _ => mem_cell_cellIndex hε (x i))
    rw [h1, h2]
  · subst hk; exact fun i _ => mem_cell_cellIndex hε (x i)
  · rw [Finset.sum_const, nsmul_eq_mul]; unfold QE.muN; ring

/-- Book: Proposition "Lines have breadth, planes have thickness". -/
theorem breadth (ε : ℝ) :
    (∀ a b : ℤ, QE.muN 2 ε (Fintype.piFinset ![({0} : Finset ℤ), Finset.Icc a b])
      = 2 * ε * QE.mu ε (Finset.Icc a b)) ∧
    (∀ (n : ℕ) (t : Fin n → Finset ℤ),
      QE.muN (n + 1) ε (Fintype.piFinset (Fin.cons ({0} : Finset ℤ) t))
        = 2 * ε * QE.muN n ε (Fintype.piFinset t)) :=
  ⟨muN_segment ε, fun _ t => muN_slab ε t⟩

end QE.Axioms
