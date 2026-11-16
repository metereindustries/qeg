-- SPDX-License-Identifier: MIT
-- Copyright 2026 Metere Industries, Inc. Author: Alfredo Metere.
-- Quasi-Euclidean Granular Geometry. Any derivative work must carry this notice:
--   This work is derivative of the Quasi-Euclidean Granular Geometry book
--   authored by Alfredo Metere. Copyright 2026 Metere Industries, Inc.
--   All rights reserved
-- See LICENSE.md and NOTICE.

import QuasiEuclidean.Basic

/-!
# Chapter 1, Section "The packing objection"

Formal counterparts of the results of the section `sec:axiom-packing`.

* Cells own space: every point of `ℝⁿ` lies in exactly one Voronoi cell
  `2εk + [-ε, ε)ⁿ` (gap points included).
* Covering: every point is within sup-distance `ε` and Euclidean distance
  `√n ε` of a centre, and within `(√n - 1) ε` of a point-sphere; the deep
  hole `(ε, …, ε)` shows that both constants are sharp, so gaps exist for
  `n ≥ 2`.
* The ball/cell volume ratio is independent of `ε` (scale invariance), and
  the uniform density factor cancels from ratios and averages.
* Classical observables: per-cell and summed error bounds for integrals of
  Lipschitz functions (constant `L √n ε` per unit volume) and for distances.
* Informational observables: the singleton and the endpoint bit, where the
  whole difference is of order `ε`.
-/

open Metric MeasureTheory

set_option linter.unusedSectionVars false

namespace QE.Packing

/-! ## Lattice points, cells and owners in `ℝⁿ` -/

/-- Centre of the point-sphere with index `k` (as a point of `Fin n → ℝ`). -/
def ptR {n : ℕ} (ε : ℝ) (k : Fin n → ℤ) : Fin n → ℝ := fun i => 2 * ε * k i

/-- Centre of the point-sphere with index `k`, as a point of Euclidean space. -/
noncomputable def ptE {n : ℕ} (ε : ℝ) (k : Fin n → ℤ) : EuclideanSpace ℝ (Fin n) :=
  WithLp.toLp 2 (ptR ε k)

/-- The Voronoi cell `2εk + [-ε, ε)ⁿ` owned by the point with index `k`. -/
def cell {n : ℕ} (ε : ℝ) (k : Fin n → ℤ) : Set (Fin n → ℝ) :=
  Set.pi Set.univ fun i => Set.Ico (2 * ε * k i - ε) (2 * ε * k i + ε)

/-- The owner of a position `x`: the index of the cell containing it. -/
noncomputable def owner {n : ℕ} (ε : ℝ) (x : Fin n → ℝ) : Fin n → ℤ :=
  fun i => ⌊x i / (2 * ε) + 1 / 2⌋

theorem mem_cell_owner {n : ℕ} {ε : ℝ} (hε : 0 < ε) (x : Fin n → ℝ) :
    x ∈ cell ε (owner ε x) := by
  intro i _
  have h2 : 0 < 2 * ε := by linarith
  have h1 := Int.floor_le (x i / (2 * ε) + 1 / 2)
  have h3 := Int.lt_floor_add_one (x i / (2 * ε) + 1 / 2)
  simp only [owner]
  set m := ⌊x i / (2 * ε) + 1 / 2⌋
  have e : x i / (2 * ε) * (2 * ε) = x i := div_mul_cancel₀ _ h2.ne'
  constructor
  · have := mul_le_mul_of_nonneg_right h1 h2.le
    nlinarith
  · have := mul_lt_mul_of_pos_right h3 h2
    nlinarith

/-- A cell determines its index: distinct cells are disjoint. -/
theorem eq_owner_of_mem_cell {n : ℕ} {ε : ℝ} (hε : 0 < ε) {x : Fin n → ℝ}
    {k : Fin n → ℤ} (hx : x ∈ cell ε k) : k = owner ε x := by
  have ho := mem_cell_owner hε x
  funext i
  obtain ⟨a1, a2⟩ := hx i (Set.mem_univ i)
  obtain ⟨b1, b2⟩ := ho i (Set.mem_univ i)
  have hk : (2 * ε) * (k i : ℝ) < (2 * ε) * ((owner ε x i : ℝ) + 1) := by nlinarith
  have hk' : (2 * ε) * (owner ε x i : ℝ) < (2 * ε) * ((k i : ℝ) + 1) := by nlinarith
  have h2 : 0 < 2 * ε := by linarith
  have c1 : (k i : ℝ) < owner ε x i + 1 := lt_of_mul_lt_mul_left hk h2.le
  have c2 : (owner ε x i : ℝ) < k i + 1 := lt_of_mul_lt_mul_left hk' h2.le
  have d1 : k i < owner ε x i + 1 := by exact_mod_cast c1
  have d2 : owner ε x i < k i + 1 := by exact_mod_cast c2
  omega

/-- **Unique ownership.** Every position of `ℝⁿ`, in particular every point
of an interstitial gap between the balls, lies in exactly one cell. -/
theorem existsUnique_owner {n : ℕ} {ε : ℝ} (hε : 0 < ε) (x : Fin n → ℝ) :
    ∃! k : Fin n → ℤ, x ∈ cell ε k :=
  ⟨owner ε x, mem_cell_owner hε x, fun _ hk => eq_owner_of_mem_cell hε hk⟩

/-! ## Covering radius -/

/-- **Covering in the sup norm.** Every position is within `ε` of a centre
in every coordinate. -/
theorem cover_sup {n : ℕ} {ε : ℝ} (hε : 0 < ε) (x : Fin n → ℝ) :
    ∃ k : Fin n → ℤ, ∀ i, |x i - 2 * ε * k i| ≤ ε := by
  refine ⟨owner ε x, fun i => ?_⟩
  obtain ⟨h1, h2⟩ := mem_cell_owner hε x i (Set.mem_univ i)
  exact abs_le.mpr ⟨by linarith, by linarith⟩

/-- Euclidean distance is at most `√n` times the sup distance. -/
theorem euclid_le_sqrt_sup {n : ℕ} (x y : Fin n → ℝ) :
    dist (WithLp.toLp 2 x : EuclideanSpace ℝ (Fin n)) (WithLp.toLp 2 y)
      ≤ Real.sqrt n * dist x y := by
  rw [EuclideanSpace.dist_eq]
  have hs : ∑ i, dist ((WithLp.toLp 2 x : EuclideanSpace ℝ (Fin n)) i)
      ((WithLp.toLp 2 y : EuclideanSpace ℝ (Fin n)) i) ^ 2 ≤ n * dist x y ^ 2 := by
    calc _ ≤ ∑ _i : Fin n, dist x y ^ 2 := by
          apply Finset.sum_le_sum
          intro i _
          have := dist_le_pi_dist x y i
          exact pow_le_pow_left₀ dist_nonneg this 2
      _ = n * dist x y ^ 2 := by simp
  calc _ ≤ Real.sqrt (n * dist x y ^ 2) := Real.sqrt_le_sqrt hs
    _ = Real.sqrt n * dist x y := by
        rw [Real.sqrt_mul (by positivity), Real.sqrt_sq dist_nonneg]

/-- Every point of a cell is within Euclidean distance `√n ε` of its centre. -/
theorem dist_centre_le_of_mem_cell {n : ℕ} {ε : ℝ} (hε : 0 < ε) {x : Fin n → ℝ}
    {k : Fin n → ℤ} (hx : x ∈ cell ε k) :
    dist (WithLp.toLp 2 x : EuclideanSpace ℝ (Fin n)) (ptE ε k) ≤ Real.sqrt n * ε := by
  have hsup : dist x (ptR ε k) ≤ ε := by
    refine (dist_pi_le_iff hε.le).mpr fun i => ?_
    obtain ⟨h1, h2⟩ := hx i (Set.mem_univ i)
    rw [Real.dist_eq]; simp only [ptR]
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  calc _ ≤ Real.sqrt n * dist x (ptR ε k) := euclid_le_sqrt_sup x (ptR ε k)
    _ ≤ Real.sqrt n * ε := mul_le_mul_of_nonneg_left hsup (Real.sqrt_nonneg _)

/-- **Covering in the Euclidean norm.** Every position is within Euclidean
distance `√n ε` of a centre (namely that of its owner). -/
theorem cover_euclid {n : ℕ} {ε : ℝ} (hε : 0 < ε) (x : EuclideanSpace ℝ (Fin n)) :
    ∃ k : Fin n → ℤ, dist x (ptE ε k) ≤ Real.sqrt n * ε := by
  refine ⟨owner ε (WithLp.ofLp x), ?_⟩
  have := dist_centre_le_of_mem_cell hε (mem_cell_owner hε (WithLp.ofLp x))
  rwa [WithLp.toLp_ofLp] at this

/-- **Distance to the nearest point-sphere.** For `n ≥ 1`, every position is
within Euclidean distance `(√n - 1) ε` of some point of some point-sphere. -/
theorem near_sphere {n : ℕ} (hn : 1 ≤ n) {ε : ℝ} (hε : 0 < ε)
    (x : EuclideanSpace ℝ (Fin n)) :
    ∃ k : Fin n → ℤ, ∃ y ∈ closedBall (ptE ε k) ε, dist x y ≤ (Real.sqrt n - 1) * ε := by
  obtain ⟨k, hk⟩ := cover_euclid hε x
  have hs1 : 1 ≤ Real.sqrt n := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_le_sqrt (by exact_mod_cast hn)
  set c := ptE ε k
  by_cases hd : dist x c ≤ ε
  · refine ⟨k, x, by rw [mem_closedBall]; exact hd, ?_⟩
    rw [dist_self]; nlinarith
  · push Not at hd
    have hdpos : 0 < dist x c := by linarith
    set t : ℝ := ε / dist x c with ht
    refine ⟨k, AffineMap.lineMap c x t, ?_, ?_⟩
    · rw [mem_closedBall, dist_lineMap_left, Real.norm_eq_abs, dist_comm,
        abs_of_pos (div_pos hε hdpos)]
      rw [div_mul_cancel₀ _ hdpos.ne']
    · rw [dist_comm, dist_lineMap_right, Real.norm_eq_abs, dist_comm]
      have ht1 : t ≤ 1 := by rw [ht, div_le_one hdpos]; exact hd.le
      rw [abs_of_nonneg (by linarith)]
      have : (1 - t) * dist x c = dist x c - ε := by
        rw [ht]; field_simp
      rw [this]; nlinarith

/-- The deep hole `(ε, …, ε)` (a corner of the cell of the origin). -/
noncomputable def deepHole (n : ℕ) (ε : ℝ) : EuclideanSpace ℝ (Fin n) :=
  WithLp.toLp 2 (fun _ => ε)

/-- **Sharpness of the covering radius.** The deep hole is at Euclidean
distance at least `√n ε` from *every* centre. -/
theorem deepHole_far {n : ℕ} {ε : ℝ} (hε : 0 < ε) (k : Fin n → ℤ) :
    Real.sqrt n * ε ≤ dist (deepHole n ε) (ptE ε k) := by
  rw [EuclideanSpace.dist_eq]
  have hs : (n : ℝ) * ε ^ 2 ≤ ∑ i, dist ((deepHole n ε) i) ((ptE ε k) i) ^ 2 := by
    calc (n : ℝ) * ε ^ 2 = ∑ _i : Fin n, ε ^ 2 := by simp
      _ ≤ _ := by
        apply Finset.sum_le_sum
        intro i _
        simp only [deepHole, ptE, ptR, PiLp.toLp_apply, Real.dist_eq, sq_abs]
        have hz : (1 : ℤ) ≤ (1 - 2 * k i) ^ 2 := by
          rcases le_or_gt (k i) 0 with h | h <;> nlinarith
        have hr : (1 : ℝ) ≤ (1 - 2 * (k i : ℝ)) ^ 2 := by exact_mod_cast hz
        have : (ε - 2 * ε * k i) ^ 2 = ε ^ 2 * (1 - 2 * (k i : ℝ)) ^ 2 := by ring
        rw [this]; nlinarith [sq_nonneg ε]
  calc Real.sqrt n * ε = Real.sqrt (n * ε ^ 2) := by
        rw [Real.sqrt_mul (by positivity), Real.sqrt_sq hε.le]
    _ ≤ _ := Real.sqrt_le_sqrt hs

/-- **Gaps exist (n ≥ 2).** The deep hole is
at distance at least `(√n - 1) ε > 0` from every point of every
point-sphere; by `near_sphere` this constant is attained. -/
theorem gap_exists {n : ℕ} (hn : 2 ≤ n) {ε : ℝ} (hε : 0 < ε) :
    0 < (Real.sqrt n - 1) * ε ∧
    ∀ (k : Fin n → ℤ), ∀ y ∈ closedBall (ptE ε k) ε,
      (Real.sqrt n - 1) * ε ≤ dist (deepHole n ε) y := by
  refine ⟨?_, fun k y hy => ?_⟩
  · have : 1 < Real.sqrt n := by
      rw [show (1 : ℝ) = Real.sqrt 1 by simp]
      exact Real.sqrt_lt_sqrt (by norm_num) (by exact_mod_cast hn)
    nlinarith
  · have h1 := deepHole_far hε k
    rw [mem_closedBall] at hy
    have h2 := dist_triangle (deepHole n ε) y (ptE ε k)
    nlinarith

/-! ## The uniform density factor cancels -/

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-- Ball content: each point contributes the volume `ω εⁿ` of the region it
*is*, rather than the volume `(2ε)ⁿ` of the cell it *owns*. -/
def ballContent (n : ℕ) (ω ε : K) (A : Finset (Fin n → ℤ)) : K := ω * ε ^ n * A.card

/-- Ball content is the granular measure times the constant `δ = ω / 2ⁿ`,
the same for every set. -/
theorem ballContent_eq (n : ℕ) (ω ε : K) (A : Finset (Fin n → ℤ)) :
    ballContent n ω ε A = ω / 2 ^ n * QE.muN n ε A := by
  unfold ballContent QE.muN
  rw [mul_pow]; field_simp

/-- **Cancellation in ratios** (relative contents, conditional probabilities,
densities): ball content and cell content give the same ratio. -/
theorem ratio_cancel (n : ℕ) {ω : K} (ε : K) (hω : ω ≠ 0)
    (A B : Finset (Fin n → ℤ)) :
    ballContent n ω ε A / ballContent n ω ε B = QE.muN n ε A / QE.muN n ε B := by
  rw [ballContent_eq, ballContent_eq]
  have : ω / 2 ^ n ≠ 0 := div_ne_zero hω (pow_ne_zero _ two_ne_zero)
  rw [mul_div_mul_left _ _ this]

/-- **Cancellation in averages.** The average of an observable `f` over a
configuration `A` is the same whether points are weighted by ball volume or
by cell volume. -/
theorem average_cancel (n : ℕ) {ω : K} (ε : K) (hω : ω ≠ 0)
    (A : Finset (Fin n → ℤ)) (f : (Fin n → ℤ) → K) :
    (∑ k ∈ A, f k * ballContent n ω ε {k}) / ballContent n ω ε A
      = (∑ k ∈ A, f k * QE.muN n ε {k}) / QE.muN n ε A := by
  simp only [ballContent_eq]
  have : ω / 2 ^ n ≠ 0 := div_ne_zero hω (pow_ne_zero _ two_ne_zero)
  have e : ∑ k ∈ A, f k * (ω / 2 ^ n * QE.muN n ε {k})
      = ω / 2 ^ n * ∑ k ∈ A, f k * QE.muN n ε {k} := by
    rw [Finset.mul_sum]; congr 1; funext k; ring
  rw [e, mul_div_mul_left _ _ this]

/-! ## Classical observables: errors of order `ε` -/

/-- **Per-cell error, one dimension (Lebesgue-free).** Let `F` be an
antiderivative of an `L`-Lipschitz `f` (`F' = f` everywhere). The content
`f(c) · 2ε` that the granular sum assigns to the point at `c` differs from
the classical increment `F(c+ε) - F(c-ε)` across its cell by at most `L ε²`.
No measure or integral is used: the comparison target is the Newton
integral, and the proof is a monotonicity argument. -/
theorem cell_error_newton {ε : ℝ} (hε : 0 < ε) (f F : ℝ → ℝ)
    (hF : ∀ x, HasDerivAt F (f x) x) (L : ℝ)
    (hL : ∀ x y, |f x - f y| ≤ L * |x - y|) (c : ℝ) :
    |f c * (2 * ε) - (F (c + ε) - F (c - ε))| ≤ L * ε ^ 2 := by
  set g : ℝ → ℝ := fun t => F (c + t) - F (c - t) - 2 * t * f c with hg
  have hgd : ∀ t, HasDerivAt g (f (c + t) + f (c - t) - 2 * f c) t := by
    intro t
    have h1 : HasDerivAt (fun t => F (c + t)) (f (c + t)) t := by
      exact HasDerivAt.comp_const_add c t (hF (c + t))
    have h2 : HasDerivAt (fun t => F (c - t)) (-f (c - t)) t := by
      exact HasDerivAt.comp_const_sub c t (hF (c - t))
    have h3 : HasDerivAt (fun t => 2 * t * f c) (2 * f c) t := by
      have := ((hasDerivAt_id t).const_mul 2).mul_const (f c)
      simpa using this
    have := (h1.sub h2).sub h3
    convert this using 1; ring
  have hbd : ∀ t, 0 ≤ t → |f (c + t) + f (c - t) - 2 * f c| ≤ 2 * L * t := by
    intro t ht
    have a1 := hL (c + t) c
    have a2 := hL (c - t) c
    rw [show c + t - c = t by ring, abs_of_nonneg ht] at a1
    rw [show c - t - c = -t by ring, abs_neg, abs_of_nonneg ht] at a2
    calc _ = |(f (c + t) - f c) + (f (c - t) - f c)| := by ring_nf
      _ ≤ |f (c + t) - f c| + |f (c - t) - f c| := abs_add_le _ _
      _ ≤ 2 * L * t := by linarith
  have hsq : ∀ t, HasDerivAt (fun t => L * t ^ 2) (2 * L * t) t := by
    intro t
    have := (hasDerivAt_pow 2 t).const_mul L
    convert this using 1; push_cast; ring
  have hint : interior (Set.Ici (0 : ℝ)) = Set.Ioi 0 := interior_Ici
  -- `L t² - g t` and `L t² + g t` are monotone on `[0, ∞)`
  have m1 : MonotoneOn (fun t => L * t ^ 2 - g t) (Set.Ici 0) := by
    refine monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ici 0)
      (fun t _ => ((hsq t).sub (hgd t)).continuousAt.continuousWithinAt)
      (fun t _ => ((hsq t).sub (hgd t)).hasDerivWithinAt) ?_
    intro t ht
    rw [hint] at ht
    have := abs_le.mp (hbd t (le_of_lt ht))
    linarith [this.2]
  have m2 : MonotoneOn (fun t => L * t ^ 2 + g t) (Set.Ici 0) := by
    refine monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ici 0)
      (fun t _ => ((hsq t).add (hgd t)).continuousAt.continuousWithinAt)
      (fun t _ => ((hsq t).add (hgd t)).hasDerivWithinAt) ?_
    intro t ht
    rw [hint] at ht
    have := abs_le.mp (hbd t (le_of_lt ht))
    linarith [this.1]
  have g0 : g 0 = 0 := by simp [hg]
  have e1 := m1 (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr hε.le) hε.le
  have e2 := m2 (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr hε.le) hε.le
  simp only [g0] at e1 e2
  have hgε : g ε = F (c + ε) - F (c - ε) - 2 * ε * f c := rfl
  rw [hgε] at e1 e2
  rw [abs_le]; constructor <;> nlinarith

/-- **Summed error, one dimension (Lebesgue-free).** Over `m` consecutive
cells starting at the centre `a`, the granular sum differs from the classical
increment `F(b) - F(a - ε)` of an antiderivative across the union of the cells
(`b = a - ε + 2εm`) by at most `L ε² m = (L ε / 2) × length`. -/
theorem cells_error_newton {ε : ℝ} (hε : 0 < ε) (f F : ℝ → ℝ)
    (hF : ∀ x, HasDerivAt F (f x) x) (L : ℝ)
    (hL : ∀ x y, |f x - f y| ≤ L * |x - y|) (a : ℝ) (m : ℕ) :
    |∑ k ∈ Finset.range m, f (a + 2 * ε * k) * (2 * ε)
        - (F (a - ε + 2 * ε * m) - F (a - ε))| ≤ L * ε ^ 2 * m := by
  have tele := Finset.sum_range_sub (fun k : ℕ => F (a - ε + 2 * ε * k)) m
  simp only [Nat.cast_zero, mul_zero, add_zero] at tele
  rw [← tele, ← Finset.sum_sub_distrib]
  calc _ ≤ ∑ k ∈ Finset.range m, |f (a + 2 * ε * k) * (2 * ε)
          - (F (a - ε + 2 * ε * ((k + 1 : ℕ) : ℝ)) - F (a - ε + 2 * ε * k))| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _k ∈ Finset.range m, L * ε ^ 2 := by
        apply Finset.sum_le_sum
        intro k _
        have e1 : a - ε + 2 * ε * ((k + 1 : ℕ) : ℝ) = (a + 2 * ε * k) + ε := by push_cast; ring
        have e2 : a - ε + 2 * ε * (k : ℝ) = (a + 2 * ε * k) - ε := by ring
        rw [e1, e2]
        exact cell_error_newton hε f F hF L hL _
    _ = L * ε ^ 2 * m := by simp; ring

/-- **Classical observables of a configuration (Lebesgue-free).** Replacing
every position `x_j` of a weighted configuration by the centre of its owner
changes the weighted sum `∑ w_j f(x_j)` of an `L`-Lipschitz observable by at
most `L √n ε ∑ w_j`. -/
theorem config_snap_error {n : ℕ} {ε : ℝ} (hε : 0 < ε) {ι : Type*} (J : Finset ι)
    (x : ι → EuclideanSpace ℝ (Fin n)) (w : ι → ℝ) (hw : ∀ j ∈ J, 0 ≤ w j)
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (L : ℝ) (hL0 : 0 ≤ L)
    (hL : ∀ p q, |f p - f q| ≤ L * dist p q) :
    |∑ j ∈ J, w j * f (x j) - ∑ j ∈ J, w j * f (ptE ε (owner ε (WithLp.ofLp (x j))))|
      ≤ L * Real.sqrt n * ε * ∑ j ∈ J, w j := by
  rw [← Finset.sum_sub_distrib, Finset.mul_sum]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j hj => ?_)
  have hd := dist_centre_le_of_mem_cell hε (mem_cell_owner hε (WithLp.ofLp (x j)))
  rw [WithLp.toLp_ofLp] at hd
  rw [← mul_sub, abs_mul, abs_of_nonneg (hw j hj)]
  have := (hL (x j) _).trans (mul_le_mul_of_nonneg_left hd hL0)
  calc w j * |f (x j) - f (ptE ε (owner ε (WithLp.ofLp (x j))))|
      ≤ w j * (L * (Real.sqrt n * ε)) := mul_le_mul_of_nonneg_left this (hw j hj)
    _ = L * Real.sqrt n * ε * w j := by ring

/-! ## Shadow comparisons (classical Lebesgue target; lossy)

The lemmas in this block, and only these, use Lebesgue measure and the
Lebesgue integral: they compare the granular sums with the classical
integral, which is the lossy shadow target.  No granular statement depends on
them. -/

/-- Each cell has volume `(2ε)ⁿ`. -/
theorem volume_cell_shadow {n : ℕ} {ε : ℝ} (hε : 0 ≤ ε) (k : Fin n → ℤ) :
    volume (cell ε k) = ENNReal.ofReal ((2 * ε) ^ n) := by
  unfold cell
  rw [Real.volume_pi_Ico]
  have h : ∀ i : Fin n, ENNReal.ofReal (2 * ε * k i + ε - (2 * ε * k i - ε))
      = ENNReal.ofReal (2 * ε) := fun i => by congr 1; ring
  simp only [h, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [← ENNReal.ofReal_pow (by linarith)]

theorem measureReal_cell_shadow {n : ℕ} {ε : ℝ} (hε : 0 ≤ ε) (k : Fin n → ℤ) :
    volume.real (cell ε k) = (2 * ε) ^ n := by
  rw [measureReal_def, volume_cell_shadow hε, ENNReal.toReal_ofReal (by positivity)]

theorem measurableSet_cell_shadow {n : ℕ} (ε : ℝ) (k : Fin n → ℤ) : MeasurableSet (cell ε k) :=
  MeasurableSet.univ_pi fun _ => measurableSet_Ico

/-! ### Classical packing densities (shadow level) -/

/-- Volume of the unit ball of `ℝⁿ`, `ω_n = π^{n/2} / Γ(n/2 + 1)`. -/
noncomputable def omegaShadow (n : ℕ) : ℝ := Real.sqrt Real.pi ^ n / Real.Gamma (n / 2 + 1)

theorem omegaShadow_pos (n : ℕ) : 0 < omegaShadow n := by
  unfold omegaShadow
  have : 0 < Real.Gamma (n / 2 + 1) := Real.Gamma_pos_of_pos (by positivity)
  have : 0 < Real.sqrt Real.pi := Real.sqrt_pos.mpr Real.pi_pos
  positivity

/-- **The packing density is scale invariant.** For every `ε > 0` the ratio
of the volume of a point-sphere to the volume of its cell is `ω_n / 2ⁿ`. -/
theorem density_scale_invariant_shadow (n : ℕ) [NeZero n] {ε : ℝ} (hε : 0 < ε) :
    (volume (ball (0 : EuclideanSpace ℝ (Fin n)) ε)).toReal / (2 * ε) ^ n
      = omegaShadow n / 2 ^ n := by
  have hω := (omegaShadow_pos n).le
  unfold omegaShadow at hω ⊢
  rw [EuclideanSpace.volume_ball, Fintype.card_fin, ENNReal.toReal_mul,
    ENNReal.toReal_pow, ENNReal.toReal_ofReal hε.le,
    ENNReal.toReal_ofReal hω]
  rw [mul_pow]
  have : ε ^ n ≠ 0 := pow_ne_zero _ hε.ne'
  field_simp

/-- Two scales give the same packing density: shrinking `ε` does not shrink
the gap fraction. -/
theorem density_indep_shadow (n : ℕ) [NeZero n] {ε ε' : ℝ} (hε : 0 < ε) (hε' : 0 < ε') :
    (volume (ball (0 : EuclideanSpace ℝ (Fin n)) ε)).toReal / (2 * ε) ^ n
      = (volume (ball (0 : EuclideanSpace ℝ (Fin n)) ε')).toReal / (2 * ε') ^ n := by
  rw [density_scale_invariant_shadow n hε, density_scale_invariant_shadow n hε']

/-- Square lattice in the plane: the discs cover the fraction `π/4 < 1` of
every cell, at every scale; the gap fraction `1 - π/4` is positive. -/
theorem square_density_shadow {ε : ℝ} (hε : 0 < ε) :
    Real.pi * ε ^ 2 / (2 * ε) ^ 2 = Real.pi / 4 ∧ Real.pi / 4 < 1 ∧
      0 < 1 - Real.pi * ε ^ 2 / (2 * ε) ^ 2 := by
  have h : Real.pi * ε ^ 2 / (2 * ε) ^ 2 = Real.pi / 4 := by
    have : ε ≠ 0 := hε.ne'
    field_simp; ring
  have h4 := Real.pi_lt_four
  exact ⟨h, by linarith, by rw [h]; linarith⟩

/-- Cubic lattice in space: density `π/6 < 1`; FCC (Kepler optimum)
`π/(3√2) < 1`. -/
theorem cubic_fcc_lt_one_shadow : Real.pi / 6 < 1 ∧ Real.pi / (3 * Real.sqrt 2) < 1 := by
  have h4 := Real.pi_lt_four
  refine ⟨by linarith, ?_⟩
  have hs : (4 : ℝ) / 3 < Real.sqrt 2 := by
    rw [show (4 : ℝ) / 3 = Real.sqrt ((4 / 3) ^ 2) by rw [Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  rw [div_lt_one (by positivity)]
  linarith [Real.pi_lt_d2]

/-- **Per-cell error, `n` dimensions.** If `f` is continuous and varies by at
most `η` over the cell of `k`, the content `f(c_k)(2ε)ⁿ` differs from
`∫_{cell} f` by at most `η (2ε)ⁿ`. -/
theorem cell_error_n_shadow {n : ℕ} {ε : ℝ} (hε : 0 < ε) (f : (Fin n → ℝ) → ℝ)
    (hf : Continuous f) (k : Fin n → ℤ) (η : ℝ)
    (hη : ∀ x ∈ cell ε k, |f x - f (ptR ε k)| ≤ η) :
    |f (ptR ε k) * (2 * ε) ^ n - ∫ x in cell ε k, f x| ≤ η * (2 * ε) ^ n := by
  have hsub : cell ε k ⊆ Set.Icc (fun i => 2 * ε * k i - ε) (fun i => 2 * ε * k i + ε) := by
    intro x hx
    refine ⟨fun i => (hx i (Set.mem_univ i)).1, fun i => (hx i (Set.mem_univ i)).2.le⟩
  have hint : IntegrableOn f (cell ε k) volume :=
    (hf.continuousOn.integrableOn_Icc).mono_set hsub
  have hfin : volume (cell ε k) < ⊤ := by rw [volume_cell_shadow hε.le]; exact ENNReal.ofReal_lt_top
  have e : (∫ x in cell ε k, f x) - f (ptR ε k) * (2 * ε) ^ n
      = ∫ x in cell ε k, (f x - f (ptR ε k)) := by
    rw [integral_sub hint (integrableOn_const hfin.ne), setIntegral_const,
      measureReal_cell_shadow hε.le, smul_eq_mul, mul_comm]
  rw [abs_sub_comm, e, ← Real.norm_eq_abs, ← measureReal_cell_shadow hε.le k]
  exact norm_setIntegral_le_of_norm_le_const hfin fun x hx => by
    rw [Real.norm_eq_abs]; exact hη x hx

/-- **Lipschitz observables, `n` dimensions.** If `f` is `L`-Lipschitz for
the Euclidean distance, the per-cell error is at most `L √n ε (2ε)ⁿ`. -/
theorem cell_error_lipschitz_shadow {n : ℕ} {ε : ℝ} (hε : 0 < ε) (f : (Fin n → ℝ) → ℝ)
    (hf : Continuous f) (L : ℝ) (hL0 : 0 ≤ L)
    (hL : ∀ x y, |f x - f y| ≤ L * dist (WithLp.toLp 2 x : EuclideanSpace ℝ (Fin n))
      (WithLp.toLp 2 y)) (k : Fin n → ℤ) :
    |f (ptR ε k) * (2 * ε) ^ n - ∫ x in cell ε k, f x|
      ≤ L * Real.sqrt n * ε * (2 * ε) ^ n := by
  refine cell_error_n_shadow hε f hf k _ fun x hx => ?_
  calc |f x - f (ptR ε k)| ≤ L * dist (WithLp.toLp 2 x : EuclideanSpace ℝ (Fin n))
        (WithLp.toLp 2 (ptR ε k)) := hL _ _
    _ ≤ L * (Real.sqrt n * ε) :=
        mul_le_mul_of_nonneg_left (dist_centre_le_of_mem_cell hε hx) hL0
    _ = L * Real.sqrt n * ε := by ring

/-- **Classical-observable theorem (integrals).** For a finite configuration
`A` and an observable varying by at most `η` on each of its cells, the
granular sum `∑_{k∈A} f(c_k)(2ε)ⁿ` differs from the integral of `f` over the
union of the cells by at most `η · μ_ε(A)`. -/
theorem config_error_shadow {n : ℕ} {ε : ℝ} (hε : 0 < ε) (f : (Fin n → ℝ) → ℝ)
    (hf : Continuous f) (A : Finset (Fin n → ℤ)) (η : ℝ)
    (hη : ∀ k ∈ A, ∀ x ∈ cell ε k, |f x - f (ptR ε k)| ≤ η) :
    |∑ k ∈ A, f (ptR ε k) * (2 * ε) ^ n - ∫ x in ⋃ k ∈ A, cell ε k, f x|
      ≤ η * QE.muN n ε A := by
  have hdisj : Set.Pairwise (A : Set (Fin n → ℤ)) (Function.onFun Disjoint fun k => cell ε k) := by
    intro k _ j _ hkj
    simp only [Function.onFun]
    rw [Set.disjoint_left]
    intro x hk hj
    exact hkj ((eq_owner_of_mem_cell hε hk).trans (eq_owner_of_mem_cell hε hj).symm)
  have hint : ∀ k ∈ A, IntegrableOn f (cell ε k) volume := by
    intro k _
    have hsub : cell ε k ⊆ Set.Icc (fun i => 2 * ε * k i - ε) (fun i => 2 * ε * k i + ε) :=
      fun x hx => ⟨fun i => (hx i (Set.mem_univ i)).1, fun i => (hx i (Set.mem_univ i)).2.le⟩
    exact (hf.continuousOn.integrableOn_Icc).mono_set hsub
  rw [integral_biUnion_finset A (fun k _ => measurableSet_cell_shadow ε k) hdisj hint,
    ← Finset.sum_sub_distrib]
  calc _ ≤ ∑ k ∈ A, |f (ptR ε k) * (2 * ε) ^ n - ∫ x in cell ε k, f x| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _k ∈ A, η * (2 * ε) ^ n :=
        Finset.sum_le_sum fun k hk => cell_error_n_shadow hε f hf k η (hη k hk)
    _ = η * QE.muN n ε A := by unfold QE.muN; simp; ring

/-- **Classical-observable theorem (distances).** Replacing two positions by
the centres of their owners changes their Euclidean distance by at most
`2 √n ε`. -/
theorem dist_error {n : ℕ} {ε : ℝ} (hε : 0 < ε) (x y : EuclideanSpace ℝ (Fin n)) :
    ∃ k j : Fin n → ℤ, |dist x y - dist (ptE ε k) (ptE ε j)| ≤ 2 * Real.sqrt n * ε := by
  obtain ⟨k, hk⟩ := cover_euclid hε x
  obtain ⟨j, hj⟩ := cover_euclid hε y
  refine ⟨k, j, ?_⟩
  have := dist_dist_dist_le x y (ptE ε k) (ptE ε j)
  rw [Real.dist_eq] at this
  linarith

/-- **Worked example: sandwich of a ball by cells.** If `x` lies in the cell
of `k` and `‖x‖ ≤ R - √n ε`, the centre of `k` lies in the closed ball of
radius `R`; if the centre lies in that ball, then `‖x‖ ≤ R + √n ε`. -/
theorem cells_sandwich {n : ℕ} {ε : ℝ} (hε : 0 < ε) {x : Fin n → ℝ} {k : Fin n → ℤ}
    (hx : x ∈ cell ε k) (R : ℝ) :
    (‖(WithLp.toLp 2 x : EuclideanSpace ℝ (Fin n))‖ ≤ R - Real.sqrt n * ε →
        ‖ptE ε k‖ ≤ R) ∧
    (‖ptE ε k‖ ≤ R →
        ‖(WithLp.toLp 2 x : EuclideanSpace ℝ (Fin n))‖ ≤ R + Real.sqrt n * ε) := by
  have h := dist_centre_le_of_mem_cell hε hx
  rw [dist_eq_norm] at h
  have t1 := norm_sub_norm_le (ptE ε k) (WithLp.toLp 2 x : EuclideanSpace ℝ (Fin n))
  have t2 := norm_sub_norm_le (WithLp.toLp 2 x : EuclideanSpace ℝ (Fin n)) (ptE ε k)
  rw [norm_sub_rev] at t1
  constructor <;> intro hR <;> linarith

/-! ## Informational observables: where `ε` survives -/

/-- **The dichotomy, counting side.** The content of a singleton is
`(2ε)ⁿ ≠ 0`, while the empty configuration has content `0`: the difference
is the *whole* content of the singleton (relative error `1`), not a small
fraction of it. -/
theorem singleton_not_negligible (n : ℕ) {ε : K} (hε : 0 < ε) (k : Fin n → ℤ) :
    QE.muN n ε {k} - QE.muN n ε ∅ = (2 * ε) ^ n ∧
    (QE.muN n ε {k} - QE.muN n ε ∅) / QE.muN n ε {k} = 1 ∧
    0 < QE.muN n ε {k} := by
  have hp : 0 < (2 * ε) ^ n := pow_pos (by linarith) n
  have e2 : QE.muN n ε {k} = (2 * ε) ^ n := by simp [QE.muN]
  have e : QE.muN n ε {k} - QE.muN n ε ∅ = (2 * ε) ^ n := by simp [QE.muN]
  exact ⟨e, by rw [e, e2, div_self hp.ne'], by rw [e2]; exact hp⟩

/-- **The endpoint bit.** Closing a lattice interval on the right adds
exactly one point, i.e. exactly `2ε` of content. -/
theorem endpoint_bit (ε : K) {a b : ℤ} (hab : a ≤ b) :
    QE.mu ε (Finset.Icc a b) - QE.mu ε (Finset.Ico a b) = 2 * ε := by
  unfold QE.mu
  rw [Int.card_Icc, Int.card_Ico]
  have h1 : ((b + 1 - a).toNat : K) = ((b + 1 - a : ℤ) : K) := by
    rw [← Int.cast_natCast, Int.toNat_of_nonneg (by omega)]
  have h2 : ((b - a).toNat : K) = ((b - a : ℤ) : K) := by
    rw [← Int.cast_natCast, Int.toNat_of_nonneg (by omega)]
  rw [h1, h2]; push_cast; ring

end QE.Packing
