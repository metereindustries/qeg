-- SPDX-License-Identifier: MIT
-- Copyright 2026 Metere Industries, Inc. Author: Alfredo Metere.
-- Quasi-Euclidean Granular Geometry. Any derivative work must carry this notice:
--   This work is derivative of the Quasi-Euclidean Granular Geometry book
--   authored by Alfredo Metere. Copyright 2026 Metere Industries, Inc.
--   All rights reserved
-- See LICENSE.md and NOTICE.

import Mathlib
import QuasiEuclidean.OpenSto
import QuasiEuclidean.Ch02_Hyper

/-!
# Fourier infrastructure: lattice points in curved bodies, polytopes, free-field shadows

Shadow results (they use Lebesgue measure, the Fourier transform and limits; book tag
`\leanshadowref`).

* **Poisson summation on `ℝⁿ`** (`poisson`) for continuous compactly supported functions with
  summable Fourier transform on `ℤⁿ`, via the torus Fourier series of the periodization.
* **Fourier decay of the ball** (`ball_fourier_decay`): `|1̂_B(ξ)| ≤ A|ξ|^{-(n+1)/2}`, from the
  slicing formula `slice` (rotation invariance + Fubini) and the one-dimensional endpoint
  estimate `decay1` for `∫_{-1}^1 (1-s²)^β e(-λs) ds`.
* **Hlawka's uniform lattice-point bound** (`hlawka_core`, `hlawka_of_decay`): for a convex body
  with Herz's decay bound, `|#((tgC+v)∩ℤⁿ) - tⁿ|det g| vol C| ≤ c t^{n-2+2/(n+1)}` uniformly for
  `g` in a compact subset of `GL_n` and all `v`; proof by smoothing (`smooth`, a scaled bump
  `bump`), convex sandwiching (`sandwich_upper/lower`), Poisson summation and the lattice sum
  `latsum`.  For ellipsoids it is unconditional (`hlawka_ellipsoid`).
* **Isotropy** (`smooth_isotropy_ellipsoid`, `smooth_isotropy_of_decay`, `isotropy_hyper`) and
  the **polytope no-go theorem** (`Polytope.polytope_nogo`, Haar average over `SO(n)` in
  `Polytope.polytope_average`).
* **Field shadows**: value-lattice Riemann sums (`ValueLattice.value_lattice_shadow`), Gaussian
  moments equal the Wick functional (`ValueLattice.gaussian_moment`), and the lattice free
  field covariance converges to the continuum one (`FreeField.free_field_shadow`).
-/

open MeasureTheory Real Complex Filter Topology
open scoped FourierTransform RealInnerProductSpace Convolution ContDiff

noncomputable section
namespace QE.FourierInfra

/-- integer point of `ℝⁿ`. -/
def zpt {n : ℕ} (k : Fin n → ℤ) : EuclideanSpace ℝ (Fin n) :=
  (EuclideanSpace.equiv (Fin n) ℝ).symm (fun i => (k i : ℝ))

-- ==== Affine.lean ====

namespace AffineAux

theorem abs_det_smul {n : ℕ} (t : ℝ) (ht : 0 < t)
    (g : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) :
    |LinearMap.det ((t • g : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) :
        EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin n))| =
      t ^ n * |LinearMap.det (g : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin n))| := by
  rw [ContinuousLinearMap.toLinearMap_smul, LinearMap.det_smul, finrank_euclideanSpace_fin, abs_mul,
    abs_pow, abs_of_pos ht]

end AffineAux

theorem vol_affine {n : ℕ} (C : Set (EuclideanSpace ℝ (Fin n)))
    (t : ℝ) (ht : 0 < t) (g : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (v : EuclideanSpace ℝ (Fin n)) :
    volume ((fun x => t • g x + v) '' C) =
      ENNReal.ofReal (t ^ n * |LinearMap.det (g : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin n))|) * volume C := by
  have h : (fun x => t • g x + v) '' C = (fun y => y + v) '' ((t • g) '' C) := by
    rw [Set.image_image]; rfl
  rw [h, Set.image_add_right, measure_preimage_add_right,
    Measure.addHaar_image_continuousLinearMap, AffineAux.abs_det_smul t ht g]

theorem fourier_affine {n : ℕ} (C : Set (EuclideanSpace ℝ (Fin n))) (hC : MeasurableSet C)
    (t : ℝ) (ht : 0 < t) (g : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (hg : LinearMap.det (g : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin n)) ≠ 0)
    (v ξ : EuclideanSpace ℝ (Fin n)) :
    𝓕 (((fun x => t • g x + v) '' C).indicator (1 : EuclideanSpace ℝ (Fin n) → ℂ)) ξ =
      (𝐞 (-⟪v, ξ⟫) : ℂ) * (((t ^ n * |LinearMap.det (g : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin n))| : ℝ) : ℂ) *
        𝓕 (C.indicator (1 : EuclideanSpace ℝ (Fin n) → ℂ)) (t • (ContinuousLinearMap.adjoint g) ξ)) := by
  set A : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) := fun x => t • g x + v with hA
  have hder : ∀ x ∈ C, HasFDerivWithinAt A (t • g) C x := by
    intro x _
    have : HasFDerivAt (fun x => (t • g) x + v) (t • g) x := (t • g).hasFDerivAt.add_const v
    exact this.hasFDerivWithinAt
  have ginj : Function.Injective g :=
    ((Module.End.isUnit_iff _).1 ((LinearMap.isUnit_iff_isUnit_det _).2
      (isUnit_iff_ne_zero.2 hg))).1
  have hinj : Set.InjOn A C := by
    intro x _ y _ hxy
    simp only [hA, add_left_inj] at hxy
    exact ginj (smul_right_injective _ ht.ne' hxy)
  have hmeas : MeasurableSet (A '' C) := measurable_image_of_fderivWithin hC hder hinj
  have key : ∀ (s : Set (EuclideanSpace ℝ (Fin n))) (ζ : EuclideanSpace ℝ (Fin n)),
      MeasurableSet s → 𝓕 (s.indicator (1 : EuclideanSpace ℝ (Fin n) → ℂ)) ζ =
        ∫ x in s, (𝐞 (-⟪x, ζ⟫) : ℂ) := by
    intro s ζ hs
    rw [Real.fourier_eq, ← integral_indicator hs]
    congr 1; funext x
    by_cases hx : x ∈ s <;> simp [hx, Circle.smul_def]
  rw [key _ _ hmeas, key _ _ hC,
    integral_image_eq_integral_abs_det_fderiv_smul volume hC hder hinj]
  rw [← integral_const_mul, ← integral_const_mul]
  refine setIntegral_congr_fun hC (fun x _ => ?_)
  simp only [hA]
  rw [ContinuousLinearMap.det, AffineAux.abs_det_smul t ht g, inner_add_left, inner_smul_left,
    inner_smul_right, ← ContinuousLinearMap.adjoint_inner_right, neg_add, AddChar.map_add_eq_mul,
    Circle.coe_mul, Complex.real_smul]
  simp only [RCLike.conj_to_real]
  ring

/-- `1_K ⋆ φ`, complex valued. -/
def smooth {n : ℕ} (K : Set (EuclideanSpace ℝ (Fin n))) (φ : EuclideanSpace ℝ (Fin n) → ℝ) :
    EuclideanSpace ℝ (Fin n) → ℂ :=
  (K.indicator (1 : EuclideanSpace ℝ (Fin n) → ℂ)) ⋆[ContinuousLinearMap.mul ℂ ℂ] (fun x => (φ x : ℂ))


namespace AffineAux

theorem smooth_eq {n : ℕ} (K : Set (EuclideanSpace ℝ (Fin n))) (φ : EuclideanSpace ℝ (Fin n) → ℝ)
    (x : EuclideanSpace ℝ (Fin n)) :
    smooth K φ x = ((∫ y, K.indicator (1 : EuclideanSpace ℝ (Fin n) → ℝ) y * φ (x - y) : ℝ) : ℂ) := by
  rw [smooth, convolution_def, ← integral_complex_ofReal]
  congr 1; funext y
  by_cases hy : y ∈ K <;> simp [hy]

theorem integrable_of_integral_eq_one {n : ℕ} {φ : EuclideanSpace ℝ (Fin n) → ℝ}
    (hφ1 : ∫ x, φ x = 1) : Integrable φ := by
  by_contra h
  rw [integral_undef h] at hφ1
  exact zero_ne_one hφ1

theorem integrable_indicator_one {n : ℕ} {K : Set (EuclideanSpace ℝ (Fin n))}
    (hK : MeasurableSet K) (hKb : Bornology.IsBounded K) :
    Integrable (K.indicator (1 : EuclideanSpace ℝ (Fin n) → ℂ)) := by
  rw [integrable_indicator_iff hK]
  exact integrableOn_const hKb.measure_lt_top.ne

theorem hasCompactSupport_ofReal {n : ℕ} {φ : EuclideanSpace ℝ (Fin n) → ℝ} {δ : ℝ}
    (hφs : ∀ x, φ x ≠ 0 → ‖x‖ ≤ δ) : HasCompactSupport (fun x => (φ x : ℂ)) := by
  refine HasCompactSupport.intro (isCompact_closedBall (0 : EuclideanSpace ℝ (Fin n)) δ) ?_
  intro x hx
  by_contra h
  apply hx
  rw [Metric.mem_closedBall, dist_zero_right]
  exact hφs x (by exact_mod_cast h)

theorem integrand_nonneg {n : ℕ} (K : Set (EuclideanSpace ℝ (Fin n))) {φ : EuclideanSpace ℝ (Fin n) → ℝ}
    (hφ0 : ∀ x, 0 ≤ φ x) (x y : EuclideanSpace ℝ (Fin n)) :
    0 ≤ K.indicator (1 : EuclideanSpace ℝ (Fin n) → ℝ) y * φ (x - y) :=
  mul_nonneg (Set.indicator_nonneg (fun _ _ => zero_le_one) _) (hφ0 _)

end AffineAux

theorem smooth_continuous {n : ℕ} (K : Set (EuclideanSpace ℝ (Fin n))) (hK : MeasurableSet K)
    (φ : EuclideanSpace ℝ (Fin n) → ℝ) (hφc : Continuous φ) (δ : ℝ)
    (hφs : ∀ x, φ x ≠ 0 → ‖x‖ ≤ δ) : Continuous (smooth K φ) := by
  refine (AffineAux.hasCompactSupport_ofReal hφs).continuous_convolution_right _ ?_ (by fun_prop)
  exact (locallyIntegrable_const (1 : ℂ)).indicator hK

theorem smooth_hasCompactSupport {n : ℕ} (K : Set (EuclideanSpace ℝ (Fin n)))
    (hKb : Bornology.IsBounded K) (φ : EuclideanSpace ℝ (Fin n) → ℝ) (δ : ℝ)
    (hφs : ∀ x, φ x ≠ 0 → ‖x‖ ≤ δ) : HasCompactSupport (smooth K φ) := by
  refine HasCompactSupport.convolution _ ?_ (AffineAux.hasCompactSupport_ofReal hφs)
  exact hKb.isCompact_closure.of_isClosed_subset isClosed_closure
    (closure_mono Set.support_indicator_subset)

theorem smooth_real {n : ℕ} (K : Set (EuclideanSpace ℝ (Fin n))) (φ : EuclideanSpace ℝ (Fin n) → ℝ)
    (x : EuclideanSpace ℝ (Fin n)) : smooth K φ x = (((smooth K φ x).re : ℝ) : ℂ) := by
  rw [AffineAux.smooth_eq, Complex.ofReal_re]

theorem smooth_re_nonneg {n : ℕ} (K : Set (EuclideanSpace ℝ (Fin n)))
    (φ : EuclideanSpace ℝ (Fin n) → ℝ) (hφ0 : ∀ x, 0 ≤ φ x) (x : EuclideanSpace ℝ (Fin n)) :
    0 ≤ (smooth K φ x).re := by
  rw [AffineAux.smooth_eq, Complex.ofReal_re]
  exact integral_nonneg (AffineAux.integrand_nonneg K hφ0 x)

theorem smooth_re_le_one {n : ℕ} (K : Set (EuclideanSpace ℝ (Fin n)))
    (φ : EuclideanSpace ℝ (Fin n) → ℝ) (hφ0 : ∀ x, 0 ≤ φ x) (hφ1 : ∫ x, φ x = 1)
    (x : EuclideanSpace ℝ (Fin n)) : (smooth K φ x).re ≤ 1 := by
  rw [AffineAux.smooth_eq, Complex.ofReal_re]
  have hint : Integrable (fun y => φ (x - y)) :=
    (AffineAux.integrable_of_integral_eq_one hφ1).comp_sub_left x
  calc ∫ y, K.indicator (1 : EuclideanSpace ℝ (Fin n) → ℝ) y * φ (x - y)
      ≤ ∫ y, φ (x - y) := by
        refine integral_mono_of_nonneg (Eventually.of_forall (AffineAux.integrand_nonneg K hφ0 x))
          hint (Eventually.of_forall fun y => ?_)
        by_cases hy : y ∈ K <;> simp [hy, hφ0]
    _ = 1 := by rw [integral_sub_left_eq_self (fun y => φ y) volume x, hφ1]

theorem smooth_ge_indicator {n : ℕ} (K K' : Set (EuclideanSpace ℝ (Fin n)))
    (φ : EuclideanSpace ℝ (Fin n) → ℝ) (hφ0 : ∀ x, 0 ≤ φ x) (δ : ℝ)
    (hφs : ∀ x, φ x ≠ 0 → ‖x‖ ≤ δ) (hφ1 : ∫ x, φ x = 1)
    (h : ∀ y ∈ K, ∀ w, ‖w‖ ≤ δ → y + w ∈ K') (x : EuclideanSpace ℝ (Fin n)) :
    K.indicator (1 : EuclideanSpace ℝ (Fin n) → ℝ) x ≤ (smooth K' φ x).re := by
  by_cases hx : x ∈ K
  · rw [Set.indicator_of_mem hx, Pi.one_apply, AffineAux.smooth_eq, Complex.ofReal_re]
    have : (fun y => K'.indicator (1 : EuclideanSpace ℝ (Fin n) → ℝ) y * φ (x - y)) =
        fun y => φ (x - y) := by
      funext y
      by_cases hφy : φ (x - y) = 0
      · simp [hφy]
      · have hy : y ∈ K' := by
          have := h x hx (y - x) (by rw [← norm_neg, neg_sub]; exact hφs _ hφy)
          simpa using this
        simp [hy]
    rw [this, integral_sub_left_eq_self (fun y => φ y) volume x, hφ1]
  · rw [Set.indicator_of_notMem hx]
    exact smooth_re_nonneg K' φ hφ0 x

theorem smooth_le_indicator {n : ℕ} (K K'' : Set (EuclideanSpace ℝ (Fin n)))
    (φ : EuclideanSpace ℝ (Fin n) → ℝ) (hφ0 : ∀ x, 0 ≤ φ x) (δ : ℝ)
    (hφs : ∀ x, φ x ≠ 0 → ‖x‖ ≤ δ) (hφ1 : ∫ x, φ x = 1)
    (h : ∀ y ∈ K'', ∀ w, ‖w‖ ≤ δ → y + w ∈ K) (x : EuclideanSpace ℝ (Fin n)) :
    (smooth K'' φ x).re ≤ K.indicator (1 : EuclideanSpace ℝ (Fin n) → ℝ) x := by
  by_cases hx : x ∈ K
  · rw [Set.indicator_of_mem hx, Pi.one_apply]
    exact smooth_re_le_one K'' φ hφ0 hφ1 x
  · rw [Set.indicator_of_notMem hx, AffineAux.smooth_eq, Complex.ofReal_re]
    have : (fun y => K''.indicator (1 : EuclideanSpace ℝ (Fin n) → ℝ) y * φ (x - y)) =
        fun _ => 0 := by
      funext y
      by_cases hφy : φ (x - y) = 0
      · simp [hφy]
      · have hy : y ∉ K'' := by
          intro hy
          apply hx
          simpa using h y hy (x - y) (hφs _ hφy)
        simp [hy]
    rw [this, integral_zero]

theorem fourier_smooth {n : ℕ} (K : Set (EuclideanSpace ℝ (Fin n))) (hK : MeasurableSet K)
    (hKb : Bornology.IsBounded K) (φ : EuclideanSpace ℝ (Fin n) → ℝ) (hφ1 : ∫ x, φ x = 1)
    (ξ : EuclideanSpace ℝ (Fin n)) :
    𝓕 (smooth K φ) ξ =
      𝓕 (K.indicator (1 : EuclideanSpace ℝ (Fin n) → ℂ)) ξ * 𝓕 (fun x => (φ x : ℂ)) ξ :=
  Real.fourier_mul_convolution_eq (AffineAux.integrable_indicator_one hK hKb)
    (AffineAux.integrable_of_integral_eq_one hφ1).ofReal ξ

theorem fourier_smooth_zero {n : ℕ} (K : Set (EuclideanSpace ℝ (Fin n))) (hK : MeasurableSet K)
    (hKb : Bornology.IsBounded K) (φ : EuclideanSpace ℝ (Fin n) → ℝ) (hφ1 : ∫ x, φ x = 1) :
    𝓕 (smooth K φ) 0 = ((volume K).toReal : ℂ) := by
  rw [fourier_smooth K hK hKb φ hφ1, Real.fourier_eq, Real.fourier_eq]
  simp only [inner_zero_right, neg_zero, AddChar.map_zero_eq_one, one_smul]
  rw [integral_indicator hK, integral_complex_ofReal, hφ1]
  simp [Measure.real]


-- ==== Slice.lean ====

namespace SliceAux

/-- splitting off the first coordinate. -/
def Φ (m : ℕ) : EuclideanSpace ℝ (Fin (m+1)) ≃ᵐ ℝ × EuclideanSpace ℝ (Fin m) :=
  (MeasurableEquiv.toLp 2 (Fin (m+1) → ℝ)).symm.trans
    ((MeasurableEquiv.piFinSuccAbove (fun _ => ℝ) 0).trans
      (MeasurableEquiv.prodCongr (MeasurableEquiv.refl ℝ) (MeasurableEquiv.toLp 2 (Fin m → ℝ))))

lemma Φ_mp (m : ℕ) : MeasurePreserving (Φ m) volume volume := by
  refine (EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp _).trans ?_
  refine (measurePreserving_piFinSuccAbove (fun _ : Fin (m+1) => (volume : Measure ℝ)) 0).trans ?_
  exact (MeasurePreserving.id volume).prod
    (EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp (Fin m)).symm

lemma Φ_fst (m : ℕ) (x : EuclideanSpace ℝ (Fin (m+1))) : (Φ m x).1 = x 0 := by
  rfl

lemma Φ_norm (m : ℕ) (x : EuclideanSpace ℝ (Fin (m+1))) :
    ‖x‖ ^ 2 = (Φ m x).1 ^ 2 + ‖(Φ m x).2‖ ^ 2 := by
  rw [EuclideanSpace.real_norm_sq_eq, EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_succ]
  rfl


/-- the inner (slice) integral. -/
lemma inner_slice (m : ℕ) (lam s : ℝ) :
    ∫ y : EuclideanSpace ℝ (Fin m),
      (if s ^ 2 + ‖y‖ ^ 2 ≤ 1 then (𝐞 (-(lam * s)) : ℂ) else 0) =
      (Set.Icc (-1:ℝ) 1).indicator (fun s => (volume (Metric.closedBall
        (0 : EuclideanSpace ℝ (Fin m)) 1)).toReal •
          (((1 - s^2) ^ ((m:ℝ) / 2) : ℝ) • (𝐞 (-(lam * s)) : ℂ))) s := by
  by_cases hs : s ∈ Set.Icc (-1:ℝ) 1
  · rw [Set.indicator_of_mem hs]
    have ha : 0 ≤ 1 - s ^ 2 := by
      have := hs.1; have := hs.2; nlinarith
    have hfun : (fun y : EuclideanSpace ℝ (Fin m) =>
        (if s ^ 2 + ‖y‖ ^ 2 ≤ 1 then (𝐞 (-(lam * s)) : ℂ) else 0)) =
        (Metric.closedBall 0 (√(1 - s^2))).indicator (fun _ => (𝐞 (-(lam * s)) : ℂ)) := by
      funext y
      simp only [Set.indicator, Metric.mem_closedBall, dist_zero_right]
      congr 1
      apply propext
      rw [Real.le_sqrt (norm_nonneg _) ha]
      constructor <;> intro h <;> linarith
    rw [hfun, integral_indicator_const _ measurableSet_closedBall, Measure.real,
      Measure.addHaar_closedBall' _ _ (Real.sqrt_nonneg _), ENNReal.toReal_mul,
      ENNReal.toReal_ofReal (by positivity), finrank_euclideanSpace_fin, smul_smul,
      Real.sqrt_eq_rpow, ← Real.rpow_mul_natCast ha]
    rw [show (1:ℝ)/2 * (m:ℝ) = (m:ℝ)/2 by ring, mul_comm]
  · rw [Set.indicator_of_notMem hs]
    have : ∀ y : EuclideanSpace ℝ (Fin m), ¬ (s ^ 2 + ‖y‖ ^ 2 ≤ 1) := by
      intro y h
      apply hs
      have := sq_nonneg ‖y‖
      constructor <;> nlinarith
    simp [this]

/-- the ball integral in `ℝ^{m+1}` against a character in the first coordinate. -/
lemma ball_integral (m : ℕ) (lam : ℝ) :
    ∫ x : EuclideanSpace ℝ (Fin (m+1)),
      (Metric.closedBall (0 : EuclideanSpace ℝ (Fin (m+1))) 1).indicator
        (fun x => (𝐞 (-(lam * x 0)) : ℂ)) x =
      (volume (Metric.closedBall (0 : EuclideanSpace ℝ (Fin m)) 1)).toReal •
        ∫ s in (-1:ℝ)..1, ((1 - s^2) ^ ((m:ℝ) / 2) : ℝ) • (𝐞 (-(lam * s)) : ℂ) := by
  set G : ℝ × EuclideanSpace ℝ (Fin m) → ℂ :=
    fun p => if p.1 ^ 2 + ‖p.2‖ ^ 2 ≤ 1 then (𝐞 (-(lam * p.1)) : ℂ) else 0 with hG
  have hFG : (fun x : EuclideanSpace ℝ (Fin (m+1)) =>
      (Metric.closedBall (0 : EuclideanSpace ℝ (Fin (m+1))) 1).indicator
        (fun x => (𝐞 (-(lam * x 0)) : ℂ)) x) = G ∘ Φ m := by
    funext x
    have hx := Φ_norm m x
    rw [Φ_fst] at hx
    simp only [Set.indicator, Metric.mem_closedBall, dist_zero_right, Function.comp_apply, hG,
      Φ_fst]
    congr 1
    apply propext
    constructor
    · intro h; nlinarith [norm_nonneg x]
    · intro h; nlinarith [norm_nonneg x]
  have hint : Integrable (fun x : EuclideanSpace ℝ (Fin (m+1)) =>
      (Metric.closedBall (0 : EuclideanSpace ℝ (Fin (m+1))) 1).indicator
        (fun x => (𝐞 (-(lam * x 0)) : ℂ)) x) := by
    rw [integrable_indicator_iff measurableSet_closedBall]
    exact (Continuous.continuousOn (by fun_prop)).integrableOn_compact (isCompact_closedBall _ _)
  rw [hFG] at hint ⊢
  have hGi : Integrable G := ((Φ_mp m).integrable_comp_emb (Φ m).measurableEmbedding).mp hint
  change ∫ x, G (Φ m x) = _
  rw [(Φ_mp m).integral_comp' (g := G)]
  rw [show (volume : Measure (ℝ × EuclideanSpace ℝ (Fin m))) = volume.prod volume from rfl,
    integral_prod G hGi]
  simp only [hG, inner_slice]
  rw [integral_indicator measurableSet_Icc, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by norm_num), intervalIntegral.integral_smul]

/-- rotation invariance: reduce to `‖ξ‖ • e₀`. -/
lemma rot {n : ℕ} (i : Fin n) (ξ : EuclideanSpace ℝ (Fin n)) :
    𝓕 ((Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1).indicator
      (1 : EuclideanSpace ℝ (Fin n) → ℂ)) ξ =
    𝓕 ((Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1).indicator
      (1 : EuclideanSpace ℝ (Fin n) → ℂ)) (‖ξ‖ • EuclideanSpace.single i 1) := by
  set w : EuclideanSpace ℝ (Fin n) := ‖ξ‖ • EuclideanSpace.single i 1
  have hw : ‖ξ‖ = ‖w‖ := by simp [w, norm_smul]
  set T := (ℝ ∙ (ξ - w))ᗮ.reflection
  have hT : T ξ = w := Submodule.reflection_sub hw
  set f := (Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1).indicator
      (1 : EuclideanSpace ℝ (Fin n) → ℂ)
  have hf : f ∘ T = f := by
    funext x
    simp [f, Set.indicator, Function.comp_apply]
  rw [← hT, ← fourier_comp_linearIsometry, hf]

end SliceAux

open SliceAux in
theorem slice {n : ℕ} (hn : 2 ≤ n) (ξ : EuclideanSpace ℝ (Fin n)) :
    𝓕 ((Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1).indicator (1 : EuclideanSpace ℝ (Fin n) → ℂ)) ξ =
      (volume (Metric.closedBall (0 : EuclideanSpace ℝ (Fin (n-1))) 1)).toReal •
        ∫ s in (-1:ℝ)..1, ((1 - s^2) ^ (((n:ℝ) - 1) / 2) : ℝ) • (𝐞 (-(‖ξ‖ * s)) : ℂ) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rw [rot 0 ξ, fourier_eq]
  have h1 : ((((m+1 : ℕ) : ℝ) - 1) / 2) = (m:ℝ) / 2 := by push_cast; ring
  rw [h1, Nat.add_sub_cancel, ← ball_integral m ‖ξ‖]
  congr 1
  funext x
  simp only [Set.indicator, real_inner_smul_right, EuclideanSpace.inner_single_right]
  simp [Circle.smul_def]

-- ==== Poisson.lean ====

namespace PoissonAux

open UnitAddTorus

/-- integer vector as a real vector. -/
def ic {n : ℕ} (k : Fin n → ℤ) : Fin n → ℝ := fun i => (k i : ℝ)

/-- projection to the torus. -/
def pr {n : ℕ} (x : Fin n → ℝ) : UnitAddTorus (Fin n) := fun i => ((x i : ℝ) : UnitAddCircle)

lemma pr_add_ic {n : ℕ} (x : Fin n → ℝ) (k : Fin n → ℤ) : pr (x + ic k) = pr x := by
  funext i
  simp only [pr, ic, Pi.add_apply]
  rw [AddCircle.coe_add, (AddCircle.coe_eq_zero_iff (1:ℝ) (x := ((k i : ℤ) : ℝ))).2 ⟨k i, by simp⟩,
    add_zero]

lemma isOpenQuotientMap_pr {n : ℕ} : IsOpenQuotientMap (pr (n := n)) :=
  IsOpenQuotientMap.piMap fun _ => QuotientAddGroup.isOpenQuotientMap_mk

lemma exists_of_pr_eq {n : ℕ} {x y : Fin n → ℝ} (h : pr x = pr y) : ∃ k, y = x + ic k := by
  have : ∀ i, ∃ m : ℤ, y i = x i + m := by
    intro i
    have hi : ((y i - x i : ℝ) : UnitAddCircle) = 0 := by
      rw [AddCircle.coe_sub]
      have := congrFun h i
      simp only [pr] at this
      rw [this, sub_self]
    obtain ⟨m, hm⟩ := (AddCircle.coe_eq_zero_iff (1:ℝ)).1 hi
    exact ⟨m, by simp at hm; linarith⟩
  choose k hk using this
  exact ⟨k, funext fun i => by simp [ic, hk i]⟩

lemma finite_shifts {n : ℕ} (f : (Fin n → ℝ) → ℂ) (hc : HasCompactSupport f)
    (B : Set (Fin n → ℝ)) (hB : Bornology.IsBounded B) :
    {k : Fin n → ℤ | ∃ x ∈ B, f (x + ic k) ≠ 0}.Finite := by
  obtain ⟨R, hR⟩ := hc.isCompact.isBounded.subset_closedBall 0
  obtain ⟨r, hr⟩ := hB.subset_closedBall 0
  apply (Set.Finite.pi (t := fun _ : Fin n => Set.Icc (-⌈R + r⌉) ⌈R + r⌉)
    (fun _ => Set.finite_Icc _ _)).subset
  rintro k ⟨x, hx, hfx⟩ i _
  have h1 : ‖x + ic k‖ ≤ R := by simpa using hR (subset_tsupport f hfx)
  have h2 : ‖x‖ ≤ r := by simpa using hr hx
  have h3 : |(k i : ℝ)| ≤ R + r := by
    have a := (norm_le_pi_norm (x + ic k) i).trans h1
    have b := (norm_le_pi_norm x i).trans h2
    simp only [Pi.add_apply, ic, Real.norm_eq_abs] at a b
    calc |(k i:ℝ)| = |(x i + k i) - x i| := by ring_nf
      _ ≤ |x i + k i| + |x i| := abs_sub _ _
      _ ≤ R + r := by linarith
  have h4 : |(k i : ℝ)| ≤ (⌈R + r⌉ : ℝ) := h3.trans (Int.le_ceil _)
  rw [abs_le] at h4
  constructor
  · have : ((-⌈R + r⌉ : ℤ) : ℝ) ≤ k i := by push_cast; linarith [h4.1]
    exact_mod_cast this
  · exact_mod_cast h4.2

/-- periodization. -/
def per {n : ℕ} (f : (Fin n → ℝ) → ℂ) (x : Fin n → ℝ) : ℂ := ∑ᶠ k, f (x + ic k)

lemma continuous_per {n : ℕ} (f : (Fin n → ℝ) → ℂ) (hf : Continuous f) (hc : HasCompactSupport f) :
    Continuous (per f) := by
  unfold per
  refine continuous_finsum (fun k => hf.comp (continuous_id.add continuous_const)) ?_
  intro x
  refine ⟨Metric.ball x 1, Metric.ball_mem_nhds _ one_pos, ?_⟩
  apply (finite_shifts f hc _ Metric.isBounded_ball).subset
  rintro k ⟨y, hy1, hy2⟩
  exact ⟨y, hy2, hy1⟩

lemma per_add {n : ℕ} (f : (Fin n → ℝ) → ℂ) (x : Fin n → ℝ) (j : Fin n → ℤ) :
    per f (x + ic j) = per f x := by
  unfold per
  have : ∀ k, x + ic j + ic k = x + ic (j + k) := fun k => by
    funext i; simp only [ic, Pi.add_apply]; push_cast; ring
  simp_rw [this]
  exact finsum_comp_equiv (Equiv.addLeft j) (f := fun k => f (x + ic k))

/-- projection as a continuous map. -/
def prC {n : ℕ} : C(Fin n → ℝ, UnitAddTorus (Fin n)) :=
  ⟨pr, continuous_pi fun _ => QuotientAddGroup.continuous_mk.comp (continuous_apply _)⟩

lemma factors_per {n : ℕ} (f : (Fin n → ℝ) → ℂ) : Function.FactorsThrough (per f) (pr (n := n)) := by
  intro x y h
  obtain ⟨k, rfl⟩ := exists_of_pr_eq h
  exact (per_add f x k).symm

/-- the torus function. -/
def perT {n : ℕ} (f : (Fin n → ℝ) → ℂ) (hf : Continuous f) (hc : HasCompactSupport f) :
    C(UnitAddTorus (Fin n), ℂ) :=
  (isOpenQuotientMap_pr (n := n)).isQuotientMap.lift (f := prC) ⟨per f, continuous_per f hf hc⟩
    (factors_per f)

lemma perT_pr {n : ℕ} (f : (Fin n → ℝ) → ℂ) (hf : Continuous f) (hc : HasCompactSupport f)
    (x : Fin n → ℝ) : perT f hf hc (pr x) = per f x := by
  have := congrArg (fun g : C(Fin n → ℝ, ℂ) => g x)
    ((isOpenQuotientMap_pr (n := n)).isQuotientMap.lift_comp (f := prC) ⟨per f, continuous_per f hf hc⟩
    (factors_per f))
  exact this

/-- the box. -/
def box (n : ℕ) : Set (Fin n → ℝ) := {x | ∀ i, x i ∈ Set.Ioc (0 : ℝ) (0 + 1)}

lemma measurableSet_box (n : ℕ) : MeasurableSet (box n) :=
  MeasurableSet.univ_pi' (fun _ => measurableSet_Ioc)

lemma isBounded_box (n : ℕ) : Bornology.IsBounded (box n) := by
  apply (Metric.isBounded_Icc (0 : Fin n → ℝ) 1).subset
  intro x hx
  exact ⟨fun i => (hx i).1.le, fun i => by simpa using (hx i).2⟩

lemma integral_eq_tsum_box {n : ℕ} (g : (Fin n → ℝ) → ℂ) (hg : Integrable g) :
    ∫ x, g x = ∑' k : Fin n → ℤ, ∫ x in box n, g (x + ic k) := by
  let s : (Fin n → ℤ) → Set (Fin n → ℝ) := fun k => (fun x => x - ic k) ⁻¹' box n
  have hs : ∀ k, MeasurableSet (s k) := fun k =>
    (measurableSet_box n).preimage (measurable_id.sub_const _)
  have hceil : ∀ (a : ℝ) (j : ℤ), a - j ∈ Set.Ioc (0:ℝ) (0 + 1) → ⌈a⌉ = j + 1 := by
    intro a j h
    rw [Int.ceil_eq_iff]
    simp only [Set.mem_Ioc] at h
    push_cast
    constructor <;> linarith [h.1, h.2]
  have hd : Pairwise (Function.onFun Disjoint s) := by
    intro j k hjk
    rw [Function.onFun, Set.disjoint_left]
    intro x hj hk
    apply hjk
    funext i
    have h1 := hceil (x i) (j i) (hj i)
    have h2 := hceil (x i) (k i) (hk i)
    omega
  have hU : (⋃ k, s k) = Set.univ := by
    apply Set.eq_univ_of_forall
    intro x
    refine Set.mem_iUnion.2 ⟨fun i => ⌈x i⌉ - 1, fun i => ?_⟩
    simp only [Pi.sub_apply, ic, Set.mem_Ioc]
    push_cast
    constructor <;> linarith [Int.le_ceil (x i), Int.ceil_lt_add_one (x i)]
  have h := hasSum_integral_iUnion hs hd hg.integrableOn
  rw [hU, Measure.restrict_univ] at h
  rw [← h.tsum_eq]
  congr 1
  funext k
  have hpre : (fun x => x + ic k) ⁻¹' s k = box n := by
    ext x; simp [s]
  rw [← hpre]
  exact ((measurePreserving_add_right volume (ic k)).setIntegral_preimage_emb
    (measurableEmbedding_addRight _) g (s k)).symm

lemma coeff_perT {n : ℕ} (f : (Fin n → ℝ) → ℂ) (hf : Continuous f) (hc : HasCompactSupport f)
    (m : Fin n → ℤ) :
    mFourierCoeff (perT f hf hc) m = ∫ x, mFourier (-m) (pr x) • f x := by
  rw [mFourierCoeff_eq_integral _ m 0]
  set g := fun x => mFourier (-m) (pr x) • f x with hgdef
  have hgc : Continuous g := ((mFourier (-m)).continuous.comp prC.continuous).smul hf
  have hgs : HasCompactSupport g := hc.mono (fun x hx h0 => hx (by simp [hgdef, h0]))
  have hg : Integrable g := hgc.integrable_of_hasCompactSupport hgs
  rw [integral_eq_tsum_box g hg]
  have hS := finite_shifts f hc (box n) (isBounded_box n)
  change ∫ x in box n, mFourier (-m) (pr x) • perT f hf hc (pr x) = _
  have step1 : ∀ x ∈ box n, mFourier (-m) (pr x) • perT f hf hc (pr x) =
      ∑ k ∈ hS.toFinset, g (x + ic k) := by
    intro x hx
    rw [perT_pr, per, finsum_eq_sum_of_support_subset _ (s := hS.toFinset), Finset.smul_sum]
    · refine Finset.sum_congr rfl fun k _ => ?_
      simp only [hgdef, pr_add_ic]
    · intro k hk
      simp only [Set.Finite.coe_toFinset]
      exact ⟨x, hx, hk⟩
  rw [setIntegral_congr_fun (measurableSet_box n) step1, integral_finsetSum]
  · rw [tsum_eq_sum (s := hS.toFinset)]
    intro k hk
    apply setIntegral_eq_zero_of_forall_eq_zero
    intro x hx
    have : f (x + ic k) = 0 := by
      by_contra hne
      exact hk (by simp only [Set.Finite.mem_toFinset]; exact ⟨x, hx, hne⟩)
    simp [hgdef, this]
  · intro k _
    exact (hg.comp_add_right (ic k)).integrableOn

lemma fourier_eq_aux {n : ℕ} (F : EuclideanSpace ℝ (Fin n) → ℂ) (m : Fin n → ℤ) :
    𝓕 F (zpt m) = ∫ x, mFourier (-m) (pr x) • F ((EuclideanSpace.equiv (Fin n) ℝ).symm x) := by
  rw [fourier_eq, ← (EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp
    (Fin n)).symm.integral_comp']
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  simp only [Circle.smul_def]
  congr 1
  rw [fourierChar_apply]
  simp only [mFourier, pr, ContinuousMap.coe_mk, Pi.neg_apply, fourier_coe_apply]
  rw [← Complex.exp_sum]
  congr 1
  simp only [zpt, PiLp.inner_apply]
  have h1 : ∀ i, ((MeasurableEquiv.toLp 2 (Fin n → ℝ)).symm.symm x).ofLp i = x i := fun i => rfl
  have h2 : ∀ i, ((EuclideanSpace.equiv (Fin n) ℝ).symm fun i => (m i : ℝ)).ofLp i = m i :=
    fun i => rfl
  simp only [h1, h2, RCLike.inner_apply, conj_trivial]
  push_cast
  rw [← Finset.sum_neg_distrib, Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

end PoissonAux

open PoissonAux UnitAddTorus in
theorem poisson {n : ℕ} (F : EuclideanSpace ℝ (Fin n) → ℂ) (hF : Continuous F) (hc : HasCompactSupport F)
    (hs : Summable fun k : Fin n → ℤ => 𝓕 F (zpt k)) :
    HasSum (fun k : Fin n → ℤ => F (zpt k)) (∑' k : Fin n → ℤ, 𝓕 F (zpt k)) := by
  set f : (Fin n → ℝ) → ℂ := F ∘ (EuclideanSpace.equiv (Fin n) ℝ).symm with hfdef
  have hf : Continuous f := hF.comp (EuclideanSpace.equiv (Fin n) ℝ).symm.continuous
  have hfc : HasCompactSupport f :=
    hc.comp_homeomorph (EuclideanSpace.equiv (Fin n) ℝ).symm.toHomeomorph
  have hcoef : ∀ m, mFourierCoeff (perT f hf hfc) m = 𝓕 F (zpt m) := fun m => by
    rw [coeff_perT, fourier_eq_aux]; rfl
  have hsum : Summable (mFourierCoeff (perT f hf hfc)) := by
    simpa only [← hcoef] using hs
  have h := hasSum_mFourier_series_apply_of_summable hsum 0
  have h0 : ∀ m : Fin n → ℤ, mFourier m (0 : UnitAddTorus (Fin n)) = 1 := fun m => by
    simp [mFourier]
  simp only [h0, smul_eq_mul, mul_one, hcoef] at h
  rw [h.tsum_eq]
  have hp0 : (0 : UnitAddTorus (Fin n)) = pr 0 := by
    funext i; simp [pr]
  rw [hp0, perT_pr]
  have hfin := finite_shifts f hfc {0} Bornology.isBounded_singleton
  have hfs : ∀ k ∉ hfin.toFinset, F (zpt k) = 0 := by
    intro k hk
    by_contra hne
    exact hk (by simp only [Set.Finite.mem_toFinset]; exact ⟨0, rfl, by rw [zero_add]; exact hne⟩)
  have := hasSum_sum_of_ne_finset_zero (L := SummationFilter.unconditional _) hfs
  convert this using 1
  unfold per
  rw [finsum_eq_sum_of_support_subset _ (s := hfin.toFinset)]
  · simp only [zero_add]; rfl
  · intro k hk
    simp only [Set.Finite.coe_toFinset]
    exact ⟨0, rfl, hk⟩


-- ==== Decay1.lean ====

namespace Decay1Aux

open Set

/-- the exponential `x ↦ exp(2π i λ x)`. -/
def E (lam x : ℝ) : ℂ := cexp (2 * π * lam * x * I)

lemma hasDerivAt_E (lam x : ℝ) :
    HasDerivAt (fun x => E lam x) (2 * π * lam * I * E lam x) x := by
  unfold E
  have h : HasDerivAt (fun x : ℝ => (2 * π * lam * x * I : ℂ)) (2 * π * lam * I) x := by
    have := ((hasDerivAt_id (x : ℂ)).const_mul (2 * π * lam * I : ℂ)).comp_ofReal
    convert this using 1
    · ext y; simp; ring
    · simp
  convert h.cexp using 1
  ring

lemma norm_E (lam x : ℝ) : ‖E lam x‖ = 1 := by
  unfold E
  have : (2 * π * lam * x * I : ℂ) = ((2 * π * lam * x : ℝ) : ℂ) * I := by push_cast; ring
  rw [this, Complex.norm_exp_ofReal_mul_I]

lemma continuous_E (lam : ℝ) : Continuous (E lam) := by
  unfold E; fun_prop

lemma ibp {a b lam : ℝ} (hab : a ≤ b) (hl : lam ≠ 0) {h h' : ℝ → ℂ}
    (hc : ContinuousOn h (Icc a b)) (hd : ∀ x ∈ Ioo a b, HasDerivAt h (h' x) x)
    (hi : IntervalIntegrable h' volume a b) :
    ∫ x in a..b, h x * E lam x =
      (h b * E lam b - h a * E lam a) / (2 * π * lam * I)
        - (∫ x in a..b, h' x * E lam x) / (2 * π * lam * I) := by
  have hc0 : (2 * π * lam * I : ℂ) ≠ 0 := by
    have : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    have : (lam : ℂ) ≠ 0 := by exact_mod_cast hl
    simp_all
  have key := intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDerivAt
    (u := h) (u' := h') (v := fun x => E lam x / (2 * π * lam * I)) (v' := fun x => E lam x)
    (a := a) (b := b) (by rwa [uIcc_of_le hab])
    ((continuous_E lam).div_const _).continuousOn
    (by simpa [min_eq_left hab, max_eq_right hab] using hd)
    (fun x _ => by
      have := (hasDerivAt_E lam x).div_const (2 * π * lam * I)
      convert this using 1; exact (mul_div_cancel_left₀ _ hc0).symm)
    hi ((continuous_E lam).intervalIntegrable _ _)
  rw [key]
  have : ∫ x in a..b, h' x * (E lam x / (2 * π * lam * I)) =
      (∫ x in a..b, h' x * E lam x) / (2 * π * lam * I) := by
    rw [← intervalIntegral.integral_div]; congr 1; ext x; ring
  rw [this]; ring

lemma ii_rpow_mul {p : ℝ} (hp : -1 < p) {g : ℝ → ℂ} (hg : Continuous g) (a b : ℝ) :
    IntervalIntegrable (fun u => ((u ^ p : ℝ) : ℂ) * g u) volume a b := by
  have h1 := intervalIntegral.intervalIntegrable_rpow' (a := a) (b := b) hp
  have h2 : IntervalIntegrable (fun u => ((u ^ p : ℝ) : ℂ)) volume a b := ⟨h1.1.ofReal, h1.2.ofReal⟩
  exact h2.mul_continuousOn hg.continuousOn

lemma hasDerivAt_rpowG {p x : ℝ} (hx : 0 < x) {G : ℝ → ℂ} (hG : DifferentiableAt ℝ G x) :
    HasDerivAt (fun u => ((u ^ p : ℝ) : ℂ) * G u)
      (((p * x ^ (p - 1) : ℝ) : ℂ) * G x + ((x ^ p : ℝ) : ℂ) * deriv G x) x :=
  ((Real.hasDerivAt_rpow_const (Or.inl hx.ne')).ofReal_comp).mul hG.hasDerivAt

lemma bound_of_cont {G : ℝ → ℂ} (hG : Continuous G) : ∃ M, ∀ u ∈ Icc (0:ℝ) 2, ‖G u‖ ≤ M := by
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn hG.continuousOn
  exact ⟨M, hM⟩

lemma key_base (γ : ℝ) (hγ1 : -1 < γ) (hγ0 : γ ≤ 0) (G : ℝ → ℂ) (hG : ContDiff ℝ ∞ G)
    (hz : ∀ u, 4/3 < u → G u = 0) :
    ∃ C, ∀ lam : ℝ, 1 ≤ |lam| →
      ‖∫ u in (0:ℝ)..2, ((u ^ γ : ℝ) : ℂ) * G u * E lam u‖ ≤ C * |lam| ^ (-(γ + 1)) := by
  have hdG := contDiff_infty_iff_deriv.1 hG
  obtain ⟨M, hM⟩ := bound_of_cont hG.continuous
  obtain ⟨M', hM'⟩ := bound_of_cont hdG.2.continuous
  have hM0 : 0 ≤ M := le_trans (norm_nonneg _) (hM 0 (by norm_num))
  have hM'0 : 0 ≤ M' := le_trans (norm_nonneg _) (hM' 0 (by norm_num))
  have hγ1' : 0 < γ + 1 := by linarith
  refine ⟨M / (γ + 1) + 2 * M + 2 * M', fun lam hl => ?_⟩
  have hlpos : 0 < |lam| := by linarith
  have hl0 : lam ≠ 0 := abs_pos.1 hlpos
  set a := |lam|⁻¹ with ha
  have ha0 : 0 < a := inv_pos.2 hlpos
  have ha1 : a ≤ 1 := inv_le_one_of_one_le₀ hl
  have hA : |lam| ^ (-(γ + 1)) = a ^ (γ + 1) := by
    rw [ha, Real.inv_rpow hlpos.le, Real.rpow_neg hlpos.le]
  rw [hA]
  set F : ℝ → ℂ := fun u => ((u ^ γ : ℝ) : ℂ) * G u * E lam u with hF
  have hFi : ∀ x y, IntervalIntegrable F volume x y := by
    intro x y
    have := ii_rpow_mul hγ1 (g := fun u => G u * E lam u)
      (hG.continuous.mul (continuous_E lam)) x y
    simpa only [hF, mul_assoc] using this
  rw [← intervalIntegral.integral_add_adjacent_intervals (hFi 0 a) (hFi a 2)]
  -- part 1
  have P1 : ‖∫ u in (0:ℝ)..a, F u‖ ≤ M / (γ + 1) * a ^ (γ + 1) := by
    have hint : ∫ u in (0:ℝ)..a, M * u ^ γ = M / (γ + 1) * a ^ (γ + 1) := by
      rw [intervalIntegral.integral_const_mul, integral_rpow (Or.inl hγ1),
        Real.zero_rpow hγ1'.ne']
      ring
    rw [← hint]
    apply intervalIntegral.norm_integral_le_of_norm_le ha0.le
    · refine Filter.Eventually.of_forall (fun u hu => ?_)
      simp only [hF, norm_mul, norm_E, mul_one, Complex.norm_real, Real.norm_eq_abs]
      rw [abs_of_nonneg (Real.rpow_nonneg hu.1.le _), mul_comm]
      exact mul_le_mul_of_nonneg_right (hM u ⟨hu.1.le, by linarith [hu.2]⟩)
        (Real.rpow_nonneg hu.1.le _)
    · exact (intervalIntegral.intervalIntegrable_rpow' hγ1).const_mul M
  -- part 2
  set h' : ℝ → ℂ := fun u => ((γ * u ^ (γ - 1) : ℝ) : ℂ) * G u + ((u ^ γ : ℝ) : ℂ) * deriv G u
    with hh'
  have hder : ∀ x, 0 < x → HasDerivAt (fun u => ((u ^ γ : ℝ) : ℂ) * G u) (h' x) x :=
    fun x hx => hasDerivAt_rpowG hx (hG.differentiable (by simp) x)
  have hh'c : ContinuousOn h' (Icc a 2) := by
    intro x hx
    have hx0 : x ≠ 0 := by linarith [hx.1]
    apply ContinuousAt.continuousWithinAt
    have c1 : ContinuousAt (fun u : ℝ => u ^ (γ - 1)) x :=
      Real.continuousAt_rpow_const _ _ (Or.inl hx0)
    have c2 : ContinuousAt (fun u : ℝ => u ^ γ) x := Real.continuousAt_rpow_const _ _ (Or.inl hx0)
    exact ((Complex.continuous_ofReal.continuousAt.comp (continuousAt_const.mul c1)).mul
      hG.continuous.continuousAt).add
      ((Complex.continuous_ofReal.continuousAt.comp c2).mul hdG.2.continuous.continuousAt)
  have hibp := ibp (a := a) (b := 2) (lam := lam) (by linarith) hl0
    (h := fun u => ((u ^ γ : ℝ) : ℂ) * G u) (h' := h')
    (fun x hx => (hder x (by linarith [hx.1])).continuousAt.continuousWithinAt)
    (fun x hx => hder x (by linarith [hx.1]))
    (hh'c.intervalIntegrable_of_Icc (by linarith))
  have hc1 : ContinuousOn (fun u : ℝ => (-γ) * M * u ^ (γ - 1)) (Icc a 2) := by
    intro x hx
    exact (continuousAt_const.mul (Real.continuousAt_rpow_const _ _
      (Or.inl (by linarith [hx.1] : x ≠ 0)))).continuousWithinAt
  have hJ : ‖∫ u in a..2, h' u * E lam u‖ ≤ (M + 2 * M') * a ^ γ := by
    have hint : ∫ u in a..2, ((-γ) * M * u ^ (γ - 1) + M' * a ^ γ)
        = M * (a ^ γ - 2 ^ γ) + M' * a ^ γ * (2 - a) := by
      rw [intervalIntegral.integral_add (hc1.intervalIntegrable_of_Icc (by linarith))
        intervalIntegrable_const, intervalIntegral.integral_const]
      have : ∫ u in a..2, (-γ) * M * u ^ (γ - 1) = M * (a ^ γ - 2 ^ γ) := by
        rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (f := fun u => -(M * u ^ γ))]
        · ring
        · intro x hx
          rw [uIcc_of_le (by linarith)] at hx
          have := ((Real.hasDerivAt_rpow_const (p := γ)
            (Or.inl (by linarith [hx.1] : x ≠ 0))).const_mul M).neg
          convert this using 1; ring
        · exact hc1.intervalIntegrable_of_Icc (by linarith)
      rw [this, smul_eq_mul]; ring
    have hle : ∫ u in a..2, ((-γ) * M * u ^ (γ - 1) + M' * a ^ γ) ≤ (M + 2 * M') * a ^ γ := by
      rw [hint]
      have : 0 ≤ (2:ℝ) ^ γ := by positivity
      have : 0 ≤ a ^ γ := by positivity
      nlinarith [mul_nonneg hM'0 this]
    refine le_trans ?_ hle
    apply intervalIntegral.norm_integral_le_of_norm_le (by linarith)
    · refine Filter.Eventually.of_forall (fun u hu => ?_)
      have hu0 : 0 < u := lt_trans ha0 hu.1
      have hu2 : u ∈ Icc (0:ℝ) 2 := ⟨hu0.le, hu.2⟩
      rw [norm_mul, norm_E, mul_one, hh']
      refine le_trans (norm_add_le _ _) ?_
      simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      rw [abs_of_nonpos hγ0, abs_of_nonneg (Real.rpow_nonneg hu0.le _),
        abs_of_nonneg (Real.rpow_nonneg hu0.le _)]
      have e1 := hM u hu2
      have e2 := hM' u hu2
      have e3 : u ^ γ ≤ a ^ γ := Real.rpow_le_rpow_of_nonpos ha0 hu.1.le hγ0
      have e4 : 0 ≤ u ^ (γ - 1) := Real.rpow_nonneg hu0.le _
      have e5 : 0 ≤ u ^ γ := Real.rpow_nonneg hu0.le _
      have e6 : 0 ≤ -γ := by linarith
      have : -γ * u ^ (γ - 1) * ‖G u‖ ≤ -γ * M * u ^ (γ - 1) := by
        have := mul_le_mul_of_nonneg_left e1 (mul_nonneg e6 e4); linarith
      have : u ^ γ * ‖deriv G u‖ ≤ M' * a ^ γ := by
        calc u ^ γ * ‖deriv G u‖ ≤ a ^ γ * M' := mul_le_mul e3 e2 (norm_nonneg _) (by positivity)
          _ = _ := by ring
      linarith
    · exact (hc1.intervalIntegrable_of_Icc (by linarith)).add intervalIntegrable_const
  have P2 : ‖∫ u in a..2, F u‖ ≤ (2 * M + 2 * M') * a ^ (γ + 1) := by
    rw [show (∫ u in a..2, F u) = ∫ u in a..2, ((u ^ γ : ℝ) : ℂ) * G u * E lam u from rfl, hibp]
    rw [hz 2 (by norm_num), mul_zero, zero_mul, zero_sub]
    have hn : ‖(2 * π * lam * I : ℂ)‖ = 2 * π * |lam| := by simp [abs_of_pos Real.pi_pos]
    have hX : ‖((a ^ γ : ℝ) : ℂ) * G a * E lam a‖ ≤ a ^ γ * M := by
      rw [norm_mul, norm_mul, norm_E, mul_one, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (by positivity)]
      exact mul_le_mul_of_nonneg_left (hM a ⟨ha0.le, by linarith⟩) (by positivity)
    have hpi : 1 ≤ 2 * π := by linarith [Real.pi_gt_three]
    calc _ ≤ ‖-(((a ^ γ : ℝ) : ℂ) * G a * E lam a) / (2 * π * lam * I)‖
          + ‖(∫ u in a..2, h' u * E lam u) / (2 * π * lam * I)‖ := norm_sub_le _ _
      _ ≤ (a ^ γ * M + (M + 2 * M') * a ^ γ) / (2 * π * |lam|) := by
          rw [norm_div, norm_div, norm_neg, hn, ← add_div]; gcongr
      _ ≤ (2 * M + 2 * M') * a ^ γ * a := by
          rw [div_le_iff₀ (by positivity)]
          have h1 : a * |lam| = 1 := inv_mul_cancel₀ hlpos.ne'
          have t0 : 0 ≤ a ^ γ := by positivity
          have : (2 * M + 2 * M') * a ^ γ * a * (2 * π * |lam|)
              = (2 * M + 2 * M') * a ^ γ * (2 * π) * (a * |lam|) := by ring
          rw [this, h1, mul_one]
          nlinarith [mul_nonneg (by linarith : 0 ≤ 2 * M + 2 * M') t0]
      _ = (2 * M + 2 * M') * a ^ (γ + 1) := by rw [Real.rpow_add_one ha0.ne']; ring
  calc _ ≤ _ := norm_add_le _ _
    _ ≤ M / (γ + 1) * a ^ (γ + 1) + (2 * M + 2 * M') * a ^ (γ + 1) := add_le_add P1 P2
    _ = _ := by ring

lemma key (γ : ℝ) (hγ1 : -1 < γ) (hγ0 : γ ≤ 0) (m : ℕ) :
    ∀ G : ℝ → ℂ, ContDiff ℝ ∞ G → (∀ u, 4/3 < u → G u = 0) →
    ∃ C, ∀ lam : ℝ, 1 ≤ |lam| →
      ‖∫ u in (0:ℝ)..2, ((u ^ (γ + m) : ℝ) : ℂ) * G u * E lam u‖
        ≤ C * |lam| ^ (-(γ + m + 1)) := by
  induction m with
  | zero => intro G hG hz; simpa using key_base γ hγ1 hγ0 G hG hz
  | succ m ih =>
    intro G hG hz
    have hdG := (contDiff_infty_iff_deriv.1 hG)
    set Gt : ℝ → ℂ := fun u => ((γ + m + 1 : ℝ) : ℂ) * G u + (u : ℂ) * deriv G u with hGt
    have hGt_cd : ContDiff ℝ ∞ Gt :=
      (contDiff_const.mul hG).add (ofRealCLM.contDiff.mul hdG.2)
    have hGt_z : ∀ u, 4/3 < u → Gt u = 0 := by
      intro u hu
      have h1 : G =ᶠ[𝓝 u] fun _ => (0:ℂ) :=
        Filter.eventually_of_mem (Ioi_mem_nhds hu) (fun v hv => hz v hv)
      have h2 : deriv G u = 0 := by rw [h1.deriv_eq]; simp
      simp [hGt, hz u hu, h2]
    obtain ⟨C, hC⟩ := ih Gt hGt_cd hGt_z
    have hp : (0:ℝ) < γ + ↑(m+1) := by push_cast; linarith [(Nat.cast_nonneg m : (0:ℝ) ≤ m)]
    have hp' : -1 < γ + (m:ℝ) := by linarith [(Nat.cast_nonneg m : (0:ℝ) ≤ m)]
    refine ⟨C / (2 * π), fun lam hl => ?_⟩
    have hl0 : lam ≠ 0 := by rintro rfl; simp at hl; linarith
    have hibp := ibp (a := 0) (b := 2) (lam := lam) (by norm_num) hl0
      (h := fun u => ((u ^ (γ + ↑(m+1)) : ℝ) : ℂ) * G u)
      (h' := fun u => ((u ^ (γ + m) : ℝ) : ℂ) * Gt u)
      (((Complex.continuous_ofReal.comp (Real.continuous_rpow_const hp.le)).mul
        hG.continuous).continuousOn)
      (by
        intro x hx
        have := hasDerivAt_rpowG (p := γ + ↑(m+1)) hx.1 (hG.differentiable (by simp) x)
        convert this using 1
        have e1 : γ + ((m+1 : ℕ) : ℝ) - 1 = γ + m := by push_cast; ring
        have e2 : x ^ (γ + ((m+1 : ℕ) : ℝ)) = x ^ (γ + (m:ℝ)) * x := by
          rw [show γ + ((m+1 : ℕ) : ℝ) = (γ + m) + 1 by push_cast; ring]
          exact Real.rpow_add_one' hx.1.le (by linarith)
        rw [e1, e2, hGt]; push_cast; ring)
      (ii_rpow_mul hp' hGt_cd.continuous 0 2)
    rw [hibp]
    have hb2 : G 2 = 0 := hz 2 (by norm_num)
    rw [hb2, Real.zero_rpow hp.ne']
    simp only [mul_zero, zero_mul, ofReal_zero, sub_zero, zero_div, zero_sub, norm_neg, norm_div]
    have hn : ‖(2 * π * lam * I : ℂ)‖ = 2 * π * |lam| := by
      simp [abs_of_pos Real.pi_pos]
    rw [hn]
    have hlpos : 0 < |lam| := by linarith
    rw [div_le_iff₀ (by positivity)]
    calc _ ≤ C * |lam| ^ (-(γ + m + 1)) := hC lam hl
      _ = _ := by
        have : |lam| ^ (-(γ + ↑(m+1) + 1)) = |lam| ^ (-(γ + m + 1)) / |lam| := by
          rw [← Real.rpow_sub_one hlpos.ne']; push_cast; ring_nf
        rw [this]; field_simp

/-- smooth cutoff with `ρ s + ρ (-s) = 1`, `ρ = 0` on `(-∞,-1/3]`. -/
def rho (s : ℝ) : ℝ := smoothTransition ((3 * s + 1) / 2)

lemma rho_add (s : ℝ) : rho s + rho (-s) = 1 := by
  unfold rho
  have : (3 * -s + 1) / 2 = 1 - (3 * s + 1) / 2 := by ring
  rw [this]
  generalize (3 * s + 1) / 2 = x
  unfold smoothTransition
  rw [sub_sub_cancel, add_comm (expNegInvGlue (1 - x)), ← add_div,
    div_self (smoothTransition.pos_denom x).ne']

lemma contDiff_rho : ContDiff ℝ ∞ rho := by
  unfold rho
  exact (smoothTransition.contDiff (n := ⊤)).comp (by fun_prop)

lemma main_piece (β : ℝ) (hβ : 0 < β) : ∃ C, ∀ lam : ℝ, 1 ≤ |lam| →
    ‖∫ s in (-1:ℝ)..1, (((1 - s^2) ^ β * rho s : ℝ) : ℂ) * E lam s‖ ≤ C * |lam| ^ (-(β + 1)) := by
  set γ := β - (⌈β⌉₊ : ℝ) with hγ
  have hγ1 : -1 < γ := by have := Nat.ceil_lt_add_one hβ.le; rw [hγ]; linarith
  have hγ0 : γ ≤ 0 := by have := Nat.le_ceil β; rw [hγ]; linarith
  set G : ℝ → ℂ := fun u => (((2 - u) ^ β * rho (1 - u) : ℝ) : ℂ) with hG
  have hGz : ∀ u, 4/3 < u → G u = 0 := by
    intro u hu; simp only [hG, rho]; rw [smoothTransition.zero_of_nonpos (by linarith)]; simp
  have hGcd : ContDiff ℝ ∞ G := by
    have : ContDiff ℝ ∞ (fun u : ℝ => (2 - u) ^ β * rho (1 - u)) := by
      rw [contDiff_iff_contDiffAt]; intro u
      rcases lt_or_ge u 2 with h | h
      · exact ((Real.contDiffAt_rpow_const_of_ne (by linarith : (2:ℝ) - u ≠ 0)).comp u
          (contDiffAt_const.sub contDiffAt_id)).mul
          ((contDiff_rho.comp (contDiff_const.sub contDiff_id)).contDiffAt)
      · apply (contDiffAt_const (c := (0:ℝ))).congr_of_eventuallyEq
        filter_upwards [Ioi_mem_nhds (show (4/3:ℝ) < u by linarith)] with v hv
        simp only [rho]; rw [smoothTransition.zero_of_nonpos (by simp at hv; linarith)]; simp
    exact ofRealCLM.contDiff.comp this
  obtain ⟨C, hC⟩ := key γ hγ1 hγ0 ⌈β⌉₊ G hGcd hGz
  have hγm : γ + (⌈β⌉₊ : ℝ) = β := by rw [hγ]; ring
  rw [hγm] at hC
  refine ⟨C, fun lam hl => ?_⟩
  have h1 : ∫ s in (-1:ℝ)..1, (((1 - s^2) ^ β * rho s : ℝ) : ℂ) * E lam s
      = ∫ u in (0:ℝ)..2, (((1 - (1-u)^2) ^ β * rho (1-u) : ℝ) : ℂ) * E lam (1-u) := by
    rw [intervalIntegral.integral_comp_sub_left
      (fun s => (((1 - s^2) ^ β * rho s : ℝ) : ℂ) * E lam s)]
    norm_num
  have h2 : ∫ u in (0:ℝ)..2, (((1 - (1-u)^2) ^ β * rho (1-u) : ℝ) : ℂ) * E lam (1-u)
      = E lam 1 * ∫ u in (0:ℝ)..2, ((u ^ β : ℝ) : ℂ) * G u * E (-lam) u := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro u hu
    rw [uIcc_of_le (by norm_num)] at hu
    have e1 : (1 - (1-u)^2) ^ β = u ^ β * (2-u) ^ β := by
      rw [← Real.mul_rpow hu.1 (by linarith [hu.2])]; congr 1; ring
    have e2 : E lam (1 - u) = E lam 1 * E (-lam) u := by
      unfold E; rw [← Complex.exp_add]; congr 1; push_cast; ring
    simp only [hG, e1, e2]; push_cast; ring
  rw [h1, h2, norm_mul, norm_E, one_mul]
  simpa using hC (-lam) (by simpa using hl)

end Decay1Aux

open Decay1Aux in
theorem decay1 (β : ℝ) (hβ : 0 < β) : ∃ C : ℝ, ∀ lam : ℝ, 1 ≤ |lam| →
    ‖∫ s in (-1:ℝ)..1, ((1 - s^2) ^ β : ℝ) • (𝐞 (-(lam * s)) : ℂ)‖ ≤ C * |lam| ^ (-(β + 1)) := by
  obtain ⟨C, hC⟩ := main_piece β hβ
  refine ⟨2 * C, fun lam hl => ?_⟩
  set F : ℝ → ℝ → ℂ := fun μ s => (((1 - s^2) ^ β * rho s : ℝ) : ℂ) * E μ s with hF
  have hcont : ∀ μ, Continuous (F μ) := by
    intro μ
    have : Continuous fun s : ℝ => (1 - s^2) ^ β :=
      (Real.continuous_rpow_const hβ.le).comp (by fun_prop)
    exact (Complex.continuous_ofReal.comp (this.mul (contDiff_rho.continuous))).mul (continuous_E μ)
  have hpt : ∀ s, ((1 - s^2) ^ β : ℝ) • (𝐞 (-(lam * s)) : ℂ) = F (-lam) s + F lam (-s) := by
    intro s
    simp only [hF]
    have h1 : rho (-s) = 1 - rho s := by linarith [rho_add s]
    have h2 : E lam (-s) = E (-lam) s := by unfold E; congr 1; push_cast; ring
    have h3 : (𝐞 (-(lam * s)) : ℂ) = E (-lam) s := by
      rw [Real.fourierChar_apply]; unfold E; congr 1; push_cast; ring
    rw [h1, h2, h3, neg_sq, Complex.real_smul]; push_cast; ring
  simp_rw [hpt]
  rw [intervalIntegral.integral_add ((hcont _).intervalIntegrable _ _)
    (f := F (-lam)) (g := fun s => F lam (-s))
    (((hcont lam).comp continuous_neg).intervalIntegrable _ _)]
  rw [intervalIntegral.integral_comp_neg (f := F lam)]
  simp only [neg_neg]
  calc _ ≤ _ := norm_add_le _ _
    _ ≤ C * |-lam| ^ (-(β+1)) + C * |lam| ^ (-(β+1)) :=
        add_le_add (hC _ (by simpa using hl)) (hC _ hl)
    _ = _ := by rw [abs_neg]; ring


-- ==== Bump.lean ====

namespace BumpAux

lemma fourier_scale {n : ℕ} (g : EuclideanSpace ℝ (Fin n) → ℂ) {δ : ℝ} (hδ : 0 < δ)
    (ξ : EuclideanSpace ℝ (Fin n)) :
    𝓕 (fun x => ((δ ^ n)⁻¹ : ℂ) * g (δ⁻¹ • x)) ξ = 𝓕 g (δ • ξ) := by
  rw [Real.fourier_eq, Real.fourier_eq]
  have key := Measure.integral_comp_inv_smul_of_nonneg
    (μ := (volume : Measure (EuclideanSpace ℝ (Fin n))))
    (fun y => (𝐞 (-⟪δ • y, ξ⟫) • (((δ : ℂ) ^ n)⁻¹ * g y))) hδ.le
  have h1 : ∀ v : EuclideanSpace ℝ (Fin n), δ • δ⁻¹ • v = v := fun v => by
    rw [smul_smul, mul_inv_cancel₀ hδ.ne', one_smul]
  simp only [h1, finrank_euclideanSpace, Fintype.card_fin] at key
  rw [key, ← integral_smul]
  congr 1
  ext v
  rw [smul_comm, real_inner_smul_left, real_inner_smul_right, Complex.real_smul]
  congr 1
  push_cast
  have hc : (δ : ℂ) ^ n ≠ 0 := pow_ne_zero _ (by exact_mod_cast hδ.ne')
  field_simp

/-- radial profile. -/
def gfun (α N δ s : ℝ) : ℝ := s ^ (-α) * (1 + δ * s) ^ (-N)

lemma gfun_nonneg (α N : ℝ) {δ s : ℝ} (hδ : 0 ≤ δ) (hs : 0 ≤ s) : 0 ≤ gfun α N δ s := by
  unfold gfun
  exact mul_nonneg (Real.rpow_nonneg hs _) (Real.rpow_nonneg (by nlinarith) _)

lemma gfun_anti {α N δ s t : ℝ} (hα : 0 ≤ α) (hN : 0 ≤ N) (hδ : 0 ≤ δ) (hs : 0 < s)
    (hst : s ≤ t) : gfun α N δ t ≤ gfun α N δ s := by
  unfold gfun
  have h1 : t ^ (-α) ≤ s ^ (-α) := Real.rpow_le_rpow_of_nonpos hs hst (by linarith)
  have h2 : (1 + δ * t) ^ (-N) ≤ (1 + δ * s) ^ (-N) :=
    Real.rpow_le_rpow_of_nonpos (by nlinarith) (by nlinarith) (by linarith)
  exact mul_le_mul h1 h2 (Real.rpow_nonneg (by nlinarith) _) (Real.rpow_nonneg hs.le _)

lemma rpow_neg_le_aux {a b c p : ℝ} (ha : 0 < a) (hc : 0 < c) (hp : 0 ≤ p)
    (h : b ≤ c * a) (hb : 0 < b) : a ^ (-p) ≤ c ^ p * b ^ (-p) := by
  have e : a ^ (-p) = c ^ p * (c * a) ^ (-p) := by
    rw [Real.mul_rpow hc.le ha.le, ← mul_assoc, ← Real.rpow_add hc]; simp
  rw [e]
  exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_nonpos hb h (by linarith)) (by positivity)

lemma gfun_shift {α N δ r c : ℝ} (hα : 0 ≤ α) (hN : 0 ≤ N) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hr : 1 ≤ r) (hc : 0 ≤ c) :
    gfun α N δ r ≤ ((1 + c) ^ α * (1 + c) ^ N) * gfun α N δ (r + c) := by
  unfold gfun
  have h1 := rpow_neg_le_aux (a := r) (b := r + c) (c := 1 + c) (p := α) (by linarith)
    (by linarith) hα (by nlinarith) (by linarith)
  have h2 := rpow_neg_le_aux (a := 1 + δ * r) (b := 1 + δ * (r + c)) (c := 1 + c) (p := N)
    (by positivity) (by linarith) hN (by nlinarith [mul_nonneg hδ.le hc, mul_nonneg hc (mul_nonneg hδ.le (by linarith : (0:ℝ) ≤ r))]) (by positivity)
  calc r ^ (-α) * (1 + δ * r) ^ (-N)
      ≤ ((1 + c) ^ α * (r + c) ^ (-α)) * ((1 + c) ^ N * (1 + δ * (r + c)) ^ (-N)) :=
        mul_le_mul h1 h2 (by positivity) (by positivity)
    _ = _ := by ring

/-- unit cube at an integer point. -/
def cube {n : ℕ} (k : Fin n → ℤ) : Set (EuclideanSpace ℝ (Fin n)) :=
  WithLp.ofLp ⁻¹' (Set.pi Set.univ fun i => Set.Ico (k i : ℝ) (k i + 1))

lemma mem_cube {n : ℕ} {k : Fin n → ℤ} {x : EuclideanSpace ℝ (Fin n)} :
    x ∈ cube k ↔ ∀ i, (k i : ℝ) ≤ x i ∧ x i < k i + 1 := by
  simp [cube]

lemma measurableSet_cube {n : ℕ} (k : Fin n → ℤ) : MeasurableSet (cube k) := by
  unfold cube
  exact (MeasurableSet.univ_pi fun i => measurableSet_Ico).preimage (by fun_prop)

lemma volume_cube {n : ℕ} (k : Fin n → ℤ) : volume (cube k) = 1 := by
  unfold cube
  rw [(PiLp.volume_preserving_ofLp (Fin n)).measure_preimage
    (MeasurableSet.univ_pi fun i => measurableSet_Ico).nullMeasurableSet, Real.volume_pi_Ico]
  simp

lemma cube_disjoint {n : ℕ} : Pairwise (Function.onFun Disjoint (cube (n := n))) := by
  intro k l hkl
  rw [Function.onFun, Set.disjoint_left]
  intro x hk hl
  apply hkl
  funext i
  rw [mem_cube] at hk hl
  have h1 : ⌊x i⌋ = k i := Int.floor_eq_iff.2 (hk i)
  have h2 : ⌊x i⌋ = l i := Int.floor_eq_iff.2 (hl i)
  rw [← h1, h2]

lemma zpt_apply {n : ℕ} (k : Fin n → ℤ) (i : Fin n) : zpt k i = (k i : ℝ) := by
  simp [zpt]

lemma one_le_norm_zpt {n : ℕ} {k : Fin n → ℤ} (hk : k ≠ 0) : 1 ≤ ‖zpt k‖ := by
  obtain ⟨i, hi⟩ : ∃ i, k i ≠ 0 := by
    by_contra h; push Not at h; exact hk (funext h)
  have h1 := PiLp.norm_apply_le (zpt k) i
  rw [zpt_apply, Real.norm_eq_abs] at h1
  have : (1 : ℝ) ≤ |(k i : ℝ)| := by
    rw [← Int.cast_abs]; exact_mod_cast Int.one_le_abs hi
  linarith

lemma norm_le_of_mem_cube {n : ℕ} {k : Fin n → ℤ} {x : EuclideanSpace ℝ (Fin n)}
    (hx : x ∈ cube k) : ‖x‖ ≤ ‖zpt k‖ + n := by
  rw [mem_cube] at hx
  have h : ‖x - zpt k‖ ^ 2 ≤ n := by
    rw [EuclideanSpace.norm_sq_eq]
    calc ∑ i, ‖(x - zpt k) i‖ ^ 2 ≤ ∑ _i : Fin n, (1 : ℝ) := by
          apply Finset.sum_le_sum
          intro i _
          rw [PiLp.sub_apply, zpt_apply, Real.norm_eq_abs, sq_abs]
          have := hx i
          nlinarith
      _ = n := by simp
  have h2 : ‖x - zpt k‖ ≤ n := by
    have : (0:ℝ) ≤ ‖x - zpt k‖ := norm_nonneg _
    rcases Nat.eq_zero_or_pos n with h0 | h0
    · subst h0; simp only [CharP.cast_eq_zero] at h ⊢; nlinarith
    · have : (1:ℝ) ≤ n := by exact_mod_cast h0
      rcases le_or_gt ‖x - zpt k‖ 1 with h3 | h3
      · linarith
      · nlinarith
  have := norm_le_norm_add_norm_sub' x (zpt k)
  linarith

lemma ne_zero_of_mem_cube {n : ℕ} {k : Fin n → ℤ} (hk : k ≠ 0) {x : EuclideanSpace ℝ (Fin n)}
    (hx : x ∈ cube k) : x ≠ 0 := by
  rintro rfl
  apply hk
  funext i
  have := (mem_cube.1 hx) i
  simp only [PiLp.zero_apply] at this
  have h1 : (k i : ℝ) < 1 := by linarith [this.2]
  have h2 : (-1 : ℝ) < k i := by linarith [this.1, this.2]
  have h1' : k i < 1 := by exact_mod_cast h1
  have h2' : -1 < k i := by exact_mod_cast h2
  simp only [Pi.zero_apply]; omega

/-- integrability of the model profile. -/
lemma integrable_model {n : ℕ} (hn : 1 ≤ n) {α : ℝ} (hα0 : 0 < α) (hαn : α < n) {N : ℝ}
    (hN : (n:ℝ) < N) :
    Integrable (fun x : EuclideanSpace ℝ (Fin n) => gfun α N 1 ‖x‖) := by
  have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  rw [integrable_fun_norm_addHaar volume (f := gfun α N 1)]
  simp only [finrank_euclideanSpace, Fintype.card_fin, smul_eq_mul]
  have hN0 : 0 ≤ N := by have : (0:ℝ) ≤ n := by positivity
                         linarith
  have hmeas : Measurable (fun y : ℝ => y ^ (n - 1) * gfun α N 1 y) := by
    unfold gfun; fun_prop
  have key : ∀ y : ℝ, 0 < y → y ^ (n - 1) * gfun α N 1 y =
      y ^ ((n : ℝ) - 1 - α) * (1 + y) ^ (-N) := by
    intro y hy
    unfold gfun
    rw [one_mul, ← mul_assoc, ← Real.rpow_natCast, ← Real.rpow_add hy]
    congr 3
    rw [Nat.cast_sub hn]; push_cast; ring
  rw [← Set.Ioc_union_Ioi_eq_Ioi zero_le_one]
  refine IntegrableOn.union ?_ ?_
  · have hg : IntegrableOn (fun y : ℝ => y ^ ((n : ℝ) - 1 - α)) (Set.Ioc 0 1) :=
      (intervalIntegral.intervalIntegrable_rpow' (a := 0) (b := 1) (r := (n : ℝ) - 1 - α)
        (by linarith)).1
    refine hg.mono' hmeas.aestronglyMeasurable ?_
    refine (ae_restrict_iff' measurableSet_Ioc).2 (Eventually.of_forall fun y hy => ?_)
    rw [key y hy.1, Real.norm_eq_abs, abs_of_nonneg (by
      exact mul_nonneg (Real.rpow_nonneg hy.1.le _) (Real.rpow_nonneg (by linarith [hy.1]) _))]
    have h1 : (1 + y) ^ (-N) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos (by linarith [hy.1])
      (by linarith)
    have h2 : 0 ≤ y ^ ((n : ℝ) - 1 - α) := Real.rpow_nonneg hy.1.le _
    nlinarith
  · have hg : IntegrableOn (fun y : ℝ => y ^ ((n : ℝ) - 1 - α - N)) (Set.Ioi 1) :=
      integrableOn_Ioi_rpow_of_lt (by linarith) zero_lt_one
    refine hg.mono' hmeas.aestronglyMeasurable ?_
    refine (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun y hy => ?_)
    have hy0 : (0 : ℝ) < y := lt_trans zero_lt_one hy
    rw [key y hy0, Real.norm_eq_abs, abs_of_nonneg (by
      exact mul_nonneg (Real.rpow_nonneg hy0.le _) (Real.rpow_nonneg (by linarith) _)),
      show ((n:ℝ) - 1 - α - N) = ((n:ℝ) - 1 - α) + (-N) by ring, Real.rpow_add hy0]
    have h1 : (1 + y) ^ (-N) ≤ y ^ (-N) :=
      Real.rpow_le_rpow_of_nonpos hy0 (by linarith) (by linarith)
    have h2 : 0 ≤ y ^ ((n : ℝ) - 1 - α) := Real.rpow_nonneg hy0.le _
    exact mul_le_mul_of_nonneg_left h1 h2

lemma integral_scale {n : ℕ} (hn : 1 ≤ n) {α : ℝ} (hα0 : 0 < α) (hαn : α < n) {N : ℝ}
    (hN : (n:ℝ) < N) {δ : ℝ} (hδ : 0 < δ) :
    Integrable (fun x : EuclideanSpace ℝ (Fin n) => gfun α N δ ‖x‖) ∧
    ∫ x : EuclideanSpace ℝ (Fin n), gfun α N δ ‖x‖ =
      δ ^ (α - n) * ∫ x : EuclideanSpace ℝ (Fin n), gfun α N 1 ‖x‖ := by
  have e : (fun x : EuclideanSpace ℝ (Fin n) => gfun α N δ ‖x‖) =
      fun x => δ ^ α * gfun α N 1 ‖δ • x‖ := by
    ext x
    unfold gfun
    rw [norm_smul, Real.norm_of_nonneg hδ.le, Real.mul_rpow hδ.le (norm_nonneg _), one_mul,
      Real.rpow_neg hδ.le, ← mul_assoc, ← mul_assoc, mul_inv_cancel₀ (by positivity), one_mul]
  have hI := integrable_model hn hα0 hαn hN
  rw [e]
  refine ⟨(hI.comp_smul hδ.ne').const_mul _, ?_⟩
  rw [integral_const_mul,
    Measure.integral_comp_smul_of_nonneg (μ := volume) (fun x => gfun α N 1 ‖x‖) δ (hR := hδ.le),
    finrank_euclideanSpace, Fintype.card_fin, smul_eq_mul, ← mul_assoc, Real.rpow_sub hδ,
    Real.rpow_natCast, div_eq_mul_inv]

lemma term_le {n : ℕ} {α N : ℝ} (hα0 : 0 < α) (hN : 0 ≤ N) {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (k : Fin n → ℤ) :
    ENNReal.ofReal (gfun α N δ ‖zpt k‖) ≤
      ENNReal.ofReal ((1 + n) ^ α * (1 + n) ^ N) *
        ∫⁻ x in cube k, ENNReal.ofReal (gfun α N δ ‖x‖) := by
  rcases eq_or_ne k 0 with rfl | hk
  · have : zpt (0 : Fin n → ℤ) = 0 := by ext i; simp [zpt_apply]
    rw [this, norm_zero]
    simp [gfun, Real.zero_rpow (neg_ne_zero.2 hα0.ne')]
  have hr := one_le_norm_zpt hk
  have h1 := gfun_shift (c := (n : ℝ)) hα0.le hN hδ hδ1 hr (by positivity)
  calc ENNReal.ofReal (gfun α N δ ‖zpt k‖)
      ≤ ENNReal.ofReal ((1 + n) ^ α * (1 + n) ^ N * gfun α N δ (‖zpt k‖ + n)) :=
        ENNReal.ofReal_le_ofReal h1
    _ = ENNReal.ofReal ((1 + n) ^ α * (1 + n) ^ N) *
          ∫⁻ x in cube k, ENNReal.ofReal (gfun α N δ (‖zpt k‖ + n)) := by
        rw [setLIntegral_const, volume_cube, mul_one, ENNReal.ofReal_mul (by positivity)]
    _ ≤ _ := by
        refine mul_le_mul_right (setLIntegral_mono' (measurableSet_cube k) fun x hx => ?_) _
        apply ENNReal.ofReal_le_ofReal
        exact gfun_anti hα0.le hN hδ.le (norm_pos_iff.2 (ne_zero_of_mem_cube hk hx))
          (norm_le_of_mem_cube hx)

end BumpAux

theorem bump (n : ℕ) : ∃ φ : EuclideanSpace ℝ (Fin n) → ℝ, Continuous φ ∧ (∀ x, 0 ≤ φ x) ∧
    (∀ x, φ x ≠ 0 → ‖x‖ ≤ 1) ∧ ∫ x, φ x = 1 ∧
    ∀ N : ℕ, ∃ B : ℝ, ∀ δ : ℝ, 0 < δ → ∀ ξ : EuclideanSpace ℝ (Fin n),
      ‖𝓕 (fun x => ((δ ^ n)⁻¹ * φ (δ⁻¹ • x) : ℂ)) ξ‖ ≤ B * (1 + δ * ‖ξ‖) ^ (-(N : ℝ)) := by
  let f : ContDiffBump (0 : EuclideanSpace ℝ (Fin n)) := ⟨1/2, 1, by norm_num, by norm_num⟩
  let φ := f.normed volume
  have hφc : HasCompactSupport (fun x => (φ x : ℂ)) :=
    f.hasCompactSupport_normed.comp_left Complex.ofReal_zero
  have hφd : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun x => (φ x : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp f.contDiff_normed
  let G : SchwartzMap (EuclideanSpace ℝ (Fin n)) ℂ := hφc.toSchwartzMap hφd
  refine ⟨φ, (f.contDiff_normed (n := 0)).continuous, f.nonneg_normed, ?_, f.integral_normed, ?_⟩
  · intro x hx
    have : x ∈ Function.support φ := hx
    rw [f.support_normed_eq] at this
    simpa using (Metric.mem_ball.1 this).le
  · intro N
    let C := 2 ^ N * (Finset.Iic (N, 0)).sup (fun m => SchwartzMap.seminorm ℝ m.1 m.2) (𝓕 G)
    refine ⟨C, fun δ hδ ξ => ?_⟩
    have h := SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℝ) (m := (N, 0)) (k := N) (n := 0)
      le_rfl le_rfl (𝓕 G) (δ • ξ)
    rw [norm_iteratedFDeriv_zero, SchwartzMap.fourier_coe] at h
    have e : (fun x => ((δ ^ n)⁻¹ * φ (δ⁻¹ • x) : ℂ)) =
        (fun x => ((δ : ℂ) ^ n)⁻¹ * (fun y => (φ y : ℂ)) (δ⁻¹ • x)) := by
      ext x; push_cast; rfl
    rw [e, BumpAux.fourier_scale (fun y => (φ y : ℂ)) hδ]
    have hG : (G : EuclideanSpace ℝ (Fin n) → ℂ) = fun y => (φ y : ℂ) := rfl
    rw [hG] at h
    rw [norm_smul, Real.norm_of_nonneg hδ.le] at h
    have hpos : 0 < (1 + δ * ‖ξ‖) ^ N := by positivity
    rw [Real.rpow_neg (by positivity), Real.rpow_natCast, ← div_eq_mul_inv, le_div_iff₀ hpos,
      mul_comm]
    exact h

theorem latsum {n : ℕ} (hn : 1 ≤ n) {α : ℝ} (hα0 : 0 < α) (hαn : α < n) {N : ℝ} (hN : (n:ℝ) < N) :
    ∃ B : ℝ, ∀ δ : ℝ, 0 < δ → δ ≤ 1 →
      Summable (fun k : Fin n → ℤ => ‖zpt k‖ ^ (-α) * (1 + δ * ‖zpt k‖) ^ (-N)) ∧
      ∑' k : Fin n → ℤ, ‖zpt k‖ ^ (-α) * (1 + δ * ‖zpt k‖) ^ (-N) ≤ B * δ ^ (α - n) := by
  open BumpAux in
  set K : ℝ := (1 + n) ^ α * (1 + n) ^ N
  set I : ℝ := ∫ x : EuclideanSpace ℝ (Fin n), gfun α N 1 ‖x‖
  refine ⟨K * I, fun δ hδ hδ1 => ?_⟩
  have hN0 : 0 ≤ N := by have : (0:ℝ) ≤ n := by positivity
                         linarith
  obtain ⟨hint, heq⟩ := integral_scale hn hα0 hαn hN hδ
  have hF : ∀ k : Fin n → ℤ, 0 ≤ gfun α N δ ‖zpt k‖ := fun k => gfun_nonneg α N hδ.le (norm_nonneg _)
  have hsum : ∑' k : Fin n → ℤ, ENNReal.ofReal (gfun α N δ ‖zpt k‖) ≤
      ENNReal.ofReal (K * (δ ^ (α - n) * I)) := by
    calc ∑' k : Fin n → ℤ, ENNReal.ofReal (gfun α N δ ‖zpt k‖)
        ≤ ∑' k : Fin n → ℤ, ENNReal.ofReal K *
            ∫⁻ x in cube k, ENNReal.ofReal (gfun α N δ ‖x‖) :=
          ENNReal.tsum_le_tsum fun k => term_le hα0 hN0 hδ hδ1 k
      _ = ENNReal.ofReal K * ∫⁻ x in ⋃ k, cube k, ENNReal.ofReal (gfun α N δ ‖x‖) := by
          rw [ENNReal.tsum_mul_left, lintegral_iUnion measurableSet_cube cube_disjoint]
      _ ≤ ENNReal.ofReal K * ∫⁻ x, ENNReal.ofReal (gfun α N δ ‖x‖) := by
          gcongr; exact Measure.restrict_le_self
      _ = ENNReal.ofReal (K * (δ ^ (α - n) * I)) := by
          rw [← ofReal_integral_eq_lintegral_ofReal hint
            (Filter.Eventually.of_forall fun x => gfun_nonneg α N hδ.le (norm_nonneg _)), heq]
          exact (ENNReal.ofReal_mul (by positivity)).symm
  have hne : ∑' k : Fin n → ℤ, ENNReal.ofReal (gfun α N δ ‖zpt k‖) ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top hsum
  have hs : Summable (fun k : Fin n → ℤ => gfun α N δ ‖zpt k‖) := by
    have := ENNReal.summable_toReal hne
    simpa [ENNReal.toReal_ofReal (hF _)] using this
  refine ⟨hs, ?_⟩
  have h2 := ENNReal.ofReal_tsum_of_nonneg hF hs
  rw [← h2] at hsum
  have hI : 0 ≤ I := integral_nonneg fun x => gfun_nonneg α N zero_le_one (norm_nonneg _)
  have := (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 hsum
  calc _ = ∑' k : Fin n → ℤ, gfun α N δ ‖zpt k‖ := rfl
    _ ≤ _ := this
    _ = _ := by ring


-- ==== Core.lean ====

/-- number of integer points in `K`. -/
def latCount {n : ℕ} (K : Set (EuclideanSpace ℝ (Fin n))) : ℕ :=
  Set.ncard {k : Fin n → ℤ | zpt k ∈ K}

variable {n : ℕ}

@[simp] theorem zpt_apply (k : Fin n → ℤ) (i : Fin n) : zpt k i = (k i : ℝ) := rfl

theorem abs_le_norm_zpt (k : Fin n → ℤ) (i : Fin n) : |(k i : ℝ)| ≤ ‖zpt k‖ := by
  have := EuclideanSpace.norm_eq (zpt k)
  rw [this]
  calc |(k i : ℝ)| = Real.sqrt ((k i : ℝ) ^ 2) := (Real.sqrt_sq_eq_abs _).symm
    _ ≤ Real.sqrt (∑ j, ‖zpt k j‖ ^ 2) := by
      apply Real.sqrt_le_sqrt
      have : ‖zpt k i‖ ^ 2 = (k i : ℝ) ^ 2 := by simp [Real.norm_eq_abs, sq_abs]
      rw [← this]
      exact Finset.single_le_sum (f := fun j => ‖zpt k j‖ ^ 2) (fun j _ => by positivity)
        (Finset.mem_univ i)

theorem one_le_norm_zpt {k : Fin n → ℤ} (hk : k ≠ 0) : 1 ≤ ‖zpt k‖ := by
  obtain ⟨i, hi⟩ : ∃ i, k i ≠ 0 := by
    by_contra h; push Not at h; exact hk (funext h)
  have h1 : (1 : ℝ) ≤ |(k i : ℝ)| := by
    rw [← Int.cast_abs]; exact_mod_cast Int.one_le_abs hi
  exact h1.trans (abs_le_norm_zpt k i)

/-- integer points of a ball lie in a box. -/
theorem latSet_ball_subset (v : EuclideanSpace ℝ (Fin n)) (r : ℝ) :
    {k : Fin n → ℤ | zpt k ∈ Metric.closedBall v r} ⊆
      (Fintype.piFinset fun i => Finset.Icc ⌈v i - r⌉ ⌊v i + r⌋ : Set (Fin n → ℤ)) := by
  intro k hk
  simp only [Set.mem_ofPred_eq, Metric.mem_closedBall, dist_eq_norm] at hk
  simp only [Finset.mem_coe, Fintype.mem_piFinset, Finset.mem_Icc]
  intro i
  have h := (abs_le_norm_zpt (n := n) 0 i)
  have hi : |(zpt k - v) i| ≤ ‖zpt k - v‖ := by
    have := EuclideanSpace.norm_eq (zpt k - v)
    rw [this]
    calc |(zpt k - v) i| = Real.sqrt (((zpt k - v) i) ^ 2) := (Real.sqrt_sq_eq_abs _).symm
      _ ≤ _ := by
        apply Real.sqrt_le_sqrt
        have : ‖(zpt k - v) i‖ ^ 2 = ((zpt k - v) i) ^ 2 := by simp [Real.norm_eq_abs, sq_abs]
        rw [← this]
        exact Finset.single_le_sum (f := fun j => ‖(zpt k - v) j‖ ^ 2) (fun j _ => by positivity)
          (Finset.mem_univ i)
  have h2 : |(k i : ℝ) - v i| ≤ r := by
    have := hi.trans hk; simpa using this
  rw [abs_le] at h2
  constructor
  · exact Int.ceil_le.2 (by linarith)
  · exact Int.le_floor.2 (by linarith)

theorem latSet_finite_of_bounded {K : Set (EuclideanSpace ℝ (Fin n))}
    (hK : Bornology.IsBounded K) : {k : Fin n → ℤ | zpt k ∈ K}.Finite := by
  obtain ⟨r, hr⟩ := hK.subset_closedBall 0
  have h1 : {k : Fin n → ℤ | zpt k ∈ K} ⊆ {k | zpt k ∈ Metric.closedBall 0 r} :=
    fun k hk => hr hk
  exact Set.Finite.subset (Finset.finite_toSet _) (h1.trans (latSet_ball_subset 0 r))

theorem latCount_ball_le (v : EuclideanSpace ℝ (Fin n)) {r : ℝ} (hr : 0 ≤ r) :
    (latCount (Metric.closedBall v r) : ℝ) ≤ (2 * r + 1) ^ n := by
  unfold latCount
  have h := Set.ncard_le_ncard (latSet_ball_subset v r) (Finset.finite_toSet _)
  rw [Set.ncard_coe_finset, Fintype.card_piFinset] at h
  calc (Set.ncard {k : Fin n → ℤ | zpt k ∈ Metric.closedBall v r} : ℝ)
      ≤ ((∏ i, (Finset.Icc ⌈v i - r⌉ ⌊v i + r⌋).card : ℕ) : ℝ) := by exact_mod_cast h
    _ = ∏ i : Fin n, ((Finset.Icc ⌈v i - r⌉ ⌊v i + r⌋).card : ℝ) := by push_cast; rfl
    _ ≤ ∏ _i : Fin n, (2 * r + 1) := by
      gcongr with i
      rw [Int.card_Icc]
      rcases le_or_gt ⌈v i - r⌉ (⌊v i + r⌋ + 1) with h | h
      · have : ((⌊v i + r⌋ + 1 - ⌈v i - r⌉).toNat : ℝ) = ((⌊v i + r⌋ + 1 - ⌈v i - r⌉ : ℤ) : ℝ) := by
          rw [← Int.cast_natCast, Int.toNat_of_nonneg (by omega)]
        rw [this]; push_cast
        have := Int.floor_le (v i + r); have := Int.le_ceil (v i - r); linarith
      · rw [Int.toNat_of_nonpos (by omega)]; simp; positivity
    _ = (2 * r + 1) ^ n := by simp

/-- the lattice count as a sum of the indicator. -/
theorem latCount_eq_tsum {K : Set (EuclideanSpace ℝ (Fin n))} (hK : Bornology.IsBounded K) :
    (latCount K : ℝ) = ∑' k : Fin n → ℤ, K.indicator (1 : EuclideanSpace ℝ (Fin n) → ℝ) (zpt k) := by
  have hfin := latSet_finite_of_bounded hK
  unfold latCount
  rw [tsum_eq_sum (s := hfin.toFinset)]
  · rw [Set.ncard_eq_toFinset_card _ hfin]
    rw [Finset.sum_congr rfl (g := fun _ => (1:ℝ))]
    · simp
    · intro k hk
      simp only [Set.Finite.mem_toFinset, Set.mem_ofPred_eq] at hk
      simp [Set.indicator_of_mem hk]
  · intro k hk
    simp only [Set.Finite.mem_toFinset, Set.mem_ofPred_eq] at hk
    simp [hk]

section Hlawka
local notation "Eu" n => EuclideanSpace ℝ (Fin n)

theorem surj_bound {g : (Eu n) →L[ℝ] (Eu n)} {σ : ℝ} (hσ : 0 < σ)
    (hg : ∀ x, σ * ‖x‖ ≤ ‖g x‖) (w : Eu n) : ∃ u, g u = w ∧ σ * ‖u‖ ≤ ‖w‖ := by
  have hinj : Function.Injective (g : (Eu n) →ₗ[ℝ] (Eu n)) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro x hx
    have h := hg x
    have : g x = 0 := hx
    rw [this, norm_zero] at h
    have : ‖x‖ ≤ 0 := by nlinarith [norm_nonneg x]
    exact norm_le_zero_iff.1 this
  obtain ⟨u, hu⟩ := (LinearMap.injective_iff_surjective.1 hinj) w
  exact ⟨u, hu, by have := hg u; rwa [← hu]⟩

/-- the outer parallel body of an affine image of a convex body. -/
theorem sandwich_upper {C : Set (Eu n)} (hC : Convex ℝ C) {c0 : Eu n} {r0 : ℝ}
    (hball : Metric.closedBall c0 r0 ⊆ C) {g : (Eu n) →L[ℝ] (Eu n)} {σ : ℝ} (hσ : 0 < σ)
    (hg : ∀ x, σ * ‖x‖ ≤ ‖g x‖) {t s δ : ℝ} (ht : 0 < t) (hs : 1 < s)
    (hδ : δ ≤ (s - 1) * (t * σ * r0)) (v : Eu n) :
    ∀ y ∈ (fun x => t • g x + v) '' C, ∀ w : Eu n, ‖w‖ ≤ δ →
      y + w ∈ (fun x => (s * t) • g x + (s • v + (1 - s) • (t • g c0 + v))) '' C := by
  rintro _ ⟨x, hx, rfl⟩ w hw
  obtain ⟨u, rfl, hu⟩ := surj_bound hσ hg w
  have hs0 : 0 < s - 1 := by linarith
  set c := ((s - 1) * t)⁻¹ • u
  have hc : c0 + c ∈ C := by
    apply hball
    rw [Metric.mem_closedBall, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
      abs_of_pos (by positivity)]
    rw [inv_mul_le_iff₀ (by positivity)]
    have : σ * ‖u‖ ≤ (s - 1) * (t * σ * r0) := hu.trans hw |>.trans hδ
    nlinarith
  refine ⟨s⁻¹ • x + (1 - s⁻¹) • (c0 + c), hC hx hc (by positivity)
    (by rw [sub_nonneg]; exact inv_le_one_of_one_le₀ hs.le) (by ring), ?_⟩
  simp only [c, map_add, map_smul]
  have hs' : s ≠ 0 := by positivity
  have ht' : t ≠ 0 := ht.ne'
  have hs1 : s - 1 ≠ 0 := hs0.ne'
  match_scalars <;> field_simp <;> ring

theorem sandwich_lower {C : Set (Eu n)} (hC : Convex ℝ C) {c0 : Eu n} {r0 : ℝ}
    (hball : Metric.closedBall c0 r0 ⊆ C) {g : (Eu n) →L[ℝ] (Eu n)} {σ : ℝ} (hσ : 0 < σ)
    (hg : ∀ x, σ * ‖x‖ ≤ ‖g x‖) {t s δ : ℝ} (ht : 0 < t) (hs0 : 0 < s) (hs : s < 1)
    (hδ : δ ≤ (1 - s) * (t * σ * r0)) (v : Eu n) :
    ∀ y ∈ (fun x => (s * t) • g x + (s • v + (1 - s) • (t • g c0 + v))) '' C, ∀ w : Eu n,
      ‖w‖ ≤ δ → y + w ∈ (fun x => t • g x + v) '' C := by
  rintro _ ⟨x, hx, rfl⟩ w hw
  obtain ⟨u, rfl, hu⟩ := surj_bound hσ hg w
  have hs1 : 0 < 1 - s := by linarith
  set c := ((1 - s) * t)⁻¹ • u
  have hc : c0 + c ∈ C := by
    apply hball
    rw [Metric.mem_closedBall, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
      abs_of_pos (by positivity)]
    rw [inv_mul_le_iff₀ (by positivity)]
    have : σ * ‖u‖ ≤ (1 - s) * (t * σ * r0) := hu.trans hw |>.trans hδ
    nlinarith
  refine ⟨s • x + (1 - s) • (c0 + c), hC hx hc hs0.le hs1.le (by ring), ?_⟩
  simp only [c, map_add, map_smul]
  have ht' : t ≠ 0 := ht.ne'
  have hs1' : 1 - s ≠ 0 := hs1.ne'
  match_scalars <;> field_simp <;> ring

theorem fourier_affine_bound {C : Set (Eu n)} (hC : MeasurableSet C) {A α : ℝ} (hα : 0 ≤ α)
    (hdecay : ∀ ξ : Eu n, 1 ≤ ‖ξ‖ →
      ‖𝓕 (C.indicator (1 : (Eu n) → ℂ)) ξ‖ ≤ A * ‖ξ‖ ^ (-α))
    {g : (Eu n) →L[ℝ] (Eu n)} (hdet : LinearMap.det (g : (Eu n) →ₗ[ℝ] (Eu n)) ≠ 0)
    {σ : ℝ} (hσ : 0 < σ) (hgs : ∀ x, σ * ‖x‖ ≤ ‖(ContinuousLinearMap.adjoint g) x‖)
    {t : ℝ} (ht : 0 < t) (htσ : 1 ≤ t * σ) (v : Eu n) {k : Fin n → ℤ} (hk : k ≠ 0) :
    ‖𝓕 (((fun x => t • g x + v) '' C).indicator (1 : (Eu n) → ℂ)) (zpt k)‖ ≤
      |LinearMap.det (g : (Eu n) →ₗ[ℝ] (Eu n))| * A * σ ^ (-α) * t ^ ((n : ℝ) - α) *
        ‖zpt k‖ ^ (-α) := by
  rw [fourier_affine C hC t ht g hdet v (zpt k)]
  set d := |LinearMap.det (g : (Eu n) →ₗ[ℝ] (Eu n))|
  set ξ' := t • (ContinuousLinearMap.adjoint g) (zpt k)
  have hk1 := one_le_norm_zpt hk
  have hξ' : t * σ * ‖zpt k‖ ≤ ‖ξ'‖ := by
    simp only [ξ', norm_smul, Real.norm_eq_abs, abs_of_pos ht]
    have := hgs (zpt k); nlinarith
  have hpos : 0 < t * σ * ‖zpt k‖ := by positivity
  have h1 : 1 ≤ ‖ξ'‖ := le_trans (by nlinarith) hξ'
  have hd := hdecay ξ' h1
  have hA : 0 ≤ A := by
    have : 0 < ‖ξ'‖ ^ (-α) := Real.rpow_pos_of_pos (by linarith) _
    by_contra hA; push Not at hA
    have := mul_neg_of_neg_of_pos hA this
    linarith [norm_nonneg (𝓕 (C.indicator (1 : (Eu n) → ℂ)) ξ')]
  have hd2 : ‖𝓕 (C.indicator (1 : (Eu n) → ℂ)) ξ'‖ ≤ A * (t * σ * ‖zpt k‖) ^ (-α) :=
    hd.trans (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_nonpos hpos hξ' (by linarith)) hA)
  rw [norm_mul, norm_mul, Circle.norm_coe, one_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (by positivity)]
  have ht2 : t ^ n * (t * σ * ‖zpt k‖) ^ (-α) = t ^ ((n : ℝ) - α) * σ ^ (-α) * ‖zpt k‖ ^ (-α) := by
    rw [Real.mul_rpow (by positivity) (by positivity), Real.mul_rpow ht.le hσ.le,
      ← Real.rpow_natCast, sub_eq_add_neg, Real.rpow_add ht]
    ring
  calc t ^ n * d * ‖𝓕 (C.indicator (1 : (Eu n) → ℂ)) ξ'‖
      ≤ t ^ n * d * (A * (t * σ * ‖zpt k‖) ^ (-α)) :=
        mul_le_mul_of_nonneg_left hd2 (by positivity)
    _ = d * A * (t ^ n * (t * σ * ‖zpt k‖) ^ (-α)) := by ring
    _ = _ := by rw [ht2]; ring

theorem zpt_zero : zpt (0 : Fin n → ℤ) = 0 := by ext i; simp

theorem poisson_estimate {K : Set (Eu n)} (hK : MeasurableSet K) (hKb : Bornology.IsBounded K)
    {ψ : (Eu n) → ℝ} (hψc : Continuous ψ) (hψ1 : ∫ x, ψ x = 1) {δ : ℝ}
    (hψs : ∀ x, ψ x ≠ 0 → ‖x‖ ≤ δ) {β : (Fin n → ℤ) → ℝ} (hβs : Summable β)
    (hβ0 : 0 ≤ β 0) (hbound : ∀ k, k ≠ 0 → ‖𝓕 (smooth K ψ) (zpt k)‖ ≤ β k) :
    Summable (fun k => (smooth K ψ (zpt k)).re) ∧
      |∑' k, (smooth K ψ (zpt k)).re - (volume K).toReal| ≤ ∑' k, β k := by
  set F := smooth K ψ
  set V : ℂ := ((volume K).toReal : ℂ)
  set c : (Fin n → ℤ) → ℂ := fun k => 𝓕 F (zpt k) - if k = 0 then V else 0
  have hc : ∀ k, ‖c k‖ ≤ β k := by
    intro k
    by_cases hk : k = 0
    · subst hk
      simp only [c, if_true, zpt_zero, F, fourier_smooth_zero K hK hKb ψ hψ1, V, sub_self,
        norm_zero]
      exact hβ0
    · simp only [c, hk, if_false, sub_zero]; exact hbound k hk
  have hcs : Summable c := Summable.of_norm_bounded hβs hc
  have hite : HasSum (fun k : Fin n → ℤ => if k = 0 then V else 0) V := hasSum_ite_eq 0 V
  have hFs : Summable (fun k => 𝓕 F (zpt k)) := by
    have := hcs.add hite.summable
    simpa [c] using this
  have hP := poisson F (smooth_continuous K hK ψ hψc δ hψs)
    (smooth_hasCompactSupport K hKb ψ δ hψs) hFs
  have htot : ∑' k, 𝓕 F (zpt k) = ∑' k, c k + V := by
    rw [← hite.tsum_eq, ← hcs.tsum_add hite.summable]
    congr 1; ext k; simp [c]
  have hre : HasSum (fun k => (F (zpt k)).re) (∑' k, 𝓕 F (zpt k)).re :=
    Complex.hasSum_re hP
  refine ⟨hre.summable, ?_⟩
  rw [hre.tsum_eq, htot]
  have : (∑' k, c k + V).re - (volume K).toReal = (∑' k, c k).re := by simp [V]
  rw [this]
  calc |(∑' k, c k).re| ≤ ‖∑' k, c k‖ := Complex.abs_re_le_norm _
    _ ≤ ∑' k, ‖c k‖ := norm_tsum_le_tsum_norm (Summable.of_norm_bounded hβs hc).norm
    _ ≤ ∑' k, β k := Summable.tsum_le_tsum hc (Summable.of_norm_bounded hβs hc).norm hβs

theorem pow_sub_one_le {s : ℝ} (hs0 : 0 ≤ s) (hs2 : s ≤ 2) (m : ℕ) :
    |s ^ m - 1| ≤ m * 2 ^ m * |s - 1| := by
  rw [← geom_sum_mul, abs_mul]
  gcongr
  calc |∑ i ∈ Finset.range m, s ^ i| ≤ ∑ i ∈ Finset.range m, |s ^ i| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i ∈ Finset.range m, (2:ℝ) ^ m := by
        apply Finset.sum_le_sum; intro i hi
        rw [abs_of_nonneg (by positivity)]
        calc s ^ i ≤ 2 ^ i := pow_le_pow_left₀ hs0 hs2 i
          _ ≤ 2 ^ m := pow_le_pow_right₀ (by norm_num) (Finset.mem_range.1 hi).le
    _ = m * 2 ^ m := by simp

theorem det_ne_zero_of_bound {g : (Eu n) →L[ℝ] (Eu n)} {σ : ℝ} (hσ : 0 < σ)
    (hg : ∀ x, σ * ‖x‖ ≤ ‖g x‖) : LinearMap.det (g : (Eu n) →ₗ[ℝ] (Eu n)) ≠ 0 := by
  have hker : LinearMap.ker (g : (Eu n) →ₗ[ℝ] (Eu n)) = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro x hx
    have h := hg x
    have : g x = 0 := hx
    rw [this, norm_zero] at h
    have : ‖x‖ ≤ 0 := by nlinarith [norm_nonneg x]
    exact norm_le_zero_iff.1 this
  have hu := (LinearMap.isUnit_iff_ker_eq_bot _).2 hker
  exact (LinearMap.isUnit_iff_isUnit_det _).1 hu |>.ne_zero

/-- The scaled bump `δ⁻ⁿ φ(x/δ)`. -/
def scaled (φ : (Eu n) → ℝ) (δ : ℝ) : (Eu n) → ℝ := fun x => (δ ^ n)⁻¹ * φ (δ⁻¹ • x)

theorem scaled_props {φ : (Eu n) → ℝ} (hφc : Continuous φ) (hφ0 : ∀ x, 0 ≤ φ x)
    (hφs : ∀ x, φ x ≠ 0 → ‖x‖ ≤ 1) (hφ1 : ∫ x, φ x = 1) {δ : ℝ} (hδ : 0 < δ) :
    Continuous (scaled φ δ) ∧ (∀ x, 0 ≤ scaled φ δ x) ∧ (∀ x, scaled φ δ x ≠ 0 → ‖x‖ ≤ δ) ∧
      ∫ x, scaled φ δ x = 1 := by
  refine ⟨?_, fun x => by unfold scaled; have := hφ0 (δ⁻¹ • x); positivity, ?_, ?_⟩
  · unfold scaled; fun_prop
  · intro x hx
    unfold scaled at hx
    have h := hφs _ (right_ne_zero_of_mul hx)
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.2 hδ), inv_mul_le_iff₀ hδ] at h
    linarith
  · unfold scaled
    rw [integral_const_mul, MeasureTheory.Measure.integral_comp_inv_smul, hφ1]
    simp only [finrank_euclideanSpace, Fintype.card_fin, smul_eq_mul, mul_one]
    rw [abs_of_pos (by positivity)]
    field_simp

/-- One side of the Poisson estimate for an affine image of `C`. -/
theorem side_estimate {C : Set (Eu n)} (hCk : IsCompact C) {A α : ℝ} (hα : 0 < α)
    (hdecay : ∀ ξ : Eu n, 1 ≤ ‖ξ‖ →
      ‖𝓕 (C.indicator (1 : (Eu n) → ℂ)) ξ‖ ≤ A * ‖ξ‖ ^ (-α)) (hA : 0 ≤ A)
    {g : (Eu n) →L[ℝ] (Eu n)} {σ : ℝ} (hσ : 0 < σ) (hg : ∀ x, σ * ‖x‖ ≤ ‖g x‖)
    (hgs : ∀ x, σ * ‖x‖ ≤ ‖(ContinuousLinearMap.adjoint g) x‖)
    {t : ℝ} (ht : 0 < t) (htσ : 1 ≤ t * σ) (v : Eu n)
    {ψ : (Eu n) → ℝ} (hψc : Continuous ψ) (hψ1 : ∫ x, ψ x = 1) {δ : ℝ}
    (hψs : ∀ x, ψ x ≠ 0 → ‖x‖ ≤ δ) {N B B' : ℝ} (hB : 0 ≤ B)
    (hψF : ∀ ξ, ‖𝓕 (fun x => (ψ x : ℂ)) ξ‖ ≤ B * (1 + δ * ‖ξ‖) ^ (-N))
    (hsum : Summable (fun k : Fin n → ℤ => ‖zpt k‖ ^ (-α) * (1 + δ * ‖zpt k‖) ^ (-N)))
    (hsumle : ∑' k : Fin n → ℤ, ‖zpt k‖ ^ (-α) * (1 + δ * ‖zpt k‖) ^ (-N) ≤ B') :
    Summable (fun k => (smooth ((fun x => t • g x + v) '' C) ψ (zpt k)).re) ∧
    |∑' k, (smooth ((fun x => t • g x + v) '' C) ψ (zpt k)).re -
        t ^ n * |LinearMap.det (g : (Eu n) →ₗ[ℝ] (Eu n))| * (volume C).toReal| ≤
      |LinearMap.det (g : (Eu n) →ₗ[ℝ] (Eu n))| * A * σ ^ (-α) * t ^ ((n : ℝ) - α) * B * B' := by
  have hdet := det_ne_zero_of_bound hσ hg
  set K := (fun x => t • g x + v) '' C
  have hTc : Continuous (fun x : Eu n => t • g x + v) := by fun_prop
  have hKk : IsCompact K := hCk.image hTc
  have hKm : MeasurableSet K := hKk.isClosed.measurableSet
  have hCm : MeasurableSet C := hCk.isClosed.measurableSet
  set d := |LinearMap.det (g : (Eu n) →ₗ[ℝ] (Eu n))|
  set κ := d * A * σ ^ (-α) * t ^ ((n : ℝ) - α) * B
  have hκ : 0 ≤ κ := by positivity
  set β : (Fin n → ℤ) → ℝ := fun k => κ * (‖zpt k‖ ^ (-α) * (1 + δ * ‖zpt k‖) ^ (-N))
  have hβs : Summable β := hsum.mul_left κ
  have hβ0 : 0 ≤ β 0 := by
    simp only [β, zpt_zero, norm_zero, Real.zero_rpow (by linarith : -α ≠ 0), zero_mul, mul_zero,
      le_refl]
  have hbound : ∀ k, k ≠ 0 → ‖𝓕 (smooth K ψ) (zpt k)‖ ≤ β k := by
    intro k hk
    rw [fourier_smooth K hKm hKk.isBounded ψ hψ1, norm_mul]
    have h1 := fourier_affine_bound hCm hα.le hdecay hdet hσ hgs ht htσ v hk
    have h2 := hψF (zpt k)
    calc _ ≤ (d * A * σ ^ (-α) * t ^ ((n : ℝ) - α) * ‖zpt k‖ ^ (-α)) *
          (B * (1 + δ * ‖zpt k‖) ^ (-N)) :=
          mul_le_mul h1 h2 (norm_nonneg _) (by positivity)
      _ = β k := by simp only [β, κ]; ring
  obtain ⟨hs, hle⟩ := poisson_estimate hKm hKk.isBounded hψc hψ1 hψs hβs hβ0 hbound
  refine ⟨hs, ?_⟩
  have hvol : (volume K).toReal = t ^ n * d * (volume C).toReal := by
    simp only [K]
    rw [vol_affine C t ht g v, ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity)]
  rw [← hvol]
  calc _ ≤ ∑' k, β k := hle
    _ = κ * ∑' k : Fin n → ℤ, ‖zpt k‖ ^ (-α) * (1 + δ * ‖zpt k‖) ^ (-N) := tsum_mul_left
    _ ≤ κ * B' := mul_le_mul_of_nonneg_left hsumle hκ

theorem latCount_mono {K K' : Set (Eu n)} (h : K ⊆ K') (hK' : Bornology.IsBounded K') :
    latCount K ≤ latCount K' :=
  Set.ncard_le_ncard (fun k hk => h hk) (latSet_finite_of_bounded hK')

/-- The exponent `n - 2 + 2/(n+1)` of Hlawka's bound. -/
def hlawkaExp (n : ℕ) : ℝ := (n : ℝ) - 2 + 2 / ((n : ℝ) + 1)

theorem hlawkaExp_nonneg (hn : 2 ≤ n) : 0 ≤ hlawkaExp n := by
  unfold hlawkaExp
  have : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have : 0 < 2 / ((n : ℝ) + 1) := by positivity
  linarith

set_option maxHeartbeats 2000000 in
/-- **Uniform lattice-point bound** (Hlawka's argument), for a convex body whose indicator has
Fourier decay `|ξ|^{-(n+1)/2}`, uniformly over linear maps with explicit bounds. -/
theorem hlawka_core (hn : 2 ≤ n) {C : Set (Eu n)} (hCc : Convex ℝ C) (hCk : IsCompact C)
    {c0 : Eu n} {r0 : ℝ} (hr0 : 0 < r0) (hball : Metric.closedBall c0 r0 ⊆ C) {A : ℝ}
    (hdecay : ∀ ξ : Eu n, 1 ≤ ‖ξ‖ →
      ‖𝓕 (C.indicator (1 : (Eu n) → ℂ)) ξ‖ ≤ A * ‖ξ‖ ^ (-(((n : ℝ) + 1) / 2)))
    {σ M D : ℝ} (hσ : 0 < σ) :
    ∃ c : ℝ, ∀ t : ℝ, 1 ≤ t → ∀ g : (Eu n) →L[ℝ] (Eu n), (∀ x, σ * ‖x‖ ≤ ‖g x‖) →
      (∀ x, σ * ‖x‖ ≤ ‖(ContinuousLinearMap.adjoint g) x‖) → ‖g‖ ≤ M →
      |LinearMap.det (g : (Eu n) →ₗ[ℝ] (Eu n))| ≤ D → ∀ v : Eu n,
      |(latCount ((fun x => t • g x + v) '' C) : ℝ) -
          t ^ n * |LinearMap.det (g : (Eu n) →ₗ[ℝ] (Eu n))| * (volume C).toReal| ≤
        c * t ^ hlawkaExp n := by
  have hn1 : 1 ≤ n := by omega
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  set α : ℝ := ((n : ℝ) + 1) / 2 with hα_def
  have hα : 0 < α := by positivity
  have hαn : α < n := by rw [hα_def]; linarith
  set θ : ℝ := ((n : ℝ) - 1) / ((n : ℝ) + 1) with hθ_def
  have hθ0 : 0 ≤ θ := div_nonneg (by linarith) (by positivity)
  set e := hlawkaExp n
  have he0 : 0 ≤ e := hlawkaExp_nonneg hn
  obtain ⟨φ, hφc, hφ0, hφs, hφ1, hφF⟩ := bump n
  obtain ⟨B, hB⟩ := hφF (n + 1)
  obtain ⟨B', hB'⟩ := latsum hn1 hα hαn (N := ((n + 1 : ℕ) : ℝ)) (by push_cast; linarith)
  set A' := max A 0
  have hdecay' : ∀ ξ : Eu n, 1 ≤ ‖ξ‖ →
      ‖𝓕 (C.indicator (1 : (Eu n) → ℂ)) ξ‖ ≤ A' * ‖ξ‖ ^ (-α) := fun ξ hξ =>
    (hdecay ξ hξ).trans (mul_le_mul_of_nonneg_right (le_max_left _ _)
      (Real.rpow_nonneg (norm_nonneg _) _))
  set B1 := max B 0
  set B2 := max B' 0
  set D' := max D 0
  set M' := max M 0
  set V := (volume C).toReal
  have hV : 0 ≤ V := ENNReal.toReal_nonneg
  obtain ⟨R, hR⟩ := hCk.isBounded.subset_closedBall 0
  set R' := max R 0
  set t0 := max 1 (max (2 / σ) (2 / (σ * r0)))
  set c1 := D' * V * n * 2 ^ n / (σ * r0)
  set c2 := D' * A' * σ ^ (-α) * (2:ℝ) ^ ((n : ℝ) - α) * B1 * B2
  set c3 := (2 * (t0 * M' * R') + 1) ^ n + t0 ^ n * D' * V
  refine ⟨c1 + c2 + c3, ?_⟩
  intro t ht g hg hgs hgM hgD v
  set d := |LinearMap.det (g : (Eu n) →ₗ[ℝ] (Eu n))|
  have hd0 : 0 ≤ d := abs_nonneg _
  have hdD : d ≤ D' := hgD.trans (le_max_left _ _)
  have ht0 : 0 < t := by linarith
  have hte : 1 ≤ t ^ e := Real.one_le_rpow ht he0
  have hc1 : 0 ≤ c1 := by positivity
  have hc2 : 0 ≤ c2 := by positivity
  have hc3 : 0 ≤ c3 := by positivity
  set K := (fun x => t • g x + v) '' C
  have hTc : Continuous (fun x : Eu n => t • g x + v) := by fun_prop
  have hKk : IsCompact K := hCk.image hTc
  have hcount0 : (0 : ℝ) ≤ latCount K := Nat.cast_nonneg _
  by_cases hsmall : t < t0
  · -- trivial bound
    have hsub : K ⊆ Metric.closedBall v (t * M' * R') := by
      rintro _ ⟨x, hx, rfl⟩
      rw [Metric.mem_closedBall, dist_eq_norm, add_sub_cancel_right, norm_smul,
        Real.norm_eq_abs, abs_of_pos ht0]
      have hx' : ‖x‖ ≤ R' := by
        have := hR hx; rw [Metric.mem_closedBall, dist_zero_right] at this
        exact this.trans (le_max_left _ _)
      calc t * ‖g x‖ ≤ t * (‖g‖ * ‖x‖) := by gcongr; exact g.le_opNorm x
        _ ≤ t * (M' * R') := by
          apply mul_le_mul_of_nonneg_left _ ht0.le
          exact mul_le_mul (hgM.trans (le_max_left _ _)) hx' (norm_nonneg _) (le_max_right _ _)
        _ = t * M' * R' := by ring
    have hcnt : (latCount K : ℝ) ≤ (2 * (t0 * M' * R') + 1) ^ n := by
      calc (latCount K : ℝ) ≤ latCount (Metric.closedBall v (t * M' * R')) := by
            exact_mod_cast latCount_mono hsub Metric.isBounded_closedBall
        _ ≤ (2 * (t * M' * R') + 1) ^ n := latCount_ball_le v (by positivity)
        _ ≤ _ := by gcongr
    have hmain : t ^ n * d * V ≤ t0 ^ n * D' * V := by
      gcongr
    have : |(latCount K : ℝ) - t ^ n * d * V| ≤ c3 := by
      have hX : 0 ≤ t ^ n * d * V := by positivity
      have hY : 0 ≤ t0 ^ n * D' * V := by positivity
      have hZ : 0 ≤ (2 * (t0 * M' * R') + 1) ^ n := by positivity
      rw [abs_le]; constructor <;> linarith
    calc _ ≤ c3 := this
      _ ≤ c3 * t ^ e := le_mul_of_one_le_right hc3 hte
      _ ≤ (c1 + c2 + c3) * t ^ e := by gcongr; linarith
  · push Not at hsmall
    have htσ2 : 2 ≤ t * σ := by
      have : 2 / σ ≤ t := (le_max_left _ _).trans ((le_max_right _ _).trans hsmall)
      rwa [div_le_iff₀ hσ] at this
    have hρ2 : 2 ≤ t * σ * r0 := by
      have : 2 / (σ * r0) ≤ t := (le_max_right _ _).trans ((le_max_right _ _).trans hsmall)
      rw [div_le_iff₀ (by positivity)] at this; linarith
    set ρ := t * σ * r0 with hρ_def
    have hρ0 : 0 < ρ := by linarith
    set δ := t ^ (-θ) with hδ_def
    have hδ0 : 0 < δ := Real.rpow_pos_of_pos ht0 _
    have hδ1 : δ ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos ht (by linarith)
    set q := δ / ρ with hq_def
    have hq0 : 0 < q := div_pos hδ0 hρ0
    have hq1 : q ≤ 1 / 2 := by
      rw [div_le_iff₀ hρ0]; linarith
    set sp := 1 + q
    set sm := 1 - q
    set x0 := t • g c0 + v
    set Kp := (fun x => (sp * t) • g x + (sp • v + (1 - sp) • x0)) '' C
    set Km := (fun x => (sm * t) • g x + (sm • v + (1 - sm) • x0)) '' C
    set ψ := scaled φ δ
    obtain ⟨hψc, hψ0, hψs, hψ1⟩ := scaled_props hφc hφ0 hφs hφ1 hδ0
    have hψF : ∀ ξ, ‖𝓕 (fun x => (ψ x : ℂ)) ξ‖ ≤ B1 * (1 + δ * ‖ξ‖) ^ (-(((n + 1 : ℕ) : ℝ))) := by
      intro ξ
      have heq : (fun x => (ψ x : ℂ)) = fun x => ((δ ^ n)⁻¹ * φ (δ⁻¹ • x) : ℂ) := by
        funext x; simp [ψ, scaled]
      rw [heq]
      exact (hB δ hδ0 ξ).trans (mul_le_mul_of_nonneg_right (le_max_left _ _)
        (Real.rpow_nonneg (by positivity) _))
    obtain ⟨hsum, hsumle⟩ := hB' δ hδ0 hδ1
    have hsumle' : ∑' k : Fin n → ℤ, ‖zpt k‖ ^ (-α) * (1 + δ * ‖zpt k‖) ^ (-(((n + 1 : ℕ) : ℝ)))
        ≤ B2 * δ ^ (α - n) :=
      hsumle.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg hδ0.le _))
    have hA' : 0 ≤ A' := le_max_right _ _
    have hB1 : 0 ≤ B1 := le_max_right _ _
    obtain ⟨hsP, hP⟩ := side_estimate hCk hα hdecay' hA' hσ hg hgs (t := sp * t) (by positivity)
      (by nlinarith) (sp • v + (1 - sp) • x0) hψc hψ1 hψs hB1 hψF hsum hsumle'
    obtain ⟨hsM, hM⟩ := side_estimate hCk hα hdecay' hA' hσ hg hgs (t := sm * t)
      (by nlinarith) (by nlinarith) (sm • v + (1 - sm) • x0) hψc hψ1 hψs hB1 hψF hsum hsumle'
    have hup : ∀ x, K.indicator (1 : (Eu n) → ℝ) x ≤ (smooth Kp ψ x).re :=
      smooth_ge_indicator K Kp ψ hψ0 δ hψs hψ1
        (sandwich_upper hCc hball hσ hg ht0 (by linarith)
          (by rw [show (sp - 1) * (t * σ * r0) = δ by simp only [sp, q, ρ]; field_simp; ring]) v)
    have hlo : ∀ x, (smooth Km ψ x).re ≤ K.indicator (1 : (Eu n) → ℝ) x :=
      smooth_le_indicator K Km ψ hψ0 δ hψs hψ1
        (sandwich_lower hCc hball hσ hg ht0 (by linarith) (by linarith)
          (by rw [show (1 - sm) * (t * σ * r0) = δ by simp only [sm, q, ρ]; field_simp; ring]) v)
    have hind0 : ∀ x, 0 ≤ K.indicator (1 : (Eu n) → ℝ) x := fun x =>
      Set.indicator_nonneg (fun _ _ => zero_le_one) x
    have hsK : Summable (fun k => K.indicator (1 : (Eu n) → ℝ) (zpt k)) :=
      Summable.of_nonneg_of_le (fun k => hind0 _) (fun k => hup _) hsP
    have hcnt : (latCount K : ℝ) = ∑' k, K.indicator (1 : (Eu n) → ℝ) (zpt k) :=
      latCount_eq_tsum hKk.isBounded
    have hcU : (latCount K : ℝ) ≤ ∑' k, (smooth Kp ψ (zpt k)).re := by
      rw [hcnt]; exact Summable.tsum_le_tsum (fun k => hup _) hsK hsP
    have hcL : ∑' k, (smooth Km ψ (zpt k)).re ≤ (latCount K : ℝ) := by
      rw [hcnt]; exact Summable.tsum_le_tsum (fun k => hlo _) hsM hsK
    -- error terms
    have hexp1 : t ^ ((n : ℝ) - α) * δ ^ (α - n) = t ^ e := by
      rw [hδ_def, ← Real.rpow_mul ht0.le, ← Real.rpow_add ht0]
      congr 1
      simp only [e, hlawkaExp, hα_def, hθ_def]
      field_simp; ring
    have hexp2 : t ^ (n - 1) * δ = t ^ e := by
      rw [hδ_def, ← Real.rpow_natCast, ← Real.rpow_add ht0]
      congr 1
      simp only [e, hlawkaExp, hθ_def]
      rw [Nat.cast_sub hn1]
      field_simp; ring
    have hEbound : ∀ s : ℝ, 0 < s → s ≤ 2 →
        d * A' * σ ^ (-α) * (s * t) ^ ((n : ℝ) - α) * B1 * (B2 * δ ^ (α - n)) ≤ c2 * t ^ e := by
      intro s hs0 hs2
      have hst : s * t ≤ 2 * t := mul_le_mul_of_nonneg_right hs2 ht0.le
      have h1 : (s * t) ^ ((n : ℝ) - α) ≤ (2:ℝ) ^ ((n : ℝ) - α) * t ^ ((n : ℝ) - α) := by
        rw [← Real.mul_rpow (by norm_num) ht0.le]
        exact Real.rpow_le_rpow (mul_pos hs0 ht0).le hst (sub_nonneg.2 hαn.le)
      have hB2 : 0 ≤ B2 := le_max_right _ _
      have hσα : 0 ≤ σ ^ (-α) := Real.rpow_nonneg hσ.le _
      have hδα : 0 ≤ δ ^ (α - n) := Real.rpow_nonneg hδ0.le _
      have hstα : 0 ≤ (s * t) ^ ((n : ℝ) - α) := Real.rpow_nonneg (mul_pos hs0 ht0).le _
      have hX : 0 ≤ A' * σ ^ (-α) := mul_nonneg hA' hσα
      have hY : 0 ≤ B1 * (B2 * δ ^ (α - n)) := mul_nonneg hB1 (mul_nonneg hB2 hδα)
      calc d * A' * σ ^ (-α) * (s * t) ^ ((n : ℝ) - α) * B1 * (B2 * δ ^ (α - n))
          = d * (A' * σ ^ (-α)) * (s * t) ^ ((n : ℝ) - α) * (B1 * (B2 * δ ^ (α - n))) := by ring
        _ ≤ D' * (A' * σ ^ (-α)) * ((2:ℝ) ^ ((n : ℝ) - α) * t ^ ((n : ℝ) - α)) *
              (B1 * (B2 * δ ^ (α - n))) := by
            apply mul_le_mul_of_nonneg_right _ hY
            apply mul_le_mul (mul_le_mul_of_nonneg_right hdD hX) h1 hstα
            exact mul_nonneg (le_max_right _ _) hX
        _ = c2 * (t ^ ((n : ℝ) - α) * δ ^ (α - n)) := by simp only [c2]; ring
        _ = c2 * t ^ e := congrArg (fun z => c2 * z) hexp1
    have hmain : ∀ s : ℝ, 0 ≤ s → s ≤ 2 → |s - 1| = q →
        |(s * t) ^ n * d * V - t ^ n * d * V| ≤ c1 * t ^ e := by
      intro s hs0 hs2 hsq
      have hb := pow_sub_one_le hs0 hs2 n
      rw [hsq] at hb
      have : (s * t) ^ n * d * V - t ^ n * d * V = (s ^ n - 1) * (t ^ n * d * V) := by ring
      rw [this, abs_mul, abs_of_nonneg (by positivity : 0 ≤ t ^ n * d * V), ← hexp2]
      have htn : t ^ n = t * t ^ (n - 1) := by
        rw [← pow_succ']; congr 1; omega
      calc |s ^ n - 1| * (t ^ n * d * V) ≤ (n * 2 ^ n * q) * (t ^ n * D' * V) := by
            gcongr
        _ = c1 * (t ^ (n - 1) * δ) := by
            simp only [c1, q, ρ, htn]; field_simp
    have hEp := hEbound sp (by positivity) (by linarith)
    have hEm := hEbound sm (by linarith) (by linarith)
    have hmp := hmain sp (by positivity) (by linarith) (by simp [sp, abs_of_pos hq0])
    have hmm := hmain sm (by linarith) (by linarith) (by simp [sm, abs_of_pos hq0])
    rw [abs_le] at hP hM hmp hmm ⊢
    have hc3t : 0 ≤ c3 * t ^ e := by positivity
    constructor <;> nlinarith

set_option synthInstance.maxHeartbeats 400000 in
/-- Bounds `σ, M, D` on a compact set of invertible maps. -/
theorem bounds_of_compact {G : Set ((Eu n) →L[ℝ] (Eu n))} (hG : IsCompact G)
    (hGu : ∀ g ∈ G, IsUnit g) : ∃ σ : ℝ, 0 < σ ∧ ∃ M D : ℝ, ∀ g ∈ G,
      (∀ x, σ * ‖x‖ ≤ ‖g x‖) ∧ (∀ x, σ * ‖x‖ ≤ ‖(ContinuousLinearMap.adjoint g) x‖) ∧
      ‖g‖ ≤ M ∧ |LinearMap.det (g : (Eu n) →ₗ[ℝ] (Eu n))| ≤ D := by
  obtain ⟨M, hM⟩ := hG.exists_bound_of_continuousOn (f := fun g => g) continuousOn_id
  obtain ⟨D, hD⟩ := hG.exists_bound_of_continuousOn
    (f := fun g : (Eu n) →L[ℝ] (Eu n) => g.det) ContinuousLinearMap.continuous_det.continuousOn
  have hinv : ContinuousOn (fun g : (Eu n) →L[ℝ] (Eu n) => Ring.inverse g) G := by
    intro g hg
    obtain ⟨u, rfl⟩ := hGu g hg
    exact (NormedRing.inverse_continuousAt u).continuousWithinAt
  obtain ⟨Mi, hMi⟩ := hG.exists_bound_of_continuousOn hinv
  set Mi' := max Mi 1
  have hMi' : 0 < Mi' := lt_of_lt_of_le one_pos (le_max_right _ _)
  refine ⟨Mi'⁻¹, inv_pos.2 hMi', M, D, fun g hg => ⟨?_, ?_, hM g hg, ?_⟩⟩
  · intro x
    have h1 : Ring.inverse g * g = 1 := Ring.inverse_mul_cancel g (hGu g hg)
    have hx : x = (Ring.inverse g) (g x) := by
      rw [← ContinuousLinearMap.mul_apply, h1]; rfl
    have : ‖x‖ ≤ Mi' * ‖g x‖ := by
      calc ‖x‖ = ‖(Ring.inverse g) (g x)‖ := by rw [← hx]
        _ ≤ ‖Ring.inverse g‖ * ‖g x‖ := (Ring.inverse g).le_opNorm _
        _ ≤ Mi' * ‖g x‖ := by
          gcongr; exact (hMi g hg).trans (le_max_left _ _)
    rw [inv_mul_le_iff₀ hMi']; exact this
  · intro x
    have h1 : g * Ring.inverse g = 1 := Ring.mul_inverse_cancel g (hGu g hg)
    have h2 : (ContinuousLinearMap.adjoint (Ring.inverse g)) ∘L (ContinuousLinearMap.adjoint g) =
        ContinuousLinearMap.id ℝ (Eu n) := by
      rw [← ContinuousLinearMap.adjoint_comp]
      have : g ∘L Ring.inverse g = ContinuousLinearMap.id ℝ (Eu n) := h1
      rw [this]; exact ContinuousLinearMap.adjoint_id
    have hx : x = (ContinuousLinearMap.adjoint (Ring.inverse g))
        ((ContinuousLinearMap.adjoint g) x) := by
      rw [← ContinuousLinearMap.comp_apply, h2]; rfl
    have : ‖x‖ ≤ Mi' * ‖(ContinuousLinearMap.adjoint g) x‖ := by
      calc ‖x‖ = ‖(ContinuousLinearMap.adjoint (Ring.inverse g))
            ((ContinuousLinearMap.adjoint g) x)‖ := by rw [← hx]
        _ ≤ ‖ContinuousLinearMap.adjoint (Ring.inverse g)‖ *
            ‖(ContinuousLinearMap.adjoint g) x‖ := ContinuousLinearMap.le_opNorm _ _
        _ ≤ Mi' * ‖(ContinuousLinearMap.adjoint g) x‖ := by
          gcongr
          rw [LinearIsometryEquiv.norm_map]
          exact (hMi g hg).trans (le_max_left _ _)
    rw [inv_mul_le_iff₀ hMi']; exact this
  · have := hD g hg
    simpa [Real.norm_eq_abs] using this

/-- **Lemma (Hlawka, uniform form)** for every convex body satisfying the Fourier decay bound
`|1̂_C(ξ)| ≤ A |ξ|^{-(n+1)/2}` (Herz's bound): uniformly over a compact set of invertible
linear maps and all translations. -/
theorem hlawka_of_decay (hn : 2 ≤ n) {C : Set (Eu n)} (hCc : Convex ℝ C) (hCk : IsCompact C)
    {c0 : Eu n} {r0 : ℝ} (hr0 : 0 < r0) (hball : Metric.closedBall c0 r0 ⊆ C) {A : ℝ}
    (hdecay : ∀ ξ : Eu n, 1 ≤ ‖ξ‖ →
      ‖𝓕 (C.indicator (1 : (Eu n) → ℂ)) ξ‖ ≤ A * ‖ξ‖ ^ (-(((n : ℝ) + 1) / 2)))
    {G : Set ((Eu n) →L[ℝ] (Eu n))} (hG : IsCompact G) (hGu : ∀ g ∈ G, IsUnit g) :
    ∃ c : ℝ, ∀ t : ℝ, 1 ≤ t → ∀ g ∈ G, ∀ v : Eu n,
      |(latCount ((fun x => t • g x + v) '' C) : ℝ) -
          t ^ n * |LinearMap.det (g : (Eu n) →ₗ[ℝ] (Eu n))| * (volume C).toReal| ≤
        c * t ^ hlawkaExp n := by
  obtain ⟨σ, hσ, M, D, hb⟩ := bounds_of_compact hG hGu
  obtain ⟨c, hc⟩ := hlawka_core hn hCc hCk hr0 hball hdecay (M := M) (D := D) hσ
  exact ⟨c, fun t ht g hg v => hc t ht g (hb g hg).1 (hb g hg).2.1 (hb g hg).2.2.1
    (hb g hg).2.2.2 v⟩

/-- **Fourier decay of the ball** (the stationary-phase bound for balls):
`|1̂_B(ξ)| ≤ A |ξ|^{-(n+1)/2}` for `|ξ| ≥ 1`. -/
theorem ball_fourier_decay (hn : 2 ≤ n) : ∃ A : ℝ, ∀ ξ : Eu n, 1 ≤ ‖ξ‖ →
    ‖𝓕 ((Metric.closedBall (0 : Eu n) 1).indicator (1 : (Eu n) → ℂ)) ξ‖ ≤
      A * ‖ξ‖ ^ (-(((n : ℝ) + 1) / 2)) := by
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  obtain ⟨Cd, hCd⟩ := decay1 (((n : ℝ) - 1) / 2) (by linarith)
  set w := (volume (Metric.closedBall (0 : EuclideanSpace ℝ (Fin (n - 1))) 1)).toReal
  refine ⟨w * Cd, fun ξ hξ => ?_⟩
  rw [slice hn ξ, norm_smul, Real.norm_eq_abs, abs_of_nonneg ENNReal.toReal_nonneg]
  have h := hCd ‖ξ‖ (by rwa [abs_of_nonneg (norm_nonneg _)])
  rw [abs_of_nonneg (norm_nonneg _)] at h
  have he : -(((n : ℝ) - 1) / 2 + 1) = -(((n : ℝ) + 1) / 2) := by ring
  rw [he] at h
  calc w * _ ≤ w * (Cd * ‖ξ‖ ^ (-(((n : ℝ) + 1) / 2))) :=
        mul_le_mul_of_nonneg_left h ENNReal.toReal_nonneg
    _ = _ := by ring

/-- **Lemma (lattice points in ellipsoids, uniformly).** For the unit ball `B` and a compact set
`G` of invertible linear maps, `|#((t g B + v) ∩ ℤⁿ) - tⁿ |det g| vol B| ≤ c t^{n-2+2/(n+1)}`. -/
theorem hlawka_ellipsoid (hn : 2 ≤ n) {G : Set ((Eu n) →L[ℝ] (Eu n))} (hG : IsCompact G)
    (hGu : ∀ g ∈ G, IsUnit g) :
    ∃ c : ℝ, ∀ t : ℝ, 1 ≤ t → ∀ g ∈ G, ∀ v : Eu n,
      |(latCount ((fun x => t • g x + v) '' Metric.closedBall (0 : Eu n) 1) : ℝ) -
          t ^ n * |LinearMap.det (g : (Eu n) →ₗ[ℝ] (Eu n))| *
            (volume (Metric.closedBall (0 : Eu n) 1)).toReal| ≤ c * t ^ hlawkaExp n := by
  obtain ⟨A, hA⟩ := ball_fourier_decay hn
  exact hlawka_of_decay hn (convex_closedBall 0 1) (isCompact_closedBall 0 1) one_pos
    le_rfl hA hG hGu

/-- Granular content of `S` for the point set `Λ = h L ℤⁿ`: `μ_Λ(S) = hⁿ #(S ∩ Λ)`. -/
def muLam (L : (Eu n) →L[ℝ] (Eu n)) (h : ℝ) (S : Set (Eu n)) : ℝ :=
  h ^ n * (Set.ncard {k : Fin n → ℤ | h • L (zpt k) ∈ S} : ℝ)

/-- The set of linear isometries, as continuous linear maps: compact. -/
def orthSet (n : ℕ) : Set ((Eu n) →L[ℝ] (Eu n)) := {g | ∀ x, ‖g x‖ = ‖x‖}

theorem isCompact_orthSet : IsCompact (orthSet n) := by
  apply Metric.isCompact_of_isClosed_isBounded
  · have : orthSet n = ⋂ x : Eu n, {g : (Eu n) →L[ℝ] (Eu n) | ‖g x‖ = ‖x‖} := by
      ext g; simp [orthSet]
    rw [this]
    exact isClosed_iInter fun x => isClosed_eq (by fun_prop) continuous_const
  · rw [Metric.isBounded_iff_subset_closedBall 0]
    refine ⟨1, fun g hg => ?_⟩
    rw [Metric.mem_closedBall, dist_zero_right]
    exact ContinuousLinearMap.opNorm_le_bound _ zero_le_one (fun x => by rw [hg x, one_mul])

theorem isUnit_of_det_ne_zero {g : (Eu n) →L[ℝ] (Eu n)}
    (h : LinearMap.det (g : (Eu n) →ₗ[ℝ] (Eu n)) ≠ 0) : IsUnit g := by
  rw [← g.coe_toContinuousLinearEquivOfDetNeZero h]
  exact ⟨(g.toContinuousLinearEquivOfDetNeZero h).toUnit, rfl⟩

theorem isUnit_of_orth {g : (Eu n) →L[ℝ] (Eu n)} (hg : g ∈ orthSet n) : IsUnit g :=
  isUnit_of_det_ne_zero (det_ne_zero_of_bound one_pos (fun x => by rw [hg x, one_mul]))

theorem abs_det_isometry (R : (Eu n) ≃ₗᵢ[ℝ] (Eu n)) :
    |LinearMap.det ((R : (Eu n) →L[ℝ] (Eu n)) : (Eu n) →ₗ[ℝ] (Eu n))| = 1 := by
  have h1 := vol_affine (Metric.closedBall (0 : Eu n) 1) 1 one_pos (R : (Eu n) →L[ℝ] (Eu n)) 0
  have himg : (fun x => (1 : ℝ) • (R : (Eu n) →L[ℝ] (Eu n)) x + 0) '' Metric.closedBall 0 1 =
      Metric.closedBall 0 1 := by
    ext y; constructor
    · rintro ⟨x, hx, rfl⟩
      simpa using hx
    · intro hy
      refine ⟨R.symm y, ?_, by simp⟩
      simpa using hy
  rw [himg, one_pow, one_mul] at h1
  have hpos : volume (Metric.closedBall (0 : Eu n) 1) ≠ 0 :=
    (Metric.measure_closedBall_pos volume 0 one_pos).ne'
  have hfin : volume (Metric.closedBall (0 : Eu n) 1) ≠ ⊤ := measure_closedBall_lt_top.ne
  have : ENNReal.ofReal |LinearMap.det ((R : (Eu n) →L[ℝ] (Eu n)) : (Eu n) →ₗ[ℝ] (Eu n))| = 1 := by
    have h2 := congrArg (fun z => z / volume (Metric.closedBall (0 : Eu n) 1)) h1
    rwa [ENNReal.div_self hpos hfin, ENNReal.mul_div_cancel_right hpos hfin, eq_comm] at h2
  have h3 := congrArg ENNReal.toReal this
  rwa [ENNReal.toReal_ofReal (abs_nonneg _), ENNReal.toReal_one] at h3

/-- The exponent `2 - 2/(n+1)` of the isotropy theorem. -/
def isoExp (n : ℕ) : ℝ := 2 - 2 / ((n : ℝ) + 1)

/-- From a uniform lattice count for `C` to the isotropy estimate for `μ_Λ`, `Λ = h L ℤⁿ`,
uniformly over all rotations (indeed all of `O(n)`) and translations. -/
theorem isotropy_of_count (hn : 2 ≤ n) {C : Set (Eu n)}
    (hcount : ∀ G : Set ((Eu n) →L[ℝ] (Eu n)), IsCompact G → (∀ g ∈ G, IsUnit g) →
      ∃ c : ℝ, ∀ t : ℝ, 1 ≤ t → ∀ g ∈ G, ∀ v : Eu n,
        |(latCount ((fun x => t • g x + v) '' C) : ℝ) -
          t ^ n * |LinearMap.det (g : (Eu n) →ₗ[ℝ] (Eu n))| * (volume C).toReal| ≤
          c * t ^ hlawkaExp n)
    {L : (Eu n) →L[ℝ] (Eu n)} (hL : IsUnit L)
    (hdet : |LinearMap.det (L : (Eu n) →ₗ[ℝ] (Eu n))| = 1) :
    ∃ c : ℝ, ∀ h : ℝ, 0 < h → h ≤ 1 → ∀ R : (Eu n) ≃ₗᵢ[ℝ] (Eu n), ∀ v : Eu n,
      |muLam L h ((fun x => R x + v) '' C) - (volume C).toReal| ≤ c * h ^ isoExp n := by
  set Li := Ring.inverse L
  have hLi1 : Li * L = 1 := Ring.inverse_mul_cancel L hL
  have hLi2 : L * Li = 1 := Ring.mul_inverse_cancel L hL
  set G := (fun g => Li ∘L g) '' orthSet n
  have hGc : IsCompact G := isCompact_orthSet.image (by fun_prop)
  have hGu : ∀ g ∈ G, IsUnit g := by
    rintro _ ⟨g, hg, rfl⟩
    show IsUnit (Li * g)
    have hLiu : IsUnit Li := ⟨⟨Li, L, hLi1, hLi2⟩, rfl⟩
    exact hLiu.mul (isUnit_of_orth hg)
  obtain ⟨c, hc⟩ := hcount G hGc hGu
  refine ⟨c, fun h hh0 hh1 R v => ?_⟩
  have hRo : (R : (Eu n) →L[ℝ] (Eu n)) ∈ orthSet n := fun x => by simp
  set g := Li ∘L (R : (Eu n) →L[ℝ] (Eu n))
  have hgG : g ∈ G := ⟨_, hRo, rfl⟩
  have eL1 : ∀ y, Li (L y) = y := fun y => by
    rw [← ContinuousLinearMap.mul_apply, hLi1]; rfl
  have eL2 : ∀ y, L (Li y) = y := fun y => by
    rw [← ContinuousLinearMap.mul_apply, hLi2]; rfl
  set t := h⁻¹
  have ht1 : 1 ≤ t := one_le_inv₀ hh0 |>.2 hh1
  have hset : {k : Fin n → ℤ | h • L (zpt k) ∈ (fun x => R x + v) '' C} =
      {k | zpt k ∈ (fun x => t • g x + t • Li v) '' C} := by
    ext k
    simp only [Set.mem_ofPred_eq, Set.mem_image]
    constructor
    · rintro ⟨x, hx, hxe⟩
      refine ⟨x, hx, ?_⟩
      have : zpt k = t • Li (h • L (zpt k)) := by
        rw [map_smul, smul_smul, inv_mul_cancel₀ hh0.ne', one_smul, eL1]
      rw [this, ← hxe, map_add, smul_add]; rfl
    · rintro ⟨x, hx, hxe⟩
      refine ⟨x, hx, ?_⟩
      rw [← hxe, ← smul_add, map_smul, smul_smul, mul_inv_cancel₀ hh0.ne', one_smul]
      have : L (g x + Li v) = R x + v := by
        rw [map_add, eL2]
        simp only [g, ContinuousLinearMap.comp_apply, eL2]
        rfl
      rw [this]
  have hdg : |LinearMap.det (g : (Eu n) →ₗ[ℝ] (Eu n))| = 1 := by
    have hdLi : |LinearMap.det (Li : (Eu n) →ₗ[ℝ] (Eu n))| = 1 := by
      have := congrArg (fun f : (Eu n) →L[ℝ] (Eu n) => LinearMap.det (f : (Eu n) →ₗ[ℝ] (Eu n)))
        hLi1
      rw [ContinuousLinearMap.coe_mul, map_mul, ContinuousLinearMap.toLinearMap_one, map_one] at this
      have := congrArg abs this
      rw [abs_mul, hdet, mul_one, abs_one] at this
      exact this
    have hc : ((Li ∘L (R : (Eu n) →L[ℝ] (Eu n)) : (Eu n) →L[ℝ] (Eu n)) : (Eu n) →ₗ[ℝ] (Eu n)) =
        (Li : (Eu n) →ₗ[ℝ] (Eu n)) ∘ₗ ((R : (Eu n) →L[ℝ] (Eu n)) : (Eu n) →ₗ[ℝ] (Eu n)) := rfl
    rw [hc, LinearMap.det_comp, abs_mul, hdLi, abs_det_isometry R, one_mul]
  have hb := hc t ht1 g hgG (t • Li v)
  simp only [latCount] at hb
  rw [hdg, mul_one, ← hset] at hb
  unfold muLam
  have hht : h ^ n * t ^ n = 1 := by rw [← mul_pow, mul_inv_cancel₀ hh0.ne', one_pow]
  have hexp : h ^ n * t ^ hlawkaExp n = h ^ isoExp n := by
    rw [← Real.rpow_natCast, Real.inv_rpow hh0.le, ← Real.rpow_neg hh0.le, ← Real.rpow_add hh0]
    congr 1; simp only [hlawkaExp, isoExp]; ring
  have hpos : 0 < h ^ n := by positivity
  calc |h ^ n * _ - (volume C).toReal|
      = h ^ n * |(Set.ncard {k : Fin n → ℤ | h • L (zpt k) ∈ (fun x => R x + v) '' C} : ℝ) -
          t ^ n * (volume C).toReal| := by
        rw [← abs_of_pos hpos, ← abs_mul, abs_of_pos hpos, mul_sub, ← mul_assoc, hht, one_mul]
    _ ≤ h ^ n * (c * t ^ hlawkaExp n) := mul_le_mul_of_nonneg_left hb hpos.le
    _ = c * h ^ isoExp n := by rw [← hexp]; ring

/-- An ellipsoid `C = E(B) + c₀` satisfies the uniform lattice count. -/
theorem ellipsoid_count (hn : 2 ≤ n) {Em : (Eu n) →L[ℝ] (Eu n)} (hEm : IsUnit Em) (c0 : Eu n)
    (G : Set ((Eu n) →L[ℝ] (Eu n))) (hG : IsCompact G) (hGu : ∀ g ∈ G, IsUnit g) :
    ∃ c : ℝ, ∀ t : ℝ, 1 ≤ t → ∀ g ∈ G, ∀ v : Eu n,
      |(latCount ((fun x => t • g x + v) '' ((fun x => Em x + c0) '' Metric.closedBall 0 1)) : ℝ) -
          t ^ n * |LinearMap.det (g : (Eu n) →ₗ[ℝ] (Eu n))| *
            (volume ((fun x => Em x + c0) '' Metric.closedBall (0 : Eu n) 1)).toReal| ≤
        c * t ^ hlawkaExp n := by
  set G' := (fun g => g ∘L Em) '' G
  have hG' : IsCompact G' := hG.image (by fun_prop)
  have hG'u : ∀ g ∈ G', IsUnit g := by
    rintro _ ⟨g, hg, rfl⟩
    show IsUnit (g * Em)
    exact (hGu g hg).mul hEm
  obtain ⟨c, hc⟩ := hlawka_ellipsoid hn hG' hG'u
  refine ⟨c, fun t ht g hg v => ?_⟩
  have h1 := hc t ht (g ∘L Em) ⟨g, hg, rfl⟩ (t • g c0 + v)
  have himg : (fun x => t • g x + v) '' ((fun x => Em x + c0) '' Metric.closedBall 0 1) =
      (fun x => t • (g ∘L Em) x + (t • g c0 + v)) '' Metric.closedBall 0 1 := by
    rw [Set.image_image]
    congr 1; funext x
    simp only [ContinuousLinearMap.comp_apply, map_add, smul_add]; abel
  have hvol : (volume ((fun x => Em x + c0) '' Metric.closedBall (0 : Eu n) 1)).toReal =
      |LinearMap.det (Em : (Eu n) →ₗ[ℝ] (Eu n))| *
        (volume (Metric.closedBall (0 : Eu n) 1)).toReal := by
    have := vol_affine (Metric.closedBall (0 : Eu n) 1) 1 one_pos Em c0
    simp only [one_smul, one_pow, one_mul] at this
    rw [this, ENNReal.toReal_mul, ENNReal.toReal_ofReal (abs_nonneg _)]
  have hdet : ((g ∘L Em : (Eu n) →L[ℝ] (Eu n)) : (Eu n) →ₗ[ℝ] (Eu n)) =
      (g : (Eu n) →ₗ[ℝ] (Eu n)) ∘ₗ (Em : (Eu n) →ₗ[ℝ] (Eu n)) := rfl
  rw [hdet, LinearMap.det_comp, abs_mul] at h1
  rw [himg, hvol]
  calc _ = _ := by ring_nf
    _ ≤ _ := h1

/-- **Theorem (smooth bodies are isotropic at first order), ellipsoids.** For `Λ = h L ℤⁿ` with
`|det L| = 1` and every ellipsoid `C = E(B) + c₀`:
`|μ_Λ(RC + v) - vol C| ≤ c h^{2 - 2/(n+1)}` for all `0 < h ≤ 1`, all `R ∈ O(n)`, all `v`. -/
theorem smooth_isotropy_ellipsoid (hn : 2 ≤ n) {L : (Eu n) →L[ℝ] (Eu n)} (hL : IsUnit L)
    (hdet : |LinearMap.det (L : (Eu n) →ₗ[ℝ] (Eu n))| = 1)
    {Em : (Eu n) →L[ℝ] (Eu n)} (hEm : IsUnit Em) (c0 : Eu n) :
    ∃ c : ℝ, ∀ h : ℝ, 0 < h → h ≤ 1 → ∀ R : (Eu n) ≃ₗᵢ[ℝ] (Eu n), ∀ v : Eu n,
      |muLam L h ((fun x => R x + v) '' ((fun x => Em x + c0) '' Metric.closedBall 0 1)) -
        (volume ((fun x => Em x + c0) '' Metric.closedBall (0 : Eu n) 1)).toReal| ≤
        c * h ^ isoExp n :=
  isotropy_of_count hn (fun G hG hGu => ellipsoid_count hn hEm c0 G hG hGu) hL hdet

/-- **Theorem (smooth bodies are isotropic at first order)**, for every convex body satisfying
Herz's Fourier decay bound `|1̂_C(ξ)| ≤ A |ξ|^{-(n+1)/2}`. -/
theorem smooth_isotropy_of_decay (hn : 2 ≤ n) {C : Set (Eu n)} (hCc : Convex ℝ C)
    (hCk : IsCompact C) {c0 : Eu n} {r0 : ℝ} (hr0 : 0 < r0) (hball : Metric.closedBall c0 r0 ⊆ C)
    {A : ℝ} (hdecay : ∀ ξ : Eu n, 1 ≤ ‖ξ‖ →
      ‖𝓕 (C.indicator (1 : (Eu n) → ℂ)) ξ‖ ≤ A * ‖ξ‖ ^ (-(((n : ℝ) + 1) / 2)))
    {L : (Eu n) →L[ℝ] (Eu n)} (hL : IsUnit L)
    (hdet : |LinearMap.det (L : (Eu n) →ₗ[ℝ] (Eu n))| = 1) :
    ∃ c : ℝ, ∀ h : ℝ, 0 < h → h ≤ 1 → ∀ R : (Eu n) ≃ₗᵢ[ℝ] (Eu n), ∀ v : Eu n,
      |muLam L h ((fun x => R x + v) '' C) - (volume C).toReal| ≤ c * h ^ isoExp n :=
  isotropy_of_count hn (fun _ hG hGu => hlawka_of_decay hn hCc hCk hr0 hball hdecay hG hGu) hL hdet

/-- The first-order consequence: `|μ_Λ(RC+v) - μ_Λ(C)| / h ≤ 2c h^{1-2/(n+1)}`. -/
theorem isotropy_first_order {L : (Eu n) →L[ℝ] (Eu n)} {C : Set (Eu n)} {c : ℝ}
    (hc : ∀ h : ℝ, 0 < h → h ≤ 1 → ∀ R : (Eu n) ≃ₗᵢ[ℝ] (Eu n), ∀ v : Eu n,
      |muLam L h ((fun x => R x + v) '' C) - (volume C).toReal| ≤ c * h ^ isoExp n)
    {h : ℝ} (hh0 : 0 < h) (hh1 : h ≤ 1) (R : (Eu n) ≃ₗᵢ[ℝ] (Eu n)) (v : Eu n) :
    |muLam L h ((fun x => R x + v) '' C) - muLam L h C| / h ≤
      2 * c * h ^ (1 - 2 / ((n : ℝ) + 1)) := by
  have h1 := hc h hh0 hh1 R v
  have h2 := hc h hh0 hh1 (LinearIsometryEquiv.refl ℝ (Eu n)) 0
  have hC : (fun x => (LinearIsometryEquiv.refl ℝ (Eu n)) x + 0) '' C = C := by simp
  rw [hC] at h2
  have hexp : h ^ isoExp n = h * h ^ (1 - 2 / ((n : ℝ) + 1)) := by
    rw [show isoExp n = 1 + (1 - 2 / ((n : ℝ) + 1)) by unfold isoExp; ring,
      Real.rpow_add hh0, Real.rpow_one]
  rw [div_le_iff₀ hh0]
  calc |muLam L h ((fun x => R x + v) '' C) - muLam L h C|
      ≤ |muLam L h ((fun x => R x + v) '' C) - (volume C).toReal| +
        |muLam L h C - (volume C).toReal| := by
          have := abs_sub_le (muLam L h ((fun x => R x + v) '' C)) ((volume C).toReal) (muLam L h C)
          rwa [abs_sub_comm (volume C).toReal] at this
    _ ≤ c * h ^ isoExp n + c * h ^ isoExp n := add_le_add h1 h2
    _ = 2 * c * h ^ (1 - 2 / ((n : ℝ) + 1)) * h := by rw [hexp]; ring

end Hlawka


-- ==== Polytope.lean ====

namespace Polytope
open scoped Pointwise
def para {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) : Set (EuclideanSpace ℝ (Fin n)) :=
  {x | ∃ s : EuclideanSpace ℝ (Fin n), (∀ i, s i ∈ Set.Icc (0:ℝ) 1) ∧ x = Matrix.toEuclideanLin A s}

namespace Aux

abbrev SO (n : ℕ) := ↥(Matrix.specialOrthogonalGroup (Fin n) ℝ)

instance (n : ℕ) : IsTopologicalGroup (SO n) where
  continuous_mul := by
    apply Continuous.subtype_mk
    exact (continuous_subtype_val.comp continuous_fst).mul (continuous_subtype_val.comp continuous_snd)
  continuous_inv := by
    apply Continuous.subtype_mk
    exact continuous_star.comp continuous_subtype_val

lemma isCompact_SO (n : ℕ) :
    IsCompact (Matrix.specialOrthogonalGroup (Fin n) ℝ : Set (Matrix (Fin n) (Fin n) ℝ)) := by
  have hK : IsCompact ((Set.Icc (-1:ℝ) 1).matrix : Set (Matrix (Fin n) (Fin n) ℝ)) :=
    isCompact_Icc.matrix
  apply hK.of_isClosed_subset
  · have : (Matrix.specialOrthogonalGroup (Fin n) ℝ : Set (Matrix (Fin n) (Fin n) ℝ)) =
        {A | A * A.transpose = 1} ∩ {A | A.det = 1} := by
      ext A; simp [Matrix.mem_specialOrthogonalGroup_iff, Matrix.mem_orthogonalGroup_iff]
    rw [this]
    exact (isClosed_eq (continuous_id.mul continuous_id.matrix_transpose) continuous_const).inter
      (isClosed_eq (continuous_id.matrix_det) continuous_const)
  · intro A hA i j
    have := entry_norm_bound_of_unitary (Matrix.specialUnitaryGroup_le_unitaryGroup hA) i j
    simp only [Real.norm_eq_abs] at this
    exact abs_le.mp this

instance (n : ℕ) : CompactSpace (SO n) := isCompact_iff_compactSpace.mp (isCompact_SO n)

/-- Haar probability measure on SO(n). -/
def nu (n : ℕ) : Measure (SO n) := Measure.haarMeasure ⊤

instance (n : ℕ) : IsProbabilityMeasure (nu n) := by
  constructor
  have := Measure.haarMeasure_self (G := SO n) (K₀ := ⊤)
  simpa [nu] using this

instance (n : ℕ) : (nu n).IsMulLeftInvariant := by unfold nu; infer_instance


variable {n : ℕ}

local notation "E" n => EuclideanSpace ℝ (Fin n)

lemma toE_mul (M N : Matrix (Fin n) (Fin n) ℝ) (v : EuclideanSpace ℝ (Fin n)) :
    Matrix.toEuclideanLin (M * N) v = Matrix.toEuclideanLin M (Matrix.toEuclideanLin N v) := by
  simp

lemma star_mul_self' (R : SO n) : star R.1 * R.1 = 1 :=
  Matrix.mem_unitaryGroup_iff'.mp (Matrix.specialUnitaryGroup_le_unitaryGroup R.2)

lemma mul_star_self' (R : SO n) : R.1 * star R.1 = 1 :=
  Matrix.mem_unitaryGroup_iff.mp (Matrix.specialUnitaryGroup_le_unitaryGroup R.2)

lemma toE_star_toE (R : SO n) (v : EuclideanSpace ℝ (Fin n)) :
    Matrix.toEuclideanLin (star R.1) (Matrix.toEuclideanLin R.1 v) = v := by
  rw [← toE_mul, star_mul_self']; simp

lemma toE_toE_star (R : SO n) (v : EuclideanSpace ℝ (Fin n)) :
    Matrix.toEuclideanLin R.1 (Matrix.toEuclideanLin (star R.1) v) = v := by
  rw [← toE_mul, mul_star_self']; simp

lemma norm_toE (R : SO n) (v : EuclideanSpace ℝ (Fin n)) :
    ‖Matrix.toEuclideanLin R.1 v‖ = ‖v‖ := by
  have h : ⟪Matrix.toEuclideanLin R.1 v, Matrix.toEuclideanLin R.1 v⟫ = ⟪v, v⟫ := by
    rw [← LinearMap.adjoint_inner_left, ← Matrix.toEuclideanLin_conjTranspose_eq_adjoint]
    have : R.1.conjTranspose = star R.1 := rfl
    rw [this, toE_star_toE]
  rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq] at h
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp h

lemma det_refl {w : EuclideanSpace ℝ (Fin n)} (hw : w ≠ 0) :
    LinearMap.det (ℝ ∙ w)ᗮ.reflection.toLinearMap = -1 := by
  have := Submodule.det_reflection (K := (ℝ ∙ w)ᗮ)
  rw [Submodule.orthogonal_orthogonal, finrank_span_singleton hw, pow_one] at this
  exact this

lemma exists_isom (hn : 2 ≤ n) (u v : EuclideanSpace ℝ (Fin n)) (h : ‖u‖ = ‖v‖) :
    ∃ f : EuclideanSpace ℝ (Fin n) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n),
      LinearMap.det f.toLinearMap = 1 ∧ f u = v := by
  by_cases huv : u = v
  · exact ⟨LinearIsometryEquiv.refl ℝ _, by simp, huv⟩
  have hw : u - v ≠ 0 := sub_ne_zero.mpr huv
  -- a nonzero vector orthogonal to v
  have hne : (ℝ ∙ v)ᗮ ≠ ⊥ := by
    intro hb
    have h1 := Submodule.finrank_add_finrank_orthogonal (ℝ ∙ v)
    rw [hb, finrank_bot, add_zero, finrank_euclideanSpace_fin] at h1
    have h2 := finrank_span_le_card (R := ℝ) ({v} : Set (EuclideanSpace ℝ (Fin n)))
    simp at h2
    omega
  obtain ⟨z, hz, hz0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  have hvz : v ∈ (ℝ ∙ z)ᗮ := by
    rw [Submodule.mem_orthogonal_singleton_iff_inner_right]
    rw [Submodule.mem_orthogonal_singleton_iff_inner_right] at hz
    rw [real_inner_comm]; exact hz
  refine ⟨((ℝ ∙ (u - v))ᗮ.reflection).trans ((ℝ ∙ z)ᗮ.reflection), ?_, ?_⟩
  · rw [LinearIsometryEquiv.toLinearEquiv_trans, LinearEquiv.coe_trans, LinearMap.det_comp,
      det_refl hz0, det_refl hw]; norm_num
  · simp [Submodule.reflection_sub h, Submodule.reflection_mem_subspace_eq_self hvz]

lemma exists_SO (hn : 2 ≤ n) (u v : EuclideanSpace ℝ (Fin n)) (h : ‖u‖ = ‖v‖) :
    ∃ Q : SO n, Matrix.toEuclideanLin Q.1 u = v := by
  obtain ⟨f, hdet, hf⟩ := exists_isom hn u v h
  let b := (EuclideanSpace.basisFun (Fin n) ℝ).toBasis
  let M := LinearMap.toMatrix b b f.toLinearMap
  have hM : Matrix.toEuclideanLin M = f.toLinearMap := by
    rw [Matrix.toEuclideanLin_eq_toLin_orthonormal, Matrix.toLin_toMatrix]
  have hU : M ∈ Matrix.unitaryGroup (Fin n) ℝ :=
    LinearIsometryEquiv.toMatrix_mem_unitaryGroup f _ _
  have hdM : M.det = 1 := by rw [LinearMap.det_toMatrix]; exact hdet
  refine ⟨⟨M, (Matrix.mem_specialUnitaryGroup_iff).mpr ⟨hU, hdM⟩⟩, ?_⟩
  show Matrix.toEuclideanLin M u = v
  rw [hM]; exact hf

/-- the unit cube in `ℝⁿ`. -/
def cube (n : ℕ) : Set (EuclideanSpace ℝ (Fin n)) := {s | ∀ i, s i ∈ Set.Icc (0:ℝ) 1}

lemma para_eq (A : Matrix (Fin n) (Fin n) ℝ) : para A = Matrix.toEuclideanLin A '' cube n := by
  ext x; simp only [para, cube, Set.mem_ofPred_eq, Set.mem_image]
  constructor
  · rintro ⟨s, hs, rfl⟩; exact ⟨s, hs, rfl⟩
  · rintro ⟨s, hs, rfl⟩; exact ⟨s, hs, rfl⟩

lemma cube_eq : cube n = (WithLp.ofLp) ⁻¹' (Set.univ.pi fun _ : Fin n => Set.Icc (0:ℝ) 1) := by
  ext x; simp only [cube, Set.mem_ofPred_eq, Set.mem_preimage, Set.mem_univ_pi]

lemma isCompact_cube : IsCompact (cube n) := by
  rw [cube_eq]
  exact (PiLp.homeomorph 2 (fun _ : Fin n => ℝ)).isCompact_preimage.mpr
    (isCompact_univ_pi fun _ => isCompact_Icc)

lemma isCompact_para (A : Matrix (Fin n) (Fin n) ℝ) : IsCompact (para A) := by
  rw [para_eq]; exact isCompact_cube.image (LinearMap.continuous_of_finiteDimensional _)

lemma smul_mem_para {A : Matrix (Fin n) (Fin n) ℝ} {c : ℝ} (hc : c ∈ Set.Icc (0:ℝ) 1)
    {p : EuclideanSpace ℝ (Fin n)} (hp : p ∈ para A) : c • p ∈ para A := by
  obtain ⟨s, hs, rfl⟩ := hp
  refine ⟨c • s, fun i => ?_, by simp⟩
  have := hs i
  simp only [PiLp.smul_apply, smul_eq_mul, Set.mem_Icc] at this ⊢
  exact ⟨mul_nonneg hc.1 this.1, by nlinarith [this.1, this.2, hc.1, hc.2]⟩

lemma volume_cube : volume (cube n) = 1 := by
  rw [cube_eq, (PiLp.volume_preserving_ofLp (Fin n)).measure_preimage
    (MeasurableSet.univ_pi (fun _ => measurableSet_Icc)).nullMeasurableSet, volume_pi_pi]
  simp

lemma volume_para {A : Matrix (Fin n) (Fin n) ℝ} (hA : |A.det| = 1) : volume (para A) = 1 := by
  rw [para_eq, Measure.addHaar_image_linearMap, LinearMap.det_toLpLin, hA, volume_cube]; simp

/-- the dilated rotated parallelepiped. -/
def T (A : Matrix (Fin n) (Fin n) ℝ) (t : ℝ) (R : SO n) : Set (EuclideanSpace ℝ (Fin n)) :=
  t • (Matrix.toEuclideanLin R.1 '' para A)

variable {A : Matrix (Fin n) (Fin n) ℝ} {t : ℝ}

lemma mem_T (ht : t ≠ 0) {R : SO n} {y : EuclideanSpace ℝ (Fin n)} :
    y ∈ T A t R ↔ Matrix.toEuclideanLin (star R.1) (t⁻¹ • y) ∈ para A := by
  unfold T; rw [Set.mem_smul_set]; constructor
  · rintro ⟨x, ⟨p, hp, rfl⟩, rfl⟩
    rwa [smul_smul, inv_mul_cancel₀ ht, one_smul, toE_star_toE]
  · intro h
    exact ⟨_, ⟨_, h, rfl⟩, by rw [toE_toE_star, smul_smul, mul_inv_cancel₀ ht, one_smul]⟩

lemma volume_T (hA : |A.det| = 1) (ht : 0 ≤ t) (R : SO n) :
    volume (T A t R) = ENNReal.ofReal (t ^ n) := by
  unfold T
  rw [Measure.addHaar_smul, Measure.addHaar_image_linearMap, LinearMap.det_toLpLin, volume_para hA,
    finrank_euclideanSpace_fin, (Matrix.mem_specialUnitaryGroup_iff.mp R.2).2]
  simp [abs_of_nonneg (pow_nonneg ht n)]

/-- the incidence set `{(y, R) : y ∈ t R P}`. -/
def Sig (A : Matrix (Fin n) (Fin n) ℝ) (t : ℝ) : Set (EuclideanSpace ℝ (Fin n) × SO n) :=
  {q | Matrix.toEuclideanLin (star q.2.1) (t⁻¹ • q.1) ∈ para A}

lemma isClosed_Sig : IsClosed (Sig A t) := by
  apply (isCompact_para A).isClosed.preimage
  show Continuous fun q : EuclideanSpace ℝ (Fin n) × SO n =>
    WithLp.toLp 2 (Matrix.mulVec (star q.2.1) (WithLp.ofLp (t⁻¹ • q.1)))
  exact (PiLp.continuous_toLp 2 _).comp (Continuous.matrix_mulVec
    (continuous_star.comp (continuous_subtype_val.comp continuous_snd))
    ((PiLp.continuous_ofLp 2 _).comp (continuous_fst.const_smul t⁻¹)))

lemma measurableSet_Sig : MeasurableSet (Sig A t) := isClosed_Sig.measurableSet

/-- `F(y) = ν{R : y ∈ t R P}`. -/
def Fm (A : Matrix (Fin n) (Fin n) ℝ) (t : ℝ) (y : EuclideanSpace ℝ (Fin n)) : ENNReal :=
  nu n {R | y ∈ T A t R}

lemma slice_eq (ht : t ≠ 0) (y : EuclideanSpace ℝ (Fin n)) :
    {R | y ∈ T A t R} = Prod.mk y ⁻¹' Sig A t := by
  ext R; simp [Sig, mem_T ht]

lemma slice_eq' (ht : t ≠ 0) (R : SO n) :
    (fun y => (y, R)) ⁻¹' Sig A t = T A t R := by
  ext y; simp [Sig, mem_T ht]

lemma measurableSet_slice (ht : t ≠ 0) (y : EuclideanSpace ℝ (Fin n)) :
    MeasurableSet {R | y ∈ T A t R} := by
  rw [slice_eq ht]; exact measurable_prodMk_left measurableSet_Sig

lemma Fm_rot (ht : t ≠ 0) (Q : SO n) (y : EuclideanSpace ℝ (Fin n)) :
    Fm A t (Matrix.toEuclideanLin Q.1 y) = Fm A t y := by
  unfold Fm
  rw [← measure_preimage_mul (nu n) Q⁻¹ {R | y ∈ T A t R}]
  congr 1; ext R
  simp only [Set.mem_preimage, Set.mem_ofPred_eq, mem_T ht]
  have : (Q⁻¹ * R).1 = star Q.1 * R.1 := rfl
  rw [this, star_mul, star_star, toE_mul]; simp only [map_smul]

lemma Fm_smul (ht : t ≠ 0) {c : ℝ} (hc : c ∈ Set.Icc (0:ℝ) 1) (y : EuclideanSpace ℝ (Fin n)) :
    Fm A t y ≤ Fm A t (c • y) := by
  apply measure_mono
  intro R hR
  simp only [Set.mem_ofPred_eq, mem_T ht] at hR ⊢
  rw [smul_comm, map_smul]
  exact smul_mem_para hc hR

lemma Fm_anti (hn : 2 ≤ n) (ht : t ≠ 0) {y z : EuclideanSpace ℝ (Fin n)} (h : ‖z‖ ≤ ‖y‖) :
    Fm A t y ≤ Fm A t z := by
  by_cases hy : y = 0
  · subst hy
    have : z = 0 := norm_le_zero_iff.mp (by simpa using h)
    subst this; exact le_rfl
  set c := ‖z‖ / ‖y‖
  have hy' : ‖y‖ ≠ 0 := norm_ne_zero_iff.mpr hy
  have hc : c ∈ Set.Icc (0:ℝ) 1 :=
    ⟨div_nonneg (norm_nonneg _) (norm_nonneg _), div_le_one_of_le₀ h (norm_nonneg _)⟩
  have hn' : ‖c • y‖ = ‖z‖ := by
    rw [norm_smul, Real.norm_of_nonneg hc.1, div_mul_cancel₀ _ hy']
  obtain ⟨Q, hQ⟩ := exists_SO hn _ _ hn'
  calc Fm A t y ≤ Fm A t (c • y) := Fm_smul ht hc y
    _ = Fm A t (Matrix.toEuclideanLin Q.1 (c • y)) := (Fm_rot ht Q _).symm
    _ = Fm A t z := by rw [hQ]

lemma norm_le_of_mem_T {R₀ : ℝ} (hP : para A ⊆ Metric.closedBall 0 R₀) (ht : 0 ≤ t) {R : SO n}
    {y : EuclideanSpace ℝ (Fin n)} (hy : y ∈ T A t R) : ‖y‖ ≤ t * R₀ := by
  obtain ⟨x, ⟨p, hp, rfl⟩, rfl⟩ := Set.mem_smul_set.mp hy
  rw [norm_smul, norm_toE, Real.norm_of_nonneg ht]
  exact mul_le_mul_of_nonneg_left (by simpa using hP hp) ht

lemma norm_le_of_Fm_pos {R₀ : ℝ} (hP : para A ⊆ Metric.closedBall 0 R₀) (ht : 0 ≤ t)
    {y : EuclideanSpace ℝ (Fin n)} (h : 0 < Fm A t y) : ‖y‖ ≤ t * R₀ := by
  obtain ⟨R, hR⟩ := nonempty_of_measure_ne_zero h.ne'
  exact norm_le_of_mem_T hP ht hR

lemma toE_inv_toE (hA : A.det ≠ 0) (v : EuclideanSpace ℝ (Fin n)) :
    Matrix.toEuclideanLin A⁻¹ (Matrix.toEuclideanLin A v) = v := by
  rw [← toE_mul, Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hA)]; simp

lemma finite_ball (hA : A.det ≠ 0) (r : ℝ) :
    {k : Fin n → ℤ | ‖Matrix.toEuclideanLin A (zpt k)‖ ≤ r}.Finite := by
  set L := LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin A⁻¹)
  set M : ℤ := ⌈‖L‖ * r⌉
  apply (Set.finite_Icc (fun _ : Fin n => -M) (fun _ => M)).subset
  intro k hk
  simp only [Set.mem_ofPred_eq] at hk
  have h2 : ‖zpt k‖ ≤ ‖L‖ * r := by
    calc ‖zpt k‖ = ‖L (Matrix.toEuclideanLin A (zpt k))‖ := by
          rw [LinearMap.coe_toContinuousLinearMap', toE_inv_toE hA]
      _ ≤ ‖L‖ * ‖Matrix.toEuclideanLin A (zpt k)‖ := L.le_opNorm _
      _ ≤ ‖L‖ * r := mul_le_mul_of_nonneg_left hk (norm_nonneg _)
  have h5 : ‖L‖ * r ≤ (M : ℝ) := Int.le_ceil _
  have key : ∀ i, |(k i : ℝ)| ≤ M := by
    intro i
    have h3 := (PiLp.norm_apply_le (zpt k) i).trans h2
    have h4 : (zpt k) i = (k i : ℝ) := by simp [zpt]
    rw [h4, Real.norm_eq_abs] at h3
    linarith
  refine ⟨fun i => ?_, fun i => ?_⟩
  · have := (abs_le.mp (key i)).1
    show -M ≤ k i
    exact_mod_cast this
  · have := (abs_le.mp (key i)).2
    show k i ≤ M
    exact_mod_cast this

lemma encard_le_ofReal {N : Set (Fin n → ℤ)} (hfin : N.Finite) {X : ℝ} (hN : (N.ncard : ℝ) ≤ X) :
    (N.encard : ENNReal) ≤ ENNReal.ofReal X := by
  rw [← hfin.cast_ncard_eq]
  have : (((N.ncard : ℕ) : ℕ∞) : ENNReal) = ENNReal.ofReal (N.ncard : ℝ) := by simp
  rw [this]; exact ENNReal.ofReal_le_ofReal hN

lemma encard_le_ball (hA : A.det ≠ 0) {c e ρ r : ℝ} (hc0 : 0 ≤ c) (he : 0 ≤ e) (hr : 0 ≤ r)
    (hrρ : r ≤ ρ) {B : Set (EuclideanSpace ℝ (Fin n))}
    (hB : volume B = volume (Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) r))
    {N : Set (Fin n → ℤ)} (hNB : {k | Matrix.toEuclideanLin A (zpt k) ∈ B} = N)
    (hNsub : N ⊆ {k : Fin n → ℤ | ‖Matrix.toEuclideanLin A (zpt k)‖ ≤ r})
    (hN : (N.ncard : ℝ) ≤
      (volume (Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1)).toReal * r ^ n + c * (1 + r ^ e)) :
    ({k | Matrix.toEuclideanLin A (zpt k) ∈ B}.encard : ENNReal) ≤
      volume B + ENNReal.ofReal (c * (1 + ρ ^ e)) := by
  rw [hNB]
  refine (encard_le_ofReal ((finite_ball hA r).subset hNsub) hN).trans ?_
  have hω : volume (Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1) ≠ ⊤ :=
    measure_closedBall_lt_top.ne
  have hvol : volume (Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) r) =
      ENNReal.ofReal ((volume (Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1)).toReal * r ^ n) := by
    rw [Measure.addHaar_closedBall' volume 0 hr, finrank_euclideanSpace_fin,
      ENNReal.ofReal_mul ENNReal.toReal_nonneg, ENNReal.ofReal_toReal hω, mul_comm]
  rw [hB, hvol, ← ENNReal.ofReal_add (mul_nonneg ENNReal.toReal_nonneg (pow_nonneg hr n))
      (mul_nonneg hc0 (add_nonneg zero_le_one (Real.rpow_nonneg (hr.trans hrρ) e)))]
  apply ENNReal.ofReal_le_ofReal
  have : r ^ e ≤ ρ ^ e := Real.rpow_le_rpow hr hrρ he
  nlinarith

lemma encard_le (hn : 1 ≤ n) (hA : A.det ≠ 0) {c e ρ : ℝ} (hc0 : 0 ≤ c) (he : 0 ≤ e)
    (hcl : ∀ r : ℝ, 0 ≤ r → (Set.ncard {k : Fin n → ℤ | ‖Matrix.toEuclideanLin A (zpt k)‖ ≤ r} : ℝ)
      ≤ (volume (Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1)).toReal * r ^ n + c * (1 + r ^ e))
    (hop : ∀ r : ℝ, 0 ≤ r → (Set.ncard {k : Fin n → ℤ | ‖Matrix.toEuclideanLin A (zpt k)‖ < r} : ℝ)
      ≤ (volume (Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1)).toReal * r ^ n + c * (1 + r ^ e))
    (S : Set (EuclideanSpace ℝ (Fin n))) (hS : ∀ x ∈ S, ∀ y, ‖y‖ ≤ ‖x‖ → y ∈ S)
    (hρ : S ⊆ Metric.closedBall 0 ρ) :
    ({k | Matrix.toEuclideanLin A (zpt k) ∈ S}.encard : ENNReal) ≤
      volume S + ENNReal.ofReal (c * (1 + ρ ^ e)) := by
  have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  rcases S.eq_empty_or_nonempty with hSe | hSne
  · subst hSe; simp
  have hbdd : BddAbove (norm '' S) := ⟨ρ, by
    rintro _ ⟨x, hx, rfl⟩; simpa using hρ hx⟩
  set r := sSup (norm '' S)
  have hle : ∀ x ∈ S, ‖x‖ ≤ r := fun x hx => le_csSup hbdd ⟨x, hx, rfl⟩
  obtain ⟨x₀, hx₀⟩ := hSne
  have hr : 0 ≤ r := (norm_nonneg _).trans (hle x₀ hx₀)
  have hrρ : r ≤ ρ := csSup_le ⟨_, x₀, hx₀, rfl⟩ (by rintro _ ⟨x, hx, rfl⟩; simpa using hρ hx)
  by_cases hmax : ∃ x ∈ S, ‖x‖ = r
  · obtain ⟨x, hx, hxr⟩ := hmax
    have hSB : S = Metric.closedBall 0 r := by
      ext y; rw [mem_closedBall_zero_iff]
      exact ⟨hle y, fun hy => hS x hx y (hxr ▸ hy)⟩
    rw [hSB]
    exact encard_le_ball hA hc0 he hr hrρ rfl (by ext k; simp) le_rfl (hcl r hr)
  · push Not at hmax
    have hSB : S = Metric.ball 0 r := by
      ext y; rw [mem_ball_zero_iff]
      constructor
      · intro hy; exact lt_of_le_of_ne (hle y hy) (hmax y hy)
      · intro hy
        obtain ⟨_, ⟨x, hx, rfl⟩, hlt⟩ := exists_lt_of_lt_csSup (⟨‖x₀‖, x₀, hx₀, rfl⟩ : (norm '' S).Nonempty) hy
        exact hS x hx y hlt.le
    rw [hSB]
    refine encard_le_ball (N := {k : Fin n → ℤ | ‖Matrix.toEuclideanLin A (zpt k)‖ < r}) hA hc0 he
      hr hrρ (Measure.addHaar_closedBall_eq_addHaar_ball volume 0 r).symm
      (by ext k; simp) (fun k (hk : _ < r) => (le_of_lt hk : _ ≤ r)) (hop r hr)

lemma encard_eq_tsum (t : ℝ) (R : SO n) :
    ({k : Fin n → ℤ | Matrix.toEuclideanLin A (zpt k) ∈ T A t R}.encard : ENNReal) =
      ∑' k, {R' : SO n | Matrix.toEuclideanLin A (zpt k) ∈ T A t R'}.indicator 1 R := by
  rw [← Measure.count_apply (Set.to_countable _).measurableSet,
    ← lintegral_indicator_one (Set.to_countable _).measurableSet, lintegral_count]
  congr 1

lemma measurable_encard (ht : t ≠ 0) :
    Measurable fun R : SO n =>
      ({k : Fin n → ℤ | Matrix.toEuclideanLin A (zpt k) ∈ T A t R}.encard : ENNReal) := by
  simp_rw [encard_eq_tsum]
  exact Measurable.tsum fun k => measurable_one.indicator (measurableSet_slice ht _)

lemma lintegral_le (hn : 2 ≤ n) (hA : |A.det| = 1) {c e R₀ : ℝ} (hc0 : 0 ≤ c) (he : 0 ≤ e)
    (hcl : ∀ r : ℝ, 0 ≤ r → (Set.ncard {k : Fin n → ℤ | ‖Matrix.toEuclideanLin A (zpt k)‖ ≤ r} : ℝ)
      ≤ (volume (Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1)).toReal * r ^ n + c * (1 + r ^ e))
    (hop : ∀ r : ℝ, 0 ≤ r → (Set.ncard {k : Fin n → ℤ | ‖Matrix.toEuclideanLin A (zpt k)‖ < r} : ℝ)
      ≤ (volume (Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1)).toReal * r ^ n + c * (1 + r ^ e))
    (hP : para A ⊆ Metric.closedBall 0 R₀) (ht : 0 < t) :
    ∫⁻ R, ({k : Fin n → ℤ | Matrix.toEuclideanLin A (zpt k) ∈ T A t R}.encard : ENNReal) ∂(nu n) ≤
      ENNReal.ofReal (t ^ n) + ENNReal.ofReal (c * (1 + (t * R₀) ^ e)) := by
  have hdet : A.det ≠ 0 := by intro h; rw [h] at hA; simp at hA
  set C := ENNReal.ofReal (c * (1 + (t * R₀) ^ e))
  set F : EuclideanSpace ℝ (Fin n) → ℝ := fun y => (Fm A t y).toReal with hFdef
  have hFm_ne : ∀ y, Fm A t y ≠ ⊤ := fun y => measure_ne_top _ _
  have hF1 : ∀ y, F y ≤ 1 := fun y => by
    have : Fm A t y ≤ 1 := prob_le_one
    exact ENNReal.toReal_le_of_le_ofReal zero_le_one (by simpa using this)
  have hFm_meas : Measurable fun y => Fm A t y := by
    have : (fun y => Fm A t y) = fun y => nu n (Prod.mk y ⁻¹' Sig A t) :=
      funext fun y => by rw [Fm, slice_eq ht.ne']
    rw [this]; exact measurable_measure_prodMk_left measurableSet_Sig
  have hFmeas : Measurable F := hFm_meas.ennreal_toReal
  -- step a : Tonelli over the lattice
  have step_a : ∫⁻ R, ({k : Fin n → ℤ | Matrix.toEuclideanLin A (zpt k) ∈ T A t R}.encard : ENNReal)
      ∂(nu n) = ∫⁻ k, ENNReal.ofReal (F (Matrix.toEuclideanLin A (zpt k))) ∂Measure.count := by
    simp_rw [encard_eq_tsum]
    rw [lintegral_tsum (fun k => (measurable_one.indicator (measurableSet_slice ht.ne' _)).aemeasurable),
      lintegral_count]
    congr 1; ext k
    rw [lintegral_indicator_one (measurableSet_slice ht.ne' _), hFdef, ENNReal.ofReal_toReal (hFm_ne _)]
    rfl
  -- step b : layer cake on the lattice
  rw [step_a, lintegral_eq_lintegral_meas_lt Measure.count
    (ae_of_all _ fun k => ENNReal.toReal_nonneg) (measurable_of_countable _).aemeasurable]
  -- step c : pointwise comparison
  have step_c : ∫⁻ s in Set.Ioi 0, Measure.count {k | s < F (Matrix.toEuclideanLin A (zpt k))} ≤
      ∫⁻ s in Set.Ioi 0, (volume {y | s < F y} + (Set.Ioc (0:ℝ) 1).indicator (fun _ => C) s) := by
    apply setLIntegral_mono' measurableSet_Ioi
    intro s hs
    by_cases hs1 : s ≤ 1
    · rw [Set.indicator_of_mem (show s ∈ Set.Ioc (0:ℝ) 1 from ⟨hs, hs1⟩), Measure.count_apply (Set.to_countable _).measurableSet]
      refine encard_le (by omega) hdet hc0 he hcl hop {y | s < F y} ?_ ?_
      · intro x hx y hy
        exact lt_of_lt_of_le hx (ENNReal.toReal_mono (hFm_ne _) (Fm_anti hn ht.ne' hy))
      · intro x hx
        rw [mem_closedBall_zero_iff]
        have hpos : 0 < F x := lt_trans hs hx
        exact norm_le_of_Fm_pos hP ht.le (ENNReal.toReal_pos_iff.mp hpos).1
    · have : {k : Fin n → ℤ | s < F (Matrix.toEuclideanLin A (zpt k))} = ∅ := by
        ext k; simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_lt]
        linarith [hF1 (Matrix.toEuclideanLin A (zpt k))]
      simp [this]
  refine step_c.trans ?_
  rw [lintegral_add_right _ (measurable_const.indicator measurableSet_Ioc)]
  gcongr
  · -- step e : volume side
    rw [← lintegral_eq_lintegral_meas_lt volume (ae_of_all _ fun y => ENNReal.toReal_nonneg)
      hFmeas.aemeasurable]
    have h1 : ∀ y, ENNReal.ofReal (F y) = nu n (Prod.mk y ⁻¹' Sig A t) := fun y => by
      rw [hFdef]
      rw [ENNReal.ofReal_toReal (hFm_ne _), Fm, slice_eq ht.ne']
    refine (lintegral_congr h1).trans_le (le_of_eq ?_)
    rw [← Measure.prod_apply measurableSet_Sig, Measure.prod_apply_symm measurableSet_Sig]
    simp_rw [slice_eq' ht.ne', volume_T hA ht.le]
    simp
  · -- step f
    refine (setLIntegral_le_lintegral _ _).trans ?_
    rw [lintegral_indicator_const measurableSet_Ioc, Real.volume_Ioc]; simp

end Aux

open Aux in
theorem polytope_average {n : ℕ} (hn : 2 ≤ n) (A : Matrix (Fin n) (Fin n) ℝ) (hA : |A.det| = 1)
    {e : ℝ} (he : 0 ≤ e)
    (hball : ∃ c : ℝ, ∀ r : ℝ, 0 ≤ r →
      |(Set.ncard {k : Fin n → ℤ | ‖Matrix.toEuclideanLin A (zpt k)‖ ≤ r} : ℝ)
          - (volume (Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1)).toReal * r ^ n| ≤ c * (1 + r ^ e) ∧
      |(Set.ncard {k : Fin n → ℤ | ‖Matrix.toEuclideanLin A (zpt k)‖ < r} : ℝ)
          - (volume (Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1)).toReal * r ^ n| ≤ c * (1 + r ^ e)) :
    ∃ c : ℝ, ∀ t : ℕ, 1 ≤ t → ∃ R ∈ Matrix.specialOrthogonalGroup (Fin n) ℝ,
      (Set.ncard {k : Fin n → ℤ | Matrix.toEuclideanLin A (zpt k) ∈
          (t : ℝ) • (Matrix.toEuclideanLin R '' para A)} : ℝ) ≤ (t : ℝ) ^ n + c * (t : ℝ) ^ e := by
  obtain ⟨c, hc⟩ := hball
  have hc0 : 0 ≤ c := by
    have h := (abs_nonneg _).trans (hc 0 le_rfl).1
    have h1 : 0 < 1 + (0:ℝ) ^ e := by have := Real.rpow_nonneg (le_refl (0:ℝ)) e; linarith
    nlinarith
  have hcl : ∀ r : ℝ, 0 ≤ r →
      (Set.ncard {k : Fin n → ℤ | ‖Matrix.toEuclideanLin A (zpt k)‖ ≤ r} : ℝ)
        ≤ (volume (Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1)).toReal * r ^ n + c * (1 + r ^ e) :=
    fun r hr => by linarith [(le_abs_self _).trans (hc r hr).1]
  have hop : ∀ r : ℝ, 0 ≤ r →
      (Set.ncard {k : Fin n → ℤ | ‖Matrix.toEuclideanLin A (zpt k)‖ < r} : ℝ)
        ≤ (volume (Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1)).toReal * r ^ n + c * (1 + r ^ e) :=
    fun r hr => by linarith [(le_abs_self _).trans (hc r hr).2]
  obtain ⟨R₀, hR₀⟩ := (isCompact_para A).isBounded.subset_closedBall 0
  have hR0 : 0 ≤ R₀ := by
    have : (0 : EuclideanSpace ℝ (Fin n)) ∈ para A := ⟨0, fun i => by simp, by simp⟩
    simpa using hR₀ this
  refine ⟨c * (1 + R₀ ^ e), fun t ht => ?_⟩
  have htpos : (0:ℝ) < t := by exact_mod_cast ht
  obtain ⟨R, hR⟩ := exists_le_lintegral (μ := nu n) (measurable_encard (A := A) htpos.ne').aemeasurable
  have hbound := hR.trans (lintegral_le hn hA hc0 he hcl hop hR₀ htpos)
  have hX : 0 ≤ c * (1 + ((t:ℝ) * R₀) ^ e) :=
    mul_nonneg hc0 (add_nonneg zero_le_one (Real.rpow_nonneg (mul_nonneg htpos.le hR0) e))
  rw [← ENNReal.ofReal_add (pow_nonneg htpos.le n) hX] at hbound
  refine ⟨R.1, R.2, ?_⟩
  have key : (Set.ncard {k : Fin n → ℤ | Matrix.toEuclideanLin A (zpt k) ∈ T A t R} : ℝ) ≤
      (t:ℝ) ^ n + c * (1 + ((t:ℝ) * R₀) ^ e) := by
    rcases Set.finite_or_infinite {k : Fin n → ℤ | Matrix.toEuclideanLin A (zpt k) ∈ T A t R}
      with hfin | hinf
    · have h2 : ENNReal.ofReal (Set.ncard {k : Fin n → ℤ |
          Matrix.toEuclideanLin A (zpt k) ∈ T A t R} : ℝ) ≤
          ENNReal.ofReal ((t:ℝ) ^ n + c * (1 + ((t:ℝ) * R₀) ^ e)) := by
        refine le_trans (le_of_eq ?_) hbound
        rw [← hfin.cast_ncard_eq]; simp
      exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp h2
    · rw [hinf.ncard]; simp only [Nat.cast_zero]; positivity
  refine key.trans ?_
  rw [Real.mul_rpow htpos.le hR0]
  have h1 : 1 ≤ (t:ℝ) ^ e := Real.one_le_rpow (by exact_mod_cast ht) he
  have h2 : 0 ≤ R₀ ^ e := Real.rpow_nonneg hR0 e
  have h3 : c * 1 ≤ c * (t:ℝ) ^ e := mul_le_mul_of_nonneg_left h1 hc0
  nlinarith

open Aux in
theorem para_count {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.det ≠ 0) (t : ℕ) :
    Set.ncard {k : Fin n → ℤ | Matrix.toEuclideanLin A (zpt k) ∈ (t : ℝ) • para A} = (t + 1) ^ n := by
  have hset : {k : Fin n → ℤ | Matrix.toEuclideanLin A (zpt k) ∈ (t : ℝ) • para A} =
      ↑(Finset.Icc (0 : Fin n → ℤ) (fun _ => (t:ℤ))) := by
    ext k
    simp only [Set.mem_ofPred_eq, Set.mem_smul_set, Finset.coe_Icc, Set.mem_Icc]
    constructor
    · rintro ⟨x, ⟨s, hs, rfl⟩, hx⟩
      have hzs : zpt k = (t:ℝ) • s := by
        have := congrArg (Matrix.toEuclideanLin A⁻¹) hx
        rw [map_smul, toE_inv_toE hA, toE_inv_toE hA] at this
        exact this.symm
      have hk : ∀ i, (k i : ℝ) = t * s i := fun i => by
        have := congrArg (fun v => v i) hzs; simpa [zpt] using this
      refine ⟨fun i => ?_, fun i => ?_⟩
      · have : (0:ℝ) ≤ k i := by rw [hk]; exact mul_nonneg (Nat.cast_nonneg _) (hs i).1
        show (0:ℤ) ≤ k i
        exact_mod_cast this
      · have : (k i : ℝ) ≤ t := by
          rw [hk]; exact mul_le_of_le_one_right (Nat.cast_nonneg _) (hs i).2
        show k i ≤ (t:ℤ)
        exact_mod_cast this
    · rintro ⟨h0, h1⟩
      have a : ∀ i, (0:ℝ) ≤ k i := fun i => by exact_mod_cast h0 i
      have b : ∀ i, (k i:ℝ) ≤ t := fun i => by exact_mod_cast h1 i
      have hz : ((t:ℝ) * (t:ℝ)⁻¹) • zpt k = zpt k := by
        rcases eq_or_ne (t:ℝ) 0 with h | h
        · have : zpt k = 0 := by
            ext i; have h5 := a i; have h6 := b i; rw [h] at h6
            have h7 : (k i : ℝ) = 0 := by linarith
            simpa [zpt] using h7
          rw [this, smul_zero]
        · rw [mul_inv_cancel₀ h, one_smul]
      refine ⟨Matrix.toEuclideanLin A ((t:ℝ)⁻¹ • zpt k), ⟨(t:ℝ)⁻¹ • zpt k, fun i => ?_, rfl⟩, ?_⟩
      · simp only [PiLp.smul_apply, smul_eq_mul, Set.mem_Icc]
        have h4 : (zpt k) i = (k i : ℝ) := by simp [zpt]
        rw [h4]
        rcases eq_or_lt_of_le (Nat.cast_nonneg t : (0:ℝ) ≤ t) with h | h
        · rw [← h]; simp
        · exact ⟨mul_nonneg (inv_nonneg.mpr h.le) (a i), by rw [inv_mul_le_iff₀ h]; linarith [b i]⟩
      · rw [← map_smul, smul_smul, hz]
  rw [hset, Set.ncard_coe_finset, Pi.card_Icc]
  simp [Int.card_Icc]
end Polytope


-- ==== Core2.lean ====

namespace Polytope
open scoped Pointwise

variable {n : ℕ}

theorem det_toEuclideanLin (M : Matrix (Fin n) (Fin n) ℝ) :
    LinearMap.det (Matrix.toEuclideanLin M) = M.det := by
  rw [Matrix.toEuclideanLin_eq_toLin_orthonormal, LinearMap.det_toLin]

/-- The lattice-point count in the balls of the lattice `Aℤⁿ` (an ellipsoid count). -/
theorem ball_count (hn : 2 ≤ n) (A : Matrix (Fin n) (Fin n) ℝ) (hA : |A.det| = 1) :
    ∃ c : ℝ, ∀ r : ℝ, 0 ≤ r →
      |(Set.ncard {k : Fin n → ℤ | ‖Matrix.toEuclideanLin A (zpt k)‖ ≤ r} : ℝ)
          - (volume (Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1)).toReal * r ^ n| ≤
            c * (1 + r ^ hlawkaExp n) ∧
      |(Set.ncard {k : Fin n → ℤ | ‖Matrix.toEuclideanLin A (zpt k)‖ < r} : ℝ)
          - (volume (Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1)).toReal * r ^ n| ≤
            c * (1 + r ^ hlawkaExp n) := by
  have hA0 : A.det ≠ 0 := by intro h; rw [h, abs_zero] at hA; exact zero_ne_one hA
  set Linv := LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin A⁻¹)
  have hLinv : ∀ v, Matrix.toEuclideanLin A (Linv v) = v := by
    intro v
    show Matrix.toEuclideanLin A (Matrix.toEuclideanLin A⁻¹ v) = v
    rw [← Aux.toE_mul, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hA0)]; simp
  have hLinv' : ∀ v, Linv (Matrix.toEuclideanLin A v) = v := fun v => Aux.toE_inv_toE hA0 v
  have hdet : |LinearMap.det (Linv : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin n))| = 1 := by
    show |LinearMap.det (Matrix.toEuclideanLin A⁻¹)| = 1
    rw [det_toEuclideanLin, Matrix.det_nonsing_inv, Ring.inverse_eq_inv', abs_inv, hA, inv_one]
  have hu : IsUnit Linv := isUnit_of_det_ne_zero (by
    intro h; rw [h, abs_zero] at hdet; exact zero_ne_one hdet)
  obtain ⟨c, hc⟩ := hlawka_ellipsoid hn (G := {Linv}) isCompact_singleton
    (fun g hg => by rw [Set.mem_singleton_iff.1 hg]; exact hu)
  set om := (volume (Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1)).toReal
  have hom : 0 ≤ om := ENNReal.toReal_nonneg
  -- the closed count as a lattice count of an ellipsoid
  have hset : ∀ r, 0 < r → {k : Fin n → ℤ | ‖Matrix.toEuclideanLin A (zpt k)‖ ≤ r} =
      {k | zpt k ∈ (fun x => r • Linv x + 0) '' Metric.closedBall 0 1} := by
    intro r hr; ext k
    simp only [Set.mem_ofPred_eq, Set.mem_image, Metric.mem_closedBall, dist_zero_right, add_zero]
    constructor
    · intro hk
      refine ⟨r⁻¹ • Matrix.toEuclideanLin A (zpt k), ?_, ?_⟩
      · rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.2 hr), inv_mul_le_iff₀ hr, mul_one]
        exact hk
      · rw [map_smul, hLinv', smul_smul, mul_inv_cancel₀ hr.ne', one_smul]
    · rintro ⟨x, hx, hxe⟩
      rw [← hxe, map_smul, hLinv, norm_smul, Real.norm_eq_abs, abs_of_pos hr]
      nlinarith [norm_nonneg x]
  have hfin : ∀ r, {k : Fin n → ℤ | ‖Matrix.toEuclideanLin A (zpt k)‖ ≤ r}.Finite :=
    fun r => Aux.finite_ball hA0 r
  set K0 := (Set.ncard {k : Fin n → ℤ | ‖Matrix.toEuclideanLin A (zpt k)‖ ≤ 1} : ℝ)
  set c' := max c 0 + K0 + om
  have hcl : ∀ r : ℝ, 0 ≤ r →
      |(Set.ncard {k : Fin n → ℤ | ‖Matrix.toEuclideanLin A (zpt k)‖ ≤ r} : ℝ) - om * r ^ n| ≤
        c' * (1 + r ^ hlawkaExp n) := by
    intro r hr
    have hre : 0 ≤ r ^ hlawkaExp n := Real.rpow_nonneg hr _
    have hK0 : 0 ≤ K0 := Nat.cast_nonneg _
    rcases lt_or_ge r 1 with hr1 | hr1
    · have hle : (Set.ncard {k : Fin n → ℤ | ‖Matrix.toEuclideanLin A (zpt k)‖ ≤ r} : ℝ) ≤ K0 := by
        have := Set.ncard_le_ncard (s := {k : Fin n → ℤ | ‖Matrix.toEuclideanLin A (zpt k)‖ ≤ r})
          (t := {k : Fin n → ℤ | ‖Matrix.toEuclideanLin A (zpt k)‖ ≤ 1})
          (fun k hk => by simp only [Set.mem_ofPred_eq] at hk ⊢; linarith) (hfin 1)
        exact Nat.cast_le.2 this
      have hrn : r ^ n ≤ 1 := pow_le_one₀ hr hr1.le
      have h0 : (0 : ℝ) ≤ Set.ncard {k : Fin n → ℤ | ‖Matrix.toEuclideanLin A (zpt k)‖ ≤ r} :=
        Nat.cast_nonneg _
      have hc0 : 0 ≤ max c 0 := le_max_right _ _
      rw [abs_le]; constructor <;> nlinarith [pow_nonneg hr n]
    · have h1 := hc r hr1 Linv rfl 0
      simp only [latCount] at h1
      rw [← hset r (by linarith), hdet, mul_one] at h1
      calc _ = |(Set.ncard {k : Fin n → ℤ | ‖Matrix.toEuclideanLin A (zpt k)‖ ≤ r} : ℝ) -
            r ^ n * om| := by ring_nf
        _ ≤ c * r ^ hlawkaExp n := h1
        _ ≤ c' * (1 + r ^ hlawkaExp n) := by
            have : c ≤ c' := by
              have := le_max_left c 0; have hK0 : 0 ≤ K0 := Nat.cast_nonneg _; linarith
            have hc'0 : 0 ≤ c' := by
              have := le_max_right c 0; have hK0 : 0 ≤ K0 := Nat.cast_nonneg _; linarith
            nlinarith
  refine ⟨c', fun r hr => ⟨hcl r hr, ?_⟩⟩
  have hc'0 : 0 ≤ c' := by
    have := le_max_right c 0; have hK0 : 0 ≤ K0 := Nat.cast_nonneg _; linarith
  rcases hr.eq_or_lt with hr0 | hr0
  · subst hr0
    have : {k : Fin n → ℤ | ‖Matrix.toEuclideanLin A (zpt k)‖ < 0} = ∅ := by
      ext k; simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_lt]
      exact norm_nonneg _
    rw [this, Set.ncard_empty, zero_pow (by omega)]
    simp only [Nat.cast_zero, mul_zero, sub_zero, abs_zero]
    positivity
  have hsub : {k : Fin n → ℤ | ‖Matrix.toEuclideanLin A (zpt k)‖ < r} ⊆
      {k | ‖Matrix.toEuclideanLin A (zpt k)‖ ≤ r} := fun k hk => by
    simp only [Set.mem_ofPred_eq] at hk ⊢; exact hk.le
  have hup : (Set.ncard {k : Fin n → ℤ | ‖Matrix.toEuclideanLin A (zpt k)‖ < r} : ℝ) ≤
      Set.ncard {k : Fin n → ℤ | ‖Matrix.toEuclideanLin A (zpt k)‖ ≤ r} := by
    exact_mod_cast Set.ncard_le_ncard hsub (hfin r)
  have hcr := hcl r hr
  rw [abs_le] at hcr ⊢
  constructor
  · -- lower bound by a limit from below
    have hlow : ∀ r' : ℝ, 0 ≤ r' → r' < r →
        om * r' ^ n ≤ Set.ncard {k : Fin n → ℤ | ‖Matrix.toEuclideanLin A (zpt k)‖ < r} +
          c' * (1 + r ^ hlawkaExp n) := by
      intro r' hr' hr'r
      have h1 := (abs_le.1 (hcl r' hr')).1
      have h2 : (Set.ncard {k : Fin n → ℤ | ‖Matrix.toEuclideanLin A (zpt k)‖ ≤ r'} : ℝ) ≤
          Set.ncard {k : Fin n → ℤ | ‖Matrix.toEuclideanLin A (zpt k)‖ < r} := by
        have := Set.ncard_le_ncard (s := {k : Fin n → ℤ | ‖Matrix.toEuclideanLin A (zpt k)‖ ≤ r'})
          (t := {k : Fin n → ℤ | ‖Matrix.toEuclideanLin A (zpt k)‖ < r})
          (fun k hk => by simp only [Set.mem_ofPred_eq] at hk ⊢; linarith) ((hfin r).subset hsub)
        exact_mod_cast this
      have h3 : r' ^ hlawkaExp n ≤ r ^ hlawkaExp n :=
        Real.rpow_le_rpow hr' hr'r.le (hlawkaExp_nonneg hn)
      nlinarith
    have hlim : Tendsto (fun r' : ℝ => om * r' ^ n) (𝓝[<] r) (𝓝 (om * r ^ n)) :=
      ((continuous_const.mul (continuous_pow n)).tendsto r).mono_left nhdsWithin_le_nhds
    have hev : ∀ᶠ r' in 𝓝[<] r, om * r' ^ n ≤
        Set.ncard {k : Fin n → ℤ | ‖Matrix.toEuclideanLin A (zpt k)‖ < r} +
          c' * (1 + r ^ hlawkaExp n) := by
      filter_upwards [Ioo_mem_nhdsLT hr0] with r' hr'
      exact hlow r' hr'.1.le hr'.2
    have := le_of_tendsto hlim hev
    linarith
  · linarith [hcr.2]

/-- The granular content for `Λ = h Aℤⁿ`. -/
def muA (A : Matrix (Fin n) (Fin n) ℝ) (h : ℝ) (S : Set (EuclideanSpace ℝ (Fin n))) : ℝ :=
  h ^ n * (Set.ncard {k : Fin n → ℤ | h • Matrix.toEuclideanLin A (zpt k) ∈ S} : ℝ)

theorem muA_set (A : Matrix (Fin n) (Fin n) ℝ) {t : ℕ} (ht : 1 ≤ t)
    (S : Set (EuclideanSpace ℝ (Fin n))) :
    {k : Fin n → ℤ | ((t : ℝ)⁻¹) • Matrix.toEuclideanLin A (zpt k) ∈ S} =
      {k | Matrix.toEuclideanLin A (zpt k) ∈ (t : ℝ) • S} := by
  have ht0 : (t : ℝ) ≠ 0 := by positivity
  ext k
  simp only [Set.mem_ofPred_eq, Set.mem_smul_set_iff_inv_smul_mem₀ ht0]

/-- **Theorem (no lattice is isotropic for polytopes).** For `L = Aℤⁿ` of covolume 1 and
`h = 1/t`, `t ∈ ℕ`: `μ_Λ(P_L) = (1+h)ⁿ`, and some rotation `R ∈ SO(n)` has
`μ_Λ(P_L) - μ_Λ(R P_L) ≥ n h - c h^{2-2/(n+1)}`. -/
theorem polytope_nogo (hn : 2 ≤ n) (A : Matrix (Fin n) (Fin n) ℝ) (hA : |A.det| = 1) :
    ∃ c : ℝ, ∀ t : ℕ, 1 ≤ t →
      muA A ((t : ℝ)⁻¹) (para A) = (1 + (t : ℝ)⁻¹) ^ n ∧
      ∃ R ∈ Matrix.specialOrthogonalGroup (Fin n) ℝ,
        n * (t : ℝ)⁻¹ - c * ((t : ℝ)⁻¹) ^ isoExp n ≤
          muA A ((t : ℝ)⁻¹) (para A) - muA A ((t : ℝ)⁻¹) (Matrix.toEuclideanLin R '' para A) := by
  have hA0 : A.det ≠ 0 := by intro h; rw [h, abs_zero] at hA; exact zero_ne_one hA
  obtain ⟨c, hc⟩ := polytope_average hn A hA (hlawkaExp_nonneg hn) (ball_count hn A hA)
  refine ⟨c, fun t ht => ?_⟩
  have htR : (1 : ℝ) ≤ t := by exact_mod_cast ht
  have ht0 : (0 : ℝ) < t := by linarith
  set h := (t : ℝ)⁻¹
  have hh0 : 0 < h := inv_pos.2 ht0
  have hP : muA A h (para A) = (1 + h) ^ n := by
    unfold muA; rw [muA_set A ht, para_count A hA0 t]
    push_cast
    rw [← mul_pow]; congr 1; simp only [h]; field_simp
  refine ⟨hP, ?_⟩
  obtain ⟨R, hR, hRb⟩ := hc t ht
  refine ⟨R, hR, ?_⟩
  rw [hP]
  unfold muA; rw [muA_set A ht]
  set N := (Set.ncard {k : Fin n → ℤ | Matrix.toEuclideanLin A (zpt k) ∈
    (t : ℝ) • (Matrix.toEuclideanLin R '' para A)} : ℝ)
  have hht : h * t = 1 := by simp only [h]; field_simp
  -- (1+h)ⁿ ≥ 1 + n h
  have hb : 1 + n * h ≤ (1 + h) ^ n := one_add_mul_le_pow (by linarith) n
  have hexp : h ^ n * (t : ℝ) ^ hlawkaExp n = h ^ isoExp n := by
    rw [← Real.rpow_natCast h, show (t : ℝ) = h⁻¹ by simp [h], Real.inv_rpow hh0.le,
      ← Real.rpow_neg hh0.le, ← Real.rpow_add hh0]
    congr 1; simp only [hlawkaExp, isoExp]; ring
  have hhn : h ^ n * (t : ℝ) ^ n = 1 := by rw [← mul_pow, hht, one_pow]
  have hpos : 0 < h ^ n := by positivity
  have : h ^ n * N ≤ 1 + c * h ^ isoExp n := by
    calc h ^ n * N ≤ h ^ n * ((t : ℝ) ^ n + c * (t : ℝ) ^ hlawkaExp n) :=
          mul_le_mul_of_nonneg_left hRb hpos.le
      _ = 1 + c * h ^ isoExp n := by rw [mul_add, hhn, ← hexp]; ring
  linarith

/-- **Hyperfinite reading of the polytope no-go theorem.** For a hypernatural `N = [t_i] ≥ 1`
(`h = 1/N`) there is an internal rotation `R = [R_i] ∈ *SO(n)` with
`μ_Λ(P_L) - μ_Λ(R P_L) ≥ n h - c h^{2-2/(n+1)}`, and `μ_Λ(P_L) = (1+h)ⁿ`. -/
theorem polytope_nogo_hyper (hn : 2 ≤ n) (A : Matrix (Fin n) (Fin n) ℝ) (hA : |A.det| = 1) :
    ∃ c : ℝ, ∀ ts : ℕ → ℕ, (∀ i, 1 ≤ ts i) →
      ∃ Rs : ℕ → Matrix (Fin n) (Fin n) ℝ, (∀ i, Rs i ∈ Matrix.specialOrthogonalGroup (Fin n) ℝ) ∧
        Hyperreal.ofSeq (fun i => muA A ((ts i : ℝ)⁻¹) (para A)) =
          Hyperreal.ofSeq (fun i => (1 + (ts i : ℝ)⁻¹) ^ n) ∧
        Hyperreal.ofSeq (fun i => n * (ts i : ℝ)⁻¹ - c * ((ts i : ℝ)⁻¹) ^ isoExp n) ≤
          Hyperreal.ofSeq (fun i => muA A ((ts i : ℝ)⁻¹) (para A) -
            muA A ((ts i : ℝ)⁻¹) (Matrix.toEuclideanLin (Rs i) '' para A)) := by
  obtain ⟨c, hc⟩ := polytope_nogo hn A hA
  refine ⟨c, fun ts hts => ?_⟩
  choose hP R hR hRb using fun i => hc (ts i) (hts i)
  exact ⟨R, hR, congrArg Hyperreal.ofSeq (funext hP),
    Hyperreal.ofSeq_le_ofSeq.2 (Filter.Eventually.of_forall hRb)⟩

end Polytope

section Hyper
open Hyperreal QE.Hyper

theorem tendsto_of_infinitesimal {f : ℕ → ℝ} (hf : Infinitesimal (ofSeq f)) :
    Tendsto f (hyperfilter ℕ) (𝓝 0) := by
  have hfin : IsFinite (ofSeq f) := le_of_lt hf
  have h := tendsto_stdPart hfin
  have h0 : ArchimedeanClass.stdPart (ofSeq f) = 0 := by
    have : Icl (ofSeq f) ((0 : ℝ) : ℝ*) := by
      unfold Icl; simpa using hf
    rw [stdPart_eq_of_icl this, st_real]
  rw [h0] at h
  exact tendsto_ofSeq.1 h

/-- **Hyperfinite reading of the isotropy theorem.** For an internal granule `h = [h_i]`,
internal rotations `R = [R_i]` and translations `v = [v_i]`:
`|μ_Λ(RC+v) - vol C| ≤ c h^{2-2/(n+1)}`, and if `h ≈ 0` then
`(μ_Λ(RC+v) - μ_Λ(C))/h ≈ 0`. -/
theorem isotropy_hyper (hn : 2 ≤ n) {L : (EuclideanSpace ℝ (Fin n)) →L[ℝ] (EuclideanSpace ℝ (Fin n))}
    {C : Set (EuclideanSpace ℝ (Fin n))} {c : ℝ}
    (hc : ∀ h : ℝ, 0 < h → h ≤ 1 → ∀ R : (EuclideanSpace ℝ (Fin n)) ≃ₗᵢ[ℝ] (EuclideanSpace ℝ (Fin n)),
      ∀ v : EuclideanSpace ℝ (Fin n),
      |muLam L h ((fun x => R x + v) '' C) - (volume C).toReal| ≤ c * h ^ isoExp n)
    (hs : ℕ → ℝ) (hpos : ∀ i, 0 < hs i) (hle : ∀ i, hs i ≤ 1)
    (Rs : ℕ → (EuclideanSpace ℝ (Fin n)) ≃ₗᵢ[ℝ] (EuclideanSpace ℝ (Fin n)))
    (vs : ℕ → EuclideanSpace ℝ (Fin n)) :
    ofSeq (fun i => |muLam L (hs i) ((fun x => Rs i x + vs i) '' C) - (volume C).toReal|) ≤
        ofSeq (fun i => c * hs i ^ isoExp n) ∧
      (Infinitesimal (ofSeq hs) →
        Infinitesimal (ofSeq (fun i =>
          (muLam L (hs i) ((fun x => Rs i x + vs i) '' C) - muLam L (hs i) C) / hs i)) ∧
        Infinitesimal (ofSeq (fun i => (muLam L (hs i) C - (volume C).toReal) / hs i))) := by
  refine ⟨ofSeq_le_ofSeq.2 (Filter.Eventually.of_forall fun i => hc _ (hpos i) (hle i) _ _), ?_⟩
  intro hinf
  have ht := tendsto_of_infinitesimal hinf
  set θ := 1 - 2 / ((n : ℝ) + 1)
  have hθ : 0 < θ := by
    simp only [θ]
    have : (2 : ℝ) ≤ n := by exact_mod_cast hn
    rw [sub_pos, div_lt_one (by linarith)]
    linarith
  have hb : Tendsto (fun i => 2 * c * hs i ^ θ) (hyperfilter ℕ) (𝓝 0) := by
    have h1 : Tendsto (fun i => hs i ^ θ) (hyperfilter ℕ) (𝓝 ((0 : ℝ) ^ θ)) :=
      (Real.continuousAt_rpow_const 0 θ (Or.inr hθ.le)).tendsto.comp ht
    rw [Real.zero_rpow hθ.ne'] at h1
    simpa using h1.const_mul (2 * c)
  have hx : Tendsto (fun i =>
      (muLam L (hs i) ((fun x => Rs i x + vs i) '' C) - muLam L (hs i) C) / hs i)
      (hyperfilter ℕ) (𝓝 0) := by
    refine squeeze_zero_norm (fun i => ?_) hb
    rw [Real.norm_eq_abs, abs_div, abs_of_pos (hpos i)]
    exact isotropy_first_order hc (hpos i) (hle i) (Rs i) (vs i)
  have hb2 : Tendsto (fun i => c * hs i ^ θ) (hyperfilter ℕ) (𝓝 0) := by
    have := hb.const_mul (1 / 2)
    simp only [mul_zero] at this
    refine this.congr (fun i => ?_)
    ring
  have hy : Tendsto (fun i => (muLam L (hs i) C - (volume C).toReal) / hs i)
      (hyperfilter ℕ) (𝓝 0) := by
    refine squeeze_zero_norm (fun i => ?_) hb2
    have h2 := hc (hs i) (hpos i) (hle i) (LinearIsometryEquiv.refl ℝ _) 0
    have hC : (fun x => (LinearIsometryEquiv.refl ℝ (EuclideanSpace ℝ (Fin n))) x + 0) '' C = C := by
      simp
    rw [hC] at h2
    have hexp : hs i ^ isoExp n = hs i * hs i ^ θ := by
      rw [show isoExp n = 1 + θ by simp only [isoExp, θ]; ring, Real.rpow_add (hpos i),
        Real.rpow_one]
    rw [Real.norm_eq_abs, abs_div, abs_of_pos (hpos i), div_le_iff₀ (hpos i)]
    calc _ ≤ c * hs i ^ isoExp n := h2
      _ = c * hs i ^ θ * hs i := by rw [hexp]; ring
  constructor
  · have := icl_of_tendsto (x := ofSeq _) (r := 0) (tendsto_ofSeq.2 hx)
    unfold Icl at this
    simpa using this
  · have := icl_of_tendsto (x := ofSeq _) (r := 0) (tendsto_ofSeq.2 hy)
    unfold Icl at this
    simpa using this

end Hyper

-- ==== ValueLattice.lean ====

namespace ValueLattice
open QE.OpenSto.Field
variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ]
/-- the value lattice `ηℤ ∩ [-ηM, ηM]`, indexed by `k ∈ [-M, M]`. -/
abbrev VL (M : ℕ) := {k : ℤ // k ∈ Finset.Icc (-(M : ℤ)) M}
/-- moment of a polynomial under the value-lattice φ⁴ measure with granule η and horizon ηM. -/
def latMoment (η : ℝ) (M : ℕ) (bonds : Finset (Λ × Λ)) (m2 lam : ℝ) (P : MvPolynomial Λ ℝ) : ℝ :=
  ∑ φ : Λ → VL M, MvPolynomial.eval (fun x => η * ((φ x : ℤ) : ℝ)) P *
    gibbs (phi4Action (fun v : VL M => η * ((v : ℤ) : ℝ)) bonds m2 lam) φ
/-- classical lattice action on `ℝ^Λ`. -/
def contAction (bonds : Finset (Λ × Λ)) (m2 lam : ℝ) (φ : Λ → ℝ) : ℝ :=
  freeForm bonds m2 φ / 2 + lam * ∑ x, φ x ^ 4
def contMoment (bonds : Finset (Λ × Λ)) (m2 lam : ℝ) (P : MvPolynomial Λ ℝ) : ℝ :=
  (∫ φ : Λ → ℝ, MvPolynomial.eval φ P * Real.exp (-contAction bonds m2 lam φ)) /
    ∫ φ : Λ → ℝ, Real.exp (-contAction bonds m2 lam φ)

namespace RAux

/-- the cell of the grid `ηℤ^Λ` with lower corner `ηk`. -/
def cell (η : ℝ) (k : Λ → ℤ) : Set (Λ → ℝ) := {φ | ∀ x, ⌊φ x / η⌋ = k x}

lemma cell_eq {η : ℝ} (hη : 0 < η) (k : Λ → ℤ) :
    cell η k = Set.pi Set.univ (fun x => Set.Ico (η * k x) (η * (k x + 1))) := by
  ext φ
  simp only [cell, Set.mem_ofPred_eq, Set.mem_pi, Set.mem_univ, true_implies, Set.mem_Ico,
    Int.floor_eq_iff]
  refine forall_congr' fun x => ?_
  rw [le_div_iff₀ hη, div_lt_iff₀ hη]
  constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith

lemma measurableSet_cell {η : ℝ} (hη : 0 < η) (k : Λ → ℤ) : MeasurableSet (cell η k) := by
  rw [cell_eq hη]
  exact MeasurableSet.univ_pi fun x => measurableSet_Ico

lemma volume_cell {η : ℝ} (hη : 0 < η) (k : Λ → ℤ) :
    (volume : Measure (Λ → ℝ)).real (cell η k) = η ^ Fintype.card Λ := by
  rw [cell_eq hη, measureReal_def, volume_pi_pi]
  simp only [Real.volume_Ico]
  rw [ENNReal.toReal_prod]
  rw [Finset.prod_congr rfl (fun x _ => show (ENNReal.ofReal (η * ((k x : ℝ) + 1) - η * k x)).toReal
    = η by rw [show η * ((k x : ℝ) + 1) - η * k x = η by ring, ENNReal.toReal_ofReal hη.le])]
  simp

/-- the piecewise constant function attached to the Riemann sum. -/
def G (F : (Λ → ℝ) → ℝ) (η : ℝ) (M : ℕ) (φ : Λ → ℝ) : ℝ :=
  ∑ k : Λ → VL M, (cell η (fun x => ((k x : ℤ)))).indicator
    (fun _ => F (fun x => η * ((k x : ℤ) : ℝ))) φ

lemma integral_G (F : (Λ → ℝ) → ℝ) {η : ℝ} (hη : 0 < η) (M : ℕ) :
    ∫ φ, G F η M φ = η ^ Fintype.card Λ * ∑ k : Λ → VL M, F (fun x => η * ((k x : ℤ) : ℝ)) := by
  unfold G
  rw [integral_finsetSum]
  · rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [integral_indicator_const _ (measurableSet_cell hη _), volume_cell hη, smul_eq_mul]
  · intro k _
    refine (integrable_indicator_iff (measurableSet_cell hη _)).2 ?_
    refine integrableOn_const ?_
    rw [cell_eq hη, volume_pi_pi]
    simp [ENNReal.prod_ne_top]

lemma G_eq (F : (Λ → ℝ) → ℝ) (η : ℝ) (M : ℕ) (φ : Λ → ℝ) :
    G F η M φ = if (∀ x, ⌊φ x / η⌋ ∈ Finset.Icc (-(M : ℤ)) M) then
      F (fun x => η * (⌊φ x / η⌋ : ℝ)) else 0 := by
  unfold G
  split_ifs with h
  · let k0 : Λ → VL M := fun x => ⟨⌊φ x / η⌋, h x⟩
    rw [Finset.sum_eq_single k0]
    · rw [Set.indicator_of_mem (show φ ∈ cell η _ from fun x => rfl)]
    · intro k _ hk
      rw [Set.indicator_of_notMem]
      intro hφ
      apply hk
      funext x
      exact Subtype.ext (hφ x).symm
    · intro h; exact absurd (Finset.mem_univ _) h
  · refine Finset.sum_eq_zero fun k _ => ?_
    rw [Set.indicator_of_notMem]
    intro hφ
    apply h
    intro x
    rw [hφ x]
    exact (k x).2

lemma floor_le' {η : ℝ} (hη : 0 < η) (s : ℝ) : η * (⌊s / η⌋ : ℝ) ≤ s := by
  have := Int.floor_le (s / η)
  have h2 : η * (s / η) = s := by field_simp
  nlinarith

lemma floor_gt' {η : ℝ} (hη : 0 < η) (s : ℝ) : s - η < η * (⌊s / η⌋ : ℝ) := by
  have := Int.lt_floor_add_one (s / η)
  have h2 : η * (s / η) = s := by field_simp
  nlinarith

lemma floor_sq {η : ℝ} (hη : 0 < η) (hη1 : η ≤ 1) (s : ℝ) :
    s ^ 2 / 2 - 1 ≤ (η * (⌊s / η⌋ : ℝ)) ^ 2 := by
  have h1 := floor_le' hη s
  have h2 := floor_gt' hη s
  set t := η * (⌊s / η⌋ : ℝ)
  rcases le_or_gt 0 s with hs | hs
  · have ht : 0 ≤ t := by
      have : (0 : ℤ) ≤ ⌊s / η⌋ := Int.floor_nonneg.2 (div_nonneg hs hη.le)
      have : (0 : ℝ) ≤ (⌊s / η⌋ : ℝ) := by exact_mod_cast this
      positivity
    rcases le_or_gt s 1 with hs1 | hs1
    · nlinarith
    · have h3 : s - 1 ≤ t := by linarith
      nlinarith [mul_le_mul h3 h3 (by linarith) ht, sq_nonneg (s - 2)]
  · nlinarith

lemma floor_mem {η Ω s : ℝ} (hη : 0 < η) (hη1 : η ≤ 1) (hΩ : |s| + 1 ≤ Ω) :
    ⌊s / η⌋ ∈ Finset.Icc (-((⌊Ω / η⌋₊ : ℕ) : ℤ)) (⌊Ω / η⌋₊ : ℕ) := by
  have hM := Nat.lt_floor_add_one (Ω / η)
  set M := ⌊Ω / η⌋₊
  have hs1 := le_abs_self s
  have hs2 := neg_abs_le s
  have e1 : η * (Ω / η) = Ω := by field_simp
  have e2 : η * (s / η) = s := by field_simp
  rw [Finset.mem_Icc]
  constructor
  · rw [Int.le_floor]
    push_cast
    nlinarith
  · have h3 := Int.floor_le (s / η)
    have : (⌊s / η⌋ : ℝ) < (M : ℝ) + 1 := by nlinarith
    have : ⌊s / η⌋ < (M : ℤ) + 1 := by exact_mod_cast this
    omega

lemma integrable_bound (c C : ℝ) (hc : 0 < c) :
    Integrable (fun φ : Λ → ℝ => C * ∏ x, Real.exp (-c * (φ x ^ 2 / 2 - 1))) := by
  refine Integrable.const_mul ?_ C
  have : ∀ x : Λ, Integrable (fun s : ℝ => Real.exp (-c * (s ^ 2 / 2 - 1))) := by
    intro x
    have h := (integrable_exp_neg_mul_sq (b := c / 2) (by positivity)).const_mul (Real.exp c)
    refine h.congr (Eventually.of_forall fun s => ?_)
    simp only
    rw [← Real.exp_add]; ring_nf
  exact Integrable.fintype_prod (μ := fun _ => volume) this

/-- Riemann sums over the truncated value lattice converge to the integral. -/
theorem riemann (F : (Λ → ℝ) → ℝ) (hF : Continuous F) {C c : ℝ} (hc : 0 < c)
    (hb : ∀ φ, |F φ| ≤ C * Real.exp (-c * ∑ x, φ x ^ 2)) :
    Tendsto (fun p : ℝ × ℝ => p.1 ^ Fintype.card Λ *
        ∑ k : Λ → VL ⌊p.2 / p.1⌋₊, F (fun x => p.1 * ((k x : ℤ) : ℝ)))
      (𝓝[>] 0 ×ˢ atTop) (𝓝 (∫ φ, F φ)) := by
  have hC : 0 ≤ C := by
    have h := hb 0
    have := abs_nonneg (F 0)
    by_contra hC; push Not at hC
    have := Real.exp_pos (-c * ∑ x, (0 : Λ → ℝ) x ^ 2)
    nlinarith
  have hη : ∀ᶠ p : ℝ × ℝ in 𝓝[>] 0 ×ˢ atTop, p.1 ∈ Set.Ioo 0 1 :=
    tendsto_fst.eventually (Ioo_mem_nhdsGT zero_lt_one)
  have hfst : Tendsto (fun p : ℝ × ℝ => p.1) (𝓝[>] 0 ×ˢ atTop) (𝓝 0) :=
    tendsto_fst.mono_right nhdsWithin_le_nhds
  have key : Tendsto (fun p : ℝ × ℝ => ∫ φ, RAux.G F p.1 ⌊p.2 / p.1⌋₊ φ)
      (𝓝[>] 0 ×ˢ atTop) (𝓝 (∫ φ, F φ)) := by
    refine tendsto_integral_filter_of_dominated_convergence
      (fun φ => C * ∏ x, Real.exp (-c * (φ x ^ 2 / 2 - 1))) ?_ ?_ (integrable_bound c C hc) ?_
    · filter_upwards [hη] with p hp
      refine Measurable.aestronglyMeasurable ?_
      refine Finset.measurable_fun_sum _ fun k _ => ?_
      exact measurable_const.indicator (measurableSet_cell hp.1 _)
    · filter_upwards [hη] with p hp
      refine Eventually.of_forall fun φ => ?_
      rw [G_eq, Real.norm_eq_abs]
      split_ifs
      · refine (hb _).trans ?_
        refine mul_le_mul_of_nonneg_left ?_ hC
        rw [← Real.exp_sum]
        refine Real.exp_le_exp.2 ?_
        rw [← Finset.mul_sum]
        have : ∑ x, (φ x ^ 2 / 2 - 1) ≤ ∑ x, (p.1 * (⌊φ x / p.1⌋ : ℝ)) ^ 2 :=
          Finset.sum_le_sum fun x _ => floor_sq hp.1 hp.2.le (φ x)
        nlinarith
      · simp only [abs_zero]; positivity
    · refine Eventually.of_forall fun φ => ?_
      have hev : ∀ᶠ p : ℝ × ℝ in 𝓝[>] 0 ×ˢ atTop,
          RAux.G F p.1 ⌊p.2 / p.1⌋₊ φ = F (fun x => p.1 * (⌊φ x / p.1⌋ : ℝ)) := by
        have h2 : ∀ᶠ p : ℝ × ℝ in 𝓝[>] 0 ×ˢ atTop, ∀ x, |φ x| + 1 ≤ p.2 :=
          eventually_all.2 fun x => tendsto_snd.eventually (eventually_ge_atTop _)
        filter_upwards [hη, h2] with p hp h2
        rw [G_eq, if_pos (fun x => floor_mem hp.1 hp.2.le (h2 x))]
      refine Tendsto.congr' (EventuallyEq.symm hev) ?_
      refine (hF.tendsto φ).comp (tendsto_pi_nhds.2 fun x => ?_)
      rw [tendsto_iff_norm_sub_tendsto_zero]
      refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_ hfst
      filter_upwards [hη] with p hp
      have := floor_le' hp.1 (φ x)
      have := floor_gt' hp.1 (φ x)
      rw [Real.norm_eq_abs, abs_le]
      constructor <;> linarith
  refine key.congr' ?_
  filter_upwards [hη] with p hp
  exact integral_G F hp.1 _

lemma abs_le_exp {a : ℝ} (ha : 0 < a) (t : ℝ) : |t| ≤ (1 + 1 / a) * Real.exp (a * t ^ 2) := by
  have h1 := Real.add_one_le_exp (a * t ^ 2)
  have h2 : |t| ≤ (1 + 1 / a) * (1 + a * t ^ 2) := by
    have hinv : 0 < 1 / a := by positivity
    have hat : 1 / a * (a * t ^ 2) = t ^ 2 := by field_simp
    rcases le_or_gt |t| 1 with h | h
    · nlinarith [sq_nonneg t]
    · have : |t| ≤ t ^ 2 := by rw [← sq_abs]; nlinarith
      nlinarith [sq_nonneg t]
  have : 0 ≤ 1 + 1 / a := by positivity
  nlinarith

lemma poly_bound (P : MvPolynomial Λ ℝ) :
    ∀ ε > 0, ∃ C, ∀ φ : Λ → ℝ, |MvPolynomial.eval φ P| ≤ C * Real.exp (ε * ∑ x, φ x ^ 2) := by
  induction P using MvPolynomial.induction_on with
  | C a =>
    intro ε hε
    refine ⟨|a|, fun φ => ?_⟩
    simp only [MvPolynomial.eval_C]
    have : 1 ≤ Real.exp (ε * ∑ x, φ x ^ 2) :=
      Real.one_le_exp (mul_nonneg hε.le (Finset.sum_nonneg fun x _ => sq_nonneg _))
    nlinarith [abs_nonneg a]
  | add p q hp hq =>
    intro ε hε
    obtain ⟨C1, h1⟩ := hp ε hε
    obtain ⟨C2, h2⟩ := hq ε hε
    refine ⟨C1 + C2, fun φ => ?_⟩
    simp only [map_add]
    refine (abs_add_le _ _).trans ?_
    have := h1 φ; have := h2 φ
    nlinarith
  | mul_X p x hp =>
    intro ε hε
    obtain ⟨C1, h1⟩ := hp (ε / 2) (by positivity)
    refine ⟨C1 * (1 + 1 / (ε / 2)), fun φ => ?_⟩
    simp only [map_mul, MvPolynomial.eval_X, abs_mul]
    have hA := h1 φ
    have hB := abs_le_exp (a := ε / 2) (by positivity) (φ x)
    have hx : φ x ^ 2 ≤ ∑ y, φ y ^ 2 :=
      Finset.single_le_sum (f := fun y => φ y ^ 2) (fun y _ => sq_nonneg _) (Finset.mem_univ x)
    have hB' : |φ x| ≤ (1 + 1 / (ε / 2)) * Real.exp (ε / 2 * ∑ y, φ y ^ 2) := by
      refine hB.trans (mul_le_mul_of_nonneg_left ?_ (by positivity))
      exact Real.exp_le_exp.2 (by nlinarith)
    have e : Real.exp (ε * ∑ y, φ y ^ 2) =
        Real.exp (ε / 2 * ∑ y, φ y ^ 2) * Real.exp (ε / 2 * ∑ y, φ y ^ 2) := by
      rw [← Real.exp_add]; ring_nf
    rw [e]
    calc |MvPolynomial.eval φ p| * |φ x|
        ≤ (C1 * Real.exp (ε / 2 * ∑ y, φ y ^ 2)) *
          ((1 + 1 / (ε / 2)) * Real.exp (ε / 2 * ∑ y, φ y ^ 2)) :=
          mul_le_mul hA hB' (abs_nonneg _) ((abs_nonneg _).trans hA)
      _ = _ := by ring

lemma action_ge (bonds : Finset (Λ × Λ)) {m2 lam : ℝ} (hlam : 0 ≤ lam) (φ : Λ → ℝ) :
    m2 / 2 * ∑ x, φ x ^ 2 ≤ contAction bonds m2 lam φ := by
  unfold contAction
  have h1 := freeForm_ge bonds m2 φ
  have h2 : 0 ≤ lam * ∑ x, φ x ^ 4 :=
    mul_nonneg hlam (Finset.sum_nonneg fun x _ => by positivity)
  linarith

lemma continuous_contAction (bonds : Finset (Λ × Λ)) (m2 lam : ℝ) :
    Continuous (contAction (Λ := Λ) bonds m2 lam) := by
  unfold contAction freeForm
  fun_prop

lemma weight_bound (bonds : Finset (Λ × Λ)) {m2 lam : ℝ} (hm : 0 < m2) (hlam : 0 ≤ lam)
    (P : MvPolynomial Λ ℝ) : ∃ C, ∀ φ : Λ → ℝ,
      |MvPolynomial.eval φ P * Real.exp (-contAction bonds m2 lam φ)| ≤
        C * Real.exp (-(m2 / 4) * ∑ x, φ x ^ 2) := by
  obtain ⟨C, hC⟩ := poly_bound P (m2 / 4) (by positivity)
  refine ⟨C, fun φ => ?_⟩
  rw [abs_mul, Real.abs_exp]
  have hA := hC φ
  have hS := action_ge bonds hlam φ (m2 := m2)
  have e : Real.exp (-(m2 / 4) * ∑ x, φ x ^ 2) ≥
      Real.exp (m2 / 4 * ∑ x, φ x ^ 2) * Real.exp (-contAction bonds m2 lam φ) := by
    rw [← Real.exp_add]; exact Real.exp_le_exp.2 (by linarith)
  have hC0 : 0 ≤ C := by
    have := abs_nonneg (MvPolynomial.eval φ P)
    have := Real.exp_pos (m2 / 4 * ∑ x, φ x ^ 2)
    by_contra h; push Not at h; nlinarith
  calc |MvPolynomial.eval φ P| * Real.exp (-contAction bonds m2 lam φ)
      ≤ (C * Real.exp (m2 / 4 * ∑ x, φ x ^ 2)) * Real.exp (-contAction bonds m2 lam φ) :=
        mul_le_mul_of_nonneg_right hA (Real.exp_pos _).le
    _ ≤ C * Real.exp (-(m2 / 4) * ∑ x, φ x ^ 2) := by
        rw [mul_assoc]; exact mul_le_mul_of_nonneg_left e hC0

lemma integrable_of_bound (F : (Λ → ℝ) → ℝ) (hF : Continuous F) {C c : ℝ} (hc : 0 < c)
    (hb : ∀ φ, |F φ| ≤ C * Real.exp (-c * ∑ x, φ x ^ 2)) : Integrable F := by
  have hI : Integrable (fun φ : Λ → ℝ => C * ∏ x, Real.exp (-c * φ x ^ 2)) :=
    (Integrable.fintype_prod (μ := fun _ => volume)
      (fun _ => integrable_exp_neg_mul_sq hc)).const_mul C
  refine hI.mono' hF.aestronglyMeasurable (Eventually.of_forall fun φ => ?_)
  rw [Real.norm_eq_abs, ← Real.exp_sum, ← Finset.mul_sum]
  exact hb φ

end RAux
open RAux in
theorem value_lattice_shadow (bonds : Finset (Λ × Λ)) {m2 lam : ℝ} (hm : 0 < m2) (hlam : 0 ≤ lam)
    (P : MvPolynomial Λ ℝ) :
    Tendsto (fun p : ℝ × ℝ => latMoment p.1 ⌊p.2 / p.1⌋₊ bonds m2 lam P) (𝓝[>] 0 ×ˢ atTop)
      (𝓝 (contMoment bonds m2 lam P)) := by
  have hc : 0 < m2 / 4 := by positivity
  have hcont := continuous_contAction (Λ := Λ) bonds m2 lam
  have hFP : Continuous fun φ : Λ → ℝ =>
      MvPolynomial.eval φ P * Real.exp (-contAction bonds m2 lam φ) :=
    (MvPolynomial.continuous_eval P).mul (hcont.neg.rexp)
  have hF1 : Continuous fun φ : Λ → ℝ => Real.exp (-contAction bonds m2 lam φ) := hcont.neg.rexp
  obtain ⟨CP, hCP⟩ := weight_bound bonds hm hlam P
  obtain ⟨C1, hC1⟩ := weight_bound bonds hm hlam 1
  have hC1' : ∀ φ : Λ → ℝ, |Real.exp (-contAction bonds m2 lam φ)| ≤
      C1 * Real.exp (-(m2 / 4) * ∑ x, φ x ^ 2) := fun φ => by simpa using hC1 φ
  have hN := riemann _ hFP hc hCP
  have hD := riemann _ hF1 hc hC1'
  have hpos : 0 < ∫ φ : Λ → ℝ, Real.exp (-contAction bonds m2 lam φ) :=
    integral_exp_pos (integrable_of_bound _ hF1 hc hC1')
  refine (hN.div hD hpos.ne').congr' ?_
  have hη : ∀ᶠ p : ℝ × ℝ in 𝓝[>] 0 ×ˢ atTop, 0 < p.1 :=
    tendsto_fst.eventually self_mem_nhdsWithin
  filter_upwards [hη] with p hp
  rw [Pi.div_apply]
  rw [mul_div_mul_left _ _ (pow_ne_zero _ hp.ne')]
  unfold latMoment gibbs partition
  simp only [← mul_div_assoc]
  rw [← Finset.sum_div]
  rfl
end ValueLattice

-- ==== GaussMoment_m.lean ====

namespace ValueLattice
open QE.OpenSto.Field
variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ]
namespace GAux
open MvPolynomial Finset

section Alg
variable {σ : Type*} [Fintype σ] [DecidableEq σ] (G : σ → σ → ℝ)

theorem Lpow_eq_zero' {k : ℕ} {P : MvPolynomial σ ℝ} (h : P.totalDegree < 2 * k) :
    (Lop G ^ k) P = 0 := by
  rw [← sum_homogeneousComponent P, map_sum]
  refine sum_eq_zero fun i hi => ?_
  rw [mem_range] at hi
  exact Lpow_eq_zero G (homogeneousComponent_isHomogeneous i P) (by omega)

theorem gaussN_stable' {P : MvPolynomial σ ℝ} {N : ℕ} (hN : P.totalDegree < 2 * N) (j : ℕ) :
    gaussN G (N + j) P = gaussN G N P := by
  unfold gaussN
  rw [sum_range_add]
  have : ∀ i ∈ range j, constantCoeff ((Lop G ^ (N + i)) P) / ((N + i).factorial : ℝ) = 0 := by
    intro i _; rw [Lpow_eq_zero' G (by omega), map_zero, zero_div]
  rw [sum_eq_zero this, add_zero]

theorem gauss_eq' {P : MvPolynomial σ ℝ} {N : ℕ} (hN : P.totalDegree < 2 * N) :
    gauss G P = gaussN G N P := by
  unfold gauss
  rcases le_total (P.totalDegree + 1) N with hle | hle
  · obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hle
    rw [gaussN_stable' G (by omega) j]
  · obtain ⟨j, hj⟩ := Nat.exists_eq_add_of_le hle
    rw [hj, gaussN_stable' G hN j]

theorem gauss_add (P Q : MvPolynomial σ ℝ) : gauss G (P + Q) = gauss G P + gauss G Q := by
  have h := totalDegree_add P Q
  set N := P.totalDegree + Q.totalDegree + 1
  rw [gauss_eq' G (N := N) (by omega), gauss_eq' G (P := P) (N := N) (by omega),
    gauss_eq' G (P := Q) (N := N) (by omega), gaussN_add]

theorem gauss_smul (c : ℝ) (P : MvPolynomial σ ℝ) : gauss G (c • P) = c * gauss G P := by
  have h : (c • P).totalDegree ≤ P.totalDegree := totalDegree_smul_le c P
  rw [gauss_eq' G (N := P.totalDegree + 1) (by omega), gauss_eq' G (P := P)
    (N := P.totalDegree + 1) (by omega), gaussN_smul]

/-- Uniqueness of a linear functional satisfying Gaussian integration by parts. -/
theorem uniq (L1 L2 : MvPolynomial σ ℝ → ℝ)
    (h1a : ∀ P Q, L1 (P + Q) = L1 P + L1 Q) (h1s : ∀ (c : ℝ) P, L1 (c • P) = c * L1 P)
    (h1o : L1 1 = 1)
    (h1X : ∀ x s c, L1 (X x * monomial s c) = ∑ y, G x y * L1 (pderiv y (monomial s c)))
    (h2a : ∀ P Q, L2 (P + Q) = L2 P + L2 Q) (h2s : ∀ (c : ℝ) P, L2 (c • P) = c * L2 P)
    (h2o : L2 1 = 1)
    (h2X : ∀ x s c, L2 (X x * monomial s c) = ∑ y, G x y * L2 (pderiv y (monomial s c)))
    (P : MvPolynomial σ ℝ) : L1 P = L2 P := by
  have hm : ∀ n, ∀ s : σ →₀ ℕ, s.degree = n → ∀ c, L1 (monomial s c) = L2 (monomial s c) := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro s hs c
      by_cases h0 : s = 0
      · subst h0
        have : (monomial 0 c : MvPolynomial σ ℝ) = c • 1 := by
          rw [smul_eq_C_mul, mul_one, C_apply]
        rw [this, h1s, h2s, h1o, h2o]
      · obtain ⟨x, hx⟩ : ∃ x, s x ≠ 0 := by
          by_contra h; push Not at h; exact h0 (Finsupp.ext h)
        set t := s - Finsupp.single x 1
        have hst : s = Finsupp.single x 1 + t := by
          rw [add_tsub_cancel_of_le]
          rw [Finsupp.single_le_iff]; omega
        have hmono : (monomial s c : MvPolynomial σ ℝ) = X x * monomial t c := by
          rw [X, monomial_mul_monomial, one_mul, ← hst]
        have hdeg : t.degree < n := by
          rw [← hs, hst, map_add, Finsupp.degree_single]; omega
        rw [hmono, h1X, h2X]
        refine sum_congr rfl fun y _ => ?_
        rw [pderiv_monomial]
        congr 1
        exact ih _ (lt_of_le_of_lt (Finsupp.degree_mono tsub_le_self) hdeg) _ rfl _
  induction P using MvPolynomial.induction_on' with
  | monomial s c => exact hm _ s rfl c
  | add p q hp hq => rw [h1a, h2a, hp, hq]

end Alg

section Ana
variable (bonds : Finset (Λ × Λ)) (m2 : ℝ)

/-- `H_y = (Aφ)_y` as a polynomial. -/
def H (y : Λ) : MvPolynomial Λ ℝ := ∑ z, precision bonds m2 y z • X z
/-- the free form as a polynomial. -/
def F : MvPolynomial Λ ℝ := ∑ x, X x * H bonds m2 x
/-- Gaussian weight. -/
def w (φ : Λ → ℝ) : ℝ := Real.exp (-(1 / 2 : ℝ) * eval φ (F bonds m2))

theorem eval_H (φ : Λ → ℝ) (y : Λ) : eval φ (H bonds m2 y) = ∑ z, precision bonds m2 y z * φ z := by
  simp [H, smul_eq_C_mul]

theorem eval_F (φ : Λ → ℝ) : eval φ (F bonds m2) = freeForm bonds m2 φ := by
  rw [← precision_quad]
  simp only [F, map_sum, map_mul, eval_X, eval_H, mul_sum]
  exact sum_congr rfl fun x _ => sum_congr rfl fun y _ => by ring

theorem prec_symm (x y : Λ) : precision bonds m2 x y = precision bonds m2 y x := by
  unfold precision
  congr 1
  · by_cases h : x = y <;> simp [h, eq_comm]
  · exact sum_congr rfl fun e _ => by ring

theorem eval_pderiv_F (φ : Λ → ℝ) (y : Λ) :
    eval φ (pderiv y (F bonds m2)) = 2 * eval φ (H bonds m2 y) := by
  have hH : ∀ x, pderiv y (H bonds m2 x) = C (precision bonds m2 x y) := by
    intro x
    simp [H, map_sum, smul_eq_C_mul, Pi.single_apply]
  simp only [F, map_sum, Derivation.leibniz, hH, pderiv_X_eq, smul_eq_mul, map_add, map_mul,
    eval_X, eval_C, eval_H]
  simp only [apply_ite (eval φ), map_one, map_zero, mul_ite, mul_one, mul_zero, sum_add_distrib,
    sum_ite_eq, mem_univ, ite_true]
  rw [show ∑ x, φ x * precision bonds m2 x y = ∑ z, precision bonds m2 y z * φ z from
    sum_congr rfl fun x _ => by rw [prec_symm]; ring]
  ring

/-- the derivative of a polynomial function. -/
def Dlin (Q : MvPolynomial Λ ℝ) (φ : Λ → ℝ) : (Λ → ℝ) →L[ℝ] ℝ :=
  ∑ y, eval φ (pderiv y Q) • ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Λ => ℝ) y

theorem hasFDerivAt_eval (Q : MvPolynomial Λ ℝ) (φ : Λ → ℝ) :
    HasFDerivAt (fun ψ => eval ψ Q) (Dlin Q φ) φ := by
  induction Q using MvPolynomial.induction_on with
  | C a =>
    simp only [eval_C, Dlin, pderiv_C, map_zero, zero_smul, sum_const_zero]
    exact hasFDerivAt_const _ _
  | add p q hp hq =>
    simp only [map_add]
    convert hp.add hq using 1
    simp only [Dlin, map_add, add_smul, sum_add_distrib]
  | mul_X p i hp =>
    simp only [map_mul, eval_X]
    convert hp.mul (hasFDerivAt_apply (𝕜 := ℝ) i φ) using 1
    ext v
    simp [Dlin, pderiv_mul, pderiv_X_eq, add_mul, sum_add_distrib, Pi.single_apply]
    simp only [apply_ite (eval φ), map_zero, ite_mul, zero_mul, sum_ite_eq, mem_univ, ite_true,
      mul_sum]
    exact congrArg _ (sum_congr rfl fun x _ => by ring)

theorem fderiv_eval (Q : MvPolynomial Λ ℝ) (φ : Λ → ℝ) (y : Λ) :
    fderiv ℝ (fun ψ => eval ψ Q) φ (Pi.single y 1) = eval φ (pderiv y Q) := by
  rw [(hasFDerivAt_eval Q φ).fderiv]
  simp [Dlin, Pi.single_apply]

theorem fderiv_w (φ : Λ → ℝ) (y : Λ) :
    fderiv ℝ (w bonds m2) φ (Pi.single y 1) = -(w bonds m2 φ * eval φ (H bonds m2 y)) := by
  have := ((hasFDerivAt_eval (F bonds m2) φ).const_mul (-(1 / 2 : ℝ))).exp
  rw [show w bonds m2 = fun ψ => Real.exp (-(1 / 2 : ℝ) * eval ψ (F bonds m2)) from rfl,
    this.fderiv]
  have h2 := eval_pderiv_F bonds m2 φ y
  simp only [smul_apply, Dlin, FunLike.coe_sum, Finset.sum_apply,
    FunLike.coe_smul, Pi.smul_apply, ContinuousLinearMap.proj_apply, Pi.single_apply,
    smul_eq_mul, mul_ite, mul_one, mul_zero, sum_ite_eq', mem_univ, ite_true, h2]
  ring

variable {m2}

theorem integ (hm : 0 < m2) (R : MvPolynomial Λ ℝ) :
    Integrable (fun φ => eval φ R * w bonds m2 φ) := by
  have hcont : ∀ R : MvPolynomial Λ ℝ, Continuous (fun φ => eval φ R * w bonds m2 φ) := by
    intro R
    unfold w
    exact (continuous_eval R).mul (Real.continuous_exp.comp
      (continuous_const.mul (continuous_eval _)))
  induction R using MvPolynomial.induction_on' with
  | add p q hp hq =>
    simp only [map_add, add_mul]; exact hp.add hq
  | monomial s c =>
    have h1 : ∀ x, Integrable (fun t : ℝ => |t| ^ s x * Real.exp (-(m2 / 2) * t ^ 2)) := by
      intro x
      have := (integrable_rpow_mul_exp_neg_mul_sq (b := m2 / 2) (by positivity)
        (s := (s x : ℝ)) (by have := (s x).cast_nonneg (α := ℝ); linarith)).norm
      refine this.congr (ae_of_all _ fun t => ?_)
      simp [Real.rpow_natCast, abs_mul, abs_pow]
    have hg : Integrable (fun φ : Λ → ℝ =>
        |c| * ∏ x, (|φ x| ^ s x * Real.exp (-(m2 / 2) * φ x ^ 2))) := by
      refine Integrable.const_mul ?_ _
      rw [volume_pi]
      exact Integrable.fintype_prod (f := fun x t => |t| ^ s x * Real.exp (-(m2 / 2) * t ^ 2)) h1
    refine hg.mono' (hcont _).aestronglyMeasurable (ae_of_all _ fun φ => ?_)
    unfold w
    rw [eval_monomial, Finsupp.prod_fintype _ _ (fun i => pow_zero _), norm_mul, norm_mul,
      Real.norm_eq_abs, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _),
      Finset.abs_prod, prod_mul_distrib, ← Real.exp_sum, mul_assoc]
    gcongr
    simp only [abs_pow, le_refl]
    rw [eval_F]
    have := freeForm_ge bonds m2 φ
    rw [← mul_sum]
    linarith

theorem ibp (hm : 0 < m2) (Q : MvPolynomial Λ ℝ) (y : Λ) :
    ∫ φ, eval φ (pderiv y Q) * w bonds m2 φ = ∫ φ, eval φ (H bonds m2 y * Q) * w bonds m2 φ := by
  have hdiff : ∀ R : MvPolynomial Λ ℝ, ∀ φ, DifferentiableAt ℝ (fun ψ => eval ψ R) φ :=
    fun R φ => (hasFDerivAt_eval R φ).differentiableAt
  have hwd : ∀ φ, DifferentiableAt ℝ (w bonds m2) φ := fun φ =>
    (((hasFDerivAt_eval (F bonds m2) φ).const_mul (-(1 / 2 : ℝ))).exp).differentiableAt
  have e1 : (fun φ => eval φ Q * fderiv ℝ (w bonds m2) φ (Pi.single y 1)) =
      fun φ => -(eval φ (H bonds m2 y * Q) * w bonds m2 φ) := by
    funext φ; rw [fderiv_w, eval_mul]; ring
  have e2 : (fun φ => fderiv ℝ (fun ψ => eval ψ Q) φ (Pi.single y 1) * w bonds m2 φ) =
      fun φ => eval φ (pderiv y Q) * w bonds m2 φ := by
    funext φ; rw [fderiv_eval]
  have := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable (μ := volume)
    (f := fun ψ => eval ψ Q) (g := w bonds m2) (v := Pi.single y (1 : ℝ))
    (by rw [e2]; exact integ bonds hm _) (by rw [e1]; exact (integ bonds hm _).neg)
    (integ bonds hm Q) (fun φ _ => hdiff Q φ) (fun φ _ => hwd φ)
  rw [e1, e2, integral_neg] at this
  linarith

theorem G_symm (hm : 0 < m2) (x y : Λ) :
    (precision bonds m2)⁻¹ x y = (precision bonds m2)⁻¹ y x := by
  have h := ((precision_posDef bonds m2 hm).isHermitian.inv).apply x y
  simpa using h.symm

theorem X_eq (hm : 0 < m2) (x : Λ) :
    (X x : MvPolynomial Λ ℝ) = ∑ y, (precision bonds m2)⁻¹ x y • H bonds m2 y := by
  have hdet : IsUnit (precision bonds m2).det :=
    (Matrix.isUnit_iff_isUnit_det _).mp (precision_invertible bonds m2 hm)
  have hGA := Matrix.nonsing_inv_mul (precision bonds m2) hdet
  simp only [H, smul_sum, smul_smul]
  rw [Finset.sum_comm]
  simp_rw [← Finset.sum_smul]
  have : ∀ z, ∑ y, (precision bonds m2)⁻¹ x y * precision bonds m2 y z =
      if x = z then 1 else 0 := by
    intro z
    rw [← Matrix.mul_apply, hGA, Matrix.one_apply]
  simp_rw [this, ite_smul, one_smul, zero_smul, sum_ite_eq, mem_univ, ite_true]

variable (m2) in
/-- unnormalised Gaussian integral. -/
def Iw (R : MvPolynomial Λ ℝ) : ℝ := ∫ φ, eval φ R * w bonds m2 φ

theorem Iw_add (hm : 0 < m2) (P Q : MvPolynomial Λ ℝ) :
    Iw bonds m2 (P + Q) = Iw bonds m2 P + Iw bonds m2 Q := by
  unfold Iw
  simp only [map_add, add_mul]
  exact integral_add (integ bonds hm P) (integ bonds hm Q)

theorem Iw_smul (c : ℝ) (P : MvPolynomial Λ ℝ) :
    Iw bonds m2 (c • P) = c * Iw bonds m2 P := by
  unfold Iw
  simp only [smul_eval, mul_assoc]
  exact integral_const_mul c _

theorem Iw_sum (hm : 0 < m2) (P : Λ → MvPolynomial Λ ℝ) :
    Iw bonds m2 (∑ y, P y) = ∑ y, Iw bonds m2 (P y) := by
  unfold Iw
  simp only [map_sum, sum_mul]
  exact integral_finsetSum _ fun y _ => integ bonds hm (P y)

theorem Iw_X_mul (hm : 0 < m2) (x : Λ) (P : MvPolynomial Λ ℝ) :
    Iw bonds m2 (X x * P) =
      ∑ y, (precision bonds m2)⁻¹ x y * Iw bonds m2 (pderiv y P) := by
  rw [X_eq bonds hm x, sum_mul, Iw_sum bonds hm]
  refine sum_congr rfl fun y _ => ?_
  rw [smul_mul_assoc, Iw_smul]
  unfold Iw
  rw [ibp bonds hm]

theorem Iw_one_pos (hm : 0 < m2) : 0 < Iw bonds m2 1 := by
  unfold Iw
  simp only [map_one, one_mul]
  have := integ bonds hm 1
  simp only [map_one, one_mul] at this
  unfold w at this ⊢
  exact integral_exp_pos this

end Ana

end GAux

theorem gaussian_moment (bonds : Finset (Λ × Λ)) {m2 : ℝ} (hm : 0 < m2) (P : MvPolynomial Λ ℝ) :
    contMoment bonds m2 0 P = gauss (fun x y => (precision bonds m2)⁻¹ x y) P := by
  open GAux in
  have hw : ∀ φ, Real.exp (-contAction bonds m2 0 φ) = w bonds m2 φ := by
    intro φ; unfold w contAction; rw [eval_F]; congr 1; ring
  have hc : contMoment bonds m2 0 P = Iw bonds m2 P / Iw bonds m2 1 := by
    unfold contMoment Iw; simp only [hw, map_one, one_mul]
  rw [hc]
  have hpos := Iw_one_pos bonds hm
  refine uniq (fun x y => (precision bonds m2)⁻¹ x y) (fun R => Iw bonds m2 R / Iw bonds m2 1)
    (gauss (fun x y => (precision bonds m2)⁻¹ x y)) ?_ ?_ ?_ ?_ (gauss_add _) (gauss_smul _)
    (gauss_one _) ?_ P
  · intro P Q; rw [Iw_add bonds hm, add_div]
  · intro c P; rw [Iw_smul, mul_div_assoc]
  · exact div_self hpos.ne'
  · intro x s c; rw [Iw_X_mul bonds hm, Finset.sum_div]
    exact Finset.sum_congr rfl fun y _ => by ring
  · intro x s c
    exact gauss_X_mul _ (G_symm bonds hm) x (MvPolynomial.isHomogeneous_monomial c rfl)
end ValueLattice

-- ==== FreeField_m.lean ====

namespace FreeField
/-- symbol of `-Δ_a` -/
def lapSym (a : ℝ) (k : EuclideanSpace ℝ (Fin 4)) : ℝ := 4 / a ^ 2 * ∑ μ, Real.sin (a * k μ / 2) ^ 2
def BZ (a : ℝ) : Set (EuclideanSpace ℝ (Fin 4)) := {k | ∀ μ, k μ ∈ Set.Icc (-π / a) (π / a)}
def Ga (a m2 : ℝ) (j : Fin 4 → ℤ) : ℝ :=
  ((2 * π) ^ 4)⁻¹ * ∫ k in BZ a, Real.cos (a * ∑ μ, k μ * j μ) / (lapSym a k + m2)
def latLap (a : ℝ) (u : (Fin 4 → ℤ) → ℝ) (j : Fin 4 → ℤ) : ℝ :=
  (a ^ 2)⁻¹ * ∑ μ, (u (j + Pi.single μ 1) + u (j - Pi.single μ 1) - 2 * u j)

local notation "E4" => EuclideanSpace ℝ (Fin 4)

namespace Aux

lemma BZ_eq (a : ℝ) :
    BZ a = WithLp.ofLp ⁻¹' (Set.univ.pi fun _ : Fin 4 => Set.Icc (-π / a) (π / a)) := by
  ext k; simp only [BZ, Set.mem_ofPred_eq, Set.mem_preimage, Set.mem_univ_pi]

lemma measurableSet_BZ (a : ℝ) : MeasurableSet (BZ a) := by
  rw [BZ_eq]
  exact (MeasurableSet.univ_pi fun _ => measurableSet_Icc).preimage (WithLp.measurable_ofLp _ _)

lemma isCompact_BZ (a : ℝ) : IsCompact (BZ a) := by
  rw [BZ_eq]
  exact (PiLp.homeomorph 2 (fun _ : Fin 4 => ℝ)).isCompact_preimage.mpr
    (isCompact_univ_pi fun _ => isCompact_Icc)

lemma volume_BZ {a : ℝ} (ha : 0 < a) : volume.real (BZ a) = (2 * π / a) ^ 4 := by
  rw [Measure.real, BZ_eq, (PiLp.volume_preserving_ofLp (Fin 4)).measure_preimage
    (MeasurableSet.univ_pi fun _ => measurableSet_Icc).nullMeasurableSet, volume_pi_pi]
  simp only [Real.volume_Icc, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [ENNReal.toReal_pow, ENNReal.toReal_ofReal (by have := pi_pos; rw [neg_div, sub_neg_eq_add]; positivity)]
  congr 1; ring

lemma volume_BZ_lt_top (a : ℝ) : volume (BZ a) < ⊤ := (isCompact_BZ a).measure_lt_top

lemma continuous_coord (μ : Fin 4) : Continuous fun k : E4 => k μ :=
  (continuous_apply μ).comp (PiLp.continuous_ofLp 2 _)

lemma continuous_lapSym (a : ℝ) : Continuous (lapSym a) := by
  unfold lapSym
  have := continuous_coord
  fun_prop

lemma lapSym_nonneg (a : ℝ) (k : E4) : 0 ≤ lapSym a k := by
  unfold lapSym; positivity

lemma integrableOn_BZ {a : ℝ} {g : E4 → ℝ} (hg : Continuous g) : IntegrableOn g (BZ a) :=
  hg.continuousOn.integrableOn_compact (isCompact_BZ a)

lemma continuous_phase (a : ℝ) (j : Fin 4 → ℤ) : Continuous fun k : E4 => a * ∑ μ, k μ * j μ := by
  have := continuous_coord
  fun_prop

lemma continuous_integrand (a m2 : ℝ) (hm : 0 < m2) (j : Fin 4 → ℤ) :
    Continuous fun k : E4 => Real.cos (a * ∑ μ, k μ * j μ) / (lapSym a k + m2) := by
  refine (Real.continuous_cos.comp (continuous_phase a j)).div ((continuous_lapSym a).add continuous_const) ?_
  intro k; have := lapSym_nonneg a k; positivity


lemma int1 {a : ℝ} (ha : 0 < a) (m : ℤ) :
    ∫ t in Set.Icc (-π / a) (π / a), cexp (↑(a * t * m) * I) = if m = 0 then ((2 * π / a : ℝ) : ℂ) else 0 := by
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by
    have := pi_pos; rw [neg_div]; linarith [div_pos this ha])]
  split_ifs with hm
  · subst hm; simp; ring
  · have hc : ((a * m : ℝ) : ℂ) * I ≠ 0 := by
      refine mul_ne_zero ?_ I_ne_zero
      exact_mod_cast mul_ne_zero ha.ne' (by exact_mod_cast hm)
    have e : ∀ t : ℝ, cexp (↑(a * t * m) * I) = cexp ((((a * m : ℝ) : ℂ) * I) * t) := by
      intro t; congr 1; push_cast; ring
    simp_rw [e]
    rw [integral_exp_mul_complex hc]
    have h1 : (((a * m : ℝ) : ℂ) * I) * ((π / a : ℝ) : ℂ)
        = (((a * m : ℝ) : ℂ) * I) * ((-π / a : ℝ) : ℂ) + m * (2 * π * I) := by
      have : (a : ℂ) ≠ 0 := by exact_mod_cast ha.ne'
      push_cast; field_simp; ring
    rw [h1, Complex.exp_add, exp_int_mul_two_pi_mul_I]; simp

lemma intpi {a : ℝ} (ha : 0 < a) (j : Fin 4 → ℤ) :
    ∫ y in Set.univ.pi (fun _ : Fin 4 => Set.Icc (-π / a) (π / a)),
      cexp (↑(a * ∑ μ, y μ * j μ) * I) = if j = 0 then (((2 * π / a) ^ 4 : ℝ) : ℂ) else 0 := by
  have e : ∀ y : Fin 4 → ℝ, cexp (↑(a * ∑ μ, y μ * j μ) * I) = ∏ μ, cexp (↑(a * y μ * j μ) * I) := by
    intro y; rw [← Complex.exp_sum]; congr 1; push_cast; rw [Finset.mul_sum, Finset.sum_mul]
    congr 1; ext μ; ring
  simp_rw [e]
  rw [volume_pi, Measure.restrict_pi_pi]
  rw [integral_fintype_prod_eq_prod (f := fun μ t => cexp (↑(a * t * j μ) * I))]
  simp_rw [int1 ha]
  split_ifs with hj
  · subst hj; simp [div_pow]
  · obtain ⟨μ, hμ⟩ : ∃ μ, j μ ≠ 0 := by
      by_contra h; push Not at h; exact hj (funext h)
    exact Finset.prod_eq_zero (Finset.mem_univ μ) (by simp [hμ])

lemma intpi_cos {a : ℝ} (ha : 0 < a) (j : Fin 4 → ℤ) :
    ∫ y in Set.univ.pi (fun _ : Fin 4 => Set.Icc (-π / a) (π / a)),
      Real.cos (a * ∑ μ, y μ * j μ) = if j = 0 then (2 * π / a) ^ 4 else 0 := by
  have hint : IntegrableOn (fun y : Fin 4 → ℝ => cexp (↑(a * ∑ μ, y μ * j μ) * I))
      (Set.univ.pi (fun _ : Fin 4 => Set.Icc (-π / a) (π / a))) := by
    refine ContinuousOn.integrableOn_compact (isCompact_univ_pi fun _ => isCompact_Icc) ?_
    apply Continuous.continuousOn; fun_prop
  have := integral_re hint
  simp only [RCLike.re_to_complex, Complex.exp_ofReal_mul_I_re] at this
  rw [this, intpi ha]
  split_ifs <;> simp only [Complex.ofReal_re, Complex.zero_re]

lemma integral_cos_BZ {a : ℝ} (ha : 0 < a) (j : Fin 4 → ℤ) :
    ∫ k in BZ a, Real.cos (a * ∑ μ, k μ * j μ) = if j = 0 then (2 * π / a) ^ 4 else 0 := by
  rw [BZ_eq]
  have := (PiLp.volume_preserving_ofLp (Fin 4)).setIntegral_preimage_emb
    (MeasurableEquiv.toLp 2 (Fin 4 → ℝ)).symm.measurableEmbedding
    (fun y : Fin 4 → ℝ => Real.cos (a * ∑ μ, y μ * j μ))
    (Set.univ.pi fun _ : Fin 4 => Set.Icc (-π / a) (π / a))
  exact this.trans (intpi_cos ha j)

lemma sum_single (k : E4) (μ : Fin 4) :
    ∑ ν, k ν * (((Pi.single μ (1 : ℤ) : Fin 4 → ℤ) ν : ℤ) : ℝ) = k μ := by
  rw [Finset.sum_eq_single μ]
  · simp
  · intro ν _ hν; simp [hν]
  · simp

lemma phase_add (a : ℝ) (k : E4) (j : Fin 4 → ℤ) (μ : Fin 4) :
    a * ∑ ν, k ν * ((j + Pi.single μ 1 : Fin 4 → ℤ) ν : ℝ) = a * ∑ ν, k ν * j ν + a * k μ := by
  simp only [Pi.add_apply, Int.cast_add, mul_add, Finset.sum_add_distrib, sum_single]

lemma phase_sub (a : ℝ) (k : E4) (j : Fin 4 → ℤ) (μ : Fin 4) :
    a * ∑ ν, k ν * ((j - Pi.single μ 1 : Fin 4 → ℤ) ν : ℝ) = a * ∑ ν, k ν * j ν - a * k μ := by
  simp only [Pi.sub_apply, Int.cast_sub, mul_sub, Finset.sum_sub_distrib, sum_single]

lemma cos_second_diff (θ y : ℝ) :
    Real.cos (θ + 2 * y) + Real.cos (θ - 2 * y) - 2 * Real.cos θ = -(4 * Real.sin y ^ 2 * Real.cos θ) := by
  rw [Real.cos_add, Real.cos_sub, Real.cos_two_mul]
  have h : Real.cos y ^ 2 = 1 - Real.sin y ^ 2 := by linarith [Real.sin_sq_add_cos_sq y]
  rw [h]; ring

end Aux

open Aux in
theorem Ga_bounded {a m2 : ℝ} (ha : 0 < a) (hm : 0 < m2) : ∃ M, ∀ j, |Ga a m2 j| ≤ M := by
  refine ⟨((2 * π) ^ 4)⁻¹ * ((1 / m2) * volume.real (BZ a)), fun j => ?_⟩
  unfold Ga
  rw [abs_mul, abs_of_pos (by positivity)]
  gcongr
  rw [← Real.norm_eq_abs]
  refine norm_setIntegral_le_of_norm_le_const (volume_BZ_lt_top a) fun k _ => ?_
  have := lapSym_nonneg a k
  rw [Real.norm_eq_abs, abs_div, abs_of_pos (by positivity : 0 < lapSym a k + m2)]
  rw [div_le_div_iff₀ (by positivity) hm]
  calc |Real.cos _| * m2 ≤ 1 * m2 := by gcongr; exact Real.abs_cos_le_one _
    _ ≤ 1 * (lapSym a k + m2) := by gcongr; linarith

theorem bounded_unique {a m2 : ℝ} (ha : 0 < a) (hm : 0 < m2) (u : (Fin 4 → ℤ) → ℝ)
    (hb : ∃ M, ∀ j, |u j| ≤ M) (hu : ∀ j, -latLap a u j + m2 * u j = 0) : u = 0 := by
  obtain ⟨M, hM⟩ := hb
  -- key: for any bounded solution v, v ≤ 0 everywhere
  have key : ∀ v : (Fin 4 → ℤ) → ℝ, (∀ j, |v j| ≤ M) → (∀ j, -latLap a v j + m2 * v j = 0) →
      ∀ j, v j ≤ 0 := by
    intro v hv hvs
    have hbdd : BddAbove (Set.range v) := ⟨M, by rintro _ ⟨j, rfl⟩; exact (le_abs_self _).trans (hv j)⟩
    set S := ⨆ j, v j
    have hle : ∀ j, v j ≤ S := fun j => le_ciSup hbdd j
    suffices hS : S ≤ 0 from fun j => (hle j).trans hS
    by_contra hS
    push Not at hS
    -- choose eps
    set c : ℝ := 8 / a ^ 2 + m2
    have hc : 0 < c := by positivity
    set ε := m2 * S / (2 * c)
    have hε : 0 < ε := by positivity
    obtain ⟨j, hj⟩ := exists_lt_of_lt_ciSup (show S - ε < S by linarith)
    have h := hvs j
    unfold latLap at h
    have hsum : ∑ μ : Fin 4, (v (j + Pi.single μ 1) + v (j - Pi.single μ 1) - 2 * v j)
        ≤ ∑ μ : Fin 4, (2 * S - 2 * v j) := by
      gcongr with μ
      linarith [hle (j + Pi.single μ 1), hle (j - Pi.single μ 1)]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hsum
    have ha2 : 0 < (a ^ 2)⁻¹ := by positivity
    have h2 : m2 * v j ≤ (a ^ 2)⁻¹ * (4 * (2 * S - 2 * v j)) := by
      have := mul_le_mul_of_nonneg_left hsum ha2.le
      push_cast at this
      linarith
    -- (8/a^2 + m2) v j ≤ 8/a^2 S
    have h3 : c * v j ≤ 8 / a ^ 2 * S := by
      have : (a ^ 2)⁻¹ * (4 * (2 * S - 2 * v j)) = 8 / a ^ 2 * S - 8 / a ^ 2 * v j := by
        field_simp; ring
      simp only [c]; nlinarith
    have h4 : c * (S - ε) < 8 / a ^ 2 * S := by
      calc c * (S - ε) < c * v j := by gcongr
        _ ≤ _ := h3
    have h5 : c * ε = m2 * S / 2 := by
      simp only [ε]; field_simp
    have : c * (S - ε) = 8 / a ^ 2 * S + m2 * S / 2 := by
      rw [mul_sub, h5]; simp only [c]; ring
    nlinarith
  funext j
  have h1 := key u hM hu j
  have h2 := key (-u) (fun j => by simpa using hM j) (fun j => by
    have := hu j; unfold latLap at this ⊢; simp only [Pi.neg_apply]
    have e : ∀ μ : Fin 4, (-u (j + Pi.single μ 1) + -u (j - Pi.single μ 1) - 2 * -u j)
      = -(u (j + Pi.single μ 1) + u (j - Pi.single μ 1) - 2 * u j) := fun μ => by ring
    simp only [e, Finset.sum_neg_distrib]; linarith) j
  simp only [Pi.neg_apply, Pi.zero_apply] at h2 ⊢
  linarith

open Aux in
theorem Ga_inverse {a m2 : ℝ} (ha : 0 < a) (hm : 0 < m2) (j : Fin 4 → ℤ) :
    -latLap a (Ga a m2) j + m2 * Ga a m2 j = if j = 0 then (a ^ 4)⁻¹ else 0 := by
  set φ : (Fin 4 → ℤ) → E4 → ℝ := fun i k => Real.cos (a * ∑ μ, k μ * i μ) / (lapSym a k + m2)
    with hφ
  have hI : ∀ i, IntegrableOn (φ i) (BZ a) := fun i => integrableOn_BZ (continuous_integrand a m2 hm i)
  have hG : ∀ i, Ga a m2 i = ((2 * π) ^ 4)⁻¹ * ∫ k in BZ a, φ i k := fun i => rfl
  set ψ : E4 → ℝ := fun k => -((a ^ 2)⁻¹ * ∑ μ, (φ (j + Pi.single μ 1) k + φ (j - Pi.single μ 1) k
      - 2 * φ j k)) + m2 * φ j k with hψ
  have hψint : ∫ k in BZ a, ψ k = -((a ^ 2)⁻¹ * ∑ μ, ((∫ k in BZ a, φ (j + Pi.single μ 1) k) +
      (∫ k in BZ a, φ (j - Pi.single μ 1) k) - 2 * ∫ k in BZ a, φ j k)) + m2 * ∫ k in BZ a, φ j k := by
    simp only [hψ]
    rw [integral_add, integral_neg, integral_const_mul, integral_const_mul, integral_finsetSum]
    · congr 3
      refine Finset.sum_congr rfl fun μ _ => ?_
      rw [integral_sub, integral_add, integral_const_mul]
      · exact hI _
      · exact hI _
      · exact (hI _).add (hI _)
      · exact (hI _).const_mul _
    · intro μ _
      exact ((hI _).add (hI _)).sub ((hI _).const_mul _)
    · exact (integrable_finsetSum _ fun μ _ =>
        ((hI _).add (hI _)).sub ((hI _).const_mul _)).const_mul _ |>.neg
    · exact (hI _).const_mul _
  have hψeq : ∀ k, ψ k = Real.cos (a * ∑ μ, k μ * j μ) := by
    intro k
    simp only [hψ, hφ, phase_add, phase_sub]
    have hL := lapSym_nonneg a k
    have hpos : 0 < lapSym a k + m2 := by linarith
    have e : ∀ μ : Fin 4, Real.cos (a * ∑ ν, k ν * j ν + a * k μ) / (lapSym a k + m2) +
        Real.cos (a * ∑ ν, k ν * j ν - a * k μ) / (lapSym a k + m2) -
        2 * (Real.cos (a * ∑ ν, k ν * j ν) / (lapSym a k + m2)) =
        -(4 * Real.sin (a * k μ / 2) ^ 2) * Real.cos (a * ∑ ν, k ν * j ν) / (lapSym a k + m2) := by
      intro μ
      have := cos_second_diff (a * ∑ ν, k ν * j ν) (a * k μ / 2)
      rw [show 2 * (a * k μ / 2) = a * k μ by ring] at this
      rw [← add_div, mul_div_assoc', ← sub_div, this]; ring
    simp only [e]
    have hsum : ∑ μ : Fin 4, -(4 * Real.sin (a * k μ / 2) ^ 2) * Real.cos (a * ∑ ν, k ν * j ν) /
        (lapSym a k + m2) = -(a ^ 2 * lapSym a k) * Real.cos (a * ∑ ν, k ν * j ν) / (lapSym a k + m2) := by
      rw [← Finset.sum_div, ← Finset.sum_mul]
      congr 2
      unfold lapSym
      rw [Finset.sum_neg_distrib, ← Finset.mul_sum]
      field_simp; try ring
    rw [hsum]
    field_simp
  have hlhs : -latLap a (Ga a m2) j + m2 * Ga a m2 j = ((2 * π) ^ 4)⁻¹ * ∫ k in BZ a, ψ k := by
    rw [hψint]; unfold latLap; simp only [hG, Fin.sum_univ_four]; ring
  rw [hlhs, integral_congr_ae (Filter.Eventually.of_forall (fun k => hψeq k)), integral_cos_BZ ha]
  split_ifs
  · have := pi_pos; field_simp
  · simp

namespace Aux

lemma zpt_apply (j : Fin 4 → ℤ) (μ : Fin 4) : zpt j μ = j μ := rfl

lemma smul_zpt_apply (a : ℝ) (j : Fin 4 → ℤ) (μ : Fin 4) : (a • zpt j) μ = a * j μ := rfl

lemma zpt_add (i j : Fin 4 → ℤ) : zpt (i + j) = zpt i + zpt j := by
  ext μ; simp [zpt]

lemma zpt_sub (i j : Fin 4 → ℤ) : zpt (i - j) = zpt i - zpt j := by
  ext μ; simp [zpt]

lemma zpt_single (μ : Fin 4) : zpt (Pi.single μ 1) = EuclideanSpace.single μ (1 : ℝ) := by
  ext ν; by_cases h : ν = μ
  · subst h; simp [zpt]
  · simp [zpt, h, Pi.single_apply]

lemma norm_single_one (μ : Fin 4) : ‖EuclideanSpace.single μ (1 : ℝ)‖ = 1 := by
  rw [EuclideanSpace.single, PiLp.norm_single]; simp

lemma abs_coord_le (x : E4) (μ : Fin 4) : |x μ| ≤ ‖x‖ := by
  have := PiLp.norm_apply_le x μ
  simpa using this

lemma norm_le_of_coord {x : E4} {c : ℝ} (hc : 0 ≤ c) (h : ∀ μ, |x μ| ≤ c) : ‖x‖ ≤ 2 * c := by
  have h1 : ‖x‖ ^ 2 ≤ (2 * c) ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    calc ∑ μ, x μ ^ 2 ≤ ∑ _μ : Fin 4, c ^ 2 :=
          Finset.sum_le_sum fun μ _ => sq_le_sq' (abs_le.mp (h μ)).1 (abs_le.mp (h μ)).2
      _ = (2 * c) ^ 2 := by simp; ring
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) (by norm_num)).mp h1

/-- the integer box `[-N, N]⁴`. -/
def lbox (N : ℕ) : Finset (Fin 4 → ℤ) := Fintype.piFinset fun _ => Finset.Icc (-(N : ℤ)) N

def Nof (a R : ℝ) : ℕ := ⌈R / a⌉₊

lemma mem_lbox {N : ℕ} {j : Fin 4 → ℤ} : j ∈ lbox N ↔ ∀ μ, |j μ| ≤ N := by
  simp [lbox, abs_le]

lemma mem_lbox_of_norm_le {a R : ℝ} (ha : 0 < a) {j : Fin 4 → ℤ} (h : ‖a • zpt j‖ ≤ R) :
    j ∈ lbox (Nof a R) := by
  rw [mem_lbox]; intro μ
  have h1 := (abs_coord_le (a • zpt j) μ).trans h
  rw [smul_zpt_apply, abs_mul, abs_of_pos ha] at h1
  have h2 : (|j μ| : ℝ) ≤ R / a := by rw [le_div_iff₀ ha]; push_cast; linarith
  have h3 : R / a ≤ (Nof a R : ℝ) := Nat.le_ceil _
  have : (|j μ| : ℝ) ≤ ((Nof a R : ℤ) : ℝ) := by push_cast; linarith
  exact_mod_cast this

lemma eq_zero_of_not_mem_lbox {a R : ℝ} (ha : 0 < a) {g : E4 → ℂ} (hg : ∀ x, R < ‖x‖ → g x = 0)
    {j : Fin 4 → ℤ} (hj : j ∉ lbox (Nof a R)) : g (a • zpt j) = 0 :=
  hg _ (lt_of_not_ge fun h => hj (mem_lbox_of_norm_le ha h))

lemma card_lbox (N : ℕ) : ((lbox N).card : ℝ) = (2 * N + 1) ^ 4 := by
  simp only [lbox, Fintype.card_piFinset, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
    Int.card_Icc]
  push_cast
  rw [show ((N : ℤ) + 1 - -(N : ℤ)).toNat = 2 * N + 1 by omega]
  push_cast; ring

lemma a4_card_le {a R : ℝ} (ha : 0 < a) (ha1 : a ≤ 1) (hR : 0 ≤ R) :
    a ^ 4 * ((lbox (Nof a R)).card : ℝ) ≤ (2 * R + 3) ^ 4 := by
  rw [card_lbox, ← mul_pow]
  have h1 : (Nof a R : ℝ) < R / a + 1 := Nat.ceil_lt_add_one (by positivity)
  have h2 : a * (2 * (Nof a R : ℝ) + 1) ≤ 2 * R + 3 := by
    have : a * (Nof a R : ℝ) ≤ R + a := by
      have := mul_le_mul_of_nonneg_left h1.le ha.le
      rw [mul_add, mul_div_cancel₀ _ ha.ne', mul_one] at this; exact this
    nlinarith
  exact pow_le_pow_left₀ (by positivity) h2 4

/-! ### Riemann sums -/

def fl (a : ℝ) (x : E4) : Fin 4 → ℤ := fun μ => ⌊x μ / a⌋

lemma measurable_fl (a : ℝ) : Measurable (fl a) := by
  apply Measurable.of_eval
  intro μ
  have : Measurable fun c : E4 => c μ := (measurable_pi_apply μ).comp (WithLp.measurable_ofLp 2 _)
  exact Int.measurable_floor.comp (this.div_const a)

lemma measurable_zpt : Measurable (zpt : (Fin 4 → ℤ) → E4) := measurable_of_countable _

lemma coord_fl {a : ℝ} (ha : 0 < a) (x : E4) (μ : Fin 4) :
    |x μ - (a • zpt (fl a x)) μ| ≤ a := by
  rw [smul_zpt_apply]
  simp only [fl]
  have h1 := Int.floor_le (x μ / a)
  have h2 := Int.lt_floor_add_one (x μ / a)
  rw [le_div_iff₀ ha] at h1
  rw [div_lt_iff₀ ha] at h2
  rw [abs_le]; constructor <;> nlinarith

lemma norm_sub_fl {a : ℝ} (ha : 0 < a) (x : E4) : ‖x - a • zpt (fl a x)‖ ≤ 2 * a :=
  norm_le_of_coord ha.le fun μ => by simpa using coord_fl ha x μ

lemma fl_eq_iff {a : ℝ} (ha : 0 < a) (x : E4) (j : Fin 4 → ℤ) :
    fl a x = j ↔ x ∈ WithLp.ofLp ⁻¹' (Set.univ.pi fun μ => Set.Ico (a * j μ) (a * (j μ + 1))) := by
  simp only [fl, Set.mem_preimage, Set.mem_univ_pi, Set.mem_Ico, funext_iff, Int.floor_eq_iff,
    le_div_iff₀ ha, div_lt_iff₀ ha]
  apply forall_congr'; intro μ
  constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith

lemma volume_cell' {a : ℝ} (ha : 0 < a) (j : Fin 4 → ℤ) :
    volume (fl a ⁻¹' {j}) = ENNReal.ofReal a ^ 4 := by
  have : fl a ⁻¹' {j} = WithLp.ofLp ⁻¹' (Set.univ.pi fun μ => Set.Ico (a * j μ) (a * (j μ + 1))) := by
    ext x; exact fl_eq_iff ha x j
  rw [this, (PiLp.volume_preserving_ofLp (Fin 4)).measure_preimage
    (MeasurableSet.univ_pi fun _ => measurableSet_Ico).nullMeasurableSet, volume_pi_pi]
  simp only [Real.volume_Ico, show ∀ x : Fin 4, a * ((j x : ℝ) + 1) - a * j x = a by intro; ring,
    Finset.prod_const, Finset.card_univ, Fintype.card_fin]

lemma volume_cell {a : ℝ} (ha : 0 < a) (j : Fin 4 → ℤ) :
    volume.real (fl a ⁻¹' {j}) = a ^ 4 := by
  rw [Measure.real, volume_cell' ha, ENNReal.toReal_pow, ENNReal.toReal_ofReal ha.le]

lemma integral_step {a R : ℝ} (ha : 0 < a) {g : E4 → ℂ} (hg : ∀ x, R < ‖x‖ → g x = 0) :
    ∫ x, g (a • zpt (fl a x)) = (a ^ 4 : ℝ) • ∑ j ∈ lbox (Nof a R), g (a • zpt j) := by
  have hfun : (fun x => g (a • zpt (fl a x))) =
      fun x => ∑ j ∈ lbox (Nof a R), (fl a ⁻¹' {j}).indicator (fun _ => g (a • zpt j)) x := by
    funext x
    simp only [Set.indicator, Set.mem_preimage, Set.mem_singleton_iff]
    rw [Finset.sum_ite_eq]
    split_ifs with h
    · rfl
    · exact eq_zero_of_not_mem_lbox ha hg h
  have hms : ∀ j, MeasurableSet (fl a ⁻¹' {j}) := fun j => measurable_fl a (measurableSet_singleton j)
  rw [hfun, integral_finsetSum]
  · rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [integral_indicator_const _ (hms j), volume_cell ha]
  · intro j _
    refine (integrable_indicator_iff (hms j)).mpr ?_
    exact integrableOn_const (by rw [volume_cell' ha]; simp)

lemma tendsto_fl (x : E4) : Tendsto (fun a : ℝ => a • zpt (fl a x)) (𝓝[>] 0) (𝓝 x) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have h2 : Tendsto (fun a : ℝ => 2 * a) (𝓝[>] 0) (𝓝 0) := by
    apply tendsto_nhdsWithin_of_tendsto_nhds
    simpa using (continuous_const.mul continuous_id).tendsto (0 : ℝ) (f := fun a : ℝ => 2 * a)
  refine squeeze_zero' (Eventually.of_forall fun a => norm_nonneg _) ?_ h2
  filter_upwards [self_mem_nhdsWithin] with a ha
  rw [norm_sub_rev]; exact norm_sub_fl ha x

lemma riemann {g : E4 → ℂ} (hg : Continuous g) {R : ℝ} (hgR : ∀ x, R < ‖x‖ → g x = 0) :
    Tendsto (fun a : ℝ => (a ^ 4 : ℝ) • ∑ j ∈ lbox (Nof a R), g (a • zpt j)) (𝓝[>] 0)
      (𝓝 (∫ x, g x)) := by
  have hcs : HasCompactSupport g := HasCompactSupport.intro (isCompact_closedBall 0 R)
    (fun x hx => hgR x (by simpa using hx))
  obtain ⟨C, hC⟩ := hg.bounded_above_of_compact_support hcs
  have key : Tendsto (fun a : ℝ => ∫ x, g (a • zpt (fl a x))) (𝓝[>] 0) (𝓝 (∫ x, g x)) := by
    refine tendsto_integral_filter_of_dominated_convergence
      ((Metric.closedBall (0 : E4) (R + 2)).indicator fun _ => C) ?_ ?_ ?_ ?_
    · exact Eventually.of_forall fun a => (hg.measurable.comp
        ((measurable_const_smul a).comp (measurable_zpt.comp (measurable_fl a)))).aestronglyMeasurable
    · filter_upwards [Ioc_mem_nhdsGT (zero_lt_one' ℝ)] with a ha
      refine Eventually.of_forall fun x => ?_
      by_cases hx : x ∈ Metric.closedBall (0 : E4) (R + 2)
      · rw [Set.indicator_of_mem hx]; exact hC _
      · rw [Set.indicator_of_notMem hx]
        have : g (a • zpt (fl a x)) = 0 := hgR _ (by
           have h1 := norm_sub_fl ha.1 x
           have h2 : R + 2 < ‖x‖ := by simpa using hx
           have := norm_sub_norm_le x (a • zpt (fl a x))
           linarith [ha.2])
        simp [this]
    · refine (integrable_indicator_iff measurableSet_closedBall).mpr ?_
      exact integrableOn_const measure_closedBall_lt_top.ne
    · exact Eventually.of_forall fun x => (hg.tendsto x).comp (tendsto_fl x)
  refine key.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with a ha
  exact integral_step ha hgR

/-! ### second differences -/

lemma one_d {φ φ1 φ2 : ℝ → ℝ} {M : ℝ} (h1 : ∀ t, HasDerivAt φ (φ1 t) t)
    (h2 : ∀ t, HasDerivAt φ1 (φ2 t) t) (hM : ∀ t, |φ2 t| ≤ M) :
    |φ 1 + φ (-1) - 2 * φ 0| ≤ 2 * M := by
  have c1 : Continuous φ := continuous_iff_continuousAt.mpr fun t => (h1 t).continuousAt
  have c2 : Continuous φ1 := continuous_iff_continuousAt.mpr fun t => (h2 t).continuousAt
  obtain ⟨s1, hs1, e1⟩ := exists_hasDerivAt_eq_slope φ φ1 (zero_lt_one' ℝ) c1.continuousOn
    (fun t _ => h1 t)
  obtain ⟨s2, hs2, e2⟩ := exists_hasDerivAt_eq_slope φ φ1 (show (-1 : ℝ) < 0 by norm_num)
    c1.continuousOn (fun t _ => h1 t)
  have hs : s2 < s1 := hs2.2.trans hs1.1
  obtain ⟨s3, -, e3⟩ := exists_hasDerivAt_eq_slope φ1 φ2 hs c2.continuousOn (fun t _ => h2 t)
  have hne : s1 - s2 ≠ 0 := sub_ne_zero.mpr hs.ne'
  have hΔ : φ 1 + φ (-1) - 2 * φ 0 = φ2 s3 * (s1 - s2) := by
    rw [e3, div_mul_cancel₀ _ hne, e1, e2]; ring
  rw [hΔ, abs_mul]
  have : |s1 - s2| ≤ 2 := by
    rw [abs_le]; constructor <;> linarith [hs1.1, hs1.2, hs2.1, hs2.2]
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM 0)
  calc |φ2 s3| * |s1 - s2| ≤ M * 2 := by gcongr; exact hM _
    _ = 2 * M := by ring

lemma fderiv_zero_far {g : E4 → ℝ} {R : ℝ} (hg : ∀ x, R < ‖x‖ → g x = 0) (v : E4) :
    ∀ x, R < ‖x‖ → fderiv ℝ g x v = 0 := by
  intro x hx
  have : g =ᶠ[𝓝 x] fun _ => 0 := by
    filter_upwards [(isOpen_lt continuous_const continuous_norm).mem_nhds hx] with y hy
    exact hg y hy
  rw [this.fderiv_eq]; simp

lemma second_diff_bound {f : E4 → ℝ} (hf : ContDiff ℝ 2 f) {R : ℝ}
    (hfR : ∀ x, R < ‖x‖ → f x = 0) :
    ∃ C, 0 ≤ C ∧ ∀ (x : E4) (μ : Fin 4) (a : ℝ),
      |f (x + a • EuclideanSpace.single μ 1) + f (x - a • EuclideanSpace.single μ 1) - 2 * f x|
        ≤ C * a ^ 2 := by
  have hf1 : ContDiff ℝ 1 (fderiv ℝ f) := hf.fderiv_right (by norm_num)
  have hd1 : Differentiable ℝ f := hf.differentiable (by norm_num)
  set g1 : Fin 4 → E4 → ℝ := fun μ y => fderiv ℝ f y (EuclideanSpace.single μ 1)
  have hg1 : ∀ μ, ContDiff ℝ 1 (g1 μ) := fun μ => hf1.clm_apply contDiff_const
  set g2 : Fin 4 → E4 → ℝ := fun μ y => fderiv ℝ (g1 μ) y (EuclideanSpace.single μ 1)
  have hg2c : ∀ μ, Continuous (g2 μ) := fun μ =>
    ((hg1 μ).continuous_fderiv one_ne_zero).clm_apply continuous_const
  have hg1R : ∀ μ x, R < ‖x‖ → g1 μ x = 0 := fun μ => fderiv_zero_far hfR _
  have hg2R : ∀ μ x, R < ‖x‖ → g2 μ x = 0 := fun μ => fderiv_zero_far (hg1R μ) _
  have hb : ∀ μ, ∃ C, ∀ x, ‖g2 μ x‖ ≤ C := fun μ =>
    (hg2c μ).bounded_above_of_compact_support (HasCompactSupport.intro (isCompact_closedBall 0 R)
      (fun x hx => hg2R μ x (by simpa using hx)))
  choose C hC using hb
  set C' := ∑ μ, |C μ|
  have hC' : ∀ μ x, |g2 μ x| ≤ C' := fun μ x =>
    ((hC μ x).trans (le_abs_self _)).trans
      (Finset.single_le_sum (f := fun μ => |C μ|) (fun _ _ => abs_nonneg _) (Finset.mem_univ μ))
  have hC'0 : 0 ≤ C' := Finset.sum_nonneg fun _ _ => abs_nonneg _
  refine ⟨2 * C', by positivity, fun x μ a => ?_⟩
  set e : E4 := EuclideanSpace.single μ 1
  have h1 : ∀ t : ℝ, HasDerivAt (fun t : ℝ => f (x + t • (a • e))) (a * g1 μ (x + t • (a • e))) t := by
    intro t
    have hl : HasDerivAt (fun t : ℝ => x + t • (a • e)) (a • e) t := by
      simpa using ((hasDerivAt_id t).smul_const (a • e)).const_add x
    have := (hd1 (x + t • (a • e))).hasFDerivAt.comp_hasDerivAt t hl
    convert this using 1
    all_goals first | rfl | simp [g1, e, map_smul]
  have h2 : ∀ t : ℝ, HasDerivAt (fun t : ℝ => a * g1 μ (x + t • (a • e)))
      (a * (a * g2 μ (x + t • (a • e)))) t := by
    intro t
    have hl : HasDerivAt (fun t : ℝ => x + t • (a • e)) (a • e) t := by
      simpa using ((hasDerivAt_id t).smul_const (a • e)).const_add x
    have := ((hg1 μ).differentiable one_ne_zero (x + t • (a • e))).hasFDerivAt.comp_hasDerivAt t hl
    have := this.const_mul a
    simpa [g2, e, map_smul] using this
  have := one_d h1 h2 (M := a ^ 2 * C') (fun t => by
    rw [abs_mul, abs_mul, ← mul_assoc, ← sq, sq_abs]
    gcongr; exact hC' μ _)
  simp only [one_smul, zero_smul, add_zero, neg_smul] at this
  rw [← sub_eq_add_neg] at this
  calc _ ≤ 2 * (a ^ 2 * C') := this
    _ = 2 * C' * a ^ 2 := by ring

/-! ### lattice Fourier transform -/

lemma zero_off_lbox {β : Type*} [Zero β] {a R : ℝ} (ha : 0 < a) {g : E4 → β}
    (hg : ∀ x, R < ‖x‖ → g x = 0) {j : Fin 4 → ℤ} (hj : j ∉ lbox (Nof a R)) : g (a • zpt j) = 0 :=
  hg _ (lt_of_not_ge fun h => hj (mem_lbox_of_norm_le ha h))

lemma mem_lbox_succ_of_add {N : ℕ} {j : Fin 4 → ℤ} (μ : Fin 4) (h : j + Pi.single μ 1 ∈ lbox N) :
    j ∈ lbox (N + 1) := by
  rw [mem_lbox] at *; intro ν; have := h ν
  simp only [Pi.add_apply] at this
  rw [abs_le] at *
  by_cases hν : ν = μ
  · subst hν; simp at this; push_cast; omega
  · simp [hν] at this; push_cast; omega

lemma mem_lbox_succ_of_sub {N : ℕ} {j : Fin 4 → ℤ} (μ : Fin 4) (h : j - Pi.single μ 1 ∈ lbox N) :
    j ∈ lbox (N + 1) := by
  rw [mem_lbox] at *; intro ν; have := h ν
  simp only [Pi.sub_apply] at this
  rw [abs_le] at *
  by_cases hν : ν = μ
  · subst hν; simp at this; push_cast; omega
  · simp [hν] at this; push_cast; omega

def ph (a : ℝ) (k : E4) (j : Fin 4 → ℤ) : ℝ := a * ∑ μ, k μ * j μ

def EE (a : ℝ) (k : E4) (j : Fin 4 → ℤ) : ℂ := cexp (↑(-ph a k j) * I)

/-- `F_a(k) = a⁴ ∑_j f(a j) e^{-i a k·j}` (finite sum). -/
def FF (f : E4 → ℝ) (R a : ℝ) (k : E4) : ℂ :=
  (a ^ 4 : ℝ) • ∑ j ∈ lbox (Nof a R), (f (a • zpt j) : ℂ) * EE a k j

lemma norm_EE (a : ℝ) (k : E4) (j : Fin 4 → ℤ) : ‖EE a k j‖ = 1 := Complex.norm_exp_ofReal_mul_I _

lemma EE_add (a : ℝ) (k : E4) (j : Fin 4 → ℤ) (μ : Fin 4) :
    EE a k (j + Pi.single μ 1) = EE a k j * cexp (↑(-(a * k μ)) * I) := by
  simp only [EE, ph, phase_add, ← Complex.exp_add]; congr 1; push_cast; ring

lemma EE_sub (a : ℝ) (k : E4) (j : Fin 4 → ℤ) (μ : Fin 4) :
    EE a k (j - Pi.single μ 1) = EE a k j * cexp (↑(a * k μ) * I) := by
  simp only [EE, ph, phase_sub, ← Complex.exp_add]; congr 1; push_cast; ring

lemma FF_norm_le {f : E4 → ℝ} {R M0 : ℝ} (hR : 0 ≤ R) (hM : ∀ x, |f x| ≤ M0) {a : ℝ}
    (ha : 0 < a) (ha1 : a ≤ 1) (k : E4) : ‖FF f R a k‖ ≤ (2 * R + 3) ^ 4 * M0 := by
  have hM0 : 0 ≤ M0 := (abs_nonneg _).trans (hM 0)
  unfold FF
  rw [norm_smul, Real.norm_of_nonneg (by positivity)]
  calc a ^ 4 * ‖∑ j ∈ lbox (Nof a R), (f (a • zpt j) : ℂ) * EE a k j‖
      ≤ a ^ 4 * ∑ _j ∈ lbox (Nof a R), M0 := by
        gcongr
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ?_)
        rw [norm_mul, norm_EE, mul_one, Complex.norm_real, Real.norm_eq_abs]; exact hM _
    _ = (a ^ 4 * (lbox (Nof a R)).card) * M0 := by rw [Finset.sum_const, nsmul_eq_mul]; ring
    _ ≤ (2 * R + 3) ^ 4 * M0 := by gcongr; exact a4_card_le ha ha1 hR

lemma sum_eq_tsum {f : E4 → ℝ} {R a : ℝ} (ha : 0 < a) (hfR : ∀ x, R < ‖x‖ → f x = 0) (k : E4) :
    ∑ j ∈ lbox (Nof a R), (f (a • zpt j) : ℂ) * EE a k j = ∑' j, (f (a • zpt j) : ℂ) * EE a k j := by
  refine (tsum_eq_sum fun j hj => ?_).symm
  rw [zero_off_lbox ha hfR hj]; simp

lemma sbp {f : E4 → ℝ} {R a : ℝ} (ha : 0 < a) (hfR : ∀ x, R < ‖x‖ → f x = 0) (μ : Fin 4) (k : E4) :
    ∑' j, ((f (a • zpt j + a • EuclideanSpace.single μ 1) + f (a • zpt j - a • EuclideanSpace.single μ 1)
      - 2 * f (a • zpt j) : ℝ) : ℂ) * EE a k j
    = -(((2 - 2 * Real.cos (a * k μ)) : ℝ) : ℂ) * ∑' j, (f (a • zpt j) : ℂ) * EE a k j := by
  set T := ∑' j, (f (a • zpt j) : ℂ) * EE a k j
  have hpa : ∀ j, a • zpt j + a • EuclideanSpace.single μ (1 : ℝ) = a • zpt (j + Pi.single μ 1) := by
    intro j; rw [zpt_add, zpt_single, smul_add]
  have hpb : ∀ j, a • zpt j - a • EuclideanSpace.single μ (1 : ℝ) = a • zpt (j - Pi.single μ 1) := by
    intro j; rw [zpt_sub, zpt_single, smul_sub]
  have S0 : Summable fun j => (f (a • zpt j) : ℂ) * EE a k j :=
    summable_of_ne_finset_zero (s := lbox (Nof a R)) fun j hj => by
      rw [zero_off_lbox ha hfR hj]; simp
  have SA : Summable fun j => (f (a • zpt j + a • EuclideanSpace.single μ 1) : ℂ) * EE a k j :=
    summable_of_ne_finset_zero (s := lbox (Nof a R + 1)) fun j hj => by
      rw [hpa, zero_off_lbox ha hfR (fun h => hj (mem_lbox_succ_of_add μ h))]; simp
  have SB : Summable fun j => (f (a • zpt j - a • EuclideanSpace.single μ 1) : ℂ) * EE a k j :=
    summable_of_ne_finset_zero (s := lbox (Nof a R + 1)) fun j hj => by
      rw [hpb, zero_off_lbox ha hfR (fun h => hj (mem_lbox_succ_of_sub μ h))]; simp
  have hA : ∑' j, (f (a • zpt j + a • EuclideanSpace.single μ 1) : ℂ) * EE a k j
      = cexp (↑(a * k μ) * I) * T := by
    rw [← (Equiv.subRight (Pi.single μ (1 : ℤ))).tsum_eq]
    simp only [Equiv.subRight_apply, hpa, sub_add_cancel, EE_sub]
    rw [← tsum_mul_left]; congr 1; funext j; ring
  have hB : ∑' j, (f (a • zpt j - a • EuclideanSpace.single μ 1) : ℂ) * EE a k j
      = cexp (↑(-(a * k μ)) * I) * T := by
    rw [← (Equiv.addRight (Pi.single μ (1 : ℤ))).tsum_eq]
    simp only [Equiv.coe_addRight, hpb, add_sub_cancel_right, EE_add]
    rw [← tsum_mul_left]; congr 1; funext j; ring
  have hsplit : (fun j => ((f (a • zpt j + a • EuclideanSpace.single μ 1) +
      f (a • zpt j - a • EuclideanSpace.single μ 1) - 2 * f (a • zpt j) : ℝ) : ℂ) * EE a k j) =
      fun j => (f (a • zpt j + a • EuclideanSpace.single μ 1) : ℂ) * EE a k j +
        (f (a • zpt j - a • EuclideanSpace.single μ 1) : ℂ) * EE a k j -
        2 * ((f (a • zpt j) : ℂ) * EE a k j) := by
    funext j; push_cast; ring
  rw [hsplit, (SA.add SB).tsum_sub (S0.mul_left 2), SA.tsum_add SB, hA, hB, tsum_mul_left]
  have h2 := Complex.two_cos (↑(a * k μ))
  push_cast at h2 ⊢
  simp only [neg_mul] at h2 ⊢
  linear_combination (-T) * h2

lemma lapSym_eq_cos (a : ℝ) (k : E4) :
    lapSym a k = (a ^ 2)⁻¹ * ∑ μ, (2 - 2 * Real.cos (a * k μ)) := by
  unfold lapSym
  rw [div_eq_mul_inv, mul_comm 4, mul_assoc, Finset.mul_sum]
  congr 1; refine Finset.sum_congr rfl fun μ _ => ?_
  have h := Real.cos_two_mul (a * k μ / 2)
  rw [show 2 * (a * k μ / 2) = a * k μ by ring] at h
  have := Real.sin_sq_add_cos_sq (a * k μ / 2)
  linarith

lemma lap_term_bound {f : E4 → ℝ} {R C2 : ℝ} (hR : 0 ≤ R)
    (hfR : ∀ x, R < ‖x‖ → f x = 0)
    (hC2 : ∀ (x : E4) (μ : Fin 4) (a : ℝ), |f (x + a • EuclideanSpace.single μ 1) +
      f (x - a • EuclideanSpace.single μ 1) - 2 * f x| ≤ C2 * a ^ 2)
    {a : ℝ} (ha : 0 < a) (ha1 : a ≤ 1) (μ : Fin 4) (k : E4) :
    (2 - 2 * Real.cos (a * k μ)) * ‖∑' j, (f (a • zpt j) : ℂ) * EE a k j‖
      ≤ (lbox (Nof a (R + 1))).card * (C2 * a ^ 2) := by
  set u : E4 := a • EuclideanSpace.single μ (1 : ℝ)
  have hu : ‖u‖ = a := by
    simp only [u, norm_smul, norm_single_one, Real.norm_of_nonneg ha.le, mul_one]
  have hcos : 0 ≤ 2 - 2 * Real.cos (a * k μ) := by linarith [Real.cos_le_one (a * k μ)]
  set g : E4 → ℂ := fun y => ((f (y + u) + f (y - u) - 2 * f y : ℝ) : ℂ)
  have hg : ∀ y, R + 1 < ‖y‖ → g y = 0 := by
    intro y hy
    have h1 : R < ‖y + u‖ := by
      have := norm_sub_norm_le y (-u); rw [sub_neg_eq_add, norm_neg] at this; linarith
    have h2 : R < ‖y - u‖ := by
      have := norm_sub_norm_le y u; linarith [norm_sub_rev y u]
    simp [g, hfR _ h1, hfR _ h2, hfR y (by linarith)]
  have key := sbp ha hfR μ k
  have hnorm : ‖∑' j, g (a • zpt j) * EE a k j‖ =
      (2 - 2 * Real.cos (a * k μ)) * ‖∑' j, (f (a • zpt j) : ℂ) * EE a k j‖ := by
    simp only [g, u]
    rw [key, norm_mul, norm_neg, Complex.norm_real, Real.norm_of_nonneg hcos]
  rw [← hnorm, tsum_eq_sum (s := lbox (Nof a (R + 1))) (fun j hj => by
    rw [zero_off_lbox ha hg hj, zero_mul])]
  refine (norm_sum_le _ _).trans ?_
  rw [← nsmul_eq_mul, ← Finset.sum_const]
  refine Finset.sum_le_sum fun j _ => ?_
  rw [norm_mul, norm_EE, mul_one, Complex.norm_real, Real.norm_eq_abs]
  exact hC2 _ μ a

lemma FF_lap_bound {f : E4 → ℝ} {R C2 : ℝ} (hR : 0 ≤ R)
    (hfR : ∀ x, R < ‖x‖ → f x = 0) (hC2pos : 0 ≤ C2)
    (hC2 : ∀ (x : E4) (μ : Fin 4) (a : ℝ), |f (x + a • EuclideanSpace.single μ 1) +
      f (x - a • EuclideanSpace.single μ 1) - 2 * f x| ≤ C2 * a ^ 2)
    {a : ℝ} (ha : 0 < a) (ha1 : a ≤ 1) (k : E4) :
    lapSym a k * ‖FF f R a k‖ ≤ 4 * C2 * (2 * (R + 1) + 3) ^ 4 := by
  have hFF : ‖FF f R a k‖ = a ^ 4 * ‖∑' j, (f (a • zpt j) : ℂ) * EE a k j‖ := by
    unfold FF; rw [norm_smul, Real.norm_of_nonneg (by positivity), sum_eq_tsum ha hfR]
  rw [hFF, lapSym_eq_cos]
  calc (a ^ 2)⁻¹ * (∑ μ, (2 - 2 * Real.cos (a * k μ))) * (a ^ 4 * ‖∑' j, (f (a • zpt j) : ℂ) * EE a k j‖)
      = (a ^ 2)⁻¹ * a ^ 4 * ∑ μ, (2 - 2 * Real.cos (a * k μ)) * ‖∑' j, (f (a • zpt j) : ℂ) * EE a k j‖ := by
        rw [← Finset.sum_mul]; ring
    _ ≤ (a ^ 2)⁻¹ * a ^ 4 * ∑ _μ : Fin 4, (lbox (Nof a (R + 1))).card * (C2 * a ^ 2) :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun μ _ => lap_term_bound hR hfR hC2 ha ha1 μ k)
          (by positivity)
    _ = 4 * C2 * (a ^ 4 * (lbox (Nof a (R + 1))).card) := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        field_simp; push_cast; ring
    _ ≤ 4 * C2 * (2 * (R + 1) + 3) ^ 4 := by
        gcongr; exact a4_card_le ha ha1 (by linarith)

/-- Jordan's inequality lower bound for the lattice symbol. -/
lemma lapSym_ge {a : ℝ} (ha : 0 < a) {k : E4} (hk : k ∈ BZ a) :
    4 / π ^ 2 * ‖k‖ ^ 2 ≤ lapSym a k := by
  unfold lapSym
  rw [EuclideanSpace.real_norm_sq_eq, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_le_sum fun μ _ => ?_
  have hb := hk μ
  rw [Set.mem_Icc] at hb
  set x := a * k μ / 2
  have hx : |x| ≤ π / 2 := by
    rw [abs_le]; simp only [x]
    constructor
    · have := mul_le_mul_of_nonneg_left hb.1 ha.le
      rw [mul_div_cancel₀ _ ha.ne'] at this; linarith
    · have := mul_le_mul_of_nonneg_left hb.2 ha.le
      rw [mul_div_cancel₀ _ ha.ne'] at this; linarith
  have hj : 2 / π * |x| ≤ |Real.sin x| := by
    rcases le_total 0 x with h | h
    · rw [abs_of_nonneg h] at hx ⊢
      have := Real.mul_le_sin h hx
      exact this.trans (le_abs_self _)
    · rw [abs_of_nonpos h] at hx ⊢
      have := Real.mul_le_sin (by linarith : 0 ≤ -x) hx
      rw [Real.sin_neg] at this
      exact this.trans (neg_le_abs _)
  have hsq : (2 / π * |x|) ^ 2 ≤ Real.sin x ^ 2 := by
    rw [← sq_abs (Real.sin x)]; exact pow_le_pow_left₀ (by positivity) hj 2
  have hπ := pi_pos
  have : k μ = 2 * x / a := by simp only [x]; field_simp
  rw [this]
  calc 4 / π ^ 2 * (2 * x / a) ^ 2 = 4 / a ^ 2 * (2 / π * |x|) ^ 2 := by
        rw [mul_pow, sq_abs]; field_simp
    _ ≤ 4 / a ^ 2 * Real.sin x ^ 2 := by gcongr

/-! ### Fourier-side identity -/

lemma normSq_sum {ι : Type*} (S : Finset ι) (c t : ι → ℝ) :
    ‖∑ j ∈ S, (c j : ℂ) * cexp (↑(-t j) * I)‖ ^ 2 =
      ∑ j ∈ S, ∑ j' ∈ S, c j * c j' * Real.cos (t j - t j') := by
  rw [Complex.sq_norm, Complex.normSq_apply, Complex.re_sum, Complex.im_sum]
  simp only [Complex.re_ofReal_mul, Complex.im_ofReal_mul, Complex.exp_ofReal_mul_I_re,
    Complex.exp_ofReal_mul_I_im, Real.cos_neg, Real.sin_neg]
  rw [Finset.sum_mul_sum, Finset.sum_mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j' _ => ?_
  rw [Real.cos_sub]; ring

lemma ph_sub (a : ℝ) (k : E4) (i j : Fin 4 → ℤ) :
    ph a k i - ph a k j = a * ∑ μ, k μ * ((i - j : Fin 4 → ℤ) μ : ℝ) := by
  simp only [ph, Pi.sub_apply, Int.cast_sub, mul_sub, Finset.sum_sub_distrib]

lemma norm_FF_sq (f : E4 → ℝ) (R a : ℝ) (k : E4) :
    ‖FF f R a k‖ ^ 2 = a ^ 8 * ∑ i ∈ lbox (Nof a R), ∑ j ∈ lbox (Nof a R),
      f (a • zpt i) * f (a • zpt j) * Real.cos (a * ∑ μ, k μ * ((i - j : Fin 4 → ℤ) μ : ℝ)) := by
  unfold FF
  rw [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs, ← pow_mul]
  simp only [EE]
  rw [normSq_sum]
  simp only [ph_sub]

lemma fourier_identity {f : E4 → ℝ} {R a m2 : ℝ} (hm : 0 < m2) :
    a ^ 8 * ∑ p ∈ lbox (Nof a R) ×ˢ lbox (Nof a R),
        f (a • zpt p.1) * Ga a m2 (p.1 - p.2) * f (a • zpt p.2) =
      ((2 * π) ^ 4)⁻¹ * ∫ k in BZ a, ‖FF f R a k‖ ^ 2 / (lapSym a k + m2) := by
  set S := lbox (Nof a R)
  have hI : ∀ i : Fin 4 → ℤ, IntegrableOn
      (fun k : E4 => Real.cos (a * ∑ μ, k μ * i μ) / (lapSym a k + m2)) (BZ a) :=
    fun i => integrableOn_BZ (continuous_integrand a m2 hm i)
  have h1 : (fun k => ‖FF f R a k‖ ^ 2 / (lapSym a k + m2)) = fun k =>
      a ^ 8 * ∑ i ∈ S, ∑ j ∈ S, f (a • zpt i) * f (a • zpt j) *
        (Real.cos (a * ∑ μ, k μ * ((i - j : Fin 4 → ℤ) μ : ℝ)) / (lapSym a k + m2)) := by
    funext k
    rw [norm_FF_sq, mul_div_assoc, Finset.sum_div]
    congr 1; refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_div]; refine Finset.sum_congr rfl fun j _ => ?_
    ring
  rw [h1, integral_const_mul, integral_finsetSum _ (fun i _ =>
    integrable_finsetSum _ fun j _ => (hI (i - j)).const_mul _)]
  simp_rw [integral_finsetSum _ (fun j _ => (hI _).const_mul _), integral_const_mul]
  rw [Finset.sum_product]
  simp only [Ga, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

lemma change_of_variables (H : E4 → ℝ) (a : ℝ) :
    ((2 * π) ^ 4)⁻¹ * ∫ k in BZ a, H k = ∫ ξ, (BZ a).indicator H ((2 * π) • ξ) := by
  rw [Measure.integral_comp_smul, finrank_euclideanSpace_fin, integral_indicator (measurableSet_BZ a),
    smul_eq_mul, abs_of_pos (by positivity)]
  
/-! ### pointwise limits -/

/-- the integrand of the Fourier transform. -/
def gxi (f : E4 → ℝ) (ξ : E4) (x : E4) : ℂ := cexp (↑(-(2 * π * ⟪x, ξ⟫)) * I) * (f x : ℂ)

lemma FF_two_pi (f : E4 → ℝ) (R a : ℝ) (ξ : E4) :
    FF f R a ((2 * π) • ξ) = (a ^ 4 : ℝ) • ∑ j ∈ lbox (Nof a R), gxi f ξ (a • zpt j) := by
  unfold FF; congr 1; refine Finset.sum_congr rfl fun j _ => ?_
  simp only [gxi, EE, ph]
  rw [mul_comm]
  have : a * ∑ μ, ((2 * π) • ξ) μ * (j μ : ℝ) = 2 * π * ⟪a • zpt j, ξ⟫ := by
    simp only [PiLp.inner_apply, PiLp.smul_apply, smul_eq_mul, smul_zpt_apply, RCLike.inner_apply,
      conj_trivial, Finset.mul_sum]
    refine Finset.sum_congr rfl fun μ _ => ?_
    rw [zpt_apply]; ring
  rw [this]

lemma fourier_gxi (f : E4 → ℝ) (ξ : E4) : ∫ x, gxi f ξ x = 𝓕 (fun x => (f x : ℂ)) ξ := by
  rw [fourier_eq]; congr 1; funext v
  rw [Circle.smul_def, Real.fourierChar_apply, smul_eq_mul, gxi]
  congr 3; ring

lemma continuous_gxi {f : E4 → ℝ} (hf : Continuous f) (ξ : E4) : Continuous (gxi f ξ) := by
  have : Continuous fun x : E4 => ⟪x, ξ⟫ := continuous_id.inner continuous_const
  unfold gxi
  fun_prop

lemma tendsto_FF {f : E4 → ℝ} (hf : Continuous f) {R : ℝ} (hfR : ∀ x, R < ‖x‖ → f x = 0) (ξ : E4) :
    Tendsto (fun a => FF f R a ((2 * π) • ξ)) (𝓝[>] 0) (𝓝 (𝓕 (fun x => (f x : ℂ)) ξ)) := by
  simp_rw [FF_two_pi]
  rw [← fourier_gxi]
  exact riemann (continuous_gxi hf ξ) (fun x hx => by simp [gxi, hfR x hx])

lemma tendsto_sin_div (c : ℝ) :
    Tendsto (fun a : ℝ => a⁻¹ * Real.sin (a * c)) (𝓝[>] 0) (𝓝 c) := by
  have h : HasDerivAt (fun t : ℝ => Real.sin (t * c)) c 0 := by
    have := ((hasDerivAt_id (0 : ℝ)).mul_const c).sin
    simpa using this
  have := h.tendsto_slope_zero
  simp only [zero_add, zero_mul, Real.sin_zero, sub_zero, smul_eq_mul] at this
  exact this.mono_left (nhdsWithin_mono _ fun x hx => ne_of_gt hx)

lemma tendsto_lapSym (ξ : E4) :
    Tendsto (fun a => lapSym a ((2 * π) • ξ)) (𝓝[>] 0) (𝓝 (4 * π ^ 2 * ‖ξ‖ ^ 2)) := by
  have hlim : Tendsto (fun a : ℝ => ∑ μ, 4 * (a⁻¹ * Real.sin (a * (π * ξ μ))) ^ 2) (𝓝[>] 0)
      (𝓝 (∑ μ, 4 * (π * ξ μ) ^ 2)) :=
    tendsto_finsetSum _ fun μ _ => ((tendsto_sin_div _).pow 2).const_mul 4
  have e2 : 4 * π ^ 2 * ‖ξ‖ ^ 2 = ∑ μ, 4 * (π * ξ μ) ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq, Finset.mul_sum]
    refine Finset.sum_congr rfl fun μ _ => ?_; ring
  rw [e2]
  refine hlim.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with a ha
  have ha' : a ≠ 0 := ne_of_gt ha
  unfold lapSym
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun μ _ => ?_
  simp only [PiLp.smul_apply, smul_eq_mul]
  rw [show a * (2 * π * ξ μ) / 2 = a * (π * ξ μ) by ring]
  field_simp

lemma eventually_mem_BZ (ξ : E4) : ∀ᶠ a in 𝓝[>] (0 : ℝ), (2 * π) • ξ ∈ BZ a := by
  have : ∀ᶠ a in 𝓝[>] (0 : ℝ), a ∈ Set.Ioo 0 (1 / (2 * ‖ξ‖ + 1)) :=
    Ioo_mem_nhdsGT (by positivity)
  filter_upwards [this] with a ha
  intro μ
  have h1 : |ξ μ| ≤ ‖ξ‖ := abs_coord_le ξ μ
  have ha1 := ha.1
  have h2 : a * (2 * ‖ξ‖ + 1) < 1 := by
    have := ha.2; rw [lt_div_iff₀ (by positivity)] at this; linarith
  have h3 : a * |ξ μ| ≤ 1 / 2 := by nlinarith [norm_nonneg ξ]
  have hπ := pi_pos
  simp only [PiLp.smul_apply, smul_eq_mul, Set.mem_Icc]
  have h4 := neg_abs_le (ξ μ)
  have h5 := le_abs_self (ξ μ)
  have h6 : -(1 / 2) ≤ a * ξ μ := by nlinarith [mul_le_mul_of_nonneg_left h4 ha1.le]
  have h7 : a * ξ μ ≤ 1 / 2 := by nlinarith [mul_le_mul_of_nonneg_left h5 ha1.le]
  have h2π : (0 : ℝ) ≤ 2 * π := by positivity
  constructor
  · rw [div_le_iff₀ ha1]; nlinarith [mul_le_mul_of_nonneg_left h6 h2π]
  · rw [le_div_iff₀ ha1]; nlinarith [mul_le_mul_of_nonneg_left h7 h2π]

lemma tendsto_h {f : E4 → ℝ} (hf : Continuous f) {R m2 : ℝ} (hm : 0 < m2)
    (hfR : ∀ x, R < ‖x‖ → f x = 0) (ξ : E4) :
    Tendsto (fun a => (BZ a).indicator (fun k => ‖FF f R a k‖ ^ 2 / (lapSym a k + m2)) ((2 * π) • ξ))
      (𝓝[>] 0) (𝓝 (‖𝓕 (fun x => (f x : ℂ)) ξ‖ ^ 2 / (4 * π ^ 2 * ‖ξ‖ ^ 2 + m2))) := by
  have h1 := ((tendsto_FF hf hfR ξ).norm.pow 2).div ((tendsto_lapSym ξ).add_const m2)
    (by positivity)
  refine h1.congr' ?_
  filter_upwards [eventually_mem_BZ ξ] with a ha
  rw [Set.indicator_of_mem ha]; rfl

/-! ### domination -/

lemma bound_ineq {F L t C0 C1 m2 : ℝ} (hF : 0 ≤ F) (hL : 0 ≤ L) (ht : 0 ≤ t) (hm : 0 < m2)
    (h0 : F ≤ C0) (h1 : L * F ≤ C1) (h2 : 16 * t ^ 2 ≤ L) :
    F ^ 2 / (L + m2) ≤ 64 * (C0 ^ 2 / m2 + C1 ^ 2 / 4096) * (1 + t) ^ (-6 : ℝ) := by
  have hC0 : 0 ≤ C0 := hF.trans h0
  have hq0 : 0 ≤ C0 ^ 2 / m2 := div_nonneg (sq_nonneg _) hm.le
  have hq1 : 0 ≤ C1 ^ 2 / 4096 := div_nonneg (sq_nonneg _) (by norm_num)
  rw [Real.rpow_neg (by positivity), show (6 : ℝ) = ((6 : ℕ) : ℝ) by norm_num, Real.rpow_natCast,
    ← div_eq_mul_inv, le_div_iff₀ (by positivity)]
  rcases le_total t 1 with ht1 | ht1
  · have hA : F ^ 2 / (L + m2) ≤ C0 ^ 2 / m2 :=
      div_le_div₀ (sq_nonneg _) (pow_le_pow_left₀ hF h0 2) hm (by linarith)
    have hB : (1 + t) ^ 6 ≤ 64 := by
      calc (1 + t) ^ 6 ≤ 2 ^ 6 := pow_le_pow_left₀ (by positivity) (by linarith) 6
        _ = 64 := by norm_num
    calc F ^ 2 / (L + m2) * (1 + t) ^ 6 ≤ C0 ^ 2 / m2 * 64 :=
          mul_le_mul hA hB (by positivity) hq0
      _ ≤ 64 * (C0 ^ 2 / m2 + C1 ^ 2 / 4096) := by linarith
  · have ht0 : 0 < t := by linarith
    have hLpos : 0 < L := by nlinarith
    have hF' : F ≤ C1 / L := by rw [le_div_iff₀ hLpos]; linarith
    have hA : F ^ 2 / (L + m2) ≤ C1 ^ 2 / L ^ 3 := by
      calc F ^ 2 / (L + m2) ≤ F ^ 2 / L :=
            div_le_div_of_nonneg_left (sq_nonneg _) hLpos (by linarith)
        _ ≤ (C1 / L) ^ 2 / L := by gcongr
        _ = C1 ^ 2 / L ^ 3 := by field_simp
    have hB : C1 ^ 2 / L ^ 3 ≤ C1 ^ 2 / (16 * t ^ 2) ^ 3 :=
      div_le_div_of_nonneg_left (sq_nonneg _) (by positivity) (pow_le_pow_left₀ (by positivity) h2 3)
    have hC : (1 + t) ^ 6 ≤ 64 * t ^ 6 := by
      calc (1 + t) ^ 6 ≤ (2 * t) ^ 6 := pow_le_pow_left₀ (by positivity) (by linarith) 6
        _ = 64 * t ^ 6 := by ring
    calc F ^ 2 / (L + m2) * (1 + t) ^ 6 ≤ C1 ^ 2 / (16 * t ^ 2) ^ 3 * (64 * t ^ 6) :=
          mul_le_mul (hA.trans hB) hC (by positivity) (by positivity)
      _ = 64 * (C1 ^ 2 / 4096) := by field_simp; ring
      _ ≤ 64 * (C0 ^ 2 / m2 + C1 ^ 2 / 4096) := by linarith

lemma continuous_FF (f : E4 → ℝ) (R a : ℝ) : Continuous (FF f R a) := by
  have hs : Continuous fun k : E4 => ∑ j ∈ lbox (Nof a R), (f (a • zpt j) : ℂ) * EE a k j :=
    continuous_finsetSum _ fun j _ => by
      unfold EE ph
      exact continuous_const.mul (Complex.continuous_exp.comp
        ((Complex.continuous_ofReal.comp (continuous_phase a j).neg).mul continuous_const))
  exact hs.const_smul (a ^ 4 : ℝ)

lemma continuous_H (f : E4 → ℝ) (R a : ℝ) {m2 : ℝ} (hm : 0 < m2) :
    Continuous fun k => ‖FF f R a k‖ ^ 2 / (lapSym a k + m2) :=
  ((continuous_FF f R a).norm.pow 2).div ((continuous_lapSym a).add continuous_const)
    (fun k => by have := lapSym_nonneg a k; positivity)

lemma dom {f : E4 → ℝ} {R m2 C0 C1 a : ℝ} (hm : 0 < m2) (ha : 0 < a)
    (hF0 : ∀ k, ‖FF f R a k‖ ≤ C0) (hF1 : ∀ k, lapSym a k * ‖FF f R a k‖ ≤ C1) (ξ : E4) :
    ‖(BZ a).indicator (fun k => ‖FF f R a k‖ ^ 2 / (lapSym a k + m2)) ((2 * π) • ξ)‖ ≤
      64 * (C0 ^ 2 / m2 + C1 ^ 2 / 4096) * (1 + ‖ξ‖) ^ (-6 : ℝ) := by
  by_cases hk : (2 * π) • ξ ∈ BZ a
  · rw [Set.indicator_of_mem hk, Real.norm_of_nonneg (by
      have := lapSym_nonneg a ((2 * π) • ξ); positivity)]
    refine bound_ineq (norm_nonneg _) (lapSym_nonneg _ _) (norm_nonneg _) hm (hF0 _) (hF1 _) ?_
    have := lapSym_ge ha hk
    rw [norm_smul, Real.norm_of_nonneg (by positivity)] at this
    have hπ := pi_pos
    calc 16 * ‖ξ‖ ^ 2 = 4 / π ^ 2 * (2 * π * ‖ξ‖) ^ 2 := by field_simp; ring
      _ ≤ _ := this
  · rw [Set.indicator_of_notMem hk, norm_zero]
    positivity

end Aux

open Aux in
/-- The free-field shadow for `C²` test functions with compact support. -/
theorem free_field_shadow {m2 : ℝ} (hm : 0 < m2) (f : EuclideanSpace ℝ (Fin 4) → ℝ)
    (hf : ContDiff ℝ 2 f) (hc : HasCompactSupport f) :
    Tendsto (fun a : ℝ => a ^ 8 * ∑' p : (Fin 4 → ℤ) × (Fin 4 → ℤ),
        f (a • zpt p.1) * Ga a m2 (p.1 - p.2) * f (a • zpt p.2)) (𝓝[>] 0)
      (𝓝 (∫ ξ, ‖𝓕 (fun x => (f x : ℂ)) ξ‖ ^ 2 / (4 * π ^ 2 * ‖ξ‖ ^ 2 + m2))) := by
  obtain ⟨R0, hR0⟩ := hc.isCompact.isBounded.subset_closedBall 0
  set R := max R0 0
  have hR : 0 ≤ R := le_max_right _ _
  have hfR : ∀ x, R < ‖x‖ → f x = 0 := fun x hx => image_eq_zero_of_notMem_tsupport (fun h => by
    have := hR0 h
    rw [Metric.mem_closedBall, dist_zero_right] at this
    linarith [le_max_left R0 0])
  obtain ⟨M0, hM0⟩ := hf.continuous.bounded_above_of_compact_support hc
  obtain ⟨C2, hC2pos, hC2⟩ := second_diff_bound hf hfR
  set H : ℝ → E4 → ℝ := fun a k => ‖FF f R a k‖ ^ 2 / (lapSym a k + m2)
  have hLHS : ∀ a : ℝ, 0 < a → a ^ 8 * ∑' p : (Fin 4 → ℤ) × (Fin 4 → ℤ),
      f (a • zpt p.1) * Ga a m2 (p.1 - p.2) * f (a • zpt p.2) =
        ∫ ξ, (BZ a).indicator (H a) ((2 * π) • ξ) := by
    intro a ha
    rw [tsum_eq_sum (s := lbox (Nof a R) ×ˢ lbox (Nof a R)), fourier_identity hm,
      change_of_variables]
    intro p hp
    rw [Finset.mem_product, not_and_or] at hp
    rcases hp with h | h
    · rw [zero_off_lbox ha hfR h]; simp
    · rw [zero_off_lbox ha hfR h]; simp
  refine Tendsto.congr' (f₁ := fun a => ∫ ξ, (BZ a).indicator (H a) ((2 * π) • ξ)) ?_ ?_
  · filter_upwards [self_mem_nhdsWithin] with a ha; exact (hLHS a ha).symm
  refine tendsto_integral_filter_of_dominated_convergence
    (fun ξ => 64 * (((2 * R + 3) ^ 4 * M0) ^ 2 / m2 + (4 * C2 * (2 * (R + 1) + 3) ^ 4) ^ 2 / 4096) *
      (1 + ‖ξ‖) ^ (-6 : ℝ)) ?_ ?_ ?_ ?_
  · exact Eventually.of_forall fun a => ((continuous_H f R a hm).measurable.indicator
      (measurableSet_BZ a) |>.comp (measurable_const_smul _)).aestronglyMeasurable
  · filter_upwards [Ioc_mem_nhdsGT (zero_lt_one' ℝ)] with a ha
    exact Eventually.of_forall (dom hm ha.1
      (fun k => FF_norm_le hR (fun x => by simpa using hM0 x) ha.1 ha.2 k)
      (fun k => FF_lap_bound hR hfR hC2pos hC2 ha.1 ha.2 k))
  · exact (integrable_one_add_norm (by rw [finrank_euclideanSpace_fin]; norm_num)).const_mul _
  · exact Eventually.of_forall (tendsto_h hf.continuous hm hfR)

end FreeField
end QE.FourierInfra
