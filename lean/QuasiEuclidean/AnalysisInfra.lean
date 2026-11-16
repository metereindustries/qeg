-- SPDX-License-Identifier: MIT
-- Copyright 2026 Metere Industries, Inc. Author: Alfredo Metere.
-- Quasi-Euclidean Granular Geometry. Any derivative work must carry this notice:
--   This work is derivative of the Quasi-Euclidean Granular Geometry book
--   authored by Alfredo Metere. Copyright 2026 Metere Industries, Inc.
--   All rights reserved
-- See LICENSE.md and NOTICE.

import QuasiEuclidean.Basic

/-!
# Analysis infrastructure

## Part A (granular, Lebesgue-free): power series at a nilpotent operator

On the space `P_d` of polynomials of degree `≤ d`, the operator `N = h D`
is nilpotent (`N^{d+1} = 0`), and a formal power series `∑ aₖ tᵏ` can be
evaluated at `N` as the *finite* sum `∑_{k ≤ d} aₖ Nᵏ`, i.e. as
`aeval N (truncation)`.  We prove the identity `log(1 + (eᵗ - 1)) = t`
modulo `t^{d+1}` as a polynomial identity, evaluate it at a nilpotent
element of any algebra, and deduce the operator logarithm
`h D = log(Sh) = ∑_{j=1}^d (-1)^{j+1}/j (Sh - 1)^j` on `P_d`
(book: `prop:differential-oplog`).
-/

open Polynomial Finset

set_option linter.unusedSectionVars false

namespace QE.AnalysisInfra

/-! ### Part A: truncated exponential and logarithm -/

section Nilpotent

variable (K : Type*) [Field K] [CharZero K]

/-- Truncated exponential `∑_{k ≤ d} tᵏ / k!`. -/
noncomputable def expTrunc (d : ℕ) : K[X] :=
  ∑ k ∈ range (d + 1), C ((k.factorial : K)⁻¹) * X ^ k

/-- Truncated logarithm `log(1+t) ≈ ∑_{j=1}^{d} (-1)^{j+1} tʲ / j`, written with
`j = i + 1`. -/
noncomputable def logTrunc (d : ℕ) : K[X] :=
  ∑ i ∈ range d, C ((-1) ^ i / ((i : K) + 1)) * X ^ (i + 1)

variable {K}

/-- Evaluation of a formal power series at an element `T` of an algebra,
truncated at order `d`: the finite sum `∑_{k ≤ d} aₖ Tᵏ`.  When `T^{d+1} = 0`
this is the (well-defined) value of the series at the nilpotent `T`. -/
noncomputable def nilEval {A : Type*} [Ring A] [Algebra K A]
    (f : PowerSeries K) (d : ℕ) (T : A) : A :=
  aeval T (PowerSeries.trunc (d + 1) f)

/-- A polynomial divisible by `X^{d+1}` vanishes at any `T` with `T^{d+1} = 0`. -/
theorem aeval_eq_zero_of_X_pow_dvd {A : Type*} [Ring A] [Algebra K A]
    {d : ℕ} {T : A} (hT : T ^ (d + 1) = 0) {P : K[X]} (hP : X ^ (d + 1) ∣ P) :
    aeval T P = 0 := by
  obtain ⟨Q, rfl⟩ := hP
  simp [hT]

/-- Polynomials agreeing modulo `X^{d+1}` take the same value at `T` with
`T^{d+1} = 0`. -/
theorem aeval_eq_of_X_pow_dvd_sub {A : Type*} [Ring A] [Algebra K A]
    {d : ℕ} {T : A} (hT : T ^ (d + 1) = 0) {P Q : K[X]} (hPQ : X ^ (d + 1) ∣ P - Q) :
    aeval T P = aeval T Q := by
  have := aeval_eq_zero_of_X_pow_dvd hT hPQ
  rw [map_sub] at this
  exact sub_eq_zero.mp this

/-- The evaluation at a nilpotent element is multiplicative:
`(fg)(T) = f(T) g(T)` when `T^{d+1} = 0` (and `T` commutes with itself). -/
theorem nilEval_mul {A : Type*} [Ring A] [Algebra K A] {d : ℕ} {T : A}
    (hT : T ^ (d + 1) = 0) (f g : PowerSeries K) :
    nilEval (f * g) d T = nilEval f d T * nilEval g d T := by
  unfold nilEval
  rw [← map_mul]
  apply aeval_eq_of_X_pow_dvd_sub hT
  rw [X_pow_dvd_iff]
  intro k hk
  rw [coeff_sub, ← PowerSeries.trunc_trunc_mul_trunc, PowerSeries.coeff_trunc,
    ite_eq_left_iff.mpr (fun h => absurd hk h), ← Polynomial.coe_mul, Polynomial.coeff_coe, sub_self]

/-- A polynomial with zero constant term whose derivative is divisible by
`X^d` is divisible by `X^{d+1}` (characteristic zero). -/
theorem X_pow_succ_dvd_of_derivative {P : K[X]} {d : ℕ} (h0 : P.coeff 0 = 0)
    (hd : X ^ d ∣ derivative P) : X ^ (d + 1) ∣ P := by
  rw [X_pow_dvd_iff] at hd ⊢
  intro k hk
  rcases k with _ | k
  · exact h0
  · have := hd k (by omega)
    rw [coeff_derivative] at this
    have hne : ((k : K) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero k
    exact (mul_eq_zero.mp this).resolve_right hne

theorem derivative_expTrunc (d : ℕ) :
    derivative (expTrunc K d) = expTrunc K d - C ((d.factorial : K)⁻¹) * X ^ d := by
  unfold expTrunc
  have h1 : derivative (∑ k ∈ range (d + 1), C ((k.factorial : K)⁻¹) * X ^ k)
      = ∑ k ∈ range d, C ((k.factorial : K)⁻¹) * X ^ k := by
    rw [map_sum, Finset.sum_range_succ']
    simp only [derivative_C_mul_X_pow, Nat.cast_zero, mul_zero, map_zero, zero_mul,
      add_zero, Nat.add_sub_cancel]
    refine Finset.sum_congr rfl fun k _ => ?_
    congr 2
    rw [Nat.factorial_succ]
    push_cast
    have : ((k : K) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero k
    have : (k.factorial : K) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero k
    field_simp
  rw [h1, Finset.sum_range_succ _ d, add_sub_cancel_right]

theorem derivative_logTrunc (d : ℕ) :
    derivative (logTrunc K d) = ∑ i ∈ range d, (-X) ^ i := by
  unfold logTrunc
  rw [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  have : ((i : K) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero i
  have hc : ((-1 : K) ^ i / ((i : K) + 1) * ((i + 1 : ℕ) : K)) = (-1) ^ i := by
    push_cast; field_simp
  rw [derivative_C_mul_X_pow, Nat.add_sub_cancel, hc, neg_pow (X : K[X]) i]
  simp

theorem expTrunc_coeff_zero (d : ℕ) : (expTrunc K d).coeff 0 = 1 := by
  unfold expTrunc
  rw [finsetSum_coeff, Finset.sum_eq_single 0]
  · simp
  · intro k _ hk
    rw [coeff_C_mul_X_pow, ite_eq_right_iff.mpr (fun h => absurd h.symm hk)]
  · simp

/-- `log(1 + (eᵗ - 1)) ≡ t (mod t^{d+1})`, as an identity of polynomials. -/
theorem log_exp_trunc (d : ℕ) :
    X ^ (d + 1) ∣ (logTrunc K d).comp (expTrunc K d - 1) - X := by
  set u : K[X] := expTrunc K d - 1 with hu
  have hXu : X ∣ u := by
    rw [X_dvd_iff, hu, coeff_sub, expTrunc_coeff_zero, coeff_one_zero, sub_self]
  apply X_pow_succ_dvd_of_derivative
  · rw [coeff_zero_eq_eval_zero, eval_sub, eval_comp, eval_X, ← coeff_zero_eq_eval_zero,
      X_dvd_iff.mp hXu]
    simp [logTrunc, eval_finsetSum]
  · set G : K[X] := ∑ i ∈ range d, (-u) ^ i with hG
    have hgeom : G * (-u - 1) = (-u) ^ d - 1 := geom_sum_mul (-u) d
    have hcomp : (derivative (logTrunc K d)).comp u = G := by
      rw [derivative_logTrunc, hG]
      simp [Polynomial.sum_comp, pow_comp, neg_comp]
    have hder : derivative u = (1 + u) - C ((d.factorial : K)⁻¹) * X ^ d := by
      rw [hu, derivative_sub, derivative_one, sub_zero, derivative_expTrunc]
      ring
    have key : derivative ((logTrunc K d).comp u - X)
        = -((-u) ^ d) - C ((d.factorial : K)⁻¹) * X ^ d * G := by
      rw [derivative_sub, derivative_X, derivative_comp, hcomp, hder]
      linear_combination (-1 : K[X]) * hgeom
    rw [key]
    refine dvd_sub (dvd_neg.mpr ?_) ?_
    · rw [neg_pow]
      exact Dvd.dvd.mul_left (pow_dvd_pow_of_dvd hXu d) _
    · exact Dvd.dvd.mul_right (Dvd.dvd.mul_left dvd_rfl _) _

end Nilpotent

/-! ### The operator logarithm on `P_d` -/

section OpLog

variable {K : Type*} [Field K] [CharZero K]

/-- The space `P_d` of polynomials of degree `≤ d`. -/
noncomputable abbrev Pd (K : Type*) [Field K] (d : ℕ) : Submodule K K[X] := degreeLE K (d : WithBot ℕ)

theorem derivative_mem_Pd {d : ℕ} {p : K[X]} (hp : p ∈ Pd K d) : derivative p ∈ Pd K d :=
  mem_degreeLE.mpr (degree_derivative_le.trans (mem_degreeLE.mp hp))

theorem taylor_mem_Pd (r : K) {d : ℕ} {p : K[X]} (hp : p ∈ Pd K d) : taylor r p ∈ Pd K d :=
  mem_degreeLE.mpr ((degree_taylor p r).le.trans (mem_degreeLE.mp hp))

/-- The operator `N = h·D` restricted to `P_d`. -/
noncomputable def opN (h : K) (d : ℕ) : Module.End K (Pd K d) :=
  (h • (derivative : K[X] →ₗ[K] K[X])).restrict
    (fun p hp => by rw [LinearMap.smul_apply]; exact Submodule.smul_mem _ h (derivative_mem_Pd hp))

/-- The shift `Sh p = p(· + h)` restricted to `P_d`. -/
noncomputable def opS (h : K) (d : ℕ) : Module.End K (Pd K d) :=
  (taylor h).restrict (fun _ hp => taylor_mem_Pd h hp)

/-- The forward difference `Δ_h = Sh - 1` on all polynomials. -/
noncomputable def fdiff (h : K) : K[X] →ₗ[K] K[X] := taylor h - LinearMap.id

theorem opN_apply (h : K) (d : ℕ) (v : Pd K d) :
    (opN h d v : K[X]) = h • derivative (v : K[X]) := rfl

theorem opS_apply (h : K) (d : ℕ) (v : Pd K d) :
    (opS h d v : K[X]) = taylor h (v : K[X]) := rfl

theorem opN_pow_coe (h : K) (d k : ℕ) (v : Pd K d) :
    ((opN h d ^ k) v : K[X]) = h ^ k • (derivative^[k] (v : K[X])) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ', Module.End.mul_apply, opN_apply, ih, map_smul,
      Function.iterate_succ_apply', smul_smul, pow_succ']

/-- `N^{d+1} = 0` on `P_d`: `N` is nilpotent. -/
theorem opN_pow_nil (h : K) (d : ℕ) : opN h d ^ (d + 1) = 0 := by
  refine LinearMap.ext fun v => Subtype.ext ?_
  rw [opN_pow_coe, LinearMap.zero_apply, Submodule.coe_zero]
  have hv : (v : K[X]).natDegree < d + 1 :=
    Nat.lt_succ_of_le (natDegree_le_of_degree_le (mem_degreeLE.mp v.2))
  rw [iterate_derivative_eq_zero hv, smul_zero]

/-- Taylor's formula, exact on `P_d`: `p(x + h) = ∑_{k ≤ d} hᵏ/k! · p⁽ᵏ⁾(x)`. -/
theorem taylor_eq_sum (h : K) {d : ℕ} {p : K[X]} (hp : p.natDegree ≤ d) :
    taylor h p = ∑ k ∈ range (d + 1), ((k.factorial : K)⁻¹ * h ^ k) • derivative^[k] p := by
  apply Polynomial.funext
  intro x
  rw [taylor_eval, add_comm, ← taylor_eval,
    eval_eq_sum_range' (n := d + 1) (by rw [natDegree_taylor]; omega), eval_finsetSum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [taylor_coeff, eval_smul, smul_eq_mul, ← factorial_smul_hasseDeriv,
    LinearMap.smul_apply, eval_smul, nsmul_eq_mul]
  have : (k.factorial : K) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero k
  field_simp

/-- On `P_d` the shift is the (finite) exponential series of `N = hD`:
`Sh = ∑_{k ≤ d} Nᵏ/k! = expTrunc(N)`. -/
theorem opS_eq_aeval (h : K) (d : ℕ) : opS h d = aeval (opN h d) (expTrunc K d) := by
  refine LinearMap.ext fun v => Subtype.ext ?_
  have hv : (v : K[X]).natDegree ≤ d := natDegree_le_of_degree_le (mem_degreeLE.mp v.2)
  rw [opS_apply, taylor_eq_sum h hv, expTrunc, map_sum, LinearMap.sum_apply,
    Submodule.coe_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [map_mul, aeval_C, aeval_X_pow, Module.End.mul_apply, Module.algebraMap_end_apply,
    Submodule.coe_smul, opN_pow_coe, smul_smul]

/-- **Operator logarithm on `P_d`.**  `log(Sh) = N`, i.e.
`∑_{j=1}^{d} (-1)^{j+1}/j · (Sh - 1)ʲ = h D` as endomorphisms of `P_d`. -/
theorem aeval_logTrunc_opS (h : K) (d : ℕ) :
    aeval (opS h d - 1) (logTrunc K d) = opN h d := by
  rw [opS_eq_aeval, ← map_one (aeval (R := K) (opN h d)),
    ← map_sub (aeval (R := K) (opN h d)), ← aeval_comp]
  exact (aeval_eq_of_X_pow_dvd_sub (A := Module.End K (Pd K d)) (opN_pow_nil h d) (log_exp_trunc (K := K) d)).trans
    (aeval_X _)

theorem opS_sub_one_pow_coe (h : K) (d k : ℕ) (v : Pd K d) :
    (((opS h d - 1) ^ k) v : K[X]) = (fdiff h ^ k) (v : K[X]) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ', Module.End.mul_apply, LinearMap.sub_apply, Module.End.one_apply,
      Submodule.coe_sub, opS_apply, ih, pow_succ', Module.End.mul_apply, fdiff,
      LinearMap.sub_apply, LinearMap.id_apply]

end OpLog

section OpLogDp

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-- Iterated granular derivatives of a polynomial function are iterated forward
differences: `Dpʲ p = Δ_{2ε}ʲ p / (2ε)ʲ`. -/
theorem Dp_iterate_eval (ε : K) (hε : ε ≠ 0) (q : K[X]) (j : ℕ) :
    (QE.Dp ε)^[j] (fun y => q.eval y)
      = fun y => ((fdiff (2 * ε) ^ j) q).eval y / (2 * ε) ^ j := by
  have h2 : (2 * ε) ≠ 0 := mul_ne_zero two_ne_zero hε
  induction j with
  | zero => funext y; simp
  | succ j ih =>
    rw [Function.iterate_succ_apply', ih]
    funext y
    rw [QE.Dp, pow_succ', Module.End.mul_apply, fdiff, LinearMap.sub_apply,
      LinearMap.id_apply, eval_sub, taylor_eval, pow_succ]
    field_simp

/-- **Operator logarithm on polynomials** (book: `prop:differential-oplog`).
For every `ε ≠ 0` and every polynomial `p` of degree `≤ d`,
`p' = ∑_{j=1}^{d} (-1)^{j+1}/j · (2ε)^{j-1} · Dpʲ p`. -/
theorem oplog_poly (ε : K) (hε : ε ≠ 0) (d : ℕ) (p : K[X]) (hp : p.natDegree ≤ d) (x : K) :
    (derivative p).eval x
      = ∑ j ∈ Finset.Icc 1 d,
          ((-1) ^ (j + 1) / (j : K)) * (2 * ε) ^ (j - 1) * (QE.Dp ε)^[j] (fun y => p.eval y) x := by
  have h2 : (2 * ε) ≠ 0 := mul_ne_zero two_ne_zero hε
  have hpd : p ∈ Pd K d := mem_degreeLE.mpr (degree_le_of_natDegree_le hp)
  have key := congrArg (fun T : Module.End K (Pd K d) => ((T ⟨p, hpd⟩ : K[X])).eval x)
    (aeval_logTrunc_opS (2 * ε) d)
  simp only [logTrunc, map_sum, map_mul, aeval_C, aeval_X_pow, LinearMap.sum_apply,
    Submodule.coe_sum, Module.End.mul_apply, Module.algebraMap_end_apply, Submodule.coe_smul,
    opS_sub_one_pow_coe, opN_apply, eval_finsetSum, eval_smul, smul_eq_mul] at key
  rw [← Finset.Ico_add_one_right_eq_Icc, Finset.sum_Ico_eq_sum_range, Nat.add_sub_cancel]
  simp_rw [Dp_iterate_eval ε hε]
  rw [← mul_right_inj' h2, ← key, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [add_comm 1 i, Nat.add_sub_cancel, pow_succ' (2 * ε) i, pow_succ (-1 : K) (i + 1),
    pow_succ (-1 : K) i]
  push_cast
  field_simp

end OpLogDp


/-! ## Part B (shadow, uses Lebesgue measure): boundary control of the shadow error

Lebesgue measure `volume` on `Fin n → ℝ` appears here only as the classical
(lossy) target of a comparison: these results are tagged `\leanshadowref`. -/

section Boundary

open MeasureTheory Metric

variable {n : ℕ}

/-- The cell `x + [-ε, ε)ⁿ` of the lattice point with index `k`, centre `2εk`. -/
def latCell (ε : ℝ) (k : Fin n → ℤ) : Set (Fin n → ℝ) :=
  Set.pi Set.univ fun i => Set.Ico (2 * ε * k i - ε) (2 * ε * k i + ε)

/-- The parallel set `S ⊕ [-δ, δ]ⁿ = {b + u : b ∈ S, ‖u‖_∞ ≤ δ}`. -/
def parallelBox (S : Set (Fin n → ℝ)) (δ : ℝ) : Set (Fin n → ℝ) :=
  {x | ∃ b ∈ S, ∀ i, |x i - b i| ≤ δ}

theorem mem_latCell {ε : ℝ} (hε : 0 < ε) {k : Fin n → ℤ} {x : Fin n → ℝ} :
    x ∈ latCell ε k ↔ ∀ i, ⌊(x i + ε) / (2 * ε)⌋ = k i := by
  have h2 : 0 < 2 * ε := by linarith
  simp only [latCell, Set.mem_univ_pi, Set.mem_Ico, Int.floor_eq_iff, le_div_iff₀ h2,
    div_lt_iff₀ h2]
  refine forall_congr' fun i => ?_
  constructor
  · rintro ⟨h1, h3⟩; constructor <;> nlinarith
  · rintro ⟨h1, h3⟩; constructor <;> nlinarith

theorem centre_mem_latCell {ε : ℝ} (hε : 0 < ε) (k : Fin n → ℤ) :
    (fun i => QE.centre ε (k i)) ∈ latCell ε k := by
  simp only [latCell, Set.mem_univ_pi, Set.mem_Ico, QE.centre]
  intro i; constructor <;> linarith

theorem mem_latCell_snap {ε : ℝ} (hε : 0 < ε) (x : Fin n → ℝ) :
    x ∈ latCell ε (fun i => ⌊(x i + ε) / (2 * ε)⌋) :=
  (mem_latCell hε).mpr fun _ => rfl

theorem latCell_disjoint {ε : ℝ} (hε : 0 < ε) {k k' : Fin n → ℤ} (hk : k ≠ k') :
    Disjoint (latCell ε k) (latCell ε k') := by
  rw [Set.disjoint_left]
  intro x hx hx'
  rw [mem_latCell hε] at hx hx'
  exact hk (funext fun i => (hx i).symm.trans (hx' i))

theorem measurableSet_latCell (ε : ℝ) (k : Fin n → ℤ) : MeasurableSet (latCell ε k) :=
  MeasurableSet.univ_pi fun _ => measurableSet_Ico

theorem volume_latCell (ε : ℝ) (k : Fin n → ℤ) :
    volume (latCell ε k) = ENNReal.ofReal (2 * ε) ^ n := by
  rw [latCell, Real.volume_pi_Ico]
  have : ∀ i : Fin n, (2 * ε * k i + ε) - (2 * ε * k i - ε) = 2 * ε := fun i => by ring
  simp only [this, Finset.prod_const, Finset.card_univ, Fintype.card_fin]

theorem isPreconnected_latCell (ε : ℝ) (k : Fin n → ℤ) : IsPreconnected (latCell ε k) :=
  isPreconnected_univ_pi fun _ => isPreconnected_Ico

/-- A preconnected set meeting both `E` and its complement meets `∂E`. -/
theorem preconnected_inter_frontier_nonempty {X : Type*} [TopologicalSpace X]
    {C E : Set X} (hC : IsPreconnected C) (h1 : (C ∩ E).Nonempty) (h2 : ¬ C ⊆ E) :
    (C ∩ frontier E).Nonempty := by
  by_contra hcon
  have hf : ∀ x ∈ C, x ∉ frontier E := fun x hx hxf => hcon ⟨x, hx, hxf⟩
  obtain ⟨a, haC, haE⟩ := h1
  obtain ⟨b, hbC, hbE⟩ := Set.not_subset.mp h2
  have hcov : C ⊆ interior E ∪ (closure E)ᶜ := by
    intro x hx
    by_cases hxi : x ∈ interior E
    · exact Or.inl hxi
    · right; intro hxc; exact hf x hx ⟨hxc, hxi⟩
  have ha : (C ∩ interior E).Nonempty := by
    refine ⟨a, haC, ?_⟩
    by_contra hai; exact hf a haC ⟨subset_closure haE, hai⟩
  have hb : (C ∩ (closure E)ᶜ).Nonempty := by
    refine ⟨b, hbC, fun hbc => hf b hbC ⟨hbc, fun hbi => hbE (interior_subset hbi)⟩⟩
  obtain ⟨z, _, hzi, hzc⟩ :=
    hC _ _ isOpen_interior isClosed_closure.isOpen_compl hcov ha hb
  exact hzc (interior_subset.trans subset_closure hzi)

theorem volume_biUnion_latCell {ε : ℝ} (hε : 0 < ε) (S : Finset (Fin n → ℤ)) :
    volume (⋃ k ∈ S, latCell ε k) = S.card * ENNReal.ofReal (2 * ε) ^ n := by
  rw [measure_biUnion_finset (fun k _ k' _ hkk' => latCell_disjoint hε hkk')
    (fun k _ => measurableSet_latCell ε k)]
  simp only [volume_latCell, Finset.sum_const, nsmul_eq_mul]

theorem isBounded_parallelBox {S : Set (Fin n → ℝ)} (hS : Bornology.IsBounded S) (δ : ℝ) :
    Bornology.IsBounded (parallelBox S δ) := by
  obtain ⟨R, hR⟩ := hS.subset_closedBall 0
  refine (isBounded_closedBall (x := (0 : Fin n → ℝ)) (r := max R 0 + max δ 0)).subset ?_
  rintro x ⟨b, hb, hxb⟩
  have hb' := hR hb
  rw [mem_closedBall, dist_pi_le_iff (by positivity)]
  intro i
  have hbi := (dist_pi_le_iff (le_max_right R 0)).mp
    (mem_closedBall.mp (closedBall_subset_closedBall (le_max_left R 0) hb')) i
  rw [Real.dist_eq] at hbi ⊢
  simp only [Pi.zero_apply, sub_zero] at hbi ⊢
  calc |x i| = |(x i - b i) + b i| := by ring_nf
    _ ≤ |x i - b i| + |b i| := abs_add_le _ _
    _ ≤ max δ 0 + max R 0 := add_le_add ((hxb i).trans (le_max_left _ _)) hbi
    _ = max R 0 + max δ 0 := add_comm _ _

/-- The indices of cells meeting a bounded set form a finite set, contained in an
explicit index box. -/
theorem latCell_index_bound {ε : ℝ} (hε : 0 < ε) {E : Set (Fin n → ℝ)}
    (hE : Bornology.IsBounded E) :
    ∃ B : ℤ, ∀ k : Fin n → ℤ, (latCell ε k ∩ E).Nonempty → ∀ i, -B ≤ k i ∧ k i ≤ B := by
  have h2 : 0 < 2 * ε := by linarith
  obtain ⟨R, hR⟩ := hE.subset_closedBall 0
  refine ⟨⌈(max R 0 + ε) / (2 * ε)⌉, fun k ⟨x, hxc, hxE⟩ i => ?_⟩
  have hx := (dist_pi_le_iff (le_max_right R 0)).mp
    (mem_closedBall.mp (closedBall_subset_closedBall (le_max_left R 0) (hR hxE))) i
  rw [Real.dist_eq, Pi.zero_apply, sub_zero, abs_le] at hx
  have hk := ((mem_latCell hε).mp hxc i)
  have hfl := Int.floor_le ((x i + ε) / (2 * ε))
  have hfl' := Int.lt_floor_add_one ((x i + ε) / (2 * ε))
  rw [hk] at hfl hfl'
  have hc := Int.le_ceil ((max R 0 + ε) / (2 * ε))
  have hR0 := le_max_right R 0
  have e1 : (x i + ε) / (2 * ε) ≤ (max R 0 + ε) / (2 * ε) :=
    div_le_div_of_nonneg_right (by linarith) h2.le
  have e2 : -((max R 0 + ε) / (2 * ε)) ≤ (x i + ε) / (2 * ε) - 1 := by
    rw [le_sub_iff_add_le, ← neg_div, div_add_one h2.ne', div_le_div_iff_of_pos_right h2]
    linarith
  constructor
  · have : (-(⌈(max R 0 + ε) / (2 * ε)⌉ : ℤ) : ℝ) < (k i : ℝ) := by linarith
    exact_mod_cast this.le
  · have : ((k i : ℤ) : ℝ) ≤ (⌈(max R 0 + ε) / (2 * ε)⌉ : ℝ) := by linarith
    exact_mod_cast this

/-- **Boundary control of the shadow error** (book: `thm:measure-boundary-error`).
For every bounded `E ⊆ ℝⁿ` and every `ε > 0`, with `A` the (finite) set of lattice
indices whose centres `2εk` lie in `E`,
`|μ_g(E ∩ (2εℤ)ⁿ) - λ(E)| ≤ λ(∂E ⊕ [-2ε, 2ε]ⁿ)`; both Lebesgue measures are finite.
(Measurability of `E` is not needed.) -/
theorem boundary_error {ε : ℝ} (hε : 0 < ε) {E : Set (Fin n → ℝ)}
    (hE : Bornology.IsBounded E) (A : Finset (Fin n → ℤ))
    (hA : ∀ k, k ∈ A ↔ (fun i => QE.centre ε (k i)) ∈ E) :
    volume E < ⊤ ∧ volume (parallelBox (frontier E) (2 * ε)) < ⊤ ∧
      |QE.muN n ε A - (volume E).toReal|
        ≤ (volume (parallelBox (frontier E) (2 * ε))).toReal := by
  classical
  have h2 : 0 < 2 * ε := by linarith
  have hEf : volume E < ⊤ := hE.measure_lt_top
  have hPf : volume (parallelBox (frontier E) (2 * ε)) < ⊤ :=
    (isBounded_parallelBox (hE.closure.subset frontier_subset_closure) _).measure_lt_top
  refine ⟨hEf, hPf, ?_⟩
  obtain ⟨B, hB⟩ := latCell_index_bound hε hE
  set Pf : Finset (Fin n → ℤ) :=
    (Finset.Icc (fun _ => -B) (fun _ => B)).filter (fun k => (latCell ε k ∩ E).Nonempty)
  set Mf : Finset (Fin n → ℤ) := Pf.filter (fun k => latCell ε k ⊆ E)
  have memPf : ∀ k, k ∈ Pf ↔ (latCell ε k ∩ E).Nonempty := by
    intro k
    simp only [Pf, Finset.mem_filter, Finset.mem_Icc, and_iff_right_iff_imp]
    intro hk
    exact ⟨fun i => (hB k hk i).1, fun i => (hB k hk i).2⟩
  have hMP : Mf ⊆ Pf := Finset.filter_subset _ _
  have hMA : Mf ⊆ A := by
    intro k hk
    rw [Finset.mem_filter] at hk
    exact (hA k).mpr (hk.2 (centre_mem_latCell hε k))
  have hAP : A ⊆ Pf := by
    intro k hk
    exact (memPf k).mpr ⟨_, centre_mem_latCell hε k, (hA k).mp hk⟩
  -- the three measure comparisons
  have hlow : (Mf.card : ENNReal) * ENNReal.ofReal (2 * ε) ^ n ≤ volume E := by
    rw [← volume_biUnion_latCell hε]
    refine measure_mono (Set.iUnion₂_subset fun k hk => ?_)
    exact (Finset.mem_filter.mp hk).2
  have hup : volume E ≤ (Pf.card : ENNReal) * ENNReal.ofReal (2 * ε) ^ n := by
    rw [← volume_biUnion_latCell hε]
    refine measure_mono fun x hx => Set.mem_iUnion₂.mpr ⟨_, ?_, mem_latCell_snap hε x⟩
    exact (memPf _).mpr ⟨x, mem_latCell_snap hε x, hx⟩
  have hbd : ((Pf \ Mf).card : ENNReal) * ENNReal.ofReal (2 * ε) ^ n
      ≤ volume (parallelBox (frontier E) (2 * ε)) := by
    rw [← volume_biUnion_latCell hε]
    refine measure_mono (Set.iUnion₂_subset fun k hk => ?_)
    rw [Finset.mem_sdiff] at hk
    have hne := (memPf k).mp hk.1
    have hns : ¬ latCell ε k ⊆ E := fun h => hk.2 (Finset.mem_filter.mpr ⟨hk.1, h⟩)
    obtain ⟨b, hbc, hbf⟩ := preconnected_inter_frontier_nonempty (isPreconnected_latCell ε k) hne hns
    intro x hx
    refine ⟨b, hbf, fun i => ?_⟩
    have hxi := (Set.mem_univ_pi.mp hx) i
    have hbi := (Set.mem_univ_pi.mp hbc) i
    simp only [Set.mem_Ico] at hxi hbi
    rw [abs_le]; constructor <;> linarith
  -- pass to real numbers
  have hc : (ENNReal.ofReal (2 * ε) ^ n).toReal = (2 * ε) ^ n := by
    rw [ENNReal.toReal_pow, ENNReal.toReal_ofReal h2.le]
  have tr : ∀ S : Finset (Fin n → ℤ),
      ((S.card : ENNReal) * ENNReal.ofReal (2 * ε) ^ n).toReal = S.card * (2 * ε) ^ n := by
    intro S; rw [ENNReal.toReal_mul, hc, ENNReal.toReal_natCast]
  have rlow := ENNReal.toReal_mono hEf.ne hlow
  have rup := ENNReal.toReal_mono (ENNReal.mul_ne_top (ENNReal.natCast_ne_top _)
    (ENNReal.pow_ne_top ENNReal.ofReal_ne_top)) hup
  have rbd := ENNReal.toReal_mono hPf.ne hbd
  rw [tr] at rlow rup rbd
  have hcard : ((Pf \ Mf).card : ℝ) = Pf.card - Mf.card := by
    rw [← Finset.card_sdiff_add_card_eq_card hMP]; push_cast; ring
  rw [hcard] at rbd
  have c1 : (Mf.card : ℝ) ≤ A.card := by exact_mod_cast Finset.card_le_card hMA
  have c2 : (A.card : ℝ) ≤ Pf.card := by exact_mod_cast Finset.card_le_card hAP
  have hpos : 0 ≤ (2 * ε) ^ n := by positivity
  unfold QE.muN
  rw [abs_le]
  constructor <;> nlinarith [mul_le_mul_of_nonneg_right c1 hpos, mul_le_mul_of_nonneg_right c2 hpos]

/-- If `λ(∂E ⊕ [-δ,δ]ⁿ) ≤ C δ` for `0 < δ ≤ δ₀` (finite upper Minkowski content of
`∂E`, cube form), the shadow error is `O(ε)`: at most `2Cε` once `2ε ≤ δ₀`. -/
theorem boundary_error_minkowski {ε δ₀ C : ℝ} (hε : 0 < ε) (h2ε : 2 * ε ≤ δ₀)
    {E : Set (Fin n → ℝ)} (hE : Bornology.IsBounded E)
    (hM : ∀ δ, 0 < δ → δ ≤ δ₀ → (volume (parallelBox (frontier E) δ)).toReal ≤ C * δ)
    (A : Finset (Fin n → ℤ)) (hA : ∀ k, k ∈ A ↔ (fun i => QE.centre ε (k i)) ∈ E) :
    |QE.muN n ε A - (volume E).toReal| ≤ 2 * C * ε := by
  have := (boundary_error hε hE A hA).2.2
  have := hM (2 * ε) (by linarith) h2ε
  linarith

/-- For closed `S`, the parallel set `S ⊕ [-δ,δ]ⁿ` is the closed `δ`-thickening of `S`
for the sup-distance. -/
theorem parallelBox_eq_cthickening {S : Set (Fin n → ℝ)} (hS : IsClosed S) {δ : ℝ}
    (hδ : 0 ≤ δ) : parallelBox S δ = cthickening δ S := by
  rw [hS.cthickening_eq_biUnion_closedBall hδ]
  ext x
  simp only [parallelBox, Set.mem_ofPred_eq, Set.mem_iUnion, mem_closedBall,
    dist_pi_le_iff hδ, Real.dist_eq, exists_prop]

/-- As `δ ↓ 0`, `λ(∂E ⊕ [-δ,δ]ⁿ) → λ(∂E)` for bounded `E`. -/
theorem tendsto_volume_parallelBox {E : Set (Fin n → ℝ)} (hE : Bornology.IsBounded E) :
    Filter.Tendsto (fun δ => volume (parallelBox (frontier E) δ)) (nhdsWithin 0 (Set.Ioi 0))
      (nhds (volume (frontier E))) := by
  have hF : Bornology.IsBounded (frontier E) := hE.closure.subset frontier_subset_closure
  have h := tendsto_measure_cthickening_of_isClosed (μ := volume)
    ⟨1, one_pos, (hF.cthickening (δ := 1)).measure_lt_top.ne⟩ isClosed_frontier
  refine (h.mono_left nhdsWithin_le_nhds).congr' ?_
  filter_upwards [self_mem_nhdsWithin] with δ hδ
  rw [parallelBox_eq_cthickening isClosed_frontier (le_of_lt hδ)]

/-- `λ(∂E ⊕ [-δ,δ]ⁿ) → 0` iff `λ(∂E) = 0`, i.e. iff `E` is Jordan measurable. -/
theorem tendsto_parallelBox_zero_iff {E : Set (Fin n → ℝ)} (hE : Bornology.IsBounded E) :
    Filter.Tendsto (fun δ => volume (parallelBox (frontier E) δ)) (nhdsWithin 0 (Set.Ioi 0))
      (nhds 0) ↔ volume (frontier E) = 0 := by
  constructor
  · intro h; exact tendsto_nhds_unique (tendsto_volume_parallelBox hE) h
  · intro h; rw [← h]; exact tendsto_volume_parallelBox hE

/-- If `λ(∂E) = 0` (Jordan measurable `E`), the shadow error tends to `0` as `ε → 0⁺`,
uniformly in the lattice trace: this re-proves the Jordan shadow theorem. -/
theorem shadow_error_tendsto_zero {E : Set (Fin n → ℝ)} (hE : Bornology.IsBounded E)
    (h0 : volume (frontier E) = 0) {η : ℝ} (hη : 0 < η) :
    ∃ ε₀ > 0, ∀ ε, 0 < ε → ε < ε₀ → ∀ A : Finset (Fin n → ℤ),
      (∀ k, k ∈ A ↔ (fun i => QE.centre ε (k i)) ∈ E) →
        |QE.muN n ε A - (volume E).toReal| < η := by
  have hev : ∀ᶠ δ in nhdsWithin (0 : ℝ) (Set.Ioi 0),
      volume (parallelBox (frontier E) δ) < ENNReal.ofReal η :=
    ((tendsto_parallelBox_zero_iff hE).mpr h0).eventually
      (gt_mem_nhds (ENNReal.ofReal_pos.mpr hη))
  obtain ⟨u, hu, hsub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp hev
  have hu' : 0 < u := hu
  refine ⟨u / 2, by linarith, fun ε hε hεu A hA => ?_⟩
  have hlt : volume (parallelBox (frontier E) (2 * ε)) < ENNReal.ofReal η :=
    hsub (show 2 * ε ∈ Set.Ioo 0 u from ⟨by linarith, by linarith⟩)
  exact lt_of_le_of_lt (boundary_error hε hE A hA).2.2 (ENNReal.toReal_lt_of_lt_ofReal hlt)

end Boundary

/-! ## Part C (shadow): ultrapower limits, Riemann sums, standard parts

A hyperreal is `Hyperreal.ofSeq u` for a real sequence `u`, modulo the
hyperfilter `𝒰 = hyperfilter ℕ`; an internal object is given levelwise.  The
standard part of a finite internal quantity is the `𝒰`-limit of its levels
(`Hyperreal.stdPart_of_tendsto`).  We prove the classical (Lebesgue/Riemann)
convergence statements along `𝒰` and transport them with `stdPart`.  These
results use Lebesgue integration and are tagged `\leanshadowref`. -/

section Ultra

open Filter Topology Hyperreal

/-- A hyperreal `ofSeq u` is infinitesimal (`0 < mk`) iff `u → 0` along the hyperfilter. -/
theorem infinitesimal_ofSeq_iff {u : ℕ → ℝ} :
    0 < ArchimedeanClass.mk (ofSeq u) ↔ Tendsto u (hyperfilter ℕ) (𝓝 0) := by
  constructor
  · intro h
    rw [← tendsto_ofSeq, tendsto_iff_forall]
    refine ⟨fun s hs => (ArchimedeanClass.lt_of_neg_of_archimedean coeRingHom h hs).le,
      fun s hs => (ArchimedeanClass.lt_of_pos_of_archimedean coeRingHom h hs).le⟩
  · intro h
    exact archimedeanClassMk_pos_of_tendsto (tendsto_ofSeq.mpr h)

/-- A positive infinite hyperreal `ofSeq u` is one with `u → +∞` along the hyperfilter. -/
theorem infinitePos_ofSeq_iff {u : ℕ → ℝ} :
    (0 < ofSeq u ∧ ArchimedeanClass.mk (ofSeq u) < 0) ↔ Tendsto u (hyperfilter ℕ) atTop := by
  rw [← tendsto_atTop_iff, tendsto_ofSeq]

theorem eventually_pos_of_ofSeq_pos {u : ℕ → ℝ} (h : 0 < ofSeq u) :
    ∀ᶠ n in hyperfilter ℕ, 0 < u n := by
  have : ofSeq (fun _ => (0 : ℝ)) < ofSeq u := h
  exact ofSeq_lt_ofSeq.mp this

theorem eventually_ge_hyperfilter (m : ℕ) : ∀ᶠ n in hyperfilter ℕ, m ≤ n :=
  hyperfilter_le_cofinite (Filter.eventually_cofinite.mpr (by
    simpa [not_le] using (Set.finite_lt_nat m)))

/-- In a compact set, every sequence has a limit along any ultrafilter. -/
theorem exists_tendsto_ultrafilter {X : Type*} [TopologicalSpace X] {K : Set X}
    (hK : IsCompact K) (𝒰 : Ultrafilter ℕ) {g : ℕ → X} (hg : ∀ᶠ n in (𝒰 : Filter ℕ), g n ∈ K) :
    ∃ x ∈ K, Tendsto g 𝒰 (𝓝 x) :=
  hK.ultrafilter_le_nhds (𝒰.map g) (by
    rw [Ultrafilter.coe_map, le_principal_iff]; exact hg)

end Ultra

section Riemann

open Filter Topology MeasureTheory

/-- Deterministic Riemann-sum estimate: if `f` oscillates by at most `ω` over
any step `h` inside `[hm, hM]`, the left Riemann sum over the lattice `hℤ` differs
from the integral by at most `(hM - hm) ω`. -/
theorem riemann_sum_sub_integral_le {f : ℝ → ℝ} (hf : Continuous f) {h ω : ℝ} (hh : 0 < h)
    {m M : ℤ} (hmM : m ≤ M)
    (hω : ∀ x y, h * m ≤ x → x ≤ h * M → h * m ≤ y → y ≤ h * M → |x - y| ≤ h →
      |f x - f y| ≤ ω) :
    |∑ k ∈ Finset.Ico m M, f (h * k) * h - ∫ x in (h * m)..(h * M), f x|
      ≤ (h * M - h * m) * ω := by
  set N := (M - m).toNat with hN
  have hNM : (M : ℝ) = m + N := by
    have : (N : ℤ) = M - m := by rw [hN]; exact Int.toNat_of_nonneg (by omega)
    have := congrArg (fun z : ℤ => (z : ℝ)) this
    push_cast at this; linarith
  have hIco : Finset.Ico m M = (Finset.range N).map ⟨fun j : ℕ => m + (j : ℤ), fun a b hab => by
      simpa using hab⟩ := by
    ext k
    simp only [Finset.mem_Ico, Finset.mem_map, Finset.mem_range]
    change (m ≤ k ∧ k < M) ↔ ∃ j : ℕ, j < N ∧ m + (j : ℤ) = k
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨(k - m).toNat, by omega, by omega⟩
    · rintro ⟨j, hj, rfl⟩; omega
  set a : ℕ → ℝ := fun j => h * (m + j) with ha
  have hint := intervalIntegral.sum_integral_adjacent_intervals (f := f) (μ := volume) (a := a)
    (n := N) (fun k _ => hf.intervalIntegrable _ _)
  have ha0 : a 0 = h * m := by simp [ha]
  have haN : a N = h * M := by simp [ha, hNM]
  rw [ha0, haN] at hint
  rw [← hint, hIco, Finset.sum_map, ← Finset.sum_sub_distrib]
  calc |∑ j ∈ Finset.range N, (f (h * ((m + (j : ℤ) : ℤ) : ℝ)) * h - ∫ x in a j..a (j + 1), f x)|
      ≤ ∑ j ∈ Finset.range N, |f (h * ((m + (j : ℤ) : ℤ) : ℝ)) * h - ∫ x in a j..a (j + 1), f x| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j ∈ Finset.range N, h * ω := by
        refine Finset.sum_le_sum fun j hj => ?_
        rw [Finset.mem_range] at hj
        have hconst : f (h * ((m + (j : ℤ) : ℤ) : ℝ)) * h
            = ∫ x in a j..a (j + 1), f (a j) := by
          rw [intervalIntegral.integral_const, smul_eq_mul]
          simp only [ha]; push_cast; ring
        rw [hconst, ← intervalIntegral.integral_sub intervalIntegrable_const
          (hf.intervalIntegrable _ _)]
        have hle : a j ≤ a (j + 1) := by simp only [ha]; push_cast; nlinarith
        have := intervalIntegral.norm_integral_le_of_norm_le_const (a := a j) (b := a (j + 1))
          (C := ω) (f := fun x => f (a j) - f x) (by
            intro x hx
            rw [Set.uIoc_of_le hle] at hx
            have hj' : (j : ℝ) + 1 ≤ N := by exact_mod_cast hj
            have e1 : h * m ≤ a j := by simp only [ha]; nlinarith [(Nat.cast_nonneg j : (0:ℝ) ≤ j)]
            have e2 : a (j + 1) ≤ h * M := by
              simp only [ha, hNM]; push_cast; nlinarith
            rw [Real.norm_eq_abs]
            refine hω (a j) x e1 (by linarith) (by linarith [hx.1]) (by linarith [hx.2]) ?_
            have : a (j + 1) - a j = h := by simp only [ha]; push_cast; ring
            rw [abs_le]; constructor
            · linarith [hx.2]
            · linarith [hx.1])
        rw [Real.norm_eq_abs] at this
        have hlen : |a (j + 1) - a j| = h := by
          simp only [ha]; push_cast; rw [show h * (m + (j + 1)) - h * (m + j) = h by ring]
          exact abs_of_pos hh
        rw [hlen] at this
        linarith
    _ = (h * M - h * m) * ω := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, hNM]; ring

/-- **Lattice Riemann sums converge** (classical shadow statement).  Along any
filter, if the mesh `h → 0⁺` and the lattice endpoints `h·m → a`, `h·M → b`, then
`∑_{m ≤ k < M} f(hk) h → ∫_a^b f` for continuous `f`. -/
theorem tendsto_riemann_lattice {ι : Type*} {L : Filter ι} {f : ℝ → ℝ} (hf : Continuous f)
    {a b : ℝ} (h : ι → ℝ) (m M : ι → ℤ) (hh : Tendsto h L (𝓝 0))
    (hpos : ∀ᶠ i in L, 0 < h i) (hmM : ∀ᶠ i in L, m i ≤ M i)
    (hm : Tendsto (fun i => h i * m i) L (𝓝 a)) (hM : Tendsto (fun i => h i * M i) L (𝓝 b)) :
    Tendsto (fun i => ∑ k ∈ Finset.Ico (m i) (M i), f (h i * k) * h i) L
      (𝓝 (∫ x in a..b, f x)) := by
  set Kc : Set ℝ := Set.Icc (min a b - 1) (max a b + 1)
  have hKc : IsCompact Kc := isCompact_Icc
  obtain ⟨C, hC⟩ := hKc.exists_bound_of_continuousOn hf.continuousOn
  set C' := max C 0
  have hC' : ∀ x ∈ Kc, |f x| ≤ C' := fun x hx => (hC x hx).trans (le_max_left _ _)
  have hC'0 : 0 ≤ C' := le_max_right _ _
  have huc := hKc.uniformContinuousOn_of_continuous hf.continuousOn
  rw [Metric.uniformContinuousOn_iff] at huc
  rw [Metric.tendsto_nhds]
  intro η hη
  set ω := η / (2 * (|b - a| + 3)) with hωdef
  have hω : 0 < ω := by positivity
  obtain ⟨ρ, hρ, hρf⟩ := huc ω hω
  set τ := min 1 (η / (8 * (C' + 1))) with hτdef
  have hτ : 0 < τ := lt_min one_pos (by positivity)
  have ev1 : ∀ᶠ i in L, h i < ρ := hh.eventually (gt_mem_nhds hρ)
  have ev2 : ∀ᶠ i in L, |h i * m i - a| < τ := by
    have := (Metric.tendsto_nhds.mp hm) τ hτ
    filter_upwards [this] with i hi; rwa [Real.dist_eq] at hi
  have ev3 : ∀ᶠ i in L, |h i * M i - b| < τ := by
    have := (Metric.tendsto_nhds.mp hM) τ hτ
    filter_upwards [this] with i hi; rwa [Real.dist_eq] at hi
  filter_upwards [ev1, ev2, ev3, hpos, hmM] with i h1 h2 h3 h4 h5
  have hτ1 : τ ≤ 1 := min_le_left _ _
  have hτ2 : τ ≤ η / (8 * (C' + 1)) := min_le_right _ _
  rw [abs_lt] at h2 h3
  have hmin1 : min a b ≤ a := min_le_left _ _
  have hmin2 : min a b ≤ b := min_le_right _ _
  have hmax1 : a ≤ max a b := le_max_left _ _
  have hmax2 : b ≤ max a b := le_max_right _ _
  have hmMr : h i * m i ≤ h i * M i := by
    have : (m i : ℝ) ≤ M i := by exact_mod_cast h5
    nlinarith
  -- Riemann part
  have hR := riemann_sum_sub_integral_le hf h4 h5 (ω := ω) (by
    intro x y hx1 hx2 hy1 hy2 hxy
    have hxK : x ∈ Kc := ⟨by linarith, by linarith⟩
    have hyK : y ∈ Kc := ⟨by linarith, by linarith⟩
    have := hρf x hxK y hyK (by rw [Real.dist_eq]; linarith)
    rw [Real.dist_eq] at this; exact this.le)
  -- endpoint parts
  have hend : ∀ u v : ℝ, |u - v| < τ → v ∈ Kc → u ∈ Set.Icc (min a b - 1 + 1 - 1) (max a b + 1) →
      |∫ x in v..u, f x| ≤ C' * |u - v| := by
    intro u v huv hv hu
    have := intervalIntegral.norm_integral_le_of_norm_le_const (a := v) (b := u) (C := C')
      (f := f) (by
        intro x hx
        rw [Real.norm_eq_abs]
        apply hC'
        have hx' := Set.uIoc_subset_uIcc hx
        rw [Set.mem_uIcc] at hx'
        rcases hx' with ⟨hx1, hx2⟩ | ⟨hx1, hx2⟩
        · exact ⟨by linarith [hv.1], by linarith [hu.2]⟩
        · exact ⟨by linarith [hu.1], by linarith [hv.2]⟩)
    simpa [Real.norm_eq_abs] using this
  have hE1 := hend (h i * m i) a (by rw [abs_lt]; constructor <;> linarith)
    ⟨by linarith, by linarith⟩ ⟨by linarith, by linarith⟩
  have hE2 := hend (h i * M i) b (by rw [abs_lt]; constructor <;> linarith)
    ⟨by linarith, by linarith⟩ ⟨by linarith, by linarith⟩
  have hsplit : ∫ x in a..b, f x = (∫ x in a..(h i * m i), f x)
      + (∫ x in (h i * m i)..(h i * M i), f x) - ∫ x in b..(h i * M i), f x := by
    rw [intervalIntegral.integral_add_adjacent_intervals (hf.intervalIntegrable _ _)
      (hf.intervalIntegrable _ _), ← intervalIntegral.integral_add_adjacent_intervals
      (hf.intervalIntegrable a b) (hf.intervalIntegrable b (h i * M i))]
    ring
  rw [Real.dist_eq, hsplit]
  have hlen : h i * M i - h i * m i ≤ |b - a| + 2 := by
    have := le_abs_self (b - a); linarith
  have hab1 : |h i * m i - a| ≤ τ := by rw [abs_le]; constructor <;> linarith
  have hab2 : |h i * M i - b| ≤ τ := by rw [abs_le]; constructor <;> linarith
  have k1 : (h i * M i - h i * m i) * ω ≤ (|b - a| + 2) * ω :=
    mul_le_mul_of_nonneg_right hlen hω.le
  have k2 : (|b - a| + 2) * ω < η / 2 := by
    rw [hωdef]; rw [mul_div_assoc']; rw [div_lt_div_iff₀ (by positivity) (by norm_num)]
    nlinarith [abs_nonneg (b - a)]
  have k3 : C' * |h i * m i - a| + C' * |h i * M i - b| ≤ C' * (2 * τ) := by
    have := mul_le_mul_of_nonneg_left hab1 hC'0
    have := mul_le_mul_of_nonneg_left hab2 hC'0
    linarith
  have k4 : C' * (2 * τ) < η / 2 := by
    have e1 : C' * (2 * τ) ≤ C' * (2 * (η / (8 * (C' + 1)))) :=
      mul_le_mul_of_nonneg_left (by linarith) hC'0
    have e2 : C' * (2 * (η / (8 * (C' + 1)))) = η / 4 * (C' / (C' + 1)) := by
      field_simp; ring
    have e3 : C' / (C' + 1) < 1 := by rw [div_lt_one (by linarith)]; linarith
    have e4 : η / 4 * (C' / (C' + 1)) < η / 4 := by
      have := mul_lt_mul_of_pos_left e3 (by positivity : 0 < η / 4); linarith
    linarith
  rw [abs_sub_comm (h i * m i) a] at hE1 k3
  rw [abs_sub_comm (h i * M i) b] at hE2 k3
  generalize ∑ k ∈ Finset.Ico (m i) (M i), f (h i * k) * h i = S at hR ⊢
  generalize ∫ x in a..(h i * m i), f x = B at hE1 ⊢
  generalize ∫ x in (h i * m i)..(h i * M i), f x = Mid at hR ⊢
  generalize ∫ x in b..(h i * M i), f x = Cc at hE2 ⊢
  have t1 : |S - (B + Mid - Cc)| ≤ |S - Mid| + |B| + |Cc| := by
    have := abs_add_le (S - Mid - B) Cc
    have := abs_sub (S - Mid) B
    rw [show S - (B + Mid - Cc) = S - Mid - B + Cc by ring]
    linarith
  linarith

end Riemann

/-! ### Shadow of the flat-prior posterior (book: `prop:stat-flat-shadow`) -/

section FlatPrior

open Filter Topology MeasureTheory Hyperreal

/-- Lattice sums `∑_{k ∈ Icc ⌈a/h⌉ ...}`: the lattice points `hk` with `a ≤ hk < b`. -/
theorem Ico_ceil_eq_filter {h a b : ℝ} (hh : 0 < h) (N : ℕ)
    (hN : max |a| |b| < h * N) :
    (Finset.Icc (-(N : ℤ)) N).filter (fun k : ℤ => a ≤ h * k ∧ h * k < b)
      = Finset.Ico ⌈a / h⌉ ⌈b / h⌉ := by
  ext k
  simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_Ico, Int.ceil_le, Int.lt_ceil,
    div_le_iff₀ hh, lt_div_iff₀ hh]
  constructor
  · rintro ⟨_, h1, h2⟩; exact ⟨by linarith, by linarith⟩
  · rintro ⟨h1, h2⟩
    refine ⟨⟨?_, ?_⟩, by linarith, by linarith⟩
    · have : -(h * N) < h * k := by
        have := le_abs_self a; have := neg_abs_le a; have := le_max_left |a| |b|; linarith
      have : (-(N : ℤ) : ℝ) < k := by
        push_cast; by_contra hc; push Not at hc; nlinarith
      exact_mod_cast this.le
    · have : h * k < h * N := by
        have := le_abs_self b; have := le_max_right |a| |b|; linarith
      have : (k : ℝ) < N := lt_of_mul_lt_mul_left this hh.le
      exact_mod_cast this.le

/-- The lattice points `hk` with `-m ≤ hk ≤ m`. -/
theorem Ico_ceil_floor_eq_filter {h m : ℝ} (hh : 0 < h) (N : ℕ) (hN : m < h * N) :
    (Finset.Icc (-(N : ℤ)) N).filter (fun k : ℤ => |h * k| ≤ m)
      = Finset.Ico ⌈-m / h⌉ (⌊m / h⌋ + 1) := by
  ext k
  simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_Ico, Int.ceil_le, Int.lt_add_one_iff,
    Int.le_floor, div_le_iff₀ hh, le_div_iff₀ hh, abs_le]
  constructor
  · rintro ⟨_, h1, h2⟩; exact ⟨by linarith, by linarith⟩
  · rintro ⟨h1, h2⟩
    refine ⟨⟨?_, ?_⟩, by linarith, by linarith⟩
    · have : (-(N : ℤ) : ℝ) < k := by
        push_cast; by_contra hc; push Not at hc; nlinarith
      exact_mod_cast this.le
    · have : (k : ℝ) < N := lt_of_mul_lt_mul_left (by linarith) hh.le
      exact_mod_cast this.le

theorem tendsto_mul_ceil_div {ι : Type*} {L : Filter ι} (h : ι → ℝ) (hh : Tendsto h L (𝓝 0))
    (hpos : ∀ᶠ i in L, 0 < h i) (a : ℝ) :
    Tendsto (fun i => h i * (⌈a / h i⌉ : ℝ)) L (𝓝 a) := by
  have hu : Tendsto (fun i => a + h i) L (𝓝 a) := by simpa using hh.const_add a
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hu ?_ ?_
  · filter_upwards [hpos] with i hi
    have := Int.le_ceil (a / h i)
    rw [div_le_iff₀ hi] at this; linarith
  · filter_upwards [hpos] with i hi
    have := Int.ceil_lt_add_one (a / h i)
    have : h i * (⌈a / h i⌉ : ℝ) < h i * (a / h i + 1) := mul_lt_mul_of_pos_left this hi
    rw [mul_add, mul_div_cancel₀ _ hi.ne', mul_one] at this; linarith

theorem tendsto_mul_floor_add_one_div {ι : Type*} {L : Filter ι} (h : ι → ℝ)
    (hh : Tendsto h L (𝓝 0)) (hpos : ∀ᶠ i in L, 0 < h i) (a : ℝ) :
    Tendsto (fun i => h i * ((⌊a / h i⌋ + 1 : ℤ) : ℝ)) L (𝓝 a) := by
  have hu : Tendsto (fun i => a + h i) L (𝓝 a) := by simpa using hh.const_add a
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hu ?_ ?_
  · filter_upwards [hpos] with i hi
    have := Int.lt_floor_add_one (a / h i)
    have : h i * (a / h i) < h i * ((⌊a / h i⌋ : ℝ) + 1) := mul_lt_mul_of_pos_left this hi
    rw [mul_div_cancel₀ _ hi.ne'] at this; push_cast; linarith
  · filter_upwards [hpos] with i hi
    have := Int.floor_le (a / h i)
    rw [le_div_iff₀ hi] at this; push_cast; nlinarith

/-- **Shadow of the flat-prior posterior.**  Hyperreal data are given by sequences
modulo the hyperfilter: `ε = ofSeq εs` positive infinitesimal, `Θ = [-Ω,Ω] ∩ 2εℤ`
with `Ω = 2ε·N` infinite, `L = *ℓ`.  If `ℓ ≥ 0` is continuous and integrable with
`∫ℓ > 0`, and `ℓ` is S-integrable on the lattice (`∑_{|θ|>R} ℓ(θ)·2ε ≈ 0` for every
positive infinite `R ≤ Ω`), then for all real `a < b` the standard part of the
granular uniform-prior posterior mass of `[a,b)` is `∫_a^b ℓ / ∫_ℝ ℓ`. -/
theorem flat_prior_shadow (ℓ : ℝ → ℝ) (hℓc : Continuous ℓ)
    (hℓi : Integrable ℓ) (hℓpos : 0 < ∫ x, ℓ x)
    (εs : ℕ → ℝ) (hεpos : 0 < ofSeq εs) (hεinf : 0 < ArchimedeanClass.mk (ofSeq εs))
    (Ns : ℕ → ℕ) (hΩ : ArchimedeanClass.mk (ofSeq (fun n => 2 * εs n * Ns n)) < 0)
    (hS : ∀ R : ℕ → ℝ, 0 < ofSeq R → ArchimedeanClass.mk (ofSeq R) < 0 →
      ofSeq R ≤ ofSeq (fun n => 2 * εs n * Ns n) →
      0 < ArchimedeanClass.mk (ofSeq (fun n =>
        ∑ k ∈ (Finset.Icc (-(Ns n : ℤ)) (Ns n)).filter (fun k : ℤ => R n < |2 * εs n * k|),
          ℓ (2 * εs n * k) * (2 * εs n))))
    (a b : ℝ) (hab : a < b) :
    ArchimedeanClass.stdPart (ofSeq (fun n =>
      (∑ k ∈ (Finset.Icc (-(Ns n : ℤ)) (Ns n)).filter
          (fun k : ℤ => a ≤ 2 * εs n * k ∧ 2 * εs n * k < b), ℓ (2 * εs n * k))
        / ∑ k ∈ Finset.Icc (-(Ns n : ℤ)) (Ns n), ℓ (2 * εs n * k)))
      = (∫ x in a..b, ℓ x) / ∫ x, ℓ x := by
  classical
  set U : Filter ℕ := (hyperfilter ℕ : Filter ℕ)
  set h : ℕ → ℝ := fun n => 2 * εs n with hdef
  set Ω : ℕ → ℝ := fun n => 2 * εs n * Ns n with hΩdef
  set Θ : ℕ → Finset ℤ := fun n => Finset.Icc (-(Ns n : ℤ)) (Ns n)
  have hpos : ∀ᶠ n in U, 0 < h n := by
    filter_upwards [eventually_pos_of_ofSeq_pos hεpos] with n hn; simp only [hdef]; linarith
  have hh0 : Tendsto h U (𝓝 0) := by
    have := (infinitesimal_ofSeq_iff.mp hεinf).const_mul 2
    simpa [hdef] using this
  have hΩtop : Tendsto Ω U atTop := by
    apply infinitePos_ofSeq_iff.mp
    refine ⟨?_, hΩ⟩
    have hnn : 0 ≤ ofSeq Ω := by
      have : ofSeq (fun _ => (0 : ℝ)) ≤ ofSeq Ω := ofSeq_le_ofSeq.mpr (by
        filter_upwards [hpos] with n hn
        simp only [hΩdef]; have := hn.le; simp only [hdef] at this; positivity)
      exact this
    refine lt_of_le_of_ne hnn fun h0 => ?_
    rw [← h0, ArchimedeanClass.mk_zero] at hΩ
    exact absurd hΩ (not_lt.mpr le_top)
  -- numerator
  have hnum : Tendsto (fun n => ∑ k ∈ (Θ n).filter (fun k : ℤ => a ≤ h n * k ∧ h n * k < b),
      ℓ (h n * k) * h n) U (𝓝 (∫ x in a..b, ℓ x)) := by
    have hR := tendsto_riemann_lattice (L := U) hℓc h (fun n => ⌈a / h n⌉) (fun n => ⌈b / h n⌉)
      hh0 hpos (by
        filter_upwards [hpos] with n hn
        exact Int.ceil_mono (div_le_div_of_nonneg_right hab.le hn.le))
      (tendsto_mul_ceil_div h hh0 hpos a) (tendsto_mul_ceil_div h hh0 hpos b)
    refine hR.congr' ?_
    filter_upwards [hpos, hΩtop.eventually_gt_atTop (max |a| |b|)] with n hn hΩn
    rw [Ico_ceil_eq_filter hn (Ns n) hΩn]
  -- denominator: truncated sums
  set Sm : ℕ → ℕ → ℝ := fun m n =>
    ∑ k ∈ (Θ n).filter (fun k : ℤ => |h n * k| ≤ m), ℓ (h n * k) * h n with hSm
  have hSmt : ∀ m : ℕ, Tendsto (Sm m) U (𝓝 (∫ x in (-(m : ℝ))..m, ℓ x)) := by
    intro m
    have hR := tendsto_riemann_lattice (L := U) hℓc h (fun n => ⌈-(m : ℝ) / h n⌉)
      (fun n => ⌊(m : ℝ) / h n⌋ + 1) hh0 hpos (by
        filter_upwards [hpos] with n hn
        have h1 := Int.ceil_le_floor_add_one (-(m : ℝ) / h n)
        have h2 : ⌊-(m : ℝ) / h n⌋ ≤ ⌊(m : ℝ) / h n⌋ :=
          Int.floor_mono (div_le_div_of_nonneg_right (by
            have := (Nat.cast_nonneg m : (0 : ℝ) ≤ m); linarith) hn.le)
        omega)
      (tendsto_mul_ceil_div h hh0 hpos _) (tendsto_mul_floor_add_one_div h hh0 hpos _)
    refine hR.congr' ?_
    filter_upwards [hpos, hΩtop.eventually_gt_atTop (m : ℝ)] with n hn hΩn
    simp only [hSm]
    rw [Ico_ceil_floor_eq_filter hn (Ns n) hΩn]
  -- the overspill sets
  set B : ℕ → Set ℕ := fun m =>
    {n | |Sm m n - ∫ x in (-(m : ℝ))..m, ℓ x| < 1 / ((m : ℝ) + 1) ∧ (m : ℝ) ≤ Ω n}
  have hB : ∀ m, B m ∈ U := by
    intro m
    have e1 := (Metric.tendsto_nhds.mp (hSmt m)) (1 / ((m : ℝ) + 1)) (by positivity)
    have e2 := hΩtop.eventually_ge_atTop (m : ℝ)
    filter_upwards [e1, e2] with n h1 h2
    exact ⟨by rwa [Real.dist_eq] at h1, h2⟩
  set P : ℕ → ℕ → Prop := fun n m => ∀ j ∈ Finset.Icc 1 m, n ∈ B j
  obtain ⟨R, hRdef⟩ : ∃ R : ℕ → ℕ, R = fun n => Nat.findGreatest (P n) n := ⟨_, rfl⟩
  have hRspec : ∀ n, 1 ≤ R n → n ∈ B (R n) := by
    intro n hn
    have := Nat.findGreatest_spec (P := P n) (m := 0) (Nat.zero_le n) (by
      intro j hj; exact absurd (Finset.mem_Icc.mp hj) (by omega))
    rw [hRdef] at hn ⊢
    exact this _ (Finset.mem_Icc.mpr ⟨hn, le_rfl⟩)
  have hRtop : Tendsto (fun n => (R n : ℝ)) U atTop := by
    rw [tendsto_atTop]
    intro r
    obtain ⟨m, hm⟩ := exists_nat_ge r
    have e1 : ∀ᶠ n in U, ∀ j ∈ Finset.Icc 1 m, n ∈ B j :=
      (Filter.eventually_all_finset _).mpr fun j _ => hB j
    filter_upwards [e1, eventually_ge_hyperfilter m] with n h1 h2
    have := Nat.le_findGreatest (P := P n) h2 h1
    rw [hRdef]
    exact hm.trans (by exact_mod_cast this)
  have hR1 : ∀ᶠ n in U, 1 ≤ R n := by
    filter_upwards [hRtop.eventually_ge_atTop 1] with n hn; exact_mod_cast hn
  -- tail
  have htail : Tendsto (fun n => ∑ k ∈ (Θ n).filter (fun k : ℤ => (R n : ℝ) < |h n * k|),
      ℓ (h n * k) * h n) U (𝓝 0) := by
    have hRpos := infinitePos_ofSeq_iff.mpr hRtop
    have hRle : ofSeq (fun n => (R n : ℝ)) ≤ ofSeq Ω := ofSeq_le_ofSeq.mpr (by
      filter_upwards [hR1] with n hn; exact (hRspec n hn).2)
    exact infinitesimal_ofSeq_iff.mp (hS (fun n => (R n : ℝ)) hRpos.1 hRpos.2 hRle)
  -- head
  have hhead : Tendsto (fun n => Sm (R n) n) U (𝓝 (∫ x, ℓ x)) := by
    have hI : Tendsto (fun n => ∫ x in (-(R n : ℝ))..(R n : ℝ), ℓ x) U (𝓝 (∫ x, ℓ x)) :=
      (MeasureTheory.intervalIntegral_tendsto_integral hℓi tendsto_neg_atTop_atBot
        tendsto_id).comp hRtop
    have hsmall : Tendsto (fun n => 1 / ((R n : ℝ) + 1)) U (𝓝 0) :=
      tendsto_const_nhds.div_atTop (tendsto_atTop_add_const_right _ 1 hRtop)
    rw [Metric.tendsto_nhds] at hI hsmall ⊢
    intro η hη
    filter_upwards [hI (η / 2) (by linarith), hsmall (η / 2) (by linarith), hR1] with n h1 h2 h3
    have h4 := (hRspec n h3).1
    rw [Real.dist_eq] at h1 h2 ⊢
    rw [sub_zero, abs_of_pos (by positivity)] at h2
    calc |Sm (R n) n - ∫ x, ℓ x|
        ≤ |Sm (R n) n - ∫ x in (-(R n : ℝ))..(R n : ℝ), ℓ x|
          + |(∫ x in (-(R n : ℝ))..(R n : ℝ), ℓ x) - ∫ x, ℓ x| := abs_sub_le _ _ _
      _ < η := by linarith
  have hden : Tendsto (fun n => ∑ k ∈ Θ n, ℓ (h n * k) * h n) U (𝓝 (∫ x, ℓ x)) := by
    have := hhead.add htail
    rw [add_zero] at this
    refine this.congr fun n => ?_
    simp only [hSm]
    rw [← Finset.sum_filter_add_sum_filter_not (Θ n) (fun k : ℤ => |h n * k| ≤ (R n : ℝ))]
    congr 1
    exact Finset.sum_congr (Finset.filter_congr fun k _ => not_le.symm) fun _ _ => rfl
  -- ratio
  have hratio := hnum.div hden hℓpos.ne'
  apply stdPart_of_tendsto
  rw [tendsto_ofSeq]
  refine hratio.congr' ?_
  filter_upwards [hpos] with n hn
  simp only [Pi.div_apply, ← Finset.sum_mul]
  rw [mul_div_mul_right _ _ hn.ne']

end FlatPrior

/-! ### Peano existence via the standard part (book: `thm:ode-existence`) -/

section Peano

open Filter Topology MeasureTheory Hyperreal

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The granular orbit `x_{k+1} = x_k + 2e F(x_k)` in a normed space (for `E = ℝ` this is
`QE.ODE.euler`). -/
def eulerV (e : ℝ) (F : E → E) (x₀ : E) : ℕ → E
  | 0 => x₀
  | k + 1 => eulerV e F x₀ k + (2 * e) • F (eulerV e F x₀ k)

@[simp] theorem eulerV_zero (e : ℝ) (F : E → E) (x₀ : E) : eulerV e F x₀ 0 = x₀ := rfl

theorem eulerV_succ (e : ℝ) (F : E → E) (x₀ : E) (k : ℕ) :
    eulerV e F x₀ (k + 1) = eulerV e F x₀ k + (2 * e) • F (eulerV e F x₀ k) := rfl

/-- Volterra form: `x_K = x₀ + ∑_{k<K} 2e F(x_k)`. -/
theorem eulerV_sum (e : ℝ) (F : E → E) (x₀ : E) (K : ℕ) :
    eulerV e F x₀ K = x₀ + ∑ k ∈ Finset.range K, (2 * e) • F (eulerV e F x₀ k) := by
  induction K with
  | zero => simp
  | succ K ih => rw [eulerV_succ, Finset.sum_range_succ, ← add_assoc, ← ih]

/-- Equi-Lipschitz bound `‖x_j - x_i‖ ≤ M·2e·(j - i)`. -/
theorem eulerV_increment {e M : ℝ} (he : 0 ≤ e) {F : E → E} (hM : ∀ x, ‖F x‖ ≤ M) (x₀ : E)
    {i j : ℕ} (hij : i ≤ j) :
    ‖eulerV e F x₀ j - eulerV e F x₀ i‖ ≤ M * (2 * e) * ((j : ℝ) - i) := by
  induction j, hij using Nat.le_induction with
  | base => simp
  | succ j hij ih =>
    rw [eulerV_succ]
    calc ‖eulerV e F x₀ j + (2 * e) • F (eulerV e F x₀ j) - eulerV e F x₀ i‖
        ≤ ‖eulerV e F x₀ j - eulerV e F x₀ i‖ + ‖(2 * e) • F (eulerV e F x₀ j)‖ := by
          rw [add_sub_right_comm]; exact norm_add_le _ _
      _ ≤ M * (2 * e) * ((j : ℝ) - i) + 2 * e * M := by
          gcongr
          rw [norm_smul, Real.norm_of_nonneg (by linarith)]
          exact mul_le_mul_of_nonneg_left (hM _) (by linarith)
      _ = M * (2 * e) * (((j + 1 : ℕ) : ℝ) - i) := by push_cast; ring

theorem eulerV_increment_abs {e M : ℝ} (he : 0 ≤ e) {F : E → E} (hM : ∀ x, ‖F x‖ ≤ M)
    (x₀ : E) (i j : ℕ) :
    ‖eulerV e F x₀ j - eulerV e F x₀ i‖ ≤ M * (2 * e) * |(j : ℝ) - i| := by
  rcases le_total i j with hij | hij
  · have : (i : ℝ) ≤ j := by exact_mod_cast hij
    rw [abs_of_nonneg (by linarith)]
    exact eulerV_increment he hM x₀ hij
  · have : (j : ℝ) ≤ i := by exact_mod_cast hij
    rw [norm_sub_rev, abs_sub_comm, abs_of_nonneg (by linarith)]
    exact eulerV_increment he hM x₀ hij

theorem floor_div_mul_bounds {h t : ℝ} (hh : 0 < h) (ht : 0 ≤ t) :
    h * (⌊t / h⌋₊ : ℝ) ≤ t ∧ t < h * (⌊t / h⌋₊ : ℝ) + h := by
  have h1 := Nat.floor_le (div_nonneg ht hh.le)
  have h2 := Nat.lt_floor_add_one (t / h)
  rw [le_div_iff₀ hh] at h1
  rw [div_lt_iff₀ hh] at h2
  constructor <;> nlinarith

/-- The internal orbit read at the lattice time `⌊t⌋ = 2e⌊t/2e⌋`, level `n`:
`x(⌊t⌋)` for `e = ofSeq εs`, `x₀ = ofSeq x0s`. -/
noncomputable def granOrbit (εs : ℕ → ℝ) (F : E → E) (x0s : ℕ → E) (n : ℕ) (t : ℝ) : E :=
  eulerV (εs n) F (x0s n) ⌊t / (2 * εs n)⌋₊

/-- The shadow `X(t) = st x(⌊t⌋)`: the hyperfilter limit of the levels. -/
noncomputable def granShadow (εs : ℕ → ℝ) (F : E → E) (x0s : ℕ → E) (t : ℝ) : E :=
  limUnder (hyperfilter ℕ : Filter ℕ) (fun n => granOrbit εs F x0s n t)

theorem granOrbit_lip {εs : ℕ → ℝ} {F : E → E} {M : ℝ} (hM : ∀ x, ‖F x‖ ≤ M) (x0s : ℕ → E)
    {n : ℕ} (hn : 0 < εs n) {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t) :
    ‖granOrbit εs F x0s n t - granOrbit εs F x0s n s‖ ≤ M * (|t - s| + 2 * εs n) := by
  have h2 : 0 < 2 * εs n := by linarith
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0)
  have ht' := floor_div_mul_bounds h2 ht
  have hs' := floor_div_mul_bounds h2 hs
  refine (eulerV_increment_abs hn.le hM _ _ _).trans ?_
  rw [mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ hM0
  rw [← abs_of_pos h2, ← abs_mul, abs_of_pos h2, mul_sub]
  rw [abs_le]; constructor
  · have := neg_abs_le (t - s); linarith
  · have := le_abs_self (t - s); linarith

theorem granOrbit_sub_init {εs : ℕ → ℝ} {F : E → E} {M : ℝ} (hM : ∀ x, ‖F x‖ ≤ M)
    (x0s : ℕ → E) {n : ℕ} (hn : 0 < εs n) {t : ℝ} (ht : 0 ≤ t) :
    ‖granOrbit εs F x0s n t - x0s n‖ ≤ M * t := by
  have h2 : 0 < 2 * εs n := by linarith
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0)
  have ht' := floor_div_mul_bounds h2 ht
  have := eulerV_increment hn.le hM (x0s n) (Nat.zero_le ⌊t / (2 * εs n)⌋₊)
  rw [eulerV_zero, Nat.cast_zero, sub_zero] at this
  refine this.trans ?_
  rw [mul_assoc]
  exact mul_le_mul_of_nonneg_left (by linarith) hM0

variable [FiniteDimensional ℝ E]

/-- The standard part `X(t) = st x(⌊t⌋)` exists for every `t ≥ 0`. -/
theorem tendsto_granShadow {εs : ℕ → ℝ} (hepos : 0 < ofSeq εs) {F : E → E} {M : ℝ}
    (hM : ∀ x, ‖F x‖ ≤ M) {x0s : ℕ → E} {ξ : E}
    (hx0 : Tendsto x0s (hyperfilter ℕ) (𝓝 ξ)) {t : ℝ} (ht : 0 ≤ t) :
    Tendsto (fun n => granOrbit εs F x0s n t) (hyperfilter ℕ) (𝓝 (granShadow εs F x0s t)) := by
  have hK : IsCompact (Metric.closedBall ξ (M * t + 1)) := isCompact_closedBall _ _
  obtain ⟨x, -, hx⟩ := exists_tendsto_ultrafilter hK (hyperfilter ℕ)
    (g := fun n => granOrbit εs F x0s n t) (by
      filter_upwards [eventually_pos_of_ofSeq_pos hepos,
        (Metric.tendsto_nhds.mp hx0) 1 one_pos] with n hn hx
      rw [Metric.mem_closedBall, dist_eq_norm]
      have := granOrbit_sub_init hM x0s hn ht
      rw [dist_eq_norm] at hx
      calc ‖granOrbit εs F x0s n t - ξ‖
          ≤ ‖granOrbit εs F x0s n t - x0s n‖ + ‖x0s n - ξ‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
        _ ≤ M * t + 1 := by linarith)
  exact tendsto_nhds_limUnder ⟨x, hx⟩

section PeanoHyp

variable {εs : ℕ → ℝ} {F : E → E} {M : ℝ} {x0s : ℕ → E} {ξ : E}

theorem tendsto_two_mul_of_infinitesimal (hεinf : 0 < ArchimedeanClass.mk (ofSeq εs)) :
    Tendsto (fun n => 2 * εs n) (hyperfilter ℕ) (𝓝 0) := by
  simpa using (infinitesimal_ofSeq_iff.mp hεinf).const_mul 2

theorem granShadow_zero (hεpos : 0 < ofSeq εs) (hM : ∀ x, ‖F x‖ ≤ M)
    (hx0 : Tendsto x0s (hyperfilter ℕ) (𝓝 ξ)) : granShadow εs F x0s 0 = ξ := by
  refine tendsto_nhds_unique (tendsto_granShadow hεpos hM hx0 le_rfl) ?_
  have : (fun n => granOrbit εs F x0s n 0) = x0s := by
    funext n; simp [granOrbit]
  rw [this]; exact hx0

theorem granShadow_lip (hεpos : 0 < ofSeq εs) (hεinf : 0 < ArchimedeanClass.mk (ofSeq εs))
    (hM : ∀ x, ‖F x‖ ≤ M) (hx0 : Tendsto x0s (hyperfilter ℕ) (𝓝 ξ)) {s t : ℝ}
    (hs : 0 ≤ s) (ht : 0 ≤ t) :
    ‖granShadow εs F x0s t - granShadow εs F x0s s‖ ≤ M * |t - s| := by
  have h1 := ((tendsto_granShadow hεpos hM hx0 ht).sub
    (tendsto_granShadow hεpos hM hx0 hs)).norm
  have h2 : Tendsto (fun n => M * (|t - s| + 2 * εs n)) (hyperfilter ℕ) (𝓝 (M * |t - s|)) := by
    have := ((tendsto_two_mul_of_infinitesimal hεinf).const_add |t - s|).const_mul M
    simpa using this
  refine le_of_tendsto_of_tendsto h1 h2 ?_
  filter_upwards [eventually_pos_of_ofSeq_pos hεpos] with n hn
  exact granOrbit_lip hM x0s hn hs ht

theorem granShadow_sub_init (hεpos : 0 < ofSeq εs) (hM : ∀ x, ‖F x‖ ≤ M)
    (hx0 : Tendsto x0s (hyperfilter ℕ) (𝓝 ξ)) {t : ℝ} (ht : 0 ≤ t) :
    ‖granShadow εs F x0s t - ξ‖ ≤ M * t := by
  have h1 := ((tendsto_granShadow hεpos hM hx0 ht).sub hx0).norm
  refine le_of_tendsto h1 ?_
  filter_upwards [eventually_pos_of_ofSeq_pos hεpos] with n hn
  exact granOrbit_sub_init hM x0s hn ht

theorem granShadow_continuousOn (hεpos : 0 < ofSeq εs)
    (hεinf : 0 < ArchimedeanClass.mk (ofSeq εs)) (hM : ∀ x, ‖F x‖ ≤ M)
    (hx0 : Tendsto x0s (hyperfilter ℕ) (𝓝 ξ)) :
    ContinuousOn (granShadow εs F x0s) (Set.Ici 0) := by
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0)
  rw [Metric.continuousOn_iff]
  intro b hb η hη
  refine ⟨η / (M + 1), by positivity, fun a ha hab => ?_⟩
  rw [dist_eq_norm]
  have := granShadow_lip hεpos hεinf hM hx0 (Set.mem_Ici.mp hb) (Set.mem_Ici.mp ha)
  rw [Real.dist_eq] at hab
  calc _ ≤ M * |a - b| := this
    _ ≤ M * (η / (M + 1)) := mul_le_mul_of_nonneg_left hab.le hM0
    _ < η := by
      rw [mul_div_assoc', div_lt_iff₀ (by linarith)]; nlinarith

/-- Uniform convergence of the levels to the shadow on `[0, t]`. -/
theorem granOrbit_uniform (hεpos : 0 < ofSeq εs) (hεinf : 0 < ArchimedeanClass.mk (ofSeq εs))
    (hM : ∀ x, ‖F x‖ ≤ M) (hx0 : Tendsto x0s (hyperfilter ℕ) (𝓝 ξ)) {t : ℝ} (ht : 0 ≤ t)
    {η : ℝ} (hη : 0 < η) :
    ∀ᶠ n in hyperfilter ℕ, ∀ s ∈ Set.Icc 0 t,
      ‖granOrbit εs F x0s n s - granShadow εs F x0s s‖ ≤ η := by
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0)
  set N0 : ℕ := ⌈4 * M * t / η⌉₊ + 1 with hN0
  have hN0pos : (0 : ℝ) < N0 := by positivity
  have hN0ge : 4 * M * t / η ≤ N0 := by
    have := Nat.le_ceil (4 * M * t / η); rw [hN0]; push_cast; linarith
  have hstep : M * (t / N0) ≤ η / 4 := by
    rw [div_le_iff₀ hη] at hN0ge
    rw [mul_div_assoc', div_le_iff₀ hN0pos]; nlinarith
  set g : ℕ → ℝ := fun i => i * t / N0
  have hg : ∀ i ∈ Finset.range (N0 + 1), 0 ≤ g i ∧ g i ≤ t := by
    intro i hi
    rw [Finset.mem_range] at hi
    have hi' : (i : ℝ) ≤ N0 := by exact_mod_cast Nat.lt_succ_iff.mp hi
    refine ⟨by positivity, ?_⟩
    simp only [g]; rw [div_le_iff₀ hN0pos]; nlinarith
  have e1 : ∀ᶠ n in hyperfilter ℕ, ∀ i ∈ Finset.range (N0 + 1),
      ‖granOrbit εs F x0s n (g i) - granShadow εs F x0s (g i)‖ ≤ η / 4 := by
    refine (Filter.eventually_all_finset _).mpr fun i hi => ?_
    have := (Metric.tendsto_nhds.mp (tendsto_granShadow hεpos hM hx0 (hg i hi).1)) (η / 4)
      (by linarith)
    filter_upwards [this] with n hn
    rw [dist_eq_norm] at hn; exact hn.le
  have e2 : ∀ᶠ n in hyperfilter ℕ, M * (2 * εs n) ≤ η / 4 := by
    have := ((tendsto_two_mul_of_infinitesimal hεinf).const_mul M)
    rw [mul_zero] at this
    filter_upwards [this.eventually (ge_mem_nhds (by linarith : (0 : ℝ) < η / 4))] with n hn
    exact hn
  filter_upwards [e1, e2, eventually_pos_of_ofSeq_pos hεpos] with n h1 h2 h3 s hs
  -- choose a grid point within `t / N0` of `s`
  obtain ⟨i, hi, hsi⟩ : ∃ i ∈ Finset.range (N0 + 1), |s - g i| ≤ t / N0 := by
    rcases eq_or_lt_of_le ht with h0 | htpos
    · refine ⟨0, by simp, ?_⟩
      have : s = 0 := by linarith [hs.1, hs.2, h0.symm.le]
      simp only [g, this, Nat.cast_zero, zero_mul, zero_div, sub_zero, abs_zero]
      positivity
    · refine ⟨⌊s * N0 / t⌋₊, ?_, ?_⟩
      · rw [Finset.mem_range, Nat.lt_succ_iff]
        apply Nat.floor_le_of_le
        rw [div_le_iff₀ htpos]; nlinarith [hs.2]
      · have hfl := Nat.floor_le (show 0 ≤ s * N0 / t by have := hs.1; positivity)
        have hfl' := Nat.lt_floor_add_one (s * N0 / t)
        simp only [g]
        set r : ℝ := (⌊s * N0 / t⌋₊ : ℝ)
        have k1 : r * t ≤ s * N0 := by rwa [le_div_iff₀ htpos] at hfl
        have k2 : s * N0 < (r + 1) * t := by rwa [div_lt_iff₀ htpos] at hfl'
        have hrw : s - r * t / N0 = (s * N0 - r * t) / N0 := by field_simp
        rw [hrw, abs_le, ← neg_div, div_le_div_iff_of_pos_right hN0pos,
          div_le_div_iff_of_pos_right hN0pos]
        constructor <;> nlinarith
  have hgi := hg i hi
  have a1 := granOrbit_lip hM x0s h3 hgi.1 hs.1 (s := g i) (t := s)
  have a2 := h1 i hi
  have a3 := granShadow_lip hεpos hεinf hM hx0 hs.1 hgi.1 (s := s) (t := g i)
  rw [abs_sub_comm] at a3
  have b1 : M * |s - g i| ≤ η / 4 := (mul_le_mul_of_nonneg_left hsi hM0).trans hstep
  calc ‖granOrbit εs F x0s n s - granShadow εs F x0s s‖
      ≤ ‖granOrbit εs F x0s n s - granOrbit εs F x0s n (g i)‖
        + ‖granOrbit εs F x0s n (g i) - granShadow εs F x0s (g i)‖
        + ‖granShadow εs F x0s (g i) - granShadow εs F x0s s‖ := by
        have := norm_sub_le_norm_sub_add_norm_sub (granOrbit εs F x0s n s)
          (granOrbit εs F x0s n (g i)) (granShadow εs F x0s s)
        have := norm_sub_le_norm_sub_add_norm_sub (granOrbit εs F x0s n (g i))
          (granShadow εs F x0s (g i)) (granShadow εs F x0s s)
        linarith
    _ ≤ M * (|s - g i| + 2 * εs n) + η / 4 + M * |s - g i| := by gcongr
    _ ≤ η := by nlinarith

/-- The shadow satisfies the integral equation `X(t) = ξ + ∫₀ᵗ F(X(σ)) dσ` for `t ≥ 0`. -/
theorem granShadow_integral (hF : Continuous F) (hεpos : 0 < ofSeq εs)
    (hεinf : 0 < ArchimedeanClass.mk (ofSeq εs)) (hM : ∀ x, ‖F x‖ ≤ M)
    (hx0 : Tendsto x0s (hyperfilter ℕ) (𝓝 ξ)) {t : ℝ} (ht : 0 ≤ t) :
    granShadow εs F x0s t = ξ + ∫ σ in (0 : ℝ)..t, F (granShadow εs F x0s σ) := by
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0)
  set X := granShadow εs F x0s with hXdef
  set G : ℝ → E := fun σ => F (X σ) with hGdef
  have hG : ContinuousOn G (Set.Ici 0) :=
    hF.comp_continuousOn (granShadow_continuousOn hεpos hεinf hM hx0)
  have hGb : ∀ σ, ‖G σ‖ ≤ M := fun σ => hM _
  have hGi : ∀ a b : ℝ, 0 ≤ a → 0 ≤ b → IntervalIntegrable G volume a b := by
    intro a b ha hb
    refine (hG.mono fun x hx => ?_).intervalIntegrable
    rw [Set.mem_uIcc] at hx
    rcases hx with ⟨h1, -⟩ | ⟨h1, -⟩
    · exact le_trans ha h1
    · exact le_trans hb h1
  refine tendsto_nhds_unique (tendsto_granShadow hεpos hM hx0 ht) ?_
  rw [Metric.tendsto_nhds]
  intro η hη
  have hKb : IsCompact (Metric.closedBall ξ (M * t + 1)) := isCompact_closedBall _ _
  have huc := hKb.uniformContinuousOn_of_continuous hF.continuousOn
  rw [Metric.uniformContinuousOn_iff] at huc
  set η' := η / (3 * (t + 1)) with hη'
  have hη'pos : 0 < η' := by positivity
  obtain ⟨ρ, hρ, hρF⟩ := huc η' hη'pos
  have evh : ∀ᶠ n in hyperfilter ℕ, M * (2 * εs n) < min (ρ / 2) (η / 3) := by
    have := (tendsto_two_mul_of_infinitesimal hεinf).const_mul M
    rw [mul_zero] at this
    exact this.eventually (gt_mem_nhds (lt_min (by linarith) (by linarith)))
  filter_upwards [eventually_pos_of_ofSeq_pos hεpos,
    (Metric.tendsto_nhds.mp hx0) (min 1 (η / 3)) (lt_min one_pos (by linarith)),
    granOrbit_uniform hεpos hεinf hM hx0 ht (η := ρ / 4) (by linarith), evh]
    with n hn hx hu hh
  set e := εs n with he
  have h2e : 0 < 2 * e := by linarith
  set K : ℕ := ⌊t / (2 * e)⌋₊ with hK
  have hfb := floor_div_mul_bounds h2e ht
  rw [← hK] at hfb
  set a : ℕ → ℝ := fun k => (k : ℝ) * (2 * e) with ha
  have hxk : ∀ k : ℕ, granOrbit εs F x0s n (a k) = eulerV e F (x0s n) k := by
    intro k
    simp only [granOrbit, ha, ← he]
    rw [mul_div_cancel_right₀ _ h2e.ne', Nat.floor_natCast]
  have haK : a K ≤ t := by simp only [ha]; linarith [hfb.1]
  have hyt : granOrbit εs F x0s n t
      = x0s n + ∑ k ∈ Finset.range K, (2 * e) • F (eulerV e F (x0s n) k) := by
    simp only [granOrbit, ← he, ← hK]; exact eulerV_sum _ _ _ _
  have hsplit : (∫ σ in (0 : ℝ)..t, G σ)
      = (∫ σ in (0 : ℝ)..(a K), G σ) + ∫ σ in (a K)..t, G σ :=
    (intervalIntegral.integral_add_adjacent_intervals (hGi _ _ le_rfl (by positivity))
      (hGi _ _ (by positivity) ht)).symm
  have hsum := intervalIntegral.sum_integral_adjacent_intervals (f := G) (μ := volume) (a := a)
    (n := K) (fun k _ => hGi _ _ (by positivity) (by positivity))
  have ha0 : a 0 = 0 := by simp [ha]
  rw [ha0] at hsum
  -- per-piece estimate
  have hpiece : ∀ k ∈ Finset.range K,
      ‖(2 * e) • F (eulerV e F (x0s n) k) - ∫ σ in (a k)..(a (k + 1)), G σ‖ ≤ η' * (2 * e) := by
    intro k hk
    rw [Finset.mem_range] at hk
    have hk1 : ((k : ℝ) + 1) ≤ K := by exact_mod_cast hk
    have hlen : a (k + 1) - a k = 2 * e := by simp only [ha]; push_cast; ring
    have hle : a k ≤ a (k + 1) := by linarith
    have hak0 : 0 ≤ a k := by simp only [ha]; positivity
    have hak1 : a (k + 1) ≤ t := by
      have : a (k + 1) ≤ a K := by simp only [ha]; push_cast; nlinarith
      linarith
    have hconst : (2 * e) • F (eulerV e F (x0s n) k)
        = ∫ σ in (a k)..(a (k + 1)), F (eulerV e F (x0s n) k) := by
      rw [intervalIntegral.integral_const, hlen]
    rw [hconst, ← intervalIntegral.integral_sub intervalIntegrable_const
      (hGi _ _ hak0 (by linarith))]
    have := intervalIntegral.norm_integral_le_of_norm_le_const (a := a k) (b := a (k + 1))
      (C := η') (f := fun σ => F (eulerV e F (x0s n) k) - G σ) (by
        intro σ hσ
        rw [Set.uIoc_of_le hle] at hσ
        have hσ0 : 0 ≤ σ := by linarith [hσ.1]
        have hσt : σ ≤ t := by linarith [hσ.2]
        have hxkmem : eulerV e F (x0s n) k ∈ Metric.closedBall ξ (M * t + 1) := by
          rw [← hxk, Metric.mem_closedBall, dist_eq_norm]
          have h1 := granOrbit_sub_init hM x0s hn hak0
          have h2 : ‖x0s n - ξ‖ < 1 := by
            rw [← dist_eq_norm]; exact lt_of_lt_of_le hx (min_le_left _ _)
          have h3 : M * a k ≤ M * t := mul_le_mul_of_nonneg_left (by linarith) hM0
          have := norm_sub_le_norm_sub_add_norm_sub (granOrbit εs F x0s n (a k)) (x0s n) ξ
          linarith
        have hXmem : X σ ∈ Metric.closedBall ξ (M * t + 1) := by
          rw [Metric.mem_closedBall, dist_eq_norm]
          have := granShadow_sub_init hεpos hM hx0 hσ0
          have h3 : M * σ ≤ M * t := mul_le_mul_of_nonneg_left hσt hM0
          linarith
        have hd : dist (eulerV e F (x0s n) k) (X σ) < ρ := by
          rw [dist_eq_norm]
          have h1 := hu (a k) ⟨hak0, by linarith⟩
          rw [hxk] at h1
          have h2 := granShadow_lip hεpos hεinf hM hx0 hσ0 hak0 (s := σ) (t := a k)
          have h3 : |a k - σ| ≤ 2 * e := by
            rw [abs_le]; constructor <;> linarith [hσ.1, hσ.2]
          have h4 : M * |a k - σ| ≤ M * (2 * e) := mul_le_mul_of_nonneg_left h3 hM0
          have h5 : M * (2 * e) < ρ / 2 := lt_of_lt_of_le hh (min_le_left _ _)
          have := norm_sub_le_norm_sub_add_norm_sub (eulerV e F (x0s n) k) (X (a k)) (X σ)
          linarith
        have := hρF _ hxkmem _ hXmem hd
        rw [dist_eq_norm] at this
        exact this.le)
    rw [hlen, abs_of_pos h2e] at this
    exact this
  -- assemble
  have htail : ‖∫ σ in (a K)..t, G σ‖ ≤ M * (2 * e) := by
    have := intervalIntegral.norm_integral_le_of_norm_le_const (a := a K) (b := t) (C := M)
      (f := G) (fun σ _ => hGb σ)
    refine this.trans (mul_le_mul_of_nonneg_left ?_ hM0)
    rw [abs_of_nonneg (by linarith)]; simp only [ha]; linarith [hfb.2]
  have hsumb : ‖∑ k ∈ Finset.range K, ((2 * e) • F (eulerV e F (x0s n) k)
      - ∫ σ in (a k)..(a (k + 1)), G σ)‖ ≤ t * η' := by
    refine (norm_sum_le _ _).trans ((Finset.sum_le_sum hpiece).trans ?_)
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    have : (K : ℝ) * (η' * (2 * e)) = η' * a K := by simp only [ha]; ring
    rw [this, mul_comm t]
    exact mul_le_mul_of_nonneg_left haK hη'pos.le
  have htη : t * η' < η / 3 := by
    rw [hη', mul_div_assoc', div_lt_div_iff₀ (by positivity) (by norm_num)]; nlinarith
  rw [dist_eq_norm, hyt, hsplit, ← hsum]
  have hx' : ‖x0s n - ξ‖ < η / 3 := by
    rw [← dist_eq_norm]; exact lt_of_lt_of_le hx (min_le_right _ _)
  have hh' : M * (2 * e) < η / 3 := lt_of_lt_of_le hh (min_le_right _ _)
  have heq : x0s n + ∑ k ∈ Finset.range K, (2 * e) • F (eulerV e F (x0s n) k)
      - (ξ + ((∑ k ∈ Finset.range K, ∫ σ in (a k)..(a (k + 1)), G σ) + ∫ σ in (a K)..t, G σ))
      = (x0s n - ξ) + (∑ k ∈ Finset.range K, ((2 * e) • F (eulerV e F (x0s n) k)
          - ∫ σ in (a k)..(a (k + 1)), G σ)) - ∫ σ in (a K)..t, G σ := by
    rw [Finset.sum_sub_distrib]; abel
  rw [heq]
  calc _ ≤ ‖(x0s n - ξ) + (∑ k ∈ Finset.range K, ((2 * e) • F (eulerV e F (x0s n) k)
          - ∫ σ in (a k)..(a (k + 1)), G σ))‖ + ‖∫ σ in (a K)..t, G σ‖ := norm_sub_le _ _
    _ ≤ ‖x0s n - ξ‖ + ‖∑ k ∈ Finset.range K, ((2 * e) • F (eulerV e F (x0s n) k)
          - ∫ σ in (a k)..(a (k + 1)), G σ)‖ + ‖∫ σ in (a K)..t, G σ‖ := by
        gcongr; exact norm_add_le _ _
    _ < η := by linarith

/-- **Peano existence via the standard part** (book: `thm:ode-existence`).
Hyperreal data are levelwise sequences modulo the hyperfilter: `ε = ofSeq εs` is a
positive infinitesimal, `x₀ = (x0s n)` is finite with `st x₀ = ξ`, and the granular
solution of `D⁺x = F(x)` is `eulerV`, read at the lattice time `⌊t⌋`
(`granOrbit`).  For `F` continuous and bounded by `M` on a finite-dimensional space
(e.g. `ℝ^d`), the shadow `X(t) = st x(⌊t⌋)` (`granShadow`) exists, `X(0) = ξ`, `X` is
`M`-Lipschitz, `X(t) = ξ + ∫₀ᵗ F(X)`, and `X ∈ C¹([0,T])` with `Ẋ = F(X)`. -/
theorem peano_shadow (hF : Continuous F) (hM : ∀ x, ‖F x‖ ≤ M) (hεpos : 0 < ofSeq εs)
    (hεinf : 0 < ArchimedeanClass.mk (ofSeq εs)) (hx0 : Tendsto x0s (hyperfilter ℕ) (𝓝 ξ))
    (T : ℝ) :
    (∀ t ∈ Set.Icc 0 T, Tendsto (fun n => granOrbit εs F x0s n t) (hyperfilter ℕ)
        (𝓝 (granShadow εs F x0s t))) ∧
    granShadow εs F x0s 0 = ξ ∧
    (∀ s ∈ Set.Icc 0 T, ∀ t ∈ Set.Icc 0 T,
        ‖granShadow εs F x0s t - granShadow εs F x0s s‖ ≤ M * |t - s|) ∧
    (∀ t ∈ Set.Icc 0 T,
        granShadow εs F x0s t = ξ + ∫ σ in (0 : ℝ)..t, F (granShadow εs F x0s σ)) ∧
    ContinuousOn (fun t => F (granShadow εs F x0s t)) (Set.Icc 0 T) ∧
    (∀ t ∈ Set.Icc 0 T,
        HasDerivWithinAt (granShadow εs F x0s) (F (granShadow εs F x0s t)) (Set.Icc 0 T) t) := by
  have hG : ContinuousOn (fun t => F (granShadow εs F x0s t)) (Set.Ici 0) :=
    hF.comp_continuousOn (granShadow_continuousOn hεpos hεinf hM hx0)
  have hGc : ContinuousOn (fun t => F (granShadow εs F x0s t)) (Set.Icc 0 T) :=
    hG.mono fun x hx => hx.1
  refine ⟨fun t ht => tendsto_granShadow hεpos hM hx0 ht.1, granShadow_zero hεpos hM hx0,
    fun s hs t ht => granShadow_lip hεpos hεinf hM hx0 hs.1 ht.1,
    fun t ht => granShadow_integral hF hεpos hεinf hM hx0 ht.1, hGc, fun t ht => ?_⟩
  have : Fact (t ∈ Set.Icc 0 T) := ⟨ht⟩
  have hint : IntervalIntegrable (fun t => F (granShadow εs F x0s t)) volume 0 t := by
    refine (hG.mono fun x hx => ?_).intervalIntegrable
    rw [Set.uIcc_of_le ht.1] at hx; exact hx.1
  have hd := intervalIntegral.integral_hasDerivWithinAt_right (s := Set.Icc 0 T)
    (t := Set.Icc 0 T) hint (hGc.stronglyMeasurableAtFilter_nhdsWithin measurableSet_Icc t)
    (hGc t ht)
  exact (hd.const_add ξ).congr (fun x hx => granShadow_integral hF hεpos hεinf hM hx0 hx.1)
    (granShadow_integral hF hεpos hεinf hM hx0 ht.1)

end PeanoHyp

/-- For scalar equations the shadow is literally Mathlib's standard part of the
hyperreal `x(⌊t⌋) = ofSeq (levels)`. -/
theorem granShadow_eq_stdPart {εs : ℕ → ℝ} (hεpos : 0 < ofSeq εs) {F : ℝ → ℝ} {M : ℝ}
    (hM : ∀ x, ‖F x‖ ≤ M) {x0s : ℕ → ℝ} {ξ : ℝ} (hx0 : Tendsto x0s (hyperfilter ℕ) (𝓝 ξ))
    {t : ℝ} (ht : 0 ≤ t) :
    granShadow εs F x0s t = ArchimedeanClass.stdPart (ofSeq (fun n => granOrbit εs F x0s n t)) :=
  (stdPart_of_tendsto (tendsto_ofSeq.mpr (tendsto_granShadow hεpos hM hx0 ht))).symm

end Peano

end QE.AnalysisInfra
