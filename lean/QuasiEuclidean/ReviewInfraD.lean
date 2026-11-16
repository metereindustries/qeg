-- SPDX-License-Identifier: MIT
-- Copyright 2026 Metere Industries, Inc. Author: Alfredo Metere.
-- Quasi-Euclidean Granular Geometry. Any derivative work must carry this notice:
--   This work is derivative of the Quasi-Euclidean Granular Geometry book
--   authored by Alfredo Metere. Copyright 2026 Metere Industries, Inc.
--   All rights reserved
-- See LICENSE.md and NOTICE.

import QuasiEuclidean.AnalysisInfra
import QuasiEuclidean.Ch04_Diff
import QuasiEuclidean.Ch11_Prob
import QuasiEuclidean.Ch12_Stat
import QuasiEuclidean.Ch13_Stoch
import QuasiEuclidean.OpenSto
import QuasiEuclidean.NSA_Loeb

/-!
# Review infrastructure D: probability, statistics, stochastic processes

Lean statements closing the gaps between the printed statements of
chapters 11–13 and their earlier formalisations:

* `thm:prob-exponential` (iii): `D⁺ f = -λ f` exactly and the shadow
  `f(t) ≃ λ e^{-λ st t}`.
* `thm:prob-random-rational`: hyperrationality (i), the reduced-denominator
  form and the union bound of (ii), the Loeb-almost-sure infinitude of the
  denominator, and (iii), all for the uniform law on `(0,1] ∩ 𝕃`.
* `thm:prob-birthday`: the exponential bound for hyperfinite `n, N`.
* `thm:stat-fisher-metric` (i): positive definiteness iff linear independence.
* `thm:stat-likelihood` (c) for `ε ≥ 0`.
* `thm:stoch-fk`: the explicit path sum, `v = u` for `g ≡ 1`, and the
  imaginary-time Schrödinger form for `g = e^{-Vτ}`.
-/

set_option linter.unusedSectionVars false

open Finset Filter Topology

/-! ## Chapter 11: the granular exponential law -/

namespace QE.Prob

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-- On the lattice, the waiting-time density `f(2εk) = λ(1-2ελ)^k` solves
`D⁺ f = -λ f` exactly. -/
theorem expDensity_Dp_lattice (ε lam : K) (hε : ε ≠ 0) (k : ℕ) :
    (lam * (1 - 2 * ε * lam) ^ (k + 1) - lam * (1 - 2 * ε * lam) ^ k) / (2 * ε)
      = -lam * (lam * (1 - 2 * ε * lam) ^ k) := by
  field_simp
  ring

/-- The granular exponential density `f(t) = λ (1 - 2ελ)^{t/(2ε)}` at every real `t`. -/
noncomputable def expDens (ε lam t : ℝ) : ℝ := lam * (1 - 2 * ε * lam) ^ (t / (2 * ε))

/-- On the lattice `f(2εk) = λ(1-2ελ)^k`, so `P(T = 2εk) = f(2εk)·2ε` (`geom_density`). -/
theorem expDens_centre (ε lam : ℝ) (hε : 0 < ε) (k : ℕ) :
    expDens ε lam (2 * ε * k) = lam * (1 - 2 * ε * lam) ^ k := by
  unfold expDens
  have : 2 * ε * (k : ℝ) / (2 * ε) = (k : ℝ) := by field_simp
  rw [this, Real.rpow_natCast]

/-- `D⁺ f = -λ f` exactly, at every real `t`, whenever `2ελ < 1`. -/
theorem Dp_expDens (ε lam : ℝ) (hε : 0 < ε) (h : 2 * ε * lam < 1) (t : ℝ) :
    QE.Dp ε (expDens ε lam) t = -lam * expDens ε lam t := by
  unfold QE.Dp expDens
  have h1 : (0 : ℝ) < 1 - 2 * ε * lam := by linarith
  have e : (t + 2 * ε) / (2 * ε) = t / (2 * ε) + 1 := by field_simp
  rw [e, Real.rpow_add_one h1.ne']
  field_simp
  ring

lemma tendsto_log_one_sub_ratio (lam : ℝ) :
    Tendsto (fun ε : ℝ => Real.log (1 - 2 * ε * lam) / (2 * ε)) (𝓝[>] 0) (𝓝 (-lam)) := by
  rcases eq_or_ne lam 0 with rfl | hlam
  · simp
  have hd := (Real.hasDerivAt_log (one_ne_zero (α := ℝ))).tendsto_slope_zero
  simp only [Real.log_one, sub_zero, smul_eq_mul, inv_one] at hd
  have hg : Tendsto (fun ε : ℝ => -(2 * ε * lam)) (𝓝[>] 0) (𝓝[≠] 0) := by
    apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
    · have : Tendsto (fun ε : ℝ => -(2 * ε * lam)) (𝓝 0) (𝓝 (-(2 * 0 * lam))) :=
        ((continuous_const.mul continuous_id).mul continuous_const).neg.tendsto 0
      simpa using this.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with ε hε
      have : (0 : ℝ) < ε := hε
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff, neg_eq_zero]
      exact mul_ne_zero (by positivity) hlam
  have := (hd.comp hg).const_mul (-lam)
  rw [mul_one] at this
  refine this.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with ε hε
  have : (0 : ℝ) < ε := hε
  simp only [Function.comp]
  rw [show 1 + -(2 * ε * lam) = 1 - 2 * ε * lam by ring]
  field_simp

/-- **Shadow of the granular exponential law**: if `t_ε → t₀` then
`f_ε(t_ε) → λ e^{-λ t₀}` as `ε → 0⁺`, i.e. `f(t) ≃ λ e^{-λ st t}` for finite `t`. -/
theorem expDens_shadow (lam : ℝ) (t : ℝ → ℝ) (t₀ : ℝ) (ht : Tendsto t (𝓝[>] 0) (𝓝 t₀)) :
    Tendsto (fun ε => expDens ε lam (t ε)) (𝓝[>] 0) (𝓝 (lam * Real.exp (-lam * t₀))) := by
  have h : Tendsto (fun ε => lam * Real.exp (Real.log (1 - 2 * ε * lam) / (2 * ε) * t ε))
      (𝓝[>] 0) (𝓝 (lam * Real.exp (-lam * t₀))) :=
    ((Real.continuous_exp.tendsto _).comp ((tendsto_log_one_sub_ratio lam).mul ht)).const_mul lam
  refine h.congr' ?_
  have hsmall : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < 1 - 2 * ε * lam := by
    have : Tendsto (fun ε : ℝ => 1 - 2 * ε * lam) (𝓝[>] 0) (𝓝 (1 - 2 * 0 * lam)) :=
      (continuous_const.sub ((continuous_const.mul continuous_id).mul continuous_const)).tendsto 0
        |>.mono_left nhdsWithin_le_nhds
    simp only [mul_zero, zero_mul, sub_zero] at this
    exact this.eventually (lt_mem_nhds one_pos)
  filter_upwards [self_mem_nhdsWithin, hsmall] with ε hε h1
  have : (0 : ℝ) < ε := hε
  unfold expDens
  rw [Real.rpow_def_of_pos h1]
  congr 2; ring

/-- `thm:prob-exponential` (iii) in one statement. -/
theorem exponential_density_shadow (lam : ℝ) :
    (∀ ε : ℝ, 0 < ε → ∀ k : ℕ, expDens ε lam (2 * ε * k) * (2 * ε)
        = (2 * ε * lam) * (1 - 2 * ε * lam) ^ k) ∧
    (∀ ε : ℝ, 0 < ε → 2 * ε * lam < 1 → ∀ t, QE.Dp ε (expDens ε lam) t = -lam * expDens ε lam t) ∧
    (∀ (t : ℝ → ℝ) (t₀ : ℝ), Tendsto t (𝓝[>] 0) (𝓝 t₀) →
      Tendsto (fun ε => expDens ε lam (t ε)) (𝓝[>] 0) (𝓝 (lam * Real.exp (-lam * t₀)))) :=
  ⟨fun ε hε k => by rw [expDens_centre ε lam hε k, geom_density],
    fun ε hε h t => Dp_expDens ε lam hε h t, fun t t₀ ht => expDens_shadow lam t t₀ ht⟩

/-! ## Chapter 11: is a random lattice point rational? -/

/-- (i) Every point `k/N` of the hyperfinite lattice is hyperrational:
`[k_n / N_n] ∈ *ℚ`. -/
theorem lattice_hyperrational (N : ℕ → ℕ) (k : ℕ → ℤ) :
    Hyperreal.ofSeq (fun n => (k n : ℝ) / N n) ∈ QE.NSA.starSet (Set.range ((↑) : ℚ → ℝ)) :=
  (QE.NSA.mem_starSet _ _).2 (Eventually.of_forall fun n => ⟨(k n : ℚ) / N n, by push_cast; rfl⟩)

/-- The reduced denominator of `k/(dm)` divides `m` iff `d ∣ k`. -/
theorem den_dvd_iff (d m k : ℕ) (hd : 0 < d) (hm : 0 < m) :
    ((k : ℚ) / ((d * m : ℕ) : ℚ)).den ∣ m ↔ d ∣ k := by
  set q : ℚ := (k : ℚ) / ((d * m : ℕ) : ℚ) with hq
  have hd' : (d : ℚ) ≠ 0 := by exact_mod_cast hd.ne'
  have hm' : (m : ℚ) ≠ 0 := by exact_mod_cast hm.ne'
  constructor
  · rintro ⟨c, hc⟩
    -- `q * m = num * c` is an integer, and `q * m = k / d`.
    have h1 : q * m = q.num * c := by
      have := Rat.mul_den_eq_num q
      rw [hc]; push_cast
      rw [← this]; ring
    have h2 : q * m = (k : ℚ) / d := by rw [hq]; push_cast; field_simp
    have h3 : (k : ℚ) = d * (q.num * c) := by rw [← h1, h2]; field_simp
    have h4 : (k : ℤ) = d * (q.num * c) := by exact_mod_cast h3
    have : (d : ℤ) ∣ (k : ℤ) := ⟨_, h4⟩
    exact_mod_cast this
  · rintro ⟨j, rfl⟩
    have : q = (j : ℤ) / ((m : ℤ) : ℚ) := by rw [hq]; push_cast; field_simp
    rw [this, ← Rat.divInt_eq_div]
    have := Rat.den_dvd (j : ℤ) (m : ℤ)
    exact_mod_cast this

/-- (ii) exact: if `N = dm`, the probability that the reduced denominator of the uniform
point `k/N` of `(0,1] ∩ 𝕃` divides `m` is exactly `m/N`. -/
theorem prob_den_dvd_reduced (d m : ℕ) (hd : 0 < d) (hm : 0 < m) :
    prob (Icc 1 (d * m)) (unif (Icc 1 (d * m)))
        (fun k : ℕ => ((k : ℚ) / ((d * m : ℕ) : ℚ)).den ∣ m)
      = (m : K) / ((d * m : ℕ) : K) := by
  rw [← prob_den_dvd (K := K) d m hd]
  unfold prob
  congr 1
  exact Finset.filter_congr fun k _ => den_dvd_iff d m k hd hm

/-- A point `k/N` with reduced denominator `m` satisfies `N ∣ m k`. -/
theorem dvd_of_den_eq (N k m : ℕ) (hN : 0 < N) (h : ((k : ℚ) / N).den = m) : N ∣ m * k := by
  set q : ℚ := (k : ℚ) / N with hq
  have hN' : (N : ℚ) ≠ 0 := by exact_mod_cast hN.ne'
  have h1 : q * m = q.num := by rw [← h]; exact Rat.mul_den_eq_num q
  have h2 : ((m * k : ℕ) : ℚ) = N * q.num := by rw [← h1, hq]; push_cast; field_simp
  have h3 : ((m * k : ℕ) : ℤ) = N * q.num := by exact_mod_cast h2
  have : (N : ℤ) ∣ ((m * k : ℕ) : ℤ) := ⟨_, h3⟩
  exact_mod_cast this

/-- At most `m` of the points `k/N`, `1 ≤ k ≤ N`, have reduced denominator `m`. -/
theorem card_den_eq_le (N m : ℕ) (hN : 0 < N) :
    ((Icc 1 N).filter (fun k : ℕ => ((k : ℚ) / N).den = m)).card ≤ m := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · have : (Icc 1 N).filter (fun k : ℕ => ((k : ℚ) / N).den = 0) = ∅ := by
      ext k; simp [Rat.den_ne_zero]
    rw [this]; simp
  calc ((Icc 1 N).filter (fun k : ℕ => ((k : ℚ) / N).den = m)).card
      ≤ (Icc 1 m).card := by
        refine Finset.card_le_card_of_injOn (fun k => m * k / N) ?_ ?_
        · intro k hk
          simp only [coe_filter, Set.mem_ofPred_eq, mem_Icc] at hk
          obtain ⟨⟨hk1, hkN⟩, hden⟩ := hk
          obtain ⟨c, hc⟩ := dvd_of_den_eq N k m hN hden
          simp only [coe_Icc, Set.mem_Icc]
          rw [hc, Nat.mul_div_cancel_left _ hN]
          constructor
          · rcases Nat.eq_zero_or_pos c with rfl | hc0
            · have : m * k = 0 := by rw [hc]; ring
              have : 0 < m * k := Nat.mul_pos hm hk1
              omega
            · exact hc0
          · have : N * c ≤ N * m := by rw [← hc]; nlinarith
            exact Nat.le_of_mul_le_mul_left this hN
        · intro k₁ hk₁ k₂ hk₂ heq
          simp only [coe_filter, Set.mem_ofPred_eq] at hk₁ hk₂
          obtain ⟨c₁, hc₁⟩ := dvd_of_den_eq N k₁ m hN hk₁.2
          obtain ⟨c₂, hc₂⟩ := dvd_of_den_eq N k₂ m hN hk₂.2
          simp only at heq
          rw [hc₁, hc₂, Nat.mul_div_cancel_left _ hN, Nat.mul_div_cancel_left _ hN] at heq
          have : m * k₁ = m * k₂ := by rw [hc₁, hc₂, heq]
          exact Nat.eq_of_mul_eq_mul_left hm this
    _ = m := by simp

/-- (ii) the union bound: `P(den X ≤ B) ≤ ∑_{m ≤ B} m/N ≤ B²/N` for the uniform point
`X = k/N` of `(0,1] ∩ 𝕃` (no divisibility hypothesis on `N` is needed). -/
theorem prob_den_le (N B : ℕ) (hN : 0 < N) :
    prob (Icc 1 N) (unif (Icc 1 N)) (fun k : ℕ => ((k : ℚ) / N).den ≤ B)
        ≤ ∑ m ∈ Icc 1 B, (m : K) / N ∧
      ∑ m ∈ Icc 1 B, (m : K) / N ≤ (B : K) ^ 2 / N := by
  have hN' : (0 : K) < N := by exact_mod_cast hN
  refine ⟨?_, ?_⟩
  · rw [prob_unif, Nat.card_Icc, Nat.add_sub_cancel, ← sum_div]
    refine div_le_div_of_nonneg_right ?_ hN'.le
    have hsub : (Icc 1 N).filter (fun k : ℕ => ((k : ℚ) / N).den ≤ B) ⊆
        (Icc 1 B).biUnion (fun m => (Icc 1 N).filter (fun k : ℕ => ((k : ℚ) / N).den = m)) := by
      intro k hk
      simp only [mem_filter] at hk
      simp only [mem_biUnion, mem_filter, mem_Icc]
      exact ⟨_, ⟨Nat.pos_of_ne_zero (Rat.den_ne_zero _), hk.2⟩, mem_Icc.1 hk.1, rfl⟩
    have h1 := (card_le_card hsub).trans card_biUnion_le
    have h2 : (((Icc 1 N).filter (fun k : ℕ => ((k : ℚ) / N).den ≤ B)).card : K)
        ≤ ∑ m ∈ Icc 1 B, (((Icc 1 N).filter (fun k : ℕ => ((k : ℚ) / N).den = m)).card : K) := by
      exact_mod_cast h1
    refine h2.trans (sum_le_sum fun m _ => ?_)
    exact_mod_cast card_den_eq_le N m hN
  · rw [← sum_div]
    refine div_le_div_of_nonneg_right ?_ hN'.le
    calc ∑ m ∈ Icc 1 B, (m : K) ≤ ∑ _m ∈ Icc 1 B, (B : K) :=
          sum_le_sum fun m hm => by exact_mod_cast (mem_Icc.1 hm).2
      _ = (B : K) ^ 2 := by rw [sum_const, Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul]; ring

end QE.Prob

/-! ## Chapter 11: the birthday bound for hyperfinite `n, N` -/

namespace QE.Prob

open QE.NSA

/-- `thm:prob-birthday` for hyperfinite `n = [n_i] ≤ N = [N_i]`: with `*exp` the
transferred exponential,
`P(no tie) ≤ *exp(-n(n-1)/(2N))` and `1 - *exp(-n(n-1)/(2N)) ≤ P(some tie)`. -/
theorem no_tie_le_exp_hyper (n N : ℕ → ℕ) (hN : ∀ᶠ i in (hyperfilter ℕ : Filter ℕ), 0 < N i)
    (h : ∀ᶠ i in (hyperfilter ℕ : Filter ℕ), n i ≤ N i) :
    Hyperreal.ofSeq (fun i => prob (univ : Finset (Fin (n i) → Fin (N i))) (unif univ)
        Function.Injective)
      ≤ hfun (fun _ => Real.exp) (Hyperreal.ofSeq fun i => -((n i : ℝ) * (n i - 1) / (2 * N i))) ∧
    1 - hfun (fun _ => Real.exp) (Hyperreal.ofSeq fun i => -((n i : ℝ) * (n i - 1) / (2 * N i)))
      ≤ 1 - Hyperreal.ofSeq (fun i => prob (univ : Finset (Fin (n i) → Fin (N i))) (unif univ)
        Function.Injective) := by
  have key : Hyperreal.ofSeq (fun i => prob (univ : Finset (Fin (n i) → Fin (N i))) (unif univ)
        Function.Injective)
      ≤ hfun (fun _ => Real.exp) (Hyperreal.ofSeq fun i => -((n i : ℝ) * (n i - 1) / (2 * N i))) := by
    rw [hfun_ofSeq]
    refine Hyperreal.ofSeq_le_ofSeq.2 ?_
    filter_upwards [hN, h] with i h1 h2
    exact no_tie_le_exp (n i) (N i) h1 h2
  exact ⟨key, by linarith⟩

end QE.Prob

/-! ## Chapter 11: Loeb statements for the uniform law on `(0,1] ∩ 𝕃` -/

namespace QE.Prob

open QE.NSA MeasureTheory

/-- The points `k/N`, `1 ≤ k ≤ N`, of `(0,1] ∩ 𝕃`. -/
noncomputable def ocPoints (N : ℕ → ℕ) (n : ℕ) : Finset ℝ :=
  (Icc 1 (N n)).image (fun k : ℕ => (k : ℝ) / N n)

/-- The uniform law of `X` on `(0,1] ∩ 𝕃` (a hyperfinite counting probability). -/
noncomputable def ocUniform (N : ℕ → ℕ) : HypMeasure ℝ := HypMeasure.counting (ocPoints N)

theorem card_ocPoints (N : ℕ → ℕ) {n : ℕ} (hN : 0 < N n) : (ocPoints N n).card = N n := by
  unfold ocPoints
  rw [card_image_of_injective _ (fun k₁ k₂ h => by
    have hN' : (N n : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
    have : (k₁ : ℝ) = k₂ := by
      have := congrArg (· * (N n : ℝ)) h
      simpa [div_mul_cancel₀ _ hN'] using this
    exact_mod_cast this), Nat.card_Icc, Nat.add_sub_cancel]

/-- The internal event `{denominator of X ≤ B}`. -/
def denLe (N : ℕ → ℕ) (B : ℕ) : Set (Ult ℝ) :=
  internal (fun n => {x : ℝ | ∃ k ∈ Icc 1 (N n), x = (k : ℝ) / N n ∧ ((k : ℚ) / N n).den ≤ B})

theorem seqMass_le_card_div {N : ℕ → ℕ} {n : ℕ} (hN : 0 < N n) (A : Set ℝ) (P : ℕ → Prop)
    [DecidablePred P] (hA : ∀ k ∈ Icc 1 (N n), (k : ℝ) / N n ∈ A → P k) :
    (ocUniform N).seqMass (fun _ => A) n ≤ (((Icc 1 (N n)).filter P).card : ℝ) / N n := by
  classical
  unfold HypMeasure.seqMass
  simp only [ocUniform, HypMeasure.counting]
  rw [sum_const, nsmul_eq_mul, card_ocPoints N hN, mul_one_div]
  refine div_le_div_of_nonneg_right ?_ (Nat.cast_nonneg _)
  have : (@Finset.filter _ (· ∈ A) (Classical.decPred _) (ocPoints N n)) ⊆
      ((Icc 1 (N n)).filter P).image (fun k : ℕ => (k : ℝ) / N n) := by
    intro x hx
    rw [mem_filter] at hx
    obtain ⟨⟨k, hk, rfl⟩, hxA⟩ := (mem_image.1 hx.1), hx.2
    exact mem_image.2 ⟨k, mem_filter.2 ⟨hk, hA k hk hxA⟩, rfl⟩
  exact_mod_cast (card_le_card this).trans card_image_le

/-- **Loeb-almost surely the denominator of `X` is infinite**: the union over standard
`B` of the events `{den X ≤ B}` is Loeb-null, for every unlimited `N`. -/
theorem loeb_den_finite_null {N : ℕ → ℕ} (hN : IsUnlimited ((N : ℕ → ℕ) : Ult ℕ)) :
    (ocUniform N).loeb (⋃ B : ℕ, denLe N B) = 0 := by
  refine measure_iUnion_null fun B => ?_
  have hpos : ∀ᶠ n in (hyperfilter ℕ : Filter ℕ), 0 < N n := Germ.coe_lt.1 (hN 0)
  rw [denLe, HypMeasure.loeb_internal _ (isInternal_internal _), HypMeasure.mass_internal]
  rw [show (0 : ENNReal) = ENNReal.ofReal 0 by simp]
  refine stE_of_isInfinitesimal_sub (isInfinitesimal_ofSeq_sub_of_tendsto ?_)
  have hlim : Tendsto (fun n => (B : ℝ) ^ 2 * ((N n : ℝ))⁻¹) (hyperfilter ℕ : Filter ℕ) (𝓝 0) := by
    simpa using (tendsto_inv_of_isUnlimited hN).const_mul ((B : ℝ) ^ 2)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim
    (Eventually.of_forall fun n => (ocUniform N).seqMass_nonneg _ n) ?_
  filter_upwards [hpos] with n hn
  have h1 := seqMass_le_card_div (N := N) hn
    {x : ℝ | ∃ k ∈ Icc 1 (N n), x = (k : ℝ) / N n ∧ ((k : ℚ) / N n).den ≤ B}
    (fun k : ℕ => ((k : ℚ) / N n).den ≤ B) (by
      rintro k hk ⟨k', hk', he, hd⟩
      have hN' : (N n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
      have : (k : ℝ) = k' := by
        have := congrArg (· * (N n : ℝ)) he
        simpa [div_mul_cancel₀ _ hN'] using this
      have : k = k' := by exact_mod_cast this
      rw [this]; exact hd)
  have h2 := (prob_den_le (K := ℝ) (N n) B hn)
  rw [prob_unif, Nat.card_Icc, Nat.add_sub_cancel] at h2
  calc (ocUniform N).seqMass _ n ≤ _ := h1
    _ ≤ (B : ℝ) ^ 2 / N n := h2.1.trans h2.2
    _ = _ := by rw [div_eq_mul_inv]

/-- Counting bound: at most `(b-a)N + 1` of the points `k/N`, `1 ≤ k ≤ N`, lie in `[a,b]`. -/
theorem card_filter_oc_le (N : ℕ) (hN : 0 < N) {a b : ℝ} (hab : a ≤ b) :
    (((Icc 1 N).filter (fun k : ℕ => a ≤ (k : ℝ) / N ∧ (k : ℝ) / N ≤ b)).card : ℝ)
      ≤ (b - a) * N + 1 := by
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have hle : ((Icc 1 N).filter (fun k : ℕ => a ≤ (k : ℝ) / N ∧ (k : ℝ) / N ≤ b)).card ≤
      (Finset.Icc ⌈a * N⌉ ⌊b * N⌋).card := by
    refine card_le_card_of_injOn (fun k : ℕ => (k : ℤ)) ?_ (fun x _ y _ h => by simpa using h)
    intro k hk
    simp only [coe_filter, Set.mem_ofPred_eq] at hk
    simp only [coe_Icc, Set.mem_Icc]
    rw [div_le_iff₀ hN', le_div_iff₀ hN'] at *
    exact ⟨Int.ceil_le.2 (by push_cast; linarith [hk.2.1]),
      Int.le_floor.2 (by push_cast; linarith [hk.2.2])⟩
  have hc : ((Finset.Icc ⌈a * N⌉ ⌊b * N⌋).card : ℝ) ≤ (b - a) * N + 1 := by
    rw [Int.card_Icc]
    have h1 : ((((⌊b * N⌋ + 1 - ⌈a * N⌉).toNat : ℕ) : ℤ) : ℝ) =
        ((max (⌊b * N⌋ + 1 - ⌈a * N⌉) 0 : ℤ) : ℝ) := by rw [Int.toNat_eq_max]
    have h2 : (((⌊b * N⌋ + 1 - ⌈a * N⌉).toNat : ℕ) : ℝ) =
        max ((⌊b * N⌋ : ℝ) + 1 - ⌈a * N⌉) 0 := by
      push_cast at h1; exact_mod_cast h1
    rw [h2]
    have := Int.floor_le (b * N)
    have := Int.le_ceil (a * N)
    have : 0 ≤ (b - a) * N := mul_nonneg (by linarith) hN'.le
    refine max_le ?_ (by linarith)
    nlinarith
  exact (by exact_mod_cast hle : (_ : ℝ) ≤ _).trans hc

/-- A single standard real has Loeb-null monad: `L(st⁻¹{r}) = 0`. -/
theorem loeb_stInv_singleton {N : ℕ → ℕ} (hN : IsUnlimited ((N : ℕ → ℕ) : Ult ℕ)) (r : ℝ) :
    (ocUniform N).loeb (stInv ({r} : Set ℝ)) = 0 := by
  have hpos : ∀ᶠ n in (hyperfilter ℕ : Filter ℕ), 0 < N n := Germ.coe_lt.1 (hN 0)
  refine le_antisymm (ENNReal.le_of_forall_pos_le_add fun δ hδ _ => ?_) bot_le
  rw [zero_add]
  set t : ℝ := (δ : ℝ) / 3 with ht
  have ht0 : 0 < t := by have : (0 : ℝ) < δ := hδ; positivity
  -- the monad of `r` lies in `*[r - t, r + t]`
  have hsub : stInv ({r} : Set ℝ) ⊆ starSet (Set.Icc (r - t) (r + t)) := by
    rintro x ⟨y, rfl, hy⟩
    obtain ⟨u, rfl⟩ := exists_rep x
    rw [near_const_iff_tendsto] at hy
    refine (mem_starSet _ u).2 ?_
    have := hy (Icc_mem_nhds (show y - t < y by linarith) (show y < y + t by linarith))
    exact this
  calc (ocUniform N).loeb (stInv {r}) ≤ (ocUniform N).loeb (starSet (Set.Icc (r - t) (r + t))) :=
        measure_mono hsub
    _ = stE ((ocUniform N).mass (starSet (Set.Icc (r - t) (r + t)))) :=
        HypMeasure.loeb_internal _ (isInternal_starSet _)
    _ ≤ ENNReal.ofReal (3 * t) := by
        refine stE_le_of_le ((ocUniform N).mass_nonneg _) ?_
        rw [starSet, HypMeasure.mass_internal]
        refine ofSeq_le_const.2 ?_
        have hsmall : ∀ᶠ n in (hyperfilter ℕ : Filter ℕ), ((N n : ℝ))⁻¹ < t :=
          (tendsto_inv_of_isUnlimited hN).eventually (gt_mem_nhds ht0)
        filter_upwards [hpos, hsmall] with n hn hs
        have hN' : (0 : ℝ) < N n := by exact_mod_cast hn
        have h1 := seqMass_le_card_div (N := N) hn (Set.Icc (r - t) (r + t))
          (fun k : ℕ => r - t ≤ (k : ℝ) / N n ∧ (k : ℝ) / N n ≤ r + t) (fun k _ hk => hk)
        have h2 := card_filter_oc_le (N n) hn (show r - t ≤ r + t by linarith)
        calc _ ≤ _ := h1
          _ ≤ ((r + t - (r - t)) * N n + 1) / N n := div_le_div_of_nonneg_right h2 hN'.le
          _ = 2 * t + (N n : ℝ)⁻¹ := by field_simp; ring
          _ ≤ 3 * t := by linarith
    _ = δ := by rw [ht]; rw [show 3 * ((δ : ℝ) / 3) = δ by ring]; simp

/-- (iii) `L(st X ∈ ℚ) = 0` for `X` uniform on `(0,1] ∩ 𝕃`, `N` unlimited. -/
theorem loeb_st_rational_null {N : ℕ → ℕ} (hN : IsUnlimited ((N : ℕ → ℕ) : Ult ℕ)) :
    (ocUniform N).loeb (stInv (Set.range ((↑) : ℚ → ℝ))) = 0 := by
  rw [← Set.iUnion_singleton_eq_range, stInv_iUnion]
  exact measure_iUnion_null fun q => loeb_stInv_singleton hN (q : ℝ)

/-- `thm:prob-random-rational` in one statement. -/
theorem random_rational :
    (∀ (N : ℕ → ℕ) (k : ℕ → ℤ),
      Hyperreal.ofSeq (fun n => (k n : ℝ) / N n) ∈ starSet (Set.range ((↑) : ℚ → ℝ))) ∧
    (∀ d m : ℕ, 0 < d → 0 < m →
      prob (Icc 1 (d * m)) (unif (Icc 1 (d * m)))
        (fun k : ℕ => ((k : ℚ) / ((d * m : ℕ) : ℚ)).den ∣ m) = (m : ℝ) / ((d * m : ℕ) : ℝ)) ∧
    (∀ N B : ℕ, 0 < N →
      prob (Icc 1 N) (unif (Icc 1 N)) (fun k : ℕ => ((k : ℚ) / N).den ≤ B)
        ≤ ∑ m ∈ Icc 1 B, (m : ℝ) / N ∧ ∑ m ∈ Icc 1 B, (m : ℝ) / N ≤ (B : ℝ) ^ 2 / N) ∧
    (∀ N : ℕ → ℕ, IsUnlimited ((N : ℕ → ℕ) : Ult ℕ) →
      (ocUniform N).loeb (⋃ B : ℕ, denLe N B) = 0 ∧
      (ocUniform N).loeb (stInv (Set.range ((↑) : ℚ → ℝ))) = 0) :=
  ⟨lattice_hyperrational, fun d m hd hm => prob_den_dvd_reduced d m hd hm,
    fun N B hN => prob_den_le N B hN,
    fun _ hN => ⟨loeb_den_finite_null hN, loeb_st_rational_null hN⟩⟩

end QE.Prob

/-! ## Chapter 12: the granular likelihood and the Fisher metric -/

namespace QE.Stat

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-- `thm:stat-likelihood` (c) for every `ε ≥ 0`: a granular density is bounded by
`1/(2ε)ⁿ` (for `ε = 0`, `n ≥ 1` the hypothesis is void). -/
theorem density_le_inv_nonneg {ι : Type*} (n : ℕ) (ε : K) (f : ι → K) (s : Finset ι)
    (hf0 : ∀ x ∈ s, 0 ≤ f x) (hε : 0 ≤ ε) (hf : ∑ x ∈ s, f x * (2 * ε) ^ n = 1)
    {x : ι} (hx : x ∈ s) : f x ≤ 1 / (2 * ε) ^ n := by
  have h := grain_prob_le_one n ε f s hf0 hε hf hx
  rcases (pow_nonneg (by linarith : (0 : K) ≤ 2 * ε) n).lt_or_eq with hp | hp
  · rw [le_div_iff₀ hp]; exact h
  · exfalso
    simp only [← hp, mul_zero, sum_const_zero] at hf
    exact zero_ne_one hf

end QE.Stat

namespace QE.OpenSto.InfoGeo

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
variable {S : Type*} [Fintype S] {d : ℕ}

/-- `thm:stat-fisher-metric` (i): the granular Fisher metric is positive definite iff
the `d` vectors `(Δ_a p_θ(x))_{x ∈ S}` are linearly independent. -/
theorem metric_posDef_iff (h : K) (p : (Fin d → ℤ) → S → K) (θ : Fin d → ℤ)
    (hp : ∀ x, 0 < p θ x) :
    (∀ v : Fin d → K, v ≠ 0 → 0 < ∑ a, ∑ b, v a * v b * metric h p a b θ) ↔
      LinearIndependent K (fun a : Fin d => fun x : S => D h p a θ x) := by
  rw [Fintype.linearIndependent_iff]
  have hzero : ∀ v : Fin d → K, ∑ a, ∑ b, v a * v b * metric h p a b θ = 0 ↔
      ∑ a, v a • (fun x : S => D h p a θ x) = 0 := by
    intro v
    rw [metric_quadratic_form, Finset.sum_eq_zero_iff_of_nonneg
      (fun x _ => div_nonneg (sq_nonneg _) (hp x).le)]
    constructor
    · intro hv; funext x
      have := hv x (mem_univ x)
      rw [div_eq_zero_iff, or_iff_left (hp x).ne', pow_eq_zero_iff two_ne_zero] at this
      simpa [Finset.sum_apply] using this
    · intro hv x _
      have := congrFun hv x
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at this
      rw [this]; simp
  constructor
  · intro hpos v hv
    by_contra hne
    have hv0 : v ≠ 0 := fun h0 => hne (fun i => by rw [h0]; rfl)
    have := hpos v hv0
    rw [(hzero v).2 hv] at this
    exact lt_irrefl _ this
  · intro hli v hv
    refine lt_of_le_of_ne (metric_psd h p θ hp v) (fun h0 => hv ?_)
    funext i
    exact hli v ((hzero v).1 h0.symm) i

end QE.OpenSto.InfoGeo

/-! ## Chapter 13: Feynman–Kac -/

namespace QE.Stoch

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-- The walk after the first coin: `W_{j+1}(ω) = ξ₀ s + W_j(tail ω)`. -/
theorem W_succ_tail {k : ℕ} (s : K) (ω : Fin (k + 1) → Bool) (j : ℕ) :
    W s ω (j + 1) = sgn (ω 0) * s + W s (Fin.tail ω) j := by
  unfold W
  rw [Finset.sum_filter, Finset.sum_filter, Fin.sum_univ_succ]
  simp only [Fin.val_zero, Nat.zero_lt_succ, ite_true, Fin.val_succ, Fin.tail]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  by_cases hi : (i : ℕ) < j
  · rw [ite_eq_left_of_eq_true _ _ (eq_true (by omega)), ite_eq_left_of_eq_true _ _ (eq_true hi)]
  · rw [ite_eq_right_of_eq_false _ _ (eq_false (by omega)), ite_eq_right_of_eq_false _ _ (eq_false hi)]

theorem W_zero' {k : ℕ} (s : K) (ω : Fin k → Bool) : W s ω 0 = 0 := by
  unfold W; simp

/-- **The Feynman–Kac path functional, explicitly**:
`F_k(ω, x) = f(x + W_k) ∏_{j<k} g(x + W_j)`. -/
theorem pathFK_eq_prod (s : K) (f g : K → K) (k : ℕ) (ω : Fin k → Bool) (x : K) :
    pathFK s f g k ω x = f (x + S ω * s) * ∏ j : Fin k, g (x + W s ω j) := by
  induction k generalizing x with
  | zero => simp [pathFK, S]
  | succ k ih =>
    simp only [pathFK, ih, Fin.prod_univ_succ, Fin.val_zero, W_zero', add_zero,
      Fin.val_succ, W_succ_tail]
    have hS : (S ω : K) = sgn (ω 0) + S (Fin.tail ω) := by
      simp only [S, Fin.sum_univ_succ, Fin.tail]
    rw [hS]
    have e1 : x + sgn (ω 0) * s + S (Fin.tail ω) * s = x + (sgn (ω 0) + S (Fin.tail ω)) * s := by
      ring
    have e2 : ∀ i : Fin k, x + sgn (ω 0) * s + W s (Fin.tail ω) i =
        x + (sgn (ω 0) * s + W s (Fin.tail ω) i) := fun i => by ring
    simp only [e1, e2]
    ring

/-- `v = u` when `g ≡ 1`. -/
theorem vFK_one (s : K) (f : K → K) (k : ℕ) (x : K) :
    vFK s f (fun _ => 1) k x = u s f k x := by
  unfold vFK u
  simp only [pathFK_one]

open Real in
/-- **Granular imaginary-time Schrödinger equation**: with `s = 2ε`, `τ = (2ε)²` and
`g = e^{-Vτ}`, `v(k+1,x) = e^{-V(x)τ} (v(k,x) + ½ D⁺D⁻ v(k,·)(x) τ)`. -/
theorem fk_schrodinger (ε : ℝ) (hε : ε ≠ 0) (f V : ℝ → ℝ) (k : ℕ) (x : ℝ) :
    vFK (2 * ε) f (fun y => exp (-V y * (2 * ε) ^ 2)) (k + 1) x =
      exp (-V x * (2 * ε) ^ 2) *
        (vFK (2 * ε) f (fun y => exp (-V y * (2 * ε) ^ 2)) k x +
          QE.Dp ε (QE.Dm ε (vFK (2 * ε) f (fun y => exp (-V y * (2 * ε) ^ 2)) k)) x / 2 *
            (2 * ε) ^ 2) := by
  rw [fk_step]
  congr 1
  unfold QE.Dp QE.Dm
  have h1 : x + 2 * ε - 2 * ε = x := by ring
  rw [h1]
  field_simp
  ring

open Real in
/-- **The hyperfinite path sum**: for `g = e^{-Vτ}`,
`v(k,x) = 2^{-k} ∑_paths f(x + W_k) exp(-∑_{j<k} V(x + W_j) τ)`. -/
theorem vFK_exp_path_sum (s τ : ℝ) (f V : ℝ → ℝ) (k : ℕ) (x : ℝ) :
    vFK s f (fun y => exp (-V y * τ)) k x =
      (∑ ω : Fin k → Bool, f (x + S ω * s) * exp (-∑ j : Fin k, V (x + W s ω j) * τ)) /
        (2 : ℝ) ^ k := by
  unfold vFK
  congr 1
  refine Finset.sum_congr rfl fun ω _ => ?_
  rw [pathFK_eq_prod, ← Finset.sum_neg_distrib, Real.exp_sum]
  simp only [neg_mul]

/-- `thm:stoch-fk` in one statement. -/
theorem feynman_kac :
    (∀ (s : K) (f g : K → K) (k : ℕ) (x : K),
      vFK s f g (k + 1) x = g x * ((vFK s f g k (x + s) + vFK s f g k (x - s)) / 2)) ∧
    (∀ (s : K) (f g : K → K) (k : ℕ) (ω : Fin k → Bool) (x : K),
      pathFK s f g k ω x = f (x + S ω * s) * ∏ j : Fin k, g (x + W s ω j)) ∧
    (∀ (s : K) (f : K → K) (k : ℕ) (x : K), vFK s f (fun _ => 1) k x = u s f k x) :=
  ⟨fk_step, pathFK_eq_prod, vFK_one⟩

end QE.Stoch

/-! ## Chapter 12: eventual monotonicity implies S-integrability (flat prior) -/

namespace QE.AnalysisInfra

open Filter Topology MeasureTheory Hyperreal Set

/-- A tail of lattice Riemann sums of a function antitone beyond `T` is bounded by the
tail integral: `∑_{k ∈ F} φ(hk) h ≤ ∫_{(R-h,∞)} φ` when every `hk > R ≥ T + h`. -/
theorem tail_sum_le_setIntegral (φ : ℝ → ℝ) (hφ0 : ∀ x, 0 ≤ φ x) (hφi : Integrable φ)
    {T h R : ℝ} (hanti : AntitoneOn φ (Set.Ici T)) (hh : 0 < h) (hRT : T ≤ R - h)
    (F : Finset ℤ) (hF : ∀ k ∈ F, R < h * k) :
    ∑ k ∈ F, φ (h * k) * h ≤ ∫ x in Set.Ioi (R - h), φ x := by
  have hdisj : (F : Set ℤ).PairwiseDisjoint (fun k : ℤ => Set.Ioc (h * (k - 1)) (h * k)) := by
    intro i _ j _ hij
    rw [Function.onFun, Set.disjoint_left]
    rintro x ⟨h1, h2⟩ ⟨h3, h4⟩
    rcases lt_or_gt_of_ne hij with hl | hl
    · have : (i : ℝ) ≤ j - 1 := by
        have : i ≤ j - 1 := by omega
        exact_mod_cast this
      nlinarith
    · have : (j : ℝ) ≤ i - 1 := by
        have : j ≤ i - 1 := by omega
        exact_mod_cast this
      nlinarith
  have hterm : ∀ k ∈ F, φ (h * k) * h ≤ ∫ x in Set.Ioc (h * (k - 1)) (h * k), φ x := by
    intro k hk
    have hk' := hF k hk
    have hcst : ∫ _x in Set.Ioc (h * (k - 1)) (h * k), φ (h * k) = φ (h * k) * h := by
      rw [setIntegral_const, measureReal_def, Real.volume_Ioc, smul_eq_mul,
        ENNReal.toReal_ofReal (by nlinarith)]
      ring
    rw [← hcst]
    refine setIntegral_mono_on (integrableOn_const measure_Ioc_lt_top.ne) hφi.integrableOn measurableSet_Ioc ?_
    intro x hx
    refine hanti (Set.mem_Ici.2 ?_) (Set.mem_Ici.2 ?_) hx.2
    · have : h * ((k : ℝ) - 1) = h * k - h := by ring
      linarith [hx.1]
    · linarith
  calc ∑ k ∈ F, φ (h * k) * h ≤ ∑ k ∈ F, ∫ x in Set.Ioc (h * (k - 1)) (h * k), φ x :=
        sum_le_sum hterm
    _ = ∫ x in ⋃ k ∈ F, Set.Ioc (h * (k - 1)) (h * k), φ x :=
        (integral_biUnion_finset F (fun _ _ => measurableSet_Ioc) hdisj
          (fun _ _ => hφi.integrableOn)).symm
    _ ≤ ∫ x in Set.Ioi (R - h), φ x := by
        refine setIntegral_mono_set hφi.integrableOn
          (ae_of_all _ fun x => hφ0 x) (Eventually.of_forall fun x (hx : _ ∈ _) => ?_)
        simp only [mem_iUnion] at hx
        obtain ⟨k, hk, h1, -⟩ := hx
        have := hF k hk
        have : h * ((k : ℝ) - 1) = h * k - h := by ring
        exact Set.mem_Ioi.2 (by linarith)

/-- Tails of an integrable function vanish: `∫_{(c,∞)} φ → 0` as `c → ∞`. -/
theorem tendsto_setIntegral_Ioi_zero (φ : ℝ → ℝ) (hφi : Integrable φ) :
    Tendsto (fun c => ∫ x in Set.Ioi c, φ x) atTop (𝓝 0) := by
  have e : (fun c => ∫ x in Set.Ioi c, φ x) = fun c => ∫ x, (Set.Ioi c).indicator φ x :=
    funext fun c => (integral_indicator measurableSet_Ioi).symm
  rw [e]
  have := tendsto_integral_filter_of_dominated_convergence (μ := volume) (l := atTop)
    (F := fun c => (Set.Ioi c).indicator φ) (f := fun _ => (0 : ℝ)) (fun x => ‖φ x‖)
    (Eventually.of_forall fun c => hφi.aestronglyMeasurable.indicator measurableSet_Ioi)
    (Eventually.of_forall fun c => ae_of_all _ fun x => norm_indicator_le_norm_self _ _)
    hφi.norm
    (ae_of_all _ fun x => tendsto_const_nhds.congr' (by
      filter_upwards [eventually_ge_atTop x] with c hc
      rw [indicator_of_notMem (by simp only [Set.mem_Ioi, not_lt]; exact hc)]))
  simpa using this

/-- **Eventual monotonicity implies S-integrability** (the parenthetical sufficient
condition of `prop:stat-flat-shadow`): if `ℓ ≥ 0` is integrable, antitone on `[T,∞)` and
monotone on `(-∞,-T]`, then `∑_{|2εk|>R, |k| ≤ N} ℓ(2εk)·2ε ≈ 0` for every positive
infinite `R` (in particular for every infinite `R ≤ Ω`). -/
theorem s_integrable_of_eventually_monotone (ℓ : ℝ → ℝ) (hℓ0 : ∀ x, 0 ≤ ℓ x)
    (hℓi : Integrable ℓ) (T : ℝ) (hanti : AntitoneOn ℓ (Set.Ici T)) (hmono : MonotoneOn ℓ (Set.Iic (-T)))
    (εs : ℕ → ℝ) (hεpos : 0 < ofSeq εs) (hεinf : 0 < ArchimedeanClass.mk (ofSeq εs))
    (Ns : ℕ → ℕ) :
    ∀ R : ℕ → ℝ, 0 < ofSeq R → ArchimedeanClass.mk (ofSeq R) < 0 →
      ofSeq R ≤ ofSeq (fun n => 2 * εs n * Ns n) →
      0 < ArchimedeanClass.mk (ofSeq (fun n =>
        ∑ k ∈ (Finset.Icc (-(Ns n : ℤ)) (Ns n)).filter (fun k : ℤ => R n < |2 * εs n * k|),
          ℓ (2 * εs n * k) * (2 * εs n))) := by
  classical
  intro R hR0 hRinf _
  rw [infinitesimal_ofSeq_iff]
  set U : Filter ℕ := (hyperfilter ℕ : Filter ℕ)
  have hRt : Tendsto R U atTop := infinitePos_ofSeq_iff.mp ⟨hR0, hRinf⟩
  have hpos : ∀ᶠ n in U, 0 < 2 * εs n := by
    filter_upwards [eventually_pos_of_ofSeq_pos hεpos] with n hn; linarith
  have hh0 : Tendsto (fun n => 2 * εs n) U (𝓝 0) := by
    simpa using (infinitesimal_ofSeq_iff.mp hεinf).const_mul 2
  have hc : Tendsto (fun n => R n - 2 * εs n) U atTop := by
    simpa [sub_eq_add_neg] using hRt.atTop_add hh0.neg
  have hneg_i : Integrable (fun x => ℓ (-x)) := hℓi.comp_neg
  have hneg_anti : AntitoneOn (fun x => ℓ (-x)) (Set.Ici T) := by
    intro x hx y hy hxy
    exact hmono (Set.mem_Iic.2 (by simp only [Set.mem_Ici] at hy; linarith))
      (Set.mem_Iic.2 (by simp only [Set.mem_Ici] at hx; linarith)) (by linarith)
  have hbound : Tendsto (fun n => (∫ x in Set.Ioi (R n - 2 * εs n), ℓ x) +
      ∫ x in Set.Ioi (R n - 2 * εs n), ℓ (-x)) U (𝓝 0) := by
    simpa using ((tendsto_setIntegral_Ioi_zero ℓ hℓi).comp hc).add
      ((tendsto_setIntegral_Ioi_zero _ hneg_i).comp hc)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hbound ?_ ?_
  · filter_upwards [hpos] with n hn
    exact sum_nonneg fun k _ => mul_nonneg (hℓ0 _) hn.le
  · filter_upwards [hpos, hc.eventually (eventually_ge_atTop T), hRt.eventually_gt_atTop 0]
      with n hn hT hR
    set h := 2 * εs n
    set G := (Finset.Icc (-(Ns n : ℤ)) (Ns n)).filter (fun k : ℤ => R n < |h * k|)
    rw [← sum_filter_add_sum_filter_not G (fun k : ℤ => 0 < k)]
    refine add_le_add ?_ ?_
    · refine tail_sum_le_setIntegral ℓ hℓ0 hℓi hanti hn hT _ fun k hk => ?_
      simp only [G, mem_filter] at hk
      have : 0 < h * k := mul_pos hn (by exact_mod_cast hk.2)
      rw [abs_of_pos this] at hk
      exact hk.1.2
    · have e : ∑ k ∈ G.filter (fun k : ℤ => ¬ 0 < k), ℓ (h * k) * h =
          ∑ j ∈ (G.filter (fun k : ℤ => ¬ 0 < k)).image (fun k : ℤ => -k), ℓ (-(h * j)) * h := by
        rw [sum_image (fun x _ y _ hxy => neg_injective hxy)]
        refine sum_congr rfl fun k _ => ?_
        push_cast; ring_nf
      rw [e]
      refine tail_sum_le_setIntegral (fun x => ℓ (-x)) (fun x => hℓ0 _) hneg_i hneg_anti hn hT
        _ fun j hj => ?_
      simp only [Finset.mem_image, G, Finset.mem_filter] at hj
      obtain ⟨k, ⟨⟨-, hk⟩, hk0⟩, rfl⟩ := hj
      have : h * k ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hn.le (by exact_mod_cast not_lt.1 hk0)
      rw [abs_of_nonpos this] at hk
      push_cast; linarith

/-- `prop:stat-flat-shadow` with the parenthetical sufficient condition: for `ℓ ≥ 0`
continuous, integrable with `∫ℓ > 0`, eventually monotone on both half-lines, the shadow
of the uniform-prior posterior mass of `[a,b)` is `∫_a^b ℓ / ∫ ℓ`. -/
theorem flat_prior_shadow_of_monotone (ℓ : ℝ → ℝ) (hℓc : Continuous ℓ) (hℓ0 : ∀ x, 0 ≤ ℓ x)
    (hℓi : Integrable ℓ) (hℓpos : 0 < ∫ x, ℓ x) (T : ℝ) (hanti : AntitoneOn ℓ (Set.Ici T))
    (hmono : MonotoneOn ℓ (Set.Iic (-T)))
    (εs : ℕ → ℝ) (hεpos : 0 < ofSeq εs) (hεinf : 0 < ArchimedeanClass.mk (ofSeq εs))
    (Ns : ℕ → ℕ) (hΩ : ArchimedeanClass.mk (ofSeq (fun n => 2 * εs n * Ns n)) < 0)
    (a b : ℝ) (hab : a < b) :
    ArchimedeanClass.stdPart (ofSeq (fun n =>
      (∑ k ∈ (Finset.Icc (-(Ns n : ℤ)) (Ns n)).filter
          (fun k : ℤ => a ≤ 2 * εs n * k ∧ 2 * εs n * k < b), ℓ (2 * εs n * k))
        / ∑ k ∈ Finset.Icc (-(Ns n : ℤ)) (Ns n), ℓ (2 * εs n * k)))
      = (∫ x in a..b, ℓ x) / ∫ x, ℓ x :=
  flat_prior_shadow ℓ hℓc hℓi hℓpos εs hεpos hεinf Ns hΩ
    (s_integrable_of_eventually_monotone ℓ hℓ0 hℓi T hanti hmono εs hεpos hεinf Ns) a b hab

end QE.AnalysisInfra
