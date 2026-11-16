-- SPDX-License-Identifier: MIT
-- Copyright 2026 Metere Industries, Inc. Author: Alfredo Metere.
-- Quasi-Euclidean Granular Geometry. Any derivative work must carry this notice:
--   This work is derivative of the Quasi-Euclidean Granular Geometry book
--   authored by Alfredo Metere. Copyright 2026 Metere Industries, Inc.
--   All rights reserved
-- See LICENSE.md and NOTICE.


import QuasiEuclidean.Ch01_Axioms
import QuasiEuclidean.Ch06_Analysis
import QuasiEuclidean.Ch08_ODE
import QuasiEuclidean.Ch10_Topology
import QuasiEuclidean.Ch11_Prob
import QuasiEuclidean.Ch15_Dyn
import QuasiEuclidean.OpenGeo
import QuasiEuclidean.Ch09_Geometry
import QuasiEuclidean.NSA_Internal

/-!
# Review infrastructure G: the last partial steps of tagged results

* `QE.Axioms.consistent_factorial_dyadic` : models of QE1–QE3 with `N = ω!` and `N = 2^ω`.
* `QE.Analysis.delta_norms` : `‖δ_ε‖_{p,ε} = (2ε)^{1/p-1}` for every `p ≥ 1`, and the
  `1`, `2`, `∞` norms, on any window containing `0`.
* `QE.OpenGeo.retained_openness_union_iff` : retained openness for finite unions of intervals
  with disjoint closures (the class `𝓔`).
* `QE.ODE.heatIterN_mono`, `QE.ODE.heatIterN_mass` : comparison and conservation of the
  `d`-dimensional explicit heat scheme for all times.
* `QE.Topology.ivt_shadow_root` : the root of the IVT from the lattice search.
* `QE.Prob.density_shadow_infinite`, `QE.Prob.density_shadow_stdPart` : natural density as
  the shadow at every infinite hypernatural.
* `QE.Dyn.predictability_horizon_exp` : the horizon `λ⁻¹ ln M`.
* `QE.Geometry.angle_sum_tolerance`, `QE.Geometry.congruence_snap`,
  `QE.Geometry.playfair_slopes`, `QE.OpenGeo.rot_box_content` : chapter 9.
* `QE.NSA.externality_consequences`, `QE.NSA.card_granularLine` : Appendix A.

Everything is Lebesgue-free.
-/

set_option linter.unusedSectionVars false

section PartAx
namespace QE.Axioms

/-- A model of QE1–QE3 with `N = [(g n)_n]` for any sequence of naturals with `g n ≥ n`:
`ε = 1/(2N)`, horizon `Ω = 2εM = N` with `M = N²`. -/
theorem model_of_seq (g : ℕ → ℕ) (hg : ∀ n, n ≤ g n) :
    ∃ m : GranularModel, m.N = Hyperreal.ofSeq (fun n => (g n : ℝ)) := by
  set N : ℝ* := Hyperreal.ofSeq (fun n => (g n : ℝ)) with hN
  have hω : Hyperreal.omega ≤ N := by
    rw [hN, Hyperreal.omega]
    exact Hyperreal.ofSeq_le_ofSeq.2 (Filter.Eventually.of_forall fun n => by
      exact_mod_cast hg n)
  have hbig : ∀ r : ℝ, (r : ℝ*) < N := fun r => lt_of_lt_of_le (Hyperreal.coe_lt_omega r) hω
  have hNpos : 0 < N := by have := hbig 0; simpa using this
  have hNz : IsHyperint N := ⟨fun n => (g n : ℤ), by rw [hN]; simp⟩
  refine ⟨GranularModel.mk (1 / (2 * N)) N (N * N) (by positivity) ?_ hNz (by field_simp) ?_ ?_,
    rfl⟩
  · intro r hr
    rw [div_lt_iff₀ (by positivity)]
    have h1 := hbig (1 / (2 * r))
    have hr' : (0 : ℝ*) < (r : ℝ*) := by exact_mod_cast hr
    have : ((1 / (2 * r) : ℝ) : ℝ*) * (2 * (r : ℝ*)) = 1 := by
      push_cast; field_simp
    nlinarith
  · obtain ⟨f, hf⟩ := hNz
    exact ⟨fun n => f n * f n, by rw [hf]; push_cast; rfl⟩
  · intro r
    have : 2 * (1 / (2 * N)) * (N * N) = N := by field_simp
    rw [this]; exact hbig r

/-- **Consistency, factorial and dyadic forms.**  The hyperreal ultrapower carries a model of
QE1–QE3 with `N = M!` (`M = ω = [(n)_n]`, `N = [(n!)_n]`) and one with `N = 2^K`
(`K = ω`, `N = [(2^n)_n]`). -/
theorem consistent_factorial_dyadic :
    (∃ m : GranularModel, m.N = Hyperreal.ofSeq (fun n => (n.factorial : ℝ))) ∧
    (∃ m : GranularModel, m.N = Hyperreal.ofSeq (fun n => ((2 ^ n : ℕ) : ℝ))) :=
  ⟨model_of_seq _ Nat.self_le_factorial,
    model_of_seq (fun n => 2 ^ n) (fun _ => (Nat.lt_two_pow_self).le)⟩

end QE.Axioms

end PartAx

section PartMisc
open Finset Filter

/-! ## Chapter 6: the norms of the granular delta for every `p` -/

namespace QE.Analysis

/-- The granular `L^p` integral of `δ_ε` over any finite window containing `0`:
`∑ |δ_ε|^p 2ε = (2ε)^{1-p}` for every real `p ≠ 0`. -/
theorem delta_lpSum (ε : ℝ) (hε : 0 < ε) {p : ℝ} (hp : p ≠ 0) (s : Finset ℤ) (h0 : (0 : ℤ) ∈ s) :
    lpSum ε p s (delta ε) = (2 * ε) ^ (1 - p) := by
  have h2 : 0 < 2 * ε := by linarith
  unfold lpSum
  rw [Finset.sum_eq_single (0 : ℤ)]
  · simp only [delta, ite_true]
    rw [abs_of_pos (by positivity), one_div, Real.inv_rpow h2.le, ← Real.rpow_neg_one,
      ← Real.rpow_mul h2.le]
    conv_lhs => rw [show (2 * ε) = (2 * ε) ^ (1 : ℝ) from (Real.rpow_one _).symm]
    rw [← Real.rpow_mul h2.le, ← Real.rpow_add h2]
    congr 1; ring
  · intro b _ hb
    simp [delta, hb, Real.zero_rpow hp]
  · intro h; exact absurd h0 h

/-- **Norms of the granular delta.**  On any finite window `s ∋ 0`:
`‖δ_ε‖_{1,ε} = 1`, `‖δ_ε‖_{2,ε}² = 1/(2ε)`, `‖δ_ε‖_∞ = max_s |δ_ε| = 1/(2ε)`, and for every
`p ≥ 1`, `‖δ_ε‖_{p,ε} = (∑ |δ_ε|^p 2ε)^{1/p} = (2ε)^{1/p - 1}`. -/
theorem delta_norms (ε : ℝ) (hε : 0 < ε) (s : Finset ℤ) (h0 : (0 : ℤ) ∈ s) :
    lpSum ε 1 s (delta ε) = 1 ∧
    lpSum ε 2 s (delta ε) = 1 / (2 * ε) ∧
    s.sup' ⟨0, h0⟩ (fun k => |delta ε k|) = 1 / (2 * ε) ∧
    ∀ p : ℝ, 1 ≤ p → lpSum ε p s (delta ε) ^ (1 / p) = (2 * ε) ^ (1 / p - 1) := by
  have h2 : 0 < 2 * ε := by linarith
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [delta_lpSum ε hε one_ne_zero s h0]; simp
  · rw [delta_lpSum ε hε two_ne_zero s h0, show (1 : ℝ) - 2 = -1 by norm_num, Real.rpow_neg_one,
      one_div]
  · apply le_antisymm
    · apply Finset.sup'_le
      intro k _
      by_cases hk : k = 0
      · subst hk; simp only [delta, ite_true]; rw [abs_of_pos (by positivity)]
      · simp only [delta, hk, ite_false, abs_zero]; positivity
    · apply Finset.le_sup'_of_le _ h0
      simp only [delta, ite_true]; rw [abs_of_pos (by positivity)]
  · intro p hp
    have hp0 : p ≠ 0 := by linarith
    rw [delta_lpSum ε hε hp0 s h0, ← Real.rpow_mul h2.le]
    congr 1; field_simp

end QE.Analysis

/-! ## Chapter 3: retained openness for finite unions of intervals -/

namespace QE.OpenGeo

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-- Number of points of the lattice `a + 2εℤ` (indices in `W`) in the union of the intervals
`I_i` with endpoints `b i < c i` and openness flags `lc i`, `rc i`, `i : Fin r`. -/
def unionCount {r : ℕ} (W : Finset ℤ) (a ε : K) (b c : Fin r → K) (lc rc : Fin r → Bool) : ℕ :=
  (W.filter (fun k : ℤ => ∃ i, inIv (lc i) (rc i) (b i) (c i) (a + 2 * ε * k))).card

/-- For pieces with pairwise disjoint closures the count of the union is the sum of the counts. -/
theorem unionCount_eq_sum {r : ℕ} (W : Finset ℤ) (a ε : K) (b c : Fin r → K)
    (hdisj : ∀ i j, i ≠ j → c i < b j ∨ c j < b i) (lc rc : Fin r → Bool) :
    unionCount W a ε b c lc rc = ∑ i, ivCount W a ε (b i) (c i) (lc i) (rc i) := by
  classical
  unfold unionCount ivCount
  rw [← Finset.card_biUnion]
  · congr 1
    ext k
    simp only [mem_filter, mem_biUnion, mem_univ, true_and]
    constructor
    · rintro ⟨hk, i, hi⟩; exact ⟨i, hk, hi⟩
    · rintro ⟨i, hk, hi⟩; exact ⟨hk, i, hi⟩
  · intro i _ j _ hij
    rw [Function.onFun, Finset.disjoint_filter]
    intro k _ hi hj
    have hbi : b i ≤ a + 2 * ε * k := by
      have := hi.1; split_ifs at this <;> linarith
    have hci : a + 2 * ε * k ≤ c i := by
      have := hi.2; split_ifs at this <;> linarith
    have hbj : b j ≤ a + 2 * ε * k := by
      have := hj.1; split_ifs at this <;> linarith
    have hcj : a + 2 * ε * k ≤ c j := by
      have := hj.2; split_ifs at this <;> linarith
    rcases hdisj i j hij with h | h <;> linarith

/-- **Retained openness for the class `𝓔`.**  Let `E = I_1 ⊔ ⋯ ⊔ I_r` with `I_i` of endpoints
`b i < c i` and pairwise disjoint closures, and let the window `W` cover every `[b i, c i]`.
Then the identity `2ε · #(E ∩ Λ) = Leb(E) + ε κ(E)`, with `Leb(E) = ∑ (c i - b i)` and
`κ(E) = ∑ κ(I_i)`, holds for every choice of openness of the endpoints iff every endpoint is a
lattice point (`∂E ⊆ Λ`). -/
theorem retained_openness_union_iff {r : ℕ} (W : Finset ℤ) (a ε : K) (hε : 0 < ε)
    (b c : Fin r → K) (hbc : ∀ i, b i < c i)
    (hdisj : ∀ i j, i ≠ j → c i < b j ∨ c j < b i)
    (hW : ∀ i, ∀ k : ℤ, b i ≤ a + 2 * ε * k → a + 2 * ε * k ≤ c i → k ∈ W) :
    (∀ lc rc : Fin r → Bool, 2 * ε * (unionCount W a ε b c lc rc : K) =
        ∑ i, (c i - b i) + ε * ∑ i, kappa (lc i) (rc i)) ↔
      ∀ i, (∃ m : ℤ, a + 2 * ε * m = b i) ∧ (∃ m : ℤ, a + 2 * ε * m = c i) := by
  classical
  -- the defect of piece `i`
  set D : Fin r → Bool → Bool → K := fun i l r' =>
    2 * ε * (ivCount W a ε (b i) (c i) l r' : K) - (c i - b i) - ε * kappa l r' with hD
  have key : ∀ lc rc : Fin r → Bool, (2 * ε * (unionCount W a ε b c lc rc : K) =
      ∑ i, (c i - b i) + ε * ∑ i, kappa (lc i) (rc i)) ↔ ∑ i, D i (lc i) (rc i) = 0 := by
    intro lc rc
    rw [unionCount_eq_sum W a ε b c hdisj lc rc]
    simp only [hD, Finset.sum_sub_distrib, ← Finset.mul_sum]
    push_cast
    rw [Finset.mul_sum]
    constructor <;> intro h <;> linarith
  simp only [key]
  constructor
  · intro h i
    have hsplit : ∀ lc rc : Fin r → Bool,
        ∑ j, D j (lc j) (rc j) = D i (lc i) (rc i) + ∑ j ∈ univ.erase i, D j (lc j) (rc j) :=
      fun lc rc => (Finset.add_sum_erase _ _ (mem_univ i)).symm
    constructor
    · by_contra hb
      push Not at hb
      have e1 := h (fun _ => true) (fun _ => true)
      have e2 := h (Function.update (fun _ => true) i false) (fun _ => true)
      rw [hsplit] at e1 e2
      have hrest : ∑ j ∈ univ.erase i, D j ((Function.update (fun _ => true) i false) j) true =
          ∑ j ∈ univ.erase i, D j true true := by
        apply Finset.sum_congr rfl
        intro j hj
        rw [Function.update_of_ne (Finset.ne_of_mem_erase hj)]
      simp only [Function.update_self] at e2
      rw [hrest] at e2
      have ht := count_left_toggle_of_not_mem W a ε (b i) (c i) true (fun k => hb k)
      have : D i true true - D i false true = -(2 * ε) := by
        simp only [hD, ht, kappa]; norm_num; ring
      linarith
    · by_contra hc
      push Not at hc
      have e1 := h (fun _ => true) (fun _ => true)
      have e2 := h (fun _ => true) (Function.update (fun _ => true) i false)
      rw [hsplit] at e1 e2
      have hrest : ∑ j ∈ univ.erase i, D j true ((Function.update (fun _ => true) i false) j) =
          ∑ j ∈ univ.erase i, D j true true := by
        apply Finset.sum_congr rfl
        intro j hj
        rw [Function.update_of_ne (Finset.ne_of_mem_erase hj)]
      simp only [Function.update_self] at e2
      rw [hrest] at e2
      have ht := count_right_toggle_of_not_mem W a ε (b i) (c i) true (fun k => hc k)
      have : D i true true - D i true false = -(2 * ε) := by
        simp only [hD, ht, kappa]; norm_num; ring
      linarith
  · intro h lc rc
    apply Finset.sum_eq_zero
    intro i _
    have := (retained_openness_iff W a ε (b i) (c i) hε (hbc i) (hW i)).2 (h i) (lc i) (rc i)
    simp only [hD]; rw [this]; ring

/-- **Endpoints on the lattice, class `𝓔`.**  If every endpoint of `E ∈ 𝓔` is a lattice point,
`2ε · #(E ∩ Λ) = Leb(E) + ε κ(E)` exactly. -/
theorem union_count_of_mem {r : ℕ} (W : Finset ℤ) (a ε : K) (hε : 0 < ε)
    (b c : Fin r → K) (hbc : ∀ i, b i < c i)
    (hdisj : ∀ i j, i ≠ j → c i < b j ∨ c j < b i)
    (hW : ∀ i, ∀ k : ℤ, b i ≤ a + 2 * ε * k → a + 2 * ε * k ≤ c i → k ∈ W)
    (hb : ∀ i, ∃ m : ℤ, a + 2 * ε * m = b i) (hc : ∀ i, ∃ m : ℤ, a + 2 * ε * m = c i)
    (lc rc : Fin r → Bool) :
    2 * ε * (unionCount W a ε b c lc rc : K) =
      ∑ i, (c i - b i) + ε * ∑ i, kappa (lc i) (rc i) :=
  (retained_openness_union_iff W a ε hε b c hbc hdisj hW).2 (fun i => ⟨hb i, hc i⟩) lc rc

end QE.OpenGeo

/-! ## Chapter 8: monotonicity and conservation of the `d`-dimensional heat scheme, all times -/

namespace QE.ODE

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
variable {G : Type*} [AddCommGroup G]

/-- Monotonicity of one `d`-dimensional heat step under `2 d r ≤ 1`. -/
theorem heatStepN_mono (r : K) (h0 : 0 ≤ r) {d : ℕ} (h1 : 2 * d * r ≤ 1) (e : Fin d → G)
    (u v : G → K) (huv : ∀ j, u j ≤ v j) (j : G) : heatStepN r e u j ≤ heatStepN r e v j := by
  simp only [heatStepN]
  have hs : ∀ w : G → K, ∑ i, (w (j + e i) - 2 * w j + w (j - e i))
      = ∑ i, (w (j + e i) + w (j - e i)) - 2 * d * w j := by
    intro w
    simp only [sum_sub_distrib, sum_add_distrib, sum_const, card_univ, Fintype.card_fin,
      nsmul_eq_mul]; ring
  rw [hs u, hs v]
  have hsum : ∑ i, (u (j + e i) + u (j - e i)) ≤ ∑ i, (v (j + e i) + v (j - e i)) :=
    Finset.sum_le_sum fun i _ => add_le_add (huv _) (huv _)
  have hr : 0 ≤ 1 - 2 * d * r := by linarith
  nlinarith [mul_le_mul_of_nonneg_left (huv j) hr, mul_le_mul_of_nonneg_left hsum h0]

/-- **Comparison principle for all times**, in `d` directions: `u⁰ ≤ v⁰` implies `uⁿ ≤ vⁿ`. -/
theorem heatIterN_mono (r : K) (h0 : 0 ≤ r) {d : ℕ} (h1 : 2 * d * r ≤ 1) (e : Fin d → G)
    (u v : G → K) (huv : ∀ j, u j ≤ v j) (n : ℕ) (j : G) :
    heatIterN r e u n j ≤ heatIterN r e v n j := by
  induction n generalizing j with
  | zero => exact huv j
  | succ n ih => exact heatStepN_mono r h0 h1 e _ _ ih j

/-- Exact conservation of heat for one `d`-dimensional step on a finite group of sites. -/
theorem heatStepN_mass [Fintype G] (r : K) {d : ℕ} (e : Fin d → G) (u : G → K) :
    ∑ j, heatStepN r e u j = ∑ j, u j := by
  have hi : ∀ i, ∑ j, (u (j + e i) - 2 * u j + u (j - e i)) = 0 := by
    intro i
    simp only [sum_add_distrib, sum_sub_distrib]
    have h1 : ∑ j, u (j + e i) = ∑ j, u j :=
      Fintype.sum_equiv (Equiv.addRight (e i)) _ _ (fun _ => rfl)
    have h2 : ∑ j, u (j - e i) = ∑ j, u j :=
      Fintype.sum_equiv (Equiv.subRight (e i)) _ _ (fun _ => rfl)
    rw [h1, h2, ← mul_sum]; ring
  have : ∑ j, ∑ i, (u (j + e i) - 2 * u j + u (j - e i)) = 0 := by
    rw [Finset.sum_comm]; exact Finset.sum_eq_zero fun i _ => hi i
  unfold heatStepN
  rw [sum_add_distrib, ← mul_sum, this, mul_zero, add_zero]

/-- **Exact conservation of heat for all times**, in `d` directions: `∑ uⁿ = ∑ u⁰`. -/
theorem heatIterN_mass [Fintype G] (r : K) {d : ℕ} (e : Fin d → G) (u : G → K) (n : ℕ) :
    ∑ j, heatIterN r e u n j = ∑ j, u j := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [heatIterN]; rw [heatStepN_mass, ih]

end QE.ODE

/-! ## Chapter 10: the classical IVT from the lattice search -/

namespace QE.Topology

/-- **The root of the classical IVT from the lattice search.**  For `f` continuous on `[0,1]`
with `f 0 ≤ 0 < f 1`, the lattice points `k/n` with `|f (k/n)| ≤ η` found by `ivt_shadow`
accumulate (by compactness) at a root of `f`. -/
theorem ivt_shadow_root (f : ℝ → ℝ) (hf : ContinuousOn f (Set.Icc 0 1))
    (h0 : f 0 ≤ 0) (h1 : 0 < f 1) : ∃ x ∈ Set.Icc (0 : ℝ) 1, f x = 0 := by
  have hpt : ∀ j : ℕ, ∃ x ∈ Set.Icc (0 : ℝ) 1, |f x| ≤ 1 / ((j : ℝ) + 1) := by
    intro j
    obtain ⟨N, hN⟩ := ivt_shadow f hf h0 h1 (1 / ((j : ℝ) + 1)) (by positivity)
    obtain ⟨k, hk, hfk⟩ := hN (N + 1) (by omega)
    refine ⟨k / (N + 1 : ℕ), ⟨by positivity, ?_⟩, hfk⟩
    rw [div_le_one (by positivity)]
    exact_mod_cast hk.le
  choose x hx hfx using hpt
  obtain ⟨y, hy, φ, hφ, hlim⟩ := isCompact_Icc.tendsto_subseq hx
  refine ⟨y, hy, ?_⟩
  have hc : Tendsto (fun j => f (x (φ j))) atTop (nhds (f y)) :=
    ((hf y hy).tendsto.comp (tendsto_nhdsWithin_iff.2 ⟨hlim, Eventually.of_forall
      (fun j => hx (φ j))⟩))
  have hz : Tendsto (fun j => f (x (φ j))) atTop (nhds 0) := by
    rw [tendsto_zero_iff_abs_tendsto_zero]
    refine squeeze_zero (fun _ => abs_nonneg _) (fun j => hfx (φ j)) ?_
    exact (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).comp hφ.tendsto_atTop
  exact tendsto_nhds_unique hc hz

end QE.Topology

/-! ## Chapter 11: natural density at every infinite hypernatural -/

namespace QE.Prob

/-- **Natural density is a shadow, at every infinite `H`.**  If `#(A ∩ [1,n])/n → d`, then for
every infinite hypernatural `H = [h n]` (`h → ∞` along the ultrafilter) the internal probability
`#(*A ∩ [1,H])/H = [#(A ∩ [1,h n])/h n]` has standard part `d`. -/
theorem density_shadow_infinite (A : ℕ → Prop) [DecidablePred A] (d : ℝ)
    (h : Filter.Tendsto (fun n : ℕ => (((Icc 1 n).filter A).card : ℝ) / n)
      Filter.atTop (nhds d))
    (H : ℕ → ℕ) (hH : Tendsto H (hyperfilter ℕ : Filter ℕ) atTop) :
    (Hyperreal.ofSeq (fun n : ℕ => (((Icc 1 (H n)).filter A).card : ℝ) / (H n))).Tendsto
      (nhds d) :=
  Hyperreal.tendsto_ofSeq.2 (h.comp hH)

/-- The same with `H` given as an unlimited element of `ℕ*` (`H > m` for every standard `m`),
and the conclusion stated with Mathlib's standard part: `st P(X_H ∈ *A) = d`. -/
theorem density_shadow_stdPart (A : ℕ → Prop) [DecidablePred A] (d : ℝ)
    (h : Filter.Tendsto (fun n : ℕ => (((Icc 1 n).filter A).card : ℝ) / n)
      Filter.atTop (nhds d))
    (H : ℕ → ℕ) (hH : ∀ m : ℕ, ∀ᶠ n in (hyperfilter ℕ : Filter ℕ), m < H n) :
    ArchimedeanClass.stdPart
      (Hyperreal.ofSeq (fun n : ℕ => (((Icc 1 (H n)).filter A).card : ℝ) / (H n))) = d := by
  have hT : Tendsto H (hyperfilter ℕ : Filter ℕ) atTop :=
    tendsto_atTop.2 fun m => (hH m).mono fun _ hn => hn.le
  exact Hyperreal.stdPart_of_tendsto (density_shadow_infinite A d h H hT)

end QE.Prob

/-! ## Chapter 15: the predictability horizon for a general granular exponent -/

namespace QE.Dyn

/-- **Predictability horizon, exponent `λ`.**  A separation of `e^{λ t}` lattice steps stays
within a budget of `M > 0` lattice steps iff `t ≤ λ⁻¹ ln M`. -/
theorem predictability_horizon_exp (lam M t : ℝ) (hlam : 0 < lam) (hM : 0 < M) :
    Real.exp (lam * t) ≤ M ↔ t ≤ Real.log M / lam := by
  rw [← Real.le_log_iff_exp_le hM, le_div_iff₀ hlam, mul_comm]

end QE.Dyn

end PartMisc

section PartGeo
/-! ## Chapter 9 companions: angle sum, planar congruence, Playfair slopes,
rotated boxes in `n` dimensions.  All Lebesgue-free. -/

namespace QE.Geometry

open Real Set

/-! ### Angle sum with tolerance -/

/-- A line whose direction deviates by `u ∈ [-π/2, π/2]` from the direction of
`c_P c_Q` (centres at distance `d`) is incident with both point-spheres of radius `ε`:
in the frame `c_P = 0`, `c_Q = (d, 0)` some offset `s` is within `ε` of both
projections (`pencil_iff`). -/
def PencilIncident (ε d u : ℝ) : Prop :=
  u ∈ Icc (-(π / 2)) (π / 2) ∧ ∃ s : ℝ, |0 - s| ≤ ε ∧ |d * sin u - s| ≤ ε

/-- The pencil half-width `α(d) = arcsin (2ε/d)`. -/
noncomputable def pencilWidth (ε d : ℝ) : ℝ := arcsin (2 * ε / d)

theorem pencilIncident_le {ε d u : ℝ} (hε : 0 ≤ ε) (hd : 0 < d) (h2 : 2 * ε ≤ d)
    (h : PencilIncident ε d u) : |u| ≤ pencilWidth ε d :=
  (pencil_iff d ε u hd hε h2 h.1).1 h.2

theorem pencilWidth_le {ε d : ℝ} (hε : 0 ≤ ε) (hd : 0 < d) (h2 : 2 * ε ≤ d) :
    pencilWidth ε d ≤ π * ε / d := by
  have h0 : 0 ≤ 2 * ε / d := by positivity
  have h1 : 2 * ε / d ≤ 1 := by rw [div_le_one hd]; exact h2
  have := (arcsin_bounds _ h0 h1).2
  unfold pencilWidth
  calc arcsin (2 * ε / d) ≤ π / 2 * (2 * ε / d) := this
    _ = π * ε / d := by ring

/-- **Angle sum with tolerance.**  Directions `φᵢⱼ` of the centre segments `cᵢcⱼ`,
directions `θᵢⱼ` of six lines, the line `θᵢⱼ` incident with `Pᵢ` and `Pⱼ`
(`PencilIncident` for the deviation `θᵢⱼ - φᵢⱼ`, distance `dᵢⱼ ≥ 2ε`).  The centre
angles are `γ₁ = φ₁₃ - φ₁₂`, `γ₂ = φ₂₁ - φ₂₃`, `γ₃ = φ₃₂ - φ₃₁` with
`γ₁ + γ₂ + γ₃ = π`; the measured angles are the same differences of the `θ`.
Each measured angle is within `α(dᵢⱼ) + α(dᵢₖ)` of the true one, and the measured
angle sum is within `2(α₁₂ + α₁₃ + α₂₃) ≤ 2πε(1/d₁₂ + 1/d₁₃ + 1/d₂₃)` of `π`. -/
theorem angle_sum_tolerance (ε : ℝ) (hε : 0 ≤ ε) (d₁₂ d₁₃ d₂₃ : ℝ)
    (h₁₂ : 2 * ε ≤ d₁₂) (h₁₃ : 2 * ε ≤ d₁₃) (h₂₃ : 2 * ε ≤ d₂₃)
    (p₁₂ : 0 < d₁₂) (p₁₃ : 0 < d₁₃) (p₂₃ : 0 < d₂₃)
    (φ₁₂ φ₁₃ φ₂₁ φ₂₃ φ₃₁ φ₃₂ θ₁₂ θ₁₃ θ₂₁ θ₂₃ θ₃₁ θ₃₂ γ₁ γ₂ γ₃ : ℝ)
    (hγ₁ : γ₁ = φ₁₃ - φ₁₂) (hγ₂ : γ₂ = φ₂₁ - φ₂₃) (hγ₃ : γ₃ = φ₃₂ - φ₃₁)
    (hsum : γ₁ + γ₂ + γ₃ = π)
    (i₁₂ : PencilIncident ε d₁₂ (θ₁₂ - φ₁₂)) (i₁₃ : PencilIncident ε d₁₃ (θ₁₃ - φ₁₃))
    (i₂₁ : PencilIncident ε d₁₂ (θ₂₁ - φ₂₁)) (i₂₃ : PencilIncident ε d₂₃ (θ₂₃ - φ₂₃))
    (i₃₁ : PencilIncident ε d₁₃ (θ₃₁ - φ₃₁)) (i₃₂ : PencilIncident ε d₂₃ (θ₃₂ - φ₃₂)) :
    |(θ₁₃ - θ₁₂) - γ₁| ≤ pencilWidth ε d₁₂ + pencilWidth ε d₁₃ ∧
    |(θ₂₁ - θ₂₃) - γ₂| ≤ pencilWidth ε d₁₂ + pencilWidth ε d₂₃ ∧
    |(θ₃₂ - θ₃₁) - γ₃| ≤ pencilWidth ε d₁₃ + pencilWidth ε d₂₃ ∧
    |(θ₁₃ - θ₁₂) + (θ₂₁ - θ₂₃) + (θ₃₂ - θ₃₁) - π| ≤
      2 * (pencilWidth ε d₁₂ + pencilWidth ε d₁₃ + pencilWidth ε d₂₃) ∧
    2 * (pencilWidth ε d₁₂ + pencilWidth ε d₁₃ + pencilWidth ε d₂₃) ≤
      2 * π * ε * (1 / d₁₂ + 1 / d₁₃ + 1 / d₂₃) := by
  have a₁₂ := abs_le.1 (pencilIncident_le hε p₁₂ h₁₂ i₁₂)
  have a₁₃ := abs_le.1 (pencilIncident_le hε p₁₃ h₁₃ i₁₃)
  have a₂₁ := abs_le.1 (pencilIncident_le hε p₁₂ h₁₂ i₂₁)
  have a₂₃ := abs_le.1 (pencilIncident_le hε p₂₃ h₂₃ i₂₃)
  have a₃₁ := abs_le.1 (pencilIncident_le hε p₁₃ h₁₃ i₃₁)
  have a₃₂ := abs_le.1 (pencilIncident_le hε p₂₃ h₂₃ i₃₂)
  have w₁₂ := pencilWidth_le hε p₁₂ h₁₂
  have w₁₃ := pencilWidth_le hε p₁₃ h₁₃
  have w₂₃ := pencilWidth_le hε p₂₃ h₂₃
  subst hγ₁ hγ₂ hγ₃
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [abs_le]; constructor <;> linarith
  · rw [abs_le]; constructor <;> linarith
  · rw [abs_le]; constructor <;> linarith
  · rw [abs_le]; constructor <;> linarith
  · have e : 2 * π * ε * (1 / d₁₂ + 1 / d₁₃ + 1 / d₂₃) =
        2 * (π * ε / d₁₂ + π * ε / d₁₃ + π * ε / d₂₃) := by ring
    rw [e]; linarith

/-! ### Congruence up to granules, planar form -/

section Congruence
variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-- Squared Euclidean distance in `K × K`. -/
def sqDist (p q : K × K) : K := (p.1 - q.1) ^ 2 + (p.2 - q.2) ^ 2

/-- Triangle inequality without square roots: if `A² = |a|²`, `B² = |a + e|²` and
`|e|² ≤ E²` (all of `A, B, E ≥ 0`), then `B ≤ A + E`. -/
theorem norm_add_le_of_sq (a₁ a₂ e₁ e₂ A B E : K) (hA : 0 ≤ A) (hB : 0 ≤ B) (hE : 0 ≤ E)
    (hA2 : A ^ 2 = a₁ ^ 2 + a₂ ^ 2) (hB2 : B ^ 2 = (a₁ + e₁) ^ 2 + (a₂ + e₂) ^ 2)
    (hE2 : e₁ ^ 2 + e₂ ^ 2 ≤ E ^ 2) : B ≤ A + E := by
  have cs : (a₁ * e₁ + a₂ * e₂) ^ 2 ≤ (A * E) ^ 2 := by
    have h1 : (a₁ * e₁ + a₂ * e₂) ^ 2 ≤ (a₁ ^ 2 + a₂ ^ 2) * (e₁ ^ 2 + e₂ ^ 2) := by
      nlinarith [sq_nonneg (a₁ * e₂ - a₂ * e₁)]
    have h2 : (a₁ ^ 2 + a₂ ^ 2) * (e₁ ^ 2 + e₂ ^ 2) ≤ A ^ 2 * E ^ 2 := by
      rw [hA2]; exact mul_le_mul_of_nonneg_left hE2 (by positivity)
    rw [mul_pow]; linarith
  have hdot : a₁ * e₁ + a₂ * e₂ ≤ A * E :=
    (abs_le_of_sq_le_sq cs (mul_nonneg hA hE)).trans' (le_abs_self _)
  have hsq : B ^ 2 ≤ (A + E) ^ 2 := by nlinarith
  exact (pow_le_pow_iff_left₀ hB (by positivity) two_ne_zero).1 hsq

/-- **Snapped distances.**  If `P, Q` are within `ε` of `p, q` in each coordinate,
`D, D' ≥ 0` are the Euclidean distances (`D² = |p - q|²`, `D'² = |P - Q|²`) and
`s = √2` (`s ≥ 0`, `s² = 2`), then `|D' - D| ≤ 2 s ε`. -/
theorem snapped_dist_le (ε : K) (p q P Q : K × K)
    (hP₁ : |P.1 - p.1| ≤ ε) (hP₂ : |P.2 - p.2| ≤ ε)
    (hQ₁ : |Q.1 - q.1| ≤ ε) (hQ₂ : |Q.2 - q.2| ≤ ε)
    (D D' s : K) (hD : 0 ≤ D) (hD' : 0 ≤ D') (hs : 0 ≤ s) (hs2 : s ^ 2 = 2)
    (hDsq : D ^ 2 = sqDist p q) (hD'sq : D' ^ 2 = sqDist P Q) :
    |D' - D| ≤ 2 * s * ε := by
  have hε : 0 ≤ ε := (abs_nonneg _).trans hP₁
  set e₁ := (P.1 - p.1) - (Q.1 - q.1)
  set e₂ := (P.2 - p.2) - (Q.2 - q.2)
  have he₁ : e₁ ^ 2 ≤ (2 * ε) ^ 2 := by
    apply sq_le_sq'
    · have := abs_le.1 hP₁; have := abs_le.1 hQ₁; linarith
    · have := abs_le.1 hP₁; have := abs_le.1 hQ₁; linarith
  have he₂ : e₂ ^ 2 ≤ (2 * ε) ^ 2 := by
    apply sq_le_sq'
    · have := abs_le.1 hP₂; have := abs_le.1 hQ₂; linarith
    · have := abs_le.1 hP₂; have := abs_le.1 hQ₂; linarith
  have hE : e₁ ^ 2 + e₂ ^ 2 ≤ (2 * s * ε) ^ 2 := by
    have : (2 * s * ε) ^ 2 = 2 * (2 * ε) ^ 2 := by rw [mul_pow, mul_pow, hs2]; ring
    rw [this]; linarith
  have hE' : (-e₁) ^ 2 + (-e₂) ^ 2 ≤ (2 * s * ε) ^ 2 := by rw [neg_sq, neg_sq]; exact hE
  have hpos : 0 ≤ 2 * s * ε := by positivity
  unfold sqDist at hDsq hD'sq
  have h1 : D' ≤ D + 2 * s * ε :=
    norm_add_le_of_sq (p.1 - q.1) (p.2 - q.2) e₁ e₂ D D' _ hD hD' hpos hDsq
      (by rw [hD'sq]; ring) hE
  have h2 : D ≤ D' + 2 * s * ε :=
    norm_add_le_of_sq (P.1 - Q.1) (P.2 - Q.2) (-e₁) (-e₂) D' D _ hD' hD hpos hD'sq
      (by rw [hDsq]; ring) hE'
  rw [abs_le]; constructor <;> linarith

/-- **Congruence up to granules (planar).**  For any map `g` of `K × K` that preserves
squared distances, and coordinatewise snaps `P` of `g p` and `Q` of `g q` with error
`≤ ε` per coordinate, the snapped distance differs from `|p - q|` by at most `2√2 ε`. -/
theorem congruence_up_to_granules (ε : K) (g : K × K → K × K)
    (hg : ∀ p q, sqDist (g p) (g q) = sqDist p q) (p q P Q : K × K)
    (hP₁ : |P.1 - (g p).1| ≤ ε) (hP₂ : |P.2 - (g p).2| ≤ ε)
    (hQ₁ : |Q.1 - (g q).1| ≤ ε) (hQ₂ : |Q.2 - (g q).2| ≤ ε)
    (D D' s : K) (hD : 0 ≤ D) (hD' : 0 ≤ D') (hs : 0 ≤ s) (hs2 : s ^ 2 = 2)
    (hDsq : D ^ 2 = sqDist p q) (hD'sq : D' ^ 2 = sqDist P Q) :
    |D' - D| ≤ 2 * s * ε :=
  snapped_dist_le ε (g p) (g q) P Q hP₁ hP₂ hQ₁ hQ₂ D D' s hD hD' hs hs2
    (by rw [hg]; exact hDsq) hD'sq

/-- The coordinatewise snap `x ↦ 2ε · round (x / 2ε)` on `K × K`. -/
def snap2 [FloorRing K] (ε : K) (p : K × K) : K × K :=
  (2 * ε * (round (p.1 / (2 * ε)) : K), 2 * ε * (round (p.2 / (2 * ε)) : K))

/-- The same with the actual snap, over any ordered field with a floor. -/
theorem congruence_snap [FloorRing K] (ε : K) (hε : 0 < ε) (g : K × K → K × K)
    (hg : ∀ p q, sqDist (g p) (g q) = sqDist p q) (p q : K × K)
    (D D' s : K) (hD : 0 ≤ D) (hD' : 0 ≤ D') (hs : 0 ≤ s) (hs2 : s ^ 2 = 2)
    (hDsq : D ^ 2 = sqDist p q) (hD'sq : D' ^ 2 = sqDist (snap2 ε (g p)) (snap2 ε (g q))) :
    |D' - D| ≤ 2 * s * ε :=
  congruence_up_to_granules ε g hg p q _ _ (snap_error ε _ hε) (snap_error ε _ hε)
    (snap_error ε _ hε) (snap_error ε _ hε) D D' s hD hD' hs hs2 hDsq hD'sq

end Congruence

/-- Over `ℝ`, with square roots: `|‖⌊gp⌉ - ⌊gq⌉‖ - ‖p - q‖| ≤ 2√2 ε`. -/
theorem congruence_snap_real (ε : ℝ) (hε : 0 < ε) (g : ℝ × ℝ → ℝ × ℝ)
    (hg : ∀ p q, sqDist (g p) (g q) = sqDist p q) (p q : ℝ × ℝ) :
    |√(sqDist (snap2 ε (g p)) (snap2 ε (g q))) - √(sqDist p q)| ≤ 2 * √2 * ε := by
  have nn : ∀ a b : ℝ × ℝ, 0 ≤ sqDist a b := fun a b => by unfold sqDist; positivity
  exact congruence_snap ε hε g hg p q _ _ _ (sqrt_nonneg _) (sqrt_nonneg _) (sqrt_nonneg _)
    (sq_sqrt (by norm_num)) (sq_sqrt (nn _ _)) (sq_sqrt (nn _ _))

/-! ### Playfair with horizon: the tube and the slope interval -/

/-- **The tube of radius `ε` about a line of slope `m` is the strip of vertical
half-width `ε√(1+m²)`.**  A point `(x, y)` is within distance `ε` of some point of the
line `y = h + m x` iff `|y - h - m x| ≤ ε √(1 + m²)`. -/
theorem tube_iff_strip (h m ε x y : ℝ) (hε : 0 ≤ ε) :
    (∃ x₀ : ℝ, (x - x₀) ^ 2 + (y - (h + m * x₀)) ^ 2 ≤ ε ^ 2) ↔
      |y - h - m * x| ≤ ε * √(1 + m ^ 2) := by
  set c := y - h - m * x with hc
  have h1 : 0 < 1 + m ^ 2 := by positivity
  have hR : (ε * √(1 + m ^ 2)) ^ 2 = ε ^ 2 * (1 + m ^ 2) := by
    rw [mul_pow, sq_sqrt h1.le]
  constructor
  · rintro ⟨x₀, hx₀⟩
    set t := x₀ - x
    have e : y - (h + m * x₀) = c - m * t := by simp only [hc, t]; ring
    have e2 : (x - x₀) ^ 2 = t ^ 2 := by simp only [t]; ring
    rw [e, e2] at hx₀
    have cs : c ^ 2 ≤ (1 + m ^ 2) * (t ^ 2 + (c - m * t) ^ 2) := by
      nlinarith [sq_nonneg (m * (c - m * t) - t)]
    apply abs_le_of_sq_le_sq _ (by positivity)
    rw [hR]; nlinarith
  · intro hle
    have hc2 : c ^ 2 ≤ ε ^ 2 * (1 + m ^ 2) := by
      rw [← hR, ← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hle 2
    refine ⟨x + m * c / (1 + m ^ 2), ?_⟩
    have e : (x - (x + m * c / (1 + m ^ 2))) ^ 2 +
        (y - (h + m * (x + m * c / (1 + m ^ 2)))) ^ 2 = c ^ 2 / (1 + m ^ 2) := by
      simp only [hc]; field_simp; ring
    rw [e, div_le_iff₀ h1]; linarith

/-- The Playfair functional `|m| Ω + ε + ε√(1+m²)`. -/
noncomputable def playfairF (Ω ε m : ℝ) : ℝ := |m| * Ω + ε + ε * √(1 + m ^ 2)

lemma playfairF_abs (Ω ε m : ℝ) : playfairF Ω ε |m| = playfairF Ω ε m := by
  unfold playfairF; rw [abs_abs, sq_abs]

lemma playfairF_mono {Ω ε : ℝ} (hΩ : 0 ≤ Ω) (hε : 0 ≤ ε) {m m' : ℝ} (h : |m'| ≤ |m|) :
    playfairF Ω ε m' ≤ playfairF Ω ε m := by
  unfold playfairF
  have : m' ^ 2 ≤ m ^ 2 := sq_le_sq.2 h
  have := sqrt_le_sqrt (by linarith : 1 + m' ^ 2 ≤ 1 + m ^ 2)
  nlinarith [mul_le_mul_of_nonneg_right h hΩ, mul_le_mul_of_nonneg_left this hε]

lemma sqrt_shift_le {t δ : ℝ} (ht : 0 ≤ t) (hδ : 0 ≤ δ) :
    √(1 + (t + δ) ^ 2) ≤ √(1 + t ^ 2) + δ := by
  have hs : t ≤ √(1 + t ^ 2) := by
    calc t = √(t ^ 2) := (sqrt_sq ht).symm
      _ ≤ √(1 + t ^ 2) := sqrt_le_sqrt (by linarith)
  rw [sqrt_le_iff]
  refine ⟨by positivity, ?_⟩
  have := sq_sqrt (by positivity : (0 : ℝ) ≤ 1 + t ^ 2)
  nlinarith

/-- **Playfair with horizon: the slope interval.**  For `Ω > 0`, `ε ≥ 0`, `h > 2ε`, the
set of slopes `m` with `|m| Ω + ε + ε√(1+m²) < h` is a symmetric open interval
`(-μ*, μ*)`, with `(h - 2ε)/(Ω + ε) ≤ μ* ≤ (h - 2ε)/Ω`. -/
theorem playfair_slopes (h Ω ε : ℝ) (hΩ : 0 < Ω) (hε : 0 ≤ ε) (hh : 2 * ε < h) :
    ∃ μ : ℝ, {m : ℝ | playfairF Ω ε m < h} = Ioo (-μ) μ ∧
      (h - 2 * ε) / (Ω + ε) ≤ μ ∧ μ ≤ (h - 2 * ε) / Ω := by
  set T := {m : ℝ | 0 ≤ m ∧ playfairF Ω ε m < h}
  have hΩε : 0 < Ω + ε := by linarith
  have upper : ∀ m, playfairF Ω ε m < h → |m| < (h - 2 * ε) / Ω := by
    intro m hm
    unfold playfairF at hm
    have : 1 ≤ √(1 + m ^ 2) := by
      calc (1 : ℝ) = √1 := sqrt_one.symm
        _ ≤ √(1 + m ^ 2) := sqrt_le_sqrt (le_add_of_nonneg_right (sq_nonneg m))
    rw [lt_div_iff₀ hΩ]; nlinarith
  have lower : ∀ m, |m| < (h - 2 * ε) / (Ω + ε) → playfairF Ω ε m < h := by
    intro m hm
    rw [lt_div_iff₀ hΩε] at hm
    unfold playfairF
    have : √(1 + m ^ 2) ≤ 1 + |m| := by
      rw [sqrt_le_iff]; refine ⟨by positivity, ?_⟩
      nlinarith [sq_abs m, abs_nonneg m]
    nlinarith [mul_le_mul_of_nonneg_left this hε]
  have h0T : (0 : ℝ) ∈ T := ⟨le_rfl, lower 0 (by rw [abs_zero]; exact div_pos (by linarith) hΩε)⟩
  have hbdd : BddAbove T := ⟨(h - 2 * ε) / Ω, fun m hm => by
    have := upper m hm.2; rw [abs_of_nonneg hm.1] at this; exact this.le⟩
  refine ⟨sSup T, ?_, ?_, ?_⟩
  · ext m
    simp only [mem_ofPred_eq, mem_Ioo, ← abs_lt]
    constructor
    · intro hm
      rw [← playfairF_abs] at hm
      set t := |m|
      have ht : 0 ≤ t := abs_nonneg m
      set δ := (h - playfairF Ω ε t) / (Ω + ε + 1)
      have hδ : 0 < δ := div_pos (by linarith) (by linarith)
      have hst : playfairF Ω ε (t + δ) < h := by
        have hsq := sqrt_shift_le ht hδ.le
        have hF : playfairF Ω ε (t + δ) ≤ playfairF Ω ε t + δ * (Ω + ε) := by
          unfold playfairF
          rw [abs_of_nonneg (by linarith), abs_of_nonneg ht]
          nlinarith [mul_le_mul_of_nonneg_left hsq hε]
        have : δ * (Ω + ε) < h - playfairF Ω ε t := by
          have e : δ * (Ω + ε + 1) = h - playfairF Ω ε t := by
            simp only [δ]; field_simp
          nlinarith
        linarith
      have : t + δ ≤ sSup T := le_csSup hbdd ⟨by linarith, hst⟩
      linarith
    · intro hm
      obtain ⟨t, ⟨ht0, htT⟩, hlt⟩ := exists_lt_of_lt_csSup ⟨0, h0T⟩ hm
      exact lt_of_le_of_lt (playfairF_mono hΩ.le hε (by rw [abs_of_nonneg ht0]; exact hlt.le)) htT
  · by_contra hc
    push Not at hc
    have hμ0 : 0 ≤ sSup T := le_csSup hbdd h0T
    set L := (h - 2 * ε) / (Ω + ε)
    have hcT : (sSup T + L) / 2 ∈ T := by
      refine ⟨by linarith, lower _ ?_⟩
      rw [abs_of_nonneg (by linarith)]; linarith
    have := le_csSup hbdd hcT
    linarith
  · refine csSup_le ⟨0, h0T⟩ fun m hm => ?_
    have := upper m hm.2; rw [abs_of_nonneg hm.1] at this; exact this.le

/-- The slope condition in the theorem is the disjointness condition of
`parallel_disjoint_iff` for the strip of half-width `r = ε√(1+m²)`. -/
theorem playfair_slope_iff (h Ω ε m : ℝ) (hh : 0 < h) (hΩ : 0 ≤ Ω) (hε : 0 ≤ ε) :
    (¬ ∃ x y : ℝ, |x| ≤ Ω ∧ |y| ≤ ε ∧ |y - h - m * x| ≤ ε * √(1 + m ^ 2)) ↔
      playfairF Ω ε m < h := by
  rw [parallel_disjoint_iff h Ω ε _ m hh hΩ hε (by positivity)]
  unfold playfairF; constructor <;> intro H <;> linarith

end QE.Geometry

namespace QE.OpenGeo

open Finset

/-! ### A rotated box in `n = k + 2` dimensions -/

/-- **The rotated box in `k + 2` dimensions.**  At spacing `1/(5m)`, the box
`[0,1]^{k+2}` has `(5m+1)²(5m+1)^k` lattice points and its rotation by
`arctan (3/4)` in the first two coordinates has `(25m²+2m+1)(5m+1)^k`. -/
theorem rot_box_count (m k : ℕ) :
    ((Icc (0 : ℤ) (5 * m) ×ˢ Icc (0 : ℤ) (5 * m)) ×ˢ
        Fintype.piFinset (fun _ : Fin k => Icc (0 : ℤ) (5 * m))).card =
      (5 * m + 1) ^ 2 * (5 * m + 1) ^ k ∧
    (((Icc (-(3 * m : ℤ)) (4 * m) ×ˢ Icc (0 : ℤ) (7 * m)).filter (fun y : ℤ × ℤ =>
      0 ≤ 4 * y.1 + 3 * y.2 ∧ 4 * y.1 + 3 * y.2 ≤ 25 * m ∧
      0 ≤ -3 * y.1 + 4 * y.2 ∧ -3 * y.1 + 4 * y.2 ≤ 25 * m)) ×ˢ
        Fintype.piFinset (fun _ : Fin k => Icc (0 : ℤ) (5 * m))).card =
      (25 * m ^ 2 + 2 * m + 1) * (5 * m + 1) ^ k := by
  have hside : (Icc (0 : ℤ) (5 * m)).card = 5 * m + 1 := by
    rw [Int.card_Icc]; omega
  constructor
  · rw [card_product, axis_square_count, Fintype.card_piFinset, prod_const, hside, card_univ,
      Fintype.card_fin]
  · rw [card_product, rot_square_count, Fintype.card_piFinset, prod_const, hside, card_univ,
      Fintype.card_fin]

/-- **Content difference of the rotated box in `k + 2` dimensions:** with `2ε·5m = 1`,
`(2ε)^{k+2}((5m+1)^{k+2} - (25m²+2m+1)(5m+1)^k) = (16/5) ε (1 + 2ε)^k`. -/
theorem rot_box_content {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    (ε : K) (m k : ℕ) (h : 2 * ε * (5 * m) = 1) :
    (2 * ε) ^ (k + 2) * (((5 * m + 1) ^ 2 * (5 * m + 1) ^ k : ℕ) : K) -
      (2 * ε) ^ (k + 2) * (((25 * m ^ 2 + 2 * m + 1) * (5 * m + 1) ^ k : ℕ) : K) =
      16 / 5 * ε * (1 + 2 * ε) ^ k := by
  push_cast
  have hk : (2 * ε) ^ k * (5 * (m : K) + 1) ^ k = (1 + 2 * ε) ^ k := by
    rw [← mul_pow]; congr 1; linarith
  have e : (2 * ε) ^ (k + 2) * ((5 * (m : K) + 1) ^ 2 * (5 * (m : K) + 1) ^ k) -
      (2 * ε) ^ (k + 2) * ((25 * (m : K) ^ 2 + 2 * m + 1) * (5 * (m : K) + 1) ^ k) =
      ((2 * ε) ^ k * (5 * (m : K) + 1) ^ k) * ((2 * ε) * (2 * ε * (5 * m)) * (8 / 5)) := by
    ring
  rw [e, hk, h]; ring

end QE.OpenGeo

end PartGeo

noncomputable section PartNSA
open Filter ArchimedeanClass


namespace QE.NSA

/-! ## Externality: the consequences (Appendix A, `prop:nsa-external`) -/

section Externality

/-- The two presentations of internal subsets of `ℝ*` agree. -/
theorem internalSet_eq_internal (B : ℕ → Set ℝ) : internalSet B = internal B := rfl

theorem isInternal_of_eq {S T : Set (Ult ℝ)} (h : S = T) (hT : IsInternal T) :
    IsInternal S := h ▸ hT

/-- **`ℕ` is external** (as a subset of `ℝ*`, in the `IsInternal` sense). -/
theorem not_isInternal_standard_naturals :
    ¬ IsInternal (Set.range (fun m : ℕ => ((m : ℝ) : ℝ*))) := by
  rintro ⟨B, hB⟩
  exact standard_naturals_external B hB.symm

/-- **The monad of `0` is external.** -/
theorem not_isInternal_monad : ¬ IsInternal {x : ℝ* | IsInfinitesimal x} := by
  rintro ⟨B, hB⟩
  exact infinitesimals_external B hB.symm

theorem mem_starSet_zero_iff (x : ℝ*) : x ∈ starSet ({0} : Set ℝ) ↔ x = 0 := by
  obtain ⟨u, rfl⟩ := exists_rep x
  exact (mem_starSet _ u).trans (Germ.coe_eq (f := u) (g := fun _ => (0 : ℝ))).symm

theorem mem_starSet_Icc_iff (a b : ℝ) (x : ℝ*) :
    x ∈ starSet (Set.Icc a b) ↔ (a : ℝ*) ≤ x ∧ x ≤ (b : ℝ*) := by
  obtain ⟨u, rfl⟩ := exists_rep x
  exact (mem_starSet _ u).trans (Filter.eventually_and.trans
    (Iff.and (Hyperreal.ofSeq_le_ofSeq (f := fun _ => a) (g := u)).symm
      (Hyperreal.ofSeq_le_ofSeq (f := u) (g := fun _ => b)).symm))

/-- Finite elements: bounded by a natural number. -/
theorem isFinite_iff_exists_nat (y : ℝ*) : IsFinite y ↔ ∃ n : ℕ, |y| ≤ n := by
  unfold IsFinite
  rw [← ArchimedeanClass.mk_one (R := ℝ*), ArchimedeanClass.mk_le_mk]
  simp [nsmul_eq_mul]

/-- A nonzero element is infinitesimal iff its inverse is not finite. -/
theorem isInfinitesimal_iff_not_isFinite_inv {x : ℝ*} (hx : x ≠ 0) :
    IsInfinitesimal x ↔ ¬ IsFinite x⁻¹ := by
  rw [isInfinitesimal_iff, isFinite_iff_exists_nat]
  push Not
  have hpos : 0 < |x| := abs_pos.2 hx
  refine forall_congr' fun n => ?_
  rw [abs_inv, ← one_div, lt_div_iff₀ hpos]

/-- The monad as the preimage of `ℝ* \ Fin(ℝ*)` under the internal map `x ↦ x⁻¹`,
together with `0`. -/
theorem monad_eq_inv_preimage :
    {x : ℝ* | IsInfinitesimal x} =
      (starFun (fun r : ℝ => r⁻¹)) ⁻¹' {x : ℝ* | IsFinite x}ᶜ ∪ starSet ({0} : Set ℝ) := by
  refine Set.ext fun x => ?_
  have hinv : starFun (fun r : ℝ => r⁻¹) x = x⁻¹ := by
    obtain ⟨u, rfl⟩ := exists_rep x; rfl
  change IsInfinitesimal x ↔ (¬ IsFinite (starFun (fun r : ℝ => r⁻¹) x) ∨
    x ∈ starSet ({0} : Set ℝ))
  refine Iff.trans ?_ (or_congr (Iff.of_eq (congrArg (fun y => ¬ IsFinite y) hinv.symm))
    (mem_starSet_zero_iff x).symm)
  by_cases hx : x = 0
  · subst hx; simp [isInfinitesimal_zero]
  · rw [isInfinitesimal_iff_not_isFinite_inv hx]
    exact ⟨fun h => Or.inl h, fun h => h.resolve_right hx⟩

/-- **`Fin(ℝ*)` is external.** -/
theorem not_isInternal_finite : ¬ IsInternal {x : ℝ* | IsFinite x} := by
  intro h
  apply not_isInternal_monad
  refine isInternal_of_eq monad_eq_inv_preimage ?_
  exact ((h.compl).preimage (fun _ => fun r : ℝ => r⁻¹)).union (isInternal_starSet _)

/-- **The infinite hypernaturals form an external set** (as a subset of `ℝ*`:
the elements of `*ℕ` that are not standard). -/
theorem not_isInternal_infinite_hypernaturals :
    ¬ IsInternal (starSet (Set.range (Nat.cast : ℕ → ℝ)) \
      Set.range (fun m : ℕ => ((m : ℝ) : ℝ*))) := by
  intro h
  apply not_isInternal_standard_naturals
  have hsub : Set.range (fun m : ℕ => ((m : ℝ) : ℝ*)) ⊆ starSet (Set.range (Nat.cast : ℕ → ℝ)) := by
    rintro _ ⟨m, rfl⟩
    exact (const_mem_starSet (Set.range (Nat.cast : ℕ → ℝ)) (m : ℝ)).2 ⟨m, rfl⟩
  have : Set.range (fun m : ℕ => ((m : ℝ) : ℝ*)) =
      starSet (Set.range (Nat.cast : ℕ → ℝ)) \
        (starSet (Set.range (Nat.cast : ℕ → ℝ)) \ Set.range (fun m : ℕ => ((m : ℝ) : ℝ*))) := by
    exact (Set.sdiff_sdiff_cancel_left hsub).symm
  exact isInternal_of_eq this ((isInternal_starSet _).diff h)

/-- `0 ≤ mk x` as soon as `|x| ≤ 1`. -/
theorem isFinite_of_abs_le_one {x : ℝ*} (hx : |x| ≤ 1) : IsFinite x :=
  (isFinite_iff_exists_nat x).2 ⟨1, by simpa using hx⟩

/-- **The standard part map is external**: `x ↦ st x` (with Mathlib's convention
`st x = 0` off `Fin(ℝ*)`) is not an internal function `ℝ* → ℝ*`. -/
theorem not_isInternalFun_stdPart :
    ¬ IsInternalFun (fun x : ℝ* => ((stdPart x : ℝ) : ℝ*)) := by
  rintro ⟨F, hF⟩
  apply not_isInternal_monad
  have hK : IsInternal ((ifun F) ⁻¹' starSet ({0} : Set ℝ)) :=
    (isInternal_starSet _).preimage F
  have hFx : ∀ x : ℝ*, ifun F x = ((stdPart x : ℝ) : ℝ*) := fun x => (congrFun hF x).symm
  have heq : {x : ℝ* | IsInfinitesimal x} =
      (ifun F) ⁻¹' starSet ({0} : Set ℝ) ∩ starSet (Set.Icc (-1) 1) := by
    refine Set.ext fun x => ?_
    have h1 : ifun F x ∈ starSet ({0} : Set ℝ) ↔ stdPart x = 0 :=
      (congrArg (fun y : Ult ℝ => y ∈ starSet ({0} : Set ℝ)) (hFx x)).to_iff.trans
        ((const_mem_starSet _ _).trans Set.mem_singleton_iff)
    change IsInfinitesimal x ↔ (ifun F x ∈ starSet ({0} : Set ℝ) ∧ x ∈ starSet (Set.Icc (-1) 1))
    refine Iff.trans ?_ (and_congr h1 (mem_starSet_Icc_iff (-1) 1 x)).symm
    constructor
    · intro h
      have h1 := (isInfinitesimal_iff x).1 h 1
      simp only [Nat.cast_one, one_mul] at h1
      refine ⟨stdPart_of_infinitesimal h, ?_⟩
      have := abs_le.1 h1.le
      push_cast
      exact this
    · rintro ⟨h0, hl, hu⟩
      have hfin : IsFinite x :=
        isFinite_of_abs_le_one (abs_le.2 ⟨by exact_mod_cast hl, by exact_mod_cast hu⟩)
      have hne : mk x ≠ 0 := stdPart_eq_zero.1 h0
      exact lt_of_le_of_ne hfin (Ne.symm hne)
  exact isInternal_of_eq heq (hK.inter (isInternal_starSet _))

/-- **The lattice points with standard index are external**: for every nonzero
`ε ∈ ℝ*` (in particular for a positive infinitesimal), `{2kε : k ∈ ℤ standard}`
is not internal. -/
theorem not_isInternal_standard_lattice (ε : ℝ*) (hε : ε ≠ 0) :
    ¬ IsInternal {x : ℝ* | ∃ k : ℤ, x = 2 * ((k : ℝ) : ℝ*) * ε} := by
  intro h
  apply not_isInternal_standard_naturals
  obtain ⟨e, rfl⟩ := exists_rep ε
  set G : ℕ → ℝ → ℝ := fun n y => 2 * y * e n
  have hG : ∀ y : ℝ*, @id ℝ* (ifun G y) = 2 * y * Hyperreal.ofSeq e := by
    intro y; obtain ⟨u, rfl⟩ := exists_rep y; rfl
  have hZ : ifun G ⁻¹' {x : ℝ* | ∃ k : ℤ, x = 2 * ((k : ℝ) : ℝ*) * Hyperreal.ofSeq e} =
      {y : ℝ* | ∃ k : ℤ, y = ((k : ℝ) : ℝ*)} := by
    refine Set.ext fun (y : ℝ*) => ?_
    change (∃ k : ℤ, @id ℝ* (ifun G y) = 2 * ((k : ℝ) : ℝ*) * Hyperreal.ofSeq e) ↔ ∃ k : ℤ, y = ((k : ℝ) : ℝ*)
    constructor
    · rintro ⟨k, hk0⟩
      have hk : 2 * y * Hyperreal.ofSeq e = 2 * ((k : ℝ) : ℝ*) * Hyperreal.ofSeq e :=
        (hG y).symm.trans hk0
      refine ⟨k, ?_⟩
      have h2 : (2 : ℝ*) * Hyperreal.ofSeq e ≠ 0 := mul_ne_zero two_ne_zero hε
      have : (2 * Hyperreal.ofSeq e) * y = (2 * Hyperreal.ofSeq e) * ((k : ℝ) : ℝ*) := by
        linear_combination hk
      exact mul_left_cancel₀ h2 this
    · rintro ⟨k, rfl⟩; exact ⟨k, hG _⟩
  have hZi : IsInternal {y : ℝ* | ∃ k : ℤ, y = ((k : ℝ) : ℝ*)} :=
    isInternal_of_eq hZ.symm (h.preimage G)
  have hN : Set.range (fun m : ℕ => ((m : ℝ) : ℝ*)) =
      {y : ℝ* | ∃ k : ℤ, y = ((k : ℝ) : ℝ*)} ∩ starSet (Set.Ici 0) := by
    refine Set.ext fun (y : ℝ*) => ?_
    change (∃ m : ℕ, ((m : ℝ) : ℝ*) = y) ↔ ((∃ k : ℤ, y = ((k : ℝ) : ℝ*)) ∧ y ∈ starSet (Set.Ici (0 : ℝ)))
    constructor
    · rintro ⟨m, rfl⟩
      refine ⟨⟨m, by push_cast; rfl⟩, ?_⟩
      exact (const_mem_starSet (Set.Ici (0 : ℝ)) (m : ℝ)).2 (Set.mem_Ici.2 (Nat.cast_nonneg m))
    · rintro ⟨⟨k, rfl⟩, hk⟩
      have hk0 : (0 : ℝ) ≤ (k : ℝ) := Set.mem_Ici.1 ((const_mem_starSet (Set.Ici (0 : ℝ)) (k : ℝ)).1 hk)
      have hk' : (0 : ℤ) ≤ k := by exact_mod_cast hk0
      refine ⟨k.toNat, ?_⟩
      have : ((k.toNat : ℕ) : ℝ) = (k : ℝ) := by
        have := Int.toNat_of_nonneg hk'
        exact_mod_cast this
      rw [this]
  exact isInternal_of_eq hN (hZi.inter (isInternal_starSet _))

/-- **Externality and its consequences** (`prop:nsa-external`): none of `ℕ`, the
monad of `0`, `Fin(ℝ*)`, the infinite hypernaturals, the standard part map, and
the lattice points `2kε` with standard index `k` (any `ε ≠ 0`) is internal. -/
theorem externality_consequences (ε : ℝ*) (hε : ε ≠ 0) :
    ¬ IsInternal (Set.range (fun m : ℕ => ((m : ℝ) : ℝ*))) ∧
    ¬ IsInternal {x : ℝ* | IsInfinitesimal x} ∧
    ¬ IsInternal {x : ℝ* | IsFinite x} ∧
    ¬ IsInternal (starSet (Set.range (Nat.cast : ℕ → ℝ)) \
      Set.range (fun m : ℕ => ((m : ℝ) : ℝ*))) ∧
    ¬ IsInternalFun (fun x : ℝ* => ((stdPart x : ℝ) : ℝ*)) ∧
    ¬ IsInternal {x : ℝ* | ∃ k : ℤ, x = 2 * ((k : ℝ) : ℝ*) * ε} :=
  ⟨not_isInternal_standard_naturals, not_isInternal_monad, not_isInternal_finite,
    not_isInternal_infinite_hypernaturals, not_isInternalFun_stdPart,
    not_isInternal_standard_lattice ε hε⟩

end Externality

/-! ## The size of the granular line (`prop:nsa-card-lattice`) -/

section CardLattice

/-- The hyperfinite granular line `{2kε : |k| ≤ M}` for `ε = [e n]`, `M = [M n]`. -/
def granularLine (e : ℕ → ℝ) (M : ℕ → ℕ) : Set (Ult ℝ) :=
  hfin (fun n => (Finset.Icc (-(M n : ℤ)) (M n)).image (fun k : ℤ => 2 * (k : ℝ) * e n))

theorem mem_granularLine (e : ℕ → ℝ) (M : ℕ → ℕ) (u : ℕ → ℝ) :
    (u : Ult ℝ) ∈ granularLine e M ↔
      ∀ᶠ n in (hyperfilter ℕ : Filter ℕ), ∃ k : ℤ, |k| ≤ (M n : ℤ) ∧ u n = 2 * (k : ℝ) * e n := by
  unfold granularLine hfin
  rw [mem_internal]
  refine Filter.eventually_congr (Filter.Eventually.of_forall fun n => ?_)
  simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe, Finset.mem_Icc, abs_le]
  constructor
  · rintro ⟨k, hk, h⟩; exact ⟨k, hk, h.symm⟩
  · rintro ⟨k, hk, h⟩; exact ⟨k, hk, h.symm⟩

/-- **Size of the granular line.**  For `ε = [e n] ≠ 0` and `M = [M n] ∈ ℕ*`, the set
`{2kε : |k| ≤ M} ⊆ ℝ*` is hyperfinite with internal cardinality `2M + 1`. -/
theorem card_granularLine (e : ℕ → ℝ) (M : ℕ → ℕ)
    (he : ∀ᶠ n in (hyperfilter ℕ : Filter ℕ), e n ≠ 0) :
    IsHyperfinite (granularLine e M) ∧
      hcard (granularLine e M) = 2 * (M : Ult ℕ) + 1 := by
  refine ⟨⟨_, rfl⟩, ?_⟩
  unfold granularLine
  rw [hcard_hfin]
  refine Germ.coe_eq.2 ?_
  filter_upwards [he] with n hn
  rw [Finset.card_image_of_injective _ (fun a b hab => by
    have h2 : (2 : ℝ) * e n ≠ 0 := mul_ne_zero two_ne_zero hn
    have : (2 * e n) * (a : ℝ) = (2 * e n) * (b : ℝ) := by linear_combination hab
    exact_mod_cast mul_left_cancel₀ h2 this), Int.card_Icc]
  show _ = 2 * M n + 1
  omega

/-- The same in the form `#𝕃 = Ω/ε + 1` when `Ω = 2εM`. -/
theorem card_granularLine_horizon (e : ℕ → ℝ) (M : ℕ → ℕ)
    (he : ∀ᶠ n in (hyperfilter ℕ : Filter ℕ), e n ≠ 0) :
    @id ℝ* (Germ.map (Nat.cast : ℕ → ℝ) (hcard (granularLine e M))) =
      (Hyperreal.ofSeq (fun n => 2 * e n * M n) / Hyperreal.ofSeq e) + 1 := by
  rw [(card_granularLine e M he).2]
  refine Germ.coe_eq.2 ?_
  filter_upwards [he] with n hn
  show ((2 * M n + 1 : ℕ) : ℝ) = 2 * e n * M n / e n + 1
  push_cast
  field_simp

end CardLattice

end QE.NSA

end PartNSA
