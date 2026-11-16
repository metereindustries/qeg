-- SPDX-License-Identifier: MIT
-- Copyright 2026 Metere Industries, Inc. Author: Alfredo Metere.
-- Quasi-Euclidean Granular Geometry. Any derivative work must carry this notice:
--   This work is derivative of the Quasi-Euclidean Granular Geometry book
--   authored by Alfredo Metere. Copyright 2026 Metere Industries, Inc.
--   All rights reserved
-- See LICENSE.md and NOTICE.

import QuasiEuclidean.Basic

/-!
# Chapter 14 — Information: zero is one bit

All entropies are measured in nats (`Real.log`); dividing by `Real.log 2`
converts to bits.  Every identity below is linear in the logarithm, so it holds
verbatim in bits.  The granule `ε` (or the cell volume `v = (2ε)^n`) is an
arbitrary positive real: this is the relative (physical / instrument) reading
of the axiom; the absolute (hyperreal) reading follows by transfer.
-/

open Real Finset Filter Topology

namespace QE.Info

/-! ## Shannon entropy of a finite (granular) distribution -/

/-- Shannon entropy (in nats) of the weights `p` on the finite set `s`. -/
noncomputable def entropy {ι : Type*} (s : Finset ι) (p : ι → ℝ) : ℝ :=
  ∑ i ∈ s, negMulLog (p i)

/-- Granular differential entropy of a density `f` sampled on cells of volume
`v`: the granular integral of `-f log f`. -/
noncomputable def hgran {ι : Type*} (s : Finset ι) (f : ι → ℝ) (v : ℝ) : ℝ :=
  ∑ i ∈ s, negMulLog (f i) * v

/-- Granular entropy is never negative. -/
theorem entropy_nonneg {ι : Type*} (s : Finset ι) (p : ι → ℝ)
    (h0 : ∀ i ∈ s, 0 ≤ p i) (h1 : ∀ i ∈ s, p i ≤ 1) : 0 ≤ entropy s p :=
  Finset.sum_nonneg fun i hi => negMulLog_nonneg (h0 i hi) (h1 i hi)

/-! ## Zero is one bit -/

/-- The empty configuration and the configuration `{0}` ("the point zero"). -/
theorem empty_ne_zero_config : (∅ : Finset ℤ) ≠ {0} := by
  intro h
  have : (0 : ℤ) ∈ (∅ : Finset ℤ) := by rw [h]; simp
  simp at this

theorem mu_empty {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    (ε : K) : QE.mu ε (∅ : Finset ℤ) = 0 := by
  simp [QE.mu]

theorem mu_zero_config {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    (ε : K) : QE.mu ε ({0} : Finset ℤ) = 2 * ε := by
  simp [QE.mu]

/-- **Zero is one bit** (`thm:zero-one-bit`).
(i) `∅` and `{0}` are distinct configurations, separated by the granular
measure (`0` versus `2ε`);
(ii) the Hartley information of the binary alternative is `log₂ 2 = 1`;
(iii) every probability assignment to the alternative "absent / the point 0"
has Shannon entropy at most one bit, with equality exactly for the fair prior;
(iv) zero bits do not suffice: there is no injective code of the two states
into the `2^0 = 1` strings of length 0. -/
theorem zero_one_bit {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    (ε : K) (hε : 0 < ε) :
    (∅ : Finset ℤ) ≠ {0} ∧ QE.mu ε ∅ < QE.mu ε {0} ∧ Real.logb 2 2 = 1 ∧
    (∀ p : ℝ, binEntropy p / Real.log 2 ≤ 1) ∧
    (∀ p : ℝ, binEntropy p / Real.log 2 = 1 ↔ p = 2⁻¹) ∧
    ¬ ∃ c : Fin 2 → Fin (2 ^ 0), Function.Injective c := by
  have hl : 0 < Real.log 2 := Real.log_pos (by norm_num)
  refine ⟨empty_ne_zero_config, ?_, ?_, ?_, ?_, ?_⟩
  · rw [mu_empty, mu_zero_config]; linarith
  · exact Real.logb_self_eq_one (by norm_num)
  · intro p; rw [div_le_one hl]; exact binEntropy_le_log_two
  · intro p; rw [div_eq_one_iff_eq hl.ne']; exact binEntropy_eq_log_two
  · rintro ⟨c, hc⟩
    have := Fintype.card_le_of_injective c hc
    simp at this

/-! ## Registers: the `+1` is the zero -/

/-- A register of `b` bits can store a number in `{0,…,M}` iff `M + 1 ≤ 2^b`. -/
theorem register_iff (M b : ℕ) :
    (∃ c : Fin (M + 1) → (Fin b → Bool), Function.Injective c) ↔ M + 1 ≤ 2 ^ b := by
  constructor
  · rintro ⟨c, hc⟩
    have := Fintype.card_le_of_injective c hc
    simpa using this
  · intro h
    have : Nonempty (Fin (M + 1) ↪ (Fin b → Bool)) := by
      rw [Function.Embedding.nonempty_iff_card_le]; simpa using h
    obtain ⟨e⟩ := this
    exact ⟨e, e.injective⟩

/-- The same bound in logarithmic form: `b ≥ log₂ (M+1)`. -/
theorem register_logb (M b : ℕ) :
    M + 1 ≤ 2 ^ b ↔ Real.logb 2 ((M : ℝ) + 1) ≤ b := by
  rw [Real.logb_le_iff_le_rpow (by norm_num) (by positivity), Real.rpow_natCast]
  constructor
  · intro h; exact_mod_cast h
  · intro h; exact_mod_cast h

/-- The zero costs: `{1,…,2^b}` fits in `b` bits, `{0,…,2^b}` does not. -/
theorem register_zero_costs (b : ℕ) :
    (∃ c : Fin (2 ^ b) → (Fin b → Bool), Function.Injective c) ∧
    ¬ ∃ c : Fin (2 ^ b + 1) → (Fin b → Bool), Function.Injective c := by
  constructor
  · have : Nonempty (Fin (2 ^ b) ↪ (Fin b → Bool)) := by
      rw [Function.Embedding.nonempty_iff_card_le]; simp
    obtain ⟨e⟩ := this
    exact ⟨e, e.injective⟩
  · rw [register_iff]; omega

/-- A nullable field (`NULL` or a value in `{0,…,M}`) has `M + 2` states. -/
theorem nullable_card (M : ℕ) : Fintype.card (Option (Fin (M + 1))) = M + 2 := by
  simp

/-! ## Uniform distributions and Gibbs' inequality -/

/-- `H(uniform on k cells) = log k`. -/
theorem entropy_uniform (k : ℕ) (hk : 0 < k) :
    entropy (Finset.univ : Finset (Fin k)) (fun _ => 1 / (k : ℝ)) = Real.log k := by
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  simp only [entropy, negMulLog, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, one_div, Real.log_inv]
  field_simp

/-- Pointwise Gibbs bound `p log (p/q) ≥ p - q`. -/
lemma gibbs_term {p q : ℝ} (hp : 0 ≤ p) (hq : 0 < q) : p - q ≤ p * Real.log (p / q) := by
  rcases hp.eq_or_lt with h | h
  · subst h; simp; linarith
  · have := Real.log_le_sub_one_of_pos (div_pos hq h)
    have e : Real.log (p / q) = - Real.log (q / p) := by
      rw [← Real.log_inv, inv_div]
    rw [e]
    have : p * Real.log (q / p) ≤ p * (q / p - 1) := mul_le_mul_of_nonneg_left this h.le
    have h2 : p * (q / p - 1) = q - p := by field_simp
    linarith

/-- **Gibbs' inequality**: the Kullback–Leibler divergence is nonnegative. -/
theorem gibbs {ι : Type*} (s : Finset ι) (p q : ι → ℝ)
    (hp : ∀ i ∈ s, 0 ≤ p i) (hq : ∀ i ∈ s, 0 < q i)
    (hps : ∑ i ∈ s, p i = 1) (hqs : ∑ i ∈ s, q i ≤ 1) :
    0 ≤ ∑ i ∈ s, p i * Real.log (p i / q i) := by
  have : ∑ i ∈ s, (p i - q i) ≤ ∑ i ∈ s, p i * Real.log (p i / q i) :=
    Finset.sum_le_sum fun i hi => gibbs_term (hp i hi) (hq i hi)
  rw [Finset.sum_sub_distrib] at this
  linarith

/-- Maximum entropy: a distribution on `k` cells has at most `log k` nats. -/
theorem entropy_le_log_card {ι : Type*} (s : Finset ι) (hs : s.Nonempty) (p : ι → ℝ)
    (hp : ∀ i ∈ s, 0 ≤ p i) (hps : ∑ i ∈ s, p i = 1) :
    entropy s p ≤ Real.log s.card := by
  have hn : (0 : ℝ) < s.card := by exact_mod_cast hs.card_pos
  have hg := gibbs s p (fun _ => 1 / (s.card : ℝ)) hp (fun _ _ => by positivity) hps
    (by simp [Finset.sum_const]; field_simp; rfl)
  have key : ∀ i ∈ s, p i * Real.log (p i / (1 / (s.card : ℝ)))
      = - negMulLog (p i) + p i * Real.log s.card := by
    intro i hi
    rcases (hp i hi).eq_or_lt with h | h
    · rw [← h]; simp
    · rw [div_div_eq_mul_div, div_one, Real.log_mul h.ne' hn.ne', negMulLog]; ring
  rw [Finset.sum_congr rfl key, Finset.sum_add_distrib, ← Finset.sum_mul, hps,
    Finset.sum_neg_distrib] at hg
  unfold entropy; linarith

/-- The maximum is attained by the uniform distribution. -/
theorem entropy_max_uniform (k : ℕ) (hk : 0 < k) (p : Fin k → ℝ)
    (hp : ∀ i, 0 ≤ p i) (hps : ∑ i, p i = 1) :
    entropy Finset.univ p ≤ entropy (Finset.univ : Finset (Fin k)) (fun _ => 1 / (k : ℝ)) := by
  rw [entropy_uniform k hk]
  have := entropy_le_log_card (Finset.univ : Finset (Fin k)) ⟨⟨0, hk⟩, by simp⟩ p
    (fun i _ => hp i) hps
  simpa using this

/-- Cross-entropy bound: `H(p) ≤ -∑ p log q` for any positive sub-probability `q`. -/
theorem entropy_le_cross {ι : Type*} (s : Finset ι) (p q : ι → ℝ)
    (hp : ∀ i ∈ s, 0 ≤ p i) (hq : ∀ i ∈ s, 0 < q i)
    (hps : ∑ i ∈ s, p i = 1) (hqs : ∑ i ∈ s, q i ≤ 1) :
    entropy s p ≤ - ∑ i ∈ s, p i * Real.log (q i) := by
  have hg := gibbs s p q hp hq hps hqs
  have key : ∀ i ∈ s, p i * Real.log (p i / q i) = - negMulLog (p i) - p i * Real.log (q i) := by
    intro i hi
    rcases (hp i hi).eq_or_lt with h | h
    · rw [← h]; simp
    · rw [Real.log_div h.ne' (hq i hi).ne', negMulLog]; ring
  rw [Finset.sum_congr rfl key, Finset.sum_sub_distrib, Finset.sum_neg_distrib] at hg
  unfold entropy; linarith

/-- **Granular maximum entropy (Gibbs/Boltzmann form).**  If `log q_i = A + B x_i`
(a granular exponential family) and `p` has the same mean of `x` as `q`, then
`H(p) ≤ H(q)`. -/
theorem maxent_exponential {ι : Type*} (s : Finset ι) (p q x : ι → ℝ) (A B : ℝ)
    (hp : ∀ i ∈ s, 0 ≤ p i) (hq : ∀ i ∈ s, 0 < q i)
    (hps : ∑ i ∈ s, p i = 1) (hqs : ∑ i ∈ s, q i = 1)
    (hlog : ∀ i ∈ s, Real.log (q i) = A + B * x i)
    (hmean : ∑ i ∈ s, p i * x i = ∑ i ∈ s, q i * x i) :
    entropy s p ≤ entropy s q := by
  have h1 := entropy_le_cross s p q hp hq hps hqs.le
  have e : ∀ r : ι → ℝ, ∑ i ∈ s, r i = 1 → ∑ i ∈ s, r i * x i = ∑ i ∈ s, q i * x i →
      - ∑ i ∈ s, r i * Real.log (q i) = - A - B * ∑ i ∈ s, q i * x i := by
    intro r hr hrm
    rw [Finset.sum_congr rfl (fun i hi => by rw [hlog i hi])]
    simp only [mul_add, Finset.sum_add_distrib, ← Finset.sum_mul, hr]
    rw [show ∑ i ∈ s, r i * (B * x i) = B * ∑ i ∈ s, r i * x i by
      rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro i _; ring, hrm]
    ring
  have hqq : entropy s q = - ∑ i ∈ s, q i * Real.log (q i) := by
    unfold entropy; rw [← Finset.sum_neg_distrib]; apply Finset.sum_congr rfl
    intro i _; simp [negMulLog]
  rw [e p hps hmean] at h1
  rw [hqq, e q hqs rfl]; exact h1

/-- The closed endpoint is worth `log (1 + 1/k)` nats: the uniform law on the
`k + 1` points of a closed lattice interval has strictly more entropy than the
uniform law on the `k` points of the half-open one; with `k = 1/(2ε)` the
excess `log (1 + 2ε)` is positive but infinitesimal. -/
theorem endpoint_entropy (k : ℕ) (hk : 0 < k) :
    entropy (Finset.univ : Finset (Fin (k + 1))) (fun _ => 1 / ((k + 1 : ℕ) : ℝ))
      - entropy (Finset.univ : Finset (Fin k)) (fun _ => 1 / (k : ℝ))
      = Real.log (1 + 1 / (k : ℝ)) ∧ 0 < Real.log (1 + 1 / (k : ℝ)) := by
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  rw [entropy_uniform _ (Nat.succ_pos k), entropy_uniform _ hk]
  constructor
  · rw [← Real.log_div (by positivity) hk'.ne']; congr 1; push_cast; field_simp
  · apply Real.log_pos; have : 0 < 1 / (k : ℝ) := by positivity
    linarith

/-! ## Rényi entropies: the same shift at every order -/

/-- Rényi entropy of order `α ≠ 1` (nats). -/
noncomputable def renyi {ι : Type*} (s : Finset ι) (α : ℝ) (p : ι → ℝ) : ℝ :=
  Real.log (∑ i ∈ s, p i ^ α) / (1 - α)

/-- Granular differential Rényi entropy of a step density. -/
noncomputable def renyiGran {ι : Type*} (s : Finset ι) (α : ℝ) (f : ι → ℝ) (v : ℝ) : ℝ :=
  Real.log (∑ i ∈ s, f i ^ α * v) / (1 - α)

/-- **Universal shift**: for every order `α ≠ 1`, `H_α(f v) = h_α(f) - log v`
exactly (when `∑ f^α > 0`).  The resolution term does not depend on the order. -/
theorem renyi_shift {ι : Type*} (s : Finset ι) (α : ℝ) (hα : α ≠ 1) (f : ι → ℝ) (v : ℝ)
    (hv : 0 < v) (hf : ∀ i ∈ s, 0 ≤ f i) (hpos : 0 < ∑ i ∈ s, f i ^ α) :
    renyi s α (fun i => f i * v) = renyiGran s α f v - Real.log v := by
  unfold renyi renyiGran
  have h1 : ∑ i ∈ s, (f i * v) ^ α = v ^ α * ∑ i ∈ s, f i ^ α := by
    rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro i hi
    rw [Real.mul_rpow (hf i hi) hv.le]; ring
  have h2 : ∑ i ∈ s, f i ^ α * v = v * ∑ i ∈ s, f i ^ α := by
    rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro i _; ring
  have hva : 0 < v ^ α := Real.rpow_pos_of_pos hv α
  rw [h1, h2, Real.log_mul hva.ne' hpos.ne', Real.log_mul hv.ne' hpos.ne', Real.log_rpow hv]
  have : (1 - α) ≠ 0 := sub_ne_zero.mpr (Ne.symm hα)
  field_simp
  ring

/-! ## Dyadic words: zero is a word of full length -/

/-- With dyadic spacing `2ε = 2^{-K}`, the `2^K` lattice points of `[0,1)` are
the binary words of length `K`; the point `0` is the word `0⋯0` of length `K`
(not the empty word), and the empty word describes a lattice with one point only. -/
theorem dyadic_word (K : ℕ) :
    Fintype.card (Fin K → Fin 2) = 2 ^ K ∧
    ((finFunctionFinEquiv (fun _ : Fin K => (0 : Fin 2)) : Fin (2 ^ K)) : ℕ) = 0 ∧
    Fintype.card (Fin 0 → Fin 2) = 1 := by
  refine ⟨by simp, ?_, by simp⟩
  rw [finFunctionFinEquiv_apply]; simp

/-! ## The entropy shift -/

/-- **Exact entropy shift** (step densities): if the granular weights are
`p_i = f_i · v` with `∑ f_i v = 1`, then `H = h_v(f) - log v` exactly. -/
theorem entropy_step {ι : Type*} (s : Finset ι) (f : ι → ℝ) (v : ℝ)
    (hnorm : ∑ i ∈ s, f i * v = 1) :
    entropy s (fun i => f i * v) = hgran s f v - Real.log v := by
  unfold entropy hgran
  have : ∀ i ∈ s, negMulLog (f i * v) = negMulLog (f i) * v - (f i * v) * Real.log v := by
    intro i _; rw [negMulLog_mul]; simp only [negMulLog]; ring
  rw [Finset.sum_congr rfl this, Finset.sum_sub_distrib, ← Finset.sum_mul, ← Finset.sum_mul, hnorm]
  ring

/-- `thm:entropy-shift`, lattice form: on the `n`-dimensional lattice with cells
of volume `(2ε)^n`, `H_ε = h_ε(f) - n log (2ε)` exactly. -/
theorem entropy_shift {ι : Type*} (s : Finset ι) (f : ι → ℝ) (n : ℕ) (ε : ℝ)
    (hnorm : ∑ i ∈ s, f i * (2 * ε) ^ n = 1) :
    entropy s (fun i => f i * (2 * ε) ^ n) = hgran s f ((2 * ε) ^ n) - n * Real.log (2 * ε) := by
  rw [entropy_step s f _ hnorm, Real.log_pow]

/-- Coordinate dependence of differential entropy is exactly the change of the
cell volume: rescaling `x ↦ c x` sends `(f, v)` to `(f / c, c v)`; the Shannon
entropy (same weights) is unchanged, while `h` shifts by `log c`. -/
theorem hgran_scale {ι : Type*} (s : Finset ι) (f : ι → ℝ) (v c : ℝ)
    (hv : 0 < v) (hc : 0 < c) (hnorm : ∑ i ∈ s, f i * v = 1) :
    hgran s (fun i => f i / c) (c * v) = hgran s f v + Real.log c := by
  have hw : ∀ i, f i / c * (c * v) = f i * v := by intro i; field_simp
  have h1 := entropy_step s f v hnorm
  have h2 := entropy_step s (fun i => f i / c) (c * v) (by simp only [hw]; exact hnorm)
  simp only [hw] at h2
  rw [Real.log_mul hc.ne' hv.ne'] at h2
  linarith

/-- Uniform density on an interval of length `1/4` (granular): Shannon entropy
`log k ≥ 0` while the differential entropy is `-log 4 < 0`. -/
theorem negative_hdiff_example (k : ℕ) (hk : 0 < k) (v : ℝ) (hkv : (k : ℝ) * v = 1 / 4) :
    hgran (Finset.univ : Finset (Fin k)) (fun _ => 4) v = - Real.log 4 ∧
    0 ≤ entropy (Finset.univ : Finset (Fin k)) (fun _ => 4 * v) := by
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  have hv : 4 * v = 1 / k := by field_simp; linarith
  constructor
  · simp only [hgran, negMulLog, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul]
    have : (k : ℝ) * (-4 * Real.log 4 * v) = -(Real.log 4) * (4 * (k * v)) := by ring
    rw [this, hkv]; ring
  · rw [hv, entropy_uniform k hk]; exact Real.log_natCast_nonneg k

/-! ## Mutual information: the `log ε` cancels -/

/-- Granular mutual information equals the (sampled) differential mutual
information: the cell volumes `v`, `w` cancel term by term, for every resolution. -/
theorem mutual_info_cancel {ι κ : Type*} (s : Finset ι) (t : Finset κ)
    (f : ι → κ → ℝ) (fx : ι → ℝ) (fy : κ → ℝ) (v w : ℝ) (hv : v ≠ 0) (hw : w ≠ 0) :
    ∑ i ∈ s, ∑ j ∈ t, (f i j * v * w) * Real.log ((f i j * v * w) / ((fx i * v) * (fy j * w)))
      = ∑ i ∈ s, ∑ j ∈ t, (f i j * (v * w)) * Real.log (f i j / (fx i * fy j)) := by
  apply Finset.sum_congr rfl; intro i _; apply Finset.sum_congr rfl; intro j _
  have : (f i j * v * w) / ((fx i * v) * (fy j * w)) = f i j / (fx i * fy j) := by
    rw [show (fx i * v) * (fy j * w) = (fx i * fy j) * (v * w) by ring,
      show f i j * v * w = f i j * (v * w) by ring]
    exact mul_div_mul_right _ _ (mul_ne_zero hv hw)
  rw [this]; ring

/-- The three entropy shifts in `I = H(X) + H(Y) - H(X,Y)` cancel. -/
theorem shift_cancel (v w : ℝ) (hv : 0 < v) (hw : 0 < w) :
    (- Real.log v) + (- Real.log w) - (- Real.log (v * w)) = 0 := by
  rw [Real.log_mul hv.ne' hw.ne']; ring

/-! ## A real number is a finite message -/

/-- A uniformly unknown point of `[0, L)` at resolution `ε` carries
`log (L / 2ε)` nats: `L = 2ε k` cells. -/
theorem info_real (k : ℕ) (hk : 0 < k) (ε L : ℝ) (hε : 0 < ε) (hL : L = 2 * ε * k) :
    entropy (Finset.univ : Finset (Fin k)) (fun _ => 1 / (k : ℝ)) = Real.log (L / (2 * ε)) := by
  rw [entropy_uniform k hk, hL]; congr 1; field_simp

/-- Refinement / fibre entropy: refining `m` coarse cells into `m k` fine cells
adds exactly `log k`; this is the information the coarse-graining discards. -/
theorem fibre_entropy (m k : ℕ) (hm : 0 < m) (hk : 0 < k) :
    entropy (Finset.univ : Finset (Fin (m * k))) (fun _ => 1 / ((m * k : ℕ) : ℝ))
      = entropy (Finset.univ : Finset (Fin m)) (fun _ => 1 / (m : ℝ)) + Real.log k := by
  rw [entropy_uniform _ (Nat.mul_pos hm hk), entropy_uniform _ hm, Nat.cast_mul,
    Real.log_mul (by positivity) (by positivity)]

/-! ## Openness information: two bits -/

/-- The four lattice intervals with the same endpoints are pairwise distinct
(and have the same shadow); the openness alternative carries `log₂ 4 = 2` bits. -/
theorem openness_two_bits (a b : ℤ) (h : a < b) :
    Finset.Icc a b ≠ Finset.Ico a b ∧ Finset.Icc a b ≠ Finset.Ioc a b ∧
    Finset.Icc a b ≠ Finset.Ioo a b ∧ Finset.Ico a b ≠ Finset.Ioc a b ∧
    Finset.Ico a b ≠ Finset.Ioo a b ∧ Finset.Ioc a b ≠ Finset.Ioo a b ∧
    Real.logb 2 4 = 2 := by
  have mem : ∀ {S T : Finset ℤ} (x : ℤ), x ∈ S → x ∉ T → S ≠ T := by
    intro S T x h1 h2 e; rw [e] at h1; exact h2 h1
  refine ⟨mem b (by simp; omega) (by simp), mem a (by simp; omega) (by simp),
    mem a (by simp; omega) (by simp), mem a (by simp; omega) (by simp),
    mem a (by simp; omega) (by simp), mem b (by simp; omega) (by simp), ?_⟩
  rw [show (4 : ℝ) = 2 ^ (2 : ℕ) by norm_num, Real.logb_pow, Real.logb_self_eq_one (by norm_num)]
  norm_num

/-- Under a uniform prior on the four openness types, the granular measure
(which takes the values `b-a+2ε`, `b-a`, `b-a`, `b-a-2ε`) has entropy
`3/2` bits; the remaining `1/2` bit is carried by the first moment. -/
theorem measure_bits :
    negMulLog (1 / 4 : ℝ) + negMulLog (1 / 2) + negMulLog (1 / 4) = 3 / 2 * Real.log 2 ∧
    Real.log 4 - (3 / 2 * Real.log 2) = 1 / 2 * Real.log 2 := by
  have h4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
  have hq : Real.log (1 / 4 : ℝ) = - (2 * Real.log 2) := by
    rw [one_div, Real.log_inv, h4]
  have hh : Real.log (1 / 2 : ℝ) = - Real.log 2 := by
    rw [one_div, Real.log_inv]
  constructor
  · simp only [negMulLog, hq, hh]; ring
  · rw [h4]; ring

/-! ## What the measure records about a configuration -/

/-- In a window of `w` cells: there are `2^w` configurations, `C(w,j)` of them
have granular measure `2εj`, and any law of the measure (a variable with
`w + 1` values, the `+1` being the empty configuration) has entropy at most
`log (w+1)`. -/
theorem measure_vs_config (w : ℕ) (p : ℕ → ℝ)
    (hp : ∀ j ∈ Finset.range (w + 1), 0 ≤ p j) (hps : ∑ j ∈ Finset.range (w + 1), p j = 1) :
    (Finset.range w).powerset.card = 2 ^ w ∧
    (∀ j, ((Finset.range w).powersetCard j).card = w.choose j) ∧
    ∑ j ∈ Finset.range (w + 1), w.choose j = 2 ^ w ∧
    entropy (Finset.range (w + 1)) p ≤ Real.log (w + 1) := by
  refine ⟨by simp, fun j => by simp, Nat.sum_range_choose w, ?_⟩
  have := entropy_le_log_card (Finset.range (w + 1)) ⟨0, by simp⟩ p hp hps
  simpa using this

/-! ## Coarse-graining never increases entropy -/

lemma negMulLog_add_le {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    negMulLog (x + y) ≤ negMulLog x + negMulLog y := by
  rcases hx.eq_or_lt with h | h
  · subst h; simp
  rcases hy.eq_or_lt with h' | h'
  · subst h'; simp
  have hxy : 0 < x + y := by linarith
  have h1 : Real.log x ≤ Real.log (x + y) := Real.log_le_log h (by linarith)
  have h2 : Real.log y ≤ Real.log (x + y) := Real.log_le_log h' (by linarith)
  simp only [negMulLog]
  nlinarith

lemma negMulLog_sum_le {ι : Type*} (s : Finset ι) (p : ι → ℝ) (hp : ∀ i ∈ s, 0 ≤ p i) :
    negMulLog (∑ i ∈ s, p i) ≤ ∑ i ∈ s, negMulLog (p i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    have hs : 0 ≤ ∑ i ∈ s, p i :=
      Finset.sum_nonneg fun i hi => hp i (Finset.mem_insert_of_mem hi)
    have := negMulLog_add_le (hp a (Finset.mem_insert_self a s)) hs
    have := ih fun i hi => hp i (Finset.mem_insert_of_mem hi)
    linarith

/-- **Coarse-graining is lossy** (QE5, quantified internally): for any map
`g` of the cells (for instance snapping to a coarser lattice), the pushed-forward
law has entropy at most that of the original. -/
theorem entropy_map_le {ι κ : Type*} [DecidableEq κ] (s : Finset ι) (p : ι → ℝ)
    (hp : ∀ i ∈ s, 0 ≤ p i) (g : ι → κ) :
    entropy (s.image g) (fun j => ∑ i ∈ s.filter (fun i => g i = j), p i) ≤ entropy s p := by
  unfold entropy
  calc ∑ j ∈ s.image g, negMulLog (∑ i ∈ s.filter (fun i => g i = j), p i)
      ≤ ∑ j ∈ s.image g, ∑ i ∈ s.filter (fun i => g i = j), negMulLog (p i) :=
        Finset.sum_le_sum fun j _ =>
          negMulLog_sum_le _ _ fun i hi => hp i (Finset.mem_filter.mp hi).1
    _ = ∑ i ∈ s, negMulLog (p i) :=
        Finset.sum_fiberwise_of_maps_to (fun i hi => Finset.mem_image_of_mem g hi) _

/-- **Chain rule along a coarse-graining.**  With `q = g_* p`,
`H(p) = H(q) + ∑_j q_j · H(p | g = j)`: the information lost by `g` is exactly
the average entropy of its fibres. -/
theorem chain_rule_fibre {ι κ : Type*} [DecidableEq κ] (s : Finset ι) (p : ι → ℝ)
    (hp : ∀ i ∈ s, 0 ≤ p i) (g : ι → κ) :
    entropy s p = entropy (s.image g) (fun j => ∑ i ∈ s.filter (fun i => g i = j), p i)
      + ∑ j ∈ s.image g, (∑ i ∈ s.filter (fun i => g i = j), p i) *
          entropy (s.filter (fun i => g i = j))
            (fun i => p i / ∑ i' ∈ s.filter (fun i' => g i' = j), p i') := by
  unfold entropy
  rw [← Finset.sum_fiberwise_of_maps_to (g := g) (t := s.image g)
    (fun i hi => Finset.mem_image_of_mem g hi), ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  set F := s.filter (fun i => g i = j)
  set q := ∑ i ∈ F, p i
  have hF : ∀ i ∈ F, 0 ≤ p i := fun i hi => hp i (Finset.mem_filter.mp hi).1
  show ∑ i ∈ F, negMulLog (p i) = negMulLog q + q * ∑ i ∈ F, negMulLog (p i / q)
  rcases (Finset.sum_nonneg hF).eq_or_lt with hq | hq
  · -- q = 0: every p i in the fibre vanishes
    have hz : ∀ i ∈ F, p i = 0 := (Finset.sum_eq_zero_iff_of_nonneg hF).mp hq.symm
    have hq0 : q = 0 := hq.symm
    rw [hq0]
    simp only [negMulLog_zero, zero_mul, add_zero]
    exact Finset.sum_eq_zero fun i hi => by rw [hz i hi, negMulLog_zero]
  · have hq' : q ≠ 0 := hq.ne'
    have key : ∀ i ∈ F, negMulLog (p i)
        = (p i / q) * negMulLog q + q * negMulLog (p i / q) := by
      intro i _
      rw [← negMulLog_mul]; congr 1; field_simp
    rw [Finset.sum_congr rfl key, Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.mul_sum,
      ← Finset.sum_div, div_self hq', one_mul]

/-- The loss of a coarse-graining onto `m` classes is at least `H(p) - log m`. -/
theorem coarse_loss_lower {ι κ : Type*} [DecidableEq κ] (s : Finset ι) (hs : s.Nonempty)
    (p : ι → ℝ) (hp : ∀ i ∈ s, 0 ≤ p i) (hps : ∑ i ∈ s, p i = 1) (g : ι → κ) :
    entropy s p - Real.log (s.image g).card
      ≤ entropy s p - entropy (s.image g) (fun j => ∑ i ∈ s.filter (fun i => g i = j), p i) := by
  have hq : ∑ j ∈ s.image g, ∑ i ∈ s.filter (fun i => g i = j), p i = 1 := by
    rw [Finset.sum_fiberwise_of_maps_to (fun i hi => Finset.mem_image_of_mem g hi), hps]
  have := entropy_le_log_card (s.image g) (hs.image g) _
    (fun j _ => Finset.sum_nonneg fun i hi => hp i (Finset.mem_filter.mp hi).1) hq
  linarith

/-! ## Observing zero -/

/-- For the uniform granular law on the `2m + 1` lattice points of `[-1, 1]`
(`2ε = 1/m`), the event `X = 0` has probability `ε/(1+ε) > 0` and surprisal
`log ((1+ε)/ε)`: finite, and growing only logarithmically as `ε → 0`. -/
theorem observe_zero (m : ℕ) (hm : 0 < m) (ε : ℝ) (hε : 2 * ε * m = 1) :
    (1 : ℝ) / (2 * m + 1) = ε / (1 + ε) ∧ 0 < ε / (1 + ε) ∧
    - Real.log ((1 : ℝ) / (2 * m + 1)) = Real.log ((1 + ε) / ε) := by
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hε0 : 0 < ε := by
    by_contra h; push Not at h; nlinarith
  have e : (1 : ℝ) / (2 * m + 1) = ε / (1 + ε) := by
    field_simp; nlinarith
  refine ⟨e, by positivity, ?_⟩
  rw [e, ← Real.log_inv, inv_div]

/-! ## Noiseless granular channel -/

/-- A noiseless channel whose input is a lattice point of `[-A, A]`, `A = 2εm`,
has `2m + 1` inputs (the `+1` is zero) and capacity `log (2m+1)`: every input
distribution has entropy at most this, and the uniform one attains it. -/
theorem noiseless_capacity (m : ℕ) (p : ℤ → ℝ)
    (hp : ∀ i ∈ Finset.Icc (-(m : ℤ)) m, 0 ≤ p i)
    (hps : ∑ i ∈ Finset.Icc (-(m : ℤ)) m, p i = 1) :
    (Finset.Icc (-(m : ℤ)) m).card = 2 * m + 1 ∧
    entropy (Finset.Icc (-(m : ℤ)) m) p ≤ Real.log (2 * m + 1) := by
  have hc : (Finset.Icc (-(m : ℤ)) m).card = 2 * m + 1 := by
    rw [Int.card_Icc]; omega
  refine ⟨hc, ?_⟩
  have := entropy_le_log_card _ ⟨0, by simp⟩ p hp hps
  rw [hc] at this; simpa using this

/-! ## Grouping and Rényi information dimension -/

/-- Grouping: a mixture `(1-α)·a` on `s` and `α·b` on a disjoint `t`. -/
theorem grouping {ι κ : Type*} (s : Finset ι) (t : Finset κ) (a : ι → ℝ) (b : κ → ℝ)
    (α : ℝ) (ha : ∑ i ∈ s, a i = 1) (hb : ∑ j ∈ t, b j = 1) :
    entropy s (fun i => (1 - α) * a i) + entropy t (fun j => α * b j)
      = binEntropy α + (1 - α) * entropy s a + α * entropy t b := by
  unfold entropy
  simp only [negMulLog_mul]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
    ← Finset.sum_mul, ← Finset.sum_mul, ha, hb, binEntropy_eq_negMulLog_add_negMulLog_one_sub]
  ring

/-- Rényi dimension of a discrete/continuous mixture: the coefficient of
`-log v` (i.e. of `log (1/(2ε)^n)`) in the granular entropy is exactly `α`. -/
theorem renyi_mixture {ι κ : Type*} (s : Finset ι) (t : Finset κ) (a : ι → ℝ) (f : κ → ℝ)
    (α v : ℝ) (ha : ∑ i ∈ s, a i = 1) (hf : ∑ j ∈ t, f j * v = 1) :
    entropy s (fun i => (1 - α) * a i) + entropy t (fun j => α * (f j * v))
      = binEntropy α + (1 - α) * entropy s a + α * hgran t f v + α * (- Real.log v) := by
  rw [grouping s t a (fun j => f j * v) α ha hf, entropy_step t f v hf]; ring

/-! ## Kolmogorov complexity: counting -/

lemma sum_pow_two_lt (n : ℕ) : ∑ i ∈ Finset.range n, 2 ^ i < 2 ^ n := by
  induction n with
  | zero => simp
  | succ n ih => rw [Finset.sum_range_succ, pow_succ]; omega

/-- There are fewer than `2^n` binary descriptions of length `< n`, so no
description method assigns distinct descriptions shorter than `n` bits to
`2^n` lattice points. -/
theorem incompressible (n : ℕ) :
    ¬ ∃ d : Fin (2 ^ n) → (Σ k : Fin n, (Fin k → Bool)), Function.Injective d := by
  rintro ⟨d, hd⟩
  have h1 := Fintype.card_le_of_injective d hd
  rw [Fintype.card_sigma] at h1
  simp only [Fintype.card_fun, Fintype.card_bool, Fintype.card_fin] at h1
  rw [Fin.sum_univ_eq_sum_range (fun k => 2 ^ k) n] at h1
  have := sum_pow_two_lt n
  omega

/-! ## Erasure: zero is not free -/

/-- Erasing a register that is uniformly distributed on `{0,…,M}` (resetting it
to `0`) lowers its entropy by `log (M+1)`; for `M ≥ 1` this is at least
`log 2` — one bit — even though the reset value is zero. -/
theorem erasure_entropy (M : ℕ) (hM : 1 ≤ M) :
    entropy (Finset.univ : Finset (Fin (M + 1))) (fun _ => 1 / ((M + 1 : ℕ) : ℝ))
      - entropy (Finset.univ : Finset (Fin (M + 1))) (fun i => if i = 0 then 1 else 0)
      = Real.log (M + 1) ∧ Real.log 2 ≤ Real.log (M + 1) := by
  constructor
  · rw [entropy_uniform _ (Nat.succ_pos M)]
    have : entropy (Finset.univ : Finset (Fin (M + 1))) (fun i => if i = 0 then 1 else 0) = 0 := by
      unfold entropy; apply Finset.sum_eq_zero; intro i _; by_cases h : i = 0 <;> simp [h]
    rw [this]; push_cast; ring
  · apply Real.log_le_log (by norm_num)
    have : (1 : ℝ) ≤ M := by exact_mod_cast hM
    linarith

/-! ## Shadow of the entropy shift (Riemann-sum version) -/

/-- **Shadow (classical comparison).** Riemann-sum error for a Lipschitz
integrand on `n` cells of width `h`, against the interval integral. -/
theorem riemann_lipschitz (g : ℝ → ℝ) (L : NNReal) (hg : LipschitzWith L g)
    (a h : ℝ) (hh : 0 < h) (n : ℕ) :
    |∑ k ∈ Finset.range n, g (a + k * h) * h - ∫ x in a..a + n * h, g x|
      ≤ L * (n * h) * h := by
  have hc : Continuous g := hg.continuous
  have hsum : ∫ x in a..a + n * h, g x
      = ∑ k ∈ Finset.range n, ∫ x in (a + k * h)..(a + ((k + 1 : ℕ) : ℝ) * h), g x := by
    have := intervalIntegral.sum_integral_adjacent_intervals (f := g) (μ := MeasureTheory.volume)
      (a := fun k : ℕ => a + k * h) (n := n) (fun k _ => hc.intervalIntegrable _ _)
    simp only [Nat.cast_zero, zero_mul, add_zero] at this
    rw [← this]
  rw [hsum, ← Finset.sum_sub_distrib]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  have cell : ∀ k ∈ Finset.range n,
      |g (a + k * h) * h - ∫ x in (a + k * h)..(a + ((k + 1 : ℕ) : ℝ) * h), g x| ≤ L * h * h := by
    intro k _
    set x0 := a + k * h
    have hx1 : a + ((k + 1 : ℕ) : ℝ) * h = x0 + h := by simp [x0]; ring
    rw [hx1]
    have e : g x0 * h - ∫ x in x0..x0 + h, g x = ∫ x in x0..x0 + h, (g x0 - g x) := by
      rw [intervalIntegral.integral_sub intervalIntegrable_const (hc.intervalIntegrable _ _),
        intervalIntegral.integral_const]
      simp; ring
    rw [e]
    have b := intervalIntegral.norm_integral_le_of_norm_le_const (a := x0) (b := x0 + h)
      (C := L * h) (f := fun x => g x0 - g x) (by
        intro x hx
        rw [Set.uIoc_of_le (by linarith)] at hx
        have := hg.dist_le_mul x0 x
        rw [Real.dist_eq, Real.dist_eq] at this
        rw [Real.norm_eq_abs]
        have hxx : |x0 - x| ≤ h := by
          rw [abs_le]; constructor <;> linarith [hx.1, hx.2]
        calc |g x0 - g x| ≤ L * |x0 - x| := this
          _ ≤ L * h := mul_le_mul_of_nonneg_left hxx L.2)
    rw [Real.norm_eq_abs] at b
    have : |x0 + h - x0| = h := by rw [add_sub_cancel_left, abs_of_pos hh]
    rw [this] at b; exact b
  refine (Finset.sum_le_sum cell).trans ?_
  simp; nlinarith [L.2]

/-- **Shadow of the entropy shift.**  Let `f` be a probability density on
`[a, a + ℓ]` such that `f` and `-f log f` are Lipschitz.  Quantise it on
`n` cells of width `δ = ℓ / n` (granular density `f(x_k)` normalised by its
Riemann sum `Z_n`).  Then `H_n + log δ_n → h(f) = ∫ -f log f`. -/
theorem entropy_shift_shadow (f : ℝ → ℝ) (L : NNReal) (hf : LipschitzWith L f)
    (hg : LipschitzWith L (fun x => negMulLog (f x))) (a ℓ : ℝ) (hℓ : 0 < ℓ)
    (hint : ∫ x in a..a + ℓ, f x = 1) :
    Tendsto (fun n : ℕ =>
        entropy (Finset.range n) (fun k => f (a + k * (ℓ / n)) * (ℓ / n) /
          ∑ j ∈ Finset.range n, f (a + j * (ℓ / n)) * (ℓ / n)) + Real.log (ℓ / n))
      atTop (𝓝 (∫ x in a..a + ℓ, negMulLog (f x))) := by
  set δ : ℕ → ℝ := fun n => ℓ / n
  set Z : ℕ → ℝ := fun n => ∑ j ∈ Finset.range n, f (a + j * δ n) * δ n
  set S : ℕ → ℝ := fun n => ∑ j ∈ Finset.range n, negMulLog (f (a + j * δ n)) * δ n
  have hnd : ∀ n : ℕ, 0 < n → (n : ℝ) * δ n = ℓ := by
    intro n hn; simp only [δ]; field_simp
  have bound : ∀ (g : ℝ → ℝ), LipschitzWith L g → ∀ n : ℕ, 0 < n →
      |∑ j ∈ Finset.range n, g (a + j * δ n) * δ n - ∫ x in a..a + ℓ, g x| ≤ L * ℓ * (ℓ / n) := by
    intro g hg' n hn
    have hδ : 0 < δ n := by simp only [δ]; positivity
    have := riemann_lipschitz g L hg' a (δ n) hδ n
    rw [hnd n hn] at this; exact this
  have conv : ∀ (g : ℝ → ℝ), LipschitzWith L g →
      Tendsto (fun n : ℕ => ∑ j ∈ Finset.range n, g (a + j * δ n) * δ n) atTop
        (𝓝 (∫ x in a..a + ℓ, g x)) := by
    intro g hg'
    have hlim : Tendsto (fun n : ℕ => (L : ℝ) * ℓ * (ℓ / n)) atTop (𝓝 0) := by
      have := (tendsto_const_div_atTop_nhds_zero_nat ℓ).const_mul ((L : ℝ) * ℓ)
      simpa using this
    rw [tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero_norm' ?_ hlim
    filter_upwards [eventually_gt_atTop 0] with n hn
    rw [norm_norm, Real.norm_eq_abs]; exact bound g hg' n hn
  have hZ : Tendsto Z atTop (𝓝 1) := by rw [← hint]; exact conv f hf
  have hS : Tendsto S atTop (𝓝 (∫ x in a..a + ℓ, negMulLog (f x))) := conv _ hg
  have hlim : Tendsto (fun n => S n / Z n + Real.log (Z n)) atTop
      (𝓝 (∫ x in a..a + ℓ, negMulLog (f x))) := by
    have := (hS.div hZ one_ne_zero).add (hZ.log one_ne_zero)
    simpa using this
  refine hlim.congr' ?_
  have hZpos : ∀ᶠ n in atTop, 0 < Z n := hZ.eventually (lt_mem_nhds one_pos)
  filter_upwards [hZpos, eventually_gt_atTop 0] with n hz hn
  have hδ : 0 < δ n := by simp only [δ]; positivity
  have hnorm : ∑ k ∈ Finset.range n, f (a + k * δ n) * (δ n / Z n) = 1 := by
    have : ∑ k ∈ Finset.range n, f (a + k * δ n) * (δ n / Z n) = Z n / Z n := by
      simp only [Z, Finset.sum_div]; apply Finset.sum_congr rfl; intro k _; ring
    rw [this, div_self hz.ne']
  have hstep := entropy_step (Finset.range n) (fun k => f (a + k * δ n)) (δ n / Z n) hnorm
  have e1 : (fun k : ℕ => f (a + k * (ℓ / n)) * (ℓ / n) /
      ∑ j ∈ Finset.range n, f (a + j * (ℓ / n)) * (ℓ / n))
      = fun k : ℕ => f (a + k * δ n) * (δ n / Z n) := by
    funext k; simp only [δ, Z]; ring
  show S n / Z n + Real.log (Z n) = _
  rw [e1, hstep]
  simp only [hgran]
  rw [Real.log_div hδ.ne' hz.ne']
  have : ∑ i ∈ Finset.range n, negMulLog (f (a + i * δ n)) * (δ n / Z n) = S n / Z n := by
    simp only [S, Finset.sum_div]; apply Finset.sum_congr rfl; intro k _; ring
  rw [this]; simp only [δ]; ring

end QE.Info
