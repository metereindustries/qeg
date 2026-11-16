-- SPDX-License-Identifier: MIT
-- Copyright 2026 Metere Industries, Inc. Author: Alfredo Metere.
-- Quasi-Euclidean Granular Geometry. Any derivative work must carry this notice:
--   This work is derivative of the Quasi-Euclidean Granular Geometry book
--   authored by Alfredo Metere. Copyright 2026 Metere Industries, Inc.
--   All rights reserved
-- See LICENSE.md and NOTICE.

import QuasiEuclidean.Ch14_Info
import QuasiEuclidean.Ch15_Dyn

/-!
# Open problems of the dynamics chapters, settled

* the circular granulation of chaotic maps: `k ↦ b k` on `ZMod M`, exact
  preperiod and exact periods (`orderOf (b : ZMod d)`), and the logistic map
  `ℓ₄` on the nodes `sin² (π k / M)`;
* the x-rounded logistic map: resolution loss at the fold, exponential
  divergence, absorbing zero;
* granular Pesin formula for the cat map (lower bound by counting);
* reversible lattice maps: symmetric cycles;
* the period bound of symmetric snapped maps (termination of the cascade),
  monotone / antitone lattice maps;
* the granular H-theorem: exact reversal symmetry of entropy changes and
  Boltzmann's counting bound;
* limit cycles of seeded stochastic training and of rounded descent.

Everything is finite combinatorics or elementary real algebra; no measure
theory is used.
-/

namespace QE.OpenDyn

open Finset Function Real

/-! ## The circular granulation: multiplication by `b` on `ZMod M` -/

section Circle

/-- Multiplication by `b` on the `M`-cell circle `ZMod M` (the granular
`θ ↦ b θ mod 1`). -/
def mulMap (b M : ℕ) (k : ZMod M) : ZMod M := (b : ZMod M) * k

theorem mulMap_iterate (b M n : ℕ) (k : ZMod M) :
    (mulMap b M)^[n] k = (b : ZMod M) ^ n * k := by
  induction n generalizing k with
  | zero => simp
  | succ n ih =>
    rw [iterate_succ_apply', ih]; simp only [mulMap]; ring

/-- **Preperiod.**  If `M = u * m` with `u ∣ b ^ a`, then after `a` steps every
state is a multiple of `u`. -/
theorem mulMap_enters (b M u a : ℕ) (hu : u ∣ b ^ a) (k : ZMod M) :
    ∃ j : ZMod M, (mulMap b M)^[a] k = (u : ZMod M) * j := by
  obtain ⟨c, hc⟩ := hu
  refine ⟨(c : ZMod M) * k, ?_⟩
  rw [mulMap_iterate]
  have : ((b : ZMod M)) ^ a = ((b ^ a : ℕ) : ZMod M) := by push_cast; ring
  rw [this, hc]; push_cast; ring

/-- The key divisibility: with `M = u m`, `u ∣ b^a`, `gcd(m, b) = 1`,
and `d = m / gcd(k, m)`, `M ∣ b^a k c ↔ d ∣ c`. -/
theorem dvd_iff_core (b M u m a k c : ℕ) (hM : M = u * m) (hu : u ∣ b ^ a)
    (hm : Nat.Coprime m b) (hm0 : 0 < m) :
    M ∣ b ^ a * k * c ↔ m / Nat.gcd k m ∣ c := by
  have hg : Nat.gcd k m ∣ m := Nat.gcd_dvd_right k m
  have hgk : Nat.gcd k m ∣ k := Nat.gcd_dvd_left k m
  have hma : Nat.Coprime m (b ^ a) := Nat.Coprime.pow_right a hm
  constructor
  · intro h
    have h1 : m ∣ b ^ a * k * c := (Dvd.intro_left u hM.symm).trans h
    have h2 : m ∣ k * c := by
      rw [mul_assoc] at h1; exact hma.dvd_of_dvd_mul_left h1
    -- m / g ∣ (k / g) * c and gcd(m/g, k/g) = 1
    rcases Nat.eq_zero_or_pos (Nat.gcd k m) with h0 | hpos
    · exact absurd (Nat.gcd_eq_zero_iff.mp h0).2 hm0.ne'
    have hcop : Nat.Coprime (m / Nat.gcd k m) (k / Nat.gcd k m) := by
      rw [Nat.coprime_comm]; exact Nat.coprime_div_gcd_div_gcd hpos
    have h3 : m / Nat.gcd k m ∣ k / Nat.gcd k m * c := by
      have e1 : m = Nat.gcd k m * (m / Nat.gcd k m) := (Nat.mul_div_cancel' hg).symm
      have e2 : k * c = Nat.gcd k m * (k / Nat.gcd k m * c) := by
        rw [← mul_assoc, Nat.mul_div_cancel' hgk]
      rw [e1, e2] at h2
      exact Nat.dvd_of_mul_dvd_mul_left hpos h2
    exact hcop.dvd_of_dvd_mul_left h3
  · intro h
    rw [hM, mul_assoc]
    apply mul_dvd_mul hu
    have e1 : m = Nat.gcd k m * (m / Nat.gcd k m) := (Nat.mul_div_cancel' hg).symm
    rw [e1]; exact mul_dvd_mul hgk h

/-- **Exact periods on the circle** (the `±`-free form).  For the state
`x = b^a k` reached after the preperiod, `b^n x = x` iff `b^n ≡ 1 (mod d)`,
`d = m / gcd(k, m)`. -/
theorem mulMap_return_iff (b M u m a k n : ℕ) (hM : M = u * m) (hu : u ∣ b ^ a)
    (hm : Nat.Coprime m b) (hm0 : 0 < m) (hb : 1 ≤ b) :
    (mulMap b M)^[n] ((mulMap b M)^[a] (k : ZMod M)) = (mulMap b M)^[a] (k : ZMod M) ↔
      ((b : ZMod (m / Nat.gcd k m))) ^ n = 1 := by
  rw [mulMap_iterate, mulMap_iterate]
  have h1 : 1 ≤ b ^ n := Nat.one_le_pow _ _ hb
  have key : (b : ZMod M) ^ n * ((b : ZMod M) ^ a * k) = (b : ZMod M) ^ a * k ↔
      M ∣ b ^ a * k * (b ^ n - 1) := by
    rw [← ZMod.natCast_eq_zero_iff]
    push_cast [Nat.cast_sub h1]
    constructor <;> intro h <;> linear_combination h
  rw [key, dvd_iff_core b M u m a k _ hM hu hm hm0]
  rw [← ZMod.natCast_eq_zero_iff]
  push_cast [Nat.cast_sub h1]
  rw [sub_eq_zero]

/-- **Exact period on the circle.**  The minimal period of the state reached
after the preperiod is the multiplicative order of `b` modulo
`d = m / gcd(k, m)`. -/
theorem mulMap_minimalPeriod (b M u m a k : ℕ) (hM : M = u * m) (hu : u ∣ b ^ a)
    (hm : Nat.Coprime m b) (hm0 : 0 < m) (hb : 1 ≤ b) :
    minimalPeriod (mulMap b M) ((mulMap b M)^[a] (k : ZMod M)) =
      orderOf ((b : ZMod (m / Nat.gcd k m))) := by
  apply Nat.dvd_antisymm
  · rw [← isPeriodicPt_iff_minimalPeriod_dvd]
    exact (mulMap_return_iff b M u m a k _ hM hu hm hm0 hb).mpr (pow_orderOf_eq_one _)
  · rw [orderOf_dvd_iff_pow_eq_one]
    exact (mulMap_return_iff b M u m a k _ hM hu hm hm0 hb).mp iterate_minimalPeriod

/-- The `±` form: `b^n x = -x` iff `b^n ≡ -1 (mod d)`. -/
theorem mulMap_return_neg_iff (b M u m a k n : ℕ) (hM : M = u * m) (hu : u ∣ b ^ a)
    (hm : Nat.Coprime m b) (hm0 : 0 < m) :
    (mulMap b M)^[n] ((mulMap b M)^[a] (k : ZMod M)) = -(mulMap b M)^[a] (k : ZMod M) ↔
      ((b : ZMod (m / Nat.gcd k m))) ^ n = -1 := by
  rw [mulMap_iterate, mulMap_iterate]
  have key : (b : ZMod M) ^ n * ((b : ZMod M) ^ a * k) = -((b : ZMod M) ^ a * k) ↔
      M ∣ b ^ a * k * (b ^ n + 1) := by
    rw [← ZMod.natCast_eq_zero_iff]
    push_cast
    constructor <;> intro h <;> linear_combination h
  rw [key, dvd_iff_core b M u m a k _ hM hu hm hm0]
  rw [← ZMod.natCast_eq_zero_iff]
  push_cast
  rw [add_eq_zero_iff_eq_neg]

/-- The dyadic and odd extremes: on `M = 2^K` every state reaches `0`
(here `m = 1`, `d = 1`); on odd `M` (`u = 1`, `a = 0`) the map is a
permutation and every state is periodic. -/
theorem mulMap_dyadic_collapse (K : ℕ) (k : ZMod (2 ^ K)) : (mulMap 2 (2 ^ K))^[K] k = 0 := by
  rw [mulMap_iterate]
  have : ((2 : ℕ) : ZMod (2 ^ K)) ^ K = 0 := by
    rw [← Nat.cast_pow, ZMod.natCast_self]
  rw [this, zero_mul]

end Circle

/-! ## The logistic map on the circular nodes `sin² (π k / M)` -/

section Logistic

/-- The conjugacy `x = sin² (π θ)` between `θ ↦ 2θ` and `ℓ₄(x) = 4x(1-x)`. -/
theorem logistic_doubling_conj (θ : ℝ) :
    4 * sin (π * θ) ^ 2 * (1 - sin (π * θ) ^ 2) = sin (π * (2 * θ)) ^ 2 := by
  have h : π * (2 * θ) = 2 * (π * θ) := by ring
  rw [h, sin_two_mul, ← cos_sq']; ring

/-- `sin²(π θ)` has period `1`. -/
theorem sin_sq_add_int (θ : ℝ) (n : ℤ) : sin (π * (θ + n)) ^ 2 = sin (π * θ) ^ 2 := by
  have h : π * (θ + n) = π * θ + n * π := by ring
  rw [h, sin_add_int_mul_pi]
  rcases Int.even_or_odd n with he | ho
  · rw [he.neg_one_zpow]; ring
  · rw [ho.neg_one_zpow]; ring

/-- The circular node `x_k = sin² (π k / M)`. -/
noncomputable def node (M k : ℕ) : ℝ := sin (π * ((k : ℝ) / M)) ^ 2

/-- **The granular logistic map is exact on the circular nodes**:
`ℓ₄(x_k) = x_{2k mod M}`; no rounding is involved. -/
theorem logistic_node (M k : ℕ) (hM : 0 < M) :
    4 * node M k * (1 - node M k) = node M ((2 * k) % M) := by
  unfold node
  rw [logistic_doubling_conj]
  have hdiv := Nat.div_add_mod (2 * k) M
  have hc : ((2 * k : ℕ) : ℝ) = (M : ℝ) * (((2 * k) / M : ℕ) : ℝ) + (((2 * k) % M : ℕ) : ℝ) := by
    rw [← Nat.cast_mul, ← Nat.cast_add, hdiv]
  have : (2 : ℝ) * ((k : ℝ) / M) = (((2 * k) % M : ℕ) : ℝ) / M + (((2 * k) / M : ℕ) : ℤ) := by
    have hM' : (M : ℝ) ≠ 0 := by exact_mod_cast hM.ne'
    rw [Int.cast_natCast]
    field_simp
    push_cast at hc
    linarith
  rw [this, sin_sq_add_int]

/-- Nodes coincide exactly when the indices agree up to sign mod `M`. -/
theorem node_eq_iff (M j k : ℕ) (hM : 0 < M) :
    node M j = node M k ↔ ((j : ZMod M) = k ∨ (j : ZMod M) = -k) := by
  unfold node
  have hM' : (M : ℝ) ≠ 0 := by exact_mod_cast hM.ne'
  have hsq : ∀ y : ℝ, sin y ^ 2 = (1 - cos (2 * y)) / 2 := fun y => by
    rw [cos_two_mul, ← sin_sq_add_cos_sq y]; ring
  rw [hsq, hsq]
  have e1 : (1 - cos (2 * (π * ((j : ℝ) / M)))) / 2 = (1 - cos (2 * (π * ((k : ℝ) / M)))) / 2 ↔
      cos (2 * (π * ((k : ℝ) / M))) = cos (2 * (π * ((j : ℝ) / M))) := by
    constructor <;> intro h <;> linarith
  rw [e1, cos_eq_cos_iff]
  have hpi : π ≠ 0 := Real.pi_ne_zero
  constructor
  · rintro ⟨l, hl | hl⟩
    · have hr : ((j : ℤ) : ℝ) = ((l * M + k : ℤ) : ℝ) := by
        push_cast
        have : 2 * π * ((j : ℝ) / M) = 2 * π * (l + (k : ℝ) / M) := by linarith
        have h2 := mul_left_cancel₀ (mul_ne_zero two_ne_zero hpi) this
        field_simp at h2; linarith
      have hz := congrArg (fun z : ℤ => (z : ZMod M)) (Int.cast_injective hr)
      simp only [Int.cast_add, Int.cast_mul, Int.cast_natCast, ZMod.natCast_self, mul_zero,
        zero_add] at hz
      exact Or.inl hz
    · have hr : ((j : ℤ) : ℝ) = ((l * M - k : ℤ) : ℝ) := by
        push_cast
        have : 2 * π * ((j : ℝ) / M) = 2 * π * (l - (k : ℝ) / M) := by linarith
        have h2 := mul_left_cancel₀ (mul_ne_zero two_ne_zero hpi) this
        field_simp at h2; linarith
      have hz := congrArg (fun z : ℤ => (z : ZMod M)) (Int.cast_injective hr)
      simp only [Int.cast_sub, Int.cast_mul, Int.cast_natCast, ZMod.natCast_self, mul_zero,
        zero_sub] at hz
      exact Or.inr hz
  · rintro (h | h)
    · have h' : ((j : ℤ) : ZMod M) = ((k : ℤ) : ZMod M) := by simpa using h
      rw [ZMod.intCast_eq_intCast_iff_dvd_sub] at h'
      obtain ⟨l, hl⟩ := h'
      refine ⟨-l, Or.inl ?_⟩
      have : (k : ℝ) - j = M * l := by exact_mod_cast hl
      field_simp
      push_cast
      linear_combination (-1 : ℝ) * this
    · have h' : ((j : ℤ) : ZMod M) = ((-(k : ℤ) : ℤ) : ZMod M) := by simpa using h
      rw [ZMod.intCast_eq_intCast_iff_dvd_sub] at h'
      obtain ⟨l, hl⟩ := h'
      refine ⟨-l, Or.inr ?_⟩
      have : -(k : ℝ) - j = M * l := by exact_mod_cast hl
      field_simp
      push_cast
      linear_combination (-1 : ℝ) * this

/-- The logistic map `ℓ₄`. -/
noncomputable def logistic (x : ℝ) : ℝ := 4 * x * (1 - x)

theorem logistic_iterate_node (M k n : ℕ) (hM : 0 < M) :
    logistic^[n] (node M k) = node M ((2 ^ n * k) % M) := by
  induction n with
  | zero =>
    simp only [iterate_zero, id_eq, pow_zero, one_mul]
    unfold node
    have h := Nat.div_add_mod k M
    have hM' : (M : ℝ) ≠ 0 := by exact_mod_cast hM.ne'
    have : (k : ℝ) / M = ((k % M : ℕ) : ℝ) / M + ((k / M : ℕ) : ℤ) := by
      rw [Int.cast_natCast]
      have hc : (k : ℝ) = (M : ℝ) * ((k / M : ℕ) : ℝ) + ((k % M : ℕ) : ℝ) := by
        rw [← Nat.cast_mul, ← Nat.cast_add, h]
      field_simp; linarith
    rw [this, sin_sq_add_int]
  | succ n ih =>
    rw [iterate_succ_apply', ih]
    unfold logistic
    rw [logistic_node M _ hM]
    congr 1
    rw [pow_succ, Nat.mul_mod, Nat.mod_mod, ← Nat.mul_mod]
    congr 1; ring

/-- **Exact periods of the granular logistic map on the circular nodes.**
For `M = u m` with `u ∣ 2^a`, `m` odd, and `d = m / gcd(k, m)`, the node
`x_{2^a k}` returns after `n` steps iff `2^n ≡ ±1 (mod d)`.  The period is
therefore the order of `2` in `(ℤ/d)^×/{±1}`. -/
theorem logistic_node_return_iff (M u m a k n : ℕ) (hM : M = u * m) (hu : u ∣ 2 ^ a)
    (hm : Nat.Coprime m 2) (hm0 : 0 < m) (hM0 : 0 < M) :
    logistic^[n] (node M (2 ^ a * k)) = node M (2 ^ a * k) ↔
      (((2 : ℕ) : ZMod (m / Nat.gcd k m)) ^ n = 1 ∨ ((2 : ℕ) : ZMod (m / Nat.gcd k m)) ^ n = -1) := by
  rw [logistic_iterate_node M _ n hM0, node_eq_iff M _ _ hM0,
    ← mulMap_return_iff 2 M u m a k n hM hu hm hm0 (by norm_num),
    ← mulMap_return_neg_iff 2 M u m a k n hM hu hm hm0]
  rw [mulMap_iterate, mulMap_iterate, ZMod.natCast_mod]
  push_cast
  exact Iff.rfl

end Logistic

/-! ## The x-rounded logistic map: an overflow into an overflow -/

section XRounded

theorem sin_sq_sub_sin_sq (a b : ℝ) : sin a ^ 2 - sin b ^ 2 = sin (a + b) * sin (a - b) := by
  rw [sin_add, sin_sub]
  have ha := sin_sq_add_cos_sq a
  have hb := sin_sq_add_cos_sq b
  linear_combination (sin b ^ 2) * ha - (sin a ^ 2) * hb

/-- **Bulk resolution.**  The coordinate change `x = sin²(π θ)` is
`π`-Lipschitz: two states one lattice step `h` apart in `x` are at least
`h / π` apart in `θ`. -/
theorem node_lipschitz (θ θ' : ℝ) :
    |sin (π * θ) ^ 2 - sin (π * θ') ^ 2| ≤ π * |θ - θ'| := by
  rw [sin_sq_sub_sin_sq, abs_mul]
  have h1 : |sin (π * θ + π * θ')| ≤ 1 := abs_sin_le_one _
  have h2 : |sin (π * θ - π * θ')| ≤ |π * θ - π * θ'| := abs_sin_le_abs
  have h3 : |π * θ - π * θ'| = π * |θ - θ'| := by
    rw [← mul_sub, abs_mul, abs_of_pos Real.pi_pos]
  calc |sin (π * θ + π * θ')| * |sin (π * θ - π * θ')| ≤ 1 * |sin (π * θ - π * θ')| :=
        mul_le_mul_of_nonneg_right h1 (abs_nonneg _)
    _ ≤ π * |θ - θ'| := by rw [one_mul, ← h3]; exact h2

/-- Snapping to the lattice `h ℤ` in the `x` coordinate. -/
noncomputable def xsnap (h x : ℝ) : ℝ := h * ⌊x / h + 1 / 2⌋

/-- **Collapse at the fold.**  Every `θ` with `π |θ| < √(h/2)` is snapped to
`x = 0`: a whole `θ`-interval of width `√(2h)/π`, against the bulk resolution
`h/π`, is erased by one rounding. -/
theorem fold_collapse (h θ : ℝ) (hh : 0 < h) (hθ : π * |θ| < Real.sqrt (h / 2)) :
    xsnap h (sin (π * θ) ^ 2) = 0 := by
  unfold xsnap
  have hs : sin (π * θ) ^ 2 ≤ (π * θ) ^ 2 := sin_sq_le_sq
  have hsq : (π * θ) ^ 2 < h / 2 := by
    have h0 : 0 ≤ π * |θ| := mul_nonneg Real.pi_pos.le (abs_nonneg θ)
    have := mul_self_lt_mul_self h0 hθ
    rw [Real.mul_self_sqrt (by positivity)] at this
    calc (π * θ) ^ 2 = (π * |θ|) * (π * |θ|) := by rw [mul_pow, ← sq_abs θ]; ring
      _ < h / 2 := this
  have hlo : 0 ≤ sin (π * θ) ^ 2 / h + 1 / 2 := by positivity
  have hhi : sin (π * θ) ^ 2 / h + 1 / 2 < 1 := by
    rw [div_add' _ _ _ hh.ne', div_lt_one hh]; linarith
  have : ⌊sin (π * θ) ^ 2 / h + 1 / 2⌋ = 0 := by
    rw [Int.floor_eq_iff]; constructor <;> push_cast <;> linarith
  rw [this]; simp

/-- `x = 0` is a fixed point of the snapped logistic map: once collapsed, the
computed orbit stays at `0` forever. -/
theorem xsnap_logistic_zero (h : ℝ) : xsnap h (logistic 0) = 0 := by
  have : ⌊(0 : ℝ) / h + 1 / 2⌋ = 0 := by
    rw [zero_div, zero_add, Int.floor_eq_iff]; norm_num
  simp only [xsnap, logistic, mul_zero, zero_mul, this, Int.cast_zero]

/-- **Exact doubling of separations** on the circle: `2^t θ - 2^t θ' = 2^t (θ - θ')`. -/
theorem doubling_separation (t : ℕ) (θ θ' : ℝ) :
    (2 : ℝ) ^ t * θ - 2 ^ t * θ' = 2 ^ t * (θ - θ') := by ring

/-- **Divergence after a collapse.**  If the true state is `θ ≠ 0` with
`|θ| ≤ 1/4` while the computed state is `0`, then after some `t` with
`2^t ≤ 1/(2|θ|)` steps the true orbit is at `x_t = sin²(π 2^t θ) ≥ 1/2`, while
the computed orbit is still `0`.  Hence the shadowing horizon is at most
`log₂ (1/|θ|)`; for `|θ| ≥ c √h` it is at most `½ log₂ (1/h) + log₂(1/c)`. -/
theorem collapse_divergence (θ : ℝ) (hθ0 : θ ≠ 0) (hθ : |θ| ≤ 1 / 4) :
    ∃ t : ℕ, (2 : ℝ) ^ t * |θ| ≤ 1 / 2 ∧ 1 / 2 ≤ sin (π * (2 ^ t * θ)) ^ 2 := by
  have hpos : 0 < |θ| := abs_pos.mpr hθ0
  have hx : (1 : ℝ) ≤ 1 / (4 * |θ|) := by
    rw [le_div_iff₀ (by positivity)]; linarith
  obtain ⟨n, hn1, hn2⟩ := exists_nat_pow_near hx (by norm_num : (1 : ℝ) < 2)
  refine ⟨n + 1, ?_, ?_⟩
  · rw [le_div_iff₀ (by positivity)] at hn1
    rw [pow_succ]; nlinarith
  · have hlow : 1 / 4 < (2 : ℝ) ^ (n + 1) * |θ| := by
      rw [div_lt_iff₀ (by positivity)] at hn2; nlinarith
    have hup : (2 : ℝ) ^ (n + 1) * |θ| ≤ 1 / 2 := by
      rw [le_div_iff₀ (by positivity)] at hn1
      rw [pow_succ]; nlinarith
    set s := (2 : ℝ) ^ (n + 1) * |θ|
    have heven : sin (π * (2 ^ (n + 1) * θ)) ^ 2 = sin (π * s) ^ 2 := by
      rcases abs_choice θ with h | h
      · simp only [s, h]
      · have : π * (2 ^ (n + 1) * θ) = -(π * s) := by simp only [s, h]; ring
        rw [this, sin_neg, neg_sq]
    rw [heven]
    have hmono : sin (π / 4) ≤ sin (π * s) := by
      apply Real.sin_le_sin_of_le_of_le_pi_div_two
      · linarith [Real.pi_pos]
      · nlinarith [Real.pi_pos]
      · nlinarith [Real.pi_pos]
    rw [Real.sin_pi_div_four] at hmono
    have h0 : 0 ≤ Real.sqrt 2 / 2 := by positivity
    have := pow_le_pow_left₀ h0 hmono 2
    rw [div_pow, Real.sq_sqrt (by norm_num)] at this
    linarith

end XRounded

/-! ## Granular Pesin formula for the cat map: the counting lower bound -/

section Pesin

open QE.Dyn

/-- The integer cat map on `ℤ²`. -/
def catZ (w : ℤ × ℤ) : ℤ × ℤ := (2 * w.1 + w.2, w.1 + w.2)

/-- Its integer inverse. -/
def catZInv (w : ℤ × ℤ) : ℤ × ℤ := (w.1 - w.2, -w.1 + 2 * w.2)

theorem catZ_left_inv : LeftInverse catZInv catZ := by
  intro w; ext <;> simp [catZ, catZInv] <;> ring

theorem catZ_injective : Injective catZ := catZ_left_inv.injective

variable (N : ℕ)

/-- Reduction `ℤ² → (ZMod N)²`. -/
def castZ (w : ℤ × ℤ) : ZMod N × ZMod N := ((w.1 : ZMod N), (w.2 : ZMod N))

theorem castZ_catZ (w : ℤ × ℤ) : castZ N (catZ w) = cat N (castZ N w) := by
  ext <;> simp [castZ, catZ, cat]

theorem castZ_catZ_iterate (i : ℕ) (w : ℤ × ℤ) :
    castZ N (catZ^[i] w) = (cat N)^[i] (castZ N w) := by
  induction i generalizing w with
  | zero => rfl
  | succ i ih => rw [iterate_succ_apply, iterate_succ_apply, ih, castZ_catZ]

/-- `v` has a lift to `ℤ²` of sup-norm at most `R`. -/
def Small (R : ℤ) (v : ZMod N × ZMod N) : Prop :=
  ∃ w : ℤ × ℤ, |w.1| ≤ R ∧ |w.2| ≤ R ∧ castZ N w = v

theorem int_unique {R a b : ℤ} (hR : 4 * R < N) (ha : |a| ≤ 3 * R) (hb : |b| ≤ R)
    (h : (a : ZMod N) = b) : a = b := by
  rw [ZMod.intCast_eq_intCast_iff_dvd_sub] at h
  have hlt : |b - a| < (N : ℤ) := by
    calc |b - a| ≤ |b| + |a| := abs_sub _ _
      _ < N := by linarith
  have := Int.eq_zero_of_abs_lt_dvd h hlt
  linarith

/-- **Lifting lemma.**  If the first `t` iterates of `v` are all `R`-small on
the torus (`4R < N`), then `v` lifts to an integer vector whose first `t`
integer iterates are all `R`-small: no wrapping occurs. -/
theorem lift_small {R : ℤ} (hR : 4 * R < N) (v : ZMod N × ZMod N) (t : ℕ) (ht : 0 < t)
    (h : ∀ i < t, Small N R ((cat N)^[i] v)) :
    ∃ w : ℤ × ℤ, castZ N w = v ∧ ∀ i < t, |(catZ^[i] w).1| ≤ R ∧ |(catZ^[i] w).2| ≤ R := by
  obtain ⟨w, hw1, hw2, hwv⟩ := h 0 ht
  simp only [iterate_zero, id_eq] at hwv
  refine ⟨w, hwv, ?_⟩
  intro i
  induction i with
  | zero => intro _; exact ⟨hw1, hw2⟩
  | succ i ih =>
    intro hi
    obtain ⟨b1, b2⟩ := ih (by omega)
    set z := catZ^[i] w
    obtain ⟨w', hw'1, hw'2, hw'v⟩ := h (i + 1) hi
    have hc : castZ N (catZ z) = (cat N)^[i + 1] v := by
      rw [castZ_catZ, castZ_catZ_iterate, hwv, iterate_succ_apply']
    have e : catZ z = w' := by
      have hcc := hc.trans hw'v.symm
      simp only [castZ, Prod.mk.injEq] at hcc
      have hb1 : |(catZ z).1| ≤ 3 * R := by
        simp only [catZ]
        calc |2 * z.1 + z.2| ≤ |2 * z.1| + |z.2| := abs_add_le _ _
          _ = 2 * |z.1| + |z.2| := by rw [abs_mul]; norm_num
          _ ≤ 3 * R := by linarith
      have hb2 : |(catZ z).2| ≤ 3 * R := by
        simp only [catZ]
        calc |z.1 + z.2| ≤ |z.1| + |z.2| := abs_add_le _ _
          _ ≤ 3 * R := by linarith [abs_nonneg z.1]
      ext
      · exact int_unique N hR hb1 hw'1 hcc.1
      · exact int_unique N hR hb2 hw'2 hcc.2
    rw [iterate_succ_apply', e]
    exact ⟨hw'1, hw'2⟩

/-- The cell of `x` in the join `P ∨ c⁻¹P ∨ … ∨ c^{-(t-1)}P`. -/
def cell {ι : Type*} [DecidableEq ι] [NeZero N] (P : ZMod N × ZMod N → ι) (t : ℕ)
    (x : ZMod N × ZMod N) : Finset (ZMod N × ZMod N) :=
  Finset.univ.filter (fun y => ∀ i < t, P ((cat N)^[i] y) = P ((cat N)^[i] x))

/-- The integer box of radius `R`. -/
def zbox (R : ℤ) : Finset (ℤ × ℤ) := Finset.Icc (-R) R ×ˢ Finset.Icc (-R) R

/-- The integer vectors that stay `R`-small at times `0` and `s`. -/
def tset (R : ℤ) (s : ℕ) : Finset (ℤ × ℤ) :=
  (zbox R).filter (fun w => |(catZ^[s] w).1| ≤ R ∧ |(catZ^[s] w).2| ≤ R)

/-- **Every cell of the join embeds in `tset`.** -/
theorem cell_card_le_tset {ι : Type*} [DecidableEq ι] [NeZero N] (P : ZMod N × ZMod N → ι)
    {R : ℤ} (hR : 4 * R < N) (hP : ∀ a b, P a = P b → Small N R (a - b))
    (t : ℕ) (ht : 0 < t) (x : ZMod N × ZMod N) :
    (cell N P t x).card ≤ (tset R (t - 1)).card := by
  classical
  have key : ∀ y ∈ cell N P t x, ∃ w : ℤ × ℤ, castZ N w = y - x ∧ w ∈ tset R (t - 1) := by
    intro y hy
    simp only [cell, Finset.mem_filter, Finset.mem_univ, true_and] at hy
    have hs : ∀ i < t, Small N R ((cat N)^[i] (y - x)) := by
      intro i hi
      rw [← cat_iterate_sub]; exact hP _ _ (hy i hi)
    obtain ⟨w, hw, hb⟩ := lift_small N hR (y - x) t ht hs
    refine ⟨w, hw, ?_⟩
    simp only [tset, zbox, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc]
    have h0 := hb 0 ht
    have h1 := hb (t - 1) (by omega)
    simp only [iterate_zero, id_eq] at h0
    refine ⟨⟨abs_le.mp h0.1, abs_le.mp h0.2⟩, h1⟩
  choose! g hg1 hg2 using key
  apply Finset.card_le_card_of_injOn g (fun y hy => hg2 y hy)
  intro y1 hy1 y2 hy2 he
  have := (hg1 y1 hy1).symm.trans ((congrArg (castZ N) he).trans (hg1 y2 hy2))
  simpa using this

/-- The unstable and stable eigen-coordinates. -/
noncomputable def ea (w : ℤ × ℤ) : ℝ := goldenRatio * w.1 + w.2
noncomputable def eb (w : ℤ × ℤ) : ℝ := w.1 - goldenRatio * w.2

theorem ea_catZ (w : ℤ × ℤ) : ea (catZ w) = goldenRatio ^ 2 * ea w := by
  simp only [ea, catZ]; push_cast
  have h := goldenRatio_sq
  generalize goldenRatio = g at h ⊢
  linear_combination (-((g + 1) * (w.1 : ℝ) + w.2)) * h

theorem eb_catZ (w : ℤ × ℤ) : eb (catZ w) = goldenConj ^ 2 * eb w := by
  simp only [eb, catZ]; push_cast
  have h1 : goldenConj = 1 - goldenRatio := by
    have := goldenRatio_add_goldenConj; linarith
  rw [h1]
  have h := goldenRatio_sq
  generalize goldenRatio = g at h ⊢
  linear_combination (-(w.1 : ℝ) + (g - 1) * (w.2 : ℝ)) * h

theorem ea_iterate (n : ℕ) (w : ℤ × ℤ) : ea (catZ^[n] w) = (goldenRatio ^ 2) ^ n * ea w := by
  induction n with
  | zero => simp
  | succ n ih => rw [iterate_succ_apply', ea_catZ, ih]; ring

theorem eb_iterate (n : ℕ) (w : ℤ × ℤ) : eb (catZ^[n] w) = (goldenConj ^ 2) ^ n * eb w := by
  induction n with
  | zero => simp
  | succ n ih => rw [iterate_succ_apply', eb_catZ, ih]; ring

theorem abs_ea_le {R : ℤ} (w : ℤ × ℤ) (h1 : |w.1| ≤ R) (h2 : |w.2| ≤ R) :
    |ea w| ≤ goldenRatio ^ 2 * R := by
  have h1' : |(w.1 : ℝ)| ≤ R := by exact_mod_cast h1
  have h2' : |(w.2 : ℝ)| ≤ R := by exact_mod_cast h2
  have hp := goldenRatio_pos
  calc |ea w| ≤ |goldenRatio * w.1| + |(w.2 : ℝ)| := abs_add_le _ _
    _ = goldenRatio * |(w.1 : ℝ)| + |(w.2 : ℝ)| := by rw [abs_mul, abs_of_pos hp]
    _ ≤ goldenRatio * R + R := by gcongr
    _ = goldenRatio ^ 2 * R := by rw [goldenRatio_sq]; ring

theorem abs_eb_le {R : ℤ} (w : ℤ × ℤ) (h1 : |w.1| ≤ R) (h2 : |w.2| ≤ R) :
    |eb w| ≤ goldenRatio ^ 2 * R := by
  have h1' : |(w.1 : ℝ)| ≤ R := by exact_mod_cast h1
  have h2' : |(w.2 : ℝ)| ≤ R := by exact_mod_cast h2
  have hp := goldenRatio_pos
  calc |eb w| ≤ |(w.1 : ℝ)| + |goldenRatio * w.2| := abs_sub _ _
    _ = |(w.1 : ℝ)| + goldenRatio * |(w.2 : ℝ)| := by rw [abs_mul, abs_of_pos hp]
    _ ≤ R + goldenRatio * R := by gcongr
    _ = goldenRatio ^ 2 * R := by rw [goldenRatio_sq]; ring

/-- Coordinates are recovered from the eigen-coordinates. -/
theorem abs_coord_le (w : ℤ × ℤ) :
    |(w.1 : ℝ)| ≤ |ea w| + |eb w| ∧ |(w.2 : ℝ)| ≤ |ea w| + |eb w| := by
  have hp := goldenRatio_pos
  have hq : (0 : ℝ) < goldenRatio ^ 2 + 1 := by positivity
  have e1 : (w.1 : ℝ) = (goldenRatio * ea w + eb w) / (goldenRatio ^ 2 + 1) := by
    simp only [ea, eb]; field_simp; ring
  have e2 : (w.2 : ℝ) = (ea w - goldenRatio * eb w) / (goldenRatio ^ 2 + 1) := by
    simp only [ea, eb]; field_simp; ring
  have hφ : goldenRatio ≤ goldenRatio ^ 2 + 1 := by nlinarith [goldenRatio_sq]
  have h1 : (1 : ℝ) ≤ goldenRatio ^ 2 + 1 := by nlinarith
  constructor
  · rw [e1, abs_div, abs_of_pos hq, div_le_iff₀ hq]
    calc |goldenRatio * ea w + eb w| ≤ goldenRatio * |ea w| + |eb w| := by
          calc _ ≤ |goldenRatio * ea w| + |eb w| := abs_add_le _ _
            _ = _ := by rw [abs_mul, abs_of_pos hp]
      _ ≤ (|ea w| + |eb w|) * (goldenRatio ^ 2 + 1) := by
          nlinarith [abs_nonneg (ea w), abs_nonneg (eb w)]
  · rw [e2, abs_div, abs_of_pos hq, div_le_iff₀ hq]
    calc |ea w - goldenRatio * eb w| ≤ |ea w| + goldenRatio * |eb w| := by
          calc _ ≤ |ea w| + |goldenRatio * eb w| := abs_sub _ _
            _ = _ := by rw [abs_mul, abs_of_pos hp]
      _ ≤ (|ea w| + |eb w|) * (goldenRatio ^ 2 + 1) := by
          nlinarith [abs_nonneg (ea w), abs_nonneg (eb w)]

/-- **The hyperbolic count.**  For every `m`, the number of integer vectors
that are `R`-small at times `0` and `s` is at most `(2ρ + 1)²` with
`ρ = φ² R (φ^{2m - 2s} + φ^{-2m})`; with `m ≈ s/2` this is
`O(R² λ^{-s} + 1)`, `λ = φ²`. -/
theorem tset_card_le (R : ℤ) (hR : 0 ≤ R) (s m : ℕ) :
    ((tset R s).card : ℝ) ≤
      (2 * (goldenRatio ^ 2 * R * (goldenRatio ^ (2 * m) / goldenRatio ^ (2 * s)
        + 1 / goldenRatio ^ (2 * m))) + 1) ^ 2 := by
  classical
  set ρ := goldenRatio ^ 2 * R * (goldenRatio ^ (2 * m) / goldenRatio ^ (2 * s)
        + 1 / goldenRatio ^ (2 * m)) with hρ
  have hp := goldenRatio_pos
  have hRr : (0 : ℝ) ≤ R := by exact_mod_cast hR
  have hρ0 : 0 ≤ ρ := by positivity
  have hbound : ∀ w ∈ tset R s, |((catZ^[m] w).1 : ℝ)| ≤ ρ ∧ |((catZ^[m] w).2 : ℝ)| ≤ ρ := by
    intro w hw
    simp only [tset, zbox, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc] at hw
    obtain ⟨⟨h1, h2⟩, h3, h4⟩ := hw
    have hw1 : |w.1| ≤ R := abs_le.mpr h1
    have hw2 : |w.2| ≤ R := abs_le.mpr h2
    have hA : |ea (catZ^[s] w)| ≤ goldenRatio ^ 2 * R := abs_ea_le _ h3 h4
    have hB : |eb w| ≤ goldenRatio ^ 2 * R := abs_eb_le _ hw1 hw2
    rw [ea_iterate] at hA
    have hpow : ∀ n : ℕ, (goldenRatio ^ 2) ^ n = goldenRatio ^ (2 * n) := fun n => by
      rw [← pow_mul]
    have hps : 0 < goldenRatio ^ (2 * s) := by positivity
    have hpm : 0 < goldenRatio ^ (2 * m) := by positivity
    have hea : |ea w| ≤ goldenRatio ^ 2 * R / goldenRatio ^ (2 * s) := by
      rw [abs_mul, abs_of_pos (by positivity), hpow] at hA
      rw [le_div_iff₀ hps]; linarith
    have hu1 : |ea (catZ^[m] w)| ≤ goldenRatio ^ 2 * R * (goldenRatio ^ (2 * m) / goldenRatio ^ (2 * s)) := by
      rw [ea_iterate, abs_mul, abs_of_pos (by positivity), hpow]
      calc goldenRatio ^ (2 * m) * |ea w|
          ≤ goldenRatio ^ (2 * m) * (goldenRatio ^ 2 * R / goldenRatio ^ (2 * s)) :=
            mul_le_mul_of_nonneg_left hea hpm.le
        _ = _ := by ring
    have hconj : |goldenConj| = 1 / goldenRatio := by
      have := inv_goldenRatio
      rw [one_div, this, abs_of_neg goldenConj_neg]
    have hu2 : |eb (catZ^[m] w)| ≤ goldenRatio ^ 2 * R * (1 / goldenRatio ^ (2 * m)) := by
      rw [eb_iterate, abs_mul, abs_pow, abs_pow, hconj]
      have : ((1 / goldenRatio) ^ 2) ^ m = 1 / goldenRatio ^ (2 * m) := by
        rw [← pow_mul, one_div_pow]
      rw [this]
      calc 1 / goldenRatio ^ (2 * m) * |eb w| ≤ 1 / goldenRatio ^ (2 * m) * (goldenRatio ^ 2 * R) :=
            mul_le_mul_of_nonneg_left hB (by positivity)
        _ = _ := by ring
    have hc := abs_coord_le (catZ^[m] w)
    constructor <;> [linarith [hc.1]; linarith [hc.2]]
  set K : ℤ := ⌊ρ⌋
  have hK0 : 0 ≤ K := Int.floor_nonneg.mpr hρ0
  have hmaps : ∀ w ∈ tset R s, catZ^[m] w ∈ zbox K := by
    intro w hw
    obtain ⟨b1, b2⟩ := hbound w hw
    simp only [zbox, Finset.mem_product, Finset.mem_Icc]
    have c1 : |(catZ^[m] w).1| ≤ K := Int.le_floor.mpr (by push_cast; exact b1)
    have c2 : |(catZ^[m] w).2| ≤ K := Int.le_floor.mpr (by push_cast; exact b2)
    exact ⟨abs_le.mp c1, abs_le.mp c2⟩
  have hcard := Finset.card_le_card_of_injOn (catZ^[m]) hmaps
    (catZ_injective.iterate m).injOn
  have hz : ((zbox K).card : ℝ) = (2 * (K : ℝ) + 1) ^ 2 := by
    simp only [zbox, Finset.card_product, Int.card_Icc]
    have : (K + 1 - -K).toNat = ((2 * K + 1 : ℤ)).toNat := by ring_nf
    rw [this]
    have e : (((2 * K + 1).toNat : ℕ) : ℝ) = 2 * (K : ℝ) + 1 := by
      have h := Int.toNat_of_nonneg (show 0 ≤ 2 * K + 1 by omega)
      have h2 := congrArg (fun z : ℤ => (z : ℝ)) h
      simp only [Int.cast_natCast] at h2
      rw [h2]; push_cast; ring
    push_cast
    rw [e]; ring
  have hKρ : (K : ℝ) ≤ ρ := Int.floor_le ρ
  calc ((tset R s).card : ℝ) ≤ (zbox K).card := by exact_mod_cast hcard
    _ = (2 * (K : ℝ) + 1) ^ 2 := hz
    _ ≤ (2 * ρ + 1) ^ 2 := by
        have : (0 : ℝ) ≤ K := by exact_mod_cast hK0
        gcongr

/-- Entropy (nats) of a partition of a finite set, written through the cells:
`H = ∑_x |X|⁻¹ log (|X| / |C(x)|)`. -/
noncomputable def cellEntropy {X : Type*} [Fintype X] (c : X → Finset X) : ℝ :=
  ∑ x, (1 / (Fintype.card X : ℝ)) * Real.log ((Fintype.card X : ℝ) / (c x).card)

/-- `cellEntropy` is the Shannon entropy of the labelling under the uniform
granular measure. -/
theorem cellEntropy_eq_entropy {X β : Type*} [Fintype X] [DecidableEq β] (lab : X → β) :
    cellEntropy (fun x => Finset.univ.filter (fun y => lab y = lab x)) =
      QE.Info.entropy (Finset.univ.image lab)
        (fun c => ((Finset.univ.filter (fun y => lab y = c)).card : ℝ) / Fintype.card X) := by
  classical
  unfold cellEntropy QE.Info.entropy
  rw [← Finset.sum_fiberwise_of_maps_to (g := lab) (t := Finset.univ.image lab)
    (fun x _ => Finset.mem_image_of_mem lab (Finset.mem_univ x))]
  apply Finset.sum_congr rfl
  intro c _
  have : ∀ x ∈ Finset.univ.filter (fun x => lab x = c),
      (1 / (Fintype.card X : ℝ)) * Real.log ((Fintype.card X : ℝ) /
        (Finset.univ.filter (fun y => lab y = lab x)).card)
      = (1 / (Fintype.card X : ℝ)) * Real.log ((Fintype.card X : ℝ) /
        (Finset.univ.filter (fun y => lab y = c)).card) := by
    intro x hx
    rw [(Finset.mem_filter.mp hx).2]
  rw [Finset.sum_congr rfl this, Finset.sum_const, nsmul_eq_mul, negMulLog]
  set F := ((Finset.univ.filter (fun y => lab y = c)).card : ℝ)
  set n := (Fintype.card X : ℝ)
  rw [show n / F = (F / n)⁻¹ by rw [inv_div], Real.log_inv]
  ring

/-- **Entropy from the largest cell**: if every cell has at most `C` points,
`H ≥ log (|X| / C)`. -/
theorem cellEntropy_ge {X : Type*} [Fintype X] [Nonempty X] (c : X → Finset X)
    (hmem : ∀ x, x ∈ c x) (C : ℝ) (hC : ∀ x, ((c x).card : ℝ) ≤ C) :
    Real.log ((Fintype.card X : ℝ) / C) ≤ cellEntropy c := by
  unfold cellEntropy
  have hn : (0 : ℝ) < Fintype.card X := by exact_mod_cast Fintype.card_pos
  have hterm : ∀ x, (1 / (Fintype.card X : ℝ)) * Real.log ((Fintype.card X : ℝ) / C) ≤
      (1 / (Fintype.card X : ℝ)) * Real.log ((Fintype.card X : ℝ) / (c x).card) := by
    intro x
    have h1 : (0 : ℝ) < (c x).card := by exact_mod_cast Finset.card_pos.mpr ⟨x, hmem x⟩
    have hCp : 0 < C := lt_of_lt_of_le h1 (hC x)
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    apply Real.log_le_log (by positivity)
    exact div_le_div_of_nonneg_left hn.le h1 (hC x)
  calc Real.log ((Fintype.card X : ℝ) / C)
      = ∑ _x : X, (1 / (Fintype.card X : ℝ)) * Real.log ((Fintype.card X : ℝ) / C) := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; field_simp
    _ ≤ _ := Finset.sum_le_sum fun x _ => hterm x

/-- The entropy never exceeds the total budget `log |X|`. -/
theorem cellEntropy_le_log_card {X : Type*} [Fintype X] (c : X → Finset X)
    (hmem : ∀ x, x ∈ c x) : cellEntropy c ≤ Real.log (Fintype.card X) := by
  unfold cellEntropy
  rcases isEmpty_or_nonempty X with hX | hX
  · simp
  have hn : (0 : ℝ) < Fintype.card X := by exact_mod_cast Fintype.card_pos
  calc ∑ x, (1 / (Fintype.card X : ℝ)) * Real.log ((Fintype.card X : ℝ) / (c x).card)
      ≤ ∑ _x : X, (1 / (Fintype.card X : ℝ)) * Real.log (Fintype.card X) := by
        apply Finset.sum_le_sum; intro x _
        have h1 : (1 : ℝ) ≤ (c x).card := by exact_mod_cast Finset.card_pos.mpr ⟨x, hmem x⟩
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        apply Real.log_le_log (by positivity)
        exact div_le_self hn.le h1
    _ = Real.log (Fintype.card X) := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; field_simp

theorem mem_cell {ι : Type*} [DecidableEq ι] [NeZero N] (P : ZMod N × ZMod N → ι) (t : ℕ)
    (x : ZMod N × ZMod N) : x ∈ cell N P t x := by
  simp [cell]

/-- The cell of the join is the fibre of the itinerary map. -/
theorem cell_eq_fibre {ι : Type*} [DecidableEq ι] [NeZero N] (P : ZMod N × ZMod N → ι) (t : ℕ)
    (x : ZMod N × ZMod N) :
    cell N P t x = Finset.univ.filter (fun y =>
      (fun i : Fin t => P ((cat N)^[i] y)) = (fun i : Fin t => P ((cat N)^[i] x))) := by
  ext y
  simp only [cell, Finset.mem_filter, Finset.mem_univ, true_and, funext_iff]
  exact ⟨fun h i => h i i.isLt, fun h i hi => h ⟨i, hi⟩⟩

/-- **Granular Pesin formula, lower bound.**  For any partition `P` of the
granular torus whose cells have sup-diameter `≤ R` (`4R < N`), and every
`t ≥ 1` and `m`, the granular entropy of the `t`-step join satisfies
`H_t ≥ log (N² / (2ρ + 1)²)`, `ρ = φ² R (φ^{2m-2(t-1)} + φ^{-2m})`. -/
theorem cat_join_entropy_ge {ι : Type*} [DecidableEq ι] [NeZero N] (P : ZMod N × ZMod N → ι)
    {R : ℤ} (hR0 : 0 ≤ R) (hR : 4 * R < N) (hP : ∀ a b, P a = P b → Small N R (a - b))
    (t : ℕ) (ht : 0 < t) (m : ℕ) :
    Real.log ((N : ℝ) ^ 2 / (2 * (goldenRatio ^ 2 * R * (goldenRatio ^ (2 * m) /
        goldenRatio ^ (2 * (t - 1)) + 1 / goldenRatio ^ (2 * m))) + 1) ^ 2)
      ≤ cellEntropy (cell N P t) := by
  have hcard : (Fintype.card (ZMod N × ZMod N) : ℝ) = (N : ℝ) ^ 2 := by
    simp [Fintype.card_prod, ZMod.card]; ring
  rw [← hcard]
  apply cellEntropy_ge _ (mem_cell N P t)
  intro x
  calc ((cell N P t x).card : ℝ) ≤ (tset R (t - 1)).card := by
        exact_mod_cast cell_card_le_tset N P hR hP t ht x
    _ ≤ _ := tset_card_le R hR0 (t - 1) m

/-- **Saturation.**  `H_t ≤ log N² = 2 log N` for every `t`. -/
theorem cat_join_entropy_le {ι : Type*} [DecidableEq ι] [NeZero N] (P : ZMod N × ZMod N → ι)
    (t : ℕ) : cellEntropy (cell N P t) ≤ 2 * Real.log N := by
  have h := cellEntropy_le_log_card (cell N P t) (mem_cell N P t)
  have hcard : (Fintype.card (ZMod N × ZMod N) : ℝ) = (N : ℝ) ^ 2 := by
    simp [Fintype.card_prod, ZMod.card]; ring
  rw [hcard, Real.log_pow] at h; exact_mod_cast h

/-- **Exact recurrence of the join.**  If `c^Π = id`, the join stops refining
at `t = Π`: `t · h_ε(t)` is constant for `t ≥ Π`. -/
theorem cell_stabilises {ι : Type*} [DecidableEq ι] [NeZero N] (P : ZMod N × ZMod N → ι)
    (per : ℕ) (hper : 0 < per) (hid : ∀ p, (cat N)^[per] p = p) (t : ℕ) (ht : per ≤ t) :
    cell N P t = cell N P per := by
  have hk : ∀ k p, (cat N)^[per * k] p = p := by
    intro k
    induction k with
    | zero => intro p; rfl
    | succ k ih => intro p; rw [Nat.mul_succ, iterate_add_apply, hid, ih]
  have hmod : ∀ i p, (cat N)^[i] p = (cat N)^[i % per] p := by
    intro i p
    conv_lhs => rw [← Nat.mod_add_div i per]
    rw [iterate_add_apply, hk]
  funext x
  ext y
  simp only [cell, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · intro h i hi; exact h i (by omega)
  · intro h i _
    rw [hmod i y, hmod i x]
    exact h _ (Nat.mod_lt _ hper)

/-- The grid partition into `q²` squares of side `W` (`N = q W`). -/
def grid (W : ℕ) (a : ZMod N × ZMod N) : ℕ × ℕ := (a.1.val / W, a.2.val / W)

theorem grid_small [NeZero N] (W : ℕ) (hW : 0 < W) (a b : ZMod N × ZMod N)
    (h : grid N W a = grid N W b) : Small N ((W : ℤ) - 1) (a - b) := by
  simp only [grid, Prod.mk.injEq] at h
  refine ⟨((a.1.val : ℤ) - b.1.val, (a.2.val : ℤ) - b.2.val), ?_, ?_, ?_⟩
  · have h1 := Nat.div_add_mod a.1.val W
    have h2 := Nat.div_add_mod b.1.val W
    have h3 := Nat.mod_lt a.1.val hW
    have h4 := Nat.mod_lt b.1.val hW
    rw [h.1] at h1
    rw [abs_le]; constructor <;> omega
  · have h1 := Nat.div_add_mod a.2.val W
    have h2 := Nat.div_add_mod b.2.val W
    have h3 := Nat.mod_lt a.2.val hW
    have h4 := Nat.mod_lt b.2.val hW
    rw [h.2] at h1
    rw [abs_le]; constructor <;> omega
  · ext <;> simp [castZ]

/-- **Granular Pesin formula for the cat map with the `q × q` grid partition.**
For `N = q W` with `q ≥ 4`, every `t ≥ 1` and every `m`,
`log (N² / (2ρ + 1)²) ≤ H_t ≤ 2 log N`, `ρ = φ² (W - 1)(φ^{2m-2(t-1)} + φ^{-2m})`. -/
theorem cat_grid_pesin [NeZero N] (q W : ℕ) (hN : N = q * W) (hq : 4 ≤ q) (hW : 0 < W)
    (t : ℕ) (ht : 0 < t) (m : ℕ) :
    Real.log ((N : ℝ) ^ 2 / (2 * (goldenRatio ^ 2 * ((W : ℤ) - 1 : ℤ) * (goldenRatio ^ (2 * m) /
        goldenRatio ^ (2 * (t - 1)) + 1 / goldenRatio ^ (2 * m))) + 1) ^ 2)
      ≤ cellEntropy (cell N (grid N W) t) ∧
    cellEntropy (cell N (grid N W) t) ≤ 2 * Real.log N := by
  refine ⟨cat_join_entropy_ge N (grid N W) (by omega) ?_ (grid_small N W hW) t ht m,
    cat_join_entropy_le N _ t⟩
  have : (4 : ℤ) * W ≤ q * W := by
    have : (4 : ℤ) ≤ q := by exact_mod_cast hq
    nlinarith
  rw [hN]; push_cast; linarith

/-! ### The upper bound: tiles -/

/-- `∑_{x ∈ D} 1 / |class of x in D| = number of classes`. -/
theorem sum_inv_class {X β : Type*} [DecidableEq β] (D : Finset X) (lab : X → β) :
    ∑ x ∈ D, (1 : ℝ) / (D.filter (fun y => lab y = lab x)).card = (D.image lab).card := by
  classical
  rw [← Finset.sum_fiberwise_of_maps_to (g := lab) (t := D.image lab)
    (fun x hx => Finset.mem_image_of_mem lab hx)]
  rw [Finset.card_eq_sum_ones, Nat.cast_sum]
  apply Finset.sum_congr rfl
  intro c hc
  have : ∀ x ∈ D.filter (fun x => lab x = c),
      (1 : ℝ) / (D.filter (fun y => lab y = lab x)).card =
        1 / (D.filter (fun y => lab y = c)).card := by
    intro x hx; rw [(Finset.mem_filter.mp hx).2]
  rw [Finset.sum_congr rfl this, Finset.sum_const, nsmul_eq_mul]
  obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hc
  have hpos : (0 : ℝ) < (D.filter (fun y => lab y = lab x)).card := by
    exact_mod_cast Finset.card_pos.mpr
      ⟨x, (show x ∈ D.filter (fun y => lab y = lab x) from Finset.mem_filter.mpr ⟨hx, rfl⟩)⟩
  field_simp
  simp

/-- **Jensen on a tile**: the entropy of a labelling restricted to `D`
(uniform on `D`) is at most `log` of the number of labels seen on `D`. -/
theorem tile_jensen {X β : Type*} [DecidableEq β] (D : Finset X) (hD : D.Nonempty)
    (lab : X → β) :
    ∑ x ∈ D, (1 / (D.card : ℝ)) * Real.log ((D.card : ℝ) / (D.filter (fun y => lab y = lab x)).card)
      ≤ Real.log (D.image lab).card := by
  have hDpos : (0 : ℝ) < D.card := by exact_mod_cast hD.card_pos
  have hcls : ∀ x ∈ D, (0 : ℝ) < (D.filter (fun y => lab y = lab x)).card := by
    intro x hx
    exact_mod_cast Finset.card_pos.mpr
      ⟨x, (show x ∈ D.filter (fun y => lab y = lab x) from Finset.mem_filter.mpr ⟨hx, rfl⟩)⟩
  have hJ := (strictConcaveOn_log_Ioi.concaveOn).le_map_sum (t := D)
    (w := fun _ => 1 / (D.card : ℝ))
    (p := fun x => (D.card : ℝ) / (D.filter (fun y => lab y = lab x)).card)
    (fun _ _ => by positivity)
    (by rw [Finset.sum_const, nsmul_eq_mul]; field_simp)
    (fun x hx => Set.mem_Ioi.mpr (div_pos hDpos (hcls x hx)))
  simp only [smul_eq_mul] at hJ
  have hsum : ∑ x ∈ D, 1 / (D.card : ℝ) * ((D.card : ℝ) / (D.filter (fun y => lab y = lab x)).card)
      = (D.image lab).card := by
    rw [← sum_inv_class D lab]
    apply Finset.sum_congr rfl; intro x _; field_simp
  rw [hsum] at hJ
  exact hJ

/-- **Splitting along tiles.**  For any labelling `lab` and any tiling `τ`,
`H(lab) ≤ H(τ) + ∑_x |X|⁻¹ log (number of labels on the tile of x)`. -/
theorem cellEntropy_le_tiles {X β κ : Type*} [Fintype X] [DecidableEq β] [DecidableEq κ]
    (lab : X → β) (τ : X → κ) :
    cellEntropy (fun x => Finset.univ.filter (fun y => lab y = lab x)) ≤
      cellEntropy (fun x => Finset.univ.filter (fun y => τ y = τ x)) +
        ∑ x, (1 / (Fintype.card X : ℝ)) *
          Real.log ((Finset.univ.filter (fun y => τ y = τ x)).image lab).card := by
  classical
  rcases isEmpty_or_nonempty X with hX | hX
  · simp [cellEntropy]
  set n := (Fintype.card X : ℝ)
  have hn : 0 < n := Nat.cast_pos.mpr Fintype.card_pos
  set T := fun x => Finset.univ.filter (fun y => τ y = τ x)
  set C' := fun x => (T x).filter (fun y => lab y = lab x)
  have hT : ∀ x, x ∈ T x := fun x => by simp [T]
  have hC' : ∀ x, x ∈ C' x := fun x => by simp [C', T]
  have hTpos : ∀ x, (0 : ℝ) < (T x).card := fun x => by exact_mod_cast Finset.card_pos.mpr ⟨x, hT x⟩
  have hCpos : ∀ x, (0 : ℝ) < (C' x).card := fun x => by exact_mod_cast Finset.card_pos.mpr ⟨x, hC' x⟩
  -- step 1: refine the cells
  have h1 : cellEntropy (fun x => Finset.univ.filter (fun y => lab y = lab x)) ≤
      ∑ x, (1 / n) * Real.log (n / (C' x).card) := by
    unfold cellEntropy
    apply Finset.sum_le_sum; intro x _
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    apply Real.log_le_log (by
      have : (0 : ℝ) < (Finset.univ.filter (fun y => lab y = lab x)).card := by
        exact_mod_cast Finset.card_pos.mpr ⟨x, by simp⟩
      positivity)
    apply div_le_div_of_nonneg_left hn.le (hCpos x)
    exact_mod_cast Finset.card_le_card (fun y hy => by
      simp only [C', T, Finset.mem_filter, Finset.mem_univ, true_and] at hy ⊢; exact hy.2)
  -- step 2: split the logarithm
  have h2 : ∑ x, (1 / n) * Real.log (n / (C' x).card) =
      cellEntropy T + ∑ x, (1 / n) * Real.log ((T x).card / (C' x).card) := by
    unfold cellEntropy
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl; intro x _
    rw [← mul_add, ← Real.log_mul (div_pos hn (hTpos x)).ne' (div_pos (hTpos x) (hCpos x)).ne']
    congr 2
    have := (hTpos x).ne'
    field_simp
  -- step 3: Jensen on every tile
  have h3 : ∑ x, (1 / n) * Real.log ((T x).card / (C' x).card) ≤
      ∑ x, (1 / n) * Real.log ((T x).image lab).card := by
    rw [← Finset.sum_fiberwise_of_maps_to (g := τ) (t := Finset.univ.image τ)
      (fun x _ => Finset.mem_image_of_mem τ (Finset.mem_univ x))]
    rw [← Finset.sum_fiberwise_of_maps_to (g := τ) (t := Finset.univ.image τ)
      (s := Finset.univ) (f := fun x => (1 / n) * Real.log ((T x).image lab).card)
      (fun x _ => Finset.mem_image_of_mem τ (Finset.mem_univ x))]
    apply Finset.sum_le_sum
    intro d hd
    obtain ⟨x0, _, rfl⟩ := Finset.mem_image.mp hd
    set D := Finset.univ.filter (fun x => τ x = τ x0)
    have hDT : ∀ x ∈ D, T x = D := by
      intro x hx
      simp only [D, Finset.mem_filter, Finset.mem_univ, true_and] at hx
      ext y; simp [T, D, hx]
    have hDne : D.Nonempty := ⟨x0, by simp [D]⟩
    have hJ := tile_jensen D hDne lab
    have hDpos : (0 : ℝ) < D.card := by exact_mod_cast hDne.card_pos
    calc ∑ x ∈ D, (1 / n) * Real.log ((T x).card / (C' x).card)
        = ((D.card : ℝ) / n) * ∑ x ∈ D, (1 / (D.card : ℝ)) *
            Real.log ((D.card : ℝ) / (D.filter (fun y => lab y = lab x)).card) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl; intro x hx
          simp only [C']
          rw [hDT x hx]
          field_simp
      _ ≤ ((D.card : ℝ) / n) * Real.log (D.image lab).card :=
          mul_le_mul_of_nonneg_left hJ (by positivity)
      _ = ∑ x ∈ D, (1 / n) * Real.log ((T x).image lab).card := by
          rw [Finset.sum_congr rfl (fun x hx => by rw [hDT x hx]), Finset.sum_const, nsmul_eq_mul]
          field_simp
  calc _ ≤ _ := h1
    _ = _ := h2
    _ ≤ cellEntropy T + ∑ x, (1 / n) * Real.log ((T x).image lab).card := by linarith [h3]

/-- The entropy of any labelling is at most `log` of the number of labels. -/
theorem cellEntropy_le_log_image {X β : Type*} [Fintype X] [Nonempty X] [DecidableEq β]
    (lab : X → β) :
    cellEntropy (fun x => Finset.univ.filter (fun y => lab y = lab x)) ≤
      Real.log (Finset.univ.image lab).card := by
  have h := tile_jensen (Finset.univ : Finset X) Finset.univ_nonempty lab
  unfold cellEntropy
  simpa [Finset.card_univ] using h

theorem catZ_right_inv : RightInverse catZInv catZ := by
  intro w; ext <;> simp [catZ, catZInv] <;> ring

theorem castZ_catZInv (w : ℤ × ℤ) : castZ N (catZInv w) = catInv N (castZ N w) := by
  ext <;> simp [castZ, catZInv, catInv]

theorem castZ_catZInv_iterate (i : ℕ) (w : ℤ × ℤ) :
    castZ N (catZInv^[i] w) = (catInv N)^[i] (castZ N w) := by
  induction i generalizing w with
  | zero => rfl
  | succ i ih => rw [iterate_succ_apply, iterate_succ_apply, ih, castZ_catZInv]

theorem catInv_sub (p q : ZMod N × ZMod N) : catInv N p - catInv N q = catInv N (p - q) := by
  ext <;> simp [catInv] <;> ring

theorem catInv_iterate_sub (t : ℕ) (p q : ZMod N × ZMod N) :
    (catInv N)^[t] p - (catInv N)^[t] q = (catInv N)^[t] (p - q) := by
  induction t generalizing p q with
  | zero => simp
  | succ t ih =>
    rw [iterate_succ_apply, iterate_succ_apply, iterate_succ_apply, ← catInv_sub]
    exact ih _ _

theorem cat_iterate_eq_catInv (m i : ℕ) (hi : i ≤ m) (x : ZMod N × ZMod N) :
    (cat N)^[i] x = (catInv N)^[m - i] ((cat N)^[m] x) := by
  have h : (cat N)^[m] x = (cat N)^[m - i] ((cat N)^[i] x) := by
    rw [← iterate_add_apply, Nat.sub_add_cancel hi]
  rw [h]
  exact ((cat_left_inv N).iterate (m - i) _).symm

theorem ea_catZInv (w : ℤ × ℤ) : ea (catZInv w) = ea w / goldenRatio ^ 2 := by
  have h := ea_catZ (catZInv w)
  rw [catZ_right_inv w] at h
  have : goldenRatio ^ 2 ≠ 0 := by positivity
  rw [eq_div_iff this, h]; ring

theorem eb_catZInv (w : ℤ × ℤ) : eb (catZInv w) = eb w / goldenConj ^ 2 := by
  have h := eb_catZ (catZInv w)
  rw [catZ_right_inv w] at h
  have : goldenConj ^ 2 ≠ 0 := pow_ne_zero 2 goldenConj_neg.ne
  rw [eq_div_iff this, h]; ring

theorem abs_goldenConj : |goldenConj| = 1 / goldenRatio := by
  rw [one_div, inv_goldenRatio, abs_of_neg goldenConj_neg]

/-- Sup-norm growth of integer cat iterates: `≤ φ² (λ^j + 1) R`. -/
theorem catZ_iterate_coord_le (j : ℕ) (w : ℤ × ℤ) (R : ℤ) (h1 : |w.1| ≤ R) (h2 : |w.2| ≤ R) :
    |((catZ^[j] w).1 : ℝ)| ≤ goldenRatio ^ 2 * ((goldenRatio ^ 2) ^ j + 1) * R ∧
    |((catZ^[j] w).2 : ℝ)| ≤ goldenRatio ^ 2 * ((goldenRatio ^ 2) ^ j + 1) * R := by
  have hA := abs_ea_le w h1 h2
  have hB := abs_eb_le w h1 h2
  have hp := goldenRatio_pos
  have hea : |ea (catZ^[j] w)| ≤ (goldenRatio ^ 2) ^ j * (goldenRatio ^ 2 * R) := by
    rw [ea_iterate, abs_mul, abs_of_pos (by positivity)]
    exact mul_le_mul_of_nonneg_left hA (by positivity)
  have heb : |eb (catZ^[j] w)| ≤ 1 * (goldenRatio ^ 2 * R) := by
    rw [eb_iterate, abs_mul, abs_pow, abs_pow, abs_goldenConj]
    apply mul_le_mul _ hB (abs_nonneg _) (by norm_num)
    apply pow_le_one₀ (by positivity)
    rw [div_pow, one_pow]
    exact div_le_one_of_le₀ (by nlinarith [goldenRatio_sq, one_lt_goldenRatio]) (by positivity)
  have hc := abs_coord_le (catZ^[j] w)
  constructor <;> nlinarith [hc.1, hc.2]

theorem catZInv_iterate_coord_le (j : ℕ) (w : ℤ × ℤ) (R : ℤ) (h1 : |w.1| ≤ R) (h2 : |w.2| ≤ R) :
    |((catZInv^[j] w).1 : ℝ)| ≤ goldenRatio ^ 2 * ((goldenRatio ^ 2) ^ j + 1) * R ∧
    |((catZInv^[j] w).2 : ℝ)| ≤ goldenRatio ^ 2 * ((goldenRatio ^ 2) ^ j + 1) * R := by
  have hA := abs_ea_le w h1 h2
  have hB := abs_eb_le w h1 h2
  have hp := goldenRatio_pos
  have hiea : ∀ k, ea (catZInv^[k] w) = ea w / (goldenRatio ^ 2) ^ k := by
    intro k; induction k with
    | zero => simp
    | succ k ih => rw [iterate_succ_apply', ea_catZInv, ih, div_div, ← pow_succ]
  have hieb : ∀ k, eb (catZInv^[k] w) = eb w / (goldenConj ^ 2) ^ k := by
    intro k; induction k with
    | zero => simp
    | succ k ih =>
      rw [iterate_succ_apply', eb_catZInv, ih, div_div, ← pow_succ]
  have hea : |ea (catZInv^[j] w)| ≤ 1 * (goldenRatio ^ 2 * R) := by
    rw [hiea, abs_div, abs_of_pos (by positivity : (0 : ℝ) < (goldenRatio ^ 2) ^ j)]
    rw [div_le_iff₀ (by positivity)]
    have : (1 : ℝ) ≤ (goldenRatio ^ 2) ^ j :=
      one_le_pow₀ (by nlinarith [goldenRatio_sq, one_lt_goldenRatio])
    nlinarith [abs_nonneg (ea w)]
  have heb : |eb (catZInv^[j] w)| ≤ (goldenRatio ^ 2) ^ j * (goldenRatio ^ 2 * R) := by
    rw [hieb, abs_div, abs_pow, abs_pow, abs_goldenConj]
    have : ((1 / goldenRatio) ^ 2) ^ j = 1 / (goldenRatio ^ 2) ^ j := by
      rw [div_pow, one_pow, one_div_pow]
    rw [this, div_div_eq_mul_div, div_one]
    rw [mul_comm]
    exact mul_le_mul_of_nonneg_left hB (by positivity)
  have hc := abs_coord_le (catZInv^[j] w)
  constructor <;> nlinarith [hc.1, hc.2]

/-- The growth radius `ρ_j = φ² (λ^j + 1)(L - 1)` of a tile after `j` steps. -/
noncomputable def growth (L j : ℕ) : ℝ := goldenRatio ^ 2 * ((goldenRatio ^ 2) ^ j + 1) * ((L : ℤ) - 1 : ℤ)

/-- **Tiles stay small.**  If `c^m x` and `c^m y` lie in the same `L`-square,
then for every `i` the difference `c^i y - c^i x` lifts to an integer vector of
sup-norm at most `ρ_{|i-m|}`. -/
theorem tile_spread [NeZero N] (L : ℕ) (hL : 0 < L) (m i : ℕ) (x y : ZMod N × ZMod N)
    (hxy : grid N L ((cat N)^[m] y) = grid N L ((cat N)^[m] x)) :
    ∃ v : ℤ × ℤ, castZ N v = (cat N)^[i] y - (cat N)^[i] x ∧
      (|(v.1 : ℝ)| ≤ growth L (if m ≤ i then i - m else m - i)) ∧
      (|(v.2 : ℝ)| ≤ growth L (if m ≤ i then i - m else m - i)) := by
  obtain ⟨w0, hw1, hw2, hw⟩ := grid_small N L hL _ _ hxy
  by_cases him : m ≤ i
  · refine ⟨catZ^[i - m] w0, ?_, ?_⟩
    · rw [castZ_catZ_iterate, hw, ← cat_iterate_sub, ← iterate_add_apply, ← iterate_add_apply,
        Nat.sub_add_cancel him]
    · simp only [him, ↓reduceIte]
      exact catZ_iterate_coord_le (i - m) w0 _ hw1 hw2
  · refine ⟨catZInv^[m - i] w0, ?_, ?_⟩
    · rw [castZ_catZInv_iterate, hw, ← catInv_iterate_sub,
        ← cat_iterate_eq_catInv N m i (by omega), ← cat_iterate_eq_catInv N m i (by omega)]
    · simp only [him, ↓reduceIte]
      exact catZInv_iterate_coord_le (m - i) w0 _ hw1 hw2

/-- `u` is within `r` of a boundary of the `W`-blocks. -/
def nearB (W r : ℕ) (u : ZMod N) : Prop := u.val % W < r ∨ W ≤ u.val % W + r

instance (W r : ℕ) (u : ZMod N) : Decidable (nearB N W r u) := by unfold nearB; infer_instance

/-- **No wrapping.**  A shift by at most `r` that changes the `W`-block of `u`
(with `N = q W`) forces `u` to be within `r` of a block boundary. -/
theorem near_of_block_change [NeZero N] (q W r : ℕ) (hN : N = q * W) (hW : 0 < W) (u : ZMod N)
    (w : ℤ) (hw : |w| ≤ r) (h : (u + (w : ZMod N)).val / W ≠ u.val / W) : nearB N W r u := by
  by_contra hc
  simp only [nearB, not_or, not_lt, not_le] at hc
  obtain ⟨hc1, hc2⟩ := hc
  have hu := ZMod.val_lt u
  have hd := Nat.div_add_mod u.val W
  have hq : u.val / W < q := by
    rw [Nat.div_lt_iff_lt_mul hW]; exact lt_of_lt_of_eq hu hN
  set a : ℤ := (u.val : ℤ) + w
  rw [abs_le] at hw
  have ha0 : 0 ≤ a := by simp only [a]; omega
  have hdZ : (W : ℤ) * (u.val / W : ℕ) + (u.val % W : ℕ) = u.val := by exact_mod_cast hd
  have haN : a < N := by
    simp only [a]
    have : (u.val / W + 1) * W ≤ N := (Nat.mul_le_mul_right W hq).trans_eq hN.symm
    have hZ : (((u.val / W : ℕ) : ℤ) + 1) * W ≤ N := by exact_mod_cast this
    have hc2' : ((u.val % W : ℕ) : ℤ) + r < W := by exact_mod_cast hc2
    nlinarith
  have hcast : u + (w : ZMod N) = ((a : ℤ) : ZMod N) := by
    simp only [a]; push_cast; rw [ZMod.natCast_zmod_val]
  have hval : ((u + (w : ZMod N)).val : ℤ) = a := by
    rw [hcast, ZMod.val_intCast, Int.emod_eq_of_lt ha0 haN]
  apply h
  apply Nat.div_eq_of_lt_le
  · have hc1' : (r : ℤ) ≤ ((u.val % W : ℕ) : ℤ) := by exact_mod_cast hc1
    have : (((u.val / W : ℕ) : ℤ) * W : ℤ) ≤ ((u + (w : ZMod N)).val : ℤ) := by
      rw [hval]; simp only [a]; nlinarith
    exact_mod_cast this
  · have hc2' : ((u.val % W : ℕ) : ℤ) + r < W := by exact_mod_cast hc2
    have : ((u + (w : ZMod N)).val : ℤ) < ((((u.val / W : ℕ) : ℤ) + 1) * W : ℤ) := by
      rw [hval]; simp only [a]; nlinarith
    exact_mod_cast this

/-- **Few points are near the boundaries**: at most `2 q r` residues. -/
theorem card_nearB [NeZero N] (q W r : ℕ) (hN : N = q * W) (hW : 0 < W) :
    (Finset.univ.filter (fun u : ZMod N => nearB N W r u)).card ≤ q * (2 * r) := by
  classical
  set E : Finset ℕ := Finset.range r ∪ Finset.Ico (W - r) W
  have hE : E.card ≤ 2 * r := by
    calc E.card ≤ (Finset.range r).card + (Finset.Ico (W - r) W).card := Finset.card_union_le _ _
      _ ≤ r + r := by simp; omega
      _ = 2 * r := by ring
  calc (Finset.univ.filter (fun u : ZMod N => nearB N W r u)).card
      ≤ (Finset.range q ×ˢ E).card := by
        apply Finset.card_le_card_of_injOn (fun u => (u.val / W, u.val % W))
        · intro u hu
          have hu' : nearB N W r u := by simpa using hu
          unfold nearB at hu'
          simp only [Finset.coe_product, Set.mem_prod, Finset.mem_coe, Finset.mem_range, E,
            Finset.mem_union, Finset.mem_Ico]
          refine ⟨?_, ?_⟩
          · rw [Nat.div_lt_iff_lt_mul hW]; rw [← hN]; exact ZMod.val_lt u
          · have := Nat.mod_lt u.val hW; omega
        · intro u _ v _ huv
          simp only [Prod.mk.injEq] at huv
          apply ZMod.val_injective
          rw [← Nat.div_add_mod u.val W, ← Nat.div_add_mod v.val W, huv.1, huv.2]
    _ = q * E.card := by rw [Finset.card_product, Finset.card_range]
    _ ≤ q * (2 * r) := Nat.mul_le_mul_left q hE

/-- The bad set: states within `r` of a grid line in either coordinate. -/
theorem card_bad [NeZero N] (q W r : ℕ) (hN : N = q * W) (hW : 0 < W) :
    (Finset.univ.filter (fun y : ZMod N × ZMod N => nearB N W r y.1 ∨ nearB N W r y.2)).card
      ≤ 2 * (q * (2 * r)) * N := by
  classical
  set B := Finset.univ.filter (fun u : ZMod N => nearB N W r u)
  have hsub : Finset.univ.filter (fun y : ZMod N × ZMod N => nearB N W r y.1 ∨ nearB N W r y.2)
      ⊆ (B ×ˢ Finset.univ) ∪ (Finset.univ ×ˢ B) := by
    intro y hy
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy
    simp only [Finset.mem_union, Finset.mem_product, Finset.mem_univ, and_true, true_and, B,
      Finset.mem_filter]
    exact hy
  have hB := card_nearB N q W r hN hW
  calc _ ≤ ((B ×ˢ Finset.univ) ∪ (Finset.univ ×ˢ B)).card := Finset.card_le_card hsub
    _ ≤ (B ×ˢ (Finset.univ : Finset (ZMod N))).card + ((Finset.univ : Finset (ZMod N)) ×ˢ B).card :=
        Finset.card_union_le _ _
    _ = B.card * N + N * B.card := by simp [Finset.card_product, ZMod.card]
    _ ≤ 2 * (q * (2 * r)) * N := by nlinarith

/-- The separation `|i - m|`. -/
def sep (i m : ℕ) : ℕ := if m ≤ i then i - m else m - i

theorem card_preimage_cat [NeZero N] (i : ℕ) (B : Finset (ZMod N × ZMod N)) :
    (Finset.univ.filter (fun x => (cat N)^[i] x ∈ B)).card = B.card := by
  apply Finset.card_bij' (fun x _ => (cat N)^[i] x) (fun y _ => (catInv N)^[i] y)
  · intro x hx; simpa using hx
  · intro y hy
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rw [(cat_right_inv N).iterate i y]; exact hy
  · intro x _; exact (cat_left_inv N).iterate i x
  · intro y _; exact (cat_right_inv N).iterate i y

/-- **Granular Pesin formula, upper bound (Ruelle side).**  For the `q × q`
grid partition (`N = q W`) and any tile side `L ∣ N` and centre time `m`,
`H_t ≤ 2 log (N/L) + (8 q log q / N) ∑_{i<t} ⌈ρ_{|i-m|}⌉`,
`ρ_j = φ² (λ^j + 1)(L - 1)`.  With `L ≈ N λ^{-t/2}` and `m ≈ t/2` this is
`t log λ + O_q(1)`. -/
theorem cat_grid_pesin_upper [NeZero N] (q W L : ℕ) (hN : N = q * W) (hW : 0 < W) (hL : 0 < L)
    (hLN : L ∣ N) (t m : ℕ) :
    cellEntropy (cell N (grid N W) t) ≤
      2 * Real.log ((N : ℝ) / L) + (8 * q * Real.log q / N) *
        ∑ i ∈ Finset.range t, (⌈growth L (sep i m)⌉₊ : ℝ) := by
  classical
  set lab : ZMod N × ZMod N → (Fin t → ℕ × ℕ) := fun x i => grid N W ((cat N)^[i] x)
  set τ : ZMod N × ZMod N → ℕ × ℕ := fun x => grid N L ((cat N)^[m] x)
  have hcell : cell N (grid N W) t = fun x => Finset.univ.filter (fun y => lab y = lab x) := by
    funext x; exact cell_eq_fibre N (grid N W) t x
  rw [hcell]
  have hsplit := cellEntropy_le_tiles lab τ
  set n : ℝ := (Fintype.card (ZMod N × ZMod N) : ℝ)
  have hn : n = (N : ℝ) ^ 2 := by simp [n, Fintype.card_prod, ZMod.card]; ring
  have hNpos : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
  have hq1 : 1 ≤ q := by
    rcases Nat.eq_zero_or_pos q with h | h
    · exfalso; rw [h, zero_mul] at hN; exact NeZero.ne N hN
    · exact h
  -- the tiles: at most (N/L)² of them
  have htiles : cellEntropy (fun x => Finset.univ.filter (fun y => τ y = τ x)) ≤
      2 * Real.log ((N : ℝ) / L) := by
    have h1 := cellEntropy_le_log_image τ
    have himg : (Finset.univ.image τ).card ≤ (N / L) * (N / L) := by
      calc (Finset.univ.image τ).card ≤ (Finset.range (N / L) ×ˢ Finset.range (N / L)).card := by
            apply Finset.card_le_card
            intro d hd
            obtain ⟨x, _, rfl⟩ := Finset.mem_image.mp hd
            simp only [τ, grid, Finset.mem_product, Finset.mem_range]
            exact ⟨Nat.div_lt_div_of_lt_of_dvd hLN (ZMod.val_lt _),
              Nat.div_lt_div_of_lt_of_dvd hLN (ZMod.val_lt _)⟩
        _ = (N / L) * (N / L) := by rw [Finset.card_product, Finset.card_range]
    have hpos : (0 : ℝ) < (Finset.univ.image τ).card := by
      exact_mod_cast Finset.card_pos.mpr (Finset.univ_nonempty.image τ)
    have hcast : (((N / L) * (N / L) : ℕ) : ℝ) = ((N : ℝ) / L) ^ 2 := by
      rw [Nat.cast_mul, Nat.cast_div hLN (by exact_mod_cast hL.ne')]; ring
    calc _ ≤ Real.log (Finset.univ.image τ).card := h1
      _ ≤ Real.log (((N / L) * (N / L) : ℕ) : ℝ) :=
          Real.log_le_log hpos (by exact_mod_cast himg)
      _ = 2 * Real.log ((N : ℝ) / L) := by rw [hcast, Real.log_pow]; push_cast; ring
  -- labels on a tile: at most the product over times
  set k : ℕ → ZMod N × ZMod N → ℕ := fun i x =>
    ((Finset.univ.filter (fun y => τ y = τ x)).image (fun y => grid N W ((cat N)^[i] y))).card
  have hkpos : ∀ i x, 1 ≤ k i x := fun i x =>
    Finset.card_pos.mpr (Finset.Nonempty.image
      (show (Finset.univ.filter (fun y => τ y = τ x)).Nonempty from ⟨x, by simp⟩) _)
  have hprod : ∀ x, Real.log ((Finset.univ.filter (fun y => τ y = τ x)).image lab).card ≤
      ∑ i ∈ Finset.range t, Real.log (k i x) := by
    intro x
    set D := Finset.univ.filter (fun y => τ y = τ x)
    have hsub : D.image lab ⊆ Fintype.piFinset (fun i : Fin t => D.image (fun y => grid N W ((cat N)^[i] y))) := by
      intro f hf
      obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hf
      rw [Fintype.mem_piFinset]; intro i
      exact Finset.mem_image_of_mem _ hy
    have hc : (D.image lab).card ≤ ∏ i : Fin t, k i x := by
      have := Finset.card_le_card hsub
      rwa [Fintype.card_piFinset] at this
    have hpos : (0 : ℝ) < (D.image lab).card := by
      exact_mod_cast Finset.card_pos.mpr (Finset.Nonempty.image
        (show D.Nonempty from ⟨x, by simp [D]⟩) _)
    calc Real.log (D.image lab).card ≤ Real.log (∏ i : Fin t, (k i x : ℝ)) := by
          apply Real.log_le_log hpos; exact_mod_cast hc
      _ = ∑ i : Fin t, Real.log (k i x) := by
          rw [Real.log_prod]; intro i _
          have := hkpos i x; positivity
      _ = ∑ i ∈ Finset.range t, Real.log (k i x) := Fin.sum_univ_eq_sum_range (fun i => Real.log (k i x)) t
  -- one time step: labels change only near the grid lines
  set Bad : ℕ → Finset (ZMod N × ZMod N) := fun i => Finset.univ.filter (fun y =>
    nearB N W ⌈growth L (sep i m)⌉₊ y.1 ∨ nearB N W ⌈growth L (sep i m)⌉₊ y.2)
  have hstep : ∀ i x, Real.log (k i x) ≤ (if (cat N)^[i] x ∈ Bad i then 2 * Real.log q else 0) := by
    intro i x
    split_ifs with hb
    · have hkq : k i x ≤ q * q := by
        calc k i x ≤ (Finset.range q ×ˢ Finset.range q).card := by
              apply Finset.card_le_card
              intro d hd
              obtain ⟨y, _, rfl⟩ := Finset.mem_image.mp hd
              simp only [grid, Finset.mem_product, Finset.mem_range]
              constructor <;> rw [Nat.div_lt_iff_lt_mul hW] <;>
                exact lt_of_lt_of_eq (ZMod.val_lt _) hN
          _ = q * q := by rw [Finset.card_product, Finset.card_range]
      have : Real.log (k i x) ≤ Real.log ((q : ℝ) * q) :=
        Real.log_le_log (by have := hkpos i x; exact_mod_cast this) (by exact_mod_cast hkq)
      rw [Real.log_mul (by positivity) (by positivity)] at this
      · linarith
    · have hk1 : k i x ≤ 1 := by
        apply Finset.card_le_one.mpr
        suffices hall : ∀ y ∈ Finset.univ.filter (fun y => τ y = τ x),
            grid N W ((cat N)^[i] y) = grid N W ((cat N)^[i] x) by
          intro a ha b hb'
          obtain ⟨y1, hy1, rfl⟩ := Finset.mem_image.mp ha
          obtain ⟨y2, hy2, rfl⟩ := Finset.mem_image.mp hb'
          rw [hall y1 hy1, hall y2 hy2]
        intro y hy
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy
        obtain ⟨v, hv, hv1, hv2⟩ := tile_spread N L hL m i x y hy
        rw [show (if m ≤ i then i - m else m - i) = sep i m from rfl] at hv1 hv2
        have hgr : growth L (sep i m) ≤ (⌈growth L (sep i m)⌉₊ : ℝ) := Nat.le_ceil _
        set r := ⌈growth L (sep i m)⌉₊
        have hw1 : |v.1| ≤ (r : ℤ) := by
          have : |(v.1 : ℝ)| ≤ (r : ℝ) := hv1.trans hgr
          exact_mod_cast this
        have hw2 : |v.2| ≤ (r : ℤ) := by
          have : |(v.2 : ℝ)| ≤ (r : ℝ) := hv2.trans hgr
          exact_mod_cast this
        have hy' : (cat N)^[i] y = (cat N)^[i] x + castZ N v := by rw [hv]; abel
        simp only [Bad, Finset.mem_filter, Finset.mem_univ, true_and, not_or] at hb
        rw [hy']
        simp only [grid, castZ, Prod.fst_add, Prod.snd_add, Prod.mk.injEq]
        constructor
        · by_contra hne
          exact hb.1 (near_of_block_change N q W r hN hW _ v.1 hw1 hne)
        · by_contra hne
          exact hb.2 (near_of_block_change N q W r hN hW _ v.2 hw2 hne)
      have : Real.log (k i x) ≤ Real.log 1 :=
        Real.log_le_log (by have := hkpos i x; exact_mod_cast this) (by exact_mod_cast hk1)
      simpa using this
  -- assemble
  have hsum : ∑ x, (1 / n) * Real.log ((Finset.univ.filter (fun y => τ y = τ x)).image lab).card ≤
      (8 * q * Real.log q / N) * ∑ i ∈ Finset.range t, (⌈growth L (sep i m)⌉₊ : ℝ) := by
    calc ∑ x, (1 / n) * Real.log ((Finset.univ.filter (fun y => τ y = τ x)).image lab).card
        ≤ ∑ x, (1 / n) * ∑ i ∈ Finset.range t,
            (if (cat N)^[i] x ∈ Bad i then 2 * Real.log q else 0) := by
          apply Finset.sum_le_sum; intro x _
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          exact (hprod x).trans (Finset.sum_le_sum fun i _ => hstep i x)
      _ = ∑ i ∈ Finset.range t, (1 / n) * (2 * Real.log q) *
            ((Finset.univ.filter (fun x => (cat N)^[i] x ∈ Bad i)).card : ℝ) := by
          simp_rw [Finset.mul_sum]
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl; intro i _
          rw [Finset.card_eq_sum_ones, Nat.cast_sum, Finset.mul_sum, Finset.sum_filter]
          apply Finset.sum_congr rfl; intro x _
          split_ifs <;> simp
      _ ≤ ∑ i ∈ Finset.range t, (1 / n) * (2 * Real.log q) *
            (2 * (q * (2 * (⌈growth L (sep i m)⌉₊ : ℝ))) * N) := by
          apply Finset.sum_le_sum; intro i _
          apply mul_le_mul_of_nonneg_left _ (by
            have : 0 ≤ Real.log q := Real.log_nonneg (by exact_mod_cast hq1)
            positivity)
          rw [card_preimage_cat N i (Bad i)]
          exact_mod_cast card_bad N q W _ hN hW
      _ = (8 * q * Real.log q / N) * ∑ i ∈ Finset.range t, (⌈growth L (sep i m)⌉₊ : ℝ) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl; intro i _
          rw [hn]; field_simp; ring
  linarith [hsplit, htiles, hsum]

/-- The join refines with `t`, so `H_t` is nondecreasing. -/
theorem cat_join_entropy_mono {ι : Type*} [DecidableEq ι] [NeZero N] (P : ZMod N × ZMod N → ι)
    (t : ℕ) : cellEntropy (cell N P t) ≤ cellEntropy (cell N P (t + 1)) := by
  unfold cellEntropy
  apply Finset.sum_le_sum; intro x _
  have hn : (0 : ℝ) < Fintype.card (ZMod N × ZMod N) := Nat.cast_pos.mpr Fintype.card_pos
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  have h1 : (0 : ℝ) < (cell N P (t + 1) x).card := by
    exact_mod_cast Finset.card_pos.mpr ⟨x, mem_cell N P (t + 1) x⟩
  apply Real.log_le_log (div_pos hn (by exact_mod_cast Finset.card_pos.mpr ⟨x, mem_cell N P t x⟩))
  apply div_le_div_of_nonneg_left hn.le h1
  exact_mod_cast Finset.card_le_card (fun y hy => by
    simp only [cell, Finset.mem_filter, Finset.mem_univ, true_and] at hy ⊢
    exact fun i hi => hy i (by omega))

/-- **Pesin lower bound in closed form**: with `m = ⌈(t-1)/2⌉`,
`H_t ≥ 2 log N - 2 log (1 + 2 φ⁴ (W - 1) φ^{-(t-1)})`, i.e.
`H_t ≥ min((t-1) log λ + 2 log q, 2 log N) - O(1)`. -/
theorem cat_grid_pesin_lower_closed [NeZero N] (q W : ℕ) (hN : N = q * W) (hq : 4 ≤ q)
    (hW : 0 < W) (t : ℕ) (ht : 0 < t) :
    2 * Real.log N - 2 * Real.log (1 + 2 * goldenRatio ^ 4 * ((W : ℤ) - 1 : ℤ) / goldenRatio ^ (t - 1))
      ≤ cellEntropy (cell N (grid N W) t) := by
  set s := t - 1
  set m := (s + 1) / 2
  have h := (cat_grid_pesin N q W hN hq hW t ht m).1
  have hp := goldenRatio_pos
  have hp1 := one_lt_goldenRatio
  have hR : (0 : ℝ) ≤ (((W : ℤ) - 1 : ℤ) : ℝ) := by
    have : (1 : ℤ) ≤ W := by exact_mod_cast hW
    exact_mod_cast (show (0 : ℤ) ≤ (W : ℤ) - 1 by omega)
  set R : ℝ := (((W : ℤ) - 1 : ℤ) : ℝ)
  -- the two exponentials
  have e1 : goldenRatio ^ (2 * m) / goldenRatio ^ (2 * s) ≤ goldenRatio / goldenRatio ^ s := by
    rw [div_le_div_iff₀ (by positivity) (by positivity), ← pow_add, ← pow_succ']
    exact pow_le_pow_right₀ hp1.le (by omega)
  have e2 : 1 / goldenRatio ^ (2 * m) ≤ 1 / goldenRatio ^ s := by
    apply one_div_le_one_div_of_le (by positivity)
    exact pow_le_pow_right₀ hp1.le (by omega)
  have hsum : goldenRatio ^ 2 * R * (goldenRatio ^ (2 * m) / goldenRatio ^ (2 * s) + 1 / goldenRatio ^ (2 * m))
      ≤ goldenRatio ^ 4 * R / goldenRatio ^ s := by
    have : goldenRatio ^ (2 * m) / goldenRatio ^ (2 * s) + 1 / goldenRatio ^ (2 * m)
        ≤ (goldenRatio + 1) / goldenRatio ^ s := by
      rw [add_div]; linarith
    calc _ ≤ goldenRatio ^ 2 * R * ((goldenRatio + 1) / goldenRatio ^ s) :=
          mul_le_mul_of_nonneg_left this (by positivity)
      _ = goldenRatio ^ 4 * R / goldenRatio ^ s := by rw [← goldenRatio_sq]; ring
  have hρ0 : 0 ≤ goldenRatio ^ 2 * R * (goldenRatio ^ (2 * m) / goldenRatio ^ (2 * s) +
      1 / goldenRatio ^ (2 * m)) := by positivity
  have hNpos : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
  have hmono : Real.log ((N : ℝ) ^ 2 / (1 + 2 * goldenRatio ^ 4 * R / goldenRatio ^ s) ^ 2) ≤
      Real.log ((N : ℝ) ^ 2 / (2 * (goldenRatio ^ 2 * R * (goldenRatio ^ (2 * m) /
        goldenRatio ^ (2 * s) + 1 / goldenRatio ^ (2 * m))) + 1) ^ 2) := by
    apply Real.log_le_log (by positivity)
    apply div_le_div_of_nonneg_left (by positivity) (by positivity)
    apply pow_le_pow_left₀ (by positivity)
    have : 2 * goldenRatio ^ 4 * R / goldenRatio ^ s = 2 * (goldenRatio ^ 4 * R / goldenRatio ^ s) := by ring
    rw [this]; linarith
  have hsplit : Real.log ((N : ℝ) ^ 2 / (1 + 2 * goldenRatio ^ 4 * R / goldenRatio ^ s) ^ 2) =
      2 * Real.log N - 2 * Real.log (1 + 2 * goldenRatio ^ 4 * R / goldenRatio ^ s) := by
    rw [Real.log_div (by positivity) (by positivity), Real.log_pow, Real.log_pow]; push_cast; ring
  linarith

/-- Geometric control of the tile spreads, `m = ⌊t/2⌋`. -/
theorem sum_lambda_sep (t : ℕ) :
    ∑ i ∈ Finset.range t, (goldenRatio ^ 2) ^ sep i (t / 2) ≤
      ((goldenRatio ^ 2) ^ (t / 2 + 1) + (goldenRatio ^ 2) ^ (t - t / 2)) / (goldenRatio ^ 2 - 1) := by
  set m := t / 2
  set l := goldenRatio ^ 2
  have hl : 1 < l := by simp only [l]; nlinarith [goldenRatio_sq, one_lt_goldenRatio]
  have hsplit : Finset.range t = Finset.range m ∪ Finset.Ico m t := by
    ext i; simp [Finset.mem_Ico]; omega
  have hdisj : Disjoint (Finset.range m) (Finset.Ico m t) := by
    rw [Finset.disjoint_left]; intro i hi hi'; simp at hi hi'; omega
  rw [hsplit, Finset.sum_union hdisj]
  have g : ∀ k : ℕ, ∑ j ∈ Finset.range k, l ^ j ≤ l ^ k / (l - 1) := by
    intro k
    rw [geom_sum_eq hl.ne', le_div_iff₀ (by linarith), div_mul_cancel₀ _ (by linarith)]
    linarith
  have h1 : ∑ i ∈ Finset.range m, l ^ sep i m ≤ l ^ (m + 1) / (l - 1) := by
    calc ∑ i ∈ Finset.range m, l ^ sep i m = ∑ i ∈ Finset.range m, (fun j => l ^ (j + 1)) (m - 1 - i) := by
          apply Finset.sum_congr rfl; intro i hi
          simp only [Finset.mem_range] at hi; simp only [sep]
          rw [if_neg (by omega)]; congr 1; omega
      _ = ∑ j ∈ Finset.range m, l ^ (j + 1) := Finset.sum_range_reflect (fun j => l ^ (j + 1)) m
      _ ≤ ∑ j ∈ Finset.range (m + 1), l ^ j := by
          rw [Finset.sum_range_succ' (fun j => l ^ j)]; simp
      _ ≤ _ := g (m + 1)
  have h2 : ∑ i ∈ Finset.Ico m t, l ^ sep i m ≤ l ^ (t - m) / (l - 1) := by
    calc ∑ i ∈ Finset.Ico m t, l ^ sep i m = ∑ j ∈ Finset.range (t - m), l ^ j := by
          rw [Finset.sum_Ico_eq_sum_range]
          apply Finset.sum_congr rfl; intro j _
          simp only [sep]; rw [if_pos (by omega)]; congr 1; omega
      _ ≤ _ := g (t - m)
  rw [add_div]; linarith

/-- **Pesin upper bound in closed form** (`m = ⌊t/2⌋`):
`H_t ≤ 2 log (N/L) + (8 q log q / N) (φ² (L-1)(t + (λ^{⌊t/2⌋+1} + λ^{t-⌊t/2⌋})/(λ-1)) + t)`. -/
theorem cat_grid_pesin_upper_closed [NeZero N] (q W L : ℕ) (hN : N = q * W) (hW : 0 < W)
    (hL : 0 < L) (hLN : L ∣ N) (t : ℕ) :
    cellEntropy (cell N (grid N W) t) ≤
      2 * Real.log ((N : ℝ) / L) + (8 * q * Real.log q / N) *
        (goldenRatio ^ 2 * ((L : ℤ) - 1 : ℤ) * (t + ((goldenRatio ^ 2) ^ (t / 2 + 1) +
          (goldenRatio ^ 2) ^ (t - t / 2)) / (goldenRatio ^ 2 - 1)) + t) := by
  have h := cat_grid_pesin_upper N q W L hN hW hL hLN t (t / 2)
  have hq1 : 1 ≤ q := by
    rcases Nat.eq_zero_or_pos q with h | h
    · exfalso; rw [h, zero_mul] at hN; exact NeZero.ne N hN
    · exact h
  have hc : 0 ≤ 8 * (q : ℝ) * Real.log q / N := by
    have : 0 ≤ Real.log q := Real.log_nonneg (by exact_mod_cast hq1)
    positivity
  have hR : (0 : ℝ) ≤ (((L : ℤ) - 1 : ℤ) : ℝ) := by
    have : (1 : ℤ) ≤ L := by exact_mod_cast hL
    exact_mod_cast (show (0 : ℤ) ≤ (L : ℤ) - 1 by omega)
  have hsum : ∑ i ∈ Finset.range t, (⌈growth L (sep i (t / 2))⌉₊ : ℝ) ≤
      goldenRatio ^ 2 * ((L : ℤ) - 1 : ℤ) * (t + ((goldenRatio ^ 2) ^ (t / 2 + 1) +
          (goldenRatio ^ 2) ^ (t - t / 2)) / (goldenRatio ^ 2 - 1)) + t := by
    have hg : ∀ i, 0 ≤ growth L (sep i (t / 2)) := fun i => by unfold growth; positivity
    calc ∑ i ∈ Finset.range t, (⌈growth L (sep i (t / 2))⌉₊ : ℝ)
        ≤ ∑ i ∈ Finset.range t, (growth L (sep i (t / 2)) + 1) :=
          Finset.sum_le_sum fun i _ => (Nat.ceil_lt_add_one (hg i)).le
      _ = goldenRatio ^ 2 * ((L : ℤ) - 1 : ℤ) *
            (∑ i ∈ Finset.range t, (goldenRatio ^ 2) ^ sep i (t / 2) + t) + t := by
          rw [Finset.sum_add_distrib]; unfold growth
          simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
          rw [← Finset.sum_mul, ← Finset.mul_sum, Finset.sum_add_distrib]
          simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]; ring
      _ ≤ _ := by
          have := sum_lambda_sep t
          have hp : 0 ≤ goldenRatio ^ 2 * (((L : ℤ) - 1 : ℤ) : ℝ) := by positivity
          nlinarith
  calc _ ≤ _ := h
    _ ≤ _ := by
        have := mul_le_mul_of_nonneg_left hsum hc
        linarith

theorem goldenRatio_lt : goldenRatio < 1.62 := by
  have h5 : Real.sqrt 5 < 2.24 := by
    rw [Real.sqrt_lt' (by norm_num)]; norm_num
  rw [goldenRatio]; linarith

theorem goldenRatio_gt : 1.6 < goldenRatio := by
  have h5 : 2.2 < Real.sqrt 5 := by
    rw [Real.lt_sqrt (by norm_num)]; norm_num
  rw [goldenRatio]; linarith

theorem nat_le_goldenRatio_pow (t : ℕ) : (t : ℝ) ≤ goldenRatio ^ t := by
  have hp1 := one_lt_goldenRatio
  have hp := goldenRatio_pos
  have hg := goldenRatio_gt
  induction t with
  | zero => simp
  | succ t ih =>
    rcases Nat.lt_or_ge t 2 with h | h
    · interval_cases t
      · simp; linarith
      · push_cast; rw [pow_two, ← pow_two, goldenRatio_sq]; linarith
    · rw [pow_succ]; push_cast
      have : (2 : ℝ) ≤ t := by exact_mod_cast h
      have h1 := mul_le_mul_of_nonneg_right ih hp.le
      nlinarith

/-- **Pesin profile, lower half**: `H_t ≥ min((t-1) ln λ + 2 ln q - 7, 2 ln N - 2 ln 2)`. -/
theorem cat_pesin_profile_lower [NeZero N] (q W : ℕ) (hN : N = q * W) (hq : 4 ≤ q) (hW : 0 < W)
    (t : ℕ) (ht : 0 < t) :
    min (2 * ((t : ℝ) - 1) * Real.log goldenRatio + 2 * Real.log q - 7) (2 * Real.log N - 2 * Real.log 2)
      ≤ cellEntropy (cell N (grid N W) t) := by
  have h := cat_grid_pesin_lower_closed N q W hN hq hW t ht
  have hp := goldenRatio_pos
  set X := 2 * goldenRatio ^ 4 * (((W : ℤ) - 1 : ℤ) : ℝ) / goldenRatio ^ (t - 1)
  have hX0 : 0 ≤ X := by
    have : (1 : ℤ) ≤ W := by exact_mod_cast hW
    have : (0 : ℝ) ≤ (((W : ℤ) - 1 : ℤ) : ℝ) := by exact_mod_cast (show (0 : ℤ) ≤ (W : ℤ) - 1 by omega)
    positivity
  have hNpos : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
  have hqpos : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
  have hWpos : (0 : ℝ) < W := by exact_mod_cast hW
  rcases le_or_gt 1 X with hX | hX
  · apply min_le_of_left_le
    -- 2 ln (1 + X) ≤ 2 ln (2X) ≤ 2 ln N - 2 ln q - 2 (t-1) ln φ + 2 ln 32 - ...
    have h1 : Real.log (1 + X) ≤ Real.log (2 * X) := Real.log_le_log (by linarith) (by linarith)
    have hXle : 2 * X ≤ 4 * goldenRatio ^ 4 * W / goldenRatio ^ (t - 1) := by
      simp only [X]
      have : (((W : ℤ) - 1 : ℤ) : ℝ) ≤ W := by push_cast; linarith
      rw [show 2 * (2 * goldenRatio ^ 4 * (((W : ℤ) - 1 : ℤ) : ℝ) / goldenRatio ^ (t - 1)) =
        4 * goldenRatio ^ 4 * (((W : ℤ) - 1 : ℤ) : ℝ) / goldenRatio ^ (t - 1) by ring]
      apply div_le_div_of_nonneg_right _ (by positivity)
      nlinarith [pow_pos hp 4]
    have h2 : Real.log (2 * X) ≤ Real.log (4 * goldenRatio ^ 4 * W / goldenRatio ^ (t - 1)) :=
      Real.log_le_log (by linarith) hXle
    have h4 : 4 * goldenRatio ^ 4 < 32 := by
      have : goldenRatio ^ 4 = 3 * goldenRatio + 2 := by
        have := goldenRatio_sq; nlinarith
      rw [this]; linarith [goldenRatio_lt]
    have hsplit : Real.log (4 * goldenRatio ^ 4 * W / goldenRatio ^ (t - 1)) =
        Real.log (4 * goldenRatio ^ 4) + Real.log W - (t - 1 : ℕ) * Real.log goldenRatio := by
      rw [Real.log_div (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
        Real.log_pow]
    have h32 : Real.log (4 * goldenRatio ^ 4) ≤ 5 * Real.log 2 := by
      rw [← Real.log_rpow (by norm_num)]
      apply Real.log_le_log (by positivity); norm_num; linarith
    have hl2 := Real.log_two_lt_d9
    have hNq : Real.log N = Real.log q + Real.log W := by
      rw [hN, Nat.cast_mul, Real.log_mul hqpos.ne' hWpos.ne']
    have hcast : (((t - 1 : ℕ) : ℝ)) = (t : ℝ) - 1 := by
      rw [Nat.cast_sub (by omega)]; simp
    rw [hcast] at hsplit
    linarith
  · apply min_le_of_right_le
    have : Real.log (1 + X) ≤ Real.log 2 := Real.log_le_log (by linarith) (by linarith)
    linarith

/-- **Pesin profile, upper half.**  If `L ∣ N` and
`q ln q φ^t L ≤ N ≤ 2 q ln q φ^t L` (`φ^t = λ^{t/2}`), then
`H_t ≤ t ln λ + 2 ln (2 q ln q) + 97`. -/
theorem cat_pesin_profile_upper [NeZero N] (q W L : ℕ) (hN : N = q * W) (hq : 2 ≤ q) (hW : 0 < W)
    (hL : 0 < L) (hLN : L ∣ N) (t : ℕ)
    (hlo : (q : ℝ) * Real.log q * goldenRatio ^ t * L ≤ N)
    (hhi : (N : ℝ) ≤ 2 * q * Real.log q * goldenRatio ^ t * L) :
    cellEntropy (cell N (grid N W) t) ≤
      2 * t * Real.log goldenRatio + 2 * Real.log (2 * q * Real.log q) + 97 := by
  have h := cat_grid_pesin_upper_closed N q W L hN hW hL hLN t
  have hp := goldenRatio_pos
  have hp1 := one_lt_goldenRatio
  have hlq : 0 < Real.log q := Real.log_pos (by exact_mod_cast (show 1 < q by omega))
  have hqpos : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
  have hLpos : (0 : ℝ) < L := by exact_mod_cast hL
  have hNpos : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
  set c := (q : ℝ) * Real.log q
  have hc : 0 < c := mul_pos hqpos hlq
  -- the tile term
  have htile : 2 * Real.log ((N : ℝ) / L) ≤ 2 * t * Real.log goldenRatio + 2 * Real.log (2 * c) := by
    have : (N : ℝ) / L ≤ 2 * c * goldenRatio ^ t := by
      rw [div_le_iff₀ hLpos]; linarith
    have h1 := Real.log_le_log (by positivity) this
    rw [Real.log_mul (by positivity) (by positivity), Real.log_pow] at h1
    linarith
  -- the error term
  set S := goldenRatio ^ 2 * (((L : ℤ) - 1 : ℤ) : ℝ) * (t + ((goldenRatio ^ 2) ^ (t / 2 + 1) +
          (goldenRatio ^ 2) ^ (t - t / 2)) / (goldenRatio ^ 2 - 1)) + t
  have hpow1 : (goldenRatio ^ 2) ^ (t / 2 + 1) ≤ goldenRatio ^ (t + 2) := by
    rw [← pow_mul]; exact pow_le_pow_right₀ hp1.le (by omega)
  have hpow2 : (goldenRatio ^ 2) ^ (t - t / 2) ≤ goldenRatio ^ (t + 2) := by
    rw [← pow_mul]; exact pow_le_pow_right₀ hp1.le (by omega)
  have hden : goldenRatio ^ 2 - 1 = goldenRatio := by rw [goldenRatio_sq]; ring
  have hgeo : ((goldenRatio ^ 2) ^ (t / 2 + 1) + (goldenRatio ^ 2) ^ (t - t / 2)) / (goldenRatio ^ 2 - 1)
      ≤ 2 * goldenRatio ^ (t + 1) := by
    rw [hden, div_le_iff₀ hp]
    have : goldenRatio ^ (t + 2) = goldenRatio ^ (t + 1) * goldenRatio := pow_succ _ _
    linarith
  have hLm : (((L : ℤ) - 1 : ℤ) : ℝ) ≤ L := by push_cast; linarith
  have hLm0 : (0 : ℝ) ≤ (((L : ℤ) - 1 : ℤ) : ℝ) := by
    have : (1 : ℤ) ≤ L := by exact_mod_cast hL
    exact_mod_cast (show (0 : ℤ) ≤ (L : ℤ) - 1 by omega)
  have hS : S ≤ goldenRatio ^ 2 * L * (t + 2 * goldenRatio ^ (t + 1)) + t := by
    simp only [S]
    have h1 : 0 ≤ (t : ℝ) + ((goldenRatio ^ 2) ^ (t / 2 + 1) + (goldenRatio ^ 2) ^ (t - t / 2)) /
        (goldenRatio ^ 2 - 1) := by rw [hden]; positivity
    have := mul_le_mul hLm (show (t : ℝ) + ((goldenRatio ^ 2) ^ (t / 2 + 1) +
      (goldenRatio ^ 2) ^ (t - t / 2)) / (goldenRatio ^ 2 - 1) ≤ t + 2 * goldenRatio ^ (t + 1) by
        linarith [hgeo]) h1 hLpos.le
    nlinarith [pow_pos hp 2]
  have hct : (t : ℝ) ≤ goldenRatio ^ t := nat_le_goldenRatio_pow t
  have hE : (8 * q * Real.log q / N) * S ≤ 97 := by
    have hcN : c * goldenRatio ^ t * L ≤ N := by simp only [c]; linarith
    have hcoef : 8 * (q : ℝ) * Real.log q / N = 8 * c / N := by simp only [c]; ring
    rw [hcoef]
    have hS0 : 0 ≤ S := by simp only [S]; rw [hden]; positivity
    calc 8 * c / N * S ≤ 8 * c / N * (goldenRatio ^ 2 * L * (t + 2 * goldenRatio ^ (t + 1)) + t) :=
          mul_le_mul_of_nonneg_left hS (by positivity)
      _ = 8 * (c * L / N) * goldenRatio ^ 2 * (t + 2 * goldenRatio ^ (t + 1)) + 8 * (c / N) * t := by
          ring
      _ ≤ 8 * (1 / goldenRatio ^ t) * goldenRatio ^ 2 * (t + 2 * goldenRatio ^ (t + 1)) +
            8 * (1 / goldenRatio ^ t) * t := by
          have h1 : c * L / N ≤ 1 / goldenRatio ^ t := by
            rw [div_le_div_iff₀ hNpos (by positivity)]; nlinarith
          have h2 : c / N ≤ 1 / goldenRatio ^ t := by
            rw [div_le_div_iff₀ hNpos (by positivity)]
            have : (1 : ℝ) ≤ L := by exact_mod_cast hL
            nlinarith [pow_pos hp t]
          have ht0 : (0 : ℝ) ≤ t := by positivity
          gcongr
      _ = 8 * goldenRatio ^ 2 * (t / goldenRatio ^ t) + 16 * goldenRatio ^ 3 +
            8 * (t / goldenRatio ^ t) := by
          rw [pow_succ goldenRatio t]; field_simp; ring
      _ ≤ 8 * goldenRatio ^ 2 * 1 + 16 * goldenRatio ^ 3 + 8 * 1 := by
          have : (t : ℝ) / goldenRatio ^ t ≤ 1 := by rw [div_le_one (by positivity)]; exact hct
          gcongr
      _ ≤ 97 := by
          have h2 := goldenRatio_sq
          have h3 : goldenRatio ^ 3 = 2 * goldenRatio + 1 := by nlinarith
          rw [h2, h3]; linarith [goldenRatio_lt]
  have e : (2 : ℝ) * q * Real.log q = 2 * c := by simp only [c]; ring
  rw [e]
  linarith

end Pesin

/-! ## The granular H-theorem -/

section HTheorem

variable {X : Type*} [Fintype X]

omit [Fintype X] in
/-- Reversibility propagates to iterates: `I ∘ f^t = f^{-t} ∘ I`. -/
theorem rev_iterate (f : X ≃ X) (I : X → X) (hI : ∀ x, I (f x) = f.symm (I x)) (t : ℕ) (x : X) :
    I (f^[t] x) = f.symm^[t] (I x) := by
  induction t generalizing x with
  | zero => rfl
  | succ t ih => rw [iterate_succ_apply', hI, ih, ← iterate_succ_apply' f.symm]

/-- **Loschmidt's symmetry, counted.**  For a bijection `f` with a reversing
involution `I` (`I f I = f⁻¹`) and an `I`-invariant coarse-grained entropy
`S`, for every time `t` and threshold `Δ`, the microstates whose entropy drops
by at least `Δ` are exactly as many as those whose entropy rises by at least
`Δ`. -/
theorem entropy_change_symm {β : Type*} [AddCommMonoid β] [LinearOrder β]
    (f : X ≃ X) (I : X → X) (hII : Involutive I) (hI : ∀ x, I (f x) = f.symm (I x))
    (S : X → β) (hS : ∀ x, S (I x) = S x) (t : ℕ) (Δ : β) :
    (Finset.univ.filter (fun x => S (f^[t] x) + Δ ≤ S x)).card =
      (Finset.univ.filter (fun x => S x + Δ ≤ S (f^[t] x))).card := by
  classical
  have hback : ∀ x, f^[t] (I (f^[t] x)) = I x := by
    intro x
    rw [rev_iterate f I hI t]
    have hr : LeftInverse f f.symm := f.apply_symm_apply
    exact hr.iterate t (I x)
  have hinv : ∀ x, I (f^[t] (I (f^[t] x))) = x := by
    intro x; rw [hback, hII]
  apply Finset.card_bij' (fun x _ => I (f^[t] x)) (fun x _ => I (f^[t] x))
  · intro x hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
    rw [hS, hback, hS]; exact hx
  · intro x hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
    rw [hS, hback, hS]; exact hx
  · intro x _; exact hinv x
  · intro x _; exact hinv x

/-- The same symmetry with strict inequalities (`Δ = 0`): exactly as many
microstates lose entropy as gain it. -/
theorem entropy_decrease_eq_increase {β : Type*} [LinearOrder β]
    (f : X ≃ X) (I : X → X) (hII : Involutive I) (hI : ∀ x, I (f x) = f.symm (I x))
    (S : X → β) (hS : ∀ x, S (I x) = S x) (t : ℕ) :
    (Finset.univ.filter (fun x => S (f^[t] x) < S x)).card =
      (Finset.univ.filter (fun x => S x < S (f^[t] x))).card := by
  classical
  have hback : ∀ x, f^[t] (I (f^[t] x)) = I x := by
    intro x
    rw [rev_iterate f I hI t]
    exact (show LeftInverse f f.symm from f.apply_symm_apply).iterate t (I x)
  have hinv : ∀ x, I (f^[t] (I (f^[t] x))) = x := by
    intro x; rw [hback, hII]
  apply Finset.card_bij' (fun x _ => I (f^[t] x)) (fun x _ => I (f^[t] x))
  · intro x hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
    rw [hS, hback, hS]; exact hx
  · intro x hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
    rw [hS, hback, hS]; exact hx
  · intro x _; exact hinv x
  · intro x _; exact hinv x

/-- The kick–drift map with its reversal satisfies the hypotheses, for any
commutative ring of positions (in particular `(Fin k → ZMod N)` for `n`
particles in `d` dimensions, `k = d n`) and any force. -/
theorem kickdrift_reversing {R : Type*} [CommRing R] (F : R → R) (x : R × R) :
    QE.Dyn.rev F (QE.Dyn.leapEquiv F x) = (QE.Dyn.leapEquiv F).symm (QE.Dyn.rev F x) := by
  show QE.Dyn.rev F (QE.Dyn.leap F x) = QE.Dyn.leapInv F (QE.Dyn.rev F x)
  exact QE.Dyn.rev_semiconj F x

/-- A position-only coarse-grained entropy is invariant under the reversal. -/
theorem rev_preserves_position {R β : Type*} [CommRing R] (F : R → R) (s : R → β) (x : R × R) :
    s (QE.Dyn.rev F x).1 = s x.1 := rfl

/-- **Granular H-theorem for kick–drift systems** (exact symmetry): for every
force, every position-only coarse-grained entropy, every `t` and `Δ`. -/
theorem kickdrift_entropy_symm {R : Type*} [CommRing R] [Fintype R] [DecidableEq R]
    (F : R → R) (s : R → ℝ) (t : ℕ) (Δ : ℝ) :
    (Finset.univ.filter (fun x : R × R => s ((QE.Dyn.leap F)^[t] x).1 + Δ ≤ s x.1)).card =
      (Finset.univ.filter (fun x : R × R => s x.1 + Δ ≤ s ((QE.Dyn.leap F)^[t] x).1)).card :=
  entropy_change_symm (QE.Dyn.leapEquiv F) (QE.Dyn.rev F) (QE.Dyn.rev_involutive F)
    (kickdrift_reversing F) (fun x => s x.1) (fun _ => rfl) t Δ

/-- Boltzmann entropy of a macrostate: `log` of its number of microstates. -/
noncomputable def boltzmann {ι : Type*} [DecidableEq ι] (mac : X → ι) (x : X) : ℝ :=
  Real.log (Finset.univ.filter (fun y => mac y = mac x)).card

/-- **Boltzmann's counting bound, from a single macrostate.**  For any
injective dynamics `g` (for instance `Λ^t` for any `t`), among the
microstates of a macrostate `M_i`, at most `K e^{-Δ} |M_i|` lower their
Boltzmann entropy by at least `Δ`, where `K` is the number of macrostates. -/
theorem boltzmann_bound_cell {ι : Type*} [Fintype ι] [DecidableEq ι] (mac : X → ι)
    (g : X → X) (hg : Injective g) (Δ : ℝ) (i : ι) :
    ((Finset.univ.filter (fun x => mac x = i ∧ boltzmann mac (g x) + Δ ≤ boltzmann mac x)).card : ℝ)
      ≤ Fintype.card ι * Real.exp (-Δ) * (Finset.univ.filter (fun y => mac y = i)).card := by
  classical
  set A := Finset.univ.filter (fun x => mac x = i ∧ boltzmann mac (g x) + Δ ≤ boltzmann mac x)
  set Mi := Finset.univ.filter (fun y => mac y = i)
  -- split A according to the macrostate of g x
  have hsplit : (A.card : ℝ) = ∑ j, ((A.filter (fun x => mac (g x) = j)).card : ℝ) := by
    rw [← Nat.cast_sum, Finset.card_eq_sum_card_fiberwise (f := fun x => mac (g x))
      (t := Finset.univ) (fun _ _ => Finset.mem_univ _)]
  have hpiece : ∀ j, ((A.filter (fun x => mac (g x) = j)).card : ℝ) ≤ Real.exp (-Δ) * Mi.card := by
    intro j
    rcases (A.filter (fun x => mac (g x) = j)).eq_empty_or_nonempty with he | ⟨x0, hx0⟩
    · rw [he]; simp only [Finset.card_empty, Nat.cast_zero]; positivity
    · simp only [A, Finset.mem_filter, Finset.mem_univ, true_and] at hx0
      obtain ⟨⟨hmi, hlow⟩, hj⟩ := hx0
      set Mj := Finset.univ.filter (fun y => mac y = j)
      -- injectivity: the piece injects into M_j
      have h1 : (A.filter (fun x => mac (g x) = j)).card ≤ Mj.card := by
        apply Finset.card_le_card_of_injOn g _ hg.injOn
        intro x hx
        rw [Finset.mem_coe, Finset.mem_filter] at hx
        rw [Finset.mem_coe]
        simp [Mj, hx.2]
      have hMj : (0 : ℝ) < Mj.card := by
        exact_mod_cast Finset.card_pos.mpr ⟨g x0, by simp [Mj, hj]⟩
      have hMi : (0 : ℝ) < Mi.card := by
        exact_mod_cast Finset.card_pos.mpr ⟨x0, by simp [Mi, hmi]⟩
      -- entropy comparison: log |M_j| + Δ ≤ log |M_i|
      have hlog : Real.log Mj.card + Δ ≤ Real.log Mi.card := by
        unfold boltzmann at hlow
        rw [hj, hmi] at hlow; exact hlow
      have hexp : (Mj.card : ℝ) ≤ Real.exp (-Δ) * Mi.card := by
        have := Real.exp_le_exp.mpr (show Real.log Mj.card ≤ Real.log Mi.card - Δ by linarith)
        rw [Real.exp_log hMj, Real.exp_sub, Real.exp_log hMi] at this
        rw [Real.exp_neg]; field_simp; field_simp at this; linarith
      calc ((A.filter (fun x => mac (g x) = j)).card : ℝ) ≤ Mj.card := by exact_mod_cast h1
        _ ≤ _ := hexp
  rw [hsplit]
  calc ∑ j, ((A.filter (fun x => mac (g x) = j)).card : ℝ)
      ≤ ∑ _j : ι, Real.exp (-Δ) * Mi.card := Finset.sum_le_sum fun j _ => hpiece j
    _ = _ := by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; ring

/-- **Boltzmann's counting bound, globally**: the fraction of all microstates
whose Boltzmann entropy drops by at least `Δ` is at most `K e^{-Δ}`. -/
theorem boltzmann_bound {ι : Type*} [Fintype ι] [DecidableEq ι] (mac : X → ι)
    (g : X → X) (hg : Injective g) (Δ : ℝ) :
    ((Finset.univ.filter (fun x => boltzmann mac (g x) + Δ ≤ boltzmann mac x)).card : ℝ)
      ≤ Fintype.card ι * Real.exp (-Δ) * Fintype.card X := by
  classical
  have hsplit := Finset.card_eq_sum_card_fiberwise (f := mac)
    (s := Finset.univ.filter (fun x => boltzmann mac (g x) + Δ ≤ boltzmann mac x))
    (t := Finset.univ) (fun _ _ => Finset.mem_univ _)
  have hX : (Fintype.card X : ℝ) = ∑ i, ((Finset.univ.filter (fun y => mac y = i)).card : ℝ) := by
    rw [← Nat.cast_sum, ← Finset.card_eq_sum_card_fiberwise (fun _ _ => Finset.mem_univ _)]
    simp
  rw [hsplit, Nat.cast_sum, hX, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  have := boltzmann_bound_cell mac g hg Δ i
  calc _ = ((Finset.univ.filter (fun x => mac x = i ∧ boltzmann mac (g x) + Δ ≤ boltzmann mac x)).card : ℝ) := by
        congr 2; ext x; simp [and_comm]
    _ ≤ _ := this

/-- Occupation numbers of `m` spatial cells by `n` particles: the macrostate
of a gas.  There are at most `(n+1)^m` of them. -/
def occupation {Q : Type*} {n m : ℕ} (cellOf : Q → Fin m) (q : Fin n → Q) : Fin m → Fin (n + 1) :=
  fun c => ⟨(Finset.univ.filter (fun i => cellOf (q i) = c)).card,
    Nat.lt_succ_of_le ((Finset.card_filter_le _ _).trans (by simp))⟩

theorem card_occupation_space (n m : ℕ) : Fintype.card (Fin m → Fin (n + 1)) = (n + 1) ^ m := by
  simp

/-- **Granular H-theorem for an `n`-particle gas**: for any bijective
dynamics (kick–drift with any force, any `t`), the fraction of microstates
whose occupation-number Boltzmann entropy drops by at least `Δ` nats is at
most `(n+1)^m e^{-Δ}`, for every `N` and every time. -/
theorem gas_htheorem {Q : Type*} {n m : ℕ} (cellOf : Q → Fin m) (pos : X → (Fin n → Q))
    (g : X → X) (hg : Injective g) (Δ : ℝ) :
    ((Finset.univ.filter (fun x => boltzmann (fun y => occupation cellOf (pos y)) (g x) + Δ ≤
        boltzmann (fun y => occupation cellOf (pos y)) x)).card : ℝ)
      ≤ ((n + 1 : ℕ) : ℝ) ^ m * Real.exp (-Δ) * Fintype.card X := by
  have := boltzmann_bound (fun y => occupation cellOf (pos y)) g hg Δ
  rw [card_occupation_space] at this
  exact_mod_cast this

end HTheorem

/-! ## Reversible lattice maps: symmetric cycles -/

section Reversible

variable {X : Type*} [Fintype X] [DecidableEq X]

/-- The orbit (cycle) of `x`, as a finite set. -/
noncomputable def orbitSet (f : X → X) (x : X) : Finset X := by
  classical exact Finset.univ.filter (fun z => ∃ k, f^[k] x = z)

omit [DecidableEq X] in
theorem mem_orbitSet (f : X → X) (x z : X) : z ∈ orbitSet f x ↔ ∃ k, f^[k] x = z := by
  classical
  unfold orbitSet
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]

omit [Fintype X] [DecidableEq X] in
/-- Two fixed points of the reversing involution on one cycle: `Λ^{2k} x = x`. -/
theorem fix_same_orbit (Λ : X ≃ X) (G : X → X) (hrev : ∀ x, G (Λ x) = Λ.symm (G x))
    {x y : X} (hx : G x = x) (hy : G y = y) (k : ℕ) (hk : Λ^[k] x = y) : Λ^[2 * k] x = x := by
  have h1 : G (Λ^[k] x) = Λ.symm^[k] (G x) := rev_iterate Λ G hrev k x
  rw [hk, hy, hx] at h1
  rw [two_mul, iterate_add_apply]
  conv_lhs => rw [show (⇑Λ)^[k] x = y from hk]
  rw [h1]
  exact (show LeftInverse Λ Λ.symm from Λ.apply_symm_apply).iterate k x

/-- **Each cycle carries at most two fixed points of the reversing
involution.** -/
theorem fix_per_orbit_le_two (Λ : X ≃ X) (G : X → X) (hrev : ∀ x, G (Λ x) = Λ.symm (G x))
    (x : X) (hx : G x = x) :
    ((Finset.univ.filter (fun y => G y = y)).filter (fun y => orbitSet Λ y = orbitSet Λ x)).card ≤ 2 := by
  classical
  obtain ⟨N0, hN0, hper⟩ := QE.Dyn.perm_periodic Λ
  have hpp : x ∈ periodicPts Λ := ⟨N0, hN0, by
    have := hper x; rw [Equiv.Perm.coe_pow] at this; exact this⟩
  set n := minimalPeriod Λ x
  have hn : 0 < n := minimalPeriod_pos_of_mem_periodicPts hpp
  apply (Finset.card_le_card (t := {x, Λ^[n / 2] x}) _).trans (Finset.card_le_two)
  intro y hy
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy
  obtain ⟨hGy, horb⟩ := hy
  have hyo : y ∈ orbitSet Λ x := by rw [← horb, mem_orbitSet]; exact ⟨0, rfl⟩
  obtain ⟨k, hk⟩ := (mem_orbitSet _ _ _).mp hyo
  set k' := k % n
  have hk' : Λ^[k'] x = y := by rw [iterate_mod_minimalPeriod_eq]; exact hk
  have h2 := fix_same_orbit Λ G hrev hx hGy k' hk'
  have hdvd : n ∣ 2 * k' := (isPeriodicPt_iff_minimalPeriod_dvd).mp h2
  have hlt : k' < n := Nat.mod_lt _ hn
  obtain ⟨c, hc⟩ := hdvd
  have hc2 : c = 0 ∨ c = 1 := by
    rcases Nat.lt_or_ge c 2 with h | h
    · omega
    · exfalso; have : n * 2 ≤ n * c := Nat.mul_le_mul_left n h; omega
  rcases hc2 with h0 | h1
  · have : k' = 0 := by subst h0; omega
    rw [this] at hk'; simp only [iterate_zero, id_eq] at hk'; simp [← hk']
  · have : k' = n / 2 := by subst h1; omega
    rw [this] at hk'; simp [← hk']

/-- **Symmetric cycles of a reversible map.**  If `G` reverses `Λ`, the
number of distinct cycles of `Λ` through fixed points of `G` is at least half
the number of those fixed points. -/
theorem symmetric_cycles_ge (Λ : X ≃ X) (G : X → X) (hrev : ∀ x, G (Λ x) = Λ.symm (G x)) :
    (Finset.univ.filter (fun y => G y = y)).card ≤
      2 * ((Finset.univ.filter (fun y => G y = y)).image (orbitSet Λ)).card := by
  classical
  apply Finset.card_le_mul_card_image
  intro O hO
  obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hO
  have hGx : G x = x := (Finset.mem_filter.mp hx).2
  exact fix_per_orbit_le_two Λ G hrev x hGx

/-- The reversal `(q, p) ↦ (q, -p - F q)` of the kick–drift map has exactly
`|R|` fixed points when `2` is a unit (e.g. `R = (ZMod N)^k`, `N` odd). -/
theorem rev_fix_card {R : Type*} [CommRing R] [Fintype R] [DecidableEq R] (F : R → R)
    (h2 : IsUnit (2 : R)) :
    (Finset.univ.filter (fun x : R × R => QE.Dyn.rev F x = x)).card = Fintype.card R := by
  classical
  obtain ⟨u, hu⟩ := h2
  set c : R := ↑u⁻¹
  have hc : 2 * c = 1 := by rw [← hu]; simp [c]
  symm
  rw [← Finset.card_univ]
  apply Finset.card_bij' (fun q _ => (q, -(F q) * c)) (fun x _ => x.1)
  · intro q _
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    simp only [QE.Dyn.rev, Prod.mk.injEq, true_and]
    linear_combination (F q) * hc
  · intro x _; exact Finset.mem_univ _
  · intro q _; rfl
  · intro x hx
    rw [Finset.mem_filter] at hx
    have h2 : -x.2 - F x.1 = x.2 := congrArg Prod.snd hx.2
    ext
    · rfl
    · simp only
      linear_combination c * h2 + (x.2) * hc

/-- **Every kick–drift map has many cycles.**  On `R²` with `2` a unit, every
kick–drift map (any force) has at least `|R| / 2` distinct symmetric cycles,
whereas a uniformly random permutation of the `|R|²` states has on average
`H_{|R|²} ≈ 2 ln |R|` cycles in total. -/
theorem kickdrift_many_cycles {R : Type*} [CommRing R] [Fintype R] [DecidableEq R] (F : R → R)
    (h2 : IsUnit (2 : R)) :
    Fintype.card R ≤ 2 * ((Finset.univ.filter (fun x : R × R => QE.Dyn.rev F x = x)).image
      (orbitSet (QE.Dyn.leapEquiv F))).card := by
  rw [← rev_fix_card F h2]
  exact symmetric_cycles_ge (QE.Dyn.leapEquiv F) (QE.Dyn.rev F) (kickdrift_reversing F)

end Reversible

/-! ## Monotone lattice maps, the cascade bound -/

section Monotone

/-- **A monotone self-map of a linear order has no cycles but fixed points.** -/
theorem monotone_periodic_fixed {α : Type*} [LinearOrder α] {g : α → α} (hg : Monotone g)
    {x : α} {n : ℕ} (hn : 0 < n) (hx : g^[n] x = x) : g x = x := by
  rcases lt_trichotomy (g x) x with h | h | h
  · exfalso
    have hdec : ∀ k, g^[k + 1] x ≤ g^[k] x := by
      intro k
      induction k with
      | zero => exact h.le
      | succ k ih =>
        have := hg ih
        rwa [← iterate_succ_apply' g (k + 1) x, ← iterate_succ_apply' g k x] at this
    have hle : ∀ k, g^[k + 1] x ≤ g x := by
      intro k
      induction k with
      | zero => exact le_rfl
      | succ k ih => exact (hdec (k + 1)).trans ih
    have := hle (n - 1)
    rw [show n - 1 + 1 = n by omega, hx] at this
    exact absurd this (not_le.mpr h)
  · exact h
  · exfalso
    have hinc : ∀ k, g^[k] x ≤ g^[k + 1] x := by
      intro k
      induction k with
      | zero => exact h.le
      | succ k ih =>
        have := hg ih
        rwa [← iterate_succ_apply' g (k + 1) x, ← iterate_succ_apply' g k x] at this
    have hge : ∀ k, g x ≤ g^[k + 1] x := by
      intro k
      induction k with
      | zero => exact le_rfl
      | succ k ih => exact ih.trans (hinc (k + 1))
    have := hge (n - 1)
    rw [show n - 1 + 1 = n by omega, hx] at this
    exact absurd this (not_le.mpr h)

/-- **An antitone self-map of a linear order has only periods `1` and `2`.** -/
theorem antitone_periodic_two {α : Type*} [LinearOrder α] {g : α → α} (hg : Antitone g)
    {x : α} {n : ℕ} (hn : 0 < n) (hx : g^[n] x = x) : g^[2] x = x := by
  have hm : Monotone (g^[2]) := by
    intro a b hab; simp only [iterate_succ, iterate_zero, comp_apply, id_eq]
    exact hg (hg hab)
  have h2n : (g^[2])^[n] x = x := by
    rw [← iterate_mul, mul_comm, iterate_mul, iterate_succ_apply, iterate_one, hx, hx]
  exact monotone_periodic_fixed hm hn h2n

/-- **Cyclic blocks.**  If `f` moves the block label forward by one
(`blk (f y) = blk y + 1` in `ZMod p`), every period of `f` is a multiple
of `p`. -/
theorem block_period_dvd {X : Type*} {p : ℕ} (f : X → X) (blk : X → ZMod p)
    (hblk : ∀ y, blk (f y) = blk y + 1) {x : X} {n : ℕ} (hx : f^[n] x = x) : p ∣ n := by
  have : ∀ k, blk (f^[k] x) = blk x + k := by
    intro k
    induction k with
    | zero => simp
    | succ k ih => rw [iterate_succ_apply', hblk, ih]; push_cast; ring
  have h := this n
  rw [hx] at h
  have h0 : ((n : ℕ) : ZMod p) = 0 := by linear_combination -h
  exact (ZMod.natCast_eq_zero_iff n p).mp h0

/-- **Periods are bounded by the image.**  The minimal period of a periodic
point of any self-map `f` of a finite set is at most `|f(X)|`. -/
theorem period_le_card_image {X : Type*} [Fintype X] [DecidableEq X] (f : X → X) (x : X)
    (hx : x ∈ periodicPts f) : minimalPeriod f x ≤ (Finset.univ.image f).card := by
  have hpos := minimalPeriod_pos_of_mem_periodicPts hx
  have hinj := iterate_injOn_Iio_minimalPeriod (f := f) (x := x)
  calc minimalPeriod f x = (Finset.range (minimalPeriod f x)).card := (Finset.card_range _).symm
    _ ≤ (Finset.univ.image f).card := by
      apply Finset.card_le_card_of_injOn (fun i => f^[i + 1] x)
      · intro i _
        show f^[i + 1] x ∈ _
        rw [Finset.mem_coe, iterate_succ_apply']
        exact Finset.mem_image_of_mem f (Finset.mem_univ _)
      · intro i hi j hj hij
        have e : ∀ l, f^[minimalPeriod f x - 1] (f^[l + 1] x) = f^[l] x := by
          intro l
          rw [← iterate_add_apply, show minimalPeriod f x - 1 + (l + 1) = l + minimalPeriod f x by
            omega, iterate_add_apply, iterate_minimalPeriod]
        have := congrArg (fun z => f^[minimalPeriod f x - 1] z) hij
        simp only [e] at this
        exact hinj (by simpa using hi) (by simpa using hj) this

/-- **Symmetric maps of the lattice `{0, …, M}`** (`f (M - k) = f k`, as for
every snapped logistic map) have image of size at most `⌊M/2⌋ + 1`, hence
all periods are `≤ ⌊M/2⌋ + 1`: the granular period-doubling cascade stops at
`2^{n*} ≤ M/2 + 1`. -/
theorem symmetric_image_card (M : ℕ) (f : Fin (M + 1) → Fin (M + 1))
    (hf : ∀ k : Fin (M + 1), f (Fin.rev k) = f k) :
    (Finset.univ.image f).card ≤ M / 2 + 1 := by
  classical
  have : Finset.univ.image f ⊆ (Finset.univ.filter (fun k : Fin (M + 1) => k.val ≤ M / 2)).image f := by
    intro y hy
    obtain ⟨k, _, rfl⟩ := Finset.mem_image.mp hy
    by_cases hk : k.val ≤ M / 2
    · exact Finset.mem_image_of_mem f (by simp [hk])
    · refine Finset.mem_image.mpr ⟨Fin.rev k, by simp [Fin.val_rev]; omega, hf k⟩
  calc (Finset.univ.image f).card
      ≤ ((Finset.univ.filter (fun k : Fin (M + 1) => k.val ≤ M / 2)).image f).card :=
        Finset.card_le_card this
    _ ≤ (Finset.univ.filter (fun k : Fin (M + 1) => k.val ≤ M / 2)).card := Finset.card_image_le
    _ = M / 2 + 1 := by
        have : (Finset.univ.filter (fun k : Fin (M + 1) => k.val ≤ M / 2)) =
            (Finset.range (M / 2 + 1)).attachFin (fun i hi => by
              simp at hi; omega) := by
          ext k; simp
        rw [this, Finset.card_attachFin, Finset.card_range]

/-- The snapped logistic map on the lattice `{k/M}`: `k ↦ round(r k (M-k)/M)`
(clamped to `[0, M]`). -/
noncomputable def snapLogistic (r : ℝ) (M : ℕ) (k : Fin (M + 1)) : Fin (M + 1) :=
  ⟨min M ⌊r * k * (M - k) / M + 1 / 2⌋₊, Nat.lt_succ_of_le (min_le_left _ _)⟩

theorem snapLogistic_symm (r : ℝ) (M : ℕ) (k : Fin (M + 1)) :
    snapLogistic r M (Fin.rev k) = snapLogistic r M k := by
  unfold snapLogistic
  congr 2
  have hk : (k.val : ℝ) ≤ M := by exact_mod_cast Nat.lt_succ_iff.mp k.isLt
  simp only [Fin.val_rev]
  rw [show M + 1 - (k.val + 1) = M - k.val by omega, Nat.cast_sub (Nat.lt_succ_iff.mp k.isLt)]
  ring_nf

/-- **Termination of the granular cascade.**  Every cycle of the snapped
logistic map on `M + 1` lattice points has length `≤ ⌊M/2⌋ + 1`; in
particular a cycle of period `2^n` requires `2^n ≤ M/2 + 1`. -/
theorem cascade_terminates (r : ℝ) (M : ℕ) (k : Fin (M + 1))
    (hk : k ∈ periodicPts (snapLogistic r M)) :
    minimalPeriod (snapLogistic r M) k ≤ M / 2 + 1 :=
  (period_le_card_image _ k hk).trans (symmetric_image_card M _ (snapLogistic_symm r M))

/-- `MonotoneOn` version: a monotone self-map of a subset of a linear order has
no cycles but fixed points. -/
theorem monotoneOn_periodic_fixed {α : Type*} [LinearOrder α] {g : α → α} {U : Set α}
    (hmap : Set.MapsTo g U U) (hg : MonotoneOn g U) {x : α} (hx : x ∈ U) {n : ℕ} (hn : 0 < n)
    (hper : g^[n] x = x) : g x = x := by
  have hU : ∀ k, g^[k] x ∈ U := fun k => hmap.iterate k hx
  rcases lt_trichotomy (g x) x with h | h | h
  · exfalso
    have hdec : ∀ k, g^[k + 1] x ≤ g^[k] x := by
      intro k
      induction k with
      | zero => exact h.le
      | succ k ih =>
        have := hg (hU (k + 1)) (hU k) ih
        rwa [← iterate_succ_apply' g (k + 1) x, ← iterate_succ_apply' g k x] at this
    have hle : ∀ k, g^[k + 1] x ≤ g x := by
      intro k
      induction k with
      | zero => exact le_rfl
      | succ k ih => exact (hdec (k + 1)).trans ih
    have := hle (n - 1)
    rw [show n - 1 + 1 = n by omega, hper] at this
    exact absurd this (not_le.mpr h)
  · exact h
  · exfalso
    have hinc : ∀ k, g^[k] x ≤ g^[k + 1] x := by
      intro k
      induction k with
      | zero => exact h.le
      | succ k ih =>
        have := hg (hU k) (hU (k + 1)) ih
        rwa [← iterate_succ_apply' g (k + 1) x, ← iterate_succ_apply' g k x] at this
    have hge : ∀ k, g x ≤ g^[k + 1] x := by
      intro k
      induction k with
      | zero => exact le_rfl
      | succ k ih => exact ih.trans (hinc (k + 1))
    have := hge (n - 1)
    rw [show n - 1 + 1 = n by omega, hper] at this
    exact absurd this (not_le.mpr h)

theorem antitoneOn_periodic_two {α : Type*} [LinearOrder α] {g : α → α} {U : Set α}
    (hmap : Set.MapsTo g U U) (hg : AntitoneOn g U) {x : α} (hx : x ∈ U) {n : ℕ} (hn : 0 < n)
    (hper : g^[n] x = x) : g^[2] x = x := by
  have hm : MonotoneOn (g^[2]) U := by
    intro a ha b hb hab
    simp only [iterate_succ, iterate_zero, comp_apply, id_eq]
    exact hg (hmap hb) (hmap ha) (hg ha hb hab)
  have h2n : (g^[2])^[n] x = x := by
    rw [← iterate_mul, mul_comm, iterate_mul, iterate_succ_apply, iterate_one, hper, hper]
  exact monotoneOn_periodic_fixed (hmap.iterate 2) hm hx hn h2n

/-- **Periods of a granular attracting cycle.**  Let `f` move a block label in
`ZMod P` forward by one on an invariant set `S`, and let `U ⊆ S` be mapped into
itself by the return map `f^P`.  For a periodic point `x ∈ U`: if `f^P` is
monotone on `U` the period is exactly `P`; if `f^P` is antitone on `U` the
period is `P` or `2P`. -/
theorem block_cycle_period {α : Type*} [LinearOrder α] (f : α → α) (P : ℕ) (hP : 0 < P)
    (blk : α → ZMod P) (S : Set α) (hS : Set.MapsTo f S S) (hblk : ∀ y ∈ S, blk (f y) = blk y + 1)
    (U : Set α) (hUS : U ⊆ S) (hmapU : Set.MapsTo (f^[P]) U U) (x : α) (hx : x ∈ U)
    (hxp : x ∈ periodicPts f) :
    (MonotoneOn (f^[P]) U → minimalPeriod f x = P) ∧
      (AntitoneOn (f^[P]) U → minimalPeriod f x = P ∨ minimalPeriod f x = 2 * P) := by
  have hxS : x ∈ S := hUS hx
  have hk : ∀ k, blk (f^[k] x) = blk x + k := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [iterate_succ_apply', hblk _ (hS.iterate k hxS), ih]; push_cast; ring
  have hdvd : ∀ n, f^[n] x = x → P ∣ n := by
    intro n hn
    have h := hk n
    rw [hn] at h
    have h0 : ((n : ℕ) : ZMod P) = 0 := by linear_combination -h
    exact (ZMod.natCast_eq_zero_iff n P).mp h0
  set mp := minimalPeriod f x
  have hmp : 0 < mp := minimalPeriod_pos_of_mem_periodicPts hxp
  have hPmp : P ∣ mp := hdvd mp iterate_minimalPeriod
  obtain ⟨k, hkmp⟩ := hPmp
  have hk0 : 0 < k := by
    rcases Nat.eq_zero_or_pos k with h | h
    · rw [h, mul_zero] at hkmp; omega
    · exact h
  have hgk : (f^[P])^[k] x = x := by rw [← iterate_mul, ← hkmp]; exact iterate_minimalPeriod
  constructor
  · intro hmono
    have hfix := monotoneOn_periodic_fixed hmapU hmono hx hk0 hgk
    have : mp ∣ P := (isPeriodicPt_iff_minimalPeriod_dvd).mp hfix
    exact Nat.dvd_antisymm this ⟨k, hkmp⟩
  · intro hanti
    have hfix2 := antitoneOn_periodic_two hmapU hanti hx hk0 hgk
    have h2 : f^[2 * P] x = x := by rw [mul_comm, iterate_mul]; exact hfix2
    have hd : mp ∣ 2 * P := (isPeriodicPt_iff_minimalPeriod_dvd).mp h2
    -- mp = P k divides 2P, so k ∣ 2
    have hk2 : k ∣ 2 := by
      rw [hkmp] at hd
      exact Nat.dvd_of_mul_dvd_mul_left hP (by rwa [mul_comm 2 P] at hd)
    have : k = 1 ∨ k = 2 := by
      have := Nat.le_of_dvd (by norm_num) hk2
      interval_cases k <;> simp_all
    rcases this with h | h
    · left; rw [hkmp, h, mul_one]
    · right; rw [hkmp, h, mul_comm]

end Monotone

/-! ## Limit cycles of training -/

section Training

/-- One step of seeded stochastic training: the parameter update depends on
the PRNG state, which is advanced by its own deterministic map. -/
def seeded {X S : Type*} (T : S → X → X) (φ : S → S) (z : X × S) : X × S := (T z.2 z.1, φ z.2)

theorem seeded_iterate_snd {X S : Type*} (T : S → X → X) (φ : S → S) (n : ℕ) (z : X × S) :
    ((seeded T φ)^[n] z).2 = φ^[n] z.2 := by
  induction n generalizing z with
  | zero => rfl
  | succ n ih => rw [iterate_succ_apply, ih]; rfl

/-- **The PRNG period divides the training period.**  Every limit cycle of
seeded training has a period that is a multiple of the period of the PRNG. -/
theorem seeded_period_dvd {X S : Type*} (T : S → X → X) (φ : S → S) (z : X × S) (n : ℕ)
    (hz : (seeded T φ)^[n] z = z) : minimalPeriod φ z.2 ∣ n := by
  rw [← isPeriodicPt_iff_minimalPeriod_dvd]
  have := congrArg Prod.snd hz
  rwa [seeded_iterate_snd] at this

/-- Seeded training on finite parameter and PRNG spaces is eventually
periodic, with preperiod plus period at most `|X| |S|`. -/
theorem seeded_eventually_periodic {X S : Type*} [Fintype X] [Fintype S]
    (T : S → X → X) (φ : S → S) (z : X × S) :
    ∃ m n : ℕ, 0 < n ∧ m + n ≤ Fintype.card X * Fintype.card S ∧
      (seeded T φ)^[m + n] z = (seeded T φ)^[m] z := by
  have := QE.Dyn.eventually_periodic (seeded T φ) z
  simpa [Fintype.card_prod] using this

/-- Snapping a real to the integer lattice (granule `1/2`). -/
theorem round_max (v : ℝ) (k : ℤ) :
    (k : ℝ) * v - (k : ℝ) ^ 2 / 2 ≤ (⌊v + 1 / 2⌋ : ℝ) * v - (⌊v + 1 / 2⌋ : ℝ) ^ 2 / 2 ∧
    ((k : ℝ) * v - (k : ℝ) ^ 2 / 2 = (⌊v + 1 / 2⌋ : ℝ) * v - (⌊v + 1 / 2⌋ : ℝ) ^ 2 / 2 →
      k ≤ ⌊v + 1 / 2⌋) := by
  set r := ⌊v + 1 / 2⌋
  have h1 : (r : ℝ) ≤ v + 1 / 2 := Int.floor_le _
  have h2 : v + 1 / 2 < (r : ℝ) + 1 := Int.lt_floor_add_one _
  have key : (r : ℝ) * v - (r : ℝ) ^ 2 / 2 - ((k : ℝ) * v - (k : ℝ) ^ 2 / 2)
      = ((r : ℝ) - k) * (v - ((r : ℝ) + k) / 2) := by ring
  rcases lt_trichotomy k r with hk | hk | hk
  · have hk' : (k : ℝ) ≤ r - 1 := by exact_mod_cast Int.le_sub_one_of_lt hk
    have : 0 ≤ ((r : ℝ) - k) * (v - ((r : ℝ) + k) / 2) :=
      mul_nonneg (by linarith) (by linarith)
    exact ⟨by linarith, fun _ => hk.le⟩
  · subst hk; exact ⟨le_rfl, fun _ => le_rfl⟩
  · have hk' : (r : ℝ) + 1 ≤ k := by exact_mod_cast hk
    have : 0 < ((r : ℝ) - k) * (v - ((r : ℝ) + k) / 2) :=
      mul_pos_of_neg_of_neg (by linarith) (by linarith)
    exact ⟨by linarith, fun h => by linarith⟩

variable {n : ℕ}

/-- Rounded descent on a quadratic loss with symmetric Hessian: `θ ↦ round (L θ + b)`
with `L = I - η H`, on the lattice `ℤ^n` (granule `1/2`; any granule by scaling). -/
noncomputable def rdesc (L : Matrix (Fin n) (Fin n) ℝ) (b : Fin n → ℝ) (θ : Fin n → ℤ) : Fin n → ℤ :=
  fun i => ⌊(L.mulVec (fun j => (θ j : ℝ)) + b) i + 1 / 2⌋

/-- The local objective maximised by one step. -/
noncomputable def phi (L : Matrix (Fin n) (Fin n) ℝ) (b : Fin n → ℝ) (x y : Fin n → ℤ) : ℝ :=
  ∑ i, ((y i : ℝ) * (L.mulVec (fun j => (x j : ℝ)) + b) i - (y i : ℝ) ^ 2 / 2)

/-- The Goles energy of a pair of consecutive states. -/
noncomputable def energy (L : Matrix (Fin n) (Fin n) ℝ) (b : Fin n → ℝ) (x y : Fin n → ℤ) : ℝ :=
  phi L b x y + ∑ i, ((x i : ℝ) * b i - (x i : ℝ) ^ 2 / 2)

theorem energy_symm (L : Matrix (Fin n) (Fin n) ℝ) (hL : L.IsSymm) (b : Fin n → ℝ)
    (x y : Fin n → ℤ) : energy L b x y = energy L b y x := by
  unfold energy phi
  simp only [Pi.add_apply, mul_add, Finset.sum_sub_distrib, Finset.sum_add_distrib]
  have hs : ∑ i, (y i : ℝ) * L.mulVec (fun j => (x j : ℝ)) i =
      ∑ i, (x i : ℝ) * L.mulVec (fun j => (y j : ℝ)) i := by
    simp only [Matrix.mulVec, dotProduct, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro i _
    apply Finset.sum_congr rfl; intro j _
    have h := congrFun (congrFun hL.eq i) j
    rw [Matrix.transpose_apply] at h
    rw [h]; ring
  rw [hs]; ring

theorem phi_le (L : Matrix (Fin n) (Fin n) ℝ) (b : Fin n → ℝ) (x y : Fin n → ℤ) :
    phi L b x y ≤ phi L b x (rdesc L b x) ∧
      (phi L b x y = phi L b x (rdesc L b x) → y ≤ rdesc L b x) := by
  unfold phi rdesc
  have hpt := fun i => round_max ((L.mulVec (fun j => (x j : ℝ)) + b) i) (y i)
  refine ⟨Finset.sum_le_sum fun i _ => (hpt i).1, fun h i => ?_⟩
  have hz := (Finset.sum_eq_sum_iff_of_le (fun i _ => (hpt i).1)).mp h i (Finset.mem_univ i)
  exact (hpt i).2 hz

/-- **Rounded descent on a quadratic has only periods `1` and `2`.**  For every
symmetric `L` (that is, every quadratic loss, every step size) and every
offset `b`, every periodic orbit of `θ ↦ round (L θ + b)` satisfies
`θ_{t+2} = θ_t` (the integer-valued form of the Goles–Olivos theorem). -/
theorem rdesc_period_two (L : Matrix (Fin n) (Fin n) ℝ) (hL : L.IsSymm) (b : Fin n → ℝ)
    (θ : Fin n → ℤ) (p : ℕ) (hp : 0 < p) (hper : (rdesc L b)^[p] θ = θ) :
    (rdesc L b)^[2] θ = θ := by
  set G := rdesc L b
  set x : ℕ → (Fin n → ℤ) := fun t => G^[t] θ with hx
  have hsucc : ∀ t, x (t + 1) = G (x t) := fun t => by simp [hx, iterate_succ_apply']
  set V : ℕ → ℝ := fun t => energy L b (x t) (x (t + 1))
  -- increments are nonnegative
  have hinc : ∀ t, V t ≤ V (t + 1) ∧ (V t = V (t + 1) → x t ≤ x (t + 2)) := by
    intro t
    have e1 : V (t + 1) - V t = phi L b (x (t + 1)) (x (t + 2)) - phi L b (x (t + 1)) (x t) := by
      simp only [V]
      rw [energy_symm L hL b (x t) (x (t + 1))]
      unfold energy; ring
    have hmax := phi_le L b (x (t + 1)) (x t)
    have h2 : x (t + 2) = rdesc L b (x (t + 1)) := hsucc (t + 1)
    rw [← h2] at hmax
    refine ⟨by linarith [hmax.1], fun h => hmax.2 (by linarith)⟩
  have hperx : ∀ t, x (t + 2 * p) = x t := by
    intro t
    simp only [hx]
    rw [iterate_add_apply]
    have : G^[2 * p] θ = θ := by
      rw [two_mul, iterate_add_apply, hper, hper]
    rw [this]
  -- telescoping over `2p` steps
  have htel : ∑ t ∈ Finset.range (2 * p), (V (t + 1) - V t) = 0 := by
    rw [Finset.sum_range_sub (fun t => V t)]
    have e0 : x (2 * p) = x 0 := by simpa using hperx 0
    have e1 : x (2 * p + 1) = x 1 := by
      have := hperx 1; rwa [show 1 + 2 * p = 2 * p + 1 by ring] at this
    dsimp only [V]
    rw [e0, e1]; simp
  have hzero : ∀ t < 2 * p, V t = V (t + 1) := by
    intro t ht
    have := (Finset.sum_eq_zero_iff_of_nonneg (fun t _ => sub_nonneg.mpr (hinc t).1)).mp htel t
      (Finset.mem_range.mpr ht)
    linarith
  have hle : ∀ t < 2 * p, x t ≤ x (t + 2) := fun t ht => (hinc t).2 (hzero t ht)
  have hchain : ∀ j, 1 ≤ j → j ≤ p → x 2 ≤ x (2 * j) := by
    intro j hj1 hjp
    induction j with
    | zero => omega
    | succ j ih =>
      rcases Nat.eq_zero_or_pos j with h0 | hpos
      · subst h0; exact le_rfl
      · exact (ih hpos (by omega)).trans (by
          have := hle (2 * j) (by omega)
          rwa [show 2 * j + 2 = 2 * (j + 1) by ring] at this)
  have h02 : x 0 ≤ x 2 := hle 0 (by omega)
  have h20 : x 2 ≤ x 0 := by
    have := hchain p hp le_rfl
    rwa [show 2 * p = 0 + 2 * p by ring, hperx 0] at this
  have : x 2 = x 0 := le_antisymm h20 h02
  simpa [hx] using this

/-- **Fixed points of rounded descent.**  `round (θ - u) = θ` iff
`-1/2 < u ≤ 1/2`: the fixed points are exactly the lattice points where every
component of the step `η H θ` is at most half a granule. -/
theorem round_fixed_iff (θ : ℤ) (u : ℝ) : ⌊(θ : ℝ) - u + 1 / 2⌋ = θ ↔ -(1 / 2) < u ∧ u ≤ 1 / 2 := by
  rw [Int.floor_eq_iff]
  constructor
  · rintro ⟨h1, h2⟩; constructor <;> linarith
  · rintro ⟨h1, h2⟩; constructor <;> linarith

/-- **The attractor is in a box.**  If one step satisfies
`ν (G θ) ≤ κ ν θ + c` with `0 ≤ κ < 1` (a contraction in a norm `ν`, plus the
rounding error `c`), every periodic point has `ν θ ≤ c / (1 - κ)`. -/
theorem periodic_in_box {X : Type*} (G : X → X) (ν : X → ℝ) (κ c : ℝ) (hκ : κ < 1)
    (hκ0 : 0 ≤ κ) (hG : ∀ θ, ν (G θ) ≤ κ * ν θ + c) (θ : X) (p : ℕ) (hp : 0 < p)
    (hper : G^[p] θ = θ) : ν θ ≤ c / (1 - κ) := by
  classical
  obtain ⟨i, hi, hmax⟩ := Finset.exists_max_image (Finset.range p) (fun i => ν (G^[i] θ))
    ⟨0, Finset.mem_range.mpr hp⟩
  -- the predecessor of `G^[i] θ` on the cycle
  set j := if i = 0 then p - 1 else i - 1
  have hj : j ∈ Finset.range p := by
    simp only [Finset.mem_range] at hi ⊢; simp only [j]; split_ifs <;> omega
  have hGj : G (G^[j] θ) = G^[i] θ := by
    rw [← iterate_succ_apply' G j θ]
    simp only [j]; split_ifs with h
    · rw [h, show (p - 1).succ = p by omega, hper]; rfl
    · rw [show (i - 1).succ = i by omega]
  have h1 : ν (G^[i] θ) ≤ κ * ν (G^[i] θ) + c := by
    have := hG (G^[j] θ)
    rw [hGj] at this
    have h2 := hmax j hj
    nlinarith
  have hbox : ν (G^[i] θ) ≤ c / (1 - κ) := by
    rw [le_div_iff₀ (by linarith)]; linarith
  have h0 := hmax 0 (Finset.mem_range.mpr hp)
  simp only [iterate_zero, id_eq] at h0
  linarith

/-- Rounding adds at most half a granule: with the sup norm and row sums
`∑_j |L_ij| ≤ κ`, one step of rounded descent satisfies
`‖G θ‖ ≤ κ ‖θ‖ + (‖b‖ + 1/2)`. -/
theorem rdesc_norm_le (L : Matrix (Fin n) (Fin n) ℝ) (b : Fin n → ℝ) (κ : ℝ) (hκ0 : 0 ≤ κ)
    (hrow : ∀ i, ∑ j, |L i j| ≤ κ) (θ : Fin n → ℤ) :
    ‖(fun i => ((rdesc L b θ i : ℤ) : ℝ))‖ ≤ κ * ‖(fun i => ((θ i : ℤ) : ℝ))‖ + (‖b‖ + 1 / 2) := by
  have hnn : 0 ≤ κ * ‖(fun i => ((θ i : ℤ) : ℝ))‖ + (‖b‖ + 1 / 2) := by positivity
  rw [pi_norm_le_iff_of_nonneg hnn]
  intro i
  set v := (L.mulVec (fun j => (θ j : ℝ)) + b) i
  have hr1 : (⌊v + 1 / 2⌋ : ℝ) ≤ v + 1 / 2 := Int.floor_le _
  have hr2 : v + 1 / 2 < (⌊v + 1 / 2⌋ : ℝ) + 1 := Int.lt_floor_add_one _
  have hv : |v| ≤ κ * ‖(fun i => ((θ i : ℤ) : ℝ))‖ + ‖b‖ := by
    simp only [v, Pi.add_apply, Matrix.mulVec, dotProduct]
    have hb : |b i| ≤ ‖b‖ := by
      have := norm_le_pi_norm b i; rwa [Real.norm_eq_abs] at this
    have hsum : |∑ j, L i j * (θ j : ℝ)| ≤ κ * ‖(fun i => ((θ i : ℤ) : ℝ))‖ := by
      calc |∑ j, L i j * (θ j : ℝ)| ≤ ∑ j, |L i j * (θ j : ℝ)| := Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ j, |L i j| * ‖(fun i => ((θ i : ℤ) : ℝ))‖ := by
            apply Finset.sum_le_sum; intro j _
            rw [abs_mul]
            apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
            have := norm_le_pi_norm (fun i => ((θ i : ℤ) : ℝ)) j
            rwa [Real.norm_eq_abs] at this
        _ = (∑ j, |L i j|) * ‖(fun i => ((θ i : ℤ) : ℝ))‖ := by rw [Finset.sum_mul]
        _ ≤ κ * ‖(fun i => ((θ i : ℤ) : ℝ))‖ := mul_le_mul_of_nonneg_right (hrow i) (norm_nonneg _)
    calc |∑ j, L i j * (θ j : ℝ) + b i| ≤ |∑ j, L i j * (θ j : ℝ)| + |b i| := abs_add_le _ _
      _ ≤ _ := by linarith
  rw [Real.norm_eq_abs]
  show |(⌊v + 1 / 2⌋ : ℝ)| ≤ _
  rw [abs_le] at hv ⊢
  constructor <;> linarith [hv.1, hv.2]

/-- **The granular attractor of rounded descent is in the box of radius
`(‖b‖ + 1/2)/(1 - κ)` granules.** -/
theorem rdesc_attractor_box (L : Matrix (Fin n) (Fin n) ℝ) (b : Fin n → ℝ) (κ : ℝ) (hκ0 : 0 ≤ κ)
    (hκ : κ < 1) (hrow : ∀ i, ∑ j, |L i j| ≤ κ) (θ : Fin n → ℤ) (p : ℕ) (hp : 0 < p)
    (hper : (rdesc L b)^[p] θ = θ) :
    ‖(fun i => ((θ i : ℤ) : ℝ))‖ ≤ (‖b‖ + 1 / 2) / (1 - κ) :=
  periodic_in_box (rdesc L b) (fun θ => ‖(fun i => ((θ i : ℤ) : ℝ))‖) κ _ hκ hκ0
    (rdesc_norm_le L b κ hκ0 hrow) θ p hp hper

/-- **Symmetry is needed.**  For the non-symmetric contraction
`L = [[-0.3, -0.6], [0.6, -0.3]]` (a rounded rotation), rounded iteration has
a cycle of length `4`: `(-1,0) → (0,-1) → (1,0) → (0,1) → (-1,0)`. -/
theorem rdesc_nonsym_four_cycle :
    let L : Matrix (Fin 2) (Fin 2) ℝ := !![(-3/10 : ℝ), -6/10; 6/10, -3/10]
    (rdesc L 0)^[4] ![-1, 0] = ![-1, 0] ∧ (rdesc L 0)^[2] ![-1, 0] ≠ ![-1, 0] := by
  intro L
  have h1 : rdesc L 0 ![-1, 0] = ![0, -1] := by
    ext i; fin_cases i <;> simp [L, rdesc, Matrix.mulVec, dotProduct, Fin.sum_univ_two] <;> norm_num
  have h2 : rdesc L 0 ![0, -1] = ![1, 0] := by
    ext i; fin_cases i <;> simp [L, rdesc, Matrix.mulVec, dotProduct, Fin.sum_univ_two] <;> norm_num
  have h3 : rdesc L 0 ![1, 0] = ![0, 1] := by
    ext i; fin_cases i <;> simp [L, rdesc, Matrix.mulVec, dotProduct, Fin.sum_univ_two] <;> norm_num
  have h4 : rdesc L 0 ![0, 1] = ![-1, 0] := by
    ext i; fin_cases i <;> simp [L, rdesc, Matrix.mulVec, dotProduct, Fin.sum_univ_two] <;> norm_num
  refine ⟨?_, ?_⟩
  · simp only [iterate_succ, iterate_zero, comp_apply, id_eq, h1, h2, h3, h4]
  · simp only [iterate_succ, iterate_zero, comp_apply, id_eq, h1, h2]
    intro h
    have := congrFun h 0
    simp at this

/-- **Cyclic mini-batches break the period-two law.**  Two rounded
gradient-descent steps on convex quadratics, `L₁ = [[-0.9, 0.4], [0.4, 0.9]]`
(`I - L₁` positive definite) and `L₂ = [[0, 0.6], [0.6, 0]]`, both symmetric,
alternate; the two-step map has a cycle of length `4` through `(0, 1)`, so the
training orbit has period `8 = 4B` (`B = 2`). -/
theorem minibatch_four_cycle :
    let L₁ : Matrix (Fin 2) (Fin 2) ℝ := !![(-9/10 : ℝ), 4/10; 4/10, 9/10]
    let L₂ : Matrix (Fin 2) (Fin 2) ℝ := !![(0 : ℝ), 6/10; 6/10, 0]
    L₁.IsSymm ∧ L₂.IsSymm ∧
    (rdesc L₂ 0 ∘ rdesc L₁ 0)^[4] ![0, 1] = ![0, 1] ∧
      (rdesc L₂ 0 ∘ rdesc L₁ 0)^[2] ![0, 1] ≠ ![0, 1] := by
  intro L₁ L₂
  have e : ∀ (a b : ℤ) (L : Matrix (Fin 2) (Fin 2) ℝ), rdesc L 0 ![a, b] =
      ![⌊L 0 0 * a + L 0 1 * b + 1 / 2⌋, ⌊L 1 0 * a + L 1 1 * b + 1 / 2⌋] := by
    intro a b L; ext i; fin_cases i <;> simp [rdesc, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  have h1 : rdesc L₁ 0 ![0, 1] = ![0, 1] := by rw [e]; ext i; fin_cases i <;> simp [L₁] <;> norm_num
  have h2 : rdesc L₂ 0 ![0, 1] = ![1, 0] := by rw [e]; ext i; fin_cases i <;> simp [L₂] <;> norm_num
  have h3 : rdesc L₁ 0 ![1, 0] = ![-1, 0] := by rw [e]; ext i; fin_cases i <;> simp [L₁] <;> norm_num
  have h4 : rdesc L₂ 0 ![-1, 0] = ![0, -1] := by rw [e]; ext i; fin_cases i <;> simp [L₂] <;> norm_num
  have h5 : rdesc L₁ 0 ![0, -1] = ![0, -1] := by rw [e]; ext i; fin_cases i <;> simp [L₁] <;> norm_num
  have h6 : rdesc L₂ 0 ![0, -1] = ![-1, 0] := by rw [e]; ext i; fin_cases i <;> simp [L₂] <;> norm_num
  have h7 : rdesc L₁ 0 ![-1, 0] = ![1, 0] := by rw [e]; ext i; fin_cases i <;> simp [L₁] <;> norm_num
  have h8 : rdesc L₂ 0 ![1, 0] = ![0, 1] := by rw [e]; ext i; fin_cases i <;> simp [L₂] <;> norm_num
  refine ⟨?_, ?_, ?_, ?_⟩
  · ext i j; fin_cases i <;> fin_cases j <;> simp [L₁, Matrix.transpose_apply]
  · ext i j; fin_cases i <;> fin_cases j <;> simp [L₂, Matrix.transpose_apply]
  · simp only [iterate_succ, iterate_zero, comp_apply, id_eq, h1, h2, h3, h4, h5, h6, h7, h8]
  · simp only [iterate_succ, iterate_zero, comp_apply, id_eq, h1, h2, h3, h4]
    intro h; have := congrFun h 1; simp at this

end Training

/-! ## Exact periods of the cat map modulo a prime -/

section CatPrime

variable (p : ℕ) [hp : Fact p.Prime]

/-- The Fibonacci matrix `Q = [[1,1],[1,0]]`, with `Q² = A` the cat matrix. -/
def fibQ : Matrix (Fin 2) (Fin 2) (ZMod p) := !![1, 1; 1, 0]

theorem fibQ_pow (k : ℕ) :
    fibQ p ^ (k + 1) = !![(Nat.fib (k + 2) : ZMod p), Nat.fib (k + 1); Nat.fib (k + 1), Nat.fib k] := by
  induction k with
  | zero => ext i j; fin_cases i <;> fin_cases j <;> simp [fibQ]
  | succ k ih =>
    rw [pow_succ, ih, fibQ]
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, Nat.fib_add_two] <;> ring

theorem fibQ_sq : fibQ p ^ 2 = fibQ p + 1 := by
  rw [pow_two, fibQ]; ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply]

/-- Frobenius on the Fibonacci matrix: `Q^p = Q` or `Q^p = 1 - Q`, according to
whether `5` is a square mod `p` (`p ≠ 2, 5`). -/
theorem fibQ_frobenius (h2 : p ≠ 2) (h5 : p ≠ 5) :
    fibQ p ^ p = fibQ p ∨ fibQ p ^ p = 1 - fibQ p := by
  set Q := fibQ p
  have hodd : p % 2 = 1 := (Nat.Prime.eq_two_or_odd hp.out).resolve_left h2
  set sc : ZMod p →+* Matrix (Fin 2) (Fin 2) (ZMod p) := Matrix.scalar (Fin 2)
  set k := (p - 1) / 2
  have hpk : p = 2 * k + 1 := by omega
  have h5ne : (5 : ZMod p) ≠ 0 := by
    intro h
    have : ((5 : ℕ) : ZMod p) = 0 := by exact_mod_cast h
    rw [ZMod.natCast_eq_zero_iff] at this
    have := (Nat.prime_dvd_prime_iff_eq hp.out (by norm_num)).mp this
    exact h5 this
  have h2ne : (2 : ZMod p) ≠ 0 := by
    intro h
    have : ((2 : ℕ) : ZMod p) = 0 := by exact_mod_cast h
    rw [ZMod.natCast_eq_zero_iff] at this
    have := (Nat.prime_dvd_prime_iff_eq hp.out Nat.prime_two).mp this
    exact h2 this
  set e : ZMod p := (5 : ZMod p) ^ k
  have he : e = 1 ∨ e = -1 := by
    apply mul_self_eq_one_iff.mp
    rw [← pow_add, ← two_mul, show 2 * k = p - 1 by omega]
    exact ZMod.pow_card_sub_one_eq_one h5ne
  set S := 2 * Q - 1
  have hS2 : S ^ 2 = 5 := by
    have h : Q ^ 2 = Q + 1 := fibQ_sq p
    have : S ^ 2 = 4 * Q ^ 2 - 4 * Q + 1 := by simp only [S]; noncomm_ring
    rw [this, h]; noncomm_ring; simp
  have hSp1 : S ^ p = sc e * S := by
    have hpow : S ^ p = S ^ (2 * k + 1) := congrArg (S ^ ·) hpk
    rw [hpow, pow_succ, pow_mul, hS2]
    congr 1
    simp only [e, map_pow, map_ofNat]
  have hSp2 : S ^ p = 2 * Q ^ p - 1 := by
    have hc : Commute (2 * Q) (-1 : Matrix (Fin 2) (Fin 2) (ZMod p)) := Commute.neg_one_right _
    have := add_pow_char_of_commute p hc
    rw [show S = 2 * Q + -1 by simp only [S]; abel, this]
    have h2p : (2 : Matrix (Fin 2) (Fin 2) (ZMod p)) ^ p = 2 := by
      rw [← map_ofNat sc 2, ← map_pow, ZMod.pow_card]
    rw [(Commute.ofNat_left 2 Q).mul_pow, h2p, Odd.neg_one_pow (by rw [Nat.odd_iff]; exact hodd)]
    abel
  have hinv : sc (2 : ZMod p)⁻¹ * 2 = 1 := by
    rw [← map_ofNat sc 2, ← map_mul, inv_mul_cancel₀ h2ne, map_one]
  rcases he with he | he
  · left
    have h : 2 * Q ^ p = 2 * Q := by
      have := hSp2.symm.trans hSp1
      rw [he, map_one, one_mul] at this
      simp only [S] at this
      exact sub_left_injective this
    have := congrArg (fun z => sc (2 : ZMod p)⁻¹ * z) h
    simpa only [← mul_assoc, hinv, one_mul] using this
  · right
    have h : 2 * Q ^ p = 2 * (1 - Q) := by
      have := hSp2.symm.trans hSp1
      rw [he, map_neg, map_one, neg_one_mul] at this
      simp only [S] at this
      have : 2 * Q ^ p = -(2 * Q - 1) + 1 := by rw [← this]; abel
      rw [this]; noncomm_ring
    have := congrArg (fun z => sc (2 : ZMod p)⁻¹ * z) h
    simpa only [← mul_assoc, hinv, one_mul] using this

/-- From `Q^{2n} = 1` to the periodicity of the cat map. -/
theorem cat_id_of_fibQ (n : ℕ) (hn : 0 < n) (h : fibQ p ^ (2 * n) = 1) :
    ∀ v, (QE.Dyn.cat p)^[n] v = v := by
  rw [QE.Dyn.cat_iterate_eq_id_iff]
  rw [show 2 * n = (2 * n - 1) + 1 by omega, fibQ_pow] at h
  have h01 := congrFun (congrFun h 0) 1
  have h00 := congrFun (congrFun h 0) 0
  simp at h01 h00
  rw [show 2 * n - 1 + 1 = 2 * n by omega] at h01
  rw [show 2 * n - 1 + 2 = 2 * n + 1 by omega] at h00
  exact ⟨h01, h00⟩

/-- **Exact periods of the cat map modulo a prime `p ≠ 2, 5`.**  Either
`c^{(p-1)/2} = id` (when `5` is a square mod `p`) or `c^{p+1} = id`; in all
cases every one of the `p²` states has period at most `p + 1`. -/
theorem cat_prime_period (h2 : p ≠ 2) (h5 : p ≠ 5) :
    (∀ v, (QE.Dyn.cat p)^[(p - 1) / 2] v = v) ∨ (∀ v, (QE.Dyn.cat p)^[p + 1] v = v) := by
  have hp3 : 3 ≤ p := by
    have := hp.out.two_le; omega
  have hodd : p % 2 = 1 := (Nat.Prime.eq_two_or_odd hp.out).resolve_left h2
  have hQinv : fibQ p * (fibQ p - 1) = 1 := by
    have h := fibQ_sq p
    rw [mul_sub, mul_one, ← pow_two, h]; abel
  rcases fibQ_frobenius p h2 h5 with h | h
  · left
    apply cat_id_of_fibQ p _ (by omega)
    rw [show 2 * ((p - 1) / 2) = p - 1 by omega]
    calc fibQ p ^ (p - 1) = fibQ p ^ (p - 1) * (fibQ p * (fibQ p - 1)) := by rw [hQinv, mul_one]
      _ = fibQ p ^ p * (fibQ p - 1) := by
          rw [← mul_assoc, ← pow_succ, show p - 1 + 1 = p by omega]
      _ = 1 := by rw [h, hQinv]
  · right
    apply cat_id_of_fibQ p _ (by omega)
    have h1 : fibQ p ^ (p + 1) = -1 := by
      rw [pow_succ, h, sub_mul, one_mul, ← pow_two, fibQ_sq]; abel
    rw [show 2 * (p + 1) = (p + 1) * 2 by ring, pow_mul, h1]; simp

/-- The state `(1, 0)` has the full period: it returns iff every state does. -/
theorem cat_one_zero_full (N n : ℕ) :
    (QE.Dyn.cat N)^[n] (1, 0) = (1, 0) ↔ ∀ v, (QE.Dyn.cat N)^[n] v = v := by
  constructor
  · intro h
    rw [QE.Dyn.cat_iterate] at h
    simp only [mul_one, mul_zero, add_zero, Prod.mk.injEq] at h
    exact (QE.Dyn.cat_iterate_eq_id_iff N n).mpr ⟨h.2, h.1⟩
  · intro h; exact h _

/-- **Lower bound on the period**: if `c^n = id` on `(ZMod N)²`, `n ≥ 1`, then
`N ≤ F_{2n}`; hence `Π(N) ≥ log_λ N + O(1)`. -/
theorem cat_period_ge (N n : ℕ) (hn : 0 < n) (h : ∀ v, (QE.Dyn.cat N)^[n] v = v) :
    N ≤ Nat.fib (2 * n) := by
  have h0 := ((QE.Dyn.cat_iterate_eq_id_iff N n).mp h).1
  rw [ZMod.natCast_eq_zero_iff] at h0
  exact Nat.le_of_dvd (Nat.fib_pos.mpr (by omega)) h0

end CatPrime

end QE.OpenDyn
