-- SPDX-License-Identifier: MIT
-- Copyright 2026 Metere Industries, Inc. Author: Alfredo Metere.
-- Quasi-Euclidean Granular Geometry. Any derivative work must carry this notice:
--   This work is derivative of the Quasi-Euclidean Granular Geometry book
--   authored by Alfredo Metere. Copyright 2026 Metere Industries, Inc.
--   All rights reserved
-- See LICENSE.md and NOTICE.

import QuasiEuclidean.Ch14_Info
import QuasiEuclidean.Ch15_Dyn
import QuasiEuclidean.OpenDyn
import QuasiEuclidean.Ch15b_Learning
import QuasiEuclidean.OpenSto
import QuasiEuclidean.Ch16_Phys
import QuasiEuclidean.CascadeInfra

/-!
# Review infrastructure E (chapters on information, dynamics, learning, physics)

Lean statements that close the gaps between printed claims and the earlier
Lean constants, found in the pre-publication review:

* `QE.Info.negative_hdiff_exact`: `prop:info-negative` with `H = log k` exactly.
* `QE.Info.nullable_bits`: `prop:info-nullable`, `⌈log₂(M+2)⌉` bits, `NULL ≠ 0`.
* `QE.Dyn.perm_order`: `thm:dyn-perm-periodic` with `n = ord σ = lcm` of cycle lengths.
* `QE.Dyn.ergodic_iff_transitive`, `QE.Dyn.orbitUnion_invariant`: `prop:dyn-ergodic`.
* `QE.Dyn.not_mixing`, `QE.Dyn.mixing_of_card_one`: `prop:dyn-no-mixing`.
* `QE.Dyn.dbl_fibre_card`, `QE.Dyn.dbl_entropy`: `thm:dyn-one-bit-per-step`.
* `QE.Dyn.dbl_lyapunov`: `prop:dyn-lyapunov-doubling`.
* `QE.OpenDyn.cascade_log_bound`: `thm:dyn-cascade` (logarithmic form, `M ≥ 3`).
* `QE.Learn.sign_flip_cells_iff_odd`: `thm:learning-quantisability` (iv).
* `QE.Learn.cube_rigidity`: `thm:learning-rigid` in full (integrality and the
  signed-permutation step included).
* `QE.Learn.chernoff_proportion`, `QE.Learn.sample_size`: `thm:learning-sampling`
  in the printed (uniform draws, proportion) form.
* `QE.OpenSto.Learn.cell_tail_any`, `QE.OpenSto.Learn.cell_two_sided`:
  `thm:learning-cancel`.
* `QE.Phys.first_law_deriv`: `prop:phys-first-law` with the derivative checked.

Everything is finitary; nothing uses Lebesgue measure or integration.
-/

open Finset Function Filter Topology

/-! ## Information -/

namespace QE.Info

/-- **`prop:info-negative`, exact form.**  Uniform on `k` cells of total length
`kv = 1/4` (density `4`): the granular differential entropy is `-log 4`, while the
Shannon entropy is exactly `log k` (in particular `≥ 0`). -/
theorem negative_hdiff_exact (k : ℕ) (hk : 0 < k) (v : ℝ) (hkv : (k : ℝ) * v = 1 / 4) :
    hgran (Finset.univ : Finset (Fin k)) (fun _ => 4) v = - Real.log 4 ∧
    entropy (Finset.univ : Finset (Fin k)) (fun _ => 4 * v) = Real.log k ∧
    0 ≤ entropy (Finset.univ : Finset (Fin k)) (fun _ => 4 * v) := by
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  have hv : 4 * v = 1 / k := by field_simp; linarith
  obtain ⟨h1, h3⟩ := negative_hdiff_example k hk v hkv
  refine ⟨h1, ?_, h3⟩
  rw [hv, entropy_uniform k hk]

/-- **`prop:info-nullable` in full.**  A nullable field has `M + 2` states,
`NULL` and `0` are different states, and `b` bits suffice iff `M + 2 ≤ 2^b`,
iff `log₂(M+2) ≤ b`, iff `⌈log₂(M+2)⌉ ≤ b`. -/
theorem nullable_bits (M b : ℕ) :
    Fintype.card (Option (Fin (M + 1))) = M + 2 ∧
    (none : Option (Fin (M + 1))) ≠ some 0 ∧
    ((∃ c : Option (Fin (M + 1)) → (Fin b → Bool), Injective c) ↔ M + 2 ≤ 2 ^ b) ∧
    ((∃ c : Option (Fin (M + 1)) → (Fin b → Bool), Injective c) ↔
      Real.logb 2 ((M : ℝ) + 2) ≤ b) ∧
    ((∃ c : Option (Fin (M + 1)) → (Fin b → Bool), Injective c) ↔
      ⌈Real.logb 2 ((M : ℝ) + 2)⌉₊ ≤ b) := by
  have hreg : (∃ c : Option (Fin (M + 1)) → (Fin b → Bool), Injective c) ↔ M + 2 ≤ 2 ^ b := by
    constructor
    · rintro ⟨c, hc⟩
      have := Fintype.card_le_of_injective c hc
      simp at this; omega
    · intro h
      have : Nonempty (Option (Fin (M + 1)) ↪ (Fin b → Bool)) := by
        rw [Function.Embedding.nonempty_iff_card_le]; simp; omega
      obtain ⟨e⟩ := this
      exact ⟨e, e.injective⟩
  have hlog : M + 2 ≤ 2 ^ b ↔ Real.logb 2 ((M : ℝ) + 2) ≤ b := by
    have := register_logb (M + 1) b
    rw [show ((M + 1 : ℕ) : ℝ) + 1 = (M : ℝ) + 2 by push_cast; ring] at this
    exact this
  refine ⟨nullable_card M, by simp, hreg, hreg.trans hlog, ?_⟩
  rw [hreg, hlog, Nat.ceil_le]

end QE.Info

/-! ## Dynamics -/

namespace QE.Dyn

section PermOrder

variable {X : Type*} [Fintype X] [DecidableEq X]

/-- **`thm:dyn-perm-periodic` in full.**  `σ^n = id` for `n = ord σ ≥ 1`, which is
the l.c.m. of the cycle lengths; and `σ^m = id` iff `ord σ ∣ m`, so `ord σ` is the
first time at which all states recur simultaneously. -/
theorem perm_order (σ : Equiv.Perm X) :
    σ ^ orderOf σ = 1 ∧ 1 ≤ orderOf σ ∧ σ.cycleType.lcm = orderOf σ ∧
    (∀ m : ℕ, σ ^ m = 1 ↔ orderOf σ ∣ m) ∧
    (∀ m : ℕ, 0 < m → σ ^ m = 1 → orderOf σ ≤ m) :=
  ⟨pow_orderOf_eq_one σ, orderOf_pos σ, Equiv.Perm.lcm_cycleType σ,
    fun _ => orderOf_dvd_iff_pow_eq_one.symm,
    fun _ hm h => Nat.le_of_dvd hm (orderOf_dvd_iff_pow_eq_one.2 h)⟩

end PermOrder

section Ergodic2

variable {X : Type*} [Fintype X]

/-- Ergodicity for the uniform granular measure: the only non-empty invariant
(internal, i.e. finite) set is the whole space. -/
def IsErgodicPerm (σ : Equiv.Perm X) : Prop :=
  ∀ A : Finset X, (∀ x ∈ A, σ x ∈ A) → A.Nonempty → A = Finset.univ

open Classical in
/-- The union of the cycles through the points of `B`. -/
noncomputable def orbitUnion (σ : Equiv.Perm X) (B : Finset X) : Finset X :=
  Finset.univ.filter fun z => ∃ b ∈ B, ∃ k : ℕ, (σ ^ k) b = z

/-- **Every union of cycles is invariant** (`prop:dyn-ergodic`, converse part). -/
theorem orbitUnion_invariant (σ : Equiv.Perm X) (B : Finset X) :
    (∀ x ∈ orbitUnion σ B, σ x ∈ orbitUnion σ B) ∧ B ⊆ orbitUnion σ B := by
  constructor
  · intro x hx
    simp only [orbitUnion, mem_filter, mem_univ, true_and] at hx ⊢
    obtain ⟨b, hb, k, rfl⟩ := hx
    exact ⟨b, hb, k + 1, by rw [pow_succ', Equiv.Perm.mul_apply]⟩
  · intro b hb
    simp only [orbitUnion, mem_filter, mem_univ, true_and]
    exact ⟨b, hb, 0, by simp⟩

/-- **`prop:dyn-ergodic`, both directions.**  A permutation is ergodic for the
uniform granular measure iff it has a single orbit (is a single cycle). -/
theorem ergodic_iff_transitive (σ : Equiv.Perm X) :
    IsErgodicPerm σ ↔ ∀ x y : X, ∃ k : ℕ, (σ ^ k) x = y := by
  constructor
  · intro h x y
    have hA := h (orbitUnion σ {x}) (orbitUnion_invariant σ {x}).1
      ⟨x, (orbitUnion_invariant σ {x}).2 (mem_singleton_self x)⟩
    have hy : y ∈ orbitUnion σ {x} := by rw [hA]; exact mem_univ y
    simp only [orbitUnion, mem_filter, mem_univ, true_and, mem_singleton] at hy
    obtain ⟨b, rfl, k, hk⟩ := hy
    exact ⟨k, hk⟩
  · intro htr A hinv hne
    exact ergodic_of_transitive σ htr A hinv hne

/-- Normalised granular measure `#A / #X`. -/
noncomputable def mnorm (A : Finset X) : ℝ := (A.card : ℝ) / Fintype.card X

/-- **`prop:dyn-no-mixing`, "never mixing".**  If `#X ≥ 2`, no permutation is
mixing in the exact sense `μ(σ^{-t}A ∩ B) → μ(A) μ(B)` (normalised measure). -/
theorem not_mixing [DecidableEq X] (σ : Equiv.Perm X) (h2 : 2 ≤ Fintype.card X) :
    ¬ ∀ A B : Finset X, Tendsto (fun t : ℕ => mnorm (B.filter fun x => (σ ^ t) x ∈ A))
        atTop (𝓝 (mnorm A * mnorm B)) := by
  intro hmix
  have hne : Nonempty X := Fintype.card_pos_iff.1 (by omega)
  obtain ⟨x⟩ := hne
  have hlim := hmix {x} {x}
  set n := orderOf σ
  have hn : 0 < n := orderOf_pos σ
  have hsub : Tendsto (fun m : ℕ => n * m) atTop atTop :=
    tendsto_atTop_atTop.2 fun b => ⟨b, fun m hm => le_trans hm (Nat.le_mul_of_pos_left m hn)⟩
  have hconst : ∀ m : ℕ, mnorm (({x} : Finset X).filter fun y => (σ ^ (n * m)) y ∈ ({x} : Finset X))
      = mnorm ({x} : Finset X) := by
    intro m
    congr 1
    ext y
    simp only [mem_filter, mem_singleton]
    constructor
    · exact fun h => h.1
    · intro hy; refine ⟨hy, ?_⟩
      rw [hy, pow_mul, pow_orderOf_eq_one, one_pow, Equiv.Perm.one_apply]
  have h1 := hlim.comp hsub
  have h1' : Tendsto (fun _ : ℕ => mnorm ({x} : Finset X)) atTop
      (𝓝 (mnorm ({x} : Finset X) * mnorm ({x} : Finset X))) := by
    refine h1.congr ?_
    intro m; exact hconst m
  have heq := tendsto_nhds_unique tendsto_const_nhds h1'
  have hN : (2 : ℝ) ≤ Fintype.card X := by exact_mod_cast h2
  simp only [mnorm, card_singleton, Nat.cast_one] at heq
  have hpos : (0 : ℝ) < Fintype.card X := by linarith
  field_simp at heq
  nlinarith

/-- **`prop:dyn-no-mixing`, the exception.**  On a one-point space every
permutation is exactly mixing. -/
theorem mixing_of_card_one [DecidableEq X] (σ : Equiv.Perm X) (h1 : Fintype.card X = 1) :
    ∀ A B : Finset X, Tendsto (fun t : ℕ => mnorm (B.filter fun x => (σ ^ t) x ∈ A))
        atTop (𝓝 (mnorm A * mnorm B)) := by
  obtain ⟨a, ha⟩ := Fintype.card_eq_one_iff.1 h1
  have hsub : ∀ A : Finset X, A = ∅ ∨ A = Finset.univ := by
    intro A
    rcases A.eq_empty_or_nonempty with h | ⟨b, hb⟩
    · exact Or.inl h
    · right; apply eq_univ_of_forall; intro y; rwa [ha y, ← ha b]
  have hm : mnorm (Finset.univ : Finset X) = 1 := by
    simp [mnorm, h1]
  intro A B
  rcases hsub A with rfl | rfl
  · simp [mnorm]
  · have : ∀ t : ℕ, (B.filter fun x => (σ ^ t) x ∈ (Finset.univ : Finset X)) = B := by
      intro t; ext; simp
    simp only [this, hm, one_mul]
    exact tendsto_const_nhds

end Ergodic2

/-- Fibres of `d_K^j` on the dyadic lattice: each image point `2^j r`
(`r < 2^{K-j}`) has exactly `2^j` preimages. -/
theorem dbl_fibre_card (K j : ℕ) (hj : j ≤ K) (r : ℕ) (hr : r < 2 ^ (K - j)) :
    ((range (2 ^ K)).filter fun k => (dbl K)^[j] k = 2 ^ j * r).card = 2 ^ j := by
  set m := 2 ^ (K - j)
  have hm : 0 < m := by positivity
  have hK : 2 ^ K = m * 2 ^ j := by rw [← pow_add]; congr 1; omega
  have hset : ((range (2 ^ K)).filter fun k => (dbl K)^[j] k = 2 ^ j * r)
      = (range (2 ^ j)).image (fun q => r + m * q) := by
    ext k
    simp only [mem_filter, mem_range, mem_image]
    constructor
    · rintro ⟨hk, h⟩
      rw [dbl_iterate_shift K j k hj hk] at h
      have h' : k % m = r := Nat.eq_of_mul_eq_mul_left (by positivity) h
      refine ⟨k / m, ?_, ?_⟩
      · rw [hK] at hk
        exact (Nat.div_lt_iff_lt_mul hm).2 (by rw [mul_comm]; exact hk)
      · rw [← h']; exact Nat.mod_add_div k m
    · rintro ⟨q, hq, rfl⟩
      have hlt : r + m * q < 2 ^ K := by
        rw [hK]
        calc r + m * q < m + m * q := by omega
          _ = m * (q + 1) := by ring
          _ ≤ m * 2 ^ j := Nat.mul_le_mul_left _ hq
      refine ⟨hlt, ?_⟩
      rw [dbl_iterate_shift K j _ hj hlt]
      congr 1
      rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hr]
  rw [hset, card_image_of_injective _ (fun a b h => by
    simpa [hm.ne'] using h), card_range]

/-- **`thm:dyn-one-bit-per-step`, entropy.**  If `X₀` is uniform on the `2^K`
dyadic lattice points, the push-forward law of `d_K^j X₀` (weight of `y` = number
of preimages `/ 2^K`) has Shannon entropy exactly `(K - j) ln 2`, i.e. `K - j`
bits, for `0 ≤ j ≤ K`. -/
theorem dbl_entropy (K j : ℕ) (hj : j ≤ K) :
    QE.Info.entropy ((range (2 ^ K)).image ((dbl K)^[j]))
      (fun y => (((range (2 ^ K)).filter fun k => (dbl K)^[j] k = y).card : ℝ) / 2 ^ K)
      = ((K - j : ℕ) : ℝ) * Real.log 2 ∧
    QE.Info.entropy ((range (2 ^ K)).image ((dbl K)^[j]))
      (fun y => (((range (2 ^ K)).filter fun k => (dbl K)^[j] k = y).card : ℝ) / 2 ^ K)
      / Real.log 2 = ((K - j : ℕ) : ℝ) := by
  have hK : (2 : ℝ) ^ K = 2 ^ (K - j) * 2 ^ j := by rw [← pow_add]; congr 1; omega
  have hw : ∀ y ∈ (range (2 ^ K)).image ((dbl K)^[j]),
      (((range (2 ^ K)).filter fun k => (dbl K)^[j] k = y).card : ℝ) / 2 ^ K
        = 1 / 2 ^ (K - j) := by
    intro y hy
    obtain ⟨k, hk, rfl⟩ := mem_image.1 hy
    rw [mem_range] at hk
    have hr : k % 2 ^ (K - j) < 2 ^ (K - j) := Nat.mod_lt _ (by positivity)
    rw [dbl_iterate_shift K j k hj hk, dbl_fibre_card K j hj _ hr, hK]
    push_cast
    field_simp
  have hE : QE.Info.entropy ((range (2 ^ K)).image ((dbl K)^[j]))
      (fun y => (((range (2 ^ K)).filter fun k => (dbl K)^[j] k = y).card : ℝ) / 2 ^ K)
      = ((K - j : ℕ) : ℝ) * Real.log 2 := by
    unfold QE.Info.entropy
    rw [sum_congr rfl (fun y hy => by simp only []; rw [hw y hy]), sum_const, dbl_image_card K j hj,
      nsmul_eq_mul]
    simp only [Real.negMulLog, one_div, Real.log_inv, Real.log_pow]
    push_cast
    have : (0 : ℝ) < 2 ^ (K - j) := by positivity
    field_simp
  refine ⟨hE, ?_⟩
  rw [hE]
  have : Real.log 2 ≠ 0 := (Real.log_pos (by norm_num)).ne'
  field_simp

/-- **`prop:dyn-lyapunov-doubling` in full.**  On `ℤ/2^K` (`K ≥ 1`), for
neighbouring lattice points (`x - y = 1`) and `t ≤ K - 1`, the circular distance
(`|valMinAbs|`, i.e. `min(v, 2^K - v)`) between the orbits after `t` steps is
exactly `2^t` lattice steps, and the granular Lyapunov exponent
`(1/t) ln(2ε·2^t / 2ε)` is exactly `ln 2` for `t ≥ 1`. -/
theorem dbl_lyapunov (K t : ℕ) (hK : 1 ≤ K) (ht : t ≤ K - 1) (x y : ZMod (2 ^ K))
    (hxy : x - y = 1) :
    (2 ^ t * x - 2 ^ t * y : ZMod (2 ^ K)).valMinAbs = 2 ^ t ∧
    (2 ^ t * x - 2 ^ t * y : ZMod (2 ^ K)).valMinAbs.natAbs =
      min (2 ^ t * x - 2 ^ t * y : ZMod (2 ^ K)).val
        (2 ^ K - (2 ^ t * x - 2 ^ t * y : ZMod (2 ^ K)).val) ∧
    (∀ ε : ℝ, 0 < ε → 1 ≤ t →
      (1 / (t : ℝ)) * Real.log (2 * ε * (2 : ℝ) ^ t / (2 * ε)) = Real.log 2) := by
  have hdiff : (2 ^ t * x - 2 ^ t * y : ZMod (2 ^ K)) = ((2 ^ t : ℕ) : ZMod (2 ^ K)) := by
    rw [dbl_separation, hxy, mul_one]; push_cast; rfl
  have hhalf : 2 ^ t ≤ 2 ^ K / 2 := by
    have : 2 ^ K = 2 ^ (K - 1) * 2 := by rw [← pow_succ]; congr 1; omega
    rw [this, Nat.mul_div_cancel _ (by norm_num)]
    exact Nat.pow_le_pow_right (by norm_num) ht
  have hNZ : NeZero (2 ^ K) := ⟨by positivity⟩
  refine ⟨?_, ZMod.valMinAbs_natAbs_eq_min _, ?_⟩
  · rw [hdiff, ZMod.valMinAbs_natCast_of_le_half hhalf]; push_cast; rfl
  · intro ε hε ht1
    have : 2 * ε * (2 : ℝ) ^ t / (2 * ε) = 2 ^ t := by field_simp
    rw [this, Real.log_pow]
    have : (t : ℝ) ≠ 0 := by exact_mod_cast (by omega : t ≠ 0)
    field_simp

end QE.Dyn

namespace QE.OpenDyn

open Function

/-- **`thm:dyn-cascade`, logarithmic form.**  For the snapped logistic map on the
`M + 1` lattice points `k/M` (`2ε = 1/M`), a cycle of period `2^n` forces
`2^n ≤ M/2 + 1`, so `n ≤ log₂(M/2 + 1)`; and for `M ≥ 3` this is `< log₂ M =
log₂(1/2ε)`.  (For `M ≤ 2` the strict inequality fails: `M/2 + 1 ≥ M`.) -/
theorem cascade_log_bound (r : ℝ) (M n : ℕ) (k : Fin (M + 1))
    (hk : k ∈ periodicPts (snapLogistic r M)) (hn : minimalPeriod (snapLogistic r M) k = 2 ^ n) :
    2 ^ n ≤ M / 2 + 1 ∧ (n : ℝ) ≤ Real.logb 2 ((M : ℝ) / 2 + 1) ∧
    (3 ≤ M → Real.logb 2 ((M : ℝ) / 2 + 1) < Real.logb 2 (M : ℝ)) ∧
    (M ≤ 2 → (M : ℝ) ≤ (M : ℝ) / 2 + 1) := by
  have h1 : 2 ^ n ≤ M / 2 + 1 := hn ▸ cascade_terminates r M k hk
  have h1r : (2 : ℝ) ^ n ≤ (M : ℝ) / 2 + 1 := by
    have : ((M / 2 : ℕ) : ℝ) ≤ (M : ℝ) / 2 := Nat.cast_div_le
    have h1' : ((2 ^ n : ℕ) : ℝ) ≤ ((M / 2 + 1 : ℕ) : ℝ) := by exact_mod_cast h1
    push_cast at h1'
    linarith
  refine ⟨h1, ?_, ?_, ?_⟩
  · rw [Real.le_logb_iff_rpow_le (by norm_num) (by positivity), Real.rpow_natCast]
    exact h1r
  · intro hM
    have hM' : (3 : ℝ) ≤ M := by exact_mod_cast hM
    exact Real.logb_lt_logb (by norm_num) (by positivity) (by linarith)
  · intro hM
    have hM' : (M : ℝ) ≤ 2 := by exact_mod_cast hM
    linarith

end QE.OpenDyn

namespace QE.CascadeInfra

open Function Set Filter Topology

/-- The classical input of `prop:dyn-cascade-standard` ("for every `n` the quadratic
family has a standard parameter with an attracting `2^n`-cycle, multiplier in
`(0,1)`, attracting `1/2`"; a consequence of Milnor–Thurston kneading theory, cited,
not formalised), stated as a hypothesis. -/
def KneadingCascadeInput : Prop :=
  ∀ n : ℕ, ∃ r : ℝ, ∃ c : ℕ → ℝ, 0 ≤ r ∧ r ≤ 4 ∧ Periodic c (2 ^ n) ∧
    (∀ i, ell r (c i) = c (i + 1)) ∧
    (∀ i < 2 ^ n, ∀ j < 2 ^ n, c i = c j → i = j) ∧ (∀ i, c i ∈ Icc (0 : ℝ) 1) ∧
    0 < multiplier r c (2 ^ n) ∧ multiplier r c (2 ^ n) < 1 ∧
    ∃ j, Tendsto (fun m => (ell r)^[m] (1 / 2) - c (m + j)) atTop (𝓝 0)

/-- **`prop:dyn-cascade-standard`, "in particular" clause, conditional on the cited
classical input.**  Granted `KneadingCascadeInput`, at every infinitesimal granule
(unlimited `N`) and for every standard `n` there is a standard parameter at which
the snapped orbit of (the lattice point nearest) `1/2` is eventually periodic with
period exactly `2^n`: the granular cascade has every standard level, so `n_*` is
infinite. -/
theorem every_level_of_kneading (hK : KneadingCascadeInput) (n : ℕ)
    {N : ℕ → ℕ} (hN : QE.NSA.IsUnlimited (N : QE.NSA.Ult ℕ)) :
    ∃ r : ℝ, ∀ᶠ k in (hyperfilter ℕ : Filter ℕ), ∃ m : ℕ,
      (QE.OpenDyn.snapLogistic r (N k))^[m] (nearest (N k) (1 / 2)) ∈
        periodicPts (QE.OpenDyn.snapLogistic r (N k)) ∧
      minimalPeriod (QE.OpenDyn.snapLogistic r (N k))
        ((QE.OpenDyn.snapLogistic r (N k))^[m] (nearest (N k) (1 / 2))) = 2 ^ n := by
  obtain ⟨r, c, hr0, hr4, hcP, hc, hinj, hc01, hμ0, hμ1, hatt⟩ := hK n
  refine ⟨r, ?_⟩
  have h := half_orbit_period_unlimited hr0 hr4 (by positivity) hcP hc hinj hc01 hμ0.ne'
    (by rw [abs_of_pos hμ0]; exact hμ1) hatt hN
  filter_upwards [h] with k hk
  obtain ⟨m, hm1, hm2, _⟩ := hk
  exact ⟨m, hm1, hm2 hμ0⟩

end QE.CascadeInfra

/-! ## Learning machines -/

namespace QE.Learn

/-- **Sign flips qualify iff the ratio is odd** (`thm:learning-quantisability` (iv)).
The sign flip `k ↦ -k` of a fine index maps every coarse cell
`{k : q_r(k) = q}` onto a coarse cell iff `r` is odd. -/
theorem sign_flip_cells_iff_odd (r : ℕ) (hr : 0 < r) :
    (∀ q : ℤ, ∃ q' : ℤ, ∀ k : ℤ, qz r k = q ↔ qz r (-k) = q') ↔ Odd r := by
  constructor
  · intro h
    by_contra hodd
    obtain ⟨m, hm⟩ := Nat.not_odd_iff_even.1 hodd
    have hm1 : 0 < m := by omega
    obtain ⟨q', hq'⟩ := h 0
    have hr' : (r : ℤ) = 2 * m := by rw [hm]; push_cast; ring
    have h4 : (0 : ℤ) < 4 * m := by omega
    -- `q_r(0) = 0`, so `q' = 0`
    have h0 : qz r 0 = 0 := by
      unfold qz; rw [hr']; simp only [mul_zero, zero_add]
      exact Int.ediv_eq_zero_of_lt (by omega) (by omega)
    have hq0 : q' = 0 := by
      have := (hq' 0).1 h0; rw [neg_zero, h0] at this; exact this.symm
    -- `q_r(-m) = 0` but `q_r(m) = 1`
    have hneg : qz r (-(m : ℤ)) = 0 := by
      unfold qz; rw [hr']
      rw [show 2 * -(m : ℤ) + 2 * m = 0 by ring]; simp
    have hpos : qz r (m : ℤ) = 1 := by
      unfold qz; rw [hr']
      rw [show 2 * (m : ℤ) + 2 * m = 4 * m by ring, show 2 * (2 * (m : ℤ)) = 4 * m by ring]
      exact Int.ediv_self h4.ne'
    have := (hq' (-(m : ℤ))).1 hneg
    rw [neg_neg, hpos, hq0] at this
    exact one_ne_zero this
  · rintro ⟨j, rfl⟩
    intro q
    refine ⟨-q, fun k => ?_⟩
    rw [qz_neg_odd]
    constructor
    · intro h; rw [h]
    · intro h; linarith

/-- **Cube rigidity, in full** (`thm:learning-rigid`).  Let `M ≥ 1` and let `A` be an
invertible real `k × k` matrix such that `x ↦ xA` maps the integer cube
`{-M,…,M}^k` into itself.  Then `A` is a signed permutation matrix:
`A i j = s i` if `j = σ i` and `0` otherwise, with `s i = ±1`.  Conversely every
signed permutation matrix maps the cube into itself.  (Integrality of `A` and the
step "one non-zero entry per column ⇒ signed permutation" are included.) -/
theorem cube_rigidity {k : ℕ} (M : ℤ) (hM : 1 ≤ M) (A : Matrix (Fin k) (Fin k) ℝ)
    (hA : IsUnit A)
    (hcube : ∀ x : Fin k → ℤ, (∀ i, |x i| ≤ M) →
      ∃ y : Fin k → ℤ, (∀ j, |y j| ≤ M) ∧ ∀ j, ∑ i, (x i : ℝ) * A i j = y j) :
    ∃ σ : Equiv.Perm (Fin k), ∃ s : Fin k → ℤ, (∀ i, s i = 1 ∨ s i = -1) ∧
      ∀ i j, A i j = if j = σ i then (s i : ℝ) else 0 := by
  classical
  -- integrality: the rows `e_i A` are lattice points
  have hint : ∀ i, ∃ y : Fin k → ℤ, ∀ j, A i j = y j := by
    intro i
    obtain ⟨y, -, hy⟩ := hcube (Pi.single i 1) (fun l => by
      by_cases h : l = i
      · subst h; simp; exact hM
      · simp [h]; omega)
    refine ⟨y, fun j => ?_⟩
    rw [← hy j]
    rw [Finset.sum_eq_single i]
    · simp
    · intro b _ hb; simp [hb]
    · simp
  choose Z hZ using hint
  have hZcube : ∀ x : Fin k → ℤ, (∀ i, |x i| ≤ M) → ∀ j, |∑ i, x i * Z i j| ≤ M := by
    intro x hx j
    obtain ⟨y, hyM, hy⟩ := hcube x hx
    have : ((∑ i, x i * Z i j : ℤ) : ℝ) = (y j : ℝ) := by
      rw [← hy j]; push_cast; simp_rw [hZ]
    have : ∑ i, x i * Z i j = y j := by exact_mod_cast this
    rw [this]; exact hyM j
  have hcol : ∀ j, (∀ i, |Z i j| ≤ 1) ∧ ∀ i i', Z i j ≠ 0 → Z i' j ≠ 0 → i = i' :=
    fun j => col_support (fun i => Z i j) (cube_col_l1 Z M hM hZcube j)
  -- every column is non-zero (left inverse)
  obtain ⟨B, hB⟩ := hA.exists_left_inv
  obtain ⟨C, hC⟩ := hA.exists_right_inv
  have hcolnz : ∀ j, ∃ i, Z i j ≠ 0 := by
    intro j
    by_contra hcon
    push Not at hcon
    have h1 : (B * A) j j = 1 := by rw [hB]; simp
    rw [Matrix.mul_apply] at h1
    simp only [hZ, hcon, Int.cast_zero, mul_zero, Finset.sum_const_zero] at h1
    exact zero_ne_one h1
  choose τ hτ using hcolnz
  have hτu : ∀ i j, Z i j ≠ 0 ↔ i = τ j := by
    intro i j
    constructor
    · intro h; exact (hcol j).2 i (τ j) h (hτ j)
    · rintro rfl; exact hτ j
  -- every row is non-zero (right inverse), so `τ` is onto
  have hsurj : Surjective τ := by
    intro i
    by_contra hcon
    push Not at hcon
    have h1 : (A * C) i i = 1 := by rw [hC]; simp
    rw [Matrix.mul_apply] at h1
    have : ∀ l, A i l = 0 := by
      intro l
      have : ¬ Z i l ≠ 0 := fun h => hcon l ((hτu i l).1 h).symm
      push Not at this
      rw [hZ, this]; simp
    simp only [this, zero_mul, Finset.sum_const_zero] at h1
    exact zero_ne_one h1
  have hbij : Bijective τ := ⟨Finite.injective_iff_surjective.2 hsurj, hsurj⟩
  let e := Equiv.ofBijective τ hbij
  refine ⟨e.symm, fun i => Z i (e.symm i), fun i => ?_, fun i j => ?_⟩
  · have hne : Z i (e.symm i) ≠ 0 := by
      rw [hτu]; exact (e.apply_symm_apply i).symm
    have hle := (hcol (e.symm i)).1 i
    show Z i (e.symm i) = 1 ∨ Z i (e.symm i) = -1
    rcases abs_le.1 hle with ⟨h1, h2⟩
    omega
  · rw [hZ]
    by_cases hj : j = e.symm i
    · rw [if_pos hj, hj]
    · rw [if_neg hj]
      have : ¬ Z i j ≠ 0 := by
        rw [hτu]
        intro h
        apply hj
        rw [h]; exact (e.symm_apply_apply j).symm
      push Not at this
      rw [this]; simp

/-- Converse of `cube_rigidity`: a signed permutation matrix maps the cube into
itself. -/
theorem signed_perm_maps_cube {k : ℕ} (M : ℤ) (σ : Equiv.Perm (Fin k)) (s : Fin k → ℤ)
    (hs : ∀ i, s i = 1 ∨ s i = -1) (x : Fin k → ℤ) (hx : ∀ i, |x i| ≤ M) :
    ∃ y : Fin k → ℤ, (∀ j, |y j| ≤ M) ∧
      ∀ j, ∑ i, (x i : ℝ) * (if j = σ i then (s i : ℝ) else 0) = y j := by
  refine ⟨fun j => x (σ.symm j) * s (σ.symm j), fun j => ?_, fun j => ?_⟩
  · show |x (σ.symm j) * s (σ.symm j)| ≤ M
    rcases hs (σ.symm j) with h | h <;> rw [h] <;> simp [hx]
  · rw [Finset.sum_eq_single (σ.symm j)]
    · simp
    · intro b _ hb
      have : j ≠ σ b := by
        intro h; apply hb; rw [h]; simp
      simp [this]
    · simp

/-- A signed permutation matrix `P` is orthogonal, `P Pᵀ = 1`; hence `P^{-T} = P` is
again a signed permutation (the last step of `thm:learning-rigid`). -/
theorem signed_perm_orthogonal {k : ℕ} (σ : Equiv.Perm (Fin k)) (s : Fin k → ℤ)
    (hs : ∀ i, s i = 1 ∨ s i = -1) :
    (Matrix.of fun i j => if j = σ i then (s i : ℝ) else 0) *
      (Matrix.of fun i j => if j = σ i then (s i : ℝ) else 0).transpose = 1 := by
  ext i i'
  rw [Matrix.mul_apply]
  simp only [Matrix.transpose_apply, Matrix.of_apply]
  rw [Finset.sum_eq_single (σ i)]
  · simp only [if_true]
    by_cases h : i = i'
    · subst h; simp only [if_true, Matrix.one_apply_eq]
      rcases hs i with h1 | h1 <;> rw [h1] <;> norm_num
    · have : σ i ≠ σ i' := fun h' => h (σ.injective h')
      simp [this, Matrix.one_apply_ne h]
  · intro b _ hb; simp [hb]
  · simp

end QE.Learn

namespace QE.OpenSto.Learn

open QE.Learn

/-- **`thm:learning-sampling` in the printed form.**  `n ≥ 1` independent uniform
draws from a finite `C`; `q̂` the sample proportion of `A ⊆ C` and `q = #A/#C`:
`P(|q̂ - q| ≥ t) ≤ 2 e^{-n t²}` for `0 ≤ t ≤ 1/2`. -/
theorem chernoff_proportion {Z : Type*} [Fintype Z] [Nonempty Z] [DecidableEq Z]
    (A : Finset Z) (n : ℕ) (hn : 0 < n) (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1 / 2) :
    probS n (fun _ => 1 / (Fintype.card Z : ℝ))
      (fun ω => t ≤ |((Finset.univ.filter fun i => ω i ∈ A).card : ℝ) / n
        - (A.card : ℝ) / Fintype.card Z|) ≤ 2 * Real.exp (-(n * t ^ 2)) := by
  classical
  have hN : (0 : ℝ) < Fintype.card Z := by exact_mod_cast Fintype.card_pos
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  set f : Z → ℝ := fun z => if z ∈ A then 1 else 0
  have hq : ∀ z : Z, 0 ≤ 1 / (Fintype.card Z : ℝ) := fun _ => by positivity
  have hq1 : ∑ _z : Z, 1 / (Fintype.card Z : ℝ) = 1 := by
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; field_simp
  have hf : ∀ z, 0 ≤ f z ∧ f z ≤ 1 := by
    intro z; simp only [f]; split_ifs <;> norm_num
  have hμ : ∑ y, 1 / (Fintype.card Z : ℝ) * f y = (A.card : ℝ) / Fintype.card Z := by
    simp only [f, mul_ite, mul_one, mul_zero]
    rw [Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const, nsmul_eq_mul]; ring
  refine le_trans (probS_mono n _ hq _ _ ?_) (chernoff_two_sided _ hq hq1 f hf n t ht0 ht1)
  intro ω hω
  rw [hμ]
  have hsum : ∑ i, (f (ω i) - (A.card : ℝ) / Fintype.card Z)
      = n * (((Finset.univ.filter fun i => ω i ∈ A).card : ℝ) / n
        - (A.card : ℝ) / Fintype.card Z) := by
    rw [Finset.sum_sub_distrib]
    simp only [f]
    rw [Finset.sum_boole, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    field_simp
  rw [hsum, abs_mul, abs_of_pos hn']
  exact mul_le_mul_of_nonneg_left hω hn'.le

/-- The sample size of `thm:learning-sampling`: `n ≥ t^{-2} ln(2/δ)` gives
`2 e^{-n t²} ≤ δ`; in particular `n = ⌈t^{-2} ln(2/δ)⌉`. -/
theorem sample_size (t δ : ℝ) (ht : 0 < t) (hδ : 0 < δ) (n : ℕ)
    (hn : Real.log (2 / δ) / t ^ 2 ≤ n) : 2 * Real.exp (-(n * t ^ 2)) ≤ δ ∧
    2 * Real.exp (-(⌈Real.log (2 / δ) / t ^ 2⌉₊ * t ^ 2)) ≤ δ := by
  have key : ∀ m : ℕ, Real.log (2 / δ) / t ^ 2 ≤ m → 2 * Real.exp (-(m * t ^ 2)) ≤ δ := by
    intro m hm
    have ht2 : 0 < t ^ 2 := by positivity
    have h1 : Real.log (2 / δ) ≤ m * t ^ 2 := by rwa [div_le_iff₀ ht2] at hm
    have h2 : Real.exp (-(m * t ^ 2)) ≤ Real.exp (-Real.log (2 / δ)) :=
      Real.exp_le_exp.2 (by linarith)
    rw [Real.exp_neg (Real.log _), Real.exp_log (by positivity)] at h2
    have : (2 / δ)⁻¹ = δ / 2 := by field_simp
    rw [this] at h2
    linarith
  exact ⟨key n hn, key _ (Nat.le_ceil _)⟩

/-- **`thm:learning-cancel` without the positivity hypothesis.**  With Lean's
convention `a / 0 = 0` the bound also holds when `Σ cᵢ² xᵢ² = 0` (it then reads
`#{…} ≤ #cell`). -/
theorem cell_tail_any {N : ℕ} (R : Fin N → Finset ℝ) (μ c : Fin N → ℝ)
    (hsym : ∀ i, ∀ y ∈ R i, 2 * μ i - y ∈ R i) (hc : ∀ i, ∀ y ∈ R i, |y - μ i| ≤ c i)
    (x : Fin N → ℝ) (t : ℝ) (ht : 0 ≤ t) :
    (((cell R).filter fun e => t ≤ ∑ i, x i * (e i - μ i)).card : ℝ) ≤
      (∏ i, ((R i).card : ℝ)) * Real.exp (-(t ^ 2 / (2 * ∑ i, c i ^ 2 * x i ^ 2))) := by
  classical
  have hV : 0 ≤ ∑ i, c i ^ 2 * x i ^ 2 := Finset.sum_nonneg fun i _ => by positivity
  rcases hV.lt_or_eq with hpos | h0
  · exact cell_tail R μ c hsym hc x t ht hpos
  · rw [← h0, mul_zero, div_zero, neg_zero, Real.exp_zero, mul_one]
    have := Finset.card_filter_le (cell R) fun e => t ≤ ∑ i, x i * (e i - μ i)
    rw [card_cell] at this
    exact_mod_cast this

/-- **`thm:learning-cancel`, two-sided form.**  If `0 ≤ cᵢ ≤ c'ᵢ` (e.g. `c'ᵢ = ε'ᵢ`),
`Σ cᵢ²xᵢ² > 0` and `λ ≥ 0`, the number of points of the cell at which
`|Σ xᵢ(eᵢ - μᵢ)| ≥ λ (Σ c'ᵢ² xᵢ²)^{1/2}` is at most `2 #cell e^{-λ²/2}`. -/
theorem cell_two_sided {N : ℕ} (R : Fin N → Finset ℝ) (μ c c' : Fin N → ℝ)
    (hsym : ∀ i, ∀ y ∈ R i, 2 * μ i - y ∈ R i) (hc : ∀ i, ∀ y ∈ R i, |y - μ i| ≤ c i)
    (hc0 : ∀ i, 0 ≤ c i) (hcc : ∀ i, c i ≤ c' i)
    (x : Fin N → ℝ) (hpos : 0 < ∑ i, c i ^ 2 * x i ^ 2) (lam : ℝ) (hlam : 0 ≤ lam) :
    (((cell R).filter fun e =>
        lam * Real.sqrt (∑ i, c' i ^ 2 * x i ^ 2) ≤ |∑ i, x i * (e i - μ i)|).card : ℝ) ≤
      2 * (∏ i, ((R i).card : ℝ)) * Real.exp (-(lam ^ 2 / 2)) := by
  classical
  set V := ∑ i, c i ^ 2 * x i ^ 2
  set W := ∑ i, c' i ^ 2 * x i ^ 2
  have hVW : V ≤ W := Finset.sum_le_sum fun i _ => by
    have : c i ^ 2 ≤ c' i ^ 2 := pow_le_pow_left₀ (hc0 i) (hcc i) 2
    exact mul_le_mul_of_nonneg_right this (sq_nonneg _)
  have hW : 0 ≤ W := le_trans hpos.le hVW
  set t := lam * Real.sqrt W
  have ht : 0 ≤ t := by positivity
  have hexp : Real.exp (-(t ^ 2 / (2 * V))) ≤ Real.exp (-(lam ^ 2 / 2)) := by
    apply Real.exp_le_exp.2
    have ht2 : t ^ 2 = lam ^ 2 * W := by
      simp only [t]; rw [mul_pow, Real.sq_sqrt hW]
    rw [ht2, neg_le_neg_iff, le_div_iff₀ (by positivity)]
    nlinarith [sq_nonneg lam]
  have hneg : ∑ i, c i ^ 2 * (-x i) ^ 2 = V := by simp only [neg_sq]; rfl
  have h1 := cell_tail R μ c hsym hc x t ht hpos
  have h2 := cell_tail R μ c hsym hc (fun i => -x i) t ht (by rw [hneg]; exact hpos)
  rw [hneg] at h2
  have hsub : ((cell R).filter fun e => t ≤ |∑ i, x i * (e i - μ i)|) ⊆
      ((cell R).filter fun e => t ≤ ∑ i, x i * (e i - μ i)) ∪
      ((cell R).filter fun e => t ≤ ∑ i, (-x i) * (e i - μ i)) := by
    intro e he
    rw [Finset.mem_filter] at he
    rw [Finset.mem_union, Finset.mem_filter, Finset.mem_filter]
    rcases le_abs'.1 he.2 with h | h
    · right; refine ⟨he.1, ?_⟩
      simp only [neg_mul, Finset.sum_neg_distrib]; linarith
    · left; exact ⟨he.1, h⟩
  have hcard := (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
  have hcard' : (((cell R).filter fun e => t ≤ |∑ i, x i * (e i - μ i)|).card : ℝ) ≤
      (((cell R).filter fun e => t ≤ ∑ i, x i * (e i - μ i)).card : ℝ) +
      (((cell R).filter fun e => t ≤ ∑ i, (-x i) * (e i - μ i)).card : ℝ) := by
    exact_mod_cast hcard
  have hP : 0 ≤ ∏ i, ((R i).card : ℝ) := Finset.prod_nonneg fun i _ => by positivity
  have := mul_le_mul_of_nonneg_left hexp hP
  linarith

end QE.OpenSto.Learn

/-! ## Physics -/

namespace QE.Phys

open Real

/-- **`prop:phys-first-law` with the derivative machine-checked.**  For
`S(M) = k_B A(M)/(4ℓ_P²)`, `A(M) = 16π G² M²/c⁴`, `ℓ_P² = ħG/c³`, the derivative
`dS/dM` at `M` is `k_B (32π G² M/c⁴)/(4ℓ_P²)`, and `T_H · dS/dM = c²`. -/
theorem first_law_deriv (ħ G c k M : ℝ) (hħ : 0 < ħ) (hG : 0 < G) (hc : 0 < c) (hk : 0 < k)
    (hM : 0 < M) :
    HasDerivAt (fun m : ℝ => k * (16 * π * G ^ 2 * m ^ 2 / c ^ 4) / (4 * (ħ * G / c ^ 3)))
      (k * (32 * π * G ^ 2 * M / c ^ 4) / (4 * (ħ * G / c ^ 3))) M ∧
    (ħ * c ^ 3 / (8 * π * G * M * k)) *
      deriv (fun m : ℝ => k * (16 * π * G ^ 2 * m ^ 2 / c ^ 4) / (4 * (ħ * G / c ^ 3))) M
      = c ^ 2 := by
  set C := k * (16 * π * G ^ 2 / c ^ 4) / (4 * (ħ * G / c ^ 3))
  have e1 : (fun m : ℝ => k * (16 * π * G ^ 2 * m ^ 2 / c ^ 4) / (4 * (ħ * G / c ^ 3)))
      = fun m => C * m ^ 2 := by funext m; simp only [C]; ring
  have hd : HasDerivAt (fun m : ℝ => k * (16 * π * G ^ 2 * m ^ 2 / c ^ 4) / (4 * (ħ * G / c ^ 3)))
      (k * (32 * π * G ^ 2 * M / c ^ 4) / (4 * (ħ * G / c ^ 3))) M := by
    rw [e1]
    have h := (hasDerivAt_pow 2 M).const_mul C
    convert h using 1
    simp only [C]; push_cast; ring
  exact ⟨hd, by rw [hd.deriv]; exact first_law ħ G c k M hħ hG hc hk hM⟩

end QE.Phys
