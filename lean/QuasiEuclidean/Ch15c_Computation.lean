-- SPDX-License-Identifier: MIT
-- Copyright 2026 Metere Industries, Inc. Author: Alfredo Metere.
-- Quasi-Euclidean Granular Geometry. Any derivative work must carry this notice:
--   This work is derivative of the Quasi-Euclidean Granular Geometry book
--   authored by Alfredo Metere. Copyright 2026 Metere Industries, Inc.
--   All rights reserved
-- See LICENSE.md and NOTICE.

import QuasiEuclidean.Basic
import QuasiEuclidean.Ch15_Dyn
import QuasiEuclidean.NSA_Internal
import Mathlib.LinearAlgebra.Matrix.Permanent

/-!
# Chapter 19: Computation — search as dynamics

Exact finitary statements about computation at the resolution of a granule.

* **Branching and entropy.**  A nondeterministic computation of depth `n` over
  binary choices has `2^n` itineraries; its entropy per step is `log 2`.  A
  deterministic trajectory is unique, so its entropy is `0`.
* **Branches are cells.**  The `2^n` itineraries are the `2^n` cells of the
  dyadic lattice at level `n`, and the itinerary of a cell is read off by the
  doubling map (symbolic dynamics, Chapter 17).  So the whole computation tree
  is one deterministic chaotic flow acting on the lattice.
* **Chaos: closed form, random source, and the ensemble beyond the data.**  The
  `t`-th iterate of the doubling map has a closed form (the linear case); a
  uniformly random seed gives uniform overflow bits; the seeds consistent with
  `t` bits of data split evenly on the next symbol, so prediction beyond the
  horizon is a search with one bit of branching per step.
* **Exact chaos in the two domains.**  `t` exact rational steps of the logistic map
  from `p/q` in lowest terms give denominator `q^(2^t)`: the exact description
  doubles every step (classical domain); on the lattice the state is `K` bits.
* **The classical iterate grows.**  The `T`-th iterate of the logistic polynomial has
  degree `2^T` (`logistic_iterate_natDegree`): the exact classical formula for `f^T`
  grows exponentially, while on the lattice `f^T` loses outputs.
* **Trace.**  One step of the doubling map loses one bit (the overflow); keeping
  the trace makes the step reversible; a trajectory of `n` steps has a trace of
  `n` bits.
* **Search.**  Decision trees querying a black-box verifier: deciding whether
  some branch accepts costs exactly `2^n` queries in the worst case (lower
  bound by an adversary, upper bound by exhaustive search), finding the unique
  accepting branch costs `≥ 2^n - 1`; a sampler of `q` queries detects at most
  `q` of the `2^n` possible witnesses.  Padding shows that the apparent cost
  can be inflated at will while the minimum, the *real entropy*, is invariant.
* **Structure collapses entropy.**  For a monotone (threshold) verifier binary
  search finds the witness in `n` queries, against `2^n - 1` without structure.
* **Clauses.**  A clause of width `k` excludes exactly one of its `2^k` local
  assignments, so it carries `log₂(2^k/(2^k-1)) → 0` bits; Schöning's base
  `2(k-1)/k` for `k`-SAT increases to `2`, the naive cost.
* **Reals are words.**  `N` lattice cells embed in `⌈log₂ N⌉` bits.
* **Conservativity.**  Every sentence of the full real language, hence every
  arithmetic sentence such as `P ≠ NP`, has the same truth value in `ℝ*` and in
  `ℝ`: the granule leaves the question where ZFC leaves it.
-/

open Finset Function

namespace QE.Comp

/-! ## Branching and trajectories -/

/-- The itineraries of a nondeterministic computation of depth `n` over binary
choices: one bit per step. -/
abbrev Itin (n : ℕ) := Fin n → Bool

theorem card_itin (n : ℕ) : Fintype.card (Itin n) = 2 ^ n := by
  simp [Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]

/-- A deterministic trajectory of length `t` from `s`: a sequence following `f`. -/
def IsTraj {S : Type*} (f : S → S) (s : S) (t : ℕ) (w : Fin (t + 1) → S) : Prop :=
  w 0 = s ∧ ∀ i : Fin t, w i.succ = f (w i.castSucc)

/-- **Determinism.** There is exactly one trajectory of each length from each
start: the iterates of `f`. -/
theorem traj_unique {S : Type*} (f : S → S) (s : S) (t : ℕ) (w : Fin (t + 1) → S)
    (hw : IsTraj f s t w) : ∀ i : Fin (t + 1), w i = f^[i] s := by
  intro i
  obtain ⟨i, hi⟩ := i
  induction i with
  | zero => simpa using hw.1
  | succ j ih =>
    have hj : j < t := by omega
    have := hw.2 ⟨j, hj⟩
    simp only [Fin.succ_mk, Fin.castSucc_mk] at this
    rw [this, ih (by omega), iterate_succ_apply']

theorem traj_exists {S : Type*} (f : S → S) (s : S) (t : ℕ) :
    IsTraj f s t (fun i : Fin (t + 1) => f^[i] s) := by
  refine ⟨by simp, fun i => ?_⟩
  simp [iterate_succ_apply']

/-- The number of trajectories of length `t` from `s` is `1`. -/
theorem card_traj {S : Type*} (f : S → S) (s : S) (t : ℕ) :
    Nat.card {w : Fin (t + 1) → S // IsTraj f s t w} = 1 := by
  rw [Nat.card_eq_one_iff_unique]
  refine ⟨⟨fun u v => Subtype.ext (funext fun i => ?_)⟩, ⟨⟨_, traj_exists f s t⟩⟩⟩
  rw [traj_unique f s t u u.2 i, traj_unique f s t v v.2 i]

/-- Entropy per step of the branching: `log(#itineraries)/n`. -/
noncomputable def branchEntropy (n : ℕ) : ℝ := Real.log (Fintype.card (Itin n)) / n

/-- **One bit per guess.** The branching entropy of binary nondeterminism is `log 2`. -/
theorem branchEntropy_eq (n : ℕ) (hn : 0 < n) : branchEntropy n = Real.log 2 := by
  unfold branchEntropy
  rw [card_itin, Nat.cast_pow, Real.log_pow]
  have : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  field_simp
  norm_num

/-- Entropy per step of a deterministic trajectory: `log 1 / t = 0`. -/
theorem trajEntropy_eq_zero {S : Type*} (f : S → S) (s : S) (t : ℕ) :
    Real.log (Nat.card {w : Fin (t + 1) → S // IsTraj f s t w}) / t = 0 := by
  rw [card_traj]; simp

/-! ## Branches are the cells of the lattice: the doubling map as the search tree -/

/-- The bit string of a cell `k < 2^n`: its binary digits from the top. -/
def code (n : ℕ) (k : ℕ) : Itin n := fun i => k.testBit (n - 1 - i)

theorem code_injOn (n : ℕ) : Set.InjOn (code n) (Set.Iio (2 ^ n)) := by
  intro a ha b hb hab
  apply Nat.eq_of_testBit_eq
  intro j
  by_cases hj : j < n
  · have := congrFun hab ⟨n - 1 - j, by omega⟩
    simpa [code, show n - 1 - (n - 1 - j) = j by omega] using this
  · have ha' : a.testBit j = false := Nat.testBit_lt_two_pow (lt_of_lt_of_le ha (Nat.pow_le_pow_right (by norm_num) (by omega)))
    have hb' : b.testBit j = false := Nat.testBit_lt_two_pow (lt_of_lt_of_le hb (Nat.pow_le_pow_right (by norm_num) (by omega)))
    rw [ha', hb']

/-- The cells of the lattice at level `n`, coded as bit strings. -/
def cellCode (n : ℕ) : Fin (2 ^ n) → Itin n := fun k => code n k

/-- **Branches are cells.** The coding `Fin (2^n) → (Fin n → Bool)` is a bijection:
the `2^n` itineraries of depth `n` are exactly the `2^n` cells. -/
theorem cellCode_bijective (n : ℕ) : Bijective (cellCode n) := by
  rw [Fintype.bijective_iff_injective_and_card]
  refine ⟨fun a b h => Fin.ext (code_injOn n a.2 b.2 h), ?_⟩
  simp [card_itin]

/-- The coding as an equivalence. -/
noncomputable def cellEquiv (n : ℕ) : Fin (2 ^ n) ≃ Itin n := Equiv.ofBijective _ (cellCode_bijective n)

/-- **The doubling map reads the branch.** The symbol observed at time `i` on the
orbit of cell `k` under the doubling map of level `n` (which half of `[0,1)` the
state is in) is the `i`-th bit of the code of `k`. So the computation tree is
the symbolic dynamics of one chaotic map. -/
theorem dbl_reads_code (n : ℕ) (k : ℕ) (hk : k < 2 ^ n) (i : Fin n) :
    ((QE.Dyn.dbl n)^[i] k / 2 ^ (n - 1) = 1) ↔ code n k i = true := by
  rw [QE.Dyn.dbl_symbol n i k i.2 hk, code, Nat.testBit_eq_decide_div_mod_eq]
  simp

/-- **NP as ensemble dynamics.** Some branch accepts iff some cell of the lattice,
run through the doubling map, produces an accepting itinerary. -/
theorem exists_branch_iff_cell (n : ℕ) (V : Itin n → Bool) :
    (∃ w, V w = true) ↔ ∃ k : Fin (2 ^ n), V (cellCode n k) = true := by
  constructor
  · rintro ⟨w, hw⟩
    obtain ⟨k, rfl⟩ := (cellCode_bijective n).2 w
    exact ⟨k, hw⟩
  · rintro ⟨k, hk⟩; exact ⟨_, hk⟩

/-- The accepting set has the same cardinality on branches and on cells: the
granular measure of the accepting set is `#accepting / 2^n`, exactly. -/
theorem card_accepting_cells (n : ℕ) (V : Itin n → Bool) :
    (univ.filter fun k : Fin (2 ^ n) => V (cellCode n k) = true).card =
      (univ.filter fun w : Itin n => V w = true).card := by
  rw [← Finset.card_image_of_injective _ (cellCode_bijective n).1]
  congr 1
  ext w
  simp only [mem_image, mem_filter, mem_univ, true_and]
  constructor
  · rintro ⟨k, hk, rfl⟩; exact hk
  · intro hw
    obtain ⟨k, rfl⟩ := (cellCode_bijective n).2 w
    exact ⟨k, hw, rfl⟩

/-- A unique witness is one cell in `2^n`: granular measure `1/2^n`, not zero. -/
theorem unique_witness_measure (n : ℕ) (w₀ : Itin n) :
    ((univ.filter fun k : Fin (2 ^ n) => (decide (cellCode n k = w₀)) = true).card : ℝ) /
      2 ^ n = 1 / 2 ^ n := by
  have : (univ.filter fun k : Fin (2 ^ n) => (decide (cellCode n k = w₀)) = true) =
      {(cellEquiv n).symm w₀} := by
    ext k
    simp only [mem_filter, mem_univ, true_and, decide_eq_true_eq, mem_singleton,
      Equiv.eq_symm_apply]
    rfl
  rw [this, card_singleton]; simp

/-! ## Chaos: closed form, random source, and the ensemble beyond the data -/

/-- **Closed form.** The `t`-th iterate of the doubling map is `2^t k mod 2^K`: a
chaotic trajectory is computed in one step, not followed. -/
theorem chaos_closed_form (K t k : ℕ) (hk : k < 2 ^ K) :
    (QE.Dyn.dbl K)^[t] k = (2 ^ t * k) % 2 ^ K :=
  QE.Dyn.dbl_iterate K t k hk

/-- **Uniform overflow.** For a uniformly random seed on the lattice of level `K`,
each pattern of the first `t ≤ K` overflow bits has exactly `2^(K-t)` seeds: the
overflow sequence is a sequence of fair, independent bits. -/
theorem overflow_uniform (K t y : ℕ) (ht : t ≤ K) (hy : y < 2 ^ t) :
    ((range (2 ^ K)).filter fun k => k / 2 ^ (K - t) = y).card = 2 ^ (K - t) := by
  have hP : 2 ^ K = 2 ^ t * 2 ^ (K - t) := by rw [← pow_add]; congr 1; omega
  have hpos : 0 < 2 ^ (K - t) := by positivity
  have : (range (2 ^ K)).filter (fun k => k / 2 ^ (K - t) = y) =
      (range (2 ^ (K - t))).map ⟨fun r => y * 2 ^ (K - t) + r, add_right_injective _⟩ := by
    ext k
    simp only [mem_filter, mem_range, mem_map, Function.Embedding.coeFn_mk]
    constructor
    · rintro ⟨hk, hd⟩
      refine ⟨k % 2 ^ (K - t), Nat.mod_lt _ hpos, ?_⟩
      show y * 2 ^ (K - t) + k % 2 ^ (K - t) = k
      rw [← hd, Nat.div_add_mod']
    · rintro ⟨r, hr, rfl⟩
      refine ⟨?_, ?_⟩
      · show y * 2 ^ (K - t) + r < 2 ^ K
        rw [hP]
        calc y * 2 ^ (K - t) + r < y * 2 ^ (K - t) + 2 ^ (K - t) := by omega
          _ = (y + 1) * 2 ^ (K - t) := by ring
          _ ≤ 2 ^ t * 2 ^ (K - t) := Nat.mul_le_mul_right _ hy
      · show (y * 2 ^ (K - t) + r) / 2 ^ (K - t) = y
        rw [Nat.add_comm, Nat.add_mul_div_right _ _ hpos, Nat.div_eq_of_lt hr, zero_add]
  rw [this, card_map, card_range]

/-- **Prediction needs the bits.** Fix the first `t < K` bits of the seed (the data).
Among the `2^(K-t)` seeds consistent with them, exactly half produce each value of
the symbol at time `t`: the next symbol is undetermined by the data, and the
consistent seeds branch. Prediction beyond the data is a search over this
ensemble, with one bit of branching per step. -/
theorem prediction_branches (K t y : ℕ) (ht : t < K) (hy : y < 2 ^ t) (b : ℕ) (hb : b < 2) :
    ((range (2 ^ K)).filter fun k =>
      k / 2 ^ (K - t) = y ∧ (QE.Dyn.dbl K)^[t] k / 2 ^ (K - 1) = b).card = 2 ^ (K - t - 1) := by
  have h1 : t + 1 ≤ K := ht
  have hy' : 2 * y + b < 2 ^ (t + 1) := by rw [pow_succ]; omega
  have key := overflow_uniform K (t + 1) (2 * y + b) h1 hy'
  have hK : K - (t + 1) = K - t - 1 := by omega
  rw [hK] at key
  rw [← key]
  congr 1
  apply Finset.filter_congr
  intro k hk
  rw [mem_range] at hk
  rw [QE.Dyn.dbl_symbol K t k ht hk]
  have e1 : K - t = (K - t - 1) + 1 := by omega
  have e2 : K - 1 - t = K - t - 1 := by omega
  rw [e2]
  constructor
  · rintro ⟨h1, h2⟩
    rw [e1, pow_succ, ← Nat.div_div_eq_div_mul] at h1
    have := Nat.div_add_mod (k / 2 ^ (K - t - 1)) 2
    omega
  · intro h
    refine ⟨?_, ?_⟩
    · rw [e1, pow_succ, ← Nat.div_div_eq_div_mul, h]; omega
    · rw [h]; omega

/-! ## Exact evolution in the two domains -/

/-- One exact step of the logistic map `x ↦ 4x(1-x)` on a fraction `p/q`, kept as a
pair of naturals: `(p, q) ↦ (4p(q-p), q²)`. -/
def logisticStep (pq : ℕ × ℕ) : ℕ × ℕ := (4 * pq.1 * (pq.2 - pq.1), pq.2 ^ 2)

/-- An exact rational state in lowest terms: `0 < p < q`, `q` odd, `p` coprime to `q`. -/
def ExactState (pq : ℕ × ℕ) : Prop :=
  0 < pq.1 ∧ pq.1 < pq.2 ∧ Odd pq.2 ∧ Nat.Coprime pq.1 pq.2

theorem exactState_third : ExactState (1, 3) :=
  ⟨by norm_num, by norm_num, ⟨1, rfl⟩, Nat.coprime_one_left 3⟩

/-- The exact step preserves lowest terms, so the new denominator is exactly `q²`. -/
theorem logisticStep_exact (pq : ℕ × ℕ) (h : ExactState pq) : ExactState (logisticStep pq) := by
  obtain ⟨p, q⟩ := pq
  obtain ⟨hp, hpq, hodd, hcop⟩ := h
  simp only [ExactState, logisticStep] at *
  have hq2 : 2 ≤ q := by omega
  refine ⟨?_, ?_, hodd.pow, ?_⟩
  · exact Nat.mul_pos (Nat.mul_pos (by norm_num) hp) (Nat.sub_pos_of_lt hpq)
  · -- `4p(q-p) < q²` since `q² - 4p(q-p) = (q-2p)² ≥ 1`, `q` being odd
    have hne : (q : ℤ) - 2 * p ≠ 0 := by
      intro h0
      have : (q : ℤ) = 2 * p := by linarith
      have h2 : Even q := ⟨p, by exact_mod_cast (by linarith : (q:ℤ) = p + p)⟩
      exact (Nat.not_even_iff_odd.mpr hodd) h2
    have h1 : 1 ≤ |(q : ℤ) - 2 * p| := Int.one_le_abs hne
    have h2 : 1 ≤ ((q : ℤ) - 2 * p) ^ 2 := by
      rw [← sq_abs]; nlinarith [abs_nonneg ((q : ℤ) - 2 * p)]
    zify [hpq.le]
    nlinarith
  · have h4 : Nat.Coprime 4 q := by
      have h := Nat.Coprime.pow_left 2 (Nat.coprime_two_left.mpr hodd)
      rwa [show (2:ℕ) ^ 2 = 4 by norm_num] at h
    have hqp : Nat.Coprime (q - p) q := (Nat.coprime_self_sub_left hpq.le).mpr hcop
    exact Nat.Coprime.pow_right 2 (Nat.Coprime.mul_left (Nat.Coprime.mul_left h4 hcop) hqp)

/-- **Exact chaos needs new symbols at every step.** From a lowest-terms state `p/q`,
`t` exact steps of the logistic map give a lowest-terms state whose denominator is
`q^(2^t)`: the description of the exact state grows by a factor `2` per step, and
after `t` steps it has at least `2^t` bits. -/
theorem logistic_exact_cost (pq : ℕ × ℕ) (h : ExactState pq) (t : ℕ) :
    ExactState ((logisticStep)^[t] pq) ∧ ((logisticStep)^[t] pq).2 = pq.2 ^ (2 ^ t) ∧
      2 ^ (2 ^ t) ≤ ((logisticStep)^[t] pq).2 := by
  have hq2 : 2 ≤ pq.2 := by obtain ⟨hp, hpq, -, -⟩ := h; omega
  have main : ∀ t : ℕ, ExactState ((logisticStep)^[t] pq) ∧
      ((logisticStep)^[t] pq).2 = pq.2 ^ (2 ^ t) := by
    intro t
    induction t with
    | zero => exact ⟨by simpa using h, by simp⟩
    | succ t ih =>
      obtain ⟨ih1, ih2⟩ := ih
      rw [iterate_succ_apply']
      refine ⟨logisticStep_exact _ ih1, ?_⟩
      show ((logisticStep)^[t] pq).2 ^ 2 = pq.2 ^ 2 ^ (t + 1)
      rw [ih2, ← pow_mul, pow_succ]
  obtain ⟨h1, h2⟩ := main t
  refine ⟨h1, h2, ?_⟩
  rw [h2]
  exact Nat.pow_le_pow_left hq2 _

/-- The logistic polynomial `4x(1-x) = 4x - 4x²` over `ℚ`. -/
noncomputable def logisticPoly : Polynomial ℚ := 4 * Polynomial.X - 4 * Polynomial.X ^ 2

theorem logisticPoly_natDegree : logisticPoly.natDegree = 2 := by
  unfold logisticPoly; compute_degree!

/-- **The classical iterate grows exponentially.** The `T`-th iterate of the logistic
map, as a polynomial, has degree exactly `2^T`: its exact classical formula has
`2^T + 1` coefficients. On the lattice the same iterate is a map on `2^K` states
whose minimal description shrinks (the companion script measures it). -/
theorem logistic_iterate_natDegree (T : ℕ) :
    ((logisticPoly.comp)^[T] Polynomial.X).natDegree = 2 ^ T := by
  rw [Polynomial.natDegree_iterate_comp, logisticPoly_natDegree, Polynomial.natDegree_X, mul_one]

/-! ## The trace: overflow, loss and reversibility -/

/-- **One bit lost per step.** The image of the lattice of level `K ≥ 1` under one
step of the doubling map has `2^(K-1)` elements: half the states, one bit. -/
theorem dbl_image_card (K : ℕ) (hK : 1 ≤ K) :
    ((range (2 ^ K)).image (QE.Dyn.dbl K)).card = 2 ^ (K - 1) := by
  have h2 : 2 ^ K = 2 * 2 ^ (K - 1) := by rw [← pow_succ']; congr 1; omega
  have : (range (2 ^ K)).image (QE.Dyn.dbl K) = (range (2 ^ (K - 1))).image (fun m => 2 * m) := by
    ext y
    simp only [mem_image, mem_range]
    constructor
    · rintro ⟨k, hk, rfl⟩
      exact ⟨k % 2 ^ (K - 1), Nat.mod_lt _ (by positivity), (QE.Dyn.dbl_bit_shift K k hK).symm⟩
    · rintro ⟨m, hm, rfl⟩
      refine ⟨m, by rw [h2]; omega, ?_⟩
      rw [QE.Dyn.dbl_bit_shift K m hK, Nat.mod_eq_of_lt hm]
  rw [this, card_image_of_injective _ (fun a b h => by simpa using h), card_range]

/-- The step with its trace: the state advances by the doubling map and the
overflow bit is appended to the trace. -/
def traced (K : ℕ) (p : ℕ × ℕ) : ℕ × ℕ := (QE.Dyn.dbl K p.1, 2 * p.2 + p.1 / 2 ^ (K - 1))

/-- **Keeping the overflow makes the step reversible.** The traced step is injective
on the lattice: the lost bit is recovered from the trace. -/
theorem traced_injOn (K : ℕ) (hK : 1 ≤ K) :
    Set.InjOn (traced K) {p : ℕ × ℕ | p.1 < 2 ^ K} := by
  rintro ⟨a, s⟩ ha ⟨b, t⟩ hb h
  simp only [traced, Prod.mk.injEq] at h
  obtain ⟨h1, h2⟩ := h
  have ha' : a < 2 ^ K := ha
  have hb' : b < 2 ^ K := hb
  have h2K : 2 ^ K = 2 * 2 ^ (K - 1) := by rw [← pow_succ']; congr 1; omega
  have ta : a / 2 ^ (K - 1) < 2 := by rw [Nat.div_lt_iff_lt_mul (by positivity)]; omega
  have tb : b / 2 ^ (K - 1) < 2 := by rw [Nat.div_lt_iff_lt_mul (by positivity)]; omega
  rw [QE.Dyn.dbl_bit_shift K a hK, QE.Dyn.dbl_bit_shift K b hK] at h1
  have key : ∀ (s t x y : ℕ), x < 2 → y < 2 → 2 * s + x = 2 * t + y → s = t ∧ x = y := by
    intros; omega
  obtain ⟨hs, htop⟩ := key _ _ _ _ ta tb h2
  have hlow : a % 2 ^ (K - 1) = b % 2 ^ (K - 1) :=
    Nat.eq_of_mul_eq_mul_left (by norm_num) h1
  have ea := Nat.div_add_mod a (2 ^ (K - 1))
  have eb := Nat.div_add_mod b (2 ^ (K - 1))
  have eab : 2 ^ (K - 1) * (a / 2 ^ (K - 1)) + a % 2 ^ (K - 1) =
      2 ^ (K - 1) * (b / 2 ^ (K - 1)) + b % 2 ^ (K - 1) :=
    congrArg₂ (fun x y => 2 ^ (K - 1) * x + y) htop hlow
  exact Prod.ext (ea.symm.trans (eab.trans eb)) hs

/-- The traced step keeps the state on the lattice and adds at most one bit to
the trace. -/
theorem traced_iterate_bound (K : ℕ) (hK : 1 ≤ K) (n : ℕ) (p : ℕ × ℕ) (hp : p.1 < 2 ^ K) :
    ((traced K)^[n] p).1 < 2 ^ K ∧ ((traced K)^[n] p).2 < 2 ^ n * (p.2 + 1) := by
  induction n generalizing p with
  | zero => simpa using hp
  | succ n ih =>
    rw [iterate_succ_apply]
    have h2K : 2 ^ K = 2 * 2 ^ (K - 1) := by rw [← pow_succ']; congr 1; omega
    have htop : p.1 / 2 ^ (K - 1) < 2 := by
      rw [Nat.div_lt_iff_lt_mul (by positivity)]; omega
    have hdbl : QE.Dyn.dbl K p.1 < 2 ^ K := Nat.mod_lt _ (by positivity)
    obtain ⟨h1, h2⟩ := ih (traced K p) hdbl
    refine ⟨h1, lt_of_lt_of_le h2 ?_⟩
    simp only [traced]
    calc 2 ^ n * (2 * p.2 + p.1 / 2 ^ (K - 1) + 1) ≤ 2 ^ n * (2 * (p.2 + 1)) :=
          Nat.mul_le_mul_left _ (by omega)
      _ = 2 ^ (n + 1) * (p.2 + 1) := by ring

/-- **The trace has one bit per step.** After `n` steps from a trace-free start on the
lattice, the trace is a number below `2^n`. -/
theorem trace_bits (K : ℕ) (hK : 1 ≤ K) (n k : ℕ) (hk : k < 2 ^ K) :
    ((traced K)^[n] (k, 0)).2 < 2 ^ n := by
  simpa using (traced_iterate_bound K hK n (k, 0) hk).2

/-! ## Search: decision trees over a black-box verifier -/

/-- A decision tree querying an oracle `α → Bool` and returning a `β`. -/
inductive DTree (α β : Type*) : Type _
  | leaf : β → DTree α β
  | node : α → DTree α β → DTree α β → DTree α β

namespace DTree

variable {α β : Type*}

/-- Run the tree against an oracle. -/
def eval : DTree α β → (α → Bool) → β
  | leaf b, _ => b
  | node q t0 t1, V => if V q then t1.eval V else t0.eval V

/-- Worst-case number of queries. -/
def depth : DTree α β → ℕ
  | leaf _ => 0
  | node _ t0 t1 => max t0.depth t1.depth + 1

/-- The queries asked along the path on which every answer is `false`. -/
def falsePath [DecidableEq α] : DTree α β → Finset α
  | leaf _ => ∅
  | node q t0 _ => insert q t0.falsePath

theorem falsePath_card_le_depth [DecidableEq α] (t : DTree α β) :
    t.falsePath.card ≤ t.depth := by
  induction t with
  | leaf b => simp [falsePath, depth]
  | node q t0 t1 ih0 ih1 =>
    simp only [falsePath, depth]
    calc (insert q t0.falsePath).card ≤ t0.falsePath.card + 1 := card_insert_le _ _
      _ ≤ max t0.depth t1.depth + 1 := by
          have := le_max_left t0.depth t1.depth; omega

/-- **The adversary.** An oracle that answers `false` on every query of the false
path is indistinguishable from the constant `false` oracle. -/
theorem eval_eq_of_false_on_path [DecidableEq α] (t : DTree α β) (V : α → Bool)
    (h : ∀ q ∈ t.falsePath, V q = false) : t.eval V = t.eval (fun _ => false) := by
  induction t with
  | leaf b => rfl
  | node q t0 t1 ih0 ih1 =>
    have hq : V q = false := h q (by simp [falsePath])
    simp only [eval, hq, Bool.false_eq_true, ↓reduceIte]
    exact ih0 (fun r hr => h r (by simp [falsePath, hr]))

/-- Padding: ask a useless question `m` more times. -/
def pad (t : DTree α β) (q : α) : ℕ → DTree α β
  | 0 => t
  | m + 1 => node q (pad t q m) (pad t q m)

theorem pad_eval (t : DTree α β) (q : α) (m : ℕ) (V : α → Bool) :
    (pad t q m).eval V = t.eval V := by
  induction m with
  | zero => rfl
  | succ m ih => simp only [pad, eval, ih]; split_ifs <;> rfl

theorem pad_depth (t : DTree α β) (q : α) (m : ℕ) : (pad t q m).depth = t.depth + m := by
  induction m with
  | zero => rfl
  | succ m ih => simp only [pad, depth, ih, max_self]; ring

/-- Exhaustive search over a list of candidates. -/
def bruteForce : List α → DTree α Bool
  | [] => leaf false
  | q :: l => node q (bruteForce l) (leaf true)

theorem bruteForce_eval (l : List α) (V : α → Bool) :
    (bruteForce l).eval V = decide (∃ q ∈ l, V q = true) := by
  induction l with
  | nil => simp [bruteForce, eval]
  | cons q l ih =>
    simp only [bruteForce, eval, ih, List.mem_cons]
    by_cases hq : V q = true
    · simp [hq]
    · simp [hq]

theorem bruteForce_depth (l : List α) : (bruteForce l).depth = l.length := by
  induction l with
  | nil => rfl
  | cons q l ih => simp [bruteForce, depth, ih]

end DTree

open DTree

variable {n : ℕ}

/-- A tree decides black-box search of depth `n` if, for every verifier, it answers
whether some branch is accepted. -/
def Decides (t : DTree (Itin n) Bool) : Prop := ∀ V : Itin n → Bool, t.eval V = decide (∃ w, V w = true)

/-- **Black-box lower bound.** Deciding whether some branch accepts costs `2^n`
queries in the worst case: the ensemble must be carried. -/
theorem decide_lower_bound (t : DTree (Itin n) Bool) (ht : Decides t) : 2 ^ n ≤ t.depth := by
  by_contra hlt
  push_neg at hlt
  have hcard : t.falsePath.card < (univ : Finset (Itin n)).card := by
    rw [card_univ, card_itin]; exact lt_of_le_of_lt (falsePath_card_le_depth t) hlt
  obtain ⟨w, -, hw⟩ := exists_mem_notMem_of_card_lt_card hcard
  have h1 := ht (fun v => decide (v = w))
  have h2 := eval_eq_of_false_on_path t (fun v => decide (v = w))
    (fun q hq => by simp only [decide_eq_false_iff_not]; rintro rfl; exact hw hq)
  have h3 := ht (fun _ => false)
  simp only [decide_eq_true_eq, exists_eq, decide_true] at h1
  simp only [Bool.false_eq_true, exists_const, decide_false] at h3
  rw [h2, h3] at h1
  exact Bool.false_ne_true h1

/-- Exhaustive search over all `2^n` branches. -/
noncomputable def exhaustive (n : ℕ) : DTree (Itin n) Bool := bruteForce (univ : Finset (Itin n)).toList

theorem exhaustive_decides (n : ℕ) : Decides (exhaustive n) := by
  intro V; simp [exhaustive, bruteForce_eval]

theorem exhaustive_depth (n : ℕ) : (exhaustive n).depth = 2 ^ n := by
  simp [exhaustive, bruteForce_depth, Finset.length_toList, card_itin]

/-- **The real entropy of black-box search**: the least worst-case number of queries
of any tree that decides it. -/
noncomputable def searchCost (n : ℕ) : ℕ :=
  sInf {d | ∃ t : DTree (Itin n) Bool, Decides t ∧ t.depth = d}

/-- **Exactly `2^n`.** The least cost of deciding a black-box search is `2^n`: lower
bound by the adversary, upper bound by exhaustive search. -/
theorem searchCost_eq (n : ℕ) : searchCost n = 2 ^ n := by
  have hmem : (2 ^ n) ∈ {d | ∃ t : DTree (Itin n) Bool, Decides t ∧ t.depth = d} :=
    ⟨exhaustive n, exhaustive_decides n, exhaustive_depth n⟩
  apply le_antisymm (Nat.sInf_le hmem)
  apply le_csInf ⟨_, hmem⟩
  rintro d ⟨t, ht, rfl⟩
  exact decide_lower_bound t ht

/-- **Apparent cost is unbounded.** For every `m` there is a correct tree of depth
`2^n + m`: inflating an algorithm is free, and says nothing about the problem. -/
theorem apparent_cost_unbounded (n m : ℕ) :
    ∃ t : DTree (Itin n) Bool, Decides t ∧ t.depth = 2 ^ n + m :=
  ⟨pad (exhaustive n) (fun _ => false) m,
    fun V => by rw [pad_eval]; exact exhaustive_decides n V,
    by rw [pad_depth, exhaustive_depth]⟩

/-- **The real entropy is invariant**: it is a lower bound for every correct tree,
however inflated. -/
theorem searchCost_le (t : DTree (Itin n) Bool) (ht : Decides t) : searchCost n ≤ t.depth := by
  rw [searchCost_eq]; exact decide_lower_bound t ht

/-- **Sampling sees only what it touches.** A tree of `q` queries changes its answer,
relative to the empty oracle, on at most `q` of the `2^n` possible unique
witnesses: a search by sampling detects a unique witness with probability at
most `q / 2^n`. -/
theorem detect_le_depth (t : DTree (Itin n) Bool) :
    (univ.filter fun w : Itin n =>
      t.eval (fun v => decide (v = w)) ≠ t.eval (fun _ => false)).card ≤ t.depth := by
  refine le_trans (card_le_card ?_) (falsePath_card_le_depth t)
  intro w hw
  simp only [mem_filter, mem_univ, true_and] at hw
  by_contra hnot
  exact hw (eval_eq_of_false_on_path t _
    (fun q hq => by simp only [decide_eq_false_iff_not]; rintro rfl; exact hnot hq))

/-- A tree finds the unique witness if it returns it for every unit verifier. -/
def Finds (t : DTree (Itin n) (Itin n)) : Prop := ∀ w : Itin n, t.eval (fun v => decide (v = w)) = w

/-- **Finding without structure costs `2^n - 1`.** -/
theorem find_lower_bound (t : DTree (Itin n) (Itin n)) (ht : Finds t) : 2 ^ n - 1 ≤ t.depth := by
  by_contra hlt
  push_neg at hlt
  have hc : 1 < (univ \ t.falsePath).card := by
    rw [card_univ_diff, card_itin]
    have := falsePath_card_le_depth t
    omega
  obtain ⟨a, ha, b, hb, hab⟩ := one_lt_card.mp hc
  rw [mem_sdiff] at ha hb
  have ea := eval_eq_of_false_on_path t (fun v => decide (v = a))
    (fun q hq => by simp only [decide_eq_false_iff_not]; rintro rfl; exact ha.2 hq)
  have eb := eval_eq_of_false_on_path t (fun v => decide (v = b))
    (fun q hq => by simp only [decide_eq_false_iff_not]; rintro rfl; exact hb.2 hq)
  exact hab ((ht a).symm.trans (ea.trans (eb.symm.trans (ht b))))

/-! ## Structure collapses entropy: binary search on a threshold -/

/-- Binary search for the threshold `x₀` in `[lo, lo + 2^m)`, querying
"is `x₀ ≤ q`?". -/
def bsearch (lo : ℕ) : ℕ → DTree ℕ ℕ
  | 0 => DTree.leaf lo
  | m + 1 => DTree.node (lo + 2 ^ m - 1) (bsearch (lo + 2 ^ m) m) (bsearch lo m)

theorem bsearch_depth (lo m : ℕ) : (bsearch lo m).depth = m := by
  induction m generalizing lo with
  | zero => rfl
  | succ m ih => simp [bsearch, DTree.depth, ih]

theorem bsearch_eval (lo m x₀ : ℕ) (h1 : lo ≤ x₀) (h2 : x₀ < lo + 2 ^ m) :
    (bsearch lo m).eval (fun q => decide (x₀ ≤ q)) = x₀ := by
  induction m generalizing lo with
  | zero => simp only [bsearch, DTree.eval]; simp at h2; omega
  | succ m ih =>
    simp only [bsearch, DTree.eval]
    have hp : 1 ≤ 2 ^ m := Nat.one_le_two_pow
    by_cases hx : x₀ ≤ lo + 2 ^ m - 1
    · rw [if_pos (by simpa using hx)]
      exact ih lo h1 (by omega)
    · rw [if_neg (by simpa using hx)]
      exact ih (lo + 2 ^ m) (by omega) (by rw [pow_succ] at h2; omega)

/-- **Structure collapses entropy.** For a monotone (threshold) verifier the
witness among `2^n` candidates is found in `n` queries, against `2^n - 1` for an
unstructured one (`find_lower_bound`). -/
theorem structure_collapse (n : ℕ) :
    ∃ t : DTree ℕ ℕ, t.depth = n ∧
      ∀ x₀ < 2 ^ n, t.eval (fun q => decide (x₀ ≤ q)) = x₀ :=
  ⟨bsearch 0 n, bsearch_depth 0 n, fun x₀ hx => bsearch_eval 0 n x₀ (Nat.zero_le _) (by simpa using hx)⟩

/-! ## Clauses: OR flattens the truth table -/

/-- A clause of width `k` is given by the signs of its literals; the assignment `a`
satisfies it iff some literal is true: `a i = s i`. -/
def ClauseSat {k : ℕ} (s a : Fin k → Bool) : Prop := ∃ i, a i = s i

instance {k : ℕ} (s a : Fin k → Bool) : Decidable (ClauseSat s a) := by
  unfold ClauseSat; infer_instance

/-- **One falsifying row.** Exactly one of the `2^k` local assignments falsifies a
clause of width `k`. -/
theorem clause_falsifier {k : ℕ} (s : Fin k → Bool) :
    (univ.filter fun a : Fin k → Bool => ¬ ClauseSat s a) = {fun i => !s i} := by
  ext a
  simp only [mem_filter, mem_univ, true_and, mem_singleton, ClauseSat, not_exists]
  constructor
  · intro h; funext i; have hi := h i; revert hi; cases a i <;> cases s i <;> decide
  · rintro rfl i; show (!s i) ≠ s i; cases s i <;> simp

theorem card_clause_sat {k : ℕ} (s : Fin k → Bool) :
    (univ.filter fun a : Fin k → Bool => ClauseSat s a).card = 2 ^ k - 1 := by
  have h := Finset.card_filter_add_card_filter_not
    (s := (univ : Finset (Fin k → Bool))) (fun a => ClauseSat s a)
  rw [clause_falsifier, card_singleton, card_univ, Fintype.card_fun, Fintype.card_bool,
    Fintype.card_fin] at h
  omega

/-- The information carried by a clause of width `k`, in bits: `log₂(2^k/(2^k-1))`. -/
noncomputable def clauseInfo (k : ℕ) : ℝ := Real.logb 2 (2 ^ k / (2 ^ k - 1))

/-- **Flat, and flatter with width.** A clause of width `k ≥ 1` carries at most
`2/(2^k - 1)` bits, which tends to `0`. -/
theorem clauseInfo_le (k : ℕ) (hk : 1 ≤ k) : clauseInfo k ≤ 2 / (2 ^ k - 1) := by
  have h2k : (2:ℝ) ≤ 2 ^ k := by
    calc (2:ℝ) = 2 ^ 1 := (pow_one 2).symm
      _ ≤ 2 ^ k := pow_le_pow_right₀ (by norm_num) hk
  have hd : (0:ℝ) < 2 ^ k - 1 := by linarith
  have hx : (0:ℝ) < 2 ^ k / (2 ^ k - 1) := by positivity
  have hlog := Real.log_le_sub_one_of_pos hx
  have hl2 : (1:ℝ) / 2 < Real.log 2 := by
    have := Real.log_two_gt_d9; linarith
  have e : (2:ℝ) ^ k / (2 ^ k - 1) - 1 = 1 / (2 ^ k - 1) := by field_simp; ring
  unfold clauseInfo Real.logb
  rw [div_le_iff₀ (by linarith)]
  calc Real.log (2 ^ k / (2 ^ k - 1)) ≤ 1 / (2 ^ k - 1) := by rw [← e]; exact hlog
    _ = 2 / (2 ^ k - 1) * (1 / 2) := by ring
    _ ≤ 2 / (2 ^ k - 1) * Real.log 2 :=
        mul_le_mul_of_nonneg_left hl2.le (by positivity)

theorem clauseInfo_pos (k : ℕ) (hk : 1 ≤ k) : 0 < clauseInfo k := by
  have h2k : (2:ℝ) ≤ 2 ^ k := by
    calc (2:ℝ) = 2 ^ 1 := (pow_one 2).symm
      _ ≤ 2 ^ k := pow_le_pow_right₀ (by norm_num) hk
  have hd : (0:ℝ) < 2 ^ k - 1 := by linarith
  unfold clauseInfo
  apply Real.logb_pos (by norm_num)
  rw [one_lt_div hd]; linarith

/-- **Majority closure.** The coordinatewise majority of three satisfying
assignments of a width-2 clause satisfies it; the three assignments `100`,
`010`, `001` of a width-3 clause have majority `000`, which falsifies it. So a
3-clause is not the projection of any 2-CNF (Schaefer): the extra OR cannot be
unpacked into 2-clauses at any cost. -/
def maj (a b c : Bool) : Bool := (a && b) || (a && c) || (b && c)

theorem maj_left (x z : Bool) : maj x x z = x := by cases x <;> cases z <;> rfl
theorem maj_mid (x z : Bool) : maj x z x = x := by cases x <;> cases z <;> rfl
theorem maj_right (x z : Bool) : maj z x x = x := by cases x <;> cases z <;> rfl

theorem clause2_maj_closed (s a b c : Fin 2 → Bool) (ha : ClauseSat s a) (hb : ClauseSat s b)
    (hc : ClauseSat s c) : ClauseSat s (fun i => maj (a i) (b i) (c i)) := by
  obtain ⟨i, hi⟩ := ha; obtain ⟨j, hj⟩ := hb; obtain ⟨l, hl⟩ := hc
  by_cases hij : i = j
  · subst hij; exact ⟨i, by show maj (a i) (b i) (c i) = s i; rw [hi, hj, maj_left]⟩
  by_cases hil : i = l
  · subst hil; exact ⟨i, by show maj (a i) (b i) (c i) = s i; rw [hi, hl, maj_mid]⟩
  have hjl : j = l := by
    have h1 : i.val ≠ j.val := fun h => hij (Fin.ext h)
    have h2 : i.val ≠ l.val := fun h => hil (Fin.ext h)
    have := i.isLt; have := j.isLt; have := l.isLt
    exact Fin.ext (by omega)
  subst hjl; exact ⟨j, by show maj (a j) (b j) (c j) = s j; rw [hj, hl, maj_right]⟩

theorem clause3_not_maj_closed :
    let s : Fin 3 → Bool := fun _ => true
    let a : Fin 3 → Bool := ![true, false, false]
    let b : Fin 3 → Bool := ![false, true, false]
    let c : Fin 3 → Bool := ![false, false, true]
    ClauseSat s a ∧ ClauseSat s b ∧ ClauseSat s c ∧
      ¬ ClauseSat s (fun i => maj (a i) (b i) (c i)) := by
  refine ⟨⟨0, rfl⟩, ⟨1, rfl⟩, ⟨2, rfl⟩, ?_⟩
  rintro ⟨i, hi⟩
  fin_cases i <;> simp [maj] at hi

/-! ## Schöning's base -/

/-- The base of Schöning's random-walk bound `(2(k-1)/k)^n` for `k`-SAT. -/
noncomputable def schoningBase (k : ℕ) : ℝ := 2 * ((k : ℝ) - 1) / k

theorem schoningBase_three : schoningBase 3 = 4 / 3 := by
  unfold schoningBase; norm_num

theorem schoningBase_lt_two (k : ℕ) (hk : 0 < k) : schoningBase k < 2 := by
  unfold schoningBase
  have : (0:ℝ) < k := by exact_mod_cast hk
  rw [div_lt_iff₀ this]; linarith

theorem schoningBase_eq (k : ℕ) (hk : 0 < k) : schoningBase k = 2 - 2 / k := by
  unfold schoningBase
  have : (k:ℝ) ≠ 0 := by exact_mod_cast hk.ne'
  field_simp

/-- **Wider clauses, weaker walk.** The base increases with the width. -/
theorem schoningBase_strictMono {j k : ℕ} (hj : 0 < j) (hjk : j < k) :
    schoningBase j < schoningBase k := by
  rw [schoningBase_eq j hj, schoningBase_eq k (by omega)]
  have hj' : (0:ℝ) < j := by exact_mod_cast hj
  have hjk' : (j:ℝ) < k := by exact_mod_cast hjk
  have : 2 / (k:ℝ) < 2 / j := div_lt_div_of_pos_left (by norm_num) hj' hjk'
  linarith

/-- **The naive cost in the limit.** As the width grows the base tends to `2`,
the base of exhaustive search over `2^n` assignments. -/
theorem schoningBase_tendsto : Filter.Tendsto schoningBase Filter.atTop (nhds 2) := by
  have h : Filter.Tendsto (fun k : ℕ => (2:ℝ) - 2 / k) Filter.atTop (nhds (2 - 0)) :=
    tendsto_const_nhds.sub (tendsto_const_div_atTop_nhds_zero_nat 2)
  rw [sub_zero] at h
  refine h.congr' ?_
  filter_upwards [Filter.eventually_gt_atTop 0] with k hk
  rw [schoningBase_eq k hk]

/-! ## Reals are words -/

/-- **A granular real is a word.** `N` lattice cells embed in `⌈log₂ N⌉` bits. -/
theorem cells_are_words (N : ℕ) : ∃ f : Fin N → Itin (Nat.clog 2 N), Injective f := by
  refine ⟨fun k => code (Nat.clog 2 N) k, fun a b h => Fin.ext ?_⟩
  have hN := Nat.le_pow_clog (b := 2) (by norm_num) N
  exact code_injOn _ (show (a : ℕ) < 2 ^ Nat.clog 2 N by omega)
    (show (b : ℕ) < 2 ^ Nat.clog 2 N by omega) h

/-! ## Conservativity: the question is where ZFC leaves it -/

open FirstOrder FirstOrder.Language in
/-- **The granule does not move P vs NP.** Every sentence of the full real language,
which includes every arithmetic sentence and hence the statement `P ≠ NP`, has the
same truth value in the hyperreal field as in the real field (semantic
conservativity, Chapter 1). -/
theorem complexity_sentence_transfer (φ : QE.NSA.realLang.Sentence) : ℝ* ⊨ φ ↔ ℝ ⊨ φ :=
  QE.NSA.conservative φ


/-! ## A circuit-lower-bound construction: what holds and what is missing -/

section Polymorphisms

/-- `f` preserves a ternary relation `R`: applied row by row to three rows whose
columns lie in `R`, it produces a triple in `R`. -/
def Preserves3 {k : ℕ} (f : (Fin k → Bool) → Bool) (R : (Fin 3 → Bool) → Prop) : Prop :=
  ∀ u : Fin 3 → Fin k → Bool, (∀ i, R (fun j => u j i)) → R (fun j => f (u j))

/-- The punctured cube `Bool³ \ {b}`: the solutions of one 3-clause. -/
def Punct (b : Fin 3 → Bool) (t : Fin 3 → Bool) : Prop := t ≠ b

/-- A polymorphism of 3-SAT: it preserves all eight punctured cubes. -/
def Pol3SAT {k : ℕ} (f : (Fin k → Bool) → Bool) : Prop := ∀ b, Preserves3 f (Punct b)

variable {k : ℕ} {f : (Fin k → Bool) → Bool}

theorem pol_apply (hf : Pol3SAT f) (b0 b1 b2 : Bool) (x y z : Fin k → Bool)
    (h : ∀ i, ¬ (x i = b0 ∧ y i = b1 ∧ z i = b2)) : ¬ (f x = b0 ∧ f y = b1 ∧ f z = b2) := by
  have key := hf ![b0, b1, b2] ![x, y, z] (fun i heq => h i
    ⟨by simpa using congrFun heq 0, by simpa using congrFun heq 1, by simpa using congrFun heq 2⟩)
  rintro ⟨h0, h1, h2⟩
  apply key
  funext j
  fin_cases j <;> simp [h0, h1, h2]

theorem pol_idem (hf : Pol3SAT f) (c : Bool) : f (fun _ => c) = c := by
  have h := pol_apply hf (!c) (!c) (!c) (fun _ => c) (fun _ => c) (fun _ => c)
    (fun i ⟨h0, _, _⟩ => by cases c <;> simp at h0)
  rcases Bool.eq_false_or_eq_true (f (fun _ => c)) with h1 | h1 <;> cases c <;> simp_all

theorem pol_selfdual (hf : Pol3SAT f) (x : Fin k → Bool) : f (fun i => !x i) = !f x := by
  have h1 := pol_apply hf true true true x (fun i => !x i) (fun i => !x i)
    (fun i ⟨a, b, _⟩ => by simp_all)
  have h2 := pol_apply hf false false false x (fun i => !x i) (fun i => !x i)
    (fun i ⟨a, b, _⟩ => by simp_all)
  rcases Bool.eq_false_or_eq_true (f x) with hx | hx <;>
    rcases Bool.eq_false_or_eq_true (f (fun i => !x i)) with hy | hy <;> simp_all

theorem pol_mono (hf : Pol3SAT f) {x y : Fin k → Bool} (hxy : ∀ i, x i = true → y i = true)
    (hx : f x = true) : f y = true := by
  have h := pol_apply hf true false false x y y
    (fun i ⟨a, b, _⟩ => by have := hxy i a; simp_all)
  by_contra hy
  exact h ⟨hx, by simpa using hy, by simpa using hy⟩

theorem pol_or3 (hf : Pol3SAT f) (x y z : Fin k → Bool)
    (hcov : ∀ i, x i = true ∨ y i = true ∨ z i = true) :
    f x = true ∨ f y = true ∨ f z = true := by
  have h := pol_apply hf false false false x y z
    (fun i ⟨a, b, c⟩ => by rcases hcov i with h | h | h <;> simp_all)
  by_contra hn
  simp only [not_or, Bool.not_eq_true] at hn
  exact h ⟨hn.1, hn.2.1, hn.2.2⟩

theorem pol_inter (hf : Pol3SAT f) {x y : Fin k → Bool} (hx : f x = true) (hy : f y = true) :
    f (fun i => x i && y i) = true := by
  have hcov : ∀ i, (fun i => x i && y i) i = true ∨ (fun i => !x i) i = true ∨
      (fun i => x i && !y i) i = true := by
    intro i; rcases Bool.eq_false_or_eq_true (x i) with h1 | h1 <;>
      rcases Bool.eq_false_or_eq_true (y i) with h2 | h2 <;> simp [h1, h2]
  rcases pol_or3 hf _ _ _ hcov with h | h | h
  · exact h
  · rw [pol_selfdual hf, hx] at h; simp at h
  · have hny : f (fun i => !y i) = false := by rw [pol_selfdual hf, hy]; rfl
    have := pol_mono hf (x := fun i => x i && !y i) (y := fun i => !y i)
      (fun i hi => by simp_all) h
    rw [hny] at this; exact absurd this (by simp)

/-- **The polymorphisms of 3-SAT are the projections.** Every function of any arity
that preserves all eight punctured cubes is a dictator. -/
theorem pol3SAT_dictator (hf : Pol3SAT f) : ∃ i, ∀ x, f x = x i := by
  classical
  have hmeet : ∀ s : Finset (Fin k → Bool), (∀ x ∈ s, f x = true) →
      f (fun j => decide (∀ x ∈ s, x j = true)) = true := by
    intro s
    refine Finset.induction_on s ?_ ?_
    · intro _; simpa using pol_idem hf true
    · intro a s ha ih h
      have e : (fun j => decide (∀ x ∈ insert a s, x j = true)) =
          fun j => a j && decide (∀ x ∈ s, x j = true) := by
        funext j; simp [Finset.forall_mem_insert]
      rw [e]
      exact pol_inter hf (h a (Finset.mem_insert_self a s))
        (ih fun x hx => h x (Finset.mem_insert_of_mem hx))
  obtain ⟨m, hm⟩ : ∃ m : Fin k → Bool, ∀ j, m j = true ↔ ∀ x, f x = true → x j = true :=
    ⟨fun j => decide (∀ x, f x = true → x j = true), fun j => by simp⟩
  have hfm : f m = true := by
    have hs := hmeet (Finset.univ.filter fun x => f x = true) (by intro x hx; simpa using hx)
    have e : m = fun j => decide (∀ x ∈ Finset.univ.filter (fun x => f x = true), x j = true) := by
      funext j
      apply Bool.eq_iff_iff.mpr
      rw [hm j]; simp
    rw [e]; exact hs
  obtain ⟨i, hi⟩ : ∃ i, m i = true := by
    by_contra hne
    simp only [not_exists, Bool.not_eq_true] at hne
    have : m = fun _ => false := funext hne
    rw [this, pol_idem hf false] at hfm
    exact Bool.false_ne_true hfm
  have hmi := (hm i).1 hi
  refine ⟨i, fun x => ?_⟩
  cases hxi : x i
  · by_contra hfx
    have h1 : f x = true := by simpa using hfx
    have := hmi x h1; rw [hxi] at this; exact Bool.false_ne_true this
  · by_contra hfx
    have hfx' : f x = false := by simpa using hfx
    have hnx : f (fun j => !x j) = true := by rw [pol_selfdual hf, hfx']; rfl
    have := hmi _ hnx
    simp [hxi] at this

/-- A single 3-clause is weaker: `x ∨ y` preserves the clause `x ∨ y ∨ z`. -/
theorem or_preserves_clause :
    Preserves3 (fun x : Fin 2 → Bool => x 0 || x 1) (Punct fun _ => false) := by
  intro u h heq
  apply h 0
  funext j
  have := congrFun heq j
  simp only at this
  exact (Bool.or_eq_false_iff.mp this).1

theorem or_not_dictator : ∀ i : Fin 2, ¬ ∀ x : Fin 2 → Bool, (x 0 || x 1) = x i := by
  intro i h
  fin_cases i
  · have := h ![false, true]; simp at this
  · have := h ![true, false]; simp at this

/-- So is a constant: the constant `true` preserves `x ∨ y ∨ z`. -/
theorem const_preserves_clause :
    Preserves3 (fun _ : Fin 1 → Bool => true) (Punct fun _ => false) := by
  intro u _ heq
  have := congrFun heq 0
  simp at this

/-- XOR-SAT has a non-dictator polymorphism: the minority `x ⊕ y ⊕ z` preserves every
parity constraint. -/
theorem minority_preserves_xor (c : Bool) :
    Preserves3 (fun x : Fin 3 → Bool => xor (xor (x 0) (x 1)) (x 2))
      (fun t => xor (xor (t 0) (t 1)) (t 2) = c) := by
  have key : ∀ (a b d e g l p r w c : Bool), xor (xor a e) p = c → xor (xor b g) r = c →
      xor (xor d l) w = c → xor (xor (xor (xor a b) d) (xor (xor e g) l)) (xor (xor p r) w) = c := by
    decide
  intro u h
  have h0 := h 0; have h1 := h 1; have h2 := h 2
  simp only at h0 h1 h2 ⊢
  exact key _ _ _ _ _ _ _ _ _ _ h0 h1 h2

theorem minority_not_dictator :
    ∀ i : Fin 3, ¬ ∀ x : Fin 3 → Bool, xor (xor (x 0) (x 1)) (x 2) = x i := by
  intro i h
  fin_cases i
  · have := h ![true, true, false]; simp at this
  · have := h ![true, true, false]; simp at this
  · have := h ![true, false, true]; simp at this

end Polymorphisms

section Encodings

/-- No power of five is a power of two's divisor-sharer: `gcd(5^k, 2^m) = 1`. -/
theorem five_pow_coprime_two_pow (k m : ℕ) : Nat.Coprime (5 ^ k) (2 ^ m) :=
  Nat.Coprime.pow k m (by norm_num)

/-- An injective binary block code for a five-letter alphabet wastes a codeword. -/
theorem alphabet_gap {k m : ℕ} (hk : 1 ≤ k) (e : Fin (5 ^ k) → Fin (2 ^ m))
    (he : Function.Injective e) : 5 ^ k < 2 ^ m := by
  have hle := Fintype.card_le_of_injective e he
  simp only [Fintype.card_fin] at hle
  rcases hle.lt_or_eq with h | h
  · exact h
  · exfalso
    have h5 : Odd (5 ^ k) := Odd.pow (by decide)
    rcases Nat.eq_zero_or_pos m with hm | hm
    · subst hm
      have : 5 ≤ 5 ^ k := Nat.le_self_pow (by omega) 5
      rw [pow_zero] at h; omega
    · have h2 : Even (2 ^ m) := Nat.even_pow.mpr ⟨even_two, hm.ne'⟩
      rw [h] at h5; exact (Nat.not_even_iff_odd.mpr h5) h2

/-- An odd cycle cannot be seen by a binary register: every additive map
`ZMod q → ZMod (2^w)` is zero when `q` is odd. -/
theorem hom_odd_to_two_pow (q w : ℕ) (hq : Odd q) (φ : ZMod q →+ ZMod (2 ^ w)) : φ = 0 := by
  have hcop : Nat.Coprime q (2 ^ w) := Nat.Coprime.pow_right w (Nat.coprime_two_right.mpr hq)
  refine AddMonoidHom.ext fun x => ?_
  rw [AddMonoidHom.zero_apply]
  have h1 : (q : ZMod (2 ^ w)) * φ x = 0 := by
    rw [← nsmul_eq_mul, ← map_nsmul, nsmul_eq_mul, ZMod.natCast_self, zero_mul, map_zero]
  have hu := ZMod.coe_unitOfCoprime q hcop
  calc φ x = (((ZMod.unitOfCoprime q hcop)⁻¹ * ZMod.unitOfCoprime q hcop :
        (ZMod (2 ^ w))ˣ) : ZMod (2 ^ w)) * φ x := by simp
    _ = 0 := by rw [Units.val_mul, mul_assoc, hu, h1, mul_zero]

/-- The exact sum of `N` values below `κ` needs no more than `N(κ-1)`. -/
theorem acc_sum_le {N κ : ℕ} (a : Fin N → ℕ) (ha : ∀ i, a i ≤ κ - 1) :
    ∑ i, a i ≤ N * (κ - 1) := by
  calc ∑ i, a i ≤ ∑ _i : Fin N, (κ - 1) := Finset.sum_le_sum fun i _ => ha i
    _ = N * (κ - 1) := by simp

/-- A register of `w` bits overflows on some input as soon as `2^w ≤ N(κ-1)`. -/
theorem acc_overflow {N κ w : ℕ} (h : 2 ^ w ≤ N * (κ - 1)) :
    (∑ _i : Fin N, (κ - 1)) % 2 ^ w ≠ ∑ _i : Fin N, (κ - 1) := by
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
  intro he
  have := Nat.mod_lt (N * (κ - 1)) (by positivity : 0 < 2 ^ w)
  omega

end Encodings

section Geometry

/-- One step of a Hamiltonian `H = ν·p + V(q)` on a lattice phase space: a shear,
hence a bijection (Liouville on the lattice). -/
def shear {G : Type*} [AddCommGroup G] (ν : G) (g : G → G) (p : G × G) : G × G :=
  (p.1 + ν, p.2 - g (p.1 + ν))

theorem shear_bijective {G : Type*} [AddCommGroup G] (ν : G) (g : G → G) :
    Function.Bijective (shear ν g) := by
  refine Function.bijective_iff_has_inverse.mpr ⟨fun p => (p.1 - ν, p.2 + g p.1), ?_, ?_⟩
  · intro p; simp [shear]
  · intro p; simp [shear]

/-- A column that starts and ends with different values crosses somewhere. -/
theorem column_crossing (g : ℕ → Bool) : ∀ L, g 0 ≠ g L → ∃ i < L, g i ≠ g (i + 1)
  | 0, h => absurd rfl h
  | L + 1, h => by
    by_cases hL : g L = g (L + 1)
    · obtain ⟨i, hi, hne⟩ := column_crossing g L (by rwa [hL])
      exact ⟨i, by omega, hne⟩
    · exact ⟨L, by omega, hL⟩

/-- **Staircase count.** A region that separates the two ends of every column of a
grid has at least one boundary cell per column. -/
theorem staircase_count {κ : Type*} [Fintype κ] [DecidableEq κ] (L : ℕ) (g : κ → ℕ → Bool)
    (h : ∀ c, g c 0 ≠ g c L) :
    Fintype.card κ ≤ ((Finset.univ ×ˢ Finset.range L).filter
      fun p : κ × ℕ => g p.1 p.2 ≠ g p.1 (p.2 + 1)).card := by
  classical
  choose i hi hne using fun c => column_crossing (g c) L (h c)
  have hsub : (Finset.univ.image fun c => (c, i c)) ⊆ (Finset.univ ×ˢ Finset.range L).filter
      fun p : κ × ℕ => g p.1 p.2 ≠ g p.1 (p.2 + 1) := by
    intro p hp
    simp only [Finset.mem_image, Finset.mem_univ, true_and] at hp
    obtain ⟨c, rfl⟩ := hp
    simp [hi c, hne c]
  calc Fintype.card κ = (Finset.univ.image fun c => (c, i c)).card := by
        rw [Finset.card_image_of_injective _ (fun a b hab => by simpa using congrArg Prod.fst hab),
          Finset.card_univ]
    _ ≤ _ := Finset.card_le_card hsub

/-- Parity, the sum of the bits modulo two. -/
def parity {N : ℕ} (x : Fin N → Bool) : ZMod 2 := ∑ i, if x i then 1 else 0

/-- **Boundary does not bound circuit size.** Flipping any bit flips the parity: every
edge of the cube is a boundary edge, while parity is a chain of `N - 1` XOR gates. -/
theorem parity_flip {N : ℕ} (x : Fin N → Bool) (j : Fin N) :
    parity (Function.update x j (!x j)) = parity x + 1 := by
  unfold parity
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ j), ← Finset.add_sum_erase _ _ (Finset.mem_univ j)]
  have hrest : ∑ i ∈ Finset.univ.erase j,
      (if Function.update x j (!x j) i then (1 : ZMod 2) else 0) =
      ∑ i ∈ Finset.univ.erase j, (if x i then 1 else 0) :=
    Finset.sum_congr rfl fun i hi => by rw [Function.update_of_ne (Finset.ne_of_mem_erase hi)]
  rw [hrest, Function.update_self]
  have h2 : (1 : ZMod 2) + 1 = 0 := by decide
  cases x j <;> simp only [Bool.not_false, Bool.not_true, if_true, if_false, Bool.false_eq_true]
  · ring
  · linear_combination (-1 : ZMod 2) * h2

theorem parity_every_edge {N : ℕ} (x : Fin N → Bool) (j : Fin N) :
    parity (Function.update x j (!x j)) ≠ parity x := by
  rw [parity_flip]; intro h
  have : (1 : ZMod 2) = 0 := by linear_combination h
  exact absurd this (by decide)

/-- The sliver of a set: the part that moves under a shift `T`. -/
def disc {α : Type*} [DecidableEq α] (T : α ≃ α) (A : Finset α) : ℕ :=
  (symmDiff A (A.map T.toEmbedding)).card

theorem disc_union {α : Type*} [DecidableEq α] (T : α ≃ α) (A B : Finset α) :
    disc T (A ∪ B) ≤ disc T A + disc T B := by
  unfold disc
  refine (Finset.card_le_card ?_).trans (Finset.card_union_le _ _)
  intro x hx
  simp only [Finset.mem_symmDiff, Finset.mem_map_equiv, Finset.mem_union] at hx ⊢
  tauto

theorem disc_inter {α : Type*} [DecidableEq α] (T : α ≃ α) (A B : Finset α) :
    disc T (A ∩ B) ≤ disc T A + disc T B := by
  unfold disc
  refine (Finset.card_le_card ?_).trans (Finset.card_union_le _ _)
  intro x hx
  simp only [Finset.mem_symmDiff, Finset.mem_map_equiv, Finset.mem_inter, Finset.mem_union] at hx ⊢
  tauto

/-- Monotone formulas over literal sets (dual rail: complements are literals too). -/
inductive Fml (ι : Type*) : Type _
  | lit : ι → Fml ι
  | and : Fml ι → Fml ι → Fml ι
  | or : Fml ι → Fml ι → Fml ι

namespace Fml

variable {ι α : Type*} [DecidableEq α]

def region (S : ι → Finset α) : Fml ι → Finset α
  | lit i => S i
  | and φ ψ => region S φ ∩ region S ψ
  | or φ ψ => region S φ ∪ region S ψ

def leafSum (T : α ≃ α) (S : ι → Finset α) : Fml ι → ℕ
  | lit i => disc T (S i)
  | and φ ψ => leafSum T S φ + leafSum T S ψ
  | or φ ψ => leafSum T S φ + leafSum T S ψ

/-- **The sub-additive ceiling.** The sliver of a formula's region is at most the sum of
the slivers of its leaves: such a measure grows at most linearly in formula size. -/
theorem disc_region_le (T : α ≃ α) (S : ι → Finset α) (φ : Fml ι) :
    disc T (region S φ) ≤ leafSum T S φ := by
  induction φ with
  | lit i => exact le_rfl
  | and φ ψ ihφ ihψ => exact (disc_inter T _ _).trans (Nat.add_le_add ihφ ihψ)
  | or φ ψ ihφ ihψ => exact (disc_union T _ _).trans (Nat.add_le_add ihφ ihψ)

end Fml

end Geometry

section Potential

variable {ι : Type*} [Fintype ι]

/-- The quadratic potential of a charge density on a finite (granular) space. -/
def psi (K : ι → ι → ℝ) (ρ : ι → ℝ) : ℝ := ∑ i, ∑ j, K i j * ρ i * ρ j

/-- **The increment of a quadratic potential has a cross term.** -/
theorem psi_increment (K : ι → ι → ℝ) (hK : ∀ i j, K i j = K j i) (ρ d : ι → ℝ) :
    psi K (ρ + d) - psi K ρ = 2 * ∑ i, ∑ j, K i j * ρ i * d j + psi K d := by
  have hswap : ∑ i, ∑ j, K i j * d i * ρ j = ∑ i, ∑ j, K i j * ρ i * d j := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [hK]; ring
  unfold psi
  have e : ∀ i j, K i j * (ρ + d) i * (ρ + d) j = K i j * ρ i * ρ j + K i j * ρ i * d j +
      K i j * d i * ρ j + K i j * d i * d j := by
    intro i j; simp only [Pi.add_apply]; ring
  simp only [e, Finset.sum_add_distrib, hswap]
  ring

/-- The granule average of a charge `σ` over the fibres of a transcript `g`. -/
noncomputable def granAvg {γ : Type*} [DecidableEq γ] (g : ι → γ) (σ : ι → ℝ) (i : ι) : ℝ :=
  (∑ j ∈ Finset.univ.filter (fun j => g j = g i), σ j) /
    (Finset.univ.filter (fun j => g j = g i)).card

/-- **The final potential does not depend on the circuit.** Once the transcript
separates the charge, the granule average is the charge itself. -/
theorem granAvg_eq_of_pure {γ : Type*} [DecidableEq γ] (g : ι → γ) (σ : ι → ℝ)
    (h : ∀ i j, g i = g j → σ i = σ j) : granAvg g σ = σ := by
  funext i
  unfold granAvg
  have hc : 0 < (Finset.univ.filter fun j => g j = g i).card :=
    Finset.card_pos.mpr ⟨i, by simp⟩
  have hc' : ((Finset.univ.filter fun j => g j = g i).card : ℝ) ≠ 0 := by exact_mod_cast hc.ne'
  rw [Finset.sum_congr rfl (fun j hj => h j i (by simpa using hj)), Finset.sum_const, nsmul_eq_mul]
  field_simp

/-- **One bit separates every pair.** The answer bit alone is a pure transcript: its
two granules carry the whole charge, however many instance pairs there are. -/
theorem one_bit_separates (ans : ι → Bool) :
    granAvg ans (fun i => if ans i then 1 else -1) = fun i => if ans i then 1 else -1 :=
  granAvg_eq_of_pure ans _ (fun i j h => by simp [h])

/-- **The conditional bound.** If no gate raises the potential by more than `c`, then
`s` gates raise it by at most `s c`: a cap per gate turns the total rise into a
lower bound on the number of gates. -/
theorem potential_lower_bound (Ψ : ℕ → ℝ) (c : ℝ) :
    ∀ s, (∀ t < s, Ψ (t + 1) - Ψ t ≤ c) → Ψ s - Ψ 0 ≤ s * c
  | 0, _ => by simp
  | s + 1, h => by
    have ih := potential_lower_bound Ψ c s (fun t ht => h t (by omega))
    have := h s (by omega)
    push_cast; linarith

end Potential


section Addendum

/-- **The input cap.** A circuit sees `Π w ∈ {0,1}^N`: at most `2^N` distinct inputs
reach it, whatever the resolution of the parameter space. -/
theorem input_cap {W : Type*} [Fintype W] {N : ℕ} (proj : W → (Fin N → Bool)) :
    (Finset.univ.image proj).card ≤ 2 ^ N := by
  classical
  calc (Finset.univ.image proj).card ≤ Fintype.card (Fin N → Bool) := Finset.card_le_univ _
    _ = 2 ^ N := by simp

/-- Two parameters with the same input string get the same answer: the answer is a
function of the formula, so a satisfiable and an unsatisfiable chamber always have
different inputs. -/
theorem same_input_same_answer {W F : Type*} (proj : W → F) (ans : F → Bool) {w w' : W}
    (h : proj w = proj w') : ans (proj w) = ans (proj w') := by rw [h]

/-- The charge of one clause over its cube: seven satisfying points, one not; the sum
is `6`. -/
theorem clause_charge (b : Fin 3 → Bool) :
    ∑ t : Fin 3 → Bool, (if t = b then (-1 : ℤ) else 1) = 6 := by
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ b)]
  have : ∑ t ∈ Finset.univ.erase b, (if t = b then (-1 : ℤ) else 1) =
      ∑ t ∈ Finset.univ.erase b, (1 : ℤ) :=
    Finset.sum_congr rfl fun t ht => by rw [if_neg (Finset.ne_of_mem_erase ht)]
  rw [this, Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ b), Finset.card_univ]
  simp

/-- **Fast exponentiation with a count of multiplications.** -/
def fpow {M : Type*} [Monoid M] (a : M) (n : ℕ) : M × ℕ :=
  if h : n = 0 then (1, 0) else
    let r := fpow (a * a) (n / 2)
    if n % 2 = 0 then (r.1, r.2 + 1) else (a * r.1, r.2 + 2)
termination_by n
decreasing_by omega

theorem fpow_val {M : Type*} [Monoid M] (a : M) (n : ℕ) : (fpow a n).1 = a ^ n := by
  induction n using Nat.strong_induction_on generalizing a with
  | _ n ih =>
    rw [fpow]
    by_cases h0 : n = 0
    · simp [h0]
    · simp only [h0, dite_false]
      have hr := ih (n / 2) (by omega) (a * a)
      have hsq : (a * a) ^ (n / 2) = a ^ (2 * (n / 2)) := by rw [pow_mul, sq]
      split_ifs with he
      · simp only; rw [hr, hsq]; congr 1; omega
      · simp only; rw [hr, hsq, ← pow_succ']; congr 1; omega

theorem fpow_count {M : Type*} [Monoid M] (a : M) (n : ℕ) :
    (fpow a n).2 ≤ 2 * Nat.log 2 n + 2 := by
  induction n using Nat.strong_induction_on generalizing a with
  | _ n ih =>
    rw [fpow]
    by_cases h0 : n = 0
    · simp [h0]
    · simp only [h0, dite_false]
      have hr := ih (n / 2) (by omega) (a * a)
      have hlog : n / 2 = 0 ∨ Nat.log 2 (n / 2) + 1 = Nat.log 2 n := by
        rcases Nat.lt_or_ge n 2 with h | h
        · left; omega
        · right; rw [Nat.log_div_base]; have := Nat.log_pos (by norm_num : 1 < 2) h; omega
      split_ifs <;> simp only <;> rcases hlog with h | h
      · rw [h] at hr ⊢; simp [fpow]
      · omega
      · rw [h] at hr ⊢; simp [fpow]
      · omega

/-- **A chaotic map can be jumped.** The `T`-th power of the cat matrix, or of the
doubling `x ↦ 2x` on an odd modulus, is computed with at most `2 log₂ T + 2`
multiplications. -/
theorem cat_jump (q T : ℕ) :
    (fpow !![(2 : ZMod q), 1; 1, 1] T).1 = !![(2 : ZMod q), 1; 1, 1] ^ T ∧
      (fpow !![(2 : ZMod q), 1; 1, 1] T).2 ≤ 2 * Nat.log 2 T + 2 :=
  ⟨fpow_val _ _, fpow_count _ _⟩

theorem odd_doubling_jump (q T : ℕ) :
    (fpow (2 : ZMod q) T).1 = 2 ^ T ∧ (fpow (2 : ZMod q) T).2 ≤ 2 * Nat.log 2 T + 2 :=
  ⟨fpow_val _ _, fpow_count _ _⟩

/-- **Every 2-clause is a 3-SAT constraint.** Repeating a variable turns the punctured
cube into any 2-clause: the full clause language encodes every step circuit,
including those of jumpable maps. -/
theorem two_clause_as_punct (b1 b2 x y : Bool) :
    Punct ![b1, b2, b2] ![x, y, y] ↔ ¬ (x = b1 ∧ y = b2) := by
  unfold Punct
  constructor
  · intro h ⟨h1, h2⟩; apply h; subst h1; subst h2; rfl
  · intro h heq; apply h
    exact ⟨by simpa using congrFun heq 0, by simpa using congrFun heq 1⟩

end Addendum


section Forces

/-- The radial force law of the potential `r^(-a)`: its derivative is `-a r^(-a-1)`. -/
theorem riesz_deriv (a r : ℝ) (hr : 0 < r) :
    HasDerivAt (fun r : ℝ => r ^ (-a)) (-a * r ^ (-a - 1)) r :=
  Real.hasDerivAt_rpow_const (Or.inl hr.ne')

/-- The dynamic range of the force between separations `r₀ < r₁`:
`r₀^(-(a+1)) / r₁^(-(a+1)) = (r₁ / r₀)^(a+1)`. -/
theorem force_ratio (a r₀ r₁ : ℝ) (h₀ : 0 < r₀) (h₁ : 0 < r₁) :
    r₀ ^ (-(a + 1)) / r₁ ^ (-(a + 1)) = (r₁ / r₀) ^ (a + 1) := by
  rw [Real.rpow_neg h₀.le, Real.rpow_neg h₁.le, Real.div_rpow h₁.le h₀.le]
  field_simp

end Forces


section Ensemble

/-- A CNF over variables `V`: a list of clauses, a clause a list of literals
`(variable, sign)`. -/
structure CNF (V : Type*) where
  clauses : List (List (V × Bool))

def CNF.Sat {V : Type*} (φ : CNF V) (a : V → Bool) : Prop :=
  ∀ c ∈ φ.clauses, ∃ l ∈ c, a l.1 = l.2

/-- The width of a CNF: the length of its longest clause. -/
def CNF.width {V : Type*} (φ : CNF V) : ℕ := (φ.clauses.map List.length).foldr max 0

/-- The instance bits from the granular torus: `y_r(w) = [⟨c_r, w⟩ mod L < θ_r]`, a
cut-and-project threshold on `(ZMod L)^D`. -/
def thresh {D N L : ℕ} (c : Fin N → Fin D → ZMod L) (θ : Fin N → ℕ) (w : Fin D → ZMod L) :
    Fin N → Bool :=
  fun r => decide ((∑ k, c r k * w k).val < θ r)

/-- **The ensemble.** A fixed template `Φ₀` over witness, instance and auxiliary
variables (`X ⊕ Fin N ⊕ Z`) instantiated by unit clauses fixing the instance bits. -/
def instantiate {X Z : Type*} {N : ℕ} (Φ₀ : CNF (X ⊕ Fin N ⊕ Z)) (y : Fin N → Bool) :
    CNF (X ⊕ Fin N ⊕ Z) :=
  ⟨Φ₀.clauses ++ (List.finRange N).map fun r => [(Sum.inr (Sum.inl r), y r)]⟩

def ensemble {X Z : Type*} {D N L : ℕ} (Φ₀ : CNF (X ⊕ Fin N ⊕ Z))
    (c : Fin N → Fin D → ZMod L) (θ : Fin N → ℕ) (w : Fin D → ZMod L) : CNF (X ⊕ Fin N ⊕ Z) :=
  instantiate Φ₀ (thresh c θ w)

/-- **Satisfiable iff the template has a solution with the threshold bits.** -/
theorem instantiate_sat_iff {X Z : Type*} {N : ℕ} (Φ₀ : CNF (X ⊕ Fin N ⊕ Z))
    (y : Fin N → Bool) (a : X ⊕ Fin N ⊕ Z → Bool) :
    (instantiate Φ₀ y).Sat a ↔ Φ₀.Sat a ∧ ∀ r, a (Sum.inr (Sum.inl r)) = y r := by
  unfold instantiate CNF.Sat
  simp only [List.mem_append, List.mem_map, List.mem_finRange, true_and]
  constructor
  · intro h
    refine ⟨fun c hc => h c (Or.inl hc), fun r => ?_⟩
    obtain ⟨l, hl, hal⟩ := h _ (Or.inr ⟨r, rfl⟩)
    simp only [List.mem_singleton] at hl
    subst hl; exact hal
  · rintro ⟨h1, h2⟩ c (hc | ⟨r, rfl⟩)
    · exact h1 c hc
    · exact ⟨_, List.mem_singleton_self _, h2 r⟩

theorem ensemble_sat_iff {X Z : Type*} {D N L : ℕ} (Φ₀ : CNF (X ⊕ Fin N ⊕ Z))
    (c : Fin N → Fin D → ZMod L) (θ : Fin N → ℕ) (w : Fin D → ZMod L) :
    (∃ a, (ensemble Φ₀ c θ w).Sat a) ↔
      ∃ a, Φ₀.Sat a ∧ ∀ r, a (Sum.inr (Sum.inl r)) = thresh c θ w r := by
  unfold ensemble
  exact exists_congr fun a => instantiate_sat_iff Φ₀ _ a

/-- The instance bits are all a circuit sees: two points with the same threshold bits
give the same formula. -/
theorem ensemble_factors {X Z : Type*} {D N L : ℕ} (Φ₀ : CNF (X ⊕ Fin N ⊕ Z))
    (c : Fin N → Fin D → ZMod L) (θ : Fin N → ℕ) {w w' : Fin D → ZMod L}
    (h : thresh c θ w = thresh c θ w') : ensemble Φ₀ c θ w = ensemble Φ₀ c θ w' := by
  unfold ensemble; rw [h]

end Ensemble


section Distribution

/-- **Each cut is exactly equidistributed.** On the granular torus `(ZMod p)^D`, `p`
prime, a nonzero linear form takes every value on exactly `p^(D-1)` points. -/
theorem linform_fiber_card {p D : ℕ} [Fact p.Prime] (c : Fin D → ZMod p) (hc : c ≠ 0)
    (v : ZMod p) :
    (Finset.univ.filter fun w : Fin D → ZMod p => ∑ k, c k * w k = v).card = p ^ (D - 1) := by
  classical
  obtain ⟨k0, hk0⟩ : ∃ k, c k ≠ 0 := by
    by_contra h; push_neg at h; exact hc (funext h)
  have hD : 1 ≤ D := by have := k0.isLt; omega
  have hshift : ∀ v, (Finset.univ.filter fun w : Fin D → ZMod p => ∑ k, c k * w k = v).card =
      (Finset.univ.filter fun w : Fin D → ZMod p => ∑ k, c k * w k = 0).card := by
    intro v
    set t : Fin D → ZMod p := Pi.single k0 (v * (c k0)⁻¹) with ht
    have hsum : ∀ w : Fin D → ZMod p, ∑ k, c k * (w + t) k = ∑ k, c k * w k + v := by
      intro w
      simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]
      congr 1
      rw [Finset.sum_eq_single k0]
      · rw [ht, Pi.single_eq_same, mul_comm v, ← mul_assoc, mul_inv_cancel₀ hk0, one_mul]
      · intro b _ hb; rw [ht, Pi.single_eq_of_ne hb, mul_zero]
      · simp
    refine Finset.card_bij (fun w _ => w - t) ?_ ?_ ?_
    · intro w hw
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hw ⊢
      have := hsum (w - t); rw [sub_add_cancel, hw] at this
      linear_combination -this
    · intro a _ b _ h; simpa using h
    · intro b hb
      refine ⟨b + t, ?_, by simp⟩
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hb ⊢
      rw [hsum, hb, zero_add]
  have htot : p ^ D = p * (Finset.univ.filter fun w : Fin D → ZMod p => ∑ k, c k * w k = 0).card := by
    have h := Finset.card_eq_sum_card_fiberwise (s := (Finset.univ : Finset (Fin D → ZMod p)))
      (t := (Finset.univ : Finset (ZMod p))) (f := fun w => ∑ k, c k * w k) (fun _ _ => Finset.mem_univ _)
    rw [Finset.card_univ, Fintype.card_fun, ZMod.card, Fintype.card_fin] at h
    rw [h, Finset.sum_congr rfl (fun v _ => hshift v), Finset.sum_const, Finset.card_univ,
      ZMod.card, smul_eq_mul]
  rw [hshift]
  have hp : 0 < p := (Fact.out : p.Prime).pos
  have : p ^ D = p * p ^ (D - 1) := by rw [← pow_succ']; congr 1; omega
  rw [this] at htot
  exact (Nat.eq_of_mul_eq_mul_left hp htot).symm

/-- **The HDR distribution lives on few strings.** The pushforward of the torus has
at most `p^D` points of `{0,1}^N` in its support, whatever `N`. -/
theorem hdr_support {D N L : ℕ} [NeZero L] (c : Fin N → Fin D → ZMod L) (θ : Fin N → ℕ) :
    (Finset.univ.image (thresh c θ)).card ≤ L ^ D := by
  calc (Finset.univ.image (thresh c θ)).card ≤ (Finset.univ : Finset (Fin D → ZMod L)).card :=
        Finset.card_image_le
    _ = L ^ D := by simp [ZMod.card]

end Distribution

section Degree

/-- The algebraic normal form over `F₂`: the coefficient of the monomial `S` of a
function on subsets of `Fin N` (Möbius inversion on the Boolean lattice). -/
def anf {N : ℕ} (f : Finset (Fin N) → ZMod 2) (S : Finset (Fin N)) : ZMod 2 :=
  ∑ T ∈ S.powerset, f T

/-- **The normal form represents the function.** -/
theorem anf_reconstruct {N : ℕ} (f : Finset (Fin N) → ZMod 2) (x : Finset (Fin N)) :
    ∑ S ∈ x.powerset, anf f S = f x := by
  unfold anf
  rw [Finset.sum_comm' (t' := x.powerset) (s' := fun T => Finset.Icc T x)]
  · rw [← Finset.add_sum_erase _ _ (Finset.mem_powerset.mpr (subset_refl x))]
    have hz : ∑ T ∈ x.powerset.erase x, ∑ _S ∈ Finset.Icc T x, f T = 0 := by
      refine Finset.sum_eq_zero fun T hT => ?_
      have hTx : T ⊆ x := Finset.mem_powerset.mp (Finset.mem_of_mem_erase hT)
      have hne : T ≠ x := Finset.ne_of_mem_erase hT
      rw [Finset.sum_const, Finset.card_Icc_finset hTx, nsmul_eq_mul]
      have hlt : T.card < x.card := Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨hTx, hne⟩)
      obtain ⟨k, hk⟩ : ∃ k, x.card - T.card = k + 1 := ⟨x.card - T.card - 1, by omega⟩
      rw [hk]; push_cast
      have h2 : (2 : ZMod 2) = 0 := by decide
      rw [pow_succ, h2]; ring
    rw [hz, add_zero, Finset.Icc_self, Finset.sum_singleton]
  · intro S T
    simp only [Finset.mem_powerset, Finset.mem_Icc, Finset.le_eq_subset]
    constructor
    · rintro ⟨hS, hT⟩; exact ⟨⟨hT, hS⟩, hT.trans hS⟩
    · rintro ⟨⟨hT, hS⟩, _⟩; exact ⟨hS, hT⟩

/-- The `F₂`-degree: the largest monomial with a nonzero coefficient. -/
def anfDeg {N : ℕ} (f : Finset (Fin N) → ZMod 2) : ℕ :=
  ((Finset.univ : Finset (Finset (Fin N))).filter fun S => anf f S ≠ 0).sup Finset.card

theorem le_anfDeg {N : ℕ} (f : Finset (Fin N) → ZMod 2) (S : Finset (Fin N)) (h : anf f S ≠ 0) :
    S.card ≤ anfDeg f :=
  Finset.le_sup (f := Finset.card) (by simp [h])

/-- **AND has full degree.** The conjunction of `N` bits, computed by `N - 1` gates,
has `F₂`-degree `N`. -/
theorem and_full_degree (N : ℕ) :
    N ≤ anfDeg (fun S : Finset (Fin N) => if S = Finset.univ then (1 : ZMod 2) else 0) := by
  have h : anf (fun S : Finset (Fin N) => if S = Finset.univ then (1 : ZMod 2) else 0)
      Finset.univ = 1 := by
    unfold anf
    rw [Finset.sum_ite_eq' (Finset.univ.powerset) Finset.univ]
    simp
  have := le_anfDeg _ Finset.univ (by rw [h]; decide)
  simpa using this

/-- **XOR-SAT is not of degree one.** The system `0 = y_i (i ∈ M)` is solvable iff the
instance bits on `M` vanish; this decision function has `F₂`-degree at least `|M|`. -/
theorem xorsat_degree {N : ℕ} (M : Finset (Fin N)) :
    M.card ≤ anfDeg (fun S : Finset (Fin N) => if S ∩ M = ∅ then (1 : ZMod 2) else 0) := by
  have h : anf (fun S : Finset (Fin N) => if S ∩ M = ∅ then (1 : ZMod 2) else 0) M = 1 := by
    unfold anf
    rw [Finset.sum_congr rfl (g := fun T => if T = ∅ then (1 : ZMod 2) else 0)]
    · rw [Finset.sum_ite_eq' M.powerset ∅]; simp
    · intro T hT
      show (if T ∩ M = ∅ then (1 : ZMod 2) else 0) = _
      rw [Finset.inter_eq_left.mpr (Finset.mem_powerset.mp hT)]
  exact le_anfDeg _ M (by rw [h]; decide)

end Degree


section Restricted

open DTree

/-- The input bits read along the path of `V` in a decision tree. -/
def DTree.pathQ {α β : Type*} [DecidableEq α] : DTree α β → (α → Bool) → Finset α
  | leaf _, _ => ∅
  | node q t0 t1, V => insert q (if V q then t1.pathQ V else t0.pathQ V)

theorem DTree.pathQ_card_le {α β : Type*} [DecidableEq α] (t : DTree α β) (V : α → Bool) :
    (t.pathQ V).card ≤ t.depth := by
  induction t with
  | leaf b => simp [pathQ, depth]
  | node q t0 t1 ih0 ih1 =>
    simp only [pathQ, depth]
    refine (Finset.card_insert_le _ _).trans ?_
    split_ifs
    · have := ih1; have := le_max_right t0.depth t1.depth; omega
    · have := ih0; have := le_max_left t0.depth t1.depth; omega

/-- Inputs that agree on the bits read along a path give the same answer. -/
theorem DTree.eval_eq_of_agree {α β : Type*} [DecidableEq α] (t : DTree α β) (V W : α → Bool)
    (h : ∀ q ∈ t.pathQ V, V q = W q) : t.eval V = t.eval W := by
  induction t with
  | leaf b => rfl
  | node q t0 t1 ih0 ih1 =>
    have hq : V q = W q := h q (by simp [pathQ])
    simp only [eval, ← hq]
    split_ifs with hv
    · exact ih1 fun r hr => h r (by simp [pathQ, hv, hr])
    · exact ih0 fun r hr => h r (by simp [pathQ, hv, hr])

/-- The sensitivity of `f` at `x`: the number of bits whose flip changes the answer. -/
def sens {N : ℕ} (f : (Fin N → Bool) → Bool) (x : Fin N → Bool) : ℕ :=
  (Finset.univ.filter fun i => f (Function.update x i (!x i)) ≠ f x).card

/-- **Decision trees: one bit per query.** A tree that computes `f` reads every
sensitive bit along the path of every input, so its depth is at least the
sensitivity of `f` at every point. -/
theorem depth_ge_sens {N : ℕ} (f : (Fin N → Bool) → Bool) (t : DTree (Fin N) Bool)
    (ht : ∀ V, t.eval V = f V) (x : Fin N → Bool) : sens f x ≤ t.depth := by
  refine le_trans (Finset.card_le_card ?_) (t.pathQ_card_le x)
  intro i hi
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
  by_contra hni
  apply hi
  rw [← ht, ← ht]
  refine (t.eval_eq_of_agree x _ fun q hq => ?_).symm
  have : q ≠ i := fun h => hni (h ▸ hq)
  rw [Function.update_of_ne this]

/-- Parity as a Boolean function. -/
def parB {N : ℕ} (x : Fin N → Bool) : Bool := decide (parity x = 1)

theorem parB_flip {N : ℕ} (x : Fin N → Bool) (j : Fin N) :
    parB (Function.update x j (!x j)) ≠ parB x := by
  unfold parB
  rw [parity_flip]
  have key : ∀ a : ZMod 2, decide (a + 1 = 1) ≠ decide (a = 1) := by decide
  exact key _

/-- **Parity needs every bit.** Every decision tree for parity of `N` bits has depth
at least `N`. -/
theorem parity_depth {N : ℕ} (t : DTree (Fin N) Bool) (ht : ∀ V, t.eval V = parB V) :
    N ≤ t.depth := by
  have h := depth_ge_sens parB t ht (fun _ => false)
  have hs : sens parB (fun _ : Fin N => false) = N := by
    unfold sens
    rw [Finset.filter_true_of_mem fun i _ => parB_flip _ i]
    simp
  omega

/-- A term of a DNF: a partial assignment. -/
def Consistent {N : ℕ} (x : Fin N → Bool) (τ : Fin N → Option Bool) : Prop :=
  ∀ i b, τ i = some b → x i = b

/-- **Depth two: every term of a DNF for parity fixes every bit.** -/
theorem parity_term_total {N : ℕ} (τ : Fin N → Option Bool)
    (himp : ∀ x, Consistent x τ → parB x = true) : ∀ j, τ j ≠ none := by
  intro j hj
  set x0 : Fin N → Bool := fun i => (τ i).getD false with hx0
  have hc0 : Consistent x0 τ := by
    intro i b hb; simp [hx0, hb]
  have hc1 : Consistent (Function.update x0 j (!x0 j)) τ := by
    intro i b hb
    have hij : i ≠ j := fun h => by rw [h, hj] at hb; exact absurd hb (by simp)
    rw [Function.update_of_ne hij]; exact hc0 i b hb
  exact parB_flip x0 j ((himp _ hc1).trans (himp _ hc0).symm)

/-- Flipping one bit is an involution exchanging the odd and the even strings, so
parity is `1` on exactly half of the cube. -/
theorem parity_ones {N : ℕ} (hN : 1 ≤ N) :
    2 * (Finset.univ.filter fun x : Fin N → Bool => parB x = true).card = 2 ^ N := by
  classical
  let j : Fin N := ⟨0, hN⟩
  let flip : (Fin N → Bool) → (Fin N → Bool) := fun x => Function.update x j (!x j)
  have hflip : ∀ x, flip (flip x) = x := by
    intro x; funext i
    by_cases hi : i = j
    · subst hi; simp [flip]
    · simp [flip, Function.update_of_ne hi]
  have hpar : ∀ x, parB (flip x) = !parB x := by
    intro x; have := parB_flip x j
    cases h : parB x <;> simp_all [flip]
  have hcard : (Finset.univ.filter fun x : Fin N → Bool => parB x = true).card =
      (Finset.univ.filter fun x : Fin N → Bool => ¬ parB x = true).card := by
    refine Finset.card_bij (fun x _ => flip x) ?_ ?_ ?_
    · intro x hx; simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
      rw [hpar, hx]; simp
    · intro a _ b _ h; rw [← hflip a, h, hflip]
    · intro y hy
      refine ⟨flip y, ?_, hflip y⟩
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy ⊢
      rw [hpar]; simpa using hy
  have htot := Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset (Fin N → Bool))) (fun x => parB x = true)
  rw [Finset.card_univ, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin] at htot
  omega

/-- **Depth two: a DNF for parity has at least `2^(N-1)` terms.** -/
theorem parity_dnf_size {N : ℕ} (hN : 1 ≤ N) (D : Finset (Fin N → Option Bool))
    (hD : ∀ x, parB x = true ↔ ∃ τ ∈ D, Consistent x τ) : 2 ^ (N - 1) ≤ D.card := by
  classical
  have himp : ∀ τ ∈ D, ∀ x, Consistent x τ → parB x = true :=
    fun τ hτ x hx => (hD x).2 ⟨τ, hτ, hx⟩
  have hones := parity_ones hN
  choose! pick hpick hcons using fun x (hx : parB x = true) => (hD x).1 hx
  have hinj : Set.InjOn pick (Finset.univ.filter fun x : Fin N → Bool => parB x = true) := by
    intro x hx y hy hxy
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hx hy
    have htot := parity_term_total (pick x) (himp _ (hpick x hx))
    funext i
    obtain ⟨b, hb⟩ := Option.ne_none_iff_exists'.mp (htot i)
    rw [hcons x hx i b hb, hcons y hy i b (hxy ▸ hb)]
  have hle := Finset.card_le_card_of_injOn pick (fun x hx => by
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq,
      Finset.mem_filter] at hx
    exact hpick x hx) hinj
  have : 2 ^ N = 2 * 2 ^ (N - 1) := by rw [← pow_succ']; congr 1; omega
  omega

end Restricted


section Communication

/-- A `1`-rectangle of a matrix `M : α → β → Bool`: a product set on which `M = 1`. -/
def IsOneRect {α β : Type*} (M : α → β → Bool) (R : Finset α × Finset β) : Prop :=
  ∀ a ∈ R.1, ∀ b ∈ R.2, M a b = true

/-- A fooling set: pairs on which `M = 1` such that any two of them are separated by
a `0` on a crossed entry. -/
def IsFooling {α β : Type*} (M : α → β → Bool) (F : Finset (α × β)) : Prop :=
  (∀ p ∈ F, M p.1 p.2 = true) ∧
    ∀ p ∈ F, ∀ q ∈ F, p ≠ q → M p.1 q.2 = false ∨ M q.1 p.2 = false

/-- **The fooling-set bound.** A `1`-rectangle contains at most one pair of a fooling
set, so any cover of the `1`s by `1`-rectangles has at least `|F|` rectangles, and
any deterministic protocol needs at least `log₂ |F|` bits. -/
theorem fooling_rect_le_one {α β : Type*} [DecidableEq α] [DecidableEq β]
    (M : α → β → Bool) (F : Finset (α × β)) (hF : IsFooling M F)
    (R : Finset α × Finset β) (hR : IsOneRect M R) :
    (F.filter fun p => p.1 ∈ R.1 ∧ p.2 ∈ R.2).card ≤ 1 := by
  rw [Finset.card_le_one]
  intro p hp q hq
  simp only [Finset.mem_filter] at hp hq
  by_contra hne
  rcases hF.2 p hp.1 q hq.1 hne with h | h
  · rw [hR _ hp.2.1 _ hq.2.2] at h; exact Bool.noConfusion h
  · rw [hR _ hq.2.1 _ hp.2.2] at h; exact Bool.noConfusion h

theorem fooling_cover {α β : Type*} [DecidableEq α] [DecidableEq β]
    (M : α → β → Bool) (F : Finset (α × β)) (hF : IsFooling M F)
    (C : Finset (Finset α × Finset β)) (hC : ∀ R ∈ C, IsOneRect M R)
    (hcov : ∀ p ∈ F, ∃ R ∈ C, p.1 ∈ R.1 ∧ p.2 ∈ R.2) : F.card ≤ C.card := by
  classical
  choose! g hg hmem using hcov
  have hinj : Set.InjOn g F := by
    intro p hp q hq hpq
    by_contra hne
    have h1 := fooling_rect_le_one M F hF (g p) (hC _ (hg p hp))
    have hp' : p ∈ F.filter fun r => r.1 ∈ (g p).1 ∧ r.2 ∈ (g p).2 :=
      Finset.mem_filter.mpr ⟨hp, hmem p hp⟩
    have hq' : q ∈ F.filter fun r => r.1 ∈ (g p).1 ∧ r.2 ∈ (g p).2 :=
      Finset.mem_filter.mpr ⟨hq, hpq ▸ hmem q hq⟩
    exact hne (Finset.card_le_one.mp h1 p hp' q hq')
  exact Finset.card_le_card_of_injOn g (fun p hp => hg p hp) hinj

/-- **A fooling set is at most the number of rows.** Two pairs of a fooling set never
share a row, so a single fixed partition of the input gives at most `log₂` of the
number of rows: linear in the input length. -/
theorem fooling_le_rows {α β : Type*} [Fintype α] [DecidableEq α] [DecidableEq β]
    (M : α → β → Bool) (F : Finset (α × β)) (hF : IsFooling M F) :
    F.card ≤ Fintype.card α := by
  have hinj : Set.InjOn (Prod.fst : α × β → α) (F : Set (α × β)) := by
    intro p hp q hq h
    by_contra hne
    rcases hF.2 p hp q hq hne with h1 | h1
    · have := hF.1 q hq; rw [← h] at this; rw [this] at h1; exact Bool.noConfusion h1
    · have := hF.1 p hp; rw [h] at this; rw [this] at h1; exact Bool.noConfusion h1
  calc F.card ≤ (Finset.univ : Finset α).card :=
        Finset.card_le_card_of_injOn Prod.fst (fun _ _ => Finset.mem_univ _) hinj
    _ = Fintype.card α := Finset.card_univ

end Communication


section TruthTablePolymorphism

/-- The clause-selection encoding: a base CNF and the selected clauses `sel r` for
`y r = true`. -/
def selectCNF {V : Type*} {N : ℕ} (base : CNF V) (sel : Fin N → List (V × Bool))
    (y : Fin N → Bool) : CNF V :=
  ⟨base.clauses ++ (List.finRange N).filterMap fun r => if y r then some (sel r) else none⟩

/-- **The satisfiable instances are closed under AND.** In the clause-selection
encoding, fewer clauses keep a formula satisfiable, so the set of satisfiable
instance strings is closed under the coordinatewise meet: at the level of the
truth table, 3-SAT has the semilattice polymorphism of Horn-SAT. -/
theorem select_sat_meet {V : Type*} {N : ℕ} (base : CNF V) (sel : Fin N → List (V × Bool))
    (y y' : Fin N → Bool) (h : ∃ a, (selectCNF base sel y).Sat a) :
    ∃ a, (selectCNF base sel (fun r => y r && y' r)).Sat a := by
  obtain ⟨a, ha⟩ := h
  refine ⟨a, fun c hc => ha c ?_⟩
  simp only [selectCNF, List.mem_append, List.mem_filterMap, List.mem_finRange, true_and] at hc ⊢
  rcases hc with hc | ⟨r, hr⟩
  · exact Or.inl hc
  · right; refine ⟨r, ?_⟩
    by_cases h1 : y r = true
    · simp only [h1, Bool.true_and] at hr
      split_ifs at hr with h2
      · simp only [Option.some.injEq] at hr; simp [h1, hr]
    · simp [Bool.eq_false_iff.mpr h1] at hr

/-- **The witness matrix is a containment matrix.** An assignment satisfies the
selected formula iff it satisfies the base and every selected clause: the row of
`x` in `W[x, y]` is the indicator of the instances `y` contained in the set of
clauses `x` satisfies. -/
theorem select_sat_iff {V : Type*} {N : ℕ} (base : CNF V) (sel : Fin N → List (V × Bool))
    (y : Fin N → Bool) (a : V → Bool) :
    (selectCNF base sel y).Sat a ↔
      base.Sat a ∧ ∀ r, y r = true → ∃ l ∈ sel r, a l.1 = l.2 := by
  simp only [CNF.Sat, selectCNF, List.mem_append, List.mem_filterMap, List.mem_finRange, true_and]
  constructor
  · intro h
    refine ⟨fun c hc => h c (Or.inl hc), fun r hr => h (sel r) (Or.inr ⟨r, by simp [hr]⟩)⟩
  · rintro ⟨h1, h2⟩ c (hc | ⟨r, hr⟩)
    · exact h1 c hc
    · by_cases hy : y r = true
      · simp only [hy, if_true, Option.some.injEq] at hr; subst hr; exact h2 r hy
      · simp [Bool.eq_false_iff.mpr hy] at hr

/-- **Polarity-encoded XOR-SAT keeps its polymorphism.** If `x`, `x'`, `x''` satisfy a
parity constraint on the variables `a, b, c` with right-hand sides `r`, `r'`, `r''`,
then `x ⊕ x' ⊕ x''` satisfies it with right-hand side `r ⊕ r' ⊕ r''`: the
satisfiable right-hand sides form a set closed under minority. -/
theorem xor_rhs_minority {V : Type*} (a b c : V) (x x' x'' : V → Bool) (r r' r'' : Bool)
    (h : xor (xor (x a) (x b)) (x c) = r) (h' : xor (xor (x' a) (x' b)) (x' c) = r')
    (h'' : xor (xor (x'' a) (x'' b)) (x'' c) = r'') :
    xor (xor (xor (xor (x a) (x' a)) (x'' a)) (xor (xor (x b) (x' b)) (x'' b)))
      (xor (xor (x c) (x' c)) (x'' c)) = xor (xor r r') r'' := by
  subst h h' h''
  generalize x a = p1; generalize x b = p2; generalize x c = p3
  generalize x' a = q1; generalize x' b = q2; generalize x' c = q3
  generalize x'' a = s1; generalize x'' b = s2; generalize x'' c = s3
  revert p1 p2 p3 q1 q2 q3 s1 s2 s3
  decide

end TruthTablePolymorphism


section Circuits

/-- The three gates: AND, OR, NOT (NOT ignores its second wire). -/
def opB : Fin 3 → Bool → Bool → Bool
  | 0 => fun a b => a && b
  | 1 => fun a b => a || b
  | 2 => fun a _ => !a

/-- Appending one gate, reading two earlier wires, to the list of wire values. -/
def step (L : List Bool) (g : Fin 3 × ℕ × ℕ) : List Bool :=
  L ++ [opB g.1 (L.getD g.2.1 false) (L.getD g.2.2 false)]

/-- The wire values of a straight-line program (a circuit) on input `x`: the inputs,
then one value per gate. -/
def wires {N : ℕ} (x : Fin N → Bool) (P : List (Fin 3 × ℕ × ℕ)) : List Bool :=
  P.foldl step (List.ofFn x)

theorem foldl_step_length (L : List Bool) (Q : List (Fin 3 × ℕ × ℕ)) :
    (Q.foldl step L).length = L.length + Q.length := by
  induction Q generalizing L with
  | nil => simp
  | cons g Q ih => simp only [List.foldl, ih, step, List.length_append, List.length_singleton,
      List.length_cons, List.length_nil]; omega

theorem wires_length {N : ℕ} (x : Fin N → Bool) (P : List (Fin 3 × ℕ × ℕ)) :
    (wires x P).length = N + P.length := by
  simp [wires, foldl_step_length]

theorem wires_snoc {N : ℕ} (x : Fin N → Bool) (P : List (Fin 3 × ℕ × ℕ)) (g : Fin 3 × ℕ × ℕ) :
    wires x (P ++ [g]) = step (wires x P) g := by
  simp [wires, List.foldl_append]

/-- A program computes `f` if some wire carries `f` on every input. -/
def Computes {N : ℕ} (P : List (Fin 3 × ℕ × ℕ)) (f : (Fin N → Bool) → Bool) : Prop :=
  ∃ i < N + P.length, ∀ x, (wires x P).getD i false = f x

/-- **Circuit complexity rises by at most one per gate.** Appending one gate to a
program keeps every function it computes and adds the gate's function: the least
size of a program computing a set of functions grows by at most one when one
gate on two of them is added. -/
theorem gate_cap {N : ℕ} (P : List (Fin 3 × ℕ × ℕ)) (o : Fin 3) {g h : (Fin N → Bool) → Bool}
    {i j : ℕ} (hi : i < N + P.length) (hg : ∀ x, (wires x P).getD i false = g x)
    (hj : j < N + P.length) (hh : ∀ x, (wires x P).getD j false = h x) :
    (∀ f : (Fin N → Bool) → Bool, Computes P f → Computes (P ++ [(o, i, j)]) f) ∧
      Computes (P ++ [(o, i, j)]) (fun x => opB o (g x) (h x)) ∧
      (P ++ [(o, i, j)]).length = P.length + 1 := by
  refine ⟨?_, ?_, by simp⟩
  · rintro f ⟨k, hk, hf⟩
    refine ⟨k, by simp; omega, fun x => ?_⟩
    rw [wires_snoc, step, List.getD_append _ _ _ _ (by rw [wires_length]; exact hk), hf]
  · refine ⟨N + P.length, by simp, fun x => ?_⟩
    have hl := wires_length x P
    rw [wires_snoc, step, List.getD_append_right _ _ _ _ (by omega), hl, Nat.sub_self, hg, hh]
    rfl

theorem foldl_step_prefix (L : List Bool) (Q : List (Fin 3 × ℕ × ℕ)) :
    ∃ T, Q.foldl step L = L ++ T := by
  induction Q generalizing L with
  | nil => exact ⟨[], by simp⟩
  | cons g Q ih =>
    obtain ⟨T, hT⟩ := ih (step L g)
    refine ⟨[opB g.1 (L.getD g.2.1 false) (L.getD g.2.2 false)] ++ T, ?_⟩
    rw [List.foldl_cons, hT, step, List.append_assoc]

/-- The full wire state of a program on input `x`. -/
def evalAll {N : ℕ} (P : List (Fin 3 × ℕ × ℕ)) (x : Fin N → Bool) : Fin (N + P.length) → Bool :=
  fun i => (wires x P).getD i false

theorem evalAll_input {N : ℕ} (P : List (Fin 3 × ℕ × ℕ)) (x : Fin N → Bool) (i : Fin N) :
    evalAll P x ⟨i, by omega⟩ = x i := by
  obtain ⟨T, hT⟩ := foldl_step_prefix (List.ofFn x) P
  simp only [evalAll, wires, hT]
  rw [List.getD_append _ _ _ _ (by simp)]
  simp

/-- **Extension variables add no states.** The wire state determines the input, so
the map from inputs to full wire states is injective. -/
theorem ext_embedding_injective {N : ℕ} (P : List (Fin 3 × ℕ × ℕ)) :
    Function.Injective (evalAll (N := N) P) := by
  intro x y h
  funext i
  rw [← evalAll_input P x i, ← evalAll_input P y i, h]

/-- The `2^N` inputs give exactly `2^N` wire states in `{0,1}^(N+s)`: extension
embeds the cube without adding states or entropy. -/
theorem ext_card_invariant {N : ℕ} (P : List (Fin 3 × ℕ × ℕ)) :
    (Finset.univ.image (evalAll (N := N) P)).card = 2 ^ N := by
  rw [Finset.card_image_of_injective _ (ext_embedding_injective P)]
  simp

/-- A program computes `f` on a set `S` of inputs (don't-cares outside `S`). -/
def ComputesOn {N : ℕ} (P : List (Fin 3 × ℕ × ℕ)) (f : (Fin N → Bool) → Bool)
    (S : Set (Fin N → Bool)) : Prop :=
  ∃ i < N + P.length, ∀ x ∈ S, (wires x P).getD i false = f x

/-- The least number of gates of a program computing `f` on `S`. -/
noncomputable def minCircuitSize {N : ℕ} (f : (Fin N → Bool) → Bool) (S : Set (Fin N → Bool)) : ℕ :=
  sInf {k | ∃ P : List (Fin 3 × ℕ × ℕ), P.length = k ∧ ComputesOn P f S}

/-- **Don't-cares can only help.** On a smaller set of inputs the least circuit size
can only drop (when `f` is computable on the larger set at all). -/
theorem minCircuitSize_mono {N : ℕ} (f : (Fin N → Bool) → Bool) {S S' : Set (Fin N → Bool)}
    (hS : S' ⊆ S) (h : ∃ P, ComputesOn P f S) : minCircuitSize f S' ≤ minCircuitSize f S := by
  obtain ⟨P, hP⟩ := h
  have hne : {k | ∃ Q : List (Fin 3 × ℕ × ℕ), Q.length = k ∧ ComputesOn Q f S}.Nonempty :=
    ⟨P.length, P, rfl, hP⟩
  obtain ⟨Q, hQ, i, hi, hf⟩ := Nat.sInf_mem hne
  exact Nat.sInf_le ⟨Q, hQ, i, hi, fun x hx => hf x (hS hx)⟩

theorem computesOn_nil {N : ℕ} (f : (Fin N → Bool) → Bool) (S : Set (Fin N → Bool)) :
    ComputesOn [] f S ↔ ∃ i : Fin N, ∀ x ∈ S, x i = f x := by
  constructor
  · rintro ⟨i, hi, hf⟩
    refine ⟨⟨i, by simpa using hi⟩, fun x hx => ?_⟩
    have := hf x hx
    simpa [wires, List.getD_eq_getElem?_getD, show i < N by simpa using hi] using this
  · rintro ⟨i, hf⟩
    refine ⟨i, by simp, fun x hx => ?_⟩
    simp [wires, List.getD_eq_getElem?_getD, hf x hx]

/-- **Size zero means a projection.** When `f` is computable on `S`, its least
circuit size there is `0` exactly when `f` agrees with one input bit on `S`. -/
theorem minCircuitSize_eq_zero_iff {N : ℕ} (f : (Fin N → Bool) → Bool) (S : Set (Fin N → Bool))
    (h : ∃ P, ComputesOn P f S) :
    minCircuitSize f S = 0 ↔ ∃ i : Fin N, ∀ x ∈ S, x i = f x := by
  obtain ⟨P, hP⟩ := h
  have hne : {k | ∃ P : List (Fin 3 × ℕ × ℕ), P.length = k ∧ ComputesOn P f S}.Nonempty :=
    ⟨P.length, P, rfl, hP⟩
  constructor
  · intro h0
    have hmem := Nat.sInf_mem hne
    rw [show sInf _ = minCircuitSize f S from rfl, h0] at hmem
    obtain ⟨Q, hQ, hc⟩ := hmem
    rw [List.length_eq_zero_iff.mp hQ] at hc
    exact (computesOn_nil f S).1 hc
  · intro hi
    exact Nat.eq_zero_of_le_zero (Nat.sInf_le ⟨[], rfl, (computesOn_nil f S).2 hi⟩)

section Lookup

variable {N : ℕ}

theorem computesOn_append {P Q : List (Fin 3 × ℕ × ℕ)} {g : (Fin N → Bool) → Bool}
    {S : Set (Fin N → Bool)} (h : ComputesOn P g S) : ComputesOn (P ++ Q) g S := by
  obtain ⟨i, hi, hg⟩ := h
  refine ⟨i, by simp; omega, fun x hx => ?_⟩
  obtain ⟨T, hT⟩ := foldl_step_prefix (wires x P) Q
  have e : wires x (P ++ Q) = Q.foldl step (wires x P) := by simp [wires, List.foldl_append]
  rw [e, hT, List.getD_append _ _ _ _ (by rw [wires_length]; exact hi), hg x hx]

theorem computesOn_input (P : List (Fin 3 × ℕ × ℕ)) (i : Fin N) (S : Set (Fin N → Bool)) :
    ComputesOn P (fun x => x i) S :=
  ⟨i, by omega, fun x _ => evalAll_input P x i⟩

theorem computesOn_congr {P : List (Fin 3 × ℕ × ℕ)} {g g' : (Fin N → Bool) → Bool}
    {S : Set (Fin N → Bool)} (h : ∀ x ∈ S, g x = g' x) (hg : ComputesOn P g S) :
    ComputesOn P g' S := by
  obtain ⟨i, hi, hgi⟩ := hg
  exact ⟨i, hi, fun x hx => (hgi x hx).trans (h x hx)⟩

/-- One gate on two computed functions extends a program by one gate. -/
theorem extend_gate {P : List (Fin 3 × ℕ × ℕ)} {g h : (Fin N → Bool) → Bool}
    {S : Set (Fin N → Bool)} (o : Fin 3) (hg : ComputesOn P g S) (hh : ComputesOn P h S) :
    ∃ P' : List (Fin 3 × ℕ × ℕ), P'.length = P.length + 1 ∧
      (∀ u, ComputesOn P u S → ComputesOn P' u S) ∧
      ComputesOn P' (fun x => opB o (g x) (h x)) S := by
  obtain ⟨i, hi, hgi⟩ := hg
  obtain ⟨j, hj, hhj⟩ := hh
  refine ⟨P ++ [(o, i, j)], by simp, fun u hu => computesOn_append hu, N + P.length, by simp,
    fun x hx => ?_⟩
  have hl := wires_length x P
  rw [wires_snoc, step, List.getD_append_right _ _ _ _ (by omega), hl, Nat.sub_self, hgi x hx,
    hhj x hx]
  rfl

/-- The negations of the first `k` inputs, in `k` gates. -/
theorem lits_prog (S : Set (Fin N → Bool)) : ∀ k ≤ N, ∃ P : List (Fin 3 × ℕ × ℕ), P.length = k ∧
    ∀ i : Fin N, (i : ℕ) < k → ComputesOn P (fun x => !x i) S
  | 0, _ => ⟨[], rfl, fun i hi => absurd hi (Nat.not_lt_zero _)⟩
  | k + 1, hk => by
    obtain ⟨P, hP, hlit⟩ := lits_prog S k (by omega)
    have hin := computesOn_input P ⟨k, by omega⟩ S
    obtain ⟨P', hl, hpres, hnew⟩ := extend_gate 2 hin hin
    refine ⟨P', by rw [hl, hP], fun i hi => ?_⟩
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with h | h
    · exact hpres _ (hlit i h)
    · have e : i = ⟨k, by omega⟩ := Fin.ext h
      rw [e]
      exact computesOn_congr (fun x _ => rfl) hnew

theorem lit_computes {P : List (Fin 3 × ℕ × ℕ)} {S : Set (Fin N → Bool)}
    (hall : ∀ i : Fin N, ComputesOn P (fun x => !x i) S) (a : Fin N → Bool) (i : Fin N) :
    ComputesOn P (fun x => decide (x i = a i)) S := by
  cases ha : a i
  · exact computesOn_congr (fun x _ => by cases x i <;> rfl) (hall i)
  · exact computesOn_congr (fun x _ => by cases x i <;> rfl) (computesOn_input P i S)

/-- The minterm of a point `a` on its first `k + 1` coordinates, in `k` further gates. -/
theorem conj_prog {S : Set (Fin N → Bool)} (a : Fin N → Bool) (P : List (Fin 3 × ℕ × ℕ))
    (hall : ∀ i : Fin N, ComputesOn P (fun x => !x i) S) :
    ∀ k, k + 1 ≤ N → ∃ P' : List (Fin 3 × ℕ × ℕ), P'.length ≤ P.length + k ∧
      (∀ u, ComputesOn P u S → ComputesOn P' u S) ∧
      ComputesOn P' (fun x => decide (∀ i : Fin N, (i : ℕ) < k + 1 → x i = a i)) S
  | 0, hk => by
    refine ⟨P, le_refl _, fun u hu => hu, computesOn_congr (fun x _ => ?_)
      (lit_computes hall a ⟨0, by omega⟩)⟩
    apply Bool.eq_iff_iff.mpr
    simp only [decide_eq_true_eq]
    constructor
    · intro h i hi; have e : i = ⟨0, by omega⟩ := Fin.ext (by simp; omega); rw [e]; exact h
    · intro h; exact h _ (by simp)
  | k + 1, hk => by
    obtain ⟨P1, hl1, hp1, hc1⟩ := conj_prog a P hall k (by omega)
    have hlit := hp1 _ (lit_computes hall a ⟨k + 1, by omega⟩)
    obtain ⟨P2, hl2, hp2, hc2⟩ := extend_gate 0 hc1 hlit
    refine ⟨P2, by omega, fun u hu => hp2 _ (hp1 _ hu), computesOn_congr (fun x _ => ?_) hc2⟩
    show (decide _ && decide _) = _
    apply Bool.eq_iff_iff.mpr
    simp only [Bool.and_eq_true, decide_eq_true_eq]
    constructor
    · rintro ⟨h1, h2⟩ i hi
      rcases Nat.lt_succ_iff_lt_or_eq.mp hi with h | h
      · exact h1 i h
      · have e : i = ⟨k + 1, by omega⟩ := Fin.ext h
        rw [e]; exact h2
    · intro h; exact ⟨fun i hi => h i (by omega), h _ (by simp)⟩

/-- The disjunction of the minterms of a list of points. -/
theorem or_prog (hN : 1 ≤ N) {S : Set (Fin N → Bool)} (P : List (Fin 3 × ℕ × ℕ))
    (hall : ∀ i : Fin N, ComputesOn P (fun x => !x i) S) :
    ∀ L : List (Fin N → Bool), ∃ P' : List (Fin 3 × ℕ × ℕ),
      P'.length ≤ P.length + 1 + L.length * N ∧ (∀ u, ComputesOn P u S → ComputesOn P' u S) ∧
      ComputesOn P' (fun x => decide (∃ a ∈ L, ∀ i, x i = a i)) S
  | [] => by
    obtain ⟨P', hl, hp, hc⟩ := extend_gate 0 (computesOn_input P ⟨0, hN⟩ S) (hall ⟨0, hN⟩)
    refine ⟨P', by simp [hl], hp, computesOn_congr (fun x _ => ?_) hc⟩
    show (x ⟨0, hN⟩ && !x ⟨0, hN⟩) = _
    cases x ⟨0, hN⟩ <;> simp
  | a :: L => by
    obtain ⟨P1, hl1, hp1, hc1⟩ := or_prog hN P hall L
    obtain ⟨P2, hl2, hp2, hc2⟩ := conj_prog a P1 (fun i => hp1 _ (hall i)) (N - 1) (by omega)
    obtain ⟨P3, hl3, hp3, hc3⟩ := extend_gate 1 (hp2 _ hc1) hc2
    refine ⟨P3, ?_, fun u hu => hp3 _ (hp2 _ (hp1 _ hu)), computesOn_congr (fun x _ => ?_) hc3⟩
    · simp only [List.length_cons]
      have : N - 1 + 1 = N := by omega
      nlinarith
    · show (decide _ || decide _) = _
      apply Bool.eq_iff_iff.mpr
      simp only [Bool.or_eq_true, decide_eq_true_eq, List.mem_cons, exists_eq_or_imp]
      have e : (∀ i : Fin N, (i : ℕ) < N - 1 + 1 → x i = a i) ↔ ∀ i, x i = a i :=
        ⟨fun h i => h i (by omega), fun h i _ => h i⟩
      rw [e]; exact or_comm

/-- **The lookup circuit.** A function on a support of `m` strings of `N ≥ 1` bits is
computed there by a program of at most `N + 1 + m N` gates: negations, a constant,
one minterm and one OR per satisfying string. A generator with polynomially many
strings therefore admits polynomial-size circuits for every function on it. -/
theorem minCircuitSize_le_lookup (hN : 1 ≤ N) (f : (Fin N → Bool) → Bool)
    (S : Finset (Fin N → Bool)) :
    minCircuitSize f (S : Set (Fin N → Bool)) ≤ N + 1 + S.card * N := by
  classical
  obtain ⟨P0, hl0, hneg⟩ := lits_prog (S : Set (Fin N → Bool)) N le_rfl
  have hall : ∀ i : Fin N, ComputesOn P0 (fun x => !x i) (S : Set (Fin N → Bool)) :=
    fun i => hneg i i.2
  set L := (S.filter fun x => f x = true).toList with hL
  obtain ⟨P, hl, -, hc⟩ := or_prog hN P0 hall L
  have hcomp : ComputesOn P f (S : Set (Fin N → Bool)) := by
    refine computesOn_congr (fun x hx => ?_) hc
    apply Bool.eq_iff_iff.mpr
    simp only [decide_eq_true_eq, hL, Finset.mem_toList, Finset.mem_filter]
    constructor
    · rintro ⟨a, ⟨-, ha⟩, hxa⟩
      have : x = a := funext hxa
      rw [this]; exact ha
    · intro h; exact ⟨x, ⟨hx, h⟩, fun _ => rfl⟩
  have hLen : L.length ≤ S.card := by
    rw [hL, Finset.length_toList]; exact Finset.card_filter_le _ _
  calc minCircuitSize f (S : Set (Fin N → Bool)) ≤ P.length := Nat.sInf_le ⟨P, rfl, hcomp⟩
    _ ≤ N + 1 + S.card * N := by rw [hl0] at hl; nlinarith


/-- **The lookup program exists.** Every `f` has a program of at most `N + 1 + |S| N`
gates computing it on `S`. -/
theorem lookup_exists (hN : 1 ≤ N) (f : (Fin N → Bool) → Bool) (S : Finset (Fin N → Bool)) :
    ∃ P : List (Fin 3 × ℕ × ℕ), P.length ≤ N + 1 + S.card * N ∧
      ComputesOn P f (S : Set (Fin N → Bool)) := by
  classical
  obtain ⟨P0, hl0, hneg⟩ := lits_prog (S : Set (Fin N → Bool)) N le_rfl
  have hall : ∀ i : Fin N, ComputesOn P0 (fun x => !x i) (S : Set (Fin N → Bool)) :=
    fun i => hneg i i.2
  set L := (S.filter fun x => f x = true).toList with hL
  obtain ⟨P, hl, -, hc⟩ := or_prog hN P0 hall L
  have hcomp : ComputesOn P f (S : Set (Fin N → Bool)) := by
    refine computesOn_congr (fun x hx => ?_) hc
    apply Bool.eq_iff_iff.mpr
    simp only [decide_eq_true_eq, hL, Finset.mem_toList, Finset.mem_filter]
    constructor
    · rintro ⟨a, ⟨-, ha⟩, hxa⟩
      have : x = a := funext hxa
      rw [this]; exact ha
    · intro h; exact ⟨x, ⟨hx, h⟩, fun _ => rfl⟩
  have hLen : L.length ≤ S.card := by
    rw [hL, Finset.length_toList]; exact Finset.card_filter_le _ _
  exact ⟨P, by rw [hl0] at hl; nlinarith, hcomp⟩

/-- **The admissible locus is never empty at exponential size.** On all `2^N` inputs some
program of at most `N + 1 + 2^N N` gates computes `f`, the De Morgan expansion of its
truth table. -/
theorem valid_locus_nonempty (hN : 1 ≤ N) (f : (Fin N → Bool) → Bool) :
    ∃ P : List (Fin 3 × ℕ × ℕ), P.length ≤ N + 1 + 2 ^ N * N ∧ ComputesOn P f Set.univ := by
  obtain ⟨P, hl, hc⟩ := lookup_exists hN f Finset.univ
  refine ⟨P, ?_, by simpa using hc⟩
  have : (Finset.univ : Finset (Fin N → Bool)).card = 2 ^ N := by simp
  rwa [this] at hl

/-- **Empty locus is a lower bound.** No program of at most `s` gates computes `f` on `S`
exactly when `s` is below the least circuit size. With `f` the switchboard function of
3-SAT, emptiness for every polynomial `s` and all large `n` is `NP ⊄ P/poly`. -/
theorem valid_locus_empty_iff {N : ℕ} (f : (Fin N → Bool) → Bool) (S : Set (Fin N → Bool))
    (s : ℕ) (h : ∃ P, ComputesOn P f S) :
    (¬ ∃ P : List (Fin 3 × ℕ × ℕ), P.length ≤ s ∧ ComputesOn P f S) ↔
      s < minCircuitSize f S := by
  obtain ⟨P0, hP0⟩ := h
  have hne : {k | ∃ P : List (Fin 3 × ℕ × ℕ), P.length = k ∧ ComputesOn P f S}.Nonempty :=
    ⟨P0.length, P0, rfl, hP0⟩
  constructor
  · intro hno
    by_contra hle
    push_neg at hle
    obtain ⟨P, hl, hc⟩ := Nat.sInf_mem hne
    exact hno ⟨P, by unfold minCircuitSize at hle; omega, hc⟩
  · rintro hlt ⟨P, hl, hc⟩
    have : minCircuitSize f S ≤ P.length := Nat.sInf_le ⟨P, rfl, hc⟩
    omega

end Lookup

/-- A program of length `s` whose gates read wires below `N + s`. -/
def toProg {N s : ℕ} (P : Fin s → Fin 3 × Fin (N + s) × Fin (N + s)) : List (Fin 3 × ℕ × ℕ) :=
  List.ofFn fun t => ((P t).1, ((P t).2.1 : ℕ), ((P t).2.2 : ℕ))

/-- **Shannon's count.** Programs of `s` gates on `N` inputs compute at most
`(3(N+s)²)^s (N+s)` functions. -/
theorem shannon_count (N s : ℕ) :
    ((Finset.univ : Finset ((Fin s → Fin 3 × Fin (N + s) × Fin (N + s)) × Fin (N + s))).image
      fun pi => fun x : Fin N → Bool => (wires x (toProg pi.1)).getD pi.2 false).card ≤
      (3 * (N + s) ^ 2) ^ s * (N + s) := by
  refine Finset.card_image_le.trans (le_of_eq ?_)
  simp only [Finset.card_univ, Fintype.card_prod, Fintype.card_fun, Fintype.card_fin]
  ring

/-- **Most functions are hard.** If `(3(N+s)²)^s (N+s) < 2^(2^N)`, some function of
`N` bits is computed by no program of `s` gates: circuit complexity is large on
random truth tables. -/
theorem exists_hard_function (N s : ℕ) (h : (3 * (N + s) ^ 2) ^ s * (N + s) < 2 ^ 2 ^ N) :
    ∃ f : (Fin N → Bool) → Bool, ∀ P : Fin s → Fin 3 × Fin (N + s) × Fin (N + s),
      ∀ i : Fin (N + s), (fun x => (wires x (toProg P)).getD i false) ≠ f := by
  classical
  have hc : ((Finset.univ : Finset ((Fin s → Fin 3 × Fin (N + s) × Fin (N + s)) × Fin (N + s))).image
      fun pi => fun x : Fin N → Bool => (wires x (toProg pi.1)).getD pi.2 false).card <
      (Finset.univ : Finset ((Fin N → Bool) → Bool)).card := by
    simp only [Finset.card_univ, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]
    exact (shannon_count N s).trans_lt h
  obtain ⟨f, -, hf⟩ := Finset.exists_mem_notMem_of_card_lt_card hc
  refine ⟨f, fun P i he => hf ?_⟩
  exact Finset.mem_image.mpr ⟨(P, i), Finset.mem_univ _, he⟩

/-- An instance: some function of `6` bits needs more than `6` gates. -/
theorem hard_six : (3 * (6 + 6) ^ 2) ^ 6 * (6 + 6) < 2 ^ 2 ^ 6 := by norm_num

end Circuits


section AlgebraicBridge

/-- A Boolean as an element of `F₂`. -/
def b2 (b : Bool) : ZMod 2 := if b then 1 else 0

/-- The gates as polynomials over `F₂` of degree at most two: `AND = ab`,
`OR = a + b + ab`, `NOT = 1 + a`. -/
def opPoly : Fin 3 → ZMod 2 → ZMod 2 → ZMod 2
  | 0 => fun a b => a * b
  | 1 => fun a b => a + b + a * b
  | 2 => fun a _ => 1 + a

/-- **The extension encoding is faithful.** Each gate's value is its polynomial of
degree at most two evaluated at its inputs, so the equations `z_t = p_t(…)` have
the circuit's wire values as their unique Boolean solution. -/
theorem opPoly_faithful (o : Fin 3) (a b : Bool) : b2 (opB o a b) = opPoly o (b2 a) (b2 b) := by
  fin_cases o <;> cases a <;> cases b <;> decide

/-- **The Boolean Nullstellensatz over `F₂`.** In the ring of functions
`{0,1}^n → F₂` (the polynomials modulo `x_i² = x_i`), a family with no common zero
generates the unit ideal. -/
theorem bool_nullstellensatz {n m : ℕ} (f : Fin m → (Fin n → Bool) → ZMod 2)
    (h : ∀ x, ∃ i, f i x ≠ 0) : (1 : (Fin n → Bool) → ZMod 2) ∈ Ideal.span (Set.range f) := by
  classical
  choose c hc using h
  have hone : ∀ x, f (c x) x = 1 := by
    intro x
    have := hc x
    generalize f (c x) x = v at this ⊢
    fin_cases v
    · exact absurd rfl this
    · rfl
  let δ : (Fin n → Bool) → (Fin n → Bool) → ZMod 2 := fun a x => if x = a then 1 else 0
  have hsum : (1 : (Fin n → Bool) → ZMod 2) = ∑ a, δ a * f (c a) := by
    funext x
    simp only [Pi.one_apply, Finset.sum_apply, Pi.mul_apply, δ]
    rw [Finset.sum_eq_single x]
    · simp [hone x]
    · intro b _ hb; simp [Ne.symm hb]
    · simp
  rw [hsum]
  exact Ideal.sum_mem _ fun a _ => Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨c a, rfl⟩)

/-- **The circuit adds nothing to ideal membership.** If the constraints `f` have no
common Boolean zero, the unit ideal is already generated by `f`; adjoining any further
equations (such as a circuit's defining equations `g`) keeps it. What a circuit could
change is only the length of a derivation of `1`. -/
theorem unit_ideal_with_circuit {n m k : ℕ} (f : Fin m → (Fin n → Bool) → ZMod 2)
    (g : Fin k → (Fin n → Bool) → ZMod 2) (h : ∀ x, ∃ i, f i x ≠ 0) :
    (1 : (Fin n → Bool) → ZMod 2) ∈ Ideal.span (Set.range f ∪ Set.range g) :=
  Ideal.span_mono Set.subset_union_left (bool_nullstellensatz f h)

/-- The Tseitin chain of a clause: `z₀ = 1`, `z_{j+1} = z_j u_{j+1}`, each step a
degree-two equation, where `u_j = 1 + ℓ_j` is the falsity of the `j`-th literal. -/
def tseitinChain : List (ZMod 2) → ZMod 2 → ZMod 2
  | [], z => z
  | u :: us, z => tseitinChain us (z * u)

theorem tseitinChain_eq (us : List (ZMod 2)) (z : ZMod 2) : tseitinChain us z = z * us.prod := by
  induction us generalizing z with
  | nil => simp [tseitinChain]
  | cons u us ih => rw [tseitinChain, ih, List.prod_cons, mul_assoc]

/-- **The Tseitin reduction to degree two is faithful.** The chain of a clause ends at
`0` exactly when some literal is true: a clause of width `k` becomes `k - 1`
equations of degree two in `k - 2` new variables, with the same solutions. -/
theorem tseitinChain_sat (us : List (ZMod 2)) : tseitinChain us 1 = 0 ↔ ∃ u ∈ us, u = 0 := by
  rw [tseitinChain_eq, one_mul, List.prod_eq_zero_iff]
  exact ⟨fun h => ⟨0, h, rfl⟩, fun ⟨u, hu, h⟩ => h ▸ hu⟩

end AlgebraicBridge

section Approximants

/-- The Pell step for `√3`: `(p, q) ↦ (2p + 3q, p + 2q)`. -/
def pellStep (pq : ℕ × ℕ) : ℕ × ℕ := (2 * pq.1 + 3 * pq.2, pq.1 + 2 * pq.2)

/-- **Rational approximants of `√3` with exact error.** Starting from `(2, 1)`, every
Pell step keeps `p² - 3q² = 1`, so `(p/q)² - 3 = 1/q²` exactly, and `q` at least
doubles at each step. These are the commensurate approximants of the `30°` rotation
(`tan 30° = 1/√3`) in a periodic box. -/
theorem pell_invariant (pq : ℕ × ℕ) (h : pq.1 ^ 2 = 3 * pq.2 ^ 2 + 1) :
    (pellStep pq).1 ^ 2 = 3 * (pellStep pq).2 ^ 2 + 1 := by
  obtain ⟨p, q⟩ := pq
  simp only [pellStep] at h ⊢
  nlinarith [h]

theorem pell_error (p q : ℕ) (hq : 0 < q) (h : p ^ 2 = 3 * q ^ 2 + 1) :
    ((p : ℚ) / q) ^ 2 - 3 = 1 / (q : ℚ) ^ 2 := by
  have hq' : (q : ℚ) ≠ 0 := by exact_mod_cast hq.ne'
  have h' : (p : ℚ) ^ 2 = 3 * (q : ℚ) ^ 2 + 1 := by exact_mod_cast h
  field_simp
  linarith

theorem pell_growth (pq : ℕ × ℕ) : 2 * pq.2 ≤ (pellStep pq).2 ∧ pq.1 ≤ (pellStep pq).2 := by
  simp only [pellStep]; constructor <;> omega

theorem pell_iterates (k : ℕ) :
    ((pellStep)^[k] (2, 1)).1 ^ 2 = 3 * ((pellStep)^[k] (2, 1)).2 ^ 2 + 1 ∧
      2 ^ k ≤ ((pellStep)^[k] (2, 1)).2 := by
  induction k with
  | zero => norm_num
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    refine ⟨pell_invariant _ ih.1, ?_⟩
    have := (pell_growth ((pellStep)^[k] (2, 1))).1
    rw [pow_succ]; omega

end Approximants


section XorCircuits

/-- One XOR/NOT gate: `true` is XOR of two earlier wires, `false` is NOT of the first. -/
def xstep (L : List Bool) (g : Bool × ℕ × ℕ) : List Bool :=
  L ++ [if g.1 then xor (L.getD g.2.1 false) (L.getD g.2.2 false) else !(L.getD g.2.1 false)]

def xwires {N : ℕ} (x : Fin N → Bool) (P : List (Bool × ℕ × ℕ)) : List Bool :=
  P.foldl xstep (List.ofFn x)

/-- `F₂`-affine functions of the inputs. -/
def IsAffine {N : ℕ} (f : (Fin N → Bool) → Bool) : Prop :=
  ∃ (a : Fin N → ZMod 2) (b : ZMod 2), ∀ x, b2 (f x) = ∑ k, a k * b2 (x k) + b

theorem b2_xor (p q : Bool) : b2 (xor p q) = b2 p + b2 q := by
  cases p <;> cases q <;> decide

theorem b2_not (p : Bool) : b2 (!p) = 1 + b2 p := by cases p <;> decide

theorem isAffine_const_false {N : ℕ} : IsAffine (fun _ : Fin N → Bool => false) :=
  ⟨0, 0, fun x => by simp [b2]⟩

theorem xwires_snoc {N : ℕ} (x : Fin N → Bool) (P : List (Bool × ℕ × ℕ)) (g : Bool × ℕ × ℕ) :
    xwires x (P ++ [g]) = xstep (xwires x P) g := by
  simp [xwires, List.foldl_append]

theorem xwires_length {N : ℕ} (x : Fin N → Bool) (P : List (Bool × ℕ × ℕ)) :
    (xwires x P).length = N + P.length := by
  induction P using List.reverseRecOn with
  | nil => simp [xwires]
  | append_singleton P g ih => rw [xwires_snoc, xstep]; simp [ih]; ring

/-- **XOR circuits compute affine functions.** Every wire of a program of XOR and
NOT gates is an `F₂`-affine function of the inputs. -/
theorem xor_circuit_is_affine {N : ℕ} (P : List (Bool × ℕ × ℕ)) (i : ℕ) :
    IsAffine (fun x : Fin N → Bool => (xwires x P).getD i false) := by
  induction P using List.reverseRecOn generalizing i with
  | nil =>
    by_cases hi : i < N
    · refine ⟨fun k => if (k : ℕ) = i then 1 else 0, 0, fun x => ?_⟩
      simp only [xwires, List.foldl_nil, add_zero]
      rw [Finset.sum_eq_single ⟨i, hi⟩]
      · simp [List.getD_eq_getElem?_getD, hi, b2]
      · intro k _ hk
        have : (k : ℕ) ≠ i := fun h => hk (Fin.ext h)
        simp [this]
      · simp
    · refine ⟨0, 0, fun x => ?_⟩
      simp only [xwires, List.foldl_nil]
      rw [List.getD_eq_default _ _ (by simp; omega)]
      simp [b2]
  | append_singleton P g ih =>
    have hl : ∀ x : Fin N → Bool, (xwires x P).length = N + P.length := fun x => xwires_length x P
    by_cases hi : i < N + P.length
    · obtain ⟨a, b, h⟩ := ih i
      beta_reduce at h
      refine ⟨a, b, fun x => ?_⟩
      beta_reduce
      rw [xwires_snoc, xstep, List.getD_append _ _ _ _ (by rw [hl]; exact hi)]
      exact h x
    · by_cases he : i = N + P.length
      · obtain ⟨a1, c1, h1⟩ := ih g.2.1
        obtain ⟨a2, c2, h2⟩ := ih g.2.2
        beta_reduce at h1 h2
        cases hg : g.1
        · refine ⟨-a1, 1 - c1, fun x => ?_⟩
          beta_reduce
          rw [xwires_snoc, xstep, List.getD_append_right _ _ _ _ (by rw [hl]; omega), hl, he,
            Nat.sub_self]
          simp only [hg, Bool.false_eq_true, if_false, List.getD_cons_zero, b2_not, h1 x]
          simp only [Pi.neg_apply, neg_mul, Finset.sum_neg_distrib]
          have h2' : (1 : ZMod 2) + 1 = 0 := by decide
          linear_combination (∑ k, a1 k * b2 (x k) + c1) * h2'
        · refine ⟨a1 + a2, c1 + c2, fun x => ?_⟩
          beta_reduce
          rw [xwires_snoc, xstep, List.getD_append_right _ _ _ _ (by rw [hl]; omega), hl, he,
            Nat.sub_self]
          simp only [hg, if_true, List.getD_cons_zero, b2_xor, h1 x, h2 x, Pi.add_apply, add_mul,
            Finset.sum_add_distrib]
          ring
      · refine ⟨0, 0, fun x => ?_⟩
        beta_reduce
        rw [List.getD_eq_default _ _ (by rw [xwires_length]; simp; omega)]
        simp [b2]

/-- **On the cut-and-project generator, XOR circuits compute parities of strips.**
Every wire of an XOR/NOT program fed with the threshold bits `y_r(w)` is the parity
of the strip memberships of a set of cuts, plus a constant. -/
theorem xor_hdr_parity_strips {D N L : ℕ} (c : Fin N → Fin D → ZMod L) (θ : Fin N → ℕ)
    (P : List (Bool × ℕ × ℕ)) (i : ℕ) :
    ∃ (a : Fin N → ZMod 2) (b : ZMod 2), ∀ w : Fin D → ZMod L,
      b2 ((xwires (thresh c θ w) P).getD i false) = ∑ r, a r * b2 (thresh c θ w r) + b := by
  obtain ⟨a, b, h⟩ := xor_circuit_is_affine (N := N) P i
  exact ⟨a, b, fun w => h _⟩

/-- **XOR circuits cannot compute AND of two cuts.** If four points of the torus
agree on every cut except `r₀, r₁` and take all four values there, no XOR/NOT
program computes the conjunction of the two cuts. -/
theorem xor_cannot_and {D N L : ℕ} (c : Fin N → Fin D → ZMod L) (θ : Fin N → ℕ)
    {r₀ r₁ : Fin N} (hr : r₀ ≠ r₁) (w : Bool → Bool → Fin D → ZMod L)
    (hw : ∀ u v, thresh c θ (w u v) r₀ = u ∧ thresh c θ (w u v) r₁ = v)
    (hrest : ∀ u v r, r ≠ r₀ → r ≠ r₁ → thresh c θ (w u v) r = thresh c θ (w false false) r)
    (P : List (Bool × ℕ × ℕ)) (i : ℕ) :
    ¬ ∀ u v, (xwires (thresh c θ (w u v)) P).getD i false = (u && v) := by
  intro hand
  obtain ⟨a, b, h⟩ := xor_hdr_parity_strips c θ P i
  have key : ∀ u v, b2 (u && v) = a r₀ * b2 u + a r₁ * b2 v +
      (∑ r, a r * b2 (thresh c θ (w false false) r) - a r₀ * b2 false - a r₁ * b2 false) + b := by
    intro u v
    rw [← hand u v, h (w u v)]
    have hsplit : ∀ z : Fin D → ZMod L, ∑ r, a r * b2 (thresh c θ z r) =
        a r₀ * b2 (thresh c θ z r₀) + a r₁ * b2 (thresh c θ z r₁) +
          ∑ r ∈ (Finset.univ.erase r₀).erase r₁, a r * b2 (thresh c θ z r) := by
      intro z
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ r₀),
        ← Finset.add_sum_erase _ _ (Finset.mem_erase.mpr ⟨Ne.symm hr, Finset.mem_univ r₁⟩)]
      ring
    have hrest' : ∑ r ∈ (Finset.univ.erase r₀).erase r₁, a r * b2 (thresh c θ (w u v) r) =
        ∑ r ∈ (Finset.univ.erase r₀).erase r₁, a r * b2 (thresh c θ (w false false) r) :=
      Finset.sum_congr rfl fun r hr' => by
        rw [hrest u v r (Finset.ne_of_mem_erase (Finset.mem_of_mem_erase hr'))
          (Finset.ne_of_mem_erase hr')]
    rw [hsplit, hsplit (w false false), hrest', (hw u v).1, (hw u v).2, (hw false false).1,
      (hw false false).2]
    ring
  have k00 := key false false
  have k01 := key false true
  have k10 := key true false
  have k11 := key true true
  simp only [b2, Bool.false_and, Bool.true_and, Bool.and_false, Bool.and_true, if_false,
    if_true, Bool.false_eq_true] at k00 k01 k10 k11
  have : (1 : ZMod 2) = 0 := by linear_combination k11 - k01 - k10 + k00
  exact absurd this (by decide)

end XorCircuits


section Resolution

variable {n : ℕ}

/-- The resolvent of two clauses (sets of literals) on the variable `v`. -/
def resolvent (C D : Finset (Fin n × Bool)) (v : Fin n) : Finset (Fin n × Bool) :=
  C.erase (v, true) ∪ D.erase (v, false)

/-- **Two literals cancel.** The resolvent of two clauses of width at most two,
clashing on `v`, has width at most two. -/
theorem resolvent_width_two (C D : Finset (Fin n × Bool)) (v : Fin n)
    (hC : C.card ≤ 2) (hD : D.card ≤ 2) (hv : (v, true) ∈ C) (hv' : (v, false) ∈ D) :
    (resolvent C D v).card ≤ 2 := by
  unfold resolvent
  have h1 := Finset.card_erase_of_mem hv
  have h2 := Finset.card_erase_of_mem hv'
  have := Finset.card_union_le (C.erase (v, true)) (D.erase (v, false))
  omega

/-- **The width-two universe is polynomial.** There are at most
`1 + 2n + (2n)²` clauses of width at most two over `n` variables, so resolution
closes a 2-CNF within polynomially many clauses. -/
theorem width_two_clauses_card :
    ((Finset.univ : Finset (Finset (Fin n × Bool))).filter fun C => C.card ≤ 2).card ≤
      1 + 2 * n + (2 * n) ^ 2 := by
  classical
  have hsub : ((Finset.univ : Finset (Finset (Fin n × Bool))).filter fun C => C.card ≤ 2) ⊆
      (Finset.range 3).biUnion fun k => Finset.powersetCard k Finset.univ := by
    intro C hC
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hC
    simp only [Finset.mem_biUnion, Finset.mem_range, Finset.mem_powersetCard, Finset.subset_univ,
      true_and]
    exact ⟨C.card, by omega, rfl⟩
  refine (Finset.card_le_card hsub).trans ((Finset.card_biUnion_le).trans ?_)
  simp only [Finset.card_powersetCard, Finset.card_univ, Fintype.card_prod, Fintype.card_fin,
    Fintype.card_bool, Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose_zero_right,
    Nat.choose_one_right]
  have : (n * 2).choose 2 ≤ (2 * n) ^ 2 := by
    rw [mul_comm]; exact (Nat.choose_le_pow _ 2).trans (by simp)
  omega

/-- **Three literals do not cancel.** Two 3-clauses clashing on one variable can
resolve to a clause of four literals: `(x₀ ∨ x₁ ∨ x₂)` and `(¬x₀ ∨ x₃ ∨ x₄)` give
`(x₁ ∨ x₂ ∨ x₃ ∨ x₄)`. -/
theorem resolvent_width_grows :
    (resolvent (n := 5) {(0, true), (1, true), (2, true)} {(0, false), (3, true), (4, true)} 0).card
      = 4 := by
  decide

end Resolution


section ClauseShape

/-- `2^k - 1` is never a power of two for `k ≥ 2`. -/
theorem clause_card_not_pow_two (k j : ℕ) (hk : 2 ≤ k) : 2 ^ k - 1 ≠ 2 ^ j := by
  intro h
  have hk4 : 4 ≤ 2 ^ k :=
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk
  rcases Nat.eq_zero_or_pos j with rfl | hj
  · simp at h; omega
  · have e1 : 2 ∣ 2 ^ k := dvd_pow_self 2 (by omega)
    have e2 : 2 ∣ 2 ^ j := dvd_pow_self 2 (by omega)
    omega

open Classical in
/-- **Affine sets over `F₂` have power-of-two size.** A coset `b + V` of a subspace
of `F₂^n` has `2^(dim V)` points; subcubes are the cosets of coordinate subspaces. -/
theorem affine_card {n : ℕ} (V : Submodule (ZMod 2) (Fin n → ZMod 2)) (b : Fin n → ZMod 2) :
    (Finset.univ.filter fun x : Fin n → ZMod 2 => x - b ∈ V).card = 2 ^ Module.finrank (ZMod 2) V := by
  classical
  have e : (Finset.univ.filter fun x : Fin n → ZMod 2 => x - b ∈ V).card = Fintype.card V := by
    rw [← Fintype.card_coe]
    refine Fintype.card_congr ⟨fun x => ⟨x.1 - b, (Finset.mem_filter.mp x.2).2⟩,
      fun v => ⟨v.1 + b, by simp⟩, fun x => by ext; simp, fun v => by ext; simp⟩
  rw [e, Module.card_eq_pow_finrank (K := ZMod 2) (V := V), ZMod.card]

open Classical in
/-- **No clause of width `k ≥ 2` is affine.** The satisfying set of `x₁ ∨ … ∨ x_k`,
the nonzero vectors, is no coset of any subspace, and so no subcube. This holds for
`k = 2` (2-SAT, in P) as for `k = 3`: the shape of one clause does not separate. -/
theorem clause_not_affine {k : ℕ} (hk : 2 ≤ k) (V : Submodule (ZMod 2) (Fin k → ZMod 2))
    (b : Fin k → ZMod 2) :
    (Finset.univ.filter fun x : Fin k → ZMod 2 => x - b ∈ V) ≠
      (Finset.univ.filter fun x : Fin k → ZMod 2 => x ≠ 0) := by
  classical
  intro h
  have h1 := affine_card V b
  rw [h, Finset.filter_ne' Finset.univ (0 : Fin k → ZMod 2), Finset.card_erase_of_mem
    (Finset.mem_univ _), Finset.card_univ, Fintype.card_fun, ZMod.card, Fintype.card_fin] at h1
  exact clause_card_not_pow_two k _ hk h1

/-- **A clause of width `k` has `F₂`-degree `k`.** The OR of `k` bits has its top
coefficient `2^k - 1 ≡ 1`; for `k = 2` this is the degree two of a 2-SAT clause. -/
theorem or_full_degree (k : ℕ) (hk : 1 ≤ k) :
    k ≤ anfDeg (fun S : Finset (Fin k) => if S = ∅ then (0 : ZMod 2) else 1) := by
  classical
  have h : anf (fun S : Finset (Fin k) => if S = ∅ then (0 : ZMod 2) else 1) Finset.univ = 1 := by
    unfold anf
    have e : ∀ T : Finset (Fin k),
        (if T = ∅ then (0 : ZMod 2) else 1) = 1 - (if T = ∅ then 1 else 0) := by
      intro T; split_ifs <;> simp
    simp only [e, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_powerset, Finset.card_univ,
      Fintype.card_fin, Finset.sum_ite_eq', Finset.mem_powerset, Finset.empty_subset, if_true,
      nsmul_eq_mul, mul_one]
    obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    have h2 : ((2 : ℕ) : ZMod 2) = 0 := by decide
    rw [pow_succ, Nat.cast_mul, h2, mul_zero]
    decide
  have := le_anfDeg _ Finset.univ (by rw [h]; decide)
  simpa using this

end ClauseShape


section Switchboard

/-- **Fewer clauses keep a formula satisfiable.** In the clause-selection encoding, if
`y' ≤ y` coordinatewise and `y` is satisfiable, so is `y'`. -/
theorem select_sat_mono {V : Type*} {N : ℕ} (base : CNF V) (sel : Fin N → List (V × Bool))
    (y y' : Fin N → Bool) (hle : ∀ r, y' r = true → y r = true)
    (h : ∃ a, (selectCNF base sel y).Sat a) : ∃ a, (selectCNF base sel y').Sat a := by
  obtain ⟨a, ha⟩ := h
  refine ⟨a, (select_sat_iff base sel y' a).2 ⟨((select_sat_iff base sel y a).1 ha).1,
    fun r hr => ((select_sat_iff base sel y a).1 ha).2 r (hle r hr)⟩⟩

/-- **Sensitivity at a minimal unsatisfiable core.** If the selected formula is
unsatisfiable and removing any one present clause makes it satisfiable, then flipping
switch `r` changes the answer exactly when clause `r` is present: the decision function
is sensitive on every switch of the core and on no other. -/
theorem mus_sensitivity {V : Type*} {N : ℕ} (base : CNF V) (sel : Fin N → List (V × Bool))
    (y : Fin N → Bool) (hunsat : ¬ ∃ a, (selectCNF base sel y).Sat a)
    (hmin : ∀ r, y r = true → ∃ a, (selectCNF base sel (Function.update y r false)).Sat a)
    (r : Fin N) :
    (∃ a, (selectCNF base sel (Function.update y r (!y r))).Sat a) ↔ y r = true := by
  constructor
  · intro hs
    by_contra hr
    simp only [Bool.not_eq_true] at hr
    apply hunsat
    refine select_sat_mono base sel _ y (fun i hi => ?_) hs
    by_cases hir : i = r
    · subst hir; rw [Function.update_self]; rw [hr] at hi ⊢; simp_all
    · rw [Function.update_of_ne hir]; exact hi
  · intro hr
    have := hmin r hr
    rwa [hr]

/-- **A clause blocks a subcube.** The assignments of `n` variables that agree with `b`
on a set `T` of variables number `2^(n - |T|)`; a 3-clause, which forbids one pattern on
its three variables, blocks `2^(n - 3)` assignments. -/
theorem subcube_card {n : ℕ} (T : Finset (Fin n)) (b : Fin n → Bool) :
    (Finset.univ.filter fun x : Fin n → Bool => ∀ i ∈ T, x i = b i).card = 2 ^ (n - T.card) := by
  classical
  have e : (Finset.univ.filter fun x : Fin n → Bool => ∀ i ∈ T, x i = b i).card =
      Fintype.card ((Tᶜ : Finset (Fin n)) → Bool) := by
    rw [← Fintype.card_coe]
    refine Fintype.card_congr
      ⟨fun x i => x.1 i.1,
       fun g => ⟨fun i => if h : i ∈ T then b i else g ⟨i, by simpa using h⟩,
         Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun i hi => by simp [hi]⟩⟩,
       fun x => ?_, fun g => ?_⟩
    · ext i
      by_cases h : i ∈ T
      · simp [h, (Finset.mem_filter.mp x.2).2 i h]
      · simp [h]
    · funext i
      have : i.1 ∉ T := Finset.mem_compl.mp i.2
      simp [this]
  rw [e, Fintype.card_fun, Fintype.card_bool, Fintype.card_coe, Finset.card_compl, Fintype.card_fin]

/-- **Satisfiability as a product of blocks.** Over `F₂`, a formula is satisfiable iff
not every assignment is blocked: `b2 SAT = 1 + ∏_x b2 (B_x)`. -/
theorem sat_eq_one_add_prod {n : ℕ} (blocked : (Fin n → Bool) → Bool) :
    b2 (decide (∃ x, blocked x = false)) = 1 + ∏ x, b2 (blocked x) := by
  classical
  by_cases h : ∃ x, blocked x = false
  · obtain ⟨x, hx⟩ := h
    have hp : ∏ x, b2 (blocked x) = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ x) (by simp [hx, b2])
    rw [hp, decide_eq_true ⟨x, hx⟩]; decide
  · push_neg at h
    have hp : ∏ x, b2 (blocked x) = 1 :=
      Finset.prod_eq_one fun x _ => by simp [Bool.not_eq_false] at h; simp [h x, b2]
    rw [hp, decide_eq_false (by push_neg; exact h)]; decide

/-- **Three variables: one switch per assignment.** With the eight 3-clauses on three
variables indexed by their forbidden assignments, the formula is unsatisfiable exactly
when all eight are present. -/
theorem three_var_switchboard (e : (Fin 3 → Bool) → Bool) :
    (∃ x : Fin 3 → Bool, ∀ c, e c = true → x ≠ c) ↔ ¬ ∀ c, e c = true := by
  constructor
  · rintro ⟨x, hx⟩ hall
    exact hx x (hall x) rfl
  · intro h
    push_neg at h
    obtain ⟨c, hc⟩ := h
    refine ⟨c, fun c' hc' heq => ?_⟩
    subst heq
    simp_all

/-- **The satisfiability polynomial.** With switches `e i` (clause `i` present) and
`c i x` (assignment `x` falsifies clause `i`), over `F₂`:
`SAT(e) = 1 + ∏_x (1 + ∏_i (1 + e_i c_i(x)))`. -/
theorem sat_polynomial {n N : ℕ} (e : Fin N → Bool) (c : Fin N → (Fin n → Bool) → Bool) :
    b2 (decide (∃ x : Fin n → Bool, ∀ i, e i = true → c i x = false)) =
      1 + ∏ x : Fin n → Bool, (1 + ∏ i, (1 + b2 (e i) * b2 (c i x))) := by
  classical
  have hblock : ∀ x : Fin n → Bool, (1 + ∏ i, (1 + b2 (e i) * b2 (c i x))) =
      b2 (decide (∃ i, e i = true ∧ c i x = true)) := by
    intro x
    by_cases h : ∃ i, e i = true ∧ c i x = true
    · obtain ⟨i, hei, hci⟩ := h
      have : ∏ i, (1 + b2 (e i) * b2 (c i x)) = 0 :=
        Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hei, hci, b2]; decide)
      rw [this, decide_eq_true ⟨i, hei, hci⟩]; decide
    · push_neg at h
      have : ∏ i, (1 + b2 (e i) * b2 (c i x)) = 1 := Finset.prod_eq_one fun i _ => by
        by_cases hei : e i = true
        · have := h i hei; simp at this; simp [hei, this, b2]
        · simp at hei; simp [hei, b2]
      rw [this, decide_eq_false (by push_neg; exact h)]; decide
  simp only [hblock]
  have := sat_eq_one_add_prod (n := n) (fun x => decide (∃ i, e i = true ∧ c i x = true))
  rw [← this]
  congr 2
  apply propext
  constructor
  · rintro ⟨x, hx⟩
    refine ⟨x, ?_⟩
    simp only [decide_eq_false_iff_not, not_exists, not_and]
    intro i hei hci; rw [hx i hei] at hci; exact Bool.false_ne_true hci
  · rintro ⟨x, hx⟩
    refine ⟨x, fun i hei => ?_⟩
    simp only [decide_eq_false_iff_not, not_exists, not_and] at hx
    simpa using hx i hei

end Switchboard


section Elimination

/-- **Peeling a variable is distributivity.** `(P ∨ Q) ∧ (P ∨ R) = P ∨ (Q ∧ R)`: the two
blocks of `(x', 0)` and `(x', 1)` share the clauses on the other variables, and the
clauses on `x_n` meet in pairs, the resolvents. -/
theorem peel_distrib (P Q R : Bool) : ((P || Q) && (P || R)) = (P || (Q && R)) := by
  cases P <;> cases Q <;> cases R <;> rfl

/-- **Over `F₂` the permanent is the determinant.** Every sign is `±1 = 1`, so the
permanent of a matrix over `F₂` equals its determinant, computable by elimination;
it counts perfect matchings modulo two, and so can vanish when matchings exist. -/
theorem permanent_eq_det_zmod2 {n : ℕ} (A : Matrix (Fin n) (Fin n) (ZMod 2)) :
    A.permanent = A.det := by
  rw [Matrix.det_apply, Matrix.permanent]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h
  · rw [h, one_smul]
  · rw [h, Units.neg_smul, one_smul]
    have : ∀ x : ZMod 2, -x = x := by decide
    exact (this _).symm

end Elimination

section AffineDegree
open MvPolynomial

/-- Substituting polynomials of total degree at most one does not raise total degree. -/
theorem totalDegree_bind1_le_of_affine {σ τ R : Type*} [CommSemiring R]
    (g : σ → MvPolynomial τ R) (hg : ∀ i, (g i).totalDegree ≤ 1) (p : MvPolynomial σ R) :
    (bind₁ g p).totalDegree ≤ p.totalDegree := by
  conv_lhs => rw [p.as_sum]
  rw [map_sum]
  refine (totalDegree_finsetSum _ _).trans (Finset.sup_le fun s hs => ?_)
  rw [bind₁_monomial]
  refine (totalDegree_mul _ _).trans ?_
  rw [totalDegree_C, zero_add]
  refine (totalDegree_finsetProd _ _).trans (le_trans ?_ (le_totalDegree hs))
  rw [Finsupp.sum]
  refine Finset.sum_le_sum fun i _ => (totalDegree_pow _ _).trans ?_
  simpa using Nat.mul_le_mul_left (s i) (hg i)

/-- `f : 𝔽₂ⁿ → 𝔽₂` has `F₂`-degree at most `d`: some polynomial of total degree `≤ d`
agrees with it on every point. -/
def DegLE {n : ℕ} (d : ℕ) (f : (Fin n → ZMod 2) → ZMod 2) : Prop :=
  ∃ p : MvPolynomial (Fin n) (ZMod 2), p.totalDegree ≤ d ∧ ∀ x, eval x p = f x

/-- The coordinate polynomials of `x ↦ A x + b`. -/
noncomputable def affPoly {n : ℕ} (A : Matrix (Fin n) (Fin n) (ZMod 2)) (b : Fin n → ZMod 2)
    (i : Fin n) : MvPolynomial (Fin n) (ZMod 2) :=
  (∑ j, C (A i j) * X j) + C (b i)

theorem affPoly_deg {n : ℕ} (A : Matrix (Fin n) (Fin n) (ZMod 2)) (b : Fin n → ZMod 2)
    (i : Fin n) : (affPoly A b i).totalDegree ≤ 1 := by
  unfold affPoly
  refine (totalDegree_add _ _).trans (max_le ?_ (by rw [totalDegree_C]; omega))
  refine (totalDegree_finsetSum _ _).trans (Finset.sup_le fun j _ => ?_)
  refine (totalDegree_mul _ _).trans ?_
  rw [totalDegree_C, zero_add]
  exact (totalDegree_X _).le

theorem eval_affPoly {n : ℕ} (A : Matrix (Fin n) (Fin n) (ZMod 2)) (b : Fin n → ZMod 2)
    (x : Fin n → ZMod 2) (i : Fin n) : eval x (affPoly A b i) = (A.mulVec x + b) i := by
  simp [affPoly, Matrix.mulVec, dotProduct, map_sum]

/-- **Affine changes of coordinates do not lower or raise `F₂`-degree.** -/
theorem degLE_comp_affine {n d : ℕ} (A : Matrix (Fin n) (Fin n) (ZMod 2)) (b : Fin n → ZMod 2)
    {f : (Fin n → ZMod 2) → ZMod 2} (h : DegLE d f) :
    DegLE d (fun x => f (A.mulVec x + b)) := by
  obtain ⟨p, hp, hf⟩ := h
  refine ⟨bind₁ (affPoly A b) p, (totalDegree_bind1_le_of_affine _ (affPoly_deg A b) p).trans hp,
    fun x => ?_⟩
  have e : eval x (bind₁ (affPoly A b) p) = eval (fun i => eval x (affPoly A b i)) p := by
    exact eval₂Hom_bind₁ _ _ _ _
  rw [e, hf]
  congr 1
  funext i
  exact eval_affPoly A b x i

theorem degLE_affine_iff {n d : ℕ} (A : Matrix (Fin n) (Fin n) (ZMod 2)) (hA : IsUnit A.det)
    (b : Fin n → ZMod 2) (f : (Fin n → ZMod 2) → ZMod 2) :
    DegLE d (fun x => f (A.mulVec x + b)) ↔ DegLE d f := by
  refine ⟨fun h => ?_, degLE_comp_affine A b⟩
  have h' := degLE_comp_affine A⁻¹ (-(A⁻¹.mulVec b)) h
  refine (show (fun x => f (A.mulVec (A⁻¹.mulVec x + -(A⁻¹.mulVec b)) + b)) = f from ?_) ▸ h'
  funext x
  congr 1
  rw [Matrix.mulVec_add, Matrix.mulVec_neg, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec,
    Matrix.mul_nonsing_inv A hA, Matrix.one_mulVec, Matrix.one_mulVec]
  abel

end AffineDegree

section FuzzyClauses

/-- Value of a literal under a fuzzy assignment `x : Fin n → ℝ`: `x i`, or `1 - x i` if negated. -/
def litVal {n : ℕ} (x : Fin n → ℝ) (l : Fin n × Bool) : ℝ := if l.2 then 1 - x l.1 else x l.1

/-- **Łukasiewicz midpoint.** At `x ≡ 1/2` every clause with at least two literals has
Łukasiewicz value `min(1, Σ ℓ) = 1`: fractional satisfiability is trivial for `k = 2` and
`k = 3` alike. -/
theorem lukasiewicz_midpoint {n : ℕ} (c : List (Fin n × Bool)) (hc : 2 ≤ c.length) :
    1 ≤ (c.map (litVal fun _ => (1 / 2 : ℝ))).sum := by
  have : c.map (litVal fun _ => (1 / 2 : ℝ)) = c.map fun _ => (1 / 2 : ℝ) :=
    List.map_congr_left fun l _ => by unfold litVal; split_ifs <;> norm_num
  rw [this, List.map_const', List.sum_replicate, nsmul_eq_mul]
  have : (2 : ℝ) ≤ c.length := by exact_mod_cast hc
  linarith

/-- **Gödel clauses round.** If some literal of a clause has fuzzy value `≥ α > 1/2`, the
Boolean assignment `x_i ↦ (x_i > 1/2)` satisfies that literal. So Gödel satisfiability at a
threshold above one half is Boolean satisfiability, for every `k`. -/
theorem godel_clause_round {n : ℕ} (c : List (Fin n × Bool)) (x : Fin n → ℝ) {α : ℝ}
    (hα : 1 / 2 < α) (h : ∃ l ∈ c, α ≤ litVal x l) :
    ∃ l ∈ c, (decide (1 / 2 < x l.1)) = !l.2 := by
  obtain ⟨l, hl, hv⟩ := h
  refine ⟨l, hl, ?_⟩
  unfold litVal at hv
  rcases l with ⟨i, s⟩
  cases s
  · simp only [Bool.false_eq_true, if_false] at hv
    simp only [Bool.not_false, decide_eq_true_eq]; linarith
  · simp only [if_true] at hv
    simp only [Bool.not_true, decide_eq_false_iff_not, not_lt]; linarith

end FuzzyClauses

section CoreSpectrum

/-- **Minimal true points survive.** If `f S = 1` and `f` vanishes on every proper subset
of `S`, the normal-form coefficient of the monomial `S` is `1`. Applied to the
unsatisfiability function of the switchboard, every minimal unsatisfiable core is a
monomial. -/
theorem anf_minimal {N : ℕ} (f : Finset (Fin N) → ZMod 2) (S : Finset (Fin N))
    (hS : f S = 1) (hmin : ∀ T ⊂ S, f T = 0) : anf f S = 1 := by
  unfold anf
  rw [← Finset.add_sum_erase _ _ (Finset.mem_powerset.mpr (subset_refl S)), hS]
  have : ∑ T ∈ S.powerset.erase S, f T = 0 :=
    Finset.sum_eq_zero fun T hT => hmin T (Finset.ssubset_iff_subset_ne.mpr
      ⟨Finset.mem_powerset.mp (Finset.mem_of_mem_erase hT), Finset.ne_of_mem_erase hT⟩)
  rw [this, add_zero]

/-- **Below the smallest core the spectrum is empty.** If `f` vanishes on all sets of size
`< m`, every monomial of degree `< m` has coefficient `0`. -/
theorem anf_below {N m : ℕ} (f : Finset (Fin N) → ZMod 2) (hf : ∀ T, T.card < m → f T = 0)
    (S : Finset (Fin N)) (hS : S.card < m) : anf f S = 0 :=
  Finset.sum_eq_zero fun T hT =>
    hf T (lt_of_le_of_lt (Finset.card_le_card (Finset.mem_powerset.mp hT)) hS)

/-- **Tight covers are exact.** If the sets `F i` (`i ∈ s`) have total size at most the size
of their union, any two of them are disjoint. For a core of `2^k` clauses of width `k` on
`n` variables, each falsifying `2^(n-k)` assignments, every assignment falsifies exactly one
clause. -/
theorem tight_cover_disjoint {α ι : Type*} [DecidableEq α] [DecidableEq ι] (s : Finset ι)
    (F : ι → Finset α) (h : ∑ i ∈ s, (F i).card ≤ (s.biUnion F).card) :
    ∀ i ∈ s, ∀ j ∈ s, i ≠ j → Disjoint (F i) (F j) := by
  intro i hi j hj hij
  by_contra hd
  obtain ⟨x, hx⟩ := Finset.not_disjoint_iff_nonempty_inter.mp hd
  set r := (s.erase i).erase j
  have hjr : j ∈ s.erase i := Finset.mem_erase.mpr ⟨hij.symm, hj⟩
  have hsum : ∑ k ∈ s, (F k).card = (F i).card + ((F j).card + ∑ k ∈ r, (F k).card) := by
    rw [← Finset.add_sum_erase _ _ hi, ← Finset.add_sum_erase _ _ hjr]
  have hU : s.biUnion F ⊆ (F i ∪ F j) ∪ r.biUnion F := by
    intro y hy
    obtain ⟨k, hk, hyk⟩ := Finset.mem_biUnion.mp hy
    by_cases hki : k = i
    · subst hki; exact Finset.mem_union_left _ (Finset.mem_union_left _ hyk)
    by_cases hkj : k = j
    · subst hkj; exact Finset.mem_union_left _ (Finset.mem_union_right _ hyk)
    exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr
      ⟨k, Finset.mem_erase.mpr ⟨hkj, Finset.mem_erase.mpr ⟨hki, hk⟩⟩, hyk⟩)
  have h1 := Finset.card_le_card hU
  have h2 := Finset.card_union_le (F i ∪ F j) (r.biUnion F)
  have h3 := Finset.card_union_add_card_inter (F i) (F j)
  have h4 : 0 < (F i ∩ F j).card := Finset.card_pos.mpr ⟨x, hx⟩
  have h5 : (r.biUnion F).card ≤ ∑ k ∈ r, (F k).card := Finset.card_biUnion_le
  omega

end CoreSpectrum

section CubeParity

/-- An involution that maps `s` to itself fixes as many points of `s` as `s` has, mod 2. -/
theorem card_mod_two_involution {α : Type*} [DecidableEq α] (f : α → α) (hf : ∀ a, f (f a) = a) :
    ∀ s : Finset α, (∀ a ∈ s, f a ∈ s) → s.card % 2 = (s.filter fun a => f a = a).card % 2 := by
  intro s
  induction s using Finset.strongInduction with
  | H s ih =>
    intro hs
    rcases s.eq_empty_or_nonempty with rfl | ⟨a, ha⟩
    · simp
    by_cases hfa : f a = a
    · have h1 := ih _ (Finset.erase_ssubset ha) (fun b hb => by
        rcases Finset.mem_erase.mp hb with ⟨hba, hbs⟩
        refine Finset.mem_erase.mpr ⟨fun h => hba ?_, hs b hbs⟩
        rw [← hf b, h, hfa])
      rw [Finset.filter_erase] at h1
      have hm : a ∈ s.filter (fun b => f b = b) := Finset.mem_filter.mpr ⟨ha, hfa⟩
      have c1 := Finset.card_erase_add_one ha
      have c2 := Finset.card_erase_add_one hm
      omega
    · have hfas : f a ∈ s.erase a := Finset.mem_erase.mpr ⟨hfa, hs a ha⟩
      have h1 := ih ((s.erase a).erase (f a))
        ((Finset.erase_ssubset hfas).trans (Finset.erase_ssubset ha)) (fun b hb => by
          simp only [Finset.mem_erase] at hb ⊢
          obtain ⟨hb1, hb2, hb3⟩ := hb
          refine ⟨fun h => hb2 (by rw [← hf b, h, hf]), fun h => hb1 (by rw [← h, hf]), hs b hb3⟩)
      have e : ((s.erase a).erase (f a)).filter (fun b => f b = b) =
          s.filter (fun b => f b = b) := by
        ext b; simp only [Finset.mem_filter, Finset.mem_erase]
        constructor
        · rintro ⟨⟨-, -, h⟩, h'⟩; exact ⟨h, h'⟩
        · rintro ⟨h, h'⟩
          refine ⟨⟨fun hb => ?_, fun hb => ?_, h⟩, h'⟩
          · subst hb; rw [hf] at h'; exact hfa h'.symm
          · subst hb; exact hfa h'
      rw [e] at h1
      have c1 := Finset.card_erase_add_one ha
      have c2 := Finset.card_erase_add_one hfas
      omega

/-- The subcube of assignments that agree with `s` on `T`. A clause on the variables `T`
is identified with the subcube of its falsifying assignments. -/
def subcube {n : ℕ} (T : Finset (Fin n)) (s : Fin n → Bool) : Finset (Fin n → Bool) :=
  univ.filter fun x => ∀ i ∈ T, x i = s i

/-- `W` contains no subcube of codimension `k`. -/
def CubeFree {n : ℕ} (k : ℕ) (W : Finset (Fin n → Bool)) : Prop :=
  ∀ T : Finset (Fin n), T.card = k → ∀ s, ¬ subcube T s ⊆ W

theorem mem_subcube {n : ℕ} {T : Finset (Fin n)} {s x : Fin n → Bool} :
    x ∈ subcube T s ↔ ∀ i ∈ T, x i = s i := by simp [subcube]

theorem cubeFree_self_iff {n : ℕ} (W : Finset (Fin n → Bool)) : CubeFree n W ↔ W = ∅ := by
  constructor
  · intro h
    by_contra hne
    obtain ⟨x, hx⟩ := Finset.nonempty_iff_ne_empty.mpr hne
    refine h univ (by simp) x fun y hy => ?_
    have : y = x := funext fun i => mem_subcube.mp hy i (mem_univ i)
    rw [this]; exact hx
  · rintro rfl T _ s hsub
    exact Finset.notMem_empty s (hsub (mem_subcube.mpr fun _ _ => rfl))

/-- Flip of the first coordinate. -/
def flip0 {n : ℕ} (x : Fin (n + 1) → Bool) : Fin (n + 1) → Bool :=
  fun i => if i = 0 then !x i else x i

theorem flip0_flip0 {n : ℕ} (x : Fin (n + 1) → Bool) : flip0 (flip0 x) = x := by
  funext i; unfold flip0; split_ifs <;> simp

theorem mem_image_flip0 {n : ℕ} (W : Finset (Fin (n + 1) → Bool)) (x : Fin (n + 1) → Bool) :
    x ∈ W.image flip0 ↔ flip0 x ∈ W := by
  constructor
  · rintro h
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp h
    rwa [flip0_flip0]
  · intro h; exact Finset.mem_image.mpr ⟨flip0 x, h, flip0_flip0 x⟩

theorem flip0_mem_subcube {n : ℕ} {T : Finset (Fin (n + 1))} {s x : Fin (n + 1) → Bool} :
    flip0 x ∈ subcube T s ↔ x ∈ subcube T (flip0 s) := by
  simp only [mem_subcube, flip0]
  refine forall₂_congr fun i _ => ?_
  split_ifs <;> cases x i <;> cases s i <;> simp

theorem cubeFree_image_flip0 {n k : ℕ} {W : Finset (Fin (n + 1) → Bool)} (h : CubeFree k W) :
    CubeFree k (W.image flip0) := by
  intro T hT s hsub
  refine h T hT (flip0 s) fun x hx => ?_
  have : flip0 x ∈ subcube T s := flip0_mem_subcube.mpr hx
  have := (mem_image_flip0 W (flip0 x)).mp (hsub this)
  rwa [flip0_flip0] at this

/-- The lift of `W'` to one more coordinate: all assignments whose tail lies in `W'`. -/
def liftW {n : ℕ} (W' : Finset (Fin n → Bool)) : Finset (Fin (n + 1) → Bool) :=
  univ.filter fun x => Fin.tail x ∈ W'

theorem tail_flip0 {n : ℕ} (x : Fin (n + 1) → Bool) : Fin.tail (flip0 x) = Fin.tail x := by
  funext i; simp [Fin.tail, flip0, Fin.succ_ne_zero]

theorem image_tail_liftW {n : ℕ} (W' : Finset (Fin n → Bool)) : (liftW W').image Fin.tail = W' := by
  ext y
  simp only [Finset.mem_image, liftW, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨x, hx, rfl⟩; exact hx
  · intro hy; exact ⟨Fin.cons false y, by simpa using hy, by simp⟩

theorem liftW_fixed {n : ℕ} (W' : Finset (Fin n → Bool)) : (liftW W').image flip0 = liftW W' := by
  ext x; rw [mem_image_flip0]; simp [liftW, tail_flip0]

theorem eq_liftW_of_fixed {n : ℕ} {W : Finset (Fin (n + 1) → Bool)} (h : W.image flip0 = W) :
    liftW (W.image Fin.tail) = W := by
  ext x
  simp only [liftW, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
  constructor
  · rintro ⟨w, hw, hwx⟩
    by_cases h0 : w 0 = x 0
    · have : w = x := by
        funext i
        refine Fin.cases h0 (fun j => ?_) i
        exact congrFun hwx j
      rwa [← this]
    · have : flip0 w = x := by
        funext i
        refine Fin.cases ?_ (fun j => ?_) i
        · simp only [flip0, if_true]; cases hw0 : w 0 <;> cases hx0 : x 0 <;> simp_all
        · simp only [flip0, Fin.succ_ne_zero, if_false]; exact congrFun hwx j
      rw [← this, ← h]
      exact (mem_image_flip0 W (flip0 w)).mpr (by rwa [flip0_flip0])
  · intro hx; exact ⟨x, hx, rfl⟩

theorem cubeFree_liftW_iff {n k : ℕ} (hk : k ≤ n) (W' : Finset (Fin n → Bool)) :
    CubeFree k (liftW W') ↔ CubeFree k W' := by
  classical
  constructor
  · intro h T hT s hsub
    refine h (T.map (Fin.succEmb n)) (by simpa using hT) (Fin.cons false s) fun x hx => ?_
    simp only [liftW, Finset.mem_filter, Finset.mem_univ, true_and]
    refine hsub (mem_subcube.mpr fun i hi => ?_)
    have := mem_subcube.mp hx i.succ (Finset.mem_map_of_mem _ hi)
    simpa [Fin.tail] using this
  · intro h T hT s hsub
    set T' := univ.filter fun i : Fin n => i.succ ∈ T
    have hT' : T'.card ≤ k := by
      rw [← hT, ← Finset.card_map (Fin.succEmb n)]
      refine Finset.card_le_card fun i hi => ?_
      obtain ⟨j, hj, rfl⟩ := Finset.mem_map.mp hi
      simpa [T'] using hj
    obtain ⟨T'', hsup, hcard⟩ := Finset.exists_superset_card_eq hT' (by simpa using hk)
    refine h T'' hcard (Fin.tail s) fun y hy => ?_
    have hx : (Fin.cons (s 0) y : Fin (n + 1) → Bool) ∈ subcube T s := by
      refine mem_subcube.mpr fun i hi => ?_
      refine Fin.cases (by simp) (fun j hj => ?_) i hi
      have : j ∈ T'' := hsup (by simpa [T'] using hj)
      simpa [Fin.tail] using mem_subcube.mp hy j this
    have := hsub hx
    simpa [liftW] using this

open Classical in
/-- The number of sets of assignments on `n` variables containing no subcube of
codimension `k`. -/
noncomputable def cubeFreeCount (n k : ℕ) : ℕ :=
  ((univ : Finset (Finset (Fin n → Bool))).filter fun W => CubeFree k W).card

theorem cubeFreeCount_self (k : ℕ) : cubeFreeCount k k = 1 := by
  classical
  unfold cubeFreeCount
  rw [Finset.card_eq_one]
  refine ⟨∅, ?_⟩
  ext W
  simp [cubeFree_self_iff]

theorem cubeFreeCount_succ {n k : ℕ} (hk : k ≤ n) :
    cubeFreeCount (n + 1) k % 2 = cubeFreeCount n k % 2 := by
  classical
  unfold cubeFreeCount
  have hinv : ∀ W : Finset (Fin (n + 1) → Bool), (W.image flip0).image flip0 = W := by
    intro W; ext x; rw [mem_image_flip0, mem_image_flip0, flip0_flip0]
  rw [card_mod_two_involution (fun W => W.image flip0) hinv _ (fun W hW => by
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hW ⊢
    exact cubeFree_image_flip0 hW)]
  congr 1
  refine Finset.card_nbij' (fun W => W.image Fin.tail) liftW ?_ ?_ ?_ ?_
  · intro W hW
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hW ⊢
    rw [← cubeFree_liftW_iff hk, eq_liftW_of_fixed hW.2]; exact hW.1
  · intro W' hW'
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hW' ⊢
    exact ⟨(cubeFree_liftW_iff hk W').mpr hW', liftW_fixed W'⟩
  · intro W hW
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hW
    exact eq_liftW_of_fixed hW.2
  · intro W' _; exact image_tail_liftW W'

/-- **Cube-free sets are odd in number.** For `n ≥ k` the sets of assignments containing
no subcube of codimension `k` are odd in number. -/
theorem cubeFreeCount_odd {n k : ℕ} (hk : k ≤ n) : cubeFreeCount n k % 2 = 1 := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hk
  induction m with
  | zero => simp [cubeFreeCount_self]
  | succ m ih => rw [← add_assoc, cubeFreeCount_succ (by omega), ih (by omega)]

theorem two_pow_zmod2 (m : ℕ) : ((2 ^ m : ℕ) : ZMod 2) = if m = 0 then 1 else 0 := by
  cases m with
  | zero => simp
  | succ m =>
    simp only [pow_succ, Nat.succ_ne_zero, if_false, Nat.cast_mul]
    exact mul_eq_zero_of_right _ (by decide)

/-- **Double counting over `F₂`.** For clauses `cs` with falsifier sets `F c`, the number of
unsatisfiable subsets of `cs` has the parity of the number of sets of assignments that
meet every falsifier set. -/
theorem unsat_parity {X C : Type*} [Fintype X] [DecidableEq X] [DecidableEq C]
    (cs : Finset C) (F : C → Finset X) :
    (((cs.powerset.filter fun e => ∀ x : X, ∃ c ∈ e, x ∈ F c).card : ℕ) : ZMod 2) =
      (((univ : Finset (Finset X)).filter fun W => ∀ c ∈ cs, ∃ x ∈ W, x ∈ F c).card : ℕ) := by
  classical
  set sol : Finset C → Finset X := fun e => univ.filter fun x => ∀ c ∈ e, x ∉ F c
  set good : Finset X → Finset C := fun W => cs.filter fun c => ∀ x ∈ W, x ∉ F c
  have key : ∑ e ∈ cs.powerset, 2 ^ (sol e).card = ∑ W : Finset X, 2 ^ (good W).card := by
    calc ∑ e ∈ cs.powerset, 2 ^ (sol e).card
        = ∑ e ∈ cs.powerset, ∑ W : Finset X, if W ⊆ sol e then 1 else 0 := by
          refine Finset.sum_congr rfl fun e _ => ?_
          rw [Finset.sum_boole, Nat.cast_id, ← Finset.card_powerset]
          congr 1; ext W; simp
      _ = ∑ W : Finset X, ∑ e ∈ cs.powerset, if W ⊆ sol e then 1 else 0 := Finset.sum_comm
      _ = ∑ W : Finset X, ∑ e ∈ cs.powerset, if e ⊆ good W then 1 else 0 := by
          refine Finset.sum_congr rfl fun W _ => Finset.sum_congr rfl fun e he => ?_
          have hecs := Finset.mem_powerset.mp he
          congr 1
          apply propext
          simp only [sol, good, Finset.subset_iff, Finset.mem_filter, Finset.mem_univ, true_and]
          exact ⟨fun h c hc => ⟨hecs hc, fun x hx => h hx c hc⟩,
            fun h x hx c hc => (h hc).2 x hx⟩
      _ = ∑ W : Finset X, 2 ^ (good W).card := by
          refine Finset.sum_congr rfl fun W _ => ?_
          rw [Finset.sum_boole, Nat.cast_id, ← Finset.card_powerset]
          congr 1; ext e
          simp only [Finset.mem_filter, Finset.mem_powerset]
          exact ⟨fun h => h.2, fun h => ⟨h.trans (Finset.filter_subset _ _), h⟩⟩
  have hk := congrArg (fun t : ℕ => (t : ZMod 2)) key
  simp only [Nat.cast_sum, two_pow_zmod2, Finset.card_eq_zero] at hk
  rw [← Finset.sum_boole, ← Finset.sum_boole]
  convert hk using 2 with e he W
  · congr 1; apply propext
    simp only [sol, Finset.filter_eq_empty_iff, Finset.mem_univ, true_and, not_forall, not_not,
      true_implies, exists_prop]
  · congr 1; apply propext
    simp only [good, Finset.filter_eq_empty_iff, not_forall, not_not, exists_prop]

/-- The 3-clauses on `n` variables, each identified with its subcube of falsifiers. -/
noncomputable def clauses3 (n : ℕ) : Finset (Finset (Fin n → Bool)) :=
  ((univ.filter fun T : Finset (Fin n) => T.card = 3) ×ˢ (univ : Finset (Fin n → Bool))).image
    fun p => subcube p.1 p.2

/-- **The unsatisfiable switchboards are odd in number.** For every `n ≥ 3` an odd number of
sets of 3-clauses on `n` variables are unsatisfiable, so the top monomial of the switchboard
function survives over `F₂`. -/
theorem unsat3_count_odd {n : ℕ} (hn : 3 ≤ n) :
    ((clauses3 n).powerset.filter fun e => ∀ x : Fin n → Bool, ∃ c ∈ e, x ∈ c).card % 2 = 1 := by
  classical
  have h1 := unsat_parity (clauses3 n) id
  simp only [id] at h1
  have h2 : ((univ : Finset (Finset (Fin n → Bool))).filter fun W =>
      ∀ c ∈ clauses3 n, ∃ x ∈ W, x ∈ c).card = cubeFreeCount n 3 := by
    unfold cubeFreeCount
    refine Finset.card_nbij' (fun W => Wᶜ) (fun V => Vᶜ) ?_ ?_ (fun W _ => compl_compl W)
      (fun V _ => compl_compl V)
    · intro W hW
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hW ⊢
      intro T hT s hsub
      obtain ⟨x, hxW, hxc⟩ := hW (subcube T s)
        (Finset.mem_image.mpr ⟨(T, s), by simp [hT], rfl⟩)
      exact Finset.mem_compl.mp (hsub hxc) hxW
    · intro V hV
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hV ⊢
      intro c hc
      obtain ⟨⟨T, s⟩, hTs, rfl⟩ := Finset.mem_image.mp hc
      have hT : T.card = 3 := by simpa using (Finset.mem_product.mp hTs).1
      by_contra hno
      push_neg at hno
      exact hV T hT s fun x hx => by
        by_contra hxV
        exact hno x (Finset.mem_compl.mpr hxV) hx
  rw [h2] at h1
  have := cubeFreeCount_odd hn
  rw [ZMod.natCast_eq_natCast_iff'] at h1
  omega

/-- **Above the threshold every formula is unsatisfiable.** If every assignment falsifies
exactly `m` of the clauses `cs`, a formula of more than `|cs| - m` of them has no model. -/
theorem threshold_unsat {X C : Type*} [DecidableEq X] [DecidableEq C] (cs : Finset C) (F : C → Finset X)
    (m : ℕ) (hm : ∀ x, (cs.filter fun c => x ∈ F c).card = m) {e : Finset C} (he : e ⊆ cs)
    (hcard : cs.card - m < e.card) : ∀ x, ∃ c ∈ e, x ∈ F c := by
  intro x
  by_contra hno
  push_neg at hno
  have hsub : e ⊆ cs.filter fun c => x ∉ F c :=
    fun c hc => Finset.mem_filter.mpr ⟨he hc, hno c hc⟩
  have h1 := Finset.card_le_card hsub
  have h2 := Finset.card_filter_add_card_filter_not (s := cs) (p := fun c => x ∈ F c)
  rw [hm x] at h2
  omega

/-- **At the threshold a model is unique.** A formula of exactly `|cs| - m` clauses is
satisfied by `x` iff it is the set of clauses that `x` satisfies. -/
theorem threshold_sat_iff {X C : Type*} [DecidableEq X] [DecidableEq C] (cs : Finset C) (F : C → Finset X)
    (m : ℕ) (hm : ∀ x, (cs.filter fun c => x ∈ F c).card = m) {e : Finset C} (he : e ⊆ cs)
    (hcard : e.card = cs.card - m) (x : X) :
    (∀ c ∈ e, x ∉ F c) ↔ e = cs.filter fun c => x ∉ F c := by
  constructor
  · intro h
    have hsub : e ⊆ cs.filter fun c => x ∉ F c :=
      fun c hc => Finset.mem_filter.mpr ⟨he hc, h c hc⟩
    refine Finset.eq_of_subset_of_card_le hsub ?_
    have h2 := Finset.card_filter_add_card_filter_not (s := cs) (p := fun c => x ∈ F c)
    rw [hm x] at h2
    omega
  · rintro rfl c hc; exact (Finset.mem_filter.mp hc).2

theorem subcube_eq_of_mem {n : ℕ} {T : Finset (Fin n)} {s x : Fin n → Bool}
    (h : x ∈ subcube T s) : subcube T s = subcube T x := by
  ext y; simp only [mem_subcube]
  exact forall₂_congr fun i hi => by rw [mem_subcube.mp h i hi]

theorem subcube_injective {n : ℕ} (x : Fin n → Bool) {T T' : Finset (Fin n)}
    (h : subcube T x = subcube T' x) : T = T' := by
  have key : ∀ {A B : Finset (Fin n)}, subcube A x = subcube B x → A ⊆ B := by
    intro A B hAB i hi
    by_contra hiB
    have hy : Function.update x i (!x i) ∈ subcube B x := by
      refine mem_subcube.mpr fun j hj => ?_
      have : j ≠ i := fun e => hiB (e ▸ hj)
      simp [Function.update_of_ne this]
    rw [← hAB] at hy
    have := mem_subcube.mp hy i hi
    simp at this
  exact Finset.Subset.antisymm (key h) (key h.symm)

/-- Every assignment falsifies exactly `C(n,3)` of the 3-clauses, one per triple of
variables. -/
theorem falsified_card {n : ℕ} (x : Fin n → Bool) :
    ((clauses3 n).filter fun c => x ∈ c).card = n.choose 3 := by
  classical
  have e : (clauses3 n).filter (fun c => x ∈ c) =
      (univ.powersetCard 3).image fun T => subcube T x := by
    ext c
    simp only [clauses3, Finset.mem_filter, Finset.mem_image, Finset.mem_product,
      Finset.mem_univ, and_true, Finset.mem_powersetCard, Finset.subset_univ, true_and,
      Prod.exists]
    constructor
    · rintro ⟨⟨T, s, hT, rfl⟩, hx⟩; exact ⟨T, hT, (subcube_eq_of_mem hx).symm⟩
    · rintro ⟨T, hT, rfl⟩; exact ⟨⟨T, x, hT, rfl⟩, mem_subcube.mpr fun _ _ => rfl⟩
  rw [e, Finset.card_image_of_injOn (fun T _ T' _ h => subcube_injective x h),
    Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]

/-- Different assignments satisfy different sets of 3-clauses (`n ≥ 3`). -/
theorem satisfied_injective {n : ℕ} (hn : 3 ≤ n) :
    Function.Injective fun x : Fin n → Bool => (clauses3 n).filter fun c => x ∉ c := by
  classical
  intro x y hxy
  funext i
  obtain ⟨T, hiT, hT⟩ := Finset.exists_superset_card_eq (s := {i}) (n := 3) (by simp)
    (by simpa using hn)
  have hc : subcube T x ∈ clauses3 n :=
    Finset.mem_image.mpr ⟨(T, x), by simp [hT], rfl⟩
  by_contra hne
  have hy : y ∉ subcube T x := fun h => hne (mem_subcube.mp h i (hiT (by simp))).symm
  have : subcube T x ∈ (clauses3 n).filter fun c => y ∉ c := Finset.mem_filter.mpr ⟨hc, hy⟩
  have hxy' : ((clauses3 n).filter fun c => x ∉ c) = (clauses3 n).filter fun c => y ∉ c := hxy
  rw [← hxy'] at this
  exact (Finset.mem_filter.mp this).2 (mem_subcube.mpr fun _ _ => rfl)

/-- **The unique-witness layer.** For `n ≥ 3`, a formula of more than `N - C(n,3)` clauses is
unsatisfiable, and exactly `2^n` formulas of `N - C(n,3)` clauses are satisfiable, one for
each assignment, which is then their only model. -/
theorem unique_witness_layer {n : ℕ} (hn : 3 ≤ n) :
    (∀ e ⊆ clauses3 n, (clauses3 n).card - n.choose 3 < e.card →
      ∀ x, ∃ c ∈ e, x ∈ c) ∧
    (((clauses3 n).powerset.filter fun e =>
      e.card = (clauses3 n).card - n.choose 3 ∧ ∃ x, ∀ c ∈ e, x ∉ c).card = 2 ^ n) := by
  classical
  refine ⟨fun e he h => threshold_unsat (clauses3 n) id _ falsified_card he h, ?_⟩
  have e1 : ((clauses3 n).powerset.filter fun e =>
      e.card = (clauses3 n).card - n.choose 3 ∧ ∃ x, ∀ c ∈ e, x ∉ c) =
      (univ : Finset (Fin n → Bool)).image fun x => (clauses3 n).filter fun c => x ∉ c := by
    ext e
    simp only [Finset.mem_filter, Finset.mem_powerset, Finset.mem_image, Finset.mem_univ,
      true_and]
    constructor
    · rintro ⟨he, hc, x, hx⟩
      exact ⟨x, ((threshold_sat_iff (clauses3 n) id _ falsified_card he hc x).mp hx).symm⟩
    · rintro ⟨x, rfl⟩
      have h2 := Finset.card_filter_add_card_filter_not (s := clauses3 n) (p := fun c => x ∈ c)
      rw [falsified_card x] at h2
      exact ⟨Finset.filter_subset _ _, by omega,
        x, fun c hc => (Finset.mem_filter.mp hc).2⟩
  rw [e1, Finset.card_image_of_injective _ (satisfied_injective hn), Finset.card_univ,
    Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]

end CubeParity

section NandLower

theorem step_getD (L : List Bool) (g : Fin 3 × ℕ × ℕ) (i : ℕ) :
    (step L g).getD i false =
      if i < L.length then L.getD i false
      else if i = L.length then opB g.1 (L.getD g.2.1 false) (L.getD g.2.2 false) else false := by
  unfold step
  split_ifs with h1 h2
  · rw [List.getD_append _ _ _ _ h1]
  · subst h2; simp
  · rw [List.getD_eq_default]; simp; omega

/-- **Classes of inputs.** Along a program, the inputs can be labelled so that every wire
depends only on the inputs of one label, and the number of labels drops by at most one
per two-input gate. -/
theorem wire_classes {N : ℕ} (P : List (Fin 3 × ℕ × ℕ)) :
    ∃ c : Fin N → ℕ, N ≤ (univ.image c).card + (P.filter fun g => g.1 ≠ 2).length ∧
      ∀ i, ∃ ℓ, ∀ x y : Fin N → Bool, (∀ j, c j = ℓ → x j = y j) →
        (wires x P).getD i false = (wires y P).getD i false := by
  classical
  induction P using List.reverseRecOn with
  | nil =>
    refine ⟨fun j => j.val, ?_, fun i => ⟨i, fun x y h => ?_⟩⟩
    · rw [Finset.card_image_of_injective _ Fin.val_injective]; simp
    · simp only [wires, List.foldl_nil]
      by_cases hi : i < N
      · rw [List.getD_eq_getElem _ _ (by simpa using hi), List.getD_eq_getElem _ _ (by simpa using hi)]
        simpa using h ⟨i, hi⟩ rfl
      · rw [List.getD_eq_default _ _ (by simpa using hi), List.getD_eq_default _ _ (by simpa using hi)]
  | append_singleton P g ih =>
    obtain ⟨c, hc, hw⟩ := ih
    obtain ⟨la, ha⟩ := hw g.2.1
    obtain ⟨lb, hb⟩ := hw g.2.2
    have hlen : ∀ x : Fin N → Bool, (wires x P).length = N + P.length := fun x => wires_length x P
    by_cases hg : g.1 = 2
    · refine ⟨c, by simpa [List.filter_append, hg] using hc, fun i => ?_⟩
      by_cases hi : i < N + P.length
      · obtain ⟨l, hl⟩ := hw i
        refine ⟨l, fun x y h => ?_⟩
        simp only [wires_snoc, step_getD, hlen, hi, if_true]
        exact hl x y h
      · refine ⟨la, fun x y h => ?_⟩
        simp only [wires_snoc, step_getD, hlen, hi, if_false]
        split_ifs
        · rw [hg]; simp only [opB]; rw [ha x y h]
        · rfl
    · set m : ℕ → ℕ := fun l => if l = lb then la else l
      refine ⟨fun j => m (c j), ?_, fun i => ?_⟩
      · have himg : univ.image (fun j => m (c j)) = (univ.image c).image m := by
          rw [Finset.image_image]; rfl
        have hsub : (univ.image c).erase lb ⊆ (univ.image c).image m := by
          intro l hl
          obtain ⟨hne, hl⟩ := Finset.mem_erase.mp hl
          exact Finset.mem_image.mpr ⟨l, hl, by simp [m, hne]⟩
        have h1 := Finset.card_le_card hsub
        have h2 := Finset.pred_card_le_card_erase (s := univ.image c) (a := lb)
        have hf : ((P ++ [g]).filter fun g => g.1 ≠ 2).length =
            (P.filter fun g => g.1 ≠ 2).length + 1 := by simp [List.filter_append, hg]
        rw [himg, hf]
        omega
      · have lift : ∀ l, ∀ x y : Fin N → Bool, (∀ j, m (c j) = m l → x j = y j) →
            (∀ j, c j = l → x j = y j) := fun l x y h j hj => h j (by rw [hj])
        by_cases hi : i < N + P.length
        · obtain ⟨l, hl⟩ := hw i
          refine ⟨m l, fun x y h => ?_⟩
          simp only [wires_snoc, step_getD, hlen, hi, if_true]
          exact hl x y (lift l x y h)
        · refine ⟨la, fun x y h => ?_⟩
          simp only [wires_snoc, step_getD, hlen, hi, if_false]
          split_ifs
          · have hA : ∀ j, c j = la → x j = y j := fun j hj => h j (by simp [m, hj])
            have hB : ∀ j, c j = lb → x j = y j := fun j hj => h j (by simp [m, hj])
            rw [ha x y hA, hb x y hB]
          · rfl

/-- **Programs without NOT are monotone.** -/
theorem wires_monotone {N : ℕ} (P : List (Fin 3 × ℕ × ℕ)) (hP : ∀ g ∈ P, g.1 ≠ 2)
    (i : ℕ) {x y : Fin N → Bool} (hxy : x ≤ y) :
    (wires x P).getD i false ≤ (wires y P).getD i false := by
  induction P using List.reverseRecOn generalizing i with
  | nil =>
    simp only [wires, List.foldl_nil]
    by_cases hi : i < N
    · rw [List.getD_eq_getElem _ _ (by simpa using hi), List.getD_eq_getElem _ _ (by simpa using hi)]
      simpa using hxy ⟨i, hi⟩
    · rw [List.getD_eq_default _ _ (by simpa using hi), List.getD_eq_default _ _ (by simpa using hi)]
  | append_singleton P g ih =>
    have hP' : ∀ g ∈ P, g.1 ≠ 2 := fun g' hg' => hP g' (List.mem_append_left _ hg')
    have hg : g.1 ≠ 2 := hP g (by simp)
    have hlen : ∀ x : Fin N → Bool, (wires x P).length = N + P.length := fun x => wires_length x P
    simp only [wires_snoc, step_getD, hlen]
    split_ifs
    · exact ih hP' i
    · have ha := ih hP' g.2.1
      have hb := ih hP' g.2.2
      generalize (wires x P).getD g.2.1 false = p1 at ha ⊢
      generalize (wires y P).getD g.2.1 false = p2 at ha ⊢
      generalize (wires x P).getD g.2.2 false = q1 at hb ⊢
      generalize (wires y P).getD g.2.2 false = q2 at hb ⊢
      rcases g with ⟨o, a, b⟩
      fin_cases o
      · simp only [opB]; revert ha hb
        cases p1 <;> cases p2 <;> cases q1 <;> cases q2 <;> decide
      · simp only [opB]; revert ha hb
        cases p1 <;> cases p2 <;> cases q1 <;> cases q2 <;> decide
      · exact absurd rfl hg
    · exact le_rfl

/-- **The NAND of `N` bits needs `N` gates.** Any program computing
`¬(x₁ ∧ … ∧ x_N)` has at least `N - 1` two-input gates, since its output depends on all
inputs, and at least one NOT, since it is not monotone. -/
theorem nand_lower {N : ℕ} (hN : 1 ≤ N) (P : List (Fin 3 × ℕ × ℕ))
    (hP : Computes P fun x : Fin N → Bool => !(decide (∀ i, x i = true))) : N ≤ P.length := by
  classical
  obtain ⟨o, -, ho⟩ := hP
  obtain ⟨c, hc, hw⟩ := wire_classes (N := N) P
  obtain ⟨l, hl⟩ := hw o
  have hall : ∀ j, c j = l := by
    intro j
    by_contra hj
    have := hl (fun _ => true) (Function.update (fun _ => true) j false) (fun k hk => by
      have : k ≠ j := fun e => hj (e ▸ hk)
      simp [Function.update_of_ne this])
    rw [ho, ho] at this
    simp at this
    exact absurd (this j) (by simp)
  have himg : univ.image c ⊆ {l} := fun a ha => by
    obtain ⟨j, -, rfl⟩ := Finset.mem_image.mp ha; simp [hall j]
  have hcard := Finset.card_le_card himg
  have hnot : ∃ g ∈ P, g.1 = 2 := by
    by_contra hno
    push_neg at hno
    have := wires_monotone (N := N) P hno o (x := fun _ => false) (y := fun _ => true) (fun i => show false ≤ true by decide)
    rw [ho, ho] at this
    have h0 : ¬ ∀ i : Fin N, (fun _ : Fin N => false) i = true := fun h => by
      simpa using h ⟨0, hN⟩
    have hF : ¬ ∀ _ : Fin N, False := fun h => h ⟨0, hN⟩
    simp [h0] at this
    simp [hF] at this
    exact absurd this (by decide)
  obtain ⟨g, hgP, hg2⟩ := hnot
  have hsplit := List.length_eq_length_filter_add (l := P) (f := fun g => decide (g.1 ≠ 2))
  have hpos : 0 < (P.filter fun g => !decide (g.1 ≠ 2)).length :=
    List.length_pos_iff_exists_mem.mpr ⟨g, List.mem_filter.mpr ⟨hgP, by simp [hg2]⟩⟩
  simp only [Finset.card_singleton] at hcard
  simp only [decide_not] at hsplit hpos hc ⊢
  omega

/-- The program `x₀ ∧ ⋯ ∧ x₇`, then NOT. -/
def nand8 : List (Fin 3 × ℕ × ℕ) :=
  [(0, 0, 1), (0, 8, 2), (0, 9, 3), (0, 10, 4), (0, 11, 5), (0, 12, 6), (0, 13, 7), (2, 14, 14)]

set_option maxRecDepth 100000 in
theorem nand8_computes :
    Computes nand8 fun x : Fin 8 → Bool => !(decide (∀ i, x i = true)) := by
  refine ⟨15, by decide, fun x => ?_⟩
  revert x
  decide

/-- **3-SAT on three variables needs exactly 8 gates.** On three variables every clause is
falsified by one assignment, so the switchboard function is the NAND of the 8 switches;
its least circuit has 8 gates. -/
theorem minCircuitSize_nand8 :
    minCircuitSize (fun x : Fin 8 → Bool => !(decide (∀ i, x i = true))) Set.univ = 8 := by
  have hne : {k | ∃ P : List (Fin 3 × ℕ × ℕ), P.length = k ∧
      ComputesOn P (fun x : Fin 8 → Bool => !(decide (∀ i, x i = true))) Set.univ}.Nonempty :=
    ⟨8, nand8, rfl, by simpa [ComputesOn, Computes] using nand8_computes⟩
  refine le_antisymm (Nat.sInf_le ⟨nand8, rfl, by simpa [ComputesOn, Computes] using
    nand8_computes⟩) ?_
  obtain ⟨P, hl, hc⟩ := Nat.sInf_mem hne
  unfold minCircuitSize
  rw [← hl]
  exact nand_lower (by norm_num) P (by simpa [ComputesOn, Computes] using hc)

/-- **The normal form is unique.** The transform is an involution over `F₂`: if
`f S = Σ_{T ⊆ S} c T` for every `S`, then `c` is the normal form of `f`. -/
theorem anf_unique {N : ℕ} (f c : Finset (Fin N) → ZMod 2)
    (h : ∀ S, f S = ∑ T ∈ S.powerset, c T) : anf f = c := by
  have hf : f = anf c := funext h
  funext S
  rw [hf]
  show ∑ T ∈ S.powerset, anf c T = c S
  exact anf_reconstruct c S

/-- The count of one-gate extensions: a gate on `m` wires is a NOT of one of them or an AND
of an unordered pair, `m + C(m,2) = C(m+1,2)` choices. -/
theorem gate_choices (m : ℕ) : m + m.choose 2 = (m + 1).choose 2 := by
  rw [Nat.choose_succ_succ', Nat.choose_one_right]

end NandLower

section CutRank

/-- **A matrix that factors through `γ` has rank at most `|γ|`.** -/
theorem rank_le_of_factor {α β γ K : Type*} [Fintype α] [Fintype β] [Fintype γ] [DecidableEq γ]
    [Field K] (φ : α → γ) (G : γ → β → K) :
    (Matrix.of fun a b => G (φ a) b).rank ≤ Fintype.card γ := by
  have e : (Matrix.of fun a b => G (φ a) b) =
      (Matrix.of fun a c => if φ a = c then (1 : K) else 0) * Matrix.of G := by
    ext a b
    simp [Matrix.mul_apply]
  rw [e]
  exact (Matrix.rank_mul_le_right _ _).trans (Matrix.rank_le_card_height _)

/-- **Single-cut rank.** Split the switches into `A` and `B`. If the decision function
depends on the two halves only through the sets of assignments their active clauses
falsify, the truth-table matrix across the cut has `F₂`-rank at most the number of
reachable falsified sets on either side, and at most `2^(2^n)`. -/
theorem single_cut_rank_bound {α β X K : Type*} [Fintype α] [Fintype β] [Fintype X]
    [DecidableEq X] [Field K] (covA : α → Finset X) (covB : β → Finset X) (F : Finset X → K) :
    (Matrix.of fun a b => F (covA a ∪ covB b)).rank ≤
        min (univ.image covA).card (univ.image covB).card ∧
      (Matrix.of fun a b => F (covA a ∪ covB b)).rank ≤ 2 ^ Fintype.card X := by
  classical
  have hA : (Matrix.of fun a b => F (covA a ∪ covB b)).rank ≤ (univ.image covA).card := by
    have := rank_le_of_factor (K := K) (β := β)
      (fun a => (⟨covA a, Finset.mem_image_of_mem _ (mem_univ a)⟩ : (univ.image covA)))
      (fun c b => F (c.1 ∪ covB b))
    rw [Fintype.card_coe] at this
    exact this
  have hB : (Matrix.of fun a b => F (covA a ∪ covB b)).rank ≤ (univ.image covB).card := by
    rw [← Matrix.rank_transpose]
    have := rank_le_of_factor (K := K) (β := α)
      (fun b => (⟨covB b, Finset.mem_image_of_mem _ (mem_univ b)⟩ : (univ.image covB)))
      (fun c a => F (covA a ∪ c.1))
    rw [Fintype.card_coe] at this
    exact this
  refine ⟨le_min hA hB, hA.trans ?_⟩
  calc (univ.image covA).card ≤ (univ : Finset (Finset X)).card := card_le_univ _
    _ = 2 ^ Fintype.card X := by simp

/-- **Essential and non-monotone functions need `N` gates.** If `f` depends on every one of
its `N` inputs and is not monotone, every program computing it has at least `N` gates. -/
theorem essential_nonmonotone_lower {N : ℕ} (f : (Fin N → Bool) → Bool)
    (hdep : ∀ j, ∃ x, f x ≠ f (Function.update x j (!x j)))
    (hnm : ∃ x y : Fin N → Bool, x ≤ y ∧ f x = true ∧ f y = false)
    (P : List (Fin 3 × ℕ × ℕ)) (hP : Computes P f) : N ≤ P.length := by
  classical
  obtain ⟨o, -, ho⟩ := hP
  obtain ⟨c, hc, hw⟩ := wire_classes (N := N) P
  obtain ⟨l, hl⟩ := hw o
  have hall : ∀ j, c j = l := by
    intro j
    by_contra hj
    obtain ⟨x, hx⟩ := hdep j
    have := hl x (Function.update x j (!x j)) (fun k hk => by
      have : k ≠ j := fun e => hj (e ▸ hk)
      simp [Function.update_of_ne this])
    rw [ho, ho] at this
    exact hx this
  have himg : univ.image c ⊆ {l} := fun a ha => by
    obtain ⟨j, -, rfl⟩ := Finset.mem_image.mp ha; simp [hall j]
  have hcard := Finset.card_le_card himg
  have hnot : ∃ g ∈ P, g.1 = 2 := by
    by_contra hno
    push_neg at hno
    obtain ⟨x, y, hxy, hx, hy⟩ := hnm
    have := wires_monotone (N := N) P hno o hxy
    rw [ho, ho, hx, hy] at this
    exact absurd this (by decide)
  obtain ⟨g, hgP, hg2⟩ := hnot
  have hsplit := List.length_eq_length_filter_add (l := P) (f := fun g => decide (g.1 ≠ 2))
  have hpos : 0 < (P.filter fun g => !decide (g.1 ≠ 2)).length :=
    List.length_pos_iff_exists_mem.mpr ⟨g, List.mem_filter.mpr ⟨hgP, by simp [hg2]⟩⟩
  simp only [Finset.card_singleton] at hcard
  simp only [decide_not] at hsplit hpos hc ⊢
  omega

/-- **The 3-SAT switchboard needs `N` gates.** Number the `N = 8 C(n,3)` clauses on `n ≥ 3`
variables by `cl`. Every program deciding satisfiability of the switchboard has at least
`N` gates: each switch is essential (the eight clauses on its triple form a core) and the
function is not monotone. -/
theorem sat3_switchboard_lower {n N : ℕ} (hn : 3 ≤ n) (cl : Fin N → Finset (Fin n → Bool))
    (hinj : Function.Injective cl) (hmem : ∀ i, cl i ∈ clauses3 n)
    (hsurj : ∀ c ∈ clauses3 n, ∃ i, cl i = c) (P : List (Fin 3 × ℕ × ℕ))
    (hP : Computes P fun e : Fin N → Bool => decide (∃ x, ∀ i, e i = true → x ∉ cl i)) :
    N ≤ P.length := by
  classical
  have hcover : ∀ (T : Finset (Fin n)), T.card = 3 → ∀ y : Fin n → Bool,
      ∃ j, cl j = subcube T y :=
    fun T hT y => hsurj _ (Finset.mem_image.mpr ⟨(T, y), by simp [hT], rfl⟩)
  have hT0 : ∃ T : Finset (Fin n), T.card = 3 := by
    obtain ⟨T, -, hT⟩ := Finset.exists_superset_card_eq (s := (∅ : Finset (Fin n))) (n := 3)
      (by simp) (by simpa using hn)
    exact ⟨T, hT⟩
  refine essential_nonmonotone_lower _ (fun i => ?_) ?_ P hP
  · obtain ⟨⟨T, s⟩, hTs, hci⟩ := Finset.mem_image.mp (hmem i)
    have hT : T.card = 3 := by simpa using (Finset.mem_product.mp hTs).1
    set e : Fin N → Bool := fun j => decide (∃ s', cl j = subcube T s')
    have hei : e i = true := by simp [e]; exact ⟨s, hci.symm⟩
    refine ⟨e, ?_⟩
    rw [hei]
    have h1 : decide (∃ x, ∀ j, e j = true → x ∉ cl j) = false := by
      simp only [decide_eq_false_iff_not, not_exists, not_forall, not_not]
      intro y
      obtain ⟨j, hj⟩ := hcover T hT y
      exact ⟨j, by simp [e]; exact ⟨y, hj⟩, by rw [hj]; exact mem_subcube.mpr fun _ _ => rfl⟩
    have h2 : decide (∃ x, ∀ j, (Function.update e i (!true)) j = true → x ∉ cl j) = true := by
      simp only [decide_eq_true_eq]
      refine ⟨s, fun j hj hsj => ?_⟩
      by_cases hji : j = i
      · subst hji; simp at hj
      · rw [Function.update_of_ne hji] at hj
        obtain ⟨s', hs'⟩ := by simpa [e] using hj
        rw [hs'] at hsj
        have : cl j = cl i := by rw [hs', subcube_eq_of_mem hsj, ← hci]
        exact hji (hinj this)
    rw [h1, h2]; decide
  · obtain ⟨T, hT⟩ := hT0
    refine ⟨fun _ => false, fun _ => true, fun i => show false ≤ true by decide, ?_, ?_⟩
    · simp only [decide_eq_true_eq]
      exact ⟨fun _ => false, fun i h => absurd h (by decide)⟩
    · simp only [decide_eq_false_iff_not, not_exists, not_forall, not_not]
      intro y
      obtain ⟨j, hj⟩ := hcover T hT y
      exact ⟨j, by simp, by rw [hj]; exact mem_subcube.mpr fun _ _ => rfl⟩

end CutRank

section CircuitCount

/-- **Quotients by a symmetry do not shrink below `|X|/|G|`.** For a finite group acting on
a finite set, the number of orbits times the order of the group is at least the size of the
set: each orbit has at most `|G|` points. -/
theorem card_le_orbits_mul {G X : Type*} [Group G] [Fintype G] [MulAction G X] [Fintype X]
    [DecidableEq (MulAction.orbitRel.Quotient G X)] :
    Fintype.card X ≤ Fintype.card G *
      (univ.image (Quotient.mk (MulAction.orbitRel G X))).card := by
  classical
  refine Finset.card_le_mul_card_image _ _ fun q _ => ?_
  obtain ⟨x, rfl⟩ := Quotient.exists_rep q
  have hsub : (univ.filter fun y : X => Quotient.mk (MulAction.orbitRel G X) y =
      Quotient.mk (MulAction.orbitRel G X) x) ⊆ univ.image fun g : G => g • x := by
    intro y hy
    have hyx := Quotient.exact (Finset.mem_filter.mp hy).2
    obtain ⟨g, hg⟩ := hyx
    exact Finset.mem_image.mpr ⟨g, mem_univ _, hg⟩
  exact (Finset.card_le_card hsub).trans (Finset.card_image_le.trans (by simp))

/-- **The wiring count.** With a NOT of one earlier wire or an AND of an unordered pair at
every step, the programs of `S` gates on `N` inputs number `∏_{t=1}^S C(N+t, 2)`. -/
theorem wiring_count (N S : ℕ) :
    ∏ t ∈ range S, ((N + t) + (N + t).choose 2) = ∏ t ∈ range S, (N + t + 1).choose 2 :=
  Finset.prod_congr rfl fun t _ => gate_choices (N + t)

end CircuitCount

section GranularLocus
open Filter Topology

/-- **The granular count is faithful.** The counting measure of a subset of a nonempty
finite universe vanishes exactly when the subset is empty. -/
theorem granular_count_faithful {α : Type*} (V Ω : Finset α) (hΩ : Ω.Nonempty) :
    ((V.card : ℚ) / Ω.card = 0) ↔ V = ∅ := by
  have : (Ω.card : ℚ) ≠ 0 := by exact_mod_cast (Finset.card_pos.mpr hΩ).ne'
  rw [div_eq_zero_iff, or_iff_left this, Nat.cast_eq_zero, Finset.card_eq_zero]

/-- **Eventually is everywhere at infinity.** A property holds for all large `n` exactly
when it holds, along the hyperfilter, at every sequence tending to infinity, that is at
every infinite hypernatural. -/
theorem eventually_iff_hyper (P : ℕ → Prop) :
    (∀ᶠ n in atTop, P n) ↔
      ∀ s : ℕ → ℕ, Tendsto s atTop atTop → ∀ᶠ k in hyperfilter ℕ, P (s k) := by
  constructor
  · intro h s hs
    have h1 : ∀ᶠ k in atTop, P (s k) := hs.eventually h
    rw [← Nat.cofinite_eq_atTop] at h1
    exact hyperfilter_le_cofinite h1
  · intro h
    by_contra hno
    rw [not_eventually] at hno
    obtain ⟨φ, hφ, hP⟩ := extraction_of_frequently_atTop hno
    have := h φ hφ.tendsto_atTop
    obtain ⟨k, hk⟩ := this.exists
    exact hP k hk

/-- **The shadow vanishes for every bounded family.** If at most `C` valid programs sit in
a universe whose size tends to infinity, their share tends to `0`: the standard part of the
granular measure is `0` whether or not the valid set is empty, for 2-SAT as for 3-SAT. -/
theorem shadow_vanishes (v w : ℕ → ℕ) (C : ℕ) (hv : ∀ n, v n ≤ C)
    (hw : Tendsto w atTop atTop) :
    Tendsto (fun n => (v n : ℝ) / w n) atTop (𝓝 0) := by
  have hC : Tendsto (fun n => (C : ℝ) / w n) atTop (𝓝 0) :=
    (tendsto_const_div_atTop_nhds_zero_nat (C : ℝ)).comp hw
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hC
    (fun n => by positivity) (fun n => ?_)
  have h1 : (v n : ℝ) ≤ C := by exact_mod_cast hv n
  exact div_le_div_of_nonneg_right h1 (by positivity)

end GranularLocus

section SafeDerivation

theorem wires_getD_input {N : ℕ} (x : Fin N → Bool) (P : List (Fin 3 × ℕ × ℕ)) (i : Fin N) :
    (wires x P).getD i false = x i := by
  obtain ⟨T, hT⟩ := foldl_step_prefix (List.ofFn x) P
  simp only [wires, hT]
  rw [List.getD_append _ _ _ _ (by simp)]
  simp

/-- **Distinct computed functions cost one gate each.** If a program computes every function
in `F` and none of them is an input bit, then `F` has at most as many elements as the program
has gates. -/
theorem card_computed_le {N : ℕ} (P : List (Fin 3 × ℕ × ℕ))
    (F : Finset ((Fin N → Bool) → Bool)) (hF : ∀ f ∈ F, Computes P f)
    (hin : ∀ f ∈ F, ∀ i : Fin N, f ≠ fun x => x i) : F.card ≤ P.length := by
  classical
  choose! idx hlt hval using hF
  have hge : ∀ f ∈ F, N ≤ idx f := by
    intro f hf
    by_contra h
    push_neg at h
    refine hin f hf ⟨idx f, h⟩ (funext fun x => ?_)
    rw [← hval f hf x]
    exact wires_getD_input x P ⟨idx f, h⟩
  have hinj : Set.InjOn (fun f => idx f - N) F := by
    intro f hf g hg h
    have h' : idx f = idx g := by
      have := hge f hf; have := hge g hg; simp only at h; omega
    funext x
    rw [← hval f hf x, ← hval g hg x, h']
  have hsub : F.image (fun f => idx f - N) ⊆ range P.length := by
    intro k hk
    obtain ⟨f, hf, rfl⟩ := Finset.mem_image.mp hk
    have := hlt f hf; have := hge f hf
    exact Finset.mem_range.mpr (by omega)
  calc F.card = (F.image fun f => idx f - N).card := (Finset.card_image_of_injOn hinj).symm
    _ ≤ (range P.length).card := Finset.card_le_card hsub
    _ = P.length := Finset.card_range _

/-- **Conditional size bound.** If every program computing `g` must compute each of `W`
distinct functions none of which is an input bit, every program for `g` has at least `W`
gates. -/
theorem blocks_force_size {N W : ℕ} (g : (Fin N → Bool) → Bool)
    (blocks : Finset ((Fin N → Bool) → Bool)) (hW : W ≤ blocks.card)
    (hin : ∀ f ∈ blocks, ∀ i : Fin N, f ≠ fun x => x i)
    (hfac : ∀ P : List (Fin 3 × ℕ × ℕ), Computes P g → ∀ f ∈ blocks, Computes P f)
    (P : List (Fin 3 × ℕ × ℕ)) (hP : Computes P g) : W ≤ P.length :=
  hW.trans (card_computed_le P blocks (hfac P hP) hin)

/-- **Repeated blocks cost nothing.** Over `F₂` a 0/1 value is idempotent, so a product of
`k ≥ 1` copies of one block is that block: a count of blocks with repetition bounds no
gate count. -/
theorem block_pow_idem (b : ZMod 2) (k : ℕ) (hk : 1 ≤ k) : b ^ k = b := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hk
  induction m with
  | zero => simp
  | succ m ih =>
    rw [← add_assoc, pow_succ, ih (by omega)]
    fin_cases b <;> rfl

/-- The program `x₀ ∨ (x₁ ∧ x₂)`. -/
def peelProg : List (Fin 3 × ℕ × ℕ) := [(0, 1, 2), (1, 0, 3)]

/-- **A product of blocks without the blocks.** The program `x₀ ∨ (x₁ ∧ x₂)` computes the
product of the blocks `x₀ ∨ x₁` and `x₀ ∨ x₂` and computes neither block: a circuit for a
product of witness blocks need not contain the blocks as wires. -/
theorem peel_avoids_blocks :
    Computes peelProg (fun x : Fin 3 → Bool => (x 0 || x 1) && (x 0 || x 2)) ∧
      ¬ Computes peelProg (fun x : Fin 3 → Bool => x 0 || x 1) ∧
      ¬ Computes peelProg (fun x : Fin 3 → Bool => x 0 || x 2) := by
  unfold Computes peelProg
  decide

end SafeDerivation

section ShiftSpan

/-- Convolution over the group of subsets under symmetric difference, over `F₂`. -/
def sconv {N : ℕ} (f h : Finset (Fin N) → ZMod 2) (S : Finset (Fin N)) : ZMod 2 :=
  ∑ U : Finset (Fin N), f U * h (symmDiff S U)

/-- **A function convolved with itself is its sum times the identity.** In characteristic
two the terms for `U` and `S ∆ U` cancel unless `S = ∅`. -/
theorem sconv_self {N : ℕ} (f : Finset (Fin N) → ZMod 2) (S : Finset (Fin N)) :
    sconv f f S = if S = ∅ then ∑ U, f U else 0 := by
  unfold sconv
  split_ifs with hS
  · subst hS
    refine Finset.sum_congr rfl fun U _ => ?_
    rw [show symmDiff (∅ : Finset (Fin N)) U = U by simp]
    generalize f U = a; fin_cases a <;> rfl
  · refine Finset.sum_involution (fun U _ => symmDiff S U) (fun U _ => ?_) (fun U _ _ => ?_)
      (fun U _ => mem_univ _) (fun U _ => by simp [symmDiff_symmDiff_cancel_left])
    · rw [symmDiff_symmDiff_cancel_left, mul_comm]
      generalize f (symmDiff S U) * f U = a; fin_cases a <;> rfl
    · intro h
      apply hS
      have : symmDiff S U = symmDiff ∅ U := by simpa using h
      exact symmDiff_left_injective U this

/-- Reindexing by `V ↦ V ∆ U`. -/
theorem sum_symmDiff_reindex {N : ℕ} (U : Finset (Fin N)) (φ : Finset (Fin N) → ZMod 2) :
    ∑ V : Finset (Fin N), φ (symmDiff V U) = ∑ W : Finset (Fin N), φ W := by
  refine Fintype.sum_equiv ⟨fun V => symmDiff V U, fun W => symmDiff W U, fun V => ?_,
    fun W => ?_⟩ _ _ fun V => rfl
  · simp [symmDiff_assoc]
  · simp [symmDiff_assoc]

theorem sconv_sconv_self {N : ℕ} (c f : Finset (Fin N) → ZMod 2) (S : Finset (Fin N)) :
    sconv (sconv c f) f S = c S * ∑ U, f U := by
  unfold sconv
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  have key : ∀ U : Finset (Fin N), ∑ V : Finset (Fin N), c U * f (symmDiff V U) * f (symmDiff S V) =
      c U * sconv f f (symmDiff S U) := by
    intro U
    unfold sconv
    rw [Finset.mul_sum]
    rw [← sum_symmDiff_reindex U (fun W => c U * (f W * f (symmDiff (symmDiff S U) W)))]
    refine Finset.sum_congr rfl fun V _ => ?_
    have : symmDiff (symmDiff S U) (symmDiff V U) = symmDiff S V := by
      rw [symmDiff_comm V U, symmDiff_assoc, ← symmDiff_assoc U U V]; simp
    rw [this, mul_assoc]
  simp_rw [key, sconv_self]
  rw [Finset.sum_eq_single S]
  · simp
  · intro U _ hU
    have : symmDiff S U ≠ ∅ := by
      intro h; exact hU (symmDiff_eq_bot.mp h).symm
    simp [this]
  · intro h; exact absurd (mem_univ S) h

/-- **Full shift span.** If the top monomial of `f` survives over `F₂` (its coefficient
`Σ_S f S` is `1`), the `2^N` shifts `S ↦ f (S ∆ U)` are linearly independent: no nonzero
combination of them vanishes. The derivatives `∂_U f` span the same space, so it is all of
`F₂^(2^N)`. -/
theorem shifts_independent {N : ℕ} (f : Finset (Fin N) → ZMod 2) (htop : anf f univ = 1)
    (c : Finset (Fin N) → ZMod 2) (h : ∀ S, ∑ U : Finset (Fin N), c U * f (symmDiff S U) = 0) :
    c = 0 := by
  have hsum : ∑ U, f U = 1 := by
    rw [← htop]; unfold anf; simp
  funext S
  have h1 : sconv c f = 0 := funext fun T => h T
  have := sconv_sconv_self c f S
  rw [h1, hsum, mul_one] at this
  simpa [sconv] using this.symm

end ShiftSpan

section CoupledScaling

/-- Input renaming for restriction: input `w < N` goes to the input `σ w` of the smaller
circuit, or to the constant-zero wire `M + 1`; gate wires shift by `M + 2 - N`. -/
def renW {N M : ℕ} (σ : Fin N → Option (Fin M)) (w : ℕ) : ℕ :=
  if h : w < N then (match σ ⟨w, h⟩ with | some k => (k : ℕ) | none => M + 1) else w - N + M + 2

/-- The restricted program: `NOT y₀`, then `y₀ ∧ ¬y₀ = 0`, then the renamed gates. -/
def restrictProg {N M : ℕ} (σ : Fin N → Option (Fin M)) (P : List (Fin 3 × ℕ × ℕ)) :
    List (Fin 3 × ℕ × ℕ) :=
  [(2, 0, 0), (0, 0, M)] ++ P.map fun g => (g.1, renW σ g.2.1, renW σ g.2.2)

/-- The substituted input: `x_w = y_{σ w}`, or `0` where `σ w` is undefined. -/
def substIn {N M : ℕ} (σ : Fin N → Option (Fin M)) (y : Fin M → Bool) : Fin N → Bool :=
  fun w => match σ w with | some k => y k | none => false

theorem renW_lt {N M : ℕ} (σ : Fin N → Option (Fin M)) (w L : ℕ) (hw : w < N + L) :
    renW σ w < M + 2 + L := by
  unfold renW
  split_ifs with h
  · cases σ ⟨w, h⟩ <;> simp <;> omega
  · omega

theorem restrict_wires {N M : ℕ} (hM : 0 < M) (σ : Fin N → Option (Fin M))
    (y : Fin M → Bool) (P : List (Fin 3 × ℕ × ℕ)) (w : ℕ) :
    (wires y (restrictProg σ P)).getD (renW σ w) false = (wires (substIn σ y) P).getD w false := by
  induction P using List.reverseRecOn generalizing w with
  | nil =>
    have h0 : wires y (restrictProg σ []) =
        List.ofFn y ++ [!y ⟨0, hM⟩] ++ [y ⟨0, hM⟩ && !y ⟨0, hM⟩] := by
      simp [restrictProg, wires, step, opB, List.getD_append, hM]
    rw [h0]
    simp only [wires, List.foldl_nil]
    unfold renW
    split_ifs with h
    · have hx : (List.ofFn (substIn σ y)).getD w false = substIn σ y ⟨w, h⟩ := by
        simp [List.getD_eq_getElem?_getD, h]
      rw [hx]
      unfold substIn
      cases hs : σ ⟨w, h⟩ with
      | none =>
        simp only
        rw [List.getD_append_right _ _ _ _ (by simp)]
        simp
      | some k =>
        simp only
        rw [List.getD_append _ _ _ _ (by simp), List.getD_append _ _ _ _ (by simp)]
        simp [List.getD_eq_getElem?_getD]
    · rw [List.getD_eq_default _ _ (by simp), List.getD_eq_default _ _ (by simp; omega)]
  | append_singleton Q g ih =>
    have hQ : restrictProg σ (Q ++ [g]) =
        restrictProg σ Q ++ [(g.1, renW σ g.2.1, renW σ g.2.2)] := by
      simp [restrictProg]
    rw [hQ, wires_snoc, wires_snoc, step_getD, step_getD]
    have hl1 : (wires y (restrictProg σ Q)).length = M + 2 + Q.length := by
      rw [wires_length]; simp [restrictProg]; omega
    have hl2 := wires_length (substIn σ y) Q
    rw [hl1, hl2]
    by_cases hw : w < N + Q.length
    · rw [if_pos (renW_lt σ w _ hw), if_pos hw, ih]
    · rw [if_neg hw]
      have hr : renW σ w = w - N + M + 2 := by
        unfold renW; rw [dif_neg (by omega)]
      rw [hr, if_neg (by omega)]
      by_cases he : w = N + Q.length
      · rw [if_pos (by omega), if_pos he, ih, ih]
      · rw [if_neg (by omega), if_neg he]

/-- **Restriction costs two gates.** Substituting inputs of a smaller circuit, or the
constant `0`, for the inputs of a program gives a program on the smaller input set with
two more gates (they build the constant). -/
theorem restrict_computes {N M : ℕ} (hM : 0 < M) (σ : Fin N → Option (Fin M))
    {P : List (Fin 3 × ℕ × ℕ)} {f : (Fin N → Bool) → Bool}
    (hP : ComputesOn P f Set.univ) :
    (restrictProg σ P).length = P.length + 2 ∧
      ComputesOn (restrictProg σ P) (fun y => f (substIn σ y)) Set.univ := by
  obtain ⟨i, hi, hf⟩ := hP
  refine ⟨by simp [restrictProg], renW σ i, ?_, fun y _ => ?_⟩
  · have := renW_lt σ i P.length hi
    simp [restrictProg]; omega
  · rw [restrict_wires hM, hf _ (Set.mem_univ _)]

/-- A 3-clause on `n` variables: indices `i < j < k` and the falsifying pattern. -/
structure Clause3 (n : ℕ) where
  i : Fin n
  j : Fin n
  k : Fin n
  hij : i < j
  hjk : j < k
  bi : Bool
  bj : Bool
  bk : Bool
  deriving DecidableEq

/-- `c.blocks x`: the assignment `x` falsifies `c`. -/
def Clause3.blocks {n : ℕ} (c : Clause3 n) (x : Fin n → Bool) : Bool :=
  (x c.i == c.bi) && (x c.j == c.bj) && (x c.k == c.bk)

/-- Clauses as a finite type: the variable triple and pattern determine the clause. -/
def Clause3.toTuple {n : ℕ} (c : Clause3 n) : (Fin n × Fin n × Fin n) × Bool × Bool × Bool :=
  ((c.i, c.j, c.k), c.bi, c.bj, c.bk)

theorem Clause3.toTuple_injective {n : ℕ} : Function.Injective (Clause3.toTuple (n := n)) := by
  rintro ⟨_, _, _, _, _, _, _, _⟩ ⟨_, _, _, _, _, _, _, _⟩ h
  simp only [Clause3.toTuple, Prod.mk.injEq] at h
  obtain ⟨⟨rfl, rfl, rfl⟩, rfl, rfl, rfl⟩ := h
  rfl

noncomputable instance {n : ℕ} : Fintype (Clause3 n) :=
  Fintype.ofInjective _ Clause3.toTuple_injective

/-- Witness block over `F₂`: `B_x(e) = 1 + ∏_{c blocks x} (1 + e_c)`. -/
noncomputable def witnessBlock {n : ℕ} (x : Fin n → Bool) (e : Clause3 n → ZMod 2) : ZMod 2 :=
  1 + ∏ c : Clause3 n, if c.blocks x then (1 + e c) else 1

/-- The 3-SAT switchboard polynomial `g(e) = 1 + ∏_x B_x(e)` over `F₂`. -/
noncomputable def g3SAT (n : ℕ) (e : Clause3 n → ZMod 2) : ZMod 2 :=
  1 + ∏ x : (Fin n → Bool), witnessBlock x e

theorem zmod2_cases (a : ZMod 2) : a = 0 ∨ a = 1 := by
  fin_cases a
  · exact Or.inl rfl
  · exact Or.inr rfl

theorem prod_one_add_zmod2 {ι : Type*} (s : Finset ι) (u : ι → ZMod 2) :
    (∏ c ∈ s, (1 + u c)) = if ∀ c ∈ s, u c = 0 then 1 else 0 := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, ih]
    rcases zmod2_cases (u a) with h | h
    · simp [h]
    · have : (1 : ZMod 2) + 1 = 0 := by decide
      simp [h, this]

theorem witnessBlock_eq {n : ℕ} (x : Fin n → Bool) (e : Clause3 n → ZMod 2) :
    witnessBlock x e = if ∃ c, c.blocks x = true ∧ e c = 1 then 1 else 0 := by
  classical
  unfold witnessBlock
  rw [← Finset.prod_filter, prod_one_add_zmod2]
  by_cases h : ∃ c, c.blocks x = true ∧ e c = 1
  · obtain ⟨c, hc, he⟩ := h
    rw [if_neg (fun hall => by simpa [he] using hall c (by simp [hc])), if_pos ⟨c, hc, he⟩]
    simp
  · push_neg at h
    rw [if_pos (fun c hc => (zmod2_cases _).resolve_right (h c (by simpa using hc))),
      if_neg (by push_neg; exact h)]
    decide

/-- **The polynomial decides satisfiability.** `g(e) = 1` exactly when some assignment
falsifies no present clause. -/
theorem g3SAT_eq (n : ℕ) (e : Clause3 n → ZMod 2) :
    g3SAT n e = if ∃ x, ∀ c, c.blocks x = true → e c = 0 then 1 else 0 := by
  classical
  unfold g3SAT
  simp_rw [witnessBlock_eq]
  have hp : (∏ x : Fin n → Bool, (if ∃ c, c.blocks x = true ∧ e c = 1 then (1 : ZMod 2) else 0))
      = if ∀ x : Fin n → Bool, ∃ c, c.blocks x = true ∧ e c = 1 then 1 else 0 := by
    rw [Finset.prod_ite_zero]; simp
  rw [hp]
  by_cases h : ∃ x, ∀ c, c.blocks x = true → e c = 0
  · obtain ⟨x, hx⟩ := h
    rw [if_neg (fun hall => by
        obtain ⟨c, hc, he⟩ := hall x
        rw [hx c hc] at he; exact absurd he (by decide)), if_pos ⟨x, hx⟩]
    simp
  · rw [if_neg h, if_pos (fun x => by
      push_neg at h
      obtain ⟨c, hc, he⟩ := h x
      exact ⟨c, hc, (zmod2_cases _).resolve_left he⟩)]
    decide

/-- Embedding of a clause on `m` variables into `n ≥ m` variables. -/
def embedClause {m n : ℕ} (hmn : m ≤ n) (c : Clause3 m) : Clause3 n where
  i := Fin.castLE hmn c.i
  j := Fin.castLE hmn c.j
  k := Fin.castLE hmn c.k
  hij := Fin.lt_def.mpr (Fin.lt_def.mp c.hij)
  hjk := Fin.lt_def.mpr (Fin.lt_def.mp c.hjk)
  bi := c.bi
  bj := c.bj
  bk := c.bk

theorem embedClause_injective {m n : ℕ} (hmn : m ≤ n) :
    Function.Injective (embedClause hmn) := by
  rintro ⟨_, _, _, _, _, _, _, _⟩ ⟨_, _, _, _, _, _, _, _⟩ h
  simp only [embedClause, Clause3.mk.injEq, Fin.castLE_inj] at h
  obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩ := h
  rfl

/-- Zero-padded lift of a switchboard: clauses touching a variable `≥ m` are off. -/
noncomputable def liftSB {α : Type*} (z : α) {m n : ℕ} (hmn : m ≤ n) (e : Clause3 m → α)
    (c : Clause3 n) : α :=
  if h : ∃ c₀, embedClause hmn c₀ = c then e h.choose else z

theorem liftSB_embed {α : Type*} (z : α) {m n : ℕ} (hmn : m ≤ n) (e : Clause3 m → α)
    (c₀ : Clause3 m) : liftSB z hmn e (embedClause hmn c₀) = e c₀ := by
  have hex : ∃ c₁, embedClause hmn c₁ = embedClause hmn c₀ := ⟨c₀, rfl⟩
  unfold liftSB
  rw [dif_pos hex, embedClause_injective hmn hex.choose_spec]

theorem blocks_embed {m n : ℕ} (hmn : m ≤ n) (c : Clause3 m) (x : Fin n → Bool) :
    (embedClause hmn c).blocks x = c.blocks (fun t => x (Fin.castLE hmn t)) := rfl

/-- The clauses present under a lift are the embedded present clauses. -/
theorem lift_sat_iff {α : Type*} (z : α) (P : α → Prop) (hz : P z) {m n : ℕ} (hmn : m ≤ n)
    (e : Clause3 m → α) :
    (∃ x : Fin n → Bool, ∀ c, c.blocks x = true → P (liftSB z hmn e c)) ↔
      ∃ y : Fin m → Bool, ∀ c, c.blocks y = true → P (e c) := by
  constructor
  · rintro ⟨x, hx⟩
    refine ⟨fun t => x (Fin.castLE hmn t), fun c hc => ?_⟩
    have := hx (embedClause hmn c) (by rw [blocks_embed]; exact hc)
    rwa [liftSB_embed] at this
  · rintro ⟨y, hy⟩
    refine ⟨fun t => if h : (t : ℕ) < m then y ⟨t, h⟩ else false, fun c hc => ?_⟩
    unfold liftSB
    split_ifs with h
    · apply hy
      have hc' := h.choose_spec ▸ hc
      rw [blocks_embed] at hc'
      convert hc' using 2
      funext t
      simp [t.2]
    · exact hz

/-- **Theorem (downward self-reducibility).** Padding a switchboard on `m` variables with
zeros leaves the switchboard polynomial on `n ≥ m` variables equal to the one on `m`. -/
theorem subcube_projection_invariant {m n : ℕ} (hmn : m ≤ n) (e : Clause3 m → ZMod 2) :
    g3SAT n (liftSB 0 hmn e) = g3SAT m e := by
  classical
  rw [g3SAT_eq, g3SAT_eq]
  congr 1
  exact propext (lift_sat_iff 0 (· = 0) rfl hmn e)

/-- The Boolean switchboard decision function. -/
noncomputable def sat3B (n : ℕ) (e : Clause3 n → Bool) : Bool :=
  decide (∃ x : Fin n → Bool, ∀ c, c.blocks x = true → e c = false)

/-- The switchboard function on `Fin N` inputs, through a fixed numbering of the clauses. -/
noncomputable def sat3Fin (n : ℕ) (y : Fin (Fintype.card (Clause3 n)) → Bool) : Bool :=
  sat3B n (y ∘ Fintype.equivFin (Clause3 n))

theorem clause3_nonempty {m : ℕ} (hm : 3 ≤ m) : 0 < Fintype.card (Clause3 m) :=
  Fintype.card_pos_iff.mpr ⟨Clause3.mk ⟨0, by omega⟩ ⟨1, by omega⟩ ⟨2, by omega⟩
    (by simp [Fin.lt_def]) (by simp [Fin.lt_def]) false false false⟩

/-- **Circuit size is monotone in the number of variables, up to two gates.** For
`3 ≤ m ≤ n`, the least circuit deciding the 3-SAT switchboard on `m` variables has at most
two more gates than the least one on `n` variables: hardwire the clauses touching a
variable `≥ m` to `0` (two gates build the constant). -/
theorem sat3_size_mono {m n : ℕ} (hm : 3 ≤ m) (hmn : m ≤ n) :
    minCircuitSize (sat3Fin m) Set.univ ≤ minCircuitSize (sat3Fin n) Set.univ + 2 := by
  classical
  set Em := Fintype.equivFin (Clause3 m)
  set En := Fintype.equivFin (Clause3 n)
  have hn3 : 3 ≤ n := hm.trans hmn
  have hN : 1 ≤ Fintype.card (Clause3 n) := clause3_nonempty hn3
  obtain ⟨P0, -, hP0⟩ := lookup_exists hN (sat3Fin n) Finset.univ
  have hne : {k | ∃ P : List (Fin 3 × ℕ × ℕ), P.length = k ∧
      ComputesOn P (sat3Fin n) Set.univ}.Nonempty := ⟨_, P0, rfl, by simpa using hP0⟩
  obtain ⟨P, hPl, hP⟩ := Nat.sInf_mem hne
  let σ : Fin (Fintype.card (Clause3 n)) → Option (Fin (Fintype.card (Clause3 m))) :=
    fun j => if h : ∃ c₀, embedClause hmn c₀ = En.symm j then some (Em h.choose) else none
  obtain ⟨hlen, hQ⟩ := restrict_computes (clause3_nonempty hm) σ hP
  have hfun : (fun y => sat3Fin n (substIn σ y)) = sat3Fin m := by
    funext y
    have hsub : (substIn σ y) ∘ En = liftSB false hmn (y ∘ Em) := by
      funext c
      simp only [Function.comp, substIn, σ, Equiv.symm_apply_apply, liftSB]
      split_ifs <;> rfl
    unfold sat3Fin sat3B
    rw [hsub]
    congr 1
    exact propext (lift_sat_iff false (· = false) rfl hmn _)
  rw [hfun] at hQ
  refine (Nat.sInf_le (s := {k | ∃ P : List (Fin 3 × ℕ × ℕ), P.length = k ∧
      ComputesOn P (sat3Fin m) Set.univ}) ⟨_, rfl, hQ⟩).trans (le_of_eq ?_)
  rw [hlen, hPl]; rfl

/-- **Two disjoint cores leave no switch sensitive.** If the present clauses contain two
disjoint unsatisfiable sets, flipping any single switch keeps the formula unsatisfiable:
the configuration of several disjoint cores has sensitivity `0`, not `8` per core. -/
theorem two_cores_insensitive {n : ℕ} (e : Clause3 n → Bool) (A B : Finset (Clause3 n))
    (hAB : Disjoint A B) (hA : ∀ c ∈ A, e c = true) (hB : ∀ c ∈ B, e c = true)
    (hAu : ∀ x, ∃ c ∈ A, c.blocks x = true) (hBu : ∀ x, ∃ c ∈ B, c.blocks x = true)
    (c₀ : Clause3 n) (b : Bool) : sat3B n (Function.update e c₀ b) = false := by
  classical
  unfold sat3B
  simp only [decide_eq_false_iff_not, not_exists, not_forall, exists_prop]
  intro x
  by_cases hc : c₀ ∈ A
  · obtain ⟨c, hcB, hbl⟩ := hBu x
    have hne : c ≠ c₀ := fun h => Finset.disjoint_left.mp hAB hc (h ▸ hcB)
    exact ⟨c, hbl, by rw [Function.update_of_ne hne, hB c hcB]; decide⟩
  · obtain ⟨c, hcA, hbl⟩ := hAu x
    have hne : c ≠ c₀ := fun h => hc (h ▸ hcA)
    exact ⟨c, hbl, by rw [Function.update_of_ne hne, hA c hcA]; decide⟩

end CoupledScaling

section ReadOnceBarrier

/-! ### Clause combinatorics -/

/-- The variables of a clause. -/
def Clause3.vars {n : ℕ} (c : Clause3 n) : Finset (Fin n) := {c.i, c.j, c.k}

/-- The value a clause forbids at one of its variables. -/
def Clause3.lit {n : ℕ} (c : Clause3 n) (a : Fin n) : Bool :=
  if a = c.i then c.bi else if a = c.j then c.bj else c.bk

/-- The falsifying assignment of a clause, `false` off its variables. -/
def Clause3.pt {n : ℕ} (c : Clause3 n) : Fin n → Bool :=
  fun v => if v ∈ c.vars then c.lit v else false

theorem Clause3.blocks_iff {n : ℕ} (c : Clause3 n) (x : Fin n → Bool) :
    c.blocks x = true ↔ x c.i = c.bi ∧ x c.j = c.bj ∧ x c.k = c.bk := by
  simp [Clause3.blocks, Bool.and_eq_true, beq_iff_eq, and_assoc]

theorem Clause3.ne_ij {n : ℕ} (c : Clause3 n) : c.i ≠ c.j := ne_of_lt c.hij
theorem Clause3.ne_jk {n : ℕ} (c : Clause3 n) : c.j ≠ c.k := ne_of_lt c.hjk
theorem Clause3.ne_ik {n : ℕ} (c : Clause3 n) : c.i ≠ c.k := ne_of_lt (c.hij.trans c.hjk)

theorem Clause3.lit_i {n : ℕ} (c : Clause3 n) : c.lit c.i = c.bi := by simp [Clause3.lit]
theorem Clause3.lit_j {n : ℕ} (c : Clause3 n) : c.lit c.j = c.bj := by
  simp [Clause3.lit, c.ne_ij.symm]
theorem Clause3.lit_k {n : ℕ} (c : Clause3 n) : c.lit c.k = c.bk := by
  simp [Clause3.lit, c.ne_ik.symm, c.ne_jk.symm]

theorem Clause3.mem_vars {n : ℕ} (c : Clause3 n) (a : Fin n) :
    a ∈ c.vars ↔ a = c.i ∨ a = c.j ∨ a = c.k := by simp [Clause3.vars]

theorem Clause3.blocks_pt {n : ℕ} (c : Clause3 n) : c.blocks c.pt = true := by
  rw [Clause3.blocks_iff]
  simp only [Clause3.pt, Clause3.mem_vars, true_or, or_true, if_true, c.lit_i, c.lit_j, c.lit_k]
  exact ⟨trivial, trivial, trivial⟩

/-- A blocked assignment takes the forbidden value at every variable of the clause. -/
theorem Clause3.blocks_lit {n : ℕ} {c : Clause3 n} {x : Fin n → Bool} (h : c.blocks x = true)
    {a : Fin n} (ha : a ∈ c.vars) : x a = c.lit a := by
  rw [Clause3.blocks_iff] at h
  rcases (c.mem_vars a).mp ha with rfl | rfl | rfl
  · rw [c.lit_i]; exact h.1
  · rw [c.lit_j]; exact h.2.1
  · rw [c.lit_k]; exact h.2.2

theorem Clause3.ext' {n : ℕ} {c d : Clause3 n} (hi : c.i = d.i) (hj : c.j = d.j) (hk : c.k = d.k)
    (hbi : c.bi = d.bi) (hbj : c.bj = d.bj) (hbk : c.bk = d.bk) : c = d := by
  cases c; cases d; simp_all

theorem Clause3.vars_eq {n : ℕ} {c d : Clause3 n} (h : c.vars = d.vars) :
    c.i = d.i ∧ c.j = d.j ∧ c.k = d.k := by
  have m : ∀ a, a ∈ c.vars ↔ a ∈ d.vars := fun a => by rw [h]
  have h1 := (m c.i).mp (by simp [Clause3.vars])
  have h2 := (m c.j).mp (by simp [Clause3.vars])
  have h3 := (m c.k).mp (by simp [Clause3.vars])
  have h4 := (m d.i).mpr (by simp [Clause3.vars])
  have h5 := (m d.j).mpr (by simp [Clause3.vars])
  have h6 := (m d.k).mpr (by simp [Clause3.vars])
  simp only [Clause3.mem_vars] at h1 h2 h3 h4 h5 h6
  have a1 := c.hij; have a2 := c.hjk; have b1 := d.hij; have b2 := d.hjk
  simp only [Fin.lt_def] at a1 a2 b1 b2
  simp only [Fin.ext_iff] at h1 h2 h3 h4 h5 h6 ⊢
  omega

/-- **One clause per triple and assignment.** Two clauses on the same variables that
block the same assignment are equal. -/
theorem Clause3.eq_of_blocks {n : ℕ} {c d : Clause3 n} (h : c.vars = d.vars) {x : Fin n → Bool}
    (hc : c.blocks x = true) (hd : d.blocks x = true) : c = d := by
  obtain ⟨hi, hj, hk⟩ := Clause3.vars_eq h
  rw [Clause3.blocks_iff] at hc hd
  exact Clause3.ext' hi hj hk (by rw [← hc.1, ← hd.1, hi]) (by rw [← hc.2.1, ← hd.2.1, hj])
    (by rw [← hc.2.2, ← hd.2.2, hk])

/-- **Every triple and assignment have a clause.** -/
theorem exists_clause_of_card {n : ℕ} (s : Finset (Fin n)) (hs : s.card = 3) (x : Fin n → Bool) :
    ∃ c : Clause3 n, c.vars = s ∧ c.blocks x = true := by
  set f := s.orderEmbOfFin hs
  refine ⟨⟨f 0, f 1, f 2, f.strictMono (by decide), f.strictMono (by decide),
    x (f 0), x (f 1), x (f 2)⟩, ?_, ?_⟩
  · ext a
    simp only [Clause3.vars, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro (rfl | rfl | rfl) <;> exact s.orderEmbOfFin_mem hs _
    · intro ha
      obtain ⟨t, rfl⟩ : a ∈ Set.range f := by rw [Finset.range_orderEmbOfFin]; exact ha
      fin_cases t <;> simp
  · rw [Clause3.blocks_iff]; exact ⟨rfl, rfl, rfl⟩

theorem card_vars {n : ℕ} (c : Clause3 n) : c.vars.card = 3 := by
  simp [Clause3.vars, c.ne_ij, c.ne_jk, c.ne_ik]

/-- The configuration holding exactly the clauses on the variables `s`. -/
def coreOn {n : ℕ} (s : Finset (Fin n)) : Clause3 n → Bool := fun d => decide (d.vars = s)

/-- Satisfiability of a configuration, as a proposition. -/
def SatC {n : ℕ} (e : Clause3 n → Bool) : Prop := ∃ x : Fin n → Bool, ∀ c, c.blocks x = true → e c = false

theorem sat3B_iff {n : ℕ} (e : Clause3 n → Bool) : sat3B n e = true ↔ SatC e := by
  simp [sat3B, SatC]

theorem satC_mono {n : ℕ} {e e' : Clause3 n → Bool} (h : ∀ c, e c = true → e' c = true)
    (h' : SatC e') : SatC e := by
  obtain ⟨x, hx⟩ := h'
  refine ⟨x, fun c hc => ?_⟩
  by_contra hne
  have := hx c hc
  rw [h c (by simpa using hne)] at this
  exact absurd this (by decide)

theorem coreOn_unsat {n : ℕ} (s : Finset (Fin n)) (hs : s.card = 3) : ¬ SatC (coreOn s) := by
  rintro ⟨x, hx⟩
  obtain ⟨c, hcs, hc⟩ := exists_clause_of_card s hs x
  have := hx c hc
  simp [coreOn, hcs] at this

theorem coreOn_minimal {n : ℕ} (d : Clause3 n) :
    SatC (Function.update (coreOn d.vars) d false) := by
  refine ⟨d.pt, fun c hc => ?_⟩
  by_cases hcd : c = d
  · subst hcd; simp
  · rw [Function.update_of_ne hcd]
    simp only [coreOn, decide_eq_false_iff_not]
    intro hv
    exact hcd (Clause3.eq_of_blocks hv hc d.blocks_pt)


/-! ### Circuits with one binary gate fewer than inputs split at the top -/

/-- The number of two-input gates of a program. -/
def binCount (P : List (Fin 3 × ℕ × ℕ)) : ℕ := (P.filter fun g => g.1 ≠ 2).length

/-- `f` depends on every input. -/
def Essential {N : ℕ} (f : (Fin N → Bool) → Bool) : Prop :=
  ∀ j, ∃ x, f x ≠ f (Function.update x j (!x j))

/-- An essential function that depends only on the inputs in `p` has every input in `p`. -/
theorem essential_support {N : ℕ} {f : (Fin N → Bool) → Bool} (hf : Essential f) (p : Fin N → Prop)
    (h : ∀ x y : Fin N → Bool, (∀ j, p j → x j = y j) → f x = f y) : ∀ j, p j := by
  intro j
  by_contra hj
  obtain ⟨x, hx⟩ := hf j
  exact hx (h _ _ fun k hk => by
    have : k ≠ j := fun e => hj (e ▸ hk)
    rw [Function.update_of_ne this])

/-- An essential function of `N` inputs needs `N - 1` two-input gates. -/
theorem no_compute_few {N : ℕ} {Q : List (Fin 3 × ℕ × ℕ)} {f : (Fin N → Bool) → Bool}
    (hf : Essential f) (hQ : Computes Q f) (hb : binCount Q + 2 ≤ N) : False := by
  classical
  obtain ⟨i, -, hi⟩ := hQ
  obtain ⟨c, hc, hw⟩ := wire_classes (N := N) Q
  obtain ⟨l, hl⟩ := hw i
  have hall := essential_support hf (fun j => c j = l) (fun x y h => by rw [← hi, ← hi]; exact hl x y h)
  have himg : univ.image c ⊆ {l} := fun a ha => by
    obtain ⟨j, -, rfl⟩ := Finset.mem_image.mp ha; simp [hall j]
  have := Finset.card_le_card himg
  simp only [Finset.card_singleton] at this
  unfold binCount at hb
  omega

/-- A split at the top: `f = s ⊕ (u ∘ v)` for a two-input gate `∘`, with `u` and `v`
reading complementary nonempty sets of inputs. -/
def TopSplit {N : ℕ} (f : (Fin N → Bool) → Bool) : Prop :=
  ∃ X : Finset (Fin N), (∃ j, j ∈ X) ∧ (∃ j, j ∉ X) ∧
    ∃ (u v : (Fin N → Bool) → Bool) (o : Fin 3) (s : Bool), o ≠ 2 ∧
      (∀ x y : Fin N → Bool, (∀ j ∈ X, x j = y j) → u x = u y) ∧
      (∀ x y : Fin N → Bool, (∀ j ∉ X, x j = y j) → v x = v y) ∧
      ∀ x, f x = (s ^^ opB o (u x) (v x))

/-- **Read-once at the top.** A program computing an essential function of `N ≥ 2`
inputs with at most `N - 1` two-input gates splits the function at the top into two
functions of complementary sets of inputs. -/
theorem top_split {N : ℕ} (hN : 2 ≤ N) (P : List (Fin 3 × ℕ × ℕ)) :
    ∀ f : (Fin N → Bool) → Bool, Essential f → Computes P f → binCount P + 1 ≤ N → TopSplit f := by
  classical
  induction P using List.reverseRecOn with
  | nil =>
    intro f hf hP _
    exact (no_compute_few hf hP (by simp [binCount]; omega)).elim
  | append_singleton Q g ih =>
    intro f hf hP hb
    obtain ⟨i, hi, hfi⟩ := hP
    have hlen : ∀ x : Fin N → Bool, (wires x Q).length = N + Q.length := fun x => wires_length x Q
    have hbin : binCount (Q ++ [g]) = binCount Q + if g.1 ≠ 2 then 1 else 0 := by
      unfold binCount; by_cases h : g.1 = 2 <;> simp [List.filter_append, h]
    by_cases hin : i < N + Q.length
    · have hQ : Computes Q f := ⟨i, hin, fun x => by
        rw [← hfi x, wires_snoc, step_getD, hlen, if_pos hin]⟩
      by_cases hg : g.1 = 2
      · exact ih f hf hQ (by rw [hbin, if_neg (by simpa using hg)] at hb; simpa using hb)
      · exact (no_compute_few hf hQ (by rw [hbin, if_pos hg] at hb; omega)).elim
    · have hieq : i = N + Q.length := by simp at hi; omega
      have hfx : ∀ x, f x = opB g.1 ((wires x Q).getD g.2.1 false) ((wires x Q).getD g.2.2 false) :=
        fun x => by rw [← hfi x, wires_snoc, step_getD, hlen, if_neg hin, if_pos hieq]
      by_cases hg : g.1 = 2
      · -- a NOT gate on top: split its input
        set h : (Fin N → Bool) → Bool := fun x => (wires x Q).getD g.2.1 false
        have hfh : ∀ x, f x = !h x := fun x => by rw [hfx, hg]; rfl
        have hhe : Essential h := fun j => by
          obtain ⟨x, hx⟩ := hf j
          exact ⟨x, fun e => hx (by rw [hfh, hfh, e])⟩
        have hhc : Computes Q h := by
          by_cases ha : g.2.1 < N + Q.length
          · exact ⟨g.2.1, ha, fun x => rfl⟩
          · exfalso
            obtain ⟨x, hx⟩ := hf ⟨0, by omega⟩
            apply hx
            rw [hfh, hfh]
            simp only [h]
            rw [List.getD_eq_default _ _ (by rw [hlen]; omega), List.getD_eq_default _ _ (by rw [hlen]; omega)]
        obtain ⟨X, h1, h2, u, v, o, s, ho, hu, hv, hsplit⟩ :=
          ih h hhe hhc (by rw [hbin, if_neg (by simpa using hg)] at hb; simpa using hb)
        exact ⟨X, h1, h2, u, v, o, !s, ho, hu, hv, fun x => by rw [hfh, hsplit]; cases s <;> cases opB o (u x) (v x) <;> rfl⟩
      · obtain ⟨c, hc, hw⟩ := wire_classes (N := N) Q
        obtain ⟨la, hla⟩ := hw g.2.1
        obtain ⟨lb, hlb⟩ := hw g.2.2
        have hsupp := essential_support hf (fun j => c j = la ∨ c j = lb) (fun x y hxy => by
          rw [hfx, hfx, hla x y (fun j hj => hxy j (Or.inl hj)),
            hlb x y (fun j hj => hxy j (Or.inr hj))])
        rw [hbin, if_pos hg] at hb
        have hcard : 2 ≤ (univ.image c).card := by simp only [binCount] at hb; omega
        have hA : ∃ j, c j = la := by
          by_contra hno
          push_neg at hno
          have : univ.image c ⊆ {lb} := fun l hl => by
            obtain ⟨j, -, rfl⟩ := Finset.mem_image.mp hl
            simp [(hsupp j).resolve_left (hno j)]
          have := Finset.card_le_card this; simp at this; omega
        have hB : ∃ j, c j = lb := by
          by_contra hno
          push_neg at hno
          have : univ.image c ⊆ {la} := fun l hl => by
            obtain ⟨j, -, rfl⟩ := Finset.mem_image.mp hl
            simp [(hsupp j).resolve_right (hno j)]
          have := Finset.card_le_card this; simp at this; omega
        have hne : la ≠ lb := by
          intro e
          have : univ.image c ⊆ {la} := fun l hl => by
            obtain ⟨j, -, rfl⟩ := Finset.mem_image.mp hl
            rcases hsupp j with h | h <;> simp [h, e]
          have := Finset.card_le_card this; simp at this; omega
        obtain ⟨ja, hja⟩ := hA
        obtain ⟨jb, hjb⟩ := hB
        refine ⟨univ.filter fun j => c j = la, ⟨ja, by simp [hja]⟩, ⟨jb, by simp [hjb, Ne.symm hne]⟩,
          fun x => (wires x Q).getD g.2.1 false, fun x => (wires x Q).getD g.2.2 false, g.1, false,
          hg, fun x y h => hla x y (fun j hj => h j (by simp [hj])),
          fun x y h => hlb x y (fun j hj => h j (by simp [hj, Ne.symm hne])), fun x => ?_⟩
        rw [hfx]; simp

/-! ### The switchboard does not split at the top -/

theorem Clause3.blocks_congr {n : ℕ} (c : Clause3 n) {x y : Fin n → Bool}
    (h : ∀ a ∈ c.vars, x a = y a) : c.blocks x = c.blocks y := by
  simp only [Clause3.blocks]
  rw [h c.i (by simp [Clause3.vars]), h c.j (by simp [Clause3.vars]), h c.k (by simp [Clause3.vars])]

theorem Clause3.pt_of_mem {n : ℕ} (c : Clause3 n) {a : Fin n} (ha : a ∈ c.vars) :
    c.pt a = c.lit a := by simp [Clause3.pt, ha]

/-- Two half-cores glued along a shared variable `a`: the clauses on `s` forbidding `β`
at `a` and the clauses on `t` forbidding `¬β` there. -/
def crossOn {n : ℕ} (s t : Finset (Fin n)) (a : Fin n) (β : Bool) : Clause3 n → Bool :=
  fun d => decide ((d.vars = s ∧ d.lit a = β) ∨ (d.vars = t ∧ d.lit a = !β))

theorem crossOn_unsat {n : ℕ} {s t : Finset (Fin n)} (hs : s.card = 3) (ht : t.card = 3)
    {a : Fin n} (has : a ∈ s) (hat : a ∈ t) (β : Bool) : ¬ SatC (crossOn s t a β) := by
  rintro ⟨x, hx⟩
  by_cases hxa : x a = β
  · obtain ⟨c, hcs, hc⟩ := exists_clause_of_card s hs x
    have := hx c hc
    have hl : c.lit a = β := by rw [← Clause3.blocks_lit hc (hcs ▸ has)]; exact hxa
    simp [crossOn, hcs, hl] at this
  · obtain ⟨c, hct, hc⟩ := exists_clause_of_card t ht x
    have := hx c hc
    have hl : c.lit a = !β := by
      rw [← Clause3.blocks_lit hc (hct ▸ hat)]; cases β <;> simp_all
    simp [crossOn, hct, hl] at this

theorem crossOn_minimal {n : ℕ} {s t : Finset (Fin n)} {a : Fin n} (has : a ∈ s) (hat : a ∈ t)
    (β : Bool) (d : Clause3 n) (hd : crossOn s t a β d = true) :
    SatC (Function.update (crossOn s t a β) d false) := by
  refine ⟨d.pt, fun c hc => ?_⟩
  by_cases hcd : c = d
  · subst hcd; simp
  rw [Function.update_of_ne hcd]
  simp only [crossOn, decide_eq_true_eq] at hd
  simp only [crossOn, decide_eq_false_iff_not]
  rintro (⟨hcs, hcl⟩ | ⟨hct, hcl⟩)
  · have e1 := Clause3.blocks_lit hc (hcs ▸ has)
    rcases hd with ⟨hds, hdl⟩ | ⟨hdt, hdl⟩
    · exact hcd (Clause3.eq_of_blocks (hcs.trans hds.symm) hc d.blocks_pt)
    · rw [d.pt_of_mem (hdt ▸ hat), hdl, hcl] at e1; cases β <;> simp at e1
  · have e1 := Clause3.blocks_lit hc (hct ▸ hat)
    rcases hd with ⟨hds, hdl⟩ | ⟨hdt, hdl⟩
    · rw [d.pt_of_mem (hds ▸ has), hdl, hcl] at e1; cases β <;> simp at e1
    · exact hcd (Clause3.eq_of_blocks (hct.trans hdt.symm) hc d.blocks_pt)

theorem unsat_blocker {n : ℕ} {M : Clause3 n → Bool} (hM : ¬ SatC M) (x : Fin n → Bool) :
    ∃ c, c.blocks x = true ∧ M c = true := by
  by_contra hno
  push_neg at hno
  exact hM ⟨x, fun c hc => by simpa using hno c hc⟩

theorem exists_off {n : ℕ} (s : Finset (Fin n)) (hs : s.card < n) : ∃ w, w ∉ s := by
  by_contra hno
  push_neg at hno
  have := Finset.card_le_card (fun w (_ : w ∈ (univ : Finset (Fin n))) => hno w)
  simp at this; omega

/-- **No split as a conjunction.** For `n ≥ 3` the switchboard is not `U ∧ V` with `U` and
`V` reading complementary nonempty sets of switches: a minimal unsatisfiable set lies on one
side, and the cores and glued half-cores connect every two switches. -/
theorem and_split_false {n : ℕ} (hn : 3 ≤ n) (side : Clause3 n → Prop)
    (U V : (Clause3 n → Bool) → Bool)
    (hU : ∀ e e', (∀ c, side c → e c = e' c) → U e = U e')
    (hV : ∀ e e', (∀ c, ¬ side c → e c = e' c) → V e = V e')
    (h : ∀ e, sat3B n e = (U e && V e)) (h1 : ∃ c, side c) (h2 : ∃ c, ¬ side c) : False := by
  classical
  have one_side : ∀ M : Clause3 n → Bool, ¬ SatC M →
      (∀ c, M c = true → SatC (Function.update M c false)) →
      ∀ c d, M c = true → M d = true → (side c ↔ side d) := by
    intro M hM hmin
    have hf : (U M && V M) = false := by
      rw [← h]; exact (Bool.not_eq_true _).mp (fun ht => hM ((sat3B_iff M).mp ht))
    have k1 : U M = false → ∀ c, M c = true → side c := by
      intro hu c hc
      by_contra hs
      have := hmin c hc
      rw [← sat3B_iff, h, hU (Function.update M c false) M (fun d hd => by
        rw [Function.update_of_ne (fun e => hs (by rw [← e]; exact hd))]), hu] at this
      simp at this
    have k2 : V M = false → ∀ c, M c = true → ¬ side c := by
      intro hv c hc hs
      have := hmin c hc
      rw [← sat3B_iff, h, hV (Function.update M c false) M (fun d hd => by
        rw [Function.update_of_ne (fun e => hd (by rw [e]; exact hs))]), hv] at this
      simp at this
    intro c d hc hd
    cases hu : U M
    · exact ⟨fun _ => k1 hu d hd, fun _ => k1 hu c hc⟩
    · have hv : V M = false := by rw [hu] at hf; simpa using hf
      exact ⟨fun hs => absurd hs (k2 hv c hc), fun hs => absurd hs (k2 hv d hd)⟩
  have core_side : ∀ c d : Clause3 n, c.vars = d.vars → (side c ↔ side d) := by
    intro c d hcd
    refine one_side (coreOn c.vars) (coreOn_unsat _ (card_vars c)) (fun e he => ?_) c d
      (by simp [coreOn]) (by simp [coreOn, hcd])
    have : e.vars = c.vars := by simpa [coreOn] using he
    rw [← this]; exact coreOn_minimal e
  have share_side : ∀ c d : Clause3 n, ∀ a, a ∈ c.vars → a ∈ d.vars → (side c ↔ side d) := by
    intro c d a hac had
    obtain ⟨e, hev, heb⟩ := exists_clause_of_card c.vars (card_vars c)
      (Function.update c.pt a (!(d.lit a)))
    have hel : e.lit a = !(d.lit a) := by
      rw [← Clause3.blocks_lit heb (hev ▸ hac)]; simp
    refine (core_side c e hev.symm).trans (one_side (crossOn c.vars d.vars a (!(d.lit a)))
      (crossOn_unsat (card_vars c) (card_vars d) hac had _)
      (fun x hx => crossOn_minimal hac had _ x hx) e d (by simp [crossOn, hev, hel])
      (by simp [crossOn]))
  have all_side : ∀ c d : Clause3 n, side c ↔ side d := by
    intro c d
    by_cases hsh : ∃ a, a ∈ c.vars ∧ a ∈ d.vars
    · obtain ⟨a, ha, hb⟩ := hsh; exact share_side c d a ha hb
    · push_neg at hsh
      have hci : c.i ∈ c.vars := by simp [Clause3.vars]
      have hdi : d.i ∈ d.vars := by simp [Clause3.vars]
      have hne : c.i ≠ d.i := fun e => hsh _ hci (e ▸ hdi)
      obtain ⟨w, hw⟩ := exists_off ({c.i, d.i} : Finset (Fin n)) (by
        have := Finset.card_insert_le c.i ({d.i} : Finset (Fin n)); simp at this; omega)
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hw
      have hs : ({c.i, d.i, w} : Finset (Fin n)).card = 3 :=
        Finset.card_eq_three.mpr ⟨c.i, d.i, w, hne, Ne.symm hw.1, Ne.symm hw.2, rfl⟩
      obtain ⟨m, hm, -⟩ := exists_clause_of_card _ hs (fun _ => false)
      exact (share_side c m c.i hci (by simp [hm])).trans (share_side m d d.i (by simp [hm]) hdi)
  obtain ⟨c1, hc1⟩ := h1
  obtain ⟨c2, hc2⟩ := h2
  exact hc2 ((all_side c1 c2).mp hc1)

/-- **No split as a disjunction.** For `n ≥ 4` the switchboard is not `U ∨ V` with `U` and
`V` reading complementary nonempty sets of switches: the unsatisfiable configurations would
be closed under mixing the two sides, every core would meet both sides, and mixing a core
with a core on a neighbouring triple keeps every core on one side. -/
theorem or_split_false {n : ℕ} (hn : 4 ≤ n) (side : Clause3 n → Prop)
    (U V : (Clause3 n → Bool) → Bool)
    (hU : ∀ e e', (∀ c, side c → e c = e' c) → U e = U e')
    (hV : ∀ e e', (∀ c, ¬ side c → e c = e' c) → V e = V e')
    (h : ∀ e, sat3B n e = (U e || V e)) (h1 : ∃ c, side c) (h2 : ∃ c, ¬ side c) : False := by
  classical
  have unsat_iff : ∀ e, ¬ SatC e ↔ U e = false ∧ V e = false := by
    intro e; rw [← sat3B_iff, h]; cases U e <;> cases V e <;> simp
  let mix : (Clause3 n → Bool) → (Clause3 n → Bool) → Clause3 n → Bool :=
    fun E E' c => if side c then E c else E' c
  have mix_unsat : ∀ E E', ¬ SatC E → ¬ SatC E' → ¬ SatC (mix E E') := by
    intro E E' hE hE'
    rw [unsat_iff] at hE hE' ⊢
    exact ⟨by rw [hU (mix E E') E (fun c hc => by simp [mix, hc])]; exact hE.1,
      by rw [hV (mix E E') E' (fun c hc => by simp [mix, hc])]; exact hE'.2⟩
  have hV0 : V (fun _ => false) = true := by
    by_contra hv
    simp only [Bool.not_eq_true] at hv
    obtain ⟨j, hj⟩ := h2
    have hK := (unsat_iff _).mp (coreOn_unsat j.vars (card_vars j))
    have hK' : ¬ SatC (mix (coreOn j.vars) (fun _ => false)) := by
      rw [unsat_iff]
      exact ⟨by rw [hU _ (coreOn j.vars) (fun c hc => by simp [mix, hc])]; exact hK.1,
        by rw [hV _ (fun _ => false) (fun c hc => by simp [mix, hc])]; exact hv⟩
    refine hK' (satC_mono (fun c hc => ?_) (coreOn_minimal j))
    by_cases hcj : c = j
    · subst hcj; simp [mix, hj] at hc
    · rw [Function.update_of_ne hcj]
      by_cases hs : side c
      · simpa [mix, hs] using hc
      · simp [mix, hs] at hc
  have hU0 : U (fun _ => false) = true := by
    by_contra hu
    simp only [Bool.not_eq_true] at hu
    obtain ⟨j, hj⟩ := h1
    have hK := (unsat_iff _).mp (coreOn_unsat j.vars (card_vars j))
    have hK' : ¬ SatC (mix (fun _ => false) (coreOn j.vars)) := by
      rw [unsat_iff]
      exact ⟨by rw [hU _ (fun _ => false) (fun c hc => by simp [mix, hc])]; exact hu,
        by rw [hV _ (coreOn j.vars) (fun c hc => by simp [mix, hc])]; exact hK.2⟩
    refine hK' (satC_mono (fun c hc => ?_) (coreOn_minimal j))
    by_cases hcj : c = j
    · subst hcj; simp [mix, hj] at hc
    · rw [Function.update_of_ne hcj]
      by_cases hs : side c
      · simp [mix, hs] at hc
      · simpa [mix, hs] using hc
  have meets : ∀ c : Clause3 n, (∃ d, d.vars = c.vars ∧ side d) ∧ (∃ d, d.vars = c.vars ∧ ¬ side d) := by
    intro c
    have hK := (unsat_iff _).mp (coreOn_unsat c.vars (card_vars c))
    constructor
    · by_contra hno
      push_neg at hno
      have : U (coreOn c.vars) = U (fun _ => false) := hU _ _ (fun d hd => by
        simp only [coreOn, decide_eq_false_iff_not]; exact fun hdv => hno d hdv hd)
      rw [this, hU0] at hK; exact absurd hK.1 (by decide)
    · by_contra hno
      push_neg at hno
      have : V (coreOn c.vars) = V (fun _ => false) := hV _ _ (fun d hd => by
        simp only [coreOn, decide_eq_false_iff_not]; exact fun hdv => hd (hno d hdv))
      rw [this, hV0] at hK; exact absurd hK.2 (by decide)
  have flip_side : ∀ d1 d2 : Clause3 n, d1.vars = d2.vars → ∀ v ∈ d1.vars,
      (∀ a ∈ d1.vars, a ≠ v → d1.lit a = d2.lit a) → (side d1 ↔ side d2) := by
    intro d1 d2 hv12 v hv hlit
    obtain ⟨w, hw⟩ := exists_off d1.vars (by rw [card_vars]; omega)
    set T' := insert w (d1.vars.erase v)
    have hT' : T'.card = 3 := by
      rw [Finset.card_insert_of_notMem (by simp [hw]), Finset.card_erase_of_mem hv, card_vars]
    have hagree : ∀ a ∈ T', d1.pt a = d2.pt a := by
      intro a ha
      rcases Finset.mem_insert.mp ha with rfl | ha'
      · simp [Clause3.pt, hw, ← hv12]
      · obtain ⟨hav, ha1⟩ := Finset.mem_erase.mp ha'
        rw [d1.pt_of_mem ha1, d2.pt_of_mem (hv12 ▸ ha1), hlit a ha1 hav]
    have uniq1 : ∀ c : Clause3 n, c.vars = d1.vars → c.blocks d1.pt = true → c = d1 :=
      fun c hc hb => Clause3.eq_of_blocks hc hb d1.blocks_pt
    have uniq2 : ∀ c : Clause3 n, c.vars = d1.vars → c.blocks d2.pt = true → c = d2 :=
      fun c hc hb => Clause3.eq_of_blocks (hc.trans hv12) hb d2.blocks_pt
    have K1 := coreOn_unsat d1.vars (card_vars d1)
    have K2 := coreOn_unsat T' hT'
    have M1 := mix_unsat _ _ K1 K2
    have M2 := mix_unsat _ _ K2 K1
    constructor
    · intro hs1
      by_contra hs2
      obtain ⟨b, hb, hbM⟩ := unsat_blocker M2 d1.pt
      obtain ⟨b', hb', hb'M⟩ := unsat_blocker M1 d2.pt
      have hbT : side b ∧ b.vars = T' := by
        by_cases hsb : side b
        · simp only [mix, hsb, if_true, coreOn, decide_eq_true_eq] at hbM; exact ⟨hsb, hbM⟩
        · simp only [mix, hsb, if_false, coreOn, decide_eq_true_eq] at hbM
          exact absurd (by rw [uniq1 b hbM hb]; exact hs1) hsb
      have hb'T : ¬ side b' ∧ b'.vars = T' := by
        by_cases hsb : side b'
        · simp only [mix, hsb, if_true, coreOn, decide_eq_true_eq] at hb'M
          exact absurd (by rw [← uniq2 b' hb'M hb']; exact hsb) hs2
        · simp only [mix, hsb, if_false, coreOn, decide_eq_true_eq] at hb'M; exact ⟨hsb, hb'M⟩
      have hb'1 : b'.blocks d1.pt = true := by
        rw [b'.blocks_congr (fun a ha => hagree a (hb'T.2 ▸ ha))]; exact hb'
      have := Clause3.eq_of_blocks (hbT.2.trans hb'T.2.symm) hb hb'1
      exact hb'T.1 (this ▸ hbT.1)
    · intro hs2
      by_contra hs1
      obtain ⟨b, hb, hbM⟩ := unsat_blocker M1 d1.pt
      obtain ⟨b', hb', hb'M⟩ := unsat_blocker M2 d2.pt
      have hbT : ¬ side b ∧ b.vars = T' := by
        by_cases hsb : side b
        · simp only [mix, hsb, if_true, coreOn, decide_eq_true_eq] at hbM
          exact absurd (by rw [← uniq1 b hbM hb]; exact hsb) hs1
        · simp only [mix, hsb, if_false, coreOn, decide_eq_true_eq] at hbM; exact ⟨hsb, hbM⟩
      have hb'T : side b' ∧ b'.vars = T' := by
        by_cases hsb : side b'
        · simp only [mix, hsb, if_true, coreOn, decide_eq_true_eq] at hb'M; exact ⟨hsb, hb'M⟩
        · simp only [mix, hsb, if_false, coreOn, decide_eq_true_eq] at hb'M
          exact absurd (by rw [uniq2 b' hb'M hb']; exact hs2) hsb
      have hb'1 : b'.blocks d1.pt = true := by
        rw [b'.blocks_congr (fun a ha => hagree a (hb'T.2 ▸ ha))]; exact hb'
      have := Clause3.eq_of_blocks (hbT.2.trans hb'T.2.symm) hb hb'1
      exact hbT.1 (this ▸ hb'T.1)
  have same_vars : ∀ c d : Clause3 n, c.vars = d.vars → (side c ↔ side d) := by
    intro c d hcd
    obtain ⟨hi, hj, hk⟩ := Clause3.vars_eq hcd
    let x1 : Fin n → Bool := fun a => if a = c.i then d.bi else c.pt a
    let x2 : Fin n → Bool := fun a => if a = c.i then d.bi else if a = c.j then d.bj else c.pt a
    obtain ⟨e1, he1v, he1⟩ := exists_clause_of_card c.vars (card_vars c) x1
    obtain ⟨e2, he2v, he2⟩ := exists_clause_of_card c.vars (card_vars c) x2
    have L1 : ∀ a ∈ c.vars, e1.lit a = x1 a := fun a ha => (Clause3.blocks_lit he1 (he1v ▸ ha)).symm
    have L2 : ∀ a ∈ c.vars, e2.lit a = x2 a := fun a ha => (Clause3.blocks_lit he2 (he2v ▸ ha)).symm
    have hci : c.i ∈ c.vars := by simp [Clause3.vars]
    have hcj : c.j ∈ c.vars := by simp [Clause3.vars]
    have hck : c.k ∈ c.vars := by simp [Clause3.vars]
    have s1 := flip_side c e1 he1v.symm c.i hci (fun a ha hav => by
      rw [L1 a ha]; simp [x1, hav, c.pt_of_mem ha])
    have s2 := flip_side e1 e2 (he1v.trans he2v.symm) c.j (he1v ▸ hcj) (fun a ha hav => by
      rw [he1v] at ha
      rw [L1 a ha, L2 a ha]; by_cases hai : a = c.i <;> simp [x1, x2, hai, hav])
    have s3 := flip_side e2 d (he2v.trans hcd) c.k (he2v ▸ hck) (fun a ha hav => by
      rw [he2v] at ha
      rw [L2 a ha]
      rcases (c.mem_vars a).mp ha with rfl | rfl | rfl
      · have : x2 c.i = d.bi := by simp [x2]
        rw [this, hi, d.lit_i]
      · have : x2 c.j = d.bj := by simp [x2, c.ne_ij.symm]
        rw [this, hj, d.lit_j]
      · exact absurd rfl hav)
    exact s1.trans (s2.trans s3)
  obtain ⟨c0, -⟩ := h1
  obtain ⟨⟨d, hd, hsd⟩, ⟨d', hd', hsd'⟩⟩ := meets c0
  exact hsd' ((same_vars d d' (hd.trans hd'.symm)).mp hsd)

/-- **The switchboard does not split at the top** for `n ≥ 4`, in any of the four forms
`s ⊕ (U ∘ V)`. -/
theorem sat3B_no_split {n : ℕ} (hn : 4 ≤ n) (side : Clause3 n → Prop)
    (u v : (Clause3 n → Bool) → Bool) (o : Fin 3) (s : Bool) (ho : o ≠ 2)
    (hu : ∀ e e', (∀ c, side c → e c = e' c) → u e = u e')
    (hv : ∀ e e', (∀ c, ¬ side c → e c = e' c) → v e = v e')
    (h : ∀ e, sat3B n e = (s ^^ opB o (u e) (v e))) (h1 : ∃ c, side c) (h2 : ∃ c, ¬ side c) :
    False := by
  have hnu : ∀ e e', (∀ c, side c → e c = e' c) → (!u e) = !u e' := fun e e' h => by rw [hu e e' h]
  have hnv : ∀ e e', (∀ c, ¬ side c → e c = e' c) → (!v e) = !v e' := fun e e' h => by rw [hv e e' h]
  have ho' : o = 0 ∨ o = 1 := by fin_cases o <;> simp_all
  rcases ho' with rfl | rfl <;> cases s
  · exact and_split_false (by omega) side u v hu hv (fun e => by rw [h]; simp only [opB]; cases u e <;> cases v e <;> rfl) h1 h2
  · exact or_split_false hn side _ _ hnu hnv (fun e => by
      rw [h]; simp only [opB]; cases u e <;> cases v e <;> rfl) h1 h2
  · exact or_split_false hn side u v hu hv (fun e => by rw [h]; simp only [opB]; cases u e <;> cases v e <;> rfl) h1 h2
  · exact and_split_false (by omega) side _ _ hnu hnv (fun e => by
      rw [h]; simp only [opB]; cases u e <;> cases v e <;> rfl) h1 h2

/-! ### The switchboard needs `N` two-input gates and `N + 1` gates for `n ≥ 4` -/

theorem update_comp_equiv {α β : Type*} [DecidableEq α] [DecidableEq β] (E : α ≃ β)
    (x : β → Bool) (j : β) (b : Bool) :
    Function.update x j b ∘ E = Function.update (x ∘ E) (E.symm j) b := by
  funext c
  by_cases h : c = E.symm j
  · subst h; simp
  · have : E c ≠ j := fun e => h (by rw [← e]; simp)
    simp [Function.update_of_ne this, Function.update_of_ne h]

/-- Every switch of the switchboard is essential: the eight clauses on its triple form a core. -/
theorem sat3Fin_essential (n : ℕ) : Essential (sat3Fin n) := by
  classical
  intro j
  set E := Fintype.equivFin (Clause3 n)
  set c := E.symm j
  refine ⟨coreOn c.vars ∘ E.symm, fun hEq => ?_⟩
  have h0 : sat3Fin n (coreOn c.vars ∘ E.symm) = false := by
    unfold sat3Fin
    have : (coreOn c.vars ∘ E.symm) ∘ E = coreOn c.vars := by funext d; simp
    rw [this]
    exact (Bool.not_eq_true _).mp (fun ht => coreOn_unsat _ (card_vars c) ((sat3B_iff _).mp ht))
  have hj : (coreOn c.vars ∘ E.symm) j = true := by simp [coreOn, c]
  have h1 : sat3Fin n (Function.update (coreOn c.vars ∘ E.symm) j
      (!(coreOn c.vars ∘ E.symm) j)) = true := by
    unfold sat3Fin
    rw [hj, update_comp_equiv]
    have : (coreOn c.vars ∘ E.symm) ∘ E = coreOn c.vars := by funext d; simp
    rw [this]
    exact (sat3B_iff _).mpr (coreOn_minimal c)
  rw [h0, h1] at hEq
  exact absurd hEq (by decide)

theorem sat3B_false {n : ℕ} : sat3B n (fun _ => false) = true :=
  (sat3B_iff _).mpr ⟨fun _ => false, fun _ _ => rfl⟩

theorem sat3B_true {n : ℕ} (hn : 3 ≤ n) : sat3B n (fun _ => true) = false := by
  classical
  obtain ⟨c⟩ := Fintype.card_pos_iff.mp (clause3_nonempty hn)
  exact (Bool.not_eq_true _).mp fun ht =>
    coreOn_unsat c.vars (card_vars c) (satC_mono (fun _ _ => rfl) ((sat3B_iff _).mp ht))

theorem card_clause3_two {n : ℕ} (hn : 3 ≤ n) : 2 ≤ Fintype.card (Clause3 n) := by
  classical
  have : 1 < Fintype.card (Clause3 n) := Fintype.one_lt_card_iff.mpr
    ⟨Clause3.mk ⟨0, by omega⟩ ⟨1, by omega⟩ ⟨2, by omega⟩ (by simp [Fin.lt_def])
      (by simp [Fin.lt_def]) false false false,
     Clause3.mk ⟨0, by omega⟩ ⟨1, by omega⟩ ⟨2, by omega⟩ (by simp [Fin.lt_def])
      (by simp [Fin.lt_def]) false false true, by simp⟩
  omega

/-- **The switchboard needs `N` two-input gates for `n ≥ 4`.** A program with `N - 1` would
split the switchboard at the top into two functions of complementary sets of switches
(`top_split`), and the switchboard has no such split (`sat3B_no_split`). On three variables
the switchboard is the NAND of its eight switches and seven suffice. -/
theorem sat3Fin_bin_lower {n : ℕ} (hn : 4 ≤ n) (P : List (Fin 3 × ℕ × ℕ))
    (hP : Computes P (sat3Fin n)) : Fintype.card (Clause3 n) ≤ binCount P := by
  classical
  by_contra hlt
  push_neg at hlt
  set E := Fintype.equivFin (Clause3 n)
  obtain ⟨X, ⟨j1, hj1⟩, ⟨j2, hj2⟩, u, v, o, s, ho, hu, hv, hsplit⟩ :=
    top_split (card_clause3_two (by omega)) P (sat3Fin n) (sat3Fin_essential n) hP (by omega)
  refine sat3B_no_split hn (fun c => E c ∈ X) (fun e => u (e ∘ E.symm)) (fun e => v (e ∘ E.symm))
    o s ho (fun e e' h => hu _ _ fun j hj => h _ (by simpa using hj))
    (fun e e' h => hv _ _ fun j hj => h _ (by simpa using hj)) (fun e => ?_)
    ⟨E.symm j1, by simpa using hj1⟩ ⟨E.symm j2, by simpa using hj2⟩
  rw [← hsplit]
  unfold sat3Fin
  congr 1
  funext c
  exact (congrArg e (E.symm_apply_apply c)).symm

/-- **The switchboard needs `N + 1` gates for `n ≥ 4`**: `N` two-input gates and a NOT,
since satisfiability is not monotone. -/
theorem sat3Fin_size_lower {n : ℕ} (hn : 4 ≤ n) (P : List (Fin 3 × ℕ × ℕ))
    (hP : Computes P (sat3Fin n)) : Fintype.card (Clause3 n) + 1 ≤ P.length := by
  have hb := sat3Fin_bin_lower hn P hP
  have hnot : ∃ g ∈ P, g.1 = 2 := by
    by_contra hno
    push_neg at hno
    obtain ⟨o, -, ho⟩ := hP
    have := wires_monotone (N := Fintype.card (Clause3 n)) P hno o (x := fun _ => false)
      (y := fun _ => true) (fun _ => Bool.false_le _)
    rw [ho, ho] at this
    unfold sat3Fin at this
    simp only [Function.comp_def] at this
    rw [sat3B_false, sat3B_true (by omega)] at this
    exact absurd this (by decide)
  obtain ⟨g, hgP, hg2⟩ := hnot
  have hsplit := List.length_eq_length_filter_add (l := P) (f := fun g => decide (g.1 ≠ 2))
  have hpos : 0 < (P.filter fun g => !decide (g.1 ≠ 2)).length :=
    List.length_pos_iff_exists_mem.mpr ⟨g, List.mem_filter.mpr ⟨hgP, by simp [hg2]⟩⟩
  unfold binCount at hb
  omega

/-- The least circuit deciding the switchboard on `n ≥ 4` variables has at least `N + 1`
gates. -/
theorem minCircuitSize_sat3_ge {n : ℕ} (hn : 4 ≤ n) :
    Fintype.card (Clause3 n) + 1 ≤ minCircuitSize (sat3Fin n) Set.univ := by
  have hN : 1 ≤ Fintype.card (Clause3 n) := clause3_nonempty (by omega)
  obtain ⟨P0, -, hP0⟩ := lookup_exists hN (sat3Fin n) Finset.univ
  refine le_csInf ⟨_, P0, rfl, by simpa using hP0⟩ ?_
  rintro k ⟨P, rfl, i, hi, hf⟩
  exact sat3Fin_size_lower hn P ⟨i, hi, fun x => hf x (Set.mem_univ _)⟩

/-! ### Witness blocks, sensitivity, the Jacobian at the cores, and a cut of exponential rank -/

/-- The clauses falsified by `x`, as many as triples of variables. -/
theorem card_blockers {n : ℕ} (x : Fin n → Bool) :
    (univ.filter fun c : Clause3 n => c.blocks x = true).card = n.choose 3 := by
  classical
  have hb : (univ.filter fun c : Clause3 n => c.blocks x = true).card =
      ((univ : Finset (Fin n)).powersetCard 3).card := by
    refine Finset.card_bij (fun c _ => c.vars) (fun c _ => by simp [card_vars])
      (fun c hc d hd h => Clause3.eq_of_blocks h (by simpa using hc) (by simpa using hd)) ?_
    intro s hs
    obtain ⟨c, hcs, hc⟩ := exists_clause_of_card s (by simpa using hs) x
    exact ⟨c, by simpa using hc, hcs⟩
  rw [hb, Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]

theorem exists_triple_with {n : ℕ} (hn : 3 ≤ n) (a : Fin n) :
    ∃ s : Finset (Fin n), s.card = 3 ∧ a ∈ s := by
  classical
  obtain ⟨t, ht, htc⟩ := Finset.exists_subset_card_eq (s := univ.erase a) (n := 2)
    (by rw [Finset.card_erase_of_mem (mem_univ _)]; simp; omega)
  refine ⟨insert a t, ?_, Finset.mem_insert_self _ _⟩
  rw [Finset.card_insert_of_notMem (fun h => by simpa using ht h), htc]

/-- Two assignments are told apart by a clause falsified by one only. -/
theorem separating_clause {n : ℕ} (hn : 3 ≤ n) {x y : Fin n → Bool} (h : y ≠ x) :
    ∃ c : Clause3 n, c.blocks y = true ∧ c.blocks x = false := by
  obtain ⟨a, ha⟩ := Function.ne_iff.mp h
  obtain ⟨s, hs, has⟩ := exists_triple_with hn a
  obtain ⟨c, hcs, hc⟩ := exists_clause_of_card s hs y
  refine ⟨c, hc, ?_⟩
  by_contra hx
  have e1 := Clause3.blocks_lit hc (hcs ▸ has)
  have e2 := Clause3.blocks_lit (by simpa using hx) (hcs ▸ has)
  exact ha (e1.trans e2.symm)

/-- The unique-witness configuration of `x`: every clause that `x` satisfies. -/
def uwLayer {n : ℕ} (x : Fin n → Bool) : Clause3 n → Bool := fun c => !c.blocks x

/-- **Sensitivity of the unique-witness layer.** Flipping a switch of the unique-witness
configuration of `x` changes the answer exactly when the clause is falsified by `x`: the
layer is sensitive on `C(n,3)` switches (`card_blockers`). -/
theorem uwLayer_sensitive {n : ℕ} (hn : 3 ≤ n) (x : Fin n → Bool) (c : Clause3 n) :
    sat3B n (Function.update (uwLayer x) c (!uwLayer x c)) = false ↔ c.blocks x = true := by
  classical
  constructor
  · intro h
    by_contra hc
    simp only [Bool.not_eq_true] at hc
    have : SatC (Function.update (uwLayer x) c (!uwLayer x c)) := ⟨x, fun d hd => by
      by_cases hdc : d = c
      · subst hdc; rw [hd] at hc; exact absurd hc (by decide)
      · rw [Function.update_of_ne hdc]; simp [uwLayer, hd]⟩
    rw [(sat3B_iff _).mpr this] at h; exact absurd h (by decide)
  · intro hc
    refine (Bool.not_eq_true _).mp fun ht => ?_
    obtain ⟨y, hy⟩ := (sat3B_iff _).mp ht
    by_cases hyx : y = x
    · subst hyx
      have := hy c hc
      simp [uwLayer, hc] at this
    · obtain ⟨d, hdy, hdx⟩ := separating_clause hn hyx
      have hdc : d ≠ c := fun e => by rw [e, hc] at hdx; exact absurd hdx (by decide)
      have := hy d hdy
      rw [Function.update_of_ne hdc] at this
      simp [uwLayer, hdx] at this

theorem uwLayer_sat {n : ℕ} (x : Fin n → Bool) : SatC (uwLayer x) :=
  ⟨x, fun c hc => by simp [uwLayer, hc]⟩

/-- **Every positive CNF of unsatisfiability contains every witness block.** If a set `F` of
disjunctions of switches expresses unsatisfiability, then for every assignment `x` the set
of clauses falsified by `x` is one of the disjunctions. -/
theorem cnf_contains_blocks {n : ℕ} (hn : 3 ≤ n) (F : Finset (Finset (Clause3 n)))
    (hF : ∀ e : Clause3 n → Bool, (∀ D ∈ F, ∃ c ∈ D, e c = true) ↔ ¬ SatC e)
    (x : Fin n → Bool) : (univ.filter fun c : Clause3 n => c.blocks x = true) ∈ F := by
  classical
  have h1 : ¬ ∀ D ∈ F, ∃ c ∈ D, uwLayer x c = true := fun h => (hF _).mp h (uwLayer_sat x)
  push_neg at h1
  obtain ⟨D, hDF, hD⟩ := h1
  have hsub : ∀ c ∈ D, c.blocks x = true := fun c hc => by
    have := hD c hc; simpa [uwLayer] using this
  have heq : D = univ.filter fun c : Clause3 n => c.blocks x = true := by
    ext d
    refine ⟨fun hd => by simpa using hsub d hd, fun hd => ?_⟩
    by_contra hdD
    have hun : ¬ SatC (fun c => decide (c ∉ D)) := by
      rintro ⟨y, hy⟩
      by_cases hyx : y = x
      · subst hyx; have := hy d (by simpa using hd); simp [hdD] at this
      · obtain ⟨c, hcy, hcx⟩ := separating_clause hn hyx
        have hcD : c ∉ D := fun h => by rw [hsub c h] at hcx; exact absurd hcx (by decide)
        have := hy c hcy; simp [hcD] at this
    obtain ⟨c, hcD, hc⟩ := (hF _).mpr hun D hDF
    simp [hcD] at hc
  exact heq ▸ hDF

/-- A configuration is minimally unsatisfiable. -/
def MinUnsat {n : ℕ} (M : Clause3 n → Bool) : Prop :=
  ¬ SatC M ∧ ∀ c, M c = true → SatC (Function.update M c false)

/-- **The Jacobian at a core is its incidence vector.** At a minimally unsatisfiable
configuration, flipping a switch changes the answer exactly when the switch is on. -/
theorem jacobian_row {n : ℕ} {M : Clause3 n → Bool} (hM : MinUnsat M) (c : Clause3 n) :
    sat3B n (Function.update M c (!M c)) ≠ sat3B n M ↔ M c = true := by
  have h0 : sat3B n M = false := (Bool.not_eq_true _).mp fun ht => hM.1 ((sat3B_iff _).mp ht)
  rw [h0]
  cases hc : M c
  · have : sat3B n (Function.update M c (!false)) = false := by
      refine (Bool.not_eq_true _).mp fun ht => hM.1 (satC_mono (fun d hd => ?_) ((sat3B_iff _).mp ht))
      by_cases hdc : d = c
      · subst hdc; simp
      · rw [Function.update_of_ne hdc]; exact hd
    rw [this]; simp
  · have : sat3B n (Function.update M c (!true)) = true := (sat3B_iff _).mpr (hM.2 c hc)
    rw [this]; simp

/-- The Jacobian of the switchboard at its cores of eight clauses, over `𝔽₂`. -/
noncomputable def jacobian8 (n : ℕ) :
    Matrix {M : Finset (Clause3 n) // M.card = 8 ∧ MinUnsat fun c => decide (c ∈ M)}
      (Clause3 n) (ZMod 2) :=
  fun M c => if sat3B n (Function.update (fun d => decide (d ∈ M.1)) c
    (!decide (c ∈ M.1))) ≠ sat3B n (fun d => decide (d ∈ M.1)) then 1 else 0

theorem jacobian8_apply {n : ℕ} (M) (c : Clause3 n) :
    jacobian8 n M c = if c ∈ M.1 then 1 else 0 := by
  classical
  unfold jacobian8
  have := jacobian_row M.2.2 c
  by_cases hc : c ∈ M.1
  · rw [if_pos (this.mpr (by simpa using hc)), if_pos hc]
  · rw [if_neg (fun h => hc (by simpa using this.mp h)), if_neg hc]

/-- **The Jacobian rank is at most `N`, hence at most the circuit size.** -/
theorem jacobian8_rank_le {n : ℕ} (hn : 3 ≤ n) (P : List (Fin 3 × ℕ × ℕ))
    (hP : Computes P (sat3Fin n)) : (jacobian8 n).rank ≤ P.length := by
  refine (Matrix.rank_le_card_width _).trans ?_
  refine essential_nonmonotone_lower _ (sat3Fin_essential n) ⟨fun _ => false, fun _ => true,
    fun _ => Bool.false_le _, ?_, ?_⟩ P hP
  · unfold sat3Fin; simp only [Function.comp_def]; exact sat3B_false
  · unfold sat3Fin; simp only [Function.comp_def]; exact sat3B_true hn

/-- **The bound `rank J_n ≥ 7 C(n,3) + 1` fails at `n = 3`.** On three variables every
unsatisfiable configuration holds all eight clauses, so `J_3` has at most one row. -/
theorem jacobian8_three_rank : (jacobian8 3).rank ≤ 1 ∧ 1 < 7 * Nat.choose 3 3 + 1 := by
  classical
  refine ⟨(Matrix.rank_le_card_height _).trans ?_, by decide⟩
  have hall : ∀ M : Finset (Clause3 3), ¬ SatC (fun c => decide (c ∈ M)) → M = univ := by
    intro M hM
    ext c
    simp only [mem_univ, iff_true]
    by_contra hc
    apply hM
    refine ⟨c.pt, fun d hd => ?_⟩
    have hv : d.vars = c.vars := by
      rw [Finset.eq_univ_of_card d.vars (by rw [card_vars]; simp),
        Finset.eq_univ_of_card c.vars (by rw [card_vars]; simp)]
    have := Clause3.eq_of_blocks hv hd c.blocks_pt
    subst this; simpa using hc
  refine Fintype.card_le_one_iff.mpr fun a b => Subtype.ext ?_
  rw [hall _ a.2.2.1, hall _ b.2.2.1]

/-- The clause of the cut gadget: variable `t < K` with helpers `h, h + 1`, forbidding `¬β`
at `t`. -/
def gadgetClause {K : ℕ} (t : Fin K) (h : ℕ) (hh : K ≤ h) (hn : h + 1 < K + 4) (β u w : Bool) :
    Clause3 (K + 4) :=
  ⟨⟨t, by omega⟩, ⟨h, by omega⟩, ⟨h + 1, hn⟩, by simp [Fin.lt_def]; omega,
    by simp [Fin.lt_def], !β, u, w⟩

/-- Alice's switches fix the bits `a`, Bob's fix `b`, through disjoint helper pairs. -/
def cutConfig {K : ℕ} (a b : Fin K → Bool) : Clause3 (K + 4) → Bool := fun c =>
  decide ((∃ t u w, c = gadgetClause t K le_rfl (by omega) (a t) u w) ∨
    (∃ t u w, c = gadgetClause t (K + 2) (by omega) (by omega) (b t) u w))

/-- **A cut of exponential rank.** On `K + 4` variables, Alice's and Bob's halves of the
switchboard can be set so that the formula is satisfiable exactly when their `K`-bit
inputs agree: the satisfiability matrix across this cut is the identity of size `2^K`. -/
theorem cutConfig_sat {K : ℕ} (a b : Fin K → Bool) :
    sat3B (K + 4) (cutConfig a b) = decide (a = b) := by
  classical
  by_cases hab : a = b
  · subst hab
    rw [decide_eq_true rfl, sat3B_iff]
    refine ⟨fun v => if h : (v : ℕ) < K then a ⟨v, h⟩ else false, fun c hc => ?_⟩
    simp only [cutConfig, decide_eq_false_iff_not, not_or, not_exists]
    refine ⟨fun t u w e => ?_, fun t u w e => ?_⟩ <;>
    · subst e
      simp [gadgetClause, Clause3.blocks, t.2] at hc
  · rw [decide_eq_false hab]
    refine (Bool.not_eq_true _).mp fun ht => hab ?_
    obtain ⟨x, hx⟩ := (sat3B_iff _).mp ht
    have hA : ∀ t, a t = x ⟨t, by omega⟩ := fun t => by
      by_contra hne
      have hb : (gadgetClause t K le_rfl (by omega) (a t) (x ⟨K, by omega⟩)
          (x ⟨K + 1, by omega⟩)).blocks x = true := by
        simp only [gadgetClause, Clause3.blocks, beq_self_eq_true, Bool.and_true]
        revert hne; cases a t <;> cases x ⟨t, by omega⟩ <;> simp
      have := hx _ hb
      simp only [cutConfig, decide_eq_false_iff_not, not_or, not_exists] at this
      exact this.1 t _ _ rfl
    have hB : ∀ t, b t = x ⟨t, by omega⟩ := fun t => by
      by_contra hne
      have hb : (gadgetClause t (K + 2) (by omega) (by omega) (b t) (x ⟨K + 2, by omega⟩)
          (x ⟨K + 3, by omega⟩)).blocks x = true := by
        simp only [gadgetClause, Clause3.blocks, beq_self_eq_true, Bool.and_true]
        revert hne; cases b t <;> cases x ⟨t, by omega⟩ <;> simp
      have := hx _ hb
      simp only [cutConfig, decide_eq_false_iff_not, not_or, not_exists] at this
      exact this.2 t _ _ rfl
    funext t; rw [hA, hB]

/-- The satisfiability matrix of the cut, over `𝔽₂`, has rank `2^K`. -/
theorem cut_rank (K : ℕ) :
    (Matrix.of fun a b : Fin K → Bool => if sat3B (K + 4) (cutConfig a b) then (1 : ZMod 2) else 0).rank
      = 2 ^ K := by
  classical
  have : (Matrix.of fun a b : Fin K → Bool =>
      if sat3B (K + 4) (cutConfig a b) then (1 : ZMod 2) else 0) = 1 := by
    ext a b
    simp only [Matrix.of_apply, cutConfig_sat, Matrix.one_apply, decide_eq_true_eq]
  rw [this, Matrix.rank_one]
  simp

/-! ### The coset of the switchboard in `ℤ[e]` modulo the Boolean ideal -/

open MvPolynomial in
/-- `X_i^k - X_i` lies in the ideal of the idempotence relations, for `k ≥ 1`. -/
theorem X_pow_sub_X_mem {R σ : Type*} [CommRing R] (i : σ) :
    ∀ k, 1 ≤ k → (X i ^ k - X i : MvPolynomial σ R) ∈
      Ideal.span (Set.range fun j : σ => (X j ^ 2 - X j : MvPolynomial σ R)) := by
  intro k hk
  induction k with
  | zero => omega
  | succ k ih =>
    rcases Nat.eq_zero_or_pos k with rfl | hk'
    · simp
    · have : (X i ^ (k + 1) - X i : MvPolynomial σ R) =
          X i * (X i ^ k - X i) + (X i ^ 2 - X i) := by ring
      rw [this]
      exact add_mem (Ideal.mul_mem_left _ _ (ih hk')) (Ideal.subset_span ⟨i, rfl⟩)

open MvPolynomial in
theorem monomial_reduce {R σ : Type*} [CommRing R] (m : σ →₀ ℕ) :
    ∃ m' : σ →₀ ℕ, (∀ j, m' j ≤ 1) ∧ (∀ j, m j = 0 → m' j = 0) ∧
      (monomial m (1 : R) - monomial m' 1) ∈
        Ideal.span (Set.range fun j : σ => (X j ^ 2 - X j : MvPolynomial σ R)) := by
  classical
  induction m using Finsupp.induction with
  | zero => exact ⟨0, by simp, by simp, by simp⟩
  | single_add a b f ha hb ih =>
    obtain ⟨f', h1, h2, h3⟩ := ih
    have hfa : f a = 0 := Finsupp.notMem_support_iff.mp ha
    refine ⟨Finsupp.single a 1 + f', fun j => ?_, fun j hj => ?_, ?_⟩
    · by_cases hj : j = a
      · subst hj; simp [h2 _ hfa]
      · simp [Finsupp.single_apply, Ne.symm hj, h1 j]
    · by_cases hja : j = a
      · subst hja; simp [hb] at hj
      · simp [Finsupp.single_apply, Ne.symm hja] at hj ⊢; exact h2 j hj
    · rw [monomial_single_add, monomial_single_add]
      have : (X a ^ b * monomial f 1 - X a ^ 1 * monomial f' 1 : MvPolynomial σ R) =
          X a ^ b * (monomial f 1 - monomial f' 1) + (X a ^ b - X a) * monomial f' 1 := by ring
      rw [this]
      exact add_mem (Ideal.mul_mem_left _ _ h3)
        (Ideal.mul_mem_right _ _ (X_pow_sub_X_mem a b (Nat.one_le_iff_ne_zero.mpr hb)))

open MvPolynomial in
/-- **Multilinear reduction.** Modulo `X_i^2 - X_i`, every polynomial is multilinear. -/
theorem reduce_multilinear {R σ : Type*} [CommRing R] (p : MvPolynomial σ R) :
    ∃ r ∈ restrictDegree σ R 1, p - r ∈
      Ideal.span (Set.range fun j : σ => (X j ^ 2 - X j : MvPolynomial σ R)) := by
  classical
  choose m' hm1 _ hm3 using monomial_reduce (R := R) (σ := σ)
  refine ⟨∑ m ∈ p.support, monomial (m' m) (p.coeff m), ?_, ?_⟩
  · refine Submodule.sum_mem _ fun m _ => ?_
    rw [mem_restrictDegree]
    intro s hs i
    have := support_monomial_subset hs
    rw [Finset.mem_singleton] at this
    subst this; exact hm1 m i
  · have hs : p - ∑ m ∈ p.support, monomial (m' m) (p.coeff m) =
        ∑ m ∈ p.support, (monomial m (p.coeff m) - monomial (m' m) (p.coeff m)) := by
      rw [Finset.sum_sub_distrib, ← p.as_sum]
    rw [hs]
    refine Ideal.sum_mem _ fun m _ => ?_
    have : (monomial m (p.coeff m) - monomial (m' m) (p.coeff m) : MvPolynomial σ R) =
        C (p.coeff m) * (monomial m 1 - monomial (m' m) 1) := by
      rw [mul_sub, C_mul_monomial, C_mul_monomial, mul_one]
    rw [this]; exact Ideal.mul_mem_left _ _ (hm3 m)

open MvPolynomial

/-- The Boolean ideal `⟨2, e_i^2 - e_i⟩` of `ℤ[e]`. -/
noncomputable def IBool (N : ℕ) : Ideal (MvPolynomial (Fin N) ℤ) :=
  Ideal.span ({C 2} ∪ Set.range fun i => X i ^ 2 - X i)

/-- Evaluation at a Boolean point, read in `𝔽₂`. -/
noncomputable def evalBool {N : ℕ} (x : Fin N → Bool) : MvPolynomial (Fin N) ℤ →+* ZMod 2 :=
  eval₂Hom (Int.castRingHom (ZMod 2)) fun i => if x i then 1 else 0

theorem zmod2_idem (a : ZMod 2) : a ^ 2 - a = 0 := by fin_cases a <;> decide

/-- **The Boolean ideal is the ideal of polynomials even at every Boolean point.** -/
theorem mem_IBool_iff {N : ℕ} (P : MvPolynomial (Fin N) ℤ) :
    P ∈ IBool N ↔ ∀ x : Fin N → Bool, evalBool x P = 0 := by
  classical
  constructor
  · intro hP x
    have hle : IBool N ≤ RingHom.ker (evalBool x) := by
      refine Ideal.span_le.mpr fun p hp => ?_
      rcases hp with hp | ⟨i, rfl⟩
      · rw [Set.mem_singleton_iff] at hp; subst hp
        simp only [SetLike.mem_coe, RingHom.mem_ker, evalBool, coe_eval₂Hom, eval₂_C]; decide
      · simp only [SetLike.mem_coe, RingHom.mem_ker, evalBool, coe_eval₂Hom, map_sub, map_pow,
          eval₂_X]
        exact zmod2_idem _
    exact hle hP
  · intro h
    set φ : MvPolynomial (Fin N) ℤ →+* MvPolynomial (Fin N) (ZMod 2) := map (Int.castRingHom _)
    set J2 : Ideal (MvPolynomial (Fin N) (ZMod 2)) :=
      Ideal.span (Set.range fun j => (X j ^ 2 - X j : MvPolynomial (Fin N) (ZMod 2)))
    have hpt : ∀ v : Fin N → ZMod 2, MvPolynomial.eval v (φ P) = 0 := by
      intro v
      have hv : v = fun i => if (fun j => decide (v j = 1)) i then 1 else 0 := by
        funext i; rcases zmod2_cases (v i) with hvi | hvi <;> simp [hvi]
      rw [hv, eval_map]
      exact h _
    have hJ2 : ∀ q ∈ J2, ∀ v : Fin N → ZMod 2, MvPolynomial.eval v q = 0 := by
      intro q hq v
      have hle : J2 ≤ RingHom.ker (MvPolynomial.eval v) := Ideal.span_le.mpr fun p ⟨i, hi⟩ => by
        subst hi; simp only [SetLike.mem_coe, RingHom.mem_ker, map_sub, map_pow, eval_X]
        exact zmod2_idem _
      exact hle hq
    obtain ⟨r, hr, hdiff⟩ := reduce_multilinear (φ P)
    have hr0 : r = 0 := by
      refine MvPolynomial.eq_zero_of_eval_eq_zero (Fin N) (ZMod 2) r (fun v => ?_) (by rw [ZMod.card]; exact hr)
      have := hJ2 _ hdiff v
      rw [map_sub, hpt v, zero_sub, neg_eq_zero] at this; exact this
    rw [hr0, sub_zero] at hdiff
    have hmap : J2 = Ideal.map φ (Ideal.span (Set.range fun j : Fin N =>
        (X j ^ 2 - X j : MvPolynomial (Fin N) ℤ))) := by
      rw [Ideal.map_span, ← Set.range_comp]
      show Ideal.span _ = _
      congr 2; funext j; simp [φ]
    have hdiff' : φ P ∈ J2 := hdiff
    rw [hmap, Ideal.mem_map_iff_of_surjective φ (map_surjective _ (ZMod.intCast_surjective))] at hdiff'
    obtain ⟨P', hP', hPP'⟩ := hdiff'
    have h2' : C ((2 : ℕ) : ℤ) ∣ P - P' :=
      (C_dvd_iff_zmod 2 _).mpr (by rw [map_sub]; exact sub_eq_zero.mpr hPP'.symm)
    have h2 : C (2 : ℤ) ∣ P - P' := by simpa using h2'
    obtain ⟨k, hk⟩ := h2
    have : P = P' + C 2 * k := by rw [← hk]; ring
    rw [this]
    refine add_mem (Ideal.span_mono Set.subset_union_right hP') (Ideal.mul_mem_right _ _ ?_)
    exact Ideal.subset_span (Set.mem_union_left _ rfl)

/-- `P` represents the Boolean function `f` modulo the Boolean ideal. -/
def RepMod2 {N : ℕ} (P : MvPolynomial (Fin N) ℤ) (f : (Fin N → Bool) → Bool) : Prop :=
  ∀ x, evalBool x P = if f x then 1 else 0

/-- **The coset is the set of representatives.** If `G` represents `f`, then `P ∈ G + I`
exactly when `P` represents `f` too. -/
theorem coset_iff {N : ℕ} {f : (Fin N → Bool) → Bool} {G P : MvPolynomial (Fin N) ℤ}
    (hG : RepMod2 G f) : P - G ∈ IBool N ↔ RepMod2 P f := by
  rw [mem_IBool_iff]
  refine ⟨fun h x => ?_, fun h x => ?_⟩
  · have := h x; rw [map_sub, sub_eq_zero] at this; rw [this, hG]
  · rw [map_sub, h x, hG x, sub_self]

/-- One gate lifted to `ℤ[e]`: `NOT a ↦ 1 - a`, any other gate `↦ a · b`. -/
noncomputable def liftStep {N : ℕ} (L : List (MvPolynomial (Fin N) ℤ)) (g : Fin 3 × ℕ × ℕ) :
    List (MvPolynomial (Fin N) ℤ) :=
  L ++ [if g.1 = 2 then 1 - L.getD g.2.1 0 else L.getD g.2.1 0 * L.getD g.2.2 0]

/-- The straight-line program over `{·, 1 - ·}` of a circuit. -/
noncomputable def liftWires {N : ℕ} (P : List (Fin 3 × ℕ × ℕ)) : List (MvPolynomial (Fin N) ℤ) :=
  P.foldl liftStep (List.ofFn X)

theorem liftWires_snoc {N : ℕ} (P : List (Fin 3 × ℕ × ℕ)) (g : Fin 3 × ℕ × ℕ) :
    liftWires (N := N) (P ++ [g]) = liftStep (liftWires P) g := by
  simp [liftWires, List.foldl_append]

theorem liftWires_length {N : ℕ} (P : List (Fin 3 × ℕ × ℕ)) :
    (liftWires (N := N) P).length = N + P.length := by
  induction P using List.reverseRecOn with
  | nil => simp [liftWires]
  | append_singleton Q g ih => rw [liftWires_snoc]; simp [liftStep, ih]; omega

theorem liftStep_getD {N : ℕ} (L : List (MvPolynomial (Fin N) ℤ)) (g : Fin 3 × ℕ × ℕ) (i : ℕ) :
    (liftStep L g).getD i 0 = if i < L.length then L.getD i 0 else if i = L.length then
      (if g.1 = 2 then 1 - L.getD g.2.1 0 else L.getD g.2.1 0 * L.getD g.2.2 0) else 0 := by
  unfold liftStep
  by_cases h1 : i < L.length
  · rw [if_pos h1, List.getD_append _ _ _ _ h1]
  · rw [if_neg h1]
    by_cases h2 : i = L.length
    · subst h2; rw [if_pos rfl, List.getD_append_right _ _ _ _ le_rfl]; simp
    · rw [if_neg h2, List.getD_eq_default _ _ (by simp; omega)]

theorem ind_zmod2 (a b : Bool) :
    ((if a then 1 else 0 : ZMod 2) = if b then 1 else 0) ↔ a = b := by
  cases a <;> cases b <;> decide

/-- **The lift evaluates to the circuit.** On a circuit of AND and NOT gates, every lifted
wire takes at each Boolean point the value `0` or `1` of the corresponding wire. -/
theorem liftWires_eval {N : ℕ} (P : List (Fin 3 × ℕ × ℕ)) (hP : ∀ g ∈ P, g.1 = 0 ∨ g.1 = 2)
    (x : Fin N → Bool) (i : ℕ) :
    evalBool x ((liftWires P).getD i 0) = if (wires x P).getD i false then 1 else 0 := by
  induction P using List.reverseRecOn generalizing i with
  | nil =>
    simp only [liftWires, wires, List.foldl_nil]
    by_cases hi : i < N
    · have e1 : (List.ofFn (X : Fin N → MvPolynomial (Fin N) ℤ)).getD i 0 = X ⟨i, hi⟩ := by
        simp [List.getD_eq_getElem?_getD, hi]
      have e2 : (List.ofFn x).getD i false = x ⟨i, hi⟩ := by simp [List.getD_eq_getElem?_getD, hi]
      simp only [e1, e2]; simp [evalBool]
    · have e1 : (List.ofFn (X : Fin N → MvPolynomial (Fin N) ℤ)).getD i 0 = 0 :=
        List.getD_eq_default _ _ (by simpa using hi)
      have e2 : (List.ofFn x).getD i false = false := List.getD_eq_default _ _ (by simpa using hi)
      simp only [e1, e2]; simp
  | append_singleton Q g ih =>
    have hQ : ∀ g ∈ Q, g.1 = 0 ∨ g.1 = 2 := fun g hg => hP g (List.mem_append_left _ hg)
    have hg := hP g (by simp)
    simp only [liftWires_snoc, wires_snoc, liftStep_getD, step_getD, liftWires_length, wires_length]
    by_cases h1 : i < N + Q.length
    · simp only [if_pos h1]; exact ih hQ i
    · simp only [if_neg h1]
      by_cases h2 : i = N + Q.length
      · simp only [if_pos h2]
        rcases hg with h0 | h0
        · have hn2 : ¬ g.1 = 2 := by rw [h0]; decide
          simp only [h0, if_neg (show ¬ ((0 : Fin 3) = 2) by decide), map_mul, ih hQ, opB]
          cases (wires x Q).getD g.2.1 false <;> cases (wires x Q).getD g.2.2 false <;> decide
        · simp only [h0, if_pos (show ((2 : Fin 3) = 2) from rfl), if_true, map_sub, map_one, ih hQ, opB]
          cases (wires x Q).getD g.2.1 false <;> decide
      · simp [if_neg h2]

/-- **The coset question is the circuit question.** For a representative `G` of `f`, some
lifted wire of a circuit of AND and NOT gates lies in `G + I_Bool` exactly when the circuit
computes `f`. A lower bound on straight-line programs in the coset is therefore the same
statement as a lower bound on circuits of AND and NOT gates. -/
theorem coset_lift_iff {N : ℕ} {f : (Fin N → Bool) → Bool} {G : MvPolynomial (Fin N) ℤ}
    (hG : RepMod2 G f) (P : List (Fin 3 × ℕ × ℕ)) (hP : ∀ g ∈ P, g.1 = 0 ∨ g.1 = 2) :
    (∃ i < N + P.length, (liftWires P).getD i 0 - G ∈ IBool N) ↔ Computes P f := by
  refine ⟨fun ⟨i, hi, h⟩ => ⟨i, hi, fun x => ?_⟩, fun ⟨i, hi, h⟩ => ⟨i, hi, ?_⟩⟩
  · have := (coset_iff hG).mp h x
    rw [liftWires_eval P hP] at this
    exact (ind_zmod2 _ _).mp this
  · rw [coset_iff hG]; intro x; rw [liftWires_eval P hP, h x]

/-- The canonical integer lift `P_SAT = 1 - ∏_x (1 - ∏_{c falsified by x} (1 - e_c))`. -/
noncomputable def PSAT (n : ℕ) : MvPolynomial (Fin (Fintype.card (Clause3 n))) ℤ :=
  1 - ∏ x : Fin n → Bool, (1 - ∏ c ∈ univ.filter (fun c : Clause3 n => c.blocks x = true),
    (1 - X (Fintype.equivFin (Clause3 n) c)))

theorem one_sub_ind (b : Bool) : (1 : ZMod 2) - (if b then 1 else 0) = if !b then 1 else 0 := by
  cases b <;> decide

/-- `P_SAT` represents the switchboard modulo the Boolean ideal. -/
theorem PSAT_rep (n : ℕ) : RepMod2 (PSAT n) (sat3Fin n) := by
  classical
  intro y
  set E := Fintype.equivFin (Clause3 n)
  have one_sub_ite : ∀ (Q : Prop) (d : Decidable Q),
      (1 : ZMod 2) - @ite _ Q d 1 0 = @ite _ (¬ Q) (@instDecidableNot Q d) 1 0 := by
    intro Q d; by_cases hQ : Q <;> simp [hQ]
  have hX : ∀ c : Clause3 n, evalBool y (1 - X (E c)) = if (!y (E c)) = true then 1 else 0 :=
    fun c => by
      rw [map_sub, map_one]; simp only [evalBool, coe_eval₂Hom, eval₂_X]; exact one_sub_ind _
  have hb : ∀ x : Fin n → Bool, evalBool y (1 - ∏ c ∈ univ.filter
      (fun c : Clause3 n => c.blocks x = true), (1 - X (E c))) =
      if ¬ ∀ c ∈ univ.filter (fun c : Clause3 n => c.blocks x = true), (!y (E c)) = true
      then 1 else 0 := by
    intro x
    rw [map_sub, map_one, map_prod]
    rw [Finset.prod_congr rfl (fun c _ => hX c), Finset.prod_boole]
    by_cases hQ : ∀ c ∈ univ.filter (fun c : Clause3 n => c.blocks x = true), (!y (E c)) = true
    · rw [if_pos hQ, if_neg (not_not.mpr hQ), sub_self]
    · rw [if_neg hQ, if_pos hQ, sub_zero]
  unfold PSAT
  rw [map_sub, map_one, map_prod, Finset.prod_congr rfl (fun x _ => hb x), Finset.prod_boole]
  have key : (∀ x ∈ (univ : Finset (Fin n → Bool)), ¬ ∀ c ∈ univ.filter
      (fun c : Clause3 n => c.blocks x = true), (!y (E c)) = true) ↔ ¬ sat3Fin n y = true := by
    simp only [sat3Fin, sat3B, decide_eq_true_eq, Function.comp_apply, Finset.mem_filter,
      Finset.mem_univ, true_and, true_implies, Bool.not_eq_true', not_exists]
    constructor
    · intro h x hx; exact h x fun c hc => by simpa using hx c hc
    · intro h x hx; exact h x fun c hc => by simpa using hx c hc
  by_cases hs : sat3Fin n y = true
  · have : ¬ ∀ x ∈ (univ : Finset (Fin n → Bool)), ¬ ∀ c ∈ univ.filter
        (fun c : Clause3 n => c.blocks x = true), (!y (E c)) = true := fun h => key.mp h hs
    rw [if_neg this, sub_zero, if_pos hs]
  · have := key.mpr hs
    rw [if_pos this, sub_self, if_neg hs]

theorem totalDegree_one_sub {σ : Type*} (q : MvPolynomial σ ℤ) (hq : 1 ≤ q.totalDegree) :
    (1 - q).totalDegree = q.totalDegree := by
  apply le_antisymm
  · exact (totalDegree_sub _ _).trans (by rw [totalDegree_one]; simp)
  · have h := totalDegree_sub (1 : MvPolynomial σ ℤ) (1 - q)
    rw [sub_sub_cancel, totalDegree_one] at h
    have := le_max_iff.mp h
    rcases this with h' | h' <;> omega

theorem totalDegree_prod_isDomain {σ ι : Type*} (s : Finset ι) (f : ι → MvPolynomial σ ℤ)
    (hf : ∀ i ∈ s, f i ≠ 0) : (∏ i ∈ s, f i).totalDegree = ∑ i ∈ s, (f i).totalDegree := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha,
      totalDegree_mul_of_isDomain (hf a (Finset.mem_insert_self _ _))
        (Finset.prod_ne_zero_iff.mpr fun i hi => hf i (Finset.mem_insert_of_mem hi)),
      ih fun i hi => hf i (Finset.mem_insert_of_mem hi)]

theorem ne_zero_of_totalDegree {σ : Type*} {q : MvPolynomial σ ℤ} (h : 1 ≤ q.totalDegree) : q ≠ 0 :=
  fun e => by rw [e, totalDegree_zero] at h; omega

/-- **The degree of the integer lift.** `P_SAT` has total degree `2^n C(n,3)`: every clause
occurs in `2^(n-3)` of the `2^n` factors, so for `n ≥ 4` the lift is not multilinear. -/
theorem PSAT_totalDegree {n : ℕ} (hn : 3 ≤ n) :
    (PSAT n).totalDegree = 2 ^ n * n.choose 3 := by
  classical
  set E := Fintype.equivFin (Clause3 n)
  have h1 : ∀ c : Clause3 n, (1 - X (E c) : MvPolynomial _ ℤ).totalDegree = 1 := fun c => by
    rw [totalDegree_one_sub _ (by rw [totalDegree_X])]; exact totalDegree_X _
  have hC : 1 ≤ n.choose 3 := Nat.choose_pos hn
  have h2 : ∀ x : Fin n → Bool, (1 - ∏ c ∈ univ.filter (fun c : Clause3 n => c.blocks x = true),
      (1 - X (E c)) : MvPolynomial _ ℤ).totalDegree = n.choose 3 := fun x => by
    have hp : (∏ c ∈ univ.filter (fun c : Clause3 n => c.blocks x = true),
        (1 - X (E c)) : MvPolynomial _ ℤ).totalDegree = n.choose 3 := by
      rw [totalDegree_prod_isDomain _ _ fun c _ => ne_zero_of_totalDegree (by rw [h1])]
      simp only [h1, Finset.sum_const, smul_eq_mul, mul_one]; exact card_blockers x
    rw [totalDegree_one_sub _ (by rw [hp]; exact hC), hp]
  have h3 : (∏ x : Fin n → Bool, (1 - ∏ c ∈ univ.filter (fun c : Clause3 n => c.blocks x = true),
      (1 - X (E c))) : MvPolynomial _ ℤ).totalDegree = 2 ^ n * n.choose 3 := by
    rw [totalDegree_prod_isDomain _ _ fun x _ => ne_zero_of_totalDegree (by rw [h2]; exact hC)]
    simp [h2]
  unfold PSAT
  rw [totalDegree_one_sub _ (by rw [h3]; exact Nat.mul_pos (by positivity) hC), h3]

/-- The lifted wires of a program of `S` gates have total degree at most `2^S`. -/
theorem liftWires_totalDegree {N : ℕ} (P : List (Fin 3 × ℕ × ℕ)) (i : ℕ) :
    ((liftWires (N := N) P).getD i 0).totalDegree ≤ 2 ^ P.length := by
  induction P using List.reverseRecOn generalizing i with
  | nil =>
    simp only [liftWires, List.foldl_nil, List.length_nil, pow_zero]
    by_cases hi : i < N
    · rw [List.getD_eq_getElem _ _ (by simpa using hi)]; simp [totalDegree_X]
    · rw [List.getD_eq_default _ _ (by simpa using hi)]; simp
  | append_singleton Q g ih =>
    rw [liftWires_snoc, liftStep_getD]
    simp only [List.length_append, List.length_singleton, pow_succ]
    split_ifs
    · exact (ih i).trans (by omega)
    · exact (totalDegree_sub _ _).trans (by rw [totalDegree_one]; have := ih g.2.1; omega)
    · exact (totalDegree_mul _ _).trans (by have := ih g.2.1; have := ih g.2.2; omega)
    · simp

/-- **A straight-line program for the unreduced lift needs `n + log₂ C(n,3)` gates.** If a
lifted wire equals `P_SAT` exactly, then `2^n C(n,3) ≤ 2^S`. The bound is logarithmic; it
says nothing about the other members of the coset, which include the lift of every
circuit for the switchboard (`coset_lift_iff`). -/
theorem PSAT_slp_lower {n : ℕ} (hn : 3 ≤ n) (P : List (Fin 3 × ℕ × ℕ)) (i : ℕ)
    (h : (liftWires P).getD i 0 = PSAT n) : 2 ^ n * n.choose 3 ≤ 2 ^ P.length := by
  rw [← PSAT_totalDegree hn, ← h]; exact liftWires_totalDegree P i

/-- The value of the lift at the point `(1/2, …, 1/2)`. -/
theorem PSAT_half {n : ℕ} :
    aeval (fun _ => (1 / 2 : ℚ)) (PSAT n) = 1 - (1 - (1 / 2) ^ n.choose 3) ^ (2 ^ n) := by
  classical
  unfold PSAT
  simp only [map_sub, map_one, map_prod, aeval_X]
  simp only [Finset.prod_const, card_blockers, Finset.card_univ, Fintype.card_fun, Fintype.card_bool,
    Fintype.card_fin]
  norm_num

end ReadOnceBarrier

end QE.Comp
