-- SPDX-License-Identifier: MIT
-- Copyright 2026 Metere Industries, Inc. Author: Alfredo Metere.
-- Quasi-Euclidean Granular Geometry. Any derivative work must carry this notice:
--   This work is derivative of the Quasi-Euclidean Granular Geometry book
--   authored by Alfredo Metere. Copyright 2026 Metere Industries, Inc.
--   All rights reserved
-- See LICENSE.md and NOTICE.

import QuasiEuclidean.Basic

/-!
# Chapter 15: Nonlinear dynamics on the granular lattice

Every statement here is an exact finitary statement.  A hyperfinite lattice
is, internally, a finite set, so the results below (proved for an arbitrary
`Fintype`) apply to the hyperfinite phase spaces of the book by transfer of
their finitary content; no limit is taken anywhere.

* pigeonhole: eventual periodicity of every self-map of a finite set;
* exact Poincaré recurrence for bijections, with the bound `≤ card`;
* Liouville ↔ bijectivity (cardinality-preserving preimages);
* Kac's lemma in counting form: `∑_{x ∈ A} τ_A(x) = card X`;
* the dyadic doubling map: bit shift, collapse to `0` in exactly `K` steps,
  loss of exactly one bit per step; odd moduli give a permutation instead;
* a finite shadowing lemma for the doubling map;
* the predictability horizon `t ≤ log₂ M`;
* Arnold's cat map on `(ZMod N)²`: inverse, determinant, Fibonacci formula,
  periodicity, and the exact period `10` modulo `5`;
* the kick–drift (standard-map/leapfrog) Hamiltonian lattice map: exact
  inverse, time-reversal involution, exact Loschmidt echo, periodicity;
* tent–logistic conjugacy at `r = 4`;
* box counting for the Cantor set (`2^n`) and Koch curve (`4^n`).
-/

namespace QE.Dyn

open Finset Function

/-! ## Pigeonhole and recurrence -/

section Recurrence

variable {X : Type*} [Fintype X]

/-- **Eventual periodicity.**  Every orbit of a self-map of a finite set
becomes periodic, with preperiod `m` and period `n`, `m + n ≤ card X`. -/
theorem eventually_periodic (f : X → X) (x : X) :
    ∃ m n : ℕ, 0 < n ∧ m + n ≤ Fintype.card X ∧ f^[m + n] x = f^[m] x := by
  have hc : Fintype.card X < Fintype.card (Fin (Fintype.card X + 1)) := by simp
  obtain ⟨i, j, hij, h⟩ :=
    Fintype.exists_ne_map_eq_of_card_lt (fun i : Fin (Fintype.card X + 1) => f^[i] x) hc
  rcases lt_or_gt_of_ne (Fin.val_injective.ne hij) with hlt | hlt
  · refine ⟨i, j - i, by omega, by have := j.isLt; omega, ?_⟩
    rw [Nat.add_sub_cancel' hlt.le]; exact h.symm
  · refine ⟨j, i - j, by omega, by have := i.isLt; omega, ?_⟩
    rw [Nat.add_sub_cancel' hlt.le]; exact h

omit [Fintype X] in
/-- Once periodic, always periodic. -/
theorem eventually_periodic_forever (f : X → X) {x : X} {m n : ℕ}
    (h : f^[m + n] x = f^[m] x) (t : ℕ) : f^[m + t + n] x = f^[m + t] x := by
  have e1 : m + t + n = t + (m + n) := by omega
  have e2 : m + t = t + m := by omega
  rw [e1, e2, iterate_add_apply, h, ← iterate_add_apply]

/-- Every self-map of a nonempty finite set has a periodic point (the granular
attractor is never empty). -/
theorem exists_periodic_point [Nonempty X] (f : X → X) :
    ∃ y : X, ∃ n : ℕ, 0 < n ∧ f^[n] y = y := by
  obtain ⟨x⟩ := ‹Nonempty X›
  obtain ⟨m, n, hn, -, h⟩ := eventually_periodic f x
  refine ⟨f^[m] x, n, hn, ?_⟩
  rw [← iterate_add_apply, add_comm, h]

/-- **Exact Poincaré recurrence.**  Under an injective self-map of a finite
set (a bijection) every point returns exactly to itself after at most
`card X` steps. -/
theorem injective_recurrence {f : X → X} (hf : Injective f) (x : X) :
    ∃ n : ℕ, 0 < n ∧ n ≤ Fintype.card X ∧ f^[n] x = x := by
  obtain ⟨m, n, hn, hle, h⟩ := eventually_periodic f x
  refine ⟨n, hn, by omega, ?_⟩
  rw [iterate_add_apply] at h
  exact hf.iterate m h

/-- **Permutations are purely periodic**: some positive power is the identity
(namely the order, the l.c.m. of the cycle lengths). -/
theorem perm_periodic [DecidableEq X] (σ : Equiv.Perm X) :
    ∃ n : ℕ, 0 < n ∧ ∀ x, (σ ^ n) x = x :=
  ⟨orderOf σ, orderOf_pos σ, fun x => by rw [pow_orderOf_eq_one]; rfl⟩

/-- **Liouville ↔ bijectivity.**  A self-map of a finite set preserves the
cardinality (hence the granular measure) of every preimage iff it is a
bijection. -/
theorem volume_preserving_iff_bijective [DecidableEq X] (f : X → X) :
    (∀ A : Finset X, (univ.filter fun x => f x ∈ A).card = A.card) ↔ Bijective f := by
  constructor
  · intro h
    have hs : Surjective f := by
      intro y
      have := h {y}
      have hpos : 0 < (univ.filter fun x => f x ∈ ({y} : Finset X)).card := by
        rw [this]; simp
      obtain ⟨x, hx⟩ := Finset.card_pos.mp hpos
      simp at hx
      exact ⟨x, hx⟩
    exact ⟨Finite.injective_iff_surjective.mpr hs, hs⟩
  · intro hb A
    apply Finset.card_bij (fun x _ => f x)
    · intro x hx; simpa using hx
    · intro a _ b _ h; exact hb.1 h
    · intro y hy
      obtain ⟨x, rfl⟩ := hb.2 y
      exact ⟨x, by simpa using hy, rfl⟩

/-- Corollary in the book's units: the granular measure `2ε · card` of every
preimage equals that of the set iff the map is a bijection. -/
theorem mu_preserving_iff_bijective {K : Type*} [Field K] [LinearOrder K]
    [IsStrictOrderedRing K] (ε : K) (hε : 0 < ε) (f : ℤ → ℤ) (S : Finset ℤ)
    (hS : ∀ x ∈ S, f x ∈ S) :
    (∀ A ⊆ S, QE.mu ε (S.filter fun x => f x ∈ A) = QE.mu ε A) ↔ Set.BijOn f S S := by
  have h2 : (2 * ε) ≠ 0 := by positivity
  have hmu : ∀ A B : Finset ℤ, QE.mu ε A = QE.mu ε B ↔ A.card = B.card := by
    intro A B; unfold QE.mu
    constructor
    · intro h; exact_mod_cast mul_left_cancel₀ h2 h
    · intro h; rw [h]
  simp only [hmu]
  constructor
  · intro h
    have hsurj : Set.SurjOn f S S := by
      intro y hy
      have := h {y} (by simpa using hy)
      have hpos : 0 < (S.filter fun x => f x ∈ ({y} : Finset ℤ)).card := by
        rw [this]; simp
      obtain ⟨x, hx⟩ := Finset.card_pos.mp hpos
      simp at hx
      exact ⟨x, hx.1, hx.2⟩
    have hmaps : Set.MapsTo f S S := fun x hx => hS x hx
    exact ⟨hmaps, Finset.injOn_of_surjOn_of_card_le f hmaps hsurj le_rfl, hsurj⟩
  · intro hb A hA
    apply Finset.card_bij (fun x _ => f x)
    · intro x hx; simp at hx; exact hx.2
    · intro a ha b hb' h; simp at ha hb'; exact hb.2.1 ha.1 hb'.1 h
    · intro y hy
      obtain ⟨x, hx, rfl⟩ := hb.2.2 (hA hy)
      exact ⟨x, by simp only [Finset.mem_filter]; exact ⟨hx, hy⟩, rfl⟩

end Recurrence

/-! ## Kac's lemma, counting form -/

section Kac

variable {X : Type*} [Fintype X] [DecidableEq X]

open Classical in
/-- First return time of `x` to the set `A` under the permutation `σ`
(`0` if `x` never enters `A`; for `x ∈ A` it is always positive). -/
noncomputable def returnTime (σ : Equiv.Perm X) (A : Finset X) (x : X) : ℕ :=
  if h : ∃ n, 0 < n ∧ (σ ^ n) x ∈ A then Nat.find h else 0

omit [DecidableEq X] in
theorem exists_return (σ : Equiv.Perm X) {A : Finset X} {x : X} (hx : x ∈ A) :
    ∃ n, 0 < n ∧ (σ ^ n) x ∈ A :=
  ⟨orderOf σ, orderOf_pos σ, by rw [pow_orderOf_eq_one]; exact hx⟩

theorem returnTime_spec (σ : Equiv.Perm X) {A : Finset X} {x : X} (hx : x ∈ A) :
    0 < returnTime σ A x ∧ (σ ^ returnTime σ A x) x ∈ A ∧
      ∀ m, 0 < m → m < returnTime σ A x → (σ ^ m) x ∉ A := by
  classical
  have h := exists_return σ hx
  have e : returnTime σ A x = Nat.find h := by
    unfold returnTime; simp only [h, dite_true]
  rw [e]
  refine ⟨(Nat.find_spec h).1, (Nat.find_spec h).2, fun m hm hlt hmA => ?_⟩
  exact Nat.find_min h hlt ⟨hm, hmA⟩

/-- **Kac's lemma (counting form).**  Let `σ` be a permutation of a finite set
`X` and `A ⊆ X` a set that meets every orbit, in the sense that every point is
of the form `σ^k a` with `a ∈ A`.  Then the first-return times to `A` add up
to the number of points: `∑_{a ∈ A} τ_A(a) = card X`.  Dividing by `card A`,
the mean return time under the uniform measure is `1/P(A)`. -/
theorem kac_counting (σ : Equiv.Perm X) (A : Finset X)
    (hA : ∀ z : X, ∃ k : ℕ, ∃ a ∈ A, (σ ^ k) a = z) :
    ∑ a ∈ A, returnTime σ A a = Fintype.card X := by
  classical
  have hsig : (A.sigma fun a => Finset.range (returnTime σ A a)).card
      = ∑ a ∈ A, returnTime σ A a := by
    rw [Finset.card_sigma]; simp
  rw [← hsig, ← Finset.card_univ]
  apply Finset.card_bij (fun p _ => (σ ^ p.2) p.1)
  · intro p _; exact Finset.mem_univ _
  · -- injectivity of the tower map
    have key : ∀ x ∈ A, ∀ y ∈ A, ∀ i j : ℕ, i ≤ j → j < returnTime σ A y →
        (σ ^ i) x = (σ ^ j) y → x = y ∧ i = j := by
      intro x hx y hy i j hij hj h
      have hxy : x = (σ ^ (j - i)) y := by
        have : (σ ^ j) y = (σ ^ i) ((σ ^ (j - i)) y) := by
          rw [← Equiv.Perm.mul_apply, ← pow_add, Nat.add_sub_cancel' hij]
        rw [this] at h
        exact (σ ^ i).injective h
      by_cases hji : j - i = 0
      · have : i = j := by omega
        subst this; simp at hxy; exact ⟨hxy, rfl⟩
      · exfalso
        exact (returnTime_spec σ hy).2.2 (j - i) (by omega) (by omega) (hxy ▸ hx)
    rintro ⟨x, i⟩ hp ⟨y, j⟩ hq h
    simp only [Finset.mem_sigma, Finset.mem_range] at hp hq h
    rcases le_total i j with hij | hji
    · obtain ⟨rfl, rfl⟩ := key x hp.1 y hq.1 i j hij hq.2 h
      rfl
    · obtain ⟨rfl, rfl⟩ := key y hq.1 x hp.1 j i hji hp.2 h.symm
      rfl
  · -- surjectivity: every point lies in the tower over A
    intro z _
    have hP : ∃ k, ∃ a ∈ A, (σ ^ k) a = z := hA z
    let k := Nat.find hP
    obtain ⟨a, ha, hk⟩ := Nat.find_spec hP
    refine ⟨⟨a, k⟩, ?_, hk⟩
    simp only [Finset.mem_sigma, Finset.mem_range]
    refine ⟨ha, ?_⟩
    by_contra hlt'
    have hlt := Nat.le_of_not_lt hlt'
    obtain ⟨hpos, hmem, -⟩ := returnTime_spec σ ha
    have : ∃ b ∈ A, (σ ^ (k - returnTime σ A a)) b = z := by
      refine ⟨(σ ^ returnTime σ A a) a, hmem, ?_⟩
      rw [← Equiv.Perm.mul_apply, ← pow_add, Nat.sub_add_cancel hlt]
      exact hk
    exact Nat.find_min hP (show k - returnTime σ A a < k by omega) this

/-- Kac's lemma as a statement about the mean return time under the uniform
(granular) probability: `(1/card A) ∑_{a∈A} τ_A(a) = 1 / P(A)` with
`P(A) = card A / card X`. -/
theorem kac_mean (σ : Equiv.Perm X) (A : Finset X) (hne : A.Nonempty)
    (hA : ∀ z : X, ∃ k : ℕ, ∃ a ∈ A, (σ ^ k) a = z) :
    ((∑ a ∈ A, returnTime σ A a : ℕ) : ℚ) / A.card
      = 1 / ((A.card : ℚ) / Fintype.card X) := by
  rw [kac_counting σ A hA]
  have hA0 : (A.card : ℚ) ≠ 0 := by exact_mod_cast hne.card_pos.ne'
  have hX : (Fintype.card X : ℚ) ≠ 0 := by
    have : 0 < Fintype.card X := Fintype.card_pos_iff.mpr ⟨hne.choose⟩
    exact_mod_cast this.ne'
  field_simp

end Kac

/-! ## The doubling map on the dyadic lattice

With dyadic spacing `2ε = 2^{-K}`, the lattice points of `[0,1)` are
`k · 2^{-K}`, `0 ≤ k < 2^K`, and `x ↦ 2x mod 1` acts on indices as
`k ↦ 2k mod 2^K`.  No rounding is involved: this *is* the classical doubling
map restricted to the invariant set of dyadic rationals of level `K`. -/

section Doubling

/-- The doubling map on the indices of the dyadic lattice of level `K`. -/
def dbl (K : ℕ) (k : ℕ) : ℕ := (2 * k) % 2 ^ K

/-- Iterating the doubling map multiplies by `2^j` modulo `2^K`. -/
theorem dbl_iterate (K j k : ℕ) (hk : k < 2 ^ K) : (dbl K)^[j] k = (2 ^ j * k) % 2 ^ K := by
  induction j with
  | zero => simp [Nat.mod_eq_of_lt hk]
  | succ j ih =>
    rw [iterate_succ_apply', ih, dbl, Nat.mul_mod, Nat.mod_mod, ← Nat.mul_mod, pow_succ]
    ring_nf

/-- **Bit shift.**  One step of the doubling map deletes the top bit and
shifts the remaining `K - 1` bits up: `dbl k = 2 · (k mod 2^{K-1})`. -/
theorem dbl_bit_shift (K k : ℕ) (hK : 1 ≤ K) : dbl K k = 2 * (k % 2 ^ (K - 1)) := by
  unfold dbl
  have : 2 ^ K = 2 * 2 ^ (K - 1) := by
    rw [← pow_succ']; congr 1; omega
  rw [this, Nat.mul_mod_mul_left]

/-- After `j ≤ K` steps exactly the top `j` bits have been shifted out:
`dbl^j k = 2^j · (k mod 2^{K-j})`. -/
theorem dbl_iterate_shift (K j k : ℕ) (hj : j ≤ K) (hk : k < 2 ^ K) :
    (dbl K)^[j] k = 2 ^ j * (k % 2 ^ (K - j)) := by
  rw [dbl_iterate K j k hk]
  have : 2 ^ K = 2 ^ j * 2 ^ (K - j) := by rw [← pow_add]; congr 1; omega
  rw [this, Nat.mul_mod_mul_left]

/-- **Collapse.**  Every orbit of the dyadic doubling map reaches the fixed
point `0` after exactly `K` steps (at the latest). -/
theorem dbl_collapse (K k : ℕ) (hk : k < 2 ^ K) : (dbl K)^[K] k = 0 := by
  rw [dbl_iterate_shift K K k le_rfl hk]; simp [Nat.mod_one]

theorem dbl_zero (K : ℕ) : dbl K 0 = 0 := by simp [dbl]

/-- The time to reach `0`: for `j ≤ K`, `dbl^j k = 0` iff `2^{K-j}` divides
`k`, i.e. iff the lowest `K - j` bits of `k` are zero. -/
theorem dbl_iterate_eq_zero_iff (K j k : ℕ) (hj : j ≤ K) (hk : k < 2 ^ K) :
    (dbl K)^[j] k = 0 ↔ 2 ^ (K - j) ∣ k := by
  rw [dbl_iterate_shift K j k hj hk, Nat.dvd_iff_mod_eq_zero]
  constructor
  · intro h; rcases Nat.mul_eq_zero.mp h with h | h
    · exact absurd h (by positivity)
    · exact h
  · intro h; rw [h, mul_zero]

/-- **The collapse takes exactly `K` steps for odd indices**: an odd lattice
index (lowest bit `1`) is not yet at `0` after `K - 1` steps. -/
theorem dbl_odd_not_zero (K k j : ℕ) (hj : j < K) (hk : k < 2 ^ K) (hodd : k % 2 = 1) :
    (dbl K)^[j] k ≠ 0 := by
  rw [Ne, dbl_iterate_eq_zero_iff K j k hj.le hk]
  intro h
  have h2 : 2 ∣ 2 ^ (K - j) := dvd_pow_self 2 (by omega)
  have := Nat.dvd_trans h2 h
  omega

/-- **The last bit.**  The state immediately before the collapse is always the
single-bit state `2^{K-1}` (the lattice point `1/2`): the fixed point `0` is
reached by deleting one last, irreducible bit. -/
theorem dbl_last_bit (K k : ℕ) (hK : 1 ≤ K) (hk : k < 2 ^ K) (hne : k ≠ 0)
    (h0 : dbl K k = 0) : k = 2 ^ (K - 1) := by
  rw [dbl_bit_shift K k hK] at h0
  have hm : k % 2 ^ (K - 1) = 0 := by omega
  obtain ⟨c, hc⟩ := Nat.dvd_of_mod_eq_zero hm
  have hP : 2 ^ K = 2 * 2 ^ (K - 1) := by rw [← pow_succ']; congr 1; omega
  have hpos : 0 < 2 ^ (K - 1) := by positivity
  rcases c with _ | _ | c
  · simp at hc; exact absurd hc hne
  · simpa using hc
  · exfalso
    have : 2 ^ (K - 1) * (c + 1 + 1) ≥ 2 * 2 ^ (K - 1) := by nlinarith
    omega

/-- **Exactly one bit is lost per step.**  The image of the level-`K` dyadic
lattice under `j ≤ K` doublings has exactly `2^{K-j}` points, so
`log₂ #(image)` drops by exactly one at every step: the Kolmogorov–Sinai
entropy `ln 2` per step, i.e. one bit, realised as an exact count. -/
theorem dbl_image_card (K j : ℕ) (hj : j ≤ K) :
    ((Finset.range (2 ^ K)).image ((dbl K)^[j])).card = 2 ^ (K - j) := by
  have himg : (Finset.range (2 ^ K)).image ((dbl K)^[j])
      = (Finset.range (2 ^ (K - j))).image (fun r => 2 ^ j * r) := by
    ext y
    simp only [Finset.mem_image, Finset.mem_range]
    constructor
    · rintro ⟨k, hk, rfl⟩
      exact ⟨k % 2 ^ (K - j), Nat.mod_lt _ (by positivity),
        (dbl_iterate_shift K j k hj hk).symm⟩
    · rintro ⟨r, hr, rfl⟩
      have hrK : r < 2 ^ K :=
        lt_of_lt_of_le hr (Nat.pow_le_pow_right (by norm_num) (by omega))
      exact ⟨r, hrK, by rw [dbl_iterate_shift K j r hj hrK, Nat.mod_eq_of_lt hr]⟩
  rw [himg, Finset.card_image_of_injective _ (fun a b h => by
    simpa using (Nat.eq_of_mul_eq_mul_left (by positivity) h)), Finset.card_range]

/-- Every lattice point has exactly two preimages or none: on `ZMod (2^K)`,
`2a = 2b ↔ a = b` or `a = b + 2^{K-1}`; we record the two-to-one property as
`dbl k = dbl (k + 2^{K-1})`. -/
theorem dbl_two_to_one (K k : ℕ) (hK : 1 ≤ K) :
    dbl K (k + 2 ^ (K - 1)) = dbl K k := by
  unfold dbl
  have : 2 * (k + 2 ^ (K - 1)) = 2 * k + 2 ^ K := by
    rw [mul_add, ← pow_succ']; congr 2; omega
  rw [this, Nat.add_mod_right]

/-- Separation of granule-adjacent initial conditions: after `t` steps the
two orbits are `2^t` granules apart (on `ZMod (2^K)`, exactly). -/
theorem dbl_separation (K t : ℕ) (x y : ZMod (2 ^ K)) :
    (2 : ZMod (2 ^ K)) ^ t * x - 2 ^ t * y = 2 ^ t * (x - y) := by ring

/-- **Predictability horizon.**  An initial uncertainty of one granule grows
to `2^t` granules; it stays within a budget of `M ≥ 1` granules (`M = L/2ε`)
iff `t ≤ ⌊log₂ M⌋`. -/
theorem predictability_horizon (M t : ℕ) (hM : M ≠ 0) :
    2 ^ t ≤ M ↔ t ≤ Nat.log 2 M :=
  (Nat.le_log_iff_pow_le (by norm_num) hM).symm

/-- On a lattice with an **odd** number `N` of cells the doubling map is a
permutation (no collapse); it is therefore purely periodic. -/
theorem dbl_odd_injective (N : ℕ) (hN : N % 2 = 1) :
    Injective (fun x : ZMod N => 2 * x) := by
  have hc : Nat.Coprime 2 N := by
    rw [Nat.coprime_two_left]; exact Nat.odd_iff.mpr hN
  have hu : IsUnit (2 : ZMod N) := by
    have := (ZMod.unitOfCoprime 2 hc).isUnit
    simpa using this
  intro a b h
  exact hu.mul_left_cancel h

theorem dbl_odd_periodic (N : ℕ) [NeZero N] (hN : N % 2 = 1) :
    ∃ n : ℕ, 0 < n ∧ ∀ x : ZMod N, (fun x : ZMod N => 2 * x)^[n] x = x := by
  have hinj := dbl_odd_injective N hN
  let σ : Equiv.Perm (ZMod N) := Equiv.ofBijective _ (Finite.injective_iff_surjective.mp hinj |>
    fun hs => ⟨hinj, hs⟩)
  obtain ⟨n, hn, h⟩ := perm_periodic σ
  refine ⟨n, hn, fun x => ?_⟩
  have := h x
  rwa [Equiv.Perm.coe_pow] at this

/-! ### Finite shadowing for the doubling map

A `δ`-pseudo-orbit `x₀, …, xₙ` of the lifted doubling map `x ↦ 2x`
(`|x_{k+1} - 2 x_k| ≤ δ`) is `δ`-shadowed by the true orbit of
`y = xₙ / 2ⁿ`. -/

theorem shadow_aux {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    (x : ℕ → K) (δ : K) (hpo : ∀ k, |x (k + 1) - 2 * x k| ≤ δ) :
    ∀ m k : ℕ, |x (k + m) / 2 ^ m - x k| ≤ δ * (1 - 1 / 2 ^ m) := by
  intro m
  induction m with
  | zero => intro k; simp
  | succ m ih =>
    intro k
    have h1 := ih (k + 1)
    have h2 := hpo k
    have e : x (k + (m + 1)) / 2 ^ (m + 1) - x k
        = (x (k + 1 + m) / 2 ^ m - x (k + 1)) / 2 + (x (k + 1) - 2 * x k) / 2 := by
      rw [show k + 1 + m = k + (m + 1) by omega, pow_succ]; field_simp; ring
    rw [e]
    calc |(x (k + 1 + m) / 2 ^ m - x (k + 1)) / 2 + (x (k + 1) - 2 * x k) / 2|
        ≤ |(x (k + 1 + m) / 2 ^ m - x (k + 1)) / 2| + |(x (k + 1) - 2 * x k) / 2| :=
          abs_add_le _ _
      _ = |x (k + 1 + m) / 2 ^ m - x (k + 1)| / 2 + |x (k + 1) - 2 * x k| / 2 := by
          rw [abs_div, abs_div, abs_two]
      _ ≤ δ * (1 - 1 / 2 ^ m) / 2 + δ / 2 := by gcongr
      _ = δ * (1 - 1 / 2 ^ (m + 1)) := by rw [pow_succ]; field_simp; ring

/-- **Shadowing lemma for the doubling map (finite form).** -/
theorem doubling_shadowing {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    (x : ℕ → K) (δ : K) (n : ℕ) (hpo : ∀ k, |x (k + 1) - 2 * x k| ≤ δ) :
    ∃ y : K, ∀ k ≤ n, |2 ^ k * y - x k| ≤ δ := by
  refine ⟨x n / 2 ^ n, fun k hk => ?_⟩
  have hδ : 0 ≤ δ := le_trans (abs_nonneg _) (hpo 0)
  have h := shadow_aux x δ hpo (n - k) k
  have e : 2 ^ k * (x n / 2 ^ n) = x (k + (n - k)) / 2 ^ (n - k) := by
    rw [show k + (n - k) = n by omega]
    have : (2 : K) ^ n = 2 ^ k * 2 ^ (n - k) := by rw [← pow_add]; congr 1; omega
    rw [this]; field_simp
  rw [e]
  refine le_trans h ?_
  have : 0 ≤ 1 / (2 : K) ^ (n - k) := by positivity
  nlinarith

/-- The terminal state `{0}` of the collapse is a point, not nothing: its
granular measure is one cell, `2ε`, while the empty configuration has
measure `0`; the two are distinct states (one bit apart). -/
theorem zero_state_is_a_point {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    (ε : K) (hε : 0 < ε) :
    QE.mu ε ({0} : Finset ℤ) = 2 * ε ∧ QE.mu ε (∅ : Finset ℤ) = 0 ∧
      QE.mu ε ({0} : Finset ℤ) ≠ QE.mu ε ∅ := by
  unfold QE.mu
  refine ⟨by simp, by simp, ?_⟩
  simp; exact hε.ne'

/-- **Symbolic dynamics on the lattice.**  Observing which half of `[0,1)` the
state lies in at time `i < K` (the coarse partition `{[0,½), [½,1)}`) reads
off the `i`-th most significant bit of the initial index. -/
theorem dbl_symbol (K i k : ℕ) (hi : i < K) (hk : k < 2 ^ K) :
    (dbl K)^[i] k / 2 ^ (K - 1) = (k / 2 ^ (K - 1 - i)) % 2 := by
  rw [dbl_iterate_shift K i k hi.le hk]
  have e1 : 2 ^ (K - 1) = 2 ^ i * 2 ^ (K - 1 - i) := by rw [← pow_add]; congr 1; omega
  have e2 : 2 ^ (K - i) = 2 ^ (K - 1 - i) * 2 := by rw [← pow_succ]; congr 1; omega
  rw [e1, Nat.mul_div_mul_left _ _ (by positivity), e2, Nat.mod_mul_right_div_self]

/-- The symbols up to time `t ≤ K` depend only on the top `t` bits
`⌊k / 2^{K-t}⌋`, which take exactly `2^t` values on the lattice. -/
theorem dbl_top_bits_card (K t : ℕ) (ht : t ≤ K) :
    ((Finset.range (2 ^ K)).image (fun k => k / 2 ^ (K - t))).card = 2 ^ t := by
  have hP : 2 ^ K = 2 ^ t * 2 ^ (K - t) := by rw [← pow_add]; congr 1; omega
  have : (Finset.range (2 ^ K)).image (fun k => k / 2 ^ (K - t)) = Finset.range (2 ^ t) := by
    ext y
    simp only [Finset.mem_image, Finset.mem_range]
    constructor
    · rintro ⟨k, hk, rfl⟩
      rw [Nat.div_lt_iff_lt_mul (by positivity), ← hP]; exact hk
    · intro hy
      refine ⟨y * 2 ^ (K - t), ?_, Nat.mul_div_cancel _ (by positivity)⟩
      rw [hP]; exact Nat.mul_lt_mul_of_pos_right hy (by positivity)
  rw [this, Finset.card_range]

theorem dbl_symbol_of_top_bits (K t i k : ℕ) (hit : i < t) (ht : t ≤ K) :
    (k / 2 ^ (K - 1 - i)) % 2 = ((k / 2 ^ (K - t)) / 2 ^ (t - 1 - i)) % 2 := by
  rw [Nat.div_div_eq_div_mul, ← pow_add]
  congr 3; omega

end Doubling

/-! ## Arnold's cat map on the granular torus `(ZMod N)²` -/

section Cat

variable (N : ℕ)

/-- The cat map `(x, y) ↦ (2x + y, x + y)`. -/
def cat (p : ZMod N × ZMod N) : ZMod N × ZMod N := (2 * p.1 + p.2, p.1 + p.2)

/-- Its inverse `(x, y) ↦ (x - y, -x + 2y)`. -/
def catInv (p : ZMod N × ZMod N) : ZMod N × ZMod N := (p.1 - p.2, -p.1 + 2 * p.2)

theorem cat_left_inv : LeftInverse (catInv N) (cat N) := by
  intro p; ext <;> simp [cat, catInv] <;> ring

theorem cat_right_inv : RightInverse (catInv N) (cat N) := by
  intro p; ext <;> simp [cat, catInv] <;> ring

/-- The cat map as a permutation of the `N²` granular cells. -/
def catEquiv : Equiv.Perm (ZMod N × ZMod N) :=
  ⟨cat N, catInv N, cat_left_inv N, cat_right_inv N⟩

/-- The matrix of the cat map has determinant `1` (area preservation). -/
theorem cat_det : Matrix.det !![(2 : ℤ), 1; 1, 1] = 1 := by
  simp [Matrix.det_fin_two]

/-- **Fibonacci formula**: `A^n = [[F_{2n+1}, F_{2n}], [F_{2n}, F_{2n-1}]]`. -/
theorem cat_iterate (n : ℕ) (p : ZMod N × ZMod N) :
    (cat N)^[n] p = ((Nat.fib (2 * n + 1) : ZMod N) * p.1 + (Nat.fib (2 * n) : ZMod N) * p.2,
      (Nat.fib (2 * n) : ZMod N) * p.1
        + ((Nat.fib (2 * n + 1) : ZMod N) - (Nat.fib (2 * n) : ZMod N)) * p.2) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [iterate_succ_apply', ih]
    have f2 : (Nat.fib (2 * n + 2) : ZMod N) = Nat.fib (2 * n) + Nat.fib (2 * n + 1) := by
      rw [Nat.fib_add_two]; push_cast; ring
    have f3 : (Nat.fib (2 * n + 2 + 1) : ZMod N) = Nat.fib (2 * n + 1) + Nat.fib (2 * n + 2) := by
      rw [show 2 * n + 2 + 1 = (2 * n + 1) + 2 by ring, Nat.fib_add_two]; push_cast; ring
    rw [show 2 * (n + 1) = 2 * n + 2 by ring, f3, f2]
    ext <;> simp [cat] <;> ring

/-- **Periodicity criterion**: `A^n = 1` on `(ZMod N)²` iff `F_{2n} ≡ 0` and
`F_{2n+1} ≡ 1 (mod N)`. -/
theorem cat_iterate_eq_id_iff (n : ℕ) :
    (∀ p, (cat N)^[n] p = p) ↔
      (Nat.fib (2 * n) : ZMod N) = 0 ∧ (Nat.fib (2 * n + 1) : ZMod N) = 1 := by
  constructor
  · intro h
    have h1 := h (1, 0)
    rw [cat_iterate] at h1
    simp only [mul_one, mul_zero, add_zero, Prod.mk.injEq] at h1
    exact ⟨h1.2, h1.1⟩
  · rintro ⟨h0, h1⟩ p
    rw [cat_iterate, h0, h1]; ext <;> simp

/-- **The cat map is purely periodic** on every granular torus. -/
theorem cat_periodic [NeZero N] : ∃ n : ℕ, 0 < n ∧ ∀ p, (cat N)^[n] p = p := by
  obtain ⟨n, hn, h⟩ := perm_periodic (catEquiv N)
  exact ⟨n, hn, fun p => by have := h p; rwa [Equiv.Perm.coe_pow] at this⟩

/-- Worked example: on the `5 × 5` torus the cat map has period exactly `10`. -/
theorem cat_period_five :
    (∀ p, (cat 5)^[10] p = p) ∧ ∀ n, 0 < n → n < 10 → ¬ ∀ p, (cat 5)^[n] p = p := by
  refine ⟨(cat_iterate_eq_id_iff 5 10).mpr ⟨by decide, by decide⟩, ?_⟩
  intro n hn hlt h
  rw [cat_iterate_eq_id_iff] at h
  interval_cases n <;> revert h <;> decide

/-- Lifting lemma behind the dyadic period: modulo `2^{j+3}`,
`F_{12·2^j} ≡ 0` and `F_{12·2^j + 1} ≡ 1`. -/
theorem cat_dyadic_aux (j : ℕ) :
    (2 : ℤ) ^ (j + 3) ∣ (Nat.fib (2 * (6 * 2 ^ j)) : ℤ) ∧
      (2 : ℤ) ^ (j + 3) ∣ (Nat.fib (2 * (6 * 2 ^ j) + 1) : ℤ) - 1 := by
  induction j with
  | zero => exact ⟨⟨18, by decide⟩, ⟨29, by decide⟩⟩
  | succ j ih =>
    obtain ⟨⟨u, hu⟩, ⟨v, hv⟩⟩ := ih
    set m := 6 * 2 ^ j with hm
    have em : 2 * (6 * 2 ^ (j + 1)) = 2 * (2 * m) := by rw [hm, pow_succ]; ring
    have hle : Nat.fib (2 * m) ≤ 2 * Nat.fib (2 * m + 1) := by
      have := Nat.fib_le_fib_succ (n := 2 * m); omega
    have f1 : (Nat.fib (2 * (2 * m)) : ℤ)
        = Nat.fib (2 * m) * (2 * Nat.fib (2 * m + 1) - Nat.fib (2 * m)) := by
      rw [Nat.fib_two_mul, Nat.cast_mul, Nat.cast_sub hle]; push_cast; ring
    have f2 : (Nat.fib (2 * (2 * m) + 1) : ℤ)
        = Nat.fib (2 * m + 1) ^ 2 + Nat.fib (2 * m) ^ 2 := by
      rw [Nat.fib_two_mul_add_one]; push_cast; ring
    have hv' : (Nat.fib (2 * m + 1) : ℤ) = 1 + 2 ^ (j + 3) * v := by linarith
    rw [em, f1, f2, hu, hv']
    constructor
    · exact ⟨u * (1 + 2 ^ (j + 3) * v - 2 ^ (j + 2) * u), by ring⟩
    · exact ⟨v + 2 ^ (j + 2) * (v ^ 2 + u ^ 2), by ring⟩

/-- **Exact recurrence time on the dyadic torus.**  On the granular torus
`(ℤ/2^k)²`, `k ≥ 3` (spacing `2ε = 2^{-k}`), the cat map satisfies
`A^{3·2^{k-2}} = 1`: every one of the `4^k` states recurs after
`3N/4` steps, `N = 2^k = 1/(2ε)`. -/
theorem cat_dyadic_period (k : ℕ) (hk : 3 ≤ k) :
    ∀ p, (cat (2 ^ k))^[3 * 2 ^ (k - 2)] p = p := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 3 := ⟨k - 3, by omega⟩
  have e : 3 * 2 ^ (j + 3 - 2) = 6 * 2 ^ j := by
    rw [show j + 3 - 2 = j + 1 by omega, pow_succ]; ring
  rw [e, cat_iterate_eq_id_iff]
  obtain ⟨h0, h1⟩ := cat_dyadic_aux j
  constructor
  · have := (ZMod.intCast_zmod_eq_zero_iff_dvd (Nat.fib (2 * (6 * 2 ^ j)) : ℤ) (2 ^ (j + 3))).mpr
      (by push_cast; exact h0)
    simpa using this
  · have := (ZMod.intCast_eq_intCast_iff_dvd_sub 1 (Nat.fib (2 * (6 * 2 ^ j) + 1) : ℤ)
      (2 ^ (j + 3))).mpr (by push_cast; exact h1)
    simpa using this.symm

/-- Linearity: the difference of two orbits evolves by the same matrix,
`c(p) - c(q) = c(p - q)`, so granular separations grow exactly like `A^t`. -/
theorem cat_sub (p q : ZMod N × ZMod N) : cat N p - cat N q = cat N (p - q) := by
  ext <;> simp [cat] <;> ring

theorem cat_iterate_sub (t : ℕ) (p q : ZMod N × ZMod N) :
    (cat N)^[t] p - (cat N)^[t] q = (cat N)^[t] (p - q) := by
  induction t generalizing p q with
  | zero => simp
  | succ t ih =>
    rw [iterate_succ_apply, iterate_succ_apply, iterate_succ_apply, ← cat_sub]
    exact ih _ _

end Cat

/-! ## Hamiltonian lattice maps: kick–drift (standard map / leapfrog)

On a ring `R` (`ℤ`, or `ZMod N` for the torus), with an arbitrary force
`F : R → R`, the kick `(q, p) ↦ (q, p + F q)` and the drift
`(q, p) ↦ (q + p, p)` are shears; their composite is the one-step leapfrog
(symplectic Euler / Chirikov standard map).  All arithmetic is integer
arithmetic: no round-off. -/

section Hamiltonian

variable {R : Type*} [CommRing R] (F : R → R)

/-- One step: kick then drift. -/
def leap (x : R × R) : R × R := (x.1 + (x.2 + F x.1), x.2 + F x.1)

/-- Exact inverse step. -/
def leapInv (x : R × R) : R × R := (x.1 - x.2, x.2 - F (x.1 - x.2))

/-- Time reversal: `(q, p) ↦ (q, -p - F q)` (momentum reversal composed with
a half-kick); an involution. -/
def rev (x : R × R) : R × R := (x.1, -x.2 - F x.1)

theorem leap_left_inv : LeftInverse (leapInv F) (leap F) := by
  intro x; ext <;> simp [leap, leapInv]

theorem leap_right_inv : RightInverse (leapInv F) (leap F) := by
  intro x; ext <;> simp [leap, leapInv]

theorem rev_involutive : Involutive (rev F) := by
  intro x; ext <;> simp [rev]

/-- **Exact reversibility**: `rev ∘ leap ∘ rev = leap⁻¹`. -/
theorem rev_leap_rev (x : R × R) : rev F (leap F (rev F x)) = leapInv F x := by
  ext <;> simp [rev, leap, leapInv] <;> ring_nf

theorem rev_semiconj : Semiconj (rev F) (leap F) (leapInv F) := by
  intro x
  have := rev_leap_rev F (rev F x)
  rwa [rev_involutive F x] at this

/-- **Exact Loschmidt echo**: run `n` steps forward, reverse the momenta, run
`n` steps forward again, reverse again: the initial state is recovered
exactly, for every `n` and every force `F`. -/
theorem loschmidt_echo (n : ℕ) (x : R × R) :
    rev F ((leap F)^[n] (rev F ((leap F)^[n] x))) = x := by
  rw [(rev_semiconj F).iterate_right n, rev_involutive F]
  exact (leap_left_inv F).iterate n x

/-- Linear force `F q = κ q`: the Jacobian `[[1+κ, 1], [κ, 1]]` has
determinant `1` (symplecticity). -/
theorem leap_linear_det (κ : R) : Matrix.det !![1 + κ, 1; κ, 1] = 1 := by
  simp [Matrix.det_fin_two]

/-- The leapfrog map as a permutation. -/
def leapEquiv : Equiv.Perm (R × R) := ⟨leap F, leapInv F, leap_left_inv F, leap_right_inv F⟩

/-- **Exact recurrence** of every Hamiltonian lattice map on the granular torus
`(ZMod N)²`: some positive power is the identity. -/
theorem leap_periodic (N : ℕ) [NeZero N] (G : ZMod N → ZMod N) :
    ∃ n : ℕ, 0 < n ∧ ∀ x, (leap G)^[n] x = x := by
  obtain ⟨n, hn, h⟩ := perm_periodic (leapEquiv G)
  exact ⟨n, hn, fun x => by have := h x; rwa [Equiv.Perm.coe_pow] at this⟩

end Hamiltonian

/-! ## Tent and logistic maps at `r = 4` -/

section TentLogistic

open Real

/-- The tent map on `[0,1]`. -/
noncomputable def tent (θ : ℝ) : ℝ := if θ ≤ 1 / 2 then 2 * θ else 2 - 2 * θ

/-- The conjugacy `h(θ) = sin²(πθ/2)`. -/
noncomputable def conj (θ : ℝ) : ℝ := sin (π * θ / 2) ^ 2

/-- **Conjugacy**: `4 h (1 - h) = h ∘ tent`. -/
theorem logistic_tent_conj (θ : ℝ) : 4 * conj θ * (1 - conj θ) = conj (tent θ) := by
  have key : conj (tent θ) = sin (π * θ) ^ 2 := by
    unfold conj tent
    split_ifs
    · congr 1; ring_nf
    · have : π * (2 - 2 * θ) / 2 = π - π * θ := by ring
      rw [this, sin_pi_sub]
  rw [key]
  unfold conj
  have h2 : sin (π * θ) = 2 * sin (π * θ / 2) * cos (π * θ / 2) := by
    rw [← sin_two_mul]; ring_nf
  rw [h2]
  have := sin_sq_add_cos_sq (π * θ / 2)
  have h3 : 1 - sin (π * θ / 2) ^ 2 = cos (π * θ / 2) ^ 2 := by linarith
  rw [h3]; ring

end TentLogistic

/-! ## Box counting at finite resolution -/

section Box

/-- Left endpoints (in units of `3^{-n}`) of the level-`n` Cantor intervals. -/
def cantor : ℕ → Finset ℕ
  | 0 => {0}
  | n + 1 => (cantor n).image (fun a => 3 * a) ∪ (cantor n).image (fun a => 3 * a + 2)

/-- **Cantor box count**: exactly `2^n` boxes of side `3^{-n}`. -/
theorem cantor_card (n : ℕ) : (cantor n).card = 2 ^ n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [cantor]
    rw [Finset.card_union_of_disjoint, Finset.card_image_of_injective _ (fun a b h => by
        simpa using h), Finset.card_image_of_injective _ (fun a b h => by simpa using h), ih,
        pow_succ]
    · ring
    · rw [Finset.disjoint_left]
      intro x hx hx'
      simp only [Finset.mem_image] at hx hx'
      obtain ⟨a, -, rfl⟩ := hx
      obtain ⟨b, -, hb⟩ := hx'
      omega

/-- All Cantor boxes lie in `[0, 3^n)`. -/
theorem cantor_lt (n : ℕ) : ∀ a ∈ cantor n, a < 3 ^ n := by
  induction n with
  | zero => simp [cantor]
  | succ n ih =>
    intro a ha
    simp only [cantor, Finset.mem_union, Finset.mem_image] at ha
    rw [pow_succ]
    rcases ha with ⟨b, hb, rfl⟩ | ⟨b, hb, rfl⟩ <;> have := ih b hb <;> omega

/-- The granular measure of the level-`n` Cantor set is `(2/3)^n > 0`. -/
theorem cantor_measure (n : ℕ) :
    ((cantor n).card : ℝ) * (1 / 3 ^ n) = (2 / 3) ^ n := by
  rw [cantor_card]; push_cast; rw [div_pow]; ring

/-- Koch curve: the level-`n` segments are addressed by words in
`{0,1,2,3}^n`, so there are exactly `4^n` of them. -/
theorem koch_card (n : ℕ) : Fintype.card (Fin n → Fin 4) = 4 ^ n := by simp

/-- **Box dimension at scale `3^{-n}` is exact**: `log N(n) / log 3^n` equals
`log 2 / log 3` (Cantor) at every level `n ≥ 1`, with no limit. -/
theorem cantor_box_dim (n : ℕ) (hn : n ≠ 0) :
    Real.log ((cantor n).card) / Real.log ((3 : ℝ) ^ n) = Real.log 2 / Real.log 3 := by
  rw [cantor_card]; push_cast
  rw [Real.log_pow, Real.log_pow]
  have h3 : Real.log 3 ≠ 0 := by positivity
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn
  field_simp

/-- Koch: `log 4^n / log 3^n = log 4 / log 3`. -/
theorem koch_box_dim (n : ℕ) (hn : n ≠ 0) :
    Real.log ((Fintype.card (Fin n → Fin 4) : ℕ) : ℝ) / Real.log ((3 : ℝ) ^ n)
      = Real.log 4 / Real.log 3 := by
  rw [koch_card]; push_cast
  rw [Real.log_pow, Real.log_pow]
  have h3 : Real.log 3 ≠ 0 := by positivity
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn
  field_simp

/-- A nonempty granular set (e.g. a granular strange attractor) has granular
measure at least one cell, `(2ε)^n`. -/
theorem attractor_measure_pos {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    (n : ℕ) (ε : K) (hε : 0 < ε) (A : Finset (Fin n → ℤ)) (hA : A.Nonempty) :
    (2 * ε) ^ n ≤ QE.muN n ε A := by
  unfold QE.muN
  have : (1 : K) ≤ A.card := by exact_mod_cast hA.card_pos
  have hp : 0 ≤ (2 * ε) ^ n := by positivity
  nlinarith

end Box


/-! ## Ergodicity and the absence of exact mixing -/

section Ergodic

variable {X : Type*} [Fintype X] [DecidableEq X]

omit [DecidableEq X] in
/-- **Granular ergodicity.**  If a permutation has a single orbit, every
non-empty forward-invariant set is the whole space. -/
theorem ergodic_of_transitive (σ : Equiv.Perm X)
    (htr : ∀ x y : X, ∃ k : ℕ, (σ ^ k) x = y) (A : Finset X)
    (hinv : ∀ x ∈ A, σ x ∈ A) (hne : A.Nonempty) : A = Finset.univ := by
  have hpow : ∀ k : ℕ, ∀ x ∈ A, (σ ^ k) x ∈ A := by
    intro k
    induction k with
    | zero => intro x hx; simpa using hx
    | succ k ih =>
      intro x hx
      rw [pow_succ', Equiv.Perm.mul_apply]
      exact hinv _ (ih x hx)
  obtain ⟨a, ha⟩ := hne
  apply Finset.eq_univ_of_forall
  intro y
  obtain ⟨k, rfl⟩ := htr a y
  exact hpow k a ha

/-- **No exact mixing; correlations recur.**  For a permutation of a finite
set there is a time `n ≥ 1` at which every correlation returns exactly:
`#(σ^{-n} A ∩ B) = #(A ∩ B)` for all `A, B`. -/
theorem correlations_recur (σ : Equiv.Perm X) :
    ∃ n : ℕ, 0 < n ∧ ∀ A B : Finset X,
      (B.filter fun x => (σ ^ n) x ∈ A).card = (A ∩ B).card := by
  obtain ⟨n, hn, h⟩ := perm_periodic σ
  refine ⟨n, hn, fun A B => ?_⟩
  congr 1
  ext x
  simp [h x, and_comm]

end Ergodic

end QE.Dyn
