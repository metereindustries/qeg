-- SPDX-License-Identifier: MIT
-- Copyright 2026 Metere Industries, Inc. Author: Alfredo Metere.
-- Quasi-Euclidean Granular Geometry. Any derivative work must carry this notice:
--   This work is derivative of the Quasi-Euclidean Granular Geometry book
--   authored by Alfredo Metere. Copyright 2026 Metere Industries, Inc.
--   All rights reserved
-- See LICENSE.md and NOTICE.

import QuasiEuclidean.OpenDyn

/-!
# Chaos as overflow of the channel capacity `log₂ (M + 1)` of the state

* The granular state space of a map of the closed interval `[0,1]` at spacing
  `1/M` is the lattice `{0, 1/M, …, 1}`: `M + 1` points.  As a register (a
  noiseless channel with `M + 1` symbols) its Shannon capacity is
  `log₂ (M + 1)` bits; the circle `ZMod M` has `M` points and `log₂ M` bits.
* One step of a deterministic map is a deterministic channel; its capacity is
  `log₂` of the size of its image.
* A map of the form `k ↦ g (k (M - k))` (every snapped logistic map) is
  symmetric under the fold `k ↦ M - k`; for odd `M` the fold has no fixed
  point, so the image has at most `(M + 1)/2` points: **one step loses at
  least one bit**.  For even `M` the loss is at least
  `log₂ (2 (M + 1)/(M + 2))`.
* The circular doubling `k ↦ 2k mod M`, `M = 2^a m`, `m` odd, has `t`-step
  image of exactly `2^(a - min t a) m` points: it overflows exactly one bit
  per step for `a` steps, then is a bijection of the remaining states.

Everything is finite combinatorics; no measure theory is used.
-/

namespace QE.OpenDyn.Cap

open Finset Function Real QE.Info

/-! ## Capacity of a register -/

/-- The **capacity** (in bits) of a register, i.e. of a noiseless channel,
with `n` distinguishable symbols: `log₂ n`. -/
noncomputable def capacity (n : ℕ) : ℝ := Real.logb 2 n

/-- **Shannon capacity of a noiseless channel with `n` symbols.**  Every input
distribution has entropy at most `capacity n` bits, and the uniform one
attains it. -/
theorem register_capacity (n : ℕ) (hn : 0 < n) :
    (∀ p : Fin n → ℝ, (∀ i, 0 ≤ p i) → ∑ i, p i = 1 →
        entropy (Finset.univ : Finset (Fin n)) p / Real.log 2 ≤ capacity n) ∧
    entropy (Finset.univ : Finset (Fin n)) (fun _ => 1 / (n : ℝ)) / Real.log 2 = capacity n := by
  have hl : 0 < Real.log 2 := Real.log_pos (by norm_num)
  refine ⟨fun p hp hs => ?_, ?_⟩
  · have := entropy_le_log_card (Finset.univ : Finset (Fin n)) ⟨⟨0, hn⟩, Finset.mem_univ _⟩ p
      (fun i _ => hp i) hs
    rw [Finset.card_univ, Fintype.card_fin] at this
    unfold capacity Real.logb
    exact div_le_div_of_nonneg_right this hl.le
  · rw [entropy_uniform n hn]; rfl

/-- The **closed lattice** `{0, 1/M, …, 1}` of `[0,1]` at spacing `1/M`. -/
def lattice (M : ℕ) : Finset ℚ := (Finset.range (M + 1)).image (fun k : ℕ => (k : ℚ) / M)

/-- The closed lattice has `M + 1` points, both endpoints included. -/
theorem lattice_card (M : ℕ) (hM : 0 < M) :
    (lattice M).card = M + 1 ∧ (0 : ℚ) ∈ lattice M ∧ (1 : ℚ) ∈ lattice M := by
  have hM' : (M : ℚ) ≠ 0 := by exact_mod_cast hM.ne'
  refine ⟨?_, ?_, ?_⟩
  · unfold lattice
    rw [Finset.card_image_of_injective _ (fun i j h => by
      exact_mod_cast (div_left_inj' hM').mp h), Finset.card_range]
  · exact Finset.mem_image.mpr ⟨0, by simp, by simp⟩
  · exact Finset.mem_image.mpr ⟨M, by simp, div_self hM'⟩

/-- **State capacity.**  The closed lattice of `[0,1]` has capacity
`log₂ (M + 1)` bits; the circle `ZMod M` has `M` cells and capacity `log₂ M`.
The difference is the closed endpoint; at `M = 1` it is exactly one bit. -/
theorem state_capacity (M : ℕ) [NeZero M] :
    capacity (lattice M).card = Real.logb 2 ((M : ℝ) + 1) ∧
    capacity (Fintype.card (ZMod M)) = Real.logb 2 M ∧
    capacity M < capacity (M + 1) ∧
    capacity 2 - capacity 1 = 1 := by
  have hM : 0 < M := Nat.pos_of_ne_zero (NeZero.ne M)
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [(lattice_card M hM).1, capacity]; push_cast; rfl
  · rw [ZMod.card, capacity]
  · unfold capacity
    exact Real.logb_lt_logb (by norm_num) (by exact_mod_cast hM) (by push_cast; linarith)
  · simp [capacity]

/-! ## A deterministic channel -/

/-- The pushed-forward law of `p` under `f`, on the image of `f`. -/
noncomputable def push {X Y : Type*} [Fintype X] [DecidableEq Y] (f : X → Y) (p : X → ℝ)
    (y : Y) : ℝ :=
  ∑ x ∈ Finset.univ.filter (fun x => f x = y), p x

/-- **Capacity of a deterministic channel.**  For a map `f` of a finite set, the
output entropy `H(f(X))` is at most `log₂ |f(X)|` bits for every input law, and
some input law attains it: the capacity of `f` as a channel is
`capacity |f(X)|`. -/
theorem det_channel_capacity {X Y : Type*} [Fintype X] [Nonempty X] [DecidableEq Y]
    (f : X → Y) :
    (∀ p : X → ℝ, (∀ x, 0 ≤ p x) → ∑ x, p x = 1 →
        entropy (Finset.univ.image f) (push f p) / Real.log 2 ≤
          capacity (Finset.univ.image f).card) ∧
    ∃ p : X → ℝ, (∀ x, 0 ≤ p x) ∧ ∑ x, p x = 1 ∧
        entropy (Finset.univ.image f) (push f p) / Real.log 2 =
          capacity (Finset.univ.image f).card := by
  classical
  have hl : 0 < Real.log 2 := Real.log_pos (by norm_num)
  set I := Finset.univ.image f with hI
  have hIne : I.Nonempty := Finset.univ_nonempty.image f
  have hsum : ∀ p : X → ℝ, ∑ y ∈ I, push f p y = ∑ x, p x := fun p =>
    Finset.sum_fiberwise_of_maps_to (fun x _ => Finset.mem_image_of_mem f (Finset.mem_univ x)) p
  refine ⟨fun p hp hs => ?_, ?_⟩
  · have := entropy_le_log_card I hIne (push f p)
      (fun y _ => Finset.sum_nonneg fun x _ => hp x) (by rw [hsum, hs])
    unfold capacity Real.logb
    exact div_le_div_of_nonneg_right this hl.le
  · -- a section of `f` over its image
    have hsec : ∀ y ∈ I, ∃ x, f x = y := fun y hy => by
      obtain ⟨x, _, hx⟩ := Finset.mem_image.mp hy; exact ⟨x, hx⟩
    let s : Y → X := fun y => if h : y ∈ I then (hsec y h).choose else Classical.arbitrary X
    have hs : ∀ y ∈ I, f (s y) = y := fun y hy => by
      simp only [s, hy, dite_true]; exact (hsec y hy).choose_spec
    have hn : (0 : ℝ) < I.card := by exact_mod_cast hIne.card_pos
    let p : X → ℝ := fun x => if s (f x) = x then 1 / (I.card : ℝ) else 0
    have hpush : ∀ y ∈ I, push f p y = 1 / (I.card : ℝ) := by
      intro y hy
      unfold push
      rw [Finset.sum_eq_single (s y)]
      · simp only [p, hs y hy, if_true]
      · intro x hx hne
        have hfx : f x = y := (Finset.mem_filter.mp hx).2
        simp only [p, hfx]
        rw [if_neg (Ne.symm hne)]
      · intro h; exfalso; exact h (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hs y hy⟩)
    have hp0 : ∀ x, 0 ≤ p x := fun x => by
      simp only [p]; split_ifs <;> positivity
    refine ⟨p, hp0, ?_, ?_⟩
    · rw [← hsum, Finset.sum_congr rfl hpush]; simp; field_simp
    · unfold entropy capacity Real.logb
      rw [Finset.sum_congr rfl (fun y hy => by rw [hpush y hy])]
      simp only [Finset.sum_const, nsmul_eq_mul, negMulLog, one_div, Real.log_inv]
      field_simp

/-! ## The fold -/

/-- Any map `k ↦ g (k (M - k))` of the lattice `{0,…,M}` is symmetric under the
reflection `k ↦ M - k` (the lattice form of `f(x) = g(x(1-x)) = f(1-x)`). -/
theorem quadratic_symm {α : Type*} (M : ℕ) (g : ℕ → α) (k : Fin (M + 1)) :
    g ((Fin.rev k).val * (M - (Fin.rev k).val)) = g (k.val * (M - k.val)) := by
  have hk := k.isLt
  simp only [Fin.val_rev]
  congr 1
  rw [show M + 1 - (k.val + 1) = M - k.val by omega, show M - (M - k.val) = k.val by omega,
    Nat.mul_comm]

/-- The real form: `x(1-x)` is invariant under `x ↦ 1 - x`. -/
theorem quadratic_symm_real {α : Type*} (g : ℝ → α) (x : ℝ) :
    g ((1 - x) * (1 - (1 - x))) = g (x * (1 - x)) := by
  congr 1; ring

/-- The **fold** `k ↦ min (k, M - k)` of the lattice `{0,…,M}`. -/
def fold (M : ℕ) (k : Fin (M + 1)) : Fin (M + 1) := if k.val ≤ M - k.val then k else Fin.rev k

/-- A symmetric map factors through the fold. -/
theorem factor_fold {Y : Type*} (M : ℕ) (f : Fin (M + 1) → Y)
    (hf : ∀ k, f (Fin.rev k) = f k) (k : Fin (M + 1)) : f (fold M k) = f k := by
  unfold fold; split_ifs
  · rfl
  · exact hf k

/-- The fold has exactly `⌊M/2⌋ + 1` values. -/
theorem fold_image_card (M : ℕ) : (Finset.univ.image (fold M)).card = M / 2 + 1 := by
  have : Finset.univ.image (fold M) =
      (Finset.range (M / 2 + 1)).attachFin (fun i hi => by simp at hi; omega) := by
    ext k
    simp only [Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_attachFin,
      Finset.mem_range]
    constructor
    · rintro ⟨j, rfl⟩
      unfold fold; split_ifs with h
      · omega
      · simp only [Fin.val_rev]; omega
    · intro hk
      exact ⟨k, by unfold fold; rw [if_pos (by omega)]⟩
  rw [this, Finset.card_attachFin, Finset.card_range]

/-- **Fixed-point-free symmetries halve the image.**  If `σ` is a self-map of a
finite set without fixed points (e.g. a fixed-point-free involution) and
`f ∘ σ = f`, then
`2 · |f(X)| ≤ |X|`. -/
theorem card_image_le_half {X Y : Type*} [Fintype X] [DecidableEq X] [DecidableEq Y]
    (σ : X → X) (hfix : ∀ x, σ x ≠ x) (f : X → Y)
    (hf : ∀ x, f (σ x) = f x) :
    2 * (Finset.univ.image f).card ≤ Fintype.card X := by
  rw [← Finset.card_univ, Finset.card_eq_sum_card_image f Finset.univ, mul_comm,
    Finset.card_eq_sum_ones, Finset.sum_mul]
  apply Finset.sum_le_sum
  intro y hy
  obtain ⟨x, _, rfl⟩ := Finset.mem_image.mp hy
  rw [one_mul]
  have h2 : ({x, σ x} : Finset X) ⊆ Finset.univ.filter (fun z => f z = f x) := by
    intro z hz
    rcases Finset.mem_insert.mp hz with rfl | hz
    · simp
    · rw [Finset.mem_singleton.mp hz]; simp [hf]
  have := Finset.card_le_card h2
  rwa [Finset.card_pair (Ne.symm (hfix x))] at this

/-- For odd `M` the reflection `k ↦ M - k` of `{0,…,M}` has no fixed point. -/
theorem rev_ne_self (M : ℕ) (hM : Odd M) (k : Fin (M + 1)) : Fin.rev k ≠ k := by
  intro h
  have := congrArg Fin.val h
  simp only [Fin.val_rev] at this
  obtain ⟨c, rfl⟩ := hM
  omega

/-- For odd `M` a symmetric map of `{0,…,M}` has at most `(M + 1)/2` values. -/
theorem symmetric_image_card_odd {Y : Type*} [DecidableEq Y] (M : ℕ) (hM : Odd M)
    (f : Fin (M + 1) → Y) (hf : ∀ k, f (Fin.rev k) = f k) :
    2 * (Finset.univ.image f).card ≤ M + 1 := by
  have := card_image_le_half Fin.rev (rev_ne_self M hM) f hf
  simpa using this

/-- For any `M` a symmetric map of `{0,…,M}` has at most `⌊M/2⌋ + 1` values. -/
theorem symmetric_image_card_fold {Y : Type*} [DecidableEq Y] (M : ℕ)
    (f : Fin (M + 1) → Y) (hf : ∀ k, f (Fin.rev k) = f k) :
    (Finset.univ.image f).card ≤ M / 2 + 1 := by
  have : Finset.univ.image f = (Finset.univ.image (fold M)).image f := by
    rw [Finset.image_image]; ext y
    simp only [Finset.mem_image, Finset.mem_univ, true_and, Function.comp]
    constructor
    · rintro ⟨k, rfl⟩; exact ⟨k, factor_fold M f hf k⟩
    · rintro ⟨k, rfl⟩; exact ⟨fold M k, rfl⟩
  rw [this, ← fold_image_card M]
  exact Finset.card_image_le

/-- **One fold step loses at least one bit (odd `M`).**  A symmetric map of the
closed lattice `{0,…,M}`, `M` odd, as a channel from a state of capacity
`log₂ (M+1)` bits, has capacity at most `log₂ (M+1) - 1`. -/
theorem one_bit_loss {Y : Type*} [DecidableEq Y] (M : ℕ) (hM : Odd M)
    (f : Fin (M + 1) → Y) (hf : ∀ k, f (Fin.rev k) = f k) :
    1 ≤ capacity (M + 1) - capacity (Finset.univ.image f).card := by
  have h2 := symmetric_image_card_odd M hM f hf
  have hpos : 0 < (Finset.univ.image f).card :=
    (Finset.univ_nonempty.image f).card_pos
  unfold capacity
  have hc : (0 : ℝ) < (Finset.univ.image f).card := by exact_mod_cast hpos
  have h2' : (2 : ℝ) * (Finset.univ.image f).card ≤ ((M + 1 : ℕ) : ℝ) := by exact_mod_cast h2
  have := Real.logb_le_logb_of_le (b := 2) (by norm_num) (by positivity) h2'
  rw [Real.logb_mul (by norm_num) hc.ne', Real.logb_self_eq_one (by norm_num)] at this
  linarith

/-- **The loss for any `M`:** at least `log₂ ((M+1)/(⌊M/2⌋+1))` bits. -/
theorem fold_bit_loss {Y : Type*} [DecidableEq Y] (M : ℕ)
    (f : Fin (M + 1) → Y) (hf : ∀ k, f (Fin.rev k) = f k) :
    Real.logb 2 (((M + 1 : ℕ) : ℝ) / ((M / 2 + 1 : ℕ) : ℝ)) ≤
      capacity (M + 1) - capacity (Finset.univ.image f).card := by
  have h := symmetric_image_card_fold M f hf
  have hpos : 0 < (Finset.univ.image f).card := (Finset.univ_nonempty.image f).card_pos
  have hc : (0 : ℝ) < (Finset.univ.image f).card := by exact_mod_cast hpos
  have h' : ((Finset.univ.image f).card : ℝ) ≤ ((M / 2 + 1 : ℕ) : ℝ) := by exact_mod_cast h
  unfold capacity
  rw [Real.logb_div (by positivity) (by positivity)]
  have := Real.logb_le_logb_of_le (b := 2) (by norm_num) hc h'
  linarith

/-- **Even `M`:** the loss is at least `log₂ (2 (M+1)/(M+2))`, which tends to
one bit. -/
theorem fold_bit_loss_even {Y : Type*} [DecidableEq Y] (M : ℕ) (hM : Even M)
    (f : Fin (M + 1) → Y) (hf : ∀ k, f (Fin.rev k) = f k) :
    Real.logb 2 (2 * ((M : ℝ) + 1) / ((M : ℝ) + 2)) ≤
      capacity (M + 1) - capacity (Finset.univ.image f).card := by
  have h := fold_bit_loss M f hf
  obtain ⟨c, rfl⟩ := hM
  have e : (c + c) / 2 = c := by omega
  rw [e] at h
  convert h using 2
  push_cast
  field_simp
  ring

/-! ## The snapped logistic map -/

/-- The snapped logistic map (any `r`), and each of its iterates `t ≥ 1`, is
symmetric under `k ↦ M - k`. -/
theorem snapLogistic_iterate_symm (r : ℝ) (M t : ℕ) (ht : 1 ≤ t) (k : Fin (M + 1)) :
    (snapLogistic r M)^[t] (Fin.rev k) = (snapLogistic r M)^[t] k := by
  obtain ⟨s, rfl⟩ := Nat.exists_eq_add_of_le' ht
  rw [iterate_succ_apply, iterate_succ_apply, snapLogistic_symm]

/-- **The snapped logistic map loses at least one bit per fold (odd `M`).**  For
every real `r`, every odd `M` and every `t ≥ 1`, the `t`-step channel of the
snapped logistic map on the `M + 1` points of `[0,1]` has capacity at most
`log₂ (M + 1) - 1`. -/
theorem snapLogistic_one_bit (r : ℝ) (M t : ℕ) (hM : Odd M) (ht : 1 ≤ t) :
    1 ≤ capacity (M + 1) - capacity (Finset.univ.image ((snapLogistic r M)^[t])).card :=
  one_bit_loss M hM _ (snapLogistic_iterate_symm r M t ht)

/-- The images of the iterates of any self-map are nested, so the capacity of the
`t`-step channel is nonincreasing in `t`. -/
theorem image_iterate_succ_subset {X : Type*} [Fintype X] [DecidableEq X] (f : X → X) (t : ℕ) :
    Finset.univ.image (f^[t + 1]) ⊆ Finset.univ.image (f^[t]) := by
  intro y hy
  obtain ⟨x, _, rfl⟩ := Finset.mem_image.mp hy
  rw [iterate_succ_apply]
  exact Finset.mem_image_of_mem _ (Finset.mem_univ _)

theorem capacity_iterate_antitone {X : Type*} [Fintype X] [DecidableEq X] (f : X → X)
    (s t : ℕ) (hst : s ≤ t) (hne : Nonempty X) :
    capacity (Finset.univ.image (f^[t])).card ≤ capacity (Finset.univ.image (f^[s])).card := by
  have hsub : Finset.univ.image (f^[t]) ⊆ Finset.univ.image (f^[s]) := by
    induction t, hst using Nat.le_induction with
    | base => exact le_rfl
    | succ t _ ih => exact (image_iterate_succ_subset f t).trans ih
  have hpos : 0 < (Finset.univ.image (f^[t])).card := (Finset.univ_nonempty.image _).card_pos
  unfold capacity
  exact Real.logb_le_logb_of_le (by norm_num) (by exact_mod_cast hpos)
    (by exact_mod_cast Finset.card_le_card hsub)

/-! ## The circular doubling: exact overflow -/

/-- The `t`-step circular doubling `k ↦ 2^t k mod M` on `{0,…,M-1}`. -/
def circ (M t k : ℕ) : ℕ := 2 ^ t * k % M

theorem circ_succ (M t k : ℕ) : circ M 1 (circ M t k) = circ M (t + 1) k := by
  unfold circ
  rw [pow_one, Nat.mul_mod, Nat.mod_mod, ← Nat.mul_mod, pow_succ]; ring_nf

/-- `circ` is the iterate of the circle map `mulMap 2 M` of `thm:dyn-circular`. -/
theorem circ_mulMap (M t k : ℕ) :
    (mulMap 2 M)^[t] (k : ZMod M) = ((circ M t k : ℕ) : ZMod M) := by
  rw [mulMap_iterate, circ, ZMod.natCast_mod]; push_cast; rfl

/-- **Exact image of the `t`-step circular doubling.**  For `M = 2^a m`, `m`
odd, the image has exactly `2^(a - min t a) m` points. -/
theorem circ_image_card (a m t : ℕ) (hm : Odd m) :
    ((Finset.range (2 ^ a * m)).image (circ (2 ^ a * m) t)).card = 2 ^ (a - min t a) * m := by
  have hm0 : 0 < m := hm.pos
  rcases le_total t a with hta | hta
  · -- overflow phase: the image is `{2^t r : r < 2^(a-t) m}`
    rw [min_eq_left hta]
    have hM : 2 ^ a * m = 2 ^ t * (2 ^ (a - t) * m) := by
      rw [← mul_assoc, ← pow_add, Nat.add_sub_cancel' hta]
    have himg : (Finset.range (2 ^ a * m)).image (circ (2 ^ a * m) t) =
        (Finset.range (2 ^ (a - t) * m)).image (fun r => 2 ^ t * r) := by
      ext y
      simp only [Finset.mem_image, Finset.mem_range, circ]
      constructor
      · rintro ⟨k, _, rfl⟩
        refine ⟨k % (2 ^ (a - t) * m), Nat.mod_lt _ (by positivity), ?_⟩
        rw [hM, Nat.mul_mod_mul_left]
      · rintro ⟨r, hr, rfl⟩
        refine ⟨r, by rw [hM]; nlinarith [Nat.one_le_two_pow (n := t)], ?_⟩
        rw [hM, Nat.mul_mod_mul_left, Nat.mod_eq_of_lt hr]
    rw [himg, Finset.card_image_of_injective _ (fun i j h => by
      simpa using h), Finset.card_range]
  · -- bijective phase: the image is `{2^a r : r < m}`
    rw [min_eq_right hta, Nat.sub_self, pow_zero, one_mul]
    have hcop : Nat.Coprime (2 ^ (t - a)) m :=
      Nat.Coprime.pow_left _ ((Nat.coprime_two_left).mpr hm)
    have himg : (Finset.range (2 ^ a * m)).image (circ (2 ^ a * m) t) =
        (Finset.range m).image (fun r => 2 ^ a * r) := by
      ext y
      simp only [Finset.mem_image, Finset.mem_range, circ]
      constructor
      · rintro ⟨k, _, rfl⟩
        refine ⟨2 ^ (t - a) * k % m, Nat.mod_lt _ hm0, ?_⟩
        rw [← Nat.mul_mod_mul_left, ← mul_assoc, ← pow_add, Nat.add_sub_cancel' hta]
      · rintro ⟨r, hr, rfl⟩
        -- solve `2^(t-a) k ≡ r (mod m)` with `k < m`
        have : NeZero m := ⟨hm0.ne'⟩
        let u := ZMod.unitOfCoprime _ hcop
        let k : ℕ := ((u⁻¹ : (ZMod m)ˣ) * (r : ZMod m) : ZMod m).val
        have hk : 2 ^ (t - a) * k % m = r := by
          have : ((2 ^ (t - a) * k : ℕ) : ZMod m) = (r : ZMod m) := by
            push_cast
            simp only [k, ZMod.natCast_val, ZMod.cast_id', id]
            rw [← mul_assoc]
            have hu : ((u : (ZMod m)ˣ) : ZMod m) = ((2 ^ (t - a) : ℕ) : ZMod m) :=
              ZMod.coe_unitOfCoprime _ hcop
            push_cast at hu
            rw [← hu, Units.mul_inv, one_mul]
          rw [← ZMod.val_natCast, this, ZMod.val_natCast, Nat.mod_eq_of_lt hr]
        refine ⟨k, ?_, ?_⟩
        · have : k < m := ZMod.val_lt _
          nlinarith [Nat.one_le_two_pow (n := a)]
        · rw [show 2 ^ t * k % (2 ^ a * m) = 2 ^ a * (2 ^ (t - a) * k % m) by
            rw [← Nat.mul_mod_mul_left, ← mul_assoc, ← pow_add, Nat.add_sub_cancel' hta], hk]
    rw [himg, Finset.card_image_of_injective _ (fun i j h => by
      simpa using h), Finset.card_range]

/-- **Exact overflow of the circular register.**  For `M = 2^a m`, `m` odd, the
capacity of the `t`-step channel of the circular doubling is
`log₂ M - min t a`: exactly one bit overflows per step for the first `a`
steps, none afterwards. -/
theorem circ_capacity (a m t : ℕ) (hm : Odd m) :
    capacity ((Finset.range (2 ^ a * m)).image (circ (2 ^ a * m) t)).card =
      capacity (2 ^ a * m) - min t a := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm.pos
  rw [circ_image_card a m t hm]
  unfold capacity
  push_cast
  rw [Real.logb_mul (by positivity) hm0.ne', Real.logb_mul (by positivity) hm0.ne',
    Real.logb_pow, Real.logb_pow, Real.logb_self_eq_one (by norm_num)]
  rw [Nat.cast_sub (min_le_right t a), Nat.cast_min]; ring

/-- **One bit per step, then none.**  The loss of the `(t+1)`-th step of the
circular doubling, `M = 2^a m`, `m` odd, is exactly one bit if `t < a` and zero
if `t ≥ a`. -/
theorem circ_step_loss (a m t : ℕ) (hm : Odd m) :
    capacity ((Finset.range (2 ^ a * m)).image (circ (2 ^ a * m) t)).card -
      capacity ((Finset.range (2 ^ a * m)).image (circ (2 ^ a * m) (t + 1))).card =
        if t < a then 1 else 0 := by
  rw [circ_capacity a m t hm, circ_capacity a m (t + 1) hm]
  split_ifs with h
  · rw [min_eq_left h.le, min_eq_left (by omega : t + 1 ≤ a)]; push_cast; ring
  · rw [min_eq_right (by omega : a ≤ t), min_eq_right (by omega : a ≤ t + 1)]; ring

/-- After the `a` overflow steps the circle map is a bijection of the surviving
states (the cycle states). -/
theorem circ_bijOn (a m t : ℕ) (hm : Odd m) (hta : a ≤ t) :
    Set.BijOn (circ (2 ^ a * m) 1)
      ((Finset.range (2 ^ a * m)).image (circ (2 ^ a * m) t) : Set ℕ)
      ((Finset.range (2 ^ a * m)).image (circ (2 ^ a * m) t) : Set ℕ) := by
  set S := (Finset.range (2 ^ a * m)).image (circ (2 ^ a * m) t)
  set S' := (Finset.range (2 ^ a * m)).image (circ (2 ^ a * m) (t + 1))
  have hS' : S.image (circ (2 ^ a * m) 1) = S' := by
    rw [Finset.image_image]; congr 1; funext k; exact circ_succ _ _ _
  have hcard : S'.card = S.card := by
    rw [circ_image_card a m t hm, circ_image_card a m (t + 1) hm,
      min_eq_right hta, min_eq_right (by omega : a ≤ t + 1)]
  have hsub : S' ⊆ S := by
    intro y hy
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hy
    exact Finset.mem_image.mpr ⟨circ (2 ^ a * m) 1 k,
      by unfold circ; exact Finset.mem_range.mpr (Nat.mod_lt _ (by
        have := (Finset.mem_range.mp hk); omega)),
      by rw [show t + 1 = 1 + t by ring]; unfold circ; rw [Nat.mul_mod, Nat.mod_mod,
        ← Nat.mul_mod, ← mul_assoc, ← pow_add, add_comm 1 t]⟩
  have heq : S' = S := Finset.eq_of_subset_of_card_le hsub hcard.ge
  have hinj : Set.InjOn (circ (2 ^ a * m) 1) (S : Set ℕ) := by
    rw [← Finset.card_image_iff, hS', hcard]
  refine ⟨fun x hx => ?_, hinj, fun y hy => ?_⟩
  · have : circ (2 ^ a * m) 1 x ∈ S.image (circ (2 ^ a * m) 1) := Finset.mem_image_of_mem _ hx
    rw [hS', heq] at this; exact this
  · have hy' : y ∈ S.image (circ (2 ^ a * m) 1) := by rw [hS', heq]; exact hy
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy'
    exact ⟨x, hx, rfl⟩

/-- **The horizon.**  The total overflow of the circular register after `t`
steps is `min t a` bits: at most one bit per step (the Lyapunov exponent
`ln 2`) and at most the initial information `log₂ M`.  On the dyadic circle
`M = 2^K` the information is exhausted (capacity `0`) exactly at `t = K = log₂ M`. -/
theorem circ_horizon (a m t : ℕ) (hm : Odd m) :
    capacity (2 ^ a * m) -
        capacity ((Finset.range (2 ^ a * m)).image (circ (2 ^ a * m) t)).card ≤ t ∧
    capacity (2 ^ a * m) -
        capacity ((Finset.range (2 ^ a * m)).image (circ (2 ^ a * m) t)).card ≤
      capacity (2 ^ a * m) ∧
    (m = 1 → (capacity ((Finset.range (2 ^ a * m)).image (circ (2 ^ a * m) t)).card = 0 ↔
      a ≤ t)) := by
  have hc := circ_capacity a m t hm
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm.pos
  have hlog : capacity (2 ^ a * m) = a + Real.logb 2 m := by
    unfold capacity; push_cast
    rw [Real.logb_mul (by positivity) (by positivity), Real.logb_pow,
      Real.logb_self_eq_one (by norm_num)]; ring
  have hlm : 0 ≤ Real.logb 2 m := Real.logb_nonneg (by norm_num) hm1
  refine ⟨?_, ?_, ?_⟩
  · rw [hc]; have : ((min t a : ℕ) : ℝ) ≤ t := by exact_mod_cast min_le_left t a
    linarith
  · rw [hc, hlog]; have : ((min t a : ℕ) : ℝ) ≤ a := by exact_mod_cast min_le_right t a
    linarith
  · rintro rfl
    rw [hc, hlog]; simp only [Nat.cast_one, Real.logb_one, add_zero]
    constructor
    · intro h
      have : ((min t a : ℕ) : ℝ) = a := by linarith
      have : min t a = a := by exact_mod_cast this
      omega
    · intro h; rw [min_eq_right h]; ring

end QE.OpenDyn.Cap
