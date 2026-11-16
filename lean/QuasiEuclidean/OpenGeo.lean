-- SPDX-License-Identifier: MIT
-- Copyright 2026 Metere Industries, Inc. Author: Alfredo Metere.
-- Quasi-Euclidean Granular Geometry. Any derivative work must carry this notice:
--   This work is derivative of the Quasi-Euclidean Granular Geometry book
--   authored by Alfredo Metere. Copyright 2026 Metere Industries, Inc.
--   All rights reserved
-- See LICENSE.md and NOTICE.

import QuasiEuclidean.NSA_Internal

/-!
# Open problems of geometry: lattice dependence, isotropy, Lorentz invariance

Exact finitary facts behind three settled open problems of the epilogue.

* **Lattice-independent retained information.**  For a lattice `a + 2εℤ` the
  openness of a boundary point `e` changes the count by `1` if `e` is a lattice
  point and by `0` otherwise (`toggle_point`, `count_closed_eq_open_of_not_mem`).
  The retained first-order term of an interval equals its openness count for every
  choice of openness iff both endpoints are lattice points
  (`retained_openness_iff`).  A point lies on all the lattices `p + (g/N)ℤ` of two
  consecutive `N` iff it lies on `p + gℤ` (`mem_consecutive_iff`).  Boxes with faces
  on lattice hyperplanes have product counts (`box_count`).
* **Isotropy.**  Exact counts of the unit square rotated by `arctan (3/4)` and of
  the unit square boosted with Doppler factor `2`, at every lattice spacing
  `1/(5m)`, resp. `1/(4m)` (`rot_square_count`, `boost_square_count`), and the
  resulting order-`ε` differences of content (`rot_square_content`,
  `boost_square_content`).
* **Lorentz invariance.**  Boosts in `1+1` dimensions over any ordered field, in
  light-cone form (`boost`).  No finite set other than a subset of `{0}` is
  invariant under a single nontrivial boost (`finite_boost_invariant`), likewise
  for hyperfinite sets (`hyperfinite_boost_invariant`) and in `1+n` dimensions
  (`finite_boostAt_invariant`); a boost-invariant subset of `ℝ²` with a nonzero
  point meets a compact set in infinitely many points (`not_locally_finite`).

Everything is counting or algebra; no Lebesgue measure is used.
-/

set_option linter.unusedSectionVars false

namespace QE.OpenGeo

open Finset

/-! ## Part 1: openness information and the lattice -/

section Openness
variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-- **Toggling a point.**  For any finite window `W` of indices, any injective
placement `f` of the indices (a lattice) and any set `A`, adding the point `e`
to `A` adds exactly the lattice points placed at `e` (one if `f` is injective and
`e` is the position of an index of `W`, none otherwise; `card_filter_eq_point`). -/
theorem toggle_point {α X : Type*} [DecidableEq α] [DecidableEq X] (W : Finset α) (f : α → X)
    (A : Set X) [DecidablePred (· ∈ A)] (e : X) :
    (W.filter (fun k => f k ∈ A ∨ f k = e)).card =
      (W.filter (fun k => f k ∈ A ∧ f k ≠ e)).card +
        (W.filter (fun k => f k = e)).card := by
  rw [← card_union_of_disjoint]
  · congr 1
    ext k
    simp only [mem_filter, mem_union]
    constructor
    · rintro ⟨hk, h⟩
      by_cases he : f k = e
      · exact Or.inr ⟨hk, he⟩
      · exact Or.inl ⟨hk, h.resolve_right he, he⟩
    · rintro (⟨hk, h, _⟩ | ⟨hk, he⟩)
      · exact ⟨hk, Or.inl h⟩
      · exact ⟨hk, Or.inr he⟩
  · rw [disjoint_filter]
    intro k _ h1 h2
    exact h1.2 h2

/-- The number of indices of `W` placed at `e` by an injective placement is `1` if
`e` is the position of an index of `W` and `0` otherwise. -/
theorem card_filter_eq_point {α X : Type*} [DecidableEq X] (W : Finset α) (f : α → X)
    (hf : Function.Injective f) (e : X) :
    (W.filter (fun k => f k = e)).card = if ∃ k ∈ W, f k = e then 1 else 0 := by
  split_ifs with h
  · obtain ⟨k, hk, hke⟩ := h
    rw [card_eq_one]
    refine ⟨k, ?_⟩
    ext j
    simp only [mem_filter, mem_singleton]
    constructor
    · rintro ⟨_, hj⟩
      exact hf (hj.trans hke.symm)
    · rintro rfl
      exact ⟨hk, hke⟩
  · rw [card_eq_zero, filter_eq_empty_iff]
    intro k hk hke
    exact h ⟨k, hk, hke⟩

/-- Membership in an interval with endpoints `b, c` whose openness is given by the
flags `lc` (left closed) and `rc` (right closed). -/
def inIv (lc rc : Bool) (b c x : K) : Prop :=
  (if lc then b ≤ x else b < x) ∧ (if rc then x ≤ c else x < c)

instance (lc rc : Bool) (b c x : K) : Decidable (inIv lc rc b c x) := by
  unfold inIv; cases lc <;> cases rc <;> simp only [Bool.false_eq_true, ite_false, ite_true] <;>
    infer_instance

/-- Number of points of the lattice `a + 2εℤ` (indices in the window `W`) in the
interval with endpoints `b, c` and openness flags `lc, rc`. -/
def ivCount (W : Finset ℤ) (a ε b c : K) (lc rc : Bool) : ℕ :=
  (W.filter (fun k : ℤ => inIv lc rc b c (a + 2 * ε * k))).card

/-- The openness count: `+1` for each closed endpoint, `-1` for each open one. -/
def kappa (lc rc : Bool) : K := (if lc then 1 else -1) + (if rc then 1 else -1)

/-- An endpoint that is not a lattice point does not see its own openness: the
count is the same whether the left endpoint is closed or open. -/
theorem count_left_toggle_of_not_mem (W : Finset ℤ) (a ε b c : K) (rc : Bool)
    (hb : ∀ k : ℤ, a + 2 * ε * k ≠ b) :
    ivCount W a ε b c true rc = ivCount W a ε b c false rc := by
  unfold ivCount
  congr 1
  apply filter_congr
  intro k _
  unfold inIv
  simp only [ite_true, Bool.false_eq_true, ite_false]
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨lt_of_le_of_ne h1 (Ne.symm (hb k)), h2⟩
  · rintro ⟨h1, h2⟩; exact ⟨h1.le, h2⟩

/-- The same for the right endpoint. -/
theorem count_right_toggle_of_not_mem (W : Finset ℤ) (a ε b c : K) (lc : Bool)
    (hc : ∀ k : ℤ, a + 2 * ε * k ≠ c) :
    ivCount W a ε b c lc true = ivCount W a ε b c lc false := by
  unfold ivCount
  congr 1
  apply filter_congr
  intro k _
  unfold inIv
  simp only [ite_true, Bool.false_eq_true, ite_false]
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨h1, lt_of_le_of_ne h2 (hc k)⟩
  · rintro ⟨h1, h2⟩; exact ⟨h1, h2.le⟩

lemma lat_le_iff {ε : K} (hε : 0 < ε) (a : K) (m k : ℤ) :
    a + 2 * ε * m ≤ a + 2 * ε * k ↔ m ≤ k := by
  constructor
  · intro h
    have : 2 * ε * (m : K) ≤ 2 * ε * k := by linarith
    exact_mod_cast le_of_mul_le_mul_left this (by linarith)
  · intro h
    have : (m : K) ≤ k := by exact_mod_cast h
    nlinarith

lemma lat_lt_iff {ε : K} (hε : 0 < ε) (a : K) (m k : ℤ) :
    a + 2 * ε * m < a + 2 * ε * k ↔ m < k := by
  rw [lt_iff_not_ge, lt_iff_not_ge, lat_le_iff hε]

/-- **Interval count with endpoints on the lattice.**  If `b = a + 2εm₁` and
`c = a + 2εm₂` with `m₁ < m₂` and the window contains all indices of `[b, c]`, then
`2ε · count = (c - b) + ε κ` for every choice of openness. -/
theorem count_of_mem (W : Finset ℤ) (a ε : K) (hε : 0 < ε) (m₁ m₂ : ℤ) (hm : m₁ < m₂)
    (hW : ∀ k : ℤ, m₁ ≤ k → k ≤ m₂ → k ∈ W) (lc rc : Bool) :
    2 * ε * (ivCount W a ε (a + 2 * ε * m₁) (a + 2 * ε * m₂) lc rc : K) =
      ((a + 2 * ε * m₂) - (a + 2 * ε * m₁)) + ε * kappa lc rc := by
  unfold ivCount kappa
  cases lc <;> cases rc
  all_goals simp only [inIv, Bool.false_eq_true, ite_false, ite_true, lat_le_iff hε,
    lat_lt_iff hε]
  · have : W.filter (fun k : ℤ => m₁ < k ∧ k < m₂) = Ioo m₁ m₂ := by
      ext k; simp only [mem_filter, mem_Ioo]
      exact ⟨fun h => h.2, fun h => ⟨hW k h.1.le h.2.le, h⟩⟩
    rw [this, Int.card_Ioo]
    have h' : ((m₂ - m₁ - 1).toNat : ℤ) = m₂ - m₁ - 1 := Int.toNat_of_nonneg (by omega)
    have h'' : ((m₂ - m₁ - 1).toNat : K) = (m₂ : K) - m₁ - 1 := by exact_mod_cast h'
    rw [h'']; ring
  · have : W.filter (fun k : ℤ => m₁ < k ∧ k ≤ m₂) = Ioc m₁ m₂ := by
      ext k; simp only [mem_filter, mem_Ioc]
      exact ⟨fun h => h.2, fun h => ⟨hW k h.1.le h.2, h⟩⟩
    rw [this, Int.card_Ioc]
    have h' : ((m₂ - m₁).toNat : ℤ) = m₂ - m₁ := Int.toNat_of_nonneg (by omega)
    have h'' : ((m₂ - m₁).toNat : K) = (m₂ : K) - m₁ := by exact_mod_cast h'
    rw [h'']; ring
  · have : W.filter (fun k : ℤ => m₁ ≤ k ∧ k < m₂) = Ico m₁ m₂ := by
      ext k; simp only [mem_filter, mem_Ico]
      exact ⟨fun h => h.2, fun h => ⟨hW k h.1 h.2.le, h⟩⟩
    rw [this, Int.card_Ico]
    have h' : ((m₂ - m₁).toNat : ℤ) = m₂ - m₁ := Int.toNat_of_nonneg (by omega)
    have h'' : ((m₂ - m₁).toNat : K) = (m₂ : K) - m₁ := by exact_mod_cast h'
    rw [h'']; ring
  · have : W.filter (fun k : ℤ => m₁ ≤ k ∧ k ≤ m₂) = Icc m₁ m₂ := by
      ext k; simp only [mem_filter, mem_Icc]
      exact ⟨fun h => h.2, fun h => ⟨hW k h.1 h.2, h⟩⟩
    rw [this, Int.card_Icc]
    have h' : ((m₂ + 1 - m₁).toNat : ℤ) = m₂ + 1 - m₁ := Int.toNat_of_nonneg (by omega)
    have h'' : ((m₂ + 1 - m₁).toNat : K) = (m₂ : K) + 1 - m₁ := by exact_mod_cast h'
    rw [h'']; ring

/-- **Characterisation of retained openness information.**  For the lattice
`a + 2εℤ` (indices in a window `W` that covers `[b, c]`), the retained first-order
term of the interval with endpoints `b < c` equals its openness count `κ` for
every choice of openness,
`2ε · #(I ∩ Λ) = (c - b) + ε κ(I)`, if and only if both endpoints are lattice
points. -/
theorem retained_openness_iff (W : Finset ℤ) (a ε b c : K) (hε : 0 < ε) (hbc : b < c)
    (hW : ∀ k : ℤ, b ≤ a + 2 * ε * k → a + 2 * ε * k ≤ c → k ∈ W) :
    (∀ lc rc : Bool, 2 * ε * (ivCount W a ε b c lc rc : K) = (c - b) + ε * kappa lc rc) ↔
      (∃ m : ℤ, a + 2 * ε * m = b) ∧ (∃ m : ℤ, a + 2 * ε * m = c) := by
  constructor
  · intro h
    constructor
    · by_contra hb
      push Not at hb
      have e1 := h true true
      have e2 := h false true
      rw [count_left_toggle_of_not_mem W a ε b c true hb] at e1
      rw [e1] at e2
      simp only [kappa, ite_true, Bool.false_eq_true, ite_false] at e2
      linarith
    · by_contra hc
      push Not at hc
      have e1 := h true true
      have e2 := h true false
      rw [count_right_toggle_of_not_mem W a ε b c true hc] at e1
      rw [e1] at e2
      simp only [kappa, ite_true, Bool.false_eq_true, ite_false] at e2
      linarith
  · rintro ⟨⟨m₁, rfl⟩, ⟨m₂, rfl⟩⟩ lc rc
    have hm : m₁ < m₂ := (lat_lt_iff hε a m₁ m₂).mp hbc
    refine count_of_mem W a ε hε m₁ m₂ hm ?_ lc rc
    intro k h1 h2
    exact hW k ((lat_le_iff hε a _ _).mpr h1) ((lat_le_iff hε a _ _).mpr h2)

/-- **The lattices of two consecutive spacings.**  For `g ≠ 0` and `N ≥ 1`, a point
lies on both lattices `p + (g/N)ℤ` and `p + (g/(N+1))ℤ` iff it lies on `p + gℤ`.
Hence the intersection of all lattices `p + (g/N)ℤ`, `N` ranging over any set
containing two consecutive integers (e.g. all infinite hypernaturals), is the
coarse lattice `p + gℤ`. -/
theorem mem_consecutive_iff (p g e : K) (hg : g ≠ 0) (N : ℕ) (hN : 1 ≤ N) :
    ((∃ j : ℤ, e = p + g / N * j) ∧ (∃ j : ℤ, e = p + g / (N + 1 : ℕ) * j)) ↔
      ∃ m : ℤ, e = p + g * m := by
  have hN0 : (N : K) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
  have hN1 : ((N + 1 : ℕ) : K) ≠ 0 := by exact_mod_cast (show N + 1 ≠ 0 by omega)
  constructor
  · rintro ⟨⟨j, hj⟩, ⟨j', hj'⟩⟩
    -- j (N+1) = j' N
    have key : (j : K) * ((N + 1 : ℕ) : K) = (j' : K) * N := by
      have h := hj.symm.trans hj'
      have h2 : g / N * j = g / (N + 1 : ℕ) * j' := by linarith
      field_simp at h2
      linarith
    have keyZ : j * ((N : ℤ) + 1) = j' * N := by
      have : ((j * ((N : ℤ) + 1) : ℤ) : K) = ((j' * N : ℤ) : K) := by push_cast at key ⊢; linarith
      exact_mod_cast this
    have hdvd : (N : ℤ) ∣ j := by
      have h1 : (N : ℤ) ∣ j * ((N : ℤ) + 1) := ⟨j', by rw [keyZ]; ring⟩
      have hcop : IsCoprime (N : ℤ) ((N : ℤ) + 1) := ⟨-1, 1, by ring⟩
      exact hcop.dvd_of_dvd_mul_right h1
    obtain ⟨m, hm⟩ := hdvd
    refine ⟨m, ?_⟩
    rw [hj, hm]
    push_cast
    field_simp
  · rintro ⟨m, rfl⟩
    refine ⟨⟨N * m, ?_⟩, ⟨(N + 1 : ℕ) * m, ?_⟩⟩
    · push_cast; field_simp
    · push_cast; field_simp

/-- **Boxes with faces on lattice hyperplanes.**  The count of lattice points of a
box `∏ᵢ Jᵢ` whose sides `Jᵢ ⊆ ℤ` are given by per-coordinate conditions is the
product of the side counts: `#(∏ Jᵢ) = ∏ #Jᵢ`.  With side counts
`mᵢ + δᵢ`, `δᵢ ∈ {1, 0, -1}` for closed, half-open and open sides, the content is
`(2ε)ⁿ ∏ (mᵢ + δᵢ) = ∏ (ℓᵢ + 2εδᵢ)`. -/
theorem box_count {n : ℕ} (W : Fin n → Finset ℤ) (P : Fin n → ℤ → Prop)
    [∀ i, DecidablePred (P i)] :
    ((Fintype.piFinset W).filter (fun k => ∀ i, P i (k i))).card =
      ∏ i, ((W i).filter (P i)).card := by
  rw [← Fintype.card_piFinset]
  congr 1
  ext k
  simp only [mem_filter, Fintype.mem_piFinset]
  exact ⟨fun h i => ⟨h.1 i, h.2 i⟩, fun h => ⟨fun i => (h i).1, fun i => (h i).2⟩⟩

/-- The content of such a box: `(2ε)ⁿ ∏ (mᵢ + δᵢ) = ∏ (ℓᵢ + 2ε δᵢ)` with
`ℓᵢ = 2ε mᵢ`. -/
theorem box_content {n : ℕ} (ε : K) (m δ : Fin n → K) :
    (2 * ε) ^ n * ∏ i, (m i + δ i) = ∏ i, (2 * ε * m i + 2 * ε * δ i) := by
  rw [← Fin.prod_const, ← prod_mul_distrib]
  congr 1; ext i; ring

end Openness

/-! ## Part 2: rotated and boosted squares (exact counts) -/

section Squares

/-- Residues in a run of `q m + 1` integers: `#{v ∈ [0, qm] : v mod q = s}` is
`m + 1` for `s = 0` and `m` for `0 < s < q`. -/
theorem card_res (q : ℤ) (m : ℕ) (s : ℤ) (hq : 0 < q) (hs0 : 0 ≤ s) (hsq : s < q) :
    ((Icc 0 (q * m)).filter (fun v => v % q = s)).card = m + if s = 0 then 1 else 0 := by
  set M : ℤ := if s = 0 then m else (m : ℤ) - 1 with hM
  have hset : (Icc 0 (q * m)).filter (fun v => v % q = s) =
      (Icc 0 M).image (fun j : ℤ => s + q * j) := by
    ext v
    simp only [mem_filter, mem_Icc, mem_image]
    constructor
    · rintro ⟨⟨h0, h1⟩, hv⟩
      refine ⟨v / q, ⟨Int.ediv_nonneg h0 hq.le, ?_⟩, ?_⟩
      · have hdiv := Int.emod_add_mul_ediv v q
        rw [hv] at hdiv
        rw [hM]
        split_ifs with hs
        · subst hs
          have : q * (v / q) ≤ q * m := by linarith
          exact le_of_mul_le_mul_left this hq
        · have hspos : 0 < s := lt_of_le_of_ne hs0 (Ne.symm hs)
          have : q * (v / q) < q * m := by linarith
          have := lt_of_mul_lt_mul_left this hq.le
          omega
      · have := Int.emod_add_mul_ediv v q
        rw [hv] at this; exact this
    · rintro ⟨j, ⟨hj0, hj1⟩, rfl⟩
      refine ⟨⟨by nlinarith, ?_⟩, ?_⟩
      · rw [hM] at hj1
        split_ifs at hj1 with hs
        · subst hs; nlinarith
        · nlinarith
      · rw [Int.add_mul_emod_self_left]; exact Int.emod_eq_of_lt hs0 hsq
  rw [hset, card_image_of_injective _ (fun x y hxy => by
    exact mul_left_cancel₀ hq.ne' (by simpa using hxy)), Int.card_Icc, hM]
  split_ifs <;> omega

/-- **The lattice points of a tilted square, in index coordinates.**  If
`r u ≡ 0 (mod q)` exactly when `u ≡ 0 (mod q)`, the set
`{(u, v) ∈ [0, qm]² : v ≡ r u (mod q)}` has `q m² + 2m + 1` elements. -/
theorem card_T (q r : ℤ) (m : ℕ) (hq : 0 < q)
    (hr : ∀ u : ℤ, (r * u) % q = 0 ↔ u % q = 0) :
    ((Icc 0 (q * m) ×ˢ Icc 0 (q * m)).filter
      (fun w : ℤ × ℤ => w.2 % q = (r * w.1) % q)).card = q.toNat * m ^ 2 + 2 * m + 1 := by
  rw [card_filter, sum_product]
  have hinner : ∀ u ∈ Icc 0 (q * m), (∑ v ∈ Icc 0 (q * m),
      if v % q = (r * u) % q then 1 else 0) = m + if u % q = 0 then 1 else 0 := by
    intro u _
    rw [← card_filter, card_res q m _ hq (Int.emod_nonneg _ hq.ne') (Int.emod_lt_of_pos _ hq)]
    simp only [hr u]
  rw [sum_congr rfl hinner, sum_add_distrib, sum_const, ← card_filter,
    card_res q m 0 hq le_rfl hq, Int.card_Icc]
  simp only [ite_true, smul_eq_mul]
  have hq' : ((q * m + 1 - 0).toNat) = q.toNat * m + 1 := by
    have : (q * m + 1 - 0 : ℤ) = ((q.toNat * m + 1 : ℕ) : ℤ) := by
      push_cast; rw [Int.toNat_of_nonneg hq.le]; ring
    rw [this, Int.toNat_natCast]
  rw [hq']; ring

/-- **Unit square rotated by `arctan (3/4)`.**  At lattice spacing `1/(5m)`, the
rotated unit square (vertices `0, (4,3)/5, (1,7)/5, (-3,4)/5`) contains
`25 m² + 2m + 1` lattice points: an index `y` lies in it iff
`0 ≤ 4y₁ + 3y₂ ≤ 25m` and `0 ≤ -3y₁ + 4y₂ ≤ 25m`. -/
theorem rot_square_count (m : ℕ) :
    ((Icc (-(3 * m : ℤ)) (4 * m) ×ˢ Icc (0 : ℤ) (7 * m)).filter (fun y : ℤ × ℤ =>
      0 ≤ 4 * y.1 + 3 * y.2 ∧ 4 * y.1 + 3 * y.2 ≤ 25 * m ∧
      0 ≤ -3 * y.1 + 4 * y.2 ∧ -3 * y.1 + 4 * y.2 ≤ 25 * m)).card = 25 * m ^ 2 + 2 * m + 1 := by
  have hT := card_T 25 18 m (by norm_num) (fun u => by omega)
  rw [show (25 : ℤ).toNat = 25 from rfl] at hT
  rw [← hT]
  refine card_nbij' (fun y => (4 * y.1 + 3 * y.2, -3 * y.1 + 4 * y.2))
    (fun w => ((4 * w.1 - 3 * w.2) / 25, (3 * w.1 + 4 * w.2) / 25)) ?_ ?_ ?_ ?_
  · intro y hy
    simp only [coe_filter, Set.mem_ofPred_eq, mem_product, mem_Icc] at hy ⊢
    omega
  · intro w hw
    simp only [coe_filter, Set.mem_ofPred_eq, mem_product, mem_Icc] at hw ⊢
    omega
  · intro y hy
    simp only [coe_filter, Set.mem_ofPred_eq, mem_product, mem_Icc] at hy
    ext <;> simp only <;> omega
  · intro w hw
    simp only [coe_filter, Set.mem_ofPred_eq, mem_product, mem_Icc] at hw
    ext <;> simp only <;> omega

/-- The axis-parallel unit square at spacing `1/(5m)` contains `(5m+1)²` points. -/
theorem axis_square_count (m : ℕ) :
    (Icc (0 : ℤ) (5 * m) ×ˢ Icc (0 : ℤ) (5 * m)).card = (5 * m + 1) ^ 2 := by
  rw [card_product, Int.card_Icc]
  have : (5 * (m : ℤ) + 1 - 0).toNat = 5 * m + 1 := by omega
  rw [this]; ring

/-- **Unit square boosted with Doppler factor `2`.**  The boost
`(t, x) ↦ ((5t + 3x)/4, (3t + 5x)/4)` maps the unit square to the parallelogram with
vertices `0, (5,3)/4, (3,5)/4, (2,2)`.  At lattice spacing `1/(4m)` it contains
`16 m² + 2m + 1` lattice points: an index `y` lies in it iff
`0 ≤ 5y₁ - 3y₂ ≤ 16m` and `0 ≤ -3y₁ + 5y₂ ≤ 16m`. -/
theorem boost_square_count (m : ℕ) :
    ((Icc (0 : ℤ) (8 * m) ×ˢ Icc (0 : ℤ) (8 * m)).filter (fun y : ℤ × ℤ =>
      0 ≤ 5 * y.1 - 3 * y.2 ∧ 5 * y.1 - 3 * y.2 ≤ 16 * m ∧
      0 ≤ -3 * y.1 + 5 * y.2 ∧ -3 * y.1 + 5 * y.2 ≤ 16 * m)).card = 16 * m ^ 2 + 2 * m + 1 := by
  have hT := card_T 16 9 m (by norm_num) (fun u => by omega)
  rw [show (16 : ℤ).toNat = 16 from rfl] at hT
  rw [← hT]
  refine card_nbij' (fun y => (5 * y.1 - 3 * y.2, -3 * y.1 + 5 * y.2))
    (fun w => ((5 * w.1 + 3 * w.2) / 16, (3 * w.1 + 5 * w.2) / 16)) ?_ ?_ ?_ ?_
  · intro y hy
    simp only [coe_filter, Set.mem_ofPred_eq, mem_product, mem_Icc] at hy ⊢
    omega
  · intro w hw
    simp only [coe_filter, Set.mem_ofPred_eq, mem_product, mem_Icc] at hw ⊢
    omega
  · intro y hy
    simp only [coe_filter, Set.mem_ofPred_eq, mem_product, mem_Icc] at hy
    ext <;> simp only <;> omega
  · intro w hw
    simp only [coe_filter, Set.mem_ofPred_eq, mem_product, mem_Icc] at hw
    ext <;> simp only <;> omega

/-- The axis-parallel unit square at spacing `1/(4m)` contains `(4m+1)²` points. -/
theorem axis_square_count4 (m : ℕ) :
    (Icc (0 : ℤ) (4 * m) ×ˢ Icc (0 : ℤ) (4 * m)).card = (4 * m + 1) ^ 2 := by
  rw [card_product, Int.card_Icc]
  have : (4 * (m : ℤ) + 1 - 0).toNat = 4 * m + 1 := by omega
  rw [this]; ring

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-- **Rotation changes the content at order `ε`.**  With `2ε = 1/(5m)`, the
granular areas of the unit square and of its rotation by `arctan (3/4)` differ by
exactly `16ε/5`:
`(2ε)²(5m+1)² - (2ε)²(25m² + 2m + 1) = 16ε/5`. -/
theorem rot_square_content (ε : K) (m : ℕ) (hm : 1 ≤ m) (h : 2 * ε * (5 * m) = 1) :
    (2 * ε) ^ 2 * (((Icc (0 : ℤ) (5 * m) ×ˢ Icc (0 : ℤ) (5 * m)).card : ℕ) : K) -
      (2 * ε) ^ 2 * ((((Icc (-(3 * m : ℤ)) (4 * m) ×ˢ Icc (0 : ℤ) (7 * m)).filter
        (fun y : ℤ × ℤ => 0 ≤ 4 * y.1 + 3 * y.2 ∧ 4 * y.1 + 3 * y.2 ≤ 25 * m ∧
          0 ≤ -3 * y.1 + 4 * y.2 ∧ -3 * y.1 + 4 * y.2 ≤ 25 * m)).card : ℕ) : K) =
      16 / 5 * ε := by
  rw [axis_square_count, rot_square_count]
  push_cast
  have hm' : (m : K) ≠ 0 := by exact_mod_cast (show m ≠ 0 by omega)
  have hε : ε = 1 / (10 * m) := by field_simp; linarith
  rw [hε]; field_simp; ring

/-- **A boost changes the content at order `ε`.**  With `2ε = 1/(4m)`, the
granular areas of the unit square and of its image under the boost with Doppler
factor `2` differ by exactly `3ε`:
`(2ε)²(4m+1)² - (2ε)²(16m² + 2m + 1) = 3ε`. -/
theorem boost_square_content (ε : K) (m : ℕ) (hm : 1 ≤ m) (h : 2 * ε * (4 * m) = 1) :
    (2 * ε) ^ 2 * (((Icc (0 : ℤ) (4 * m) ×ˢ Icc (0 : ℤ) (4 * m)).card : ℕ) : K) -
      (2 * ε) ^ 2 * ((((Icc (0 : ℤ) (8 * m) ×ˢ Icc (0 : ℤ) (8 * m)).filter
        (fun y : ℤ × ℤ => 0 ≤ 5 * y.1 - 3 * y.2 ∧ 5 * y.1 - 3 * y.2 ≤ 16 * m ∧
          0 ≤ -3 * y.1 + 5 * y.2 ∧ -3 * y.1 + 5 * y.2 ≤ 16 * m)).card : ℕ) : K) =
      3 * ε := by
  rw [axis_square_count4, boost_square_count]
  push_cast
  have hm' : (m : K) ≠ 0 := by exact_mod_cast (show m ≠ 0 by omega)
  have hε : ε = 1 / (8 * m) := by field_simp; linarith
  rw [hε]; field_simp; ring

end Squares

/-! ## Part 3: boosts and the Lorentz no-go -/

section Boost
variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-- The boost of `1+1`-dimensional Minkowski space (`c = 1`, coordinates `(t, x)`)
with Doppler factor `l > 0`: `t' = ½(l + l⁻¹) t + ½(l - l⁻¹) x`,
`x' = ½(l - l⁻¹) t + ½(l + l⁻¹) x`.  For `l = e^φ` this is the boost of rapidity
`φ` (`boost_exp`). -/
def boost (l : K) (p : K × K) : K × K :=
  ((l + l⁻¹) / 2 * p.1 + (l - l⁻¹) / 2 * p.2, (l - l⁻¹) / 2 * p.1 + (l + l⁻¹) / 2 * p.2)

/-- In light-cone coordinates `u = t + x`, `v = t - x` a boost is `u ↦ l u`,
`v ↦ l⁻¹ v`. -/
theorem boost_lightcone (l : K) (p : K × K) :
    (boost l p).1 + (boost l p).2 = l * (p.1 + p.2) ∧
      (boost l p).1 - (boost l p).2 = l⁻¹ * (p.1 - p.2) := by
  unfold boost; constructor <;> ring

/-- Boosts preserve the Minkowski form `t² - x²`. -/
theorem boost_minkowski (l : K) (hl : l ≠ 0) (p : K × K) :
    (boost l p).1 ^ 2 - (boost l p).2 ^ 2 = p.1 ^ 2 - p.2 ^ 2 := by
  have h := boost_lightcone l p
  have e : (boost l p).1 ^ 2 - (boost l p).2 ^ 2 =
      ((boost l p).1 + (boost l p).2) * ((boost l p).1 - (boost l p).2) := by ring
  rw [e, h.1, h.2]
  field_simp
  ring

/-- Boosts form a one-parameter group: `B_l ∘ B_{l'} = B_{l l'}`, `B_1 = id`. -/
theorem boost_mul (l l' : K) (hl : l ≠ 0) (hl' : l' ≠ 0) (p : K × K) :
    boost l (boost l' p) = boost (l * l') p := by
  unfold boost
  ext <;> simp only <;> field_simp <;> ring

theorem boost_one (p : K × K) : boost 1 p = p := by
  unfold boost; ext <;> simp only <;> norm_num

/-- Iterates of a boost: `B_l^k = B_{l^k}`. -/
theorem boost_iterate (l : K) (hl : l ≠ 0) (k : ℕ) (p : K × K) :
    (boost l)^[k] p = boost (l ^ k) p := by
  induction k with
  | zero => simp [boost_one]
  | succ k ih =>
    rw [Function.iterate_succ_apply', ih, boost_mul l (l ^ k) hl (pow_ne_zero _ hl), pow_succ,
      mul_comm]

/-- Boosts of a nonzero point with distinct Doppler factors are distinct. -/
theorem boost_injective_param (l l' : K) (p : K × K)
    (hp : p ≠ 0) (h : boost l p = boost l' p) : l = l' := by
  have h1 := boost_lightcone l p
  have h2 := boost_lightcone l' p
  rw [h] at h1
  by_cases hu : p.1 + p.2 = 0
  · have hv : p.1 - p.2 ≠ 0 := by
      intro hv
      apply hp
      ext
      · show p.1 = 0; linarith
      · show p.2 = 0; linarith
    have : l⁻¹ = l'⁻¹ := mul_right_cancel₀ hv (h1.2.symm.trans h2.2)
    exact inv_injective this
  · exact mul_right_cancel₀ hu (h1.1.symm.trans h2.1)

/-- **No finite set is invariant under a boost (exact no-go).**  If a finite subset
`S` of `1+1`-dimensional Minkowski space over any ordered field is mapped into
itself by a single boost `B_l` with `l > 0`, `l ≠ 1`, then `S ⊆ {0}`. -/
theorem finite_boost_invariant (S : Set (K × K)) (hS : S.Finite) (l : K) (hl : 0 < l)
    (hl1 : l ≠ 1) (hinv : ∀ p ∈ S, boost l p ∈ S) : S ⊆ {0} := by
  intro p hp
  by_contra hp0
  have hp0' : p ≠ 0 := hp0
  have hmem : ∀ k : ℕ, boost (l ^ k) p ∈ S := by
    intro k
    rw [← boost_iterate l hl.ne' k p]
    induction k with
    | zero => simpa using hp
    | succ k ih => rw [Function.iterate_succ_apply']; exact hinv _ ih
  have hinj : Function.Injective (fun k : ℕ => boost (l ^ k) p) := by
    intro j k hjk
    have := boost_injective_param _ _ p hp0' hjk
    exact pow_right_injective₀ hl hl1 this
  exact (Set.infinite_range_of_injective hinj) (hS.subset (by
    rintro _ ⟨k, rfl⟩; exact hmem k))

/-- The boost in the plane of the time axis `0` and the space axis `j` of
`1+n`-dimensional Minkowski space (coordinates `Fin (n+1) → K`, time first). -/
def boostAt {n : ℕ} (j : Fin (n + 1)) (l : K) (p : Fin (n + 1) → K) : Fin (n + 1) → K :=
  fun i => if i = 0 then (boost l (p 0, p j)).1 else if i = j then (boost l (p 0, p j)).2
    else p i

lemma boostAt_proj {n : ℕ} (j : Fin (n + 1)) (hj : j ≠ 0) (l : K) (p : Fin (n + 1) → K) :
    (boostAt j l p 0, boostAt j l p j) = boost l (p 0, p j) := by
  unfold boostAt
  simp [hj]

lemma boostAt_iterate {n : ℕ} (j : Fin (n + 1)) (hj : j ≠ 0) (l : K) (hl : l ≠ 0) (k : ℕ)
    (p : Fin (n + 1) → K) :
    ((boostAt j l)^[k] p 0, (boostAt j l)^[k] p j) = boost (l ^ k) (p 0, p j) := by
  induction k with
  | zero => simp [boost_one]
  | succ k ih =>
    rw [Function.iterate_succ_apply', boostAt_proj j hj, ih,
      boost_mul l (l ^ k) hl (pow_ne_zero _ hl), pow_succ, mul_comm]

/-- **No-go in `1+n` dimensions.**  For `n ≥ 1`, a finite subset of
`1+n`-dimensional Minkowski space mapped into itself by the boosts `B^{(j)}_l` in all
coordinate planes `(t, xⱼ)`, for one Doppler factor `l > 0`, `l ≠ 1`, lies in `{0}`. -/
theorem finite_boostAt_invariant {n : ℕ} (hn : 1 ≤ n) (S : Set (Fin (n + 1) → K))
    (hS : S.Finite) (l : K) (hl : 0 < l) (hl1 : l ≠ 1)
    (hinv : ∀ j : Fin (n + 1), j ≠ 0 → ∀ p ∈ S, boostAt j l p ∈ S) : S ⊆ {0} := by
  intro p hp
  by_contra hp0
  have hp0' : p ≠ 0 := hp0
  -- a space axis `j` with `(p 0, p j) ≠ 0`
  obtain ⟨j, hj, hpj⟩ : ∃ j : Fin (n + 1), j ≠ 0 ∧ (p 0, p j) ≠ 0 := by
    by_cases h0 : p 0 = 0
    · obtain ⟨i, hi⟩ : ∃ i, p i ≠ 0 := by
        by_contra h; push Not at h; exact hp0' (funext h)
      have hi0 : i ≠ 0 := by rintro rfl; exact hi h0
      exact ⟨i, hi0, fun h => hi (congrArg Prod.snd h)⟩
    · refine ⟨⟨1, by omega⟩, ?_, fun h => h0 (congrArg Prod.fst h)⟩
      intro h; have := congrArg Fin.val h; simp at this
  have hmem : ∀ k : ℕ, (boostAt j l)^[k] p ∈ S := by
    intro k
    induction k with
    | zero => simpa using hp
    | succ k ih => rw [Function.iterate_succ_apply']; exact hinv j hj _ ih
  have hinj : Function.Injective (fun k : ℕ => (boostAt j l)^[k] p) := by
    intro a b hab
    have h1 := boostAt_iterate j hj l hl.ne' a p
    have h2 := boostAt_iterate j hj l hl.ne' b p
    simp only at hab
    rw [hab] at h1
    have := boost_injective_param _ _ _ hpj (h1.symm.trans h2)
    exact pow_right_injective₀ hl hl1 this
  exact (Set.infinite_range_of_injective hinj) (hS.subset (by
    rintro _ ⟨k, rfl⟩; exact hmem k))

/-- Boosted copies of a non-null line through the origin are pairwise distinct
lines: if `s B_l p = s' B_{l'} p ≠ 0` for a non-null `p` (`t² ≠ x²`) and Doppler
factors `l, l' > 0`, then `l = l'`. -/
theorem boost_lines_distinct (l l' s s' : K) (hl : 0 < l) (hl' : 0 < l') (p : K × K)
    (hp : p.1 ^ 2 ≠ p.2 ^ 2) (hs : s ≠ 0)
    (h : s • boost l p = s' • boost l' p) : l = l' := by
  have h1 := boost_lightcone l p
  have h2 := boost_lightcone l' p
  have hu : p.1 + p.2 ≠ 0 := by
    intro hu; apply hp; rw [show p.1 = -p.2 by linarith]; ring
  have hv : p.1 - p.2 ≠ 0 := by
    intro hv; apply hp; rw [show p.1 = p.2 by linarith]
  have e1 : s * ((boost l p).1 + (boost l p).2) = s' * ((boost l' p).1 + (boost l' p).2) := by
    have a := congrArg Prod.fst h; have b := congrArg Prod.snd h
    simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul] at a b; linarith
  have e2 : s * ((boost l p).1 - (boost l p).2) = s' * ((boost l' p).1 - (boost l' p).2) := by
    have a := congrArg Prod.fst h; have b := congrArg Prod.snd h
    simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul] at a b; linarith
  rw [h1.1, h2.1] at e1
  rw [h1.2, h2.2] at e2
  have e1' : s * l = s' * l' := mul_right_cancel₀ hu (by linarith)
  have e2' : s * l⁻¹ = s' * l'⁻¹ := mul_right_cancel₀ hv (by linarith)
  have e3 : s * l' = s' * l := by
    calc s * l' = (s * l⁻¹) * (l * l') := by field_simp
      _ = (s' * l'⁻¹) * (l * l') := by rw [e2']
      _ = s' * l := by field_simp
  have hsq : l ^ 2 = l' ^ 2 := by
    have : s * (l ^ 2 - l' ^ 2) = 0 := by linear_combination l * e1' - l' * e3
    have := (mul_eq_zero.mp this).resolve_left hs
    linarith
  exact (sq_eq_sq₀ hl.le hl'.le).mp hsq

open Classical in
/-- **Points on distinct boosted lines are distinct.**  For a finite set `Λ`, a
non-null `p` and a finite set `D` of Doppler factors `l > 0`, the nonzero points of
`Λ` on the lines `ℝ · B_l p` are disjoint across `l ∈ D`, so
`∑_{l ∈ D} #{x ∈ Λ : x ≠ 0, x ∈ K · B_l p} ≤ #Λ`. -/
theorem sum_boosted_lines_le (Λ : Finset (K × K)) (D : Finset K)
    (hD : ∀ l ∈ D, 0 < l) (p : K × K) (hp : p.1 ^ 2 ≠ p.2 ^ 2) :
    ∑ l ∈ D, (Λ.filter (fun x => x ≠ 0 ∧ ∃ s : K, x = s • boost l p)).card ≤ Λ.card := by
  classical
  rw [← card_biUnion]
  · exact card_le_card (biUnion_subset.mpr (fun l _ => filter_subset _ _))
  · intro l hl l' hl' hll'
    rw [Function.onFun, disjoint_filter]
    rintro x _ ⟨hx0, s, rfl⟩ ⟨_, s', hs'⟩
    have hs : s ≠ 0 := by rintro rfl; exact hx0 (by simp)
    exact hll' (boost_lines_distinct l l' s s' (hD l hl) (hD l' hl') p hp hs hs')

end Boost

section RealBoost
open Real

/-- For `l = e^φ` the boost is the boost of rapidity `φ`. -/
theorem boost_exp (φ : ℝ) (p : ℝ × ℝ) :
    boost (Real.exp φ) p = (cosh φ * p.1 + sinh φ * p.2, sinh φ * p.1 + cosh φ * p.2) := by
  unfold boost
  rw [Real.cosh_eq, Real.sinh_eq, Real.exp_neg]

/-- **Boost-invariant sets are not locally finite.**  If `S ⊆ ℝ²` is mapped into
itself by every boost `B_l`, `l ∈ [1, 2]`, and contains a point `p ≠ 0`, then some
compact set (the arc `{B_l p : l ∈ [1,2]}` of the hyperbola or light ray through
`p`) contains infinitely many points of `S`. -/
theorem not_locally_finite (S : Set (ℝ × ℝ))
    (hinv : ∀ l ∈ Set.Icc (1 : ℝ) 2, ∀ p ∈ S, boost l p ∈ S) (p : ℝ × ℝ) (hp : p ∈ S)
    (hp0 : p ≠ 0) : ∃ C : Set (ℝ × ℝ), IsCompact C ∧ (S ∩ C).Infinite := by
  refine ⟨(fun l => boost l p) '' Set.Icc 1 2, ?_, ?_⟩
  · refine isCompact_Icc.image_of_continuousOn ?_
    intro l hl
    have hl0 : l ≠ 0 := by have := hl.1; linarith
    unfold boost
    apply ContinuousAt.continuousWithinAt
    fun_prop (disch := exact hl0)
  · have hinj : Set.InjOn (fun l => boost l p) (Set.Icc 1 2) := by
      intro a ha b hb hab
      exact boost_injective_param a b p hp0 hab
    have himg : ((fun l => boost l p) '' Set.Icc (1 : ℝ) 2).Infinite :=
      (Set.Icc_infinite (by norm_num : (1 : ℝ) < 2)).image hinj
    have hsub : (fun l => boost l p) '' Set.Icc (1 : ℝ) 2 ⊆ S := by
      rintro _ ⟨l, hl, rfl⟩; exact hinv l hl p hp
    rwa [Set.inter_eq_right.mpr hsub]

/-- **Hyperfinite version of the no-go.**  A hyperfinite subset of the
nonstandard Minkowski plane `(ℝ × ℝ)*` that is mapped into itself by the extension
`*B_l` of one standard boost (`l > 0`, `l ≠ 1`) is contained in `{0}`. -/
theorem hyperfinite_boost_invariant (A : ℕ → Finset (ℝ × ℝ)) (l : ℝ) (hl : 0 < l)
    (hl1 : l ≠ 1)
    (hinv : ∀ u ∈ QE.NSA.hfin A, QE.NSA.starFun (boost l) u ∈ QE.NSA.hfin A) :
    QE.NSA.hfin A ⊆ {((0 : ℝ × ℝ) : QE.NSA.Ult (ℝ × ℝ))} := by
  -- eventually every `A n` is boost invariant
  have hev : ∀ᶠ n in (Filter.hyperfilter ℕ : Filter ℕ), ∀ p ∈ A n, boost l p ∈ A n := by
    by_contra hne
    have hbad : ∀ᶠ n in (Filter.hyperfilter ℕ : Filter ℕ), ∃ p ∈ A n, boost l p ∉ A n := by
      have := (Ultrafilter.eventually_not (f := Filter.hyperfilter ℕ)).mpr hne
      refine this.mono ?_
      intro n hn; push Not at hn; exact hn
    classical
    let w : ℕ → ℝ × ℝ := fun n =>
      if h : ∃ p ∈ A n, boost l p ∉ A n then h.choose else 0
    have hw : ∀ᶠ n in (Filter.hyperfilter ℕ : Filter ℕ), w n ∈ A n ∧ boost l (w n) ∉ A n := by
      refine hbad.mono ?_
      intro n hn
      simp only [w, hn, ↓reduceDIte]
      exact hn.choose_spec
    have hu : ((w : ℕ → ℝ × ℝ) : QE.NSA.Ult (ℝ × ℝ)) ∈ QE.NSA.hfin A := by
      unfold QE.NSA.hfin
      rw [QE.NSA.mem_internal]
      exact hw.mono (fun n hn => by simpa using hn.1)
    have h2 := hinv _ hu
    unfold QE.NSA.hfin QE.NSA.starFun at h2
    rw [QE.NSA.ifun_coe, QE.NSA.mem_internal] at h2
    obtain ⟨n, hn1, hn2⟩ := (hw.and h2).exists
    exact hn1.2 (by simpa using hn2)
  intro u hu
  obtain ⟨w, rfl⟩ := QE.NSA.exists_rep u
  unfold QE.NSA.hfin at hu
  rw [QE.NSA.mem_internal] at hu
  rw [Set.mem_singleton_iff]
  apply Filter.Germ.coe_eq.mpr
  filter_upwards [hu, hev] with n h1 h2
  have := finite_boost_invariant (A n : Set (ℝ × ℝ)) (A n).finite_toSet l hl hl1
    (fun p hp => by simpa using h2 p (by simpa using hp))
  exact this h1

/-- **Only countably many boosted lines meet a countable set.**  For a countable
`X ⊆ ℝ²` and a non-null `p`, the set of Doppler factors `l > 0` such that the
line `ℝ · B_l p` contains a nonzero point of `X` is countable. -/
theorem countable_boosted_lines (X : Set (ℝ × ℝ)) (hX : X.Countable) (p : ℝ × ℝ)
    (hp : p.1 ^ 2 ≠ p.2 ^ 2) :
    {l : ℝ | 0 < l ∧ ∃ x ∈ X, x ≠ 0 ∧ ∃ s : ℝ, x = s • boost l p}.Countable := by
  set S := {l : ℝ | 0 < l ∧ ∃ x ∈ X, x ≠ 0 ∧ ∃ s : ℝ, x = s • boost l p}
  have hc : Countable X := hX.to_subtype
  have hw : ∀ l : S, ∃ x : X, (x : ℝ × ℝ) ≠ 0 ∧ ∃ s : ℝ, (x : ℝ × ℝ) = s • boost (l : ℝ) p := by
    intro l
    obtain ⟨_, x, hx, hx0, hs⟩ := l.2
    exact ⟨⟨x, hx⟩, hx0, hs⟩
  choose f hf using hw
  have hinj : Function.Injective f := by
    intro l l' hll'
    obtain ⟨h0, s, hs⟩ := hf l
    obtain ⟨_, s', hs'⟩ := hf l'
    have hs0 : s ≠ 0 := by rintro rfl; exact h0 (by rw [hs]; simp)
    rw [hll'] at hs
    exact Subtype.ext (boost_lines_distinct (l : ℝ) l' s s' l.2.1 l'.2.1 p hp hs0
      (hs.symm.trans hs'))
  exact Set.countable_coe_iff.mp (hinj.countable)

/-- **Frame dependence in the ultrapower model.**  In `ℝ* = ℝ^ℕ/U`, for every
hyperfinite `Λ = [Λₙ] ⊆ (ℝ²)*` and every non-null `p`, the boosted line
`ℝ · B_l p` (minus the origin) meets `Λ` for at most countably many standard
`l > 0`.  So for all other standard `l` every segment `F ⊆ ℝ p` with `0 ∉ F` has
`μ_Λ(B_l F) = 0`. -/
theorem ultrapower_frame_dependence (A : ℕ → Finset (ℝ × ℝ)) (p : ℝ × ℝ)
    (hp : p.1 ^ 2 ≠ p.2 ^ 2) :
    {l : ℝ | 0 < l ∧ (QE.NSA.hfin A ∩
      QE.NSA.starSet {x : ℝ × ℝ | x ≠ 0 ∧ ∃ s : ℝ, x = s • boost l p}).Nonempty}.Countable := by
  refine (countable_boosted_lines (⋃ n, (A n : Set (ℝ × ℝ)))
    (Set.countable_iUnion (fun n => (A n).countable_toSet)) p hp).mono ?_
  rintro l ⟨hl, u, hu1, hu2⟩
  obtain ⟨w, rfl⟩ := QE.NSA.exists_rep u
  unfold QE.NSA.hfin at hu1
  rw [QE.NSA.mem_internal] at hu1
  rw [QE.NSA.mem_starSet] at hu2
  obtain ⟨n, h1, h2⟩ := (hu1.and hu2).exists
  exact ⟨hl, w n, Set.mem_iUnion.mpr ⟨n, h1⟩, h2.1, h2.2⟩

end RealBoost

end QE.OpenGeo
