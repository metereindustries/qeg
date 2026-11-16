-- SPDX-License-Identifier: MIT
-- Copyright 2026 Metere Industries, Inc. Author: Alfredo Metere.
-- Quasi-Euclidean Granular Geometry. Any derivative work must carry this notice:
--   This work is derivative of the Quasi-Euclidean Granular Geometry book
--   authored by Alfredo Metere. Copyright 2026 Metere Industries, Inc.
--   All rights reserved
-- See LICENSE.md and NOTICE.

import QuasiEuclidean.Ch15c_Computation

/-!
# Chapter 19: Granular Computational Complexity

The switchboard of 3-SAT read on a bounded granular lattice.

* **Three variables.** The switchboard is the NAND of its eight switches; the least
  circuit has exactly eight gates, seven of them two-input gates.
* **The lowest layer is not the triples.** Every minimally unsatisfiable set of clauses
  has normal-form coefficient `1`; for `n ≥ 4` there are cores of eight clauses spread over
  two triples, so the degree-eight monomials are not the `C(n,3)` triple cores.
* **Bounded horizon.** On the lattice `{-m,…,m}³` with `q` bits per cell, a switchboard
  that fits satisfies `4 (n-2)³ ≤ 3 q (2m+1)³`; one circuit decides every `n ≤ n_max` by
  padding; a deterministic map on a finite state space is eventually periodic (and periodic
  when it is a bijection), and need not be a bijection.
* **2-SAT inside the horizon; growth beyond it.** The same padding circuit decides 2-SAT;
  one constant bounds the least circuits of 2-SAT and 3-SAT on every `n ≤ n_max`; whether
  circuit sizes grow polynomially is unchanged by any finitely many values, and every finite
  table of sizes begins both a polynomially bounded function and one that is not.
* **General formulas.** A three-term AND or OR is two two-term ones, so formulas with
  two-term combinations express every CNF; the three-term carry is two exclusive two-term
  carries. In clause form, 2-CNF resolution closes in a polynomial universe with no trace.
* **The intrinsic difference.** Every relation on two variables, whatever combination of
  AND, OR, NOT defines it, is closed under majority, so every general 2-SAT instance is; the
  constraint `x₀ ∨ x₁ ∨ x₂` is not, and no general 2-SAT instance with extra variables has its
  solutions. Every program deciding a function accepts its solutions, so no circuit, of any
  size or fan-out, changes this.
* **Thresholds.** `2^398 < 10^120 < 2^399`; the first `n` with `8 C(n,3) > 10^80`;
  `8 C(399,3) = 84 059 192`.
* **Locality.** A cubic lattice box of radius `r` holds `(2r+1)³` cells, a path of `t` unit
  steps moves at most `t` in every coordinate, so `S` gates spread over a radius of at least
  `((S^{1/3}) - 1)/2` and a signal reaching `F` other cells needs `(2t+1)³ > F`.
-/

open Finset Function

namespace QE.Comp

section GranularComplexity

/-! ### Three variables -/

/-- On three variables every clause has all three variables. -/
theorem vars_three (c : Clause3 3) : c.vars = univ :=
  Finset.eq_univ_of_card c.vars (by rw [card_vars]; simp)

/-- **On three variables the switchboard is a NAND.** -/
theorem sat3B_three (e : Clause3 3 → Bool) : sat3B 3 e = !(decide (∀ c, e c = true)) := by
  classical
  by_cases h : ∀ c, e c = true
  · rw [decide_eq_true h]
    exact (Bool.not_eq_true _).mp fun ht => by
      obtain ⟨x, hx⟩ := (sat3B_iff _).mp ht
      obtain ⟨c, -, hc⟩ := exists_clause_of_card univ (by simp) x
      have := hx c hc; rw [h c] at this; exact absurd this (by decide)
  · push_neg at h
    obtain ⟨c, hc⟩ := h
    rw [decide_eq_false (fun hall => by rw [hall c] at hc; exact absurd hc (by decide))]
    refine (sat3B_iff _).mpr ⟨c.pt, fun d hd => ?_⟩
    have : d = c := Clause3.eq_of_blocks ((vars_three d).trans (vars_three c).symm) hd c.blocks_pt
    subst this; simpa using hc

/-- On three variables there are exactly eight clauses, one per falsifying assignment. -/
theorem card_clause3_three : Fintype.card (Clause3 3) = 8 := by
  classical
  have : Fintype.card (Clause3 3) = Fintype.card (Fin 3 → Bool) := by
    refine Fintype.card_congr (Equiv.ofBijective (fun c => c.pt) ⟨fun c d h => ?_, fun x => ?_⟩)
    · simp only at h
      have hd : d.blocks c.pt = true := by
        have := d.blocks_pt; rw [← h] at this; exact this
      exact (Clause3.eq_of_blocks ((vars_three d).trans (vars_three c).symm) hd c.blocks_pt).symm
    · obtain ⟨c, -, hc⟩ := exists_clause_of_card univ (by simp) x
      refine ⟨c, funext fun v => ?_⟩
      show c.pt v = x v
      rw [c.pt_of_mem (by simp [vars_three]), ← Clause3.blocks_lit hc (by simp [vars_three])]
  rw [this]; simp

/-- A program of `N` gates computing the NAND of `N ≥ 1` inputs: `N - 1` ANDs and one NOT. -/
theorem nand_prog {N : ℕ} (hN : 1 ≤ N) :
    ∃ P : List (Fin 3 × ℕ × ℕ), P.length = N ∧
      ComputesOn P (fun x : Fin N → Bool => !(decide (∀ j, x j = true))) Set.univ := by
  have chain : ∀ k, k + 1 ≤ N → ∃ P : List (Fin 3 × ℕ × ℕ), P.length = k ∧
      ComputesOn P (fun x : Fin N → Bool => decide (∀ j : Fin N, (j : ℕ) < k + 1 → x j = true))
        Set.univ := by
    intro k
    induction k with
    | zero =>
      intro hk
      refine ⟨[], rfl, computesOn_congr (fun x _ => ?_) (computesOn_input [] ⟨0, by omega⟩ _)⟩
      by_cases h0 : x ⟨0, by omega⟩ = true
      · rw [h0]; symm; simp only [decide_eq_true_eq]
        intro j hj; have : j = ⟨0, by omega⟩ := Fin.ext (by simp; omega); rw [this]; exact h0
      · simp only [Bool.not_eq_true] at h0
        rw [h0]; symm; simp only [decide_eq_false_iff_not, not_forall]
        exact ⟨⟨0, by omega⟩, by simp, by simp [h0]⟩
    | succ k ih =>
      intro hk
      obtain ⟨P, hP, hc⟩ := ih (by omega)
      obtain ⟨P', hl, -, hnew⟩ := extend_gate 0 hc (computesOn_input P ⟨k + 1, by omega⟩ _)
      refine ⟨P', by omega, computesOn_congr (fun x _ => ?_) hnew⟩
      simp only [opB]
      by_cases h : ∀ j : Fin N, (j : ℕ) < k + 1 → x j = true
      · by_cases hx : x ⟨k + 1, by omega⟩ = true
        · rw [decide_eq_true h, hx]; symm; simp only [decide_eq_true_eq, Bool.true_and]
          intro j hj
          rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | hj
          · exact h j hj
          · have : j = ⟨k + 1, by omega⟩ := Fin.ext hj; rw [this]; exact hx
        · simp only [Bool.not_eq_true] at hx
          rw [hx, Bool.and_false]; symm; simp only [decide_eq_false_iff_not, not_forall]
          exact ⟨⟨k + 1, by omega⟩, by simp, by simp [hx]⟩
      · rw [decide_eq_false h, Bool.false_and]; symm
        simp only [decide_eq_false_iff_not, not_forall] at h ⊢
        obtain ⟨j, hj, hx⟩ := h
        exact ⟨j, by omega, hx⟩
  obtain ⟨P, hP, hc⟩ := chain (N - 1) (by omega)
  obtain ⟨P', hl, -, hnew⟩ := extend_gate 2 hc hc
  refine ⟨P', by omega, computesOn_congr (fun x _ => ?_) hnew⟩
  simp only [opB]
  congr 1
  apply decide_eq_decide.mpr
  exact ⟨fun h j => h j (by have := j.2; omega), fun h j _ => h j⟩

/-- **On three variables the least circuit has exactly eight gates.** -/
theorem minCircuitSize_sat3_three : minCircuitSize (sat3Fin 3) Set.univ = 8 := by
  classical
  have hfun : sat3Fin 3 = fun y => !(decide (∀ j, y j = true)) := by
    funext y
    unfold sat3Fin
    rw [sat3B_three]
    congr 1
    apply decide_eq_decide.mpr
    exact ⟨fun h j => by simpa using h ((Fintype.equivFin (Clause3 3)).symm j), fun h c => h _⟩
  have hN : 1 ≤ Fintype.card (Clause3 3) := by rw [card_clause3_three]; norm_num
  obtain ⟨P, hP, hc⟩ := nand_prog hN
  apply le_antisymm
  · refine Nat.sInf_le ⟨P, ?_, by rw [hfun]; exact hc⟩
    rw [hP, card_clause3_three]
  · refine le_csInf ⟨_, P, rfl, by rw [hfun]; exact hc⟩ ?_
    rintro k ⟨Q, rfl, i, hi, hf⟩
    have := essential_nonmonotone_lower _ (sat3Fin_essential 3) ⟨fun _ => false, fun _ => true,
      fun _ => Bool.false_le _, by unfold sat3Fin; simp only [Function.comp_def]; exact sat3B_false,
      by unfold sat3Fin; simp only [Function.comp_def]; exact sat3B_true le_rfl⟩ Q
      ⟨i, hi, fun x => hf x (Set.mem_univ _)⟩
    rw [card_clause3_three] at this; exact this

/-- **Seven two-input gates are necessary and suffice on three variables.** Every circuit
for the switchboard on three variables has at least seven two-input gates, and the
eight-gate circuit has seven. -/
theorem sat3_three_bin (P : List (Fin 3 × ℕ × ℕ)) (hP : Computes P (sat3Fin 3)) :
    7 ≤ binCount P := by
  by_contra h
  push_neg at h
  exact no_compute_few (sat3Fin_essential 3) hP (by rw [card_clause3_three]; omega)

/-! ### The lowest layer: every minimal core, not only the triples -/

/-- The normal-form coefficient of a set of clauses: the parity of its satisfiable subsets. -/
noncomputable def anfC {n : ℕ} (S : Finset (Clause3 n)) : ZMod 2 :=
  ∑ T ∈ S.powerset, if sat3B n (fun c => decide (c ∈ T)) then 1 else 0

/-- **A minimal core has coefficient one.** If `S` is minimally unsatisfiable, all its proper
subsets are satisfiable, so its coefficient is `2^|S| - 1 ≡ 1`. -/
theorem anfC_minUnsat {n : ℕ} (S : Finset (Clause3 n)) (hS : MinUnsat fun c => decide (c ∈ S))
    (hne : S.Nonempty) : anfC S = 1 := by
  classical
  have hsub : ∀ T ∈ S.powerset, (if sat3B n (fun c => decide (c ∈ T)) then (1 : ZMod 2) else 0) =
      1 - if T = S then 1 else 0 := by
    intro T hT
    by_cases hTS : T = S
    · subst hTS
      rw [if_neg (fun h => hS.1 ((sat3B_iff _).mp h)), if_pos rfl]; decide
    · rw [if_neg hTS, sub_zero]
      obtain ⟨c, hcS, hcT⟩ : ∃ c ∈ S, c ∉ T := by
        by_contra hno; push_neg at hno
        exact hTS (Finset.Subset.antisymm (Finset.mem_powerset.mp hT) hno)
      rw [if_pos ((sat3B_iff _).mpr (satC_mono (fun d hd => ?_) (hS.2 c (by simpa using hcS))))]
      by_cases hdc : d = c
      · subst hdc; simp [hcT] at hd
      · rw [Function.update_of_ne hdc]
        simp only [decide_eq_true_eq] at hd ⊢
        exact Finset.mem_powerset.mp hT hd
  rw [anfC, Finset.sum_congr rfl hsub, Finset.sum_sub_distrib, Finset.sum_ite_eq' S.powerset S,
    if_pos (Finset.mem_powerset_self S)]
  simp only [Finset.sum_const, Finset.card_powerset, nsmul_eq_mul, mul_one]
  have h2 : ((2 ^ S.card : ℕ) : ZMod 2) = 0 := by
    rw [Nat.cast_pow, show ((2 : ℕ) : ZMod 2) = 0 from rfl]
    exact zero_pow (Finset.card_pos.mpr hne).ne'
  rw [h2]; decide

/-- The clause on the variables `0 < 1 < k` (`k = 2` or `3`) with pattern `(β, u, w)`. -/
def clauseOn {n : ℕ} (hn : 4 ≤ n) (k : ℕ) (hk : 2 ≤ k ∧ k ≤ 3) (β u w : Bool) : Clause3 n :=
  ⟨⟨0, by omega⟩, ⟨1, by omega⟩, ⟨k, by omega⟩, by simp [Fin.lt_def], by simp [Fin.lt_def]; omega,
    β, u, w⟩

/-- The glued core: the four clauses on `{0,1,2}` forbidding `x₀ = 0` and the four clauses on
`{0,1,3}` forbidding `x₀ = 1`. -/
noncomputable def gluedCore {n : ℕ} (hn : 4 ≤ n) : Finset (Clause3 n) :=
  ((univ : Finset (Bool × Bool)).image fun p => clauseOn hn 2 (by omega) false p.1 p.2) ∪
    ((univ : Finset (Bool × Bool)).image fun p => clauseOn hn 3 (by omega) true p.1 p.2)

theorem clauseOn_blocks {n : ℕ} (hn : 4 ≤ n) (k : ℕ) (hk : 2 ≤ k ∧ k ≤ 3) (β u w : Bool)
    (x : Fin n → Bool) : (clauseOn hn k hk β u w).blocks x = true ↔
      x ⟨0, by omega⟩ = β ∧ x ⟨1, by omega⟩ = u ∧ x ⟨k, by omega⟩ = w :=
  Clause3.blocks_iff _ _

theorem gluedCore_card {n : ℕ} (hn : 4 ≤ n) : (gluedCore hn).card = 8 := by
  classical
  unfold gluedCore
  rw [Finset.card_union_of_disjoint, Finset.card_image_of_injective, Finset.card_image_of_injective]
  · simp
  · intro p q h; simp only [clauseOn, Clause3.mk.injEq] at h; exact Prod.ext h.2.2.2.2.1 h.2.2.2.2.2
  · intro p q h; simp only [clauseOn, Clause3.mk.injEq] at h; exact Prod.ext h.2.2.2.2.1 h.2.2.2.2.2
  · rw [Finset.disjoint_left]
    intro c h1 h2
    obtain ⟨p, -, rfl⟩ := Finset.mem_image.mp h1
    obtain ⟨q, -, h⟩ := Finset.mem_image.mp h2
    simp only [clauseOn, Clause3.mk.injEq] at h
    exact absurd h.2.2.2.1 (by decide)

/-- **The glued core is minimally unsatisfiable.** -/
theorem gluedCore_minUnsat {n : ℕ} (hn : 4 ≤ n) : MinUnsat fun c => decide (c ∈ gluedCore hn) := by
  classical
  have mem1 : ∀ u w, clauseOn hn 2 (by omega) false u w ∈ gluedCore hn := fun u w =>
    Finset.mem_union_left _ (Finset.mem_image.mpr ⟨(u, w), mem_univ _, rfl⟩)
  have mem2 : ∀ u w, clauseOn hn 3 (by omega) true u w ∈ gluedCore hn := fun u w =>
    Finset.mem_union_right _ (Finset.mem_image.mpr ⟨(u, w), mem_univ _, rfl⟩)
  refine ⟨fun ⟨x, hx⟩ => ?_, fun c hc => ?_⟩
  · cases h0 : x ⟨0, by omega⟩
    · have := hx _ ((clauseOn_blocks hn 2 ⟨le_rfl, by omega⟩ false (x ⟨1, by omega⟩) (x ⟨2, by omega⟩) x).mpr
        ⟨h0, rfl, rfl⟩)
      simp [mem1] at this
    · have := hx _ ((clauseOn_blocks hn 3 ⟨by omega, le_rfl⟩ true (x ⟨1, by omega⟩) (x ⟨3, by omega⟩) x).mpr
        ⟨h0, rfl, rfl⟩)
      simp [mem2] at this
  · refine ⟨c.pt, fun d hd => ?_⟩
    by_cases hdc : d = c
    · subst hdc; simp
    rw [Function.update_of_ne hdc]
    simp only [decide_eq_false_iff_not]
    intro hdK
    simp only [decide_eq_true_eq] at hc
    apply hdc
    unfold gluedCore at hc hdK
    rcases Finset.mem_union.mp hc with hc | hc <;> rcases Finset.mem_union.mp hdK with hd' | hd' <;>
      obtain ⟨p, -, rfl⟩ := Finset.mem_image.mp hc <;> obtain ⟨q, -, rfl⟩ := Finset.mem_image.mp hd'
    · exact Clause3.eq_of_blocks (by simp [Clause3.vars, clauseOn]) hd (Clause3.blocks_pt _)
    · have h0 := Clause3.blocks_lit hd (a := ⟨0, by omega⟩) (by simp [Clause3.vars, clauseOn])
      rw [Clause3.pt_of_mem _ (by simp [Clause3.vars, clauseOn])] at h0
      simp [Clause3.lit, clauseOn] at h0
    · have h0 := Clause3.blocks_lit hd (a := ⟨0, by omega⟩) (by simp [Clause3.vars, clauseOn])
      rw [Clause3.pt_of_mem _ (by simp [Clause3.vars, clauseOn])] at h0
      simp [Clause3.lit, clauseOn] at h0
    · exact Clause3.eq_of_blocks (by simp [Clause3.vars, clauseOn]) hd (Clause3.blocks_pt _)

/-- **The degree-eight monomials are not only the triple cores.** For `n ≥ 4` the glued core
has eight clauses, normal-form coefficient `1`, and clauses on two different triples. -/
theorem lowest_layer_not_triples {n : ℕ} (hn : 4 ≤ n) :
    (gluedCore hn).card = 8 ∧ anfC (gluedCore hn) = 1 ∧
      ∃ c ∈ gluedCore hn, ∃ d ∈ gluedCore hn, c.vars ≠ d.vars := by
  refine ⟨gluedCore_card hn, anfC_minUnsat _ (gluedCore_minUnsat hn)
    (Finset.card_pos.mp (by rw [gluedCore_card]; norm_num)),
    clauseOn hn 2 (by omega) false false false,
    Finset.mem_union_left _ (Finset.mem_image.mpr ⟨(false, false), mem_univ _, rfl⟩),
    clauseOn hn 3 (by omega) true false false,
    Finset.mem_union_right _ (Finset.mem_image.mpr ⟨(false, false), mem_univ _, rfl⟩), ?_⟩
  intro h
  have : (⟨2, by omega⟩ : Fin n) ∈ (clauseOn hn 3 (by omega) true false false).vars := by
    rw [← h]; simp [Clause3.vars, clauseOn]
  simp [Clause3.vars, clauseOn, Fin.ext_iff] at this

/-! ### The bounded granular horizon -/

/-- The lattice of a horizon of `m` cells per half-axis: `{-m,…,m}³` (the points `2kr` with
`|2k_i r| ≤ Ω` when `m = ⌊Ω/h⌋`). -/
def latBox (m : ℕ) : Finset (Fin 3 → ℤ) := Fintype.piFinset fun _ => Finset.Icc (-(m : ℤ)) m

theorem card_latBox (m : ℕ) : (latBox m).card = (2 * m + 1) ^ 3 := by
  simp only [latBox, Fintype.card_piFinset, Int.card_Icc, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin]
  congr 1; omega

/-- The granular measure of a finite set of cells of diameter `h`: `h³ · card`. -/
noncomputable def mugr {α : Type*} (h : ℝ) (A : Finset α) : ℝ := h ^ 3 * A.card

/-- **The granular measure is faithful.** -/
theorem mugr_eq_zero_iff {α : Type*} {h : ℝ} (hh : 0 < h) (A : Finset α) :
    mugr h A = 0 ↔ A = ∅ := by
  unfold mugr
  rw [mul_eq_zero, Nat.cast_eq_zero, Finset.card_eq_zero]
  exact ⟨fun H => H.resolve_left (pow_pos hh 3).ne', Or.inr⟩

/-- **A nonempty set carries at least one quantum of content.** -/
theorem mugr_ge {α : Type*} {h : ℝ} (hh : 0 < h) {A : Finset α} (hA : A.Nonempty) :
    h ^ 3 ≤ mugr h A := by
  unfold mugr
  have : (1 : ℝ) ≤ A.card := by exact_mod_cast Finset.card_pos.mpr hA
  nlinarith [pow_pos hh 3]

theorem mugr_mono {α : Type*} {h : ℝ} (hh : 0 < h) {A B : Finset α} (hAB : A ⊆ B) :
    mugr h A ≤ mugr h B := by
  unfold mugr
  exact mul_le_mul_of_nonneg_left (by exact_mod_cast Finset.card_le_card hAB) (pow_pos hh 3).le

/-- **No doubling.** A finite set as large as twice itself is empty. -/
theorem no_doubling {α : Type*} (A : Finset α) (h : A.card = 2 * A.card) : A = ∅ :=
  Finset.card_eq_zero.mp (by omega)

/-- **Storage fits the horizon.** If the `N` switch bits are stored injectively in `K` cells of
`q` bits each, then `N ≤ q K`. -/
theorem horizon_capacity {N K q : ℕ} (f : Fin N → Fin K × Fin q) (hf : Injective f) :
    N ≤ q * K := by
  have := Fintype.card_le_of_injective f hf
  simp only [Fintype.card_fin, Fintype.card_prod] at this
  linarith [mul_comm K q]

theorem six_choose_three (n : ℕ) : 6 * n.choose 3 = n * (n - 1) * (n - 2) := by
  have h := Nat.descFactorial_eq_factorial_mul_choose n 3
  simp only [Nat.descFactorial_succ, Nat.descFactorial_zero, Nat.factorial] at h
  norm_num at h
  linarith [h]

/-- **A switchboard that fits bounds the number of variables.** If `8 C(n,3) ≤ q K` then
`4 (n-2)³ ≤ 3 q K`, i.e. `n ≤ (3qK/4)^{1/3} + 2`. -/
theorem horizon_n_bound {n q K : ℕ} (h : 8 * n.choose 3 ≤ q * K) : 4 * (n - 2) ^ 3 ≤ 3 * (q * K) := by
  have h6 := six_choose_three n
  have hc : (n - 2) ^ 3 ≤ n * (n - 1) * (n - 2) := by
    rw [pow_three]
    have h1 : n - 2 ≤ n := Nat.sub_le n 2
    have h2 : n - 2 ≤ n - 1 := by omega
    calc (n - 2) * ((n - 2) * (n - 2)) ≤ n * ((n - 1) * (n - 2)) :=
          Nat.mul_le_mul h1 (Nat.mul_le_mul h2 le_rfl)
      _ = n * (n - 1) * (n - 2) := by ring
  nlinarith

/-- **The horizon in numbers.** On the lattice `{-m,…,m}³` with `q` bits per cell, a switchboard
stored there satisfies `4 (n-2)³ ≤ 3 q (2m+1)³`. -/
theorem horizon_lattice_bound {n q m : ℕ}
    (f : Fin (8 * n.choose 3) → latBox m × Fin q) (hf : Injective f) :
    4 * (n - 2) ^ 3 ≤ 3 * (q * (2 * m + 1) ^ 3) := by
  have := Fintype.card_le_of_injective f hf
  simp only [Fintype.card_fin, Fintype.card_prod, Fintype.card_coe, card_latBox] at this
  exact horizon_n_bound (by linarith [mul_comm ((2 * m + 1) ^ 3) q])

/-- **One circuit for every `n ≤ n_max`.** A single program decides the switchboard on `n_max`
variables, with at most `N + 1 + 2^N N` gates (`N = 8 C(n_max,3)`), and on the zero-padded
switchboard of every `m ≤ n_max` it returns the answer for `m`. -/
theorem one_circuit {nmax : ℕ} (hn : 3 ≤ nmax) :
    ∃ P : List (Fin 3 × ℕ × ℕ), ∃ i,
      P.length ≤ Fintype.card (Clause3 nmax) + 1 +
        2 ^ Fintype.card (Clause3 nmax) * Fintype.card (Clause3 nmax) ∧
      ∀ m (hm : m ≤ nmax) (e : Clause3 m → Bool),
        (wires (liftSB false hm e ∘ (Fintype.equivFin (Clause3 nmax)).symm) P).getD i false =
          sat3B m e := by
  classical
  obtain ⟨P, hP, i, -, hi⟩ := lookup_exists (clause3_nonempty hn) (sat3Fin nmax) Finset.univ
  refine ⟨P, i, by simpa using hP, fun m hm e => ?_⟩
  rw [hi _ (by simp)]
  unfold sat3Fin sat3B
  have : (liftSB false hm e ∘ (Fintype.equivFin (Clause3 nmax)).symm) ∘
      Fintype.equivFin (Clause3 nmax) = liftSB false hm e := by funext c; simp
  rw [this]
  exact decide_eq_decide.mpr (lift_sat_iff false (· = false) rfl hm e)

/-! ### Dynamics on a finite state space -/

/-- **Every orbit repeats within `card` steps.** -/
theorem orbit_repeats {α : Type*} [Fintype α] (f : α → α) (x : α) :
    ∃ i j, i < j ∧ j ≤ Fintype.card α ∧ f^[i] x = f^[j] x := by
  obtain ⟨a, b, hab, h⟩ := Fintype.exists_ne_map_eq_of_card_lt
    (fun k : Fin (Fintype.card α + 1) => f^[k] x) (by simp)
  rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hab) with hlt | hlt
  · exact ⟨a, b, hlt, by omega, h⟩
  · exact ⟨b, a, hlt, by omega, h.symm⟩

/-- **Every point of an orbit already occurs within the first `card` steps.** -/
theorem orbit_reduce {α : Type*} [Fintype α] (f : α → α) (x : α) :
    ∀ k, ∃ k' ≤ Fintype.card α, f^[k'] x = f^[k] x := by
  obtain ⟨i, j, hij, hj, hfij⟩ := orbit_repeats f x
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    by_cases hk : k ≤ Fintype.card α
    · exact ⟨k, hk, rfl⟩
    · obtain ⟨k', hk', h⟩ := ih (k - j + i) (by omega)
      refine ⟨k', hk', h.trans ?_⟩
      rw [Function.iterate_add_apply, hfij, ← Function.iterate_add_apply,
        show k - j + j = k by omega]

/-- **Reachability is decided within `card` steps.** A state space of `M` states reaches a set
`H` from `x` exactly when it does so within `M` steps: halting of a finite system is decidable
by running it `M` steps. -/
theorem reach_iff_bounded {α : Type*} [Fintype α] (f : α → α) (x : α) (H : Set α) :
    (∃ k, f^[k] x ∈ H) ↔ ∃ k ≤ Fintype.card α, f^[k] x ∈ H := by
  constructor
  · rintro ⟨k, hk⟩
    obtain ⟨k', hk', h⟩ := orbit_reduce f x k
    exact ⟨k', hk', h ▸ hk⟩
  · rintro ⟨k, -, hk⟩; exact ⟨k, hk⟩

/-- **A bijection of a finite set is periodic at every point.** -/
theorem bijective_periodic {α : Type*} [Fintype α] {f : α → α} (hf : Bijective f) (x : α) :
    ∃ p, 0 < p ∧ p ≤ Fintype.card α ∧ f^[p] x = x := by
  obtain ⟨i, j, hij, hj, h⟩ := orbit_repeats f x
  refine ⟨j - i, by omega, by omega, ?_⟩
  apply (hf.1.iterate i)
  rw [← Function.iterate_add_apply, show i + (j - i) = j by omega]
  exact h.symm

/-- **A deterministic map need not be a bijection.** -/
theorem deterministic_not_bijective : ∃ f : Bool → Bool, ¬ Bijective f := by
  refine ⟨fun _ => false, fun h => ?_⟩
  have := h.1 (a₁ := true) (a₂ := false) rfl
  exact absurd this (by decide)

/-! ### Thresholds -/

theorem three_mul_switchboard (n : ℕ) : 3 * (8 * n.choose 3) = 4 * (n * (n - 1) * (n - 2)) := by
  have := six_choose_three n; omega

/-- **The operation wall.** `2^398 < 10^120 < 2^399`. -/
theorem lloyd_wall : (2 : ℕ) ^ 398 < 10 ^ 120 ∧ (10 : ℕ) ^ 120 < 2 ^ 399 := by
  constructor <;> decide

/-- The switchboard on `399` variables has `84 059 192` switches. -/
theorem switchboard_399 : 8 * Nat.choose 399 3 = 84059192 := by
  have := three_mul_switchboard 399; norm_num at this; omega

/-- **The storage wall.** `n₀ = 421 716 332 650 874 621 422 854 877` is the least `n` with
`8 C(n,3) > 10^80`. -/
theorem baryon_wall :
    10 ^ 80 < 8 * Nat.choose 421716332650874621422854877 3 ∧
      8 * Nat.choose 421716332650874621422854876 3 ≤ 10 ^ 80 := by
  have h1 := three_mul_switchboard 421716332650874621422854877
  have h2 := three_mul_switchboard 421716332650874621422854876
  norm_num at h1 h2
  omega

theorem switchboard_mono {m n : ℕ} (h : m ≤ n) : 8 * m.choose 3 ≤ 8 * n.choose 3 :=
  Nat.mul_le_mul_left 8 (Nat.choose_le_choose 3 h)

/-- The switchboard of `10^80` variables has about `1.333 × 10^240` switches. -/
theorem switchboard_baryon :
    1333 * 10 ^ 237 ≤ 8 * Nat.choose (10 ^ 80) 3 ∧ 8 * Nat.choose (10 ^ 80) 3 ≤ 1334 * 10 ^ 237 := by
  have h := three_mul_switchboard (10 ^ 80)
  generalize Nat.choose (10 ^ 80) 3 = C at h ⊢
  norm_num at h
  omega

/-! ### Locality on the cubic lattice -/

/-- **A box of radius `r` holds `(2r+1)³` cells.** -/
theorem card_near_le (p : Fin 3 → ℤ) (r : ℕ) (G : Finset (Fin 3 → ℤ))
    (hG : ∀ g ∈ G, ∀ i, |g i - p i| ≤ r) : G.card ≤ (2 * r + 1) ^ 3 := by
  classical
  have hsub : G ⊆ Fintype.piFinset fun i => Finset.Icc (p i - r) (p i + r) := by
    intro g hg
    rw [Fintype.mem_piFinset]
    intro i
    have := abs_le.mp (hG g hg i)
    rw [Finset.mem_Icc]; constructor <;> linarith [this.1, this.2]
  refine (Finset.card_le_card hsub).trans (le_of_eq ?_)
  simp only [Fintype.card_piFinset, Int.card_Icc]
  rw [Finset.prod_congr rfl (fun x _ => (show (p x + (r : ℤ) + 1 - (p x - r)).toNat = 2 * r + 1 by
    omega))]
  simp

/-- **`S` gates spread out.** If `(2r+1)³ < S`, then for every cell `p` some gate lies more than
`r` steps away from `p` in some coordinate. -/
theorem gates_spread (p : Fin 3 → ℤ) (r : ℕ) (G : Finset (Fin 3 → ℤ))
    (hS : (2 * r + 1) ^ 3 < G.card) : ∃ g ∈ G, ∃ i, (r : ℤ) < |g i - p i| := by
  by_contra h
  push_neg at h
  exact absurd (card_near_le p r G h) (by omega)

/-- One step on the cubic lattice: to one of the six face neighbours. -/
def IsStep (a b : Fin 3 → ℤ) : Prop := ∑ i, |a i - b i| = 1

theorem step_coord {a b : Fin 3 → ℤ} (h : IsStep a b) (i : Fin 3) : |b i - a i| ≤ 1 := by
  rw [abs_sub_comm]
  unfold IsStep at h
  rw [← h]
  exact Finset.single_le_sum (f := fun i => |a i - b i|) (fun _ _ => abs_nonneg _) (mem_univ i)

/-- **A signal moves one cell per tick.** After `t` steps every coordinate has moved at most
`t`. -/
theorem path_coord (γ : ℕ → Fin 3 → ℤ) (t : ℕ) (h : ∀ k < t, IsStep (γ k) (γ (k + 1)))
    (i : Fin 3) : |γ t i - γ 0 i| ≤ t := by
  induction t with
  | zero => simp
  | succ t ih =>
    have h1 := ih (fun k hk => h k (by omega))
    have h2 := step_coord (h t (by omega)) i
    calc |γ (t + 1) i - γ 0 i| = |(γ (t + 1) i - γ t i) + (γ t i - γ 0 i)| := by ring_nf
      _ ≤ |γ (t + 1) i - γ t i| + |γ t i - γ 0 i| := abs_add_le _ _
      _ ≤ 1 + t := by linarith
      _ = ((t + 1 : ℕ) : ℤ) := by push_cast; ring

/-- **Latency of a circuit.** If a source at `p` must reach every one of `S > (2r+1)³` gates
along lattice paths, some path takes more than `r` ticks. -/
theorem latency_floor (p : Fin 3 → ℤ) (r : ℕ) (G : Finset (Fin 3 → ℤ))
    (hS : (2 * r + 1) ^ 3 < G.card)
    (reach : ∀ g ∈ G, ∃ t, ∃ γ : ℕ → Fin 3 → ℤ, γ 0 = p ∧ γ t = g ∧ ∀ k < t, IsStep (γ k) (γ (k + 1))) :
    ∃ g ∈ G, ∀ t, ∀ γ : ℕ → Fin 3 → ℤ, γ 0 = p → γ t = g →
      (∀ k < t, IsStep (γ k) (γ (k + 1))) → r < t := by
  obtain ⟨g, hg, i, hi⟩ := gates_spread p r G hS
  refine ⟨g, hg, fun t γ h0 ht hγ => ?_⟩
  have := path_coord γ t hγ i
  rw [h0, ht] at this
  have : (r : ℤ) < t := lt_of_lt_of_le hi this
  exact_mod_cast this

/-- **Fan-out in `t` ticks.** A signal delivered within `t` steps to `F` distinct cells other
than its source has `F + 1 ≤ (2t+1)³`. -/
theorem fanout_ticks (p : Fin 3 → ℤ) (t : ℕ) (T : Finset (Fin 3 → ℤ)) (hp : p ∉ T)
    (hT : ∀ g ∈ T, ∀ i, |g i - p i| ≤ t) : T.card + 1 ≤ (2 * t + 1) ^ 3 := by
  classical
  have := card_near_le p t (insert p T) (by
    intro g hg i
    rcases Finset.mem_insert.mp hg with rfl | hg
    · simp
    · exact hT g hg i)
  rwa [Finset.card_insert_of_notMem hp] at this

/-- **Six cells are one tick away.** The six face neighbours of the origin are distinct and each
is one step away, so a fan-out of six needs no repeater. -/
theorem six_neighbours :
    let nb : Finset (Fin 3 → ℤ) := {![1, 0, 0], ![-1, 0, 0], ![0, 1, 0], ![0, -1, 0], ![0, 0, 1],
      ![0, 0, -1]}
    nb.card = 6 ∧ ∀ b ∈ nb, IsStep 0 b := by
  refine ⟨by decide, ?_⟩
  intro b hb
  simp only [Finset.mem_insert, Finset.mem_singleton] at hb
  rcases hb with rfl | rfl | rfl | rfl | rfl | rfl <;> simp [IsStep, Fin.sum_univ_three]

/-! ### 2-SAT inside the horizon -/

/-- A 2-clause on `n` variables: indices `i < j` and the falsifying pattern. -/
structure Clause2 (n : ℕ) where
  i : Fin n
  j : Fin n
  hij : i < j
  bi : Bool
  bj : Bool
  deriving DecidableEq

/-- `c.blocks x`: the assignment `x` falsifies the 2-clause `c`. -/
def Clause2.blocks {n : ℕ} (c : Clause2 n) (x : Fin n → Bool) : Bool :=
  (x c.i == c.bi) && (x c.j == c.bj)

def Clause2.toTuple {n : ℕ} (c : Clause2 n) : (Fin n × Fin n) × Bool × Bool :=
  ((c.i, c.j), c.bi, c.bj)

theorem Clause2.toTuple_injective {n : ℕ} : Injective (Clause2.toTuple (n := n)) := by
  rintro ⟨_, _, _, _, _⟩ ⟨_, _, _, _, _⟩ h
  simp only [Clause2.toTuple, Prod.mk.injEq] at h
  obtain ⟨⟨rfl, rfl⟩, rfl, rfl⟩ := h
  rfl

noncomputable instance {n : ℕ} : Fintype (Clause2 n) :=
  Fintype.ofInjective _ Clause2.toTuple_injective

/-- The 2-SAT switchboard decision function. -/
noncomputable def sat2B (n : ℕ) (e : Clause2 n → Bool) : Bool :=
  decide (∃ x : Fin n → Bool, ∀ c, c.blocks x = true → e c = false)

/-- The 2-SAT switchboard on `Fin N` inputs, through a fixed numbering of the clauses. -/
noncomputable def sat2Fin (n : ℕ) (y : Fin (Fintype.card (Clause2 n)) → Bool) : Bool :=
  sat2B n (y ∘ Fintype.equivFin (Clause2 n))

theorem clause2_nonempty {m : ℕ} (hm : 2 ≤ m) : 0 < Fintype.card (Clause2 m) :=
  Fintype.card_pos_iff.mpr ⟨Clause2.mk ⟨0, by omega⟩ ⟨1, by omega⟩
    (by simp [Fin.lt_def]) false false⟩

/-- Embedding of a 2-clause on `m` variables into `n ≥ m` variables. -/
def embedClause2 {m n : ℕ} (hmn : m ≤ n) (c : Clause2 m) : Clause2 n where
  i := Fin.castLE hmn c.i
  j := Fin.castLE hmn c.j
  hij := Fin.lt_def.mpr (Fin.lt_def.mp c.hij)
  bi := c.bi
  bj := c.bj

theorem embedClause2_injective {m n : ℕ} (hmn : m ≤ n) : Injective (embedClause2 hmn) := by
  rintro ⟨_, _, _, _, _⟩ ⟨_, _, _, _, _⟩ h
  simp only [embedClause2, Clause2.mk.injEq, Fin.castLE_inj] at h
  obtain ⟨rfl, rfl, rfl, rfl⟩ := h
  rfl

/-- Zero-padded lift of a 2-SAT switchboard. -/
noncomputable def liftSB2 {m n : ℕ} (hmn : m ≤ n) (e : Clause2 m → Bool) (c : Clause2 n) :
    Bool :=
  if h : ∃ c₀, embedClause2 hmn c₀ = c then e h.choose else false

theorem liftSB2_embed {m n : ℕ} (hmn : m ≤ n) (e : Clause2 m → Bool) (c₀ : Clause2 m) :
    liftSB2 hmn e (embedClause2 hmn c₀) = e c₀ := by
  have hex : ∃ c₁, embedClause2 hmn c₁ = embedClause2 hmn c₀ := ⟨c₀, rfl⟩
  unfold liftSB2
  rw [dif_pos hex, embedClause2_injective hmn hex.choose_spec]

theorem blocks_embed2 {m n : ℕ} (hmn : m ≤ n) (c : Clause2 m) (x : Fin n → Bool) :
    (embedClause2 hmn c).blocks x = c.blocks (fun t => x (Fin.castLE hmn t)) := rfl

/-- **Padding preserves 2-SAT.** -/
theorem lift2_sat_iff {m n : ℕ} (hmn : m ≤ n) (e : Clause2 m → Bool) :
    sat2B n (liftSB2 hmn e) = sat2B m e := by
  unfold sat2B
  refine decide_eq_decide.mpr ⟨?_, ?_⟩
  · rintro ⟨x, hx⟩
    refine ⟨fun t => x (Fin.castLE hmn t), fun c hc => ?_⟩
    have := hx (embedClause2 hmn c) (by rw [blocks_embed2]; exact hc)
    rwa [liftSB2_embed] at this
  · rintro ⟨y, hy⟩
    refine ⟨fun t => if h : (t : ℕ) < m then y ⟨t, h⟩ else false, fun c hc => ?_⟩
    unfold liftSB2
    split_ifs with h
    · apply hy
      have hc' := h.choose_spec ▸ hc
      rw [blocks_embed2] at hc'
      convert hc' using 2
      funext t
      simp [t.2]
    · rfl

/-- **One circuit for 2-SAT on every `n ≤ n_max`.** The lookup program on the 2-SAT
switchboard of `n_max` variables decides the zero-padded switchboard of every `m ≤ n_max`. -/
theorem one_circuit_2sat {nmax : ℕ} (hn : 2 ≤ nmax) :
    ∃ P : List (Fin 3 × ℕ × ℕ), ∃ i,
      P.length ≤ Fintype.card (Clause2 nmax) + 1 +
        2 ^ Fintype.card (Clause2 nmax) * Fintype.card (Clause2 nmax) ∧
      ∀ m (hm : m ≤ nmax) (e : Clause2 m → Bool),
        (wires (liftSB2 hm e ∘ (Fintype.equivFin (Clause2 nmax)).symm) P).getD i false =
          sat2B m e := by
  classical
  obtain ⟨P, hP, i, -, hi⟩ := lookup_exists (clause2_nonempty hn) (sat2Fin nmax) Finset.univ
  refine ⟨P, i, by simpa using hP, fun m hm e => ?_⟩
  rw [hi _ (by simp)]
  unfold sat2Fin
  have : (liftSB2 hm e ∘ (Fintype.equivFin (Clause2 nmax)).symm) ∘
      Fintype.equivFin (Clause2 nmax) = liftSB2 hm e := by funext c; simp
  rw [this, lift2_sat_iff]

/-- The least circuit is at most the size of any circuit. -/
theorem minCircuitSize_le_of {N : ℕ} {f : (Fin N → Bool) → Bool} {P : List (Fin 3 × ℕ × ℕ)}
    (hP : ComputesOn P f Set.univ) : minCircuitSize f Set.univ ≤ P.length :=
  Nat.sInf_le ⟨P, rfl, hP⟩

/-- **Horizon collapse.** For any family of Boolean functions, the least circuit sizes on
the finitely many input sizes below a horizon are bounded by one constant. -/
theorem horizon_collapse (A : ℕ → ℕ) (hA : ∀ n, 1 ≤ A n)
    (f : ∀ n, (Fin (A n) → Bool) → Bool) (nmax : ℕ) :
    ∃ C, ∀ n ≤ nmax, minCircuitSize (f n) Set.univ ≤ C := by
  refine ⟨∑ n ∈ Finset.range (nmax + 1), (A n + 1 + 2 ^ A n * A n), fun n hn => ?_⟩
  obtain ⟨P, hl, hc⟩ := valid_locus_nonempty (hA n) (f n)
  calc minCircuitSize (f n) Set.univ ≤ P.length := minCircuitSize_le_of hc
    _ ≤ A n + 1 + 2 ^ A n * A n := hl
    _ ≤ _ := Finset.single_le_sum (f := fun n => A n + 1 + 2 ^ A n * A n)
        (fun _ _ => Nat.zero_le _) (Finset.mem_range.mpr (by omega))

/-- **2-SAT and 3-SAT are alike inside the horizon.** For every `n_max` one constant bounds
the least circuit for the 2-SAT switchboard and for the 3-SAT switchboard on every
`3 ≤ n ≤ n_max`. -/
theorem horizon_2sat_3sat (nmax : ℕ) :
    ∃ C, ∀ n, 3 ≤ n → n ≤ nmax →
      minCircuitSize (sat2Fin n) Set.univ ≤ C ∧ minCircuitSize (sat3Fin n) Set.univ ≤ C := by
  refine ⟨∑ n ∈ Finset.range (nmax + 1),
    ((Fintype.card (Clause2 n) + 1 + 2 ^ Fintype.card (Clause2 n) * Fintype.card (Clause2 n)) +
     (Fintype.card (Clause3 n) + 1 + 2 ^ Fintype.card (Clause3 n) * Fintype.card (Clause3 n))),
    fun n h3 hn => ?_⟩
  have hmem : n ∈ Finset.range (nmax + 1) := Finset.mem_range.mpr (by omega)
  have hle := Finset.single_le_sum (f := fun n =>
    ((Fintype.card (Clause2 n) + 1 + 2 ^ Fintype.card (Clause2 n) * Fintype.card (Clause2 n)) +
     (Fintype.card (Clause3 n) + 1 + 2 ^ Fintype.card (Clause3 n) * Fintype.card (Clause3 n))))
    (fun _ _ => Nat.zero_le _) hmem
  obtain ⟨P, hl, hc⟩ := valid_locus_nonempty (clause2_nonempty (by omega : 2 ≤ n)) (sat2Fin n)
  obtain ⟨Q, hl', hc'⟩ := valid_locus_nonempty (clause3_nonempty h3) (sat3Fin n)
  have h1 := minCircuitSize_le_of hc
  have h2 := minCircuitSize_le_of hc'
  constructor <;> omega

/-! ### Growth is decided beyond every horizon -/

/-- Polynomially bounded growth of a size function. -/
def PolyBounded (s : ℕ → ℕ) : Prop := ∃ k C : ℕ, ∀ n, s n ≤ C * (n + 1) ^ k

/-- **Finitely many values never matter.** If two size functions agree from `n₀` on, one is
polynomially bounded exactly when the other is. -/
theorem polyBounded_congr {s t : ℕ → ℕ} (n₀ : ℕ) (h : ∀ n, n₀ ≤ n → s n = t n) :
    PolyBounded s ↔ PolyBounded t := by
  have key : ∀ {s t : ℕ → ℕ}, (∀ n, n₀ ≤ n → s n = t n) → PolyBounded t → PolyBounded s := by
    rintro s t h ⟨k, C, hC⟩
    refine ⟨k, C + ∑ m ∈ Finset.range n₀, s m, fun n => ?_⟩
    have hp : 1 ≤ (n + 1) ^ k := Nat.one_le_pow _ _ (Nat.succ_pos n)
    by_cases hn : n₀ ≤ n
    · rw [h n hn]
      exact (hC n).trans (Nat.mul_le_mul_right _ (Nat.le_add_right _ _))
    · have : s n ≤ ∑ m ∈ Finset.range n₀, s m :=
        Finset.single_le_sum (f := s) (fun _ _ => Nat.zero_le _)
          (Finset.mem_range.mpr (by omega))
      calc s n ≤ (C + ∑ m ∈ Finset.range n₀, s m) * 1 := by omega
        _ ≤ _ := Nat.mul_le_mul_left _ hp
  exact ⟨key (fun n hn => (h n hn).symm), key h⟩

theorem not_polyBounded_of {s : ℕ → ℕ} (n₀ : ℕ) (h : ∀ n, n₀ ≤ n → s n = (n + 1) ^ n) :
    ¬ PolyBounded s := by
  rintro ⟨k, C, hC⟩
  set n := n₀ + k + C + 1
  have h1 := hC n
  rw [h n (by omega)] at h1
  have h2 : (n + 1) ^ (k + 1) ≤ (n + 1) ^ n := Nat.pow_le_pow_right (by omega) (by omega)
  have h3 : (n + 1) ^ (k + 1) = (n + 1) * (n + 1) ^ k := by ring
  have h4 : 0 < (n + 1) ^ k := Nat.pow_pos (by omega)
  have h5 : C * (n + 1) ^ k < (n + 1) * (n + 1) ^ k := Nat.mul_lt_mul_of_pos_right (by omega) h4
  omega

/-- **No table inside a horizon decides growth.** Every table of values below `n₀` is the
beginning of a polynomially bounded size function and of one that is not. -/
theorem horizon_blind (n₀ : ℕ) (v : ℕ → ℕ) :
    (∃ s, (∀ n < n₀, s n = v n) ∧ PolyBounded s) ∧
      (∃ s, (∀ n < n₀, s n = v n) ∧ ¬ PolyBounded s) := by
  refine ⟨⟨fun n => if n < n₀ then v n else 0, fun n hn => if_pos hn, ?_⟩,
    ⟨fun n => if n < n₀ then v n else (n + 1) ^ n, fun n hn => if_pos hn, ?_⟩⟩
  · exact (polyBounded_congr n₀ (t := fun _ => 0) (fun n hn => if_neg (by omega))).mpr
      ⟨0, 0, fun _ => le_refl _⟩
  · exact not_polyBounded_of n₀ (fun n hn => if_neg (by omega))

/-- **The horizon hides the question.** For each `n_max`, replacing the least circuit sizes
of 2-SAT or 3-SAT below `n_max` by anything leaves polynomial growth unchanged. -/
theorem growth_beyond_horizon (nmax : ℕ) (s t : ℕ → ℕ) (h : ∀ n, nmax < n → s n = t n) :
    PolyBounded s ↔ PolyBounded t :=
  polyBounded_congr (nmax + 1) (fun n hn => h n (by omega))

/-! ### The trace: 2-SAT has none to keep -/

/-- **Saturation inside a finite universe needs no history.** An inflationary map on the
subsets of a finite universe `W` reaches a fixed point within `|W|` steps. -/
theorem saturate_stable {α : Type*} [DecidableEq α] (W : Finset α)
    (f : Finset α → Finset α) (hf : ∀ s, s ⊆ f s) (hW : ∀ s, s ⊆ W → f s ⊆ W)
    (s : Finset α) (hs : s ⊆ W) : f (f^[W.card] s) = f^[W.card] s := by
  have hin : ∀ k, f^[k] s ⊆ W := by
    intro k; induction k with
    | zero => exact hs
    | succ k ih => rw [iterate_succ_apply']; exact hW _ ih
  by_contra hne
  have hstep : ∀ k ≤ W.card, f^[k + 1] s ≠ f^[k] s := by
    intro k hk heq
    apply hne
    have : ∀ j, f^[k + j] s = f^[k] s := by
      intro j; induction j with
      | zero => rfl
      | succ j ih =>
        rw [← add_assoc, iterate_succ_apply', ih, ← iterate_succ_apply' f k, heq]
    have h1 := this (W.card - k)
    have h2 := this (W.card - k + 1)
    rw [Nat.add_sub_cancel' hk] at h1
    rw [← add_assoc, Nat.add_sub_cancel' hk, iterate_succ_apply'] at h2
    rw [h2, h1]
  have hgrow : ∀ k ≤ W.card + 1, k ≤ (f^[k] s).card := by
    intro k; induction k with
    | zero => intro _; exact Nat.zero_le _
    | succ k ih =>
      intro hk
      have hsub : f^[k] s ⊂ f^[k + 1] s := by
        rw [iterate_succ_apply']
        exact Finset.ssubset_iff_subset_ne.mpr ⟨hf _, fun h => hstep k (by omega)
          (by rw [iterate_succ_apply']; exact h.symm)⟩
      have := Finset.card_lt_card hsub
      have := ih (by omega)
      omega
  have := hgrow (W.card + 1) le_rfl
  have := Finset.card_le_card (hin (W.card + 1))
  omega

/-- Clauses as sets of literals. -/
abbrev Lits (n : ℕ) := Finset (Fin n × Bool)

/-- One round of resolution: add every resolvent of two clauses that clash. -/
noncomputable def resStep {n : ℕ} (s : Finset (Lits n)) : Finset (Lits n) := by
  classical
  exact s ∪ ((s ×ˢ s ×ˢ (Finset.univ : Finset (Fin n))).filter
    (fun p => (p.2.2, true) ∈ p.1 ∧ (p.2.2, false) ∈ p.2.1)).image
      (fun p => resolvent p.1 p.2.1 p.2.2)

/-- The clauses of width at most two. -/
noncomputable def width2 (n : ℕ) : Finset (Lits n) := by
  classical
  exact (Finset.univ : Finset (Lits n)).filter fun C => C.card ≤ 2

theorem resStep_width2 {n : ℕ} (s : Finset (Lits n)) (hs : s ⊆ width2 n) :
    resStep s ⊆ width2 n := by
  classical
  intro C hC
  unfold resStep at hC
  rcases Finset.mem_union.mp hC with h | h
  · exact hs h
  · obtain ⟨⟨A, B, v⟩, hp, rfl⟩ := Finset.mem_image.mp h
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_univ, and_true] at hp
    obtain ⟨⟨hA, hB⟩, hv, hv'⟩ := hp
    have wA := hs hA
    have wB := hs hB
    unfold width2 at wA wB ⊢
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at wA wB ⊢
    convert resolvent_width_two A B v wA wB hv hv' using 2

/-- **2-SAT keeps no trace.** Resolution started from a 2-CNF stays among the at most
`1 + 2n + (2n)²` clauses of width at most two, and after that many rounds it has reached its
closure: the current set of clauses is the whole state, and no record of the derivation is
needed. -/
theorem two_sat_no_trace {n : ℕ} (s : Finset (Lits n)) (hs : s ⊆ width2 n) :
    (width2 n).card ≤ 1 + 2 * n + (2 * n) ^ 2 ∧
      resStep (resStep^[(width2 n).card] s) = resStep^[(width2 n).card] s ∧
      resStep^[(width2 n).card] s ⊆ width2 n := by
  classical
  refine ⟨?_, saturate_stable _ resStep (fun _ => Finset.subset_union_left) resStep_width2 s hs,
    ?_⟩
  · unfold width2; convert width_two_clauses_card (n := n) using 3
  · have : ∀ k, resStep^[k] s ⊆ width2 n := by
      intro k; induction k with
      | zero => exact hs
      | succ k ih => rw [iterate_succ_apply']; exact resStep_width2 _ ih
    exact this _

/-- **3-SAT leaves its space.** Two 3-clauses can resolve to four literals, so the derived
clauses of a 3-CNF range over all `2^(2n)` sets of literals, and the closure has to carry
clauses that are not 3-clauses. -/
theorem three_sat_leaves_space :
    (resolvent (n := 5) {(0, true), (1, true), (2, true)} {(0, false), (3, true), (4, true)} 0).card
      = 4 ∧ ∀ n, Fintype.card (Lits n) = 2 ^ (2 * n) := by
  refine ⟨resolvent_width_grows, fun n => ?_⟩
  simp [Lits, Fintype.card_finset, mul_comm]

/-! ### The order of overflows and products -/

/-- **A two-term sum overflows in the product.** -/
theorem carry_two (a b : Bool) :
    a.toNat + b.toNat = (xor a b).toNat + 2 * (a && b).toNat := by
  cases a <;> cases b <;> rfl

/-- **A three-term sum overflows in the majority.** The carry of three bits is their
majority, the polymorphism of 2-SAT. -/
theorem carry_three (a b c : Bool) :
    a.toNat + b.toNat + c.toNat = (xor (xor a b) c).toNat + 2 * (maj a b c).toNat := by
  cases a <;> cases b <;> cases c <;> rfl

/-- The carry of three bits as an integer polynomial: `ab + ac + bc - 2abc`. -/
theorem carry_three_poly (a b c : Bool) :
    ((maj a b c).toNat : ℤ) = a.toNat * b.toNat + a.toNat * c.toNat + b.toNat * c.toNat
      - 2 * (a.toNat * b.toNat * c.toNat) := by
  cases a <;> cases b <;> cases c <;> rfl

/-- **OR of `k` terms over `F₂`.** `1 + ∏ (1 + x_i)` is the sum of the products over every
nonempty set of terms: `2^k - 1` monomials, up to degree `k`. -/
theorem or_anf {ι : Type*} [DecidableEq ι] (s : Finset ι) (x : ι → ZMod 2) :
    1 + ∏ i ∈ s, (1 + x i) = ∑ t ∈ s.powerset.erase ∅, ∏ i ∈ t, x i := by
  classical
  have h := Finset.prod_one_add (s := s) (f := x)
  rw [add_comm (1 : ZMod 2), h, ← Finset.add_sum_erase _ _ (Finset.empty_mem_powerset s),
    Finset.prod_empty]
  generalize (∑ t ∈ s.powerset.erase ∅, ∏ i ∈ t, x i) = S
  have : (2 : ZMod 2) = 0 := rfl
  linear_combination (1 : ZMod 2) * this

theorem or_anf_card {ι : Type*} [DecidableEq ι] (s : Finset ι) : (s.powerset.erase ∅).card = 2 ^ s.card - 1 := by
  rw [Finset.card_erase_of_mem (Finset.empty_mem_powerset s), Finset.card_powerset]

/-- The two-term and three-term ORs written out. -/
theorem or_two_three (a b c : ZMod 2) :
    1 + (1 + a) * (1 + b) = a + b + a * b ∧
      1 + (1 + a) * (1 + b) * (1 + c) = a + b + c + a * b + a * c + b * c + a * b * c := by
  constructor
  · have : (2 : ZMod 2) = 0 := rfl
    linear_combination (1 : ZMod 2) * this
  · have : (2 : ZMod 2) = 0 := rfl
    linear_combination (1 : ZMod 2) * this

/-! ### General formulas: two-term and three-term combinations -/

/-- General Boolean formulas over AND, OR, NOT with two-term and three-term combinations. -/
inductive GF (n : ℕ) : Type
  | const : Bool → GF n
  | var : Fin n → GF n
  | not : GF n → GF n
  | and2 : GF n → GF n → GF n
  | or2 : GF n → GF n → GF n
  | and3 : GF n → GF n → GF n → GF n
  | or3 : GF n → GF n → GF n → GF n

namespace GF

variable {n : ℕ}

def eval (x : Fin n → Bool) : GF n → Bool
  | const b => b
  | var i => x i
  | not φ => !(eval x φ)
  | and2 φ ψ => eval x φ && eval x ψ
  | or2 φ ψ => eval x φ || eval x ψ
  | and3 φ ψ χ => eval x φ && eval x ψ && eval x χ
  | or3 φ ψ χ => eval x φ || eval x ψ || eval x χ

/-- The number of connectives. -/
def size : GF n → ℕ
  | const _ => 0
  | var _ => 0
  | not φ => size φ + 1
  | and2 φ ψ => size φ + size ψ + 1
  | or2 φ ψ => size φ + size ψ + 1
  | and3 φ ψ χ => size φ + size ψ + size χ + 1
  | or3 φ ψ χ => size φ + size ψ + size χ + 1

/-- Only two-term combinations. -/
def IsBin : GF n → Prop
  | const _ => True
  | var _ => True
  | not φ => IsBin φ
  | and2 φ ψ => IsBin φ ∧ IsBin ψ
  | or2 φ ψ => IsBin φ ∧ IsBin ψ
  | and3 _ _ _ => False
  | or3 _ _ _ => False

/-- Rewrite every three-term combination as two two-term ones. -/
def bin : GF n → GF n
  | const b => const b
  | var i => var i
  | not φ => not (bin φ)
  | and2 φ ψ => and2 (bin φ) (bin ψ)
  | or2 φ ψ => or2 (bin φ) (bin ψ)
  | and3 φ ψ χ => and2 (and2 (bin φ) (bin ψ)) (bin χ)
  | or3 φ ψ χ => or2 (or2 (bin φ) (bin ψ)) (bin χ)

/-- **A three-term combination is two two-term ones.** The rewrite keeps the value,
uses only two-term combinations, and at most doubles the number of connectives. -/
theorem bin_spec (φ : GF n) :
    (∀ x, eval x (bin φ) = eval x φ) ∧ IsBin (bin φ) ∧ size (bin φ) ≤ 2 * size φ := by
  induction φ with
  | const b => exact ⟨fun _ => rfl, trivial, le_refl _⟩
  | var i => exact ⟨fun _ => rfl, trivial, le_refl _⟩
  | not φ ih =>
    obtain ⟨h1, h2, h3⟩ := ih
    exact ⟨fun x => by simp [bin, eval, h1], h2, by simp only [bin, size]; omega⟩
  | and2 φ ψ ihφ ihψ =>
    obtain ⟨a1, a2, a3⟩ := ihφ; obtain ⟨b1, b2, b3⟩ := ihψ
    exact ⟨fun x => by simp [bin, eval, a1, b1], ⟨a2, b2⟩, by simp only [bin, size]; omega⟩
  | or2 φ ψ ihφ ihψ =>
    obtain ⟨a1, a2, a3⟩ := ihφ; obtain ⟨b1, b2, b3⟩ := ihψ
    exact ⟨fun x => by simp [bin, eval, a1, b1], ⟨a2, b2⟩, by simp only [bin, size]; omega⟩
  | and3 φ ψ χ ihφ ihψ ihχ =>
    obtain ⟨a1, a2, a3⟩ := ihφ; obtain ⟨b1, b2, b3⟩ := ihψ; obtain ⟨c1, c2, c3⟩ := ihχ
    exact ⟨fun x => by simp [bin, eval, a1, b1, c1], ⟨⟨a2, b2⟩, c2⟩,
      by simp only [bin, size]; omega⟩
  | or3 φ ψ χ ihφ ihψ ihχ =>
    obtain ⟨a1, a2, a3⟩ := ihφ; obtain ⟨b1, b2, b3⟩ := ihψ; obtain ⟨c1, c2, c3⟩ := ihχ
    exact ⟨fun x => by simp [bin, eval, a1, b1, c1], ⟨⟨a2, b2⟩, c2⟩,
      by simp only [bin, size]; omega⟩

/-- **Satisfiability does not see the arity.** A formula with three-term combinations and
its two-term rewrite are satisfiable together. -/
theorem sat_bin_iff (φ : GF n) : (∃ x, eval x (bin φ) = true) ↔ ∃ x, eval x φ = true := by
  simp only [(bin_spec φ).1]

/-- The OR of a list of formulas with two-term combinations. -/
def orList : List (GF n) → GF n
  | [] => const false
  | φ :: L => or2 φ (orList L)

/-- The AND of a list of formulas with two-term combinations. -/
def andList : List (GF n) → GF n
  | [] => const true
  | φ :: L => and2 φ (andList L)

def litF (l : Fin n × Bool) : GF n := if l.2 then var l.1 else not (var l.1)

theorem eval_orList (x : Fin n → Bool) (L : List (GF n)) :
    eval x (orList L) = true ↔ ∃ φ ∈ L, eval x φ = true := by
  induction L with
  | nil => simp [orList, eval]
  | cons φ L ih => simp [orList, eval, ih]

theorem eval_andList (x : Fin n → Bool) (L : List (GF n)) :
    eval x (andList L) = true ↔ ∀ φ ∈ L, eval x φ = true := by
  induction L with
  | nil => simp [andList, eval]
  | cons φ L ih => simp [andList, eval, ih]

theorem isBin_orList (L : List (GF n)) (h : ∀ φ ∈ L, IsBin φ) : IsBin (orList L) := by
  induction L with
  | nil => trivial
  | cons φ L ih => exact ⟨h φ (by simp), ih fun ψ hψ => h ψ (by simp [hψ])⟩

theorem isBin_andList (L : List (GF n)) (h : ∀ φ ∈ L, IsBin φ) : IsBin (andList L) := by
  induction L with
  | nil => trivial
  | cons φ L ih => exact ⟨h φ (by simp), ih fun ψ hψ => h ψ (by simp [hψ])⟩

theorem eval_litF (x : Fin n → Bool) (l : Fin n × Bool) :
    eval x (litF l) = true ↔ x l.1 = l.2 := by
  unfold litF; split_ifs with h <;> cases hx : x l.1 <;> simp_all [eval]

/-- A CNF of any width, as a formula with two-term combinations only. -/
def cnfF (C : List (List (Fin n × Bool))) : GF n := andList (C.map fun c => orList (c.map litF))

/-- **Two-term formulas already hold every CNF.** For every CNF, of any clause width, the
formula `cnfF C` uses only two-term combinations and is true exactly where the CNF is. So
satisfiability of general formulas with two-term combinations contains 3-SAT. -/
theorem cnfF_spec (C : List (List (Fin n × Bool))) :
    IsBin (cnfF C) ∧ ∀ x, eval x (cnfF C) = true ↔ ∀ c ∈ C, ∃ l ∈ c, x l.1 = l.2 := by
  refine ⟨isBin_andList _ fun φ hφ => ?_, fun x => ?_⟩
  · obtain ⟨c, -, rfl⟩ := List.mem_map.mp hφ
    exact isBin_orList _ fun ψ hψ => by
      obtain ⟨l, -, rfl⟩ := List.mem_map.mp hψ
      unfold litF; split_ifs <;> trivial
  · simp only [cnfF, eval_andList, List.mem_map, forall_exists_index, and_imp,
      forall_apply_eq_imp_iff₂, eval_orList, exists_exists_and_eq_and, eval_litF]

end GF

/-- **The sequence of overflows in a three-term sum.** Adding `a + b` overflows in `ab`
and leaves `a ⊕ b`; adding `c` to that overflows in `(a ⊕ b) c`. The two overflows never
happen together, and their OR is the majority: the three-term carry is two two-term
carries in sequence. -/
theorem carry_sequence (a b c : Bool) :
    maj a b c = ((a && b) || (xor a b && c)) ∧ ((a && b) && (xor a b && c)) = false ∧
      a.toNat + b.toNat + c.toNat =
        (xor (xor a b) c).toNat + 2 * ((a && b).toNat + (xor a b && c).toNat) := by
  cases a <;> cases b <;> cases c <;> decide

/-! ### The intrinsic difference: majority, independent of every circuit -/

/-- Coordinatewise majority of three assignments. -/
def majA {m : ℕ} (x y z : Fin m → Bool) : Fin m → Bool := fun i => maj (x i) (y i) (z i)

/-- A set of assignments closed under coordinatewise majority. -/
def MajClosed {m : ℕ} (S : Set (Fin m → Bool)) : Prop :=
  ∀ x ∈ S, ∀ y ∈ S, ∀ z ∈ S, majA x y z ∈ S

/-- An assignment satisfies a CNF given as a list of clauses (sets of literals). -/
def SatCNF {m : ℕ} (C : List (Finset (Fin m × Bool))) (x : Fin m → Bool) : Prop :=
  ∀ c ∈ C, ∃ l ∈ c, x l.1 = l.2

/-- **A clause of width at most two is closed under majority.** Of the three literals that
make three assignments true, two coincide, and the majority keeps that literal. -/
theorem clause_width2_maj {m : ℕ} (c : Finset (Fin m × Bool)) (hc : c.card ≤ 2)
    {x y z : Fin m → Bool} (hx : ∃ l ∈ c, x l.1 = l.2) (hy : ∃ l ∈ c, y l.1 = l.2)
    (hz : ∃ l ∈ c, z l.1 = l.2) : ∃ l ∈ c, majA x y z l.1 = l.2 := by
  classical
  obtain ⟨a, ha, hxa⟩ := hx
  obtain ⟨b, hb, hyb⟩ := hy
  obtain ⟨d, hd, hzd⟩ := hz
  by_cases hab : a = b
  · subst hab; exact ⟨a, ha, by simp only [majA]; rw [hxa, hyb, maj_left]⟩
  by_cases had : a = d
  · subst had; exact ⟨a, ha, by simp only [majA]; rw [hxa, hzd, maj_mid]⟩
  by_cases hbd : b = d
  · subst hbd; exact ⟨b, hb, by simp only [majA]; rw [hyb, hzd, maj_right]⟩
  exfalso
  have h3 : ({a, b, d} : Finset (Fin m × Bool)).card = 3 :=
    Finset.card_eq_three.mpr ⟨a, b, d, hab, had, hbd, rfl⟩
  have hsub : ({a, b, d} : Finset (Fin m × Bool)) ⊆ c := by
    intro l hl; simp only [Finset.mem_insert, Finset.mem_singleton] at hl
    rcases hl with rfl | rfl | rfl <;> assumption
  have := Finset.card_le_card hsub
  omega

/-- **Every 2-CNF is closed under majority.** -/
theorem twoCNF_majClosed {m : ℕ} (C : List (Finset (Fin m × Bool)))
    (hC : ∀ c ∈ C, c.card ≤ 2) : MajClosed {x | SatCNF C x} := by
  intro x hx y hy z hz c hc
  exact clause_width2_maj c (hC c hc) (hx c hc) (hy c hc) (hz c hc)

/-- **Hiding variables keeps majority closure.** Majority acts coordinate by coordinate, so
it commutes with every renaming or forgetting of coordinates. -/
theorem proj_majClosed {m n : ℕ} (σ : Fin n → Fin m) {S : Set (Fin m → Bool)}
    (hS : MajClosed S) : MajClosed ((fun x => x ∘ σ) '' S) := by
  rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩ _ ⟨z, hz, rfl⟩
  exact ⟨majA x y z, hS x hx y hy z hz, rfl⟩

/-- The solutions of the 3-clause `x₀ ∨ x₁ ∨ x₂`. -/
def clause3Set : Set (Fin 3 → Bool) := {x | x 0 = true ∨ x 1 = true ∨ x 2 = true}

/-- **A 3-clause is not closed under majority.** `100`, `010`, `001` satisfy it and their
majority `000` does not. -/
theorem clause3Set_not_majClosed : ¬ MajClosed clause3Set := by
  intro h
  have := h ![true, false, false] (by simp [clause3Set]) ![false, true, false]
    (by simp [clause3Set]) ![false, false, true] (by simp [clause3Set])
  simp [clause3Set, majA, maj] at this

/-- **A 3-clause is no 2-CNF, with any number of extra variables.** No 2-CNF on any number
of variables, read through any choice of three of its coordinates, has exactly the
solutions of `x₀ ∨ x₁ ∨ x₂`. -/
theorem clause3_not_2cnf_projection :
    ¬ ∃ (m : ℕ) (σ : Fin 3 → Fin m) (C : List (Finset (Fin m × Bool))),
      (∀ c ∈ C, c.card ≤ 2) ∧ (fun x => x ∘ σ) '' {x | SatCNF C x} = clause3Set := by
  rintro ⟨m, σ, C, hC, hS⟩
  exact clause3Set_not_majClosed (hS ▸ proj_majClosed σ (twoCNF_majClosed C hC))

/-- **Every circuit for a function accepts the same set.** Whatever program decides `f`, of
whatever size, depth or fan-out, the inputs it accepts are the solutions of `f`. -/
theorem accepted_eq {N : ℕ} (f : (Fin N → Bool) → Bool) (P : List (Fin 3 × ℕ × ℕ)) (i : ℕ)
    (hP : ∀ x, (wires x P).getD i false = f x) :
    {x | (wires x P).getD i false = true} = {x | f x = true} := by
  ext x; simp only [Set.mem_setOf_eq, hP]

/-- **The difference does not depend on the circuit.** For every program that computes `x₀ ∨ x₁ ∨ x₂`, the accepted set is not closed under majority, while for every
program that decides a 2-CNF it is. -/
theorem dag_independent :
    (∀ (P : List (Fin 3 × ℕ × ℕ)) (i : ℕ),
        (∀ x : Fin 3 → Bool, (wires x P).getD i false = (x 0 || x 1 || x 2)) →
        ¬ MajClosed {x : Fin 3 → Bool | (wires x P).getD i false = true}) ∧
    (∀ (m : ℕ) (C : List (Finset (Fin m × Bool))), (∀ c ∈ C, c.card ≤ 2) →
      ∀ (P : List (Fin 3 × ℕ × ℕ)) (i : ℕ),
        (∀ x : Fin m → Bool, ((wires x P).getD i false = true ↔ SatCNF C x)) →
        MajClosed {x : Fin m → Bool | (wires x P).getD i false = true}) := by
  refine ⟨fun P i hP => ?_, fun m C hC P i hP => ?_⟩
  · have : {x : Fin 3 → Bool | (wires x P).getD i false = true} = clause3Set := by
      ext x; simp only [Set.mem_setOf_eq, hP, clause3Set, Bool.or_eq_true]; tauto
    rw [this]; exact clause3Set_not_majClosed
  · have : {x | (wires x P).getD i false = true} = {x | SatCNF C x} := by
      ext x; exact hP x
    rw [this]; exact twoCNF_majClosed C hC

/-! ### General k-SAT: constraints of any shape on k variables -/

/-- A general `k`-SAT instance on `n` variables: each constraint reads `k` variables through a
scope and allows an arbitrary set of patterns (any combination of AND, OR, NOT). -/
abbrev GInst (n k : ℕ) := List ((Fin k → Fin n) × Set (Fin k → Bool))

/-- An assignment satisfies every constraint. -/
def SatG {n k : ℕ} (I : GInst n k) (x : Fin n → Bool) : Prop := ∀ c ∈ I, x ∘ c.1 ∈ c.2

/-- **A constraint is the list of its forbidden patterns.** A pattern is allowed exactly
when it differs from every forbidden one: each forbidden pattern is one switch. -/
theorem constraint_forbidden {k : ℕ} (R : Set (Fin k → Bool)) (p : Fin k → Bool) :
    p ∈ R ↔ ∀ q, q ∉ R → p ≠ q := by
  constructor
  · rintro hp q hq rfl; exact hq hp
  · intro h; by_contra hp; exact h p hp rfl

/-- On two bits the majority of three patterns is one of them. -/
theorem majA_two_mem (x y z : Fin 2 → Bool) : majA x y z = x ∨ majA x y z = y ∨ majA x y z = z := by
  revert x y z; decide

/-- **Every relation on two variables is closed under majority.** -/
theorem binary_majClosed (R : Set (Fin 2 → Bool)) : MajClosed R := by
  intro x hx y hy z hz
  rcases majA_two_mem x y z with h | h | h <;> rw [h] <;> assumption

/-- Constraints closed under majority give solution sets closed under majority. -/
theorem satG_majClosed {n k : ℕ} (I : GInst n k) (hI : ∀ c ∈ I, MajClosed c.2) :
    MajClosed {x | SatG I x} := by
  intro x hx y hy z hz c hc
  exact hI c hc _ (hx c hc) _ (hy c hc) _ (hz c hc)

/-- **General 2-SAT is closed under majority.** Whatever combination of AND, OR and NOT
each two-variable constraint is, the solutions of the instance are closed under majority. -/
theorem gen2_majClosed {n : ℕ} (I : GInst n 2) : MajClosed {x | SatG I x} :=
  satG_majClosed I fun c _ => binary_majClosed c.2

/-- **General 3-SAT is not.** The single constraint `x₀ ∨ x₁ ∨ x₂` has solutions not closed
under majority, and no general 2-SAT instance on any number of variables, read through any
three of them, has exactly its solutions. -/
theorem gen3_not_gen2 :
    ¬ MajClosed {x | SatG ([(id, clause3Set)] : GInst 3 3) x} ∧
      ¬ ∃ (m : ℕ) (σ : Fin 3 → Fin m) (I : GInst m 2),
        (fun x => x ∘ σ) '' {x | SatG I x} = clause3Set := by
  refine ⟨?_, ?_⟩
  · have : {x | SatG ([(id, clause3Set)] : GInst 3 3) x} = clause3Set := by
      ext x; simp [SatG]
    rw [this]; exact clause3Set_not_majClosed
  · rintro ⟨m, σ, I, hS⟩
    exact clause3Set_not_majClosed (hS ▸ proj_majClosed σ (gen2_majClosed I))

/-- **The difference does not depend on the circuit, for general k-SAT.** Every program that
decides a general 2-SAT instance accepts a set closed under majority, however it is built. -/
theorem dag_independent_gen {m : ℕ} (I : GInst m 2) (P : List (Fin 3 × ℕ × ℕ)) (i : ℕ)
    (hP : ∀ x : Fin m → Bool, ((wires x P).getD i false = true ↔ SatG I x)) :
    MajClosed {x : Fin m → Bool | (wires x P).getD i false = true} := by
  have : {x : Fin m → Bool | (wires x P).getD i false = true} = {x | SatG I x} := by
    ext x; exact hP x
  rw [this]; exact gen2_majClosed I

/-! ### The irreducible differences

A difference between general 2-SAT and general 3-SAT is *irreducible* when no reduction
available to an algorithm removes it: not the choice of circuit, not extra variables, not
renaming or negating variables, and not rewriting three-term connectives into two-term ones.
The theorems below prove each invariance and collect the differences in one statement. -/

/-- On the cube the majority of the three patterns at distance one from `000` is `000`. -/
theorem majA_cube_example :
    majA ![true, false, false] ![false, true, false] ![false, false, true] = ![false, false, false] := by
  decide

/-- Majority commutes with negating a coordinate. -/
theorem maj_xor (t a b c : Bool) : maj (xor t a) (xor t b) (xor t c) = xor t (maj a b c) := by
  cases t <;> cases a <;> cases b <;> cases c <;> decide

/-- **Negating variables keeps majority closure.** -/
theorem flip_majClosed {m : ℕ} (t : Fin m → Bool) {S : Set (Fin m → Bool)} (hS : MajClosed S) :
    MajClosed ((fun x i => xor (t i) (x i)) '' S) := by
  rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩ _ ⟨z, hz, rfl⟩
  refine ⟨majA x y z, hS x hx y hy z hz, ?_⟩
  funext i; simp only [majA, maj_xor]

/-- **Every single forbidden pattern on three or more variables breaks majority.** The three
patterns that differ from `s` in exactly one of three coordinates avoid `s`, and their
majority is `s`. -/
theorem forbid_not_majClosed {k : ℕ} (hk : 3 ≤ k) (s : Fin k → Bool) :
    ¬ MajClosed {x | x ≠ s} := by
  intro h
  let i0 : Fin k := ⟨0, by omega⟩
  let i1 : Fin k := ⟨1, by omega⟩
  let i2 : Fin k := ⟨2, by omega⟩
  have h01 : i0 ≠ i1 := by simp [i0, i1, Fin.ext_iff]
  have h02 : i0 ≠ i2 := by simp [i0, i2, Fin.ext_iff]
  have h12 : i1 ≠ i2 := by simp [i1, i2, Fin.ext_iff]
  have hne : ∀ i, Function.update s i (!s i) ≠ s := by
    intro i he; have := congrFun he i; simp at this
  have := h _ (hne i0) _ (hne i1) _ (hne i2)
  apply this
  funext j
  simp only [majA, Function.update_apply]
  by_cases a0 : j = i0
  · subst a0; simp [h01, h02, maj]
  by_cases a1 : j = i1
  · subst a1; simp [h01.symm, h12, maj]
  by_cases a2 : j = i2
  · subst a2; simp [h02.symm, h12.symm, maj]
  simp [a0, a1, a2, maj]

/-- **No general 2-SAT instance, with any extra variables, has the solutions of any
three-variable clause**, whatever the signs of its literals. -/
theorem forbid3_not_gen2 (s : Fin 3 → Bool) :
    ¬ ∃ (m : ℕ) (σ : Fin 3 → Fin m) (I : GInst m 2),
      (fun x => x ∘ σ) '' {x | SatG I x} = {x | x ≠ s} := by
  rintro ⟨m, σ, I, hS⟩
  exact forbid_not_majClosed le_rfl s (hS ▸ proj_majClosed σ (gen2_majClosed I))

/-- **Rewriting the arity of connectives keeps the solution set.** -/
theorem bin_solutions {n : ℕ} (φ : GF n) :
    {x | GF.eval x (GF.bin φ) = true} = {x | GF.eval x φ = true} := by
  ext x; simp only [Set.mem_setOf_eq, (GF.bin_spec φ).1 x]

/-- **The irreducible differences between general 2-SAT and general 3-SAT.**
1. *Solutions.* Every general 2-SAT instance has solutions closed under majority; every
   single forbidden pattern on three or more variables breaks it.
2. *Extra variables and renaming.* No general 2-SAT instance on any number of variables,
   read through any three of them, has the solutions of any three-variable clause.
3. *Negation.* Negating any variables keeps majority closure.
4. *Circuits.* Every program deciding a general 2-SAT instance accepts a set closed under
   majority; every program deciding a three-variable clause accepts one that is not.
5. *Arity.* Rewriting three-term connectives as two-term ones keeps every solution set.
6. *Overflows.* Two terms overflow once, in their product; three terms overflow twice in
   sequence, never together, and the two overflows make the majority.
7. *Resolution.* Two clashing patterns on two variables resolve on two variables; two on
   three variables can resolve on four. -/
theorem irreducible_differences :
    (∀ (n : ℕ) (I : GInst n 2), MajClosed {x | SatG I x}) ∧
    (∀ k, 3 ≤ k → ∀ s : Fin k → Bool, ¬ MajClosed {x | x ≠ s}) ∧
    (∀ s : Fin 3 → Bool, ¬ ∃ (m : ℕ) (σ : Fin 3 → Fin m) (I : GInst m 2),
      (fun x => x ∘ σ) '' {x | SatG I x} = {x | x ≠ s}) ∧
    (∀ (m : ℕ) (t : Fin m → Bool) (S : Set (Fin m → Bool)), MajClosed S →
      MajClosed ((fun x i => xor (t i) (x i)) '' S)) ∧
    (∀ (m : ℕ) (I : GInst m 2) (P : List (Fin 3 × ℕ × ℕ)) (i : ℕ),
      (∀ x : Fin m → Bool, ((wires x P).getD i false = true ↔ SatG I x)) →
      MajClosed {x : Fin m → Bool | (wires x P).getD i false = true}) ∧
    (∀ (s : Fin 3 → Bool) (P : List (Fin 3 × ℕ × ℕ)) (i : ℕ),
      (∀ x : Fin 3 → Bool, ((wires x P).getD i false = true ↔ x ≠ s)) →
      ¬ MajClosed {x : Fin 3 → Bool | (wires x P).getD i false = true}) ∧
    (∀ (n : ℕ) (φ : GF n), {x | GF.eval x (GF.bin φ) = true} = {x | GF.eval x φ = true}) ∧
    (∀ a b c : Bool,
      a.toNat + b.toNat = (xor a b).toNat + 2 * (a && b).toNat ∧
      maj a b c = ((a && b) || (xor a b && c)) ∧ ((a && b) && (xor a b && c)) = false ∧
      a.toNat + b.toNat + c.toNat =
        (xor (xor a b) c).toNat + 2 * ((a && b).toNat + (xor a b && c).toNat)) ∧
    (∀ (n : ℕ) (C D : Finset (Fin n × Bool)) (v : Fin n), C.card ≤ 2 → D.card ≤ 2 →
      (v, true) ∈ C → (v, false) ∈ D → (resolvent C D v).card ≤ 2) ∧
    (resolvent (n := 5) {(0, true), (1, true), (2, true)} {(0, false), (3, true), (4, true)} 0).card
      = 4 := by
  refine ⟨fun n I => gen2_majClosed I, fun k hk s => forbid_not_majClosed hk s,
    forbid3_not_gen2, fun m t S hS => flip_majClosed t hS,
    fun m I P i hP => dag_independent_gen I P i hP, fun s P i hP => ?_,
    fun n φ => bin_solutions φ, fun a b c => ⟨carry_two a b, carry_sequence a b c⟩,
    fun n C D v hC hD hv hv' => resolvent_width_two C D v hC hD hv hv', resolvent_width_grows⟩
  have : {x : Fin 3 → Bool | (wires x P).getD i false = true} = {x | x ≠ s} := by
    ext x; exact hP x
  rw [this]; exact forbid_not_majClosed le_rfl s

/-! ### What keeping a trace means

A step *keeps a trace* when the information it discards is stored, so that what it
computed can be recovered. In a one-bit register the discarded information is the overflow. -/

/-- **The register forgets the sum.** The kept bit `a ⊕ b` does not determine `a + b`; the
overflow `ab` is exactly the trace that does (`carry_two`). -/
theorem register_trace_two :
    ∃ a b a' b' : Bool, xor a b = xor a' b' ∧ a.toNat + b.toNat ≠ a'.toNat + b'.toNat :=
  ⟨true, true, false, false, rfl, by decide⟩

/-- **A three-term sum needs the second overflow.** The kept bit and the first overflow do not
determine `a + b + c`; the second overflow `(a ⊕ b) c`, which reads the bit kept by the first
step, completes the trace (`carry_sequence`). -/
theorem register_trace_three :
    ∃ a b c a' b' c' : Bool, xor (xor a b) c = xor (xor a' b') c' ∧ (a && b) = (a' && b') ∧
      a.toNat + b.toNat + c.toNat ≠ a'.toNat + b'.toNat + c'.toNat :=
  ⟨true, false, true, false, false, false, rfl, rfl, by decide⟩

/-- **The state of resolution, in bits.** Resolution of general 2-SAT lives among the subsets
of the patterns on two variables, so its whole state is a list of at most `1 + 2n + (2n)²`
bits; the subsets of all patterns over `n` variables number `2^(2^(2n))`. -/
theorem resolution_state_space (n : ℕ) :
    (width2 n).powerset.card ≤ 2 ^ (1 + 2 * n + (2 * n) ^ 2) ∧
      Fintype.card (Finset (Lits n)) = 2 ^ (2 ^ (2 * n)) := by
  classical
  refine ⟨?_, ?_⟩
  · rw [Finset.card_powerset]
    exact Nat.pow_le_pow_right (by norm_num) (two_sat_no_trace (n := n) ∅ (by simp)).1
  · rw [Fintype.card_finset, (three_sat_leaves_space).2 n]

/-- **Keeping a trace.** (i) The one-bit register discards the overflow, and the overflow is
what recovers the sum; a three-term sum needs a second overflow that reads the bit kept by the
first. (ii) The doubling step discards one bit; keeping it makes the step injective, and the
trace grows by one bit per step. (iii) Resolution of general 2-SAT needs no trace: it closes
within the polynomial universe of patterns on two variables, whose subsets are described by
at most `1 + 2n + (2n)²` bits, while patterns from three-variable constraints grow wider. -/
theorem trace_meaning :
    (∃ a b a' b' : Bool, xor a b = xor a' b' ∧ a.toNat + b.toNat ≠ a'.toNat + b'.toNat) ∧
    (∃ a b c a' b' c' : Bool, xor (xor a b) c = xor (xor a' b') c' ∧ (a && b) = (a' && b') ∧
      a.toNat + b.toNat + c.toNat ≠ a'.toNat + b'.toNat + c'.toNat) ∧
    (∀ K, 1 ≤ K → ((Finset.range (2 ^ K)).image (QE.Dyn.dbl K)).card = 2 ^ (K - 1) ∧
      Set.InjOn (traced K) {p : ℕ × ℕ | p.1 < 2 ^ K} ∧
      ∀ n k, k < 2 ^ K → ((traced K)^[n] (k, 0)).2 < 2 ^ n) ∧
    (∀ (n : ℕ) (s : Finset (Lits n)), s ⊆ width2 n →
      resStep (resStep^[(width2 n).card] s) = resStep^[(width2 n).card] s ∧
      resStep^[(width2 n).card] s ⊆ width2 n ∧
      (width2 n).powerset.card ≤ 2 ^ (1 + 2 * n + (2 * n) ^ 2)) ∧
    (resolvent (n := 5) {(0, true), (1, true), (2, true)} {(0, false), (3, true), (4, true)} 0).card
      = 4 :=
  ⟨register_trace_two, register_trace_three,
    fun K hK => ⟨dbl_image_card K hK, traced_injOn K hK, fun n k hk => trace_bits K hK n k hk⟩,
    fun n s hs => ⟨(two_sat_no_trace s hs).2.1, (two_sat_no_trace s hs).2.2,
      (resolution_state_space n).1⟩, resolvent_width_grows⟩

/-- Every round of 2-SAT resolution stays among the patterns on two variables. -/
theorem iter_width2 {n : ℕ} (s : Finset (Lits n)) (hs : s ⊆ width2 n) (k : ℕ) :
    resStep^[k] s ⊆ width2 n := by
  induction k with
  | zero => simpa using hs
  | succ k ih => rw [Function.iterate_succ_apply']; exact resStep_width2 _ ih

/-- One round of resolution produces at most `|s| + |s|² n` patterns. -/
theorem resStep_card {n : ℕ} (s : Finset (Lits n)) :
    (resStep s).card ≤ s.card + s.card * s.card * n := by
  classical
  unfold resStep
  refine (Finset.card_union_le _ _).trans (Nat.add_le_add_left ?_ _)
  refine Finset.card_image_le.trans ((Finset.card_filter_le _ _).trans ?_)
  simp [Finset.card_product, mul_assoc]

/-- **Resolution of 2-SAT in polynomial time needs no trace.** The procedure is the iteration
of one map on the current set of patterns, with no other memory. Every state it visits is a
subset of the at most `1 + 2n + (2n)²` patterns on two variables, each round produces at most
`|s| + |s|² n` patterns from the current state `s`, and from round `1 + 2n + (2n)²` on the
state no longer changes. -/
theorem two_sat_poly_no_trace {n : ℕ} (s : Finset (Lits n)) (hs : s ⊆ width2 n) :
    (width2 n).card ≤ 1 + 2 * n + (2 * n) ^ 2 ∧
    (∀ k, resStep^[k] s ⊆ width2 n ∧ (resStep^[k] s).card ≤ 1 + 2 * n + (2 * n) ^ 2) ∧
    (∀ t : Finset (Lits n), (resStep t).card ≤ t.card + t.card * t.card * n) ∧
    (∀ k, 1 + 2 * n + (2 * n) ^ 2 ≤ k →
      resStep^[k] s = resStep^[1 + 2 * n + (2 * n) ^ 2] s) := by
  obtain ⟨hc, hfix, -⟩ := two_sat_no_trace s hs
  have hstab : ∀ k, (width2 n).card ≤ k → resStep^[k] s = resStep^[(width2 n).card] s := by
    intro k hk
    obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hk
    rw [add_comm, Function.iterate_add_apply]
    exact Function.IsFixedPt.iterate hfix j
  refine ⟨hc, fun k => ⟨iter_width2 s hs k,
    (Finset.card_le_card (iter_width2 s hs k)).trans hc⟩, resStep_card, fun k hk => ?_⟩
  rw [hstab k (hc.trans hk), hstab _ hc]

/-! ### When the trace can be avoided: the patterns of a three-variable constraint

A constraint on three variables is a set of allowed patterns, one of `2^8 = 256`. Schaefer's
theorem says that a constraint language is solvable in polynomial time when all its relations
are `0`-valid, all `1`-valid, all closed under AND (Horn), all closed under OR (dual Horn), all
closed under majority (bijunctive, the 2-SAT case) or all closed under `x ⊕ y ⊕ z` (affine),
and NP-complete otherwise. Below the relation on three variables with bitmask `m` allows the
pattern `x` exactly when bit `x₀ + 2x₁ + 4x₂` of `m` is set; the classes are decided on the
bitmask and shown to agree with the closure properties of the set. -/

/-- The number of a pattern on three bits. -/
def code3 (x : Fin 3 → Bool) : ℕ := (x 0).toNat + 2 * (x 1).toNat + 4 * (x 2).toNat

/-- The pattern with a given number. -/
def decode3 (p : ℕ) : Fin 3 → Bool := fun i => p.testBit i

/-- The relation on three variables with bitmask `m`. -/
def relOf (m : ℕ) : Set (Fin 3 → Bool) := {x | m.testBit (code3 x) = true}

/-- Closure of a bitmask under a binary bitwise operation on pattern numbers. -/
def closedN2 (op : ℕ → ℕ → ℕ) (m : ℕ) : Bool :=
  (List.range 8).all fun p => (List.range 8).all fun q =>
    !(m.testBit p && m.testBit q) || m.testBit (op p q)

/-- Closure of a bitmask under a ternary bitwise operation on pattern numbers. -/
def closedN3 (op : ℕ → ℕ → ℕ → ℕ) (m : ℕ) : Bool :=
  (List.range 8).all fun p => (List.range 8).all fun q => (List.range 8).all fun r =>
    !(m.testBit p && m.testBit q && m.testBit r) || m.testBit (op p q r)

/-- Majority of pattern numbers, bit by bit. -/
def majN (p q r : ℕ) : ℕ := (p &&& q) ||| (p &&& r) ||| (q &&& r)

/-- Schaefer's six tractable classes, decided on the bitmask. -/
def schaeferN (m : ℕ) : Bool :=
  m.testBit 0 || m.testBit 7 || closedN2 (· &&& ·) m || closedN2 (· ||| ·) m ||
    closedN3 majN m || closedN3 (fun p q r => p ^^^ q ^^^ r) m

theorem code3_lt (x : Fin 3 → Bool) : code3 x < 8 := by revert x; decide

theorem code3_decode3 : ∀ p, p < 8 → code3 (decode3 p) = p := by decide

theorem code3_injective : Function.Injective code3 := by
  intro x y h; revert x y; decide

theorem closed2_iff (op : Bool → Bool → Bool) (opN : ℕ → ℕ → ℕ)
    (h : ∀ x y : Fin 3 → Bool, code3 (fun i => op (x i) (y i)) = opN (code3 x) (code3 y))
    (m : ℕ) :
    (∀ x ∈ relOf m, ∀ y ∈ relOf m, (fun i => op (x i) (y i)) ∈ relOf m) ↔
      closedN2 opN m = true := by
  simp only [closedN2, List.all_eq_true, List.mem_range, Bool.or_eq_true, Bool.not_eq_true',
    Bool.and_eq_false_iff, relOf, Set.mem_setOf_eq]
  constructor
  · intro H p hp q hq
    by_cases hb : m.testBit p = true ∧ m.testBit q = true
    · right
      have := H (decode3 p) (by rw [code3_decode3 p hp]; exact hb.1) (decode3 q)
        (by rw [code3_decode3 q hq]; exact hb.2)
      rwa [h, code3_decode3 p hp, code3_decode3 q hq] at this
    · left; simp only [not_and_or, Bool.not_eq_true] at hb; exact hb
  · intro H x hx y hy
    rcases H _ (code3_lt x) _ (code3_lt y) with h1 | h1
    · rcases h1 with h1 | h1 <;> simp_all
    · rwa [h]

theorem closed3_iff (op : Bool → Bool → Bool → Bool) (opN : ℕ → ℕ → ℕ → ℕ)
    (h : ∀ x y z : Fin 3 → Bool,
      code3 (fun i => op (x i) (y i) (z i)) = opN (code3 x) (code3 y) (code3 z)) (m : ℕ) :
    (∀ x ∈ relOf m, ∀ y ∈ relOf m, ∀ z ∈ relOf m, (fun i => op (x i) (y i) (z i)) ∈ relOf m) ↔
      closedN3 opN m = true := by
  simp only [closedN3, List.all_eq_true, List.mem_range, Bool.or_eq_true, Bool.not_eq_true',
    Bool.and_eq_false_iff, relOf, Set.mem_setOf_eq]
  constructor
  · intro H p hp q hq r hr
    by_cases hb : m.testBit p = true ∧ m.testBit q = true ∧ m.testBit r = true
    · right
      have := H (decode3 p) (by rw [code3_decode3 p hp]; exact hb.1) (decode3 q)
        (by rw [code3_decode3 q hq]; exact hb.2.1) (decode3 r)
        (by rw [code3_decode3 r hr]; exact hb.2.2)
      rwa [h, code3_decode3 p hp, code3_decode3 q hq, code3_decode3 r hr] at this
    · left; simp only [not_and_or, Bool.not_eq_true] at hb
      rcases hb with hb | hb | hb <;> simp_all
  · intro H x hx y hy z hz
    rcases H _ (code3_lt x) _ (code3_lt y) _ (code3_lt z) with h1 | h1
    · rcases h1 with (h1 | h1) | h1 <;> simp_all
    · rwa [h]

theorem code3_and (x y : Fin 3 → Bool) : code3 (fun i => x i && y i) = code3 x &&& code3 y := by
  revert x y; decide
theorem code3_or (x y : Fin 3 → Bool) : code3 (fun i => x i || y i) = code3 x ||| code3 y := by
  revert x y; decide
theorem code3_maj (x y z : Fin 3 → Bool) :
    code3 (majA x y z) = majN (code3 x) (code3 y) (code3 z) := by
  revert x y z; decide
theorem code3_xor (x y z : Fin 3 → Bool) :
    code3 (fun i => xor (xor (x i) (y i)) (z i)) = code3 x ^^^ code3 y ^^^ code3 z := by
  revert x y z; decide

/-- Schaefer's six classes for a set of patterns on three variables. -/
def Schaefer3 (R : Set (Fin 3 → Bool)) : Prop :=
  (fun _ => false) ∈ R ∨ (fun _ => true) ∈ R ∨
  (∀ x ∈ R, ∀ y ∈ R, (fun i => x i && y i) ∈ R) ∨
  (∀ x ∈ R, ∀ y ∈ R, (fun i => x i || y i) ∈ R) ∨ MajClosed R ∨
  (∀ x ∈ R, ∀ y ∈ R, ∀ z ∈ R, (fun i => xor (xor (x i) (y i)) (z i)) ∈ R)

/-- The bitmask decision is the semantic one. -/
theorem schaefer3_iff (m : ℕ) : Schaefer3 (relOf m) ↔ schaeferN m = true := by
  have h0 : (fun _ => false) ∈ relOf m ↔ m.testBit 0 = true := by
    simp only [relOf, Set.mem_setOf_eq]; rfl
  have h7 : (fun _ => true) ∈ relOf m ↔ m.testBit 7 = true := by
    simp only [relOf, Set.mem_setOf_eq]; rfl
  have hM : MajClosed (relOf m) ↔ closedN3 majN m = true := by
    rw [← closed3_iff maj majN code3_maj m]; rfl
  have hA := closed2_iff (fun a b => a && b) (· &&& ·) code3_and m
  have hO := closed2_iff (fun a b => a || b) (· ||| ·) code3_or m
  have hX := closed3_iff (fun a b c => xor (xor a b) c) (fun p q r => p ^^^ q ^^^ r) code3_xor m
  simp only [Schaefer3, schaeferN, Bool.or_eq_true]
  rw [h0, h7, hM, hA, hO, hX]; simp only [or_assoc]

/-- **Exactly fifteen of the 256 relations on three variables lie in none of Schaefer's
classes.** They are the relations whose constraint problem is NP-complete on its own. -/
theorem schaefer3_count :
    (List.range 256).filter (fun m => !schaeferN m) =
      [22, 30, 54, 62, 86, 94, 104, 106, 108, 110, 118, 120, 122, 124, 126] := by
  decide

/-- **One-in-three and not-all-equal are in no class.** -/
theorem oneInThree_nae_not_schaefer : ¬ Schaefer3 (relOf 22) ∧ ¬ Schaefer3 (relOf 126) := by
  rw [schaefer3_iff, schaefer3_iff]; decide

/-- **Every single three-variable clause is trivial on its own.** A clause forbids one
pattern, so it allows `000` or `111`: an instance of one sign pattern is satisfied by a
constant assignment. -/
theorem clause_alone_trivial : ∀ p, p < 8 → schaeferN (255 - 2 ^ p) = true := by decide

/-- **The clauses of 3-SAT together lie in no class.** For each of Schaefer's six closure
properties some three-variable clause (some single forbidden pattern) fails it: the language of
3-SAT is NP-complete, and no single shortcut operation preserves all its constraints. -/
theorem threeSAT_language_none :
    (∃ p < 8, (255 - 2 ^ p).testBit 0 = false) ∧ (∃ p < 8, (255 - 2 ^ p).testBit 7 = false) ∧
    (∃ p < 8, closedN2 (· &&& ·) (255 - 2 ^ p) = false) ∧
    (∃ p < 8, closedN2 (· ||| ·) (255 - 2 ^ p) = false) ∧
    (∃ p < 8, closedN3 majN (255 - 2 ^ p) = false) ∧
    (∃ p < 8, closedN3 (fun p q r => p ^^^ q ^^^ r) (255 - 2 ^ p) = false) := by
  decide


/-! ### The fraction of arrangements that admit no shortcut -/

/-- Closure of a relation on `k` variables (bitmask `m` over the `P = 2^k` pattern numbers)
under a binary bitwise operation. -/
def closedK2 (P : ℕ) (op : ℕ → ℕ → ℕ) (m : ℕ) : Bool :=
  (List.range P).all fun p => !(m.testBit p) || (List.range P).all fun q =>
    !(m.testBit q) || m.testBit (op p q)

/-- Closure under a ternary bitwise operation. -/
def closedK3 (P : ℕ) (op : ℕ → ℕ → ℕ → ℕ) (m : ℕ) : Bool :=
  (List.range P).all fun p => !(m.testBit p) || (List.range P).all fun q =>
    !(m.testBit q) || (List.range P).all fun r => !(m.testBit r) || m.testBit (op p q r)

/-- Schaefer's six classes for a relation on `k` variables, `P = 2^k`. -/
def schaeferK (P : ℕ) (m : ℕ) : Bool :=
  m.testBit 0 || m.testBit (P - 1) || closedK2 P (· &&& ·) m || closedK2 P (· ||| ·) m ||
    closedK3 P majN m || closedK3 P (fun p q r => p ^^^ q ^^^ r) m

/-- The number of relations on four variables with bitmask in `[a, a + n)` and no shortcut. -/
def cnt4 (a n : ℕ) : ℕ := ((List.range' a n).filter (fun m => !schaeferK 16 m)).length

theorem cnt4_add (a m n : ℕ) : cnt4 a (m + n) = cnt4 a m + cnt4 (a + m) n := by
  unfold cnt4
  rw [← List.length_append, ← List.filter_append]
  congr 2
  have := List.range'_append (s := a) (m := m) (n := n) (step := 1)
  simpa using this.symm

theorem cnt4_chunks (k : ℕ) :
    cnt4 0 (4096 * k) = ((List.range k).map (fun i => cnt4 (4096 * i) 4096)).sum := by
  induction k with
  | zero => simp [cnt4]
  | succ k ih =>
    rw [Nat.mul_succ, cnt4_add, ih, List.range_succ, List.map_append, List.sum_append]
    simp

theorem cnt4_c0 : cnt4 0 4096 = 1471 := by unfold cnt4; decide +kernel
theorem cnt4_c1 : cnt4 4096 4096 = 1867 := by unfold cnt4; decide +kernel
theorem cnt4_c2 : cnt4 8192 4096 = 1829 := by unfold cnt4; decide +kernel
theorem cnt4_c3 : cnt4 12288 4096 = 1868 := by unfold cnt4; decide +kernel
theorem cnt4_c4 : cnt4 16384 4096 = 1829 := by unfold cnt4; decide +kernel
theorem cnt4_c5 : cnt4 20480 4096 = 1868 := by unfold cnt4; decide +kernel
theorem cnt4_c6 : cnt4 24576 4096 = 2009 := by unfold cnt4; decide +kernel
theorem cnt4_c7 : cnt4 28672 4096 = 1973 := by unfold cnt4; decide +kernel
theorem cnt4_c8 : cnt4 32768 4096 = 0 := by unfold cnt4; decide +kernel
theorem cnt4_c9 : cnt4 36864 4096 = 0 := by unfold cnt4; decide +kernel
theorem cnt4_c10 : cnt4 40960 4096 = 0 := by unfold cnt4; decide +kernel
theorem cnt4_c11 : cnt4 45056 4096 = 0 := by unfold cnt4; decide +kernel
theorem cnt4_c12 : cnt4 49152 4096 = 0 := by unfold cnt4; decide +kernel
theorem cnt4_c13 : cnt4 53248 4096 = 0 := by unfold cnt4; decide +kernel
theorem cnt4_c14 : cnt4 57344 4096 = 0 := by unfold cnt4; decide +kernel
theorem cnt4_c15 : cnt4 61440 4096 = 0 := by unfold cnt4; decide +kernel

/-- **On four variables, 14 714 of the 65 536 relations admit no shortcut operation.**
Checked by the kernel in sixteen blocks of 4096 bitmasks. -/
theorem schaefer4_count :
    ((List.range 65536).filter (fun m => !schaeferK 16 m)).length = 14714 := by
  have h := cnt4_chunks 16
  simp only [List.range_succ, List.range_zero, List.nil_append, List.map_append, List.map_cons,
    List.map_nil, List.sum_append, List.sum_cons, List.sum_nil, Nat.reduceMul,
    cnt4_c0, cnt4_c1, cnt4_c2, cnt4_c3, cnt4_c4, cnt4_c5, cnt4_c6, cnt4_c7, cnt4_c8, cnt4_c9,
    cnt4_c10, cnt4_c11, cnt4_c12, cnt4_c13, cnt4_c14, cnt4_c15] at h
  rw [List.range_eq_range']
  exact h

/-- **On three variables, 15 of 256.** -/
theorem schaefer3_count_K :
    ((List.range 256).filter (fun m => !schaeferK 8 m)).length = 15 := by
  decide

/-- **On one and two variables, none.** -/
theorem schaefer12_count :
    ((List.range 4).filter (fun m => !schaeferK 2 m)).length = 0 ∧
      ((List.range 16).filter (fun m => !schaeferK 4 m)).length = 0 := by
  decide

/-- Schaefer's six classes for a set of patterns on `k` variables. -/
def SchaeferK {k : ℕ} (R : Set (Fin k → Bool)) : Prop :=
  (fun _ => false) ∈ R ∨ (fun _ => true) ∈ R ∨
  (∀ x ∈ R, ∀ y ∈ R, (fun i => x i && y i) ∈ R) ∨
  (∀ x ∈ R, ∀ y ∈ R, (fun i => x i || y i) ∈ R) ∨ MajClosed R ∨
  (∀ x ∈ R, ∀ y ∈ R, ∀ z ∈ R, (fun i => xor (xor (x i) (y i)) (z i)) ∈ R)

open Classical in
/-- **At most a quarter of all arrangements admit no shortcut, for every `k`.** A relation
that allows the all-zero or the all-one pattern is satisfied by a constant assignment; the
relations that allow neither are `2^(2^k − 2)` of the `2^(2^k)`. -/
theorem outside_le_quarter (k : ℕ) (hk : 1 ≤ k) :
    (Finset.univ.filter (fun R : Finset (Fin k → Bool) => ¬ SchaeferK (R : Set (Fin k → Bool)))).card
      ≤ 2 ^ (2 ^ k - 2) ∧ 2 ^ (2 ^ k - 2) * 4 = 2 ^ (2 ^ k) := by
  classical
  have hne : (fun _ : Fin k => false) ≠ (fun _ => true) := by
    intro h; have := congrFun h ⟨0, by omega⟩; simp at this
  have hcard : (Finset.univ \ ({(fun _ : Fin k => false), (fun _ : Fin k => true)} : Finset (Fin k → Bool))).card = 2 ^ k - 2 := by
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ, Finset.card_pair hne]
    simp
  have hpow : 2 ≤ 2 ^ k := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk
  refine ⟨?_, ?_⟩
  · rw [← hcard, ← Finset.card_powerset]
    apply Finset.card_le_card
    intro R hR
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, SchaeferK, not_or] at hR
    rw [Finset.mem_powerset]
    intro x hx
    simp only [Finset.mem_sdiff, Finset.mem_univ, Finset.mem_insert, Finset.mem_singleton,
      true_and]
    rintro (rfl | rfl)
    · exact hR.1 (by simpa using hx)
    · exact hR.2.1 (by simpa using hx)
  · rw [show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_add]; congr 1; omega

/-! ### Every arrangement of patterns on three variables -/

/-- **The table of clauses.** For every one of the eight clauses on three variables, the three
patterns next to its forbidden corner satisfy it and their majority is the forbidden corner. For
every one of the four clauses on two variables, the three allowed patterns have an allowed
majority. -/
theorem clause_table :
    (∀ s : Fin 3 → Bool,
      Function.update s 0 (!s 0) ≠ s ∧ Function.update s 1 (!s 1) ≠ s ∧
      Function.update s 2 (!s 2) ≠ s ∧
      majA (Function.update s 0 (!s 0)) (Function.update s 1 (!s 1))
        (Function.update s 2 (!s 2)) = s) ∧
    (∀ s x y z : Fin 2 → Bool, x ≠ s → y ≠ s → z ≠ s → majA x y z ≠ s) := by
  refine ⟨by decide, fun s x y z hx hy hz => ?_⟩
  rcases majA_two_mem x y z with h | h | h <;> rw [h] <;> assumption

/-- **A set of patterns on three variables is general 2-SAT exactly when it is closed under
majority.** If it is closed, it is the set of solutions of its three projections onto pairs of
variables: a pattern whose three pairs are each seen in some solution is the majority of those
three solutions. -/
theorem majClosed_iff_gen2 (R : Set (Fin 3 → Bool)) :
    MajClosed R ↔ ∃ I : GInst 3 2, {x | SatG I x} = R := by
  constructor
  · intro h
    let S : Fin 3 → Fin 3 → Set (Fin 2 → Bool) := fun i j => (fun r => r ∘ ![i, j]) '' R
    refine ⟨[(![0, 1], S 0 1), (![0, 2], S 0 2), (![1, 2], S 1 2)], ?_⟩
    ext x
    simp only [Set.mem_setOf_eq, SatG, List.mem_cons, List.not_mem_nil, or_false,
      forall_eq_or_imp, forall_eq]
    constructor
    · rintro ⟨⟨r, hr, e1⟩, ⟨t, ht, e2⟩, ⟨u, hu, e3⟩⟩
      dsimp only at e1 e2 e3
      have a0 := congrFun e1 0; have a1 := congrFun e1 1
      have b0 := congrFun e2 0; have b1 := congrFun e2 1
      have c0 := congrFun e3 0; have c1 := congrFun e3 1
      simp only [Function.comp_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.head_cons] at a0 a1 b0 b1 c0 c1
      have hm : majA r t u = x := by
        funext i
        simp only [majA]
        fin_cases i
        · show maj (r 0) (t 0) (u 0) = x 0
          rw [a0, b0]; generalize x 0 = p; generalize u 0 = q; cases p <;> cases q <;> rfl
        · show maj (r 1) (t 1) (u 1) = x 1
          rw [a1, c0]; generalize x 1 = p; generalize t 1 = q; cases p <;> cases q <;> rfl
        · show maj (r 2) (t 2) (u 2) = x 2
          rw [b1, c1]; generalize x 2 = p; generalize r 2 = q; cases p <;> cases q <;> rfl
      exact hm ▸ h r hr t ht u hu
    · intro hx; exact ⟨⟨x, hx, rfl⟩, ⟨x, hx, rfl⟩, ⟨x, hx, rfl⟩⟩
  · rintro ⟨I, rfl⟩; exact gen2_majClosed I

/-- **Placing a constraint on any three of `n` variables keeps the failure.** -/
theorem scope_not_majClosed {n : ℕ} (σ : Fin 3 → Fin n) (hσ : Function.Injective σ)
    {R : Set (Fin 3 → Bool)} (hR : ¬ MajClosed R) :
    ¬ MajClosed {x : Fin n → Bool | x ∘ σ ∈ R} := by
  intro h; apply hR
  intro a ha b hb c hc
  have e : ∀ a : Fin 3 → Bool, Function.extend σ a (fun _ => false) ∘ σ = a :=
    fun a => funext fun j => hσ.extend_apply a _ j
  have := h _ (show _ ∘ σ ∈ R by rw [e]; exact ha) _ (show _ ∘ σ ∈ R by rw [e]; exact hb)
    _ (show _ ∘ σ ∈ R by rw [e]; exact hc)
  simp only [Set.mem_setOf_eq] at this
  have hc' : majA (Function.extend σ a fun _ => false) (Function.extend σ b fun _ => false)
      (Function.extend σ c fun _ => false) ∘ σ = majA a b c := by
    funext j; simp only [Function.comp_apply, majA, hσ.extend_apply]
  rwa [hc'] at this

/-- **Of the 256 arrangements on three variables, 166 are closed under majority.** -/
theorem majClosed3_count : ((List.range 256).filter (closedN3 majN)).length = 166 := by
  decide +kernel

/-- **Every arrangement, every placement, every sign.** (i) A set of patterns on three variables
is the solution set of a general 2-SAT instance exactly when it is closed under majority, and
the bitmask check decides which; 166 of the 256 are, 90 are not. (ii) For each of the 90, no
general 2-SAT instance with any extra variables, read through any three of them, has its
solutions, and placed on any three distinct variables among `n` it stays not closed. (iii) Each
of the eight clauses, one per forbidden pattern, is among the 90. -/
theorem every_arrangement :
    (∀ R : Set (Fin 3 → Bool), MajClosed R ↔ ∃ I : GInst 3 2, {x | SatG I x} = R) ∧
    (∀ m : ℕ, MajClosed (relOf m) ↔ closedN3 majN m = true) ∧
    ((List.range 256).filter (closedN3 majN)).length = 166 ∧
    (∀ R : Set (Fin 3 → Bool), ¬ MajClosed R →
      ¬ ∃ (m : ℕ) (σ : Fin 3 → Fin m) (I : GInst m 2), (fun x => x ∘ σ) '' {x | SatG I x} = R) ∧
    (∀ (n : ℕ) (σ : Fin 3 → Fin n), Function.Injective σ → ∀ R : Set (Fin 3 → Bool),
      ¬ MajClosed R → ¬ MajClosed {x : Fin n → Bool | x ∘ σ ∈ R}) ∧
    (∀ s : Fin 3 → Bool, ¬ MajClosed {x | x ≠ s}) := by
  refine ⟨majClosed_iff_gen2, fun m => ?_, majClosed3_count, fun R hR => ?_,
    fun n σ hσ R hR => scope_not_majClosed σ hσ hR, fun s => forbid_not_majClosed le_rfl s⟩
  · rw [← closed3_iff maj majN code3_maj m]; rfl
  · rintro ⟨m, σ, I, hS⟩
    exact hR (hS ▸ proj_majClosed σ (gen2_majClosed I))

/-! ### The table of pairs: general 2-SAT needs no trace, general 3-SAT does -/

/-- An assignment *agrees on every pair* with a set `S` when each pair of its coordinates is
seen together in some member of `S`. -/
def PairConsistent {n : ℕ} (S : Set (Fin n → Bool)) (x : Fin n → Bool) : Prop :=
  ∀ i j, ∃ s ∈ S, s i = x i ∧ s j = x j

/-- The majority of three bits two of which equal `b` is `b`. -/
theorem maj_two_of {a b c d : Bool} (h : (a = d ∧ b = d) ∨ (a = d ∧ c = d) ∨ (b = d ∧ c = d)) :
    maj a b c = d := by
  revert h; cases a <;> cases b <;> cases c <;> cases d <;> decide

/-- **Majority rebuilds a solution from its pairs** (the case of majority of the theorem of
Baker and Pixley). If `S` is closed under majority and nonempty, every assignment that agrees on
every pair with `S` agrees on every set of coordinates with some member of `S`. -/
theorem majClosed_agree_on {n : ℕ} {S : Set (Fin n → Bool)} (h : MajClosed S) (hne : S.Nonempty)
    {x : Fin n → Bool} (hx : PairConsistent S x) :
    ∀ J : Finset (Fin n), ∃ s ∈ S, ∀ i ∈ J, s i = x i := by
  intro J
  induction' hJ : J.card using Nat.strong_induction_on with k ih generalizing J
  by_cases hk : k ≤ 2
  · -- at most two coordinates: a pair witness
    subst hJ
    rcases Nat.lt_or_ge J.card 1 with h0 | h1
    · obtain ⟨s, hs⟩ := hne
      refine ⟨s, hs, fun i hi => ?_⟩
      have h00 : J.card = 0 := by omega
      simp [Finset.card_eq_zero.mp h00] at hi
    · rcases Nat.lt_or_ge J.card 2 with h1' | h2
      · obtain ⟨i, rfl⟩ := Finset.card_eq_one.mp (show J.card = 1 by omega)
        obtain ⟨s, hs, hi, -⟩ := hx i i
        exact ⟨s, hs, fun j hj => by simp at hj; subst hj; exact hi⟩
      · obtain ⟨i, j, -, rfl⟩ := Finset.card_eq_two.mp (show J.card = 2 by omega)
        obtain ⟨s, hs, hi, hj⟩ := hx i j
        exact ⟨s, hs, fun l hl => by
          simp only [Finset.mem_insert, Finset.mem_singleton] at hl
          rcases hl with rfl | rfl <;> assumption⟩
  · -- three or more coordinates: majority of three witnesses on smaller sets
    push Not at hk
    obtain ⟨T, hTJ, hT⟩ := Finset.exists_subset_card_eq (s := J) (n := 3) (by omega)
    obtain ⟨a, b, c, hab, hac, hbc, rfl⟩ := Finset.card_eq_three.mp hT
    have ha : a ∈ J := hTJ (by simp)
    have hb : b ∈ J := hTJ (by simp)
    have hc : c ∈ J := hTJ (by simp)
    have hcard : ∀ y ∈ J, (J.erase y).card < k := fun y hy => by
      rw [Finset.card_erase_of_mem hy]; omega
    obtain ⟨s1, h1, e1⟩ := ih _ (hcard a ha) (J.erase a) rfl
    obtain ⟨s2, h2, e2⟩ := ih _ (hcard b hb) (J.erase b) rfl
    obtain ⟨s3, h3, e3⟩ := ih _ (hcard c hc) (J.erase c) rfl
    refine ⟨majA s1 s2 s3, h s1 h1 s2 h2 s3 h3, fun i hi => ?_⟩
    simp only [majA]
    apply maj_two_of
    by_cases hia : i = a
    · subst hia
      right; right
      exact ⟨e2 _ (Finset.mem_erase.mpr ⟨hab, hi⟩), e3 _ (Finset.mem_erase.mpr ⟨hac, hi⟩)⟩
    · by_cases hib : i = b
      · subst hib
        right; left
        exact ⟨e1 _ (Finset.mem_erase.mpr ⟨hia, hi⟩),
          e3 _ (Finset.mem_erase.mpr ⟨hbc, hi⟩)⟩
      · left
        exact ⟨e1 _ (Finset.mem_erase.mpr ⟨hia, hi⟩), e2 _ (Finset.mem_erase.mpr ⟨hib, hi⟩)⟩

/-- The general 2-SAT instance of all pair projections of `S`. -/
def pairInst {n : ℕ} (S : Set (Fin n → Bool)) : GInst n 2 :=
  ((List.finRange n).product (List.finRange n)).map
    fun ij => (![ij.1, ij.2], (fun r => r ∘ ![ij.1, ij.2]) '' S)

theorem satG_pairInst {n : ℕ} (S : Set (Fin n → Bool)) (x : Fin n → Bool) :
    SatG (pairInst S) x ↔ PairConsistent S x := by
  unfold SatG pairInst PairConsistent
  constructor
  · intro H i j
    obtain ⟨s, hs, e⟩ := H _ (List.mem_map.2 ⟨(i, j),
      List.mem_product.2 ⟨List.mem_finRange _, List.mem_finRange _⟩, rfl⟩)
    exact ⟨s, hs, by simpa using congrFun e 0, by simpa using congrFun e 1⟩
  · intro H c hc
    obtain ⟨⟨i, j⟩, -, rfl⟩ := List.mem_map.1 hc
    obtain ⟨s, hs, hi, hj⟩ := H i j
    refine ⟨s, hs, funext fun t => ?_⟩
    fin_cases t <;> simp [hi, hj]

/-- **General 2-SAT is decided by its table of pairs.** A nonempty set of assignments on any
number of variables is closed under majority exactly when it contains every assignment that
agrees with it on every pair of variables, that is, exactly when it is the solution set of the
general 2-SAT instance of its pair projections. -/
theorem majClosed_iff_pairs {n : ℕ} (S : Set (Fin n → Bool)) (hne : S.Nonempty) :
    MajClosed S ↔ ∀ x, PairConsistent S x → x ∈ S := by
  constructor
  · intro h x hx
    obtain ⟨s, hs, e⟩ := majClosed_agree_on h hne hx Finset.univ
    have : s = x := funext fun i => e i (Finset.mem_univ i)
    exact this ▸ hs
  · intro H
    have : {x | SatG (pairInst S) x} = S := by
      ext x
      simp only [Set.mem_setOf_eq, satG_pairInst]
      exact ⟨H x, fun hx i j => ⟨x, hx, rfl, rfl⟩⟩
    rw [← this]; exact gen2_majClosed _

/-- **A set not closed under majority has a phantom.** Some assignment agrees with it on every
pair of variables and is still not in it: the table of pairs cannot exclude it, and a record on
more than two variables at once, a trace, is needed. -/
theorem phantom_of_not_majClosed {n : ℕ} {S : Set (Fin n → Bool)} (h : ¬ MajClosed S) :
    ∃ x, PairConsistent S x ∧ x ∉ S := by
  have hne : S.Nonempty := by
    by_contra he
    exact h fun x hx => absurd ⟨x, hx⟩ he
  by_contra hc
  push Not at hc
  exact h ((majClosed_iff_pairs S hne).2 hc)

/-! ### All constraints on two and three variables, up to renaming and negation -/

/-- Rename and negate the coordinates of a pattern number on `k` bits. -/
def permNegK (k : ℕ) (π : List ℕ) (t p : ℕ) : ℕ :=
  (List.range k).foldl (fun acc i => acc + (xor (p.testBit (π.getD i 0)) (t.testBit i)).toNat * 2 ^ i) 0

/-- Apply a map of pattern numbers to a bitmask on `P` patterns. -/
def tmaskK (P : ℕ) (f : ℕ → ℕ) (m : ℕ) : ℕ :=
  (List.range P).foldl (fun acc p => if m.testBit p then acc + 2 ^ f p else acc) 0

/-- The least bitmask in the class of `m` under renaming and negating variables. -/
def canonK (k : ℕ) (perms : List (List ℕ)) (m : ℕ) : ℕ :=
  ((perms.product (List.range (2 ^ k))).map fun πt => tmaskK (2 ^ k) (permNegK k πt.1 πt.2) m).foldl
    min (2 ^ (2 ^ k))

/-- The six permutations of three coordinates. -/
def perms3 : List (List ℕ) := [[0,1,2],[0,2,1],[1,0,2],[1,2,0],[2,0,1],[2,1,0]]

/-- **The sixteen constraints on two variables fall into six classes**, all closed under
majority. -/
theorem table2 :
    (List.range 16).all (fun m => [0, 1, 3, 6, 7, 15].contains (canonK 2 [[0,1],[1,0]] m)) ∧
    [0, 1, 3, 6, 7, 15].all (fun r => canonK 2 [[0,1],[1,0]] r = r) ∧
    [0, 1, 3, 6, 7, 15].all (closedN3 majN) ∧
    [0, 1, 3, 6, 7, 15].map (fun r => ((List.range 16).filter
      fun m => canonK 2 [[0,1],[1,0]] m = r).length) = [1, 4, 4, 2, 4, 1] := by
  decide +kernel

/-- **The 256 constraints on three variables fall into 22 classes.** Listed with their sizes
and whether they are closed under majority: 14 classes (166 constraints) are, 8 classes (90
constraints) are not. -/
theorem table3 :
    (List.range 256).all (fun m =>
      [0, 1, 3, 6, 7, 15, 22, 23, 24, 25, 27, 30, 31, 60, 61, 63, 105, 107, 111, 126, 127, 255].contains
        (canonK 3 perms3 m)) ∧
    [0, 1, 3, 6, 7, 15, 22, 23, 24, 25, 27, 30, 31, 60, 61, 63, 105, 107, 111, 126, 127, 255].all
      (fun r => canonK 3 perms3 r = r) ∧
    [0, 1, 3, 6, 7, 15, 22, 23, 24, 25, 27, 30, 31, 60, 61, 63, 105, 107, 111, 126, 127, 255].map
      (fun r => ((List.range 256).filter fun m => canonK 3 perms3 m = r).length) =
      [1, 8, 12, 12, 24, 6, 8, 8, 4, 24, 24, 24, 24, 6, 24, 12, 2, 8, 12, 4, 8, 1] ∧
    [0, 1, 3, 6, 7, 15, 22, 23, 24, 25, 27, 30, 31, 60, 61, 63, 105, 107, 111, 126, 127, 255].map
      (closedN3 majN) =
      [true, true, true, true, true, true, false, true, true, true, true, false, true, true,
        false, true, false, false, false, false, false, true] := by
  decide +kernel

/-- Pattern `p` agrees with some allowed pattern of `m` on the pair of coordinates `i, j`. -/
def pairSeen (m p i j : ℕ) : Bool :=
  (List.range 8).any fun q => m.testBit q && (q.testBit i == p.testBit i) && (q.testBit j == p.testBit j)

/-- **The phantoms of the table.** For each of the eight classes not closed under majority, the
listed pattern is forbidden and agrees with an allowed pattern on every pair of variables; and
the constraints "at most one" and "exactly one" have the same table of pairs. -/
theorem table3_phantoms :
    [(22, 0), (30, 0), (61, 1), (105, 1), (107, 2), (111, 4), (126, 0), (127, 7)].all
      (fun rp => !rp.1.testBit rp.2 && pairSeen rp.1 rp.2 0 1 && pairSeen rp.1 rp.2 0 2 &&
        pairSeen rp.1 rp.2 1 2) ∧
    (List.range 8).all (fun p => [(0,1),(0,2),(1,2)].all fun ij =>
      pairSeen 22 p ij.1 ij.2 == pairSeen 23 p ij.1 ij.2) := by
  decide

/-- The solutions of *exactly one of `x₀, x₁, x₂`*. -/
def exactlyOneSet : Set (Fin 3 → Bool) :=
  {x | (x 0).toNat + (x 1).toNat + (x 2).toNat = 1}

/-- **Exactly one is not closed under majority.** `100`, `010`, `001` satisfy it and their
majority `000` does not. No general 2-SAT instance, with any extra variables read through any
three of them, has its solutions. -/
theorem exactlyOne_not_gen2 :
    ¬ MajClosed exactlyOneSet ∧
      ¬ ∃ (m : ℕ) (σ : Fin 3 → Fin m) (I : GInst m 2),
        (fun x => x ∘ σ) '' {x | SatG I x} = exactlyOneSet := by
  have h : ¬ MajClosed exactlyOneSet := by
    intro h
    have := h ![true, false, false] (by simp [exactlyOneSet]) ![false, true, false]
      (by simp [exactlyOneSet]) ![false, false, true] (by simp [exactlyOneSet])
    simp [exactlyOneSet, majA, maj] at this
  refine ⟨h, ?_⟩
  rintro ⟨m, σ, I, hS⟩
  exact h (hS ▸ proj_majClosed σ (gen2_majClosed I))

end GranularComplexity

end QE.Comp
