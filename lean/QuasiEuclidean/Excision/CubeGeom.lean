-- SPDX-License-Identifier: MIT
-- Copyright 2026 Metere Industries, Inc. Author: Alfredo Metere.
-- Quasi-Euclidean Granular Geometry. Any derivative work must carry this notice:
--   This work is derivative of the Quasi-Euclidean Granular Geometry book
--   authored by Alfredo Metere. Copyright 2026 Metere Industries, Inc.
--   All rights reserved
-- See LICENSE.md and NOTICE.

import QuasiEuclidean.Excision.CubicalStar

/-!
# Carrier cubes and open stars in `ℝⁿ`

Book: Proposition `prop:topology-homology-singular` (Chapter 10), infrastructure.

* Every point `x ∈ ℝⁿ` lies in the relative interior of a unique elementary cube, its
  *carrier* `cc x = (⌊x⌋, {j | xⱼ ∉ ℤ})`; a closed elementary cube contains `x` iff it
  contains `cc x` as a face (`cc_le`), so `cc x ∈ X` for `x ∈ |X|` (`cc_mem`).
* The open star of a lattice point `v` in the cubical structure of `ℝⁿ` is the open box
  `ostar v = {x | ‖x - v‖_∞ < 1}`: `x ∈ ostar v` iff `v` is a vertex of `cc x`
  (`vert_le_cc`).  The open stars form an open cover of `ℝⁿ`.
* For a singular simplex `s` with image in `ostar v`, its cubical carrier `Kcar s` (all faces
  of carriers of its points) is a cubical star about `v` (`isStarAt_Kcar`), and its
  geometric carrier `Rcar s` (the union of the carriers) is star-convex about `v`
  (`starConvex_Rcar`).

No measure theory is used.
-/

namespace QE.Excision

open Finsupp QE.Cubical QE.CubicalSingular

noncomputable section

variable {n : ℕ}

/-! ## The face order -/

theorem CLe.refl (c : Cube n) : CLe c c := fun _ => ⟨le_rfl, le_rfl⟩

theorem CLe.trans {a b c : Cube n} (h1 : CLe a b) (h2 : CLe b c) : CLe a c :=
  fun k => ⟨(h2 k).1.trans (h1 k).1, (h1 k).2.trans (h2 k).2⟩

theorem cubeSet_mono {e c : Cube n} (h : CLe e c) : cubeSet e ⊆ cubeSet c := by
  intro x hx
  simp only [cubeSet, Set.mem_univ_pi, Set.mem_Icc] at hx ⊢
  intro k
  have h1 : (c.1 k : ℝ) ≤ e.1 k := by exact_mod_cast (h k).1
  have h2 : (top e k : ℝ) ≤ top c k := by exact_mod_cast (h k).2
  exact ⟨h1.trans (hx k).1, (hx k).2.trans h2⟩

/-- A face (in the order `CLe`) of a cube of a complex is in the complex. -/
theorem mem_of_CLe {X : Finset (Cube n)} (hX : IsComplex X) :
    ∀ m, ∀ c ∈ X, c.2.card = m → ∀ e, CLe e c → e ∈ X := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro c hc hcm e hle
    by_cases hcard : c.2.card ≤ e.2.card
    · rw [hle.eq hcard]; exact hc
    · obtain ⟨j, hjc, hje⟩ : ∃ j ∈ c.2, j ∉ e.2 := by
        by_contra hne
        push Not at hne
        exact hcard (Finset.card_le_card hne)
      obtain ⟨s, hs, hle'⟩ := hle.face hjc hje
      have hc' := facet_mem hX hc hjc hs
      exact ih _ (by rw [Finset.card_erase_of_mem hjc]; omega) _ hc' rfl e hle'

theorem mem_of_CLe' {X : Finset (Cube n)} (hX : IsComplex X) {c e : Cube n} (hc : c ∈ X)
    (h : CLe e c) : e ∈ X := mem_of_CLe hX _ c hc rfl e h

/-! ## Carrier cubes -/

/-- The carrier cube of a point: the elementary cube containing it in its relative interior. -/
def cc (x : Fin n → ℝ) : Cube n :=
  (fun j => ⌊x j⌋, Finset.univ.filter fun j => (⌊x j⌋ : ℝ) ≠ x j)

theorem mem_cc (x : Fin n → ℝ) : x ∈ cubeSet (cc x) := by
  rw [mem_cubeSet_iff]
  intro k
  simp only [cc, Finset.mem_filter, Finset.mem_univ, true_and]
  refine ⟨Int.floor_le _, ?_⟩
  split_ifs with h
  · exact (Int.lt_floor_add_one _).le
  · push Not at h; rw [h]; simp

theorem cc_le {x : Fin n → ℝ} {c : Cube n} (hx : x ∈ cubeSet c) : CLe (cc x) c := by
  rw [mem_cubeSet_iff] at hx
  intro k
  have hk := hx k
  simp only [cc, top, Finset.mem_filter, Finset.mem_univ, true_and]
  have h1 : c.1 k ≤ ⌊x k⌋ := Int.le_floor.mpr hk.1
  refine ⟨h1, ?_⟩
  by_cases hint : (⌊x k⌋ : ℝ) ≠ x k
  · rw [ite_eq_left hint]
    have hlt : (⌊x k⌋ : ℝ) < x k := lt_of_le_of_ne (Int.floor_le _) hint
    by_cases hkc : k ∈ c.2
    · rw [ite_eq_left hkc]
      have h2 : x k ≤ (c.1 k : ℝ) + 1 := by simpa [hkc] using hk.2
      have : ⌊x k⌋ < c.1 k + 1 := by
        have : (⌊x k⌋ : ℝ) < c.1 k + 1 := lt_of_lt_of_le hlt h2
        exact_mod_cast this
      omega
    · rw [ite_eq_right hkc]
      have h2 : x k ≤ (c.1 k : ℝ) := by simpa [hkc] using hk.2
      have : (⌊x k⌋ : ℝ) < c.1 k := lt_of_lt_of_le hlt h2
      have : ⌊x k⌋ < c.1 k := by exact_mod_cast this
      omega
  · push Not at hint
    rw [ite_eq_right (not_not.mpr hint), add_zero]
    have h2 : x k ≤ (c.1 k : ℝ) + if k ∈ c.2 then 1 else 0 := hk.2
    rw [← hint] at h2
    have : (⌊x k⌋ : ℝ) ≤ ((c.1 k + if k ∈ c.2 then 1 else 0 : ℤ) : ℝ) := by
      push_cast; split_ifs at h2 ⊢ <;> simpa using h2
    exact_mod_cast this

theorem cc_mem {X : Finset (Cube n)} (hX : IsComplex X) {x : Fin n → ℝ}
    (hx : x ∈ realisation X) : cc x ∈ X := by
  obtain ⟨c, hc, hxc⟩ := Set.mem_iUnion₂.mp hx
  exact mem_of_CLe' hX hc (cc_le hxc)

theorem cubeSet_cc_subset {X : Finset (Cube n)} (hX : IsComplex X) {x : Fin n → ℝ}
    (hx : x ∈ realisation X) : cubeSet (cc x) ⊆ realisation X :=
  fun _ hy => Set.mem_biUnion (cc_mem hX hx) hy

/-! ## Open stars of lattice points -/

/-- The open star of the lattice point `v`: the open unit box around it. -/
def ostar (v : Fin n → ℤ) : Set (Fin n → ℝ) := {x | ∀ j, |x j - v j| < 1}

theorem isOpen_ostar (v : Fin n → ℤ) : IsOpen (ostar v) := by
  have : ostar v = ⋂ j, {x : Fin n → ℝ | |x j - v j| < 1} := by ext; simp [ostar]
  rw [this]
  exact isOpen_iInter_of_finite fun j =>
    isOpen_lt (continuous_abs.comp ((continuous_apply j).sub continuous_const)) continuous_const

theorem mem_ostar_floor (x : Fin n → ℝ) : x ∈ ostar (fun j => ⌊x j⌋) := by
  intro j
  have h1 := Int.floor_le (x j)
  have h2 := Int.lt_floor_add_one (x j)
  rw [abs_lt]; constructor <;> linarith

/-- `x ∈ ostar v` iff `v` is a vertex of the carrier of `x` (the direction used here). -/
theorem vert_le_cc {v : Fin n → ℤ} {x : Fin n → ℝ} (hx : x ∈ ostar v) :
    CLe ((v, ∅) : Cube n) (cc x) := by
  intro k
  have hk := abs_lt.mp (hx k)
  simp only [cc, top, Finset.notMem_empty, ite_false, add_zero, Finset.mem_filter,
    Finset.mem_univ, true_and]
  have hf1 := Int.floor_le (x k)
  have hf2 := Int.lt_floor_add_one (x k)
  constructor
  · have : (⌊x k⌋ : ℝ) < v k + 1 := by linarith
    have : ⌊x k⌋ < v k + 1 := by exact_mod_cast this
    omega
  · split_ifs with h
    · have : (v k : ℝ) < ⌊x k⌋ + 2 := by linarith
      have : v k < ⌊x k⌋ + 2 := by exact_mod_cast this
      omega
    · push Not at h
      have : (v k : ℝ) < ⌊x k⌋ + 1 := by linarith
      have : v k < ⌊x k⌋ + 1 := by exact_mod_cast this
      omega

/-- The open stars of all lattice points. -/
def ostars (n : ℕ) : Set (Set (Fin n → ℝ)) := Set.range (ostar (n := n))

theorem isOpen_ostars : ∀ U ∈ ostars n, IsOpen U := by
  rintro _ ⟨v, rfl⟩; exact isOpen_ostar v

theorem cover_ostars (A : Set (Fin n → ℝ)) : A ⊆ ⋃₀ ostars n :=
  fun x _ => ⟨_, ⟨_, rfl⟩, mem_ostar_floor x⟩

/-! ## Stars -/

theorem isStarAt_of {K : Set (Cube n)} {v : Fin n → ℤ}
    (h : ∀ e ∈ K, ∃ c, CLe ((v, ∅) : Cube n) c ∧ CLe e c ∧ ∀ e', CLe e' c → e' ∈ K) :
    IsStarAt K v := by
  intro e he
  obtain ⟨c, hvc, hec, hK⟩ := h e he
  refine ⟨fun j => ?_, fun i hi => ⟨hK _ fun l => ?_, hK _ fun l => ?_⟩,
    fun i hi hne => hK _ fun l => ?_, fun i hi => hK _ fun l => ?_⟩
  · have h1 := hvc j; have h2 := hec j
    simp only [top, Finset.notMem_empty, ite_false, add_zero] at h1 h2
    constructor
    · intro hj; simp only [hj, ite_true] at h2; split_ifs at h1 h2 <;> omega
    · intro hj; simp only [hj, ite_false, add_zero] at h2; split_ifs at h1 h2 <;> omega
  all_goals
    have h1 := hvc l; have h2 := hec l; have h3 := hvc i; have h4 := hec i
    simp only [top, Finset.notMem_empty, ite_false, add_zero] at h1 h2 h3 h4 ⊢
    by_cases hl : l = i
    · subst hl
      simp_all [unit_apply, Finset.mem_erase, Finset.mem_insert]
      all_goals (split_ifs at * <;> omega)
    · simp_all [unit_apply, Finset.mem_erase, Finset.mem_insert]

end

end QE.Excision
