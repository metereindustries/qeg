-- SPDX-License-Identifier: MIT
-- Copyright 2026 Metere Industries, Inc. Author: Alfredo Metere.
-- Quasi-Euclidean Granular Geometry. Any derivative work must carry this notice:
--   This work is derivative of the Quasi-Euclidean Granular Geometry book
--   authored by Alfredo Metere. Copyright 2026 Metere Industries, Inc.
--   All rights reserved
-- See LICENSE.md and NOTICE.

import QuasiEuclidean.SaturationHomologyInfra
import QuasiEuclidean.Ch10c_CubicalInfra

/-!
# Cubical versus singular homology: elementary collapses

Book: Proposition `prop:topology-homology-singular` (Chapter 10).

An elementary collapse `X ↦ X ∖ {σ, τ}` of a finite cubical complex (`σ` a free primary
face of `τ`) leaves the cubical homology unchanged (`QE.Cubical.homology_collapse`).  We
show that it also leaves the singular homology of the realisation unchanged, in every
degree: `|X ∖ {σ, τ}|` is a deformation retract of `|X|`.

The retraction pushes the cube `τ` onto the union `Λ` of its facets other than `σ`, by
radial projection from a point `p` beyond `σ`.  In coordinates (with `h ∈ [0,1]` the height
of a point of `τ` measured from the facet opposite to `σ`, and `y_j = 2(x_j - a_j) - 1 ∈
[-1,1]` the centred coordinates in the other free directions) the projection is the explicit
map `ρ(x) = p + m(x)⁻¹ (x - p)` with `m(x) = max(‖y‖_∞, 1 - h/2, 1/2)`, which is
continuous because `m ≥ 1/2`.  On `τ` it lands in `Λ` and fixes `Λ` pointwise, and
`|X ∖ {σ, τ}| ∩ τ ⊆ Λ` because a cube of `X` meeting the relative interior of `σ ∪ τ`
contains `σ` and hence, by freeness of `σ`, is `σ` or `τ`.  The straight-line homotopy from
the identity to the retraction stays in `|X|` (cubes are convex), and Mathlib's homotopy
invariance of singular homology gives the isomorphism.

Consequences: for every complex `X` that collapses onto a subcomplex `Y`, cubical and
singular homology agree for `X` in degree `k` iff they agree for `Y` in degree `k`; in
particular they agree in every degree for every collapsible complex.  (Degree `0` holds for
every complex: `QE.CubicalSingular.homology_zero_singular`.)  The general case, in every
degree and for every complex, is `QE.Excision.comparison` (SingularExcision.lean), which
builds barycentric subdivision and the small-simplices theorem.

No measure theory is used.
-/

namespace QE.CubicalSingular

open Finset QE.Cubical CategoryTheory AlgebraicTopology

variable {n : ℕ}

/-! ## Coordinates of cubes -/

theorem mem_cubeSet_iff (c : Cube n) (x : Fin n → ℝ) :
    x ∈ cubeSet c ↔ ∀ k, (c.1 k : ℝ) ≤ x k ∧ x k ≤ c.1 k + if k ∈ c.2 then 1 else 0 := by
  simp only [cubeSet, top, Set.mem_univ_pi, Set.mem_Icc]
  refine forall_congr' fun k => ?_
  split_ifs <;> push_cast <;> rfl

theorem shift_apply (a : Fin n → ℤ) (s : ℤ) (j k : Fin n) :
    (a + s • unit j) k = a k + if k = j then s else 0 := by
  simp [unit_apply]

/-- A primary face of a cube of a complex is in the complex. -/
theorem facet_mem {X : Finset (Cube n)} (hX : IsComplex X) {a : Fin n → ℤ} {S : Finset (Fin n)}
    (h : (a, S) ∈ X) {j : Fin n} (hj : j ∈ S) {s : ℤ} (hs : s = 0 ∨ s = 1) :
    (a + s • unit j, S.erase j) ∈ X := by
  rcases hs with rfl | rfl
  · simpa using (hX _ h j hj).2
  · simpa using (hX _ h j hj).1

theorem facet_ne {a : Fin n → ℤ} {S : Finset (Fin n)} {j : Fin n} (hj : j ∈ S) (s : ℤ) :
    ((a + s • unit j, S.erase j) : Cube n) ≠ (a, S) := by
  intro e
  have := congrArg (fun c : Cube n => c.2.card) e
  simp only [card_erase_of_mem hj] at this
  have := card_pos.mpr ⟨j, hj⟩
  omega

/-- A primary face lies in the cube. -/
theorem cubeSet_facet_subset {a : Fin n → ℤ} {S : Finset (Fin n)} {j : Fin n} (hj : j ∈ S)
    {s : ℤ} (hs : s = 0 ∨ s = 1) :
    cubeSet ((a + s • unit j, S.erase j) : Cube n) ⊆ cubeSet (a, S) := by
  intro x hx
  rw [mem_cubeSet_iff] at hx ⊢
  intro k
  have h := hx k
  simp only [shift_apply, mem_erase] at h ⊢
  by_cases hk : k = j
  · subst hk
    simp only [ite_true, hj, ne_eq, not_true_eq_false, false_and, ite_false] at h ⊢
    rcases hs with rfl | rfl <;> push_cast at h ⊢ <;> constructor <;> linarith [h.1, h.2]
  · simp only [hk, ite_false, add_zero, ne_eq, not_false_eq_true, true_and] at h ⊢
    exact h

/-- A point of `τ` on a facet lies in the facet. -/
theorem mem_facet {a : Fin n → ℤ} {S : Finset (Fin n)} {j : Fin n} {s : ℤ}
    {x : Fin n → ℝ} (hx : x ∈ cubeSet ((a, S) : Cube n)) (hxj : x j = a j + s) :
    x ∈ cubeSet ((a + s • unit j, S.erase j) : Cube n) := by
  rw [mem_cubeSet_iff] at hx ⊢
  intro k
  have h := hx k
  simp only [shift_apply, mem_erase] at h ⊢
  by_cases hk : k = j
  · subst hk
    simp only [ite_true, ne_eq, not_true_eq_false, false_and, ite_false]
    push_cast
    constructor <;> linarith
  · simp only [hk, ite_false, add_zero, ne_eq, not_false_eq_true, true_and] at h ⊢
    exact h

/-! ## The face order -/

/-- `ρ ≤ c`: every coordinate interval of `ρ` lies in the corresponding one of `c`. -/
def CLe (ρ c : Cube n) : Prop := ∀ k, c.1 k ≤ ρ.1 k ∧ top ρ k ≤ top c k

theorem CLe.subset {ρ c : Cube n} (h : CLe ρ c) : ρ.2 ⊆ c.2 := by
  intro j hj
  by_contra hjc
  have := h j
  simp only [top, hj, hjc, ite_true, ite_false] at this
  omega

theorem CLe.eq {ρ c : Cube n} (h : CLe ρ c) (hcard : c.2.card ≤ ρ.2.card) : ρ = c := by
  have hS : ρ.2 = c.2 := eq_of_subset_of_card_le h.subset hcard
  refine Prod.ext (funext fun k => ?_) hS
  have := h k
  simp only [top, hS] at this
  split_ifs at this <;> omega

theorem CLe.face {ρ c : Cube n} (h : CLe ρ c) {j : Fin n} (hj : j ∈ c.2) (hjr : j ∉ ρ.2) :
    ∃ s : ℤ, (s = 0 ∨ s = 1) ∧ CLe ρ (c.1 + s • unit j, c.2.erase j) := by
  have hj' := h j
  simp only [top, hj, hjr, ite_true, ite_false] at hj'
  refine ⟨ρ.1 j - c.1 j, by omega, fun k => ?_⟩
  have hk := h k
  simp only [top, shift_apply, mem_erase] at hk ⊢
  by_cases hkj : k = j
  · subst hkj; simp only [ite_true, ne_eq, not_true_eq_false, false_and, ite_false, hjr]; omega
  · simp only [hkj, ite_false, add_zero, ne_eq, not_false_eq_true, true_and]
    exact hk

/-- **A cube of `X` above a free face `σ` of `τ` is `σ` or `τ`.** -/
theorem eq_of_cle {X : Finset (Cube n)} (hX : IsComplex X) {σ τ : Cube n}
    (hστ : IsFace σ τ) (hfree : ∀ c ∈ X, IsFace σ c → c = τ) :
    ∀ m, ∀ c ∈ X, c.2.card = m → CLe σ c → c = σ ∨ c = τ := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro c hc hcm hle
    by_cases hcard : c.2.card ≤ σ.2.card
    · exact Or.inl (hle.eq hcard).symm
    · obtain ⟨j, hjc, hjσ⟩ : ∃ j ∈ c.2, j ∉ σ.2 := by
        by_contra hne
        push Not at hne
        exact hcard (card_le_card hne)
      obtain ⟨s, hs, hle'⟩ := hle.face hjc hjσ
      have hc'X : (c.1 + s • unit j, c.2.erase j) ∈ X := facet_mem hX hc hjc hs
      have hcard' : (c.2.erase j).card < m := by rw [card_erase_of_mem hjc]; omega
      have hface : IsFace (c.1 + s • unit j, c.2.erase j) c := ⟨j, hjc, s, hs, rfl⟩
      rcases ih _ hcard' _ hc'X rfl hle' with h | h
      · rw [h] at hface
        exact Or.inr (hfree c hc hface)
      · rw [h] at hface
        exact absurd hface (not_isFace_coface hX hστ hfree hc)

/-! ## The radial projection of `τ` onto `Λ` -/

noncomputable section Proj

variable (a : Fin n → ℤ) (S : Finset (Fin n)) (i : Fin n) (t : ℤ)

/-- The value of the `i`-th coordinate on the facet opposite to `σ`. -/
def bot : ℝ := a i + (1 - t)

/-- The orientation `±1` of the collapse direction. -/
def dir : ℝ := 2 * t - 1

/-- The height of `x` above the facet opposite to `σ` (`σ` is at height `1`). -/
def hgt (x : Fin n → ℝ) : ℝ := dir t * (x i - bot a i t)

/-- The centre of projection: above the centre of `σ`, at height `2`. -/
def ctr : Fin n → ℝ := fun j =>
  if j = i then bot a i t + 2 * dir t else if j ∈ S then a j + 1 / 2 else a j

/-- Centred coordinates in the free directions other than `i`. -/
def yv (x : Fin n → ℝ) : Fin n → ℝ := fun j =>
  if j ∈ S.erase i then 2 * (x j - a j) - 1 else 0

/-- The scaling factor `m = max(‖y‖, 1 - h/2, 1/2)`. -/
def mm (x : Fin n → ℝ) : ℝ := max ‖yv a S i x‖ (max (1 - hgt a i t x / 2) (1 / 2))

/-- The radial projection `ρ(x) = p + m(x)⁻¹ (x - p)`. -/
def rho (x : Fin n → ℝ) : Fin n → ℝ := ctr a S i t + (mm a S i t x)⁻¹ • (x - ctr a S i t)

/-- The relative interior of `σ ∪ τ` inside `τ`: no other facet constraint is active. -/
def Inner (x : Fin n → ℝ) : Prop := (∀ j ∈ S.erase i, |yv a S i x j| < 1) ∧ 0 < hgt a i t x

variable {a S i t}

theorem half_le_mm (x : Fin n → ℝ) : 1 / 2 ≤ mm a S i t x :=
  le_max_of_le_right (le_max_right _ _)

theorem mm_pos (x : Fin n → ℝ) : 0 < mm a S i t x :=
  lt_of_lt_of_le (by norm_num) (half_le_mm x)

theorem continuous_mm : Continuous (mm a S i t) := by
  have hy : Continuous (yv a S i) := continuous_pi fun j => by
    unfold yv; split_ifs <;> fun_prop
  unfold mm hgt
  fun_prop

theorem continuous_rho : Continuous (rho a S i t) := by
  unfold rho
  have := continuous_mm (a := a) (S := S) (i := i) (t := t)
  exact continuous_const.add ((this.inv₀ fun x => (mm_pos x).ne').smul
    (continuous_id.sub continuous_const))

theorem rho_apply (x : Fin n → ℝ) (j : Fin n) :
    rho a S i t x j = ctr a S i t j + (mm a S i t x)⁻¹ * (x j - ctr a S i t j) := rfl

theorem yv_rho (x : Fin n → ℝ) :
    yv a S i (rho a S i t x) = (mm a S i t x)⁻¹ • yv a S i x := by
  funext j
  simp only [yv, Pi.smul_apply, smul_eq_mul, rho_apply]
  split_ifs with hj
  · have hji : j ≠ i := (mem_erase.mp hj).1
    have hjS : j ∈ S := (mem_erase.mp hj).2
    simp only [ctr, hji, hjS, ite_false, ite_true]
    ring
  · simp

theorem hgt_rho (ht : t = 0 ∨ t = 1) (x : Fin n → ℝ) :
    hgt a i t (rho a S i t x) = 2 + (hgt a i t x - 2) * (mm a S i t x)⁻¹ := by
  simp only [hgt, rho_apply, ctr, ite_true]
  rcases ht with rfl | rfl <;> simp only [dir, bot] <;> push_cast <;> ring

/-- Membership in `τ = (a, S)` in the projection coordinates. -/
theorem memτ (hi : i ∈ S) (ht : t = 0 ∨ t = 1) (x : Fin n → ℝ) :
    x ∈ cubeSet ((a, S) : Cube n) ↔ (∀ j ∈ S.erase i, |yv a S i x j| ≤ 1) ∧
      (0 ≤ hgt a i t x ∧ hgt a i t x ≤ 1) ∧ (∀ j ∉ S, x j = a j) := by
  rw [mem_cubeSet_iff]
  constructor
  · intro h
    refine ⟨fun j hj => ?_, ?_, fun j hj => ?_⟩
    · have := h j
      simp only [(mem_erase.mp hj).2, ite_true] at this
      simp only [yv, hj, ite_true, abs_le]
      constructor <;> linarith [this.1, this.2]
    · have := h i
      simp only [hi, ite_true] at this
      rcases ht with rfl | rfl <;> simp only [hgt, dir, bot] <;> push_cast <;>
        constructor <;> linarith [this.1, this.2]
    · have := h j
      simp only [hj, ite_false, add_zero] at this
      exact le_antisymm this.2 this.1
  · rintro ⟨h1, h2, h3⟩ k
    by_cases hk : k = i
    · subst hk
      simp only [hi, ite_true]
      rcases ht with rfl | rfl <;> simp only [hgt, dir, bot] at h2 <;> push_cast at h2 <;>
        constructor <;> linarith [h2.1, h2.2]
    · by_cases hkS : k ∈ S
      · have := h1 k (mem_erase.mpr ⟨hk, hkS⟩)
        simp only [yv, mem_erase.mpr ⟨hk, hkS⟩, ite_true, abs_le] at this
        simp only [hkS, ite_true]
        constructor <;> linarith [this.1, this.2]
      · simp only [hkS, ite_false, add_zero, h3 k hkS, le_refl, and_self]

theorem abs_yv_le_norm (x : Fin n → ℝ) (j : Fin n) : |yv a S i x j| ≤ ‖yv a S i x‖ := by
  have := norm_le_pi_norm (yv a S i x) j
  rwa [Real.norm_eq_abs] at this

theorem mm_le_one (hi : i ∈ S) (ht : t = 0 ∨ t = 1) {x : Fin n → ℝ}
    (hx : x ∈ cubeSet ((a, S) : Cube n)) : mm a S i t x ≤ 1 := by
  obtain ⟨h1, h2, -⟩ := (memτ hi ht x).mp hx
  have hy : ‖yv a S i x‖ ≤ 1 := (pi_norm_le_iff_of_nonneg zero_le_one).mpr fun j => by
    rw [Real.norm_eq_abs]
    by_cases hj : j ∈ S.erase i
    · exact h1 j hj
    · simp [yv, hj]
  exact max_le hy (max_le (by linarith [h2.1]) (by norm_num))

/-- **`ρ` maps `τ` into `τ`.** -/
theorem rho_mem (hi : i ∈ S) (ht : t = 0 ∨ t = 1) {x : Fin n → ℝ}
    (hx : x ∈ cubeSet ((a, S) : Cube n)) : rho a S i t x ∈ cubeSet ((a, S) : Cube n) := by
  obtain ⟨h1, h2, h3⟩ := (memτ hi ht x).mp hx
  have hm := mm_pos (a := a) (S := S) (i := i) (t := t) x
  have hm1 := mm_le_one hi ht hx
  have hmh : 1 - hgt a i t x / 2 ≤ mm a S i t x := le_max_of_le_right (le_max_left _ _)
  have hmy : ‖yv a S i x‖ ≤ mm a S i t x := le_max_left _ _
  rw [memτ hi ht]
  refine ⟨fun j hj => ?_, ?_, fun j hj => ?_⟩
  · rw [yv_rho, Pi.smul_apply, smul_eq_mul, abs_mul, abs_inv, abs_of_pos hm,
      inv_mul_le_iff₀ hm, mul_one]
    exact (abs_yv_le_norm x j).trans hmy
  · rw [hgt_rho ht]
    set m := mm a S i t x
    have hmi : m * m⁻¹ = 1 := mul_inv_cancel₀ hm.ne'
    have hinv : 0 < m⁻¹ := inv_pos.mpr hm
    constructor <;> nlinarith [h2.1, h2.2]
  · have hji : j ≠ i := fun e => hj (e ▸ hi)
    rw [rho_apply, h3 j hj]
    simp [ctr, hji, hj]

/-- **`ρ` maps `τ` into `Λ`**: the image of a point of `τ` is not inner. -/
theorem not_inner_rho (hi : i ∈ S) (ht : t = 0 ∨ t = 1) {x : Fin n → ℝ}
    (hx : x ∈ cubeSet ((a, S) : Cube n)) : ¬ Inner a S i t (rho a S i t x) := by
  rintro ⟨h1, h2⟩
  obtain ⟨-, h2x, -⟩ := (memτ hi ht x).mp hx
  have hm := mm_pos (a := a) (S := S) (i := i) (t := t) x
  have hy : ‖yv a S i x‖ < mm a S i t x := (pi_norm_lt_iff hm).mpr fun j => by
    rw [Real.norm_eq_abs]
    by_cases hj : j ∈ S.erase i
    · have := h1 j hj
      rwa [yv_rho, Pi.smul_apply, smul_eq_mul, abs_mul, abs_inv, abs_of_pos hm,
        inv_mul_lt_iff₀ hm, mul_one] at this
    · simp [yv, hj, hm]
  rw [hgt_rho ht] at h2
  have hh : 1 - hgt a i t x / 2 < mm a S i t x := by
    set m := mm a S i t x
    have hmi : m * m⁻¹ = 1 := mul_inv_cancel₀ hm.ne'
    nlinarith
  have hhalf : (1 : ℝ) / 2 < mm a S i t x := by linarith [h2x.2]
  exact lt_irrefl _ (max_lt hy (max_lt hh hhalf))

/-- **`ρ` fixes `Λ`**: a point of `τ` that is not inner is fixed. -/
theorem rho_eq_self (hi : i ∈ S) (ht : t = 0 ∨ t = 1) {x : Fin n → ℝ}
    (hx : x ∈ cubeSet ((a, S) : Cube n)) (hn : ¬ Inner a S i t x) : rho a S i t x = x := by
  obtain ⟨-, h2, -⟩ := (memτ hi ht x).mp hx
  have h1 : 1 ≤ mm a S i t x := by
    unfold Inner at hn
    push Not at hn
    by_cases hall : ∀ j ∈ S.erase i, |yv a S i x j| < 1
    · have := hn hall
      have h0 : hgt a i t x = 0 := le_antisymm this h2.1
      exact le_max_of_le_right (le_max_of_le_left (by rw [h0]; norm_num))
    · push Not at hall
      obtain ⟨j, -, hj⟩ := hall
      exact le_max_of_le_left (hj.trans (abs_yv_le_norm x j))
  have hm : mm a S i t x = 1 := le_antisymm (mm_le_one hi ht hx) h1
  simp only [rho, hm, inv_one, one_smul, add_sub_cancel]

end Proj

/-! ## The deformation retraction of an elementary collapse -/

theorem realisation_mono {X Y : Finset (Cube n)} (h : X ⊆ Y) :
    realisation X ⊆ realisation Y := fun _ hx => by
  obtain ⟨c, hc, hxc⟩ := Set.mem_iUnion₂.mp hx
  exact Set.mem_biUnion (h hc) hxc

theorem isClosed_realisation (X : Finset (Cube n)) : IsClosed (realisation X) :=
  isClosed_biUnion_finset fun c _ => isClosed_cubeSet c

theorem int_le_of_lt {u v : ℤ} {x : ℝ} (h1 : (u : ℝ) ≤ x) (h2 : x < v + 1) : u ≤ v := by
  have : (u : ℝ) < v + 1 := lt_of_le_of_lt h1 h2
  have : u < v + 1 := by exact_mod_cast this
  omega

theorem int_succ_le_of_lt {u v : ℤ} {x : ℝ} (h1 : (v : ℝ) < x) (h2 : x ≤ u) : v + 1 ≤ u := by
  have : (v : ℝ) < u := lt_of_lt_of_le h1 h2
  have : v < u := by exact_mod_cast this
  omega

theorem int_le_of_le {u v : ℤ} {x : ℝ} (h1 : (u : ℝ) ≤ x) (h2 : x ≤ v) : u ≤ v := by
  exact_mod_cast h1.trans h2

section Retract

variable {a : Fin n → ℤ} {S : Finset (Fin n)} {i : Fin n} {t : ℤ}

/-- A cube containing an inner point of `τ` lies above `σ`. -/
theorem cle_of_inner (hi : i ∈ S) (ht : t = 0 ∨ t = 1) {c : Cube n} {x : Fin n → ℝ}
    (hxc : x ∈ cubeSet c) (hx : x ∈ cubeSet ((a, S) : Cube n)) (hin : Inner a S i t x) :
    CLe ((a + t • unit i, S.erase i) : Cube n) c := by
  obtain ⟨h1, h2⟩ := hin
  intro k
  have hc := Set.mem_univ_pi.mp hxc k
  have hτ := Set.mem_univ_pi.mp hx k
  simp only [Set.mem_Icc] at hc hτ
  simp only [top, shift_apply, mem_erase] at hτ ⊢
  by_cases hk : k = i
  · subst hk
    simp only [hi, ite_true, ne_eq, not_true_eq_false, false_and, ite_false, add_zero] at hτ ⊢
    simp only [hgt, dir, bot] at h2
    push_cast at hτ
    rcases ht with rfl | rfl
    · norm_num at h2 ⊢
      exact ⟨int_le_of_lt hc.1 (by linarith), int_le_of_le hτ.1 hc.2⟩
    · norm_num at h2 ⊢
      exact ⟨int_le_of_le hc.1 (by push_cast; linarith [hτ.2]),
        int_succ_le_of_lt (by linarith) hc.2⟩
  · simp only [hk, ite_false, add_zero, ne_eq, not_false_eq_true, true_and] at hτ ⊢
    by_cases hkS : k ∈ S
    · have hy := h1 k (mem_erase.mpr ⟨hk, hkS⟩)
      simp only [yv, mem_erase.mpr ⟨hk, hkS⟩, ite_true, abs_lt] at hy
      simp only [hkS, ite_true]
      exact ⟨int_le_of_lt hc.1 (by linarith [hy.2]), int_succ_le_of_lt (by linarith [hy.1]) hc.2⟩
    · simp only [hkS, ite_false, add_zero] at hτ ⊢
      exact ⟨int_le_of_le hc.1 hτ.2, int_le_of_le hτ.1 hc.2⟩

variable {X : Finset (Cube n)}

/-- **`|X ∖ {σ, τ}| ∩ τ ⊆ Λ`.** -/
theorem not_inner_of_mem_collapse (hX : IsComplex X) (hi : i ∈ S) (ht : t = 0 ∨ t = 1)
    (hfree : ∀ c ∈ X, IsFace (a + t • unit i, S.erase i) c → c = (a, S)) {x : Fin n → ℝ}
    (hx' : x ∈ realisation (collapse X (a + t • unit i, S.erase i) (a, S)))
    (hx : x ∈ cubeSet ((a, S) : Cube n)) : ¬ Inner a S i t x := by
  intro hin
  obtain ⟨c, hc, hxc⟩ := Set.mem_iUnion₂.mp hx'
  obtain ⟨hcσ, hcτ, hcX⟩ := mem_collapse.mp hc
  have hστ : IsFace ((a + t • unit i, S.erase i) : Cube n) (a, S) := ⟨i, hi, t, ht, rfl⟩
  rcases eq_of_cle hX hστ hfree _ c hcX rfl (cle_of_inner hi ht hxc hx hin) with h | h
  exacts [hcσ h, hcτ h]

/-- **`Λ ⊆ |X ∖ {σ, τ}|`.** -/
theorem mem_collapse_of_not_inner (hX : IsComplex X) (hτX : ((a, S) : Cube n) ∈ X)
    (hi : i ∈ S) (ht : t = 0 ∨ t = 1) {x : Fin n → ℝ}
    (hx : x ∈ cubeSet ((a, S) : Cube n)) (hn : ¬ Inner a S i t x) :
    x ∈ realisation (collapse X (a + t • unit i, S.erase i) (a, S)) := by
  obtain ⟨-, h2, -⟩ := (memτ hi ht x).mp hx
  unfold Inner at hn
  push Not at hn
  by_cases hall : ∀ j ∈ S.erase i, |yv a S i x j| < 1
  · have h0 : hgt a i t x = 0 := le_antisymm (hn hall) h2.1
    have hxi : x i = (a i : ℝ) + ((1 - t : ℤ) : ℝ) := by
      simp only [hgt, dir, bot] at h0
      rcases ht with rfl | rfl <;> push_cast at h0 ⊢ <;> linarith
    refine Set.mem_biUnion (mem_collapse.mpr ⟨?_, facet_ne hi _,
      facet_mem hX hτX hi (by omega)⟩) (mem_facet hx hxi)
    intro e
    have := congrFun (congrArg Prod.fst e) i
    simp only [shift_apply, ite_true] at this
    omega
  · push Not at hall
    obtain ⟨j, hj, hyj⟩ := hall
    have hji := (mem_erase.mp hj).1
    have hjS := (mem_erase.mp hj).2
    have hτj := (mem_cubeSet_iff _ x).mp hx j
    simp only [hjS, ite_true] at hτj
    simp only [yv, hj, ite_true] at hyj
    obtain ⟨s, hs, hxj⟩ : ∃ s : ℤ, (s = 0 ∨ s = 1) ∧ x j = a j + s := by
      rcases le_abs'.mp hyj with h | h
      · exact ⟨0, Or.inl rfl, by push_cast; linarith [hτj.1]⟩
      · exact ⟨1, Or.inr rfl, by push_cast; linarith [hτj.2]⟩
    refine Set.mem_biUnion (mem_collapse.mpr ⟨?_, facet_ne hjS _,
      facet_mem hX hτX hjS hs⟩) (mem_facet hx hxj)
    intro e
    have := congrArg Prod.snd e
    have hmem : i ∈ S.erase j := mem_erase.mpr ⟨Ne.symm hji, hi⟩
    simp only at this
    rw [this] at hmem
    simp at hmem

variable (a S i t) in
open Classical in
/-- The retraction `|X| → |X ∖ {σ, τ}|`: `ρ` on `τ`, the identity elsewhere. -/
noncomputable def ret (x : Fin n → ℝ) : Fin n → ℝ :=
  if x ∈ cubeSet ((a, S) : Cube n) then rho a S i t x else x

theorem ret_eq_self_of_mem (hX : IsComplex X) (hi : i ∈ S) (ht : t = 0 ∨ t = 1)
    (hfree : ∀ c ∈ X, IsFace (a + t • unit i, S.erase i) c → c = (a, S)) {x : Fin n → ℝ}
    (hx : x ∈ realisation (collapse X (a + t • unit i, S.erase i) (a, S))) :
    ret a S i t x = x := by
  unfold ret
  split_ifs with h
  · exact rho_eq_self hi ht h (not_inner_of_mem_collapse hX hi ht hfree hx h)
  · rfl

theorem realisation_eq (hτX : ((a, S) : Cube n) ∈ X) (hi : i ∈ S) (ht : t = 0 ∨ t = 1) :
    realisation X =
      realisation (collapse X (a + t • unit i, S.erase i) (a, S)) ∪ cubeSet ((a, S) : Cube n) := by
  ext x
  constructor
  · intro hx
    obtain ⟨c, hc, hxc⟩ := Set.mem_iUnion₂.mp hx
    by_cases hcτ : c = (a, S)
    · subst hcτ; exact Or.inr hxc
    by_cases hcσ : c = (a + t • unit i, S.erase i)
    · subst hcσ; exact Or.inr (cubeSet_facet_subset hi ht hxc)
    exact Or.inl (Set.mem_biUnion (mem_collapse.mpr ⟨hcσ, hcτ, hc⟩) hxc)
  · rintro (h | h)
    · exact realisation_mono (collapse_subset _ _ _) h
    · exact Set.mem_biUnion hτX h

theorem continuousOn_ret (hX : IsComplex X) (hτX : ((a, S) : Cube n) ∈ X) (hi : i ∈ S)
    (ht : t = 0 ∨ t = 1)
    (hfree : ∀ c ∈ X, IsFace (a + t • unit i, S.erase i) c → c = (a, S)) :
    ContinuousOn (ret a S i t) (realisation X) := by
  rw [realisation_eq hτX hi ht]
  refine ContinuousOn.union_of_isClosed ?_ ?_ (isClosed_realisation _) (isClosed_cubeSet _)
  · exact continuousOn_id.congr fun x hx => ret_eq_self_of_mem hX hi ht hfree hx
  · exact (continuous_rho (a := a) (S := S) (i := i) (t := t)).continuousOn.congr
      fun x hx => by simp [ret, hx]

theorem ret_mem (hX : IsComplex X) (hτX : ((a, S) : Cube n) ∈ X) (hi : i ∈ S)
    (ht : t = 0 ∨ t = 1) {x : Fin n → ℝ} (hx : x ∈ realisation X) :
    ret a S i t x ∈ realisation (collapse X (a + t • unit i, S.erase i) (a, S)) := by
  unfold ret
  split_ifs with h
  · exact mem_collapse_of_not_inner hX hτX hi ht (rho_mem hi ht h) (not_inner_rho hi ht h)
  · rw [realisation_eq hτX hi ht] at hx
    exact hx.resolve_right h

theorem homotopy_mem (hτX : ((a, S) : Cube n) ∈ X) (hi : i ∈ S) (ht : t = 0 ∨ t = 1)
    {x : Fin n → ℝ} (hx : x ∈ realisation X) {s : ℝ} (hs : s ∈ Set.Icc (0 : ℝ) 1) :
    x + s • (ret a S i t x - x) ∈ realisation X := by
  by_cases h : x ∈ cubeSet ((a, S) : Cube n)
  · have e : ret a S i t x = rho a S i t x := by unfold ret; simp [h]
    rw [e]
    exact Set.mem_biUnion hτX ((convex_cubeSet _).add_smul_sub_mem h (rho_mem hi ht h) hs)
  · have e : ret a S i t x = x := by unfold ret; simp [h]
    rw [e, sub_self, smul_zero, add_zero]
    exact hx

end Retract

/-! ## Singular homology of an elementary collapse -/

/-- Singular homology `H_k(Y; ℤ)` (Mathlib's `singularHomologyFunctor`). -/
noncomputable abbrev sing (k : ℕ) (Y : TopCat.{0}) : ModuleCat.{0} ℤ :=
  ((singularHomologyFunctor (ModuleCat.{0} ℤ) k).obj (ModuleCat.of ℤ ℤ)).obj Y

/-- A retraction `r` of `ι` (`ι ≫ r = 𝟙`) with `r ≫ ι` homotopic to the identity induces an
isomorphism on singular homology in every degree. -/
noncomputable def singularIsoOfRetract {A B : TopCat.{0}} (ι : A ⟶ B) (r : B ⟶ A)
    (h1 : ι ≫ r = 𝟙 A) (H : TopCat.Homotopy (r ≫ ι) (𝟙 B)) (k : ℕ) : sing k A ≅ sing k B where
  hom := ((singularHomologyFunctor (ModuleCat.{0} ℤ) k).obj (ModuleCat.of ℤ ℤ)).map ι
  inv := ((singularHomologyFunctor (ModuleCat.{0} ℤ) k).obj (ModuleCat.of ℤ ℤ)).map r
  hom_inv_id := by rw [← CategoryTheory.Functor.map_comp, h1, CategoryTheory.Functor.map_id]
  inv_hom_id := by
    rw [← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_id]
    exact H.congr_homologyMap_singularChainComplexFunctor (ModuleCat.of ℤ ℤ) k

section CollapseIso

variable {X : Finset (Cube n)} {a : Fin n → ℤ} {S : Finset (Fin n)} {i : Fin n} {t : ℤ}

/-- **An elementary collapse is a deformation retraction of realisations**, hence induces
isomorphisms on singular homology in every degree. -/
noncomputable def singularCollapseIso' (hX : IsComplex X) (hτX : ((a, S) : Cube n) ∈ X)
    (hi : i ∈ S) (ht : t = 0 ∨ t = 1)
    (hfree : ∀ c ∈ X, IsFace (a + t • unit i, S.erase i) c → c = (a, S)) (k : ℕ) :
    sing k (TopCat.of (realisation (collapse X (a + t • unit i, S.erase i) (a, S)))) ≅
      sing k (TopCat.of (realisation X)) :=
  let A := realisation (collapse X (a + t • unit i, S.erase i) (a, S))
  let B := realisation X
  have hAB : A ⊆ B := realisation_mono (collapse_subset _ _ _)
  have hc := continuousOn_ret hX hτX hi ht hfree
  let ιc : C(A, B) := ⟨Set.inclusion hAB, continuous_inclusion hAB⟩
  let rc : C(B, A) := ⟨fun x => ⟨ret a S i t x.1, ret_mem hX hτX hi ht x.2⟩,
    hc.domRestrict.subtype_mk _⟩
  have h1 : rc.comp ιc = ContinuousMap.id A := by
    ext x j
    exact congrFun (ret_eq_self_of_mem hX hi ht hfree x.2) j
  let H : ContinuousMap.Homotopy (ContinuousMap.id B) (ιc.comp rc) :=
    { toFun := fun p => ⟨p.2.1 + (p.1 : ℝ) • (ret a S i t p.2.1 - p.2.1),
        homotopy_mem hτX hi ht p.2.2 p.1.2⟩
      continuous_toFun := by
        have h2 : Continuous fun p : unitInterval × B => ret a S i t p.2.1 :=
          hc.domRestrict.comp continuous_snd
        exact Continuous.subtype_mk ((continuous_subtype_val.comp continuous_snd).add
          ((continuous_subtype_val.comp continuous_fst).smul
            (h2.sub (continuous_subtype_val.comp continuous_snd)))) _
      map_zero_left := fun x => by ext; simp
      map_one_left := fun x => by
        ext j
        show (x.1 + ((1 : unitInterval) : ℝ) • (ret a S i t x.1 - x.1)) j = ret a S i t x.1 j
        simp }
  singularIsoOfRetract (TopCat.ofHom ιc) (TopCat.ofHom rc)
    (by rw [← TopCat.ofHom_comp, h1]; rfl) (H.symm) k

end CollapseIso

/-- **Singular homology is invariant under elementary collapses**: if `σ` is a free primary
face of `τ ∈ X`, then `H_k(|X ∖ {σ, τ}|; ℤ) ≅ H_k(|X|; ℤ)` for every `k`. -/
theorem singular_collapse {X : Finset (Cube n)} (hX : IsComplex X) {σ τ : Cube n}
    (hτX : τ ∈ X) (hστ : IsFace σ τ) (hfree : ∀ c ∈ X, IsFace σ c → c = τ) (k : ℕ) :
    Nonempty (sing k (TopCat.of (realisation (collapse X σ τ))) ≃ₗ[ℤ]
      sing k (TopCat.of (realisation X))) := by
  obtain ⟨i, hi, t, ht, rfl⟩ := hστ
  obtain ⟨a, S⟩ := τ
  exact ⟨(singularCollapseIso' hX hτX hi ht hfree k).toLinearEquiv⟩

/-! ## The comparison -/

/-- The comparison statement in degree `k`: `H_k(X) ≅ H_k(|X|; ℤ)`. -/
def Comparison (X : Finset (Cube n)) (k : ℕ) : Prop :=
  Nonempty (homology X k ≃ₗ[ℤ] sing k (TopCat.of (realisation X)))

/-- **The comparison holds for `X` iff it holds for an elementary collapse of `X`.** -/
theorem comparison_collapse_iff {X : Finset (Cube n)} (hX : IsComplex X) {σ τ : Cube n}
    (hτX : τ ∈ X) (hστ : IsFace σ τ) (hfree : ∀ c ∈ X, IsFace σ c → c = τ) (k : ℕ) :
    Comparison (collapse X σ τ) k ↔ Comparison X k := by
  obtain ⟨e1⟩ := homology_collapse hX hτX hστ hfree k
  obtain ⟨e2⟩ := singular_collapse hX hτX hστ hfree k
  exact ⟨fun ⟨f⟩ => ⟨e1.symm.trans (f.trans e2)⟩, fun ⟨f⟩ => ⟨e1.trans (f.trans e2.symm)⟩⟩

/-- `X` collapses onto `Y` by a finite sequence of elementary collapses. -/
inductive Collapses : Finset (Cube n) → Finset (Cube n) → Prop
  | refl (X : Finset (Cube n)) : Collapses X X
  | step {X Y : Finset (Cube n)} (σ τ : Cube n) (hτX : τ ∈ X) (hστ : IsFace σ τ)
      (hfree : ∀ c ∈ X, IsFace σ c → c = τ) (h : Collapses (collapse X σ τ) Y) : Collapses X Y

theorem Collapses.isComplex {X Y : Finset (Cube n)} (h : Collapses X Y) (hX : IsComplex X) :
    IsComplex Y := by
  induction h with
  | refl => exact hX
  | step σ τ hτX hστ hfree _ ih => exact ih (isComplex_collapse hX hστ hfree)

/-- **Reduction to the collapsed core.** If the finite cubical complex `X` collapses onto
`Y`, then `H_k(X) ≅ H_k(|X|; ℤ)` iff `H_k(Y) ≅ H_k(|Y|; ℤ)`, in every degree `k`. -/
theorem comparison_iff_of_collapses {X Y : Finset (Cube n)} (hX : IsComplex X)
    (h : Collapses X Y) (k : ℕ) : Comparison X k ↔ Comparison Y k := by
  induction h with
  | refl => exact Iff.rfl
  | step σ τ hτX hστ hfree _ ih =>
    exact (comparison_collapse_iff hX hτX hστ hfree k).symm.trans
      (ih (isComplex_collapse hX hστ hfree))

/-- **Degree `0`**: the comparison holds for every finite cubical complex. -/
theorem comparison_zero {X : Finset (Cube n)} (hX : IsComplex X) : Comparison X 0 :=
  homology_zero_singular hX

theorem isComplex_vertex (v : Fin n → ℤ) : IsComplex ({(v, ∅)} : Finset (Cube n)) := by
  intro c hc j hj
  rw [mem_singleton] at hc
  subst hc
  simp at hj

theorem subsingleton_realisation_vertex (v : Fin n → ℤ) :
    Subsingleton (realisation ({(v, ∅)} : Finset (Cube n))) := by
  have key : ∀ x ∈ realisation ({(v, ∅)} : Finset (Cube n)), x = vpt v := by
    intro x hx
    simp only [realisation, mem_singleton, Set.iUnion_iUnion_eq_left] at hx
    rw [mem_cubeSet_iff] at hx
    funext k
    have := hx k
    simp only [notMem_empty, ite_false, add_zero] at this
    exact le_antisymm this.2 this.1
  exact ⟨fun x y => Subtype.ext ((key x.1 x.2).trans (key y.1 y.2).symm)⟩

theorem subsingleton_homology_vertex (v : Fin n → ℤ) (k : ℕ) :
    Subsingleton (homology ({(v, ∅)} : Finset (Cube n)) (k + 1)) := by
  have hcells : cells ({(v, ∅)} : Finset (Cube n)) (k + 1) = ∅ := by
    ext c
    simp only [cells, mem_filter, mem_singleton, notMem_empty, iff_false, not_and]
    rintro rfl
    simp
  have : Subsingleton (cycles ({(v, ∅)} : Finset (Cube n)) (k + 1)) := by
    refine ⟨fun x y => Subtype.ext ?_⟩
    have h0 : ∀ z ∈ cycles ({(v, ∅)} : Finset (Cube n)) (k + 1), z = 0 := by
      intro z hz
      have := hz.1
      rw [chains, hcells, coe_empty, Finsupp.supported_empty] at this
      exact (Submodule.mem_bot ℤ).mp this
    rw [h0 _ x.2, h0 _ y.2]
  exact (Submodule.mkQ_surjective _).subsingleton

/-- **A single vertex**: the comparison holds in every degree. -/
theorem comparison_vertex (v : Fin n → ℤ) (k : ℕ) : Comparison ({(v, ∅)} : Finset (Cube n)) k := by
  rcases k with _ | k
  · exact comparison_zero (isComplex_vertex v)
  · have := subsingleton_realisation_vertex v
    have hz : Limits.IsZero (sing (k + 1) (TopCat.of (realisation ({(v, ∅)} : Finset (Cube n))))) :=
      isZero_singularHomologyFunctor_of_totallyDisconnectedSpace _ _ _ _ (Nat.succ_ne_zero k)
    have := ModuleCat.isZero_iff_subsingleton.mp hz
    have := subsingleton_homology_vertex v k
    exact ⟨LinearEquiv.ofSubsingleton _ _⟩

/-- A complex is **collapsible** if it collapses onto a single vertex. -/
def Collapsible (X : Finset (Cube n)) : Prop := ∃ v : Fin n → ℤ, Collapses X {(v, ∅)}

/-- **Cubical and singular homology agree in every degree for every collapsible finite
cubical complex**: `H_k(X) ≅ H_k(|X|; ℤ)` for all `k`. -/
theorem comparison_of_collapsible {X : Finset (Cube n)} (hX : IsComplex X)
    (h : Collapsible X) (k : ℕ) : Comparison X k := by
  obtain ⟨v, hv⟩ := h
  exact (comparison_iff_of_collapses hX hv k).mpr (comparison_vertex v k)

/-- The unit interval complex `{[0], [1], [0,1]}` in `ℤ¹`. -/
def intervalComplex : Finset (Cube 1) := {(0, ∅), (unit 0, ∅), (0, {0})}

theorem intervalComplex_collapsible : Collapsible intervalComplex := by
  have hne : (unit 0 : Fin 1 → ℤ) ≠ 0 := unit_ne_zero 0
  refine ⟨0, Collapses.step (unit 0, ∅) (0, {0}) (by simp [intervalComplex])
    ⟨0, by simp, 1, Or.inr rfl, by simp⟩ ?_ ?_⟩
  · intro c hc hf
    obtain ⟨j, hj, s, hs, e⟩ := hf
    simp only [intervalComplex, mem_insert, mem_singleton] at hc
    rcases hc with rfl | rfl | rfl
    · simp at hj
    · simp at hj
    · rfl
  · have : collapse intervalComplex (unit 0, ∅) (0, {0}) = {(0, ∅)} := by
      ext c
      simp only [mem_collapse, intervalComplex, mem_insert, mem_singleton]
      constructor
      · rintro ⟨h1, h2, h3 | h3 | h3⟩
        · exact h3
        · exact absurd h3 h1
        · exact absurd h3 h2
      · rintro rfl
        refine ⟨fun e => hne (congrArg Prod.fst e).symm, fun e => ?_, Or.inl rfl⟩
        have := congrArg Prod.snd e
        simp at this
    rw [this]
    exact Collapses.refl _

/-- The interval complex: cubical and singular homology agree in every degree. -/
theorem comparison_interval (k : ℕ) : Comparison intervalComplex k :=
  comparison_of_collapsible (by
    intro c hc j hj
    simp only [intervalComplex, mem_insert, mem_singleton] at hc
    rcases hc with rfl | rfl | rfl
    · simp at hj
    · simp at hj
    · simp only [mem_singleton] at hj
      subst hj
      simp [intervalComplex]) intervalComplex_collapsible k

end QE.CubicalSingular
