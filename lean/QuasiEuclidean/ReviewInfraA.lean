-- SPDX-License-Identifier: MIT
-- Copyright 2026 Metere Industries, Inc. Author: Alfredo Metere.
-- Quasi-Euclidean Granular Geometry. Any derivative work must carry this notice:
--   This work is derivative of the Quasi-Euclidean Granular Geometry book
--   authored by Alfredo Metere. Copyright 2026 Metere Industries, Inc.
--   All rights reserved
-- See LICENSE.md and NOTICE.

import QuasiEuclidean.Ch01_Axioms
import QuasiEuclidean.Ch01b_Packing
import QuasiEuclidean.Ch02_Hyper
import QuasiEuclidean.NSA_Internal

/-!
# Review infrastructure A: chapters 1, 2 and Appendix A

Lean statements closing the gaps between printed claims and their Lean tags in
`01-axiom.tex`, `01-packing.tex`, `02-hyperfinite-continuum.tex` and
`A-nonstandard-primer.tex`. All results are Lebesgue-free.
-/

open Filter

set_option linter.unusedSectionVars false

/-! ## Chapter 1: the axiom -/

namespace QE.Axioms

section Field

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-- `prop:axiom-separation`, equality case: `|2kε - 2jε| = 2ε` iff `|k - j| = 1`. -/
theorem centre_dist_eq_iff {ε : K} (hε : 0 < ε) (k j : ℤ) :
    |QE.centre ε k - QE.centre ε j| = 2 * ε ↔ |k - j| = 1 := by
  unfold QE.centre
  have h2 : (0 : K) < 2 * ε := by linarith
  have e : 2 * ε * (k : K) - 2 * ε * j = 2 * ε * ((k - j : ℤ) : K) := by push_cast; ring
  rw [e, abs_mul, abs_of_pos h2, ← Int.cast_abs]
  constructor
  · intro h
    have : ((|k - j| : ℤ) : K) = 1 := by
      have := mul_left_cancel₀ h2.ne' (h.trans (mul_one _).symm)
      exact this
    exact_mod_cast this
  · intro h; rw [h]; simp

/-- **Separation of centres** (`prop:axiom-separation`), with the equality case. -/
theorem separation_iff :
    ∀ (K : Type) [Field K] [LinearOrder K] [IsStrictOrderedRing K] (ε : K), 0 < ε →
      (∀ k j : ℤ, k ≠ j → 2 * ε ≤ |QE.centre ε k - QE.centre ε j|) ∧
      (∀ k j : ℤ, |QE.centre ε k - QE.centre ε j| = 2 * ε ↔ |k - j| = 1) ∧
      Function.Injective (QE.centre ε) :=
  fun _ _ _ _ _ hε => ⟨fun _ _ h => centre_dist_ge hε h, centre_dist_eq_iff hε,
    centre_injective hε.ne'⟩

/-- `thm:axiom-cells` (b), explicit form: `x` lies in the cell `k` iff
`k = ⌊x/(2ε) + 1/2⌋`. -/
theorem mem_cell_iff_cellIndex [FloorRing K] {ε : K} (hε : 0 < ε) (x : K) (k : ℤ) :
    x ∈ cell ε k ↔ k = cellIndex ε x := by
  constructor
  · intro hk
    by_contra hne
    exact Set.disjoint_left.mp (cell_disjoint hε hne) hk (mem_cell_cellIndex hε x)
  · rintro rfl; exact mem_cell_cellIndex hε x

/-- **Cell decomposition, explicit owner** (`thm:axiom-cells` (b)): every `x` lies in
exactly one cell, namely the one with index `⌊x/(2ε) + 1/2⌋`. -/
theorem cell_decomposition_explicit [FloorRing K] {ε : K} (hε : 0 < ε) (x : K) :
    x ∈ cell ε ⌊x / (2 * ε) + 1 / 2⌋ ∧ ∀ k : ℤ, x ∈ cell ε k → k = ⌊x / (2 * ε) + 1 / 2⌋ :=
  ⟨mem_cell_cellIndex hε x, fun k hk => (mem_cell_iff_cellIndex hε x k).1 hk⟩

/-- `prop:axiom-tube`, two-row case: two distinct rows are incident with the line at
height `y` iff `y` is an odd multiple of `ε`. -/
theorem two_rows_iff {ε : K} (hε : 0 < ε) (y : K) :
    (∃ m m' : ℤ, m ≠ m' ∧ |QE.centre ε m - y| ≤ ε ∧ |QE.centre ε m' - y| ≤ ε) ↔
      ∃ j : ℤ, y = (2 * j + 1) * ε := by
  constructor
  · rintro ⟨m, m', hne, h, h'⟩
    have hadj := line_rows_adjacent hε h h'
    unfold QE.centre at h h'
    rw [abs_le] at h h'
    rcases lt_or_gt_of_ne hne with hlt | hlt
    · have : m' = m + 1 := by rw [abs_le] at hadj; omega
      subst this
      refine ⟨m, ?_⟩
      push_cast at h'
      linarith [h.2, h'.1]
    · have : m = m' + 1 := by rw [abs_le] at hadj; omega
      subst this
      refine ⟨m', ?_⟩
      push_cast at h
      linarith [h.1, h'.2]
  · rintro ⟨j, rfl⟩
    refine ⟨j, j + 1, by omega, ?_, ?_⟩ <;> unfold QE.centre <;> push_cast
    · rw [show 2 * ε * (j : K) - (2 * j + 1) * ε = -ε by ring, abs_neg, abs_of_pos hε]
    · rw [show 2 * ε * ((j : K) + 1) - (2 * j + 1) * ε = ε by ring, abs_of_pos hε]

/-- **A line is a tube one or two points thick** (`prop:axiom-tube`), complete:
existence, adjacency, and the two-row case. -/
theorem line_tube_full [FloorRing K] {ε : K} (hε : 0 < ε) (y : K) :
    (∃ m : ℤ, |QE.centre ε m - y| ≤ ε) ∧
    (∀ m m' : ℤ, |QE.centre ε m - y| ≤ ε → |QE.centre ε m' - y| ≤ ε → |m - m'| ≤ 1) ∧
    ((∃ m m' : ℤ, m ≠ m' ∧ |QE.centre ε m - y| ≤ ε ∧ |QE.centre ε m' - y| ≤ ε) ↔
      ∃ j : ℤ, y = (2 * j + 1) * ε) :=
  ⟨line_meets_row hε y, fun _ _ h h' => line_rows_adjacent hε h h', two_rows_iff hε y⟩

end Field

end QE.Axioms

/-! ## Chapter 1, packing: distances through the owners -/

namespace QE.Packing

/-- **Classical-observable theorem (distances), owner form**
(`thm:axiom-packing-classical` (d)): replacing two positions by the centres of
*their owners* changes their Euclidean distance by at most `2 √n ε`. -/
theorem dist_error_owner {n : ℕ} {ε : ℝ} (hε : 0 < ε) (x y : EuclideanSpace ℝ (Fin n)) :
    |dist x y - dist (ptE ε (owner ε (WithLp.ofLp x))) (ptE ε (owner ε (WithLp.ofLp y)))|
      ≤ 2 * Real.sqrt n * ε := by
  have hk := dist_centre_le_of_mem_cell hε (mem_cell_owner hε (WithLp.ofLp x))
  have hj := dist_centre_le_of_mem_cell hε (mem_cell_owner hε (WithLp.ofLp y))
  rw [WithLp.toLp_ofLp] at hk hj
  have := dist_dist_dist_le x y (ptE ε (owner ε (WithLp.ofLp x)))
    (ptE ε (owner ε (WithLp.ofLp y)))
  rw [Real.dist_eq] at this
  linarith

/-- The relative error of representing a position by the centre of its owner, in a
context whose smallest length is `L > 0`, is at most `√n ε / L`
(`cor:axiom-packing-unobservable`, relative version). -/
theorem owner_relative_error {n : ℕ} {ε : ℝ} (hε : 0 < ε) {L : ℝ} (hL : 0 < L)
    (x : EuclideanSpace ℝ (Fin n)) :
    dist x (ptE ε (owner ε (WithLp.ofLp x))) / L ≤ Real.sqrt n * ε / L := by
  have hk := dist_centre_le_of_mem_cell hε (mem_cell_owner hε (WithLp.ofLp x))
  rw [WithLp.toLp_ofLp] at hk
  exact div_le_div_of_nonneg_right hk hL.le

end QE.Packing

/-! ## Chapter 1, packing: the absolute version of "no gap is observable" -/

namespace QE.Packing

open QE.NSA Metric

variable {n : ℕ}

/-- The internal map sending a position of `*ℝⁿ` to the centre of its owner
(granule `ε = [e m]`). -/
noncomputable def hOwnerCentre (e : ℕ → ℝ) :
    Ult (EuclideanSpace ℝ (Fin n)) → Ult (EuclideanSpace ℝ (Fin n)) :=
  ifun (fun m x => ptE (e m) (owner (e m) (WithLp.ofLp x)))

/-- The internal union of the closed point-spheres of radius `ε = [e m]`. -/
def hSpheres (e : ℕ → ℝ) : Set (Ult (EuclideanSpace ℝ (Fin n))) :=
  internal (fun m => ⋃ k : Fin n → ℤ, closedBall (ptE (e m) k) (e m))

theorem isInternal_hSpheres (e : ℕ → ℝ) : IsInternal (hSpheres (n := n) e) :=
  isInternal_internal _

/-- Sequence-wise choice of a nearest point of a point-sphere. -/
theorem exists_near_sphere_seq (hn : 1 ≤ n) {e : ℕ → ℝ}
    (he : ∀ᶠ m in (hyperfilter ℕ : Filter ℕ), 0 < e m) (u : ℕ → EuclideanSpace ℝ (Fin n)) :
    ∃ v : ℕ → EuclideanSpace ℝ (Fin n),
      ((v : Ult (EuclideanSpace ℝ (Fin n))) ∈ hSpheres e) ∧
      ∀ᶠ m in (hyperfilter ℕ : Filter ℕ), dist (u m) (v m) ≤ (Real.sqrt n - 1) * e m := by
  classical
  let v : ℕ → EuclideanSpace ℝ (Fin n) := fun m =>
    if h : 0 < e m then (near_sphere hn h (u m)).choose_spec.choose else u m
  have hv : ∀ᶠ m in (hyperfilter ℕ : Filter ℕ),
      (∃ k : Fin n → ℤ, v m ∈ closedBall (ptE (e m) k) (e m)) ∧
        dist (u m) (v m) ≤ (Real.sqrt n - 1) * e m := by
    filter_upwards [he] with m hm
    simp only [v, hm, ↓reduceDIte]
    obtain ⟨h1, h2⟩ := (near_sphere hn hm (u m)).choose_spec.choose_spec
    exact ⟨⟨_, h1⟩, h2⟩
  refine ⟨v, ?_, hv.mono fun m h => h.2⟩
  unfold hSpheres
  rw [mem_internal]
  filter_upwards [hv] with m hm
  exact Set.mem_iUnion.2 hm.1

/-- **No gap is observable, absolute version** (`cor:axiom-packing-unobservable`).
Let `ε = [e m]` be a positive infinitesimal and `n ≥ 1` standard. Then
(i) every position `x ∈ *ℝⁿ` is in the monad of the centre of its owner;
(ii) every position is in the monad of some point of some point-sphere;
(iii) the gap set contains no ball of non-infinitesimal radius: every ball
`{y : |x - y| < r}` with `r > 0` not infinitesimal meets a point-sphere;
(iv) every standard `x ∈ ℝⁿ` is the shadow of a point of a point-sphere, so the
shadow of the union of the point-spheres (in the finite part) is all of `ℝⁿ`. -/
theorem unobservable_absolute (hn : 1 ≤ n) (e : ℕ → ℝ) (he0 : 0 < Hyperreal.ofSeq e)
    (he : IsInfinitesimal (Hyperreal.ofSeq e)) :
    (∀ x : Ult (EuclideanSpace ℝ (Fin n)), Near x (hOwnerCentre e x)) ∧
    (∀ x : Ult (EuclideanSpace ℝ (Fin n)), ∃ y ∈ hSpheres e, Near x y) ∧
    (∀ (x : Ult (EuclideanSpace ℝ (Fin n))) (r : ℝ*), 0 < r → ¬ IsInfinitesimal r →
      ∃ y ∈ hSpheres e, hdist x y < r) ∧
    (∀ x : EuclideanSpace ℝ (Fin n), ∃ y ∈ hSpheres e,
      Near y (Germ.const x : Ult (EuclideanSpace ℝ (Fin n)))) := by
  have hpos : ∀ᶠ m in (hyperfilter ℕ : Filter ℕ), 0 < e m := Hyperreal.ofSeq_lt_ofSeq.1 he0
  -- `c ε` is infinitesimal for every standard `c`
  have hc : ∀ c : ℝ, IsInfinitesimal (Hyperreal.ofSeq (fun m => c * e m)) := by
    intro c
    have : Hyperreal.ofSeq (fun m => c * e m) = (c : ℝ*) * Hyperreal.ofSeq e := rfl
    rw [this, mul_comm]
    exact he.mul_finite (coe_isFinite c)
  have part2 : ∀ x : Ult (EuclideanSpace ℝ (Fin n)), ∃ y ∈ hSpheres e, Near x y := by
    intro x
    obtain ⟨u, rfl⟩ := exists_rep x
    obtain ⟨v, hv, hd⟩ := exists_near_sphere_seq hn hpos u
    refine ⟨v, hv, near_of_hdist_le (hc (Real.sqrt n - 1)) ?_⟩
    rw [hdist_coe]
    exact Hyperreal.ofSeq_le_ofSeq.2 hd
  refine ⟨fun x => ?_, part2, fun x r hr hri => ?_, fun x => ?_⟩
  · obtain ⟨u, rfl⟩ := exists_rep x
    refine near_of_hdist_le (hc (Real.sqrt n)) ?_
    show Hyperreal.ofSeq (fun m => dist (u m) (ptE (e m) (owner (e m) (WithLp.ofLp (u m)))))
      ≤ _
    refine Hyperreal.ofSeq_le_ofSeq.2 ?_
    filter_upwards [hpos] with m hm
    have := dist_centre_le_of_mem_cell hm (mem_cell_owner hm (WithLp.ofLp (u m)))
    rwa [WithLp.toLp_ofLp] at this
  · obtain ⟨y, hy, hxy⟩ := part2 x
    have : ∃ s : ℝ, 0 < s ∧ (s : ℝ*) ≤ r := by
      by_contra hcon
      push Not at hcon
      apply hri
      rw [hyper_isInfinitesimal_iff]
      intro s hs
      rw [abs_of_pos hr]; exact hcon s hs
    obtain ⟨s, hs, hsr⟩ := this
    exact ⟨y, hy, lt_of_lt_of_le (hxy.hdist_lt hs) hsr⟩
  · obtain ⟨y, hy, hxy⟩ := part2 (Germ.const x)
    exact ⟨y, hy, hxy.symm⟩

end QE.Packing

/-! ## Chapter 2: the snap stays inside the horizon -/

namespace QE.Hyper

section FieldSnap

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K] [FloorRing K]

/-- If `|x| ≤ 2εP` then the snap index of `x` satisfies `|⌊x/(2ε)+1/2⌋| ≤ P`. -/
theorem abs_snapIdx_le {ε : K} (hε : 0 < ε) {P : ℤ} {x : K} (hx : |x| ≤ 2 * ε * P) :
    |snapIdx ε x| ≤ P := by
  rw [abs_le] at hx
  have h2 : (0 : K) < 2 * ε := by linarith
  have hlo := snap_mono hε (show QE.centre ε (-P) ≤ x by unfold QE.centre; push_cast; linarith)
  have hhi := snap_mono hε (show x ≤ QE.centre ε P by unfold QE.centre; linarith)
  rw [snap_centre hε, snap_eq_centre] at hlo hhi
  unfold QE.centre at hlo hhi
  have a1 : ((-P : ℤ) : K) ≤ snapIdx ε x := le_of_mul_le_mul_left hlo h2
  have a2 : (snapIdx ε x : K) ≤ P := le_of_mul_le_mul_left hhi h2
  have b1 : -P ≤ snapIdx ε x := by exact_mod_cast a1
  have b2 : snapIdx ε x ≤ P := by exact_mod_cast a2
  rw [abs_le]; exact ⟨b1, b2⟩

end FieldSnap

open Hyperreal

/-- The hyperfinite granular line `Λ = {2εk : k ∈ *ℤ, |k| ≤ P} = 2ε*ℤ ∩ [-Ω, Ω]`,
`Ω = 2εP` (`def:lattice`). -/
def hLat (e P : ℝ*) : Set ℝ* := {x | ∃ z : ℝ*, IsHyperint z ∧ |z| ≤ P ∧ x = 2 * e * z}

/-- **The lattice is ε-dense, horizon clause** (`thm:hyper-dense`): if `|x| ≤ Ω = 2εP`
for a hyperinteger `P`, then `⌊x⌉_ε ∈ Λ`. -/
theorem hsnap_mem_hLat {e P x : ℝ*} (he : 0 < e) (hP : IsHyperint P)
    (hx : |x| ≤ 2 * e * P) : hsnap e x ∈ hLat e P := by
  obtain ⟨f, rfl⟩ := ofSeq_surjective e
  obtain ⟨g, rfl⟩ := ofSeq_surjective x
  obtain ⟨p, rfl⟩ := hP
  have hf : ∀ᶠ n in (hyperfilter ℕ : Filter ℕ), 0 < f n := ofSeq_lt_ofSeq.mp he
  have hx' : ∀ᶠ n in (hyperfilter ℕ : Filter ℕ), |g n| ≤ 2 * f n * p n := by
    rw [QE.NSA.abs_ofSeq] at hx
    exact ofSeq_le_ofSeq.mp hx
  refine ⟨ofSeq (fun n => (snapIdx (f n) (g n) : ℝ)), ⟨_, rfl⟩, ?_, rfl⟩
  rw [QE.NSA.abs_ofSeq]
  refine ofSeq_le_ofSeq.mpr ?_
  filter_upwards [hf, hx'] with n h1 h2
  have := abs_snapIdx_le h1 h2
  rw [← Int.cast_abs]; exact_mod_cast this

/-- `thm:hyper-dense` in one statement: `⌊x⌉_ε` is a hyperinteger multiple of `2ε`
within `ε` of `x`, and lies in `Λ` when `|x| ≤ Ω`. -/
theorem hyper_dense {e : ℝ*} (he : 0 < e) (x : ℝ*) :
    (∃ z : ℝ*, IsHyperint z ∧ hsnap e x = 2 * e * z) ∧ |x - hsnap e x| ≤ e ∧
    (∀ P : ℝ*, IsHyperint P → |x| ≤ 2 * e * P → hsnap e x ∈ hLat e P) :=
  ⟨hsnap_on_lattice e x, abs_sub_hsnap_le he x, fun _ hP hx => hsnap_mem_hLat he hP hx⟩

end QE.Hyper

/-! ## Chapter 1: the hyperfinite line is a discrete order (`prop:axiom-discrete`) -/

namespace QE.Axioms

open QE.NSA

/-- The hyperfinite granular line `Λ = [{2 f n k : k ∈ ℤ, |k| ≤ p n}]`, an internal
subset of `ℝ*` (granule `ε = [f n]`, horizon `Ω = [2 f n p n]`). -/
def latLine (f : ℕ → ℝ) (p : ℕ → ℤ) : Set ℝ* :=
  internal (fun n => {x : ℝ | ∃ k : ℤ, |k| ≤ p n ∧ x = 2 * f n * k})

theorem mem_latLine (f : ℕ → ℝ) (p : ℕ → ℤ) (u : ℕ → ℝ) :
    Hyperreal.ofSeq u ∈ latLine f p ↔
      ∀ᶠ n in (hyperfilter ℕ : Filter ℕ), ∃ k : ℤ, |k| ≤ p n ∧ u n = 2 * f n * k :=
  mem_internal _ u

theorem latLine_finite (f : ℕ → ℝ) (p : ℕ → ℤ) (n : ℕ) :
    {x : ℝ | ∃ k : ℤ, |k| ≤ p n ∧ x = 2 * f n * k}.Finite := by
  refine ((Set.finite_Icc (-p n) (p n)).image (fun k : ℤ => 2 * f n * k)).subset ?_
  rintro x ⟨k, hk, rfl⟩
  exact ⟨k, abs_le.1 hk, rfl⟩

/-- `latLine` is the lattice `hLat ε P = {2εz : z ∈ *ℤ, |z| ≤ P}` of chapter 2. -/
theorem latLine_eq_hLat (f : ℕ → ℝ) (p : ℕ → ℤ) :
    latLine f p = QE.Hyper.hLat (Hyperreal.ofSeq f) (Hyperreal.ofSeq (fun n => (p n : ℝ))) := by
  ext x
  obtain ⟨u, rfl⟩ := exists_rep x
  unfold latLine
  refine (mem_internal _ u).trans ?_
  constructor
  · intro h
    classical
    let k : ℕ → ℤ := fun n =>
      if hk : ∃ k : ℤ, |k| ≤ p n ∧ u n = 2 * f n * k then hk.choose else 0
    have hk : ∀ᶠ n in (hyperfilter ℕ : Filter ℕ), |k n| ≤ p n ∧ u n = 2 * f n * k n := by
      filter_upwards [h] with n hn
      simp only [k, hn, ↓reduceDIte]
      exact hn.choose_spec
    refine ⟨Hyperreal.ofSeq (fun n => (k n : ℝ)), ⟨k, rfl⟩, ?_, ?_⟩
    · rw [abs_ofSeq]
      refine Hyperreal.ofSeq_le_ofSeq.2 ?_
      filter_upwards [hk] with n hn
      rw [← Int.cast_abs]; exact_mod_cast hn.1
    · show Hyperreal.ofSeq u = Hyperreal.ofSeq (fun n => 2 * f n * (k n : ℝ))
      exact Germ.coe_eq.2 (hk.mono fun n hn => hn.2)
  · rintro ⟨z, ⟨k, rfl⟩, hz, hx⟩
    rw [abs_ofSeq] at hz
    have hz' := Hyperreal.ofSeq_le_ofSeq.1 hz
    have hx' : ∀ᶠ n in (hyperfilter ℕ : Filter ℕ), u n = 2 * f n * k n :=
      Germ.coe_eq.1 (hx : Hyperreal.ofSeq u = Hyperreal.ofSeq (fun n => 2 * f n * (k n : ℝ)))
    filter_upwards [hz', hx'] with n h1 h2
    refine ⟨k n, ?_, h2⟩
    have : ((|k n| : ℤ) : ℝ) ≤ p n := by rw [Int.cast_abs]; exact h1
    exact_mod_cast this

/-- **Every nonempty internal subset of `Λ` has a greatest and a least element**
(`prop:axiom-discrete`). -/
theorem internal_subset_latLine_max_min (f : ℕ → ℝ) (p : ℕ → ℤ) {S : Set ℝ*}
    (hS : IsInternal (S : Set (Ult ℝ))) (hSL : S ⊆ latLine f p) (hne : S.Nonempty) :
    (∃ a ∈ S, ∀ y ∈ S, y ≤ a) ∧ (∃ b ∈ S, ∀ y ∈ S, b ≤ y) := by
  obtain ⟨A, rfl⟩ := hS
  set L : ℕ → Set ℝ := fun n => {x : ℝ | ∃ k : ℤ, |k| ≤ p n ∧ x = 2 * f n * k}
  have hSeq : internal A = internal (fun n => A n ∩ L n) := by
    rw [internal_inter]
    exact (Set.inter_eq_left.2 hSL).symm
  have hfin : ∀ᶠ m in (hyperfilter ℕ : Filter ℕ), (A m ∩ L m).Finite :=
    Eventually.of_forall fun m => (latLine_finite f p m).subset Set.inter_subset_right
  rw [hSeq] at hne ⊢
  have hid : ∀ c : Ult ℝ, hval (fun _ (x : ℝ) => x) c = c := by
    intro c; obtain ⟨u, rfl⟩ := exists_rep c; rfl
  have hneg : ∀ c : Ult ℝ, hval (fun _ (x : ℝ) => -x) c = -c := by
    intro c; obtain ⟨u, rfl⟩ := exists_rep c; rfl
  obtain ⟨a, ha, hmax⟩ := exists_max_hyperfinite _ hfin hne (fun _ x => x)
  obtain ⟨b, hb, hmin⟩ := exists_max_hyperfinite _ hfin hne (fun _ x => -x)
  refine ⟨⟨a, ha, fun y hy => ?_⟩, ⟨b, hb, fun y hy => ?_⟩⟩
  · exact (hid y).symm.le.trans ((hmax y hy).trans (hid a).le)
  · have := (hneg y).symm.le.trans ((hmin y hy).trans (hneg b).le)
    exact neg_le_neg_iff.1 this

/-- **Immediate successors and predecessors in `Λ`** (`prop:axiom-discrete`):
every `x ∈ Λ` with `x < Ω` has the immediate successor `x + 2ε ∈ Λ`, and every
`x ∈ Λ` with `-Ω < x` has the immediate predecessor `x - 2ε ∈ Λ`. -/
theorem latLine_succ_pred (f : ℕ → ℝ) (p : ℕ → ℤ) (hf : 0 < Hyperreal.ofSeq f) {x : ℝ*}
    (hx : x ∈ latLine f p) :
    (x < Hyperreal.ofSeq (fun n => 2 * f n * p n) →
      x + 2 * Hyperreal.ofSeq f ∈ latLine f p ∧
      ∀ y ∈ latLine f p, x < y → x + 2 * Hyperreal.ofSeq f ≤ y) ∧
    (Hyperreal.ofSeq (fun n => -(2 * f n * p n)) < x →
      x - 2 * Hyperreal.ofSeq f ∈ latLine f p ∧
      ∀ y ∈ latLine f p, y < x → y ≤ x - 2 * Hyperreal.ofSeq f) := by
  have hpos : ∀ᶠ n in (hyperfilter ℕ : Filter ℕ), 0 < f n := Hyperreal.ofSeq_lt_ofSeq.1 hf
  obtain ⟨u, rfl⟩ := Hyperreal.ofSeq_surjective x
  rw [mem_latLine] at hx
  -- the index relation between two lattice points
  have step : ∀ n, 0 < f n → ∀ k k' : ℤ, 2 * f n * (k : ℝ) < 2 * f n * k' → k + 1 ≤ k' := by
    intro n hn k k' h
    have : (k : ℝ) < k' := lt_of_mul_lt_mul_left h (by linarith)
    exact_mod_cast this
  refine ⟨fun hlt => ⟨?_, fun y hy hxy => ?_⟩, fun hlt => ⟨?_, fun y hy hxy => ?_⟩⟩
  · have hlt' := Hyperreal.ofSeq_lt_ofSeq.1 hlt
    show Hyperreal.ofSeq (fun n => u n + 2 * f n) ∈ latLine f p
    rw [mem_latLine]
    filter_upwards [hx, hlt', hpos] with n ⟨k, hk, hu⟩ h2 h3
    refine ⟨k + 1, ?_, by rw [hu]; push_cast; ring⟩
    have := step n h3 k (p n) (by rw [← hu]; exact h2)
    rw [abs_le] at hk ⊢; omega
  · obtain ⟨v, rfl⟩ := Hyperreal.ofSeq_surjective y
    rw [mem_latLine] at hy
    have hxy' := Hyperreal.ofSeq_lt_ofSeq.1 hxy
    show Hyperreal.ofSeq (fun n => u n + 2 * f n) ≤ Hyperreal.ofSeq v
    refine Hyperreal.ofSeq_le_ofSeq.2 ?_
    filter_upwards [hx, hy, hxy', hpos] with n ⟨k, _, hu⟩ ⟨k', _, hv⟩ h3 h4
    have := step n h4 k k' (by rw [← hu, ← hv]; exact h3)
    have : (k : ℝ) + 1 ≤ k' := by exact_mod_cast this
    rw [hu, hv]; nlinarith
  · have hlt' := Hyperreal.ofSeq_lt_ofSeq.1 hlt
    show Hyperreal.ofSeq (fun n => u n - 2 * f n) ∈ latLine f p
    rw [mem_latLine]
    filter_upwards [hx, hlt', hpos] with n ⟨k, hk, hu⟩ h2 h3
    refine ⟨k - 1, ?_, by rw [hu]; push_cast; ring⟩
    have := step n h3 (-p n) k (by rw [← hu]; push_cast; linarith)
    rw [abs_le] at hk ⊢; omega
  · obtain ⟨v, rfl⟩ := Hyperreal.ofSeq_surjective y
    rw [mem_latLine] at hy
    have hxy' := Hyperreal.ofSeq_lt_ofSeq.1 hxy
    show Hyperreal.ofSeq v ≤ Hyperreal.ofSeq (fun n => u n - 2 * f n)
    refine Hyperreal.ofSeq_le_ofSeq.2 ?_
    filter_upwards [hx, hy, hxy', hpos] with n ⟨k, _, hu⟩ ⟨k', _, hv⟩ h3 h4
    have := step n h4 k' k (by rw [← hu, ← hv]; exact h3)
    have : (k' : ℝ) + 1 ≤ k := by exact_mod_cast this
    rw [hu, hv]; nlinarith

/-- **Discreteness** (`prop:axiom-discrete`) in one statement: no centre lies between
neighbours (any ordered field); in the hyperfinite line `Λ` every element below `Ω`
has an immediate successor, every element above `-Ω` an immediate predecessor, and
every nonempty internal subset of `Λ` has a least and a greatest element. -/
theorem discrete_full (f : ℕ → ℝ) (p : ℕ → ℤ) (hf : 0 < Hyperreal.ofSeq f) :
    (∀ k m : ℤ, ¬ (QE.centre (Hyperreal.ofSeq f) k < QE.centre (Hyperreal.ofSeq f) m ∧
      QE.centre (Hyperreal.ofSeq f) m < QE.centre (Hyperreal.ofSeq f) (k + 1))) ∧
    (∀ x ∈ latLine f p,
      (x < Hyperreal.ofSeq (fun n => 2 * f n * p n) →
        x + 2 * Hyperreal.ofSeq f ∈ latLine f p ∧
        ∀ y ∈ latLine f p, x < y → x + 2 * Hyperreal.ofSeq f ≤ y) ∧
      (Hyperreal.ofSeq (fun n => -(2 * f n * p n)) < x →
        x - 2 * Hyperreal.ofSeq f ∈ latLine f p ∧
        ∀ y ∈ latLine f p, y < x → y ≤ x - 2 * Hyperreal.ofSeq f)) ∧
    (∀ S : Set ℝ*, IsInternal (S : Set (Ult ℝ)) → S ⊆ latLine f p → S.Nonempty →
      (∃ a ∈ S, ∀ y ∈ S, y ≤ a) ∧ (∃ b ∈ S, ∀ y ∈ S, b ≤ y)) :=
  ⟨no_centre_between hf, fun _ hx => latLine_succ_pred f p hf hx,
    fun _ hS hSL hne => internal_subset_latLine_max_min f p hS hSL hne⟩

end QE.Axioms

/-! ## Appendix A -/

namespace QE.NSA

open ArchimedeanClass

/-- **Granular shifts are invisible to the shadow** (`cor:nsa-st-shift`) for an
*arbitrary* infinitesimal `ε₀`: `st(r + kε₀) = r`, and `st(x + δ) = st x` for `δ ≃ 0`. -/
theorem stdPart_shift_general :
    (∀ (r : ℝ) (k : ℤ) (ε₀ : ℝ*), IsInfinitesimal ε₀ → stdPart ((r : ℝ*) + (k : ℝ*) * ε₀) = r) ∧
    (∀ x δ : ℝ*, IsInfinitesimal δ → stdPart (x + δ) = stdPart x) := by
  refine ⟨fun r k ε₀ h => ?_, fun _ _ h => stdPart_add_infinitesimal h⟩
  rw [stdPart_add_infinitesimal (h.int_mul k)]
  exact Hyperreal.stdPart_coe r

/-- **Underspill, both forms** (`cor:nsa-underspill`): an internal set of hypernaturals
containing every unlimited hypernatural contains a standard one; an internal subset
of `ℝ*` containing every positive infinitesimal contains a standard `r > 0`. -/
theorem underspill_both :
    (∀ S : Set (Ult ℕ), IsInternal S → (∀ ν, IsUnlimited ν → ν ∈ S) →
      ∃ m : ℕ, (Germ.const m : Ult ℕ) ∈ S) ∧
    (∀ S : Set ℝ*, IsInternal (S : Set (Ult ℝ)) →
      (∀ δ : ℝ*, 0 < δ → IsInfinitesimal δ → δ ∈ S) → ∃ r : ℝ, 0 < r ∧ (r : ℝ*) ∈ S) :=
  ⟨underspill_internal, underspill_real⟩

end QE.NSA
