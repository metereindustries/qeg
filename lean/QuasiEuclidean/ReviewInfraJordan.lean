-- SPDX-License-Identifier: MIT
-- Copyright 2026 Metere Industries, Inc. Author: Alfredo Metere.
-- Quasi-Euclidean Granular Geometry. Any derivative work must carry this notice:
--   This work is derivative of the Quasi-Euclidean Granular Geometry book
--   authored by Alfredo Metere. Copyright 2026 Metere Industries, Inc.
--   All rights reserved
-- See LICENSE.md and NOTICE.

import QuasiEuclidean.Ch03_Measure
import QuasiEuclidean.NSA_Internal
import QuasiEuclidean.NSA_Loeb
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# Jordan content and the shadow theorem, Jordan case (`thm:shadow`)

Mathlib has no Jordan content, so we build it.  A set `E ⊆ ℝⁿ` (modelled as
`Fin n → ℝ`) *has Jordan content `J`* if for every `δ > 0`

* there are finitely many pairwise disjoint half-open boxes `∏ [aᵢ, bᵢ)` inside
  `E` whose total volume exceeds `J - δ` (inner approximation), and
* there are finitely many closed boxes `∏ [aᵢ, bᵢ]` covering `E` whose total
  volume is below `J + δ` (outer approximation).

This is the classical Darboux–Jordan definition (inner and outer elementary
sets of volumes within `δ`); volumes of boxes are the products of side
lengths, so no measure theory is involved.  A Jordan-measurable set is
bounded (it is covered by finitely many boxes).

Main results.

* `jordan_shadow` (Lebesgue-free): `(2ε)ⁿ · #(E ∩ (2εℤ)ⁿ) → J` as `ε → 0⁺`.
* `jordan_shadow_star` (Lebesgue-free): for a positive infinitesimal `ε ∈ ℝ*`,
  `*E ∩ 𝕃ⁿ` is internal and hyperfinite, and
  `st ((2ε)ⁿ · #(*E ∩ 𝕃ⁿ)) = J`.  This is the printed form of `thm:shadow`
  with the classical size of `E` given by its Jordan content.
* `jordan_content_unique`: the Jordan content is unique (proved through the
  granular count, with no measure theory).
* `isJordanContent_Icc`, `isJordanContent_hbox`: boxes are Jordan measurable
  with content the product of the side lengths.
* `jordan_volume` (shadow, uses Lebesgue measure): the Jordan content equals
  Lebesgue measure, `volume E = ofReal J`.
* `shadow_jordan` (shadow): the combined statement of `thm:shadow`:
  `*E ∩ 𝕃ⁿ` is internal and `λ(E) = st μ(*E ∩ 𝕃ⁿ)`.
-/

set_option linter.unusedSectionVars false

namespace QE.Measure

open Finset Filter Topology

variable {n : ℕ}

/-- The half-open box `∏ᵢ [aᵢ, bᵢ)`. -/
def hbox (a b : Fin n → ℝ) : Set (Fin n → ℝ) := Set.pi Set.univ fun i => Set.Ico (a i) (b i)

/-- The (elementary) volume of a box with corners `a ≤ b`: the product of side lengths. -/
def bvol (a b : Fin n → ℝ) : ℝ := ∏ i, (b i - a i)

/-- The lattice indices `k ∈ ℤⁿ` whose point `2εk` lies in `E`. -/
def latPts (ε : ℝ) (E : Set (Fin n → ℝ)) : Set (Fin n → ℤ) :=
  {k | (fun i => 2 * ε * (k i : ℝ)) ∈ E}

/-- The granular measure `(2ε)ⁿ · #(E ∩ (2εℤ)ⁿ)` of the lattice trace of a real set. -/
noncomputable def gmu (ε : ℝ) (E : Set (Fin n → ℝ)) : ℝ :=
  (2 * ε) ^ n * ((latPts ε E).ncard : ℝ)

/-- **Jordan content.** `E` has Jordan content `J`: inner disjoint half-open boxes of
total volume `> J - δ` and outer closed boxes of total volume `< J + δ`, for every
`δ > 0`. -/
structure IsJordanContent (E : Set (Fin n → ℝ)) (J : ℝ) : Prop where
  inner : ∀ δ > 0, ∃ (m : ℕ) (a b : Fin m → Fin n → ℝ), (∀ r, a r ≤ b r) ∧
    Pairwise (fun r s => Disjoint (hbox (a r) (b r)) (hbox (a s) (b s))) ∧
    (∀ r, hbox (a r) (b r) ⊆ E) ∧ J - δ < ∑ r, bvol (a r) (b r)
  outer : ∀ δ > 0, ∃ (m : ℕ) (a b : Fin m → Fin n → ℝ), (∀ r, a r ≤ b r) ∧
    E ⊆ ⋃ r, Set.Icc (a r) (b r) ∧ ∑ r, bvol (a r) (b r) < J + δ

/-- `E` is Jordan measurable: it has a Jordan content. -/
def JordanMeasurable (E : Set (Fin n → ℝ)) : Prop := ∃ J, IsJordanContent E J

/-! ## Lattice points of boxes -/

theorem bvol_nonneg {a b : Fin n → ℝ} (h : a ≤ b) : 0 ≤ bvol a b :=
  prod_nonneg fun i _ => sub_nonneg.2 (h i)

theorem latPts_mono (ε : ℝ) {E F : Set (Fin n → ℝ)} (h : E ⊆ F) : latPts ε E ⊆ latPts ε F :=
  fun _ hk => h hk

theorem latPts_Icc {ε : ℝ} (hε : 0 < ε) (a b : Fin n → ℝ) :
    latPts ε (Set.Icc a b) =
      ↑(Fintype.piFinset fun i => Icc ⌈a i / (2 * ε)⌉ ⌊b i / (2 * ε)⌋) := by
  have h2 : 0 < 2 * ε := by linarith
  ext k
  simp only [latPts, Set.mem_ofPred_eq, Set.mem_Icc, mem_coe, Fintype.mem_piFinset, mem_Icc,
    Pi.le_def]
  constructor
  · rintro ⟨h1, h3⟩ i
    refine ⟨Int.ceil_le.2 ?_, Int.le_floor.2 ?_⟩
    · rw [div_le_iff₀ h2]; linarith [h1 i]
    · rw [le_div_iff₀ h2]; linarith [h3 i]
  · intro h
    refine ⟨fun i => ?_, fun i => ?_⟩
    · have := Int.ceil_le.1 (h i).1
      rw [div_le_iff₀ h2] at this; linarith
    · have := Int.le_floor.1 (h i).2
      rw [le_div_iff₀ h2] at this; linarith

theorem latPts_hbox {ε : ℝ} (hε : 0 < ε) (a b : Fin n → ℝ) :
    latPts ε (hbox a b) =
      ↑(Fintype.piFinset fun i => Ico ⌈a i / (2 * ε)⌉ ⌈b i / (2 * ε)⌉) := by
  have h2 : 0 < 2 * ε := by linarith
  ext k
  simp only [latPts, hbox, Set.mem_ofPred_eq, Set.mem_pi, Set.mem_univ, Set.mem_Ico,
    forall_true_left, mem_coe, Fintype.mem_piFinset, mem_Ico]
  refine forall_congr' fun i => ?_
  constructor
  · rintro ⟨h1, h3⟩
    refine ⟨Int.ceil_le.2 ?_, Int.lt_ceil.2 ?_⟩
    · rw [div_le_iff₀ h2]; linarith
    · rw [lt_div_iff₀ h2]; linarith
  · rintro ⟨h1, h3⟩
    have h1' := Int.ceil_le.1 h1
    have h3' := Int.lt_ceil.1 h3
    rw [div_le_iff₀ h2] at h1'
    rw [lt_div_iff₀ h2] at h3'
    constructor <;> linarith

/-- One-dimensional count for a half-open interval: `|2ε #([a,b) ∩ 2εℤ) - (b-a)| ≤ 2ε`. -/
theorem latCountIco_bound {ε : ℝ} (hε : 0 < ε) {a b : ℝ} (hab : a ≤ b) :
    |2 * ε * ((Ico ⌈a / (2 * ε)⌉ ⌈b / (2 * ε)⌉).card : ℝ) - (b - a)| ≤ 2 * ε := by
  rw [Int.card_Ico]
  set x := a / (2 * ε)
  set y := b / (2 * ε)
  have h2 : 0 < 2 * ε := by linarith
  have hxy : x ≤ y := div_le_div_of_nonneg_right hab h2.le
  have hcc : ⌈x⌉ ≤ ⌈y⌉ := Int.ceil_mono hxy
  have c1 := Int.le_ceil x
  have c2 := Int.ceil_lt_add_one x
  have d1 := Int.le_ceil y
  have d2 := Int.ceil_lt_add_one y
  have hc : (((⌈y⌉ - ⌈x⌉).toNat : ℕ) : ℝ) = ((⌈y⌉ : ℝ) - ⌈x⌉) := by
    rw [← Int.cast_natCast, Int.toNat_of_nonneg (by omega)]; push_cast; ring
  rw [hc]
  have ha : a = 2 * ε * x := by simp only [x]; field_simp
  have hb : b = 2 * ε * y := by simp only [y]; field_simp
  rw [abs_le]
  constructor
  · rw [ha, hb]; nlinarith
  · rw [ha, hb]; nlinarith

theorem shadow_intervalIco {a b : ℝ} (hab : a ≤ b) :
    Tendsto (fun ε => 2 * ε * ((Ico ⌈a / (2 * ε)⌉ ⌈b / (2 * ε)⌉).card : ℝ))
      (𝓝[>] 0) (𝓝 (b - a)) := by
  rw [Metric.tendsto_nhdsWithin_nhds]
  intro δ hδ
  refine ⟨δ / 4, by positivity, fun ε hε hd => ?_⟩
  have hε' : 0 < ε := hε
  rw [Real.dist_eq] at hd ⊢
  rw [sub_zero, abs_of_pos hε'] at hd
  have := latCountIco_bound hε' hab
  linarith

theorem gmu_hbox {ε : ℝ} (hε : 0 < ε) (a b : Fin n → ℝ) :
    gmu ε (hbox a b) = ∏ i, 2 * ε * ((Ico ⌈a i / (2 * ε)⌉ ⌈b i / (2 * ε)⌉).card : ℝ) := by
  unfold gmu
  rw [latPts_hbox hε, Set.ncard_coe_finset, Fintype.card_piFinset]; push_cast
  rw [prod_mul_distrib]; simp

theorem gmu_Icc {ε : ℝ} (hε : 0 < ε) (a b : Fin n → ℝ) :
    gmu ε (Set.Icc a b) = ∏ i, 2 * ε * (latCount ε (a i) (b i) : ℝ) := by
  unfold gmu
  rw [latPts_Icc hε, Set.ncard_coe_finset]
  exact box_count_eq n ε a b

/-- Shadow of a half-open box. -/
theorem tendsto_gmu_hbox {a b : Fin n → ℝ} (hab : a ≤ b) :
    Tendsto (fun ε => gmu ε (hbox a b)) (𝓝[>] 0) (𝓝 (bvol a b)) := by
  have h : Tendsto (fun ε => ∏ i, 2 * ε * ((Ico ⌈a i / (2 * ε)⌉ ⌈b i / (2 * ε)⌉).card : ℝ))
      (𝓝[>] 0) (𝓝 (∏ i, (b i - a i))) :=
    tendsto_finsetProd _ fun i _ => shadow_intervalIco (hab i)
  refine h.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with ε hε
  exact (gmu_hbox hε a b).symm

/-- Shadow of a closed box. -/
theorem tendsto_gmu_Icc {a b : Fin n → ℝ} (hab : a ≤ b) :
    Tendsto (fun ε => gmu ε (Set.Icc a b)) (𝓝[>] 0) (𝓝 (bvol a b)) := by
  refine (shadow_box n hab).congr' ?_
  filter_upwards [self_mem_nhdsWithin] with ε hε
  exact (gmu_Icc hε a b).symm

/-! ## Inner and outer counts -/

/-- Outer bound: if `E` is covered by finitely many closed boxes, its lattice trace is
finite and its granular measure is at most the sum of theirs. -/
theorem gmu_le_of_cover {ε : ℝ} (hε : 0 < ε) {E : Set (Fin n → ℝ)} {m : ℕ}
    (a b : Fin m → Fin n → ℝ) (hE : E ⊆ ⋃ r, Set.Icc (a r) (b r)) :
    (latPts ε E).Finite ∧ gmu ε E ≤ ∑ r, gmu ε (Set.Icc (a r) (b r)) := by
  classical
  set F : Fin m → Finset (Fin n → ℤ) :=
    fun r => Fintype.piFinset fun i => Icc ⌈a r i / (2 * ε)⌉ ⌊b r i / (2 * ε)⌋
  have hsub : latPts ε E ⊆ ↑(univ.biUnion F) := by
    intro k hk
    obtain ⟨r, hr⟩ := Set.mem_iUnion.1 (hE hk)
    have : k ∈ latPts ε (Set.Icc (a r) (b r)) := hr
    rw [latPts_Icc hε, mem_coe] at this
    rw [mem_coe, mem_biUnion]
    exact ⟨r, mem_univ _, this⟩
  have hfin : (latPts ε E).Finite := (finite_toSet _).subset hsub
  refine ⟨hfin, ?_⟩
  have h1 : (latPts ε E).ncard ≤ (univ.biUnion F).card := by
    rw [← Set.ncard_coe_finset]; exact Set.ncard_le_ncard hsub (finite_toSet _)
  have h2 : (univ.biUnion F).card ≤ ∑ r, (F r).card := card_biUnion_le
  have h3 : ∀ r, gmu ε (Set.Icc (a r) (b r)) = (2 * ε) ^ n * ((F r).card : ℝ) := by
    intro r; unfold gmu; rw [latPts_Icc hε, Set.ncard_coe_finset]
  simp_rw [h3]
  rw [← mul_sum]
  unfold gmu
  have h2ε : 0 ≤ (2 * ε) ^ n := by positivity
  refine mul_le_mul_of_nonneg_left ?_ h2ε
  have : ((latPts ε E).ncard : ℝ) ≤ ((∑ r, (F r).card : ℕ) : ℝ) := by exact_mod_cast h1.trans h2
  simpa using this

/-- Inner bound: disjoint half-open boxes inside `E` (whose lattice trace is finite)
have total granular measure at most that of `E`. -/
theorem sum_le_gmu_of_inner {ε : ℝ} (hε : 0 < ε) {E : Set (Fin n → ℝ)} {m : ℕ}
    (a b : Fin m → Fin n → ℝ)
    (hd : Pairwise (fun r s => Disjoint (hbox (a r) (b r)) (hbox (a s) (b s))))
    (hin : ∀ r, hbox (a r) (b r) ⊆ E) (hfin : (latPts ε E).Finite) :
    ∑ r, gmu ε (hbox (a r) (b r)) ≤ gmu ε E := by
  classical
  set F : Fin m → Finset (Fin n → ℤ) :=
    fun r => Fintype.piFinset fun i => Ico ⌈a r i / (2 * ε)⌉ ⌈b r i / (2 * ε)⌉
  have hF : ∀ r, (F r : Set (Fin n → ℤ)) = latPts ε (hbox (a r) (b r)) :=
    fun r => (latPts_hbox hε (a r) (b r)).symm
  have hsub : (↑(univ.biUnion F) : Set (Fin n → ℤ)) ⊆ latPts ε E := by
    intro k hk
    rw [mem_coe, mem_biUnion] at hk
    obtain ⟨r, -, hr⟩ := hk
    rw [← mem_coe, hF r] at hr
    exact latPts_mono ε (hin r) hr
  have hdisj : ((univ : Finset (Fin m)) : Set (Fin m)).PairwiseDisjoint F := by
    intro r _ s _ hrs
    rw [Function.onFun, ← disjoint_coe, hF r, hF s]
    exact Set.disjoint_left.2 fun k hk1 hk2 => Set.disjoint_left.1 (hd hrs) hk1 hk2
  have h1 : (univ.biUnion F).card = ∑ r, (F r).card := card_biUnion hdisj
  have h2 : (univ.biUnion F).card ≤ (latPts ε E).ncard := by
    rw [← Set.ncard_coe_finset]; exact Set.ncard_le_ncard hsub hfin
  have h3 : ∀ r, gmu ε (hbox (a r) (b r)) = (2 * ε) ^ n * ((F r).card : ℝ) := by
    intro r; unfold gmu; rw [← hF r, Set.ncard_coe_finset]
  simp_rw [h3]
  rw [← mul_sum]
  unfold gmu
  have h2ε : 0 ≤ (2 * ε) ^ n := by positivity
  refine mul_le_mul_of_nonneg_left ?_ h2ε
  have : ((∑ r, (F r).card : ℕ) : ℝ) ≤ ((latPts ε E).ncard : ℝ) := by
    exact_mod_cast h1 ▸ h2
  simpa using this

/-! ## The shadow theorem, Jordan case -/

/-- **Shadow theorem, Jordan case (limit form, Lebesgue-free).** If `E ⊆ ℝⁿ` has Jordan
content `J`, then `(2ε)ⁿ · #(E ∩ (2εℤ)ⁿ) → J` as `ε → 0⁺`. -/
theorem jordan_shadow {E : Set (Fin n → ℝ)} {J : ℝ} (hJ : IsJordanContent E J) :
    Tendsto (fun ε => gmu ε E) (𝓝[>] 0) (𝓝 J) := by
  obtain ⟨m₀, a₀, b₀, -, hE₀, -⟩ := hJ.outer 1 one_pos
  have hfin : ∀ᶠ ε in 𝓝[>] (0 : ℝ), (latPts ε E).Finite := by
    filter_upwards [self_mem_nhdsWithin] with ε hε
    exact (gmu_le_of_cover hε a₀ b₀ hE₀).1
  rw [tendsto_order]
  constructor
  · intro c hc
    obtain ⟨m, a, b, hab, hd, hin, hsum⟩ := hJ.inner (J - c) (by linarith)
    have hL : Tendsto (fun ε => ∑ r, gmu ε (hbox (a r) (b r))) (𝓝[>] 0)
        (𝓝 (∑ r, bvol (a r) (b r))) :=
      tendsto_finsetSum _ fun r _ => tendsto_gmu_hbox (hab r)
    have hlt : c < ∑ r, bvol (a r) (b r) := by linarith
    filter_upwards [hL.eventually_const_lt hlt, self_mem_nhdsWithin, hfin] with ε h1 hε h3
    exact h1.trans_le (sum_le_gmu_of_inner hε a b hd hin h3)
  · intro c hc
    obtain ⟨m, a, b, hab, hE, hsum⟩ := hJ.outer (c - J) (by linarith)
    have hU : Tendsto (fun ε => ∑ r, gmu ε (Set.Icc (a r) (b r))) (𝓝[>] 0)
        (𝓝 (∑ r, bvol (a r) (b r))) :=
      tendsto_finsetSum _ fun r _ => tendsto_gmu_Icc (hab r)
    have hlt : ∑ r, bvol (a r) (b r) < c := by linarith
    filter_upwards [hU.eventually_lt_const hlt, self_mem_nhdsWithin] with ε h1 hε
    exact ((gmu_le_of_cover hε a b hE).2).trans_lt h1

/-- The Jordan content is unique (a consequence of the granular count). -/
theorem jordan_content_unique {E : Set (Fin n → ℝ)} {J J' : ℝ} (hJ : IsJordanContent E J)
    (hJ' : IsJordanContent E J') : J = J' :=
  tendsto_nhds_unique (jordan_shadow hJ) (jordan_shadow hJ')

/-- A Jordan-measurable set is bounded. -/
theorem IsJordanContent.isBounded {E : Set (Fin n → ℝ)} {J : ℝ} (hJ : IsJordanContent E J) :
    Bornology.IsBounded E := by
  obtain ⟨m, a, b, -, hE, -⟩ := hJ.outer 1 one_pos
  refine Bornology.IsBounded.subset ?_ hE
  exact Bornology.isBounded_iUnion.2 fun r => Metric.isBounded_Icc (a r) (b r)

/-- The Jordan content of a measurable set is nonnegative. -/
theorem IsJordanContent.nonneg {E : Set (Fin n → ℝ)} {J : ℝ} (hJ : IsJordanContent E J) :
    0 ≤ J := by
  refine ge_of_tendsto (jordan_shadow hJ) ?_
  filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε)
  unfold gmu; positivity

/-- A closed box is Jordan measurable, with content the product of its sides. -/
theorem isJordanContent_Icc {a b : Fin n → ℝ} (hab : a ≤ b) :
    IsJordanContent (Set.Icc a b) (bvol a b) := by
  refine ⟨fun δ hδ => ⟨1, fun _ => a, fun _ => b, fun _ => hab, ?_, ?_, ?_⟩,
    fun δ hδ => ⟨1, fun _ => a, fun _ => b, fun _ => hab, ?_, ?_⟩⟩
  · intro r s hrs; exact absurd (Subsingleton.elim r s) hrs
  · intro _ x hx
    exact ⟨fun i => (hx i (Set.mem_univ i)).1, fun i => (hx i (Set.mem_univ i)).2.le⟩
  · simp; linarith
  · intro x hx; exact Set.mem_iUnion.2 ⟨0, hx⟩
  · simp; linarith

/-- A half-open box is Jordan measurable, with content the product of its sides. -/
theorem isJordanContent_hbox {a b : Fin n → ℝ} (hab : a ≤ b) :
    IsJordanContent (hbox a b) (bvol a b) := by
  refine ⟨fun δ hδ => ⟨1, fun _ => a, fun _ => b, fun _ => hab, ?_, ?_, ?_⟩,
    fun δ hδ => ⟨1, fun _ => a, fun _ => b, fun _ => hab, ?_, ?_⟩⟩
  · intro r s hrs; exact absurd (Subsingleton.elim r s) hrs
  · intro _; exact le_rfl
  · simp; linarith
  · intro x hx
    exact Set.mem_iUnion.2 ⟨0, fun i => (hx i (Set.mem_univ i)).1,
      fun i => (hx i (Set.mem_univ i)).2.le⟩
  · simp; linarith

/-! ## The hyperreal (printed) form -/

open QE.NSA ArchimedeanClass in
/-- **Shadow theorem, Jordan case (printed form, Lebesgue-free).** Let `E ⊆ ℝⁿ` have
Jordan content `J` and let `ε ∈ ℝ*` be a positive infinitesimal. Then `*E ∩ 𝕃ⁿ`
(`𝕃ⁿ = (2ε ℤ*)ⁿ`) is internal and hyperfinite, and
`st ((2ε)ⁿ · #(*E ∩ 𝕃ⁿ)) = J`. -/
theorem jordan_shadow_star {E : Set (Fin n → ℝ)} {J : ℝ} (hJ : IsJordanContent E J)
    (ε : ℝ*) (hε0 : 0 < ε) (hε : IsInfinitesimal ε) :
    IsInternal (starSet E ∩ latN (d := n) ε) ∧ IsHyperfinite (starSet E ∩ latN (d := n) ε) ∧
      stdPart ((2 * ε) ^ n *
        HypMeasure.hcardR (starSet E ∩ latN (d := n) ε)) = J := by
  classical
  obtain ⟨e, rfl⟩ := Hyperreal.ofSeq_surjective ε
  have he : ∀ᶠ m in (hyperfilter ℕ : Filter ℕ), 0 < e m := Hyperreal.ofSeq_lt_ofSeq.1 hε0
  obtain ⟨m₀, a₀, b₀, -, hE₀, -⟩ := hJ.outer 1 one_pos
  -- the level sets `E ∩ (2 e_m ℤ)ⁿ`
  set L : ℕ → Set (Fin n → ℝ) := fun m => E ∩ {y | ∀ i, ∃ k : ℤ, y i = 2 * e m * k}
  have hLimg : ∀ m, 0 < e m →
      L m = (fun k : Fin n → ℤ => fun i => 2 * e m * (k i : ℝ)) '' latPts (e m) E := by
    intro m hm
    ext y
    simp only [L, Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_image, latPts]
    constructor
    · rintro ⟨hy, hk⟩
      choose k hk using hk
      refine ⟨k, ?_, ?_⟩
      · have : (fun i => 2 * e m * (k i : ℝ)) = y := funext fun i => (hk i).symm
        rw [this]; exact hy
      · exact funext fun i => (hk i).symm
    · rintro ⟨k, hk, rfl⟩
      exact ⟨hk, fun i => ⟨k i, rfl⟩⟩
  have hinj : ∀ m, 0 < e m →
      Function.Injective (fun k : Fin n → ℤ => fun i => 2 * e m * (k i : ℝ)) := by
    intro m hm k k' h
    funext i
    have := congrFun h i
    have h2 : (2 * e m) ≠ 0 := by positivity
    exact_mod_cast mul_left_cancel₀ h2 this
  have hLfin : ∀ m, 0 < e m → (L m).Finite := by
    intro m hm
    rw [hLimg m hm]
    exact ((gmu_le_of_cover hm a₀ b₀ hE₀).1).image _
  set A : ℕ → Finset (Fin n → ℝ) := fun m =>
    if h : 0 < e m then (hLfin m h).toFinset else ∅
  have hset : starSet E ∩ latN (d := n) (Hyperreal.ofSeq e) = hfin A := by
    unfold starSet hfin
    rw [latN_eq_internal, ← internal_inter]
    refine internal_congr ?_
    filter_upwards [he] with m hm
    simp only [A, hm, ↓reduceDIte, Set.Finite.coe_toFinset]
    rfl
  have hcardA : ∀ m, 0 < e m → ((A m).card : ℝ) = ((latPts (e m) E).ncard : ℝ) := by
    intro m hm
    simp only [A, hm, ↓reduceDIte]
    rw [← Set.ncard_eq_toFinset_card _ (hLfin m hm), hLimg m hm,
      Set.ncard_image_of_injective _ (hinj m hm)]
  refine ⟨hset ▸ (IsHyperfinite.isInternal ⟨A, rfl⟩), ⟨A, hset⟩, ?_⟩
  rw [hset]
  have hval : (2 * Hyperreal.ofSeq e) ^ n * HypMeasure.hcardR (hfin A) =
        Hyperreal.ofSeq (fun m => gmu (e m) E) := by
    rw [HypMeasure.hcardR, hcard_hfin]
    show Hyperreal.ofSeq (fun m => (2 * e m) ^ n * ((A m).card : ℝ)) = _
    refine Germ.coe_eq.2 ?_
    filter_upwards [he] with m hm
    simp only [gmu, hcardA m hm]
  rw [hval]
  refine Hyperreal.stdPart_of_tendsto (Hyperreal.tendsto_ofSeq.2 ?_)
  have hlim : Tendsto e (hyperfilter ℕ : Filter ℕ) (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, he⟩
    rw [Metric.tendsto_nhds]
    intro t ht
    filter_upwards [(isInfinitesimal_ofSeq_iff e).1 hε t ht] with m hm
    simpa [Real.dist_eq] using hm
  exact (jordan_shadow hJ).comp hlim

/-! ## Comparison with Lebesgue measure (shadow results) -/

open MeasureTheory in
/-- **Jordan content is Lebesgue measure** (shadow, uses Lebesgue measure). -/
theorem jordan_volume {E : Set (Fin n → ℝ)} {J : ℝ} (hJ : IsJordanContent E J) :
    volume E = ENNReal.ofReal J := by
  have hinner : ∀ δ > 0, ENNReal.ofReal (J - δ) ≤ volume E := by
    intro δ hδ
    obtain ⟨m, a, b, hab, hd, hin, hsum⟩ := hJ.inner δ hδ
    have hmeas : ∀ r, MeasurableSet (hbox (a r) (b r)) :=
      fun r => MeasurableSet.univ_pi fun i => measurableSet_Ico
    calc ENNReal.ofReal (J - δ) ≤ ENNReal.ofReal (∑ r, bvol (a r) (b r)) :=
          ENNReal.ofReal_le_ofReal hsum.le
      _ = ∑ r, ENNReal.ofReal (bvol (a r) (b r)) :=
          ENNReal.ofReal_sum_of_nonneg fun r _ => bvol_nonneg (hab r)
      _ = ∑ r, volume (hbox (a r) (b r)) := by
          refine sum_congr rfl fun r _ => ?_
          rw [hbox, Real.volume_pi_Ico, bvol, ENNReal.ofReal_prod_of_nonneg]
          exact fun i _ => sub_nonneg.2 (hab r i)
      _ = volume (⋃ r, hbox (a r) (b r)) := by
          rw [measure_iUnion hd hmeas, tsum_fintype]
      _ ≤ volume E := measure_mono (Set.iUnion_subset hin)
  have houter : ∀ δ > 0, volume E ≤ ENNReal.ofReal (J + δ) ∧ 0 ≤ J + δ := by
    intro δ hδ
    obtain ⟨m, a, b, hab, hE, hsum⟩ := hJ.outer δ hδ
    have hs0 : 0 ≤ ∑ r, bvol (a r) (b r) := sum_nonneg fun r _ => bvol_nonneg (hab r)
    refine ⟨?_, by linarith⟩
    calc volume E ≤ volume (⋃ r, Set.Icc (a r) (b r)) := measure_mono hE
      _ ≤ ∑ r, volume (Set.Icc (a r) (b r)) := measure_iUnion_fintype_le _ _
      _ = ∑ r, ENNReal.ofReal (bvol (a r) (b r)) := by
          refine sum_congr rfl fun r _ => ?_
          rw [Real.volume_Icc_pi, bvol, ENNReal.ofReal_prod_of_nonneg]
          exact fun i _ => sub_nonneg.2 (hab r i)
      _ = ENNReal.ofReal (∑ r, bvol (a r) (b r)) :=
          (ENNReal.ofReal_sum_of_nonneg fun r _ => bvol_nonneg (hab r)).symm
      _ ≤ ENNReal.ofReal (J + δ) := ENNReal.ofReal_le_ofReal hsum.le
  have hfin : volume E ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top (houter 1 one_pos).1
  have h1 : (volume E).toReal ≤ J := by
    refine le_of_forall_pos_le_add fun δ hδ => ?_
    exact ENNReal.toReal_le_of_le_ofReal (houter δ hδ).2 (houter δ hδ).1
  have h2 : J ≤ (volume E).toReal := by
    refine le_of_forall_pos_le_add fun δ hδ => ?_
    have := (ENNReal.ofReal_le_iff_le_toReal hfin).1 (hinner δ hδ)
    linarith
  rw [← ENNReal.ofReal_toReal hfin, le_antisymm h1 h2]

open QE.NSA ArchimedeanClass MeasureTheory in
/-- **Shadow theorem, Jordan case (`thm:shadow`), combined statement.** For a
Jordan-measurable `E ⊆ ℝⁿ` and a positive infinitesimal `ε`, `*E ∩ 𝕃ⁿ` is internal
and `λ(E) = st μ(*E ∩ 𝕃ⁿ)`, with `λ` Lebesgue measure; moreover the limit form
holds for real `ε → 0⁺`, and the explicit one-dimensional box bound holds. -/
theorem shadow_jordan {E : Set (Fin n → ℝ)} (hE : JordanMeasurable E) :
    (volume E ≠ ⊤) ∧
    (∀ ε : ℝ*, 0 < ε → IsInfinitesimal ε →
      IsInternal (starSet E ∩ latN (d := n) ε) ∧
      (volume E).toReal = stdPart ((2 * ε) ^ n *
        HypMeasure.hcardR (starSet E ∩ latN (d := n) ε))) ∧
    Tendsto (fun ε => gmu ε E) (𝓝[>] 0) (𝓝 (volume E).toReal) ∧
    (∀ {ε a b : ℝ}, 0 < ε → a ≤ b → |2 * ε * latCount ε a b - (b - a)| ≤ 2 * ε) := by
  obtain ⟨J, hJ⟩ := hE
  have hv := jordan_volume hJ
  have hvJ : (volume E).toReal = J := by rw [hv, ENNReal.toReal_ofReal hJ.nonneg]
  refine ⟨by rw [hv]; exact ENNReal.ofReal_ne_top, fun ε hε0 hε => ?_, hvJ ▸ jordan_shadow hJ,
    fun hε hab => latCount_bound hε hab⟩
  obtain ⟨h1, -, h3⟩ := jordan_shadow_star hJ ε hε0 hε
  exact ⟨h1, hvJ.trans h3.symm⟩

end QE.Measure
