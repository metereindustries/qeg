-- SPDX-License-Identifier: MIT
-- Copyright 2026 Metere Industries, Inc. Author: Alfredo Metere.
-- Quasi-Euclidean Granular Geometry. Any derivative work must carry this notice:
--   This work is derivative of the Quasi-Euclidean Granular Geometry book
--   authored by Alfredo Metere. Copyright 2026 Metere Industries, Inc.
--   All rights reserved
-- See LICENSE.md and NOTICE.

import QuasiEuclidean.OpenGeo
import QuasiEuclidean.NSA_Internal
import QuasiEuclidean.Ch10c_CubicalInfra

/-!
# Enlargements and standard boosts

The countable ultrapower `ℝ^ℕ/U` is not saturated enough to contain a hyperfinite set
containing every standard real.  An **enlargement** is: index by the finite subsets
`J ⊆ ℝ`, and take an ultrafilter `U` containing every cone `{J | S ⊆ J}` (it exists:
the cones form the filter `atTop` on `Finset ℝ`).  In `ℝ^I/U` the hyperfinite set
`[J ↦ J]` contains every standard real (`mem_eventually`), which is the only use of
saturation in the book's construction of a hyperfinite point set whose retained
boundary term of a segment is invariant under all standard boosts.

Everything is finite combinatorics at each index `J`, followed by `U`-almost-everywhere
reasoning.  No measure theory is used.
-/

namespace QE.Enlargement

open Filter Finset QE.OpenGeo

/-- The index set: finite subsets of `ℝ`. -/
abbrev Idx := Finset ℝ

/-- An ultrafilter on `Finset ℝ` refining the cone filter `atTop`. -/
noncomputable def U : Ultrafilter Idx := Ultrafilter.of (atTop : Filter Idx)

/-- The enlargement `*ℝ = ℝ^I/U`. -/
abbrev M := (U : Filter Idx).Germ ℝ

theorem U_le_atTop : (U : Filter Idx) ≤ atTop := Ultrafilter.of_le _

/-- **Enlargement property**: every standard real lies in `J` for `U`-almost every `J`,
i.e. the hyperfinite set `[J ↦ J]` contains every standard real. -/
theorem mem_eventually (r : ℝ) : ∀ᶠ J in (U : Filter Idx), r ∈ J := by
  have h : ∀ᶠ J in (atTop : Filter Idx), ({r} : Finset ℝ) ≤ J := eventually_ge_atTop _
  exact (h.filter_mono U_le_atTop).mono fun J hJ => singleton_subset_iff.mp hJ

/-- The internal cardinality `[J ↦ #J]` is unlimited. -/
theorem card_eventually (m : ℕ) : ∀ᶠ J in (U : Filter Idx), m ≤ J.card := by
  set S : Finset ℝ := (range m).image (Nat.cast : ℕ → ℝ)
  have hS : S.card = m := by
    rw [card_image_of_injective _ Nat.cast_injective, card_range]
  have h : ∀ᶠ J in (atTop : Filter Idx), S ≤ J := eventually_ge_atTop _
  exact (h.filter_mono U_le_atTop).mono fun J hJ => hS ▸ card_le_card hJ

/-- `*ℝ` as Mathlib's `Filter.Product`, carrying the ultrapower structure. -/
abbrev MPow : Type := (U : Filter Idx).Product fun _ : Idx => ℝ

theorem mpow_eq : MPow = M := rfl

open FirstOrder FirstOrder.Language in
/-- `*ℝ` is an elementary extension of `ℝ` for the language with a symbol for every
real function and relation (Łoś). -/
noncomputable def starEmbedding : QE.NSA.realLang.ElementaryEmbedding ℝ MPow :=
  QE.NSA.diagonalEmbedding QE.NSA.realLang ℝ U

/-- Infinitesimals of `*ℝ`. -/
def Infinitesimal (x : M) : Prop := ∀ r : ℝ, 0 < r → (↑(-r) : M) < x ∧ x < ↑r

theorem infinitesimal_coe {f : Idx → ℝ} :
    Infinitesimal (f : M) ↔ ∀ r : ℝ, 0 < r → ∀ᶠ J in (U : Filter Idx), |f J| < r := by
  unfold Infinitesimal
  refine forall₂_congr fun r _ => ?_
  show ((fun _ => -r : Idx → ℝ) : M) < ↑f ∧ (f : M) < ((fun _ => r : Idx → ℝ) : M) ↔ _
  rw [Filter.Germ.coe_lt, Filter.Germ.coe_lt, ← eventually_and]
  exact eventually_congr (Eventually.of_forall fun J => by rw [abs_lt])


/-! ## The finite construction at one index -/

section Finite

/-- Boosts are linear. -/
theorem boost_smul (l s : ℝ) (p : ℝ × ℝ) : boost l (s • p) = s • boost l p := by
  unfold boost; ext <;> simp <;> ring

theorem boost_injective {l : ℝ} (hl : 0 < l) : Function.Injective (boost l) := by
  intro p q h
  have := congrArg (boost l⁻¹) h
  rwa [boost_mul _ _ (inv_ne_zero hl.ne') hl.ne', boost_mul _ _ (inv_ne_zero hl.ne') hl.ne',
    inv_mul_cancel₀ hl.ne', boost_one, boost_one] at this

/-- The standard segment `F = {s b : s₀ ≤ s ≤ s₁}`. -/
def seg (s₀ s₁ : ℝ) (b : ℝ × ℝ) : Set (ℝ × ℝ) := {x | ∃ s, s₀ ≤ s ∧ s ≤ s₁ ∧ x = s • b}

/-- The standard box `[-R, R]²`. -/
def box (R : ℝ) : Set (ℝ × ℝ) := {x | |x.1| ≤ R ∧ |x.2| ≤ R}

/-- Boosted copies of a segment avoiding `0` on a non-null line are pairwise disjoint. -/
theorem boost_seg_disjoint {s₀ s₁ : ℝ} (hs₀ : 0 < s₀) {b : ℝ × ℝ} (hb : b.1 ^ 2 ≠ b.2 ^ 2)
    {l l' : ℝ} (hl : 0 < l) (hl' : 0 < l') {x : ℝ × ℝ} (hx : x ∈ boost l '' seg s₀ s₁ b)
    (hx' : x ∈ boost l' '' seg s₀ s₁ b) : l = l' := by
  obtain ⟨_, ⟨s, h1, _, rfl⟩, rfl⟩ := hx
  obtain ⟨_, ⟨s', _, _, rfl⟩, h⟩ := hx'
  rw [boost_smul, boost_smul] at h
  exact boost_lines_distinct l l' s s' hl hl' b hb (by linarith) h.symm

/-- The truncated lattice `h ℤ² ∩ [-hN, hN]²`. -/
noncomputable def latPts (h : ℝ) (N : ℕ) : Finset (ℝ × ℝ) :=
  ((Icc (-(N : ℤ)) N) ×ˢ (Icc (-(N : ℤ)) N)).image (fun k => (h * k.1, h * k.2))

/-- The `n` equally spaced points `B_l(s₀ b + (j/n)(s₁ - s₀) b)`, `1 ≤ j ≤ n`, on `B_l F`. -/
noncomputable def addPts (s₀ s₁ : ℝ) (b : ℝ × ℝ) (n : ℕ) (l : ℝ) : Finset (ℝ × ℝ) :=
  (Icc 1 n).image (fun j : ℕ => boost l ((s₀ + (j : ℝ) / n * (s₁ - s₀)) • b))

open Classical in
/-- The modified point set at one index: remove the lattice points on `B_l F` for
`l ∈ H`, and put `n` points on each `B_l F`. -/
noncomputable def modPts (s₀ s₁ : ℝ) (b : ℝ × ℝ) (h : ℝ) (N n : ℕ) (H : Finset ℝ) :
    Finset (ℝ × ℝ) :=
  (latPts h N).filter (fun x => ∀ l ∈ H, x ∉ boost l '' seg s₀ s₁ b) ∪
    H.biUnion (addPts s₀ s₁ b n)

theorem addPts_subset {s₀ s₁ : ℝ} (hs : s₀ < s₁) (b : ℝ × ℝ) (n : ℕ) (l : ℝ) :
    ∀ x ∈ addPts s₀ s₁ b n l, x ∈ boost l '' seg s₀ s₁ b := by
  intro x hx
  obtain ⟨j, hj, rfl⟩ := mem_image.mp hx
  rw [mem_Icc] at hj
  have hn : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hjn : (j : ℝ) / n ≤ 1 := by
    rw [div_le_one hn]; exact_mod_cast hj.2
  have hj0 : 0 ≤ (j : ℝ) / n := by positivity
  refine ⟨_, ⟨s₀ + (j : ℝ) / n * (s₁ - s₀), ?_, ?_, rfl⟩, rfl⟩
  · nlinarith
  · nlinarith

theorem card_addPts {s₀ s₁ : ℝ} (hs : s₀ < s₁) {b : ℝ × ℝ} (hb : b ≠ 0) (n : ℕ) {l : ℝ}
    (hl : 0 < l) : (addPts s₀ s₁ b n l).card = n := by
  unfold addPts
  rw [card_image_of_injOn, Nat.card_Icc, Nat.add_sub_cancel]
  intro j hj j' hj' e
  have hn : (n : ℝ) ≠ 0 := by
    have := (mem_Icc.mp (mem_coe.mp hj)).1; have := (mem_Icc.mp (mem_coe.mp hj)).2
    exact_mod_cast (show n ≠ 0 by omega)
  have e1 : s₀ + (j : ℝ) / n * (s₁ - s₀) = s₀ + (j' : ℝ) / n * (s₁ - s₀) :=
    smul_left_injective ℝ hb (boost_injective hl e)
  have : (j : ℝ) = j' := by
    have h2 : (j : ℝ) / n * (s₁ - s₀) = j' / n * (s₁ - s₀) := by linarith
    have h3 := mul_right_cancel₀ (sub_ne_zero.mpr hs.ne') h2
    field_simp at h3; exact h3
  exact_mod_cast this

open Classical in
/-- **Exact count on every prescribed boost.**  For `l ∈ H`, the modified set has
exactly `n` points on `B_l F`. -/
theorem card_modPts_boost {s₀ s₁ : ℝ} (hs₀ : 0 < s₀) (hs : s₀ < s₁) {b : ℝ × ℝ}
    (hb : b.1 ^ 2 ≠ b.2 ^ 2) (h : ℝ) (N n : ℕ) {H : Finset ℝ} (hH : ∀ l ∈ H, 0 < l)
    {l : ℝ} (hl : l ∈ H) :
    ((modPts s₀ s₁ b h N n H).filter (· ∈ boost l '' seg s₀ s₁ b)).card = n := by
  have hb0 : b ≠ 0 := by rintro rfl; exact hb rfl
  refine (congrArg card ?_).trans (card_addPts hs hb0 n (hH l hl))
  ext x
  simp only [modPts, mem_filter, mem_union, mem_biUnion]
  constructor
  · rintro ⟨h1 | ⟨l', hl', hx⟩, h2⟩
    · exact absurd h2 (h1.2 l hl)
    · have := boost_seg_disjoint hs₀ hb (hH l' hl') (hH l hl) (addPts_subset hs b n l' x hx) h2
      exact this ▸ hx
  · intro hx
    exact ⟨Or.inr ⟨l, hl, hx⟩, addPts_subset hs b n l x hx⟩

open Classical in
/-- Lattice points of `h ℤ²` in a box on a line through `0`: at most `2⌊R/h⌋ + 1`. -/
theorem card_lat_line {h : ℝ} (hh : 0 < h) (N : ℕ) {R : ℝ} (hR : 0 ≤ R) {d : ℝ × ℝ}
    (hd : d ≠ 0) (P : Set (ℝ × ℝ)) (hP : ∀ x ∈ P, ∃ s : ℝ, x = s • d) :
    (((latPts h N).filter (· ∈ box R)).filter (· ∈ P)).card ≤ 2 * ⌊R / h⌋₊ + 1 := by
  -- choose a coordinate in which `d` is nonzero
  obtain ⟨π, hπd, hπs, hπl⟩ : ∃ π : ℝ × ℝ → ℝ, π d ≠ 0 ∧ (∀ s : ℝ, π (s • d) = s * π d) ∧
      ∀ x ∈ (latPts h N).filter (· ∈ box R), ∃ k : ℤ, π x = h * k ∧ |π x| ≤ R := by
    by_cases h1 : d.1 = 0
    · have h2 : d.2 ≠ 0 := fun h2 => hd (Prod.ext h1 h2)
      refine ⟨Prod.snd, h2, fun s => by simp, fun x hx => ?_⟩
      obtain ⟨hx, hxR⟩ := mem_filter.mp hx
      obtain ⟨k, _, rfl⟩ := mem_image.mp hx
      exact ⟨k.2, rfl, hxR.2⟩
    · refine ⟨Prod.fst, h1, fun s => by simp, fun x hx => ?_⟩
      obtain ⟨hx, hxR⟩ := mem_filter.mp hx
      obtain ⟨k, _, rfl⟩ := mem_image.mp hx
      exact ⟨k.1, rfl, hxR.1⟩
  set K : ℕ := ⌊R / h⌋₊
  have hmap : ∀ x ∈ ((latPts h N).filter (· ∈ box R)).filter (· ∈ P),
      ⌊π x / h⌋ ∈ Icc (-(K : ℤ)) K := by
    intro x hx
    obtain ⟨hx1, _⟩ := mem_filter.mp hx
    obtain ⟨k, hk, hkR⟩ := hπl x hx1
    have hfl : ⌊π x / h⌋ = k := by
      rw [hk, mul_div_cancel_left₀ _ hh.ne', Int.floor_intCast]
    rw [hfl, mem_Icc]
    have hk' : |(k : ℝ)| ≤ R / h := by
      rw [le_div_iff₀ hh]
      have : |(k : ℝ)| * h = |π x| := by rw [hk, abs_mul, abs_of_pos hh, mul_comm]
      rw [this]; exact hkR
    have hK : ((K : ℤ) : ℝ) = (K : ℝ) := by simp
    have hle : |k| ≤ (K : ℤ) := by
      have : (|k| : ℤ) ≤ ⌊R / h⌋ := Int.le_floor.mpr (by simpa using hk')
      have h0 : 0 ≤ R / h := div_nonneg hR hh.le
      rw [show ⌊R / h⌋ = ((⌊R / h⌋₊ : ℕ) : ℤ) from (Int.natCast_floor_eq_floor h0).symm] at this
      exact this
    constructor <;> [linarith [neg_abs_le k]; linarith [le_abs_self k]]
  have hinj : Set.InjOn (fun x => ⌊π x / h⌋)
      ↑(((latPts h N).filter (· ∈ box R)).filter (· ∈ P)) := by
    intro x hx y hy e
    obtain ⟨hx1, hxP⟩ := mem_filter.mp (mem_coe.mp hx)
    obtain ⟨hy1, hyP⟩ := mem_filter.mp (mem_coe.mp hy)
    obtain ⟨k, hk, _⟩ := hπl x hx1
    obtain ⟨k', hk', _⟩ := hπl y hy1
    have e' : π x = π y := by
      simp only at e
      rw [hk, hk', mul_div_cancel_left₀ _ hh.ne', mul_div_cancel_left₀ _ hh.ne',
        Int.floor_intCast, Int.floor_intCast] at e
      rw [hk, hk', e]
    obtain ⟨s, rfl⟩ := hP x hxP
    obtain ⟨s', rfl⟩ := hP y hyP
    rw [hπs, hπs] at e'
    rw [mul_right_cancel₀ hπd e']
  calc _ ≤ (Icc (-(K : ℤ)) K).card := card_le_card_of_injOn _ hmap hinj
    _ = 2 * K + 1 := by rw [Int.card_Icc]; omega

open Classical in
/-- Points added: at most `#H · n`. -/
theorem card_modPts_le (s₀ s₁ : ℝ) (b : ℝ × ℝ) (h : ℝ) (N n : ℕ) (H : Finset ℝ)
    (A : Set (ℝ × ℝ)) :
    ((modPts s₀ s₁ b h N n H).filter (· ∈ A)).card ≤
      ((latPts h N).filter (· ∈ A)).card + H.card * n := by
  have hsub : (modPts s₀ s₁ b h N n H).filter (· ∈ A) ⊆
      (latPts h N).filter (· ∈ A) ∪ H.biUnion (addPts s₀ s₁ b n) := by
    intro x hx
    simp only [modPts, mem_filter, mem_union] at hx ⊢
    rcases hx with ⟨h1 | h1, h2⟩
    · exact Or.inl ⟨h1.1, h2⟩
    · exact Or.inr h1
  refine (card_le_card hsub).trans ((card_union_le _ _).trans (Nat.add_le_add_left ?_ _))
  refine card_biUnion_le.trans ?_
  rw [← smul_eq_mul, ← sum_const]
  refine sum_le_sum fun l _ => ?_
  unfold addPts
  exact card_image_le.trans (by simp)

open Classical in
/-- Points removed inside a standard box: at most `#H · (2⌊R/h⌋ + 1)`. -/
theorem card_latPts_le {s₀ s₁ : ℝ} {b : ℝ × ℝ} (hb : b ≠ 0) {h : ℝ} (hh : 0 < h) (N n : ℕ)
    {H : Finset ℝ} (hH : ∀ l ∈ H, 0 < l) {R : ℝ} (hR : 0 ≤ R) {A : Set (ℝ × ℝ)}
    (hA : A ⊆ box R) :
    ((latPts h N).filter (· ∈ A)).card ≤
      ((modPts s₀ s₁ b h N n H).filter (· ∈ A)).card + H.card * (2 * ⌊R / h⌋₊ + 1) := by
  have hsub : (latPts h N).filter (· ∈ A) ⊆ (modPts s₀ s₁ b h N n H).filter (· ∈ A) ∪
      H.biUnion (fun l => ((latPts h N).filter (· ∈ box R)).filter
        (· ∈ boost l '' seg s₀ s₁ b)) := by
    intro x hx
    obtain ⟨hx1, hx2⟩ := mem_filter.mp hx
    by_cases hc : ∀ l ∈ H, x ∉ boost l '' seg s₀ s₁ b
    · exact mem_union_left _ (mem_filter.mpr ⟨mem_union_left _ (mem_filter.mpr ⟨hx1, hc⟩), hx2⟩)
    · push Not at hc
      obtain ⟨l, hl, hxl⟩ := hc
      exact mem_union_right _ (mem_biUnion.mpr ⟨l, hl, mem_filter.mpr
        ⟨mem_filter.mpr ⟨hx1, hA hx2⟩, hxl⟩⟩)
  refine (card_le_card hsub).trans ((card_union_le _ _).trans (Nat.add_le_add_left ?_ _))
  refine card_biUnion_le.trans ?_
  rw [← smul_eq_mul, ← sum_const]
  refine sum_le_sum fun l hl => ?_
  have hd : boost l b ≠ 0 := by
    intro e
    have h0 : boost l (0 : ℝ × ℝ) = 0 := by ext <;> simp [boost]
    exact hb (boost_injective (hH l hl) (e.trans h0.symm))
  refine card_lat_line hh N hR hd _ ?_
  rintro x ⟨_, ⟨s, _, _, rfl⟩, rfl⟩
  exact ⟨s, boost_smul l s b⟩

end Finite

/-! ## The internal point set in the enlargement -/

section Internal

/-- The internal count `#(A ∩ Λ) = [J ↦ #(A ∩ Λ_J)] ∈ *ℝ` of a standard set `A` in a
hyperfinite set `Λ = [J ↦ Λ_J]`. -/
noncomputable def cnt (Λ : Idx → Finset (ℝ × ℝ)) (A : Set (ℝ × ℝ)) : M :=
  by classical exact ↑(fun J => (((Λ J).filter (· ∈ A)).card : ℝ))

/-- Number of points put on each boosted segment: `n = ⌊1/(2ε)⌋`. -/
noncomputable def nPts (e : Idx → ℝ) (J : Idx) : ℕ := ⌊1 / (2 * e J)⌋₊

/-- Truncation of the lattice: `N = ⌈1/(2ε)²⌉`. -/
noncomputable def nTrunc (e : Idx → ℝ) (J : Idx) : ℕ := ⌈1 / (2 * e J) ^ 2⌉₊

/-- The hyperfinite lattice `2ε ℤ² ∩ [-2εN, 2εN]²`. -/
noncomputable def lat (e : Idx → ℝ) (J : Idx) : Finset (ℝ × ℝ) := latPts (2 * e J) (nTrunc e J)

/-- The hyperfinite point set `Λ`: the lattice `2ε ℤ²`, with the points on the boosted
segments `B_l F`, `l ∈ H = [J ↦ J ∩ (0, ∞)]`, replaced by `n` equally spaced points on
each. -/
noncomputable def grainSet (e : Idx → ℝ) (s₀ s₁ : ℝ) (b : ℝ × ℝ) (J : Idx) : Finset (ℝ × ℝ) :=
  modPts s₀ s₁ b (2 * e J) (nTrunc e J) (nPts e J) (J.filter (0 < ·))

theorem infinitesimal_of_card {e : Idx → ℝ} (he : ∀ J, 0 < e J)
    (hsmall : Infinitesimal (↑(fun J => (J.card : ℝ) * e J) : M)) :
    ∀ r : ℝ, 0 < r → ∀ᶠ J in (U : Filter Idx), e J < r := by
  intro r hr
  filter_upwards [infinitesimal_coe.mp hsmall r hr, card_eventually 1] with J h1 h2
  have h2' : (1 : ℝ) ≤ J.card := by exact_mod_cast h2
  have := he J
  rw [abs_of_pos (by positivity)] at h1
  nlinarith

theorem cnt_eq_nPts {e : Idx → ℝ} {s₀ s₁ : ℝ} (hs₀ : 0 < s₀) (hs : s₀ < s₁) {b : ℝ × ℝ}
    (hb : b.1 ^ 2 ≠ b.2 ^ 2) {l : ℝ} (hl : 0 < l) :
    cnt (grainSet e s₀ s₁ b) (boost l '' seg s₀ s₁ b) = ↑(fun J => (nPts e J : ℝ)) := by
  classical
  unfold cnt
  refine Filter.Germ.coe_eq.mpr ?_
  filter_upwards [mem_eventually l] with J hJ
  unfold grainSet
  convert congrArg (Nat.cast : ℕ → ℝ) (card_modPts_boost hs₀ hs hb (2 * e J) (nTrunc e J)
    (nPts e J) (H := J.filter (0 < ·)) (fun l hl => (mem_filter.mp hl).2)
    (mem_filter.mpr ⟨hJ, hl⟩))

theorem boost_one_seg (s₀ s₁ : ℝ) (b : ℝ × ℝ) : boost 1 '' seg s₀ s₁ b = seg s₀ s₁ b := by
  simp [boost_one]

/-- **Standard boosts in the enlargement.**  Let `ε = [e] > 0` be a grain with
`ε · #J ≈ 0` (`#J` the internal size of the enlargement), and let
`F = {s b : s₀ ≤ s ≤ s₁}`, `0 < s₀ < s₁`, be a standard segment on a non-null line.
The hyperfinite set `Λ = grainSet e s₀ s₁ b` satisfies:
1. `#(B_l F ∩ Λ) = #(F ∩ Λ)` exactly for every standard `l > 0`;
2. `ρ(F) = st((2ε)² #(F ∩ Λ) / ε) = 2`;
3. on every standard bounded set its content `(2ε)² #(A ∩ Λ)` differs infinitesimally
   from that of the lattice `2ε ℤ²`, so it has the lattice's shadow;
4. it is faithful: a standard set meeting `Λ` has content at least `(2ε)²`. -/
theorem standard_boost_invariance {e : Idx → ℝ} (he : ∀ J, 0 < e J)
    (hsmall : Infinitesimal (↑(fun J => (J.card : ℝ) * e J) : M))
    {s₀ s₁ : ℝ} (hs₀ : 0 < s₀) (hs : s₀ < s₁) {b : ℝ × ℝ} (hb : b.1 ^ 2 ≠ b.2 ^ 2) :
    (∀ l : ℝ, 0 < l →
      cnt (grainSet e s₀ s₁ b) (boost l '' seg s₀ s₁ b) = cnt (grainSet e s₀ s₁ b) (seg s₀ s₁ b)) ∧
    Infinitesimal ((2 * (e : M)) ^ 2 * cnt (grainSet e s₀ s₁ b) (seg s₀ s₁ b) / (e : M) - 2) ∧
    (∀ R : ℝ, ∀ A : Set (ℝ × ℝ), A ⊆ box R →
      Infinitesimal ((2 * (e : M)) ^ 2 * cnt (grainSet e s₀ s₁ b) A -
        (2 * (e : M)) ^ 2 * cnt (lat e) A)) ∧
    (∀ A : Set (ℝ × ℝ), 0 < cnt (grainSet e s₀ s₁ b) A →
      (2 * (e : M)) ^ 2 ≤ (2 * (e : M)) ^ 2 * cnt (grainSet e s₀ s₁ b) A) := by
  classical
  have hsm := infinitesimal_of_card he hsmall
  refine ⟨fun l hl => ?_, ?_, fun R A hA => ?_, fun A hA => ?_⟩
  · rw [cnt_eq_nPts hs₀ hs hb hl, ← boost_one_seg, cnt_eq_nPts hs₀ hs hb one_pos]
  · rw [← boost_one_seg, cnt_eq_nPts hs₀ hs hb one_pos]
    show Infinitesimal (↑(fun J => (2 * e J) ^ 2 * (nPts e J : ℝ) / e J - 2) : M)
    rw [infinitesimal_coe]
    intro r hr
    filter_upwards [hsm (r / 4) (by positivity)] with J hJ
    have he' := he J
    have h1 : (nPts e J : ℝ) ≤ 1 / (2 * e J) := Nat.floor_le (by positivity)
    have h2 : 1 / (2 * e J) < nPts e J + 1 := Nat.lt_floor_add_one _
    have h1' : 2 * e J * nPts e J ≤ 1 := by
      rw [le_div_iff₀ (by positivity)] at h1; linarith
    have h2' : 1 < 2 * e J * (nPts e J + 1) := by
      rw [div_lt_iff₀ (by positivity)] at h2; linarith
    have hval : (2 * e J) ^ 2 * (nPts e J : ℝ) / e J - 2 = 2 * (2 * e J * nPts e J) - 2 := by
      field_simp
    rw [hval, abs_lt]
    constructor <;> nlinarith
  · set R' := max R 0
    have hR' : 0 ≤ R' := le_max_right _ _
    have hA' : A ⊆ box R' := fun x hx =>
      ⟨(hA hx).1.trans (le_max_left _ _), (hA hx).2.trans (le_max_left _ _)⟩
    show Infinitesimal (↑(fun J => (2 * e J) ^ 2 * ((((grainSet e s₀ s₁ b J).filter
      (· ∈ A)).card : ℕ) : ℝ) - (2 * e J) ^ 2 * ((((lat e J).filter (· ∈ A)).card : ℕ) : ℝ)) : M)
    rw [infinitesimal_coe]
    intro r hr
    have hc : 0 < 2 * (3 + 2 * R') := by positivity
    filter_upwards [infinitesimal_coe.mp hsmall (r / (2 * (3 + 2 * R'))) (by positivity),
      hsm 1 one_pos] with J hJ he1
    have he' := he J
    have hb0 : b ≠ 0 := by rintro rfl; exact hb rfl
    set h := 2 * e J
    have hh : 0 < h := by positivity
    set H := J.filter (0 < ·)
    have hHc : (H.card : ℝ) ≤ J.card := by exact_mod_cast card_filter_le _ _
    have i1 := card_modPts_le s₀ s₁ b h (nTrunc e J) (nPts e J) H A
    have i2 := card_latPts_le (s₀ := s₀) (s₁ := s₁) hb0 hh (nTrunc e J) (nPts e J)
      (H := H) (fun l hl => (mem_filter.mp hl).2) hR' hA'
    have i1' : (((modPts s₀ s₁ b h (nTrunc e J) (nPts e J) H).filter (· ∈ A)).card : ℝ) ≤
        ((latPts h (nTrunc e J)).filter (· ∈ A)).card + H.card * (nPts e J : ℝ) := by
      exact_mod_cast i1
    have i2' : (((latPts h (nTrunc e J)).filter (· ∈ A)).card : ℝ) ≤
        ((modPts s₀ s₁ b h (nTrunc e J) (nPts e J) H).filter (· ∈ A)).card +
          H.card * (2 * (⌊R' / h⌋₊ : ℝ) + 1) := by
      exact_mod_cast i2
    have hn : (nPts e J : ℝ) ≤ 1 / h := Nat.floor_le (by positivity)
    have hK : (⌊R' / h⌋₊ : ℝ) ≤ R' / h := Nat.floor_le (by positivity)
    have hn' : h * (nPts e J : ℝ) ≤ 1 := by
      rw [le_div_iff₀ hh] at hn; linarith
    have hK' : h * (⌊R' / h⌋₊ : ℝ) ≤ R' := by
      rw [le_div_iff₀ hh] at hK; linarith
    have hJc : |(J.card : ℝ) * e J| = J.card * e J := abs_of_nonneg (by positivity)
    rw [hJc, lt_div_iff₀ hc] at hJ
    have hH0 : (0 : ℝ) ≤ H.card := by positivity
    -- the bound `h² · #H · (n + 2K + 1) ≤ 2 #J e (3 + 2R')`
    have key : h ^ 2 * (H.card * ((nPts e J : ℝ) + (2 * (⌊R' / h⌋₊ : ℝ) + 1))) <  r := by
      have : h ^ 2 * (H.card * ((nPts e J : ℝ) + (2 * (⌊R' / h⌋₊ : ℝ) + 1))) =
          h * H.card * (h * nPts e J + 2 * (h * ⌊R' / h⌋₊) + h) := by ring
      rw [this]
      have hh1 : h ≤ 2 := by linarith
      have : h * H.card * (h * nPts e J + 2 * (h * ⌊R' / h⌋₊) + h) ≤
          h * H.card * (1 + 2 * R' + 2) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity); linarith
      have : h * H.card * (1 + 2 * R' + 2) ≤ 2 * e J * J.card * (3 + 2 * R') := by
        have : h * H.card ≤ 2 * e J * J.card := by
          show 2 * e J * H.card ≤ _
          exact mul_le_mul_of_nonneg_left hHc (by positivity)
        nlinarith
      nlinarith
    show |h ^ 2 * (((modPts s₀ s₁ b h (nTrunc e J) (nPts e J) H).filter (· ∈ A)).card : ℝ) -
      h ^ 2 * (((latPts h (nTrunc e J)).filter (· ∈ A)).card : ℝ)| < r
    rw [abs_lt]
    have hh2 : 0 ≤ h ^ 2 := by positivity
    have hKn : (0 : ℝ) ≤ (⌊R' / h⌋₊ : ℝ) := by positivity
    have hnn : (0 : ℝ) ≤ (nPts e J : ℝ) := by positivity
    constructor
    · nlinarith [mul_le_mul_of_nonneg_left i2' hh2, mul_nonneg hH0 hnn]
    · nlinarith [mul_le_mul_of_nonneg_left i1' hh2, mul_nonneg hH0 hKn]
  · unfold cnt at hA ⊢
    have hA' := Filter.Germ.coe_pos.mp hA
    show (↑(fun J => (2 * e J) ^ 2) : M) ≤
      ↑(fun J => (2 * e J) ^ 2 * ((((grainSet e s₀ s₁ b J).filter (· ∈ A)).card : ℕ) : ℝ))
    refine Filter.Germ.coe_le.mpr ?_
    filter_upwards [hA'] with J hJ
    have : (1 : ℝ) ≤ (((grainSet e s₀ s₁ b J).filter (· ∈ A)).card : ℕ) := by
      have : 0 < ((grainSet e s₀ s₁ b J).filter (· ∈ A)).card := by exact_mod_cast hJ
      exact_mod_cast this
    have := sq_nonneg (2 * e J)
    nlinarith

/-- The hyperfinite lattice `lat e` is `2ε ℤ²` on every standard box. -/
theorem lat_spec {e : Idx → ℝ} (he : ∀ J, 0 < e J)
    (hsmall : Infinitesimal (↑(fun J => (J.card : ℝ) * e J) : M)) :
    (∀ J, ∀ x ∈ lat e J, ∃ k : ℤ × ℤ, x = (2 * e J * k.1, 2 * e J * k.2)) ∧
    ∀ R : ℝ, ∀ᶠ J in (U : Filter Idx), ∀ k : ℤ × ℤ, |2 * e J * k.1| ≤ R →
      |2 * e J * k.2| ≤ R → (2 * e J * k.1, 2 * e J * k.2) ∈ lat e J := by
  refine ⟨fun J x hx => ?_, fun R => ?_⟩
  · obtain ⟨k, _, rfl⟩ := mem_image.mp hx
    exact ⟨k, rfl⟩
  · set R' := max R 1
    filter_upwards [infinitesimal_of_card he hsmall (1 / (2 * R')) (by positivity)] with J hJ
    intro k h1 h2
    have he' := he J
    set h := 2 * e J
    have hh : 0 < h := by positivity
    have hR' : 1 ≤ R' := le_max_right _ _
    have hhR : h * R' < 1 := by
      have : e J * (2 * R') < 1 := by rwa [lt_div_iff₀ (by positivity)] at hJ
      linarith
    have hN : 1 / h ^ 2 ≤ (nTrunc e J : ℝ) := Nat.le_ceil _
    -- `|k_i| ≤ R/h ≤ 1/h² ≤ N`
    have bound : ∀ m : ℤ, |h * m| ≤ R → |m| ≤ (nTrunc e J : ℤ) := by
      intro m hm
      have hm' : |(m : ℝ)| * h ≤ R' := by
        rw [abs_mul, abs_of_pos hh] at hm; linarith [le_max_left R 1]
      have : |(m : ℝ)| ≤ 1 / h ^ 2 := by
        rw [le_div_iff₀ (by positivity)]
        nlinarith [abs_nonneg (m : ℝ)]
      have : |(m : ℝ)| ≤ (nTrunc e J : ℝ) := this.trans hN
      exact_mod_cast this
    unfold lat latPts
    refine mem_image.mpr ⟨k, ?_, rfl⟩
    rw [mem_product, mem_Icc, mem_Icc]
    have b1 := bound k.1 h1
    have b2 := bound k.2 h2
    rw [abs_le] at b1 b2
    exact ⟨b1, b2⟩

/-- A grain satisfying the hypothesis exists: `ε = [J ↦ 1/(#J+1)²]`. -/
theorem exists_grain : ∃ e : Idx → ℝ, (∀ J, 0 < e J) ∧
    Infinitesimal (↑(fun J => (J.card : ℝ) * e J) : M) := by
  refine ⟨fun J => 1 / ((J.card : ℝ) + 1) ^ 2, fun J => by positivity, ?_⟩
  rw [infinitesimal_coe]
  intro r hr
  obtain ⟨m, hm⟩ := exists_nat_gt (1 / r)
  filter_upwards [card_eventually m] with J hJ
  have hJ' : (m : ℝ) ≤ J.card := by exact_mod_cast hJ
  have hc : (0 : ℝ) < J.card + 1 := by positivity
  rw [abs_of_nonneg (by positivity)]
  have : (J.card : ℝ) * (1 / ((J.card : ℝ) + 1) ^ 2) ≤ 1 / (J.card + 1) := by
    rw [mul_one_div, div_le_div_iff₀ (by positivity) hc]
    nlinarith
  refine this.trans_lt ?_
  rw [div_lt_iff₀ hc]
  rw [div_lt_iff₀ hr] at hm
  nlinarith

end Internal

end QE.Enlargement

/-!
# Cubical `H₀` and singular `H₀` of the geometric realisation

For a finite cubical complex `X ⊆ ℤⁿ` with geometric realisation `|X| ⊆ ℝⁿ` (the union
of the closed cubes `∏ᵢ [vᵢ, vᵢ + [i ∈ S]]`), the cubical `H₀(X)` is isomorphic to the
singular `H₀(|X|; ℤ)`, Mathlib's `singularHomologyFunctor` in degree `0`.

* Combinatorics: every integer point of a cube of `X` is a vertex of `X` joined to the
  corner by an edge path (`vertex_conn`); two cubes that meet share such a vertex
  (`max_mem`).
* Topology: the union of the cubes whose corner lies in one edge-path class is clopen in
  `|X|` (`conn_of_joined`), so path components of `|X|` are edge-path classes of vertices.
* Algebra: `H₀(X) ≃ (π₀|X| →₀ ℤ)` (`homology_zero_equiv`), and Mathlib's
  `TopCat.singularHomology₀Iso` gives singular `H₀ ≅ ⨁_{π₀} ℤ`.
-/

namespace QE.CubicalSingular

open Finset QE.Cubical

variable {n : ℕ}

/-- Upper corner of an elementary cube. -/
def top (c : Cube n) (i : Fin n) : ℤ := c.1 i + if i ∈ c.2 then 1 else 0

/-- The closed cube `∏ᵢ [vᵢ, vᵢ + [i ∈ S]] ⊆ ℝⁿ`. -/
def cubeSet (c : Cube n) : Set (Fin n → ℝ) :=
  Set.univ.pi fun i => Set.Icc (c.1 i : ℝ) (top c i : ℝ)

/-- The geometric realisation `|X| = ⋃_{c ∈ X} c ⊆ ℝⁿ`. -/
def realisation (X : Finset (Cube n)) : Set (Fin n → ℝ) := ⋃ c ∈ X, cubeSet c

/-- A lattice point of `ℤⁿ` as a point of `ℝⁿ`. -/
def vpt (v : Fin n → ℤ) : Fin n → ℝ := fun i => (v i : ℝ)

/-- Two vertices are joined by an edge `(v, {i})` of `X`. -/
def edgeRel (X : Finset (Cube n)) (v w : Fin n → ℤ) : Prop :=
  ∃ i, (v, ({i} : Finset (Fin n))) ∈ X ∧ w = v + unit i

/-- Edge-path equivalence of vertices. -/
abbrev Conn (X : Finset (Cube n)) : (Fin n → ℤ) → (Fin n → ℤ) → Prop :=
  Relation.EqvGen (edgeRel X)

theorem face_mem {X : Finset (Cube n)} (hX : IsComplex X) {v : Fin n → ℤ}
    {S : Finset (Fin n)} (h : (v, S) ∈ X) {T : Finset (Fin n)} (hT : T ⊆ S) : (v, T) ∈ X := by
  classical
  have key : ∀ D : Finset (Fin n), D ⊆ S → (v, S \ D) ∈ X := by
    intro D
    induction D using Finset.induction_on with
    | empty => intro _; simpa using h
    | insert a D ha ih =>
      intro hD
      have h1 := ih ((subset_insert _ _).trans hD)
      have haS : a ∈ S \ D := mem_sdiff.mpr ⟨hD (mem_insert_self _ _), ha⟩
      have h2 := (hX _ h1 a haS).2
      have e : S \ insert a D = (S \ D).erase a := by
        ext x; simp only [mem_sdiff, mem_insert, mem_erase]; tauto
      rw [e]; exact h2
  have := key (S \ T) sdiff_subset
  rwa [Finset.sdiff_sdiff_eq_self hT] at this

theorem unit_apply (i j : Fin n) : unit i j = if j = i then 1 else 0 := by
  simp [unit, Pi.single_apply]

/-- **Integer points of a cube of `X` are vertices of `X`, edge-path connected to the
corner.** -/
theorem vertex_conn {X : Finset (Cube n)} (hX : IsComplex X) :
    ∀ (k : ℕ) (v : Fin n → ℤ) (S : Finset (Fin n)), S.card = k → (v, S) ∈ X →
      ∀ u : Fin n → ℤ, (∀ i, v i ≤ u i ∧ u i ≤ v i + if i ∈ S then 1 else 0) →
        (u, ∅) ∈ X ∧ Conn X v u := by
  intro k
  induction k with
  | zero =>
    intro v S hS h u hu
    rw [card_eq_zero] at hS; subst hS
    have : u = v := funext fun i => le_antisymm (by simpa using (hu i).2) (hu i).1
    subst this
    exact ⟨h, Relation.EqvGen.refl _⟩
  | succ k ih =>
    intro v S hS h u hu
    obtain ⟨i, hi⟩ : S.Nonempty := card_pos.mp (by omega)
    have hS' : (S.erase i).card = k := by rw [card_erase_of_mem hi]; omega
    obtain ⟨hf1, hf2⟩ := hX _ h i hi
    simp only at hf1 hf2
    by_cases hui : u i = v i
    · refine ih v (S.erase i) hS' hf2 u fun j => ?_
      by_cases hji : j = i
      · subst hji; simp [hui]
      · have := hu j; simpa [mem_erase, hji] using this
    · have hui' : u i = v i + 1 := by
        have := hu i; simp [hi] at this; omega
      obtain ⟨hu1, hu2⟩ := ih (v + unit i) (S.erase i) hS' hf1 u fun j => by
        by_cases hji : j = i
        · subst hji; simp [unit_apply, hui']
        · have := hu j; simpa [mem_erase, hji, unit_apply] using this
      have hedge : (v, ({i} : Finset (Fin n))) ∈ X := face_mem hX h (singleton_subset_iff.mpr hi)
      exact ⟨hu1, Relation.EqvGen.trans _ _ _ (Relation.EqvGen.rel _ _ ⟨i, hedge, rfl⟩) hu2⟩

theorem vpt_mem_cubeSet_iff (c : Cube n) (u : Fin n → ℤ) :
    vpt u ∈ cubeSet c ↔ ∀ i, c.1 i ≤ u i ∧ u i ≤ top c i := by
  simp only [cubeSet, vpt, Set.mem_univ_pi, Set.mem_Icc, Int.cast_le]

theorem corner_mem (c : Cube n) : vpt c.1 ∈ cubeSet c := by
  rw [vpt_mem_cubeSet_iff]
  intro i
  refine ⟨le_rfl, ?_⟩
  unfold top; split_ifs <;> omega

/-- Two cubes that meet share the integer point `max(v, v')`. -/
theorem max_mem {c c' : Cube n} {p : Fin n → ℝ} (hp : p ∈ cubeSet c) (hp' : p ∈ cubeSet c') :
    ∀ i, c.1 i ≤ max (c.1 i) (c'.1 i) ∧ max (c.1 i) (c'.1 i) ≤ top c i := by
  intro i
  refine ⟨le_max_left _ _, ?_⟩
  have h1 := (Set.mem_univ_pi.mp hp i)
  have h2 := (Set.mem_univ_pi.mp hp' i)
  have : ((max (c.1 i) (c'.1 i) : ℤ) : ℝ) ≤ (top c i : ℝ) := by
    rw [Int.cast_max]; exact max_le (h1.1.trans h1.2) (h2.1.trans h1.2)
  exact_mod_cast this

theorem isClosed_cubeSet (c : Cube n) : IsClosed (cubeSet c) :=
  isClosed_set_pi fun _ _ => isClosed_Icc

theorem convex_cubeSet (c : Cube n) : Convex ℝ (cubeSet c) :=
  convex_pi fun _ _ => convex_Icc _ _

theorem corner_mem_realisation {X : Finset (Cube n)} {c : Cube n} (hc : c ∈ X) :
    vpt c.1 ∈ realisation X :=
  Set.mem_biUnion hc (corner_mem c)

/-- Every point of a cube of `X` is joined in `|X|` to the corner of the cube. -/
theorem joined_corner {X : Finset (Cube n)} {c : Cube n} (hc : c ∈ X) {p : Fin n → ℝ}
    (hp : p ∈ cubeSet c) :
    Joined (⟨p, Set.mem_biUnion hc hp⟩ : realisation X) ⟨vpt c.1, corner_mem_realisation hc⟩ := by
  have hJ : JoinedIn (cubeSet c) p (vpt c.1) :=
    ((convex_cubeSet c).isPathConnected ⟨p, hp⟩).joinedIn p hp _ (corner_mem c)
  exact (hJ.mono (Set.subset_biUnion_of_mem (u := cubeSet) hc)).joined_subtype

/-- **Path components are edge-path classes.**  If two vertices of `X` are joined by a
path in `|X|`, they are joined by an edge path of `X`. -/
theorem conn_of_joined {X : Finset (Cube n)} (hX : IsComplex X) {v w : Fin n → ℤ}
    (hv : (v, (∅ : Finset (Fin n))) ∈ X) (hw : (w, (∅ : Finset (Fin n))) ∈ X)
    (h : Joined (⟨vpt v, corner_mem_realisation hv⟩ : realisation X)
      ⟨vpt w, corner_mem_realisation hw⟩) : Conn X v w := by
  classical
  set C : Set (Fin n → ℤ) := {u | Conn X v u}
  set A : Set (Fin n → ℝ) := ⋃ c ∈ X.filter (fun c => c.1 ∈ C), cubeSet c
  set B : Set (Fin n → ℝ) := ⋃ c ∈ X.filter (fun c => c.1 ∉ C), cubeSet c
  have hA : IsClosed A := isClosed_biUnion_finset fun c _ => isClosed_cubeSet c
  have hB : IsClosed B := isClosed_biUnion_finset fun c _ => isClosed_cubeSet c
  have conn_cube : ∀ c ∈ X, ∀ u, (∀ i, c.1 i ≤ u i ∧ u i ≤ top c i) → Conn X c.1 u :=
    fun c hc u hu => (vertex_conn hX _ c.1 c.2 rfl hc u hu).2
  have hdisj : ∀ p ∈ A, p ∉ B := by
    intro p hpA hpB
    simp only [A, B, Set.mem_iUnion, mem_filter, exists_prop] at hpA hpB
    obtain ⟨c, ⟨hc, hcC⟩, hpc⟩ := hpA
    obtain ⟨c', ⟨hc', hc'C⟩, hpc'⟩ := hpB
    have h1 := conn_cube c hc _ (max_mem hpc hpc')
    have h2 := conn_cube c' hc' (fun i => max (c.1 i) (c'.1 i)) (fun i => by
      rw [max_comm]; exact max_mem hpc' hpc i)
    exact hc'C (Relation.EqvGen.trans _ _ _ hcC (Relation.EqvGen.trans _ _ _ h1
      (Relation.EqvGen.symm _ _ h2)))
  have hcov : ∀ p ∈ realisation X, p ∈ A ∨ p ∈ B := by
    intro p hp
    obtain ⟨c, hc, hpc⟩ := Set.mem_iUnion₂.mp hp
    by_cases hcC : c.1 ∈ C
    · exact Or.inl (Set.mem_biUnion (mem_filter.mpr ⟨hc, hcC⟩) hpc)
    · exact Or.inr (Set.mem_biUnion (mem_filter.mpr ⟨hc, hcC⟩) hpc)
  set s : Set (realisation X) := Subtype.val ⁻¹' A
  have hcompl : sᶜ = Subtype.val ⁻¹' B := by
    ext y
    simp only [s, Set.mem_compl_iff, Set.mem_preimage]
    constructor
    · intro hy; exact (hcov y.1 y.2).resolve_left hy
    · intro hy hy'; exact hdisj _ hy' hy
  have hclopen : IsClopen s := by
    refine ⟨hA.preimage continuous_subtype_val, ?_⟩
    rw [← isClosed_compl_iff, hcompl]
    exact hB.preimage continuous_subtype_val
  have hvs : (⟨vpt v, corner_mem_realisation hv⟩ : realisation X) ∈ s :=
    Set.mem_biUnion (mem_filter.mpr ⟨hv, Relation.EqvGen.refl _⟩) (corner_mem _)
  have hws := hclopen.connectedComponent_subset hvs (pathComponent_subset_component _ h)
  simp only [s, A, Set.mem_preimage, Set.mem_iUnion, mem_filter, exists_prop] at hws
  obtain ⟨c, ⟨hc, hcC⟩, hwc⟩ := hws
  rw [vpt_mem_cubeSet_iff] at hwc
  exact Relation.EqvGen.trans _ _ _ hcC (conn_cube c hc w hwc)


/-! ## The algebra: `H₀(X) ≃ (π₀|X| →₀ ℤ)` -/

section Algebra

variable (X : Finset (Cube n))

/-- `π₀|X|`, the set of path components of the realisation. -/
abbrev Pi0 : Type := ZerothHomotopy (realisation X)

/-- A cube contributes the path component of its corner. -/
noncomputable def gen (c : Cube n) : Pi0 X →₀ ℤ :=
  if h : c ∈ X then Finsupp.single (ZerothHomotopy.mk ⟨vpt c.1, corner_mem_realisation h⟩) 1
  else 0

/-- The augmentation `C₀(X) → ℤ[π₀|X|]`, a vertex to its path component. -/
noncomputable def aug : Chain n →ₗ[ℤ] (Pi0 X →₀ ℤ) := Finsupp.linearCombination ℤ (gen X)

variable {X}

theorem gen_of_mem {c : Cube n} (h : c ∈ X) :
    gen X c = Finsupp.single (ZerothHomotopy.mk ⟨vpt c.1, corner_mem_realisation h⟩) 1 := by
  simp [gen, h]

theorem aug_single (c : Cube n) : aug X (Finsupp.single c 1) = gen X c := by
  simp [aug, Finsupp.linearCombination_single]

theorem mk_eq_of_joined {Y : Type*} [TopologicalSpace Y] {y z : Y} (h : Joined y z) :
    ZerothHomotopy.mk y = ZerothHomotopy.mk z :=
  Quotient.sound h

theorem joined_of_mk_eq {Y : Type*} [TopologicalSpace Y] {y z : Y}
    (h : ZerothHomotopy.mk y = ZerothHomotopy.mk z) : Joined y z :=
  Quotient.exact h

theorem cycles_zero : cycles X 0 = chains X 0 := by
  refine le_antisymm inf_le_left (fun x hx => ⟨hx, ?_⟩)
  simp [bd_chains_zero hx]

theorem bd_edge (v : Fin n → ℤ) (i : Fin n) :
    bd n (Finsupp.single (v, ({i} : Finset (Fin n))) 1) =
      Finsupp.single (v + unit i, ∅) 1 - Finsupp.single (v, ∅) 1 := by
  rw [bd_single]
  simp [bdCube, sgn, Finset.filter_singleton]

theorem cells_one {c : Cube n} (hc : c ∈ cells X 1) :
    c ∈ X ∧ ∃ i, c.2 = ({i} : Finset (Fin n)) := by
  simp only [cells, mem_filter] at hc
  exact ⟨hc.1, card_eq_one.mp hc.2⟩

theorem cells_zero {c : Cube n} (hc : c ∈ cells X 0) :
    c ∈ X ∧ c.2 = (∅ : Finset (Fin n)) := by
  simp only [cells, mem_filter, card_eq_zero] at hc
  exact hc

theorem edge_mem_chains {v : Fin n → ℤ} {i : Fin n} (h : (v, ({i} : Finset (Fin n))) ∈ X) :
    Finsupp.single (v, ({i} : Finset (Fin n))) 1 ∈ chains X 1 :=
  Finsupp.single_mem_supported ℤ _ (by simp [cells, h])

theorem vertex_mem_chains {v : Fin n → ℤ} (h : (v, (∅ : Finset (Fin n))) ∈ X) :
    Finsupp.single (v, (∅ : Finset (Fin n))) 1 ∈ chains X 0 :=
  Finsupp.single_mem_supported ℤ _ (by simp [cells, h])

/-- Edge-path equivalent vertices are homologous. -/
theorem homologous_of_conn {v w : Fin n → ℤ} (h : Conn X v w) :
    Finsupp.single (v, (∅ : Finset (Fin n))) 1 - Finsupp.single (w, ∅) 1 ∈ boundaries X 0 := by
  induction h with
  | rel v w hvw =>
    obtain ⟨i, hi, rfl⟩ := hvw
    refine ⟨-Finsupp.single (v, ({i} : Finset (Fin n))) 1,
      Submodule.neg_mem _ (edge_mem_chains hi), ?_⟩
    rw [map_neg, bd_edge, neg_sub]
  | refl v => simp
  | symm v w _ ih =>
    rw [← neg_sub]; exact Submodule.neg_mem _ ih
  | trans u v w _ _ ih1 ih2 =>
    rw [← sub_add_sub_cancel _ (Finsupp.single (v, (∅ : Finset (Fin n))) 1)]
    exact Submodule.add_mem _ ih1 ih2

theorem aug_bd (hX : IsComplex X) {y : Chain n} (hy : y ∈ chains X 1) : aug X (bd n y) = 0 := by
  have hle : chains X 1 ≤ LinearMap.ker (aug X ∘ₗ bd n) := by
    unfold chains
    rw [Finsupp.supported_eq_span_single, Submodule.span_le]
    rintro _ ⟨c, hc, rfl⟩
    obtain ⟨hcX, i, hci⟩ := cells_one hc
    obtain ⟨v, S⟩ := c
    simp only at hci; subst hci
    have hf := hX _ hcX i (mem_singleton_self i)
    simp only [erase_singleton] at hf
    simp only [SetLike.mem_coe, LinearMap.mem_ker, LinearMap.coe_comp, Function.comp_apply,
      bd_edge, map_sub, aug_single, gen_of_mem hf.1, gen_of_mem hf.2]
    rw [sub_eq_zero]
    congr 1
    refine mk_eq_of_joined ?_
    have hp : vpt (v + unit i) ∈ cubeSet (v, ({i} : Finset (Fin n))) := by
      rw [vpt_mem_cubeSet_iff]
      intro j
      simp only [top, mem_singleton, Pi.add_apply, unit_apply]
      split_ifs <;> omega
    exact joined_corner hcX hp
  exact hle hy

theorem exists_vertex (hX : IsComplex X) (p : Pi0 X) :
    ∃ v : Fin n → ℤ, ∃ h : (v, (∅ : Finset (Fin n))) ∈ X,
      ZerothHomotopy.mk ⟨vpt v, corner_mem_realisation h⟩ = p := by
  obtain ⟨⟨y, hy⟩, rfl⟩ := ZerothHomotopy.mk_surjective p
  obtain ⟨c, hc, hyc⟩ := Set.mem_iUnion₂.mp hy
  exact ⟨c.1, face_mem hX hc (empty_subset _), (mk_eq_of_joined (joined_corner hc hyc)).symm⟩

theorem aug_surjective (hX : IsComplex X) :
    ∀ q : Pi0 X →₀ ℤ, ∃ x ∈ chains X 0, aug X x = q := by
  intro q
  induction q using Finsupp.induction_linear with
  | zero => exact ⟨0, Submodule.zero_mem _, map_zero _⟩
  | add f g hf hg =>
    obtain ⟨x, hx, rfl⟩ := hf
    obtain ⟨y, hy, rfl⟩ := hg
    exact ⟨x + y, Submodule.add_mem _ hx hy, map_add _ _ _⟩
  | single p a =>
    obtain ⟨v, hv, rfl⟩ := exists_vertex hX p
    refine ⟨a • Finsupp.single (v, (∅ : Finset (Fin n))) 1,
      Submodule.smul_mem _ _ (vertex_mem_chains hv), ?_⟩
    rw [map_smul, aug_single, gen_of_mem hv]
    simp

theorem ker_aug (hX : IsComplex X) {x : Chain n} (hx : x ∈ chains X 0) (h0 : aug X x = 0) :
    x ∈ boundaries X 0 := by
  classical
  choose rep hrep hrepp using (exists_vertex hX)
  set ψ : (Pi0 X →₀ ℤ) →ₗ[ℤ] Chain n :=
    Finsupp.linearCombination ℤ (fun p => Finsupp.single (rep p, (∅ : Finset (Fin n))) 1)
  have key : chains X 0 ≤ (boundaries X 0).comap (LinearMap.id - ψ ∘ₗ aug X) := by
    unfold chains
    rw [Finsupp.supported_eq_span_single, Submodule.span_le]
    rintro _ ⟨c, hc, rfl⟩
    obtain ⟨hcX, hc0⟩ := cells_zero hc
    obtain ⟨v, S⟩ := c
    simp only at hc0; subst hc0
    simp only [SetLike.mem_coe, Submodule.mem_comap, LinearMap.sub_apply, LinearMap.id_apply,
      LinearMap.coe_comp, Function.comp_apply, aug_single, gen_of_mem hcX]
    have hψ : ∀ p : Pi0 X, ψ (Finsupp.single p 1) = Finsupp.single (rep p, ∅) 1 := fun p => by
      simp [ψ, Finsupp.linearCombination_single]
    rw [hψ]
    exact homologous_of_conn (conn_of_joined hX hcX (hrep _) (joined_of_mk_eq (hrepp _).symm))
  have := key hx
  simp only [Submodule.mem_comap, LinearMap.sub_apply, LinearMap.id_apply, LinearMap.coe_comp,
    Function.comp_apply, h0, map_zero, sub_zero] at this
  exact this

/-- **Cubical `H₀` is free on the path components of the realisation**:
`H₀(X) ≃ ℤ[π₀|X|]`. -/
noncomputable def homology_zero_equiv (hX : IsComplex X) :
    homology X 0 ≃ₗ[ℤ] (Pi0 X →₀ ℤ) := by
  set φ : cycles X 0 →ₗ[ℤ] (Pi0 X →₀ ℤ) := aug X ∘ₗ (cycles X 0).subtype
  have hsurj : Function.Surjective φ := by
    intro q
    obtain ⟨x, hx, hxq⟩ := aug_surjective hX q
    exact ⟨⟨x, cycles_zero.symm ▸ hx⟩, hxq⟩
  have hker : (boundaries X 0).comap (cycles X 0).subtype = LinearMap.ker φ := by
    ext ⟨x, hx⟩
    simp only [Submodule.mem_comap, Submodule.subtype_apply, LinearMap.mem_ker, φ,
      LinearMap.coe_comp, Function.comp_apply]
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact aug_bd hX hy
    · intro h0
      exact ker_aug hX (cycles_zero ▸ hx) h0
  exact (Submodule.quotEquivOfEq _ _ hker).trans (φ.quotKerEquivOfSurjective hsurj)

end Algebra

section Singular

open CategoryTheory AlgebraicTopology

open Classical in
/-- Mathlib's singular `H₀(Y; ℤ)` is the free abelian group on the path components. -/
noncomputable def singularH0Equiv (Y : TopCat.{0}) :
    ((singularHomologyFunctor (ModuleCat.{0} ℤ) 0).obj (ModuleCat.of ℤ ℤ)).obj Y ≃ₗ[ℤ]
      (ZerothHomotopy Y →₀ ℤ) :=
  ((TopCat.singularHomology₀Iso Y (ModuleCat.of ℤ ℤ)) ≪≫
    ModuleCat.coprodIsoDirectSum _).toLinearEquiv ≪≫ₗ (finsuppLEquivDirectSum ℤ ℤ _).symm

/-- **Cubical and singular `H₀` agree**: for a finite cubical complex `X ⊆ ℤⁿ`,
`H₀(X) ≅ H₀(|X|; ℤ)` (Mathlib's singular homology of the realisation `|X| ⊆ ℝⁿ`). -/
theorem homology_zero_singular {X : Finset (Cube n)} (hX : IsComplex X) :
    Nonempty (homology X 0 ≃ₗ[ℤ]
      ((singularHomologyFunctor (ModuleCat.{0} ℤ) 0).obj (ModuleCat.of ℤ ℤ)).obj
        (TopCat.of (realisation X))) :=
  ⟨(homology_zero_equiv hX).trans (singularH0Equiv (TopCat.of (realisation X))).symm⟩

end Singular

end QE.CubicalSingular
