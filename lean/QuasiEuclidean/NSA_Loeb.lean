-- SPDX-License-Identifier: MIT
-- Copyright 2026 Metere Industries, Inc. Author: Alfredo Metere.
-- Quasi-Euclidean Granular Geometry. Any derivative work must carry this notice:
--   This work is derivative of the Quasi-Euclidean Granular Geometry book
--   authored by Alfredo Metere. Copyright 2026 Metere Industries, Inc.
--   All rights reserved
-- See LICENSE.md and NOTICE.

import QuasiEuclidean.NSA_Internal
import QuasiEuclidean.BerryEsseenInfra

/-!
# Loeb measure, Anderson's theorem, and Anderson's construction of Brownian motion

Built on the internal-set calculus of `QuasiEuclidean.NSA_Internal`.

* `HypMeasure α` : an internal finitely additive measure on a hyperfinite set
  `Ω = [supp n]`, given by internal nonnegative weights `[weight n]`;
  `HypMeasure.mass S ∈ ℝ*` is its value on an internal set `S`.  Examples:
  the normalised counting measure `HypMeasure.counting A`
  (`mass S = hcard (S ∩ Ω) / hcard Ω`) and the granular lattice measure `latMeasure`.
* `stE : ℝ* → ℝ≥0∞` : the standard part, `∞` on unlimited hyperreals.
* **Countable additivity on the internal algebra via saturation**
  (`isInternal_cover_finite`, `internal_iUnion_eventually_empty`): a countable
  internal cover of an internal set has a finite subcover; pairwise disjoint internal
  sets with internal union are eventually empty.
* `HypMeasure.loeb` : the **Loeb measure**, the Carathéodory extension
  (Mathlib's `AddContent.measure`) of `st ∘ ν` from the internal algebra to the
  σ-algebra it generates (the `MeasurableSpace` instance on `Ult α`).  It extends
  `st ∘ ν` (`loeb_internal`), is unique (`loeb_unique`), is a probability measure
  for the counting measure, and its completion is characterised by internal inner
  and outer approximation (`nullMeasurableSet_iff_approx`, `loeb_eq_iInf`,
  `loeb_eq_iSup`).  The Loeb algebra is `{B | NullMeasurableSet B ν.loeb}`.  When
  `ν(Ω)` is unlimited the same construction is the σ-finite Loeb measure; it agrees box by
  box with the Loeb measure of the restriction (`loeb_restrict`).
* **Standard part map**: `stInv E` (the monadic preimage `st⁻¹(E)`), its measurability for
  Borel `E` (`measurableSet_stInv`), the push-forward `stMeasure`, and shadow criteria on
  boxes (`stMeasure_eq_of_Icc`, `stMeasure_eq_volume_pi`, `stMeasure_eq_pi`).
* **Anderson's theorem** (shadow results): `anderson`, `anderson_pushforward`,
  `anderson_iff` (the Loeb-measurable shadows are exactly the Lebesgue sets) for the granular
  lattice measure on `𝕃ⁿ`, and `loeb_shadow_uniform` for the uniform law on `[0,1) ∩ 𝕃`.
* **External uncountability** of `{0,1}^K` by an internal diagonal
  (`exists_mem_bitStringsH_ne`, `bitStringsH_not_countable`).
* **Anderson's random walk** on the hyperfinite coin space: exact independence of disjoint
  blocks of coins, the CLT step (from `QE.Prob.BE.clt_error_explicit`), the reflection
  principle and an internal oscillation bound; the Loeb shadow `b = st W` is a standard
  Brownian motion on `[0, T]` (`anderson_wiener`).  Gaussian laws and Lebesgue measure appear
  only as shadows.
-/

open Filter MeasureTheory Set ArchimedeanClass Function
open scoped ENNReal Topology

noncomputable section

namespace QE.NSA

variable {α : Type*}

/-! ## The extended standard part -/

section StE

open Classical in
/-- The standard part of a hyperreal as an extended nonnegative real: `ofReal (st x)` for
limited `x`, and `∞` for unlimited `x`. -/
def stE (x : ℝ*) : ℝ≥0∞ := if IsFinite x then ENNReal.ofReal (stdPart x) else ⊤

theorem stE_of_isFinite {x : ℝ*} (hx : IsFinite x) : stE x = ENNReal.ofReal (stdPart x) := by
  simp [stE, hx]

theorem stE_of_not_isFinite {x : ℝ*} (hx : ¬ IsFinite x) : stE x = ⊤ := by
  simp [stE, hx]

theorem isFinite_of_nonneg_of_le {x y : ℝ*} (hx : 0 ≤ x) (hxy : x ≤ y) (hy : IsFinite y) :
    IsFinite x := by
  obtain ⟨r, hr⟩ := (isFinite_iff_abs_le y).1 hy
  refine (isFinite_iff_abs_le x).2 ⟨r, ?_⟩
  rw [abs_of_nonneg hx]
  exact hxy.trans ((le_abs_self y).trans hr)

theorem stdPart_nonneg' {x : ℝ*} (hx0 : 0 ≤ x) (hx : IsFinite x) : 0 ≤ stdPart x := by
  have h := stdPart_mono (coe_isFinite 0) hx (by simpa using hx0)
  rwa [Hyperreal.stdPart_coe] at h

theorem stE_add {x y : ℝ*} (hx : 0 ≤ x) (hy : 0 ≤ y) : stE (x + y) = stE x + stE y := by
  by_cases hxy : IsFinite (x + y)
  · have hxf : IsFinite x := isFinite_of_nonneg_of_le hx (le_add_of_nonneg_right hy) hxy
    have hyf : IsFinite y := isFinite_of_nonneg_of_le hy (le_add_of_nonneg_left hx) hxy
    rw [stE_of_isFinite hxy, stE_of_isFinite hxf, stE_of_isFinite hyf, stdPart_add' hxf hyf,
      ENNReal.ofReal_add (stdPart_nonneg' hx hxf) (stdPart_nonneg' hy hyf)]
  · rw [stE_of_not_isFinite hxy]
    by_cases hxf : IsFinite x
    · have hyf : ¬ IsFinite y := fun h => hxy (hxf.add h)
      rw [stE_of_not_isFinite hyf]; simp
    · rw [stE_of_not_isFinite hxf]; simp

theorem stE_mono {x y : ℝ*} (hx : 0 ≤ x) (hxy : x ≤ y) : stE x ≤ stE y := by
  by_cases hy : IsFinite y
  · have hxf := isFinite_of_nonneg_of_le hx hxy hy
    rw [stE_of_isFinite hy, stE_of_isFinite hxf]
    exact ENNReal.ofReal_le_ofReal (stdPart_mono hxf hy hxy)
  · rw [stE_of_not_isFinite hy]; exact le_top

theorem stE_coe (r : ℝ) : stE (r : ℝ*) = ENNReal.ofReal r := by
  rw [stE_of_isFinite (coe_isFinite r), Hyperreal.stdPart_coe]

theorem stE_zero : stE 0 = 0 := by
  have := stE_coe 0; simpa using this

theorem stE_lt_top {x : ℝ*} (hx : IsFinite x) : stE x < ⊤ := by
  rw [stE_of_isFinite hx]; exact ENNReal.ofReal_lt_top

theorem stE_lt_top_iff {x : ℝ*} : stE x < ⊤ ↔ IsFinite x := by
  refine ⟨fun h => ?_, stE_lt_top⟩
  by_contra hx; rw [stE_of_not_isFinite hx] at h; exact lt_irrefl _ h

/-- If `stE x < r` for a standard `r`, then `x < r`. -/
theorem lt_of_stE_lt {x : ℝ*} {r : ℝ} (h : stE x < ENNReal.ofReal r) : x < (r : ℝ*) := by
  by_cases hx : IsFinite x
  · rw [stE_of_isFinite hx] at h
    have h1 : stdPart x < r := (ENNReal.ofReal_lt_ofReal_iff'.1 h).1
    have h2 := isInfinitesimal_sub_stdPart hx
    have h3 := h2.abs_lt (sub_pos.2 h1)
    have h4 : x - (stdPart x : ℝ*) ≤ |x - (stdPart x : ℝ*)| := le_abs_self _
    rw [Hyperreal.coe_sub] at h3
    linarith
  · rw [stE_of_not_isFinite hx] at h; exact absurd h (not_lt.2 le_top)

/-- If `x ≤ r` for a standard `r`, then `stE x ≤ r`. -/
theorem stE_le_of_le {x : ℝ*} {r : ℝ} (hx : 0 ≤ x) (h : x ≤ (r : ℝ*)) :
    stE x ≤ ENNReal.ofReal r := by
  rw [← stE_coe]; exact stE_mono hx h

/-- If `[f n] - L` is infinitesimal for a standard `L`, then `stE [f n] = L`. -/
theorem stE_of_isInfinitesimal_sub {x : ℝ*} {L : ℝ} (h : IsInfinitesimal (x - (L : ℝ*))) :
    stE x = ENNReal.ofReal L := by
  have hx : IsFinite x := by
    have : x = (x - (L : ℝ*)) + (L : ℝ*) := by ring
    rw [this]; exact h.isFinite.add (coe_isFinite L)
  rw [stE_of_isFinite hx, stdPart_unique h]

/-- `x_n → L` along the ultrafilter implies `[x_n] - L` is infinitesimal. -/
theorem isInfinitesimal_ofSeq_sub_of_tendsto {f : ℕ → ℝ} {L : ℝ}
    (h : Tendsto f (hyperfilter ℕ : Filter ℕ) (𝓝 L)) :
    IsInfinitesimal (Hyperreal.ofSeq f - (L : ℝ*)) := by
  show IsInfinitesimal (Hyperreal.ofSeq (fun n => f n - L))
  rw [isInfinitesimal_ofSeq_iff]
  intro r hr
  filter_upwards [Metric.tendsto_nhds.1 h r hr] with n hn
  rwa [Real.dist_eq] at hn

/-- If `x_n → L` along the ultrafilter, then `stE [x_n] = L`. -/
theorem stE_ofSeq_of_tendsto {f : ℕ → ℝ} {L : ℝ}
    (h : Tendsto f (hyperfilter ℕ : Filter ℕ) (𝓝 L)) :
    stE (Hyperreal.ofSeq f) = ENNReal.ofReal L :=
  stE_of_isInfinitesimal_sub (isInfinitesimal_ofSeq_sub_of_tendsto h)

end StE

/-! ## Internal finitely additive measures on hyperfinite sets -/

/-- An internal finitely additive measure on the hyperfinite set `Ω = [supp n]`: the
internal measure of an internal set `[B n]` is the hyperfinite sum
`[∑_{x ∈ supp n, x ∈ B n} weight n x]` of internal nonnegative weights. -/
structure HypMeasure (α : Type*) where
  /-- The finite sets presenting the hyperfinite support `Ω`. -/
  supp : ℕ → Finset α
  /-- The internal weights. -/
  weight : ℕ → α → ℝ
  weight_nonneg : ∀ n x, 0 ≤ weight n x

namespace HypMeasure

variable (ν : HypMeasure α)

/-- The hyperfinite support `Ω = [supp n]`. -/
def carrier : Set (Ult α) := hfin ν.supp

/-- The `n`-th coordinate of the internal measure of `[B n]`. -/
def seqMass (B : ℕ → Set α) (n : ℕ) : ℝ :=
  ∑ x ∈ @Finset.filter _ (· ∈ B n) (Classical.decPred _) (ν.supp n), ν.weight n x

/-- The internal measure of the internal set presented by `B`. -/
def massOf (B : ℕ → Set α) : ℝ* := Hyperreal.ofSeq (ν.seqMass B)

theorem seqMass_nonneg (B : ℕ → Set α) (n : ℕ) : 0 ≤ ν.seqMass B n :=
  Finset.sum_nonneg fun x _ => ν.weight_nonneg n x

theorem seqMass_congr {B C : ℕ → Set α} {n : ℕ} (h : B n = C n) :
    ν.seqMass B n = ν.seqMass C n := by
  unfold seqMass; congr 1; ext x; simp [h]

theorem massOf_congr {B C : ℕ → Set α} (h : internal B = internal C) :
    ν.massOf B = ν.massOf C := by
  have := (internal_eq_iff B C).1 h
  refine Germ.coe_eq.2 ?_
  filter_upwards [this] with n hn using ν.seqMass_congr hn

open Classical in
/-- The internal measure `ν(S) ∈ ℝ*` of an internal set `S` (junk value `0` on external
sets, which are never used). -/
def mass (S : Set (Ult α)) : ℝ* := if h : IsInternal S then ν.massOf h.choose else 0

theorem mass_internal (B : ℕ → Set α) : ν.mass (internal B) = ν.massOf B := by
  have h : IsInternal (internal B) := ⟨B, rfl⟩
  simp only [mass, h, dite_true]
  exact ν.massOf_congr h.choose_spec.symm

theorem mass_nonneg (S : Set (Ult α)) : 0 ≤ ν.mass S := by
  unfold mass
  split_ifs
  · exact Germ.coe_nonneg.2 (Eventually.of_forall fun n => ν.seqMass_nonneg _ n)
  · exact le_rfl

theorem mass_empty : ν.mass ∅ = 0 := by
  rw [← internal_empty, mass_internal]
  show Hyperreal.ofSeq _ = Hyperreal.ofSeq (fun _ => 0)
  congr 1; funext n; simp [seqMass]

/-- **Finite additivity** of the internal measure. -/
theorem mass_union {S T : Set (Ult α)} (hS : IsInternal S) (hT : IsInternal T)
    (hd : Disjoint S T) : ν.mass (S ∪ T) = ν.mass S + ν.mass T := by
  obtain ⟨B, rfl⟩ := hS; obtain ⟨C, rfl⟩ := hT
  rw [← internal_union, mass_internal, mass_internal, mass_internal]
  have h0 : internal (fun n => B n ∩ C n) = internal (fun _ => (∅ : Set α)) := by
    rw [internal_inter, Set.disjoint_iff_inter_eq_empty.1 hd, internal_empty]
  have hev := (internal_eq_iff _ _).1 h0
  refine Germ.coe_eq.2 ?_
  filter_upwards [hev] with n hn
  classical
  show ν.seqMass _ n = ν.seqMass B n + ν.seqMass C n
  unfold seqMass
  rw [← Finset.sum_union]
  · apply Finset.sum_congr _ (fun _ _ => rfl)
    ext x; simp [Finset.mem_union, Finset.mem_filter]; tauto
  · rw [Finset.disjoint_filter]
    intro x _ hb hc
    have : x ∈ B n ∩ C n := ⟨hb, hc⟩
    rw [hn] at this; exact this

/-- Monotonicity of the internal measure. -/
theorem mass_mono {S T : Set (Ult α)} (hS : IsInternal S) (hT : IsInternal T) (h : S ⊆ T) :
    ν.mass S ≤ ν.mass T := by
  obtain ⟨B, rfl⟩ := hS; obtain ⟨C, rfl⟩ := hT
  rw [mass_internal, mass_internal]
  have hsub := (internal_subset_iff _ _).1 h
  refine Germ.coe_le.2 ?_
  filter_upwards [hsub] with n hn
  classical
  show ν.seqMass B n ≤ ν.seqMass C n
  unfold seqMass
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun x _ _ => ν.weight_nonneg n x)
  intro x hx
  simp only [Finset.mem_filter] at hx ⊢
  exact ⟨hx.1, hn hx.2⟩

/-- The internal measure only sees the support: `ν(S) = ν(S ∩ Ω)`. -/
theorem mass_inter_carrier {S : Set (Ult α)} (hS : IsInternal S) :
    ν.mass (S ∩ ν.carrier) = ν.mass S := by
  obtain ⟨B, rfl⟩ := hS
  rw [carrier, hfin, ← internal_inter, mass_internal, mass_internal]
  refine Germ.coe_eq.2 (Eventually.of_forall fun n => ?_)
  show ν.seqMass _ n = ν.seqMass B n
  unfold seqMass
  congr 1; ext x; simp only [Finset.mem_filter, Set.mem_inter_iff, Finset.mem_coe]; tauto

theorem mass_compl_carrier : ν.mass ν.carrierᶜ = 0 := by
  have h := ν.mass_inter_carrier (S := ν.carrierᶜ) (isInternal_internal _).compl
  rw [Set.compl_inter_self, mass_empty] at h
  exact h.symm

/-! ### The normalised counting measure -/

/-- The internal cardinality `hcard S`, cast to `ℝ*`. -/
def hcardR (S : Set (Ult α)) : ℝ* := Germ.map (fun k : ℕ => (k : ℝ)) (hcard S)

end HypMeasure

/-- The **normalised counting measure** (uniform probability) on the hyperfinite set
`Ω = [A n]`: every point of `A n` has weight `1 / #(A n)`. -/
def HypMeasure.counting (A : ℕ → Finset α) : HypMeasure α where
  supp := A
  weight n _ := 1 / ((A n).card : ℝ)
  weight_nonneg n _ := by positivity

namespace HypMeasure

/-- The counting measure is `ν(S) = hcard (S ∩ Ω) / hcard Ω`. -/
theorem counting_mass (A : ℕ → Finset α) {S : Set (Ult α)} (hS : IsInternal S) :
    (counting A).mass S = hcardR (S ∩ hfin A) / hcardR (hfin A) := by
  classical
  obtain ⟨B, rfl⟩ := hS
  have hinter : internal B ∩ hfin A = hfin (fun n => (A n).filter (· ∈ B n)) := by
    unfold hfin; rw [← internal_inter]
    apply internal_congr; refine Eventually.of_forall fun n => ?_
    ext x; simp [and_comm]
  rw [mass_internal, hinter, hcardR, hcardR, hcard_hfin, hcard_hfin]
  refine Germ.coe_eq.2 (Eventually.of_forall fun n => ?_)
  show ∑ x ∈ @Finset.filter _ (· ∈ B n) (Classical.decPred _) (A n), 1 / ((A n).card : ℝ) =
    ((A n).filter (· ∈ B n)).card / ((A n).card : ℝ)
  rw [Finset.sum_const, nsmul_eq_mul, mul_one_div]

/-- The counting measure of a nonempty hyperfinite set has total mass `1`. -/
theorem counting_mass_univ (A : ℕ → Finset α) (hne : (hfin A).Nonempty) :
    (counting A).mass univ = 1 := by
  rw [← internal_univ, mass_internal]
  have hev : ∀ᶠ n in (hyperfilter ℕ : Filter ℕ), (A n).Nonempty := by
    filter_upwards [(internal_nonempty_iff _).1 hne] with n hn
    exact Finset.coe_nonempty.1 hn
  refine Germ.coe_eq.2 ?_
  filter_upwards [hev] with n hn
  show ∑ x ∈ @Finset.filter _ (· ∈ (Set.univ : Set α)) (Classical.decPred _) (A n),
    1 / ((A n).card : ℝ) = 1
  rw [Finset.sum_filter]
  simp only [Set.mem_univ, ite_true]
  rw [Finset.sum_const, nsmul_eq_mul, mul_one_div, div_self]
  exact_mod_cast hn.card_pos.ne'

end HypMeasure

/-! ## Countable additivity on the internal algebra, via saturation -/

section Saturation

/-- A finite union of internal sets is internal. -/
theorem isInternal_biUnion_range (f : ℕ → Set (Ult α)) (hf : ∀ i, IsInternal (f i)) (k : ℕ) :
    IsInternal (⋃ i ∈ Finset.range k, f i) := by
  induction k with
  | zero => simpa using (isInternal_empty : IsInternal (∅ : Set (Ult α)))
  | succ k ih =>
    rw [Finset.range_add_one, Finset.set_biUnion_insert]
    exact (hf k).union ih

/-- **Finite subcovers (countable saturation).** If an internal set `S` is covered by
countably many internal sets `f i`, then finitely many of them already cover `S`. -/
theorem isInternal_cover_finite {S : Set (Ult α)} (hS : IsInternal S) (f : ℕ → Set (Ult α))
    (hf : ∀ i, IsInternal (f i)) (hcov : S ⊆ ⋃ i, f i) :
    ∃ N, S ⊆ ⋃ i ∈ Finset.range N, f i := by
  by_contra hne
  push Not at hne
  let T : ℕ → Set (Ult α) := fun k => S \ ⋃ i ∈ Finset.range k, f i
  have hT : ∀ k, IsInternal (T k) := fun k => hS.diff (isInternal_biUnion_range f hf k)
  have hne' : ∀ k, (T k).Nonempty := fun k => by
    obtain ⟨x, hxS, hx⟩ := Set.not_subset.1 (hne k); exact ⟨x, hxS, hx⟩
  have hanti : Antitone T := by
    intro j k hjk x hx
    refine ⟨hx.1, fun h => hx.2 ?_⟩
    obtain ⟨i, hi, hxi⟩ := Set.mem_iUnion₂.1 h
    exact Set.mem_iUnion₂.2 ⟨i, Finset.range_mono hjk hi, hxi⟩
  obtain ⟨x, hx⟩ := saturation_decreasing T hT hne' hanti
  rw [Set.mem_iInter] at hx
  obtain ⟨i, hi⟩ := Set.mem_iUnion.1 (hcov (hx 0).1)
  exact (hx (i + 1)).2 (Set.mem_iUnion₂.2 ⟨i, Finset.mem_range.2 (Nat.lt_succ_self i), hi⟩)

/-- **The classic step.** If pairwise disjoint internal sets `B k` have an internal
union, then all but finitely many of them are empty. -/
theorem internal_iUnion_eventually_empty (B : ℕ → Set (Ult α)) (hB : ∀ k, IsInternal (B k))
    (hd : Pairwise (Disjoint on B)) (hU : IsInternal (⋃ k, B k)) :
    ∃ N, ∀ k, N ≤ k → B k = ∅ := by
  obtain ⟨N, hN⟩ := isInternal_cover_finite hU B hB subset_rfl
  refine ⟨N, fun k hk => Set.eq_empty_of_forall_notMem fun x hx => ?_⟩
  obtain ⟨j, hj, hxj⟩ := Set.mem_iUnion₂.1 (hN (Set.mem_iUnion.2 ⟨k, hx⟩))
  have hjk : j ≠ k := by
    intro h; rw [h] at hj; exact absurd (Finset.mem_range.1 hj) (not_lt.2 hk)
  exact Set.disjoint_left.1 (hd hjk) hxj hx

end Saturation

/-! ## The Loeb measure -/

/-- The internal subsets of `Ult α` form a ring (indeed an algebra) of sets. -/
theorem isSetRing_internal : IsSetRing {S : Set (Ult α) | IsInternal S} where
  empty_mem := isInternal_empty
  union_mem := fun _ _ hs ht => IsInternal.union hs ht
  sdiff_mem := fun _ _ hs ht => IsInternal.diff hs ht

/-- The **Loeb σ-algebra** `σ(𝒜)` on `Ult α`: the σ-algebra generated by the internal
sets. -/
instance loebMeasurableSpace : MeasurableSpace (Ult α) :=
  MeasurableSpace.generateFrom {S | IsInternal S}

theorem IsInternal.measurableSet {S : Set (Ult α)} (h : IsInternal S) : MeasurableSet S :=
  MeasurableSpace.measurableSet_generateFrom h

theorem isPiSystem_internal : IsPiSystem {S : Set (Ult α) | IsInternal S} :=
  fun _ hs _ ht _ => IsInternal.inter hs ht

namespace HypMeasure

variable (ν : HypMeasure α)

/-- The finitely additive set function `st ∘ ν` on the internal algebra, as a Mathlib
additive content. -/
def stContent : AddContent ℝ≥0∞ {S : Set (Ult α) | IsInternal S} :=
  isSetRing_internal.addContent_of_union (fun S => stE (ν.mass S))
    (by simp only [mass_empty, stE_zero])
    (fun hs ht hd => by
      rw [ν.mass_union hs ht hd, stE_add (ν.mass_nonneg _) (ν.mass_nonneg _)])

theorem stContent_apply (S : Set (Ult α)) : ν.stContent S = stE (ν.mass S) := rfl

/-- `st ∘ ν` is σ-subadditive on the internal algebra (by saturation, every countable
internal cover of an internal set has a finite subcover). -/
theorem stContent_isSigmaSubadditive : ν.stContent.IsSigmaSubadditive := by
  intro f hf hU
  obtain ⟨N, hN⟩ := isInternal_cover_finite hU f hf subset_rfl
  calc ν.stContent (⋃ i, f i) ≤ ν.stContent (⋃ i ∈ Finset.range N, f i) :=
        addContent_mono isSetRing_internal.isSetSemiring hU (isInternal_biUnion_range f hf N) hN
    _ ≤ ∑ i ∈ Finset.range N, ν.stContent (f i) :=
        addContent_biUnion_le isSetRing_internal (fun i _ => hf i)
    _ ≤ ∑' i, ν.stContent (f i) := ENNReal.sum_le_tsum _

/-- **`st ∘ ν` is countably additive on the internal algebra** (a premeasure). -/
theorem stContent_iUnion (f : ℕ → Set (Ult α)) (hf : ∀ i, IsInternal (f i))
    (hU : IsInternal (⋃ i, f i)) (hd : Pairwise (Disjoint on f)) :
    stE (ν.mass (⋃ i, f i)) = ∑' i, stE (ν.mass (f i)) :=
  addContent_iUnion_eq_tsum_of_disjoint_of_IsSigmaSubadditive isSetRing_internal.isSetSemiring
    ν.stContent_isSigmaSubadditive f hf hU hd

/-- The **Loeb measure** of `ν`: the Carathéodory extension of `st ∘ ν` to the
σ-algebra generated by the internal sets. -/
def loeb : Measure (Ult α) :=
  ν.stContent.measure isSetRing_internal.isSetSemiring le_rfl ν.stContent_isSigmaSubadditive

/-- The Loeb measure extends `st ∘ ν`. -/
theorem loeb_internal {S : Set (Ult α)} (hS : IsInternal S) : ν.loeb S = stE (ν.mass S) :=
  ν.stContent.measure_eq isSetRing_internal.isSetSemiring rfl ν.stContent_isSigmaSubadditive hS

theorem isInternal_carrier : IsInternal ν.carrier := isInternal_internal _

theorem loeb_compl_carrier : ν.loeb ν.carrierᶜ = 0 := by
  rw [ν.loeb_internal ν.isInternal_carrier.compl, mass_compl_carrier, stE_zero]

/-- The Loeb measure is concentrated on the support `Ω`. -/
theorem loeb_inter_carrier (B : Set (Ult α)) : ν.loeb (B ∩ ν.carrier) = ν.loeb B :=
  measure_inter_conull ν.loeb_compl_carrier

theorem loeb_univ : ν.loeb univ = stE (ν.mass univ) := ν.loeb_internal isInternal_univ

theorem isFiniteMeasure_loeb (hfin : IsFinite (ν.mass univ)) : IsFiniteMeasure ν.loeb :=
  ⟨by rw [loeb_univ]; exact stE_lt_top hfin⟩

/-- **Uniqueness**: when `ν(Ω)` is limited, the Loeb measure is the only measure on
`σ(𝒜)` extending `st ∘ ν`. -/
theorem loeb_unique (hfin : IsFinite (ν.mass univ)) (μ : Measure (Ult α))
    (hμ : ∀ S, IsInternal S → μ S = stE (ν.mass S)) : μ = ν.loeb := by
  have := ν.isFiniteMeasure_loeb hfin
  refine (ext_of_generate_finite _ rfl isPiSystem_internal (fun S hS => ?_) ?_).symm
  · rw [ν.loeb_internal hS, hμ S hS]
  · rw [loeb_univ, hμ _ isInternal_univ]

/-- The Loeb measure of the normalised counting measure on a nonempty hyperfinite set is a
**probability measure**. -/
theorem isProbabilityMeasure_loeb_counting (A : ℕ → Finset α) (hne : (hfin A).Nonempty) :
    IsProbabilityMeasure (counting A).loeb :=
  ⟨by rw [loeb_univ, counting_mass_univ A hne, ← Hyperreal.coe_one, stE_coe,
    ENNReal.ofReal_one]⟩

/-! ## Internal approximation and the Loeb algebra -/

/-- **Saturation for internal measures.** An increasing sequence of internal sets, each of
internal measure `≤ c` (`c` standard), is contained in a single internal set of internal
measure `≤ c`. (Countable saturation applied to the internal sets
`{X : X ⊇ D k, ν(X) ≤ c}` of the ultrapower of `Set α`.) -/
theorem exists_internal_superset_mass_le (D : ℕ → Set (Ult α)) (hD : ∀ k, IsInternal (D k))
    (hmono : Monotone D) {c : ℝ} (hc : ∀ k, ν.mass (D k) ≤ (c : ℝ*)) :
    ∃ E, IsInternal E ∧ (∀ k, D k ⊆ E) ∧ ν.mass E ≤ (c : ℝ*) := by
  choose B hB using hD
  let S : ℕ → Set (Ult (Set α)) := fun k =>
    internal (fun n => {X : Set α | B k n ⊆ X ∧ ν.seqMass (fun _ => X) n ≤ c})
  have hS : ∀ k, IsInternal (S k) := fun k => isInternal_internal _
  have hsub : ∀ j k, j ≤ k → ∀ᶠ n in (hyperfilter ℕ : Filter ℕ), B j n ⊆ B k n := by
    intro j k hjk
    have := hmono hjk; rw [hB j, hB k] at this
    exact (internal_subset_iff _ _).1 this
  have hmass : ∀ k, ∀ᶠ n in (hyperfilter ℕ : Filter ℕ), ν.seqMass (B k) n ≤ c := by
    intro k
    have := hc k; rw [hB k, mass_internal] at this
    exact ofSeq_le_const.1 this
  obtain ⟨x, hx⟩ := countable_saturation_internal S hS (fun K => by
    refine ⟨((fun n => B K n : ℕ → Set α) : Ult (Set α)), fun k hk => ?_⟩
    refine (mem_internal _ _).2 ?_
    filter_upwards [hsub k K hk, hmass K] with n h1 h2
    exact ⟨h1, h2⟩)
  obtain ⟨X, rfl⟩ := exists_rep x
  have hX : ∀ k, ∀ᶠ n in (hyperfilter ℕ : Filter ℕ),
      B k n ⊆ X n ∧ ν.seqMass (fun _ => X n) n ≤ c :=
    fun k => (mem_internal _ X).1 (hx k)
  refine ⟨internal X, isInternal_internal _, fun k => ?_, ?_⟩
  · rw [hB k]; exact (internal_subset_iff _ _).2 ((hX k).mono fun n h => h.1)
  · rw [mass_internal]
    refine ofSeq_le_const.2 ?_
    filter_upwards [hX 0] with n h
    exact h.2

theorem loeb_eq_inducedOuterMeasure {B : Set (Ult α)} (hB : MeasurableSet B) :
    ν.loeb B = inducedOuterMeasure (fun x (_ : x ∈ {S : Set (Ult α) | IsInternal S}) =>
      ν.stContent x) isSetRing_internal.isSetSemiring.empty_mem addContent_empty B := by
  unfold loeb AddContent.measure
  exact trim_measurableSet_eq _ hB

/-- The Loeb measure of a measurable set is approximated by countable internal covers. -/
theorem exists_cover_of_loeb_lt {B : Set (Ult α)} (hB : MeasurableSet B) {c : ℝ≥0∞}
    (hc : ν.loeb B < c) :
    ∃ f : ℕ → Set (Ult α), (∀ i, IsInternal (f i)) ∧ B ⊆ ⋃ i, f i ∧
      ∑' i, stE (ν.mass (f i)) < c := by
  rw [ν.loeb_eq_inducedOuterMeasure hB, inducedOuterMeasure,
    OuterMeasure.ofFunction_apply] at hc
  simp only [iInf_lt_iff] at hc
  obtain ⟨f, hcov, hsum⟩ := hc
  set m := fun x (_ : x ∈ {S : Set (Ult α) | IsInternal S}) => ν.stContent x
  have hfin : ∀ i, extend m (f i) < ⊤ := fun i =>
    lt_of_le_of_lt (ENNReal.le_tsum (f := fun n => extend m (f n)) i) (hsum.trans_le le_top)
  have hint : ∀ i, IsInternal (f i) := fun i => by
    by_contra h
    have := extend_eq_top m h
    have h2 := hfin i
    rw [this] at h2; exact lt_irrefl _ h2
  refine ⟨f, hint, hcov, ?_⟩
  convert hsum using 3 with i
  rw [extend_eq m (hint i)]; rfl

/-- **Outer approximation.** If `ν(Ω)` is limited, every set of `σ(𝒜)` is contained in an
internal set of almost the same Loeb measure. -/
theorem exists_internal_superset (hfin : IsFinite (ν.mass univ)) {B : Set (Ult α)}
    (hB : MeasurableSet B) {η : ℝ} (hη : 0 < η) :
    ∃ C, IsInternal C ∧ B ⊆ C ∧ ν.loeb (C \ B) ≤ ENNReal.ofReal η := by
  have := ν.isFiniteMeasure_loeb hfin
  set c0 := (ν.loeb B).toReal
  have hc0n : 0 ≤ c0 := ENNReal.toReal_nonneg
  have hc0 : ν.loeb B = ENNReal.ofReal c0 := (ENNReal.ofReal_toReal (measure_ne_top _ _)).symm
  obtain ⟨f, hf, hcov, hsum⟩ := ν.exists_cover_of_loeb_lt hB (c := ENNReal.ofReal (c0 + η / 2))
    (by rw [hc0]; exact (ENNReal.ofReal_lt_ofReal_iff'.2 ⟨by linarith, by linarith⟩))
  let D : ℕ → Set (Ult α) := fun k => ⋃ i ∈ Finset.range k, f i
  have hD : ∀ k, IsInternal (D k) := isInternal_biUnion_range f hf
  have hmono : Monotone D := by
    intro j k hjk x hx
    obtain ⟨i, hi, hxi⟩ := Set.mem_iUnion₂.1 hx
    exact Set.mem_iUnion₂.2 ⟨i, Finset.range_mono hjk hi, hxi⟩
  have hDc : ∀ k, ν.mass (D k) ≤ ((c0 + η / 2 : ℝ) : ℝ*) := by
    intro k
    refine (lt_of_stE_lt ?_).le
    calc stE (ν.mass (D k)) = ν.stContent (D k) := rfl
      _ ≤ ∑ i ∈ Finset.range k, ν.stContent (f i) :=
          addContent_biUnion_le isSetRing_internal (fun i _ => hf i)
      _ ≤ ∑' i, ν.stContent (f i) := ENNReal.sum_le_tsum _
      _ < _ := hsum
  obtain ⟨E, hE, hDE, hEm⟩ := ν.exists_internal_superset_mass_le D hD hmono hDc
  have hBE : B ⊆ E := by
    intro x hx
    obtain ⟨i, hi⟩ := Set.mem_iUnion.1 (hcov hx)
    exact hDE (i + 1) (Set.mem_iUnion₂.2 ⟨i, Finset.mem_range.2 (Nat.lt_succ_self i), hi⟩)
  refine ⟨E, hE, hBE, ?_⟩
  rw [measure_sdiff hBE hB.nullMeasurableSet (measure_ne_top _ _), ν.loeb_internal hE]
  have h1 : stE (ν.mass E) ≤ ENNReal.ofReal (c0 + η / 2) := stE_le_of_le (ν.mass_nonneg _) hEm
  rw [tsub_le_iff_left, hc0, ← ENNReal.ofReal_add hc0n hη.le]
  exact h1.trans (ENNReal.ofReal_le_ofReal (by linarith))

/-- **Inner approximation.** If `ν(Ω)` is limited, every set of `σ(𝒜)` contains an internal
set of almost the same Loeb measure. -/
theorem exists_internal_subset (hfin : IsFinite (ν.mass univ)) {B : Set (Ult α)}
    (hB : MeasurableSet B) {η : ℝ} (hη : 0 < η) :
    ∃ A, IsInternal A ∧ A ⊆ B ∧ ν.loeb (B \ A) ≤ ENNReal.ofReal η := by
  obtain ⟨C, hC, hBC, hle⟩ := ν.exists_internal_superset hfin hB.compl hη
  refine ⟨Cᶜ, hC.compl, Set.compl_subset_comm.1 hBC, ?_⟩
  have : B \ Cᶜ = C \ Bᶜ := by ext x; simp [and_comm]
  rwa [this]

/-- **The Loeb algebra** (the completion of `σ(𝒜)`): `B` is Loeb measurable iff for every
standard `η > 0` there are internal `A ⊆ B ⊆ C` with `ν(C \ A) < η`. -/
theorem nullMeasurableSet_iff_approx (hfin : IsFinite (ν.mass univ)) (B : Set (Ult α)) :
    NullMeasurableSet B ν.loeb ↔ ∀ η : ℝ, 0 < η → ∃ A C, IsInternal A ∧ IsInternal C ∧
      A ⊆ B ∧ B ⊆ C ∧ ν.mass (C \ A) < (η : ℝ*) := by
  have := ν.isFiniteMeasure_loeb hfin
  constructor
  · intro hB η hη
    obtain ⟨B1, hB1B, hB1, hae⟩ := hB.exists_measurable_subset_ae_eq
    set B2 := toMeasurable ν.loeb B
    have hBB2 : B ⊆ B2 := subset_toMeasurable _ _
    have hB2 : MeasurableSet B2 := measurableSet_toMeasurable _ _
    have hae2 : B2 =ᵐ[ν.loeb] B := hB.toMeasurable_ae_eq
    obtain ⟨A, hA, hAB1, hA'⟩ := ν.exists_internal_subset hfin hB1 (η := η / 3) (by positivity)
    obtain ⟨C, hC, hB2C, hC'⟩ := ν.exists_internal_superset hfin hB2 (η := η / 3)
      (by positivity)
    refine ⟨A, C, hA, hC, hAB1.trans hB1B, hBB2.trans hB2C, lt_of_stE_lt ?_⟩
    rw [← ν.loeb_internal (hC.diff hA)]
    have h0 : ν.loeb (B2 \ B1) = 0 := (ae_eq_set.1 (hae.trans hae2.symm)).2
    calc ν.loeb (C \ A) ≤ ν.loeb ((C \ B2) ∪ (B2 \ B1) ∪ (B1 \ A)) := by
          refine measure_mono ?_
          rintro x ⟨hxC, hxA⟩
          by_cases h2 : x ∈ B2 <;> by_cases h1 : x ∈ B1 <;> simp_all
      _ ≤ ν.loeb (C \ B2) + ν.loeb (B2 \ B1) + ν.loeb (B1 \ A) :=
          (measure_union_le _ _).trans (add_le_add_left (measure_union_le _ _) _)
      _ ≤ ENNReal.ofReal (η / 3) + 0 + ENNReal.ofReal (η / 3) := by
          rw [h0]; exact add_le_add (add_le_add hC' le_rfl) hA'
      _ < ENNReal.ofReal η := by
          rw [add_zero, ← ENNReal.ofReal_add (by positivity) (by positivity)]
          exact ENNReal.ofReal_lt_ofReal_iff'.2 ⟨by linarith, hη⟩
  · intro h
    choose A C hA hC hAB hBC hm using fun k : ℕ => h (1 / ((k : ℝ) + 1)) (by positivity)
    set B1 := ⋃ k, A k
    set B2 := ⋂ k, C k
    have hB1 : MeasurableSet B1 := MeasurableSet.iUnion fun k => (hA k).measurableSet
    have h12 : B1 ⊆ B := iUnion_subset hAB
    have h2 : B ⊆ B2 := subset_iInter hBC
    have hbound : ∀ k : ℕ, ν.loeb (B2 \ B1) ≤ ENNReal.ofReal (1 / ((k : ℝ) + 1)) := by
      intro k
      have hsub : B2 \ B1 ⊆ C k \ A k := fun x hx =>
        ⟨Set.mem_iInter.1 hx.1 k, fun h => hx.2 (Set.mem_iUnion.2 ⟨k, h⟩)⟩
      calc ν.loeb (B2 \ B1) ≤ ν.loeb (C k \ A k) := measure_mono hsub
        _ = stE (ν.mass (C k \ A k)) := ν.loeb_internal ((hC k).diff (hA k))
        _ ≤ _ := stE_le_of_le (ν.mass_nonneg _) (hm k).le
    have hnull : ν.loeb (B2 \ B1) = 0 := by
      refine le_antisymm ?_ bot_le
      have ht : Tendsto (fun k : ℕ => ENNReal.ofReal (1 / ((k : ℝ) + 1))) atTop (𝓝 0) := by
        rw [← ENNReal.ofReal_zero]
        exact ENNReal.tendsto_ofReal tendsto_one_div_add_atTop_nhds_zero_nat
      exact ge_of_tendsto' ht hbound
    have hle : ν.loeb B ≤ ν.loeb B1 := by
      calc ν.loeb B ≤ ν.loeb B2 := measure_mono h2
        _ ≤ ν.loeb (B1 ∪ (B2 \ B1)) := measure_mono (fun x hx => by
            by_cases h : x ∈ B1
            · exact Or.inl h
            · exact Or.inr ⟨hx, h⟩)
        _ ≤ ν.loeb B1 + ν.loeb (B2 \ B1) := measure_union_le _ _
        _ = ν.loeb B1 := by rw [hnull, add_zero]
    have hae : B1 =ᵐ[ν.loeb] B :=
      ae_eq_of_subset_of_measure_ge h12 hle hB1.nullMeasurableSet (measure_ne_top _ _)
    exact hB1.nullMeasurableSet.congr hae

/-- **Outer formula**: `L(B) = inf {st ν(C) : C ⊇ B internal}` for Loeb-measurable `B`. -/
theorem loeb_eq_iInf (hfin : IsFinite (ν.mass univ)) {B : Set (Ult α)}
    (hB : NullMeasurableSet B ν.loeb) :
    ν.loeb B = ⨅ (C : Set (Ult α)) (_ : IsInternal C) (_ : B ⊆ C), stE (ν.mass C) := by
  refine le_antisymm (le_iInf₂ fun C hC => le_iInf fun hBC => ?_) ?_
  · rw [← ν.loeb_internal hC]; exact measure_mono hBC
  · refine ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_
    obtain ⟨A, C, hA, hC, hAB, hBC, hm⟩ :=
      (ν.nullMeasurableSet_iff_approx hfin B).1 hB ε (by exact_mod_cast hε)
    calc (⨅ (C : Set (Ult α)) (_ : IsInternal C) (_ : B ⊆ C), stE (ν.mass C))
        ≤ stE (ν.mass C) := iInf₂_le_of_le C hC (iInf_le _ hBC)
      _ = ν.loeb C := (ν.loeb_internal hC).symm
      _ ≤ ν.loeb (B ∪ (C \ A)) := measure_mono (fun x hx => by
          by_cases h : x ∈ A
          · exact Or.inl (hAB h)
          · exact Or.inr ⟨hx, h⟩)
      _ ≤ ν.loeb B + ν.loeb (C \ A) := measure_union_le _ _
      _ ≤ ν.loeb B + ε := by
          refine add_le_add le_rfl ?_
          rw [ν.loeb_internal (hC.diff hA), ← ENNReal.ofReal_coe_nnreal]
          exact stE_le_of_le (ν.mass_nonneg _) hm.le

/-- **Inner formula**: `L(B) = sup {st ν(A) : A ⊆ B internal}` for Loeb-measurable `B`. -/
theorem loeb_eq_iSup (hfin : IsFinite (ν.mass univ)) {B : Set (Ult α)}
    (hB : NullMeasurableSet B ν.loeb) :
    ν.loeb B = ⨆ (A : Set (Ult α)) (_ : IsInternal A) (_ : A ⊆ B), stE (ν.mass A) := by
  refine le_antisymm ?_ (iSup₂_le fun A hA => iSup_le fun hAB => ?_)
  · refine ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_
    obtain ⟨A, C, hA, hC, hAB, hBC, hm⟩ :=
      (ν.nullMeasurableSet_iff_approx hfin B).1 hB ε (by exact_mod_cast hε)
    calc ν.loeb B ≤ ν.loeb (A ∪ (C \ A)) := measure_mono (fun x hx => by
          by_cases h : x ∈ A
          · exact Or.inl h
          · exact Or.inr ⟨hBC hx, h⟩)
      _ ≤ ν.loeb A + ν.loeb (C \ A) := measure_union_le _ _
      _ ≤ (⨆ (A : Set (Ult α)) (_ : IsInternal A) (_ : A ⊆ B), stE (ν.mass A)) + ε := by
          refine add_le_add ?_ ?_
          · rw [ν.loeb_internal hA]; exact le_iSup₂_of_le A hA (le_iSup_of_le hAB le_rfl)
          · rw [ν.loeb_internal (hC.diff hA), ← ENNReal.ofReal_coe_nnreal]
            exact stE_le_of_le (ν.mass_nonneg _) hm.le
  · rw [← ν.loeb_internal hA]; exact measure_mono hAB

end HypMeasure

/-! ## The standard-part map and preimages of standard sets -/

section Shadow

variable {X : Type*} [MetricSpace X]

theorem starSet_mono {S T : Set α} (h : S ⊆ T) : starSet S ⊆ starSet T := by
  intro x hx
  obtain ⟨u, rfl⟩ := exists_rep x
  rw [mem_starSet] at hx ⊢
  exact hx.mono fun n hn => h hn

theorem measurableSet_starSet (S : Set α) : MeasurableSet (starSet S) :=
  (isInternal_starSet S).measurableSet

/-- `st⁻¹(E)`: the points of `Ult X` infinitely close to a standard point of `E` (the
near-standard points whose standard part lies in `E`). -/
def stInv (E : Set X) : Set (Ult X) := {x | ∃ y ∈ E, Near x (Germ.const y)}

theorem near_const_unique {x : Ult X} {y y' : X} (h : Near x (Germ.const y))
    (h' : Near x (Germ.const y')) : y = y' :=
  near_const_const (h.symm.trans h')

theorem stInv_empty : stInv (∅ : Set X) = ∅ := by
  ext x; simp [stInv]

theorem stInv_mono {E F : Set X} (h : E ⊆ F) : stInv E ⊆ stInv F :=
  fun _ ⟨y, hy, hxy⟩ => ⟨y, h hy, hxy⟩

theorem stInv_iUnion {ι : Sort*} (E : ι → Set X) : stInv (⋃ i, E i) = ⋃ i, stInv (E i) := by
  ext x; simp only [stInv, Set.mem_iUnion, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨y, ⟨i, hi⟩, h⟩; exact ⟨i, y, hi, h⟩
  · rintro ⟨i, y, hi, h⟩; exact ⟨y, ⟨i, hi⟩, h⟩

theorem stInv_iUnion_two (E F : Set X) : stInv (E ∪ F) = stInv E ∪ stInv F := by
  ext x; simp only [stInv, Set.mem_union, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨y, hy | hy, h⟩
    · exact Or.inl ⟨y, hy, h⟩
    · exact Or.inr ⟨y, hy, h⟩
  · rintro (⟨y, hy, h⟩ | ⟨y, hy, h⟩)
    · exact ⟨y, Or.inl hy, h⟩
    · exact ⟨y, Or.inr hy, h⟩

/-- `st⁻¹` commutes with differences (standard parts are unique). -/
theorem stInv_diff (E F : Set X) : stInv (E \ F) = stInv E \ stInv F := by
  ext x; constructor
  · rintro ⟨y, ⟨hyE, hyF⟩, h⟩
    refine ⟨⟨y, hyE, h⟩, ?_⟩
    rintro ⟨y', hy', h'⟩
    exact hyF (near_const_unique h h' ▸ hy')
  · rintro ⟨⟨y, hy, h⟩, hn⟩
    exact ⟨y, ⟨hy, fun hyF => hn ⟨y, hyF, h⟩⟩, h⟩

theorem disjoint_stInv {E F : Set X} (h : Disjoint E F) : Disjoint (stInv E) (stInv F) := by
  rw [Set.disjoint_left]
  rintro x ⟨y, hy, h1⟩ ⟨y', hy', h2⟩
  exact Set.disjoint_left.1 h hy (near_const_unique h1 h2 ▸ hy')

/-- `st⁻¹(K)` as a countable intersection of internal sets `*F m`, for closed `F m`
shrinking to `K` with `F 0` bounded and every point of `K` interior to every `F m`. -/
theorem stInv_eq_iInter [ProperSpace X] {K : Set X} {F : ℕ → Set X} (hF : ∀ m, IsClosed (F m))
    (hb : Bornology.IsBounded (F 0)) (hball : ∀ m, ∀ y ∈ K, ∃ r > 0, Metric.ball y r ⊆ F m)
    (hK : ⋂ m, F m ⊆ K) : stInv K = ⋂ m, starSet (F m) := by
  ext x
  obtain ⟨u, rfl⟩ := exists_rep x
  simp only [Set.mem_iInter]
  constructor
  · rintro ⟨y, hy, hnear⟩ m
    obtain ⟨r, hr, hsub⟩ := hball m y hy
    rw [near_const_iff_tendsto] at hnear
    rw [mem_starSet]
    filter_upwards [hnear (Metric.ball_mem_nhds y hr)] with n hn using hsub hn
  · intro h
    obtain ⟨R, hR⟩ := (Metric.isBounded_iff_subset_closedBall (u 0)).1 hb
    have hfin : IsFinite (hdist (u : Ult X) (Germ.const (u 0))) := by
      rw [show (Germ.const (u 0) : Ult X) = ((fun _ => u 0 : ℕ → X) : Ult X) from rfl, hdist_coe,
        isFinite_ofSeq_iff]
      refine ⟨R, ?_⟩
      filter_upwards [(mem_starSet _ u).1 (h 0)] with n hn
      rw [abs_of_nonneg dist_nonneg]; exact hR hn
    obtain ⟨b, hb⟩ := exists_near_of_isFinite (u : Ult X) (u 0) hfin
    refine ⟨b, hK (Set.mem_iInter.2 fun m => ?_), hb⟩
    exact (hF m).mem_of_tendsto ((near_const_iff_tendsto u b).1 hb) ((mem_starSet _ u).1 (h m))

/-- For compact `K`, `st⁻¹(K) = ⋂ₘ *(K_{1/(m+1)})` (closed thickenings). -/
theorem stInv_isCompact [ProperSpace X] {K : Set X} (hK : IsCompact K) :
    stInv K = ⋂ m : ℕ, starSet (Metric.cthickening (1 / ((m : ℝ) + 1)) K) := by
  refine stInv_eq_iInter (fun m => Metric.isClosed_cthickening) hK.isBounded.cthickening
    (fun m y hy => ⟨1 / ((m : ℝ) + 1), by positivity,
      (Metric.ball_subset_thickening hy _).trans (Metric.thickening_subset_cthickening _ _)⟩) ?_
  intro z hz
  rw [← hK.isClosed.closure_eq, Metric.closure_eq_iInter_cthickening]
  simp only [Set.mem_iInter]
  intro δ hδ
  obtain ⟨m, hm⟩ := exists_nat_one_div_lt hδ
  exact Metric.cthickening_mono hm.le K (Set.mem_iInter.1 hz m)

theorem measurableSet_stInv_of_isCompact [ProperSpace X] {K : Set X} (hK : IsCompact K) :
    MeasurableSet (stInv K) := by
  rw [stInv_isCompact hK]; exact MeasurableSet.iInter fun m => measurableSet_starSet _

theorem measurableSet_stInv_of_isClosed [ProperSpace X] {F : Set X} (hF : IsClosed F) :
    MeasurableSet (stInv F) := by
  rcases isEmpty_or_nonempty X with hX | ⟨⟨x0⟩⟩
  · have : stInv F = ∅ := by
      ext x; obtain ⟨u, rfl⟩ := exists_rep x; exact (hX.false (u 0)).elim
    rw [this]; exact MeasurableSet.empty
  · have : F = ⋃ R : ℕ, F ∩ Metric.closedBall x0 R := by
      ext y; simp only [Set.mem_iUnion, Set.mem_inter_iff, Metric.mem_closedBall]
      constructor
      · intro hy; obtain ⟨R, hR⟩ := exists_nat_ge (dist y x0); exact ⟨R, hy, hR⟩
      · rintro ⟨R, hy, -⟩; exact hy
    rw [this, stInv_iUnion]
    exact MeasurableSet.iUnion fun R =>
      measurableSet_stInv_of_isCompact ((isCompact_closedBall x0 R).inter_left hF)

set_option warn.classDefReducibility false in
/-- The σ-algebra of sets `E ⊆ X` with `st⁻¹(E) ∈ σ(𝒜)` (used to prove that it contains the
Borel sets). -/
def stInvMeasurableSpace [ProperSpace X] : MeasurableSpace X where
  MeasurableSet' := fun E => MeasurableSet (stInv E)
  measurableSet_empty := by
    show MeasurableSet (stInv ∅); rw [stInv_empty]; exact MeasurableSet.empty
  measurableSet_compl := fun E h => by
    show MeasurableSet (stInv Eᶜ)
    rw [Set.compl_eq_univ_sdiff, stInv_diff]
    exact (measurableSet_stInv_of_isClosed isClosed_univ).diff h
  measurableSet_iUnion := fun f h => by
    show MeasurableSet (stInv (⋃ i, f i))
    rw [stInv_iUnion]; exact MeasurableSet.iUnion h

/-- **`st⁻¹` maps Borel sets to Loeb-measurable sets**: `st⁻¹(E) ∈ σ(𝒜)` for every Borel
`E` (in a proper metric space). -/
theorem measurableSet_stInv [ProperSpace X] [MeasurableSpace X] [BorelSpace X] {E : Set X}
    (hE : MeasurableSet E) : MeasurableSet (stInv E) := by
  have hle : borel X ≤ stInvMeasurableSpace := by
    rw [borel_eq_generateFrom_isClosed]
    exact MeasurableSpace.generateFrom_le fun F hF => measurableSet_stInv_of_isClosed hF
  have hE' : MeasurableSet[borel X] E := by
    rw [← BorelSpace.measurable_eq (α := X)]; exact hE
  exact hle _ hE'

/-- The **push-forward under the standard part**: `E ↦ μ(st⁻¹ E)` on Borel sets. -/
def stMeasure [ProperSpace X] [MeasurableSpace X] [BorelSpace X] (μ : Measure (Ult X)) :
    Measure X :=
  Measure.ofMeasurable (fun E _ => μ (stInv E)) (by simp only [stInv_empty, measure_empty])
    (fun f hf hd => by
      rw [stInv_iUnion]
      exact measure_iUnion (fun i j hij => disjoint_stInv (hd hij))
        (fun i => measurableSet_stInv (hf i)))

theorem stMeasure_apply [ProperSpace X] [MeasurableSpace X] [BorelSpace X]
    (μ : Measure (Ult X)) {E : Set X} (hE : MeasurableSet E) : stMeasure μ E = μ (stInv E) :=
  Measure.ofMeasurable_apply _ hE

/-- If `E` is measurable for the completion of `stMeasure μ`, then `st⁻¹(E)` is measurable for
the completion of `μ`, with the same measure. -/
theorem nullMeasurableSet_stInv [ProperSpace X] [MeasurableSpace X] [BorelSpace X]
    (μ : Measure (Ult X)) {E : Set X} (hE : NullMeasurableSet E (stMeasure μ)) :
    NullMeasurableSet (stInv E) μ ∧ μ (stInv E) = stMeasure μ E := by
  obtain ⟨F, hFE, hF, hae⟩ := hE.exists_measurable_subset_ae_eq
  set G := toMeasurable (stMeasure μ) E
  have hEG : E ⊆ G := subset_toMeasurable _ _
  have hG : MeasurableSet G := measurableSet_toMeasurable _ _
  have hGF : stMeasure μ (G \ F) = 0 := (ae_eq_set.1 (hE.toMeasurable_ae_eq.trans hae.symm)).1
  have h0 : μ (stInv E \ stInv F) = 0 := by
    refine measure_mono_null (Set.sdiff_subset_sdiff_left (stInv_mono hEG)) ?_
    rw [← stInv_diff, ← stMeasure_apply μ (hG.diff hF)]; exact hGF
  have hae' : stInv F =ᵐ[μ] stInv E := by
    rw [ae_eq_set]; refine ⟨?_, h0⟩
    rw [Set.sdiff_eq_empty.2 (stInv_mono hFE), measure_empty]
  refine ⟨(measurableSet_stInv hF).nullMeasurableSet.congr hae', ?_⟩
  rw [← measure_congr hae', ← stMeasure_apply μ hF, measure_congr hae]

/-- Continuity from above for `μ(st⁻¹ K)`. -/
theorem measure_stInv_eq_of_iInter [ProperSpace X] [MeasurableSpace X] [BorelSpace X]
    (μ : Measure (Ult X)) (lam : Measure X) {K : Set X} {F : ℕ → Set X}
    (hF : ∀ m, IsClosed (F m)) (hb : Bornology.IsBounded (F 0))
    (hball : ∀ m, ∀ y ∈ K, ∃ r > 0, Metric.ball y r ⊆ F m) (hK : ⋂ m, F m = K)
    (hanti : Antitone F) (hfin : lam (F 0) ≠ ∞) (h : ∀ m, μ (starSet (F m)) = lam (F m)) :
    μ (stInv K) = lam K := by
  rw [stInv_eq_iInter hF hb hball hK.le]
  have hanti' : Antitone fun m => starSet (F m) := fun i j hij => starSet_mono (hanti hij)
  rw [hanti'.measure_iInter (fun m => (measurableSet_starSet _).nullMeasurableSet)
    ⟨0, by rw [h 0]; exact hfin⟩, ← hK,
    hanti.measure_iInter (fun m => (hF m).measurableSet.nullMeasurableSet) ⟨0, hfin⟩]
  simp_rw [h]

theorem one_div_succ_pos (m : ℕ) : (0 : ℝ) < 1 / ((m : ℝ) + 1) := by positivity

theorem one_div_succ_anti : Antitone fun m : ℕ => (1 : ℝ) / ((m : ℝ) + 1) := by
  intro i j hij
  exact one_div_le_one_div_of_le (by positivity) (by exact_mod_cast Nat.add_le_add_right hij 1)

/-- **Shadow criterion on the line.** If `μ(*[a,b]) = λ[a,b]` for all standard `a ≤ b`, for a
locally finite `λ`, then the push-forward of `μ` under `st` is `λ`. -/
theorem stMeasure_eq_of_Icc (μ : Measure (Ult ℝ)) (lam : Measure ℝ) [IsLocallyFiniteMeasure lam]
    (h : ∀ a b : ℝ, a ≤ b → μ (starSet (Icc a b)) = lam (Icc a b)) : stMeasure μ = lam := by
  have hbox : ∀ a b : ℝ, a ≤ b → stMeasure μ (Icc a b) = lam (Icc a b) := by
    intro a b hab
    rw [stMeasure_apply μ measurableSet_Icc]
    refine measure_stInv_eq_of_iInter μ lam
      (F := fun m => Icc (a - 1 / ((m : ℝ) + 1)) (b + 1 / ((m : ℝ) + 1)))
      (fun m => isClosed_Icc) (Metric.isBounded_Icc _ _) ?_ ?_ ?_ measure_Icc_lt_top.ne
      (fun m => h _ _ (by linarith [one_div_succ_pos m]))
    · intro m y hy
      refine ⟨1 / ((m : ℝ) + 1), one_div_succ_pos m, fun z hz => ?_⟩
      rw [Metric.mem_ball, Real.dist_eq, abs_lt] at hz
      exact ⟨by linarith [hy.1], by linarith [hy.2]⟩
    · ext z; simp only [Set.mem_iInter, Set.mem_Icc]
      constructor
      · intro hz
        constructor
        · by_contra hc; push Not at hc
          obtain ⟨m, hm⟩ := exists_nat_one_div_lt (sub_pos.2 hc)
          linarith [(hz m).1]
        · by_contra hc; push Not at hc
          obtain ⟨m, hm⟩ := exists_nat_one_div_lt (sub_pos.2 hc)
          linarith [(hz m).2]
      · intro hz m; constructor <;> linarith [hz.1, hz.2, one_div_succ_pos m]
    · intro i j hij z hz
      have := one_div_succ_anti hij
      exact ⟨by linarith [hz.1], by linarith [hz.2]⟩
  exact (Measure.ext_of_Icc lam (stMeasure μ) (fun a b hab => (hbox a b hab).symm)).symm

/-- **Shadow criterion in `ℝⁿ`.** If `μ(*Q) = vol(Q)` for every standard closed box `Q`,
then the push-forward of `μ` under `st` is Lebesgue measure. -/
theorem stMeasure_eq_volume_pi {d : ℕ} (μ : Measure (Ult (Fin d → ℝ)))
    (h : ∀ a b : Fin d → ℝ, a ≤ b → μ (starSet (Icc a b)) = volume (Icc a b)) :
    stMeasure μ = volume := by
  have hbox : ∀ a b : Fin d → ℝ, a ≤ b → stMeasure μ (Icc a b) = volume (Icc a b) := by
    intro a b hab
    rw [stMeasure_apply μ measurableSet_Icc]
    let c : ℕ → Fin d → ℝ := fun m _ => 1 / ((m : ℝ) + 1)
    refine measure_stInv_eq_of_iInter μ volume (F := fun m => Icc (a - c m) (b + c m))
      (fun m => isClosed_Icc) (Metric.isBounded_Icc _ _) ?_ ?_ ?_ measure_Icc_lt_top.ne
      (fun m => h _ _ (fun i => by
        have hi : a i ≤ b i := hab i
        have := one_div_succ_pos m
        simp only [c, Pi.sub_apply, Pi.add_apply]
        linarith))
    · intro m y hy
      refine ⟨1 / ((m : ℝ) + 1), one_div_succ_pos m, fun z hz => ?_⟩
      rw [Metric.mem_ball] at hz
      have hzi : ∀ i, |z i - y i| < 1 / ((m : ℝ) + 1) := fun i => by
        have := (dist_le_pi_dist z y i).trans_lt hz; rwa [Real.dist_eq] at this
      refine ⟨fun i => ?_, fun i => ?_⟩
      · have := abs_lt.1 (hzi i)
        simp only [c, Pi.sub_apply]; linarith [hy.1 i]
      · have := abs_lt.1 (hzi i)
        simp only [c, Pi.add_apply]; linarith [hy.2 i]
    · ext z; simp only [Set.mem_iInter, Set.mem_Icc]
      constructor
      · intro hz
        refine ⟨fun i => ?_, fun i => ?_⟩
        · by_contra hc; push Not at hc
          obtain ⟨m, hm⟩ := exists_nat_one_div_lt (sub_pos.2 hc)
          have := (hz m).1 i; simp only [c, Pi.sub_apply] at this; linarith
        · by_contra hc; push Not at hc
          obtain ⟨m, hm⟩ := exists_nat_one_div_lt (sub_pos.2 hc)
          have := (hz m).2 i; simp only [c, Pi.add_apply] at this; linarith
      · intro hz m
        refine ⟨fun i => ?_, fun i => ?_⟩
        · simp only [c, Pi.sub_apply]; linarith [hz.1 i, one_div_succ_pos m]
        · simp only [c, Pi.add_apply]; linarith [hz.2 i, one_div_succ_pos m]
    · intro i j hij z hz
      have := one_div_succ_anti hij
      refine ⟨fun k => ?_, fun k => ?_⟩
      · have h1 := hz.1 k; simp only [c, Pi.sub_apply] at h1 ⊢; linarith
      · have h1 := hz.2 k; simp only [c, Pi.add_apply] at h1 ⊢; linarith
  rw [volume_pi]
  symm
  refine Measure.pi_eq_generateFrom (C := fun _ => {S : Set ℝ | ∃ l u, l ≤ u ∧ Icc l u = S})
    (fun i => (borel_eq_generateFrom_Icc ℝ).symm.trans BorelSpace.measurable_eq.symm)
    (fun i => by simpa using isPiSystem_Icc (id : ℝ → ℝ) id) (fun i => ?_) ?_
  · exact
      { set := fun n => Icc (-(n : ℝ)) n
        set_mem := fun n => ⟨-(n : ℝ), n, by linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)], rfl⟩
        finite := fun n => measure_Icc_lt_top
        spanning := by
          ext x; simp only [Set.mem_iUnion, Set.mem_Icc, Set.mem_univ, iff_true]
          obtain ⟨n, hn⟩ := exists_nat_ge |x|
          exact ⟨n, by linarith [neg_abs_le x], by linarith [le_abs_self x]⟩ }
  · intro s hs
    choose l u hlu hs' using hs
    have hpi : Set.pi univ s = Icc l u := by
      rw [← Set.pi_univ_Icc]; congr; funext i; exact (hs' i).symm
    rw [hpi, hbox l u hlu, Real.volume_Icc_pi]
    congr 1; funext i; rw [← hs' i, Real.volume_Icc]

end Shadow

/-! ## Lattice counting -/

section Counting

theorem filter_Icc_eq_Icc {t : ℝ} (ht : 0 < t) (p q : ℤ) (a b : ℝ) :
    (Finset.Icc p q).filter (fun k : ℤ => a ≤ t * k ∧ t * k ≤ b) =
      Finset.Icc (max p ⌈a / t⌉) (min q ⌊b / t⌋) := by
  ext k
  simp only [Finset.mem_filter, Finset.mem_Icc, max_le_iff, le_min_iff, Int.ceil_le,
    Int.le_floor]
  rw [div_le_iff₀ ht, le_div_iff₀ ht, mul_comm (k : ℝ) t]
  tauto

/-- The number `c` of integers `k ∈ [p, q]` with `t k ∈ [a, b]` satisfies
`|t c - max (min (t q) b - max (t p) a) 0| ≤ t`. -/
theorem card_filter_Icc_bound {t : ℝ} (ht : 0 < t) (p q : ℤ) (a b : ℝ) :
    |t * (((Finset.Icc p q).filter (fun k : ℤ => a ≤ t * k ∧ t * k ≤ b)).card : ℝ) -
      max (min (t * q) b - max (t * p) a) 0| ≤ t := by
  rw [filter_Icc_eq_Icc ht, Int.card_Icc]
  set P := max p ⌈a / t⌉ with hPdef
  set Q := min q ⌊b / t⌋ with hQdef
  have hcast : (((Q + 1 - P).toNat : ℕ) : ℝ) = max ((Q : ℝ) + 1 - P) 0 := by
    have h1 : (((Q + 1 - P).toNat : ℤ) : ℝ) = ((max (Q + 1 - P) 0 : ℤ) : ℝ) := by
      rw [Int.toNat_eq_max]
    push_cast at h1; exact_mod_cast h1
  rw [hcast, mul_max_of_nonneg _ _ ht.le, mul_zero]
  refine (abs_max_sub_max_le_abs _ _ _).trans ?_
  have hPc : (P : ℝ) = max (p : ℝ) (⌈a / t⌉ : ℝ) := by rw [hPdef]; push_cast; rfl
  have hQc : (Q : ℝ) = min (q : ℝ) (⌊b / t⌋ : ℝ) := by rw [hQdef]; push_cast; rfl
  have hc1 : a ≤ t * ⌈a / t⌉ := by
    have := Int.le_ceil (a / t); rw [div_le_iff₀ ht] at this; linarith [mul_comm t (⌈a / t⌉ : ℝ)]
  have hc2 : t * ⌈a / t⌉ < a + t := by
    have h := mul_lt_mul_of_pos_left (Int.ceil_lt_add_one (a / t)) ht
    rw [mul_add, mul_div_cancel₀ _ ht.ne', mul_one] at h; exact h
  have hf1 : t * ⌊b / t⌋ ≤ b := by
    have h := mul_le_mul_of_nonneg_left (Int.floor_le (b / t)) ht.le
    rwa [mul_div_cancel₀ _ ht.ne'] at h
  have hf2 : b - t < t * ⌊b / t⌋ := by
    have h := mul_lt_mul_of_pos_left (Int.lt_floor_add_one (b / t)) ht
    rw [mul_add, mul_div_cancel₀ _ ht.ne', mul_one] at h; linarith
  have hP1 : max (t * p) a ≤ t * P := by
    rw [hPc, mul_max_of_nonneg _ _ ht.le]; exact max_le_max le_rfl hc1
  have hP2 : t * P < max (t * p) a + t := by
    rw [hPc, mul_max_of_nonneg _ _ ht.le]
    exact max_lt (by linarith [le_max_left (t * p) a]) (by linarith [le_max_right (t * p) a])
  have hQ1 : t * Q ≤ min (t * q) b := by
    rw [hQc, mul_min_of_nonneg _ _ ht.le]; exact min_le_min le_rfl hf1
  have hQ2 : min (t * q) b - t < t * Q := by
    rw [hQc, mul_min_of_nonneg _ _ ht.le]
    exact lt_min (by linarith [min_le_left (t * q) b]) (by linarith [min_le_right (t * q) b])
  have e1 : t * ((Q : ℝ) + 1 - P) = t * Q + t - t * P := by ring
  rw [e1, abs_le]
  constructor <;> linarith

theorem card_filter_image_mul {t : ℝ} (ht : t ≠ 0) (I : Finset ℤ) (a b : ℝ)
    {inst : DecidablePred (· ∈ Icc a b)} :
    (@Finset.filter _ (· ∈ Icc a b) inst (I.image (fun k : ℤ => t * k))).card =
      (I.filter (fun k : ℤ => a ≤ t * k ∧ t * k ≤ b)).card := by
  rw [Finset.filter_image, Finset.card_image_of_injective]
  · congr 1; ext k; simp [Set.mem_Icc]
  · intro k₁ k₂ h
    exact_mod_cast mul_left_cancel₀ ht h

theorem card_filter_image_pi {d : ℕ} {t : ℝ} (ht : t ≠ 0) (I : Finset ℤ) (a b : Fin d → ℝ)
    {inst : DecidablePred (· ∈ Icc a b)} :
    (@Finset.filter _ (· ∈ Icc a b) inst
      ((Fintype.piFinset fun _ : Fin d => I).image (fun k i => t * (k i : ℝ)))).card =
      ∏ i, (I.filter (fun k : ℤ => a i ≤ t * k ∧ t * k ≤ b i)).card := by
  rw [Finset.filter_image, Finset.card_image_of_injective]
  · have : ∀ inst : DecidablePred (fun k : Fin d → ℤ => (fun i => t * (k i : ℝ)) ∈ Icc a b),
        @Finset.filter _ _ inst (Fintype.piFinset fun _ : Fin d => I) =
          Fintype.piFinset fun i => I.filter (fun k : ℤ => a i ≤ t * k ∧ t * k ≤ b i) := by
      intro inst
      ext k
      simp only [Finset.mem_filter, Fintype.mem_piFinset, Set.mem_Icc, Pi.le_def]
      constructor
      · rintro ⟨h1, h2, h3⟩ i; exact ⟨h1 i, h2 i, h3 i⟩
      · intro h; exact ⟨fun i => (h i).1, fun i => (h i).2.1, fun i => (h i).2.2⟩
    rw [this, Fintype.card_piFinset]
  · intro k₁ k₂ h
    funext i
    have := congrFun h i
    exact_mod_cast mul_left_cancel₀ ht this

theorem tendsto_of_abs_sub_le {f g : ℕ → ℝ} {L : ℝ}
    (hg : Tendsto g (hyperfilter ℕ : Filter ℕ) (𝓝 0))
    (h : ∀ᶠ n in (hyperfilter ℕ : Filter ℕ), |f n - L| ≤ g n) :
    Tendsto f (hyperfilter ℕ : Filter ℕ) (𝓝 L) := by
  rw [Metric.tendsto_nhds] at hg ⊢
  intro r hr
  filter_upwards [hg r hr, h] with n h1 h2
  rw [Real.dist_eq, sub_zero] at h1
  rw [Real.dist_eq]
  exact lt_of_le_of_lt h2 (lt_of_le_of_lt (le_abs_self _) h1)

theorem tendsto_of_isInfinitesimal {e : ℕ → ℝ} (h : IsInfinitesimal (Hyperreal.ofSeq e)) :
    Tendsto e (hyperfilter ℕ : Filter ℕ) (𝓝 0) := by
  rw [Metric.tendsto_nhds]; intro r hr
  filter_upwards [(isInfinitesimal_ofSeq_iff e).1 h r hr] with n hn
  rwa [Real.dist_eq, sub_zero]

end Counting

/-! ## Anderson's theorem: the granular lattice measure -/

section Anderson

variable {d : ℕ}

/-- The **granular lattice measure** `μ_ε` on `𝕃ⁿ ∩ [-Ω, Ω]ⁿ`, `𝕃 = 2ε ℤ*`, `Ω = 2εM`:
the hyperfinite set `[{2 e n k : k ∈ ℤⁿ, |kᵢ| ≤ M n}]` with weight `(2ε)ⁿ` per point. -/
def latMeasure (d : ℕ) (e : ℕ → ℝ) (M : ℕ → ℕ) : HypMeasure (Fin d → ℝ) where
  supp n := (Fintype.piFinset fun _ : Fin d => Finset.Icc (-(M n : ℤ)) (M n)).image
    (fun k i => 2 * e n * (k i : ℝ))
  weight n _ := |2 * e n| ^ d
  weight_nonneg n _ := by positivity

theorem latMeasure_seqMass_Icc (e : ℕ → ℝ) (M : ℕ → ℕ) (a b : Fin d → ℝ) (n : ℕ)
    (hen : e n ≠ 0) :
    (latMeasure d e M).seqMass (fun _ => Icc a b) n = ∏ i, (|2 * e n| *
      ((Finset.Icc (-(M n : ℤ)) (M n)).filter
        (fun k : ℤ => a i ≤ 2 * e n * k ∧ 2 * e n * k ≤ b i)).card) := by
  unfold HypMeasure.seqMass
  simp only [latMeasure]
  rw [Finset.sum_const, nsmul_eq_mul, card_filter_image_pi (by positivity) _ a b,
    Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  push_cast; ring

/-- **Boxes.** For a standard closed box `Q`, `L(*Q) = st μ_ε(*Q ∩ 𝕃ⁿ) = vol(Q)`. -/
theorem latMeasure_loeb_box {e : ℕ → ℝ} {M : ℕ → ℕ} (he : 0 < Hyperreal.ofSeq e)
    (hε : IsInfinitesimal (Hyperreal.ofSeq e))
    (hΩ : ∀ r : ℝ, (r : ℝ*) < 2 * Hyperreal.ofSeq e * Hyperreal.ofSeq (fun n => (M n : ℝ)))
    (a b : Fin d → ℝ) (hab : a ≤ b) :
    (latMeasure d e M).loeb (starSet (Icc a b)) = volume (Icc a b) := by
  have hab' : ∀ i, a i ≤ b i := hab
  rw [HypMeasure.loeb_internal _ (isInternal_starSet _), starSet, HypMeasure.mass_internal,
    Real.volume_Icc_pi, ← ENNReal.ofReal_prod_of_nonneg (fun i _ => sub_nonneg.2 (hab' i))]
  apply stE_ofSeq_of_tendsto
  set R : ℝ := ∑ i, (|a i| + |b i|)
  have hpos : ∀ᶠ n in (hyperfilter ℕ : Filter ℕ), 0 < e n := Hyperreal.ofSeq_lt_ofSeq.1 he
  have hbig : ∀ᶠ n in (hyperfilter ℕ : Filter ℕ), R < 2 * e n * M n :=
    Hyperreal.ofSeq_lt_ofSeq.1 (hΩ R)
  have he0 := tendsto_of_isInfinitesimal hε
  refine Tendsto.congr' (f₁ := fun n => ∏ i, (|2 * e n| *
      ((Finset.Icc (-(M n : ℤ)) (M n)).filter
        (fun k : ℤ => a i ≤ 2 * e n * k ∧ 2 * e n * k ≤ b i)).card)) ?_ ?_
  · filter_upwards [hpos] with n hn
    exact (latMeasure_seqMass_Icc e M a b n hn.ne').symm
  · refine tendsto_finsetProd _ (fun i _ => ?_)
    refine tendsto_of_abs_sub_le (g := fun n => 2 * e n) (by simpa using he0.const_mul 2) ?_
    filter_upwards [hpos, hbig] with n hn hR
    have h := card_filter_Icc_bound (t := 2 * e n) (by positivity) (-(M n : ℤ)) (M n) (a i) (b i)
    have hai : |a i| + |b i| ≤ R :=
      Finset.single_le_sum (f := fun i => |a i| + |b i|)
        (fun j _ => by positivity) (Finset.mem_univ i)
    have h1 : min (2 * e n * ((M n : ℤ) : ℝ)) (b i) = b i := by
      push_cast
      exact min_eq_right (by linarith [le_abs_self (b i), abs_nonneg (a i)])
    have h2 : max (2 * e n * ((-(M n : ℤ) : ℤ) : ℝ)) (a i) = a i := by
      push_cast
      exact max_eq_right (by linarith [neg_abs_le (a i), abs_nonneg (b i)])
    rw [h1, h2, max_eq_left (sub_nonneg.2 (hab' i))] at h
    rw [abs_of_pos (by positivity : 0 < 2 * e n)]
    exact h

/-- **Anderson's theorem, push-forward form**: the standard part map pushes the Loeb
measure of the granular measure `μ_ε` forward to Lebesgue measure on `ℝⁿ`. -/
theorem anderson_pushforward {e : ℕ → ℝ} {M : ℕ → ℕ} (he : 0 < Hyperreal.ofSeq e)
    (hε : IsInfinitesimal (Hyperreal.ofSeq e))
    (hΩ : ∀ r : ℝ, (r : ℝ*) < 2 * Hyperreal.ofSeq e * Hyperreal.ofSeq (fun n => (M n : ℝ))) :
    stMeasure (latMeasure d e M).loeb = volume :=
  stMeasure_eq_volume_pi _ (fun a b hab => latMeasure_loeb_box he hε hΩ a b hab)

/-- **Anderson's theorem (Loeb–Anderson representation).** Let `𝕃 = 2εℤ* ∩ [-Ω, Ω]` with
`ε > 0` infinitesimal and `Ω = 2εM` infinite, and let `L` be the Loeb measure of the granular
measure on `𝕃ⁿ`.  For every Lebesgue-measurable `E ⊆ ℝⁿ`, `st⁻¹(E) ∩ 𝕃ⁿ` is Loeb measurable
and `L(st⁻¹(E) ∩ 𝕃ⁿ) = λ(E)`. -/
theorem anderson {e : ℕ → ℝ} {M : ℕ → ℕ} (he : 0 < Hyperreal.ofSeq e)
    (hε : IsInfinitesimal (Hyperreal.ofSeq e))
    (hΩ : ∀ r : ℝ, (r : ℝ*) < 2 * Hyperreal.ofSeq e * Hyperreal.ofSeq (fun n => (M n : ℝ)))
    {E : Set (Fin d → ℝ)} (hE : NullMeasurableSet E volume) :
    NullMeasurableSet (stInv E ∩ (latMeasure d e M).carrier) (latMeasure d e M).loeb ∧
      (latMeasure d e M).loeb (stInv E ∩ (latMeasure d e M).carrier) = volume E := by
  have hpush := anderson_pushforward (d := d) he hε hΩ
  rw [← hpush] at hE
  obtain ⟨h1, h2⟩ := nullMeasurableSet_stInv _ hE
  refine ⟨h1.inter (HypMeasure.isInternal_carrier _).measurableSet.nullMeasurableSet, ?_⟩
  rw [HypMeasure.loeb_inter_carrier, h2, hpush]

/-- Anderson's theorem for Borel sets: `st⁻¹(E) ∩ 𝕃ⁿ` is in the σ-algebra `σ(𝒜)`. -/
theorem anderson_borel {e : ℕ → ℝ} {M : ℕ → ℕ} (he : 0 < Hyperreal.ofSeq e)
    (hε : IsInfinitesimal (Hyperreal.ofSeq e))
    (hΩ : ∀ r : ℝ, (r : ℝ*) < 2 * Hyperreal.ofSeq e * Hyperreal.ofSeq (fun n => (M n : ℝ)))
    {E : Set (Fin d → ℝ)} (hE : MeasurableSet E) :
    MeasurableSet (stInv E ∩ (latMeasure d e M).carrier) ∧
      (latMeasure d e M).loeb (stInv E ∩ (latMeasure d e M).carrier) = volume E :=
  ⟨(measurableSet_stInv hE).inter (HypMeasure.isInternal_carrier _).measurableSet,
    (anderson he hε hΩ hE.nullMeasurableSet).2⟩

/-- The support of `μ_ε` is the hyperfinite lattice box `𝕃ⁿ ∩ [-Ω, Ω]ⁿ`, `Ω = 2εM`. -/
theorem latMeasure_carrier {e : ℕ → ℝ} (M : ℕ → ℕ) (he : 0 < Hyperreal.ofSeq e) :
    (latMeasure d e M).carrier = {x | x ∈ latN (Hyperreal.ofSeq e) ∧
      ∀ i, |coordG i x| ≤ 2 * Hyperreal.ofSeq e * Hyperreal.ofSeq (fun n => (M n : ℝ))} := by
  have hpos : ∀ᶠ n in (hyperfilter ℕ : Filter ℕ), 0 < e n := Hyperreal.ofSeq_lt_ofSeq.1 he
  ext x
  obtain ⟨u, rfl⟩ := exists_rep x
  have hcoord : ∀ i, |coordG i (u : Ult (Fin d → ℝ))| ≤
      2 * Hyperreal.ofSeq e * Hyperreal.ofSeq (fun n => (M n : ℝ)) ↔
      ∀ᶠ n in (hyperfilter ℕ : Filter ℕ), |u n i| ≤ 2 * e n * M n := by
    intro i; rw [coordG_coe, abs_ofSeq]; exact Hyperreal.ofSeq_le_ofSeq
  change (u : Ult (Fin d → ℝ)) ∈ internal _ ↔ _ ∧ _
  rw [mem_internal, mem_latN_coe]
  simp_rw [hcoord, ← Filter.eventually_all, ← eventually_and]
  constructor
  · intro h
    filter_upwards [h, hpos] with n hn hen
    obtain ⟨k, hk, hku⟩ := Finset.mem_image.1 hn
    refine ⟨fun i => ⟨k i, (congrFun hku i).symm⟩, fun i => ?_⟩
    rw [← congrFun hku i, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * e n)]
    have hki := Finset.mem_Icc.1 (Fintype.mem_piFinset.1 hk i)
    have : |(k i : ℝ)| ≤ M n := by
      rw [abs_le]; constructor
      · have := hki.1; exact_mod_cast this
      · have := hki.2; exact_mod_cast this
    exact mul_le_mul_of_nonneg_left this (by positivity)
  · intro h
    filter_upwards [h, hpos] with n hn hen
    choose k hk using hn.1
    refine Finset.mem_image.2 ⟨k, Fintype.mem_piFinset.2 fun i => ?_, funext fun i => (hk i).symm⟩
    have h2 := hn.2 i
    rw [hk i, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * e n)] at h2
    have h3 : |(k i : ℝ)| ≤ M n := le_of_mul_le_mul_left h2 (by positivity)
    rw [Finset.mem_Icc]
    constructor
    · have := (abs_le.1 h3).1; exact_mod_cast this
    · have := (abs_le.1 h3).2; exact_mod_cast this

end Anderson

/-! ## The uniform lattice law on `[0,1)` (Lebesgue measure as a Loeb shadow) -/

section Uniform

/-- `[0,1) ∩ 𝕃` for the lattice of spacing `1/N`: the points `k/N`, `0 ≤ k ≤ N - 1`. -/
def unifPoints (N : ℕ → ℕ) (n : ℕ) : Finset ℝ :=
  (Finset.Icc (0 : ℤ) ((N n : ℤ) - 1)).image (fun k : ℤ => (N n : ℝ)⁻¹ * k)

/-- The uniform law on `Samp = [0,1) ∩ 𝕃` (spacing `1/N`), as a hyperfinite counting
probability. -/
def uniformLattice (N : ℕ → ℕ) : HypMeasure ℝ := HypMeasure.counting (unifPoints N)

theorem card_unifPoints (N : ℕ → ℕ) {n : ℕ} (hN : N n ≠ 0) : (unifPoints N n).card = N n := by
  unfold unifPoints
  rw [Finset.card_image_of_injective _ (fun k₁ k₂ h => by
    exact_mod_cast mul_left_cancel₀ (inv_ne_zero (Nat.cast_ne_zero.2 hN)) h), Int.card_Icc]
  omega

theorem uniform_seqMass_Icc (N : ℕ → ℕ) (a b : ℝ) {n : ℕ} (hN : N n ≠ 0) :
    (uniformLattice N).seqMass (fun _ => Icc a b) n = (N n : ℝ)⁻¹ *
      ((Finset.Icc (0 : ℤ) ((N n : ℤ) - 1)).filter
        (fun k : ℤ => a ≤ (N n : ℝ)⁻¹ * k ∧ (N n : ℝ)⁻¹ * k ≤ b)).card := by
  unfold HypMeasure.seqMass
  simp only [uniformLattice, HypMeasure.counting]
  rw [Finset.sum_const, nsmul_eq_mul, card_unifPoints N hN]
  unfold unifPoints
  rw [card_filter_image_mul (inv_ne_zero (Nat.cast_ne_zero.2 hN))]
  ring

theorem ofReal_max_zero (x : ℝ) : ENNReal.ofReal (max x 0) = ENNReal.ofReal x := by
  rcases le_total x 0 with h | h
  · rw [max_eq_right h, ENNReal.ofReal_zero, ENNReal.ofReal_of_nonpos h]
  · rw [max_eq_left h]

theorem tendsto_inv_of_isUnlimited {N : ℕ → ℕ} (hN : IsUnlimited ((N : ℕ → ℕ) : Ult ℕ)) :
    Tendsto (fun n => ((N n : ℝ))⁻¹) (hyperfilter ℕ : Filter ℕ) (𝓝 0) := by
  rw [Metric.tendsto_nhds]; intro r hr
  obtain ⟨m, hm⟩ := exists_nat_gt (1 / r)
  filter_upwards [Germ.coe_lt.1 (hN m)] with n hn
  have hNn : (m : ℝ) < N n := by exact_mod_cast hn
  have hpos : (0 : ℝ) < N n := lt_of_le_of_lt (Nat.cast_nonneg m) hNn
  rw [Real.dist_eq, sub_zero, abs_of_pos (inv_pos.2 hpos), inv_lt_comm₀ hpos hr]
  calc r⁻¹ = 1 / r := (one_div r).symm
    _ < m := hm
    _ < N n := hNn

/-- For a standard interval, `L(*[a,b] ∩ Samp) = λ([a,b] ∩ [0,1])`. -/
theorem uniform_loeb_box {N : ℕ → ℕ} (hN : IsUnlimited ((N : ℕ → ℕ) : Ult ℕ)) (a b : ℝ)
    (_hab : a ≤ b) :
    (uniformLattice N).loeb (starSet (Icc a b)) = volume.restrict (Icc 0 1) (Icc a b) := by
  rw [HypMeasure.loeb_internal _ (isInternal_starSet _), starSet, HypMeasure.mass_internal,
    Measure.restrict_apply measurableSet_Icc, Set.Icc_inter_Icc, Real.volume_Icc]
  rw [show b ⊓ 1 - a ⊔ 0 = min 1 b - max 0 a by rw [min_comm, max_comm],
    ← ofReal_max_zero]
  apply stE_ofSeq_of_tendsto
  have hpos : ∀ᶠ n in (hyperfilter ℕ : Filter ℕ), 0 < N n := Germ.coe_lt.1 (hN 0)
  refine Tendsto.congr' (f₁ := fun n => (N n : ℝ)⁻¹ *
      ((Finset.Icc (0 : ℤ) ((N n : ℤ) - 1)).filter
        (fun k : ℤ => a ≤ (N n : ℝ)⁻¹ * k ∧ (N n : ℝ)⁻¹ * k ≤ b)).card) ?_ ?_
  · filter_upwards [hpos] with n hn
    exact (uniform_seqMass_Icc N a b hn.ne').symm
  · refine tendsto_of_abs_sub_le (g := fun n => 2 * (N n : ℝ)⁻¹)
      (by simpa using (tendsto_inv_of_isUnlimited hN).const_mul 2) ?_
    filter_upwards [hpos] with n hn
    have hNpos : (0 : ℝ) < N n := by exact_mod_cast hn
    set t := (N n : ℝ)⁻¹ with ht
    have htpos : 0 < t := inv_pos.2 hNpos
    have h := card_filter_Icc_bound htpos 0 ((N n : ℤ) - 1) a b
    have htq : t * ((((N n : ℤ) - 1 : ℤ)) : ℝ) = 1 - t := by
      push_cast; rw [mul_sub, mul_one, ht, inv_mul_cancel₀ hNpos.ne']
    rw [htq, Int.cast_zero, mul_zero] at h
    have hmin : |max (min (1 - t) b - max 0 a) 0 - max (min 1 b - max 0 a) 0| ≤ t := by
      refine (abs_max_sub_max_le_abs _ _ _).trans ?_
      rw [abs_le]; constructor
      · have : min 1 b - t ≤ min (1 - t) b :=
          le_min (by linarith [min_le_left 1 b]) (by linarith [min_le_right 1 b])
        linarith
      · have : min (1 - t) b ≤ min 1 b := min_le_min (by linarith) le_rfl
        linarith
    calc _ ≤ _ := abs_sub_le _ (max (min (1 - t) b - max 0 a) 0) _
      _ ≤ t + t := add_le_add h hmin
      _ = 2 * t := by ring

theorem uniformLattice_carrier_nonempty {N : ℕ → ℕ} (hN : IsUnlimited ((N : ℕ → ℕ) : Ult ℕ)) :
    (uniformLattice N).carrier.Nonempty := by
  refine (internal_nonempty_iff _).2 ?_
  filter_upwards [Germ.coe_lt.1 (hN 0)] with n hn
  refine ⟨(N n : ℝ)⁻¹ * ((0 : ℤ) : ℝ), Finset.mem_coe.2 (Finset.mem_image.2 ⟨0, ?_, rfl⟩)⟩
  rw [Finset.mem_Icc]; constructor <;> omega

/-- The Loeb measure of the uniform lattice law is a probability measure. -/
theorem uniform_isProbabilityMeasure {N : ℕ → ℕ} (hN : IsUnlimited ((N : ℕ → ℕ) : Ult ℕ)) :
    IsProbabilityMeasure (uniformLattice N).loeb :=
  HypMeasure.isProbabilityMeasure_loeb_counting _ (uniformLattice_carrier_nonempty hN)

/-- `Samp` is `[0,1) ∩ 𝕃` with `𝕃 = 2εℤ*`, `2ε = 1/N`. -/
theorem uniformLattice_carrier {N : ℕ → ℕ} (hN : IsUnlimited ((N : ℕ → ℕ) : Ult ℕ)) :
    (uniformLattice N).carrier = {x : ℝ* | x ∈ lattice (Hyperreal.ofSeq fun n => 1 / (2 * (N n : ℝ)))
      ∧ 0 ≤ x ∧ x < 1} := by
  have hpos : ∀ᶠ n in (hyperfilter ℕ : Filter ℕ), 0 < N n := Germ.coe_lt.1 (hN 0)
  ext x
  obtain ⟨u, rfl⟩ := Hyperreal.ofSeq_surjective x
  change (u : Ult ℝ) ∈ internal _ ↔ Hyperreal.ofSeq u ∈ lattice _ ∧ 0 ≤ Hyperreal.ofSeq u ∧
    Hyperreal.ofSeq u < 1
  rw [mem_internal]
  rw [mem_lattice_ofSeq, show (0 : ℝ*) ≤ Hyperreal.ofSeq u ↔ _ from Germ.coe_nonneg,
    show Hyperreal.ofSeq u < (1 : ℝ*) ↔ _ from ofSeq_lt_const (r := 1), ← eventually_and,
    ← eventually_and]
  refine eventually_congr ?_
  filter_upwards [hpos] with n hn
  have hNpos : (0 : ℝ) < N n := by exact_mod_cast hn
  have h2 : 2 * (1 / (2 * (N n : ℝ))) = (N n : ℝ)⁻¹ := by field_simp
  show u n ∈ (unifPoints N n : Set ℝ) ↔ _
  rw [Finset.mem_coe, unifPoints, Finset.mem_image, h2]
  simp only [Finset.mem_Icc]
  constructor
  · rintro ⟨k, ⟨hk0, hk1⟩, hku⟩
    rw [← hku]
    refine ⟨⟨k, rfl⟩, by positivity, ?_⟩
    rw [inv_mul_lt_iff₀ hNpos, mul_one]
    have : (k : ℝ) ≤ (N n : ℝ) - 1 := by exact_mod_cast hk1
    linarith
  · rintro ⟨⟨k, hk⟩, h0, h1⟩
    refine ⟨k, ⟨?_, ?_⟩, hk.symm⟩
    · rw [hk] at h0
      have : (0 : ℝ) ≤ k := by
        by_contra hc; push Not at hc
        have : (N n : ℝ)⁻¹ * k < 0 := mul_neg_of_pos_of_neg (inv_pos.2 hNpos) hc
        linarith
      exact_mod_cast this
    · rw [hk, inv_mul_lt_iff₀ hNpos, mul_one] at h1
      have : (k : ℤ) < (N n : ℤ) := by exact_mod_cast h1
      omega

/-- **Push-forward form**: the image of the Loeb measure of the uniform law on
`[0,1) ∩ 𝕃` under `st : Samp → [0,1]` is Lebesgue measure on `[0,1]`. -/
theorem uniform_pushforward {N : ℕ → ℕ} (hN : IsUnlimited ((N : ℕ → ℕ) : Ult ℕ)) :
    stMeasure (uniformLattice N).loeb = volume.restrict (Icc 0 1) :=
  stMeasure_eq_of_Icc _ _ (fun a b hab => uniform_loeb_box hN a b hab)

/-- **Lebesgue measure is the Loeb shadow of the uniform lattice law.** For every Borel
`E ⊆ ℝ`, `st⁻¹(E) ∩ Samp` is Loeb measurable and `L(st⁻¹(E) ∩ Samp) = λ(E ∩ [0,1])`. -/
theorem loeb_shadow_uniform {N : ℕ → ℕ} (hN : IsUnlimited ((N : ℕ → ℕ) : Ult ℕ)) {E : Set ℝ}
    (hE : MeasurableSet E) :
    MeasurableSet (stInv E ∩ (uniformLattice N).carrier) ∧
      (uniformLattice N).loeb (stInv E ∩ (uniformLattice N).carrier) = volume (E ∩ Icc 0 1) := by
  refine ⟨(measurableSet_stInv hE).inter (HypMeasure.isInternal_carrier _).measurableSet, ?_⟩
  rw [HypMeasure.loeb_inter_carrier, ← stMeasure_apply _ hE, uniform_pushforward hN,
    Measure.restrict_apply hE]

/-- The book's form: for Borel `E ⊆ [0,1)`, `L(st⁻¹(E) ∩ Samp) = λ(E)`. -/
theorem loeb_shadow_uniform_of_subset {N : ℕ → ℕ} (hN : IsUnlimited ((N : ℕ → ℕ) : Ult ℕ))
    {E : Set ℝ} (hE : MeasurableSet E) (hsub : E ⊆ Ico 0 1) :
    MeasurableSet (stInv E ∩ (uniformLattice N).carrier) ∧
      (uniformLattice N).loeb (stInv E ∩ (uniformLattice N).carrier) = volume E := by
  obtain ⟨h1, h2⟩ := loeb_shadow_uniform hN hE
  refine ⟨h1, ?_⟩
  rw [h2, Set.inter_eq_left.2 (hsub.trans Ico_subset_Icc_self)]

/-- The mass at `1` is zero: `L(st⁻¹{1}) = 0`. -/
theorem uniform_loeb_stInv_one {N : ℕ → ℕ} (hN : IsUnlimited ((N : ℕ → ℕ) : Ult ℕ)) :
    (uniformLattice N).loeb (stInv {1}) = 0 := by
  rw [← stMeasure_apply _ (measurableSet_singleton 1), uniform_pushforward hN,
    Measure.restrict_apply (measurableSet_singleton 1)]
  exact measure_mono_null Set.inter_subset_left Real.volume_singleton

end Uniform

/-! ## Restriction to an internal box (the σ-finite case box by box) -/

namespace HypMeasure

variable (ν : HypMeasure α)

/-- The restriction of `ν` to the internal set `[B n]`. -/
def restrict (B : ℕ → Set α) : HypMeasure α where
  supp n := @Finset.filter _ (· ∈ B n) (Classical.decPred _) (ν.supp n)
  weight := ν.weight
  weight_nonneg := ν.weight_nonneg

theorem restrict_mass (B : ℕ → Set α) {S : Set (Ult α)} (hS : IsInternal S) :
    (ν.restrict B).mass S = ν.mass (S ∩ internal B) := by
  obtain ⟨C, rfl⟩ := hS
  rw [← internal_inter, mass_internal, mass_internal]
  refine Germ.coe_eq.2 (Eventually.of_forall fun n => ?_)
  show (ν.restrict B).seqMass C n = ν.seqMass (fun n => C n ∩ B n) n
  unfold seqMass
  simp only [restrict]
  rw [Finset.filter_filter]
  apply Finset.sum_congr _ (fun _ _ => rfl)
  ext x; simp only [Finset.mem_filter, Set.mem_inter_iff]; tauto

/-- **Box by box**: the Loeb measure of the restriction of `ν` to an internal set `S` of
limited mass is the restriction of the Loeb measure of `ν` to `S`. -/
theorem loeb_restrict (B : ℕ → Set α) (hfin : IsFinite ((ν.restrict B).mass univ)) :
    (ν.restrict B).loeb = ν.loeb.restrict (internal B) := by
  refine ((ν.restrict B).loeb_unique hfin _ fun T hT => ?_).symm
  rw [Measure.restrict_apply hT.measurableSet, ν.loeb_internal (hT.inter (isInternal_internal B)),
    ν.restrict_mass B hT]

end HypMeasure

/-! ## The standard part of an internal set -/

section StImg

variable {X : Type*} [MetricSpace X]

/-- The standard part `st(A) = {y : ∃ x ∈ A, x ≈ y}` of a set `A ⊆ Ult X`. -/
def stImg (A : Set (Ult X)) : Set X := {y | ∃ x ∈ A, Near x (Germ.const y)}

/-- **The standard part of an internal set is closed** (countable saturation). -/
theorem isClosed_stImg {A : Set (Ult X)} (hA : IsInternal A) : IsClosed (stImg A) := by
  refine isClosed_of_closure_subset fun y hy => ?_
  rw [Metric.mem_closure_iff] at hy
  let T : ℕ → Set (Ult X) := fun j => A ∩ starSet (Metric.closedBall y (2 / ((j : ℝ) + 1)))
  have hT : ∀ j, IsInternal (T j) := fun j => hA.inter (isInternal_starSet _)
  have hne : ∀ j, (T j).Nonempty := by
    intro j
    obtain ⟨b, ⟨x, hxA, hxb⟩, hyb⟩ := hy (1 / ((j : ℝ) + 1)) (one_div_succ_pos j)
    refine ⟨x, hxA, ?_⟩
    obtain ⟨u, rfl⟩ := exists_rep x
    rw [mem_starSet]
    rw [near_const_iff_tendsto] at hxb
    filter_upwards [hxb (Metric.ball_mem_nhds b (one_div_succ_pos j))] with n hn
    have hn' : u n ∈ Metric.ball b (1 / ((j : ℝ) + 1)) := hn
    rw [Metric.mem_closedBall]; rw [Metric.mem_ball] at hn'
    have h2 : 2 / ((j : ℝ) + 1) = 1 / ((j : ℝ) + 1) + 1 / ((j : ℝ) + 1) := by ring
    calc dist (u n) y ≤ dist (u n) b + dist b y := dist_triangle _ _ _
      _ ≤ 2 / ((j : ℝ) + 1) := by rw [dist_comm b y, h2]; linarith
  have hanti : Antitone T := by
    intro i j hij
    refine Set.inter_subset_inter_right _ (starSet_mono (Metric.closedBall_subset_closedBall ?_))
    have := one_div_succ_anti hij
    have e1 : 2 / ((j : ℝ) + 1) = 2 * (1 / ((j : ℝ) + 1)) := by ring
    have e2 : 2 / ((i : ℝ) + 1) = 2 * (1 / ((i : ℝ) + 1)) := by ring
    rw [e1, e2]; linarith
  obtain ⟨x, hx⟩ := saturation_decreasing T hT hne hanti
  rw [Set.mem_iInter] at hx
  refine ⟨x, (hx 0).1, ?_⟩
  obtain ⟨u, rfl⟩ := exists_rep x
  rw [near_const_iff_tendsto, Metric.tendsto_nhds]
  intro r hr
  obtain ⟨j, hj⟩ := exists_nat_one_div_lt (half_pos hr)
  filter_upwards [(mem_starSet _ u).1 (hx j).2] with n hn
  rw [Metric.mem_closedBall] at hn
  have e1 : 2 / ((j : ℝ) + 1) = 2 * (1 / ((j : ℝ) + 1)) := by ring
  linarith

theorem subset_stInv_stImg {A : Set (Ult X)} (h : A ⊆ stInv univ) : A ⊆ stInv (stImg A) := by
  intro x hx
  obtain ⟨y, -, hxy⟩ := h hx
  exact ⟨y, ⟨x, hx, hxy⟩, hxy⟩

theorem stImg_subset {A : Set (Ult X)} {E : Set X} (h : A ⊆ stInv E) : stImg A ⊆ E := by
  rintro y ⟨x, hx, hxy⟩
  obtain ⟨y', hy', hxy'⟩ := h hx
  rwa [near_const_unique hxy hxy']

/-- A point of `*F`, `F` closed, near a standard `y` has `y ∈ F`. -/
theorem mem_of_near_of_mem_starSet {F : Set X} (hF : IsClosed F) {x : Ult X} {y : X}
    (hx : x ∈ starSet F) (hxy : Near x (Germ.const y)) : y ∈ F := by
  obtain ⟨u, rfl⟩ := exists_rep x
  exact hF.mem_of_tendsto ((near_const_iff_tendsto u y).1 hxy) ((mem_starSet _ u).1 hx)

end StImg

/-! ## The converse: the Loeb-measurable shadows are exactly the Lebesgue sets -/

section AndersonConverse

variable {d : ℕ}

/-- **Converse of Anderson's theorem (Henson–Anderson).** If `st⁻¹(E) ∩ 𝕃ⁿ` is Loeb
measurable, then `E` is Lebesgue measurable.  (Inner approximation by internal sets inside a
box, whose standard parts are closed.) -/
theorem nullMeasurableSet_of_anderson {e : ℕ → ℝ} {M : ℕ → ℕ} (he : 0 < Hyperreal.ofSeq e)
    (hε : IsInfinitesimal (Hyperreal.ofSeq e))
    (hΩ : ∀ r : ℝ, (r : ℝ*) < 2 * Hyperreal.ofSeq e * Hyperreal.ofSeq (fun n => (M n : ℝ)))
    {E : Set (Fin d → ℝ)}
    (hE : NullMeasurableSet (stInv E ∩ (latMeasure d e M).carrier) (latMeasure d e M).loeb) :
    NullMeasurableSet E volume := by
  set ν := latMeasure d e M with hν
  let Q : ℕ → Set (Fin d → ℝ) := fun m => Icc (fun _ => -(m : ℝ)) (fun _ => (m : ℝ))
  have hQle : ∀ m : ℕ, (fun _ : Fin d => -(m : ℝ)) ≤ fun _ => (m : ℝ) :=
    fun m i => by linarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ m)]
  have hEU : E = ⋃ m : ℕ, E ∩ Q m := by
    ext y; simp only [Set.mem_iUnion, Set.mem_inter_iff]
    constructor
    · intro hy
      obtain ⟨m, hm⟩ := exists_nat_ge ‖y‖
      refine ⟨m, hy, fun i => ?_, fun i => ?_⟩
      · have := norm_le_pi_norm y i; rw [Real.norm_eq_abs] at this
        linarith [neg_abs_le (y i)]
      · have := norm_le_pi_norm y i; rw [Real.norm_eq_abs] at this
        linarith [le_abs_self (y i)]
    · rintro ⟨m, hy, -⟩; exact hy
  have hpush := anderson_pushforward (d := d) he hε hΩ
  rw [hEU]
  refine NullMeasurableSet.iUnion fun m => ?_
  -- work inside the internal box `W = *Q ∩ Ω`
  set W := starSet (Q m) ∩ ν.carrier
  set ν' := ν.restrict (fun _ => Q m)
  have hbox := latMeasure_loeb_box he hε hΩ _ _ (hQle m)
  have hfin' : IsFinite (ν'.mass univ) := by
    rw [ν.restrict_mass _ isInternal_univ, Set.univ_inter]
    rw [ν.loeb_internal (isInternal_starSet _)] at hbox
    refine stE_lt_top_iff.1 ?_
    show stE (ν.mass (starSet (Q m))) < ⊤
    rw [hbox]; exact measure_Icc_lt_top
  have hloeb' : ν'.loeb = ν.loeb.restrict (starSet (Q m)) := ν.loeb_restrict _ hfin'
  set B' := stInv E ∩ ν.carrier ∩ starSet (Q m)
  have hB' : NullMeasurableSet B' ν'.loeb := by
    rw [hloeb']
    exact (hE.inter (measurableSet_starSet _).nullMeasurableSet).mono Measure.restrict_le_self
  have hQc : IsCompact (Q m) := isCompact_Icc
  have hstQ : starSet (Q m) ⊆ stInv (Q m) := by
    intro x hx
    obtain ⟨y, hy, hxy⟩ := (isCompact_iff_near _).1 hQc x hx
    exact ⟨y, hy, hxy⟩
  have hvolQ : stMeasure ν.loeb (Q m) = ν.loeb (starSet (Q m)) := by
    rw [hbox, hpush]
  have hnullQ : ν.loeb (stInv (Q m) \ starSet (Q m)) = 0 := by
    rw [measure_sdiff hstQ (measurableSet_starSet _).nullMeasurableSet
      (by rw [hbox]; exact measure_Icc_lt_top.ne), ← stMeasure_apply _ measurableSet_Icc,
      hvolQ, tsub_self]
  -- the approximating closed sets
  have key : ∀ k : ℕ, ∃ F G : Set (Fin d → ℝ), IsClosed F ∧ IsClosed G ∧ F ⊆ E ∩ Q m ∧
      G ⊆ Q m \ E ∧ volume (Q m \ (F ∪ G)) ≤ ENNReal.ofReal (1 / ((k : ℝ) + 1)) := by
    intro k
    obtain ⟨A, C, hA, hC, hAB, hBC, hmass⟩ :=
      (ν'.nullMeasurableSet_iff_approx hfin' B').1 hB' _ (one_div_succ_pos k)
    have hWi : IsInternal W := (isInternal_starSet _).inter ν.isInternal_carrier
    set A' := W \ (C ∩ W)
    have hA'i : IsInternal A' := hWi.diff (hC.inter hWi)
    have hAsub : A ⊆ stInv (E ∩ Q m) := by
      intro x hx
      obtain ⟨⟨⟨y, hy, hxy⟩, -⟩, hxQ⟩ := hAB hx
      exact ⟨y, ⟨hy, mem_of_near_of_mem_starSet isClosed_Icc hxQ hxy⟩, hxy⟩
    have hA'sub : A' ⊆ stInv (Q m \ E) := by
      rintro x ⟨⟨hxQ, hxΩ⟩, hxC⟩
      obtain ⟨y, hy, hxy⟩ := (isCompact_iff_near _).1 hQc x hxQ
      refine ⟨y, ⟨hy, fun hyE => hxC ⟨hBC ⟨⟨⟨y, hyE, hxy⟩, hxΩ⟩, hxQ⟩, hxQ, hxΩ⟩⟩, hxy⟩
    have hAns : A ⊆ stInv univ := hAsub.trans (stInv_mono (Set.subset_univ _))
    have hA'ns : A' ⊆ stInv univ := hA'sub.trans (stInv_mono (Set.subset_univ _))
    refine ⟨stImg A, stImg A', isClosed_stImg hA, isClosed_stImg hA'i, stImg_subset hAsub,
      stImg_subset hA'sub, ?_⟩
    have hmeas : MeasurableSet (Q m \ (stImg A ∪ stImg A')) :=
      measurableSet_Icc.diff ((isClosed_stImg hA).measurableSet.union
        (isClosed_stImg hA'i).measurableSet)
    rw [← hpush, stMeasure_apply _ hmeas, stInv_diff, stInv_iUnion_two]
    have hsub : stInv (Q m) \ (stInv (stImg A) ∪ stInv (stImg A')) ∩ ν.carrier ⊆
        (stInv (Q m) \ starSet (Q m)) ∪ ((C \ A) ∩ starSet (Q m)) := by
      rintro x ⟨⟨hxQ, hxn⟩, hxΩ⟩
      by_cases hxs : x ∈ starSet (Q m)
      · refine Or.inr ⟨⟨?_, fun hxA => hxn (Or.inl (subset_stInv_stImg hAns hxA))⟩, hxs⟩
        by_contra hxC
        exact hxn (Or.inr (subset_stInv_stImg hA'ns ⟨⟨hxs, hxΩ⟩, fun h => hxC h.1⟩))
      · exact Or.inl ⟨hxQ, hxs⟩
    rw [← HypMeasure.loeb_inter_carrier]
    calc ν.loeb ((stInv (Q m) \ (stInv (stImg A) ∪ stInv (stImg A'))) ∩ ν.carrier)
        ≤ ν.loeb ((stInv (Q m) \ starSet (Q m)) ∪ ((C \ A) ∩ starSet (Q m))) := measure_mono hsub
      _ ≤ ν.loeb (stInv (Q m) \ starSet (Q m)) + ν.loeb ((C \ A) ∩ starSet (Q m)) :=
          measure_union_le _ _
      _ = ν'.loeb (C \ A) := by
          rw [hnullQ, zero_add, hloeb', Measure.restrict_apply (hC.diff hA).measurableSet]
      _ = stE (ν'.mass (C \ A)) := ν'.loeb_internal (hC.diff hA)
      _ ≤ _ := stE_le_of_le (ν'.mass_nonneg _) hmass.le
  choose F G hF hG hFE hGE hvol using key
  set Finf := ⋃ k, F k
  set Ginf := ⋂ k, (Q m \ G k)
  have hFinf : MeasurableSet Finf := MeasurableSet.iUnion fun k => (hF k).measurableSet
  have h1 : Finf ⊆ E ∩ Q m := Set.iUnion_subset hFE
  have h2 : E ∩ Q m ⊆ Ginf := Set.subset_iInter fun k x hx =>
    ⟨hx.2, fun hxG => ((hGE k) hxG).2 hx.1⟩
  have hbound : ∀ k : ℕ, volume (Ginf \ Finf) ≤ ENNReal.ofReal (1 / ((k : ℝ) + 1)) := by
    intro k
    refine le_trans (measure_mono ?_) (hvol k)
    rintro x ⟨hxG, hxF⟩
    have hx := Set.mem_iInter.1 hxG k
    refine ⟨hx.1, ?_⟩
    rintro (h | h)
    · exact hxF (Set.mem_iUnion.2 ⟨k, h⟩)
    · exact hx.2 h
  have hnull : volume (Ginf \ Finf) = 0 := by
    refine le_antisymm ?_ bot_le
    have ht : Tendsto (fun k : ℕ => ENNReal.ofReal (1 / ((k : ℝ) + 1))) atTop (𝓝 0) := by
      rw [← ENNReal.ofReal_zero]
      exact ENNReal.tendsto_ofReal tendsto_one_div_add_atTop_nhds_zero_nat
    exact ge_of_tendsto' ht hbound
  have hle : volume (E ∩ Q m) ≤ volume Finf := by
    calc volume (E ∩ Q m) ≤ volume Ginf := measure_mono h2
      _ ≤ volume (Finf ∪ (Ginf \ Finf)) := measure_mono (fun x hx => by
          by_cases h : x ∈ Finf
          · exact Or.inl h
          · exact Or.inr ⟨hx, h⟩)
      _ ≤ volume Finf + volume (Ginf \ Finf) := measure_union_le _ _
      _ = volume Finf := by rw [hnull, add_zero]
  have hfinE : volume (E ∩ Q m) ≠ ∞ :=
    ne_top_of_le_ne_top measure_Icc_lt_top.ne (measure_mono Set.inter_subset_right)
  exact hFinf.nullMeasurableSet.congr
    (ae_eq_of_subset_of_measure_ge h1 hle hFinf.nullMeasurableSet hfinE)

/-- **Shadow theorem, Loeb case, with the converse**: `E` is Lebesgue measurable iff
`st⁻¹(E) ∩ 𝕃ⁿ` is Loeb measurable, and then `λ(E) = L(st⁻¹(E) ∩ 𝕃ⁿ)`. -/
theorem anderson_iff {e : ℕ → ℝ} {M : ℕ → ℕ} (he : 0 < Hyperreal.ofSeq e)
    (hε : IsInfinitesimal (Hyperreal.ofSeq e))
    (hΩ : ∀ r : ℝ, (r : ℝ*) < 2 * Hyperreal.ofSeq e * Hyperreal.ofSeq (fun n => (M n : ℝ)))
    (E : Set (Fin d → ℝ)) :
    NullMeasurableSet E volume ↔
      NullMeasurableSet (stInv E ∩ (latMeasure d e M).carrier) (latMeasure d e M).loeb :=
  ⟨fun h => (anderson he hε hΩ h).1, nullMeasurableSet_of_anderson he hε hΩ⟩

end AndersonConverse

/-! ## External uncountability of `{0,1}^K` by an internal diagonal -/

section External

/-- The internal set `{0,1}^K` of bit strings of hyperfinite length `K = [K n]` (a string is
a map `ℕ → Bool` vanishing from position `K n` on). -/
def bitStringsH (K : ℕ → ℕ) : Set (Ult (ℕ → Bool)) :=
  internal (fun n => {s : ℕ → Bool | ∀ j, K n ≤ j → s j = false})

/-- **No sequence exhausts `{0,1}^K`** for infinite `K`: extend the sequence to an internal
hypersequence (countable saturation) and take its internal diagonal. -/
theorem exists_mem_bitStringsH_ne {K : ℕ → ℕ} (hK : IsUnlimited ((K : ℕ → ℕ) : Ult ℕ))
    (x : ℕ → Ult (ℕ → Bool)) : ∃ y ∈ bitStringsH K, ∀ k, y ≠ x k := by
  obtain ⟨X, hX, -⟩ := extension_of_sequences Set.univ isInternal_univ x (fun _ => Set.mem_univ _)
  let D : ℕ → ℕ → Bool := fun n j => if j < K n then !(X n j j) else false
  refine ⟨(D : Ult (ℕ → Bool)), (mem_internal _ _).2 (Eventually.of_forall fun n j hj => ?_),
    fun k hk => ?_⟩
  · simp [D, not_lt.2 hj]
  · have hk' : ((D : ℕ → ℕ → Bool) : Ult (ℕ → Bool)) =
        ((fun n => X n k : ℕ → ℕ → Bool) : Ult (ℕ → Bool)) := hk.trans (hX k).symm
    have hev := Germ.coe_eq.1 hk'
    obtain ⟨n, hn1, hn2⟩ := (hev.and (Germ.coe_lt.1 (hK k))).exists
    have := congrFun hn1 k
    simp [D, hn2] at this

/-- **External uncountability**: for infinite `K`, `{0,1}^K` is not countable. -/
theorem bitStringsH_not_countable {K : ℕ → ℕ} (hK : IsUnlimited ((K : ℕ → ℕ) : Ult ℕ)) :
    ¬ (bitStringsH K).Countable := by
  intro hc
  have hne : (bitStringsH K).Nonempty :=
    ⟨((fun _ _ => false : ℕ → ℕ → Bool) : Ult (ℕ → Bool)),
      (mem_internal _ _).2 (Eventually.of_forall fun _ _ _ => rfl)⟩
  obtain ⟨f, hf⟩ := hc.exists_eq_range hne
  obtain ⟨y, hy, hne'⟩ := exists_mem_bitStringsH_ne hK f
  rw [hf] at hy
  obtain ⟨k, rfl⟩ := hy
  exact hne' k rfl

end External

/-! ## Anderson's random walk: coin combinatorics -/

section CoinSpace

open QE.Prob

/-- A sequence of `N` coins, extended by `false` (the coin space `{±1}^N` inside `ℕ → Bool`). -/
def coinExt (N : ℕ) (ω : Fin N → Bool) : ℕ → Bool := fun j => if h : j < N then ω ⟨j, h⟩ else false

theorem coinExt_injective (N : ℕ) : Function.Injective (coinExt N) := by
  intro ω ω' h; funext i
  have := congrFun h i
  simpa [coinExt, i.isLt] using this

/-- Shift a coin sequence `p` places to the right. -/
def shiftR (p : ℕ) (ω : ℕ → Bool) : ℕ → Bool := fun j => if j < p then false else ω (j - p)

open Classical in
/-- The probability of an event under the uniform law on `N` fair coins. -/
def probU (N : ℕ) (A : (ℕ → Bool) → Prop) : ℝ :=
  (∑ ω : Fin N → Bool, if A (coinExt N ω) then (1 : ℝ) else 0) / 2 ^ N

theorem coinExt_append_lt {p q : ℕ} (u : Fin p → Bool) (v : Fin q → Bool) {j : ℕ} (hj : j < p) :
    coinExt (p + q) (Fin.append u v) j = coinExt p u j := by
  have h1 : j < p + q := by omega
  simp only [coinExt, h1, hj, dite_true]
  have : (⟨j, h1⟩ : Fin (p + q)) = Fin.castAdd q ⟨j, hj⟩ := rfl
  rw [this, Fin.append_left]

theorem coinExt_append_ge {p q : ℕ} (u : Fin p → Bool) (v : Fin q → Bool) {j : ℕ} (hj : p ≤ j) :
    coinExt (p + q) (Fin.append u v) j = shiftR p (coinExt q v) j := by
  simp only [shiftR, not_lt.2 hj, ite_false, coinExt]
  by_cases h : j < p + q
  · have h' : j - p < q := by omega
    simp only [h, h', dite_true]
    have : (⟨j, h⟩ : Fin (p + q)) = Fin.natAdd p ⟨j - p, h'⟩ := by ext; simp; omega
    rw [this, Fin.append_right]
  · have h' : ¬ j - p < q := by omega
    simp [h, h']

theorem probU_true (N : ℕ) : probU N (fun _ => True) = 1 := by
  unfold probU
  simp only [ite_true, Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_bool,
    Fintype.card_fin, nsmul_eq_mul, mul_one]
  push_cast
  exact div_self (by positivity)

/-- **Independence of disjoint blocks of coins.** If `A` depends only on the coins before `p`
and `B` only on the coins from `p` on, then `P(A ∧ B) = P(A) P(B)`. -/
theorem probU_split (p q : ℕ) (A B : (ℕ → Bool) → Prop)
    (hA : ∀ ω ω' : ℕ → Bool, (∀ j < p, ω j = ω' j) → (A ω ↔ A ω'))
    (hB : ∀ ω ω' : ℕ → Bool, (∀ j, p ≤ j → ω j = ω' j) → (B ω ↔ B ω')) :
    probU (p + q) (fun ω => A ω ∧ B ω) = probU p A * probU q (fun ω => B (shiftR p ω)) := by
  classical
  unfold probU
  rw [pow_add, div_mul_div_comm, Finset.sum_mul_sum, ← Fintype.sum_prod_type']
  congr 1
  refine (Fintype.sum_equiv (Fin.appendEquiv p q) _ _ (fun uv => ?_)).symm
  obtain ⟨u, v⟩ := uv
  have he : (Fin.appendEquiv p q) (u, v) = Fin.append u v := rfl
  have h1 : A (coinExt (p + q) (Fin.append u v)) ↔ A (coinExt p u) :=
    hA _ _ (fun j hj => coinExt_append_lt u v hj)
  have h2 : B (coinExt (p + q) (Fin.append u v)) ↔ B (shiftR p (coinExt q v)) :=
    hB _ _ (fun j hj => coinExt_append_ge u v hj)
  rw [he]
  by_cases ha : A (coinExt p u) <;> by_cases hb : B (shiftR p (coinExt q v))
  · rw [ite_eq_left ha, ite_eq_left (show B (shiftR p (coinExt q v)) from hb),
      ite_eq_left (show A _ ∧ B _ from ⟨h1.2 ha, h2.2 hb⟩), mul_one]
  · rw [ite_eq_left ha, ite_eq_right (show ¬ B (shiftR p (coinExt q v)) from hb),
      ite_eq_right (show ¬ (A _ ∧ B _) from fun h => hb (h2.1 h.2)), mul_zero]
  · rw [ite_eq_right ha, ite_eq_right (show ¬ (A _ ∧ B _) from fun h => ha (h1.1 h.1)), zero_mul]
  · rw [ite_eq_right ha, ite_eq_right (show ¬ (A _ ∧ B _) from fun h => ha (h1.1 h.1)), zero_mul]

theorem probU_left (p q : ℕ) (A : (ℕ → Bool) → Prop)
    (hA : ∀ ω ω' : ℕ → Bool, (∀ j < p, ω j = ω' j) → (A ω ↔ A ω')) :
    probU (p + q) A = probU p A := by
  have := probU_split p q A (fun _ => True) hA (fun _ _ _ => Iff.rfl)
  simp only [and_true] at this
  rw [this, probU_true, mul_one]

theorem probU_right (p q : ℕ) (B : (ℕ → Bool) → Prop)
    (hB : ∀ ω ω' : ℕ → Bool, (∀ j, p ≤ j → ω j = ω' j) → (B ω ↔ B ω')) :
    probU (p + q) B = probU q (fun ω => B (shiftR p ω)) := by
  have := probU_split p q (fun _ => True) B (fun _ _ _ => Iff.rfl) hB
  simp only [true_and] at this
  rw [this, probU_true, one_mul]

/-- **Independence of finitely many disjoint blocks.** -/
theorem probU_forall_lt (N : ℕ) (K : ℕ → ℕ) (hK : Monotone K) (E : ℕ → (ℕ → Bool) → Prop)
    (hE : ∀ i ω ω', (∀ j, K i ≤ j → j < K (i + 1) → ω j = ω' j) → (E i ω ↔ E i ω')) :
    ∀ M, K M ≤ N → probU N (fun ω => ∀ i < M, E i ω) = ∏ i ∈ Finset.range M, probU N (E i) := by
  intro M
  induction M with
  | zero =>
    intro _
    simp only [Nat.not_lt_zero, false_imp_iff, imp_true_iff, Finset.range_zero, Finset.prod_empty]
    exact probU_true N
  | succ M ih =>
    intro hM
    have hMN : K M ≤ N := (hK (Nat.le_succ M)).trans hM
    obtain ⟨q, hq⟩ := Nat.exists_eq_add_of_le hMN
    have hsplit : (fun ω => ∀ i < M + 1, E i ω) = fun ω => (∀ i < M, E i ω) ∧ E M ω := by
      funext ω; apply propext
      constructor
      · intro h; exact ⟨fun i hi => h i (by omega), h M (by omega)⟩
      · rintro ⟨h1, h2⟩ i hi
        rcases Nat.lt_succ_iff_lt_or_eq.1 hi with h | h
        · exact h1 i h
        · rw [h]; exact h2
    rw [hsplit, Finset.prod_range_succ, ← ih hMN, hq]
    have hA : ∀ ω ω' : ℕ → Bool, (∀ j < K M, ω j = ω' j) →
        ((∀ i < M, E i ω) ↔ (∀ i < M, E i ω')) := by
      intro ω ω' h
      refine forall_congr' fun i => imp_congr_right fun hi => hE i ω ω' fun j _ hj2 => h j ?_
      exact lt_of_lt_of_le hj2 (hK (Nat.succ_le_of_lt hi))
    have hB : ∀ ω ω' : ℕ → Bool, (∀ j, K M ≤ j → ω j = ω' j) → (E M ω ↔ E M ω') :=
      fun ω ω' h => hE M ω ω' fun j hj1 _ => h j hj1
    rw [probU_split (K M) q _ _ hA hB, probU_left (K M) q _ hA, probU_right (K M) q _ hB]

/-- The sum of the signs of the coins `p ≤ j < q`. -/
def blockSum (ω : ℕ → Bool) (p q : ℕ) : ℝ := ∑ j ∈ Finset.Ico p q, (sgn (ω j) : ℝ)

theorem blockSum_congr {ω ω' : ℕ → Bool} {p q : ℕ} (h : ∀ j, p ≤ j → j < q → ω j = ω' j) :
    blockSum ω p q = blockSum ω' p q := by
  unfold blockSum
  refine Finset.sum_congr rfl fun j hj => ?_
  rw [Finset.mem_Ico] at hj
  rw [h j hj.1 hj.2]

theorem blockSum_shiftR (ω : ℕ → Bool) (p L : ℕ) :
    blockSum (shiftR p ω) p (p + L) = blockSum ω 0 L := by
  unfold blockSum
  rw [Finset.sum_Ico_eq_sum_range, Finset.range_eq_Ico]
  simp only [Nat.add_sub_cancel_left, shiftR]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp

theorem blockSum_coinExt (L : ℕ) (ω : Fin L → Bool) : blockSum (coinExt L ω) 0 L = S ω := by
  unfold blockSum S
  rw [← Finset.range_eq_Ico, ← Fin.sum_univ_eq_sum_range]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp [coinExt, i.isLt]

theorem blockSum_add {ω : ℕ → Bool} {p q r : ℕ} (hpq : p ≤ q) (hqr : q ≤ r) :
    blockSum ω p q + blockSum ω q r = blockSum ω p r := by
  unfold blockSum
  exact Finset.sum_Ico_consecutive _ hpq hqr

/-- The law of a block of coins is that of the first `L` coins (shift invariance). -/
theorem probU_block (N p L : ℕ) (h : p + L ≤ N) (A : ℝ → Prop) :
    probU N (fun ω => A (blockSum ω p (p + L))) = probU L (fun ω => A (blockSum ω 0 L)) := by
  obtain ⟨r, hr⟩ := Nat.exists_eq_add_of_le h
  rw [hr, add_assoc, probU_right p (L + r) _ (fun ω ω' hω => by
    rw [blockSum_congr (fun j hj _ => hω j hj)])]
  simp only [blockSum_shiftR]
  exact probU_left L r _ (fun ω ω' hω => by rw [blockSum_congr (fun j _ hj => hω j hj)])

end CoinSpace

/-! ## Anderson's random walk: the central limit step and Gaussian intervals -/

section WalkCLT

open QE.Prob QE.Prob.BE ProbabilityTheory
open scoped NNReal

theorem probU_blockSum_le (L : ℕ) (hL : 0 < L) (y : ℝ) :
    probU L (fun ω => blockSum ω 0 L ≤ y) = Fn L (y / √L) := by
  classical
  unfold probU Fn prob unif
  rw [Finset.sum_filter, Finset.card_univ, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin,
    Finset.sum_div]
  refine Finset.sum_congr rfl fun ω _ => ?_
  have hL' : √(L : ℝ) ≠ 0 := by positivity
  beta_reduce
  rw [blockSum_coinExt, div_mul_cancel₀ _ hL']
  split_ifs <;> push_cast <;> ring

theorem probU_add_not (N : ℕ) (A B : (ℕ → Bool) → Prop) :
    probU N A = probU N (fun ω => A ω ∧ B ω) + probU N (fun ω => A ω ∧ ¬ B ω) := by
  classical
  unfold probU
  rw [← add_div, ← Finset.sum_add_distrib]
  congr 1
  refine Finset.sum_congr rfl fun ω _ => ?_
  by_cases ha : A (coinExt N ω) <;> by_cases hb : B (coinExt N ω) <;> simp [ha, hb]

theorem probU_mono (N : ℕ) {A B : (ℕ → Bool) → Prop} (h : ∀ ω, A ω → B ω) :
    probU N A ≤ probU N B := by
  classical
  unfold probU
  refine div_le_div_of_nonneg_right (Finset.sum_le_sum fun ω _ => ?_) (by positivity)
  by_cases ha : A (coinExt N ω)
  · simp [ha, h _ ha]
  · simp only [ha, ite_false]; split_ifs <;> norm_num

theorem tendsto_two_thousand_div_sqrt {L : ℕ → ℕ}
    (hL : ∀ k : ℕ, ∀ᶠ m in (hyperfilter ℕ : Filter ℕ), k ≤ L m) :
    Tendsto (fun m => 2000 / √(L m : ℝ)) (hyperfilter ℕ : Filter ℕ) (𝓝 0) := by
  rw [Metric.tendsto_nhds]
  intro r hr
  obtain ⟨k, hk⟩ := exists_nat_gt ((2000 / r) ^ 2)
  filter_upwards [hL k] with m hm
  have hk' : ((2000 / r) ^ 2 : ℝ) < L m := lt_of_lt_of_le hk (by exact_mod_cast hm)
  have hpos : (0 : ℝ) < L m := lt_of_le_of_lt (by positivity) hk'
  have hs : 2000 / r < √(L m : ℝ) := by
    rw [← Real.sqrt_sq (by positivity : (0 : ℝ) ≤ 2000 / r)]
    exact Real.sqrt_lt_sqrt (by positivity) hk'
  rw [Real.dist_eq, sub_zero, abs_of_pos (by positivity)]
  rw [div_lt_iff₀ (by positivity)] at hs ⊢
  rw [mul_comm]; exact hs

/-- **CLT along the ultrafilter**: `P(S_L ≤ x_m √L) → Φ(x)` when `L → ∞` and `x_m → x`. -/
theorem tendsto_Fn {L : ℕ → ℕ} (hL : ∀ k : ℕ, ∀ᶠ m in (hyperfilter ℕ : Filter ℕ), k ≤ L m)
    {x : ℕ → ℝ} {x0 : ℝ} (hx : Tendsto x (hyperfilter ℕ : Filter ℕ) (𝓝 x0)) :
    Tendsto (fun m => Fn (L m) (x m)) (hyperfilter ℕ : Filter ℕ) (𝓝 (Phi x0)) := by
  refine tendsto_of_abs_sub_le (g := fun m => 2000 / √(L m : ℝ) + |x m - x0|) ?_ ?_
  · have h2 : Tendsto (fun m => |x m - x0|) (hyperfilter ℕ : Filter ℕ) (𝓝 0) := by
      have := (hx.sub_const x0).abs; simpa using this
    simpa using (tendsto_two_thousand_div_sqrt hL).add h2
  · filter_upwards [hL 1] with m hm
    calc |Fn (L m) (x m) - Phi x0| ≤ |Fn (L m) (x m) - Phi (x m)| + |Phi (x m) - Phi x0| :=
          abs_sub_le _ _ _
      _ ≤ 2000 / √(L m : ℝ) + |x m - x0| :=
          add_le_add (clt_error_explicit _ hm _) (Phi_lipschitz _ _)

/-- **The law of a long block of coins**: if `L → ∞` and `c √L → σ > 0`, then
`P(a ≤ c S_L ≤ b) → Φ(b/σ) - Φ(a/σ)`. -/
theorem tendsto_probU_Icc {L : ℕ → ℕ} {c : ℕ → ℝ} {σ : ℝ} (hσ : 0 < σ)
    (hc : ∀ᶠ m in (hyperfilter ℕ : Filter ℕ), 0 < c m)
    (hL : ∀ k : ℕ, ∀ᶠ m in (hyperfilter ℕ : Filter ℕ), k ≤ L m)
    (hcL : Tendsto (fun m => c m * √(L m : ℝ)) (hyperfilter ℕ : Filter ℕ) (𝓝 σ)) {a b : ℝ}
    (hab : a ≤ b) :
    Tendsto (fun m => probU (L m) (fun ω => a ≤ c m * blockSum ω 0 (L m) ∧
      c m * blockSum ω 0 (L m) ≤ b)) (hyperfilter ℕ : Filter ℕ) (𝓝 (Phi (b / σ) - Phi (a / σ))) := by
  have hdiv : ∀ y : ℝ, Tendsto (fun m => y / (c m * √(L m : ℝ))) (hyperfilter ℕ : Filter ℕ)
      (𝓝 (y / σ)) := fun y => tendsto_const_nhds.div hcL hσ.ne'
  have hL1 := hL 1
  -- `P(cS ≤ y) = Fn L (y / (c √L))`
  have hle : ∀ y : ℝ, ∀ᶠ m in (hyperfilter ℕ : Filter ℕ),
      probU (L m) (fun ω => c m * blockSum ω 0 (L m) ≤ y) = Fn (L m) (y / (c m * √(L m : ℝ))) := by
    intro y
    filter_upwards [hL1, hc] with m hm hcm
    have h1 : (fun ω => c m * blockSum ω 0 (L m) ≤ y) = fun ω => blockSum ω 0 (L m) ≤ y / c m := by
      funext ω; apply propext; rw [le_div_iff₀ hcm, mul_comm]
    rw [h1, probU_blockSum_le _ hm, div_div]
  have hup : ∀ y : ℝ, Tendsto (fun m => probU (L m) (fun ω => c m * blockSum ω 0 (L m) ≤ y))
      (hyperfilter ℕ : Filter ℕ) (𝓝 (Phi (y / σ))) := fun y =>
    (tendsto_Fn hL (hdiv y)).congr' (by filter_upwards [hle y] with m hm using hm.symm)
  -- `P(cS < a) → Φ(a/σ)` by a squeeze
  have hlt : Tendsto (fun m => probU (L m) (fun ω => c m * blockSum ω 0 (L m) < a))
      (hyperfilter ℕ : Filter ℕ) (𝓝 (Phi (a / σ))) := by
    rw [tendsto_order]
    constructor
    · intro r hr
      set δ := (Phi (a / σ) - r) / 2 with hδ
      have hδpos : 0 < δ := by rw [hδ]; linarith
      have hlow : Tendsto (fun m => Fn (L m) (a / (c m * √(L m : ℝ)) - δ))
          (hyperfilter ℕ : Filter ℕ) (𝓝 (Phi (a / σ - δ))) :=
        tendsto_Fn hL ((hdiv a).sub_const δ)
      have hΦ : Phi (a / σ) - δ ≤ Phi (a / σ - δ) := by
        have := Phi_lipschitz (a / σ - δ) (a / σ)
        rw [abs_le] at this
        have h2 : |a / σ - (a / σ - δ)| = δ := by rw [sub_sub_cancel, abs_of_pos hδpos]
        rw [h2] at this; linarith [this.2]
      have hr' : r < Phi (a / σ - δ) := by rw [hδ] at hΦ ⊢; linarith
      filter_upwards [(tendsto_order.1 hlow).1 r hr', hL1, hc] with m hm hm1 hcm
      refine lt_of_lt_of_le hm ?_
      have hcs : 0 < c m * √(L m : ℝ) := mul_pos hcm (by positivity)
      have h1 := probU_blockSum_le (L m) hm1 ((a / (c m * √(L m : ℝ)) - δ) * √(L m : ℝ))
      rw [mul_div_cancel_right₀ _ (by positivity : √(L m : ℝ) ≠ 0)] at h1
      rw [← h1]
      refine probU_mono _ fun ω hω => ?_
      have : (a / (c m * √(L m : ℝ)) - δ) * √(L m : ℝ) < a / c m := by
        have e : a / (c m * √(L m : ℝ)) * √(L m : ℝ) = a / c m := by
          field_simp
        nlinarith [show 0 < √(L m : ℝ) by positivity]
      have h3 : blockSum ω 0 (L m) < a / c m := lt_of_le_of_lt hω this
      rwa [lt_div_iff₀ hcm, mul_comm] at h3
    · intro r hr
      filter_upwards [(tendsto_order.1 (hup a)).2 r hr] with m hm
      exact lt_of_le_of_lt (probU_mono _ fun ω hω => hω.le) hm
  have heq : ∀ m, probU (L m) (fun ω => a ≤ c m * blockSum ω 0 (L m) ∧
      c m * blockSum ω 0 (L m) ≤ b) = probU (L m) (fun ω => c m * blockSum ω 0 (L m) ≤ b) -
        probU (L m) (fun ω => c m * blockSum ω 0 (L m) < a) := by
    intro m
    rw [probU_add_not (L m) (fun ω => c m * blockSum ω 0 (L m) ≤ b)
      (fun ω => c m * blockSum ω 0 (L m) < a)]
    have e1 : (fun ω => c m * blockSum ω 0 (L m) ≤ b ∧ c m * blockSum ω 0 (L m) < a) =
        fun ω => c m * blockSum ω 0 (L m) < a := by
      funext ω; apply propext
      exact ⟨fun h => h.2, fun h => ⟨by linarith, h⟩⟩
    have e2 : (fun ω => c m * blockSum ω 0 (L m) ≤ b ∧ ¬ c m * blockSum ω 0 (L m) < a) =
        fun ω => a ≤ c m * blockSum ω 0 (L m) ∧ c m * blockSum ω 0 (L m) ≤ b := by
      funext ω; apply propext; rw [not_lt]; exact And.comm
    rw [e1, e2]; ring
  simp_rw [heq]
  exact (hup b).sub hlt

/-- The Gaussian measure of an interval, `N(0,τ)[a,b] = Φ(b/√τ) - Φ(a/√τ)`. -/
theorem gaussianReal_Icc {τ : ℝ≥0} (hτ : τ ≠ 0) {a b : ℝ} (hab : a ≤ b) :
    gaussianReal 0 τ (Icc a b) = ENNReal.ofReal (Phi (b / √(τ : ℝ)) - Phi (a / √(τ : ℝ))) := by
  have hs : 0 < √(τ : ℝ) := Real.sqrt_pos.2 (by positivity)
  have hmap : (gaussianReal 0 1).map (fun x => √(τ : ℝ) * x) = gaussianReal 0 τ := by
    rw [gaussianReal_map_const_mul, mul_zero]
    congr 1
    ext; simp
  rw [← hmap, Measure.map_apply (measurable_const_mul _) measurableSet_Icc]
  have hpre : (fun x => √(τ : ℝ) * x) ⁻¹' Icc a b = Icc (a / √(τ : ℝ)) (b / √(τ : ℝ)) := by
    ext x
    simp only [Set.mem_preimage, Set.mem_Icc]
    rw [div_le_iff₀ hs, le_div_iff₀ hs]
    simp only [mul_comm x]
  rw [hpre, gaussianReal_apply_eq_integral 0 one_ne_zero, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (div_le_div_of_nonneg_right hab hs.le), Phi_sub]
  congr 1
  refine intervalIntegral.integral_congr fun u _ => ?_
  simp only [gaussianPDFReal, gd, NNReal.coe_one, mul_one, sub_zero]
  ring

end WalkCLT

/-! ## Standard parts as random variables -/

section StdPartRV

open ProbabilityTheory

theorem measurable_ifun {β : Type*} (F : ℕ → α → β) : Measurable (ifun F) :=
  measurable_generateFrom fun _ hS => ((show IsInternal _ from hS).preimage F).measurableSet

/-- `ℝ* = Ult ℝ` carries the Loeb σ-algebra. -/
instance hyperrealMeasurableSpace : MeasurableSpace ℝ* := loebMeasurableSpace (α := ℝ)

theorem mem_stInv_univ_iff (x : ℝ*) : x ∈ stInv (univ : Set ℝ) ↔ IsFinite x := by
  constructor
  · rintro ⟨y, -, hy⟩
    have h1 : IsInfinitesimal (x - (y : ℝ*)) := (near_real_iff x (y : ℝ*)).1 hy
    have : x = (x - (y : ℝ*)) + (y : ℝ*) := by ring
    rw [this]; exact h1.isFinite.add (coe_isFinite y)
  · intro hx
    exact ⟨stdPart x, Set.mem_univ _, (near_real_iff x _).2 (isInfinitesimal_sub_stdPart hx)⟩

theorem stdPart_eq_of_near {x : ℝ*} {y : ℝ} (h : Near (X := ℝ) x (Germ.const y)) :
    stdPart x = y :=
  stdPart_unique ((near_real_iff x (y : ℝ*)).1 h)

theorem stdPart_of_not_isFinite {x : ℝ*} (hx : ¬ IsFinite x) : stdPart x = 0 := by
  refine stdPart_eq_zero.2 fun h => hx ?_
  show 0 ≤ ArchimedeanClass.mk x
  rw [h]

theorem stdPart_mem_iff {x : ℝ*} (hx : IsFinite x) (E : Set ℝ) :
    stdPart x ∈ E ↔ x ∈ stInv E := by
  constructor
  · intro h
    exact ⟨stdPart x, h, (near_real_iff x _).2 (isInfinitesimal_sub_stdPart hx)⟩
  · rintro ⟨y, hy, hxy⟩
    rwa [stdPart_eq_of_near hxy]

/-- The standard part `ℝ* → ℝ` is measurable for the Loeb σ-algebra. -/
theorem measurable_stdPart : Measurable (fun x : ℝ* => stdPart x) := by
  intro E hE
  have hpre : (fun x : ℝ* => stdPart x) ⁻¹' E =
      (stInv E : Set ℝ*) ∪ ({_x : ℝ* | (0 : ℝ) ∈ E} ∩ (stInv (univ : Set ℝ) : Set ℝ*)ᶜ) := by
    ext x
    show stdPart x ∈ E ↔ x ∈ stInv E ∨ ((0 : ℝ) ∈ E ∧ x ∉ stInv (univ : Set ℝ))
    by_cases hx : IsFinite x
    · have hn := (mem_stInv_univ_iff x).2 hx
      rw [stdPart_mem_iff hx]
      constructor
      · intro h; exact Or.inl h
      · rintro (h | ⟨-, h⟩)
        · exact h
        · exact absurd hn h
    · rw [stdPart_of_not_isFinite hx]
      have hn : x ∉ stInv (univ : Set ℝ) := fun h => hx ((mem_stInv_univ_iff x).1 h)
      constructor
      · intro h0; exact Or.inr ⟨h0, hn⟩
      · rintro (h | ⟨h0, -⟩)
        · exact absurd (stInv_mono (Set.subset_univ E) h) hn
        · exact h0
  by_cases h0 : (0 : ℝ) ∈ E
  · have : (fun x : ℝ* => stdPart x) ⁻¹' E =
        (stInv E : Set ℝ*) ∪ (stInv (univ : Set ℝ) : Set ℝ*)ᶜ := by
      rw [hpre]; ext x
      exact ⟨fun h => h.elim Or.inl (fun h' => Or.inr h'.2), fun h => h.elim Or.inl
        (fun h' => Or.inr ⟨h0, h'⟩)⟩
    rw [this]
    exact (measurableSet_stInv hE).union (measurableSet_stInv (X := ℝ) MeasurableSet.univ).compl
  · have : (fun x : ℝ* => stdPart x) ⁻¹' E = (stInv E : Set ℝ*) := by
      rw [hpre]; ext x
      exact ⟨fun h => h.elim id (fun h' => absurd h'.1 h0), Or.inl⟩
    rw [this]
    exact measurableSet_stInv hE

theorem measurable_coordG {d : ℕ} (i : Fin d) : Measurable (coordG (d := d) i) := by
  have : coordG (d := d) i = ifun (fun _ (v : Fin d → ℝ) => v i) := by
    funext y; obtain ⟨v, rfl⟩ := exists_rep y; rfl
  rw [this]; exact measurable_ifun _

/-- The coordinatewise standard part of a vector of hyperreals. -/
def stVec {d : ℕ} (x : Ult (Fin d → ℝ)) : Fin d → ℝ := fun i => stdPart (coordG i x)

theorem measurable_stVec {d : ℕ} : Measurable (stVec (d := d)) :=
  Measurable.of_eval fun i => measurable_stdPart.comp (measurable_coordG i)

theorem stVec_eq_of_near {d : ℕ} {x : Ult (Fin d → ℝ)} {y : Fin d → ℝ}
    (h : Near x (Germ.const y)) : stVec x = y := by
  funext i
  obtain ⟨u, rfl⟩ := exists_rep x
  refine stdPart_unique ?_
  rw [show (Germ.const y : Ult (Fin d → ℝ)) = ((fun _ => y : ℕ → Fin d → ℝ) : Ult _) from rfl,
    near_coe_iff] at h
  show IsInfinitesimal (Hyperreal.ofSeq (fun m => u m i - y i))
  rw [isInfinitesimal_ofSeq_iff]
  intro r hr
  filter_upwards [h r hr] with m hm
  have := (dist_le_pi_dist (u m) y i).trans_lt hm
  rwa [Real.dist_eq] at this

/-- If `μ` is a finite measure carried by the near-standard points, the law of the
coordinatewise standard part is the push-forward `stMeasure μ`. -/
theorem map_stVec_eq {d : ℕ} (μ : Measure (Ult (Fin d → ℝ)))
    (hns : μ (stInv (univ : Set (Fin d → ℝ)))ᶜ = 0) : μ.map stVec = stMeasure μ := by
  ext E hE
  rw [Measure.map_apply measurable_stVec hE, stMeasure_apply _ hE]
  refine measure_congr ?_
  have hns' : ∀ᵐ x ∂μ, x ∈ stInv (univ : Set (Fin d → ℝ)) := by
    rw [ae_iff]; exact hns
  filter_upwards [hns'] with x hx
  obtain ⟨y, -, hxy⟩ := hx
  show (x ∈ stVec ⁻¹' E) = (x ∈ stInv E)
  apply propext
  rw [Set.mem_preimage, stVec_eq_of_near hxy]
  constructor
  · intro hy; exact ⟨y, hy, hxy⟩
  · rintro ⟨y', hy', hxy'⟩; rwa [near_const_unique hxy hxy']

/-- **Shadow criterion for product measures** on `ℝⁿ`. -/
theorem stMeasure_eq_pi {d : ℕ} (μ : Measure (Ult (Fin d → ℝ))) (lam : Fin d → Measure ℝ)
    [∀ i, IsFiniteMeasure (lam i)]
    (h : ∀ a b : Fin d → ℝ, a ≤ b → μ (starSet (Icc a b)) = ∏ i, lam i (Icc (a i) (b i))) :
    stMeasure μ = Measure.pi lam := by
  have hpiIcc : ∀ a b : Fin d → ℝ, Measure.pi lam (Icc a b) = ∏ i, lam i (Icc (a i) (b i)) := by
    intro a b; rw [← Set.pi_univ_Icc, Measure.pi_pi]
  have hbox : ∀ a b : Fin d → ℝ, a ≤ b → stMeasure μ (Icc a b) = Measure.pi lam (Icc a b) := by
    intro a b hab
    rw [stMeasure_apply μ measurableSet_Icc]
    let c : ℕ → Fin d → ℝ := fun m _ => 1 / ((m : ℝ) + 1)
    refine measure_stInv_eq_of_iInter μ (Measure.pi lam) (F := fun m => Icc (a - c m) (b + c m))
      (fun m => isClosed_Icc) (Metric.isBounded_Icc _ _) ?_ ?_ ?_
      (by rw [hpiIcc]; exact (ENNReal.prod_lt_top fun i _ => measure_lt_top _ _).ne)
      (fun m => by
        rw [h _ _ (fun i => by
          have hi : a i ≤ b i := hab i
          have := one_div_succ_pos m
          simp only [c, Pi.sub_apply, Pi.add_apply]
          linarith), hpiIcc])
    · intro m y hy
      refine ⟨1 / ((m : ℝ) + 1), one_div_succ_pos m, fun z hz => ?_⟩
      rw [Metric.mem_ball] at hz
      have hzi : ∀ i, |z i - y i| < 1 / ((m : ℝ) + 1) := fun i => by
        have := (dist_le_pi_dist z y i).trans_lt hz; rwa [Real.dist_eq] at this
      refine ⟨fun i => ?_, fun i => ?_⟩
      · have := abs_lt.1 (hzi i)
        simp only [c, Pi.sub_apply]; linarith [hy.1 i]
      · have := abs_lt.1 (hzi i)
        simp only [c, Pi.add_apply]; linarith [hy.2 i]
    · ext z; simp only [Set.mem_iInter, Set.mem_Icc]
      constructor
      · intro hz
        refine ⟨fun i => ?_, fun i => ?_⟩
        · by_contra hc; push Not at hc
          obtain ⟨m, hm⟩ := exists_nat_one_div_lt (sub_pos.2 hc)
          have := (hz m).1 i; simp only [c, Pi.sub_apply] at this; linarith
        · by_contra hc; push Not at hc
          obtain ⟨m, hm⟩ := exists_nat_one_div_lt (sub_pos.2 hc)
          have := (hz m).2 i; simp only [c, Pi.add_apply] at this; linarith
      · intro hz m
        refine ⟨fun i => ?_, fun i => ?_⟩
        · simp only [c, Pi.sub_apply]; linarith [hz.1 i, one_div_succ_pos m]
        · simp only [c, Pi.add_apply]; linarith [hz.2 i, one_div_succ_pos m]
    · intro i j hij z hz
      have := one_div_succ_anti hij
      refine ⟨fun k => ?_, fun k => ?_⟩
      · have h1 := hz.1 k; simp only [c, Pi.sub_apply] at h1 ⊢; linarith
      · have h1 := hz.2 k; simp only [c, Pi.add_apply] at h1 ⊢; linarith
  symm
  refine Measure.pi_eq_generateFrom (C := fun _ => {S : Set ℝ | ∃ l u, l ≤ u ∧ Icc l u = S})
    (fun i => (borel_eq_generateFrom_Icc ℝ).symm.trans BorelSpace.measurable_eq.symm)
    (fun i => by simpa using isPiSystem_Icc (id : ℝ → ℝ) id) (fun i => ?_) ?_
  · exact
      { set := fun n => Icc (-(n : ℝ)) n
        set_mem := fun n => ⟨-(n : ℝ), n, by linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)], rfl⟩
        finite := fun n => measure_lt_top _ _
        spanning := by
          ext x; simp only [Set.mem_iUnion, Set.mem_Icc, Set.mem_univ, iff_true]
          obtain ⟨n, hn⟩ := exists_nat_ge |x|
          exact ⟨n, by linarith [neg_abs_le x], by linarith [le_abs_self x]⟩ }
  · intro s hs
    choose l u hlu hs' using hs
    have hpi : Set.pi univ s = Icc l u := by
      rw [← Set.pi_univ_Icc]; congr; funext i; exact (hs' i).symm
    rw [hpi, hbox l u hlu, hpiIcc]
    congr 1; funext i; rw [← hs' i]

end StdPartRV

/-! ## Anderson's random walk on the hyperfinite coin space -/

section AndersonWalk

open QE.Prob QE.Prob.BE ProbabilityTheory
open scoped NNReal

open Classical in
/-- The hyperfinite coin space `Ξ = {±1}^n`, `n = [n m]`. -/
def coinSet (n : ℕ → ℕ) (m : ℕ) : Finset (ℕ → Bool) := Finset.univ.image (coinExt (n m))

/-- The uniform probability on the coin space. -/
def coinMeasure (n : ℕ → ℕ) : HypMeasure (ℕ → Bool) := HypMeasure.counting (coinSet n)

theorem card_coinSet (n : ℕ → ℕ) (m : ℕ) : (coinSet n m).card = 2 ^ n m := by
  classical
  rw [coinSet, Finset.card_image_of_injective _ (coinExt_injective _), Finset.card_univ,
    Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]

theorem coin_seqMass (n : ℕ → ℕ) (B : ℕ → Set (ℕ → Bool)) (m : ℕ) :
    (coinMeasure n).seqMass B m = probU (n m) (· ∈ B m) := by
  classical
  unfold HypMeasure.seqMass probU
  simp only [coinMeasure, HypMeasure.counting]
  rw [Finset.sum_const, nsmul_eq_mul, card_coinSet]
  have hc : (@Finset.filter _ (· ∈ B m) (Classical.decPred _) (coinSet n m)).card =
      ∑ ω : Fin (n m) → Bool, if coinExt (n m) ω ∈ B m then (1 : ℝ) else 0 := by
    rw [Finset.sum_boole]
    unfold coinSet
    rw [Finset.filter_image, Finset.card_image_of_injective _ (coinExt_injective _)]
  rw [hc]; push_cast; ring

theorem coinMeasure_isProbability (n : ℕ → ℕ) : IsProbabilityMeasure (coinMeasure n).loeb := by
  classical
  refine HypMeasure.isProbabilityMeasure_loeb_counting _ ((internal_nonempty_iff _).2 ?_)
  refine Eventually.of_forall fun m => ⟨coinExt (n m) (fun _ => true), Finset.mem_coe.2 ?_⟩
  unfold coinSet
  exact Finset.mem_image.2 ⟨_, Finset.mem_univ _, rfl⟩

/-- The index `k = ⌊t/Δt⌋` of the time cell `[t_k, t_{k+1})` containing `t`, `Δt = T/N`. -/
def walkIdx (T : ℝ) (N : ℕ) (t : ℝ) : ℕ := ⌊t / (T / N)⌋₊

/-- The `m`-th coordinate of the Anderson walk: `W(t) = √Δt · ∑_{j<k} ξ_j`, `k = ⌊t/Δt⌋`. -/
def walkSeq (T : ℝ) (n : ℕ → ℕ) (t : ℝ) (m : ℕ) (ω : ℕ → Bool) : ℝ :=
  √(T / n m) * blockSum ω 0 (walkIdx T (n m) t)

/-- **Anderson's walk** `W(t, ω) ∈ ℝ*` on the hyperfinite coin space, `Δt = T/n`. -/
def andersonW (T : ℝ) (n : ℕ → ℕ) (t : ℝ) (ω : Ult (ℕ → Bool)) : ℝ* := ifun (walkSeq T n t) ω

/-- Its standard part `b(t, ω) = st W(t, ω)`. -/
def andersonB (T : ℝ) (n : ℕ → ℕ) (t : ℝ) (ω : Ult (ℕ → Bool)) : ℝ := stdPart (andersonW T n t ω)

theorem walkIdx_zero (T : ℝ) (N : ℕ) : walkIdx T N 0 = 0 := by simp [walkIdx]

theorem walkIdx_mono {T : ℝ} (hT : 0 < T) (N : ℕ) {s t : ℝ} (hst : s ≤ t) :
    walkIdx T N s ≤ walkIdx T N t :=
  Nat.floor_mono (div_le_div_of_nonneg_right hst (by positivity))

theorem walkIdx_le {T : ℝ} (hT : 0 < T) {N : ℕ} (hN : 0 < N) {t : ℝ} (ht : t ≤ T) :
    walkIdx T N t ≤ N := by
  unfold walkIdx
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  refine Nat.floor_le_of_le ?_
  rw [div_div_eq_mul_div, div_le_iff₀ hT]
  nlinarith

theorem walkIdx_bounds {T : ℝ} (hT : 0 < T) {N : ℕ} (hN : 0 < N) {t : ℝ} (ht : 0 ≤ t) :
    t - T / N < walkIdx T N t * (T / N) ∧ walkIdx T N t * (T / N) ≤ t := by
  have hd : 0 < T / N := by positivity
  have h1 := Nat.floor_le (div_nonneg ht hd.le)
  have h2 := Nat.lt_floor_add_one (t / (T / N))
  unfold walkIdx
  constructor
  · have := mul_lt_mul_of_pos_right h2 hd
    rw [div_mul_cancel₀ _ hd.ne', add_mul, one_mul] at this
    linarith
  · have := mul_le_mul_of_nonneg_right h1 hd.le
    rwa [div_mul_cancel₀ _ hd.ne'] at this

theorem andersonW_zero (T : ℝ) (n : ℕ → ℕ) (ω : Ult (ℕ → Bool)) : andersonW T n 0 ω = 0 := by
  obtain ⟨u, rfl⟩ := exists_rep ω
  unfold andersonW
  rw [ifun_coe]
  show Hyperreal.ofSeq _ = Hyperreal.ofSeq (fun _ => 0)
  congr 1; funext m
  simp [walkSeq, walkIdx_zero, blockSum]

theorem andersonB_zero (T : ℝ) (n : ℕ → ℕ) (ω : Ult (ℕ → Bool)) : andersonB T n 0 ω = 0 := by
  rw [andersonB, andersonW_zero]
  exact stdPart_of_infinitesimal isInfinitesimal_zero

theorem measurable_andersonW (T : ℝ) (n : ℕ → ℕ) (t : ℝ) : Measurable (andersonW T n t) :=
  measurable_ifun _

theorem measurable_andersonB (T : ℝ) (n : ℕ → ℕ) (t : ℝ) : Measurable (andersonB T n t) :=
  measurable_stdPart.comp (measurable_andersonW T n t)

theorem tendsto_dt {T : ℝ} {n : ℕ → ℕ} (hn : IsUnlimited ((n : ℕ → ℕ) : Ult ℕ)) :
    Tendsto (fun m => T / (n m : ℝ)) (hyperfilter ℕ : Filter ℕ) (𝓝 0) := by
  have := (tendsto_inv_of_isUnlimited hn).const_mul T
  simpa [div_eq_mul_inv] using this

/-- The vector of increments `(W(t_{i+1}) - W(t_i))_i`, coordinatewise. -/
def incrSeq (T : ℝ) (n : ℕ → ℕ) {M : ℕ} (t : Fin (M + 1) → ℝ≥0) (m : ℕ) (ω : ℕ → Bool) :
    Fin M → ℝ :=
  fun i => walkSeq T n (t i.succ) m ω - walkSeq T n (t i.castSucc) m ω

open Classical in
theorem probU_zero (P : (ℕ → Bool) → Prop) (hP : ∀ ω ω', P ω ↔ P ω') (ω₀ : ℕ → Bool) :
    probU 0 P = if P ω₀ then 1 else 0 := by
  classical
  unfold probU
  simp only [pow_zero, div_one, Fintype.sum_unique]
  by_cases h : P ω₀
  · rw [ite_eq_left ((hP _ _).2 h), ite_eq_left h]
  · rw [ite_eq_right (fun h' => h ((hP _ _).1 h')), ite_eq_right h]

/-- The limit law of one increment: `P(a ≤ √Δt S_{block} ≤ b) → N(0, u - s)[a,b]`. -/
theorem tendsto_block_prob {T : ℝ} (hT : 0 < T) {n : ℕ → ℕ}
    (hn : IsUnlimited ((n : ℕ → ℕ) : Ult ℕ)) {s u : ℝ≥0} (hsu : s ≤ u) (huT : (u : ℝ) ≤ T)
    {a b : ℝ} (hab : a ≤ b) :
    Tendsto (fun m => probU (n m) (fun ω =>
        a ≤ √(T / n m) * blockSum ω (walkIdx T (n m) s) (walkIdx T (n m) u) ∧
        √(T / n m) * blockSum ω (walkIdx T (n m) s) (walkIdx T (n m) u) ≤ b))
      (hyperfilter ℕ : Filter ℕ) (𝓝 ((gaussianReal 0 (u - s) (Icc a b)).toReal)) := by
  have hpos : ∀ᶠ m in (hyperfilter ℕ : Filter ℕ), 0 < n m := Germ.coe_lt.1 (hn 0)
  have hsu' : (s : ℝ) ≤ u := by exact_mod_cast hsu
  set L : ℕ → ℕ := fun m => walkIdx T (n m) u - walkIdx T (n m) s with hLdef
  have hKL : ∀ m, walkIdx T (n m) u = walkIdx T (n m) s + L m := fun m => by
    rw [hLdef]; exact (Nat.add_sub_cancel' (walkIdx_mono hT _ hsu')).symm
  have hblock : ∀ᶠ m in (hyperfilter ℕ : Filter ℕ), probU (n m) (fun ω =>
        a ≤ √(T / n m) * blockSum ω (walkIdx T (n m) s) (walkIdx T (n m) u) ∧
        √(T / n m) * blockSum ω (walkIdx T (n m) s) (walkIdx T (n m) u) ≤ b) =
      probU (L m) (fun ω => a ≤ √(T / n m) * blockSum ω 0 (L m) ∧
        √(T / n m) * blockSum ω 0 (L m) ≤ b) := by
    filter_upwards [hpos] with m hm
    have hle : walkIdx T (n m) s + L m ≤ n m := by rw [← hKL]; exact walkIdx_le hT hm huT
    rw [hKL m]
    exact probU_block (n m) _ (L m) hle (fun x => a ≤ √(T / n m) * x ∧ √(T / n m) * x ≤ b)
  refine Tendsto.congr' (EventuallyEq.symm hblock) ?_
  rcases eq_or_lt_of_le hsu with hsu0 | hlt
  · -- equal times: the increment vanishes
    subst hsu0
    have hL0 : ∀ m, L m = 0 := fun m => by simp [hLdef]
    rw [tsub_self, gaussianReal_zero_var, Measure.dirac_apply' _ measurableSet_Icc]
    refine tendsto_const_nhds.congr' (Eventually.of_forall fun m => ?_)
    simp only
    rw [hL0 m, probU_zero _ (fun _ _ => by simp [blockSum]) (fun _ => false)]
    simp only [blockSum, Finset.Ico_self, Finset.sum_empty, mul_zero]
    by_cases h : a ≤ 0 ∧ 0 ≤ b
    · rw [ite_eq_left h, Set.indicator_of_mem (show (0 : ℝ) ∈ Icc a b from h)]; simp
    · rw [ite_eq_right h, Set.indicator_of_notMem (show (0 : ℝ) ∉ Icc a b from h)]; simp
  · set τ : ℝ≥0 := u - s with hτ
    have hτpos : (0 : ℝ) < τ := by
      rw [hτ, NNReal.coe_sub hsu]; exact sub_pos.2 (by exact_mod_cast hlt)
    have hτ0 : τ ≠ 0 := fun h => by rw [h] at hτpos; exact lt_irrefl _ hτpos
    have hdt := tendsto_dt (T := T) hn
    -- `L Δt → τ`
    have hLdt : Tendsto (fun m => (L m : ℝ) * (T / n m)) (hyperfilter ℕ : Filter ℕ) (𝓝 τ) := by
      refine tendsto_of_abs_sub_le (g := fun m => 2 * (T / n m)) (by simpa using hdt.const_mul 2) ?_
      filter_upwards [hpos] with m hm
      have hu := walkIdx_bounds hT hm (NNReal.coe_nonneg u)
      have hs := walkIdx_bounds hT hm (NNReal.coe_nonneg s)
      have hcast : (L m : ℝ) = (walkIdx T (n m) u : ℝ) - walkIdx T (n m) s := by
        rw [hLdef]; simp only
        rw [Nat.cast_sub (walkIdx_mono hT _ hsu')]
      have hd : 0 < T / (n m : ℝ) := by positivity
      rw [hcast, sub_mul, hτ, NNReal.coe_sub hsu, abs_le]
      constructor <;> linarith [hu.1, hu.2, hs.1, hs.2]
    have hLinf : ∀ k : ℕ, ∀ᶠ m in (hyperfilter ℕ : Filter ℕ), k ≤ L m := by
      intro k
      have h1 := (tendsto_order.1 hLdt).1 ((τ : ℝ) / 2) (by linarith)
      have h2 := (tendsto_order.1 hdt).2 ((τ : ℝ) / (2 * ((k : ℝ) + 1))) (by positivity)
      filter_upwards [h1, h2, hpos] with m hm1 hm2 hm3
      have hd : 0 < T / (n m : ℝ) := by positivity
      by_contra hc; push Not at hc
      have hc' : (L m : ℝ) ≤ k := by exact_mod_cast hc.le
      have : (L m : ℝ) * (T / n m) ≤ k * ((τ : ℝ) / (2 * ((k : ℝ) + 1))) :=
        mul_le_mul hc' hm2.le hd.le (by positivity)
      have h3 : (k : ℝ) * ((τ : ℝ) / (2 * ((k : ℝ) + 1))) < (τ : ℝ) / 2 := by
        rw [mul_div_assoc', div_lt_div_iff₀ (by positivity) (by norm_num)]
        nlinarith
      linarith
    have hcL : Tendsto (fun m => √(T / n m) * √(L m : ℝ)) (hyperfilter ℕ : Filter ℕ)
        (𝓝 √(τ : ℝ)) := by
      have h1 := (Real.continuous_sqrt.tendsto _).comp hLdt
      refine h1.congr' (Eventually.of_forall fun m => ?_)
      simp only [Function.comp]
      rw [mul_comm, Real.sqrt_mul' _ (Nat.cast_nonneg _)]
    have hc : ∀ᶠ m in (hyperfilter ℕ : Filter ℕ), 0 < √(T / n m) := by
      filter_upwards [hpos] with m hm
      exact Real.sqrt_pos.2 (by positivity)
    have := tendsto_probU_Icc (Real.sqrt_pos.2 hτpos) hc hLinf hcL hab
    rw [gaussianReal_Icc hτ0 hab, ENNReal.toReal_ofReal (sub_nonneg.2 (Phi_mono
      (div_le_div_of_nonneg_right hab (Real.sqrt_nonneg _))))]
    exact this

/-- **The joint law of the increments**, level by level and along the ultrafilter. -/
theorem tendsto_incr_prob {T : ℝ} (hT : 0 < T) {n : ℕ → ℕ}
    (hn : IsUnlimited ((n : ℕ → ℕ) : Ult ℕ)) {M : ℕ} (t : Fin (M + 1) → ℝ≥0) (ht : Monotone t)
    (htT : ∀ i, (t i : ℝ) ≤ T) (a b : Fin M → ℝ) :
    Tendsto (fun m => probU (n m) (fun ω => incrSeq T n t m ω ∈ Icc a b))
      (hyperfilter ℕ : Filter ℕ)
      (𝓝 (∏ i, (gaussianReal 0 (t i.succ - t i.castSucc) (Icc (a i) (b i))).toReal)) := by
  by_cases hab : a ≤ b
  · have hpos : ∀ᶠ m in (hyperfilter ℕ : Filter ℕ), 0 < n m := Germ.coe_lt.1 (hn 0)
    have hfac : ∀ᶠ m in (hyperfilter ℕ : Filter ℕ),
        probU (n m) (fun ω => incrSeq T n t m ω ∈ Icc a b) = ∏ i, probU (n m) (fun ω =>
          a i ≤ √(T / n m) * blockSum ω (walkIdx T (n m) (t i.castSucc))
            (walkIdx T (n m) (t i.succ)) ∧
          √(T / n m) * blockSum ω (walkIdx T (n m) (t i.castSucc))
            (walkIdx T (n m) (t i.succ)) ≤ b i) := by
      filter_upwards [hpos] with m hm
      let tj : ℕ → ℝ≥0 := fun j => t ⟨min j M, by omega⟩
      let Kn : ℕ → ℕ := fun j => walkIdx T (n m) (tj j)
      have hKn : Monotone Kn := by
        intro j j' hjj'
        refine walkIdx_mono hT _ ?_
        have : tj j ≤ tj j' := ht (Fin.mk_le_mk.2 (min_le_min_right M hjj'))
        exact_mod_cast this
      let En : ℕ → (ℕ → Bool) → Prop := fun j ω => if h : j < M then
        (a ⟨j, h⟩ ≤ √(T / n m) * blockSum ω (Kn j) (Kn (j + 1)) ∧
          √(T / n m) * blockSum ω (Kn j) (Kn (j + 1)) ≤ b ⟨j, h⟩) else True
      have hE : ∀ j ω ω', (∀ i, Kn j ≤ i → i < Kn (j + 1) → ω i = ω' i) → (En j ω ↔ En j ω') := by
        intro j ω ω' hω
        simp only [En]
        split_ifs
        · rw [blockSum_congr hω]
        · exact Iff.rfl
      have hKM : Kn M ≤ n m := walkIdx_le hT hm (htT _)
      have hcs : ∀ i : Fin M, Kn i = walkIdx T (n m) (t i.castSucc) := fun i => by
        simp only [Kn, tj]; congr 3; ext; simp
      have hsu : ∀ i : Fin M, Kn (i + 1) = walkIdx T (n m) (t i.succ) := fun i => by
        simp only [Kn, tj]; congr 3; ext; simp
      have hev : (fun ω => incrSeq T n t m ω ∈ Icc a b) = fun ω => ∀ j < M, En j ω := by
        funext ω; apply propext
        simp only [Set.mem_Icc, Pi.le_def, En]
        constructor
        · rintro ⟨h1, h2⟩ j hj
          rw [dite_eq_left hj]
          have e := hcs ⟨j, hj⟩; have e' := hsu ⟨j, hj⟩
          simp only at e e'
          have hle := walkIdx_mono hT (n m) (show ((t (Fin.castSucc ⟨j, hj⟩) : ℝ)) ≤
            t (Fin.succ ⟨j, hj⟩) by exact_mod_cast ht (Fin.castSucc_le_succ _))
          have hinc : incrSeq T n t m ω ⟨j, hj⟩ =
              √(T / n m) * blockSum ω (Kn j) (Kn (j + 1)) := by
            simp only [incrSeq, walkSeq]
            rw [e, e', ← blockSum_add (Nat.zero_le _) hle]; ring
          rw [← hinc]; exact ⟨h1 _, h2 _⟩
        · intro h
          refine ⟨fun i => ?_, fun i => ?_⟩
          all_goals
            have hi := h i i.isLt
            rw [dite_eq_left i.isLt] at hi
            have e := hcs i; have e' := hsu i
            have hle := walkIdx_mono hT (n m) (show ((t i.castSucc : ℝ)) ≤ t i.succ by
              exact_mod_cast ht (Fin.castSucc_le_succ _))
            have hinc : incrSeq T n t m ω i = √(T / n m) * blockSum ω (Kn i) (Kn (i + 1)) := by
              simp only [incrSeq, walkSeq]
              rw [e, e', ← blockSum_add (Nat.zero_le _) hle]; ring
          · rw [hinc]; exact hi.1
          · rw [hinc]; exact hi.2
      rw [hev, probU_forall_lt (n m) Kn hKn En hE M hKM, ← Fin.prod_univ_eq_prod_range]
      refine Finset.prod_congr rfl fun i _ => ?_
      congr 1; funext ω
      simp only [En, dite_eq_left i.isLt, Fin.eta, hcs i, hsu i]
    refine Tendsto.congr' (EventuallyEq.symm hfac) (tendsto_finsetProd _ fun i _ => ?_)
    exact tendsto_block_prob hT hn (ht (Fin.castSucc_le_succ i)) (htT _) (hab i)
  · -- an empty box
    have hne : ∃ i, b i < a i := by
      by_contra h; push Not at h; exact hab fun i => h i
    obtain ⟨i₀, hi₀⟩ := hne
    have h0 : ∏ i, (gaussianReal 0 (t i.succ - t i.castSucc) (Icc (a i) (b i))).toReal = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ i₀) (by rw [Set.Icc_eq_empty (not_le.2 hi₀)]; simp)
    rw [h0]
    refine tendsto_const_nhds.congr' (Eventually.of_forall fun m => ?_)
    have : (fun ω => incrSeq T n t m ω ∈ Icc a b) = fun _ => False := by
      funext ω; apply propext
      rw [Set.Icc_eq_empty hab]; simp
    simp only
    rw [this]
    unfold probU
    simp

theorem coordG_ifun_incrSeq (T : ℝ) (n : ℕ → ℕ) {M : ℕ} (t : Fin (M + 1) → ℝ≥0)
    (ω : Ult (ℕ → Bool)) (i : Fin M) :
    coordG i (ifun (incrSeq T n t) ω) = andersonW T n (t i.succ) ω - andersonW T n (t i.castSucc) ω := by
  obtain ⟨u, rfl⟩ := exists_rep ω
  rfl

theorem isInfinitesimal_coordG_sub_of_near {d : ℕ} {x : Ult (Fin d → ℝ)} {y : Fin d → ℝ}
    (h : Near x (Germ.const y)) (i : Fin d) : IsInfinitesimal (coordG i x - (y i : ℝ*)) := by
  obtain ⟨u, rfl⟩ := exists_rep x
  rw [show (Germ.const y : Ult (Fin d → ℝ)) = ((fun _ => y : ℕ → Fin d → ℝ) : Ult _) from rfl,
    near_coe_iff] at h
  show IsInfinitesimal (Hyperreal.ofSeq (fun m => u m i - y i))
  rw [isInfinitesimal_ofSeq_iff]
  intro r hr
  filter_upwards [h r hr] with m hm
  have := (dist_le_pi_dist (u m) y i).trans_lt hm
  rwa [Real.dist_eq] at this

/-- The image of the Loeb measure under the internal vector of increments, on a box. -/
theorem incr_loeb_box {T : ℝ} (hT : 0 < T) {n : ℕ → ℕ}
    (hn : IsUnlimited ((n : ℕ → ℕ) : Ult ℕ)) {M : ℕ} (t : Fin (M + 1) → ℝ≥0) (ht : Monotone t)
    (htT : ∀ i, (t i : ℝ) ≤ T) (a b : Fin M → ℝ) :
    ((coinMeasure n).loeb.map (ifun (incrSeq T n t))) (starSet (Icc a b)) =
      ∏ i, gaussianReal 0 (t i.succ - t i.castSucc) (Icc (a i) (b i)) := by
  rw [Measure.map_apply (measurable_ifun _) (measurableSet_starSet _), starSet,
    ifun_preimage_internal, HypMeasure.loeb_internal _ (isInternal_internal _),
    HypMeasure.mass_internal]
  have hseq : (coinMeasure n).seqMass (fun m => incrSeq T n t m ⁻¹' Icc a b) =
      fun m => probU (n m) (fun ω => incrSeq T n t m ω ∈ Icc a b) :=
    funext fun m => coin_seqMass n _ m
  show stE (Hyperreal.ofSeq _) = _
  rw [hseq, stE_ofSeq_of_tendsto (tendsto_incr_prob hT hn t ht htT a b),
    ENNReal.ofReal_prod_of_nonneg (fun i _ => ENNReal.toReal_nonneg)]
  congr 1; funext i
  exact ENNReal.ofReal_toReal (measure_ne_top _ _)

/-- **The law of the hyperfinite increments**: the standard part map pushes the image of the
Loeb measure forward to the product of the centred Gaussians `N(0, t_{i+1} - t_i)`. -/
theorem incr_stMeasure {T : ℝ} (hT : 0 < T) {n : ℕ → ℕ}
    (hn : IsUnlimited ((n : ℕ → ℕ) : Ult ℕ)) {M : ℕ} (t : Fin (M + 1) → ℝ≥0) (ht : Monotone t)
    (htT : ∀ i, (t i : ℝ) ≤ T) :
    stMeasure ((coinMeasure n).loeb.map (ifun (incrSeq T n t))) =
      Measure.pi fun i => gaussianReal 0 (t i.succ - t i.castSucc) :=
  stMeasure_eq_pi _ _ fun a b _ => incr_loeb_box hT hn t ht htT a b

theorem incr_ns_null {T : ℝ} (hT : 0 < T) {n : ℕ → ℕ}
    (hn : IsUnlimited ((n : ℕ → ℕ) : Ult ℕ)) {M : ℕ} (t : Fin (M + 1) → ℝ≥0) (ht : Monotone t)
    (htT : ∀ i, (t i : ℝ) ≤ T) :
    ((coinMeasure n).loeb.map (ifun (incrSeq T n t))) (stInv (univ : Set (Fin M → ℝ)))ᶜ = 0 := by
  have := coinMeasure_isProbability n
  rw [measure_compl (measurableSet_stInv MeasurableSet.univ) (measure_ne_top _ _),
    ← stMeasure_apply _ MeasurableSet.univ, incr_stMeasure hT hn t ht htT, measure_univ,
    measure_univ, tsub_self]

/-- `W(t)` is limited for Loeb-almost every path, `t ≤ T`. -/
theorem ae_isFinite_andersonW {T : ℝ} (hT : 0 < T) {n : ℕ → ℕ}
    (hn : IsUnlimited ((n : ℕ → ℕ) : Ult ℕ)) {t : ℝ≥0} (htT : (t : ℝ) ≤ T) :
    ∀ᵐ ω ∂(coinMeasure n).loeb, IsFinite (andersonW T n t ω) := by
  let tt : Fin 2 → ℝ≥0 := ![0, t]
  have htt : Monotone tt := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp [tt] at hij ⊢
  have httT : ∀ i, (tt i : ℝ) ≤ T := by
    intro i; fin_cases i
    · simp [tt]; exact hT.le
    · simpa [tt] using htT
  have h0 := incr_ns_null hT hn tt htt httT
  rw [Measure.map_apply (measurable_ifun _)
    (measurableSet_stInv MeasurableSet.univ).compl] at h0
  have hae : ∀ᵐ ω ∂(coinMeasure n).loeb, ifun (incrSeq T n tt) ω ∈ stInv (univ : Set (Fin 1 → ℝ)) := by
    rw [ae_iff]; exact h0
  filter_upwards [hae] with ω hω
  obtain ⟨y, -, hy⟩ := hω
  have h1 := isInfinitesimal_coordG_sub_of_near hy 0
  rw [coordG_ifun_incrSeq] at h1
  have e1 : tt (Fin.succ 0) = t := rfl
  have e0 : tt (Fin.castSucc 0) = 0 := rfl
  rw [e1, e0, NNReal.coe_zero, andersonW_zero, sub_zero] at h1
  have : andersonW T n t ω = (andersonW T n t ω - (y 0 : ℝ*)) + (y 0 : ℝ*) := by ring
  rw [this]; exact h1.isFinite.add (coe_isFinite _)

theorem isFinite_neg {x : ℝ*} (hx : IsFinite x) : IsFinite (-x) := by
  unfold IsFinite at *; rwa [ArchimedeanClass.mk_neg]

theorem stdPart_sub' {x y : ℝ*} (hx : IsFinite x) (hy : IsFinite y) :
    stdPart (x - y) = stdPart x - stdPart y := by
  refine stdPart_unique ?_
  have h := (isInfinitesimal_sub_stdPart hx).sub (isInfinitesimal_sub_stdPart hy)
  have e : x - y - ((stdPart x - stdPart y : ℝ) : ℝ*) =
      (x - (stdPart x : ℝ*)) - (y - (stdPart y : ℝ*)) := by
    rw [Hyperreal.coe_sub]; ring
  rw [e]; exact h

/-- **Finite-dimensional distributions of the Loeb shadow of Anderson's walk.** For standard
times `0 ≤ t₀ ≤ t₁ ≤ ⋯ ≤ t_M ≤ T`, the increments `b(t_{i+1}) - b(t_i)` of `b = st W` have,
jointly under the Loeb measure, the law `⊗ᵢ N(0, t_{i+1} - t_i)`. -/
theorem andersonB_increments_hasLaw {T : ℝ} (hT : 0 < T) {n : ℕ → ℕ}
    (hn : IsUnlimited ((n : ℕ → ℕ) : Ult ℕ)) {M : ℕ} (t : Fin (M + 1) → ℝ≥0) (ht : Monotone t)
    (htT : ∀ i, (t i : ℝ) ≤ T) :
    HasLaw (fun ω (i : Fin M) => andersonB T n (t i.succ) ω - andersonB T n (t i.castSucc) ω)
      (Measure.pi fun i => gaussianReal 0 (t i.succ - t i.castSucc)) (coinMeasure n).loeb := by
  have hfin : ∀ᵐ ω ∂(coinMeasure n).loeb, ∀ j, IsFinite (andersonW T n (t j) ω) :=
    ae_all_iff.2 fun j => ae_isFinite_andersonW hT hn (htT j)
  have hX : (fun ω (i : Fin M) => andersonB T n (t i.succ) ω - andersonB T n (t i.castSucc) ω)
      =ᵐ[(coinMeasure n).loeb] stVec ∘ ifun (incrSeq T n t) := by
    filter_upwards [hfin] with ω hω
    funext i
    simp only [Function.comp, stVec, coordG_ifun_incrSeq, andersonB]
    rw [stdPart_sub' (hω _) (hω _)]
  have hmeas : Measurable (fun ω (i : Fin M) =>
      andersonB T n (t i.succ) ω - andersonB T n (t i.castSucc) ω) :=
    Measurable.of_eval fun i => (measurable_andersonB _ _ _).sub (measurable_andersonB _ _ _)
  refine ⟨hmeas.aemeasurable, ?_⟩
  rw [Measure.map_congr hX, ← Measure.map_map measurable_stVec (measurable_ifun _),
    map_stVec_eq _ (incr_ns_null hT hn t ht htT), incr_stMeasure hT hn t ht htT]

/-- **Independent increments** of the Loeb shadow of Anderson's walk on `[0, T]`. -/
theorem andersonB_iIndepFun {T : ℝ} (hT : 0 < T) {n : ℕ → ℕ}
    (hn : IsUnlimited ((n : ℕ → ℕ) : Ult ℕ)) {M : ℕ} (t : Fin (M + 1) → ℝ≥0) (ht : Monotone t)
    (htT : ∀ i, (t i : ℝ) ≤ T) :
    iIndepFun (fun (i : Fin M) ω => andersonB T n (t i.succ) ω - andersonB T n (t i.castSucc) ω)
      (coinMeasure n).loeb := by
  have := coinMeasure_isProbability n
  have hL := andersonB_increments_hasLaw hT hn t ht htT
  have hmeas : ∀ i : Fin M, Measurable (fun ω =>
      andersonB T n (t i.succ) ω - andersonB T n (t i.castSucc) ω) :=
    fun i => (measurable_andersonB _ _ _).sub (measurable_andersonB _ _ _)
  have hmX : Measurable (fun ω (i : Fin M) =>
      andersonB T n (t i.succ) ω - andersonB T n (t i.castSucc) ω) := Measurable.of_eval hmeas
  rw [iIndepFun_iff_map_fun_eq_pi_map fun i => (hmeas i).aemeasurable, hL.map_eq]
  congr 1; funext i
  have : (fun ω => andersonB T n (t i.succ) ω - andersonB T n (t i.castSucc) ω) =
      Function.eval i ∘ fun ω (i : Fin M) =>
        andersonB T n (t i.succ) ω - andersonB T n (t i.castSucc) ω := rfl
  rw [this, ← Measure.map_map (measurable_pi_apply i) hmX, hL.map_eq,
    (measurePreserving_eval _ i).map_eq]

/-- **The one-dimensional marginals**: `b(t) = st W(t)` has law `N(0, t)` under the Loeb
measure, for every standard `t ∈ [0, T]`. -/
theorem andersonB_hasLaw {T : ℝ} (hT : 0 < T) {n : ℕ → ℕ}
    (hn : IsUnlimited ((n : ℕ → ℕ) : Ult ℕ)) {t : ℝ≥0} (htT : (t : ℝ) ≤ T) :
    HasLaw (andersonB T n t) (gaussianReal 0 t) (coinMeasure n).loeb := by
  let tt : Fin 2 → ℝ≥0 := ![0, t]
  have htt : Monotone tt := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp [tt] at hij ⊢
  have httT : ∀ i, (tt i : ℝ) ≤ T := by
    intro i; fin_cases i
    · simp [tt]; exact hT.le
    · simpa [tt] using htT
  have hL := andersonB_increments_hasLaw hT hn tt htt httT
  have hmX : Measurable (fun ω (i : Fin 1) =>
      andersonB T n (tt i.succ) ω - andersonB T n (tt i.castSucc) ω) :=
    Measurable.of_eval fun i => (measurable_andersonB _ _ _).sub (measurable_andersonB _ _ _)
  have e : andersonB T n t = Function.eval 0 ∘ fun ω (i : Fin 1) =>
      andersonB T n (tt i.succ) ω - andersonB T n (tt i.castSucc) ω := by
    funext ω
    simp only [Function.comp, Function.eval]
    have e1 : tt (Fin.succ 0) = t := rfl
    have e0 : tt (Fin.castSucc 0) = 0 := rfl
    rw [e1, e0, NNReal.coe_zero, andersonB_zero, sub_zero]
  refine ⟨(measurable_andersonB _ _ _).aemeasurable, ?_⟩
  rw [e, ← Measure.map_map (measurable_pi_apply 0) hmX, hL.map_eq,
    (measurePreserving_eval _ 0).map_eq]
  simp [tt]

end AndersonWalk

/-! ## The reflection principle and the maximal inequality for the fair walk -/

section Reflection

open QE.Prob QE.Prob.BE

variable (L : ℕ) (lam : ℝ)

/-- The partial sums `S_k` of a sequence of `L` coins. -/
def psum (ω : Fin L → Bool) (k : ℕ) : ℝ := blockSum (coinExt L ω) 0 k

/-- The walk reaches level `λ` in absolute value by time `L`. -/
def Hit (ω : Fin L → Bool) : Prop := ∃ k, k ≤ L ∧ lam ≤ |psum L ω k|

open Classical in
/-- The first passage time of `|S|` through `λ`. -/
def hitTime (ω : Fin L → Bool) : ℕ := if h : Hit L lam ω then Nat.find h else L + 1

open Classical in
/-- Reflection of the coins after the first passage time. -/
def reflect (ω : Fin L → Bool) : Fin L → Bool :=
  fun j => if hitTime L lam ω ≤ j then !ω j else ω j

variable {L lam}

theorem hitTime_spec {ω : Fin L → Bool} (h : Hit L lam ω) :
    hitTime L lam ω ≤ L ∧ lam ≤ |psum L ω (hitTime L lam ω)| := by
  classical
  have : hitTime L lam ω = Nat.find h := by simp [hitTime, h]
  rw [this]; exact Nat.find_spec h

theorem hitTime_min {ω : Fin L → Bool} (h : Hit L lam ω) {k : ℕ} (hk : k < hitTime L lam ω) :
    |psum L ω k| < lam := by
  classical
  have e : hitTime L lam ω = Nat.find h := by simp [hitTime, h]
  rw [e] at hk
  have := Nat.find_min h hk
  push Not at this
  exact this (by have := (hitTime_spec h).1; rw [e] at this; omega)

theorem psum_reflect_of_le (ω : Fin L → Bool) {k : ℕ} (hk : k ≤ hitTime L lam ω) :
    psum L (reflect L lam ω) k = psum L ω k := by
  unfold psum
  refine blockSum_congr fun j _ hj => ?_
  unfold coinExt
  split_ifs with hjL
  · unfold reflect
    split_ifs with h2
    · exfalso; simp only at h2; omega
    · rfl
  · rfl

theorem hit_reflect {ω : Fin L → Bool} (h : Hit L lam ω) : Hit L lam (reflect L lam ω) :=
  ⟨hitTime L lam ω, (hitTime_spec h).1, by
    rw [psum_reflect_of_le ω le_rfl]; exact (hitTime_spec h).2⟩

theorem hitTime_le {ω : Fin L → Bool} (h : Hit L lam ω) {k : ℕ} (hk : k ≤ L)
    (hk' : lam ≤ |psum L ω k|) : hitTime L lam ω ≤ k := by
  classical
  have e : hitTime L lam ω = Nat.find h := by simp [hitTime, h]
  rw [e]; exact Nat.find_min' h ⟨hk, hk'⟩

theorem hitTime_reflect {ω : Fin L → Bool} (h : Hit L lam ω) :
    hitTime L lam (reflect L lam ω) = hitTime L lam ω := by
  have h' := hit_reflect h
  refine le_antisymm (hitTime_le h' (hitTime_spec h).1 ?_) ?_
  · rw [psum_reflect_of_le ω le_rfl]; exact (hitTime_spec h).2
  · by_contra hc
    push Not at hc
    have h1 := (hitTime_spec h').2
    rw [psum_reflect_of_le ω hc.le] at h1
    have h2 := hitTime_min h hc
    linarith

theorem reflect_reflect {ω : Fin L → Bool} (h : Hit L lam ω) :
    reflect L lam (reflect L lam ω) = ω := by
  funext j
  have e := hitTime_reflect h
  rw [reflect]
  rw [e]
  unfold reflect
  split_ifs <;> simp

theorem psum_reflect_L {ω : Fin L → Bool} (h : Hit L lam ω) :
    psum L (reflect L lam ω) L = 2 * psum L ω (hitTime L lam ω) - psum L ω L := by
  have hτ := (hitTime_spec h).1
  unfold psum
  rw [← blockSum_add (Nat.zero_le _) hτ, ← blockSum_add (ω := coinExt L ω) (Nat.zero_le _) hτ]
  have h1 : blockSum (coinExt L (reflect L lam ω)) 0 (hitTime L lam ω) =
      blockSum (coinExt L ω) 0 (hitTime L lam ω) := psum_reflect_of_le ω le_rfl
  have h2 : blockSum (coinExt L (reflect L lam ω)) (hitTime L lam ω) L =
      - blockSum (coinExt L ω) (hitTime L lam ω) L := by
    unfold blockSum
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [Finset.mem_Ico] at hj
    simp only [coinExt, hj.2, dite_true]
    unfold reflect
    split_ifs with h2
    · cases ω ⟨j, hj.2⟩ <;> simp [sgn]
    · exfalso; simp only at h2; omega
  rw [h1, h2]; ring

theorem hit_or_reflect {ω : Fin L → Bool} (h : Hit L lam ω) :
    lam ≤ |psum L ω L| ∨ lam ≤ |psum L (reflect L lam ω) L| := by
  by_contra hc
  push Not at hc
  have h1 := (hitTime_spec h).2
  rw [psum_reflect_L h] at hc
  have := abs_add_le (psum L ω L) (2 * psum L ω (hitTime L lam ω) - psum L ω L)
  have e : psum L ω L + (2 * psum L ω (hitTime L lam ω) - psum L ω L) =
      2 * psum L ω (hitTime L lam ω) := by ring
  rw [e, abs_mul, abs_two] at this
  linarith [hc.1, hc.2]

open Classical in
/-- **Reflection principle (maximal inequality)**: `#{max_{k ≤ L} |S_k| ≥ λ} ≤ 2 #{|S_L| ≥ λ}`. -/
theorem card_hit_le :
    (Finset.univ.filter (fun ω : Fin L → Bool => Hit L lam ω)).card ≤
      2 * (Finset.univ.filter (fun ω : Fin L → Bool => lam ≤ |psum L ω L|)).card := by
  classical
  set H := Finset.univ.filter (fun ω : Fin L → Bool => Hit L lam ω)
  set G := Finset.univ.filter (fun ω : Fin L → Bool => lam ≤ |psum L ω L|)
  have hsplit := Finset.card_filter_add_card_filter_not (s := H) (fun ω => lam ≤ |psum L ω L|)
  have hle : (H.filter (fun ω => ¬ lam ≤ |psum L ω L|)).card ≤
      (H.filter (fun ω => lam ≤ |psum L ω L|)).card := by
    refine Finset.card_le_card_of_injOn (reflect L lam) ?_ ?_
    · intro ω hω
      simp only [Finset.coe_filter, Set.mem_ofPred_eq, H, Finset.mem_filter, Finset.mem_univ,
        true_and] at hω ⊢
      exact ⟨hit_reflect hω.1, (hit_or_reflect hω.1).resolve_left hω.2⟩
    · intro ω₁ h₁ ω₂ h₂ he
      simp only [Finset.coe_filter, Set.mem_ofPred_eq, H, Finset.mem_filter, Finset.mem_univ,
        true_and] at h₁ h₂
      rw [← reflect_reflect h₁.1, ← reflect_reflect h₂.1, he]
  have hG : (H.filter (fun ω => lam ≤ |psum L ω L|)).card ≤ G.card := by
    refine Finset.card_le_card fun ω hω => ?_
    simp only [H, G, Finset.mem_filter, Finset.mem_univ, true_and] at hω ⊢
    exact hω.2
  omega

open Classical in
theorem probU_eq_card (N : ℕ) (A : (ℕ → Bool) → Prop) :
    probU N A = (Finset.univ.filter (fun ω : Fin N → Bool => A (coinExt N ω))).card / 2 ^ N := by
  unfold probU
  rw [Finset.sum_boole]

/-- **Maximal inequality**: `P(max_{k ≤ L} |S_k| ≥ λ) ≤ 2 P(|S_L| ≥ λ)`. -/
theorem probU_max_le (L : ℕ) (lam : ℝ) :
    probU L (fun ω => ∃ k, k ≤ L ∧ lam ≤ |blockSum ω 0 k|) ≤
      2 * probU L (fun ω => lam ≤ |blockSum ω 0 L|) := by
  classical
  rw [probU_eq_card, probU_eq_card, ← mul_div_assoc]
  refine div_le_div_of_nonneg_right ?_ (by positivity)
  have := card_hit_le (L := L) (lam := lam)
  exact_mod_cast this

/-- **Fourth-moment bound**: `P(|S_L| ≥ λ) ≤ 3L²/λ⁴`. -/
theorem probU_abs_ge_le (L : ℕ) {lam : ℝ} (hlam : 0 < lam) :
    probU L (fun ω => lam ≤ |blockSum ω 0 L|) ≤ 3 * (L : ℝ) ^ 2 / lam ^ 4 := by
  classical
  unfold probU
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  have hterm : ∀ ω : Fin L → Bool, (if lam ≤ |blockSum (coinExt L ω) 0 L| then (1 : ℝ) else 0) ≤
      (S ω : ℝ) ^ 4 / lam ^ 4 := by
    intro ω
    rw [blockSum_coinExt]
    split_ifs with h
    · rw [le_div_iff₀ (by positivity), one_mul]
      have : lam ^ 4 ≤ |(S ω : ℝ)| ^ 4 := pow_le_pow_left₀ hlam.le h 4
      rwa [pow_abs, abs_of_nonneg (by positivity)] at this
    · positivity
  have hsum := Finset.sum_le_sum fun ω (_ : ω ∈ Finset.univ) => hterm ω
  rw [← Finset.sum_div, sum_S_four] at hsum
  have h2 : ((3 * (L : ℝ) ^ 2 - 2 * L) * 2 ^ L) / lam ^ 4 ≤ (3 * (L : ℝ) ^ 2 * 2 ^ L) / lam ^ 4 :=
    div_le_div_of_nonneg_right (by nlinarith [(by positivity : (0 : ℝ) ≤ 2 ^ L),
      (Nat.cast_nonneg L : (0 : ℝ) ≤ L)]) (by positivity)
  have h3 := hsum.trans h2
  rw [le_div_iff₀ (by positivity)] at h3
  nlinarith [h3]

end Reflection

/-! ## Oscillation bound for the fair walk (the Kolmogorov–Čentsov step, internally) -/

section Oscillation

open QE.Prob QE.Prob.BE

theorem probU_window (N p L : ℕ) (h : p + L ≤ N) (A : (ℕ → Bool) → Prop)
    (hA : ∀ ω ω' : ℕ → Bool, (∀ j, p ≤ j → j < p + L → ω j = ω' j) → (A ω ↔ A ω')) :
    probU N A = probU L (fun ω => A (shiftR p ω)) := by
  obtain ⟨r, hr⟩ := Nat.exists_eq_add_of_le h
  rw [hr, add_assoc, probU_right p (L + r) A (fun ω ω' hω => hA ω ω' fun j hj _ => hω j hj)]
  refine probU_left L r _ fun ω ω' hω => hA _ _ fun j hj1 hj2 => ?_
  simp only [shiftR, not_lt.2 hj1, ite_false]
  exact hω _ (by omega)

/-- The maximum of a window of `L` coins starting at `p` reaches `λ`. -/
def WinMax (p L : ℕ) (lam : ℝ) (ω : ℕ → Bool) : Prop :=
  ∃ k, k ≤ L ∧ lam ≤ |blockSum ω p (p + k)|

theorem probU_winMax_le (N p L : ℕ) (h : p + L ≤ N) {lam : ℝ} (hlam : 0 < lam) :
    probU N (WinMax p L lam) ≤ 6 * (L : ℝ) ^ 2 / lam ^ 4 := by
  rw [probU_window N p L h]
  · have e : (fun ω => WinMax p L lam (shiftR p ω)) =
        fun ω => ∃ k, k ≤ L ∧ lam ≤ |blockSum ω 0 k| := by
      funext ω; simp only [WinMax, blockSum_shiftR]
    rw [e]
    calc _ ≤ 2 * probU L (fun ω => lam ≤ |blockSum ω 0 L|) := probU_max_le L lam
      _ ≤ 2 * (3 * (L : ℝ) ^ 2 / lam ^ 4) := by
          have := probU_abs_ge_le L hlam; linarith
      _ = 6 * (L : ℝ) ^ 2 / lam ^ 4 := by ring
  · intro ω ω' hω
    simp only [WinMax]
    refine exists_congr fun k => and_congr_right fun hk => ?_
    rw [blockSum_congr fun j hj1 hj2 => hω j hj1 (by omega)]

theorem probU_exists_le (N J : ℕ) (E : ℕ → (ℕ → Bool) → Prop) :
    probU N (fun ω => ∃ j, j < J ∧ E j ω) ≤ ∑ j ∈ Finset.range J, probU N (E j) := by
  classical
  unfold probU
  rw [← Finset.sum_div, Finset.sum_comm]
  refine div_le_div_of_nonneg_right (Finset.sum_le_sum fun ω _ => ?_) (by positivity)
  split_ifs with h
  · obtain ⟨j, hj, hE⟩ := h
    calc (1 : ℝ) = if E j (coinExt N ω) then 1 else 0 := by rw [ite_eq_left hE]
      _ ≤ ∑ j ∈ Finset.range J, if E j (coinExt N ω) then (1 : ℝ) else 0 :=
          Finset.single_le_sum (f := fun j => if E j (coinExt N ω) then (1 : ℝ) else 0)
            (fun i _ => by split_ifs <;> norm_num) (Finset.mem_range.2 hj)
  · exact Finset.sum_nonneg fun i _ => by split_ifs <;> norm_num

/-- The walk oscillates by `3λ` on some pair of times at distance `≤ L`. -/
def Osc (N L : ℕ) (lam : ℝ) (ω : ℕ → Bool) : Prop :=
  ∃ k k', k ≤ k' ∧ k' ≤ N ∧ k' ≤ k + L ∧ 3 * lam ≤ |blockSum ω k k'|

theorem osc_subset {N L : ℕ} (hL : 0 < L) {lam : ℝ} (hlam : 0 < lam) {ω : ℕ → Bool}
    (h : Osc N L lam ω) : ∃ j, j < N / L + 1 ∧ WinMax (j * L) L lam ω := by
  obtain ⟨k, k', hkk', hk'N, hk'L, hbig⟩ := h
  by_contra hno
  push Not at hno
  set j := k / L with hj
  have hjL : j * L ≤ k := Nat.div_mul_le_self k L
  have hkL : k < j * L + L := by
    have := Nat.lt_div_mul_add hL (a := k); rw [hj]; linarith
  have hjJ : j < N / L + 1 := by
    have : j ≤ N / L := Nat.div_le_div_right (hkk'.trans hk'N)
    omega
  have hw : ∀ i, i < N / L + 1 → ∀ q, q ≤ L → |blockSum ω (i * L) (i * L + q)| < lam := by
    intro i hi q hq
    have := hno i hi
    simp only [WinMax, not_exists, not_and, not_le] at this
    exact this q hq
  have hsplit1 : blockSum ω k k' = blockSum ω (j * L) k' - blockSum ω (j * L) k := by
    rw [← blockSum_add hjL hkk']; ring
  have hA : |blockSum ω (j * L) k| < lam := by
    have := hw j hjJ (k - j * L) (by omega)
    rwa [Nat.add_sub_cancel' hjL] at this
  rcases le_or_gt k' (j * L + L) with hc | hc
  · have hB : |blockSum ω (j * L) k'| < lam := by
      have := hw j hjJ (k' - j * L) (by omega)
      rwa [Nat.add_sub_cancel' (hjL.trans hkk')] at this
    have : |blockSum ω k k'| < 3 * lam := by
      rw [hsplit1]
      calc _ ≤ |blockSum ω (j * L) k'| + |blockSum ω (j * L) k| := abs_sub _ _
        _ < 3 * lam := by linarith
    linarith
  · have hj1 : j + 1 < N / L + 1 := by
      have : (j + 1) * L ≤ N := by rw [add_mul, one_mul]; omega
      have := (Nat.le_div_iff_mul_le hL).2 this
      omega
    have hsplit2 : blockSum ω (j * L) k' =
        blockSum ω (j * L) (j * L + L) + blockSum ω ((j + 1) * L) k' := by
      rw [show (j + 1) * L = j * L + L by ring, blockSum_add (by omega) hc.le]
    have hC : |blockSum ω (j * L) (j * L + L)| < lam := hw j hjJ L le_rfl
    have hD : |blockSum ω ((j + 1) * L) k'| < lam := by
      have := hw (j + 1) hj1 (k' - (j + 1) * L) (by
        rw [show (j + 1) * L = j * L + L by ring]; omega)
      rwa [Nat.add_sub_cancel' (by rw [show (j + 1) * L = j * L + L by ring]; omega)] at this
    have : |blockSum ω k k'| < 3 * lam := by
      rw [hsplit1, hsplit2]
      calc _ ≤ |blockSum ω (j * L) (j * L + L)| + |blockSum ω ((j + 1) * L) k'| +
            |blockSum ω (j * L) k| := by
            have := abs_sub (blockSum ω (j * L) (j * L + L) + blockSum ω ((j + 1) * L) k')
              (blockSum ω (j * L) k)
            linarith [abs_add_le (blockSum ω (j * L) (j * L + L)) (blockSum ω ((j + 1) * L) k')]
        _ < 3 * lam := by linarith
    linarith

/-- **Oscillation bound**: `P(Osc) ≤ (N/L + 1) · 6L²/λ⁴`. -/
theorem probU_osc_le (N L : ℕ) (hL : 0 < L) {lam : ℝ} (hlam : 0 < lam) :
    probU N (Osc N L lam) ≤ ((N / L + 1 : ℕ) : ℝ) * (6 * (L : ℝ) ^ 2 / lam ^ 4) := by
  set J := N / L + 1
  have hJN : N ≤ J * L := by
    have := Nat.lt_div_mul_add hL (a := N); rw [show J * L = (N / L) * L + L by ring]; omega
  obtain ⟨r, hr⟩ := Nat.exists_eq_add_of_le hJN
  have hdep : ∀ ω ω' : ℕ → Bool, (∀ j < N, ω j = ω' j) → (Osc N L lam ω ↔ Osc N L lam ω') := by
    intro ω ω' hω
    simp only [Osc]
    refine exists_congr fun k => exists_congr fun k' => ?_
    constructor
    · rintro ⟨h1, h2, h3, h4⟩
      exact ⟨h1, h2, h3, by rwa [← blockSum_congr fun j _ hj => hω j (by omega)]⟩
    · rintro ⟨h1, h2, h3, h4⟩
      exact ⟨h1, h2, h3, by rwa [blockSum_congr fun j _ hj => hω j (by omega)]⟩
  rw [← probU_left N r _ hdep, ← hr]
  calc probU (J * L) (Osc N L lam)
      ≤ probU (J * L) (fun ω => ∃ j, j < J ∧ WinMax (j * L) L lam ω) :=
        probU_mono _ fun ω h => osc_subset hL hlam h
    _ ≤ ∑ j ∈ Finset.range J, probU (J * L) (WinMax (j * L) L lam) := probU_exists_le _ _ _
    _ ≤ ∑ _j ∈ Finset.range J, 6 * (L : ℝ) ^ 2 / lam ^ 4 := by
        refine Finset.sum_le_sum fun j hj => probU_winMax_le _ _ _ ?_ hlam
        have := Finset.mem_range.1 hj
        calc j * L + L = (j + 1) * L := by ring
          _ ≤ J * L := Nat.mul_le_mul_right _ this
    _ = (J : ℝ) * (6 * (L : ℝ) ^ 2 / lam ^ 4) := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]

end Oscillation

/-! ## S-continuity of Anderson's walk and continuity of its shadow -/

section SContinuity

open QE.Prob QE.Prob.BE ProbabilityTheory
open scoped NNReal

variable {T : ℝ} {n : ℕ → ℕ}

/-- Window length `⌊δ/Δt⌋` at level `m`. -/
def winL (T : ℝ) (n : ℕ → ℕ) (δ : ℝ) (m : ℕ) : ℕ := ⌊δ / (T / n m)⌋₊

/-- The level `λ = η/(3√Δt)` at level `m`. -/
def levelL (T : ℝ) (n : ℕ → ℕ) (η : ℝ) (m : ℕ) : ℝ := η / (3 * √(T / n m))

/-- The internal set of paths oscillating by `η` over some pair of lattice times at distance
at most `δ`. -/
def badSet (T : ℝ) (n : ℕ → ℕ) (η δ : ℝ) : Set (Ult (ℕ → Bool)) :=
  internal (fun m => {ω | Osc (n m) (winL T n δ m) (levelL T n η m) ω})

theorem eventually_winL_pos (hT : 0 < T) (hn : IsUnlimited ((n : ℕ → ℕ) : Ult ℕ)) {δ : ℝ}
    (hδ : 0 < δ) : ∀ᶠ m in (hyperfilter ℕ : Filter ℕ), 0 < n m ∧ T / n m ≤ δ / 4 ∧
      0 < winL T n δ m := by
  have hpos : ∀ᶠ m in (hyperfilter ℕ : Filter ℕ), 0 < n m := Germ.coe_lt.1 (hn 0)
  have hsmall := (tendsto_order.1 (tendsto_dt (T := T) hn)).2 (δ / 4) (by positivity)
  filter_upwards [hpos, hsmall] with m hm hs
  refine ⟨hm, hs.le, ?_⟩
  unfold winL
  have hd : 0 < T / (n m : ℝ) := by positivity
  refine Nat.floor_pos.2 ?_
  rw [le_div_iff₀ hd, one_mul]; linarith

/-- **Loeb bound for the bad set**: `L(bad(η, δ)) ≤ 486 (Tδ + δ²)/η⁴`. -/
theorem loeb_badSet_le (hT : 0 < T) (hn : IsUnlimited ((n : ℕ → ℕ) : Ult ℕ)) {η δ : ℝ}
    (hη : 0 < η) (hδ : 0 < δ) :
    (coinMeasure n).loeb (badSet T n η δ) ≤ ENNReal.ofReal (486 * (T * δ + δ ^ 2) / η ^ 4) := by
  rw [badSet, HypMeasure.loeb_internal _ (isInternal_internal _), HypMeasure.mass_internal]
  refine stE_le_of_le (Germ.coe_nonneg.2 (Eventually.of_forall fun m =>
    HypMeasure.seqMass_nonneg _ _ m)) ?_
  refine ofSeq_le_const.2 ?_
  filter_upwards [eventually_winL_pos hT hn hδ] with m hm'
  obtain ⟨hm, -, hL⟩ := hm'
  rw [coin_seqMass]
  set N := n m
  set L := winL T n δ m
  set dt : ℝ := T / N with hdt
  have hdtpos : 0 < dt := by positivity
  have hlam : 0 < levelL T n η m := by unfold levelL; positivity
  have h1 := probU_osc_le N L hL hlam
  have hlam4 : 6 * (L : ℝ) ^ 2 / levelL T n η m ^ 4 = 486 * ((L : ℝ) * dt) ^ 2 / η ^ 4 := by
    unfold levelL
    have hs : (√dt) ^ 2 = dt := Real.sq_sqrt hdtpos.le
    rw [div_pow, mul_pow, show (√(T / (N : ℝ))) ^ 4 = ((√dt) ^ 2) ^ 2 by rw [hdt]; ring, hs]
    field_simp
    ring
  have hLdt : (L : ℝ) * dt ≤ δ := by
    have := Nat.floor_le (div_nonneg hδ.le hdtpos.le)
    have h2 := mul_le_mul_of_nonneg_right this hdtpos.le
    rwa [div_mul_cancel₀ _ hdtpos.ne'] at h2
  have hNdt : (N : ℝ) * dt = T := by rw [hdt]; field_simp
  have hJ : ((N / L + 1 : ℕ) : ℝ) ≤ (N : ℝ) / L + 1 := by
    push_cast
    have := Nat.cast_div_le (α := ℝ) (m := N) (n := L)
    linarith
  have hLpos : (0 : ℝ) < L := by exact_mod_cast hL
  calc probU N (fun ω => ω ∈ {ω | Osc N L (levelL T n η m) ω})
      = probU N (Osc N L (levelL T n η m)) := rfl
    _ ≤ ((N / L + 1 : ℕ) : ℝ) * (6 * (L : ℝ) ^ 2 / levelL T n η m ^ 4) := h1
    _ ≤ ((N : ℝ) / L + 1) * (486 * ((L : ℝ) * dt) ^ 2 / η ^ 4) := by
        rw [hlam4]; exact mul_le_mul_of_nonneg_right hJ (by positivity)
    _ = 486 * ((N * dt) * (L * dt) + (L * dt) ^ 2) / η ^ 4 := by field_simp
    _ ≤ 486 * (T * δ + δ ^ 2) / η ^ 4 := by
        rw [hNdt]
        have : (L : ℝ) * dt ≥ 0 := by positivity
        gcongr

/-- Loeb-almost every path is good at every scale. -/
theorem ae_not_badSet (hT : 0 < T) (hn : IsUnlimited ((n : ℕ → ℕ) : Ult ℕ)) :
    ∀ᵐ ω ∂(coinMeasure n).loeb, ∀ i : ℕ, ∃ j : ℕ,
      ω ∉ badSet T n (1 / ((i : ℝ) + 1)) (1 / ((j : ℝ) + 1)) := by
  rw [ae_all_iff]
  intro i
  rw [ae_iff]
  simp only [not_exists, not_not]
  have hsub : {ω | ∀ j : ℕ, ω ∈ badSet T n (1 / ((i : ℝ) + 1)) (1 / ((j : ℝ) + 1))} ⊆
      ⋂ j : ℕ, badSet T n (1 / ((i : ℝ) + 1)) (1 / ((j : ℝ) + 1)) :=
    fun ω h => Set.mem_iInter.2 h
  refine measure_mono_null hsub (le_antisymm ?_ bot_le)
  have hb : ∀ j : ℕ, (coinMeasure n).loeb (⋂ j : ℕ, badSet T n (1 / ((i : ℝ) + 1))
      (1 / ((j : ℝ) + 1))) ≤ ENNReal.ofReal (486 * (T * (1 / ((j : ℝ) + 1)) +
        (1 / ((j : ℝ) + 1)) ^ 2) / (1 / ((i : ℝ) + 1)) ^ 4) := fun j =>
    (measure_mono (Set.iInter_subset _ j)).trans
      (loeb_badSet_le hT hn (one_div_succ_pos i) (one_div_succ_pos j))
  have ht : Tendsto (fun j : ℕ => ENNReal.ofReal (486 * (T * (1 / ((j : ℝ) + 1)) +
      (1 / ((j : ℝ) + 1)) ^ 2) / (1 / ((i : ℝ) + 1)) ^ 4)) atTop (𝓝 0) := by
    rw [← ENNReal.ofReal_zero]
    refine ENNReal.tendsto_ofReal ?_
    have h0 : Tendsto (fun j : ℕ => 1 / ((j : ℝ) + 1)) atTop (𝓝 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    have h2 : Tendsto (fun j : ℕ => T * (1 / ((j : ℝ) + 1)) + (1 / ((j : ℝ) + 1)) ^ 2) atTop
        (𝓝 (T * 0 + 0 ^ 2)) := (h0.const_mul T).add (h0.pow 2)
    have h3 := h2.const_mul (486 * ((1 / ((i : ℝ) + 1)) ^ 4)⁻¹)
    rw [show (486 * ((1 / ((i : ℝ) + 1)) ^ 4)⁻¹ * (T * 0 + 0 ^ 2) : ℝ) = 0 by ring] at h3
    refine h3.congr fun j => ?_
    simp only [div_eq_mul_inv]; ring
  exact ge_of_tendsto' ht hb

/-- **The walk at a level** moves by less than `η` over times at distance `≤ δ/2`, off the bad
set. -/
theorem walkSeq_close {m : ℕ} (hT : 0 < T) {η δ : ℝ} (hη : 0 < η) (_hδ : 0 < δ)
    (hm : 0 < n m) (hdt : T / n m ≤ δ / 4) {u : ℕ → Bool}
    (hu : ¬ Osc (n m) (winL T n δ m) (levelL T n η m) u) {s t : ℝ} (hs0 : 0 ≤ s) (hsT : s ≤ T)
    (ht0 : 0 ≤ t) (htT : t ≤ T) (hst : |t - s| ≤ δ / 2) :
    |walkSeq T n t m u - walkSeq T n s m u| < η := by
  wlog hle : s ≤ t generalizing s t
  · rw [abs_sub_comm]
    exact this ht0 htT hs0 hsT (by rw [abs_sub_comm]; exact hst) (le_of_not_ge hle)
  set dt : ℝ := T / n m with hdtdef
  have hdtpos : 0 < dt := by positivity
  have hKs := walkIdx_bounds hT hm hs0
  have hKt := walkIdx_bounds hT hm ht0
  have hmono := walkIdx_mono hT (n m) hle
  have hKtN := walkIdx_le hT hm htT
  have hwin : walkIdx T (n m) t ≤ walkIdx T (n m) s + winL T n δ m := by
    have hL := Nat.lt_floor_add_one (δ / dt)
    have hLdt : δ - dt < (winL T n δ m : ℝ) * dt := by
      have := mul_lt_mul_of_pos_right hL hdtpos
      rw [div_mul_cancel₀ _ hdtpos.ne', add_mul, one_mul] at this
      unfold winL; rw [← hdtdef]; linarith
    have hts : t - s ≤ δ / 2 := by rw [abs_of_nonneg (sub_nonneg.2 hle)] at hst; exact hst
    have : ((walkIdx T (n m) t : ℝ) - walkIdx T (n m) s) * dt < (winL T n δ m : ℝ) * dt := by
      rw [sub_mul]; linarith [hKt.2, hKs.1]
    have h2 := lt_of_mul_lt_mul_right this hdtpos.le
    have h3 : (walkIdx T (n m) t : ℝ) < walkIdx T (n m) s + winL T n δ m := by linarith
    exact_mod_cast h3.le
  simp only [Osc, not_exists, not_and, not_le] at hu
  have hB := hu _ _ hmono hKtN hwin
  have hdiff : walkSeq T n t m u - walkSeq T n s m u =
      √dt * blockSum u (walkIdx T (n m) s) (walkIdx T (n m) t) := by
    simp only [walkSeq]
    rw [← blockSum_add (Nat.zero_le _) hmono]; ring
  rw [hdiff, abs_mul, abs_of_pos (Real.sqrt_pos.2 hdtpos)]
  have hlev : √dt * (3 * levelL T n η m) = η := by
    unfold levelL; rw [← hdtdef]
    field_simp
  calc √dt * |blockSum u (walkIdx T (n m) s) (walkIdx T (n m) t)| < √dt * (3 * levelL T n η m) :=
        mul_lt_mul_of_pos_left hB (Real.sqrt_pos.2 hdtpos)
    _ = η := hlev

/-- Anderson's walk evaluated at a hyperreal time `τ` (the time cell `⌊τ/Δt⌋`). -/
def andersonWh (T : ℝ) (n : ℕ → ℕ) (τ : ℝ*) (ω : Ult (ℕ → Bool)) : ℝ* :=
  ifun (fun m (p : ℝ × (ℕ → Bool)) => walkSeq T n p.1 m p.2) (Germ.map₂ Prod.mk τ ω)

theorem andersonWh_coe (T : ℝ) (n : ℕ → ℕ) (t : ℝ) (ω : Ult (ℕ → Bool)) :
    andersonWh T n (t : ℝ*) ω = andersonW T n t ω := by
  obtain ⟨u, rfl⟩ := exists_rep ω
  rfl

/-- Off the bad set, `|W(τ) - W(τ')| ≤ η` for hyperreal times in `[0, T]` at distance
`≤ δ/2`. -/
theorem andersonWh_close (hT : 0 < T) (hn : IsUnlimited ((n : ℕ → ℕ) : Ult ℕ)) {η δ : ℝ}
    (hη : 0 < η) (hδ : 0 < δ) {ω : Ult (ℕ → Bool)} (hω : ω ∉ badSet T n η δ) {τ τ' : ℝ*}
    (hτ0 : 0 ≤ τ) (hτT : τ ≤ (T : ℝ*)) (hτ'0 : 0 ≤ τ') (hτ'T : τ' ≤ (T : ℝ*))
    (hd : |τ - τ'| ≤ ((δ / 2 : ℝ) : ℝ*)) :
    |andersonWh T n τ ω - andersonWh T n τ' ω| ≤ (η : ℝ*) := by
  obtain ⟨u, rfl⟩ := exists_rep ω
  obtain ⟨a, rfl⟩ := Hyperreal.ofSeq_surjective τ
  obtain ⟨b, rfl⟩ := Hyperreal.ofSeq_surjective τ'
  have hgood : ∀ᶠ m in (hyperfilter ℕ : Filter ℕ),
      ¬ Osc (n m) (winL T n δ m) (levelL T n η m) (u m) := by
    have := (not_congr (mem_internal _ u)).1 hω
    rwa [← Ultrafilter.eventually_not] at this
  have ha0 : ∀ᶠ m in (hyperfilter ℕ : Filter ℕ), 0 ≤ a m := Germ.coe_nonneg.1 hτ0
  have hb0 : ∀ᶠ m in (hyperfilter ℕ : Filter ℕ), 0 ≤ b m := Germ.coe_nonneg.1 hτ'0
  have haT : ∀ᶠ m in (hyperfilter ℕ : Filter ℕ), a m ≤ T := ofSeq_le_const.1 hτT
  have hbT : ∀ᶠ m in (hyperfilter ℕ : Filter ℕ), b m ≤ T := ofSeq_le_const.1 hτ'T
  have hab : ∀ᶠ m in (hyperfilter ℕ : Filter ℕ), |a m - b m| ≤ δ / 2 := by
    have : |Hyperreal.ofSeq a - Hyperreal.ofSeq b| = Hyperreal.ofSeq (fun m => |a m - b m|) :=
      abs_ofSeq (fun m => a m - b m)
    rw [this] at hd
    exact ofSeq_le_const.1 hd
  show |Hyperreal.ofSeq (fun m => walkSeq T n (a m) m (u m) - walkSeq T n (b m) m (u m))| ≤ _
  rw [abs_ofSeq]
  refine ofSeq_le_const.2 ?_
  filter_upwards [eventually_winL_pos hT hn hδ, hgood, ha0, hb0, haT, hbT, hab] with
    m hm' hg h1 h2 h3 h4 h5
  obtain ⟨hm, hdt, -⟩ := hm'
  exact (walkSeq_close hT hη hδ hm hdt hg h2 h4 h1 h3 h5).le

theorem andersonWh_zero (T : ℝ) (n : ℕ → ℕ) (ω : Ult (ℕ → Bool)) : andersonWh T n 0 ω = 0 := by
  have := andersonWh_coe T n 0 ω
  rw [Hyperreal.coe_zero] at this
  rw [this, andersonW_zero]

/-- **S-continuity and limitedness**: for Loeb-almost every path, `t ↦ W(t, ω)` is S-continuous
and limited on `[0, T]` (hyperreal times). -/
theorem ae_sContinuous_limited (hT : 0 < T) (hn : IsUnlimited ((n : ℕ → ℕ) : Ult ℕ)) :
    ∀ᵐ ω ∂(coinMeasure n).loeb,
      (∀ τ τ' : ℝ*, 0 ≤ τ → τ ≤ (T : ℝ*) → 0 ≤ τ' → τ' ≤ (T : ℝ*) →
        IsInfinitesimal (τ - τ') → IsInfinitesimal (andersonWh T n τ ω - andersonWh T n τ' ω)) ∧
      (∀ τ : ℝ*, 0 ≤ τ → τ ≤ (T : ℝ*) → IsFinite (andersonWh T n τ ω)) := by
  filter_upwards [ae_not_badSet hT hn] with ω hω
  constructor
  · intro τ τ' h0 h1 h2 h3 hinf
    refine isInfinitesimal_of_abs_lt fun r hr => ?_
    obtain ⟨i, hi⟩ := exists_nat_one_div_lt hr
    obtain ⟨j, hj⟩ := hω i
    have hd : |τ - τ'| ≤ ((1 / ((j : ℝ) + 1) / 2 : ℝ) : ℝ*) :=
      (hinf.abs_lt (by have := one_div_succ_pos j; positivity)).le
    have := andersonWh_close hT hn (one_div_succ_pos i) (one_div_succ_pos j) hj h0 h1 h2 h3 hd
    exact lt_of_le_of_lt this (Hyperreal.coe_lt_coe.2 hi)
  · intro τ h0 h1
    obtain ⟨j, hj⟩ := hω 0
    have hj1 : (1 : ℝ) / (((0 : ℕ) : ℝ) + 1) = 1 := by norm_num
    rw [hj1] at hj
    set δ : ℝ := 1 / ((j : ℝ) + 1)
    have hδ : 0 < δ := one_div_succ_pos j
    -- chain from `0` to `τ` in steps of `δ/2`
    have hchain : ∀ k : ℕ, |andersonWh T n (min τ ((k * (δ / 2) : ℝ) : ℝ*)) ω| ≤ ((k : ℝ) : ℝ*) := by
      intro k
      induction k with
      | zero =>
        have : min τ (((0 : ℕ) * (δ / 2) : ℝ) : ℝ*) = 0 := by
          simp only [Nat.cast_zero, zero_mul, Hyperreal.coe_zero]; exact min_eq_right h0
        rw [this, andersonWh_zero, abs_zero]; simp
      | succ k ih =>
        have hk0 : (0 : ℝ*) ≤ (((k : ℝ) * (δ / 2) : ℝ) : ℝ*) := by
          rw [← Hyperreal.coe_zero, Hyperreal.coe_le_coe]; positivity
        have hk1 : (0 : ℝ*) ≤ ((((k + 1 : ℕ) : ℝ) * (δ / 2) : ℝ) : ℝ*) := by
          rw [← Hyperreal.coe_zero, Hyperreal.coe_le_coe]; positivity
        have hstep := andersonWh_close hT hn one_pos hδ hj
          (le_min h0 hk1) ((min_le_left _ _).trans h1) (le_min h0 hk0)
          ((min_le_left _ _).trans h1) (by
            refine (abs_min_sub_min_le_max _ _ _ _).trans ?_
            rw [sub_self, abs_zero]
            refine max_le (by rw [← Hyperreal.coe_zero, Hyperreal.coe_le_coe]; positivity) ?_
            rw [← Hyperreal.coe_sub, ← Hyperreal.coe_abs, Hyperreal.coe_le_coe]
            push_cast
            rw [show ((k : ℝ) + 1) * (δ / 2) - k * (δ / 2) = δ / 2 by ring,
              abs_of_pos (by positivity)])
        have := abs_sub_abs_le_abs_sub
          (andersonWh T n (min τ ((((k + 1 : ℕ) : ℝ) * (δ / 2) : ℝ) : ℝ*)) ω)
          (andersonWh T n (min τ (((k : ℝ) * (δ / 2) : ℝ) : ℝ*)) ω)
        have h1' : ((1 : ℝ) : ℝ*) = 1 := Hyperreal.coe_one
        rw [h1'] at hstep
        push_cast at this ⊢ hstep ih
        linarith
    obtain ⟨q, hq⟩ := exists_nat_ge (T / (δ / 2))
    have hqτ : min τ (((q : ℝ) * (δ / 2) : ℝ) : ℝ*) = τ := by
      refine min_eq_left (h1.trans ?_)
      rw [Hyperreal.coe_le_coe]
      rwa [div_le_iff₀ (by positivity)] at hq
    have := hchain q
    rw [hqτ] at this
    exact (isFinite_iff_abs_le _).2 ⟨q, this⟩

/-- **Continuity of the shadow**: for Loeb-almost every path, `t ↦ b(t, ω) = st W(t, ω)` is
continuous on `[0, T]`. -/
theorem ae_continuousOn_andersonB (hT : 0 < T) (hn : IsUnlimited ((n : ℕ → ℕ) : Ult ℕ)) :
    ∀ᵐ ω ∂(coinMeasure n).loeb, ContinuousOn (fun t => andersonB T n t ω) (Icc 0 T) := by
  filter_upwards [ae_not_badSet hT hn, ae_sContinuous_limited hT hn] with ω hω hlim
  rw [Metric.continuousOn_iff]
  intro t ht ε hε
  obtain ⟨i, hi⟩ := exists_nat_one_div_lt hε
  obtain ⟨j, hj⟩ := hω i
  refine ⟨1 / ((j : ℝ) + 1) / 2, by have := one_div_succ_pos j; positivity, fun s hs hst => ?_⟩
  have hfin : ∀ r ∈ Icc (0 : ℝ) T, IsFinite (andersonW T n r ω) := fun r hr => by
    rw [← andersonWh_coe]
    exact hlim.2 _ (by rw [← Hyperreal.coe_zero, Hyperreal.coe_le_coe]; exact hr.1)
      (Hyperreal.coe_le_coe.2 hr.2)
  have hclose := andersonWh_close hT hn (one_div_succ_pos i) (one_div_succ_pos j) hj
    (τ := (s : ℝ*)) (τ' := (t : ℝ*))
    (by rw [← Hyperreal.coe_zero, Hyperreal.coe_le_coe]; exact hs.1) (Hyperreal.coe_le_coe.2 hs.2)
    (by rw [← Hyperreal.coe_zero, Hyperreal.coe_le_coe]; exact ht.1) (Hyperreal.coe_le_coe.2 ht.2)
    (by rw [← Hyperreal.coe_sub, ← Hyperreal.coe_abs, Hyperreal.coe_le_coe]
        rw [Real.dist_eq] at hst; exact hst.le)
  rw [andersonWh_coe, andersonWh_coe] at hclose
  rw [Real.dist_eq]
  simp only [andersonB]
  rw [← stdPart_sub' (hfin s hs) (hfin t ht)]
  have hfs := (hfin s hs).add (isFinite_neg (hfin t ht))
  have hle : |stdPart (andersonW T n s ω - andersonW T n t ω)| ≤ 1 / ((i : ℝ) + 1) := by
    rw [abs_le] at hclose ⊢
    have hf : IsFinite (andersonW T n s ω - andersonW T n t ω) := by
      rw [sub_eq_add_neg]; exact hfs
    have hl : (((-(1 / ((i : ℝ) + 1))) : ℝ) : ℝ*) ≤ andersonW T n s ω - andersonW T n t ω := by
      rw [Hyperreal.coe_neg]; exact hclose.1
    constructor
    · have := stdPart_mono (coe_isFinite _) hf hl
      rwa [Hyperreal.stdPart_coe] at this
    · have := stdPart_mono hf (coe_isFinite _) hclose.2
      rwa [Hyperreal.stdPart_coe] at this
  exact lt_of_le_of_lt hle hi

/-- **Anderson: Wiener measure is the Loeb shadow** (`thm:stoch-anderson`). Let `T > 0` be
standard, `n` an infinite hypernatural, `Δt = T/n`, and `L` the Loeb measure of the uniform
probability on the coin space `Ξ = {±1}^n`.  Then for `L`-almost every `ω` the path
`t ↦ W(t, ω)` is S-continuous and limited on `[0, T]`; and `b(t, ω) = st W(t, ω)` is a standard
Brownian motion on `[0, T]`: `b(0) = 0`, `b(t)` has law `N(0, t)`, the increments over
`t₀ ≤ ⋯ ≤ t_M` are independent with laws `N(0, t_{i+1} - t_i)`, and the paths are continuous
`L`-almost surely. -/
theorem anderson_wiener (hT : 0 < T) (hn : IsUnlimited ((n : ℕ → ℕ) : Ult ℕ)) :
    (∀ᵐ ω ∂(coinMeasure n).loeb,
      (∀ τ τ' : ℝ*, 0 ≤ τ → τ ≤ (T : ℝ*) → 0 ≤ τ' → τ' ≤ (T : ℝ*) →
        IsInfinitesimal (τ - τ') → IsInfinitesimal (andersonWh T n τ ω - andersonWh T n τ' ω)) ∧
      (∀ τ : ℝ*, 0 ≤ τ → τ ≤ (T : ℝ*) → IsFinite (andersonWh T n τ ω))) ∧
    (∀ ω, andersonB T n 0 ω = 0) ∧
    (∀ t : ℝ≥0, (t : ℝ) ≤ T → HasLaw (andersonB T n t) (gaussianReal 0 t) (coinMeasure n).loeb) ∧
    (∀ (M : ℕ) (t : Fin (M + 1) → ℝ≥0), Monotone t → (∀ i, (t i : ℝ) ≤ T) →
      iIndepFun (fun (i : Fin M) ω => andersonB T n (t i.succ) ω - andersonB T n (t i.castSucc) ω)
        (coinMeasure n).loeb ∧
      HasLaw (fun ω (i : Fin M) => andersonB T n (t i.succ) ω - andersonB T n (t i.castSucc) ω)
        (Measure.pi fun i => gaussianReal 0 (t i.succ - t i.castSucc)) (coinMeasure n).loeb) ∧
    (∀ᵐ ω ∂(coinMeasure n).loeb, ContinuousOn (fun t => andersonB T n t ω) (Icc 0 T)) :=
  ⟨ae_sContinuous_limited hT hn, andersonB_zero T n, fun _ ht => andersonB_hasLaw hT hn ht,
    fun _ t ht htT => ⟨andersonB_iIndepFun hT hn t ht htT,
      andersonB_increments_hasLaw hT hn t ht htT⟩, ae_continuousOn_andersonB hT hn⟩

end SContinuity

end QE.NSA

end
