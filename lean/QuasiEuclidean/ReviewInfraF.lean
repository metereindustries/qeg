-- SPDX-License-Identifier: MIT
-- Copyright 2026 Metere Industries, Inc. Author: Alfredo Metere.
-- Quasi-Euclidean Granular Geometry. Any derivative work must carry this notice:
--   This work is derivative of the Quasi-Euclidean Granular Geometry book
--   authored by Alfredo Metere. Copyright 2026 Metere Industries, Inc.
--   All rights reserved
-- See LICENSE.md and NOTICE.

import QuasiEuclidean.OpenGeo
import QuasiEuclidean.NSA_Loeb

/-!
# Retained boundary terms are frame dependent: the hyperreal items (ii), (iii)

`thm:phys-lorentz-retained` (ii) and (iii), in the ultrapower `ℝ* = ℝ^ℕ/𝒰`, with
the transfer to internal sets and the countability of lattice directions done
formally.

* `Λ ⊆ (ℝ²)*` is an internal set; `μ_Λ(S) = (2ε)² · #(S ∩ Λ)` (`muLam`), with `#`
  the internal cardinality `hcard`.
* For a segment (a Lebesgue-null set) the retained term is
  `ρ(S) = st (μ_Λ(S)/ε)` (`rhoSeg`); for a null set `leb = 0`, so this is the
  printed `ρ` without any measure theory.
* `latSet b₁ b₂ = ℤ b₁ + ℤ b₂` is the standard lattice with basis `b₁, b₂`
  (any basis, `det ≠ 0`; covolume `1` is not needed), and
  `granLat e L = [2 eₖ L]` is `Λ = 2ε L` for `ε = [eₖ]`.

Main results: `retained_every_lattice` (item (ii)) and `retained_uniform`
(item (iii)).
-/

set_option linter.unusedSectionVars false

namespace QE.OpenGeo

open QE.NSA Filter Topology

/-! ## Definitions -/

/-- The standard lattice `ℤ b₁ + ℤ b₂ ⊆ ℝ²`. -/
def latSet (b₁ b₂ : ℝ × ℝ) : Set (ℝ × ℝ) := {x | ∃ m n : ℤ, x = (m : ℝ) • b₁ + (n : ℝ) • b₂}

/-- The scaled set `c L`. -/
def scaledLat (c : ℝ) (L : Set (ℝ × ℝ)) : Set (ℝ × ℝ) := {x | ∃ y ∈ L, x = c • y}

/-- The internal lattice `Λ = 2ε L = [2 eₖ L]`. -/
def granLat (e : ℕ → ℝ) (L : Set (ℝ × ℝ)) : Set (Ult (ℝ × ℝ)) :=
  internal (fun k => scaledLat (2 * e k) L)

/-- The granular measure `μ_Λ(S) = (2ε)² #(S ∩ Λ)` of a set of hyperreal points. -/
noncomputable def muLam (ε : ℝ*) (Λ S : Set (Ult (ℝ × ℝ))) : ℝ* :=
  (2 * ε) ^ 2 * HypMeasure.hcardR (S ∩ Λ)

/-- The retained first-order term `ρ(S) = st (μ_Λ(S)/ε)` of a Lebesgue-null set `S`
(for such `S`, `(μ_Λ(S) - leb S)/ε = μ_Λ(S)/ε`). -/
noncomputable def rhoSeg (ε : ℝ*) (Λ S : Set (Ult (ℝ × ℝ))) : ℝ :=
  ArchimedeanClass.stdPart (muLam ε Λ S / ε)

/-- The segment `{s b : s₀ ≤ s ≤ s₁}`. -/
def lineSeg (b : ℝ × ℝ) (s₀ s₁ : ℝ) : Set (ℝ × ℝ) := {x | ∃ s, s₀ ≤ s ∧ s ≤ s₁ ∧ x = s • b}

/-! ## Helpers -/

/-- The internal cardinality of an internal set with `𝒰`-almost all levels finite. -/
theorem hcardR_internal_of_finite (S : ℕ → Set (ℝ × ℝ))
    (h : ∀ᶠ k in (hyperfilter ℕ : Filter ℕ), (S k).Finite) :
    HypMeasure.hcardR (internal S) = Hyperreal.ofSeq (fun k => ((S k).ncard : ℝ)) := by
  classical
  set A : ℕ → Finset (ℝ × ℝ) := fun k => if hk : (S k).Finite then hk.toFinset else ∅
  have hA : internal S = hfin A := by
    unfold hfin; apply internal_congr
    filter_upwards [h] with k hk
    simp [A, hk]
  rw [hA, HypMeasure.hcardR, hcard_hfin]
  show Hyperreal.ofSeq (fun k => ((A k).card : ℝ)) = _
  refine Germ.coe_eq.2 ?_
  filter_upwards [h] with k hk
  simp only [A, hk, ↓reduceDIte]
  rw [Set.ncard_eq_toFinset_card _ hk]

/-- `μ_Λ(S)/ε` for an internal `S` with finite levels, as a germ. -/
theorem muLam_div_internal (e : ℕ → ℝ) (L : ℕ → Set (ℝ × ℝ)) (S : ℕ → Set (ℝ × ℝ))
    (h : ∀ᶠ k in (hyperfilter ℕ : Filter ℕ), (S k ∩ L k).Finite) :
    muLam (Hyperreal.ofSeq e) (internal L) (internal S) / Hyperreal.ofSeq e =
      Hyperreal.ofSeq (fun k => (2 * e k) ^ 2 * ((S k ∩ L k).ncard : ℝ) / e k) := by
  unfold muLam
  rw [← internal_inter, hcardR_internal_of_finite _ h]
  rfl

theorem boost_smul_pt (l s : ℝ) (b : ℝ × ℝ) : boost l (s • b) = s • boost l b := by
  ext <;> simp [boost, Prod.smul_fst, Prod.smul_snd] <;> ring

theorem boost_ne_zero_of_ne {l : ℝ} (hl : 0 < l) {b : ℝ × ℝ} (hb : b ≠ 0) : boost l b ≠ 0 := by
  intro h
  have h1 := boost_lightcone l b
  rw [h] at h1
  simp only [Prod.fst_zero, Prod.snd_zero, add_zero, sub_zero] at h1
  have hu : b.1 + b.2 = 0 := by
    have := h1.1.symm; rcases mul_eq_zero.1 this with h | h
    · exact absurd h hl.ne'
    · exact h
  have hv : b.1 - b.2 = 0 := by
    have := h1.2.symm; rcases mul_eq_zero.1 this with h | h
    · exact absurd h (inv_ne_zero hl.ne')
    · exact h
  exact hb (Prod.ext (by show b.1 = 0; linarith) (by show b.2 = 0; linarith))

theorem smul_eq_smul_iff' {c : ℝ} (hc : c ≠ 0) (y b : ℝ × ℝ) (s : ℝ) :
    c • y = s • b ↔ y = (c⁻¹ * s) • b := by
  constructor
  · intro h
    rw [← smul_smul, ← h, inv_smul_smul₀ hc]
  · intro h
    rw [h, smul_smul, ← mul_assoc, mul_inv_cancel₀ hc, one_mul]

/-- Linear independence of a basis with nonzero determinant. -/
theorem basis_indep {b₁ b₂ : ℝ × ℝ} (hdet : b₁.1 * b₂.2 - b₁.2 * b₂.1 ≠ 0) {α β : ℝ}
    (h : α • b₁ + β • b₂ = 0) : α = 0 ∧ β = 0 := by
  have h1 : α * b₁.1 + β * b₂.1 = 0 := by
    have := congrArg Prod.fst h; simpa using this
  have h2 : α * b₁.2 + β * b₂.2 = 0 := by
    have := congrArg Prod.snd h; simpa using this
  constructor
  · have : α * (b₁.1 * b₂.2 - b₁.2 * b₂.1) = 0 := by linear_combination b₂.2 * h1 - b₂.1 * h2
    exact (mul_eq_zero.1 this).resolve_right hdet
  · have : β * (b₁.1 * b₂.2 - b₁.2 * b₂.1) = 0 := by linear_combination b₁.1 * h2 - b₁.2 * h1
    exact (mul_eq_zero.1 this).resolve_right hdet

/-- Primitive vectors `u b₁ + v b₂` with `u = 1` or `v = 1`: the points of the lattice
on the line `ℝ b` are exactly `ℤ b`. -/
theorem prim_of_coeff {b₁ b₂ : ℝ × ℝ} (hdet : b₁.1 * b₂.2 - b₁.2 * b₂.1 ≠ 0) (u v : ℤ)
    (huv : u = 1 ∨ v = 1) :
    ∀ y ∈ latSet b₁ b₂, ∀ s : ℝ, y = s • ((u : ℝ) • b₁ + (v : ℝ) • b₂) → ∃ j : ℤ, s = j := by
  rintro y ⟨m, n, rfl⟩ s hs
  have h0 : ((m : ℝ) - s * u) • b₁ + ((n : ℝ) - s * v) • b₂ = 0 := by
    rw [smul_add, smul_smul, smul_smul] at hs
    calc ((m : ℝ) - s * u) • b₁ + ((n : ℝ) - s * v) • b₂
        = ((m : ℝ) • b₁ + (n : ℝ) • b₂) - ((s * u) • b₁ + (s * v) • b₂) := by
          rw [sub_smul, sub_smul]; abel
      _ = 0 := by rw [hs, sub_self]
  obtain ⟨ha, hb⟩ := basis_indep hdet h0
  rcases huv with rfl | rfl
  · exact ⟨m, by simp at ha; linarith⟩
  · exact ⟨n, by simp at hb; linarith⟩

/-- Of `b₁`, `b₂`, `b₁ + b₂` for a basis, at least one is non-null. -/
theorem exists_nonnull_basis {b₁ b₂ : ℝ × ℝ} (hdet : b₁.1 * b₂.2 - b₁.2 * b₂.1 ≠ 0) :
    b₁.1 ^ 2 ≠ b₁.2 ^ 2 ∨ b₂.1 ^ 2 ≠ b₂.2 ^ 2 ∨
      (b₁ + b₂).1 ^ 2 ≠ (b₁ + b₂).2 ^ 2 := by
  by_contra h
  push Not at h
  obtain ⟨e1, e2, e3⟩ := h
  simp only [Prod.fst_add, Prod.snd_add] at e3
  apply hdet
  have : (b₁.1 * b₂.2 - b₁.2 * b₂.1) ^ 2 = 0 := by
    linear_combination (-(b₂.1) ^ 2 - b₁.1 * b₂.1) * e1 + (-(b₁.1) ^ 2 - b₁.1 * b₂.1) * e2
      + b₁.1 * b₂.1 * e3
  exact pow_eq_zero_iff (n := 2) (by norm_num) |>.1 this

theorem latSet_countable (b₁ b₂ : ℝ × ℝ) : (latSet b₁ b₂).Countable := by
  refine (Set.countable_range (fun mn : ℤ × ℤ => (mn.1 : ℝ) • b₁ + (mn.2 : ℝ) • b₂)).mono ?_
  rintro x ⟨m, n, rfl⟩; exact ⟨(m, n), rfl⟩

theorem zero_mem_latSet (b₁ b₂ : ℝ × ℝ) : (0 : ℝ × ℝ) ∈ latSet b₁ b₂ := ⟨0, 0, by simp⟩

theorem zsmul_mem_latSet {b₁ b₂ : ℝ × ℝ} (u v j : ℤ) :
    ((j : ℝ) * 1) • ((u : ℝ) • b₁ + (v : ℝ) • b₂) ∈ latSet b₁ b₂ :=
  ⟨j * u, j * v, by push_cast; rw [mul_one, smul_add, smul_smul, smul_smul]⟩

/-- The lattice points of the segment `[0, b]` for a primitive `b`:
`#([0,b] ∩ c L) = ⌊1/c⌋ + 1`. -/
theorem seg_lattice_ncard {b₁ b₂ : ℝ × ℝ} (u v : ℤ) {c : ℝ} (hc : 0 < c)
    (hb : (u : ℝ) • b₁ + (v : ℝ) • b₂ ≠ 0)
    (hprim : ∀ y ∈ latSet b₁ b₂, ∀ s : ℝ, y = s • ((u : ℝ) • b₁ + (v : ℝ) • b₂) →
      ∃ j : ℤ, s = j) :
    (lineSeg ((u : ℝ) • b₁ + (v : ℝ) • b₂) 0 1 ∩ scaledLat c (latSet b₁ b₂)).Finite ∧
    ((lineSeg ((u : ℝ) • b₁ + (v : ℝ) • b₂) 0 1 ∩ scaledLat c (latSet b₁ b₂)).ncard : ℝ) =
      (⌊1 / c⌋ : ℝ) + 1 := by
  classical
  set b := (u : ℝ) • b₁ + (v : ℝ) • b₂
  have hset : lineSeg b 0 1 ∩ scaledLat c (latSet b₁ b₂) =
      ↑((Finset.Icc (0 : ℤ) ⌊1 / c⌋).image fun j : ℤ => (c * j) • b) := by
    ext x
    simp only [Set.mem_inter_iff, lineSeg, scaledLat, Set.mem_ofPred_eq, Finset.coe_image,
      Finset.coe_Icc, Set.mem_image, Set.mem_Icc]
    constructor
    · rintro ⟨⟨s, hs0, hs1, rfl⟩, y, hy, hxy⟩
      have hy' := (smul_eq_smul_iff' hc.ne' y b s).1 hxy.symm
      obtain ⟨j, hj⟩ := hprim y hy _ hy'
      have hsj : s = c * j := by
        have : s = c * (c⁻¹ * s) := by field_simp
        rw [this, hj]
      refine ⟨j, ⟨?_, ?_⟩, by rw [hsj]⟩
      · have : (0 : ℝ) ≤ j := by
          by_contra hneg; push Not at hneg; nlinarith
        exact_mod_cast this
      · refine Int.le_floor.2 ?_
        rw [le_div_iff₀ hc]; nlinarith
    · rintro ⟨j, ⟨hj0, hj1⟩, rfl⟩
      have hj1' := Int.le_floor.1 hj1
      rw [le_div_iff₀ hc] at hj1'
      have hj0' : (0 : ℝ) ≤ j := by exact_mod_cast hj0
      refine ⟨⟨c * j, by positivity, by nlinarith, rfl⟩, ((j : ℝ) * 1) • b,
        zsmul_mem_latSet u v j, ?_⟩
      rw [smul_smul, mul_one]
  rw [hset]
  refine ⟨Finset.finite_toSet _, ?_⟩
  rw [Set.ncard_coe_finset, Finset.card_image_of_injective]
  · rw [Int.card_Icc, sub_zero]
    have h0 : (0 : ℤ) ≤ ⌊1 / c⌋ := Int.floor_nonneg.2 (by positivity)
    rw [← Int.cast_natCast, Int.toNat_of_nonneg (by omega)]; push_cast; ring
  · intro j j' h
    simp only at h
    have : c * j = c * j' := by
      by_contra hne
      have h2 : (c * j - c * j') • b = 0 := by rw [sub_smul, h, sub_self]
      exact hb ((smul_eq_zero.1 h2).resolve_left (sub_ne_zero.2 hne))
    exact_mod_cast mul_left_cancel₀ hc.ne' this

/-- The boosted segment `B_l [0,b]` meets `c L` only at `0` when the line `ℝ B_l b`
contains no nonzero lattice vector. -/
theorem boosted_seg_lattice {L : Set (ℝ × ℝ)} (h0 : (0 : ℝ × ℝ) ∈ L) {c : ℝ} (hc : 0 < c)
    (b : ℝ × ℝ) (l : ℝ) (hgood : ¬ ∃ x ∈ L, x ≠ 0 ∧ ∃ s : ℝ, x = s • boost l b) :
    boost l '' lineSeg b 0 1 ∩ scaledLat c L = {0} := by
  ext x
  simp only [Set.mem_inter_iff, Set.mem_image, lineSeg, scaledLat, Set.mem_ofPred_eq,
    Set.mem_singleton_iff]
  constructor
  · rintro ⟨⟨_, ⟨s, -, -, rfl⟩, rfl⟩, y, hy, hxy⟩
    rw [boost_smul_pt] at hxy
    have hy' := (smul_eq_smul_iff' hc.ne' y (boost l b) s).1 hxy.symm
    by_cases hy0 : y = 0
    · rw [boost_smul_pt, hxy, hy0, smul_zero]
    · exact absurd ⟨y, hy, hy0, _, hy'⟩ hgood
  · rintro rfl
    exact ⟨⟨0, ⟨0, le_rfl, zero_le_one, by simp⟩, by simp [boost]⟩, 0, h0, by simp⟩

/-! ## Item (ii): every lattice -/

/-- **`thm:phys-lorentz-retained` (ii).** Let `L = ℤ b₁ + ℤ b₂` be any standard
lattice (`det ≠ 0`), `ε = [eₖ]` a positive infinitesimal and `Λ = 2εL`. There is a
standard non-null lattice vector `b` such that the segment `F = [0,b]` has
`ρ(F) = 2`, and outside a countable set of standard `l > 0` the boosted segment
has `μ_Λ(B_l F)/ε` infinitesimal, so `ρ(B_l F) = 0`. -/
theorem retained_every_lattice (b₁ b₂ : ℝ × ℝ) (hdet : b₁.1 * b₂.2 - b₁.2 * b₂.1 ≠ 0)
    (e : ℕ → ℝ) (he0 : 0 < Hyperreal.ofSeq e) (hinf : IsInfinitesimal (Hyperreal.ofSeq e)) :
    ∃ b ∈ latSet b₁ b₂, b.1 ^ 2 ≠ b.2 ^ 2 ∧
      rhoSeg (Hyperreal.ofSeq e) (granLat e (latSet b₁ b₂)) (starSet (lineSeg b 0 1)) = 2 ∧
      ∃ Bad : Set ℝ, Bad.Countable ∧ ∀ l : ℝ, 0 < l → l ∉ Bad →
        IsInfinitesimal (muLam (Hyperreal.ofSeq e) (granLat e (latSet b₁ b₂))
          (starSet (boost l '' lineSeg b 0 1)) / Hyperreal.ofSeq e) ∧
        rhoSeg (Hyperreal.ofSeq e) (granLat e (latSet b₁ b₂))
          (starSet (boost l '' lineSeg b 0 1)) = 0 := by
  have he : ∀ᶠ k in (hyperfilter ℕ : Filter ℕ), 0 < e k := Hyperreal.ofSeq_lt_ofSeq.1 he0
  have hlim : Tendsto e (hyperfilter ℕ : Filter ℕ) (𝓝 0) := by
    rw [Metric.tendsto_nhds]
    intro t ht
    filter_upwards [(isInfinitesimal_ofSeq_iff e).1 hinf t ht] with m hm
    simpa [Real.dist_eq] using hm
  -- choose the primitive non-null vector `b = u b₁ + v b₂`
  obtain ⟨u, v, huv, hnn⟩ : ∃ u v : ℤ, (u = 1 ∨ v = 1) ∧
      ((u : ℝ) • b₁ + (v : ℝ) • b₂).1 ^ 2 ≠ ((u : ℝ) • b₁ + (v : ℝ) • b₂).2 ^ 2 := by
    rcases exists_nonnull_basis hdet with h | h | h
    · exact ⟨1, 0, Or.inl rfl, by simpa using h⟩
    · exact ⟨0, 1, Or.inr rfl, by simpa using h⟩
    · exact ⟨1, 1, Or.inl rfl, by simpa using h⟩
  set b := (u : ℝ) • b₁ + (v : ℝ) • b₂ with hbdef
  have hb0 : b ≠ 0 := by intro h; apply hnn; rw [h]; simp
  have hprim := prim_of_coeff hdet u v huv
  refine ⟨b, ⟨u, v, rfl⟩, hnn, ?_, ?_⟩
  · -- `ρ(F) = 2`
    have hfin : ∀ᶠ k in (hyperfilter ℕ : Filter ℕ),
        ((fun _ => lineSeg b 0 1) k ∩ scaledLat (2 * e k) (latSet b₁ b₂)).Finite := by
      filter_upwards [he] with k hk
      exact (seg_lattice_ncard u v (by positivity : 0 < 2 * e k) hb0 hprim).1
    unfold rhoSeg starSet granLat
    rw [muLam_div_internal e _ _ hfin]
    refine Hyperreal.stdPart_of_tendsto (Hyperreal.tendsto_ofSeq.2 ?_)
    -- `4 e (⌊1/(2e)⌋ + 1) → 2`
    have hval : ∀ᶠ k in (hyperfilter ℕ : Filter ℕ),
        (2 * e k) ^ 2 * ((lineSeg b 0 1 ∩ scaledLat (2 * e k) (latSet b₁ b₂)).ncard : ℝ) / e k =
          4 * e k * ((⌊1 / (2 * e k)⌋ : ℝ) + 1) := by
      filter_upwards [he] with k hk
      rw [(seg_lattice_ncard u v (by positivity : 0 < 2 * e k) hb0 hprim).2]
      field_simp; ring
    refine Tendsto.congr' (EventuallyEq.symm hval) ?_
    rw [Metric.tendsto_nhds]
    intro t ht
    filter_upwards [he, (isInfinitesimal_ofSeq_iff e).1 hinf (t / 8) (by positivity)] with k hk hk'
    rw [abs_of_pos hk] at hk'
    have hc : 0 < 2 * e k := by positivity
    have f1 := Int.floor_le (1 / (2 * e k))
    have f2 := Int.lt_floor_add_one (1 / (2 * e k))
    have hid : 2 * e k * (1 / (2 * e k)) = 1 := by field_simp
    rw [Real.dist_eq, abs_lt]
    constructor <;> nlinarith
  · -- the countable exceptional set
    refine ⟨{l : ℝ | 0 < l ∧ ∃ x ∈ latSet b₁ b₂, x ≠ 0 ∧ ∃ s : ℝ, x = s • boost l b},
      countable_boosted_lines _ (latSet_countable b₁ b₂) b hnn, fun l hl hbad => ?_⟩
    have hgood : ¬ ∃ x ∈ latSet b₁ b₂, x ≠ 0 ∧ ∃ s : ℝ, x = s • boost l b :=
      fun h => hbad ⟨hl, h⟩
    have hfin : ∀ᶠ k in (hyperfilter ℕ : Filter ℕ),
        ((fun _ => boost l '' lineSeg b 0 1) k ∩ scaledLat (2 * e k) (latSet b₁ b₂)).Finite := by
      filter_upwards [he] with k hk
      rw [boosted_seg_lattice (zero_mem_latSet b₁ b₂) (by positivity) b l hgood]
      exact Set.finite_singleton 0
    have hinfi : IsInfinitesimal (muLam (Hyperreal.ofSeq e) (granLat e (latSet b₁ b₂))
        (starSet (boost l '' lineSeg b 0 1)) / Hyperreal.ofSeq e) := by
      unfold starSet granLat
      rw [muLam_div_internal e _ _ hfin, isInfinitesimal_ofSeq_iff]
      intro t ht
      filter_upwards [he, (isInfinitesimal_ofSeq_iff e).1 hinf (t / 4) (by positivity)]
        with k hk hk'
      rw [boosted_seg_lattice (zero_mem_latSet b₁ b₂) (by positivity) b l hgood,
        Set.ncard_singleton]
      rw [abs_of_pos hk] at hk'
      have : (2 * e k) ^ 2 * ((1 : ℕ) : ℝ) / e k = 4 * e k := by field_simp; ring
      rw [this, abs_of_pos (by positivity)]
      linarith
    exact ⟨hinfi, stdPart_of_infinitesimal hinfi⟩

/-! ## Item (iii): every deterministic set, uniformly -/

/-- **`thm:phys-lorentz-retained` (iii).** Let `Λ = [Λₖ]` be internal, `ε = [eₖ]` a
positive infinitesimal, and `D` a standard set with `Λ ∩ *D` hyperfinite and
`#(Λ ∩ *D) ≤ C (2ε)⁻²`. Let `F = {s b : s₀ ≤ s ≤ s₁}` with `0 < s₀ < s₁`, `b`
non-null, and `B_l F ⊆ D` for `l ∈ [1,2]`. If for every internal boost
`l = [lₖ] ∈ *[1,2]` the change `|μ_Λ(*B_l F) - μ_Λ(F)|/ε` is infinitesimal, then
`μ_Λ(F)/ε` is infinitesimal, so `ρ(F) = 0`. -/
theorem retained_uniform (Λs : ℕ → Set (ℝ × ℝ)) (D : Set (ℝ × ℝ)) (C : ℝ) (e : ℕ → ℝ)
    (he0 : 0 < Hyperreal.ofSeq e)
    (hD : IsHyperfinite (internal Λs ∩ starSet D))
    (hcount : HypMeasure.hcardR (internal Λs ∩ starSet D) ≤
      (C : ℝ*) / (2 * Hyperreal.ofSeq e) ^ 2)
    (b : ℝ × ℝ) (hb : b.1 ^ 2 ≠ b.2 ^ 2) (s₀ s₁ : ℝ) (hs₀ : 0 < s₀)
    (hFD : ∀ l ∈ Set.Icc (1 : ℝ) 2, boost l '' lineSeg b s₀ s₁ ⊆ D)
    (hinv : ∀ lseq : ℕ → ℝ, (∀ k, lseq k ∈ Set.Icc (1 : ℝ) 2) →
      IsInfinitesimal (|muLam (Hyperreal.ofSeq e) (internal Λs)
          (internal fun k => boost (lseq k) '' lineSeg b s₀ s₁) -
        muLam (Hyperreal.ofSeq e) (internal Λs) (starSet (lineSeg b s₀ s₁))| /
          Hyperreal.ofSeq e)) :
    IsInfinitesimal (muLam (Hyperreal.ofSeq e) (internal Λs) (starSet (lineSeg b s₀ s₁)) /
        Hyperreal.ofSeq e) ∧
      rhoSeg (Hyperreal.ofSeq e) (internal Λs) (starSet (lineSeg b s₀ s₁)) = 0 := by
  classical
  set F := lineSeg b s₀ s₁ with hFdef
  have he : ∀ᶠ k in (hyperfilter ℕ : Filter ℕ), 0 < e k := Hyperreal.ofSeq_lt_ofSeq.1 he0
  have hb0 : b ≠ 0 := by intro h; apply hb; rw [h]; simp
  -- levels of `Λ ∩ *D`: finite, with the count bound
  obtain ⟨A, hA⟩ := hD
  have hlev : ∀ᶠ k in (hyperfilter ℕ : Filter ℕ), Λs k ∩ D = (A k : Set (ℝ × ℝ)) := by
    unfold starSet hfin at hA
    rw [← internal_inter] at hA
    exact (internal_eq_iff _ _).1 hA
  have hDfin : ∀ᶠ k in (hyperfilter ℕ : Filter ℕ), (Λs k ∩ D).Finite := by
    filter_upwards [hlev] with k hk; rw [hk]; exact Finset.finite_toSet _
  have hcount' : ∀ᶠ k in (hyperfilter ℕ : Filter ℕ),
      ((Λs k ∩ D).ncard : ℝ) ≤ C / (2 * e k) ^ 2 := by
    have h1 : internal Λs ∩ starSet D = internal (fun k => Λs k ∩ D) := by
      unfold starSet; rw [← internal_inter]
    rw [h1, hcardR_internal_of_finite _ hDfin] at hcount
    exact Hyperreal.ofSeq_le_ofSeq.1 hcount
  -- `N k l = #(B_l F ∩ Λₖ)`
  set N : ℕ → ℝ → ℝ := fun k l => ((boost l '' F ∩ Λs k).ncard : ℝ)
  have hsubD : ∀ k, ∀ l ∈ Set.Icc (1 : ℝ) 2, boost l '' F ∩ Λs k ⊆ Λs k ∩ D :=
    fun k l hl x hx => ⟨hx.2, hFD l hl hx.1⟩
  have hNfin : ∀ᶠ k in (hyperfilter ℕ : Filter ℕ), ∀ l ∈ Set.Icc (1 : ℝ) 2,
      (boost l '' F ∩ Λs k).Finite := by
    filter_upwards [hDfin] with k hk l hl using hk.subset (hsubD k l hl)
  have hone : (1 : ℝ) ∈ Set.Icc (1 : ℝ) 2 := ⟨le_rfl, by norm_num⟩
  have hF1 : boost 1 '' F = F := by
    ext x; simp [boost_one]
  -- `μ(F)/ε` as a germ
  have hμF : muLam (Hyperreal.ofSeq e) (internal Λs) (starSet F) / Hyperreal.ofSeq e =
      Hyperreal.ofSeq (fun k => 4 * e k * N k 1) := by
    have hfin : ∀ᶠ k in (hyperfilter ℕ : Filter ℕ), ((fun _ => F) k ∩ Λs k).Finite := by
      filter_upwards [hNfin] with k hk
      have := hk 1 hone; rwa [hF1] at this
    unfold starSet
    rw [muLam_div_internal e _ _ hfin]
    refine Germ.coe_eq.2 ?_
    filter_upwards [he] with k hk
    simp only [N, hF1]
    field_simp; ring
  have hres : IsInfinitesimal
      (muLam (Hyperreal.ofSeq e) (internal Λs) (starSet F) / Hyperreal.ofSeq e) := by
    rw [hμF, isInfinitesimal_ofSeq_iff]
    intro r hr
    by_contra hnot
    have hbig : ∀ᶠ k in (hyperfilter ℕ : Filter ℕ), r ≤ 4 * e k * N k 1 := by
      have := (Ultrafilter.eventually_not (f := hyperfilter ℕ)).2 hnot
      filter_upwards [this, he] with k hk hk'
      push Not at hk
      rwa [abs_of_nonneg (by positivity)] at hk
    -- uniformly in `l ∈ [1,2]`, `4 e N(l) ≥ r/2`
    have hunif : ∀ᶠ k in (hyperfilter ℕ : Filter ℕ), ∀ l ∈ Set.Icc (1 : ℝ) 2,
        r / 2 ≤ 4 * e k * N k l := by
      by_contra hnu
      have hbad := (Ultrafilter.eventually_not (f := hyperfilter ℕ)).2 hnu
      set lseq : ℕ → ℝ := fun k =>
        if h : ∃ l ∈ Set.Icc (1 : ℝ) 2, 4 * e k * N k l < r / 2 then h.choose else 1
      have hlseq : ∀ k, lseq k ∈ Set.Icc (1 : ℝ) 2 := by
        intro k; simp only [lseq]; split_ifs with h
        · exact h.choose_spec.1
        · exact hone
      have hlbad : ∀ᶠ k in (hyperfilter ℕ : Filter ℕ), 4 * e k * N k (lseq k) < r / 2 := by
        filter_upwards [hbad] with k hk
        push Not at hk
        have h : ∃ l ∈ Set.Icc (1 : ℝ) 2, 4 * e k * N k l < r / 2 := hk
        simp only [lseq, h, ↓reduceDIte]
        exact h.choose_spec.2
      have hI := hinv lseq hlseq
      have hfinl : ∀ᶠ k in (hyperfilter ℕ : Filter ℕ),
          (boost (lseq k) '' F ∩ Λs k).Finite := by
        filter_upwards [hNfin] with k hk using hk _ (hlseq k)
      have hval : |muLam (Hyperreal.ofSeq e) (internal Λs)
            (internal fun k => boost (lseq k) '' F) -
          muLam (Hyperreal.ofSeq e) (internal Λs) (starSet F)| / Hyperreal.ofSeq e =
          Hyperreal.ofSeq (fun k => |4 * e k * N k (lseq k) - 4 * e k * N k 1|) := by
        have hfin1 : ∀ᶠ k in (hyperfilter ℕ : Filter ℕ), ((fun _ => F) k ∩ Λs k).Finite := by
          filter_upwards [hNfin] with k hk
          have := hk 1 hone; rwa [hF1] at this
        unfold muLam starSet
        rw [← internal_inter, ← internal_inter, hcardR_internal_of_finite _ hfinl,
          hcardR_internal_of_finite _ hfin1]
        show Hyperreal.ofSeq (fun k => |(2 * e k) ^ 2 * ((boost (lseq k) '' F ∩ Λs k).ncard : ℝ)
            - (2 * e k) ^ 2 * ((F ∩ Λs k).ncard : ℝ)| / e k) = _
        refine Germ.coe_eq.2 ?_
        filter_upwards [he] with k hk
        simp only [N, hF1]
        have h4 : ∀ x y : ℝ, (2 * e k) ^ 2 * x - (2 * e k) ^ 2 * y =
            e k * (4 * e k * x - 4 * e k * y) := fun x y => by ring
        rw [h4, abs_mul, abs_of_pos hk]
        field_simp
      rw [hval, isInfinitesimal_ofSeq_iff] at hI
      obtain ⟨k, h1, h2, h3⟩ := (hbig.and (hlbad.and (hI (r / 2) (by positivity)))).exists
      have h4 := (abs_lt.1 (lt_of_le_of_lt (le_abs_self _) h3)).1
      linarith
    -- pick a level and count `K` boosted segments
    obtain ⟨k, hk, hcnt, hDf, hu⟩ := (he.and (hcount'.and (hDfin.and hunif))).exists
    set K : ℕ := ⌈2 * C / (r * e k)⌉₊ + 1 with hKdef
    have hKpos : 0 < K := Nat.succ_pos _
    have hKgt : 2 * C / (r * e k) < K := by
      have := Nat.le_ceil (2 * C / (r * e k)); push_cast [hKdef]; linarith
    set Ls : Finset ℝ := (Finset.range K).image fun j : ℕ => 1 + (j : ℝ) / K
    have hKr : (0 : ℝ) < K := by exact_mod_cast hKpos
    have hLs_mem : ∀ l ∈ Ls, l ∈ Set.Icc (1 : ℝ) 2 := by
      intro l hl
      simp only [Ls, Finset.mem_image, Finset.mem_range] at hl
      obtain ⟨j, hj, rfl⟩ := hl
      have hj' : (j : ℝ) ≤ K := by exact_mod_cast hj.le
      constructor
      · have : 0 ≤ (j : ℝ) / K := by positivity
        linarith
      · have : (j : ℝ) / K ≤ 1 := (div_le_one hKr).2 hj'
        linarith
    have hLs_card : Ls.card = K := by
      rw [Finset.card_image_of_injective, Finset.card_range]
      intro j j' h
      simp only [add_right_inj] at h
      have := (div_left_inj' hKr.ne').1 h
      exact_mod_cast this
    set Λf : Finset (ℝ × ℝ) := hDf.toFinset
    have hsum := sum_boosted_lines_le Λf Ls
      (fun l hl => lt_of_lt_of_le one_pos (hLs_mem l hl).1) b hb
    have hterm : ∀ l ∈ Ls, N k l ≤
        ((Λf.filter (fun x => x ≠ 0 ∧ ∃ s : ℝ, x = s • boost l b)).card : ℝ) := by
      intro l hl
      have hl' := hLs_mem l hl
      have hlpos : 0 < l := lt_of_lt_of_le one_pos hl'.1
      simp only [N]
      rw [← Set.ncard_coe_finset]
      refine Nat.cast_le.2 (Set.ncard_le_ncard ?_ (Finset.finite_toSet _))
      rintro x ⟨⟨_, ⟨s, hs0, hs1, rfl⟩, rfl⟩, hxΛ⟩
      rw [Finset.coe_filter]
      refine ⟨?_, ?_, s, boost_smul_pt l s b⟩
      · rw [Set.Finite.mem_toFinset]
        exact ⟨hxΛ, hFD l hl' ⟨s • b, ⟨s, hs0, hs1, rfl⟩, rfl⟩⟩
      · rw [boost_smul_pt]
        exact smul_ne_zero (by linarith) (boost_ne_zero_of_ne hlpos hb0)
    have hsumR : ∑ l ∈ Ls, N k l ≤ C / (2 * e k) ^ 2 := by
      calc ∑ l ∈ Ls, N k l
          ≤ ∑ l ∈ Ls, ((Λf.filter (fun x => x ≠ 0 ∧ ∃ s : ℝ, x = s • boost l b)).card : ℝ) :=
            Finset.sum_le_sum hterm
        _ ≤ (Λf.card : ℝ) := by exact_mod_cast hsum
        _ = ((Λs k ∩ D).ncard : ℝ) := by rw [Set.ncard_eq_toFinset_card _ hDf]
        _ ≤ C / (2 * e k) ^ 2 := hcnt
    have hlow : (K : ℝ) * (r / (8 * e k)) ≤ ∑ l ∈ Ls, N k l := by
      calc (K : ℝ) * (r / (8 * e k)) = ∑ _l ∈ Ls, r / (8 * e k) := by
            rw [Finset.sum_const, hLs_card, nsmul_eq_mul]
        _ ≤ ∑ l ∈ Ls, N k l := by
            refine Finset.sum_le_sum fun l hl => ?_
            have := hu l (hLs_mem l hl)
            rw [div_le_iff₀ (by positivity)]
            nlinarith
    have h1 := mul_lt_mul_of_pos_right hKgt (show 0 < r / (8 * e k) by positivity)
    have h2 : 2 * C / (r * e k) * (r / (8 * e k)) = C / (2 * e k) ^ 2 := by
      field_simp; ring
    linarith
  exact ⟨hres, stdPart_of_infinitesimal hres⟩

end QE.OpenGeo
