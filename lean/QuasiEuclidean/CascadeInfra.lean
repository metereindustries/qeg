-- SPDX-License-Identifier: MIT
-- Copyright 2026 Metere Industries, Inc. Author: Alfredo Metere.
-- Quasi-Euclidean Granular Geometry. Any derivative work must carry this notice:
--   This work is derivative of the Quasi-Euclidean Granular Geometry book
--   authored by Alfredo Metere. Copyright 2026 Metere Industries, Inc.
--   All rights reserved
-- See LICENSE.md and NOTICE.

import QuasiEuclidean.OpenDyn
import QuasiEuclidean.NSA_Internal

/-!
# Every standard level of the granular cascade survives

The standard-part step of `prop:dyn-cascade-standard`: a classical attracting
cycle of the logistic map `ℓ_r(x) = r x (1 - x)` (standard `r`, standard period
`P`, multiplier `0 < |μ| < 1`) produces, for every sufficiently fine lattice
`{k/M}` (equivalently, at every unlimited `M`, i.e. infinitesimal granule), a
cycle of lattice intervals `U_i ∋ c_i` mapped into one another by the snapped
logistic map `QE.OpenDyn.snapLogistic r M`, monotonically in the sense of
`ℓ_r'(c_i)`.  The combinatorial core `QE.OpenDyn.block_cycle_period`
(`thm:dyn-cycle-blocks`) then gives the period `P` (`μ > 0`) or `P`/`2P`
(`μ < 0`).

* A. Mean-value contraction estimates (Mathlib's derivative and MVT):
  `image_near_of_deriv_le`, `mapsTo_Icc_of_deriv_le`,
  `invariant_Icc_of_contraction`.
* B. Cycles of blocks with signs: `exists_periodic_of_mapsTo`,
  `mem_periodicPts_of_iterate`, `mapsTo_iterate_blocks`,
  `period_of_interval_cycle`, `iterate_sign_on_blocks`,
  `prod_range_shift_periodic`, `period_of_signed_interval_cycle`.
* C. The snapped logistic map: `snapIdx_err`, `snapIdx_mono`,
  `snapLogistic_val`, `lattice_mapsTo`, `lattice_monotoneOn`,
  `lattice_antitoneOn`, `latI_disjoint`, `nearest_mem`, `snap_shadow`.
* D. Standard-part theorems: `exists_lattice_cycle_intervals`,
  `lattice_cycle_period`, `half_orbit_period`, and their transfer to an
  unlimited `M`: `eventually_hyper_of_atTop`, `cycle_intervals_unlimited`,
  `cycle_period_unlimited`, `half_orbit_period_unlimited`.

No measure theory is used.
-/

namespace QE.CascadeInfra

open Function Set Filter Topology

/-! ## A. Mean-value contraction estimates -/

/-- **Mean-value estimate.**  If `|f'| ≤ L` on `[c - δ, c + δ]` and `y` is within `ε`
of `f x` for some `x` in that interval, then `|y - f c| ≤ L δ + ε`. -/
theorem image_near_of_deriv_le {f f' : ℝ → ℝ} {c δ L : ℝ}
    (hf : ∀ x ∈ Icc (c - δ) (c + δ), HasDerivAt f (f' x) x)
    (hL : ∀ x ∈ Icc (c - δ) (c + δ), |f' x| ≤ L)
    {x : ℝ} (hx : x ∈ Icc (c - δ) (c + δ)) {y ε : ℝ} (hy : |y - f x| ≤ ε) :
    |y - f c| ≤ L * δ + ε := by
  have hc : c ∈ Icc (c - δ) (c + δ) := ⟨by linarith [hx.1, hx.2], by linarith [hx.1, hx.2]⟩
  have h := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun z hz => (hf z hz).hasDerivWithinAt)
    (fun z hz => by simpa [Real.norm_eq_abs] using hL z hz) (convex_Icc _ _) hc hx
  simp only [Real.norm_eq_abs] at h
  have hxc : |x - c| ≤ δ := abs_sub_le_iff.2 ⟨by linarith [hx.2], by linarith [hx.1]⟩
  have hL0 : 0 ≤ L := (abs_nonneg _).trans (hL c hc)
  calc |y - f c| = |(y - f x) + (f x - f c)| := by ring_nf
    _ ≤ |y - f x| + |f x - f c| := abs_add_le _ _
    _ ≤ ε + L * δ := add_le_add hy (h.trans (mul_le_mul_of_nonneg_left hxc hL0))
    _ = L * δ + ε := add_comm _ _

/-- **A perturbed map sends an interval into an interval.**  If `|f'| ≤ L` on
`[c - δ, c + δ]`, `|g - f| ≤ ε` there, and `L δ + ε ≤ δ'`, then `g` maps
`[c - δ, c + δ]` into `[f c - δ', f c + δ']`. -/
theorem mapsTo_Icc_of_deriv_le {f f' g : ℝ → ℝ} {c δ L ε δ' : ℝ}
    (hf : ∀ x ∈ Icc (c - δ) (c + δ), HasDerivAt f (f' x) x)
    (hL : ∀ x ∈ Icc (c - δ) (c + δ), |f' x| ≤ L)
    (hg : ∀ x ∈ Icc (c - δ) (c + δ), |g x - f x| ≤ ε) (hδ : L * δ + ε ≤ δ') :
    MapsTo g (Icc (c - δ) (c + δ)) (Icc (f c - δ') (f c + δ')) := by
  intro x hx
  have := (image_near_of_deriv_le hf hL hx (hg x hx)).trans hδ
  rw [abs_le] at this
  exact ⟨by linarith [this.1], by linarith [this.2]⟩

/-- **Invariant interval of a perturbed contraction.**  If `f c = c`, `|f'| ≤ q`
on `[c - δ, c + δ]`, and `|g - f| ≤ ε ≤ (1 - q) δ` there, then `g` maps
`[c - δ, c + δ]` into itself.  (Applied to `f = ℓ_r^P` this is the finitary form of
the standard-part step.) -/
theorem invariant_Icc_of_contraction {f f' g : ℝ → ℝ} {c δ q ε : ℝ}
    (hf : ∀ x ∈ Icc (c - δ) (c + δ), HasDerivAt f (f' x) x)
    (hq : ∀ x ∈ Icc (c - δ) (c + δ), |f' x| ≤ q) (hfc : f c = c)
    (hg : ∀ x ∈ Icc (c - δ) (c + δ), |g x - f x| ≤ ε) (hε : ε ≤ (1 - q) * δ) :
    MapsTo g (Icc (c - δ) (c + δ)) (Icc (c - δ) (c + δ)) := by
  have := mapsTo_Icc_of_deriv_le hf hq hg (δ' := δ)
    (by linarith [show (1 - q) * δ = δ - q * δ by ring])
  rwa [hfc] at this

/-! ## B. Cycles of blocks -/

/-- A self-map of a finite type mapping a set `U` into itself has a periodic point
in `U` on the forward orbit of every point of `U`. -/
theorem exists_periodic_of_mapsTo {α : Type*} [Finite α] (g : α → α) {U : Set α}
    (hU : MapsTo g U U) {x : α} (hx : x ∈ U) :
    ∃ m, g^[m] x ∈ U ∧ g^[m] x ∈ periodicPts g := by
  obtain ⟨a, b, hab, he⟩ := Finite.exists_ne_map_eq_of_infinite (fun n : ℕ => g^[n] x)
  wlog h : a < b generalizing a b
  · exact this b a hab.symm he.symm (lt_of_le_of_ne (not_lt.1 h) hab.symm)
  refine ⟨a, hU.iterate a hx, b - a, Nat.sub_pos_of_lt h, ?_⟩
  show g^[b - a] (g^[a] x) = g^[a] x
  rw [← iterate_add_apply, Nat.sub_add_cancel h.le]
  exact he.symm

/-- A periodic point of `g^[P]` (`P > 0`) is a periodic point of `g`. -/
theorem mem_periodicPts_of_iterate {α : Type*} {g : α → α} {P : ℕ} (hP : 0 < P) {x : α}
    (hx : x ∈ periodicPts (g^[P])) : x ∈ periodicPts g := by
  obtain ⟨n, hn, h⟩ := hx
  exact ⟨P * n, Nat.mul_pos hP hn, by show g^[P * n] x = x; rw [iterate_mul]; exact h⟩

/-- If `S` maps each block `U i` into `U (i + 1)`, then `S^[k]` maps `U i` into
`U (i + k)`. -/
theorem mapsTo_iterate_blocks {α : Type*} {S : α → α} {U : ℕ → Set α}
    (hmap : ∀ i, MapsTo S (U i) (U (i + 1))) (i k : ℕ) :
    MapsTo (S^[k]) (U i) (U (i + k)) := by
  induction k with
  | zero => intro x hx; simpa using hx
  | succ k ih => rw [iterate_succ']; exact (hmap (i + k)).comp ih

/-- **Periods of a cycle of blocks.**  Let `U` be a `P`-periodic family of pairwise
disjoint (for indices `< P`) subsets of a linear order, with `S (U i) ⊆ U (i+1)`.
A periodic point of `S` in a block `U i₀` has period exactly `P` if the return map
`S^[P]` is monotone on `U i₀`, and `P` or `2P` if it is antitone. -/
theorem period_of_interval_cycle {α : Type*} [LinearOrder α] (S : α → α) {P : ℕ}
    (hP : 0 < P) (U : ℕ → Set α) (hUP : Periodic U P)
    (hdisj : ∀ i < P, ∀ j < P, i ≠ j → Disjoint (U i) (U j))
    (hmap : ∀ i, MapsTo S (U i) (U (i + 1)))
    {i₀ : ℕ} {x : α} (hx : x ∈ U i₀) (hxp : x ∈ periodicPts S) :
    (MonotoneOn (S^[P]) (U i₀) → minimalPeriod S x = P) ∧
      (AntitoneOn (S^[P]) (U i₀) → minimalPeriod S x = P ∨ minimalPeriod S x = 2 * P) := by
  classical
  have hmod : ∀ i, U (i % P) = U i := hUP.map_mod_nat
  have key : ∀ y i j, y ∈ U i → y ∈ U j → ((i : ZMod P) = j) := by
    intro y i j hi hj
    rw [ZMod.natCast_eq_natCast_iff']
    by_contra hne
    rw [← hmod i] at hi
    rw [← hmod j] at hj
    exact Set.disjoint_left.1 (hdisj _ (Nat.mod_lt _ hP) _ (Nat.mod_lt _ hP) hne) hi hj
  let blk : α → ZMod P := fun y =>
    if h : ∃ i, y ∈ U i then ((Classical.choose h : ℕ) : ZMod P) else 0
  have hblk_eq : ∀ y i, y ∈ U i → blk y = i := by
    intro y i hy
    have h : ∃ i, y ∈ U i := ⟨i, hy⟩
    simp only [blk, h, dite_true]
    exact key y _ _ (Classical.choose_spec h) hy
  have hS : MapsTo S (⋃ i, U i) (⋃ i, U i) := by
    intro y hy
    obtain ⟨i, hi⟩ := mem_iUnion.1 hy
    exact mem_iUnion.2 ⟨i + 1, hmap i hi⟩
  have hblk : ∀ y ∈ ⋃ i, U i, blk (S y) = blk y + 1 := by
    intro y hy
    obtain ⟨i, hi⟩ := mem_iUnion.1 hy
    rw [hblk_eq _ _ (hmap i hi), hblk_eq _ _ hi]
    push_cast
    ring
  have hmapU : MapsTo (S^[P]) (U i₀) (U i₀) := by
    have := mapsTo_iterate_blocks hmap i₀ P
    rwa [hUP i₀] at this
  exact QE.OpenDyn.block_cycle_period S P hP blk _ hS hblk (U i₀) (subset_iUnion U i₀)
    hmapU x hx hxp

/-- **Signs compose.**  If `S` is monotone on `U i` when `d i > 0` and antitone when
`d i < 0`, then `S^[k]` on `U i₀` is monotone when `∏_{j<k} d (i₀ + j) > 0` and
antitone when it is `< 0`. -/
theorem iterate_sign_on_blocks {α : Type*} [Preorder α] {S : α → α} {U : ℕ → Set α}
    (hmap : ∀ i, MapsTo S (U i) (U (i + 1))) (d : ℕ → ℝ)
    (hmono : ∀ i, 0 < d i → MonotoneOn S (U i)) (hanti : ∀ i, d i < 0 → AntitoneOn S (U i))
    (i₀ : ℕ) : ∀ k, (0 < ∏ j ∈ Finset.range k, d (i₀ + j) → MonotoneOn (S^[k]) (U i₀)) ∧
      (∏ j ∈ Finset.range k, d (i₀ + j) < 0 → AntitoneOn (S^[k]) (U i₀)) := by
  intro k
  induction k with
  | zero =>
    refine ⟨fun _ => ?_, fun h => by simp at h; linarith⟩
    intro a _ b _ hab
    simpa using hab
  | succ k ih =>
    rw [Finset.prod_range_succ]
    have hk := mapsTo_iterate_blocks hmap i₀ k
    have mm : MonotoneOn S (U (i₀ + k)) → MonotoneOn (S^[k]) (U i₀) →
        MonotoneOn (S^[k + 1]) (U i₀) := by
      intro h1 h2 a ha b hb hab
      rw [iterate_succ_apply', iterate_succ_apply']
      exact h1 (hk ha) (hk hb) (h2 ha hb hab)
    have aa : AntitoneOn S (U (i₀ + k)) → AntitoneOn (S^[k]) (U i₀) →
        MonotoneOn (S^[k + 1]) (U i₀) := by
      intro h1 h2 a ha b hb hab
      rw [iterate_succ_apply', iterate_succ_apply']
      exact h1 (hk hb) (hk ha) (h2 ha hb hab)
    have am : AntitoneOn S (U (i₀ + k)) → MonotoneOn (S^[k]) (U i₀) →
        AntitoneOn (S^[k + 1]) (U i₀) := by
      intro h1 h2 a ha b hb hab
      rw [iterate_succ_apply', iterate_succ_apply']
      exact h1 (hk ha) (hk hb) (h2 ha hb hab)
    have ma : MonotoneOn S (U (i₀ + k)) → AntitoneOn (S^[k]) (U i₀) →
        AntitoneOn (S^[k + 1]) (U i₀) := by
      intro h1 h2 a ha b hb hab
      rw [iterate_succ_apply', iterate_succ_apply']
      exact h1 (hk hb) (hk ha) (h2 ha hb hab)
    constructor
    · intro h
      rcases mul_pos_iff.1 h with ⟨hp, hd⟩ | ⟨hp, hd⟩
      · exact mm (hmono _ hd) (ih.1 hp)
      · exact aa (hanti _ hd) (ih.2 hp)
    · intro h
      rcases mul_neg_iff.1 h with ⟨hp, hd⟩ | ⟨hp, hd⟩
      · exact am (hanti _ hd) (ih.1 hp)
      · exact ma (hmono _ hd) (ih.2 hp)

/-- The product of a `P`-periodic, nowhere-zero sequence over any window of length
`P` is the same. -/
theorem prod_range_shift_periodic {d : ℕ → ℝ} {P : ℕ} (hd : Periodic d P)
    (hd0 : ∀ i, d i ≠ 0) (i₀ : ℕ) :
    ∏ j ∈ Finset.range P, d (i₀ + j) = ∏ j ∈ Finset.range P, d j := by
  induction i₀ with
  | zero => simp
  | succ i ih =>
    rw [← ih]
    have e : ∏ j ∈ Finset.range P, d (i + 1 + j) = ∏ j ∈ Finset.range P, d (i + (j + 1)) :=
      Finset.prod_congr rfl (fun j _ => by rw [add_assoc, add_comm 1 j])
    rw [e]
    apply mul_right_cancel₀ (hd0 i)
    have h1 := Finset.prod_range_succ (fun j => d (i + j)) P
    have h2 := Finset.prod_range_succ' (fun j => d (i + j)) P
    simp only [add_zero, hd i] at h1 h2
    rw [← h2, h1]

/-- **Periods of a signed cycle of blocks** (the combinatorial core with signs).
With `U`, `S` as in `period_of_interval_cycle`, and `S` monotone on `U i` when
`d i > 0`, antitone when `d i < 0` (`d` periodic and nowhere zero), every periodic
point of `S` in any block has period `P` if `∏_{i<P} d i > 0` and `P` or `2P` if
`∏_{i<P} d i < 0`. -/
theorem period_of_signed_interval_cycle {α : Type*} [LinearOrder α] (S : α → α) {P : ℕ}
    (hP : 0 < P) (U : ℕ → Set α) (hUP : Periodic U P)
    (hdisj : ∀ i < P, ∀ j < P, i ≠ j → Disjoint (U i) (U j))
    (hmap : ∀ i, MapsTo S (U i) (U (i + 1))) (d : ℕ → ℝ) (hdP : Periodic d P)
    (hd0 : ∀ i, d i ≠ 0)
    (hmono : ∀ i, 0 < d i → MonotoneOn S (U i)) (hanti : ∀ i, d i < 0 → AntitoneOn S (U i))
    {i₀ : ℕ} {x : α} (hx : x ∈ U i₀) (hxp : x ∈ periodicPts S) :
    (0 < ∏ i ∈ Finset.range P, d i → minimalPeriod S x = P) ∧
      (∏ i ∈ Finset.range P, d i < 0 →
        minimalPeriod S x = P ∨ minimalPeriod S x = 2 * P) := by
  have hcyc := period_of_interval_cycle S hP U hUP hdisj hmap hx hxp
  have hsign := iterate_sign_on_blocks hmap d hmono hanti i₀ P
  rw [prod_range_shift_periodic hdP hd0 i₀] at hsign
  exact ⟨fun h => hcyc.1 (hsign.1 h), fun h => hcyc.2 (hsign.2 h)⟩

/-! ## C. The snapped logistic map -/

/-- The logistic map `ℓ_r(x) = r x (1 - x)`. -/
def ell (r x : ℝ) : ℝ := r * x * (1 - x)

/-- The lattice index of the rounding of `y` to `{k/M}`, clamped to `[0, M]`. -/
noncomputable def snapIdx (M : ℕ) (y : ℝ) : ℕ := min M ⌊(M : ℝ) * y + 1 / 2⌋₊

/-- The position `k/M` of a lattice index. -/
noncomputable def pos (M : ℕ) (k : Fin (M + 1)) : ℝ := ((k : ℕ) : ℝ) / M

/-- The lattice interval `{k : |k/M - c| ≤ δ}`. -/
def latI (M : ℕ) (c δ : ℝ) : Set (Fin (M + 1)) := {k | |pos M k - c| ≤ δ}

/-- The lattice point nearest to `c`. -/
noncomputable def nearest (M : ℕ) (c : ℝ) : Fin (M + 1) :=
  ⟨snapIdx M c, Nat.lt_succ_of_le (min_le_left _ _)⟩

theorem snapIdx_le (M : ℕ) (y : ℝ) : snapIdx M y ≤ M := min_le_left _ _

/-- **Snap error.**  For `y ∈ [0, 1]`, `|snap(y) - y| ≤ 1/(2M)`. -/
theorem snapIdx_err {M : ℕ} (hM : 0 < M) {y : ℝ} (hy0 : 0 ≤ y) (hy1 : y ≤ 1) :
    |(snapIdx M y : ℝ) / M - y| ≤ 1 / (2 * M) := by
  have hMr : (0 : ℝ) < M := by exact_mod_cast hM
  set t := (M : ℝ) * y + 1 / 2 with ht
  have ht0 : 0 ≤ t := by positivity
  have hfl := Nat.floor_le ht0
  have hfl2 := Nat.lt_floor_add_one t
  have hMy : (M : ℝ) * y ≤ M := mul_le_of_le_one_right hMr.le hy1
  have hle : ⌊t⌋₊ ≤ M := by
    have : (⌊t⌋₊ : ℝ) < ((M + 1 : ℕ) : ℝ) := by push_cast; linarith
    exact Nat.lt_succ_iff.1 (Nat.cast_lt.1 this)
  have hs : snapIdx M y = ⌊t⌋₊ := min_eq_right hle
  rw [hs]
  have h1 : (⌊t⌋₊ : ℝ) - M * y ≤ 1 / 2 := by linarith
  have h2 : -(1 / 2) ≤ (⌊t⌋₊ : ℝ) - M * y := by linarith
  have e : (⌊t⌋₊ : ℝ) / M - y = ((⌊t⌋₊ : ℝ) - M * y) / M := by field_simp
  rw [e, abs_div, abs_of_pos hMr, div_le_div_iff₀ hMr (by positivity)]
  have := abs_le.2 ⟨h2, h1⟩
  nlinarith

theorem snapIdx_mono (M : ℕ) : Monotone (snapIdx M) := by
  intro a b h
  apply min_le_min_left
  apply Nat.floor_le_floor
  have := Nat.cast_nonneg (α := ℝ) M
  nlinarith

theorem pos_mem_Icc {M : ℕ} (hM : 0 < M) (k : Fin (M + 1)) : pos M k ∈ Icc (0 : ℝ) 1 := by
  have hMr : (0 : ℝ) < M := by exact_mod_cast hM
  have hk : ((k : ℕ) : ℝ) ≤ M := by exact_mod_cast Nat.lt_succ_iff.1 k.isLt
  exact ⟨by unfold pos; positivity, by unfold pos; rw [div_le_one hMr]; exact hk⟩

theorem pos_mono {M : ℕ} {a b : Fin (M + 1)} (h : a ≤ b) : pos M a ≤ pos M b := by
  unfold pos
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  exact_mod_cast Fin.le_iff_val_le_val.1 h

/-- `snapLogistic r M k` is the snap of `ℓ_r(k/M)`. -/
theorem snapLogistic_val {r : ℝ} {M : ℕ} (hM : 0 < M) (k : Fin (M + 1)) :
    ((QE.OpenDyn.snapLogistic r M k : Fin (M + 1)) : ℕ) = snapIdx M (ell r (pos M k)) := by
  unfold QE.OpenDyn.snapLogistic snapIdx ell pos
  have hMr : (M : ℝ) ≠ 0 := by positivity
  simp only
  congr 3
  field_simp

theorem ell_sub (r x y : ℝ) : ell r x - ell r y = (x - y) * (r * (1 - x - y)) := by
  unfold ell; ring

theorem ell_mem_Icc {r x : ℝ} (hr0 : 0 ≤ r) (hr4 : r ≤ 4) (hx : x ∈ Icc (0 : ℝ) 1) :
    ell r x ∈ Icc (0 : ℝ) 1 := by
  unfold ell
  have h0 : 0 ≤ x * (1 - x) := mul_nonneg hx.1 (sub_nonneg.2 hx.2)
  have h1 : x * (1 - x) ≤ 1 / 4 := by nlinarith [sq_nonneg (x - 1 / 2)]
  have h2 := mul_le_mul_of_nonneg_left h1 hr0
  have h3 := mul_nonneg hr0 h0
  constructor <;> nlinarith

theorem ell_iterate_mem_Icc {r x : ℝ} (hr0 : 0 ≤ r) (hr4 : r ≤ 4) (hx : x ∈ Icc (0 : ℝ) 1) :
    ∀ m, (ell r)^[m] x ∈ Icc (0 : ℝ) 1 := by
  intro m
  induction m with
  | zero => simpa using hx
  | succ m ih => rw [iterate_succ_apply']; exact ell_mem_Icc hr0 hr4 ih

theorem ell_hasDerivAt (r x : ℝ) : HasDerivAt (ell r) (r * (1 - 2 * x)) x := by
  have := ((hasDerivAt_id' x).const_mul r).mul ((hasDerivAt_const x (1 : ℝ)).sub (hasDerivAt_id' x))
  convert this using 1
  · ext y; simp [ell]
  · simp; ring

theorem ell_lip {r x y : ℝ} (hr0 : 0 ≤ r) (hx : x ∈ Icc (0 : ℝ) 1) (hy : y ∈ Icc (0 : ℝ) 1) :
    |ell r x - ell r y| ≤ r * |x - y| := by
  rw [ell_sub, abs_mul, abs_mul, abs_of_nonneg hr0]
  have : |1 - x - y| ≤ 1 := abs_le.2 ⟨by linarith [hx.2, hy.2], by linarith [hx.1, hy.1]⟩
  have h := mul_le_mul_of_nonneg_left this hr0
  have := abs_nonneg (x - y)
  nlinarith

/-- **One step of the snapped map on lattice intervals** (mean value theorem).
If `(|ℓ_r'(c)| + 2 r δ) δ + 1/(2M) ≤ δ'`, the snapped logistic map sends the lattice
interval of radius `δ` around `c` into the lattice interval of radius `δ'` around
`ℓ_r(c)`. -/
theorem lattice_mapsTo {r : ℝ} (hr0 : 0 ≤ r) (hr4 : r ≤ 4) {M : ℕ} (hM : 0 < M) {c δ δ' : ℝ}
    (hδ : (|r * (1 - 2 * c)| + 2 * r * δ) * δ + 1 / (2 * M) ≤ δ') :
    MapsTo (QE.OpenDyn.snapLogistic r M) (latI M c δ) (latI M (ell r c) δ') := by
  intro k hk
  have hk' : |pos M k - c| ≤ δ := hk
  have hx : pos M k ∈ Icc (c - δ) (c + δ) :=
    ⟨by linarith [(abs_le.1 hk').1], by linarith [(abs_le.1 hk').2]⟩
  have hpk := pos_mem_Icc hM k
  have hE := ell_mem_Icc hr0 hr4 hpk
  have herr := snapIdx_err hM hE.1 hE.2
  have hder : ∀ x ∈ Icc (c - δ) (c + δ),
      |r * (1 - 2 * x)| ≤ |r * (1 - 2 * c)| + 2 * r * δ := by
    intro x hx
    have e : r * (1 - 2 * x) = r * (1 - 2 * c) + (-(2 * r) * (x - c)) := by ring
    rw [e]
    refine (abs_add_le _ _).trans (add_le_add le_rfl ?_)
    rw [abs_mul, abs_neg, abs_of_nonneg (by linarith : (0 : ℝ) ≤ 2 * r)]
    exact mul_le_mul_of_nonneg_left
      (abs_sub_le_iff.2 ⟨by linarith [hx.2], by linarith [hx.1]⟩) (by linarith)
  have := image_near_of_deriv_le (fun x _ => ell_hasDerivAt r x) hder hx herr
  show |pos M _ - ell r c| ≤ δ'
  unfold pos
  rw [snapLogistic_val hM]
  exact this.trans hδ

/-- On a lattice interval where `ℓ_r' > 0` stays positive, the snapped map is
monotone. -/
theorem lattice_monotoneOn {r : ℝ} (hr0 : 0 ≤ r) {M : ℕ} (hM : 0 < M) {c δ : ℝ}
    (hδ : 2 * r * δ ≤ r * (1 - 2 * c)) :
    MonotoneOn (QE.OpenDyn.snapLogistic r M) (latI M c δ) := by
  intro a ha b hb hab
  have ha' : |pos M a - c| ≤ δ := ha
  have hb' : |pos M b - c| ≤ δ := hb
  rw [Fin.le_iff_val_le_val, snapLogistic_val hM, snapLogistic_val hM]
  apply snapIdx_mono
  have hpab : pos M a ≤ pos M b := pos_mono hab
  have hfac : 0 ≤ r * (1 - pos M b - pos M a) := by
    have h1 := abs_le.1 ha'
    have h2 := abs_le.1 hb'
    have := mul_le_mul_of_nonneg_left
      (show (pos M b - c) + (pos M a - c) ≤ 2 * δ by linarith) hr0
    nlinarith
  have := ell_sub r (pos M b) (pos M a)
  nlinarith [mul_nonneg (sub_nonneg.2 hpab) hfac]

/-- On a lattice interval where `ℓ_r' < 0` stays negative, the snapped map is
antitone. -/
theorem lattice_antitoneOn {r : ℝ} (hr0 : 0 ≤ r) {M : ℕ} (hM : 0 < M) {c δ : ℝ}
    (hδ : 2 * r * δ ≤ -(r * (1 - 2 * c))) :
    AntitoneOn (QE.OpenDyn.snapLogistic r M) (latI M c δ) := by
  intro a ha b hb hab
  have ha' : |pos M a - c| ≤ δ := ha
  have hb' : |pos M b - c| ≤ δ := hb
  rw [Fin.le_iff_val_le_val, snapLogistic_val hM, snapLogistic_val hM]
  apply snapIdx_mono
  have hpab : pos M a ≤ pos M b := pos_mono hab
  have hfac : r * (1 - pos M b - pos M a) ≤ 0 := by
    have h1 := abs_le.1 ha'
    have h2 := abs_le.1 hb'
    have := mul_le_mul_of_nonneg_left
      (show -(2 * δ) ≤ (pos M b - c) + (pos M a - c) by linarith) hr0
    nlinarith
  have := ell_sub r (pos M b) (pos M a)
  nlinarith [mul_nonneg (sub_nonneg.2 hpab) (neg_nonneg.2 hfac)]

theorem latI_disjoint {M : ℕ} {c c' δ δ' : ℝ} (h : δ + δ' < |c - c'|) :
    Disjoint (latI M c δ) (latI M c' δ') := by
  rw [Set.disjoint_left]
  intro k h1 h2
  have h1' : |pos M k - c| ≤ δ := h1
  have h2' : |pos M k - c'| ≤ δ' := h2
  have := abs_sub_le c (pos M k) c'
  rw [abs_sub_comm c (pos M k)] at this
  linarith

theorem nearest_mem {M : ℕ} (hM : 0 < M) {c δ : ℝ} (hc : c ∈ Icc (0 : ℝ) 1)
    (hδ : 1 / (2 * M) ≤ δ) : nearest M c ∈ latI M c δ :=
  (snapIdx_err hM hc.1 hc.2).trans hδ

/-- **Shadowing for standard times.**  The snapped orbit of the lattice point nearest
`x₀ ∈ [0,1]` stays within `5^m / M` of the classical orbit (`0 ≤ r ≤ 4`). -/
theorem snap_shadow {r : ℝ} (hr0 : 0 ≤ r) (hr4 : r ≤ 4) {M : ℕ} (hM : 0 < M) {x₀ : ℝ}
    (hx₀ : x₀ ∈ Icc (0 : ℝ) 1) (m : ℕ) :
    |pos M ((QE.OpenDyn.snapLogistic r M)^[m] (nearest M x₀)) - (ell r)^[m] x₀| ≤
      5 ^ m / M := by
  have hMr : (0 : ℝ) < M := by exact_mod_cast hM
  induction m with
  | zero =>
    simp only [iterate_zero, id_eq, pow_zero]
    refine (snapIdx_err hM hx₀.1 hx₀.2).trans ?_
    rw [div_le_div_iff₀ (by positivity) hMr]
    linarith
  | succ m ih =>
    rw [iterate_succ_apply', iterate_succ_apply']
    set k := (QE.OpenDyn.snapLogistic r M)^[m] (nearest M x₀)
    set x := (ell r)^[m] x₀
    have hx := ell_iterate_mem_Icc hr0 hr4 hx₀ m
    have hpk := pos_mem_Icc hM k
    have hE := ell_mem_Icc hr0 hr4 hpk
    have herr := snapIdx_err hM hE.1 hE.2
    have hlip := ell_lip hr0 hpk hx
    have e : pos M (QE.OpenDyn.snapLogistic r M k) = (snapIdx M (ell r (pos M k)) : ℝ) / M := by
      show (((QE.OpenDyn.snapLogistic r M k : Fin (M + 1)) : ℕ) : ℝ) / M = _
      rw [snapLogistic_val hM]
    rw [e]
    have h5 : (1 : ℝ) ≤ 5 ^ m := one_le_pow₀ (by norm_num)
    have hq : 1 / (2 * (M : ℝ)) ≤ 5 ^ m / M := by
      rw [div_le_div_iff₀ (by positivity) hMr]; nlinarith
    have hr : r * |pos M k - x| ≤ 4 * (5 ^ m / M) :=
      (mul_le_mul_of_nonneg_left ih hr0).trans
        (mul_le_mul_of_nonneg_right hr4 (by positivity))
    have e5 : (5 : ℝ) ^ (m + 1) / M = 5 * (5 ^ m / M) := by rw [pow_succ]; ring
    rw [e5]
    calc |(snapIdx M (ell r (pos M k)) : ℝ) / M - ell r x|
        = |((snapIdx M (ell r (pos M k)) : ℝ) / M - ell r (pos M k)) +
            (ell r (pos M k) - ell r x)| := by ring_nf
      _ ≤ |(snapIdx M (ell r (pos M k)) : ℝ) / M - ell r (pos M k)| +
            |ell r (pos M k) - ell r x| := abs_add_le _ _
      _ ≤ 5 * (5 ^ m / M) := by linarith

/-! ## D. The standard-part theorems -/

/-- The multiplier `μ = ∏_{i<P} ℓ_r'(c_i)` of the cycle `c`. -/
def multiplier (r : ℝ) (c : ℕ → ℝ) (P : ℕ) : ℝ := ∏ i ∈ Finset.range P, r * (1 - 2 * c i)

/-- The partial products `∏_{j<a} (|d j| + β)` used as radii weights. -/
def wt (d : ℕ → ℝ) (β : ℝ) (a : ℕ) : ℝ := ∏ j ∈ Finset.range a, (|d j| + β)

theorem wt_zero (d : ℕ → ℝ) (β : ℝ) : wt d β 0 = 1 := by simp [wt]

theorem wt_succ (d : ℕ → ℝ) (β : ℝ) (a : ℕ) : wt d β (a + 1) = wt d β a * (|d a| + β) :=
  Finset.prod_range_succ _ _

theorem wt_pos (d : ℕ → ℝ) {β : ℝ} (hβ : 0 < β) (a : ℕ) : 0 < wt d β a :=
  Finset.prod_pos (fun j _ => by positivity)

theorem ev_mul_lt {K A : ℝ} (hA : 0 < A) : ∀ᶠ ρ in 𝓝 (0 : ℝ), ρ * K < A := by
  have h : Tendsto (fun ρ : ℝ => ρ * K) (𝓝 0) (𝓝 (0 * K)) := tendsto_id.mul_const K
  rw [zero_mul] at h
  exact h.eventually (gt_mem_nhds hA)

/-- The derivatives `ℓ_r'(c_i)` along a cycle with nonzero multiplier are
`P`-periodic and nowhere zero. -/
theorem deriv_cycle_facts {r : ℝ} {P : ℕ} {c : ℕ → ℝ} (hP : 0 < P) (hcP : Periodic c P)
    (hμ0 : multiplier r c P ≠ 0) :
    Periodic (fun i => r * (1 - 2 * c i)) P ∧ ∀ i, r * (1 - 2 * c i) ≠ 0 := by
  have hdP : Periodic (fun i => r * (1 - 2 * c i)) P := fun i => by simp only [hcP i]
  refine ⟨hdP, fun i => ?_⟩
  have hd0' := Finset.prod_ne_zero_iff.1 hμ0
  have := hdP.map_mod_nat i
  rw [← this]
  exact hd0' _ (Finset.mem_range.2 (Nat.mod_lt _ hP))

/-- **The standard-part step: invariant lattice intervals.**  Let `0 ≤ r ≤ 4` and let
`c` be a cycle of `ℓ_r` in `[0,1]` of (minimal) period `P` with multiplier
`μ = ∏_{i<P} ℓ_r'(c_i)`, `0 < |μ| < 1`.  For every `η > 0` there are radii
`0 < δ_i ≤ η` (`P`-periodic, bounded below) such that for every sufficiently large
`M` the lattice intervals `U_i = {k : |k/M - c_i| ≤ δ_i}` are nonempty, pairwise
disjoint, mapped into one another by the snapped logistic map
(`U_i → U_{i+1}`), monotonically if `ℓ_r'(c_i) > 0` and antitonically if
`ℓ_r'(c_i) < 0`. -/
theorem exists_lattice_cycle_intervals {r : ℝ} {P : ℕ} {c : ℕ → ℝ}
    (hr0 : 0 ≤ r) (hr4 : r ≤ 4) (hP : 0 < P)
    (hcP : Periodic c P) (hc : ∀ i, ell r (c i) = c (i + 1))
    (hinj : ∀ i < P, ∀ j < P, c i = c j → i = j) (hc01 : ∀ i, c i ∈ Icc (0 : ℝ) 1)
    (hμ0 : multiplier r c P ≠ 0) (hμ1 : |multiplier r c P| < 1) {η : ℝ} (hη : 0 < η) :
    ∃ δ : ℕ → ℝ, Periodic δ P ∧ (∀ i, 0 < δ i ∧ δ i ≤ η) ∧ (∃ δlo > 0, ∀ i, δlo ≤ δ i) ∧
      ∀ᶠ M in atTop, 0 < M ∧
        (∀ i, MapsTo (QE.OpenDyn.snapLogistic r M) (latI M (c i) (δ i))
          (latI M (c (i + 1)) (δ (i + 1)))) ∧
        (∀ i, nearest M (c i) ∈ latI M (c i) (δ i)) ∧
        (∀ i, 0 < r * (1 - 2 * c i) →
          MonotoneOn (QE.OpenDyn.snapLogistic r M) (latI M (c i) (δ i))) ∧
        (∀ i, r * (1 - 2 * c i) < 0 →
          AntitoneOn (QE.OpenDyn.snapLogistic r M) (latI M (c i) (δ i))) ∧
        (∀ i < P, ∀ j < P, i ≠ j → Disjoint (latI M (c i) (δ i)) (latI M (c j) (δ j))) := by
  obtain ⟨hdP, hd0⟩ := deriv_cycle_facts hP hcP hμ0
  set d : ℕ → ℝ := fun i => r * (1 - 2 * c i) with hd_def
  have hmod : ∀ i, d (i % P) = d i := hdP.map_mod_nat
  -- the slack `β`
  have hβex : ∃ β > 0, wt d β P < 1 := by
    have hcont : Continuous (fun β : ℝ => ∏ j ∈ Finset.range P, (|d j| + β)) :=
      continuous_finsetProd _ (fun j _ => continuous_const.add continuous_id)
    have h0 : ∏ j ∈ Finset.range P, (|d j| + 0) < 1 := by
      simp only [add_zero, ← Finset.abs_prod]
      exact hμ1
    have hev := (hcont.tendsto 0).eventually (gt_mem_nhds h0)
    obtain ⟨β, hβ, hβpos⟩ :=
      ((hev.filter_mono nhdsWithin_le_nhds).and
        (eventually_mem_nhdsWithin : ∀ᶠ x in 𝓝[>] (0 : ℝ), x ∈ Ioi 0)).exists
    exact ⟨β, hβpos, hβ⟩
  obtain ⟨β, hβ, hQ⟩ := hβex
  have hrec : ∀ i, (|d i| + β) * wt d β (i % P) ≤ wt d β ((i + 1) % P) := by
    intro i
    rw [← hmod i, ← Nat.mod_add_mod i P 1]
    rcases Nat.lt_or_ge (i % P + 1) P with h | h
    · rw [Nat.mod_eq_of_lt h, wt_succ, mul_comm]
    · have h' : i % P + 1 = P := by have := Nat.mod_lt i hP; omega
      have e : wt d β (i % P + 1) = (|d (i % P)| + β) * wt d β (i % P) := by
        rw [wt_succ, mul_comm]
      rw [h'] at e
      rw [h', Nat.mod_self, wt_zero]
      linarith
  -- the scale `ρ`
  have hρev : ∀ᶠ ρ in 𝓝 (0 : ℝ), ∀ a ∈ Finset.range P,
      ρ * (2 * r * wt d β a) < β / 2 ∧ ρ * (2 * r * wt d β a) < |d a| ∧ ρ * wt d β a < η ∧
      ∀ b ∈ Finset.range P, a ≠ b → ρ * (wt d β a + wt d β b) < |c a - c b| := by
    rw [Filter.eventually_all_finset]
    intro a ha
    refine (ev_mul_lt (by positivity)).and ((ev_mul_lt (abs_pos.2 (hd0 a))).and
      ((ev_mul_lt hη).and ?_))
    rw [Filter.eventually_all_finset]
    intro b hb
    by_cases hab : a = b
    · exact Eventually.of_forall (fun _ h => absurd hab h)
    · have : 0 < |c a - c b| := abs_pos.2 (sub_ne_zero.2 (fun h =>
        hab (hinj a (Finset.mem_range.1 ha) b (Finset.mem_range.1 hb) h)))
      exact (ev_mul_lt this).mono (fun _ h _ => h)
  obtain ⟨ρ, hρ, hρpos⟩ := ((hρev.filter_mono nhdsWithin_le_nhds).and
    (eventually_mem_nhdsWithin : ∀ᶠ x in 𝓝[>] (0 : ℝ), x ∈ Ioi 0)).exists
  have hρ0 : 0 < ρ := hρpos
  have hmem : ∀ i, i % P ∈ Finset.range P := fun i => Finset.mem_range.2 (Nat.mod_lt _ hP)
  obtain ⟨a₀, -, hmin⟩ := Finset.exists_min_image (Finset.range P) (wt d β)
    ⟨0, Finset.mem_range.2 hP⟩
  have hδlo : ∀ i, ρ * wt d β a₀ ≤ ρ * wt d β (i % P) :=
    fun i => mul_le_mul_of_nonneg_left (hmin _ (hmem i)) hρ0.le
  have hlo : 0 < ρ * wt d β a₀ := mul_pos hρ0 (wt_pos d hβ a₀)
  refine ⟨fun i => ρ * wt d β (i % P), fun i => by simp only [Nat.add_mod_right],
    fun i => ⟨mul_pos hρ0 (wt_pos d hβ _), (hρ _ (hmem i)).2.2.1.le⟩,
    ⟨ρ * wt d β a₀, hlo, hδlo⟩, ?_⟩
  have hM1 := (tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ)).eventually
    (gt_mem_nhds (show (0 : ℝ) < β / 2 * (ρ * wt d β a₀) by positivity))
  have hM2 := (tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ)).eventually (gt_mem_nhds hlo)
  filter_upwards [hM1, hM2, eventually_ge_atTop 1] with M hM1 hM2 hM1'
  have hM : 0 < M := hM1'
  have hMr : (0 : ℝ) < M := by exact_mod_cast hM
  have hhalf : 1 / (2 * (M : ℝ)) ≤ 1 / M := by
    rw [div_le_div_iff₀ (by positivity) hMr]; linarith
  refine ⟨hM, fun i => ?_, fun i => ?_, fun i hdi => ?_, fun i hdi => ?_,
    fun i hi j hj hij => ?_⟩
  · -- the step `U_i → U_{i+1}`
    have hC1 := (hρ _ (hmem i)).1
    have hw := wt_pos d hβ (i % P)
    have e1 : (2 * r * (ρ * wt d β (i % P))) * (ρ * wt d β (i % P)) ≤
        (β / 2) * (ρ * wt d β (i % P)) :=
      mul_le_mul_of_nonneg_right (by linarith) (mul_pos hρ0 hw).le
    have e2 : ρ * ((|d i| + β) * wt d β (i % P)) ≤ ρ * wt d β ((i + 1) % P) :=
      mul_le_mul_of_nonneg_left (hrec i) hρ0.le
    have e3 : 1 / (2 * (M : ℝ)) ≤ β / 2 * (ρ * wt d β (i % P)) :=
      hhalf.trans (hM1.le.trans (mul_le_mul_of_nonneg_left (hδlo i) (by positivity)))
    have := lattice_mapsTo hr0 hr4 hM (c := c i) (δ := ρ * wt d β (i % P))
      (δ' := ρ * wt d β ((i + 1) % P)) (by
        have : |r * (1 - 2 * c i)| = |d i| := rfl
        rw [this]; nlinarith)
    rwa [hc i] at this
  · exact nearest_mem hM (hc01 i) (hhalf.trans (hM2.le.trans (hδlo i)))
  · have hC2 := (hρ _ (hmem i)).2.1
    rw [hmod i, abs_of_pos hdi] at hC2
    exact lattice_monotoneOn hr0 hM (by linarith)
  · have hC2 := (hρ _ (hmem i)).2.1
    rw [hmod i, abs_of_neg hdi] at hC2
    exact lattice_antitoneOn hr0 hM (by linarith)
  · have hC4 := (hρ i (Finset.mem_range.2 hi)).2.2.2 j (Finset.mem_range.2 hj) hij
    apply latI_disjoint
    simp only [Nat.mod_eq_of_lt hi, Nat.mod_eq_of_lt hj]
    linarith

/-- **Every standard level survives: a granular cycle of period `P` or `2P`.**
Under the hypotheses of `exists_lattice_cycle_intervals`, for every `η > 0` and every
sufficiently large `M`, the snapped logistic map has a periodic point within `η` of
`c_0`; its minimal period is exactly `P` if `μ > 0`, and `P` or `2P` if `μ < 0`. -/
theorem lattice_cycle_period {r : ℝ} {P : ℕ} {c : ℕ → ℝ}
    (hr0 : 0 ≤ r) (hr4 : r ≤ 4) (hP : 0 < P)
    (hcP : Periodic c P) (hc : ∀ i, ell r (c i) = c (i + 1))
    (hinj : ∀ i < P, ∀ j < P, c i = c j → i = j) (hc01 : ∀ i, c i ∈ Icc (0 : ℝ) 1)
    (hμ0 : multiplier r c P ≠ 0) (hμ1 : |multiplier r c P| < 1) {η : ℝ} (hη : 0 < η) :
    ∀ᶠ M in atTop, ∃ k : Fin (M + 1), |pos M k - c 0| ≤ η ∧
      k ∈ periodicPts (QE.OpenDyn.snapLogistic r M) ∧
      (0 < multiplier r c P → minimalPeriod (QE.OpenDyn.snapLogistic r M) k = P) ∧
      (multiplier r c P < 0 → minimalPeriod (QE.OpenDyn.snapLogistic r M) k = P ∨
        minimalPeriod (QE.OpenDyn.snapLogistic r M) k = 2 * P) := by
  obtain ⟨hdP, hd0⟩ := deriv_cycle_facts hP hcP hμ0
  obtain ⟨δ, hδP, hδ, -, hev⟩ :=
    exists_lattice_cycle_intervals hr0 hr4 hP hcP hc hinj hc01 hμ0 hμ1 hη
  filter_upwards [hev] with M ⟨hM, hmap, hnear, hmono, hanti, hdisj⟩
  set S := QE.OpenDyn.snapLogistic r M
  let U : ℕ → Set (Fin (M + 1)) := fun i => latI M (c i) (δ i)
  have hUP : Periodic U P := fun i => by simp only [U, hcP i, hδP i]
  have hmapP : MapsTo (S^[P]) (U 0) (U 0) := by
    have h1 := mapsTo_iterate_blocks (U := U) hmap 0 P
    have h2 := hUP 0
    rw [zero_add] at h1 h2
    rwa [h2] at h1
  obtain ⟨m, hmU, hmper⟩ := exists_periodic_of_mapsTo (S^[P]) hmapP (hnear 0)
  have hxp := mem_periodicPts_of_iterate hP hmper
  have := period_of_signed_interval_cycle S hP U hUP hdisj hmap _ hdP hd0 hmono hanti hmU hxp
  exact ⟨_, (show |pos M _ - c 0| ≤ δ 0 from hmU).trans (hδ 0).2, hxp, this.1, this.2⟩

/-- **The snapped orbit of `1/2` is eventually periodic with period `P` or `2P`.**
If moreover the cycle attracts the critical point (`ℓ_r^n(1/2) - c_{n+j} → 0` for
some phase `j`), then for every sufficiently large `M` the snapped orbit of the
lattice point nearest `1/2` reaches a periodic point of minimal period `P`
(`μ > 0`), or `P` or `2P` (`μ < 0`). -/
theorem half_orbit_period {r : ℝ} {P : ℕ} {c : ℕ → ℝ}
    (hr0 : 0 ≤ r) (hr4 : r ≤ 4) (hP : 0 < P)
    (hcP : Periodic c P) (hc : ∀ i, ell r (c i) = c (i + 1))
    (hinj : ∀ i < P, ∀ j < P, c i = c j → i = j) (hc01 : ∀ i, c i ∈ Icc (0 : ℝ) 1)
    (hμ0 : multiplier r c P ≠ 0) (hμ1 : |multiplier r c P| < 1)
    (hatt : ∃ j, Tendsto (fun n => (ell r)^[n] (1 / 2) - c (n + j)) atTop (𝓝 0)) :
    ∀ᶠ M in atTop, ∃ m : ℕ,
      (QE.OpenDyn.snapLogistic r M)^[m] (nearest M (1 / 2)) ∈
        periodicPts (QE.OpenDyn.snapLogistic r M) ∧
      (0 < multiplier r c P → minimalPeriod (QE.OpenDyn.snapLogistic r M)
        ((QE.OpenDyn.snapLogistic r M)^[m] (nearest M (1 / 2))) = P) ∧
      (multiplier r c P < 0 →
        minimalPeriod (QE.OpenDyn.snapLogistic r M)
          ((QE.OpenDyn.snapLogistic r M)^[m] (nearest M (1 / 2))) = P ∨
        minimalPeriod (QE.OpenDyn.snapLogistic r M)
          ((QE.OpenDyn.snapLogistic r M)^[m] (nearest M (1 / 2))) = 2 * P) := by
  obtain ⟨hdP, hd0⟩ := deriv_cycle_facts hP hcP hμ0
  obtain ⟨δ, hδP, -, ⟨δlo, hδlo, hlo⟩, hev⟩ :=
    exists_lattice_cycle_intervals hr0 hr4 hP hcP hc hinj hc01 hμ0 hμ1 one_pos
  obtain ⟨j, hj⟩ := hatt
  obtain ⟨n, hn⟩ := (Metric.tendsto_nhds.1 hj (δlo / 2) (half_pos hδlo)).exists
  have hMn := (tendsto_const_div_atTop_nhds_zero_nat ((5 : ℝ) ^ n)).eventually
    (gt_mem_nhds (half_pos hδlo))
  filter_upwards [hev, hMn] with M ⟨hM, hmap, hnear, hmono, hanti, hdisj⟩ hMn
  set S := QE.OpenDyn.snapLogistic r M
  let U : ℕ → Set (Fin (M + 1)) := fun i => latI M (c i) (δ i)
  have hUP : Periodic U P := fun i => by simp only [U, hcP i, hδP i]
  have hsh := snap_shadow hr0 hr4 hM (x₀ := 1 / 2) ⟨by norm_num, by norm_num⟩ n
  have hin : S^[n] (nearest M (1 / 2)) ∈ U (n + j) := by
    show |pos M _ - c (n + j)| ≤ δ (n + j)
    have hn' : |(ell r)^[n] (1 / 2) - c (n + j)| < δlo / 2 := by
      simpa [Real.dist_eq] using hn
    have := abs_sub_le (pos M (S^[n] (nearest M (1 / 2)))) ((ell r)^[n] (1 / 2)) (c (n + j))
    linarith [hlo (n + j)]
  have hV : MapsTo S (⋃ i, U i) (⋃ i, U i) := by
    intro y hy
    obtain ⟨i, hi⟩ := mem_iUnion.1 hy
    exact mem_iUnion.2 ⟨i + 1, hmap i hi⟩
  obtain ⟨m', hm'V, hm'p⟩ := exists_periodic_of_mapsTo S hV (mem_iUnion.2 ⟨_, hin⟩)
  obtain ⟨i₀, hi₀⟩ := mem_iUnion.1 hm'V
  have := period_of_signed_interval_cycle S hP U hUP hdisj hmap _ hdP hd0 hmono hanti hi₀ hm'p
  refine ⟨m' + n, ?_, ?_, ?_⟩ <;> rw [iterate_add_apply]
  · exact hm'p
  · exact this.1
  · exact this.2

/-! ### Transfer to an unlimited lattice (infinitesimal granule) -/

/-- A property holding for all large `M` holds at every unlimited hypernatural
`N = [N n]`, i.e. for `U`-almost all `n`. -/
theorem eventually_hyper_of_atTop {Q : ℕ → Prop} (hQ : ∀ᶠ M in atTop, Q M) {N : ℕ → ℕ}
    (hN : QE.NSA.IsUnlimited (N : QE.NSA.Ult ℕ)) :
    ∀ᶠ n in (hyperfilter ℕ : Filter ℕ), Q (N n) := by
  obtain ⟨M₀, hM₀⟩ := eventually_atTop.1 hQ
  have h : ∀ᶠ n in (hyperfilter ℕ : Filter ℕ), M₀ < N n := Germ.coe_lt.1 (hN M₀)
  exact h.mono fun n hn => hM₀ _ hn.le

/-- **Invariant lattice intervals at an infinitesimal granule.**  With the
hypotheses of `exists_lattice_cycle_intervals`, there are standard radii
`0 < δ_i ≤ η` such that, at every unlimited `N` (granule `1/(2N)` infinitesimal),
the internal snapped logistic map sends `U_i` into `U_{i+1}`, monotonically in the
sense of `ℓ_r'(c_i)`, the `U_i` being nonempty and pairwise disjoint. -/
theorem cycle_intervals_unlimited {r : ℝ} {P : ℕ} {c : ℕ → ℝ}
    (hr0 : 0 ≤ r) (hr4 : r ≤ 4) (hP : 0 < P)
    (hcP : Periodic c P) (hc : ∀ i, ell r (c i) = c (i + 1))
    (hinj : ∀ i < P, ∀ j < P, c i = c j → i = j) (hc01 : ∀ i, c i ∈ Icc (0 : ℝ) 1)
    (hμ0 : multiplier r c P ≠ 0) (hμ1 : |multiplier r c P| < 1) {η : ℝ} (hη : 0 < η) :
    ∃ δ : ℕ → ℝ, Periodic δ P ∧ (∀ i, 0 < δ i ∧ δ i ≤ η) ∧
      ∀ N : ℕ → ℕ, QE.NSA.IsUnlimited (N : QE.NSA.Ult ℕ) →
      ∀ᶠ n in (hyperfilter ℕ : Filter ℕ),
        (∀ i, MapsTo (QE.OpenDyn.snapLogistic r (N n)) (latI (N n) (c i) (δ i))
          (latI (N n) (c (i + 1)) (δ (i + 1)))) ∧
        (∀ i, (latI (N n) (c i) (δ i)).Nonempty) ∧
        (∀ i, 0 < r * (1 - 2 * c i) →
          MonotoneOn (QE.OpenDyn.snapLogistic r (N n)) (latI (N n) (c i) (δ i))) ∧
        (∀ i, r * (1 - 2 * c i) < 0 →
          AntitoneOn (QE.OpenDyn.snapLogistic r (N n)) (latI (N n) (c i) (δ i))) ∧
        (∀ i < P, ∀ j < P, i ≠ j →
          Disjoint (latI (N n) (c i) (δ i)) (latI (N n) (c j) (δ j))) := by
  obtain ⟨δ, hδP, hδ, -, hev⟩ :=
    exists_lattice_cycle_intervals hr0 hr4 hP hcP hc hinj hc01 hμ0 hμ1 hη
  refine ⟨δ, hδP, hδ, fun N hN => (eventually_hyper_of_atTop hev hN).mono ?_⟩
  rintro n ⟨-, h1, h2, h3, h4, h5⟩
  exact ⟨h1, fun i => ⟨_, h2 i⟩, h3, h4, h5⟩

/-- **Every standard level of the cascade survives** (infinitesimal granule): at
every unlimited `N`, the internal snapped logistic map has a periodic point
within any standard `η` of `c_0` (hence infinitely close to it), of minimal
period `P` if `μ > 0` and `P` or `2P` if `μ < 0`. -/
theorem cycle_period_unlimited {r : ℝ} {P : ℕ} {c : ℕ → ℝ}
    (hr0 : 0 ≤ r) (hr4 : r ≤ 4) (hP : 0 < P)
    (hcP : Periodic c P) (hc : ∀ i, ell r (c i) = c (i + 1))
    (hinj : ∀ i < P, ∀ j < P, c i = c j → i = j) (hc01 : ∀ i, c i ∈ Icc (0 : ℝ) 1)
    (hμ0 : multiplier r c P ≠ 0) (hμ1 : |multiplier r c P| < 1) {η : ℝ} (hη : 0 < η)
    {N : ℕ → ℕ} (hN : QE.NSA.IsUnlimited (N : QE.NSA.Ult ℕ)) :
    ∀ᶠ n in (hyperfilter ℕ : Filter ℕ), ∃ k : Fin (N n + 1), |pos (N n) k - c 0| ≤ η ∧
      k ∈ periodicPts (QE.OpenDyn.snapLogistic r (N n)) ∧
      (0 < multiplier r c P → minimalPeriod (QE.OpenDyn.snapLogistic r (N n)) k = P) ∧
      (multiplier r c P < 0 → minimalPeriod (QE.OpenDyn.snapLogistic r (N n)) k = P ∨
        minimalPeriod (QE.OpenDyn.snapLogistic r (N n)) k = 2 * P) :=
  eventually_hyper_of_atTop
    (lattice_cycle_period hr0 hr4 hP hcP hc hinj hc01 hμ0 hμ1 hη) hN

/-- **The snapped orbit of `1/2` at an infinitesimal granule** is eventually
periodic with period `P` (`μ > 0`), or `P` or `2P` (`μ < 0`). -/
theorem half_orbit_period_unlimited {r : ℝ} {P : ℕ} {c : ℕ → ℝ}
    (hr0 : 0 ≤ r) (hr4 : r ≤ 4) (hP : 0 < P)
    (hcP : Periodic c P) (hc : ∀ i, ell r (c i) = c (i + 1))
    (hinj : ∀ i < P, ∀ j < P, c i = c j → i = j) (hc01 : ∀ i, c i ∈ Icc (0 : ℝ) 1)
    (hμ0 : multiplier r c P ≠ 0) (hμ1 : |multiplier r c P| < 1)
    (hatt : ∃ j, Tendsto (fun n => (ell r)^[n] (1 / 2) - c (n + j)) atTop (𝓝 0))
    {N : ℕ → ℕ} (hN : QE.NSA.IsUnlimited (N : QE.NSA.Ult ℕ)) :
    ∀ᶠ n in (hyperfilter ℕ : Filter ℕ), ∃ m : ℕ,
      (QE.OpenDyn.snapLogistic r (N n))^[m] (nearest (N n) (1 / 2)) ∈
        periodicPts (QE.OpenDyn.snapLogistic r (N n)) ∧
      (0 < multiplier r c P → minimalPeriod (QE.OpenDyn.snapLogistic r (N n))
        ((QE.OpenDyn.snapLogistic r (N n))^[m] (nearest (N n) (1 / 2))) = P) ∧
      (multiplier r c P < 0 →
        minimalPeriod (QE.OpenDyn.snapLogistic r (N n))
          ((QE.OpenDyn.snapLogistic r (N n))^[m] (nearest (N n) (1 / 2))) = P ∨
        minimalPeriod (QE.OpenDyn.snapLogistic r (N n))
          ((QE.OpenDyn.snapLogistic r (N n))^[m] (nearest (N n) (1 / 2))) = 2 * P) :=
  eventually_hyper_of_atTop
    (half_orbit_period hr0 hr4 hP hcP hc hinj hc01 hμ0 hμ1 hatt) hN

end QE.CascadeInfra
