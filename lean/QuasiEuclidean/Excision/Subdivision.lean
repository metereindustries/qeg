-- SPDX-License-Identifier: MIT
-- Copyright 2026 Metere Industries, Inc. Author: Alfredo Metere.
-- Quasi-Euclidean Granular Geometry. Any derivative work must carry this notice:
--   This work is derivative of the Quasi-Euclidean Granular Geometry book
--   authored by Alfredo Metere. Copyright 2026 Metere Industries, Inc.
--   All rights reserved
-- See LICENSE.md and NOTICE.

import QuasiEuclidean.Excision.Simplex

/-!
# Barycentric subdivision of singular chains and the small-simplices theorem

Book: Proposition `prop:topology-homology-singular` (Chapter 10), infrastructure.

Following Hatcher (§2.1, Prop. 2.21):

* `sSd σ = σ_♯ Sd(ι_k)` and `sT σ = σ_♯ T(ι_k)`, where `ι_k` is the identity simplex of
  `Δ k` viewed as a linear simplex.  `sSd` is a chain map (`sd_sSd`), `sT` is a chain
  homotopy `∂ sT + sT ∂ = id - sSd` (`sd_sT`), and both send a simplex to chains of simplices
  with image inside the image of the simplex.
* The simplices of `Sd^q(ι_k)` have diameter at most `(k/(k+1))^q` (`Sd_pow_fine`), so by
  the Lebesgue number lemma `sSd^q σ` is `𝒰`-small for large `q`, for any open cover `𝒰` of
  the image of `σ` (`exists_small`).
* **The small-simplices theorem** (`small_surj`, `small_inj`): for `A ⊆ ⋃ 𝒰` with `𝒰` open,
  every singular cycle of `A` is homologous in `A` to a `𝒰`-small cycle, and a small cycle
  that bounds in `A` bounds a small chain.  Hence the inclusion of small chains induces an
  isomorphism on homology in every degree (`smallEquiv`).

No measure theory is used.
-/

namespace QE.Excision

open Finsupp

noncomputable section

/-! ## Convex hulls and diameters of subdivided linear simplices -/

section Hull

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- Linear simplices with all vertices in `K`. -/
def Hull (K : Set V) : Set (LG V).β := {s | ∀ j, s.2 j ∈ K}

theorem bary_mem_convexHull {m : ℕ} (w : Fin (m + 1) → V) :
    bary w ∈ convexHull ℝ (Set.range w) := by
  unfold bary
  rw [Finset.smul_sum]
  refine (convex_convexHull ℝ _).sum_mem (fun _ _ => by positivity) ?_
    (fun j _ => subset_convexHull ℝ _ ⟨j, rfl⟩)
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  push_cast
  field_simp

theorem cone_mem_supported {b : V} {P Q : Set (LG V).β}
    (h : ∀ s ∈ P, (⟨s.1 + 1, Fin.cons b s.2⟩ : (LG V).β) ∈ Q) {x : LC V}
    (hx : x ∈ supported ℤ ℤ P) : cone b x ∈ supported ℤ ℤ Q := by
  unfold cone
  exact lc_mem fun s hs => single_mem_supported ℤ _ (h s ((mem_supported ℤ _).mp hx hs))

theorem cone_mem_Hull {K : Set V} {b : V} (hb : b ∈ K) {x : LC V}
    (hx : x ∈ supported ℤ ℤ (Hull K)) : cone b x ∈ supported ℤ ℤ (Hull K) :=
  cone_mem_supported (fun s hs => by
    show ∀ j, (Fin.cons b s.2 : Fin (s.1 + 2) → V) j ∈ K
    intro j
    refine Fin.cases ?_ (fun j => ?_) j
    · simpa using hb
    · simpa using hs j) hx

theorem Hull_mono {K K' : Set V} (h : K ⊆ K') : Hull K ⊆ Hull K' := fun _ hs j => h (hs j)

theorem lsim_mem_Hull {m : ℕ} (w : Fin (m + 1) → V) :
    lsim w ∈ supported ℤ ℤ (Hull (convexHull ℝ (Set.range w))) :=
  single_mem_supported ℤ _ fun j => subset_convexHull ℝ _ ⟨j, rfl⟩

theorem convexHull_face {m k : ℕ} (w : Fin (m + 1) → V) (f : Fin (k + 1) → Fin (m + 1)) :
    convexHull ℝ (Set.range (w ∘ f)) ⊆ convexHull ℝ (Set.range w) :=
  convexHull_mono (Set.range_comp_subset_range _ _)

theorem sdS_mem_Hull : ∀ (m : ℕ) (w : Fin (m + 1) → V),
    sdS m w ∈ supported ℤ ℤ (Hull (convexHull ℝ (Set.range w)))
  | 0, w => lsim_mem_Hull w
  | m + 1, w => by
    show cone _ _ ∈ _
    refine cone_mem_Hull (bary_mem_convexHull w) (Submodule.sum_mem _ fun i _ =>
      Submodule.smul_mem _ _ (supported_mono (Hull_mono (convexHull_face w _))
        (sdS_mem_Hull m _)))

theorem tS_mem_Hull : ∀ (m : ℕ) (w : Fin (m + 1) → V),
    tS m w ∈ supported ℤ ℤ (Hull (convexHull ℝ (Set.range w)))
  | 0, _ => Submodule.zero_mem _
  | m + 1, w => by
    show cone _ _ ∈ _
    refine cone_mem_Hull (bary_mem_convexHull w) (Submodule.sub_mem _ (lsim_mem_Hull w)
      (Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _
        (supported_mono (Hull_mono (convexHull_face w _)) (tS_mem_Hull m _))))

theorem Sd_mem_Hull {K : Set V} (hK : Convex ℝ K) {x : LC V} (hx : x ∈ supported ℤ ℤ (Hull K)) :
    Sd x ∈ supported ℤ ℤ (Hull K) := by
  unfold Sd
  refine lc_mem fun s hs => ?_
  have h := (mem_supported ℤ _).mp hx hs
  exact supported_mono (Hull_mono (convexHull_min (by rintro _ ⟨j, rfl⟩; exact h j) hK))
    (sdS_mem_Hull s.1 s.2)

theorem Tl_mem_Hull {K : Set V} (hK : Convex ℝ K) {x : LC V} (hx : x ∈ supported ℤ ℤ (Hull K)) :
    Tl x ∈ supported ℤ ℤ (Hull K) := by
  unfold Tl
  refine lc_mem fun s hs => ?_
  have h := (mem_supported ℤ _).mp hx hs
  exact supported_mono (Hull_mono (convexHull_min (by rintro _ ⟨j, rfl⟩; exact h j) hK))
    (tS_mem_Hull s.1 s.2)

theorem ld_mem_Hull {K : Set V} {x : LC V} (hx : x ∈ supported ℤ ℤ (Hull K)) :
    (LG V).d x ∈ supported ℤ ℤ (Hull K) := by
  refine GC.d_mem_supported (fun s hs => ?_) hx
  obtain ⟨m, w⟩ := s
  rcases m with _ | m
  · rw [show (single ⟨0, w⟩ 1 : LC V) = lsim w from rfl, ld_lsim_zero]
    exact Submodule.zero_mem _
  · rw [show (single ⟨m + 1, w⟩ 1 : LC V) = lsim w from rfl, ld_lsim_succ]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _
      (single_mem_supported ℤ _ fun j => hs _)

/-- The distance from the barycentre to a vertex. -/
theorem norm_bary_sub_le {m : ℕ} (w : Fin (m + 1) → V) {r : ℝ} (h : ∀ i j, ‖w i - w j‖ ≤ r)
    (i : Fin (m + 1)) : ‖bary w - w i‖ ≤ (m : ℝ) / (m + 1) * r := by
  have hm : (0 : ℝ) < m + 1 := by positivity
  have e : bary w - w i = ((m : ℝ) + 1)⁻¹ • ∑ j, (w j - w i) := by
    unfold bary
    rw [Finset.sum_sub_distrib, smul_sub, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      ← Nat.cast_smul_eq_nsmul ℝ, smul_smul]
    push_cast
    rw [inv_mul_cancel₀ hm.ne', one_smul]
  rw [e, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hm)]
  have hs : ‖∑ j, (w j - w i)‖ ≤ m * r := by
    refine (norm_sum_le _ _).trans ?_
    rw [← Finset.sum_erase_add _ _ (Finset.mem_univ i), sub_self, norm_zero, add_zero]
    have := Finset.sum_le_card_nsmul (Finset.univ.erase i) (fun j => ‖w j - w i‖) r
      (fun j _ => h j i)
    rw [Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul] at this
    simpa using this
  calc ((m : ℝ) + 1)⁻¹ * ‖∑ j, (w j - w i)‖ ≤ ((m : ℝ) + 1)⁻¹ * (m * r) :=
        mul_le_mul_of_nonneg_left hs (inv_pos.mpr hm).le
    _ = (m : ℝ) / (m + 1) * r := by field_simp

theorem norm_bary_sub_le_of_mem {m : ℕ} (w : Fin (m + 1) → V) {r : ℝ}
    (h : ∀ i j, ‖w i - w j‖ ≤ r) {u : V} (hu : u ∈ convexHull ℝ (Set.range w)) :
    ‖bary w - u‖ ≤ (m : ℝ) / (m + 1) * r := by
  have hsub : Set.range w ⊆ Metric.closedBall (bary w) ((m : ℝ) / (m + 1) * r) := by
    rintro _ ⟨i, rfl⟩
    rw [Metric.mem_closedBall, dist_eq_norm, norm_sub_rev]
    exact norm_bary_sub_le w h i
  have := convexHull_min hsub (convex_closedBall _ _) hu
  rw [Metric.mem_closedBall, dist_eq_norm, norm_sub_rev] at this
  exact this

/-- **Diameter estimate**: the simplices of `Sd [w]` lie in the convex hull of `w` and have
diameter at most `m/(m+1)` times that of `w`. -/
theorem sdS_fine : ∀ (m : ℕ) (w : Fin (m + 1) → V) (r : ℝ), (∀ i j, ‖w i - w j‖ ≤ r) →
    sdS m w ∈ supported ℤ ℤ {s : (LG V).β | (∀ j, s.2 j ∈ convexHull ℝ (Set.range w)) ∧
      ∀ i j, ‖s.2 i - s.2 j‖ ≤ (m : ℝ) / (m + 1) * r}
  | 0, w, r, _ => single_mem_supported ℤ _
      ⟨fun j => subset_convexHull ℝ _ ⟨j, rfl⟩, fun i j => by
        have hij : i = j := Fin.ext (by have := i.2; have := j.2; simp only at *; omega)
        rw [hij, sub_self, norm_zero]; simp⟩
  | m + 1, w, r, h => by
    have hr : 0 ≤ r := (norm_nonneg _).trans (h 0 0)
    show cone _ _ ∈ _
    have hle : (m : ℝ) / (m + 1) * r ≤ ((m + 1 : ℕ) : ℝ) / ((m + 1 : ℕ) + 1) * r := by
      apply mul_le_mul_of_nonneg_right _ hr
      push_cast
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith
    refine cone_mem_supported (P := {s : (LG V).β | (∀ j, s.2 j ∈ convexHull ℝ (Set.range w)) ∧
      ∀ i j, ‖s.2 i - s.2 j‖ ≤ (m : ℝ) / (m + 1) * r}) ?_ ?_
    · rintro s ⟨hs1, hs2⟩
      have hb := bary_mem_convexHull w
      have hbd := fun u hu => norm_bary_sub_le_of_mem w h (u := u) hu
      refine ⟨fun j => ?_, fun i j => ?_⟩
      · refine Fin.cases ?_ (fun j => ?_) j
        · simpa using hb
        · simpa using hs1 j
      · refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j
        · simp only [Fin.cons_zero, sub_self, norm_zero]; positivity
        · simpa using hbd _ (hs1 j)
        · simpa [norm_sub_rev] using hbd _ (hs1 i)
        · simpa using (hs2 i j).trans hle
    · refine Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ ?_
      refine supported_mono ?_ (sdS_fine m (w ∘ Fin.succAbove i) r (fun a c => h _ _))
      rintro s ⟨hs1, hs2⟩
      exact ⟨fun j => convexHull_face w _ (hs1 j), hs2⟩

/-- Linear simplices of dimension `m` with vertices in `K` and diameter at most `ρ`. -/
def FineSet (K : Set V) (m : ℕ) (ρ : ℝ) : Set (LG V).β :=
  {s | s.1 = m ∧ (∀ j, s.2 j ∈ K) ∧ ∀ i j, ‖s.2 i - s.2 j‖ ≤ ρ}

theorem Sd_fine {K : Set V} (hK : Convex ℝ K) {m : ℕ} {ρ : ℝ} {x : LC V}
    (hx : x ∈ supported ℤ ℤ (FineSet K m ρ)) :
    Sd x ∈ supported ℤ ℤ (FineSet K m ((m : ℝ) / (m + 1) * ρ)) := by
  unfold Sd
  refine lc_mem fun s hs => ?_
  obtain ⟨hs1, hs2, hs3⟩ := (mem_supported ℤ _).mp hx hs
  obtain ⟨k, w⟩ := s
  simp only at hs1 hs2 hs3
  subst hs1
  have h1 := (mem_supported ℤ _).mp (sdS_mem_homog k w)
  have h2 := (mem_supported ℤ _).mp (sdS_fine k w ρ hs3)
  refine (mem_supported ℤ _).mpr fun t ht => ?_
  obtain ⟨h21, h22⟩ := h2 ht
  exact ⟨h1 ht, fun j => convexHull_min (by rintro _ ⟨j, rfl⟩; exact hs2 j) hK (h21 j), h22⟩

end Hull

/-! ## Subdivision of singular chains -/

section SingularSd

variable {E : Type} [TopologicalSpace E]

/-- The identity simplex of `Δ k`, as a linear simplex. -/
abbrev idS (k : ℕ) : LC (Vk k) := lsim (vert : Fin (k + 1) → Vk k)

theorem InΔ_eq (k : ℕ) : InΔ k = Hull (Δset k) := rfl

theorem idS_mem (k : ℕ) : idS k ∈ supported ℤ ℤ (InΔ k) := single_mem_supported ℤ _ vert_mem

theorem Sd_InΔ {k : ℕ} {x : LC (Vk k)} (hx : x ∈ supported ℤ ℤ (InΔ k)) :
    Sd x ∈ supported ℤ ℤ (InΔ k) := Sd_mem_Hull (convex_Δset k) hx

theorem Tl_InΔ {k : ℕ} {x : LC (Vk k)} (hx : x ∈ supported ℤ ℤ (InΔ k)) :
    Tl x ∈ supported ℤ ℤ (InΔ k) := Tl_mem_Hull (convex_Δset k) hx

theorem ld_InΔ {k : ℕ} {x : LC (Vk k)} (hx : x ∈ supported ℤ ℤ (InΔ k)) :
    (LG (Vk k)).d x ∈ supported ℤ ℤ (InΔ k) := ld_mem_Hull hx

theorem lmap_InΔ {m k : ℕ} {u : Fin (m + 1) → Vk k} (hu : ∀ j, u j ∈ Δset k) {x : LC (Vk m)}
    (hx : x ∈ supported ℤ ℤ (InΔ m)) : lmap (affL u) x ∈ supported ℤ ℤ (InΔ k) := by
  have h := Finsupp.lmapDomain_supported (M := ℤ) (R := ℤ)
    (fun s : (LG (Vk m)).β => (⟨s.1, affL u ∘ s.2⟩ : (LG (Vk k)).β)) (InΔ m)
  have hx' : lmap (affL u) x ∈ supported ℤ ℤ
      ((fun s : (LG (Vk m)).β => (⟨s.1, affL u ∘ s.2⟩ : (LG (Vk k)).β)) '' InΔ m) := by
    rw [← h]; exact Submodule.mem_map_of_mem hx
  refine supported_mono ?_ hx'
  rintro _ ⟨s, hs, rfl⟩ j
  exact affL_mem hu (hs j)

theorem Sd_pow_InΔ {k : ℕ} (q : ℕ) : (Sd ^ q) (idS k) ∈ supported ℤ ℤ (InΔ k) := by
  induction q with
  | zero => exact idS_mem k
  | succ q ih => rw [pow_succ', Module.End.mul_apply]; exact Sd_InΔ ih

theorem ld_idS_succ (k : ℕ) : (LG (Vk (k + 1))).d (idS (k + 1)) =
    ∑ i : Fin (k + 2), ((-1 : ℤ) ^ (i : ℕ)) • lmap (affL (vert ∘ Fin.succAbove i)) (idS k) := by
  rw [ld_lsim_succ]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [lmap_lsim, affL_comp_vert]

theorem push_face {k : ℕ} (σ : C(Δ (k + 1), E)) (i : Fin (k + 2)) {y : LC (Vk k)}
    (hy : y ∈ supported ℤ ℤ (InΔ k)) :
    push σ (lmap (affL (vert ∘ Fin.succAbove i)) y) = push (σ.comp (smap (Fin.succAbove i))) y := by
  rw [smap_eq, push_comp σ _ _ hy]

/-- **Barycentric subdivision of singular chains**: `sSd σ = σ_♯ Sd(ι_k)`. -/
def sSd : SC E →ₗ[ℤ] SC E :=
  linearCombination ℤ (fun s : (SG E).β => push s.2 (Sd (idS s.1)))

/-- **The subdivision homotopy** `sT σ = σ_♯ T(ι_k)`. -/
def sT : SC E →ₗ[ℤ] SC E :=
  linearCombination ℤ (fun s : (SG E).β => push s.2 (Tl (idS s.1)))

theorem sSd_ssim {k : ℕ} (σ : C(Δ k, E)) : sSd (ssim σ) = push σ (Sd (idS k)) := by
  unfold sSd ssim; rw [linearCombination_single, one_smul]

theorem sT_ssim {k : ℕ} (σ : C(Δ k, E)) : sT (ssim σ) = push σ (Tl (idS k)) := by
  unfold sT ssim; rw [linearCombination_single, one_smul]

theorem sSd_sd_ssim {k : ℕ} (σ : C(Δ k, E)) :
    sSd ((SG E).d (ssim σ)) = push σ (Sd ((LG (Vk k)).d (idS k))) := by
  rcases k with _ | k
  · rw [sd_ssim_zero, ld_lsim_zero, map_zero, map_zero, map_zero]
  · rw [sd_ssim_succ, ld_idS_succ, map_sum, map_sum, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_zsmul, map_zsmul, map_zsmul, sSd_ssim, ← lmap_Sd, push_face σ i (Sd_InΔ (idS_mem k))]

theorem sT_sd_ssim {k : ℕ} (σ : C(Δ k, E)) :
    sT ((SG E).d (ssim σ)) = push σ (Tl ((LG (Vk k)).d (idS k))) := by
  rcases k with _ | k
  · rw [sd_ssim_zero, ld_lsim_zero, map_zero, map_zero, map_zero]
  · rw [sd_ssim_succ, ld_idS_succ, map_sum, map_sum, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_zsmul, map_zsmul, map_zsmul, sT_ssim, ← lmap_Tl, push_face σ i (Tl_InΔ (idS_mem k))]

/-- **`sSd` is a chain map.** -/
theorem sd_sSd (x : SC E) : (SG E).d (sSd x) = sSd ((SG E).d x) := by
  refine linearMap_congr_support ((SG E).d ∘ₗ sSd) (sSd ∘ₗ (SG E).d) (fun s _ => ?_)
  obtain ⟨k, σ⟩ := s
  simp only [LinearMap.coe_comp, Function.comp_apply]
  rw [show (single ⟨k, σ⟩ 1 : SC E) = ssim σ from rfl, sSd_sd_ssim, sSd_ssim,
    ← push_ld σ (Sd_InΔ (idS_mem k)), ld_Sd]

/-- **The subdivision homotopy formula** `∂ sT + sT ∂ = id - sSd`. -/
theorem sd_sT (x : SC E) : (SG E).d (sT x) + sT ((SG E).d x) = x - sSd x := by
  refine linearMap_congr_support ((SG E).d ∘ₗ sT + sT ∘ₗ (SG E).d) (LinearMap.id - sSd)
    (fun s _ => ?_)
  obtain ⟨k, σ⟩ := s
  simp only [LinearMap.add_apply, LinearMap.coe_comp, Function.comp_apply, LinearMap.sub_apply,
    LinearMap.id_coe, id_eq]
  rw [show (single ⟨k, σ⟩ 1 : SC E) = ssim σ from rfl, sT_sd_ssim, sT_ssim, sSd_ssim,
    ← push_ld σ (Tl_InΔ (idS_mem k)), ← map_add, ld_Tl, map_sub, push_vert]

/-- Subdividing a pushed chain is pushing the subdivided chain. -/
theorem sSd_push {k : ℕ} (σ : C(Δ k, E)) {y : LC (Vk k)} (hy : y ∈ supported ℤ ℤ (InΔ k)) :
    sSd (push σ y) = push σ (Sd y) := by
  refine linearMap_congr_support (sSd ∘ₗ push σ) (push σ ∘ₗ Sd) (fun s hs => ?_)
  obtain ⟨m, w⟩ := s
  have hw : ∀ j, w j ∈ Δset k := (mem_supported ℤ _).mp hy hs
  simp only [LinearMap.coe_comp, Function.comp_apply]
  rw [show (single ⟨m, w⟩ 1 : LC (Vk k)) = lsim w from rfl, push_lsim σ w hw, sSd_ssim,
    push_comp σ w hw (Sd_InΔ (idS_mem m)), lmap_Sd, lmap_lsim, affL_comp_vert]

theorem sSd_pow_ssim {k : ℕ} (σ : C(Δ k, E)) (q : ℕ) :
    (sSd ^ q) (ssim σ) = push σ ((Sd ^ q) (idS k)) := by
  induction q with
  | zero => rw [pow_zero, pow_zero, Module.End.one_apply, Module.End.one_apply, push_vert]
  | succ q ih =>
    rw [pow_succ', Module.End.mul_apply, ih, sSd_push σ (Sd_pow_InΔ q), pow_succ',
      Module.End.mul_apply]

/-- A set of singular simplices closed under passing to simplices with smaller image. -/
def Hered (P : Set (SG E).β) : Prop :=
  ∀ s ∈ P, ∀ t : (SG E).β, Set.range t.2 ⊆ Set.range s.2 → t ∈ P

theorem push_mem_hered {P : Set (SG E).β} (hP : Hered P) {k : ℕ} {σ : C(Δ k, E)}
    (hσ : (⟨k, σ⟩ : (SG E).β) ∈ P) (y : LC (Vk k)) : push σ y ∈ supported ℤ ℤ P :=
  supported_mono (fun t ht => hP _ hσ t ht) (push_mem_supported σ y)

theorem sSd_mem_hered {P : Set (SG E).β} (hP : Hered P) {x : SC E}
    (hx : x ∈ supported ℤ ℤ P) : sSd x ∈ supported ℤ ℤ P := by
  unfold sSd
  exact lc_mem fun s hs => push_mem_hered hP ((mem_supported ℤ _).mp hx hs) _

theorem sT_mem_hered {P : Set (SG E).β} (hP : Hered P) {x : SC E}
    (hx : x ∈ supported ℤ ℤ P) : sT x ∈ supported ℤ ℤ P := by
  unfold sT
  exact lc_mem fun s hs => push_mem_hered hP ((mem_supported ℤ _).mp hx hs) _

theorem sSd_pow_mem_hered {P : Set (SG E).β} (hP : Hered P) {x : SC E}
    (hx : x ∈ supported ℤ ℤ P) (q : ℕ) : (sSd ^ q) x ∈ supported ℤ ℤ P := by
  induction q with
  | zero => simpa using hx
  | succ q ih => rw [pow_succ', Module.End.mul_apply]; exact sSd_mem_hered hP ih

theorem sSd_mem_homog {k : ℕ} {x : SC E} (hx : x ∈ (SG E).homog k) : sSd x ∈ (SG E).homog k := by
  unfold sSd
  refine lc_mem fun s hs => ?_
  have : s.1 = k := (mem_supported ℤ _).mp hx hs
  rw [← this]
  exact push_mem_homog _ (Sd_mem_homog (lsim_mem_homog _))

theorem sT_mem_homog {k : ℕ} {x : SC E} (hx : x ∈ (SG E).homog k) :
    sT x ∈ (SG E).homog (k + 1) := by
  unfold sT
  refine lc_mem fun s hs => ?_
  have : s.1 = k := (mem_supported ℤ _).mp hx hs
  rw [← this]
  exact push_mem_homog _ (Tl_mem_homog (lsim_mem_homog _))

theorem sSd_pow_mem_homog {k : ℕ} {x : SC E} (hx : x ∈ (SG E).homog k) (q : ℕ) :
    (sSd ^ q) x ∈ (SG E).homog k := by
  induction q with
  | zero => simpa using hx
  | succ q ih => rw [pow_succ', Module.End.mul_apply]; exact sSd_mem_homog ih

theorem sd_sSd_pow (q : ℕ) (x : SC E) : (SG E).d ((sSd ^ q) x) = (sSd ^ q) ((SG E).d x) := by
  induction q generalizing x with
  | zero => simp
  | succ q ih => rw [pow_succ', Module.End.mul_apply, Module.End.mul_apply, sd_sSd, ih]

/-- The iterated homotopy `D_q = Σ_{i<q} sT ∘ sSd^i`. -/
def sD (q : ℕ) : SC E →ₗ[ℤ] SC E := ∑ i ∈ Finset.range q, sT ∘ₗ (sSd ^ i)

/-- `∂ D_q + D_q ∂ = id - sSd^q`. -/
theorem sd_sD (q : ℕ) (x : SC E) :
    (SG E).d (sD q x) + sD q ((SG E).d x) = x - (sSd ^ q) x := by
  induction q with
  | zero => simp [sD]
  | succ q ih =>
    have hD : (sD (q + 1) : SC E →ₗ[ℤ] SC E) = sD q + sT ∘ₗ (sSd ^ q) := by
      simp only [sD, Finset.sum_range_succ]
    have h2 := sd_sT ((sSd ^ q) x)
    rw [sd_sSd_pow] at h2
    rw [hD, LinearMap.add_apply, LinearMap.add_apply, map_add, LinearMap.comp_apply,
      LinearMap.comp_apply, pow_succ', Module.End.mul_apply]
    calc (SG E).d (sD q x) + (SG E).d (sT ((sSd ^ q) x)) +
          (sD q ((SG E).d x) + sT ((sSd ^ q) ((SG E).d x)))
        = ((SG E).d (sD q x) + sD q ((SG E).d x)) +
          ((SG E).d (sT ((sSd ^ q) x)) + sT ((sSd ^ q) ((SG E).d x))) := by abel
      _ = x - sSd ((sSd ^ q) x) := by rw [ih, h2]; abel

theorem sD_mem_hered {P : Set (SG E).β} (hP : Hered P) {x : SC E}
    (hx : x ∈ supported ℤ ℤ P) (q : ℕ) : sD q x ∈ supported ℤ ℤ P := by
  unfold sD
  rw [LinearMap.sum_apply]
  exact Submodule.sum_mem _ fun i _ => sT_mem_hered hP (sSd_pow_mem_hered hP hx i)

theorem sD_mem_homog {k : ℕ} {x : SC E} (hx : x ∈ (SG E).homog k) (q : ℕ) :
    sD q x ∈ (SG E).homog (k + 1) := by
  unfold sD
  rw [LinearMap.sum_apply]
  exact Submodule.sum_mem _ fun i _ => sT_mem_homog (sSd_pow_mem_homog hx i)

end SingularSd

/-! ## Small simplices -/

section Small

variable {E : Type} [TopologicalSpace E]

/-- `𝒰`-small singular simplices: image inside one member of `𝒰`. -/
def Small (𝒰 : Set (Set E)) : Set (SG E).β := {s | ∃ U ∈ 𝒰, Set.range s.2 ⊆ U}

theorem hered_SA (A : Set E) : Hered (SA A) := fun _ hs _ ht => ht.trans hs

theorem hered_Small (𝒰 : Set (Set E)) : Hered (Small 𝒰) := fun _ ⟨U, hU, hs⟩ _ ht =>
  ⟨U, hU, ht.trans hs⟩

theorem hered_inter {P Q : Set (SG E).β} (hP : Hered P) (hQ : Hered Q) : Hered (P ∩ Q) :=
  fun s hs t ht => ⟨hP s hs.1 t ht, hQ s hs.2 t ht⟩

theorem Sd_pow_fine (k q : ℕ) :
    (Sd ^ q) (idS k) ∈ supported ℤ ℤ (FineSet (Δset k) k (((k : ℝ) / (k + 1)) ^ q)) := by
  induction q with
  | zero =>
    rw [pow_zero (Sd : Module.End ℤ (LC (Vk k))), Module.End.one_apply, pow_zero]
    exact single_mem_supported ℤ _ ⟨rfl, vert_mem, norm_vert_sub_le⟩
  | succ q ih =>
    rw [pow_succ' (Sd : Module.End ℤ (LC (Vk k))), Module.End.mul_apply,
      pow_succ' ((k : ℝ) / (k + 1))]
    exact Sd_fine (convex_Δset k) ih

theorem norm_affL_sub_le {m k : ℕ} (w : Fin (m + 1) → Vk k) {ρ : ℝ}
    (h : ∀ i j, ‖w i - w j‖ ≤ ρ) {x : Vk m} (hx : x ∈ Δset m) : ‖affL w x - w 0‖ ≤ ρ := by
  have e : affL w x - w 0 = ∑ j, x j • (w j - w 0) := by
    rw [affL_apply]
    simp only [smul_sub, Finset.sum_sub_distrib, ← Finset.sum_smul, hx.2, one_smul]
  rw [e]
  refine (norm_sum_le _ _).trans ?_
  calc ∑ j, ‖x j • (w j - w 0)‖ ≤ ∑ j, x j * ρ := Finset.sum_le_sum fun j _ => by
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (hx.1 j)]
        exact mul_le_mul_of_nonneg_left (h j 0) (hx.1 j)
    _ = ρ := by rw [← Finset.sum_mul, hx.2, one_mul]

/-- **Fine subdivisions are small**: for an open cover `𝒰` of the image of `σ`, the iterated
subdivision `sSd^q σ` is `𝒰`-small for all large `q` (Lebesgue number lemma). -/
theorem exists_small {k : ℕ} (σ : C(Δ k, E)) {𝒰 : Set (Set E)} (hU : ∀ U ∈ 𝒰, IsOpen U)
    (hcov : Set.range σ ⊆ ⋃₀ 𝒰) :
    ∃ q, ∀ q' ≥ q, (sSd ^ q') (ssim σ) ∈ supported ℤ ℤ (Small 𝒰) := by
  have : CompactSpace (Δset k) := isCompact_iff_compactSpace.mp (isCompact_Δset k)
  let g : Δset k → E := fun x => σ (mkS x.1 x.2)
  have hmk : Continuous fun x : Δset k => mkS x.1 x.2 := by
    rw [(isEmbedding_wt k).continuous_iff]
    exact continuous_subtype_val.congr fun x => (wt_mkS x.1 x.2).symm
  have hg : Continuous g := σ.continuous.comp hmk
  let c : 𝒰 → Set (Δset k) := fun U => g ⁻¹' U.1
  have hc : ∀ U, IsOpen (c U) := fun U => (hU U.1 U.2).preimage hg
  have hcov' : (Set.univ : Set (Δset k)) ⊆ ⋃ U, c U := by
    intro x _
    obtain ⟨U, hU, hxU⟩ := hcov ⟨mkS x.1 x.2, rfl⟩
    exact Set.mem_iUnion.mpr ⟨⟨U, hU⟩, hxU⟩
  obtain ⟨δ, hδ, hleb⟩ := lebesgue_number_lemma_of_metric isCompact_univ hc hcov'
  have hr : (k : ℝ) / (k + 1) < 1 := by
    rw [div_lt_one (by positivity)]; linarith
  have hr0 : 0 ≤ (k : ℝ) / (k + 1) := by positivity
  obtain ⟨q, hq⟩ := exists_pow_lt_of_lt_one hδ hr
  refine ⟨q, fun q' hq' => ?_⟩
  have hρ : ((k : ℝ) / (k + 1)) ^ q' < δ :=
    lt_of_le_of_lt (pow_le_pow_of_le_one hr0 hr.le hq') hq
  rw [sSd_pow_ssim]
  have hfine := Sd_pow_fine k q'
  unfold push
  refine lc_mem fun s hs => ?_
  obtain ⟨-, hs2, hs3⟩ := (mem_supported ℤ _).mp hfine hs
  simp only [hs2, implies_true, ↓reduceDIte]
  refine single_mem_supported ℤ _ ?_
  obtain ⟨⟨U, hUmem⟩, hball⟩ := hleb ⟨s.2 0, hs2 0⟩ (Set.mem_univ _)
  refine ⟨U, hUmem, ?_⟩
  rintro _ ⟨t, rfl⟩
  have hin : (⟨affL s.2 (wt t), affL_mem hs2 (wt_mem t)⟩ : Δset k) ∈
      Metric.ball (⟨s.2 0, hs2 0⟩ : Δset k) δ := by
    rw [Metric.mem_ball, Subtype.dist_eq, dist_eq_norm]
    exact lt_of_le_of_lt (norm_affL_sub_le s.2 hs3 (wt_mem t)) hρ
  exact hball hin

theorem exists_small_chain {A : Set E} {𝒰 : Set (Set E)} (hU : ∀ U ∈ 𝒰, IsOpen U)
    (hcov : A ⊆ ⋃₀ 𝒰) {x : SC E} (hx : x ∈ supported ℤ ℤ (SA A)) :
    ∃ q, (sSd ^ q) x ∈ supported ℤ ℤ (Small 𝒰) := by
  classical
  have hex : ∀ s : (SG E).β, s ∈ SA A →
      ∃ q, ∀ q' ≥ q, (sSd ^ q') (single s 1) ∈ supported ℤ ℤ (Small 𝒰) := fun s hs =>
    exists_small s.2 hU (hs.trans hcov)
  let qf : (SG E).β → ℕ := fun s => if h : s ∈ SA A then (hex s h).choose else 0
  refine ⟨x.support.sup qf, ?_⟩
  rw [← lc_comp_single (A := SG E) (sSd ^ x.support.sup qf) x]
  refine lc_mem fun s hs => ?_
  have hsA : s ∈ SA A := (mem_supported ℤ _).mp hx hs
  refine (hex s hsA).choose_spec _ ?_
  have : qf s = (hex s hsA).choose := by simp only [qf, hsA, ↓reduceDIte]
  rw [← this]
  exact Finset.le_sup hs

theorem Ch_inter_iff {P Q : Set (SG E).β} {k : ℕ} {x : SC E} :
    x ∈ (SG E).Ch (P ∩ Q) k ↔ x ∈ (SG E).Ch P k ∧ x ∈ supported ℤ ℤ Q := by
  rw [GC.mem_Ch, GC.mem_Ch, supported_inter, Submodule.mem_inf]
  tauto

/-- **The small-simplices theorem, surjectivity**: every singular `k`-cycle of `A` is
homologous in `A` to a `𝒰`-small cycle. -/
theorem small_surj {A : Set E} {𝒰 : Set (Set E)} (hU : ∀ U ∈ 𝒰, IsOpen U)
    (hcov : A ⊆ ⋃₀ 𝒰) {k : ℕ} {z : SC E} (hz : z ∈ (SG E).Z (SA A) k) :
    ∃ z' ∈ (SG E).Z (SA A ∩ Small 𝒰) k, z - z' ∈ (SG E).B (SA A) k := by
  have hzC : z ∈ (SG E).Ch (SA A) k := hz.1
  have hzd : (SG E).d z = 0 := hz.2
  have hzS := (GC.mem_Ch.mp hzC).1
  have hzH := (GC.mem_Ch.mp hzC).2
  obtain ⟨q, hq⟩ := exists_small_chain hU hcov hzS
  refine ⟨(sSd ^ q) z, ⟨Ch_inter_iff.mpr ⟨GC.mem_Ch.mpr
    ⟨sSd_pow_mem_hered (hered_SA A) hzS q, sSd_pow_mem_homog hzH q⟩, hq⟩, ?_⟩, ?_⟩
  · show (SG E).d ((sSd ^ q) z) = 0
    rw [sd_sSd_pow, hzd, map_zero]
  · refine ⟨sD q z, GC.mem_Ch.mpr ⟨sD_mem_hered (hered_SA A) hzS q, sD_mem_homog hzH q⟩, ?_⟩
    have := sd_sD q z
    rw [hzd, map_zero, add_zero] at this
    exact this

/-- **The small-simplices theorem, injectivity**: a `𝒰`-small cycle of `A` that bounds in `A`
bounds a `𝒰`-small chain of `A`. -/
theorem small_inj {A : Set E} {𝒰 : Set (Set E)} (hU : ∀ U ∈ 𝒰, IsOpen U)
    (hcov : A ⊆ ⋃₀ 𝒰) {k : ℕ} {z : SC E} (hz : z ∈ (SG E).Z (SA A ∩ Small 𝒰) k)
    (hb : z ∈ (SG E).B (SA A) k) : z ∈ (SG E).B (SA A ∩ Small 𝒰) k := by
  have hzC : z ∈ (SG E).Ch (SA A ∩ Small 𝒰) k := hz.1
  have hzd : (SG E).d z = 0 := hz.2
  obtain ⟨w, hwC, rfl⟩ := hb
  have hwS := (GC.mem_Ch.mp hwC).1
  have hwH := (GC.mem_Ch.mp hwC).2
  have hzC' := GC.mem_Ch.mp hzC
  obtain ⟨q, hq⟩ := exists_small_chain hU hcov hwS
  have hP := hered_inter (hered_SA A) (hered_Small 𝒰)
  refine ⟨(sSd ^ q) w + sD q ((SG E).d w), ?_, ?_⟩
  · refine Submodule.add_mem _ (Ch_inter_iff.mpr ⟨GC.mem_Ch.mpr
      ⟨sSd_pow_mem_hered (hered_SA A) hwS q, sSd_pow_mem_homog hwH q⟩, hq⟩) ?_
    exact GC.mem_Ch.mpr ⟨sD_mem_hered hP hzC'.1 q, sD_mem_homog hzC'.2 q⟩
  · have := sd_sD q ((SG E).d w)
    rw [hzd, map_zero, add_zero] at this
    rw [map_add, sd_sSd_pow, this]
    abel

/-- **The small-simplices theorem**: the inclusion of `𝒰`-small chains induces an isomorphism
`H_k(C^𝒰(A)) ≅ H_k(C(A))` in every degree. -/
noncomputable def smallEquiv {A : Set E} {𝒰 : Set (Set E)} (hU : ∀ U ∈ 𝒰, IsOpen U)
    (hcov : A ⊆ ⋃₀ 𝒰) (k : ℕ) : (SG E).H (SA A ∩ Small 𝒰) k ≃ₗ[ℤ] (SG E).H (SA A) k :=
  HQ.equiv LinearMap.id (GC.Z_mono Set.inter_subset_left k) (GC.B_mono Set.inter_subset_left k)
    (fun z hz => by
      obtain ⟨z', hz', h⟩ := small_surj hU hcov hz
      exact ⟨z', hz', by simpa using h⟩)
    (fun z hz hb => small_inj hU hcov hz (by simpa using hb))

theorem closed_of_hered {P : Set (SG E).β} (hP : Hered P) : (SG E).Closed P := by
  rintro ⟨k, σ⟩ hσ
  rcases k with _ | k
  · rw [show (single ⟨0, σ⟩ 1 : SC E) = ssim σ from rfl, sd_ssim_zero]; exact Submodule.zero_mem _
  · rw [show (single ⟨k + 1, σ⟩ 1 : SC E) = ssim σ from rfl, sd_ssim_succ]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _
      (single_mem_supported ℤ _ (hP _ hσ _ (range_comp_subset σ _)))

theorem hered_le (s : (SG E).β) : Hered {t : (SG E).β | Set.range t.2 ⊆ Set.range s.2} :=
  fun _ h _ ht => ht.trans h

theorem range_of_mem_support_sd {s t : (SG E).β} (ht : t ∈ ((SG E).d (single s 1)).support) :
    Set.range t.2 ⊆ Set.range s.2 :=
  (mem_supported ℤ _).mp (closed_of_hered (hered_le s) s (show Set.range s.2 ⊆ Set.range s.2 from
    subset_refl _)) ht

end Small

end

end QE.Excision
