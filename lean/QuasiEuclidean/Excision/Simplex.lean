-- SPDX-License-Identifier: MIT
-- Copyright 2026 Metere Industries, Inc. Author: Alfredo Metere.
-- Quasi-Euclidean Granular Geometry. Any derivative work must carry this notice:
--   This work is derivative of the Quasi-Euclidean Granular Geometry book
--   authored by Alfredo Metere. Copyright 2026 Metere Industries, Inc.
--   All rights reserved
-- See LICENSE.md and NOTICE.

import QuasiEuclidean.Excision.Linear

/-!
# Singular chains and affine simplices

Book: Proposition `prop:topology-homology-singular` (Chapter 10), infrastructure.

The singular `k`-simplices of a space `E` are the continuous maps from Mathlib's standard
simplex `Δ k = StdSimplex ℝ (Fin (k+1))` (the domain used by Mathlib's singular homology)
to `E`; with precomposition by `StdSimplex.map` they form a simplicial basis, and the
singular chain complex is `SG E`.

A tuple `w` of points of `Δ k` (in weight coordinates `Vk k = ℝ^{k+1}`) defines the affine
simplex `affΔ w : Δ m → Δ k`, `t ↦ Σ tⱼ wⱼ`.  Pushing linear chains of `Δ k` forward along
a singular simplex `σ : Δ k → E` (`push σ`) is a chain map, compatible with affine maps;
this is how the subdivision of linear chains is transported to singular chains.

No measure theory is used.
-/

namespace QE.Excision

open Finsupp

noncomputable section

/-! ## The standard simplex in weight coordinates -/

/-- Mathlib's standard topological `k`-simplex. -/
abbrev Δ (k : ℕ) : Type := Convexity.StdSimplex ℝ (Fin (k + 1))

/-- The weight space `ℝ^{k+1}` (with the sup norm). -/
abbrev Vk (k : ℕ) : Type := Fin (k + 1) → ℝ

/-- Weight coordinates of a point of the standard simplex. -/
def wt {k : ℕ} (t : Δ k) : Vk k := fun i => t.weights i

/-- The standard simplex as a subset of `ℝ^{k+1}`. -/
def Δset (k : ℕ) : Set (Vk k) := {x | (∀ i, 0 ≤ x i) ∧ ∑ i, x i = 1}

theorem wt_mem {k : ℕ} (t : Δ k) : wt t ∈ Δset k :=
  ⟨fun i => t.nonneg i, Convexity.StdSimplex.total_of_fintype t⟩

theorem isEmbedding_wt (k : ℕ) : Topology.IsEmbedding (wt : Δ k → Vk k) :=
  Convexity.StdSimplex.isEmbedding_toFun_comp_weights ℝ (Fin (k + 1))

theorem continuous_wt (k : ℕ) : Continuous (wt : Δ k → Vk k) := (isEmbedding_wt k).continuous

theorem wt_injective {k : ℕ} : Function.Injective (wt : Δ k → Vk k) := (isEmbedding_wt k).injective

/-- The point of the standard simplex with given weights. -/
def mkS {k : ℕ} (x : Vk k) (hx : x ∈ Δset k) : Δ k where
  weights := Finsupp.equivFunOnFinite.symm x
  nonneg := fun i => by simpa using hx.1 i
  total := by
    rw [Finsupp.sum_fintype _ _ (fun _ => rfl)]
    simpa using hx.2

theorem wt_mkS {k : ℕ} (x : Vk k) (hx : x ∈ Δset k) : wt (mkS x hx) = x := by
  funext i; simp [wt, mkS]

theorem mkS_wt {k : ℕ} (t : Δ k) : mkS (wt t) (wt_mem t) = t :=
  wt_injective (wt_mkS _ _)

theorem range_wt (k : ℕ) : Set.range (wt : Δ k → Vk k) = Δset k := by
  ext x
  exact ⟨fun ⟨t, ht⟩ => ht ▸ wt_mem t, fun hx => ⟨mkS x hx, wt_mkS x hx⟩⟩

theorem isCompact_Δset (k : ℕ) : IsCompact (Δset k) := by
  rw [← range_wt]; exact isCompact_range (continuous_wt k)

theorem convex_Δset (k : ℕ) : Convex ℝ (Δset k) := by
  intro x hx y hy a b ha hb hab
  refine ⟨fun i => ?_, ?_⟩
  · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    nlinarith [hx.1 i, hy.1 i]
  · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_add_distrib,
      ← Finset.mul_sum, hx.2, hy.2]
    linarith

/-- The `j`-th vertex `eⱼ`. -/
def vert {k : ℕ} (j : Fin (k + 1)) : Vk k := Pi.single j 1

theorem vert_mem {k : ℕ} (j : Fin (k + 1)) : vert j ∈ Δset k := by
  refine ⟨fun i => ?_, ?_⟩
  · simp only [vert, Pi.single_apply]; split_ifs <;> norm_num
  · simp [vert]

theorem norm_vert_sub_le {k : ℕ} (i j : Fin (k + 1)) : ‖vert i - vert j‖ ≤ 1 := by
  refine (pi_norm_le_iff_of_nonneg zero_le_one).mpr fun l => ?_
  simp only [vert, Pi.sub_apply, Pi.single_apply, Real.norm_eq_abs]
  split_ifs <;> norm_num

/-- The linear map `x ↦ Σ xⱼ wⱼ` of a vertex tuple. -/
def affL {m k : ℕ} (w : Fin (m + 1) → Vk k) : Vk m →ₗ[ℝ] Vk k := Fintype.linearCombination ℝ w

theorem affL_apply {m k : ℕ} (w : Fin (m + 1) → Vk k) (x : Vk m) :
    affL w x = ∑ j, x j • w j := Fintype.linearCombination_apply ℝ w x

theorem affL_vert {m k : ℕ} (w : Fin (m + 1) → Vk k) (j : Fin (m + 1)) :
    affL w (vert j) = w j := by
  rw [affL_apply]
  simp [vert, Pi.single_apply]

theorem affL_comp_vert {m k : ℕ} (w : Fin (m + 1) → Vk k) :
    (affL w ∘ vert : Fin (m + 1) → Vk k) = w := funext (affL_vert w)

theorem affL_of_vert {k : ℕ} : affL (vert : Fin (k + 1) → Vk k) = LinearMap.id := by
  refine LinearMap.ext fun x => funext fun i => ?_
  rw [affL_apply]
  simp [vert, Finset.sum_apply, Pi.single_apply]

theorem affL_comp {l m k : ℕ} (w : Fin (m + 1) → Vk k) (u : Fin (l + 1) → Vk m) :
    affL w ∘ₗ affL u = affL (affL w ∘ u) := by
  ext x
  simp only [LinearMap.comp_apply, affL_apply, map_sum, map_smul, Function.comp_apply]

theorem affL_mem {m k : ℕ} {w : Fin (m + 1) → Vk k} (hw : ∀ j, w j ∈ Δset k) {x : Vk m}
    (hx : x ∈ Δset m) : affL w x ∈ Δset k := by
  rw [affL_apply]
  exact (convex_Δset k).sum_mem (fun j _ => hx.1 j) hx.2 (fun j _ => hw j)

/-- The affine simplex `Δ m → Δ k` with vertices `w`. -/
def affΔ {m k : ℕ} (w : Fin (m + 1) → Vk k) (hw : ∀ j, w j ∈ Δset k) : C(Δ m, Δ k) where
  toFun t := mkS (affL w (wt t)) (affL_mem hw (wt_mem t))
  continuous_toFun := by
    rw [(isEmbedding_wt k).continuous_iff]
    exact ((affL w).continuous_of_finiteDimensional.comp (continuous_wt m)).congr
      (fun t => (wt_mkS _ _).symm)

theorem wt_affΔ {m k : ℕ} (w : Fin (m + 1) → Vk k) (hw : ∀ j, w j ∈ Δset k) (t : Δ m) :
    wt (affΔ w hw t) = affL w (wt t) := wt_mkS _ (affL_mem hw (wt_mem t))

theorem affΔ_comp {l m k : ℕ} (w : Fin (m + 1) → Vk k) (hw : ∀ j, w j ∈ Δset k)
    (u : Fin (l + 1) → Vk m) (hu : ∀ j, u j ∈ Δset m) :
    (affΔ w hw).comp (affΔ u hu) =
      affΔ (affL w ∘ u) (fun j => affL_mem hw (hu j)) := by
  ext t : 1
  apply wt_injective
  simp only [ContinuousMap.comp_apply, wt_affΔ]
  rw [← LinearMap.comp_apply, affL_comp]

theorem affΔ_vert (k : ℕ) : affΔ (vert : Fin (k + 1) → Vk k) vert_mem = ContinuousMap.id _ := by
  ext t : 1
  apply wt_injective
  simp [wt_affΔ, affL_of_vert]

/-- The map of standard simplices induced by a map of vertex sets. -/
def smap {m k : ℕ} (f : Fin (m + 1) → Fin (k + 1)) : C(Δ m, Δ k) :=
  ⟨Convexity.StdSimplex.map f, Convexity.StdSimplex.continuous_map ℝ f⟩

theorem wt_smap {m k : ℕ} (f : Fin (m + 1) → Fin (k + 1)) (t : Δ m) :
    wt (smap f t) = affL (vert ∘ f) (wt t) := by
  funext i
  simp only [wt, smap, ContinuousMap.coe_mk, Convexity.StdSimplex.weights_map,
    Finsupp.mapDomain_fintype, affL_apply, Function.comp_apply, vert]
  simp [Finsupp.finsetSum_apply, Finset.sum_apply, Pi.single_apply, Finsupp.single_apply,
    eq_comm]

theorem smap_eq {m k : ℕ} (f : Fin (m + 1) → Fin (k + 1)) :
    smap f = affΔ (vert ∘ f) (fun _ => vert_mem _) := by
  ext t : 1
  apply wt_injective
  rw [wt_smap, wt_affΔ]

/-! ## Singular chains -/

section Singular

variable (E : Type) [TopologicalSpace E]

/-- The simplicial basis of singular simplices `Δ k → E`. -/
abbrev sBasis : SBasis where
  X k := C(Δ k, E)
  act f σ := σ.comp (smap f)
  act_comp f g σ := by
    ext t : 1
    simp only [ContinuousMap.comp_apply, smap, ContinuousMap.coe_mk]
    rw [Convexity.StdSimplex.map_map]
    rfl

/-- The singular chain complex of `E`. -/
abbrev SG : GC := (sBasis E).toGC

/-- Singular chains. -/
abbrev SC : Type := (SG E).β →₀ ℤ

variable {E}

/-- A singular simplex, as a chain. -/
abbrev ssim {k : ℕ} (σ : C(Δ k, E)) : SC E := single (⟨k, σ⟩ : (SG E).β) 1

theorem sd_ssim_zero (σ : C(Δ 0, E)) : (SG E).d (ssim σ) = 0 := by
  rw [SBasis.toGC_d]; exact SBasis.d_single_zero (sBasis E) σ

theorem sd_ssim_succ {k : ℕ} (σ : C(Δ (k + 1), E)) :
    (SG E).d (ssim σ) = ∑ i : Fin (k + 2), ((-1 : ℤ) ^ (i : ℕ)) • ssim (σ.comp (smap (Fin.succAbove i))) := by
  rw [SBasis.toGC_d]; exact SBasis.d_single_succ (sBasis E) σ

theorem ssim_mem_homog {k : ℕ} (σ : C(Δ k, E)) : ssim σ ∈ (SG E).homog k :=
  single_mem_supported ℤ _ rfl

theorem range_comp_subset {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (σ : C(X, E)) (f : C(Y, X)) : Set.range (σ.comp f) ⊆ Set.range σ := by
  rw [ContinuousMap.coe_comp]; exact Set.range_comp_subset_range _ _

/-- The singular simplices with image in `A`. -/
def SA (A : Set E) : Set (SG E).β := {s | Set.range s.2 ⊆ A}

theorem SA_closed (A : Set E) : (SG E).Closed (SA A) := by
  rintro ⟨k, σ⟩ hσ
  rcases k with _ | k
  · rw [show (single ⟨0, σ⟩ 1 : SC E) = ssim σ from rfl, sd_ssim_zero]; exact Submodule.zero_mem _
  · rw [show (single ⟨k + 1, σ⟩ 1 : SC E) = ssim σ from rfl, sd_ssim_succ]
    refine Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (single_mem_supported ℤ _ ?_)
    exact (range_comp_subset σ _).trans hσ

theorem SA_mono {A A' : Set E} (h : A ⊆ A') : SA A ⊆ SA A' := fun _ hs => hs.trans h

/-! ## Pushing linear chains of `Δ k` forward along a singular simplex -/

/-- Linear simplices of `Δ k`: all vertices in `Δset k`. -/
def InΔ (k : ℕ) : Set (LG (Vk k)).β := {s | ∀ j, s.2 j ∈ Δset k}

open Classical in
/-- `push σ`: the linear simplex `[w]` of `Δ k` goes to the singular simplex `σ ∘ affΔ w`. -/
def push {k : ℕ} (σ : C(Δ k, E)) : LC (Vk k) →ₗ[ℤ] SC E :=
  linearCombination ℤ (fun s : (LG (Vk k)).β =>
    if h : ∀ j, s.2 j ∈ Δset k then ssim (σ.comp (affΔ s.2 h)) else 0)

theorem push_lsim {k m : ℕ} (σ : C(Δ k, E)) (w : Fin (m + 1) → Vk k) (hw : ∀ j, w j ∈ Δset k) :
    push σ (lsim w) = ssim (σ.comp (affΔ w hw)) := by
  unfold push lsim
  rw [linearCombination_single, one_smul]; simp only [hw, implies_true, ↓reduceDIte]

theorem push_vert {k : ℕ} (σ : C(Δ k, E)) : push σ (lsim (vert : Fin (k + 1) → Vk k)) = ssim σ := by
  rw [push_lsim σ _ vert_mem, affΔ_vert]; rfl

/-- `push σ` is a chain map on linear chains of `Δ k`. -/
theorem push_ld {k : ℕ} (σ : C(Δ k, E)) {x : LC (Vk k)} (hx : x ∈ supported ℤ ℤ (InΔ k)) :
    push σ ((LG (Vk k)).d x) = (SG E).d (push σ x) := by
  refine linearMap_congr_support (push σ ∘ₗ (LG (Vk k)).d) ((SG E).d ∘ₗ push σ)
    (fun s hs => ?_)
  obtain ⟨m, w⟩ := s
  have hw : ∀ j, w j ∈ Δset k := (mem_supported ℤ _).mp hx hs
  simp only [LinearMap.coe_comp, Function.comp_apply]
  rw [show (single ⟨m, w⟩ 1 : LC (Vk k)) = lsim w from rfl, push_lsim σ w hw]
  rcases m with _ | m
  · rw [ld_lsim_zero, sd_ssim_zero, map_zero]
  · rw [ld_lsim_succ, sd_ssim_succ, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_zsmul, push_lsim σ (w ∘ Fin.succAbove i) (fun j => hw _)]
    congr 2
    rw [ContinuousMap.comp_assoc, smap_eq, affΔ_comp]
    congr 2
    rw [← Function.comp_assoc, affL_comp_vert]

/-- Pushing along `σ ∘ affΔ u` is pushing the image under `affL u` along `σ`. -/
theorem push_comp {k m : ℕ} (σ : C(Δ k, E)) (u : Fin (m + 1) → Vk k) (hu : ∀ j, u j ∈ Δset k)
    {x : LC (Vk m)} (hx : x ∈ supported ℤ ℤ (InΔ m)) :
    push (σ.comp (affΔ u hu)) x = push σ (lmap (affL u) x) := by
  refine linearMap_congr_support (push (σ.comp (affΔ u hu))) (push σ ∘ₗ lmap (affL u))
    (fun s hs => ?_)
  obtain ⟨l, w⟩ := s
  have hw : ∀ j, w j ∈ Δset m := (mem_supported ℤ _).mp hx hs
  simp only [LinearMap.coe_comp, Function.comp_apply]
  rw [show (single ⟨l, w⟩ 1 : LC (Vk m)) = lsim w from rfl, lmap_lsim, push_lsim _ w hw,
    push_lsim σ (affL u ∘ w) (fun j => affL_mem hu (hw j)), ContinuousMap.comp_assoc,
    affΔ_comp]

/-- Images of pushed simplices lie in the image of `σ`. -/
theorem push_mem_supported {k : ℕ} (σ : C(Δ k, E)) (x : LC (Vk k)) :
    push σ x ∈ supported ℤ ℤ {s : (SG E).β | Set.range s.2 ⊆ Set.range σ} := by
  unfold push
  refine lc_mem fun s _ => ?_
  split_ifs with h
  · exact single_mem_supported ℤ _ (range_comp_subset σ _)
  · exact Submodule.zero_mem _

theorem push_mem_homog {k m : ℕ} (σ : C(Δ k, E)) {x : LC (Vk k)} (hx : x ∈ (LG (Vk k)).homog m) :
    push σ x ∈ (SG E).homog m := by
  unfold push
  refine lc_mem fun s hs => ?_
  have : s.1 = m := (mem_supported ℤ _).mp hx hs
  split_ifs with h
  · rw [← this]; exact ssim_mem_homog _
  · exact Submodule.zero_mem _

end Singular

end

end QE.Excision
