-- SPDX-License-Identifier: MIT
-- Copyright 2026 Metere Industries, Inc. Author: Alfredo Metere.
-- Quasi-Euclidean Granular Geometry. Any derivative work must carry this notice:
--   This work is derivative of the Quasi-Euclidean Granular Geometry book
--   authored by Alfredo Metere. Copyright 2026 Metere Industries, Inc.
--   All rights reserved
-- See LICENSE.md and NOTICE.

import QuasiEuclidean.Excision.Bridge
import QuasiEuclidean.SingularHomologyInfra

/-!
# Singular chains of star-convex sets are acyclic

Book: Proposition `prop:topology-homology-singular` (Chapter 10), infrastructure.

For a set `W` star-convex about a point `p ∈ W` of a real topological vector space, every
singular cycle of `W` of positive degree bounds in `W`, and so does every `0`-chain of
augmentation `0` (`acyclic_starConvex`).  Positive degrees: the straight-line homotopy
contracts `W` to `p`, so Mathlib's homotopy invariance gives `H_k(W) ≅ H_k(pt) = 0`, which is
transported to the concrete chains by `bridge`.  Degree `0`: the straight segment from `p`
to each vertex.

No measure theory is used.
-/

namespace QE.Excision

open CategoryTheory AlgebraicTopology Finsupp

noncomputable section

variable {E : Type} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E] [IsTopologicalAddGroup E]
  [ContinuousSMul ℝ E]

/-- **Contractibility kills homology**: the singular homology of a star-convex set vanishes in
positive degrees. -/
theorem subsingleton_mSing_starConvex {W : Set E} {p : E} (hW : StarConvex ℝ p W) (hp : p ∈ W)
    {k : ℕ} (hk : k ≠ 0) : Subsingleton (mSing k (TopCat.of W)) := by
  let c : W := ⟨p, hp⟩
  let ι : TopCat.of Unit ⟶ TopCat.of W := TopCat.ofHom (ContinuousMap.const Unit c)
  let r : TopCat.of W ⟶ TopCat.of Unit := TopCat.ofHom (ContinuousMap.const W ())
  have h1 : ι ≫ r = 𝟙 _ := by ext x
  let H : ContinuousMap.Homotopy (ContinuousMap.const W c) (ContinuousMap.id W) :=
    { toFun := fun q => ⟨(1 - (q.1 : ℝ)) • p + (q.1 : ℝ) • (q.2 : E),
        hW q.2.2 (sub_nonneg.mpr q.1.2.2) q.1.2.1 (sub_add_cancel _ _)⟩
      continuous_toFun := by fun_prop
      map_zero_left := fun x => Subtype.ext (by simp [c])
      map_one_left := fun x => Subtype.ext (by simp) }
  have e := QE.CubicalSingular.singularIsoOfRetract ι r h1 H k
  have hz : Limits.IsZero (QE.CubicalSingular.sing k (TopCat.of Unit)) :=
    isZero_singularHomologyFunctor_of_totallyDisconnectedSpace _ _ _ _ hk
  exact ModuleCat.isZero_iff_subsingleton.mp (hz.of_iso e.symm)

/-- The straight segment `[p, q]` as a singular `1`-simplex. -/
def seg (p q : E) : C(Δ 1, E) where
  toFun t := t.weights 0 • p + t.weights 1 • q
  continuous_toFun := by
    have h0 := Convexity.StdSimplex.continuous_weights_apply ℝ (M := Fin 2) 0
    have h1 := Convexity.StdSimplex.continuous_weights_apply ℝ (M := Fin 2) 1
    exact (h0.smul continuous_const).add (h1.smul continuous_const)

theorem weights_zero_add_one (t : Δ 1) : t.weights 0 + t.weights 1 = 1 := by
  have := Convexity.StdSimplex.total_of_fintype t
  rwa [Fin.sum_univ_two] at this

theorem range_seg {W : Set E} {p q : E} (hW : StarConvex ℝ p W) (hq : q ∈ W) :
    Set.range (seg p q) ⊆ W := by
  rintro _ ⟨t, rfl⟩
  exact hW hq (t.nonneg 0) (t.nonneg 1) (weights_zero_add_one t)

theorem Δ0_eq (t t' : Δ 0) : t = t' := Subsingleton.elim t t'

theorem eq_const_of_Δ0 (σ : C(Δ 0, E)) (t : Δ 0) : σ = ContinuousMap.const _ (σ t) := by
  ext t'; rw [Δ0_eq t' t]; rfl

theorem seg_face_zero (p q : E) : (seg p q).comp (smap (Fin.succAbove 0)) =
    ContinuousMap.const _ q := by
  ext t
  have h := wt_smap (Fin.succAbove (0 : Fin 2)) t
  have ht : wt t = vert 0 := by
    funext i; fin_cases i
    simp [wt, vert]
  rw [ht, affL_vert] at h
  have h0 := congrFun h 0
  have h1 := congrFun h 1
  simp only [wt, Function.comp_apply, vert] at h0 h1
  simp only [ContinuousMap.comp_apply, seg, ContinuousMap.coe_mk, ContinuousMap.const_apply]
  rw [h0, h1]
  simp

theorem seg_face_one (p q : E) : (seg p q).comp (smap (Fin.succAbove 1)) =
    ContinuousMap.const _ p := by
  ext t
  have h := wt_smap (Fin.succAbove (1 : Fin 2)) t
  have ht : wt t = vert 0 := by
    funext i; fin_cases i
    simp [wt, vert]
  rw [ht, affL_vert] at h
  have h0 := congrFun h 0
  have h1 := congrFun h 1
  simp only [wt, Function.comp_apply, vert] at h0 h1
  simp only [ContinuousMap.comp_apply, seg, ContinuousMap.coe_mk, ContinuousMap.const_apply]
  rw [h0, h1]
  simp

theorem sd_seg (p q : E) :
    (SG E).d (ssim (seg p q)) = ssim (ContinuousMap.const (Δ 0) q) -
      ssim (ContinuousMap.const (Δ 0) p) := by
  rw [sd_ssim_succ, Fin.sum_univ_two, seg_face_zero, seg_face_one]
  simp [sub_eq_add_neg]

/-- **Star-convex sets are acyclic.** -/
theorem acyclic_starConvex {W : Set E} {p : E} (hW : StarConvex ℝ p W) (hp : p ∈ W) :
    Acyclic (SG E) (SA W) := by
  intro k z hzS hzH hzd hza
  rcases k with _ | j
  · -- degree `0`: cone off from `p`
    have ha := hza rfl
    let pt : (SG E).β → E := fun s => s.2 (Classical.arbitrary _)
    refine ⟨linearCombination ℤ (fun s => ssim (seg p (pt s))) z, ?_, ?_, ?_⟩
    · refine lc_mem fun s hs => single_mem_supported ℤ _ (range_seg hW ?_)
      exact ((mem_supported ℤ _).mp hzS hs) ⟨_, rfl⟩
    · exact lc_mem fun s _ => ssim_mem_homog _
    · rw [map_lc]
      refine (lc_congr (g := fun s => ssim (ContinuousMap.const (Δ 0) (pt s)) -
        ssim (ContinuousMap.const (Δ 0) p)) (fun s _ => sd_seg p (pt s))).trans ?_
      have e1 : linearCombination ℤ (fun s : (SG E).β => ssim (ContinuousMap.const (Δ 0) (pt s))) z
          = z := by
        refine (lc_congr fun s hs => ?_).trans (lc_comp_single (A := SG E) LinearMap.id z)
        obtain ⟨m, σ⟩ := s
        have hm : m = 0 := (mem_supported ℤ _).mp hzH hs
        subst hm
        simp only [LinearMap.id_coe, id_eq]
        rw [← eq_const_of_Δ0 σ]
      have e2 : linearCombination ℤ (fun _ : (SG E).β => ssim (ContinuousMap.const (Δ 0) p)) z
          = (SG E).aug z • ssim (ContinuousMap.const (Δ 0) p) := by
        have := linearMap_congr_support
          (linearCombination ℤ (fun _ : (SG E).β => ssim (ContinuousMap.const (Δ 0) p)))
          (LinearMap.smulRight (SG E).aug (ssim (ContinuousMap.const (Δ 0) p))) (x := z)
          (fun s hs => by
            have hm : (SG E).deg s = 0 := (mem_supported ℤ _).mp hzH hs
            rw [lc_single_one, LinearMap.smulRight_apply, GC.aug_single]
            simp only [show s.1 = 0 from hm, ↓reduceIte, one_smul])
        simpa using this
      have e3 : linearCombination ℤ (fun s : (SG E).β => ssim (ContinuousMap.const (Δ 0) (pt s)) -
          ssim (ContinuousMap.const (Δ 0) p)) z = z := by
        have hsub : linearCombination ℤ (fun s : (SG E).β =>
            ssim (ContinuousMap.const (Δ 0) (pt s)) - ssim (ContinuousMap.const (Δ 0) p)) z =
            linearCombination ℤ (fun s => ssim (ContinuousMap.const (Δ 0) (pt s))) z -
            linearCombination ℤ (fun _ : (SG E).β => ssim (ContinuousMap.const (Δ 0) p)) z := by
          simp only [linearCombination_apply, smul_sub, Finsupp.sum_sub]
        rw [hsub, e1, e2, ha, zero_smul, sub_zero]
      exact e3
  · -- positive degree: contractibility
    have hsub : Subsingleton ((SG E).H (SA W) (j + 1)) :=
      have := subsingleton_mSing_starConvex hW hp (Nat.succ_ne_zero j)
      (bridge W (j + 1)).toEquiv.subsingleton
    have hzZ : z ∈ (SG E).Z (SA W) (j + 1) :=
      Submodule.mem_inf.mpr ⟨GC.mem_Ch.mpr ⟨hzS, hzH⟩, hzd⟩
    have h0 : (Submodule.Quotient.mk ⟨z, hzZ⟩ : (SG E).H (SA W) (j + 1)) = 0 :=
      Subsingleton.elim _ _
    rw [Submodule.Quotient.mk_eq_zero] at h0
    obtain ⟨y, hy, hyz⟩ := h0
    obtain ⟨hyS, hyH⟩ := GC.mem_Ch.mp hy
    exact ⟨y, hyS, hyH, hyz⟩

end

end QE.Excision
