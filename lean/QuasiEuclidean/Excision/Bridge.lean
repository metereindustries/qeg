-- SPDX-License-Identifier: MIT
-- Copyright 2026 Metere Industries, Inc. Author: Alfredo Metere.
-- Quasi-Euclidean Granular Geometry. Any derivative work must carry this notice:
--   This work is derivative of the Quasi-Euclidean Granular Geometry book
--   authored by Alfredo Metere. Copyright 2026 Metere Industries, Inc.
--   All rights reserved
-- See LICENSE.md and NOTICE.

import QuasiEuclidean.Excision.Subdivision

/-!
# The concrete singular chains compute Mathlib's singular homology

Book: Proposition `prop:topology-homology-singular` (Chapter 10), infrastructure.

For a subspace `A ⊆ E`, Mathlib's singular chain complex of `A` (the alternating face map
complex of the free simplicial abelian group on `TopCat.toSSet A`) is degreewise isomorphic
to the chains of `SG E` supported on the simplices with image in `A`, compatibly with the
boundaries.  Hence `H_k(SA A) ≅ H_k(A; ℤ)` (Mathlib's `singularHomologyFunctor`), in every
degree (`bridge`).

Consequence (`acyclic_starConvex`): the singular chains of a star-convex set are acyclic,
from Mathlib's homotopy invariance (a star-convex set is contractible) and the vanishing of
the homology of a point in positive degrees; in degree `0` directly by straight paths.

No measure theory is used.
-/

namespace QE.Excision

open CategoryTheory AlgebraicTopology Simplicial Opposite Limits Finsupp

noncomputable section

/-- Mathlib's singular homology `H_k(Y; ℤ)`. -/
abbrev mSing (k : ℕ) (Y : TopCat.{0}) : ModuleCat.{0} ℤ :=
  ((singularHomologyFunctor (ModuleCat.{0} ℤ) k).obj (ModuleCat.of ℤ ℤ)).obj Y

/-- Mathlib's singular chain complex of `Y`. -/
abbrev MK (Y : TopCat.{0}) : ChainComplex (ModuleCat.{0} ℤ) ℕ :=
  (TopCat.toSSet.obj Y).chainComplex (ModuleCat.of ℤ ℤ)

/-! ## Homology quotients under degreewise isomorphisms -/

section Generic

attribute [local instance 2000] Submodule.module Submodule.Quotient.module

variable {M₁ M₂ M₃ N : Type*} [AddCommGroup M₁] [Module ℤ M₁] [AddCommGroup M₂] [Module ℤ M₂]
  [AddCommGroup M₃] [Module ℤ M₃] [AddCommGroup N]

/-- A three-term complex `M₁ → M₂ → M₃` whose first two terms are identified with chain groups
`C₁, C₂` compatibly with the boundary `D` has homology `HQ (C₂ ∩ ker D) (D C₁)`. -/
def hqEquiv (f : M₁ →ₗ[ℤ] M₂) (g : M₂ →ₗ[ℤ] M₃) (h : ∀ x, g (f x) = 0)
    (C₁ C₂ : Submodule ℤ N) (D : N →ₗ[ℤ] N) (Φ₁ : M₁ ≃ₗ[ℤ] C₁) (Φ₂ : M₂ ≃ₗ[ℤ] C₂)
    (hf : ∀ x, (Φ₂ (f x) : N) = D (Φ₁ x)) (hg : ∀ y, g y = 0 ↔ D (Φ₂ y) = 0) :
    (LinearMap.ker g ⧸ LinearMap.range (f.codRestrict (LinearMap.ker g) h)) ≃ₗ[ℤ]
      HQ (C₂ ⊓ LinearMap.ker D) (C₁.map D) := by
  let Z := C₂ ⊓ LinearMap.ker D
  let ψ : LinearMap.ker g →ₗ[ℤ] Z := LinearMap.codRestrict Z
    (C₂.subtype ∘ₗ Φ₂.toLinearMap ∘ₗ (LinearMap.ker g).subtype) (fun y =>
      Submodule.mem_inf.mpr ⟨(Φ₂ y.1).2, (hg y.1).mp y.2⟩)
  have hψ : ∀ y, (ψ y : N) = Φ₂ y.1 := fun _ => rfl
  have hbij : Function.Bijective ψ := by
    constructor
    · intro y y' hyy
      have : (Φ₂ y.1 : N) = Φ₂ y'.1 := by rw [← hψ, ← hψ, hyy]
      exact Subtype.ext (Φ₂.injective (Subtype.ext this))
    · intro z
      obtain ⟨hz1, hz2⟩ := Submodule.mem_inf.mp z.2
      refine ⟨⟨Φ₂.symm ⟨z, hz1⟩, (hg _).mpr ?_⟩, ?_⟩
      · rw [LinearEquiv.apply_symm_apply]; exact hz2
      · apply Subtype.ext; rw [hψ, LinearEquiv.apply_symm_apply]
  let Ψ : LinearMap.ker g ≃ₗ[ℤ] Z := LinearEquiv.ofBijective ψ hbij
  refine Submodule.Quotient.equiv _ _ Ψ ?_
  ext z
  simp only [Submodule.mem_map, LinearMap.mem_range, Submodule.mem_comap, Submodule.coe_subtype]
  constructor
  · rintro ⟨_, ⟨x, rfl⟩, rfl⟩
    exact ⟨Φ₁ x, (Φ₁ x).2, (hf x).symm⟩
  · rintro ⟨c, hc, hcz⟩
    refine ⟨_, ⟨Φ₁.symm ⟨c, hc⟩, rfl⟩, ?_⟩
    apply Subtype.ext
    change (ψ _ : N) = z
    rw [hψ]
    change (Φ₂ (f (Φ₁.symm ⟨c, hc⟩)) : N) = z
    rw [hf, LinearEquiv.apply_symm_apply]
    exact hcz

end Generic

/-! ## Degreewise identification of the chain groups -/

section Chains

variable {E : Type} [TopologicalSpace E] (A : Set E)

/-- The `k`-simplices of `SG E` with image in `A`. -/
def cellSet (k : ℕ) : Set (SG E).β := {b | b ∈ SA A ∧ (SG E).deg b = k}

/-- Composition with the inclusion `A ⊆ E`. -/
def inclA {X : Type} [TopologicalSpace X] (σ : C(X, A)) : C(X, E) :=
  (⟨Subtype.val, continuous_subtype_val⟩ : C(A, E)).comp σ

theorem range_inclA {X : Type} [TopologicalSpace X] (σ : C(X, A)) : Set.range (inclA A σ) ⊆ A := by
  rintro _ ⟨t, rfl⟩; exact (σ t).2

/-- Singular simplices of `A` are the simplices of `E` with image in `A`. -/
def simpEquiv (k : ℕ) : C(Δ k, A) ≃ cellSet A k :=
  Equiv.ofBijective (fun σ => ⟨⟨k, inclA A σ⟩, range_inclA A σ, rfl⟩) (by
    constructor
    · intro σ τ h
      have h2 := congrArg (fun b : cellSet A k => b.1) h
      simp only [Sigma.mk.inj_iff, heq_eq_eq, true_and] at h2
      ext t
      exact congrFun (congrArg DFunLike.coe h2) t
    · rintro ⟨⟨j, τ⟩, hA, hj⟩
      subst hj
      refine ⟨⟨fun t => ⟨τ t, hA ⟨t, rfl⟩⟩, τ.continuous.subtype_mk _⟩, ?_⟩
      rfl)

theorem simpEquiv_apply (k : ℕ) (σ : C(Δ k, A)) :
    ((simpEquiv A k σ : cellSet A k) : (SG E).β) = ⟨k, inclA A σ⟩ := rfl

open Classical in
/-- Mathlib's singular `k`-chains of `A` are the `k`-chains of `SG E` supported in `A`. -/
def chainEquiv (k : ℕ) :
    (MK (TopCat.of A)).X k ≃ₗ[ℤ] (SG E).Ch (SA A) k :=
  (ModuleCat.coprodIsoDirectSum
      (fun _ : (TopCat.toSSet.obj (TopCat.of A)) _⦋k⦌ => ModuleCat.of ℤ ℤ)).toLinearEquiv ≪≫ₗ
    (finsuppLEquivDirectSum ℤ ℤ _).symm ≪≫ₗ
    Finsupp.domLCongr ((TopCat.of A).toSSetObjEquiv (op ⦋k⦌)) ≪≫ₗ
    Finsupp.domLCongr (simpEquiv A k) ≪≫ₗ
    (Finsupp.supportedEquivFinsupp (cellSet A k)).symm

open Classical in
theorem chainEquiv_ι (k : ℕ) (x : (TopCat.toSSet.obj (TopCat.of A)) _⦋k⦌) :
    ((chainEquiv A k ((SSet.ιChainComplex _ x : ModuleCat.of ℤ ℤ ⟶ (MK (TopCat.of A)).X k).hom
      (1 : ℤ)) : (SG E).Ch (SA A) k) : SC E) =
      single ⟨k, inclA A ((TopCat.of A).toSSetObjEquiv (op ⦋k⦌) x)⟩ 1 := by
  unfold chainEquiv SSet.ιChainComplex
  erw [LinearEquiv.trans_apply, LinearEquiv.trans_apply, LinearEquiv.trans_apply,
    LinearEquiv.trans_apply, Iso.toLinearEquiv_apply, ModuleCat.ι_coprodIsoDirectSum_hom_apply,
    finsuppLEquivDirectSum_symm_lof, Finsupp.domLCongr_single, Finsupp.domLCongr_single,
    Finsupp.supportedEquivFinsupp_symm_single]
  rfl

theorem toSSet_δ (k : ℕ) (i : Fin (k + 2)) (x : (TopCat.toSSet.obj (TopCat.of A)) _⦋k + 1⦌) :
    (TopCat.of A).toSSetObjEquiv (op ⦋k⦌) ((TopCat.toSSet.obj (TopCat.of A)).δ i x) =
      ((TopCat.of A).toSSetObjEquiv (op ⦋k + 1⦌) x).comp (smap (Fin.succAbove i)) := rfl

/-- The identification of chain groups commutes with the boundaries. -/
theorem chainEquiv_d (j : ℕ) (y : (MK (TopCat.of A)).X (j + 1)) :
    ((chainEquiv A j ((MK (TopCat.of A)).d (j + 1) j y) : (SG E).Ch (SA A) j) : SC E) =
      (SG E).d (chainEquiv A (j + 1) y) := by
  let M₁ : (MK (TopCat.of A)).X (j + 1) ⟶ ModuleCat.of ℤ (SC E) :=
    (MK (TopCat.of A)).d (j + 1) j ≫
      ModuleCat.ofHom (((SG E).Ch (SA A) j).subtype ∘ₗ (chainEquiv A j).toLinearMap)
  let M₂ : (MK (TopCat.of A)).X (j + 1) ⟶ ModuleCat.of ℤ (SC E) :=
    ModuleCat.ofHom ((SG E).d ∘ₗ ((SG E).Ch (SA A) (j + 1)).subtype ∘ₗ
      (chainEquiv A (j + 1)).toLinearMap)
  have hM : M₁ = M₂ := by
    refine SSet.chainComplex_hom_ext (fun x => ?_)
    ext1
    refine LinearMap.ext_ring ?_
    simp only [M₁, M₂, SSet.ιChainComplex_d_assoc, Preadditive.sum_comp, Preadditive.zsmul_comp,
      ModuleCat.hom_sum, ModuleCat.hom_zsmul, ModuleCat.hom_comp, ModuleCat.hom_ofHom,
      LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.coe_comp,
      Function.comp_apply, LinearEquiv.coe_coe, Submodule.coe_subtype]
    erw [chainEquiv_ι A (j + 1) x]
    rw [show (single ⟨j + 1, inclA A ((TopCat.of A).toSSetObjEquiv (op ⦋j + 1⦌) x)⟩ 1 : SC E) =
      ssim (inclA A ((TopCat.of A).toSSetObjEquiv (op ⦋j + 1⦌) x)) from rfl, ← SBasis.toGC_d,
      sd_ssim_succ]
    refine Finset.sum_congr rfl fun i _ => ?_
    erw [chainEquiv_ι A j]
    rfl
  exact congrArg (fun M => M.hom y) hM

theorem next_down (k : ℕ) : (ComplexShape.down ℕ).next k = k - 1 := by
  cases k <;> simp

/-- **Bridge**: the homology of the singular chains of `E` supported in `A` is Mathlib's
singular homology `H_k(A; ℤ)`, in every degree. -/
def bridge (k : ℕ) : (SG E).H (SA A) k ≃ₗ[ℤ] mSing k (TopCat.of A) := by
  let K := MK (TopCat.of A)
  let S := K.sc' (k + 1) k (k - 1)
  have hf : ∀ x, ((chainEquiv A k (S.f.hom x) : (SG E).Ch (SA A) k) : SC E) =
      (SG E).d (chainEquiv A (k + 1) x) := fun x => chainEquiv_d A k x
  have hg : ∀ y, S.g.hom y = 0 ↔ (SG E).d (chainEquiv A k y) = 0 := by
    intro y
    rcases k with _ | j
    · have h0 : S.g = 0 := K.shape 0 (0 - 1) (by simp)
      have h1 : (SG E).d (chainEquiv A 0 y) = 0 :=
        GC.d_homog_zero (GC.mem_Ch.mp (chainEquiv A 0 y).2).2
      simp only [h0, h1, iff_true]
      rfl
    · have e := chainEquiv_d A j y
      constructor
      · intro hy
        rw [← e]
        have : (MK (TopCat.of A)).d (j + 1) j y = 0 := hy
        rw [this, map_zero]; rfl
      · intro hy
        rw [← e] at hy
        have : chainEquiv A j ((MK (TopCat.of A)).d (j + 1) j y) = 0 := Subtype.ext hy
        exact (LinearEquiv.map_eq_zero_iff _).mp this
  have hq := hqEquiv S.f.hom S.g.hom (fun x => S.moduleCat_zero_apply x)
    ((SG E).Ch (SA A) (k + 1)) ((SG E).Ch (SA A) k) (SG E).d (chainEquiv A (k + 1))
    (chainEquiv A k) hf hg
  exact hq.symm ≪≫ₗ (S.moduleCatHomologyIso.symm ≪≫
    (K.homologyIsoSc' (k + 1) k (k - 1) (ChainComplex.prev ℕ k) (next_down k)).symm).toLinearEquiv

end Chains

end

end QE.Excision
