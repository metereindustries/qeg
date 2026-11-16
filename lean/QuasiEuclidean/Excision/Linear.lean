-- SPDX-License-Identifier: MIT
-- Copyright 2026 Metere Industries, Inc. Author: Alfredo Metere.
-- Quasi-Euclidean Granular Geometry. Any derivative work must carry this notice:
--   This work is derivative of the Quasi-Euclidean Granular Geometry book
--   authored by Alfredo Metere. Copyright 2026 Metere Industries, Inc.
--   All rights reserved
-- See LICENSE.md and NOTICE.

import QuasiEuclidean.Excision.Graded

/-!
# Barycentric subdivision of linear chains

Book: Proposition `prop:topology-homology-singular` (Chapter 10), infrastructure.

A *linear simplex* in a real vector space `V` is a tuple of vertices `w : Fin (m+1) → V`;
linear chains form the simplicial chain complex `LG V` of the simplicial basis of vertex
tuples.  Following Hatcher (§2.1, proof of Prop. 2.21) we define

* the cone `b · [w₀,…,wₘ] = [b,w₀,…,wₘ]`, with `∂(b·x) = x - b·∂x - ε(x)[b]`;
* the barycentric subdivision `Sd [w] = b_w · Sd(∂[w])` (`Sd = id` on vertices);
* the operator `T [w] = b_w · ([w] - T ∂[w])` (`T = 0` on vertices),

and prove that `Sd` is an augmentation-preserving chain map, that `∂T + T∂ = id - Sd`,
that both commute with linear maps `V → W` (naturality), and the diameter estimate: the
simplices of `Sd [w]` lie in the convex hull of `w` and have diameter at most
`m/(m+1)` times that of `w`.

No measure theory is used.
-/

namespace QE.Excision

open Finsupp

noncomputable section

/-! ## Linear simplices -/

section Basis

variable (V : Type)

/-- The simplicial basis of vertex tuples in `V`. -/
abbrev lBasis : SBasis where
  X k := Fin (k + 1) → V
  act f w := w ∘ f
  act_comp _ _ _ := rfl

/-- The chain complex of linear chains in `V`. -/
abbrev LG : GC := (lBasis V).toGC

/-- Linear chains. -/
abbrev LC : Type := (LG V).β →₀ ℤ

end Basis

variable {V : Type} [AddCommGroup V] [Module ℝ V]

/-- The linear simplex with vertex tuple `w`, as a chain. -/
abbrev lsim {m : ℕ} (w : Fin (m + 1) → V) : LC V := single (⟨m, w⟩ : (LG V).β) 1

theorem ld_lsim_zero (w : Fin 1 → V) : (LG V).d (lsim w) = 0 := by
  rw [SBasis.toGC_d]; exact SBasis.d_single_zero (lBasis V) w

theorem ld_lsim_succ {m : ℕ} (w : Fin (m + 2) → V) :
    (LG V).d (lsim w) = ∑ i : Fin (m + 2), ((-1 : ℤ) ^ (i : ℕ)) • lsim (w ∘ Fin.succAbove i) := by
  rw [SBasis.toGC_d]; exact SBasis.d_single_succ (lBasis V) w

theorem lsim_mem_homog {m : ℕ} (w : Fin (m + 1) → V) : lsim w ∈ (LG V).homog m :=
  single_mem_supported ℤ _ rfl

theorem aug_lsim {m : ℕ} (w : Fin (m + 1) → V) :
    (LG V).aug (lsim w) = if m = 0 then 1 else 0 := by
  unfold GC.aug lsim
  rw [linearCombination_single, smul_eq_mul, one_mul]

/-- Two linear maps agreeing on all linear simplices of degree `m` agree on `homog m`. -/
theorem ext_homog {N : Type*} [AddCommGroup N] (L L' : LC V →ₗ[ℤ] N) {m : ℕ}
    (h : ∀ w : Fin (m + 1) → V, L (lsim w) = L' (lsim w)) {x : LC V}
    (hx : x ∈ (LG V).homog m) : L x = L' x := by
  refine linearMap_congr_support L L' fun s hs => ?_
  obtain ⟨k, w⟩ := s
  have hk : k = m := (mem_supported ℤ _).mp hx hs
  subst hk
  exact h w

/-! ## Cones -/

/-- The cone `b · [w] = [b, w₀, …, wₘ]`. -/
def cone (b : V) : LC V →ₗ[ℤ] LC V :=
  linearCombination ℤ (fun s : (LG V).β => lsim (Fin.cons b s.2 : Fin (s.1 + 2) → V))

theorem cone_lsim (b : V) {m : ℕ} (w : Fin (m + 1) → V) :
    cone b (lsim w) = lsim (Fin.cons b w : Fin (m + 2) → V) := by
  unfold cone lsim
  rw [linearCombination_single, one_smul]

/-- The vertex `[b]`. -/
abbrev pt (b : V) : LC V := lsim (fun _ : Fin 1 => b)

theorem cons_comp_succAbove_succ (b : V) {m : ℕ} (w : Fin (m + 2) → V) (i : Fin (m + 2)) :
    (Fin.cons b w : Fin (m + 3) → V) ∘ Fin.succAbove i.succ =
      Fin.cons b (w ∘ Fin.succAbove i) := by
  funext j
  refine Fin.cases ?_ (fun j => ?_) j
  · simp
  · simp [Fin.succ_succAbove_succ]

theorem cone_mem_homog (b : V) {m : ℕ} {x : LC V} (hx : x ∈ (LG V).homog m) :
    cone b x ∈ (LG V).homog (m + 1) := by
  rw [← ext_homog (cone b) (cone b) (fun _ => rfl) hx]
  unfold cone
  refine lc_mem fun s hs => ?_
  have : s.1 = m := (mem_supported ℤ _).mp hx hs
  rw [← this]
  exact lsim_mem_homog _

/-- **The cone formula** `∂(b·x) = x - b·∂x - ε(x)[b]`. -/
theorem ld_cone (b : V) (x : LC V) :
    (LG V).d (cone b x) = x - cone b ((LG V).d x) - (LG V).aug x • pt b := by
  have key : ∀ s : (LG V).β, (LG V).d (cone b (single s 1)) =
      single s 1 - cone b ((LG V).d (single s 1)) - (LG V).aug (single s 1) • pt b := by
    rintro ⟨m, w⟩
    rcases m with _ | m
    · rw [show (single ⟨0, w⟩ 1 : LC V) = lsim w from rfl, cone_lsim, ld_lsim_succ,
        ld_lsim_zero, map_zero, aug_lsim, Fin.sum_univ_two]
      have h0 : (Fin.cons b w : Fin 2 → V) ∘ Fin.succAbove 0 = w := by
        funext j; fin_cases j; rfl
      have h1 : (Fin.cons b w : Fin 2 → V) ∘ Fin.succAbove 1 = fun _ => b := by
        funext j; fin_cases j; rfl
      rw [h0, h1]
      simp [sub_eq_add_neg]
    · rw [show (single ⟨m + 1, w⟩ 1 : LC V) = lsim w from rfl, cone_lsim, ld_lsim_succ,
        Fin.sum_univ_succ, aug_lsim, ld_lsim_succ, map_sum]
      simp only [Fin.val_zero, pow_zero, one_smul, Fin.val_succ, Fin.succAbove_zero,
        Nat.succ_ne_zero, ↓reduceIte, zero_smul,
        sub_zero, map_zsmul, cone_lsim, cons_comp_succAbove_succ, pow_succ, mul_neg, mul_one,
        neg_smul, Finset.sum_neg_distrib]
      rw [show (Fin.cons b w : Fin (m + 3) → V) ∘ Fin.succ = w from rfl]
      abel
  have := linearMap_congr_support ((LG V).d ∘ₗ cone b)
    (LinearMap.id - cone b ∘ₗ (LG V).d - (LinearMap.smulRight (LG V).aug (pt b))) (x := x)
    (fun s _ => by simpa using key s)
  simpa using this

/-! ## Barycentres -/

/-- The barycentre of a vertex tuple. -/
def bary {m : ℕ} (w : Fin (m + 1) → V) : V := ((m : ℝ) + 1)⁻¹ • ∑ j, w j

theorem map_bary {W : Type} [AddCommGroup W] [Module ℝ W] (L : V →ₗ[ℝ] W) {m : ℕ}
    (w : Fin (m + 1) → V) : L (bary w) = bary (L ∘ w) := by
  simp [bary, map_sum]

/-! ## Barycentric subdivision -/

/-- Barycentric subdivision of one linear simplex. -/
def sdS : (m : ℕ) → (Fin (m + 1) → V) → LC V
  | 0, w => lsim w
  | m + 1, w => cone (bary w)
      (∑ i : Fin (m + 2), ((-1 : ℤ) ^ (i : ℕ)) • sdS m (w ∘ Fin.succAbove i))

/-- **Barycentric subdivision** of linear chains. -/
def Sd : LC V →ₗ[ℤ] LC V := linearCombination ℤ (fun s : (LG V).β => sdS s.1 s.2)

theorem Sd_lsim {m : ℕ} (w : Fin (m + 1) → V) : Sd (lsim w) = sdS m w := by
  unfold Sd lsim
  rw [linearCombination_single, one_smul]

theorem Sd_ld_lsim {m : ℕ} (w : Fin (m + 2) → V) :
    Sd ((LG V).d (lsim w)) = ∑ i : Fin (m + 2), ((-1 : ℤ) ^ (i : ℕ)) • sdS m (w ∘ Fin.succAbove i) := by
  rw [ld_lsim_succ, map_sum]
  simp only [map_zsmul, Sd_lsim]

theorem sdS_zero (w : Fin 1 → V) : sdS 0 w = lsim w := rfl

theorem sdS_succ {m : ℕ} (w : Fin (m + 2) → V) :
    sdS (m + 1) w = cone (bary w) (Sd ((LG V).d (lsim w))) := by
  rw [Sd_ld_lsim]; rfl

theorem sdS_mem_homog : ∀ (m : ℕ) (w : Fin (m + 1) → V), sdS m w ∈ (LG V).homog m
  | 0, w => lsim_mem_homog w
  | m + 1, w => by
    rw [sdS_succ, Sd_ld_lsim]
    exact cone_mem_homog _ (Submodule.sum_mem _ fun i _ =>
      Submodule.smul_mem _ _ (sdS_mem_homog m _))

theorem Sd_mem_homog {m : ℕ} {x : LC V} (hx : x ∈ (LG V).homog m) : Sd x ∈ (LG V).homog m := by
  unfold Sd
  refine lc_mem fun s hs => ?_
  have : s.1 = m := (mem_supported ℤ _).mp hx hs
  rw [← this]
  exact sdS_mem_homog _ _

theorem aug_sdS : ∀ (m : ℕ) (w : Fin (m + 1) → V), (LG V).aug (sdS m w) = (LG V).aug (lsim w)
  | 0, _ => rfl
  | m + 1, w => by
    rw [GC.aug_homog_succ (sdS_mem_homog _ _), GC.aug_homog_succ (lsim_mem_homog w)]

theorem aug_Sd (x : LC V) : (LG V).aug (Sd x) = (LG V).aug x := by
  have := linearMap_congr_support ((LG V).aug ∘ₗ Sd) (LG V).aug (x := x) (fun s _ => by
    obtain ⟨m, w⟩ := s
    change (LG V).aug (Sd (lsim w)) = (LG V).aug (lsim w)
    rw [Sd_lsim]; exact aug_sdS m w)
  simpa using this

/-- `Sd` commutes with the boundary on simplices. -/
theorem ld_sdS : ∀ (m : ℕ) (w : Fin (m + 1) → V), (LG V).d (sdS m w) = Sd ((LG V).d (lsim w))
  | 0, w => by rw [sdS_zero, ld_lsim_zero, map_zero]
  | m + 1, w => by
    rw [sdS_succ, ld_cone]
    have h1 : (LG V).d (Sd ((LG V).d (lsim w))) = 0 := by
      have := ext_homog ((LG V).d ∘ₗ Sd) (Sd ∘ₗ (LG V).d) (m := m)
        (fun w' => by
          change (LG V).d (Sd (lsim w')) = Sd ((LG V).d (lsim w'))
          rw [Sd_lsim]; exact ld_sdS m w')
        (GC.d_mem_homog (lsim_mem_homog w))
      simp only [LinearMap.coe_comp, Function.comp_apply] at this
      rw [this, (LG V).dd, map_zero]
    rw [h1, map_zero, aug_Sd, GC.aug_comp_d, zero_smul, sub_zero, sub_zero]

/-- **`Sd` is a chain map.** -/
theorem ld_Sd (x : LC V) : (LG V).d (Sd x) = Sd ((LG V).d x) := by
  have := linearMap_congr_support ((LG V).d ∘ₗ Sd) (Sd ∘ₗ (LG V).d) (x := x) (fun s _ => by
    obtain ⟨m, w⟩ := s
    change (LG V).d (Sd (lsim w)) = Sd ((LG V).d (lsim w))
    rw [Sd_lsim]; exact ld_sdS m w)
  simpa using this

/-! ## The chain homotopy `T` -/

/-- The homotopy operator on one linear simplex. -/
def tS : (m : ℕ) → (Fin (m + 1) → V) → LC V
  | 0, _ => 0
  | m + 1, w => cone (bary w)
      (lsim w - ∑ i : Fin (m + 2), ((-1 : ℤ) ^ (i : ℕ)) • tS m (w ∘ Fin.succAbove i))

/-- **The chain homotopy** `T` between `id` and `Sd`. -/
def Tl : LC V →ₗ[ℤ] LC V := linearCombination ℤ (fun s : (LG V).β => tS s.1 s.2)

theorem Tl_lsim {m : ℕ} (w : Fin (m + 1) → V) : Tl (lsim w) = tS m w := by
  unfold Tl lsim
  rw [linearCombination_single, one_smul]

theorem tS_succ {m : ℕ} (w : Fin (m + 2) → V) :
    tS (m + 1) w = cone (bary w) (lsim w - Tl ((LG V).d (lsim w))) := by
  rw [ld_lsim_succ, map_sum]
  simp only [map_zsmul, Tl_lsim]
  rfl

theorem tS_mem_homog : ∀ (m : ℕ) (w : Fin (m + 1) → V), tS m w ∈ (LG V).homog (m + 1)
  | 0, _ => Submodule.zero_mem _
  | m + 1, w => by
    rw [tS_succ, ld_lsim_succ, map_sum]
    simp only [map_zsmul, Tl_lsim]
    exact cone_mem_homog _ (Submodule.sub_mem _ (lsim_mem_homog w)
      (Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (tS_mem_homog m _)))

theorem Tl_mem_homog {m : ℕ} {x : LC V} (hx : x ∈ (LG V).homog m) :
    Tl x ∈ (LG V).homog (m + 1) := by
  unfold Tl
  refine lc_mem fun s hs => ?_
  have : s.1 = m := (mem_supported ℤ _).mp hx hs
  rw [← this]
  exact tS_mem_homog _ _

theorem ld_tS : ∀ (m : ℕ) (w : Fin (m + 1) → V),
    (LG V).d (tS m w) + Tl ((LG V).d (lsim w)) = lsim w - sdS m w
  | 0, w => by
    rw [show tS 0 w = 0 from rfl, show sdS 0 w = lsim w from rfl, ld_lsim_zero (V := V) w,
      map_zero, map_zero, zero_add, sub_self]
  | m + 1, w => by
    rw [tS_succ, ld_cone]
    have hz : (LG V).aug (lsim w - Tl ((LG V).d (lsim w))) = 0 :=
      GC.aug_homog_succ (Submodule.sub_mem _ (lsim_mem_homog w)
        (Tl_mem_homog (GC.d_mem_homog (lsim_mem_homog w))))
    have hT : (LG V).d (Tl ((LG V).d (lsim w))) =
        (LG V).d (lsim w) - Sd ((LG V).d (lsim w)) := by
      have := ext_homog ((LG V).d ∘ₗ Tl + Tl ∘ₗ (LG V).d) (LinearMap.id - Sd) (m := m)
        (fun w' => by
          change (LG V).d (Tl (lsim w')) + Tl ((LG V).d (lsim w')) = lsim w' - Sd (lsim w')
          rw [Tl_lsim, Sd_lsim]; exact ld_tS m w')
        (GC.d_mem_homog (lsim_mem_homog w))
      simp only [LinearMap.add_apply, LinearMap.coe_comp, Function.comp_apply, (LG V).dd,
        map_zero, add_zero, LinearMap.sub_apply, LinearMap.id_coe, id_eq] at this
      exact this
    rw [hz, zero_smul, sub_zero, map_sub, hT, sub_sub_cancel, sdS_succ]
    abel

/-- **The homotopy formula** `∂T + T∂ = id - Sd`. -/
theorem ld_Tl (x : LC V) : (LG V).d (Tl x) + Tl ((LG V).d x) = x - Sd x := by
  have := linearMap_congr_support ((LG V).d ∘ₗ Tl + Tl ∘ₗ (LG V).d) (LinearMap.id - Sd)
    (x := x) (fun s _ => by
      obtain ⟨m, w⟩ := s
      change (LG V).d (Tl (lsim w)) + Tl ((LG V).d (lsim w)) = lsim w - Sd (lsim w)
      rw [Tl_lsim, Sd_lsim]; exact ld_tS m w)
  simpa using this

/-! ## Naturality under linear maps -/

section Natural

variable {W : Type} [AddCommGroup W] [Module ℝ W]

/-- The map of linear chains induced by a linear map `V → W`. -/
def lmap (L : V →ₗ[ℝ] W) : LC V →ₗ[ℤ] LC W :=
  Finsupp.lmapDomain ℤ ℤ (fun s : (LG V).β => (⟨s.1, L ∘ s.2⟩ : (LG W).β))

theorem lmap_lsim (L : V →ₗ[ℝ] W) {m : ℕ} (w : Fin (m + 1) → V) :
    lmap L (lsim w) = lsim (L ∘ w) := by
  unfold lmap lsim
  rw [Finsupp.lmapDomain_apply, Finsupp.mapDomain_single]

theorem lmap_ld (L : V →ₗ[ℝ] W) (x : LC V) : lmap L ((LG V).d x) = (LG W).d (lmap L x) := by
  have := linearMap_congr_support (lmap L ∘ₗ (LG V).d) ((LG W).d ∘ₗ lmap L) (x := x)
    (fun s _ => by
      obtain ⟨m, w⟩ := s
      rcases m with _ | m
      · simp only [LinearMap.coe_comp, Function.comp_apply]
        rw [show (single ⟨0, w⟩ 1 : LC V) = lsim w from rfl, lmap_lsim, ld_lsim_zero,
          ld_lsim_zero, map_zero]
      · simp only [LinearMap.coe_comp, Function.comp_apply]
        rw [show (single ⟨m + 1, w⟩ 1 : LC V) = lsim w from rfl, lmap_lsim, ld_lsim_succ,
          ld_lsim_succ, map_sum]
        simp only [map_zsmul, lmap_lsim]
        rfl)
  simpa using this

theorem lmap_cone (L : V →ₗ[ℝ] W) (b : V) (x : LC V) :
    lmap L (cone b x) = cone (L b) (lmap L x) := by
  have := linearMap_congr_support (lmap L ∘ₗ cone b) (cone (L b) ∘ₗ lmap L) (x := x)
    (fun s _ => by
      obtain ⟨m, w⟩ := s
      simp only [LinearMap.coe_comp, Function.comp_apply]
      rw [show (single ⟨m, w⟩ 1 : LC V) = lsim w from rfl, cone_lsim, lmap_lsim, lmap_lsim,
        cone_lsim, Fin.comp_cons])
  simpa using this

theorem lmap_sdS (L : V →ₗ[ℝ] W) : ∀ (m : ℕ) (w : Fin (m + 1) → V),
    lmap L (sdS m w) = sdS m (L ∘ w)
  | 0, w => lmap_lsim L w
  | m + 1, w => by
    simp only [sdS, lmap_cone, map_sum, map_zsmul, lmap_sdS L m, map_bary]
    rfl

theorem lmap_Sd (L : V →ₗ[ℝ] W) (x : LC V) : lmap L (Sd x) = Sd (lmap L x) := by
  have := linearMap_congr_support (lmap L ∘ₗ Sd) (Sd ∘ₗ lmap L) (x := x) (fun s _ => by
    obtain ⟨m, w⟩ := s
    simp only [LinearMap.coe_comp, Function.comp_apply]
    rw [show (single ⟨m, w⟩ 1 : LC V) = lsim w from rfl, Sd_lsim, lmap_lsim, Sd_lsim,
      lmap_sdS])
  simpa using this

theorem lmap_tS (L : V →ₗ[ℝ] W) : ∀ (m : ℕ) (w : Fin (m + 1) → V),
    lmap L (tS m w) = tS m (L ∘ w)
  | 0, _ => map_zero _
  | m + 1, w => by
    simp only [tS, lmap_cone, map_sub, map_sum, map_zsmul, lmap_tS L m, map_bary, lmap_lsim]
    rfl

theorem lmap_Tl (L : V →ₗ[ℝ] W) (x : LC V) : lmap L (Tl x) = Tl (lmap L x) := by
  have := linearMap_congr_support (lmap L ∘ₗ Tl) (Tl ∘ₗ lmap L) (x := x) (fun s _ => by
    obtain ⟨m, w⟩ := s
    simp only [LinearMap.coe_comp, Function.comp_apply]
    rw [show (single ⟨m, w⟩ 1 : LC V) = lsim w from rfl, Tl_lsim, lmap_lsim, Tl_lsim,
      lmap_tS])
  simpa using this

end Natural

end

end QE.Excision
