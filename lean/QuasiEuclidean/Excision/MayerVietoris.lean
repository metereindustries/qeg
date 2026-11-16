-- SPDX-License-Identifier: MIT
-- Copyright 2026 Metere Industries, Inc. Author: Alfredo Metere.
-- Quasi-Euclidean Granular Geometry. Any derivative work must carry this notice:
--   This work is derivative of the Quasi-Euclidean Granular Geometry book
--   authored by Alfredo Metere. Copyright 2026 Metere Industries, Inc.
--   All rights reserved
-- See LICENSE.md and NOTICE.

import QuasiEuclidean.Excision.Subdivision

/-!
# The Mayer–Vietoris sequence of singular homology

Book: Proposition `prop:topology-homology-singular` (Chapter 10), infrastructure.

Let `A, B ⊆ E` with `Y = A ∪ B` covered by the interiors of `A` and `B` relative to `Y`,
given as open sets `O_A, O_B` of `E` with `Y ∩ O_A ⊆ A`, `Y ∩ O_B ⊆ B`, `Y ⊆ O_A ∪ O_B`
(`MVCover`).  With `i(c) = (c, -c)`, `j(a, b) = a + b` and the connecting map
`δ [z] = [∂ z_A]` (for a `{O_A, O_B}`-small representative `z = z_A + z_B`, split by
whether a simplex lies in `A`), the sequence

`⋯ → H_{k+1}(Y) --δ--> H_k(A ∩ B) --i--> H_k(A) × H_k(B) --j--> H_k(Y) --δ--> ⋯`

is exact at every term (`mv_exact_AB`, `mv_exact_Y`, `mv_exact_AcapB`).  The connecting map
is defined through the small-simplices theorem (`smallEquiv`).

This sequence is not needed for the comparison of cubical with singular homology, which is
proved by acyclic carriers; it is provided as part of the singular-homology infrastructure.
No measure theory is used.
-/

namespace QE.Excision

open Finsupp

noncomputable section

variable {E : Type} [TopologicalSpace E]

/-- `A ∪ B` is the union of the interiors of `A` and `B` relative to `A ∪ B`, witnessed by
open sets of the ambient space. -/
structure MVCover (A B : Set E) where
  /-- An open set whose trace on `A ∪ B` lies in `A`. -/
  OA : Set E
  /-- An open set whose trace on `A ∪ B` lies in `B`. -/
  OB : Set E
  isOpen_OA : IsOpen OA
  isOpen_OB : IsOpen OB
  sub_A : (A ∪ B) ∩ OA ⊆ A
  sub_B : (A ∪ B) ∩ OB ⊆ B
  cover : A ∪ B ⊆ OA ∪ OB

namespace MVCover

variable {A B : Set E} (M : MVCover A B)

/-- The open cover `{O_A, O_B}`. -/
def U : Set (Set E) := {M.OA, M.OB}

theorem isOpen_U : ∀ V ∈ M.U, IsOpen V := by
  rintro V (rfl | rfl)
  exacts [M.isOpen_OA, M.isOpen_OB]

theorem cover_U : A ∪ B ⊆ ⋃₀ M.U := fun x hx => by
  rcases M.cover hx with h | h
  exacts [⟨M.OA, Or.inl rfl, h⟩, ⟨M.OB, Or.inr rfl, h⟩]

end MVCover

theorem SA_inter (A B : Set E) : SA (A ∩ B) = SA A ∩ SA B := by
  ext s; simp [SA, Set.subset_inter_iff]

theorem mem_supported_inter {A B : Set E} {x : SC E} (hA : x ∈ supported ℤ ℤ (SA A))
    (hB : x ∈ supported ℤ ℤ (SA B)) : x ∈ supported ℤ ℤ (SA (A ∩ B)) := by
  rw [SA_inter, supported_inter]; exact Submodule.mem_inf.mpr ⟨hA, hB⟩

/-! ## Splitting a small chain -/

section Split

variable (A : Set E)

open Classical in
/-- The part of a chain consisting of the simplices that lie in `A`. -/
def fA : SC E →ₗ[ℤ] SC E where
  toFun x := x.filter (· ∈ SA A)
  map_add' x y := by ext s; simp only [filter_apply, coe_add, Pi.add_apply]; split_ifs <;> simp
  map_smul' c x := by
    ext s; simp only [filter_apply, coe_smul, Pi.smul_apply, RingHom.id_apply]; split_ifs <;> simp

open Classical in
theorem fA_apply (x : SC E) (s : (SG E).β) : fA A x s = if s ∈ SA A then x s else 0 := rfl

variable {A}

theorem fA_mem (x : SC E) : fA A x ∈ supported ℤ ℤ (SA A) := by
  intro s hs
  rw [Finset.mem_coe, mem_support_iff, fA_apply] at hs
  by_contra h; exact hs (by simp [h])

theorem fA_mem_of {P : Set (SG E).β} {x : SC E} (hx : x ∈ supported ℤ ℤ P) :
    fA A x ∈ supported ℤ ℤ P := by
  intro s hs
  rw [Finset.mem_coe, mem_support_iff, fA_apply] at hs
  by_cases h : s ∈ SA A
  · rw [ite_eq_left h] at hs; exact hx (mem_support_iff.mpr hs)
  · exact absurd (by simp [h]) hs

theorem fA_eq_self {x : SC E} (hx : x ∈ supported ℤ ℤ (SA A)) : fA A x = x := by
  ext s
  rw [fA_apply]
  split_ifs with h
  · rfl
  · by_contra hne
    exact h (hx (mem_support_iff.mpr (Ne.symm hne)))

theorem fA_homog {k : ℕ} {x : SC E} (hx : x ∈ (SG E).homog k) : fA A x ∈ (SG E).homog k :=
  fA_mem_of hx

theorem sub_fA_mem {B : Set E} (M : MVCover A B) {x : SC E}
    (hx : x ∈ supported ℤ ℤ (SA (A ∪ B) ∩ Small M.U)) : x - fA A x ∈ supported ℤ ℤ (SA B) := by
  intro s hs
  rw [Finset.mem_coe, mem_support_iff, coe_sub, Pi.sub_apply, fA_apply] at hs
  by_cases h : s ∈ SA A
  · rw [ite_eq_left h, sub_self] at hs; exact absurd rfl hs
  · rw [ite_eq_right h, sub_zero] at hs
    obtain ⟨hY, V, hV, hsV⟩ := hx (mem_support_iff.mpr hs)
    rcases hV with rfl | rfl
    · exact absurd (fun y hy => M.sub_A ⟨hY hy, hsV hy⟩) h
    · exact fun y hy => M.sub_B ⟨hY hy, hsV hy⟩

end Split

/-! ## The maps -/

section Maps

variable {A B : Set E}

theorem SA_inter_left : SA (A ∩ B) ⊆ SA A := SA_mono Set.inter_subset_left
theorem SA_inter_right : SA (A ∩ B) ⊆ SA B := SA_mono Set.inter_subset_right
theorem SA_left : SA A ⊆ SA (A ∪ B) := SA_mono Set.subset_union_left
theorem SA_right : SA B ⊆ SA (A ∪ B) := SA_mono Set.subset_union_right

/-- The map induced by an inclusion of subcomplexes. -/
def incl {P Q : Set (SG E).β} (h : P ⊆ Q) (k : ℕ) : (SG E).H P k →ₗ[ℤ] (SG E).H Q k :=
  HQ.map LinearMap.id (GC.Z_mono h k) (GC.B_mono h k)

theorem incl_mk {P Q : Set (SG E).β} (h : P ⊆ Q) (k : ℕ) (z : (SG E).Z P k) :
    incl h k (Submodule.Quotient.mk z) = Submodule.Quotient.mk ⟨z, GC.Z_mono h k z.2⟩ := rfl

variable (A B)

/-- `i(c) = (c, -c)`. -/
def mvI (k : ℕ) : (SG E).H (SA (A ∩ B)) k →ₗ[ℤ] (SG E).H (SA A) k × (SG E).H (SA B) k :=
  LinearMap.prod (incl SA_inter_left k) (-incl SA_inter_right k)

/-- `j(a, b) = a + b`. -/
def mvJ (k : ℕ) : (SG E).H (SA A) k × (SG E).H (SA B) k →ₗ[ℤ] (SG E).H (SA (A ∪ B)) k :=
  LinearMap.coprod (incl SA_left k) (incl SA_right k)

variable {A B} (M : MVCover A B)

theorem d_fA_mem {k : ℕ} {z : SC E} (hz : z ∈ (SG E).Z (SA (A ∪ B) ∩ Small M.U) (k + 1)) :
    (SG E).d (fA A z) ∈ (SG E).Z (SA (A ∩ B)) k := by
  obtain ⟨hzC, hzd⟩ := Submodule.mem_inf.mp hz
  have hzd' : (SG E).d z = 0 := hzd
  obtain ⟨hzS, hzH⟩ := GC.mem_Ch.mp hzC
  have h1 : (SG E).d (fA A z) ∈ supported ℤ ℤ (SA A) :=
    GC.d_mem_supported (SA_closed A) (fA_mem z)
  have h2 : (SG E).d (fA A z) ∈ supported ℤ ℤ (SA B) := by
    have : (SG E).d (fA A z) = -(SG E).d (z - fA A z) := by rw [map_sub, hzd']; abel
    rw [this]
    exact Submodule.neg_mem _ (GC.d_mem_supported (SA_closed B) (sub_fA_mem M hzS))
  refine Submodule.mem_inf.mpr ⟨GC.mem_Ch.mpr ⟨mem_supported_inter h1 h2,
    GC.d_mem_homog (fA_homog hzH)⟩, ?_⟩
  show (SG E).d ((SG E).d _) = 0
  exact (SG E).dd _

theorem d_fA_B {k : ℕ} {z : SC E} (hz : z ∈ (SG E).B (SA (A ∪ B) ∩ Small M.U) (k + 1)) :
    (SG E).d (fA A z) ∈ (SG E).B (SA (A ∩ B)) k := by
  obtain ⟨u, huC, rfl⟩ := hz
  obtain ⟨huS, huH⟩ := GC.mem_Ch.mp huC
  have hdu : (SG E).d u ∈ supported ℤ ℤ (SA (A ∪ B) ∩ Small M.U) :=
    GC.d_mem_supported (closed_of_hered (hered_inter (hered_SA _) (hered_Small _))) huS
  -- `c = fA(∂u) - ∂(fA u)` lies in `A` and in `B`
  set c := fA A ((SG E).d u) - (SG E).d (fA A u) with hc
  have hcA : c ∈ supported ℤ ℤ (SA A) :=
    Submodule.sub_mem _ (fA_mem _) (GC.d_mem_supported (SA_closed A) (fA_mem u))
  have hcB : c ∈ supported ℤ ℤ (SA B) := by
    have : c = (SG E).d (u - fA A u) - ((SG E).d u - fA A ((SG E).d u)) := by
      rw [hc, map_sub]; abel
    rw [this]
    exact Submodule.sub_mem _ (GC.d_mem_supported (SA_closed B) (sub_fA_mem M huS))
      (sub_fA_mem M hdu)
  refine ⟨c, GC.mem_Ch.mpr ⟨mem_supported_inter hcA hcB, Submodule.sub_mem _
    (fA_homog (GC.d_mem_homog huH)) (GC.d_mem_homog (fA_homog huH))⟩, ?_⟩
  rw [hc, map_sub, (SG E).dd, sub_zero]

/-- The connecting map on small cycles. -/
def mvDs (k : ℕ) :
    (SG E).H (SA (A ∪ B) ∩ Small M.U) (k + 1) →ₗ[ℤ] (SG E).H (SA (A ∩ B)) k :=
  HQ.map ((SG E).d ∘ₗ fA A) (fun _ hz => d_fA_mem M hz) (fun _ hz => d_fA_B M hz)

/-- **The connecting map** `δ : H_{k+1}(A ∪ B) → H_k(A ∩ B)`. -/
def mvD (k : ℕ) : (SG E).H (SA (A ∪ B)) (k + 1) →ₗ[ℤ] (SG E).H (SA (A ∩ B)) k :=
  mvDs M k ∘ₗ (smallEquiv M.isOpen_U M.cover_U (k + 1)).symm.toLinearMap

end Maps

/-! ## Exactness -/

section Exact

variable {A B : Set E} (M : MVCover A B)

theorem mk_eq_mk_iff {P : Set (SG E).β} {k : ℕ} (z₁ z₂ : (SG E).Z P k) :
    (Submodule.Quotient.mk z₁ : (SG E).H P k) = Submodule.Quotient.mk z₂ ↔
      (z₁ : SC E) - z₂ ∈ (SG E).B P k := by
  rw [Submodule.Quotient.eq]; rfl

theorem mk_eq_zero_iff {P : Set (SG E).β} {k : ℕ} (z : (SG E).Z P k) :
    (Submodule.Quotient.mk z : (SG E).H P k) = 0 ↔ (z : SC E) ∈ (SG E).B P k := by
  rw [Submodule.Quotient.mk_eq_zero]; rfl

theorem small_pow_mono' {𝒰 : Set (Set E)} {x : SC E} {q q' : ℕ} (h : q ≤ q')
    (hx : (sSd ^ q) x ∈ supported ℤ ℤ (Small 𝒰)) : (sSd ^ q') x ∈ supported ℤ ℤ (Small 𝒰) := by
  obtain ⟨r, rfl⟩ := Nat.exists_eq_add_of_le' h
  rw [pow_add, Module.End.mul_apply]
  exact sSd_pow_mem_hered (hered_Small _) hx r

theorem exists_small_two {Y : Set E} {𝒰 : Set (Set E)} (hU : ∀ V ∈ 𝒰, IsOpen V)
    (hcov : Y ⊆ ⋃₀ 𝒰) {x y : SC E} (hx : x ∈ supported ℤ ℤ (SA Y))
    (hy : y ∈ supported ℤ ℤ (SA Y)) :
    ∃ m, (sSd ^ m) x ∈ supported ℤ ℤ (Small 𝒰) ∧ (sSd ^ m) y ∈ supported ℤ ℤ (Small 𝒰) := by
  obtain ⟨q₁, h₁⟩ := exists_small_chain hU hcov hx
  obtain ⟨q₂, h₂⟩ := exists_small_chain hU hcov hy
  exact ⟨max q₁ q₂, small_pow_mono' (le_max_left _ _) h₁, small_pow_mono' (le_max_right _ _) h₂⟩

theorem sSd_pow_Z {P : Set (SG E).β} (hP : Hered P) {k : ℕ} {z : SC E}
    (hz : z ∈ (SG E).Z P k) (m : ℕ) : (sSd ^ m) z ∈ (SG E).Z P k := by
  obtain ⟨hzC, hzd⟩ := Submodule.mem_inf.mp hz
  obtain ⟨hzS, hzH⟩ := GC.mem_Ch.mp hzC
  refine Submodule.mem_inf.mpr ⟨GC.mem_Ch.mpr ⟨sSd_pow_mem_hered hP hzS m,
    sSd_pow_mem_homog hzH m⟩, ?_⟩
  show (SG E).d _ = 0
  rw [sd_sSd_pow]; rw [show (SG E).d z = 0 from hzd, map_zero]

/-- Subdivision does not change homology classes. -/
theorem subdiv_homologous {P : Set (SG E).β} (hP : Hered P) {k : ℕ} {z : SC E}
    (hz : z ∈ (SG E).Z P k) (m : ℕ) : z - (sSd ^ m) z ∈ (SG E).B P k := by
  obtain ⟨hzC, hzd⟩ := Submodule.mem_inf.mp hz
  obtain ⟨hzS, hzH⟩ := GC.mem_Ch.mp hzC
  have h := sd_sD m z
  rw [show (SG E).d z = 0 from hzd, map_zero, add_zero] at h
  exact ⟨sD m z, GC.mem_Ch.mpr ⟨sD_mem_hered hP hzS m, sD_mem_homog hzH m⟩, h⟩

theorem hered_SAY_small : Hered (SA (A ∪ B) ∩ Small M.U) :=
  hered_inter (hered_SA _) (hered_Small _)

/-- Computing `δ` from any small representative. -/
theorem mvD_eq {k : ℕ} {z z' : SC E} (hz : z ∈ (SG E).Z (SA (A ∪ B)) (k + 1))
    (hz' : z' ∈ (SG E).Z (SA (A ∪ B) ∩ Small M.U) (k + 1))
    (h : z - z' ∈ (SG E).B (SA (A ∪ B)) (k + 1)) :
    mvD M k (Submodule.Quotient.mk ⟨z, hz⟩) =
      Submodule.Quotient.mk ⟨(SG E).d (fA A z'), d_fA_mem M hz'⟩ := by
  have e : (smallEquiv M.isOpen_U M.cover_U (k + 1)).symm (Submodule.Quotient.mk ⟨z, hz⟩) =
      Submodule.Quotient.mk ⟨z', hz'⟩ := by
    rw [LinearEquiv.symm_apply_eq]
    show _ = Submodule.Quotient.mk _
    rw [mk_eq_mk_iff]; exact h
  simp only [mvD, LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply, e]
  rfl

include M in
/-- **Mayer–Vietoris, exactness at `H_k(A) × H_k(B)`.** -/
theorem mv_exact_AB (k : ℕ) : LinearMap.range (mvI A B k) = LinearMap.ker (mvJ A B k) := by
  ext ⟨qa, qb⟩
  constructor
  · rintro ⟨q, hq⟩
    rw [← hq]
    induction q using Submodule.Quotient.induction_on with
    | H c =>
      rw [LinearMap.mem_ker]
      show incl SA_left k (incl SA_inter_left k (Submodule.Quotient.mk c)) +
        incl SA_right k (-incl SA_inter_right k (Submodule.Quotient.mk c)) = 0
      rw [map_neg, incl_mk, incl_mk, incl_mk, incl_mk, add_neg_eq_zero]
  · intro hq
    rw [LinearMap.mem_ker] at hq
    induction qa using Submodule.Quotient.induction_on with
    | H a =>
    induction qb using Submodule.Quotient.induction_on with
    | H b =>
    simp only [mvJ, LinearMap.coprod_apply] at hq
    erw [incl_mk, incl_mk, ← Submodule.Quotient.mk_add, mk_eq_zero_iff] at hq
    obtain ⟨w, hwC, hw⟩ := hq
    obtain ⟨hwS, hwH⟩ := GC.mem_Ch.mp hwC
    obtain ⟨haC, had⟩ := Submodule.mem_inf.mp a.2
    obtain ⟨hbC, hbd⟩ := Submodule.mem_inf.mp b.2
    obtain ⟨m, hm, -⟩ := exists_small_two M.isOpen_U M.cover_U hwS hwS
    set w' := (sSd ^ m) w
    have hw'S : w' ∈ supported ℤ ℤ (SA (A ∪ B) ∩ Small M.U) := by
      rw [supported_inter]
      exact Submodule.mem_inf.mpr ⟨sSd_pow_mem_hered (hered_SA _) hwS m, hm⟩
    have hw'H : w' ∈ (SG E).homog (k + 1) := sSd_pow_mem_homog hwH m
    have hab : (sSd ^ m) (a : SC E) + (sSd ^ m) (b : SC E) = (SG E).d w' := by
      rw [← map_add, show (SG E).d w' = (sSd ^ m) ((SG E).d w) from sd_sSd_pow m w, hw]; rfl
    set c := (sSd ^ m) (a : SC E) - (SG E).d (fA A w') with hc
    have haS := (GC.mem_Ch.mp haC).1
    have hbS := (GC.mem_Ch.mp hbC).1
    have hcA : c ∈ supported ℤ ℤ (SA A) := Submodule.sub_mem _
      (sSd_pow_mem_hered (hered_SA _) haS m) (GC.d_mem_supported (SA_closed A) (fA_mem w'))
    have hc' : c = -((sSd ^ m) (b : SC E) - (SG E).d (w' - fA A w')) := by
      rw [hc, map_sub, ← hab]; abel
    have hcB : c ∈ supported ℤ ℤ (SA B) := by
      rw [hc']
      exact Submodule.neg_mem _ (Submodule.sub_mem _ (sSd_pow_mem_hered (hered_SA _) hbS m)
        (GC.d_mem_supported (SA_closed B) (sub_fA_mem M hw'S)))
    have hcH : c ∈ (SG E).homog k := Submodule.sub_mem _
      (sSd_pow_mem_homog (GC.mem_Ch.mp haC).2 m) (GC.d_mem_homog (fA_homog hw'H))
    have hcd : (SG E).d c = 0 := by
      rw [hc, map_sub, (SG E).dd, sub_zero, sd_sSd_pow, show (SG E).d (a : SC E) = 0 from had,
        map_zero]
    have hcZ : c ∈ (SG E).Z (SA (A ∩ B)) k :=
      Submodule.mem_inf.mpr ⟨GC.mem_Ch.mpr ⟨mem_supported_inter hcA hcB, hcH⟩, hcd⟩
    refine ⟨Submodule.Quotient.mk ⟨c, hcZ⟩, ?_⟩
    show (incl SA_inter_left k (Submodule.Quotient.mk ⟨c, hcZ⟩),
      -incl SA_inter_right k (Submodule.Quotient.mk ⟨c, hcZ⟩)) = _
    rw [incl_mk, incl_mk, Prod.mk.injEq]
    constructor
    · rw [mk_eq_mk_iff]
      have h1 := subdiv_homologous (hered_SA A) a.2 m
      have : c - (a : SC E) = -((a : SC E) - (sSd ^ m) (a : SC E)) - (SG E).d (fA A w') := by
        rw [hc]; abel
      rw [this]
      exact Submodule.sub_mem _ (Submodule.neg_mem _ h1)
        ⟨fA A w', GC.mem_Ch.mpr ⟨fA_mem w', fA_homog hw'H⟩, rfl⟩
    · rw [← Submodule.Quotient.mk_neg, mk_eq_mk_iff]
      have h1 := subdiv_homologous (hered_SA B) b.2 m
      have : -c - (b : SC E) =
          -((b : SC E) - (sSd ^ m) (b : SC E)) - (SG E).d (w' - fA A w') := by
        rw [hc']; abel
      simp only [Submodule.coe_neg]
      rw [this]
      exact Submodule.sub_mem _ (Submodule.neg_mem _ h1)
        ⟨w' - fA A w', GC.mem_Ch.mpr ⟨sub_fA_mem M hw'S, Submodule.sub_mem _ hw'H
          (fA_homog hw'H)⟩, rfl⟩

theorem fA_inter_mem {k : ℕ} {x : SC E} (hx : x ∈ (SG E).Ch (SA B) k) :
    fA A x ∈ (SG E).Ch (SA (A ∩ B)) k := by
  obtain ⟨hxS, hxH⟩ := GC.mem_Ch.mp hx
  exact GC.mem_Ch.mpr ⟨mem_supported_inter (fA_mem x) (fA_mem_of hxS), fA_homog hxH⟩

/-- **Mayer–Vietoris, exactness at `H_{k+1}(A ∪ B)`.** -/
theorem mv_exact_Y (k : ℕ) : LinearMap.range (mvJ A B (k + 1)) = LinearMap.ker (mvD M k) := by
  ext q
  constructor
  · rintro ⟨⟨qa, qb⟩, hq⟩
    rw [← hq]
    induction qa using Submodule.Quotient.induction_on with
    | H a =>
    induction qb using Submodule.Quotient.induction_on with
    | H b =>
    rw [LinearMap.mem_ker]
    show mvD M k (incl SA_left (k + 1) (Submodule.Quotient.mk a) +
      incl SA_right (k + 1) (Submodule.Quotient.mk b)) = 0
    rw [incl_mk, incl_mk, ← Submodule.Quotient.mk_add]
    set z := (⟨a, GC.Z_mono SA_left (k + 1) a.2⟩ + ⟨b, GC.Z_mono SA_right (k + 1) b.2⟩ :
      (SG E).Z (SA (A ∪ B)) (k + 1)) with hzdef
    have hzv : (z : SC E) = a + b := rfl
    obtain ⟨haC, -⟩ := Submodule.mem_inf.mp a.2
    obtain ⟨hbC, -⟩ := Submodule.mem_inf.mp b.2
    have haS := (GC.mem_Ch.mp haC).1
    have hbS := (GC.mem_Ch.mp hbC).1
    obtain ⟨m, hma, hmb⟩ := exists_small_two M.isOpen_U M.cover_U
      (supported_mono SA_left haS) (supported_mono SA_right hbS)
    have hz'Z : (sSd ^ m) (z : SC E) ∈ (SG E).Z (SA (A ∪ B) ∩ Small M.U) (k + 1) := by
      have h := sSd_pow_Z (hered_SA _) z.2 m
      obtain ⟨hC, hd⟩ := Submodule.mem_inf.mp h
      refine Submodule.mem_inf.mpr ⟨Ch_inter_iff.mpr ⟨hC, ?_⟩, hd⟩
      rw [hzv, map_add]; exact Submodule.add_mem _ hma hmb
    rw [show (Submodule.Quotient.mk z : (SG E).H (SA (A ∪ B)) (k + 1)) =
      Submodule.Quotient.mk ⟨(z : SC E), z.2⟩ from rfl,
      mvD_eq M z.2 hz'Z (subdiv_homologous (hered_SA _) z.2 m), mk_eq_zero_iff]
    have e : (SG E).d (fA A ((sSd ^ m) (z : SC E))) =
        (SG E).d (fA A ((sSd ^ m) (b : SC E))) := by
      rw [hzv, map_add, map_add, fA_eq_self (sSd_pow_mem_hered (hered_SA _) haS m), map_add,
        sd_sSd_pow, show (SG E).d (a : SC E) = 0 from (Submodule.mem_inf.mp a.2).2, map_zero,
        zero_add]
    show (SG E).d (fA A ((sSd ^ m) (z : SC E))) ∈ _
    rw [e]
    exact ⟨_, fA_inter_mem (GC.mem_Ch.mpr ⟨sSd_pow_mem_hered (hered_SA _) hbS m,
      sSd_pow_mem_homog (GC.mem_Ch.mp hbC).2 m⟩), rfl⟩
  · intro hq
    rw [LinearMap.mem_ker] at hq
    induction q using Submodule.Quotient.induction_on with
    | H z =>
    obtain ⟨z', hz', hzz'⟩ := small_surj M.isOpen_U M.cover_U z.2
    rw [show (Submodule.Quotient.mk z : (SG E).H (SA (A ∪ B)) (k + 1)) =
      Submodule.Quotient.mk ⟨(z : SC E), z.2⟩ from rfl, mvD_eq M z.2 hz' hzz',
      mk_eq_zero_iff] at hq
    obtain ⟨e, heC, he⟩ := hq
    obtain ⟨hz'C, hz'd⟩ := Submodule.mem_inf.mp hz'
    have hz'd' : (SG E).d z' = 0 := hz'd
    obtain ⟨hz'S, hz'H⟩ := GC.mem_Ch.mp hz'C
    obtain ⟨heS, heH⟩ := GC.mem_Ch.mp heC
    have he' : (SG E).d e = (SG E).d (fA A z') := he
    have haZ : fA A z' - e ∈ (SG E).Z (SA A) (k + 1) := by
      refine Submodule.mem_inf.mpr ⟨GC.mem_Ch.mpr ⟨Submodule.sub_mem _ (fA_mem z')
        (supported_mono SA_inter_left heS), Submodule.sub_mem _ (fA_homog hz'H) heH⟩, ?_⟩
      show (SG E).d _ = 0
      rw [map_sub, he', sub_self]
    have hbZ : (z' - fA A z') + e ∈ (SG E).Z (SA B) (k + 1) := by
      refine Submodule.mem_inf.mpr ⟨GC.mem_Ch.mpr ⟨Submodule.add_mem _ (sub_fA_mem M hz'S)
        (supported_mono SA_inter_right heS), Submodule.add_mem _
        (Submodule.sub_mem _ hz'H (fA_homog hz'H)) heH⟩, ?_⟩
      show (SG E).d _ = 0
      rw [map_add, map_sub, hz'd', he']; abel
    refine ⟨(Submodule.Quotient.mk ⟨_, haZ⟩, Submodule.Quotient.mk ⟨_, hbZ⟩), ?_⟩
    show incl SA_left (k + 1) (Submodule.Quotient.mk _) +
      incl SA_right (k + 1) (Submodule.Quotient.mk _) = _
    rw [incl_mk, incl_mk, ← Submodule.Quotient.mk_add, mk_eq_mk_iff]
    have : (fA A z' - e) + ((z' - fA A z') + e) - (z : SC E) = -((z : SC E) - z') := by abel
    show (fA A z' - e) + ((z' - fA A z') + e) - (z : SC E) ∈ _
    rw [this]
    exact Submodule.neg_mem _ hzz'

/-- **Mayer–Vietoris, exactness at `H_k(A ∩ B)`.** -/
theorem mv_exact_AcapB (k : ℕ) : LinearMap.range (mvD M k) = LinearMap.ker (mvI A B k) := by
  ext q
  constructor
  · rintro ⟨q', hq⟩
    rw [← hq]
    induction q' using Submodule.Quotient.induction_on with
    | H z =>
    obtain ⟨z', hz', hzz'⟩ := small_surj M.isOpen_U M.cover_U z.2
    rw [show (Submodule.Quotient.mk z : (SG E).H (SA (A ∪ B)) (k + 1)) =
      Submodule.Quotient.mk ⟨(z : SC E), z.2⟩ from rfl, mvD_eq M z.2 hz' hzz',
      LinearMap.mem_ker]
    obtain ⟨hz'C, hz'd⟩ := Submodule.mem_inf.mp hz'
    have hz'd' : (SG E).d z' = 0 := hz'd
    obtain ⟨hz'S, hz'H⟩ := GC.mem_Ch.mp hz'C
    show (incl SA_inter_left k (Submodule.Quotient.mk _),
      -incl SA_inter_right k (Submodule.Quotient.mk _)) = (0, 0)
    rw [incl_mk, incl_mk]
    refine Prod.ext ?_ ?_
    · show Submodule.Quotient.mk _ = (0 : (SG E).H (SA A) k)
      rw [mk_eq_zero_iff]
      exact ⟨_, GC.mem_Ch.mpr ⟨fA_mem z', fA_homog hz'H⟩, rfl⟩
    · show -Submodule.Quotient.mk _ = (0 : (SG E).H (SA B) k)
      rw [neg_eq_zero, mk_eq_zero_iff]
      have : (SG E).d (fA A z') = (SG E).d (-(z' - fA A z')) := by
        rw [map_neg, map_sub, hz'd']; abel
      show (SG E).d (fA A z') ∈ _
      rw [this]
      exact ⟨_, GC.mem_Ch.mpr ⟨Submodule.neg_mem _ (sub_fA_mem M hz'S), Submodule.neg_mem _
        (Submodule.sub_mem _ hz'H (fA_homog hz'H))⟩, rfl⟩
  · intro hq
    rw [LinearMap.mem_ker] at hq
    induction q using Submodule.Quotient.induction_on with
    | H c =>
    have h1 : incl SA_inter_left k (Submodule.Quotient.mk c) = 0 := congrArg Prod.fst hq
    have h2 : -incl SA_inter_right k (Submodule.Quotient.mk c) = 0 := congrArg Prod.snd hq
    rw [neg_eq_zero] at h2
    rw [incl_mk, mk_eq_zero_iff] at h1 h2
    obtain ⟨u, huC, hu⟩ := h1
    obtain ⟨v, hvC, hv⟩ := h2
    obtain ⟨huS, huH⟩ := GC.mem_Ch.mp huC
    obtain ⟨hvS, hvH⟩ := GC.mem_Ch.mp hvC
    have hu' : (SG E).d u = c := hu
    have hv' : (SG E).d v = c := hv
    have hzZ : u - v ∈ (SG E).Z (SA (A ∪ B)) (k + 1) := by
      refine Submodule.mem_inf.mpr ⟨GC.mem_Ch.mpr ⟨Submodule.sub_mem _
        (supported_mono SA_left huS) (supported_mono SA_right hvS), Submodule.sub_mem _ huH hvH⟩,
        ?_⟩
      show (SG E).d _ = 0
      rw [map_sub, hu', hv', sub_self]
    obtain ⟨m, hmu, hmv⟩ := exists_small_two M.isOpen_U M.cover_U
      (supported_mono SA_left huS) (supported_mono SA_right hvS)
    have hz'Z : (sSd ^ m) (u - v) ∈ (SG E).Z (SA (A ∪ B) ∩ Small M.U) (k + 1) := by
      have h := sSd_pow_Z (hered_SA _) hzZ m
      obtain ⟨hC, hd⟩ := Submodule.mem_inf.mp h
      refine Submodule.mem_inf.mpr ⟨Ch_inter_iff.mpr ⟨hC, ?_⟩, hd⟩
      rw [map_sub]; exact Submodule.sub_mem _ hmu hmv
    refine ⟨Submodule.Quotient.mk ⟨u - v, hzZ⟩, ?_⟩
    rw [mvD_eq M hzZ hz'Z (subdiv_homologous (hered_SA _) hzZ m), mk_eq_mk_iff]
    have hcZ := c.2
    have hsub := subdiv_homologous (hered_SA (A ∩ B)) hcZ m
    have e : (SG E).d (fA A ((sSd ^ m) (u - v))) - (c : SC E) =
        -((c : SC E) - (sSd ^ m) (c : SC E)) - (SG E).d (fA A ((sSd ^ m) v)) := by
      rw [map_sub, map_sub, fA_eq_self (sSd_pow_mem_hered (hered_SA _) huS m), map_sub,
        sd_sSd_pow, hu']
      abel
    show (SG E).d (fA A ((sSd ^ m) (u - v))) - (c : SC E) ∈ _
    rw [e]
    exact Submodule.sub_mem _ (Submodule.neg_mem _ hsub) ⟨_, fA_inter_mem
      (GC.mem_Ch.mpr ⟨sSd_pow_mem_hered (hered_SA _) hvS m, sSd_pow_mem_homog hvH m⟩), rfl⟩

end Exact

end

end QE.Excision
