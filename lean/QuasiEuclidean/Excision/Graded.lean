-- SPDX-License-Identifier: MIT
-- Copyright 2026 Metere Industries, Inc. Author: Alfredo Metere.
-- Quasi-Euclidean Granular Geometry. Any derivative work must carry this notice:
--   This work is derivative of the Quasi-Euclidean Granular Geometry book
--   authored by Alfredo Metere. Copyright 2026 Metere Industries, Inc.
--   All rights reserved
-- See LICENSE.md and NOTICE.

import Mathlib

/-!
# Free graded chain complexes and acyclic carriers

Book: Proposition `prop:topology-homology-singular` (Chapter 10), infrastructure.

A *free graded chain complex* (`GC`) is a type `β` of basis elements with a degree
`deg : β → ℕ` and a boundary `d` on `β →₀ ℤ` of degree `-1` with `d ∘ d = 0` and
`ε ∘ d = 0`, where `ε` is the augmentation (sum of the coefficients of the degree-`0`
basis elements).  Cubical chains and singular chains are both of this form.  A subcomplex
is given by a set `S ⊆ β` of basis elements.

* `HQ Z B`: the homology quotient `Z / (B ∩ Z)`; `HQ.map` the map induced by a linear map,
  with injectivity and surjectivity criteria at the level of cycles.
* `graded_construction`: construction of a function on `β` by induction on the degree.
* `exists_chainMap`, `exists_homotopy`: the **acyclic carrier theorem**.  If every basis
  element `b` of a subcomplex `S` is assigned an acyclic set `Φ b` of basis elements of a
  second complex, monotone along the boundary, then there is an augmentation-preserving
  chain map carried by `Φ`, and any two such chain maps are chain homotopic through a
  homotopy carried by `Φ`.
* `sum_succAbove_succAbove`: the sign cancellation behind `∂ ∘ ∂ = 0` for simplicial
  boundaries.

No measure theory is used.
-/

namespace QE.Excision

open Finsupp

noncomputable section

/-! ## The homology quotient and induced maps -/

section HQ

variable {M N : Type*} [AddCommGroup M] [AddCommGroup N]

/-- The homology quotient `Z / (B ∩ Z)` of two submodules (cycles and boundaries). -/
abbrev HQ (Z B : Submodule ℤ M) : Type _ := Z ⧸ B.comap Z.subtype

/-- The map induced on homology quotients by a linear map preserving cycles and
boundaries. -/
noncomputable def HQ.map {Z B : Submodule ℤ M} {Z' B' : Submodule ℤ N} (F : M →ₗ[ℤ] N)
    (hZ : Z ≤ Z'.comap F) (hB : B ≤ B'.comap F) : HQ Z B →ₗ[ℤ] HQ Z' B' :=
  Submodule.mapQ _ _ (F.restrict hZ) (fun x hx => by
    simp only [Submodule.mem_comap, Submodule.coe_subtype, LinearMap.coe_restrict_apply] at hx ⊢
    exact hB hx)

theorem HQ.map_mk {Z B : Submodule ℤ M} {Z' B' : Submodule ℤ N} (F : M →ₗ[ℤ] N)
    (hZ : Z ≤ Z'.comap F) (hB : B ≤ B'.comap F) (z : Z) :
    HQ.map F hZ hB (Submodule.Quotient.mk z) = Submodule.Quotient.mk ⟨F z, hZ z.2⟩ := rfl

theorem HQ.map_surjective {Z B : Submodule ℤ M} {Z' B' : Submodule ℤ N} (F : M →ₗ[ℤ] N)
    (hZ : Z ≤ Z'.comap F) (hB : B ≤ B'.comap F)
    (h : ∀ z' ∈ Z', ∃ z ∈ Z, z' - F z ∈ B') : Function.Surjective (HQ.map F hZ hB) := by
  intro q
  induction q using Submodule.Quotient.induction_on with
  | H z' =>
    obtain ⟨z, hz, hzz⟩ := h z'.1 z'.2
    refine ⟨Submodule.Quotient.mk ⟨z, hz⟩, ?_⟩
    rw [HQ.map_mk, Submodule.Quotient.eq]
    simp only [Submodule.mem_comap, Submodule.coe_subtype, AddSubgroupClass.coe_sub]
    have := B'.neg_mem hzz
    simpa using this

theorem HQ.map_injective {Z B : Submodule ℤ M} {Z' B' : Submodule ℤ N} (F : M →ₗ[ℤ] N)
    (hZ : Z ≤ Z'.comap F) (hB : B ≤ B'.comap F)
    (h : ∀ z ∈ Z, F z ∈ B' → z ∈ B) : Function.Injective (HQ.map F hZ hB) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro q hq
  induction q using Submodule.Quotient.induction_on with
  | H z =>
    rw [HQ.map_mk, Submodule.Quotient.mk_eq_zero] at hq
    rw [Submodule.Quotient.mk_eq_zero]
    exact h z.1 z.2 hq

/-- A bijective induced map gives a linear equivalence of homology quotients. -/
noncomputable def HQ.equiv {Z B : Submodule ℤ M} {Z' B' : Submodule ℤ N} (F : M →ₗ[ℤ] N)
    (hZ : Z ≤ Z'.comap F) (hB : B ≤ B'.comap F)
    (hs : ∀ z' ∈ Z', ∃ z ∈ Z, z' - F z ∈ B') (hi : ∀ z ∈ Z, F z ∈ B' → z ∈ B) :
    HQ Z B ≃ₗ[ℤ] HQ Z' B' :=
  LinearEquiv.ofBijective (HQ.map F hZ hB)
    ⟨HQ.map_injective F hZ hB hi, HQ.map_surjective F hZ hB hs⟩

end HQ

/-! ## Free graded chain complexes -/

/-- A free graded chain complex over `ℤ`: basis `β`, degree, boundary of degree `-1`,
`d ∘ d = 0`, and the augmentation kills boundaries of `1`-cells. -/
structure GC where
  /-- Basis elements (cells). -/
  β : Type
  /-- Degree of a cell. -/
  deg : β → ℕ
  /-- The boundary operator. -/
  d : (β →₀ ℤ) →ₗ[ℤ] (β →₀ ℤ)
  d_deg : ∀ b, d (single b 1) ∈ supported ℤ ℤ {b' | deg b' + 1 = deg b}
  dd : ∀ x, d (d x) = 0
  aug_d : ∀ b, deg b = 1 →
    linearCombination ℤ (fun b => if deg b = 0 then (1 : ℤ) else 0) (d (single b 1)) = 0

namespace GC

variable (C : GC)

/-- The augmentation `ε`: the sum of the coefficients of the `0`-cells. -/
noncomputable def aug : (C.β →₀ ℤ) →ₗ[ℤ] ℤ :=
  linearCombination ℤ (fun b => if C.deg b = 0 then (1 : ℤ) else 0)

/-- Homogeneous chains of degree `k`. -/
def homog (k : ℕ) : Submodule ℤ (C.β →₀ ℤ) := supported ℤ ℤ {b | C.deg b = k}

/-- The chains of degree `k` of the subcomplex spanned by `S`. -/
def Ch (S : Set C.β) (k : ℕ) : Submodule ℤ (C.β →₀ ℤ) :=
  supported ℤ ℤ {b | b ∈ S ∧ C.deg b = k}

/-- Cycles of degree `k` of `S`. -/
def Z (S : Set C.β) (k : ℕ) : Submodule ℤ (C.β →₀ ℤ) := C.Ch S k ⊓ LinearMap.ker C.d

/-- Boundaries of degree `k` of `S`. -/
def B (S : Set C.β) (k : ℕ) : Submodule ℤ (C.β →₀ ℤ) := (C.Ch S (k + 1)).map C.d

/-- `S` is a subcomplex: closed under the boundary. -/
def Closed (S : Set C.β) : Prop := ∀ b ∈ S, C.d (single b 1) ∈ supported ℤ ℤ S

/-- Homology of the subcomplex `S` in degree `k`. -/
abbrev H (S : Set C.β) (k : ℕ) : Type := HQ (C.Z S k) (C.B S k)

variable {C}

theorem mem_Ch {S : Set C.β} {k : ℕ} {x : C.β →₀ ℤ} :
    x ∈ C.Ch S k ↔ x ∈ supported ℤ ℤ S ∧ x ∈ C.homog k := by
  simp only [Ch, homog, mem_supported]
  constructor
  · intro h; exact ⟨fun b hb => (h hb).1, fun b hb => (h hb).2⟩
  · rintro ⟨h1, h2⟩ b hb; exact ⟨h1 hb, h2 hb⟩

theorem single_mem_homog (b : C.β) (c : ℤ) : single b c ∈ C.homog (C.deg b) :=
  single_mem_supported ℤ c rfl

theorem d_mem_homog {k : ℕ} {x : C.β →₀ ℤ} (hx : x ∈ C.homog (k + 1)) : C.d x ∈ C.homog k := by
  have h : C.homog (k + 1) ≤ (C.homog k).comap C.d := by
    unfold homog
    rw [supported_eq_span_single, Submodule.span_le]
    rintro _ ⟨b, hb, rfl⟩
    simp only [SetLike.mem_coe, Submodule.mem_comap]
    have := C.d_deg b
    refine supported_mono (fun b' hb' => ?_) this
    simp only [Set.mem_ofPred_eq] at hb hb' ⊢
    omega
  exact h hx

theorem d_homog_zero {x : C.β →₀ ℤ} (hx : x ∈ C.homog 0) : C.d x = 0 := by
  have h : C.homog 0 ≤ LinearMap.ker C.d := by
    unfold homog
    rw [supported_eq_span_single, Submodule.span_le]
    rintro _ ⟨b, hb, rfl⟩
    simp only [SetLike.mem_coe, LinearMap.mem_ker]
    have := C.d_deg b
    simp only [Set.mem_ofPred_eq] at hb
    rw [hb] at this
    have he : {b' : C.β | C.deg b' + 1 = 0} = ∅ := by ext; simp
    rw [he, supported_empty] at this
    exact (Submodule.mem_bot ℤ).mp this
  exact h hx

theorem d_mem_supported {S : Set C.β} (hS : C.Closed S) {x : C.β →₀ ℤ}
    (hx : x ∈ supported ℤ ℤ S) : C.d x ∈ supported ℤ ℤ S := by
  rw [supported_eq_span_single] at hx
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨b, hb, rfl⟩ := hy
    exact hS b hb
  | zero => simp
  | add x y _ _ hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
  | smul c x _ hx => rw [map_smul]; exact Submodule.smul_mem _ c hx

theorem d_mem_Ch {S : Set C.β} (hS : C.Closed S) {k : ℕ} {x : C.β →₀ ℤ}
    (hx : x ∈ C.Ch S (k + 1)) : C.d x ∈ C.Ch S k := by
  rw [mem_Ch] at hx ⊢
  exact ⟨d_mem_supported hS hx.1, d_mem_homog hx.2⟩

theorem B_le_Z {S : Set C.β} (hS : C.Closed S) (k : ℕ) : C.B S k ≤ C.Z S k := by
  rintro _ ⟨x, hx, rfl⟩
  exact ⟨d_mem_Ch hS hx, by simp [C.dd]⟩

theorem Ch_mono {S T : Set C.β} (h : S ⊆ T) (k : ℕ) : C.Ch S k ≤ C.Ch T k :=
  supported_mono fun _ hb => ⟨h hb.1, hb.2⟩

theorem Z_mono {S T : Set C.β} (h : S ⊆ T) (k : ℕ) : C.Z S k ≤ C.Z T k :=
  inf_le_inf_right _ (Ch_mono h k)

theorem B_mono {S T : Set C.β} (h : S ⊆ T) (k : ℕ) : C.B S k ≤ C.B T k :=
  Submodule.map_mono (Ch_mono h (k + 1))

theorem aug_single (b : C.β) : C.aug (single b 1) = if C.deg b = 0 then 1 else 0 := by
  simp [aug]

theorem aug_homog_succ {k : ℕ} {x : C.β →₀ ℤ} (hx : x ∈ C.homog (k + 1)) : C.aug x = 0 := by
  have h : C.homog (k + 1) ≤ LinearMap.ker C.aug := by
    unfold homog
    rw [supported_eq_span_single, Submodule.span_le]
    rintro _ ⟨b, hb, rfl⟩
    simp only [Set.mem_ofPred_eq] at hb
    simp [aug_single, hb]
  exact h hx

theorem aug_comp_d (x : C.β →₀ ℤ) : C.aug (C.d x) = 0 := by
  induction x using Finsupp.induction_linear with
  | zero => simp
  | add x y hx hy => simp [hx, hy]
  | single b c =>
    rw [← mul_one c, ← smul_eq_mul, ← smul_single, map_zsmul, map_zsmul]
    rcases h : C.deg b with _ | _ | k
    · rw [d_homog_zero (h ▸ single_mem_homog b 1)]; simp
    · have := C.aug_d b h
      simp only [aug] at this ⊢
      simp [this]
    · have : C.d (single b 1) ∈ C.homog (k + 1) := d_mem_homog (h ▸ single_mem_homog b 1)
      rw [aug_homog_succ this]; simp

end GC

/-! ## Linear combinations and locality -/

section LC

variable {α M : Type*} [AddCommGroup M]

theorem lc_congr {f g : α → M} {x : α →₀ ℤ} (h : ∀ b ∈ x.support, f b = g b) :
    linearCombination ℤ f x = linearCombination ℤ g x := by
  simp only [linearCombination_apply]
  exact Finsupp.sum_congr fun b hb => by rw [h b hb]

theorem lc_mem {f : α → M} {x : α →₀ ℤ} {P : Submodule ℤ M} (h : ∀ b ∈ x.support, f b ∈ P) :
    linearCombination ℤ f x ∈ P := by
  rw [linearCombination_apply]
  exact Submodule.finsuppSum_mem _ _ _ _ fun b hb => P.smul_mem _ (h b (Finsupp.mem_support_iff.mpr hb))

theorem lc_single_one (f : α → M) (b : α) : linearCombination ℤ f (single b 1) = f b := by
  rw [linearCombination_single, one_smul]

/-- A linear map applied to a linear combination. -/
theorem map_lc {N : Type*} [AddCommGroup N] (L : M →ₗ[ℤ] N) (f : α → M)
    (x : α →₀ ℤ) : L (linearCombination ℤ f x) = linearCombination ℤ (fun b => L (f b)) x := by
  simp only [linearCombination_apply, map_finsuppSum, map_zsmul]

/-- Two linear maps out of `α →₀ ℤ` agree on `x` if they agree on the support of `x`. -/
theorem linearMap_congr_support {N : Type*} [AddCommGroup N]
    (L L' : (α →₀ ℤ) →ₗ[ℤ] N) {x : α →₀ ℤ}
    (h : ∀ b ∈ x.support, L (single b 1) = L' (single b 1)) : L x = L' x := by
  rw [← Finsupp.sum_single x]
  simp only [map_finsuppSum]
  refine Finsupp.sum_congr fun b hb => ?_
  rw [← mul_one (x b), ← smul_eq_mul, ← smul_single, map_zsmul, map_zsmul, h b hb]

end LC

/-! ## Construction by induction on the degree -/

section Construction

variable {α γ : Type*}

/-- **Construction by induction on the degree.**  If the property `Good f b` depends only on
the values of `f` in degrees `≤ deg b`, and a good value at `b` can always be chosen once
`f` is good in lower degrees, then there is a function good everywhere. -/
theorem graded_construction [Nonempty γ] (deg : α → ℕ) (Good : (α → γ) → α → Prop)
    (hloc : ∀ f f' b, (∀ b', deg b' ≤ deg b → f b' = f' b') → Good f b → Good f' b)
    (hstep : ∀ f b, (∀ b', deg b' < deg b → Good f b') →
      ∃ y, ∀ f', f' b = y → (∀ b', deg b' < deg b → f' b' = f b') → Good f' b) :
    ∃ f, ∀ b, Good f b := by
  classical
  let Q : (α → γ) → α → γ → Prop := fun f b y =>
    ∀ f', f' b = y → (∀ b', deg b' < deg b → f' b' = f b') → Good f' b
  let ext : ℕ → (α → γ) → α → γ := fun k f b =>
    if deg b = k then (if h : ∃ y, Q f b y then h.choose else f b) else f b
  let seq : ℕ → α → γ := fun k => Nat.rec (ext 0 fun _ => Classical.arbitrary γ)
    (fun k f => ext (k + 1) f) k
  have seq_zero : seq 0 = ext 0 fun _ => Classical.arbitrary γ := rfl
  have seq_succ : ∀ k, seq (k + 1) = ext (k + 1) (seq k) := fun _ => rfl
  have agree : ∀ k b, deg b ≤ k → seq k b = seq (deg b) b := by
    intro k
    induction k with
    | zero => intro b hb; rw [Nat.le_zero.mp hb]
    | succ k ih =>
      intro b hb
      by_cases hk : deg b = k + 1
      · rw [hk]
      · rw [seq_succ]
        simp only [ext, hk, ↓reduceIte]
        exact ih b (by omega)
  have good : ∀ k b, deg b ≤ k → Good (seq k) b := by
    intro k
    induction k with
    | zero =>
      intro b hb
      have hb0 : deg b = 0 := Nat.le_zero.mp hb
      obtain ⟨y, hy⟩ := hstep (fun _ => Classical.arbitrary γ) b (fun _ h => by omega)
      have hex : ∃ y, Q (fun _ => Classical.arbitrary γ) b y := ⟨y, hy⟩
      refine hex.choose_spec (seq 0) ?_ (fun b' h => by omega)
      rw [seq_zero]; simp only [ext, hb0, ↓reduceIte, hex, ↓reduceDIte]
    | succ k ih =>
      intro b hb
      by_cases hk : deg b = k + 1
      · obtain ⟨y, hy⟩ := hstep (seq k) b (fun b' h => ih b' (by omega))
        have hex : ∃ y, Q (seq k) b y := ⟨y, hy⟩
        refine hex.choose_spec (seq (k + 1)) ?_ (fun b' h => ?_)
        · rw [seq_succ]; simp only [ext, hk, ↓reduceIte, hex, ↓reduceDIte]
        · rw [seq_succ]; simp only [ext, show deg b' ≠ k + 1 by omega, ↓reduceIte]
      · refine hloc (seq k) (seq (k + 1)) b (fun b' h => ?_) (ih b (by omega))
        rw [seq_succ]; simp only [ext, show deg b' ≠ k + 1 by omega, ↓reduceIte]
  refine ⟨fun b => seq (deg b) b, fun b => ?_⟩
  refine hloc (seq (deg b)) _ b (fun b' h => agree (deg b) b' h) (good _ b le_rfl)

end Construction

/-! ## The acyclic carrier theorem -/

section Carrier

variable {A B : GC}

/-- A set of cells of `B` is **acyclic**: every cycle in it of positive degree, and every
`0`-chain in it of augmentation `0`, bounds in it. -/
def Acyclic (B : GC) (K : Set B.β) : Prop :=
  ∀ k, ∀ z ∈ supported ℤ ℤ K, z ∈ B.homog k → B.d z = 0 → (k = 0 → B.aug z = 0) →
    ∃ y ∈ supported ℤ ℤ K, y ∈ B.homog (k + 1) ∧ B.d y = z

/-- `F = Σ f` commutes with the boundaries on `x` if it does on every cell of `x`. -/
theorem d_lc_of_cells {f : A.β → (B.β →₀ ℤ)} {x : A.β →₀ ℤ}
    (h : ∀ b ∈ x.support, B.d (f b) = linearCombination ℤ f (A.d (single b 1))) :
    B.d (linearCombination ℤ f x) = linearCombination ℤ f (A.d x) := by
  have := linearMap_congr_support (B.d ∘ₗ linearCombination ℤ f)
    (linearCombination ℤ f ∘ₗ A.d) (x := x) (fun b hb => by simpa using h b hb)
  simpa using this

theorem support_d_subset {S : Set A.β} (hS : A.Closed S) {b : A.β} (hb : b ∈ S) :
    ∀ b' ∈ (A.d (single b 1)).support, b' ∈ S ∧ A.deg b' + 1 = A.deg b := fun _ hb' =>
  ⟨(mem_supported ℤ _).mp (hS b hb) hb', (mem_supported ℤ _).mp (A.d_deg b) hb'⟩

/-- **Acyclic carriers, existence.**  An augmentation-preserving chain map carried by an
acyclic carrier `Φ` exists. -/
theorem exists_chainMap {S : Set A.β} (hS : A.Closed S) (Φ : A.β → Set B.β)
    (hΦm : ∀ b ∈ S, ∀ b' ∈ (A.d (single b 1)).support, Φ b' ⊆ Φ b)
    (hΦa : ∀ b ∈ S, Acyclic B (Φ b))
    (hΦ0 : ∀ b ∈ S, A.deg b = 0 → ∃ y ∈ supported ℤ ℤ (Φ b), y ∈ B.homog 0 ∧ B.aug y = 1) :
    ∃ f : A.β → (B.β →₀ ℤ), ∀ b ∈ S, f b ∈ supported ℤ ℤ (Φ b) ∧ f b ∈ B.homog (A.deg b) ∧
      B.d (f b) = linearCombination ℤ f (A.d (single b 1)) ∧
      (A.deg b = 0 → B.aug (f b) = 1) := by
  refine graded_construction A.deg (fun f b => b ∈ S → f b ∈ supported ℤ ℤ (Φ b) ∧
      f b ∈ B.homog (A.deg b) ∧ B.d (f b) = linearCombination ℤ f (A.d (single b 1)) ∧
      (A.deg b = 0 → B.aug (f b) = 1)) ?_ ?_
  · intro f f' b hff h hb
    obtain ⟨h1, h2, h3, h4⟩ := h hb
    rw [← hff b le_rfl]
    refine ⟨h1, h2, ?_, h4⟩
    rw [h3]
    exact lc_congr fun b' hb' => hff b' (by have := (support_d_subset hS hb b' hb').2; omega)
  · intro f b hlow
    by_cases hb : b ∈ S
    swap
    · exact ⟨f b, fun _ _ _ h => absurd h hb⟩
    rcases hdb : A.deg b with _ | k
    · obtain ⟨y, hy1, hy2, hy3⟩ := hΦ0 b hb hdb
      refine ⟨y, fun f' hf' _ _ => ?_⟩
      rw [hf']
      refine ⟨hy1, hy2, ?_, fun _ => hy3⟩
      rw [GC.d_homog_zero hy2, GC.d_homog_zero (hdb ▸ GC.single_mem_homog b 1), map_zero]
    · set z := linearCombination ℤ f (A.d (single b 1)) with hz
      have hsupp := support_d_subset hS hb
      have hgood : ∀ b' ∈ (A.d (single b 1)).support, B.d (f b') =
          linearCombination ℤ f (A.d (single b' 1)) ∧ f b' ∈ supported ℤ ℤ (Φ b') ∧
          f b' ∈ B.homog k ∧ (A.deg b' = 0 → B.aug (f b') = 1) := by
        intro b' hb'
        obtain ⟨hb'S, hdeg⟩ := hsupp b' hb'
        obtain ⟨h1, h2, h3, h4⟩ := hlow b' (by omega) hb'S
        exact ⟨h3, h1, by rw [show k = A.deg b' by omega]; exact h2, h4⟩
      have hzs : z ∈ supported ℤ ℤ (Φ b) := lc_mem fun b' hb' =>
        supported_mono (hΦm b hb b' hb') (hgood b' hb').2.1
      have hzh : z ∈ B.homog k := lc_mem fun b' hb' => (hgood b' hb').2.2.1
      have hzd : B.d z = 0 := by
        rw [hz, d_lc_of_cells fun b' hb' => (hgood b' hb').1, A.dd, map_zero]
      have hza : k = 0 → B.aug z = 0 := by
        intro hk0
        rw [hz, map_lc, ← A.aug_comp_d (single b 1)]
        refine lc_congr fun b' hb' => ?_
        have h0 : A.deg b' = 0 := by have := (hsupp b' hb').2; omega
        rw [(hgood b' hb').2.2.2 h0]; simp [h0]
      obtain ⟨y, hy1, hy2, hy3⟩ := hΦa b hb k z hzs hzh hzd hza
      refine ⟨y, fun f' hf' hagree _ => ?_⟩
      rw [hf']
      refine ⟨hy1, hy2, ?_, fun h => absurd h (Nat.succ_ne_zero k)⟩
      rw [hy3, hz]
      exact lc_congr fun b' hb' => (hagree b' (by have := (hsupp b' hb').2; omega)).symm

theorem lc_comp_single {N : Type*} [AddCommGroup N] (L : (A.β →₀ ℤ) →ₗ[ℤ] N) (x : A.β →₀ ℤ) :
    linearCombination ℤ (fun b => L (single b 1)) x = L x :=
  linearMap_congr_support (linearCombination ℤ fun b => L (single b 1)) L
    (fun b _ => lc_single_one _ b)

/-- **Acyclic carriers, uniqueness up to homotopy.**  Two augmentation-compatible chain maps
carried by an acyclic carrier `Φ` are chain homotopic, through a homotopy carried by
`Φ`. -/
theorem exists_homotopy {S : Set A.β} (hS : A.Closed S) (Φ : A.β → Set B.β)
    (hΦm : ∀ b ∈ S, ∀ b' ∈ (A.d (single b 1)).support, Φ b' ⊆ Φ b)
    (hΦa : ∀ b ∈ S, Acyclic B (Φ b)) (f g : A.β → (B.β →₀ ℤ))
    (hf : ∀ b ∈ S, f b ∈ supported ℤ ℤ (Φ b) ∧ f b ∈ B.homog (A.deg b) ∧
      B.d (f b) = linearCombination ℤ f (A.d (single b 1)))
    (hg : ∀ b ∈ S, g b ∈ supported ℤ ℤ (Φ b) ∧ g b ∈ B.homog (A.deg b) ∧
      B.d (g b) = linearCombination ℤ g (A.d (single b 1)))
    (h0 : ∀ b ∈ S, A.deg b = 0 → B.aug (f b) = B.aug (g b)) :
    ∃ T : A.β → (B.β →₀ ℤ), ∀ b ∈ S, T b ∈ supported ℤ ℤ (Φ b) ∧
      T b ∈ B.homog (A.deg b + 1) ∧
      B.d (T b) + linearCombination ℤ T (A.d (single b 1)) = f b - g b := by
  refine graded_construction A.deg (fun T b => b ∈ S → T b ∈ supported ℤ ℤ (Φ b) ∧
      T b ∈ B.homog (A.deg b + 1) ∧
      B.d (T b) + linearCombination ℤ T (A.d (single b 1)) = f b - g b) ?_ ?_
  · intro T T' b hTT h hb
    obtain ⟨h1, h2, h3⟩ := h hb
    rw [← hTT b le_rfl]
    refine ⟨h1, h2, ?_⟩
    rw [← h3]
    congr 1
    exact (lc_congr fun b' hb' =>
      hTT b' (by have := (support_d_subset hS hb b' hb').2; omega)).symm
  · intro T b hlow
    by_cases hb : b ∈ S
    swap
    · exact ⟨T b, fun _ _ _ h => absurd h hb⟩
    obtain ⟨hf1, hf2, hf3⟩ := hf b hb
    obtain ⟨hg1, hg2, hg3⟩ := hg b hb
    have hsupp := support_d_subset hS hb
    rcases hdb : A.deg b with _ | k
    · have hz1 : f b - g b ∈ supported ℤ ℤ (Φ b) := Submodule.sub_mem _ hf1 hg1
      have hz2 : f b - g b ∈ B.homog 0 := Submodule.sub_mem _ (hdb ▸ hf2) (hdb ▸ hg2)
      obtain ⟨y, hy1, hy2, hy3⟩ := hΦa b hb 0 _ hz1 hz2 (GC.d_homog_zero hz2)
        (fun _ => by rw [map_sub, h0 b hb hdb, sub_self])
      refine ⟨y, fun T' hT' _ _ => ?_⟩
      rw [hT']
      refine ⟨hy1, hy2, ?_⟩
      rw [hy3, GC.d_homog_zero (hdb ▸ GC.single_mem_homog b 1), map_zero, add_zero]
    · have hlow' : ∀ b' ∈ (A.d (single b 1)).support, T b' ∈ supported ℤ ℤ (Φ b') ∧
          T b' ∈ B.homog (k + 1) ∧
          B.d (T b') + linearCombination ℤ T (A.d (single b' 1)) = f b' - g b' := by
        intro b' hb'
        obtain ⟨hb'S, hdeg⟩ := hsupp b' hb'
        obtain ⟨h1, h2, h3⟩ := hlow b' (by omega) hb'S
        exact ⟨h1, by rw [show k + 1 = A.deg b' + 1 by omega]; exact h2, h3⟩
      set z := f b - g b - linearCombination ℤ T (A.d (single b 1)) with hz
      have hz1 : z ∈ supported ℤ ℤ (Φ b) := Submodule.sub_mem _ (Submodule.sub_mem _ hf1 hg1)
        (lc_mem fun b' hb' => supported_mono (hΦm b hb b' hb') (hlow' b' hb').1)
      have hz2 : z ∈ B.homog (k + 1) := Submodule.sub_mem _
        (Submodule.sub_mem _ (hdb ▸ hf2) (hdb ▸ hg2)) (lc_mem fun b' hb' => (hlow' b' hb').2.1)
      have hz3 : B.d z = 0 := by
        have e1 : B.d (linearCombination ℤ T (A.d (single b 1))) =
            linearCombination ℤ f (A.d (single b 1)) - linearCombination ℤ g (A.d (single b 1))
            - linearCombination ℤ T (A.d (A.d (single b 1))) := by
          rw [map_lc, lc_congr (g := fun b' => f b' - g b' -
              linearCombination ℤ T (A.d (single b' 1)))
            (fun b' hb' => eq_sub_of_add_eq (hlow' b' hb').2.2)]
          have e2 := (lc_comp_single (linearCombination ℤ T ∘ₗ A.d) (A.d (single b 1))).symm
          simp only [LinearMap.coe_comp, Function.comp_apply] at e2
          rw [e2]
          simp only [linearCombination_apply, ← Finsupp.sum_sub]
          exact Finsupp.sum_congr fun b' _ => by rw [smul_sub, smul_sub]
        rw [hz, map_sub, map_sub, e1, hf3, hg3, A.dd, map_zero]
        abel
      obtain ⟨y, hy1, hy2, hy3⟩ := hΦa b hb (k + 1) z hz1 hz2 hz3
        (fun h => absurd h (Nat.succ_ne_zero k))
      refine ⟨y, fun T' hT' hagree _ => ?_⟩
      rw [hT']
      refine ⟨hy1, hy2, ?_⟩
      rw [hy3, hz, lc_congr (g := T) fun b' hb' =>
        hagree b' (by have := (hsupp b' hb').2; omega)]
      abel

end Carrier

/-! ## The simplicial sign cancellation -/

section Simplicial

theorem val_succAbove {n : ℕ} (p : Fin (n + 1)) (k : Fin n) :
    ((p.succAbove k : Fin (n + 1)) : ℕ) = if (k : ℕ) < p then (k : ℕ) else (k : ℕ) + 1 := by
  by_cases h : (k : ℕ) < p
  · rw [Fin.succAbove_of_castSucc_lt _ _ (by simp [Fin.lt_def, h])]; simp [h]
  · rw [Fin.succAbove_of_le_castSucc _ _ (by simp [Fin.le_def]; omega)]; simp [h]

/-- The simplicial identity `δ_{j+1} ∘ δ_i = δ_i ∘ δ_j` for `i ≤ j`. -/
theorem succAbove_comp_succAbove {n : ℕ} (i j : Fin (n + 2)) (hij : (i : ℕ) ≤ j) :
    (Fin.succAbove j.succ ∘ Fin.succAbove i : Fin (n + 1) → Fin (n + 3)) =
      Fin.succAbove i.castSucc ∘ Fin.succAbove j := by
  funext k
  apply Fin.ext
  simp only [Function.comp_apply, val_succAbove, Fin.val_succ, Fin.val_castSucc]
  split_ifs <;> omega

/-- **The sign cancellation behind `∂ ∘ ∂ = 0`**: for any function `F` of the composite
coface maps, `Σ_j Σ_i (-1)^{j+i} F(δ_j ∘ δ_i) = 0`. -/
theorem sum_succAbove_succAbove {M : Type*} [AddCommGroup M] {n : ℕ}
    (F : (Fin (n + 1) → Fin (n + 3)) → M) :
    ∑ j : Fin (n + 3), ∑ i : Fin (n + 2),
      ((-1 : ℤ) ^ (j : ℕ) * (-1) ^ (i : ℕ)) • F (Fin.succAbove j ∘ Fin.succAbove i) = 0 := by
  classical
  rw [← Finset.sum_product']
  set t : Fin (n + 3) × Fin (n + 2) → M := fun p =>
    ((-1 : ℤ) ^ (p.1 : ℕ) * (-1) ^ (p.2 : ℕ)) • F (Fin.succAbove p.1 ∘ Fin.succAbove p.2)
  rw [Finset.univ_product_univ, ← Finset.sum_filter_add_sum_filter_not Finset.univ
    (fun p : Fin (n + 3) × Fin (n + 2) => (p.2 : ℕ) < p.1)]
  rw [add_eq_zero_iff_eq_neg, ← Finset.sum_neg_distrib]
  refine Finset.sum_bij' (fun p hp => (p.2.castSucc, p.1.pred (by
      simp only [Finset.mem_filter] at hp
      intro h; rw [h] at hp; simp at hp)))
    (fun p hp => (p.2.succ, p.1.castLT (by
      simp only [Finset.mem_filter, not_lt] at hp
      exact lt_of_le_of_lt hp.2 p.2.2))) ?_ ?_ ?_ ?_ ?_
  · intro p hp
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_lt, Fin.val_castSucc,
      Fin.val_pred] at hp ⊢
    omega
  · intro p hp
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_lt, Fin.val_succ,
      Fin.val_castLT] at hp ⊢
    omega
  · intro p hp
    simp
  · intro p hp
    simp
  · intro p hp
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp
    have hp0 : p.1 ≠ 0 := by intro h; rw [h] at hp; simp at hp
    have key := succAbove_comp_succAbove p.2 (p.1.pred hp0)
      (by rw [Fin.val_pred]; omega)
    rw [Fin.succ_pred] at key
    simp only [key, Fin.val_castSucc, Fin.val_pred]
    rw [← neg_smul]
    congr 1
    obtain ⟨j, hj⟩ : ∃ j, (p.1 : ℕ) = j + 1 := ⟨p.1 - 1, by omega⟩
    rw [hj, Nat.add_sub_cancel, pow_succ]
    ring

end Simplicial

/-! ## Simplicial bases -/

/-- A **simplicial basis**: types `X k` of `k`-simplices with a contravariant action of all
maps `Fin (m+1) → Fin (k+1)` (faces, degeneracies, reorderings).  Singular simplices and
linear (vertex-tuple) simplices are the two examples. -/
structure SBasis where
  /-- The `k`-simplices. -/
  X : ℕ → Type
  /-- Precomposition with a map of vertex sets. -/
  act : {m k : ℕ} → (Fin (m + 1) → Fin (k + 1)) → X k → X m
  act_comp : ∀ {l m k : ℕ} (f : Fin (l + 1) → Fin (m + 1)) (g : Fin (m + 1) → Fin (k + 1))
    (x : X k), act f (act g x) = act (g ∘ f) x

namespace SBasis

variable (P : SBasis)

/-- The `i`-th face of a simplex. -/
def face {k : ℕ} (x : P.X (k + 1)) (i : Fin (k + 2)) : P.X k := P.act (Fin.succAbove i) x

/-- The alternating sum of faces of one simplex. -/
def bdry : (Σ k, P.X k) → ((Σ k, P.X k) →₀ ℤ)
  | ⟨0, _⟩ => 0
  | ⟨k + 1, x⟩ => ∑ i : Fin (k + 2), ((-1 : ℤ) ^ (i : ℕ)) • single ⟨k, P.face x i⟩ 1

/-- The simplicial boundary. -/
def d : ((Σ k, P.X k) →₀ ℤ) →ₗ[ℤ] ((Σ k, P.X k) →₀ ℤ) := linearCombination ℤ P.bdry

theorem d_single_zero (x : P.X 0) : P.d (single ⟨0, x⟩ 1) = 0 := by
  simp [d, bdry]

theorem d_single_succ {k : ℕ} (x : P.X (k + 1)) :
    P.d (single ⟨k + 1, x⟩ 1) =
      ∑ i : Fin (k + 2), ((-1 : ℤ) ^ (i : ℕ)) • single ⟨k, P.face x i⟩ 1 := by
  simp [d, bdry]

theorem d_d_single (s : Σ k, P.X k) : P.d (P.d (single s 1)) = 0 := by
  obtain ⟨k, x⟩ := s
  rcases k with _ | _ | k
  · simp [d_single_zero]
  · simp [d_single_succ, d_single_zero]
  · rw [d_single_succ, map_sum]
    simp only [map_zsmul, d_single_succ, Finset.smul_sum, smul_smul]
    have := sum_succAbove_succAbove (M := (Σ k, P.X k) →₀ ℤ) (n := k)
      (fun φ => single ⟨k, P.act φ x⟩ 1)
    convert this using 4 with j _ i _
    simp only [face, P.act_comp]

/-- The simplicial chain complex of a simplicial basis. -/
abbrev toGC : GC where
  β := Σ k, P.X k
  deg := Sigma.fst
  d := P.d
  d_deg := by
    rintro ⟨k, x⟩
    rcases k with _ | k
    · rw [d_single_zero]; exact Submodule.zero_mem _
    · rw [d_single_succ]
      exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _
        (single_mem_supported ℤ _ rfl)
  dd := by
    have : P.d ∘ₗ P.d = 0 := by
      apply Finsupp.lhom_ext'
      intro s
      apply LinearMap.ext_ring
      simpa using P.d_d_single s
    intro x
    simpa using congrArg (fun L => L x) this
  aug_d := by
    rintro ⟨k, x⟩ (rfl : k = 1)
    rw [d_single_succ]
    simp [Fin.sum_univ_two]

theorem toGC_d : P.toGC.d = P.d := rfl

theorem toGC_deg : P.toGC.deg = Sigma.fst := rfl

end SBasis

end

end QE.Excision
