-- SPDX-License-Identifier: MIT
-- Copyright 2026 Metere Industries, Inc. Author: Alfredo Metere.
-- Quasi-Euclidean Granular Geometry. Any derivative work must carry this notice:
--   This work is derivative of the Quasi-Euclidean Granular Geometry book
--   authored by Alfredo Metere. Copyright 2026 Metere Industries, Inc.
--   All rights reserved
-- See LICENSE.md and NOTICE.

import QuasiEuclidean.Excision.CubeGeom
import QuasiEuclidean.Excision.MayerVietoris

/-!
# Cubical homology equals singular homology

Book: Proposition `prop:topology-homology-singular` (Chapter 10).

**Theorem** (`QE.Excision.comparison`).  For every finite cubical complex `X ⊆ ℤⁿ` and every
degree `k`, the cubical homology `H_k(X)` is isomorphic to the singular homology
`H_k(|X|; ℤ)` (Mathlib's `singularHomologyFunctor`) of its realisation `|X| ⊆ ℝⁿ`.

The proof is by acyclic carriers, with the small-simplices theorem
(`QE.Excision.small_surj`, `QE.Excision.small_inj`, built on barycentric subdivision) for
the open cover of `|X|` by the open stars `ostar v` of the lattice points.

* `θ`: cubical chains → singular chains, an augmentation-preserving chain map carrying each
  cube `c` into the singular chains of the closed cube `|c|` (acyclic: convex);
* `ψ`: small singular chains of `|X|` → cubical chains of `X`, carrying a simplex `s` with
  image in `ostar v` into the cubical star `Kcar s` about `v` (acyclic: `acyclic_star`);
* `θ' = sSd^m ∘ θ` lands in small chains for `m` large;
* `ψ ∘ θ' ≃ id` on cubical chains (carrier: the closure of a cube, a cubical star);
* `θ ∘ ψ ≃ ι` on small chains (carrier: the star-convex union `Rcar s` of carrier cubes);
* `θ' ≃ θ` by the subdivision homotopy.

Then `θ` induces a bijection `H_k(X) → H_k(C(|X|))` (surjectivity from `θψ ≃ ι` and the
small-simplices theorem, injectivity from `ψθ' ≃ id` and the small-simplices theorem), and
`bridge` identifies `H_k(C(|X|))` with Mathlib's singular homology.

Mayer–Vietoris is not needed for this argument.  No measure theory is used.
-/

namespace QE.Excision

open Finsupp QE.Cubical QE.CubicalSingular

noncomputable section

variable {n : ℕ}

/-- The ambient space `ℝⁿ`. -/
abbrev En (n : ℕ) : Type := Fin n → ℝ

/-! ## Generalities on singular chains -/

section SingularGen

variable {E : Type} [TopologicalSpace E]

theorem sSd_ssim_zero (σ : C(Δ 0, E)) : sSd (ssim σ) = ssim σ := by
  rw [sSd_ssim, Sd_lsim]; exact push_vert σ

theorem aug_sSd (x : SC E) : (SG E).aug (sSd x) = (SG E).aug x := by
  refine linearMap_congr_support ((SG E).aug ∘ₗ sSd) (SG E).aug (fun s _ => ?_)
  obtain ⟨k, σ⟩ := s
  simp only [LinearMap.coe_comp, Function.comp_apply]
  rw [show (single ⟨k, σ⟩ 1 : SC E) = ssim σ from rfl]
  rcases k with _ | k
  · rw [sSd_ssim_zero]
  · rw [GC.aug_homog_succ (sSd_mem_homog (ssim_mem_homog σ)), GC.aug_homog_succ (ssim_mem_homog σ)]

theorem aug_sSd_pow (q : ℕ) (x : SC E) : (SG E).aug ((sSd ^ q) x) = (SG E).aug x := by
  induction q with
  | zero => simp
  | succ q ih => rw [pow_succ', Module.End.mul_apply, aug_sSd, ih]

end SingularGen

/-! ## Carriers of singular simplices in `ℝⁿ` -/

section Carriers

/-- The cubical carrier of a singular simplex: all faces of the carrier cubes of its points. -/
def Kcar (s : (SG (En n)).β) : Set (Cube n) := {e | ∃ x ∈ Set.range s.2, CLe e (cc x)}

/-- The geometric carrier of a singular simplex: the union of the carrier cubes of its
points. -/
def Rcar (s : (SG (En n)).β) : Set (En n) := ⋃ x ∈ Set.range s.2, cubeSet (cc x)

theorem isStarAt_Kcar {s : (SG (En n)).β} {v : Fin n → ℤ} (hs : Set.range s.2 ⊆ ostar v) :
    IsStarAt (Kcar s) v :=
  isStarAt_of fun _ ⟨x, hx, hex⟩ => ⟨cc x, vert_le_cc (hs hx), hex, fun _ he' => ⟨x, hx, he'⟩⟩

theorem Kcar_mono {s t : (SG (En n)).β} (h : Set.range t.2 ⊆ Set.range s.2) : Kcar t ⊆ Kcar s :=
  fun _ ⟨_, hx, hex⟩ => ⟨_, h hx, hex⟩

theorem Kcar_sub {X : Finset (Cube n)} (hX : IsComplex X) {s : (SG (En n)).β}
    (hs : Set.range s.2 ⊆ realisation X) : Kcar s ⊆ ↑X :=
  fun _ ⟨_, hx, hex⟩ => mem_of_CLe' hX (cc_mem hX (hs hx)) hex

theorem Kcar_sub_closure {s : (SG (En n)).β} {c : Cube n} (hs : Set.range s.2 ⊆ cubeSet c) :
    Kcar s ⊆ {e | CLe e c} :=
  fun _ ⟨_, hx, hex⟩ => CLe.trans hex (cc_le (hs hx))

theorem range_sub_Rcar (s : (SG (En n)).β) : Set.range s.2 ⊆ Rcar s :=
  fun x hx => Set.mem_biUnion hx (mem_cc x)

theorem Rcar_mono {s t : (SG (En n)).β} (h : Set.range t.2 ⊆ Set.range s.2) : Rcar t ⊆ Rcar s :=
  Set.biUnion_subset_biUnion_left h

theorem Rcar_sub {X : Finset (Cube n)} (hX : IsComplex X) {s : (SG (En n)).β}
    (hs : Set.range s.2 ⊆ realisation X) : Rcar s ⊆ realisation X :=
  Set.iUnion₂_subset fun _ hx => cubeSet_cc_subset hX (hs hx)

theorem cubeSet_sub_Rcar {s : (SG (En n)).β} {e : Cube n} (he : e ∈ Kcar s) :
    cubeSet e ⊆ Rcar s := by
  obtain ⟨x, hx, hex⟩ := he
  exact (cubeSet_mono hex).trans (Set.subset_biUnion_of_mem (u := fun x => cubeSet (cc x)) hx)

theorem vpt_mem_cc {v : Fin n → ℤ} {x : En n} (hx : x ∈ ostar v) : vpt v ∈ cubeSet (cc x) := by
  rw [vpt_mem_cubeSet_iff]
  intro i
  have := vert_le_cc hx i
  simp only [top, Finset.notMem_empty, ite_false, add_zero] at this
  exact this

theorem starConvex_Rcar {s : (SG (En n)).β} {v : Fin n → ℤ} (hs : Set.range s.2 ⊆ ostar v) :
    StarConvex ℝ (vpt v) (Rcar s) := by
  intro y hy a b ha hb hab
  obtain ⟨x, hx, hyx⟩ := Set.mem_iUnion₂.mp hy
  exact Set.mem_biUnion hx ((convex_cubeSet _) (vpt_mem_cc (hs hx)) hyx ha hb hab)

theorem vpt_mem_Rcar {s : (SG (En n)).β} {v : Fin n → ℤ} (hs : Set.range s.2 ⊆ ostar v) :
    vpt v ∈ Rcar s := by
  have hx : s.2 (Classical.arbitrary _) ∈ Set.range s.2 := ⟨_, rfl⟩
  exact Set.mem_biUnion hx (vpt_mem_cc (hs hx))

end Carriers

/-! ## The chain map `θ` from cubical to singular chains -/

section Theta

theorem bd_mem_CLe (c : Cube n) : bd n (single c 1) ∈ supported ℤ ℤ {e : Cube n | CLe e c} := by
  rw [bd_single]
  refine Submodule.sum_mem _ fun i hi => Submodule.smul_mem _ _ (Submodule.sub_mem _ ?_ ?_) <;>
  refine single_mem_supported ℤ _ fun l => ?_ <;>
  · by_cases hl : l = i
    · subst hl; simp [top, unit_apply, hi]
    · simp [top, unit_apply, hl]

theorem CLe_of_mem_support_bd {c b : Cube n} (hb : b ∈ (bd n (single c 1)).support) : CLe b c :=
  (mem_supported ℤ _).mp (bd_mem_CLe c) hb

theorem acyclic_cubeSet (c : Cube n) : Acyclic (SG (En n)) (SA (cubeSet c)) :=
  acyclic_starConvex ((convex_cubeSet c).starConvex (corner_mem c)) (corner_mem c)

theorem theta_exists : ∃ f : Cube n → SC (En n), ∀ c ∈ (Set.univ : Set (Cube n)),
    f c ∈ supported ℤ ℤ (SA (cubeSet c)) ∧ f c ∈ (SG (En n)).homog c.2.card ∧
    (SG (En n)).d (f c) = linearCombination ℤ f (bd n (single c 1)) ∧
    (c.2.card = 0 → (SG (En n)).aug (f c) = 1) :=
  exists_chainMap (A := cGC n) (B := SG (En n)) (S := Set.univ)
    (fun c _ => by rw [supported_univ]; exact Submodule.mem_top) (fun c => SA (cubeSet c))
    (fun _ _ _ hb => SA_mono (cubeSet_mono (CLe_of_mem_support_bd hb)))
    (fun c _ => acyclic_cubeSet c)
    (fun c _ _ => ⟨ssim (ContinuousMap.const (Δ 0) (vpt c.1)),
      single_mem_supported ℤ _ (by rintro _ ⟨t, rfl⟩; exact corner_mem c), ssim_mem_homog _,
      by rw [GC.aug_single]; rfl⟩)

/-- `θ` on a cube. -/
def thf : Cube n → SC (En n) := Classical.choose (theta_exists (n := n))

theorem thf_spec (c : Cube n) :
    thf c ∈ supported ℤ ℤ (SA (cubeSet c)) ∧ thf c ∈ (SG (En n)).homog c.2.card ∧
    (SG (En n)).d (thf c) = linearCombination ℤ thf (bd n (single c 1)) ∧
    (c.2.card = 0 → (SG (En n)).aug (thf c) = 1) :=
  Classical.choose_spec (theta_exists (n := n)) c (Set.mem_univ c)

/-- **The chain map `θ`** from cubical to singular chains. -/
def th : Chain n →ₗ[ℤ] SC (En n) := linearCombination ℤ thf

theorem th_single (c : Cube n) : th (single c 1) = thf c := lc_single_one _ c

theorem sd_th (x : Chain n) : (SG (En n)).d (th x) = th (bd n x) :=
  d_lc_of_cells (A := cGC n) (fun c _ => (thf_spec c).2.2.1)

theorem th_mem_homog {k : ℕ} {x : Chain n} (hx : x ∈ (cGC n).homog k) :
    th x ∈ (SG (En n)).homog k :=
  lc_mem fun c hc => by
    have : c.2.card = k := (mem_supported ℤ _).mp hx hc
    rw [← this]; exact (thf_spec c).2.1

theorem aug_th (x : Chain n) : (SG (En n)).aug (th x) = (cGC n).aug x := by
  refine linearMap_congr_support ((SG (En n)).aug ∘ₗ th) (cGC n).aug (fun c _ => ?_)
  simp only [LinearMap.coe_comp, Function.comp_apply]
  erw [th_single]
  rw [GC.aug_single]
  by_cases h : c.2.card = 0
  · rw [(thf_spec c).2.2.2 h]; simp [h]
  · obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero h
    have := (thf_spec c).2.1
    rw [hk] at this
    rw [GC.aug_homog_succ this]; simp [h]

theorem th_mem_SA {X : Finset (Cube n)} {x : Chain n} (hx : x ∈ supported ℤ ℤ (↑X : Set (Cube n))) :
    th x ∈ supported ℤ ℤ (SA (realisation X)) :=
  lc_mem fun c hc => supported_mono (SA_mono fun _ hy => Set.mem_biUnion
    ((mem_supported ℤ _).mp hx hc) hy) (thf_spec c).1

end Theta

/-! ## The chain map `ψ` from small singular chains to cubical chains -/

section Psi

variable (X : Finset (Cube n))

/-- The small singular simplices of `|X|`: image in `|X|` and in one open star. -/
def Sψ : Set (SG (En n)).β := SA (realisation X) ∩ Small (ostars n)

theorem hered_Sψ : Hered (Sψ X) := hered_inter (hered_SA _) (hered_Small _)

theorem psi_exists : ∃ f : (SG (En n)).β → Chain n, ∀ s ∈ Sψ X,
    f s ∈ supported ℤ ℤ (Kcar s) ∧ f s ∈ (cGC n).homog s.1 ∧
    bd n (f s) = linearCombination ℤ f ((SG (En n)).d (single s 1)) ∧
    (s.1 = 0 → (cGC n).aug (f s) = 1) :=
  exists_chainMap (A := SG (En n)) (B := cGC n) (S := Sψ X) (closed_of_hered (hered_Sψ X)) Kcar
    (fun _ _ _ ht => Kcar_mono (range_of_mem_support_sd ht))
    (fun s hs => by
      obtain ⟨_, ⟨v, rfl⟩, hv⟩ := hs.2
      exact acyclic_star (isStarAt_Kcar hv))
    (fun s hs _ => by
      obtain ⟨_, ⟨v, rfl⟩, hv⟩ := hs.2
      have hx : s.2 (Classical.arbitrary _) ∈ Set.range s.2 := ⟨_, rfl⟩
      refine ⟨single (v, ∅) 1, single_mem_supported ℤ _ ⟨_, hx, vert_le_cc (hv hx)⟩,
        single_mem_supported ℤ _ (by simp), ?_⟩
      rw [GC.aug_single]; simp)

/-- `ψ` on a simplex. -/
def psf : (SG (En n)).β → Chain n := Classical.choose (psi_exists X)

theorem psf_spec {s : (SG (En n)).β} (hs : s ∈ Sψ X) :
    psf X s ∈ supported ℤ ℤ (Kcar s) ∧ psf X s ∈ (cGC n).homog s.1 ∧
    bd n (psf X s) = linearCombination ℤ (psf X) ((SG (En n)).d (single s 1)) ∧
    (s.1 = 0 → (cGC n).aug (psf X s) = 1) :=
  Classical.choose_spec (psi_exists X) s hs

/-- **The chain map `ψ`** from small singular chains to cubical chains. -/
def ps : SC (En n) →ₗ[ℤ] Chain n := linearCombination ℤ (psf X)

theorem ps_single (s : (SG (En n)).β) : ps X (single s 1) = psf X s := lc_single_one _ s

variable {X}

theorem bd_ps {y : SC (En n)} (hy : y ∈ supported ℤ ℤ (Sψ X)) :
    bd n (ps X y) = ps X ((SG (En n)).d y) :=
  d_lc_of_cells (B := cGC n) (fun _ hs => (psf_spec X ((mem_supported ℤ _).mp hy hs)).2.2.1)

theorem ps_mem_homog {k : ℕ} {y : SC (En n)} (hy : y ∈ supported ℤ ℤ (Sψ X))
    (hk : y ∈ (SG (En n)).homog k) : ps X y ∈ (cGC n).homog k :=
  lc_mem fun s hs => by
    have : s.1 = k := (mem_supported ℤ _).mp hk hs
    rw [← this]; exact (psf_spec X ((mem_supported ℤ _).mp hy hs)).2.1

theorem ps_mem_X (hX : IsComplex X) {y : SC (En n)} (hy : y ∈ supported ℤ ℤ (Sψ X)) :
    ps X y ∈ supported ℤ ℤ (↑X : Set (Cube n)) :=
  lc_mem fun s hs => by
    have h := (mem_supported ℤ _).mp hy hs
    exact supported_mono (Kcar_sub hX h.1) (psf_spec X h).1

theorem aug_ps {y : SC (En n)} (hy : y ∈ supported ℤ ℤ (Sψ X)) :
    (cGC n).aug (ps X y) = (SG (En n)).aug y := by
  refine linearMap_congr_support ((cGC n).aug ∘ₗ ps X) (SG (En n)).aug (fun s hs => ?_)
  have h := (mem_supported ℤ _).mp hy hs
  simp only [LinearMap.coe_comp, Function.comp_apply]
  erw [ps_single]
  rw [GC.aug_single]
  by_cases h0 : s.1 = 0
  · rw [(psf_spec X h).2.2.2 h0]; simp [h0]
  · obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero h0
    have := (psf_spec X h).2.1
    rw [hk] at this
    rw [GC.aug_homog_succ this]; simp [h0]

end Psi

/-! ## Assembly -/

section Assembly

theorem small_pow_mono {x : SC (En n)} {q q' : ℕ} (h : q ≤ q')
    (hx : (sSd ^ q) x ∈ supported ℤ ℤ (Small (ostars n))) :
    (sSd ^ q') x ∈ supported ℤ ℤ (Small (ostars n)) := by
  obtain ⟨r, rfl⟩ := Nat.exists_eq_add_of_le' h
  rw [pow_add, Module.End.mul_apply]
  exact sSd_pow_mem_hered (hered_Small _) hx r

theorem exists_m (X : Finset (Cube n)) :
    ∃ m : ℕ, ∀ c ∈ X, (sSd ^ m) (thf c) ∈ supported ℤ ℤ (Small (ostars n)) := by
  classical
  have hex : ∀ c : Cube n, ∃ q, (sSd ^ q) (thf c) ∈ supported ℤ ℤ (Small (ostars n)) :=
    fun c => exists_small_chain isOpen_ostars (cover_ostars (cubeSet c)) (thf_spec c).1
  refine ⟨X.sup fun c => (hex c).choose, fun c hc => ?_⟩
  exact small_pow_mono (Finset.le_sup (f := fun c => (hex c).choose) hc) (hex c).choose_spec

/-- The number of subdivisions making `θ` of every cube of `X` small. -/
def mX (X : Finset (Cube n)) : ℕ := Classical.choose (exists_m X)

theorem mX_spec (X : Finset (Cube n)) {c : Cube n} (hc : c ∈ X) :
    (sSd ^ mX X) (thf c) ∈ supported ℤ ℤ (Small (ostars n)) :=
  Classical.choose_spec (exists_m X) c hc

/-- `θ' = sSd^m ∘ θ`, with values in small chains. -/
def th' (X : Finset (Cube n)) : Chain n →ₗ[ℤ] SC (En n) := (sSd ^ mX X) ∘ₗ th

variable {X : Finset (Cube n)} (hX : IsComplex X)
include hX

theorem th'_single_mem {c : Cube n} (hc : c ∈ X) :
    th' X (single c 1) ∈ supported ℤ ℤ (SA (cubeSet c) ∩ Small (ostars n)) := by
  simp only [th', LinearMap.coe_comp, Function.comp_apply, th_single]
  rw [supported_inter]
  exact Submodule.mem_inf.mpr ⟨sSd_pow_mem_hered (hered_SA _) (thf_spec c).1 _, mX_spec X hc⟩

theorem cubeSet_sub_real {c : Cube n} (hc : c ∈ X) : cubeSet c ⊆ realisation X :=
  fun _ hy => Set.mem_biUnion hc hy

theorem th'_single_mem_Sψ {c : Cube n} (hc : c ∈ X) :
    th' X (single c 1) ∈ supported ℤ ℤ (Sψ X) :=
  supported_mono (s := SA (cubeSet c) ∩ Small (ostars n)) (t := Sψ X)
    (fun _ hs => (⟨hs.1.trans (cubeSet_sub_real hX hc), hs.2⟩ : _ ∈ Sψ X)) (th'_single_mem hX hc)

theorem th'_mem_Sψ {x : Chain n} (hx : x ∈ supported ℤ ℤ (↑X : Set (Cube n))) :
    th' X x ∈ supported ℤ ℤ (Sψ X) := by
  rw [← lc_comp_single (A := cGC n) (th' X) x]
  exact lc_mem fun c hc => th'_single_mem_Sψ hX ((mem_supported ℤ _).mp hx hc)

omit hX in
theorem sd_th' (x : Chain n) : (SG (En n)).d (th' X x) = th' X (bd n x) := by
  show (SG (En n)).d ((sSd ^ mX X) (th x)) = (sSd ^ mX X) (th (bd n x))
  rw [sd_sSd_pow, sd_th]

omit hX in
theorem th'_mem_homog {k : ℕ} {x : Chain n} (hx : x ∈ (cGC n).homog k) :
    th' X x ∈ (SG (En n)).homog k :=
  sSd_pow_mem_homog (th_mem_homog hx) _

omit hX in
theorem aug_th' (x : Chain n) : (SG (En n)).aug (th' X x) = (cGC n).aug x := by
  show (SG (En n)).aug ((sSd ^ mX X) (th x)) = _
  rw [aug_sSd_pow, aug_th]

omit hX in
theorem corner_le (c : Cube n) : CLe ((c.1, ∅) : Cube n) c := by
  intro k
  simp only [top, Finset.notMem_empty, ite_false, add_zero, le_refl, true_and]
  split_ifs <;> omega

/-- **`ψ ∘ θ' ≃ id`** on the cubical chains of `X`. -/
theorem H1_exists : ∃ T : Cube n → Chain n, ∀ c ∈ (↑X : Set (Cube n)),
    T c ∈ supported ℤ ℤ {e : Cube n | CLe e c} ∧ T c ∈ (cGC n).homog (c.2.card + 1) ∧
    bd n (T c) + linearCombination ℤ T (bd n (single c 1)) =
      ps X (th' X (single c 1)) - single c 1 := by
  refine exists_homotopy (A := cGC n) (B := cGC n) (S := ↑X) (closed_complex hX)
    (fun c => {e | CLe e c}) (fun _ _ _ hb _ he => CLe.trans he (CLe_of_mem_support_bd hb))
    (fun c _ => acyclic_star (isStarAt_of (v := c.1) fun _ he =>
      ⟨c, corner_le c, he, fun _ h => h⟩))
    (fun c => ps X (th' X (single c 1))) (fun c => single c 1) ?_ ?_ ?_
  · intro c hc
    have h1 := th'_single_mem hX hc
    have h2 := th'_single_mem_Sψ hX hc
    refine ⟨?_, ps_mem_homog h2 (th'_mem_homog (GC.single_mem_homog (C := cGC n) c 1)), ?_⟩
    · refine lc_mem fun s hs => ?_
      have hs1 := (mem_supported ℤ _).mp h1 hs
      exact supported_mono (Kcar_sub_closure hs1.1) (psf_spec X ((mem_supported ℤ _).mp h2 hs)).1
    · show bd n (ps X (th' X (single c 1))) = _
      rw [bd_ps h2, sd_th']
      exact (lc_comp_single (A := cGC n) (ps X ∘ₗ th' X) _).symm
  · intro c _
    refine ⟨single_mem_supported ℤ _ (CLe.refl c), GC.single_mem_homog (C := cGC n) c 1, ?_⟩
    exact (lc_comp_single (A := cGC n) LinearMap.id _).symm
  · intro c hc h0
    show (cGC n).aug (ps X (th' X (single c 1))) = (cGC n).aug (single c 1)
    rw [aug_ps (th'_single_mem_Sψ hX hc), aug_th']

/-- **`θ ∘ ψ ≃ ι`** on the small singular chains of `|X|`. -/
theorem H2_exists : ∃ T : (SG (En n)).β → SC (En n), ∀ s ∈ Sψ X,
    T s ∈ supported ℤ ℤ (SA (Rcar s)) ∧ T s ∈ (SG (En n)).homog (s.1 + 1) ∧
    (SG (En n)).d (T s) + linearCombination ℤ T ((SG (En n)).d (single s 1)) =
      th (psf X s) - single s 1 := by
  refine exists_homotopy (A := SG (En n)) (B := SG (En n)) (S := Sψ X)
    (closed_of_hered (hered_Sψ X)) (fun s => SA (Rcar s))
    (fun _ _ _ ht => SA_mono (Rcar_mono (range_of_mem_support_sd ht)))
    (fun s hs => by
      obtain ⟨_, ⟨v, rfl⟩, hv⟩ := hs.2
      exact acyclic_starConvex (starConvex_Rcar hv) (vpt_mem_Rcar hv))
    (fun s => th (psf X s)) (fun s => single s 1) ?_ ?_ ?_
  · intro s hs
    have hp := psf_spec X hs
    refine ⟨lc_mem fun e he => supported_mono (SA_mono (cubeSet_sub_Rcar
      ((mem_supported ℤ _).mp hp.1 he))) (thf_spec e).1, th_mem_homog hp.2.1, ?_⟩
    show (SG (En n)).d (th (psf X s)) = _
    rw [sd_th, hp.2.2.1, map_lc]
  · intro s _
    refine ⟨single_mem_supported ℤ _ (range_sub_Rcar s), GC.single_mem_homog (C := SG (En n)) s 1,
      ?_⟩
    exact (lc_comp_single (A := SG (En n)) LinearMap.id _).symm
  · intro s hs h0
    show (SG (En n)).aug (th (psf X s)) = (SG (En n)).aug (single s 1)
    rw [aug_th, GC.aug_single, (psf_spec X hs).2.2.2 h0]
    simp only [show s.1 = 0 from h0, ite_true]

end Assembly

/-! ## The comparison theorem -/

section Final

variable {X : Finset (Cube n)} (hX : IsComplex X)
include hX

/-- The homotopy `ψ θ' ≃ id` on cubes. -/
def T1f : Cube n → Chain n := Classical.choose (H1_exists hX)

theorem T1f_spec {c : Cube n} (hc : c ∈ X) :
    T1f hX c ∈ supported ℤ ℤ {e : Cube n | CLe e c} ∧ T1f hX c ∈ (cGC n).homog (c.2.card + 1) ∧
    bd n (T1f hX c) + linearCombination ℤ (T1f hX) (bd n (single c 1)) =
      ps X (th' X (single c 1)) - single c 1 :=
  Classical.choose_spec (H1_exists hX) c hc

/-- The homotopy `θ ψ ≃ ι` on small simplices. -/
def T2f : (SG (En n)).β → SC (En n) := Classical.choose (H2_exists hX)

theorem T2f_spec {s : (SG (En n)).β} (hs : s ∈ Sψ X) :
    T2f hX s ∈ supported ℤ ℤ (SA (Rcar s)) ∧ T2f hX s ∈ (SG (En n)).homog (s.1 + 1) ∧
    (SG (En n)).d (T2f hX s) + linearCombination ℤ (T2f hX) ((SG (En n)).d (single s 1)) =
      th (psf X s) - single s 1 :=
  Classical.choose_spec (H2_exists hX) s hs

theorem H1_lin {x : Chain n} (hx : x ∈ supported ℤ ℤ (↑X : Set (Cube n))) :
    bd n (linearCombination ℤ (T1f hX) x) + linearCombination ℤ (T1f hX) (bd n x) =
      ps X (th' X x) - x := by
  have := linearMap_congr_support
    (bd n ∘ₗ linearCombination ℤ (T1f hX) + linearCombination ℤ (T1f hX) ∘ₗ bd n)
    (ps X ∘ₗ th' X - LinearMap.id) (x := x) (fun c hc => by
      simp only [LinearMap.add_apply, LinearMap.coe_comp, Function.comp_apply,
        LinearMap.sub_apply, LinearMap.id_coe, id_eq]
      rw [lc_single_one]
      exact (T1f_spec hX ((mem_supported ℤ _).mp hx hc)).2.2)
  simpa using this

theorem H2_lin {y : SC (En n)} (hy : y ∈ supported ℤ ℤ (Sψ X)) :
    (SG (En n)).d (linearCombination ℤ (T2f hX) y) +
      linearCombination ℤ (T2f hX) ((SG (En n)).d y) = th (ps X y) - y := by
  have := linearMap_congr_support
    ((SG (En n)).d ∘ₗ linearCombination ℤ (T2f hX) +
      linearCombination ℤ (T2f hX) ∘ₗ (SG (En n)).d)
    (th ∘ₗ ps X - LinearMap.id) (x := y) (fun s hs => by
      simp only [LinearMap.add_apply, LinearMap.coe_comp, Function.comp_apply,
        LinearMap.sub_apply, LinearMap.id_coe, id_eq]
      rw [lc_single_one, ps_single]
      exact (T2f_spec hX ((mem_supported ℤ _).mp hy hs)).2.2)
  simpa using this

theorem T1_mem {k : ℕ} {x : Chain n} (hx : x ∈ (cGC n).Ch (↑X) k) :
    linearCombination ℤ (T1f hX) x ∈ (cGC n).Ch (↑X) (k + 1) := by
  obtain ⟨hxS, hxH⟩ := GC.mem_Ch.mp hx
  refine GC.mem_Ch.mpr ⟨lc_mem fun c hc => ?_, lc_mem fun c hc => ?_⟩
  · have hcX := (mem_supported ℤ _).mp hxS hc
    exact supported_mono (fun e he => mem_of_CLe' hX hcX he) (T1f_spec hX hcX).1
  · have hcX := (mem_supported ℤ _).mp hxS hc
    have hk : c.2.card = k := (mem_supported ℤ _).mp hxH hc
    rw [← hk]; exact (T1f_spec hX hcX).2.1

theorem T2_mem {k : ℕ} {y : SC (En n)} (hy : y ∈ (SG (En n)).Ch (Sψ X) k) :
    linearCombination ℤ (T2f hX) y ∈ (SG (En n)).Ch (SA (realisation X)) (k + 1) := by
  obtain ⟨hyS, hyH⟩ := GC.mem_Ch.mp hy
  refine GC.mem_Ch.mpr ⟨lc_mem fun s hs => ?_, lc_mem fun s hs => ?_⟩
  · have h := (mem_supported ℤ _).mp hyS hs
    exact supported_mono (SA_mono (Rcar_sub hX h.1)) (T2f_spec hX h).1
  · have h := (mem_supported ℤ _).mp hyS hs
    have hk : s.1 = k := (mem_supported ℤ _).mp hyH hs
    rw [← hk]; exact (T2f_spec hX h).2.1

omit hX in
theorem th_Z (k : ℕ) :
    (cGC n).Z (↑X) k ≤ ((SG (En n)).Z (SA (realisation X)) k).comap th := by
  intro a ha
  obtain ⟨haC, had⟩ := Submodule.mem_inf.mp ha
  obtain ⟨haS, haH⟩ := GC.mem_Ch.mp haC
  refine Submodule.mem_inf.mpr ⟨GC.mem_Ch.mpr ⟨th_mem_SA haS, th_mem_homog haH⟩, ?_⟩
  rw [LinearMap.mem_ker, sd_th]
  rw [LinearMap.mem_ker] at had
  rw [show bd n a = (cGC n).d a from rfl, had, map_zero]

omit hX in
theorem th_B (k : ℕ) :
    (cGC n).B (↑X) k ≤ ((SG (En n)).B (SA (realisation X)) k).comap th := by
  rintro _ ⟨b, hb, rfl⟩
  obtain ⟨hbS, hbH⟩ := GC.mem_Ch.mp hb
  exact ⟨th b, GC.mem_Ch.mpr ⟨th_mem_SA hbS, th_mem_homog hbH⟩, sd_th b⟩

/-- **Surjectivity**: every singular cycle of `|X|` is homologous to `θ` of a cubical cycle. -/
theorem th_surj (k : ℕ) : ∀ z ∈ (SG (En n)).Z (SA (realisation X)) k,
    ∃ a ∈ (cGC n).Z (↑X) k, z - th a ∈ (SG (En n)).B (SA (realisation X)) k := by
  intro z hz
  obtain ⟨z', hz', hzz'⟩ := small_surj isOpen_ostars (cover_ostars _) hz
  obtain ⟨hz'C, hz'd⟩ := Submodule.mem_inf.mp hz'
  rw [LinearMap.mem_ker] at hz'd
  obtain ⟨hz'S, hz'H⟩ := GC.mem_Ch.mp hz'C
  refine ⟨ps X z', Submodule.mem_inf.mpr ⟨GC.mem_Ch.mpr ⟨ps_mem_X hX hz'S,
    ps_mem_homog hz'S hz'H⟩, ?_⟩, ?_⟩
  · rw [LinearMap.mem_ker]
    show bd n (ps X z') = 0
    rw [bd_ps hz'S, hz'd, map_zero]
  · have h2 := H2_lin hX hz'S
    rw [hz'd, map_zero, add_zero] at h2
    have e : z - th (ps X z') = (z - z') - (SG (En n)).d (linearCombination ℤ (T2f hX) z') := by
      rw [h2]; abel
    rw [e]
    exact Submodule.sub_mem _ hzz' ⟨_, T2_mem hX hz'C, rfl⟩

/-- **Injectivity**: a cubical cycle whose image under `θ` bounds in `|X|` bounds in `X`. -/
theorem th_inj (k : ℕ) : ∀ a ∈ (cGC n).Z (↑X) k,
    th a ∈ (SG (En n)).B (SA (realisation X)) k → a ∈ (cGC n).B (↑X) k := by
  intro a ha hb
  obtain ⟨haC, had⟩ := Submodule.mem_inf.mp ha
  rw [LinearMap.mem_ker] at had
  have had' : bd n a = 0 := had
  obtain ⟨haS, haH⟩ := GC.mem_Ch.mp haC
  -- `θ' a` is a small cycle that bounds in `|X|`
  have hyS := th'_mem_Sψ hX haS
  have hyH : th' X a ∈ (SG (En n)).homog k := th'_mem_homog haH
  have hyd : (SG (En n)).d (th' X a) = 0 := by rw [sd_th', had', map_zero]
  have hyZ : th' X a ∈ (SG (En n)).Z (SA (realisation X) ∩ Small (ostars n)) k :=
    Submodule.mem_inf.mpr ⟨GC.mem_Ch.mpr ⟨hyS, hyH⟩, hyd⟩
  have hD := sd_sD (mX X) (th a)
  rw [sd_th, had', map_zero, map_zero, add_zero] at hD
  have hyB : th' X a ∈ (SG (En n)).B (SA (realisation X)) k := by
    have e : th' X a = th a - (SG (En n)).d (sD (mX X) (th a)) := by
      rw [hD]; simp [th']
    rw [e]
    refine Submodule.sub_mem _ hb ⟨_, GC.mem_Ch.mpr ⟨sD_mem_hered (hered_SA _) (th_mem_SA haS) _,
      sD_mem_homog (th_mem_homog haH) _⟩, rfl⟩
  obtain ⟨w, hwC, hw⟩ := small_inj isOpen_ostars (cover_ostars _) hyZ hyB
  obtain ⟨hwS, hwH⟩ := GC.mem_Ch.mp hwC
  -- now `a = ψ θ' a - ∂ T₁ a = ∂ (ψ w - T₁ a)`
  have h1 := H1_lin hX haS
  rw [had', map_zero, add_zero] at h1
  refine ⟨ps X w - linearCombination ℤ (T1f hX) a, Submodule.sub_mem _
    (GC.mem_Ch.mpr ⟨ps_mem_X hX hwS, ps_mem_homog hwS hwH⟩) (T1_mem hX haC), ?_⟩
  show bd n (ps X w - linearCombination ℤ (T1f hX) a) = a
  rw [map_sub, bd_ps hwS, show (SG (En n)).d w = th' X a from hw, h1]
  abel

/-- The isomorphism `H_k(X) ≅ H_k(C(|X|))` induced by `θ`. -/
def mainEquiv (k : ℕ) : (cGC n).H (↑X) k ≃ₗ[ℤ] (SG (En n)).H (SA (realisation X)) k :=
  HQ.equiv th (th_Z k) (th_B k) (th_surj hX k) (th_inj hX k)

/-- **Cubical homology equals singular homology.**  For every finite cubical complex
`X ⊆ ℤⁿ` and every degree `k`, `H_k(X) ≅ H_k(|X|; ℤ)`, the singular homology (Mathlib's
`singularHomologyFunctor` with `ℤ` coefficients) of the realisation `|X| ⊆ ℝⁿ`. -/
theorem comparison (k : ℕ) : Comparison X k :=
  ⟨(cubHomologyEquiv X k).trans ((mainEquiv hX k).trans (bridge (realisation X) k))⟩

end Final

end

end QE.Excision
