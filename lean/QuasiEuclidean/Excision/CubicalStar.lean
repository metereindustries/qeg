-- SPDX-License-Identifier: MIT
-- Copyright 2026 Metere Industries, Inc. Author: Alfredo Metere.
-- Quasi-Euclidean Granular Geometry. Any derivative work must carry this notice:
--   This work is derivative of the Quasi-Euclidean Granular Geometry book
--   authored by Alfredo Metere. Copyright 2026 Metere Industries, Inc.
--   All rights reserved
-- See LICENSE.md and NOTICE.

import QuasiEuclidean.Excision.Star

/-!
# Cubical chains and the acyclicity of cubical stars

Book: Proposition `prop:topology-homology-singular` (Chapter 10), infrastructure.

Cubical chains of `ℤⁿ` (`QE.Cubical.Chain`, boundary `QE.Cubical.bd`) form the free graded
chain complex `cGC n`, and the cubical homology of a complex `X` is the homology of its
subcomplex (`cubHomologyEquiv`).

A set `K` of cubes is a *star about the vertex `v`* (`IsStarAt`) if every cube of `K` lies,
together with `v`, in a common elementary cube, and `K` contains every face of the smallest
such cube.  Pushing a cube towards `v` in one direction `i` (`hOp`, `pOp`) gives a chain
homotopy `∂h + h∂ = id - p` (`bd_hOp`), and composing the projections over all directions
deforms every chain onto multiples of the vertex `v`.  Hence **cubical stars are acyclic**
(`acyclic_star`); in particular the closure of a single cube is acyclic.

No measure theory is used.
-/

namespace QE.Excision

open Finsupp QE.Cubical QE.CubicalSingular

noncomputable section

variable {n : ℕ}

/-! ## Cubical chains as a free graded complex -/

theorem bdCube_mem (c : Cube n) :
    bdCube c ∈ supported ℤ ℤ {c' : Cube n | c'.2.card + 1 = c.2.card} := by
  refine Submodule.sum_mem _ fun i hi => Submodule.smul_mem _ _ (Submodule.sub_mem _ ?_ ?_)
  · exact single_mem_supported ℤ _ (by simp [Finset.card_erase_add_one hi])
  · exact single_mem_supported ℤ _ (by simp [Finset.card_erase_add_one hi])

/-- The cubical chain complex of `ℤⁿ`. -/
abbrev cGC (n : ℕ) : GC where
  β := Cube n
  deg c := c.2.card
  d := bd n
  d_deg c := by rw [bd_single]; exact bdCube_mem c
  dd := bd_bd_apply
  aug_d c hc := by
    obtain ⟨i, hi⟩ := Finset.card_eq_one.mp hc
    obtain ⟨w, S⟩ := c
    simp only at hi
    subst hi
    rw [bd_single]
    simp [bdCube, sgn]

theorem cGC_d : (cGC n).d = bd n := rfl

theorem cGC_Ch (X : Finset (Cube n)) (k : ℕ) : (cGC n).Ch (↑X) k = chains X k := by
  unfold GC.Ch chains cells
  congr 1
  ext c
  simp [cGC]

theorem cGC_Z (X : Finset (Cube n)) (k : ℕ) : (cGC n).Z (↑X) k = cycles X k := by
  unfold GC.Z cycles; rw [cGC_Ch]

theorem cGC_B (X : Finset (Cube n)) (k : ℕ) : (cGC n).B (↑X) k = boundaries X k := by
  unfold GC.B boundaries; rw [cGC_Ch]

/-- Cubical homology is the homology of the subcomplex `X` of `cGC n`. -/
def cubHomologyEquiv (X : Finset (Cube n)) (k : ℕ) :
    homology X k ≃ₗ[ℤ] (cGC n).H (↑X) k :=
  HQ.equiv LinearMap.id (by rw [cGC_Z]; exact fun _ h => h) (by rw [cGC_B]; exact fun _ h => h)
    (fun z hz => ⟨z, by rw [← cGC_Z]; exact hz, by simp⟩)
    (fun z _ hz => by rw [cGC_B] at hz; simpa using hz)

theorem closed_complex {X : Finset (Cube n)} (hX : IsComplex X) : (cGC n).Closed ↑X := by
  intro c hc
  rw [cGC_d, bd_single]
  refine Submodule.sum_mem _ fun i hi => Submodule.smul_mem _ _ (Submodule.sub_mem _ ?_ ?_)
  · exact single_mem_supported ℤ _ (hX c hc i hi).1
  · exact single_mem_supported ℤ _ (hX c hc i hi).2

/-! ## Signs -/

theorem sgn_mul_self (S : Finset (Fin n)) (i : Fin n) : sgn S i * sgn S i = 1 := by
  unfold sgn; rw [← pow_add, ← two_mul, pow_mul]; norm_num

theorem sgn_identity {T : Finset (Fin n)} {i j : Fin n} (hi : i ∉ T) (hj : j ∈ T) :
    sgn (insert i T) i * sgn (insert i T) j + sgn T j * sgn ((insert i T).erase j) i = 0 := by
  have hij : i ≠ j := fun h => hi (h ▸ hj)
  have h := sgn_swap (insert i T) i j (Finset.mem_insert_self i T) (Finset.mem_insert_of_mem hj) hij
  rw [Finset.erase_insert hi] at h
  have h1 := sgn_mul_self T j
  have h2 := sgn_mul_self (insert i T) j
  have h3 := sgn_mul_self (insert i T) i
  have h4 := sgn_mul_self ((insert i T).erase j) i
  -- `a b = -(c d)` with all of `a, b, c, d` squaring to `1` gives `a c = -(b d)`.
  set a := sgn (insert i T) i
  set b := sgn T j
  set c := sgn (insert i T) j
  set d := sgn ((insert i T).erase j) i
  have : a * c = -(b * d) := by
    calc a * c = (a * b) * (b * c) := by rw [show (a * b) * (b * c) = a * (b * b) * c by ring, h1]; ring
      _ = -(c * d) * (b * c) := by rw [h]
      _ = -(b * d) * (c * c) := by ring
      _ = -(b * d) := by rw [h2, mul_one]
  linarith

theorem update_add_unit (w : Fin n → ℤ) {i j : Fin n} (hij : j ≠ i) (x : ℤ) :
    Function.update (w + unit j) i x = Function.update w i x + unit j := by
  funext l
  by_cases hl : l = i
  · subst hl; simp [unit_apply, hij.symm]
  · simp [Function.update_of_ne hl]

/-! ## Pushing a cube towards a vertex in one direction -/

section Push

variable (v : Fin n → ℤ) (i : Fin n)

/-- The coefficient of the cone over a face in direction `i`. -/
def kap (T : Finset (Fin n)) (a : ℤ) : ℤ :=
  if a = v i + 1 then sgn (insert i T) i else if a + 1 = v i then -sgn (insert i T) i else 0

/-- The homotopy in direction `i`: a cube not spanning `i` and at distance `1` from `v` in
direction `i` goes to the cube it spans with its projection. -/
def hval (e : Cube n) : Chain n :=
  if i ∈ e.2 then 0 else
    kap v i e.2 (e.1 i) • single (Function.update e.1 i (min (e.1 i) (v i)), insert i e.2) 1

/-- The projection in direction `i`: kills cubes spanning `i`, moves the others to `vᵢ`. -/
def pval (e : Cube n) : Chain n :=
  if i ∈ e.2 then 0 else single (Function.update e.1 i (v i), e.2) 1

/-- The homotopy operator. -/
def hOp : Chain n →ₗ[ℤ] Chain n := linearCombination ℤ (hval v i)

/-- The projection operator. -/
def pOp : Chain n →ₗ[ℤ] Chain n := linearCombination ℤ (pval v i)

/-- `e` and `v` lie in a common elementary cube. -/
def Near (e : Cube n) : Prop :=
  ∀ j, (j ∈ e.2 → e.1 j ≤ v j ∧ v j ≤ e.1 j + 1) ∧ (j ∉ e.2 → e.1 j ≤ v j + 1 ∧ v j ≤ e.1 j + 1)

theorem hOp_single (e : Cube n) : hOp v i (single e 1) = hval v i e := by
  rw [hOp, linearCombination_single, one_smul]

theorem pOp_single (e : Cube n) : pOp v i (single e 1) = pval v i e := by
  rw [pOp, linearCombination_single, one_smul]

theorem hOp_bdCube (w : Fin n → ℤ) (T : Finset (Fin n)) :
    hOp v i (bdCube (w, T)) = ∑ j ∈ T, sgn T j •
      (hval v i (w + unit j, T.erase j) - hval v i (w, T.erase j)) := by
  simp only [bdCube, map_sum, map_zsmul, map_sub, hOp_single]

theorem hval_face {w : Fin n → ℤ} {T : Finset (Fin n)} {j : Fin n} (hiT : i ∉ T) (hjT : j ∈ T)
    (s : ℤ) : hval v i (w + s • unit j, T.erase j) =
      kap v i (T.erase j) (w i) • single (Function.update w i (min (w i) (v i)) + s • unit j,
        (insert i T).erase j) 1 := by
  have hij : j ≠ i := fun h => hiT (h ▸ hjT)
  have hi' : i ∉ T.erase j := fun h => hiT (Finset.mem_of_mem_erase h)
  have hwi : (w + s • unit j) i = w i := by simp [unit_apply, hij.symm]
  have hupd : Function.update (w + s • unit j) i (min (w i) (v i)) =
      Function.update w i (min (w i) (v i)) + s • unit j := by
    funext l
    by_cases hl : l = i
    · subst hl; simp [unit_apply, hij.symm]
    · simp [Function.update_of_ne hl]
  simp only [hval, hi', ↓reduceIte, hwi, hupd, Finset.erase_insert_of_ne hij.symm]

/-- **The homotopy formula** `∂h + h∂ = id - p` on cubes near `v`. -/
theorem bd_hOp (e : Cube n) (he : Near v e) :
    bd n (hval v i e) + hOp v i (bdCube e) = single e 1 - pval v i e := by
  obtain ⟨w, T⟩ := e
  by_cases hiT : i ∈ T
  · have hpe : pval v i (w, T) = 0 := by simp [pval, hiT]
    have hhe : hval v i (w, T) = 0 := by simp [hval, hiT]
    rw [hpe, hhe, map_zero, zero_add, sub_zero, hOp_bdCube, Finset.sum_eq_single i]
    · have hi' : i ∉ T.erase i := Finset.notMem_erase i T
      have hins : insert i (T.erase i) = T := Finset.insert_erase hiT
      obtain ⟨h1, h2⟩ := (he i).1 hiT
      simp only at h1 h2
      have hwi : (w + unit i) i = w i + 1 := by simp [unit_apply]
      rcases (show v i = w i ∨ v i = w i + 1 by omega) with hv | hv
      · have hu : Function.update (w + unit i) i (min (w i + 1) (v i)) = w := by
          funext l
          by_cases hl : l = i
          · subst hl; simp [hv]
          · simp [unit_apply, hl]
        have e1 : hval v i (w + unit i, T.erase i) = sgn T i • single (w, T) 1 := by
          simp only [hval, hi', ↓reduceIte, kap, hins, hwi, hv]
          simp [hv] at hu ⊢
          rw [hu]
        have e2 : hval v i (w, T.erase i) = 0 := by
          simp only [hval, hi', ↓reduceIte, kap]
          rw [ite_eq_right (by omega), ite_eq_right (by omega), zero_smul]
        rw [e1, e2, sub_zero, smul_smul, sgn_mul_self, one_smul]
      · have e1 : hval v i (w + unit i, T.erase i) = 0 := by
          simp only [hval, hi', ↓reduceIte, kap, hwi]
          rw [ite_eq_right (by omega), ite_eq_right (by omega), zero_smul]
        have hu : Function.update w i (min (w i) (v i)) = w := by
          rw [show min (w i) (v i) = w i by omega]; simp
        have e2 : hval v i (w, T.erase i) = -sgn T i • single (w, T) 1 := by
          simp only [hval, hi', ↓reduceIte, kap, hins, hu]
          rw [ite_eq_right (by omega), ite_eq_left (by omega)]
        rw [e1, e2, zero_sub, neg_smul]
        simp only [neg_neg, smul_smul, sgn_mul_self, one_smul]
    · intro j hjT hji
      have hi' : i ∈ T.erase j := Finset.mem_erase.mpr ⟨Ne.symm hji, hiT⟩
      simp [hval, hi']
    · intro h; exact absurd hiT h
  · obtain ⟨h1, h2⟩ := (he i).2 hiT
    simp only at h1 h2
    set S := insert i T with hS
    set u := Function.update w i (min (w i) (v i)) with hu
    have hhe : hval v i (w, T) = kap v i T (w i) • single (u, S) 1 := by
      simp only [hval, hiT, ↓reduceIte]; rfl
    have hpe : pval v i (w, T) = single (Function.update w i (v i), T) 1 := by
      simp only [pval, hiT, ↓reduceIte]
    have hbd : bdCube (u, S) = sgn S i • (single (u + unit i, T) 1 - single (u, T) 1) +
        ∑ j ∈ T, sgn S j • (single (u + unit j, S.erase j) 1 - single (u, S.erase j) 1) := by
      unfold bdCube
      simp only [hS]
      rw [Finset.sum_insert hiT, Finset.erase_insert hiT]
    have hface : ∀ j ∈ T, hval v i (w + unit j, T.erase j) - hval v i (w, T.erase j) =
        kap v i (T.erase j) (w i) •
          (single (u + unit j, S.erase j) 1 - single (u, S.erase j) 1) := by
      intro j hj
      have e1 := hval_face v i (w := w) hiT hj 1
      have e0 := hval_face v i (w := w) hiT hj 0
      simp only [one_smul, zero_smul, add_zero] at e1 e0
      rw [e1, e0, smul_sub]
    have hcoef : ∀ j ∈ T, kap v i T (w i) * sgn S j + sgn T j * kap v i (T.erase j) (w i) = 0 := by
      intro j hj
      have hij : j ≠ i := fun h => hiT (h ▸ hj)
      have hins : insert i (T.erase j) = S.erase j := (Finset.erase_insert_of_ne hij.symm).symm
      have key := sgn_identity hiT hj
      unfold kap
      rw [hins]
      split_ifs <;> linarith
    rw [hhe, map_zsmul, bd_single, hOp_bdCube,
      Finset.sum_congr rfl (fun j hj => congrArg (sgn T j • ·) (hface j hj)), hbd, smul_add,
      Finset.smul_sum, add_assoc, ← Finset.sum_add_distrib]
    rw [Finset.sum_eq_zero (fun j hj => by
      rw [smul_smul, smul_smul, ← add_smul, hcoef j hj, zero_smul]), add_zero, hpe, smul_smul]
    rcases (show w i = v i + 1 ∨ w i + 1 = v i ∨ w i = v i by omega) with hw | hw | hw
    · have hk : kap v i T (w i) = sgn S i := by simp only [kap, hS, hw, ↓reduceIte]
      have hm : min (w i) (v i) = v i := by omega
      have hu1 : u + unit i = w := by
        funext l; by_cases hl : l = i
        · subst hl; simp [hu, unit_apply, hw]
        · simp [hu, unit_apply, hl]
      rw [hk, sgn_mul_self, one_smul, hu1, hu, hm]
    · have hk : kap v i T (w i) = -sgn S i := by
        simp only [kap, hS]; rw [ite_eq_right (by omega), ite_eq_left hw]
      have hm : min (w i) (v i) = w i := by omega
      have hu0 : u = w := by rw [hu, hm]; simp
      have hu1 : w + unit i = Function.update w i (v i) := by
        funext l; by_cases hl : l = i
        · subst hl; simp [unit_apply, hw]
        · simp [unit_apply, hl]
      rw [hk, neg_mul, sgn_mul_self, hu0, hu1, neg_smul, one_smul, neg_sub]
    · have hk : kap v i T (w i) = 0 := by
        simp only [kap]; rw [ite_eq_right (by omega), ite_eq_right (by omega)]
      have hp : Function.update w i (v i) = w := by rw [← hw]; simp
      rw [hk, zero_mul, zero_smul, hp, sub_self]

end Push

/-! ## Cubical stars are acyclic -/

section StarAcyclic

/-- `K` is a **cubical star about `v`**: its cubes are near `v`, and it is closed under faces
and under the two push operations towards `v`. -/
def IsStarAt (K : Set (Cube n)) (v : Fin n → ℤ) : Prop :=
  ∀ e ∈ K, Near v e ∧ (∀ i ∈ e.2, (e.1 + unit i, e.2.erase i) ∈ K ∧ (e.1, e.2.erase i) ∈ K) ∧
    (∀ i ∉ e.2, e.1 i ≠ v i → (Function.update e.1 i (min (e.1 i) (v i)), insert i e.2) ∈ K) ∧
    (∀ i ∉ e.2, (Function.update e.1 i (v i), e.2) ∈ K)

variable {K : Set (Cube n)} {v : Fin n → ℤ}

theorem hval_mem (hK : IsStarAt K v) (i : Fin n) {e : Cube n} (he : e ∈ K) :
    hval v i e ∈ supported ℤ ℤ K := by
  unfold hval
  split_ifs with hi
  · exact Submodule.zero_mem _
  · by_cases hv : e.1 i = v i
    · have : kap v i e.2 (e.1 i) = 0 := by
        unfold kap; rw [ite_eq_right (by omega), ite_eq_right (by omega)]
      rw [this, zero_smul]; exact Submodule.zero_mem _
    · exact Submodule.smul_mem _ _ (single_mem_supported ℤ _ ((hK e he).2.2.1 i hi hv))

theorem pval_mem (hK : IsStarAt K v) (i : Fin n) {e : Cube n} (he : e ∈ K) :
    pval v i e ∈ supported ℤ ℤ K := by
  unfold pval
  split_ifs with hi
  · exact Submodule.zero_mem _
  · exact single_mem_supported ℤ _ ((hK e he).2.2.2 i hi)

theorem hOp_mem (hK : IsStarAt K v) (i : Fin n) {x : Chain n} (hx : x ∈ supported ℤ ℤ K) :
    hOp v i x ∈ supported ℤ ℤ K :=
  lc_mem fun _ he => hval_mem hK i ((mem_supported ℤ _).mp hx he)

theorem pOp_mem (hK : IsStarAt K v) (i : Fin n) {x : Chain n} (hx : x ∈ supported ℤ ℤ K) :
    pOp v i x ∈ supported ℤ ℤ K :=
  lc_mem fun _ he => pval_mem hK i ((mem_supported ℤ _).mp hx he)

theorem hOp_homog (i : Fin n) {k : ℕ} {x : Chain n} (hx : x ∈ (cGC n).homog k) :
    hOp v i x ∈ (cGC n).homog (k + 1) := by
  refine lc_mem fun e he => ?_
  have hk : e.2.card = k := (mem_supported ℤ _).mp hx he
  unfold hval
  split_ifs with hi
  · exact Submodule.zero_mem _
  · refine Submodule.smul_mem _ _ (single_mem_supported ℤ _ ?_)
    show (insert i e.2).card = k + 1
    rw [Finset.card_insert_of_notMem hi, hk]

theorem pOp_homog (i : Fin n) {k : ℕ} {x : Chain n} (hx : x ∈ (cGC n).homog k) :
    pOp v i x ∈ (cGC n).homog k := by
  refine lc_mem fun e he => ?_
  have hk : e.2.card = k := (mem_supported ℤ _).mp hx he
  unfold pval
  split_ifs with hi
  · exact Submodule.zero_mem _
  · exact single_mem_supported ℤ _ hk

theorem bd_hOp_chain (hK : IsStarAt K v) (i : Fin n) {x : Chain n}
    (hx : x ∈ supported ℤ ℤ K) : bd n (hOp v i x) + hOp v i (bd n x) = x - pOp v i x := by
  refine linearMap_congr_support (bd n ∘ₗ hOp v i + hOp v i ∘ₗ bd n) (LinearMap.id - pOp v i)
    (fun e he => ?_)
  have := bd_hOp v i e (hK e ((mem_supported ℤ _).mp hx he)).1
  simpa [hOp_single, pOp_single, bd_single] using this

theorem aug_pOp (i : Fin n) {x : Chain n} (hx : x ∈ (cGC n).homog 0) :
    (cGC n).aug (pOp v i x) = (cGC n).aug x := by
  refine linearMap_congr_support ((cGC n).aug ∘ₗ pOp v i) (cGC n).aug (fun e he => ?_)
  have hk : e.2.card = 0 := (mem_supported ℤ _).mp hx he
  have he2 : e.2 = ∅ := Finset.card_eq_zero.mp hk
  simp only [LinearMap.coe_comp, Function.comp_apply, pOp_single, pval, he2,
    Finset.notMem_empty, ↓reduceIte]
  erw [GC.aug_single, GC.aug_single]
  simp [he2]

/-- Chains whose cubes are already at `v` in the directions outside `D`. -/
def AtV (v : Fin n → ℤ) (D : Finset (Fin n)) : Set (Cube n) :=
  {e | ∀ j ∉ D, j ∉ e.2 ∧ e.1 j = v j}

theorem pOp_AtV (i : Fin n) {D : Finset (Fin n)} {x : Chain n}
    (hx : x ∈ supported ℤ ℤ (AtV v (insert i D))) : pOp v i x ∈ supported ℤ ℤ (AtV v D) := by
  refine lc_mem fun e he => ?_
  have h := (mem_supported ℤ _).mp hx he
  unfold pval
  split_ifs with hi
  · exact Submodule.zero_mem _
  · refine single_mem_supported ℤ _ fun j hj => ?_
    by_cases hji : j = i
    · subst hji; exact ⟨hi, by simp⟩
    · have := h j (by simp [hji, hj])
      exact ⟨this.1, by simp [Function.update_of_ne hji, this.2]⟩

/-- **Cubical stars are acyclic.** -/
theorem acyclic_star (hK : IsStarAt K v) : Acyclic (cGC n) K := by
  suffices H : ∀ D : Finset (Fin n), ∀ (k : ℕ) (z : Chain n), z ∈ supported ℤ ℤ K →
      z ∈ (cGC n).homog k → bd n z = 0 → (k = 0 → (cGC n).aug z = 0) →
      z ∈ supported ℤ ℤ (AtV v D) →
      ∃ y ∈ supported ℤ ℤ K, y ∈ (cGC n).homog (k + 1) ∧ bd n y = z by
    intro k z hzK hzH hzd hza
    exact H Finset.univ k z hzK hzH hzd hza
      (supported_mono (show Set.univ ⊆ AtV v Finset.univ from
        fun _ _ j hj => absurd (Finset.mem_univ j) hj) (by
        rw [supported_univ]; exact Submodule.mem_top))
  intro D
  induction D using Finset.induction_on with
  | empty =>
    intro k z _ hzH _ hza hzA
    have hsub : z.support ⊆ {((v, ∅) : Cube n)} := by
      intro e he
      have h := (mem_supported ℤ _).mp hzA he
      rw [Finset.mem_singleton]
      refine Prod.ext (funext fun j => (h j (Finset.notMem_empty j)).2) ?_
      ext j; simp [(h j (Finset.notMem_empty j)).1]
    have hz : z = single ((v, ∅) : Cube n) (z (v, ∅)) :=
      Finsupp.support_subset_singleton.mp hsub
    have h0 : z (v, ∅) = 0 := by
      by_contra hne
      have hmem : ((v, ∅) : Cube n) ∈ z.support := Finsupp.mem_support_iff.mpr hne
      have hdeg : (∅ : Finset (Fin n)).card = k := (mem_supported ℤ _).mp hzH hmem
      simp only [Finset.card_empty] at hdeg
      have ha := hza hdeg.symm
      rw [hz] at ha
      simp [GC.aug, cGC] at ha
      exact hne ha
    refine ⟨0, Submodule.zero_mem _, Submodule.zero_mem _, ?_⟩
    rw [map_zero, hz, h0, single_zero]
  | insert i D hiD ih =>
    intro k z hzK hzH hzd hza hzA
    have hp := bd_hOp_chain hK i hzK
    rw [hzd, map_zero, add_zero] at hp
    obtain ⟨y, hyK, hyH, hyz⟩ := ih k (pOp v i z) (pOp_mem hK i hzK) (pOp_homog i hzH)
      (by rw [show pOp v i z = z - bd n (hOp v i z) by rw [hp]; abel, map_sub, hzd,
        bd_bd_apply, sub_zero])
      (fun hk => by subst hk; rw [aug_pOp i hzH]; exact hza rfl)
      (pOp_AtV i hzA)
    refine ⟨y + hOp v i z, Submodule.add_mem _ hyK (hOp_mem hK i hzK),
      Submodule.add_mem _ hyH (hOp_homog i hzH), ?_⟩
    rw [map_add, hyz, show pOp v i z = z - bd n (hOp v i z) by rw [hp]; abel]
    abel

end StarAcyclic

end

end QE.Excision
