-- SPDX-License-Identifier: MIT
-- Copyright 2026 Metere Industries, Inc. Author: Alfredo Metere.
-- Quasi-Euclidean Granular Geometry. Any derivative work must carry this notice:
--   This work is derivative of the Quasi-Euclidean Granular Geometry book
--   authored by Alfredo Metere. Copyright 2026 Metere Industries, Inc.
--   All rights reserved
-- See LICENSE.md and NOTICE.

import QuasiEuclidean.Ch10_Topology

/-!
# Chapter 10, infrastructure: cubical chain complexes on `ℤⁿ`

Mathlib has no cubical homology; we build it.

* An **elementary cube** of `ℤⁿ` is a pair `(v, S)`: the corner `v : Fin n → ℤ`
  and the set `S ⊆ Fin n` of non-degenerate directions; it stands for
  `∏ᵢ [vᵢ, vᵢ + [i ∈ S]]`, of dimension `#S`.
* **Chains** are finitely supported `ℤ`-combinations of cubes,
  `Cube n →₀ ℤ`.
* The **boundary** of `(v, S)` is
  `∑_{i ∈ S} (-1)^{#{j ∈ S, j < i}} ((v + eᵢ, S∖i) - (v, S∖i))`,
  the formula `∂(I₁×⋯×Iₙ) = ∑ᵢ (-1)^{∑_{j<i} dim Iⱼ} I₁×⋯×∂Iᵢ×⋯×Iₙ` with
  `∂[k,k+1] = [k+1] - [k]`, extended linearly.
* `bd_bd : ∂ ∘ ∂ = 0`.
* For a finite cubical complex `X` (closed under faces): chain groups,
  cycles, boundaries, homology `H_k(X)`, finite generation of `H_k(X)`, and the
  **Euler–Poincaré formula** `χ(X) = ∑ₖ (-1)ᵏ rank H_k(X)` (ranks over `ℤ`).

Everything is finite linear algebra over `ℤ`; no measure theory is used.

The file also contains the digital Jordan curve theorem (Rosenfeld) for simple
closed 8-curves (two 4-components) and 4-curves (two 8-components), in the
namespace `QE.DigitalJordan`.
-/

namespace QE.Cubical

open Finset

/-- An elementary cube in `ℤⁿ`: corner `v` and set `S` of non-degenerate
directions. -/
abbrev Cube (n : ℕ) := (Fin n → ℤ) × Finset (Fin n)

/-- Dimension of an elementary cube. -/
def Cube.dim {n : ℕ} (c : Cube n) : ℕ := c.2.card

/-- The unit vector in direction `i`. -/
def unit {n : ℕ} (i : Fin n) : Fin n → ℤ := Pi.single i 1

/-- Orientation sign of the `i`-th face: `(-1)^{#{j ∈ S | j < i}}`. -/
def sgn {n : ℕ} (S : Finset (Fin n)) (i : Fin n) : ℤ :=
  (-1) ^ (S.filter (· < i)).card

/-- Cubical chains: finitely supported integer combinations of cubes. -/
abbrev Chain (n : ℕ) := Cube n →₀ ℤ

/-- Boundary of one elementary cube. -/
noncomputable def bdCube {n : ℕ} (c : Cube n) : Chain n :=
  ∑ i ∈ c.2, sgn c.2 i •
    (Finsupp.single (c.1 + unit i, c.2.erase i) 1 - Finsupp.single (c.1, c.2.erase i) 1)

/-- The cubical boundary operator, the linear extension of `bdCube`. -/
noncomputable def bd (n : ℕ) : Chain n →ₗ[ℤ] Chain n :=
  Finsupp.linearCombination ℤ bdCube

theorem bd_single {n : ℕ} (c : Cube n) : bd n (Finsupp.single c 1) = bdCube c := by
  simp [bd, Finsupp.linearCombination_single]

/-- A degenerate (zero-dimensional) cube, a vertex, has boundary `0`:
`∂[k,k] = 0`. -/
theorem bdCube_vertex {n : ℕ} (v : Fin n → ℤ) : bdCube (v, ∅) = 0 := by
  simp [bdCube]

/-- One-dimensional case: `∂[k,k+1] = [k+1] - [k]`. -/
theorem bdCube_interval (k : ℤ) :
    bdCube ((fun _ => k), ({0} : Finset (Fin 1))) =
      Finsupp.single ((fun _ => k + 1), ∅) 1 - Finsupp.single ((fun _ => k), ∅) 1 := by
  have h : ((fun _ : Fin 1 => k) + unit 0) = fun _ => k + 1 := by
    funext j; fin_cases j; simp [unit]
  simp [bdCube, sgn, h]

/-- The sign rule behind `∂² = 0`: removing two directions in the two
possible orders gives opposite signs. -/
theorem sgn_swap {n : ℕ} (S : Finset (Fin n)) (i j : Fin n) (hi : i ∈ S) (hj : j ∈ S)
    (hij : i ≠ j) :
    sgn S i * sgn (S.erase i) j = -(sgn S j * sgn (S.erase j) i) := by
  -- wlog `j < i`
  have key : ∀ a b : Fin n, a ∈ S → b ∈ S → b < a →
      sgn S a * sgn (S.erase a) b = -(sgn S b * sgn (S.erase b) a) := by
    intro a b ha hb hba
    have h1 : (S.erase a).filter (· < b) = S.filter (· < b) := by
      ext x; simp only [mem_filter, mem_erase]
      constructor
      · rintro ⟨⟨_, h⟩, h'⟩; exact ⟨h, h'⟩
      · rintro ⟨h, h'⟩; exact ⟨⟨fun e => by subst e; exact absurd (h'.trans hba) (lt_irrefl _), h⟩, h'⟩
    have h2 : (S.erase b).filter (· < a) = (S.filter (· < a)).erase b := by
      ext x; simp only [mem_filter, mem_erase]; tauto
    have hbm : b ∈ S.filter (· < a) := mem_filter.mpr ⟨hb, hba⟩
    have h3 : ((S.filter (· < a)).erase b).card + 1 = (S.filter (· < a)).card :=
      card_erase_add_one hbm
    unfold sgn
    rw [h1, h2, ← h3, pow_succ]
    ring
  rcases lt_or_gt_of_ne hij with h | h
  · have := key j i hj hi h
    linarith
  · exact key i j hi hj h

/-- An antisymmetric double sum over ordered pairs of distinct indices
vanishes. -/
theorem sum_offDiag_antisymm {ι M : Type*} [DecidableEq ι] [AddCommGroup M]
    (S : Finset ι) (f : ι → ι → M)
    (hf : ∀ i ∈ S, ∀ j ∈ S, i ≠ j → f j i = -f i j) :
    ∑ i ∈ S, ∑ j ∈ S.erase i, f i j = 0 := by
  have h : ∀ i ∈ S, ∑ j ∈ S.erase i, f i j = ∑ j ∈ S, if j ≠ i then f i j else 0 := by
    intro i _
    rw [← sum_filter, filter_ne']
  rw [sum_congr rfl h, ← sum_product' (f := fun i j => if j ≠ i then f i j else 0)]
  refine sum_involution (fun p _ => (p.2, p.1)) ?_ ?_ ?_ ?_
  · rintro ⟨i, j⟩ hp
    simp only [mem_product] at hp
    by_cases hij : j = i
    · simp [hij]
    · have hji : i ≠ j := fun e => hij e.symm
      simp only [ne_eq, hij, not_false_eq_true, ite_true, hji]
      rw [hf i hp.1 j hp.2 hji]; abel
  · rintro ⟨i, j⟩ _ hne
    intro e
    simp only [Prod.mk.injEq] at e
    apply hne
    simp [e.1]
  · rintro ⟨i, j⟩ hp
    simp only [mem_product] at hp ⊢
    exact ⟨hp.2, hp.1⟩
  · rintro ⟨i, j⟩ _; rfl

/-- The second boundary of a single cube, as a double sum over ordered pairs
of distinct directions. -/
theorem bd_bdCube {n : ℕ} (c : Cube n) :
    bd n (bdCube c) =
      ∑ i ∈ c.2, ∑ j ∈ c.2.erase i, (sgn c.2 i * sgn (c.2.erase i) j) •
        (Finsupp.single (c.1 + unit i + unit j, (c.2.erase i).erase j) 1
          - Finsupp.single (c.1 + unit i, (c.2.erase i).erase j) 1
          - Finsupp.single (c.1 + unit j, (c.2.erase i).erase j) 1
          + Finsupp.single (c.1, (c.2.erase i).erase j) 1) := by
  rcases c with ⟨v, S⟩
  simp only [bdCube, map_sum, map_zsmul, map_sub, bd_single]
  refine sum_congr rfl (fun i _ => ?_)
  rw [← sum_sub_distrib, smul_sum]
  refine sum_congr rfl (fun j _ => ?_)
  rw [mul_smul, ← smul_sub]
  congr 1
  congr 1
  abel

/-- **`∂ ∘ ∂ = 0`** on every elementary cube. -/
theorem bd_bdCube_eq_zero {n : ℕ} (c : Cube n) : bd n (bdCube c) = 0 := by
  rw [bd_bdCube]
  apply sum_offDiag_antisymm
  intro i hi j hj hij
  rw [sgn_swap c.2 j i hj hi (Ne.symm hij), neg_smul, erase_right_comm,
    add_right_comm c.1 (unit i) (unit j)]
  congr 2
  abel

/-- **The cubical boundary squares to zero: `∂ ∘ ∂ = 0`.** -/
theorem bd_bd (n : ℕ) : bd n ∘ₗ bd n = 0 := by
  apply Finsupp.lhom_ext'
  intro c
  apply LinearMap.ext_ring
  simp [bd_single, bd_bdCube_eq_zero]

theorem bd_bd_apply {n : ℕ} (x : Chain n) : bd n (bd n x) = 0 := by
  have := congrArg (fun f => f x) (bd_bd n)
  simpa using this

/-! ## Finite cubical complexes and their homology -/

section Complex

variable {n : ℕ}

/-- A finite set of elementary cubes is a **cubical complex** if it is closed
under taking the two primary faces in every non-degenerate direction (hence
under all faces). -/
def IsComplex (X : Finset (Cube n)) : Prop :=
  ∀ c ∈ X, ∀ i ∈ c.2, (c.1 + unit i, c.2.erase i) ∈ X ∧ (c.1, c.2.erase i) ∈ X

/-- The `k`-cubes of `X`. -/
def cells (X : Finset (Cube n)) (k : ℕ) : Finset (Cube n) :=
  X.filter (fun c => c.2.card = k)

/-- The chain group `C_k(X)`: integer combinations of the `k`-cubes of `X`. -/
def chains (X : Finset (Cube n)) (k : ℕ) : Submodule ℤ (Chain n) :=
  Finsupp.supported ℤ ℤ (↑(cells X k) : Set (Cube n))

theorem bdCube_mem_chains {X : Finset (Cube n)} (hX : IsComplex X) {k : ℕ} {c : Cube n}
    (hc : c ∈ cells X (k + 1)) : bdCube c ∈ chains X k := by
  simp only [cells, mem_filter] at hc
  refine Submodule.sum_mem _ (fun i hi => Submodule.smul_mem _ _ (Submodule.sub_mem _ ?_ ?_))
  · refine Finsupp.single_mem_supported ℤ _ ?_
    simp only [cells, coe_filter, Set.mem_ofPred_eq]
    exact ⟨(hX c hc.1 i hi).1, by rw [card_erase_of_mem hi, hc.2]; rfl⟩
  · refine Finsupp.single_mem_supported ℤ _ ?_
    simp only [cells, coe_filter, Set.mem_ofPred_eq]
    exact ⟨(hX c hc.1 i hi).2, by rw [card_erase_of_mem hi, hc.2]; rfl⟩

/-- The boundary maps `C_{k+1}(X)` into `C_k(X)`. -/
theorem bd_mem_chains {X : Finset (Cube n)} (hX : IsComplex X) {k : ℕ} {x : Chain n}
    (hx : x ∈ chains X (k + 1)) : bd n x ∈ chains X k := by
  have h : chains X (k + 1) ≤ (chains X k).comap (bd n) := by
    unfold chains
    rw [Finsupp.supported_eq_span_single, Submodule.span_le]
    rintro _ ⟨c, hc, rfl⟩
    simp only [SetLike.mem_coe, Submodule.mem_comap, bd_single]
    exact bdCube_mem_chains hX hc
  exact h hx

/-- The boundary vanishes on `0`-chains. -/
theorem bd_chains_zero {X : Finset (Cube n)} {x : Chain n} (hx : x ∈ chains X 0) :
    bd n x = 0 := by
  have h : chains X 0 ≤ LinearMap.ker (bd n) := by
    unfold chains
    rw [Finsupp.supported_eq_span_single, Submodule.span_le]
    rintro _ ⟨c, hc, rfl⟩
    simp only [cells, coe_filter, Set.mem_ofPred_eq, card_eq_zero] at hc
    rcases c with ⟨v, S⟩
    simp only at hc
    simp [bd_single, hc.2, bdCube_vertex]
  exact h hx

/-- The cycles `Z_k(X) = C_k(X) ∩ ker ∂`. -/
noncomputable def cycles (X : Finset (Cube n)) (k : ℕ) : Submodule ℤ (Chain n) :=
  chains X k ⊓ LinearMap.ker (bd n)

/-- The boundaries `B_k(X) = ∂ C_{k+1}(X)`. -/
noncomputable def boundaries (X : Finset (Cube n)) (k : ℕ) : Submodule ℤ (Chain n) :=
  (chains X (k + 1)).map (bd n)

/-- `B_k(X) ⊆ Z_k(X)`, a restatement of `∂² = 0`. -/
theorem boundaries_le_cycles {X : Finset (Cube n)} (hX : IsComplex X) (k : ℕ) :
    boundaries X k ≤ cycles X k := by
  rintro _ ⟨x, hx, rfl⟩
  exact ⟨bd_mem_chains hX hx, by simp [bd_bd_apply]⟩

/-- The cubical homology group `H_k(X) = Z_k(X) / B_k(X)`. -/
noncomputable abbrev homology (X : Finset (Cube n)) (k : ℕ) : Type :=
  cycles X k ⧸ (boundaries X k).comap (cycles X k).subtype

instance chains_finite (X : Finset (Cube n)) (k : ℕ) : Module.Finite ℤ (chains X k) :=
  Module.Finite.equiv (Finsupp.supportedEquivFinsupp (M := ℤ) (R := ℤ)
    (↑(cells X k) : Set (Cube n))).symm

instance cycles_finite (X : Finset (Cube n)) (k : ℕ) : Module.Finite ℤ (cycles X k) :=
  Module.Finite.of_injective (Submodule.inclusion (inf_le_left : cycles X k ≤ chains X k))
    (Submodule.inclusion_injective _)

/-- **`H_k(X)` is a finitely generated abelian group.** -/
instance homology_finite (X : Finset (Cube n)) (k : ℕ) :
    Module.Finite ℤ (homology X k) := inferInstance

theorem finrank_chains (X : Finset (Cube n)) (k : ℕ) :
    Module.finrank ℤ (chains X k) = (cells X k).card := by
  unfold chains
  rw [(Finsupp.supportedEquivFinsupp (M := ℤ) (R := ℤ)
    (↑(cells X k) : Set (Cube n))).finrank_eq, Module.finrank_finsupp_self]
  simp

/-- Rank–nullity for `∂_{k+1}`: `#X_{k+1} = rank B_k + rank Z_{k+1}`. -/
theorem card_cells_succ (X : Finset (Cube n)) (k : ℕ) :
    (cells X (k + 1)).card =
      Module.finrank ℤ (boundaries X k) + Module.finrank ℤ (cycles X (k + 1)) := by
  set φ := bd n ∘ₗ (chains X (k + 1)).subtype
  have e1 : LinearMap.range φ = boundaries X k := by
    rw [LinearMap.range_comp, Submodule.range_subtype]; rfl
  have e2 : Module.finrank ℤ (LinearMap.ker φ) = Module.finrank ℤ (cycles X (k + 1)) := by
    rw [(Submodule.equivMapOfInjective _ (chains X (k + 1)).injective_subtype
      (LinearMap.ker φ)).finrank_eq, LinearMap.ker_comp, Submodule.map_comap_subtype]
    rfl
  rw [← finrank_chains, ← φ.finrank_range_add_finrank_ker, e1, e2]

theorem card_cells_zero (X : Finset (Cube n)) :
    (cells X 0).card = Module.finrank ℤ (cycles X 0) := by
  have : cycles X 0 = chains X 0 := by
    refine le_antisymm inf_le_left (fun x hx => ⟨hx, ?_⟩)
    simp [bd_chains_zero hx]
  rw [this, finrank_chains]

/-- `rank H_k + rank B_k = rank Z_k`. -/
theorem finrank_homology {X : Finset (Cube n)} (hX : IsComplex X) (k : ℕ) :
    Module.finrank ℤ (homology X k) + Module.finrank ℤ (boundaries X k) =
      Module.finrank ℤ (cycles X k) := by
  rw [← (Submodule.comapSubtypeEquivOfLe (boundaries_le_cycles hX k)).finrank_eq]
  exact Submodule.finrank_quotient_add_finrank _

theorem cells_eq_empty (X : Finset (Cube n)) {k : ℕ} (hk : n < k) : cells X k = ∅ := by
  ext c
  simp only [cells, mem_filter, Finset.notMem_empty, iff_false, not_and]
  intro _ h
  have := card_le_univ c.2
  simp at this
  omega

/-- Telescoping identity behind Euler–Poincaré. -/
theorem telescope (c z b β : ℕ → ℕ) (h0 : c 0 = z 0) (hs : ∀ k, c (k + 1) = b k + z (k + 1))
    (hh : ∀ k, β k + b k = z k) (m : ℕ) :
    ∑ k ∈ range (m + 1), (-1 : ℤ) ^ k * c k =
      ∑ k ∈ range (m + 1), (-1 : ℤ) ^ k * β k + (-1) ^ m * b m := by
  induction m with
  | zero =>
    have := hh 0
    simp [h0]; omega
  | succ m ih =>
    rw [sum_range_succ (fun k => (-1 : ℤ) ^ k * (c k : ℤ)), ih,
      sum_range_succ (fun k => (-1 : ℤ) ^ k * (β k : ℤ)) (m + 1), hs m]
    have := hh (m + 1)
    have e : (z (m + 1) : ℤ) = β (m + 1) + b (m + 1) := by exact_mod_cast this.symm
    push_cast
    rw [e, pow_succ]
    ring

/-- The Euler characteristic of a cubical complex counts its cubes by
dimension. -/
theorem euler_eq_sum_cells (X : Finset (Cube n)) :
    QE.Topology.euler X Cube.dim = ∑ k ∈ range (n + 1), (-1 : ℤ) ^ k * (cells X k).card := by
  unfold QE.Topology.euler
  rw [← sum_fiberwise_of_maps_to (g := fun c : Cube n => c.2.card) (t := range (n + 1))]
  · refine sum_congr rfl (fun k _ => ?_)
    rw [cells, sum_congr rfl (g := fun _ => (-1 : ℤ) ^ k)]
    · simp [mul_comm]
    · intro c hc
      simp only [mem_filter] at hc
      simp [Cube.dim, hc.2]
  · intro c _
    have := card_le_univ c.2
    simp only [Fintype.card_fin] at this
    simp only [mem_range]; omega

/-- **Euler–Poincaré formula.** For every finite cubical complex `X ⊆ ℤⁿ`,
`χ(X) = ∑ₖ (-1)ᵏ rank H_k(X)`, the ranks taken over `ℤ`. -/
theorem euler_poincare {X : Finset (Cube n)} (hX : IsComplex X) :
    QE.Topology.euler X Cube.dim =
      ∑ k ∈ range (n + 1), (-1 : ℤ) ^ k * (Module.finrank ℤ (homology X k) : ℤ) := by
  rw [euler_eq_sum_cells, telescope (fun k => (cells X k).card)
    (fun k => Module.finrank ℤ (cycles X k)) (fun k => Module.finrank ℤ (boundaries X k))
    (fun k => Module.finrank ℤ (homology X k)) (card_cells_zero X) (card_cells_succ X)
    (finrank_homology hX) n]
  have hb : Module.finrank ℤ (boundaries X n) = 0 := by
    have := card_cells_succ X n
    rw [cells_eq_empty X (Nat.lt_succ_self n)] at this
    simp at this
    omega
  simp [hb]

end Complex

/-! ## Invariance of homology under elementary collapses -/

section Collapse

variable {n : ℕ}

/-- `σ` is a primary face of `c`: `σ = (c.1 + t·eᵢ, c.2 ∖ i)` for some
non-degenerate direction `i` of `c` and `t ∈ {0, 1}`. -/
def IsFace (σ c : Cube n) : Prop :=
  ∃ i ∈ c.2, ∃ t : ℤ, (t = 0 ∨ t = 1) ∧ σ = (c.1 + t • unit i, c.2.erase i)

theorem unit_ne_zero (i : Fin n) : unit i ≠ 0 := by
  intro h; have := congrFun h i; simp [unit] at this

theorem IsFace.card {σ c : Cube n} (h : IsFace σ c) : σ.2.card + 1 = c.2.card := by
  obtain ⟨i, hi, t, _, rfl⟩ := h
  exact card_erase_add_one hi

theorem not_isFace_self (c : Cube n) : ¬ IsFace c c := fun h => by
  have := h.card; omega

/-- If `σ` is not a primary face of `c`, its coefficient in `∂c` is `0`. -/
theorem bdCube_apply_of_not_isFace {σ c : Cube n} (h : ¬ IsFace σ c) : bdCube c σ = 0 := by
  unfold bdCube
  rw [Finsupp.finsetSum_apply]
  refine sum_eq_zero (fun i hi => ?_)
  have h1 : (c.1 + unit i, c.2.erase i) ≠ σ := fun e =>
    h ⟨i, hi, 1, Or.inr rfl, by rw [← e, one_smul]⟩
  have h0 : (c.1, c.2.erase i) ≠ σ := fun e =>
    h ⟨i, hi, 0, Or.inl rfl, by rw [← e, zero_smul, add_zero]⟩
  simp [h1, h0]

/-- The incidence number of a primary face is a unit: `[∂τ : σ] = ±1`. -/
theorem bdCube_apply_face {σ τ : Cube n} (h : IsFace σ τ) :
    bdCube τ σ * bdCube τ σ = 1 := by
  obtain ⟨i0, hi0, t, ht, hσ⟩ := h
  have hσ2 : σ.2 = τ.2.erase i0 := by rw [hσ]
  have hne : (τ.1 + unit i0, τ.2.erase i0) ≠ (τ.1, τ.2.erase i0) := by
    intro e
    simp only [Prod.mk.injEq, and_true] at e
    exact unit_ne_zero i0 (by simpa using e)
  have hs : sgn τ.2 i0 * sgn τ.2 i0 = 1 := by
    unfold sgn; rw [← pow_add, ← two_mul, pow_mul]; simp
  unfold bdCube
  rw [Finsupp.finsetSum_apply, sum_eq_single i0]
  · rcases ht with rfl | rfl
    · rw [zero_smul, add_zero] at hσ
      subst hσ
      simp [hne, hs]
    · rw [one_smul] at hσ
      subst hσ
      simp [hne.symm, hs]
  · intro i hi hii0
    have hS : τ.2.erase i ≠ σ.2 := by
      rw [hσ2]; intro e
      have : i0 ∈ τ.2.erase i := mem_erase.mpr ⟨Ne.symm hii0, hi0⟩
      rw [e] at this; simp at this
    have h1 : (τ.1 + unit i, τ.2.erase i) ≠ σ := fun e => hS (by rw [← e])
    have h0 : (τ.1, τ.2.erase i) ≠ σ := fun e => hS (by rw [← e])
    simp [h1, h0]
  · intro h; exact absurd hi0 h

/-- The coefficient of a free face `σ` (whose only coface in `X` is `τ`) in the
boundary of a chain on `X`. -/
theorem bd_apply_free {X : Finset (Cube n)} {σ τ : Cube n}
    (hfree : ∀ c ∈ X, IsFace σ c → c = τ) {k : ℕ} {x : Chain n} (hx : x ∈ chains X k) :
    bd n x σ = bdCube τ σ * x τ := by
  rw [bd, Finsupp.linearCombination_apply, Finsupp.sum_apply]
  unfold Finsupp.sum
  rw [sum_eq_single τ]
  · simp [mul_comm]
  · intro c hc hcτ
    have hcX : c ∈ X := by
      have := (Finsupp.mem_supported ℤ x).mp hx hc
      simp only [cells, coe_filter, Set.mem_ofPred_eq] at this
      exact this.1
    have : ¬ IsFace σ c := fun h => hcτ (hfree c hcX h)
    simp [bdCube_apply_of_not_isFace this]
  · intro h; simp [Finsupp.notMem_support_iff.mp h]

/-- Under freeness, `τ` itself is a face of no cube of `X`. -/
theorem not_isFace_coface {X : Finset (Cube n)} (hX : IsComplex X) {σ τ : Cube n}
    (hστ : IsFace σ τ) (hfree : ∀ c ∈ X, IsFace σ c → c = τ) {c : Cube n} (hc : c ∈ X) :
    ¬ IsFace τ c := by
  rintro ⟨i, hi, t, ht, rfl⟩
  obtain ⟨j, hj, s, hs, rfl⟩ := hστ
  simp only at hj
  have hji : j ≠ i := fun e => by subst e; simp at hj
  have hjc : j ∈ c.2 := (mem_erase.mp hj).2
  set c' : Cube n := (c.1 + s • unit j, c.2.erase j) with hc'
  have hc'X : c' ∈ X := by
    rw [hc']
    rcases hs with rfl | rfl
    · simpa using (hX c hc j hjc).2
    · simpa using (hX c hc j hjc).1
  have hface : IsFace (c.1 + t • unit i + s • unit j, (c.2.erase i).erase j) c' :=
    ⟨i, mem_erase.mpr ⟨Ne.symm hji, hi⟩, t, ht, by
      rw [hc']; simp only [Prod.mk.injEq]
      exact ⟨add_right_comm _ _ _, erase_right_comm⟩⟩
  have e := congrArg Prod.snd (hfree c' hc'X hface)
  simp only [hc'] at e
  have : i ∈ c.2.erase j := mem_erase.mpr ⟨Ne.symm hji, hi⟩
  rw [e] at this; simp at this

/-- The complex obtained by an elementary collapse. -/
def collapse (X : Finset (Cube n)) (σ τ : Cube n) : Finset (Cube n) := (X.erase τ).erase σ

theorem mem_collapse {X : Finset (Cube n)} {σ τ c : Cube n} :
    c ∈ collapse X σ τ ↔ c ≠ σ ∧ c ≠ τ ∧ c ∈ X := by
  simp [collapse, mem_erase]

/-- **An elementary collapse of a cubical complex is a cubical complex.** -/
theorem isComplex_collapse {X : Finset (Cube n)} (hX : IsComplex X) {σ τ : Cube n}
    (hστ : IsFace σ τ) (hfree : ∀ c ∈ X, IsFace σ c → c = τ) :
    IsComplex (collapse X σ τ) := by
  intro c hc i hi
  rw [mem_collapse] at hc
  obtain ⟨_, hcτ, hcX⟩ := hc
  have hnt := not_isFace_coface hX hστ hfree hcX
  constructor
  · rw [mem_collapse]
    refine ⟨fun e => hcτ (hfree c hcX ⟨i, hi, 1, Or.inr rfl, by rw [← e, one_smul]⟩),
      fun e => hnt ⟨i, hi, 1, Or.inr rfl, by rw [← e, one_smul]⟩, (hX c hcX i hi).1⟩
  · rw [mem_collapse]
    refine ⟨fun e => hcτ (hfree c hcX ⟨i, hi, 0, Or.inl rfl, by rw [← e, zero_smul, add_zero]⟩),
      fun e => hnt ⟨i, hi, 0, Or.inl rfl, by rw [← e, zero_smul, add_zero]⟩,
      (hX c hcX i hi).2⟩

theorem chains_mono {X Y : Finset (Cube n)} (h : X ⊆ Y) (k : ℕ) : chains X k ≤ chains Y k :=
  Finsupp.supported_mono (by
    intro c hc
    simp only [cells, coe_filter, Set.mem_ofPred_eq] at hc ⊢
    exact ⟨h hc.1, hc.2⟩)

theorem collapse_subset (X : Finset (Cube n)) (σ τ : Cube n) : collapse X σ τ ⊆ X := by
  intro c hc; exact (mem_collapse.mp hc).2.2

theorem mem_chains_collapse {X : Finset (Cube n)} {σ τ : Cube n} {k : ℕ} {x : Chain n}
    (hx : x ∈ chains X k) (hσ : x σ = 0) (hτ : x τ = 0) : x ∈ chains (collapse X σ τ) k := by
  rw [chains, Finsupp.mem_supported] at hx ⊢
  intro c hc
  have h1 := hx hc
  simp only [cells, coe_filter, Set.mem_ofPred_eq, mem_collapse] at h1 ⊢
  have hc' : x c ≠ 0 := Finsupp.mem_support_iff.mp hc
  exact ⟨⟨fun e => hc' (e ▸ hσ), fun e => hc' (e ▸ hτ), h1.1⟩, h1.2⟩

theorem apply_eq_zero_of_mem_chains {X : Finset (Cube n)} {k : ℕ} {x : Chain n}
    (hx : x ∈ chains X k) {c : Cube n} (hc : c ∉ X) : x c = 0 := by
  rw [chains, Finsupp.mem_supported'] at hx
  exact hx c (by simp [cells, hc])

/-- The correction `x̂ = x - (x_σ [∂τ:σ]) ∂τ`, which kills the `σ`-coefficient
without changing the boundary. -/
theorem correction {X : Finset (Cube n)} (hX : IsComplex X) {σ τ : Cube n} (hτX : τ ∈ X)
    (hστ : IsFace σ τ) {m : ℕ} {x : Chain n} (hx : x ∈ chains X m) :
    x - (x σ * bdCube τ σ) • bdCube τ ∈ chains X m ∧
      (x - (x σ * bdCube τ σ) • bdCube τ) σ = 0 ∧
      (x - (x σ * bdCube τ σ) • bdCube τ) τ = x τ ∧
      bd n (x - (x σ * bdCube τ σ) • bdCube τ) = bd n x := by
  have hε := bdCube_apply_face hστ
  refine ⟨?_, ?_, ?_, ?_⟩
  · by_cases h0 : x σ = 0
    · simpa [h0] using hx
    · refine Submodule.sub_mem _ hx (Submodule.smul_mem _ _ ?_)
      have hσc : σ ∈ cells X m := by
        have := (Finsupp.mem_supported ℤ x).mp hx (Finsupp.mem_support_iff.mpr h0)
        simpa using this
      have hτc : τ ∈ cells X (m + 1) := by
        simp only [cells, mem_filter] at hσc ⊢
        exact ⟨hτX, by rw [← hστ.card, hσc.2]⟩
      exact bdCube_mem_chains hX hτc
  · simp only [Finsupp.sub_apply, Finsupp.smul_apply, smul_eq_mul]
    rw [mul_assoc, hε, mul_one, sub_self]
  · simp [bdCube_apply_of_not_isFace (not_isFace_self τ)]
  · simp [bd_bdCube_eq_zero]

/-- Abstract second-isomorphism step. -/
theorem quot_iso {R M : Type*} [Ring R] [AddCommGroup M] [Module R M]
    (Z B Z' B' : Submodule R M)
    (h1 : Z' ≤ Z) (h2 : Z ≤ Z' ⊔ B) (h3 : B ≤ Z) (h4 : B' ≤ B) (h5 : B ⊓ Z' ≤ B') :
    Nonempty ((Z' ⧸ B'.comap Z'.subtype) ≃ₗ[R] (Z ⧸ B.comap Z.subtype)) := by
  have hZ : Z' ⊔ B = Z := le_antisymm (sup_le h1 h3) h2
  have hB : B'.comap Z'.subtype = Z'.comap Z'.subtype ⊓ B.comap Z'.subtype := by
    ext x
    simp only [Submodule.mem_comap, Submodule.subtype_apply, Submodule.mem_inf,
      SetLike.coe_mem, true_and]
    exact ⟨fun h => h4 h, fun h => h5 ⟨h, x.2⟩⟩
  subst hZ
  rw [hB]
  exact ⟨LinearMap.quotientInfEquivSupQuotient Z' B⟩

/-- **Homology is invariant under elementary collapses.** Let `X` be a finite
cubical complex, `τ ∈ X`, and `σ` a primary face of `τ` that is *free*: `τ` is
the only cube of `X` having `σ` as a face. Then `X ∖ {σ, τ}` is a cubical
complex and `H_k(X ∖ {σ, τ}) ≅ H_k(X)` for every `k`. -/
theorem homology_collapse {X : Finset (Cube n)} (hX : IsComplex X) {σ τ : Cube n}
    (hτX : τ ∈ X) (hστ : IsFace σ τ) (hfree : ∀ c ∈ X, IsFace σ c → c = τ)
    (k : ℕ) : Nonempty (homology (collapse X σ τ) k ≃ₗ[ℤ] homology X k) := by
  have hsub := collapse_subset X σ τ
  have hε := bdCube_apply_face hστ
  have hεne : bdCube τ σ ≠ 0 := fun e => by rw [e] at hε; simp at hε
  have hσ' : σ ∉ collapse X σ τ := fun h => (mem_collapse.mp h).1 rfl
  apply quot_iso
  · exact inf_le_inf_right _ (chains_mono hsub k)
  · rintro z ⟨hz, hbz⟩
    have hbz' : bd n z = 0 := hbz
    have hzτ : z τ = 0 := by
      have := bd_apply_free hfree hz
      rw [hbz', Finsupp.zero_apply] at this
      exact (mul_eq_zero.mp this.symm).resolve_left hεne
    obtain ⟨c1, c2, c3, c4⟩ := correction hX hτX hστ hz
    have hw : z - (z σ * bdCube τ σ) • bdCube τ ∈ cycles (collapse X σ τ) k :=
      ⟨mem_chains_collapse c1 c2 (c3.trans hzτ), by
        show _ ∈ LinearMap.ker (bd n); rw [LinearMap.mem_ker, c4, hbz']⟩
    have hb : (z σ * bdCube τ σ) • bdCube τ ∈ boundaries X k := by
      by_cases h0 : z σ = 0
      · simp [h0]
      · refine Submodule.smul_mem _ _ ⟨Finsupp.single τ 1, ?_, bd_single τ⟩
        have hσc : σ ∈ cells X k := by
          have := (Finsupp.mem_supported ℤ z).mp hz (Finsupp.mem_support_iff.mpr h0)
          simpa using this
        refine Finsupp.single_mem_supported ℤ _ ?_
        simp only [cells, coe_filter, Set.mem_ofPred_eq, mem_filter] at hσc ⊢
        exact ⟨hτX, by rw [← hστ.card, hσc.2]⟩
    have := Submodule.add_mem_sup hw hb
    simpa using this
  · exact boundaries_le_cycles hX k
  · exact Submodule.map_mono (chains_mono hsub (k + 1))
  · rintro y ⟨⟨x, hx, rfl⟩, hy, _⟩
    have hyσ : bd n x σ = 0 := apply_eq_zero_of_mem_chains hy hσ'
    have hxτ : x τ = 0 := by
      rw [bd_apply_free hfree hx] at hyσ
      exact (mul_eq_zero.mp hyσ).resolve_left hεne
    obtain ⟨c1, c2, c3, c4⟩ := correction hX hτX hστ hx
    exact ⟨_, mem_chains_collapse c1 c2 (c3.trans hxτ), c4⟩

/-- Betti numbers are invariant under elementary collapses. -/
theorem betti_collapse {X : Finset (Cube n)} (hX : IsComplex X) {σ τ : Cube n}
    (hτX : τ ∈ X) (hστ : IsFace σ τ) (hfree : ∀ c ∈ X, IsFace σ c → c = τ) (k : ℕ) :
    Module.finrank ℤ (homology (collapse X σ τ) k) = Module.finrank ℤ (homology X k) :=
  (homology_collapse hX hτX hστ hfree k).some.finrank_eq

end Collapse

end QE.Cubical

/-!
# The digital Jordan curve theorem (Rosenfeld)
-/

/-!
# The digital Jordan curve theorem (Rosenfeld)

Book: Theorem `thm:topology-jordan` (Chapter 10). Main results: `digital_jordan_8`,
`digital_jordan_4` (and the `Nat.card = 2` corollaries).

Proof: (at least two components) the crossing parity `par` of the ray to `+∞` (pushed up
infinitesimally) is invariant under complement steps (`par_step4`, `par_step8`, via exact
local identities checked by `omega`), vanishes far away and equals `1` next to the topmost
curve point; (at most two) every complement point walks horizontally to a neighbour of the
curve (`reach_edge_cell`), the neighbour ring of each curve point splits into a left and a
right side (finite checks by `decide` on ring offsets), and consecutive sides are linked.
-/

namespace QE.DigitalJordan

open Finset

/-! ## Adjacencies on `ℤ²` -/

/-- 4-adjacency: the indices differ by `±1` in exactly one coordinate. -/
def G4 : SimpleGraph (ℤ × ℤ) where
  Adj p q := |p.1 - q.1| + |p.2 - q.2| = 1
  symm := ⟨fun p q (h : |p.1 - q.1| + |p.2 - q.2| = 1) => by
    show |q.1 - p.1| + |q.2 - p.2| = 1
    rw [abs_sub_comm q.1, abs_sub_comm q.2]; exact h⟩
  loopless := ⟨fun p (h : |p.1 - p.1| + |p.2 - p.2| = 1) => by simp at h⟩

/-- 8-adjacency: the indices differ by at most `1` in every coordinate (and are distinct). -/
def G8 : SimpleGraph (ℤ × ℤ) where
  Adj p q := max |p.1 - q.1| |p.2 - q.2| = 1
  symm := ⟨fun p q (h : max |p.1 - q.1| |p.2 - q.2| = 1) => by
    show max |q.1 - p.1| |q.2 - p.2| = 1
    rw [abs_sub_comm q.1, abs_sub_comm q.2]; exact h⟩
  loopless := ⟨fun p (h : max |p.1 - p.1| |p.2 - p.2| = 1) => by simp at h⟩

instance : DecidableRel G4.Adj := fun p q =>
  inferInstanceAs (Decidable (|p.1 - q.1| + |p.2 - q.2| = 1))
instance : DecidableRel G8.Adj := fun p q =>
  inferInstanceAs (Decidable (max |p.1 - q.1| |p.2 - q.2| = 1))

theorem G4_adj {p q : ℤ × ℤ} : G4.Adj p q ↔ |p.1 - q.1| + |p.2 - q.2| = 1 := Iff.rfl
theorem G8_adj {p q : ℤ × ℤ} : G8.Adj p q ↔ max |p.1 - q.1| |p.2 - q.2| = 1 := Iff.rfl

/-- `Near p q`: the two points lie in a common `3 × 3` block centred at `q`. -/
def Near (p q : ℤ × ℤ) : Prop :=
  -1 ≤ p.1 - q.1 ∧ p.1 - q.1 ≤ 1 ∧ -1 ≤ p.2 - q.2 ∧ p.2 - q.2 ≤ 1

instance (p q : ℤ × ℤ) : Decidable (Near p q) := by unfold Near; infer_instance

theorem G4_le_G8 {p q : ℤ × ℤ} (h : G4.Adj p q) : G8.Adj p q := by
  rw [G4_adj] at h; rw [G8_adj]; simp only [abs_eq_max_neg] at *; omega

theorem near_of_G8 {p q : ℤ × ℤ} (h : G8.Adj p q) : Near q p := by
  rw [G8_adj] at h; unfold Near; simp only [abs_eq_max_neg] at *; omega

theorem near_of_G4 {p q : ℤ × ℤ} (h : G4.Adj p q) : Near q p := near_of_G8 (G4_le_G8 h)

/-! ## Simple closed curves -/

/-- A simple closed `G`-curve with `n` points: an injective cyclic sequence in which
two points are `G`-adjacent exactly when their indices are consecutive mod `n`. -/
def IsSimpleClosedCurve (G : SimpleGraph (ℤ × ℤ)) {n : ℕ} [NeZero n] (c : Fin n → ℤ × ℤ) :
    Prop :=
  Function.Injective c ∧ ∀ i j, G.Adj (c i) (c j) ↔ (j = i + 1 ∨ i = j + 1)

/-! ## The crossing parity -/

/-- The curve edge `p p'` crosses the horizontal ray from `q` to `+∞`, pushed up by an
infinitesimal amount: the edge joins row `q.2` to row `q.2 + 1`, and its endpoint on row
`q.2` lies strictly to the right of `q`. -/
def Cross (q p p' : ℤ × ℤ) : Prop :=
  (p.2 = q.2 ∧ p'.2 = q.2 + 1 ∧ q.1 < p.1) ∨ (p'.2 = q.2 ∧ p.2 = q.2 + 1 ∧ q.1 < p'.1)

instance (q p p' : ℤ × ℤ) : Decidable (Cross q p p') := by unfold Cross; infer_instance

/-- Crossing parity of `q` with respect to the closed curve `c`. -/
def par {n : ℕ} [NeZero n] (c : Fin n → ℤ × ℤ) (q : ℤ × ℤ) : ZMod 2 :=
  ∑ i, if Cross q (c i) (c (i + 1)) then 1 else 0

theorem par_eq_of_local {n : ℕ} [NeZero n] (c : Fin n → ℤ × ℤ) (q r : ℤ × ℤ)
    (S : ℤ × ℤ → Prop)
    (h : ∀ i, (Cross q (c i) (c (i + 1)) ↔ Cross r (c i) (c (i + 1))) ↔
      (S (c i) ↔ S (c (i + 1)))) : par c q = par c r := by
  classical
  have key : ∀ i, ((if Cross q (c i) (c (i + 1)) then (1 : ZMod 2) else 0) +
      (if Cross r (c i) (c (i + 1)) then 1 else 0)) =
      (if S (c i) then 1 else 0) + (if S (c (i + 1)) then 1 else 0) := by
    intro i
    have := h i
    by_cases h1 : Cross q (c i) (c (i + 1)) <;> by_cases h2 : Cross r (c i) (c (i + 1)) <;>
      by_cases h3 : S (c i) <;> by_cases h4 : S (c (i + 1)) <;> simp_all <;> decide
  have hsum : par c q + par c r = 0 := by
    unfold par
    rw [← Finset.sum_add_distrib, Finset.sum_congr rfl (fun i _ => key i),
      Finset.sum_add_distrib]
    have : ∑ i, (if S (c (i + 1)) then (1 : ZMod 2) else 0) = ∑ i, if S (c i) then 1 else 0 :=
      Fintype.sum_equiv (Equiv.addRight 1) _ _ (fun i => rfl)
    rw [this]
    generalize ∑ i, (if S (c i) then (1 : ZMod 2) else 0) = x
    revert x; decide
  revert hsum; generalize par c q = x; generalize par c r = y; revert x y; decide


theorem par_eq_of_edges {n : ℕ} [NeZero n] (c : Fin n → ℤ × ℤ) (E : ℤ × ℤ → ℤ × ℤ → Prop)
    (hedge : ∀ i, E (c i) (c (i + 1))) (S : ℤ × ℤ → Prop) (q r : ℤ × ℤ)
    (hloc : ∀ u v, E u v → u ≠ q → u ≠ r → v ≠ q → v ≠ r →
      ((Cross q u v ↔ Cross r u v) ↔ (S u ↔ S v)))
    (hq : ∀ i, c i ≠ q) (hr : ∀ i, c i ≠ r) : par c q = par c r :=
  par_eq_of_local c q r S
    (fun i => hloc _ _ (hedge i) (hq i) (hr i) (hq (i + 1)) (hr (i + 1)))

/-! Local crossing identities: moving the base point of the ray by one step changes the
crossing status of an edge exactly when the edge has one endpoint in an explicit set `S`. -/

theorem loc_h (q r u v : ℤ × ℤ) (hr1 : r.1 = q.1 + 1) (hr2 : r.2 = q.2) (huv : Near v u)
    (h1 : u ≠ q) (h2 : u ≠ r) (h3 : v ≠ q) (h4 : v ≠ r) :
    (Cross q u v ↔ Cross r u v) ↔ (False ↔ False) := by
  obtain ⟨q1, q2⟩ := q; obtain ⟨r1, r2⟩ := r; obtain ⟨u1, u2⟩ := u; obtain ⟨v1, v2⟩ := v
  simp only [Cross, Near, ne_eq, Prod.mk.injEq, iff_self, iff_true] at *
  omega

theorem loc_v (q r u v : ℤ × ℤ) (hr1 : r.1 = q.1) (hr2 : r.2 = q.2 + 1) (huv : Near v u)
    (h1 : u ≠ q) (h2 : u ≠ r) (h3 : v ≠ q) (h4 : v ≠ r) :
    (Cross q u v ↔ Cross r u v) ↔
      ((fun x : ℤ × ℤ => x.2 = q.2 + 1 ∧ q.1 < x.1) u ↔
        (fun x : ℤ × ℤ => x.2 = q.2 + 1 ∧ q.1 < x.1) v) := by
  obtain ⟨q1, q2⟩ := q; obtain ⟨r1, r2⟩ := r; obtain ⟨u1, u2⟩ := u; obtain ⟨v1, v2⟩ := v
  simp only [Cross, Near, ne_eq, Prod.mk.injEq] at *
  omega

theorem loc_d1 (q r u v : ℤ × ℤ) (hr1 : r.1 = q.1 + 1) (hr2 : r.2 = q.2 + 1) (huv : G4.Adj u v)
    (h1 : u ≠ q) (h2 : u ≠ r) (h3 : v ≠ q) (h4 : v ≠ r) :
    (Cross q u v ↔ Cross r u v) ↔
      ((fun x : ℤ × ℤ => x.2 = q.2 + 1 ∧ q.1 < x.1) u ↔
        (fun x : ℤ × ℤ => x.2 = q.2 + 1 ∧ q.1 < x.1) v) := by
  obtain ⟨q1, q2⟩ := q; obtain ⟨r1, r2⟩ := r; obtain ⟨u1, u2⟩ := u; obtain ⟨v1, v2⟩ := v
  simp only [Cross, G4_adj, abs_eq_max_neg, ne_eq, Prod.mk.injEq] at *
  omega

theorem loc_d2 (q r u v : ℤ × ℤ) (hr1 : r.1 = q.1 + 1) (hr2 : r.2 = q.2 - 1) (huv : G4.Adj u v)
    (h1 : u ≠ q) (h2 : u ≠ r) (h3 : v ≠ q) (h4 : v ≠ r) :
    (Cross q u v ↔ Cross r u v) ↔
      ((fun x : ℤ × ℤ => x.2 = q.2 ∧ q.1 < x.1) u ↔
        (fun x : ℤ × ℤ => x.2 = q.2 ∧ q.1 < x.1) v) := by
  obtain ⟨q1, q2⟩ := q; obtain ⟨r1, r2⟩ := r; obtain ⟨u1, u2⟩ := u; obtain ⟨v1, v2⟩ := v
  simp only [Cross, G4_adj, abs_eq_max_neg, ne_eq, Prod.mk.injEq] at *
  omega

/-- The crossing parity is invariant under 4-steps avoiding a curve whose consecutive points
are 8-adjacent (or 4-adjacent). -/
theorem par_step4 {n : ℕ} [NeZero n] (c : Fin n → ℤ × ℤ) (hedge : ∀ i, Near (c (i + 1)) (c i))
    (q r : ℤ × ℤ) (hq : ∀ i, c i ≠ q) (hr : ∀ i, c i ≠ r) (h : G4.Adj q r) :
    par c q = par c r := by
  have hd : (r.1 = q.1 + 1 ∧ r.2 = q.2) ∨ (q.1 = r.1 + 1 ∧ q.2 = r.2) ∨
      (r.1 = q.1 ∧ r.2 = q.2 + 1) ∨ (q.1 = r.1 ∧ q.2 = r.2 + 1) := by
    rw [G4_adj] at h; simp only [abs_eq_max_neg] at h; omega
  have hE : ∀ i, (fun u v => Near v u) (c i) (c (i + 1)) := hedge
  rcases hd with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact par_eq_of_edges c _ hE _ q r (fun u v huv => loc_h q r u v h1 h2 huv) hq hr
  · exact (par_eq_of_edges c _ hE _ r q (fun u v huv => loc_h r q u v h1 h2 huv) hr hq).symm
  · exact par_eq_of_edges c _ hE _ q r (fun u v huv => loc_v q r u v h1 h2 huv) hq hr
  · exact (par_eq_of_edges c _ hE _ r q (fun u v huv => loc_v r q u v h1 h2 huv) hr hq).symm

/-- The crossing parity is invariant under 8-steps avoiding a curve whose consecutive points
are 4-adjacent. -/
theorem par_step8 {n : ℕ} [NeZero n] (c : Fin n → ℤ × ℤ) (hedge : ∀ i, G4.Adj (c i) (c (i + 1)))
    (q r : ℤ × ℤ) (hq : ∀ i, c i ≠ q) (hr : ∀ i, c i ≠ r) (h : G8.Adj q r) :
    par c q = par c r := by
  have hd : (r.1 = q.1 + 1 ∧ r.2 = q.2) ∨ (q.1 = r.1 + 1 ∧ q.2 = r.2) ∨
      (r.1 = q.1 ∧ r.2 = q.2 + 1) ∨ (q.1 = r.1 ∧ q.2 = r.2 + 1) ∨
      (r.1 = q.1 + 1 ∧ r.2 = q.2 + 1) ∨ (q.1 = r.1 + 1 ∧ q.2 = r.2 + 1) ∨
      (r.1 = q.1 + 1 ∧ r.2 = q.2 - 1) ∨ (q.1 = r.1 + 1 ∧ q.2 = r.2 - 1) := by
    rw [G8_adj] at h; simp only [abs_eq_max_neg] at h; omega
  have hN : ∀ i, (fun u v => Near v u) (c i) (c (i + 1)) := fun i => near_of_G4 (hedge i)
  have hE : ∀ i, G4.Adj (c i) (c (i + 1)) := hedge
  rcases hd with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ |
    ⟨h1, h2⟩
  · exact par_eq_of_edges c _ hN _ q r (fun u v huv => loc_h q r u v h1 h2 huv) hq hr
  · exact (par_eq_of_edges c _ hN _ r q (fun u v huv => loc_h r q u v h1 h2 huv) hr hq).symm
  · exact par_eq_of_edges c _ hN _ q r (fun u v huv => loc_v q r u v h1 h2 huv) hq hr
  · exact (par_eq_of_edges c _ hN _ r q (fun u v huv => loc_v r q u v h1 h2 huv) hr hq).symm
  · exact par_eq_of_edges c _ hE _ q r (fun u v huv => loc_d1 q r u v h1 h2 huv) hq hr
  · exact (par_eq_of_edges c _ hE _ r q (fun u v huv => loc_d1 r q u v h1 h2 huv) hr hq).symm
  · exact par_eq_of_edges c _ hE _ q r (fun u v huv => loc_d2 q r u v h1 h2 huv) hq hr
  · exact (par_eq_of_edges c _ hE _ r q (fun u v huv => loc_d2 r q u v h1 h2 huv) hr hq).symm


/-! ## Reachability in the complement -/

/-- One step inside the complement of `C`. -/
def CStep (G : SimpleGraph (ℤ × ℤ)) (C : Set (ℤ × ℤ)) (x y : ℤ × ℤ) : Prop :=
  x ∉ C ∧ y ∉ C ∧ G.Adj x y

/-- Reachability inside the complement of `C`. -/
abbrev CR (G : SimpleGraph (ℤ × ℤ)) (C : Set (ℤ × ℤ)) : ℤ × ℤ → ℤ × ℤ → Prop :=
  Relation.ReflTransGen (CStep G C)

theorem CR_symm {G : SimpleGraph (ℤ × ℤ)} {C : Set (ℤ × ℤ)} {x y : ℤ × ℤ} (h : CR G C x y) :
    CR G C y x :=
  by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hs ih =>
    exact Relation.ReflTransGen.head ⟨hs.2.1, hs.1, hs.2.2.symm⟩ ih

theorem CR_mem {G : SimpleGraph (ℤ × ℤ)} {C : Set (ℤ × ℤ)} {x y : ℤ × ℤ} (h : CR G C x y)
    (hx : x ∉ C) : y ∉ C := by
  induction h with
  | refl => exact hx
  | tail _ hs _ => exact hs.2.1

theorem CR_step {G : SimpleGraph (ℤ × ℤ)} {C : Set (ℤ × ℤ)} {x y : ℤ × ℤ} (hx : x ∉ C)
    (hy : y ∉ C) (h : G.Adj x y) : CR G C x y :=
  Relation.ReflTransGen.single ⟨hx, hy, h⟩

theorem par_of_CR {n : ℕ} [NeZero n] (c : Fin n → ℤ × ℤ) (G : SimpleGraph (ℤ × ℤ))
    (hstep : ∀ x y, (∀ i, c i ≠ x) → (∀ i, c i ≠ y) → G.Adj x y → par c x = par c y)
    {x y : ℤ × ℤ} (h : CR G (Set.range c) x y) : par c x = par c y := by
  induction h with
  | refl => rfl
  | tail _ hs ih =>
    exact ih.trans (hstep _ _ (fun i hi => hs.1 ⟨i, hi⟩) (fun i hi => hs.2.1 ⟨i, hi⟩) hs.2.2)

/-! ## Walking along lattice lines -/

/-- The point `q + t • e`. -/
def line (q e : ℤ × ℤ) (t : ℕ) : ℤ × ℤ := (q.1 + t * e.1, q.2 + t * e.2)

@[simp] theorem line_zero (q e : ℤ × ℤ) : line q e 0 = q := by simp [line]

theorem reach_line {G : SimpleGraph (ℤ × ℤ)} (hG : ∀ x y, G4.Adj x y → G.Adj x y)
    {C : Set (ℤ × ℤ)} (q e : ℤ × ℤ) (he : |e.1| + |e.2| = 1) :
    ∀ t : ℕ, (∀ s ≤ t, line q e s ∉ C) → CR G C q (line q e t) := by
  intro t
  induction t with
  | zero => intro _; simp; exact Relation.ReflTransGen.refl
  | succ t ih =>
    intro h
    refine Relation.ReflTransGen.tail (ih (fun s hs => h s (by omega)))
      ⟨h t (by omega), h (t + 1) le_rfl, hG _ _ ?_⟩
    rw [G4_adj]
    have e1 : (line q e t).1 - (line q e (t + 1)).1 = -e.1 := by simp [line]; ring
    have e2 : (line q e t).2 - (line q e (t + 1)).2 = -e.2 := by simp [line]; ring
    rw [e1, e2, abs_neg, abs_neg, he]

theorem hit_line {G : SimpleGraph (ℤ × ℤ)} (hG : ∀ x y, G4.Adj x y → G.Adj x y)
    {C : Set (ℤ × ℤ)} (q e : ℤ × ℤ) (he : |e.1| + |e.2| = 1) (hq : q ∉ C) (m : ℕ)
    (hm : line q e m ∈ C) : ∃ s, CR G C q (line q e s) ∧ line q e (s + 1) ∈ C := by
  classical
  have hm0 : m ≠ 0 := by rintro rfl; simp at hm; exact hq hm
  have hex : ∃ t, line q e (t + 1) ∈ C := ⟨m - 1, by rwa [Nat.sub_add_cancel (by omega)]⟩
  refine ⟨Nat.find hex, reach_line hG q e he _ ?_, Nat.find_spec hex⟩
  intro s hs
  rcases s with _ | k
  · simpa using hq
  · exact Nat.find_min hex (show k < Nat.find hex by omega)

/-- A bound on all coordinates of the curve. -/
def bnd {n : ℕ} (c : Fin n → ℤ × ℤ) : ℤ := ∑ i, (|(c i).1| + |(c i).2|)

theorem bnd_spec {n : ℕ} (c : Fin n → ℤ × ℤ) (i : Fin n) :
    |(c i).1| ≤ bnd c ∧ |(c i).2| ≤ bnd c := by
  have h := Finset.single_le_sum (f := fun i => |(c i).1| + |(c i).2|)
    (fun i _ => by positivity) (Finset.mem_univ i)
  have := abs_nonneg (c i).1; have := abs_nonneg (c i).2
  simp only [bnd] at *
  constructor <;> linarith

theorem reach_free {G : SimpleGraph (ℤ × ℤ)} (hG : ∀ x y, G4.Adj x y → G.Adj x y)
    {C : Set (ℤ × ℤ)} (q e : ℤ × ℤ) (he : |e.1| + |e.2| = 1) (hfree : ∀ s, line q e s ∉ C)
    (t : ℕ) : CR G C q (line q e t) :=
  reach_line hG q e he t (fun s _ => hfree s)

/-- Vertical walk in a column free of curve points. -/
theorem col_reach {G : SimpleGraph (ℤ × ℤ)} (hG : ∀ x y, G4.Adj x y → G.Adj x y)
    {C : Set (ℤ × ℤ)} (q : ℤ × ℤ) (hcol : ∀ p ∈ C, p.1 ≠ q.1) (y : ℤ) :
    CR G C q (q.1, y) := by
  rcases le_or_gt q.2 y with h | h
  · have := reach_free hG (C := C) q (0, 1) (by norm_num)
      (fun s hs => hcol _ hs (by simp [line])) (y - q.2).toNat
    convert this using 1; ext <;> simp [line]; omega
  · have := reach_free hG (C := C) q (0, -1) (by norm_num)
      (fun s hs => hcol _ hs (by simp [line])) (q.2 - y).toNat
    convert this using 1; ext <;> simp [line]; omega

/-- Horizontal walk in a row free of curve points. -/
theorem row_reach {G : SimpleGraph (ℤ × ℤ)} (hG : ∀ x y, G4.Adj x y → G.Adj x y)
    {C : Set (ℤ × ℤ)} (q : ℤ × ℤ) (hrow : ∀ p ∈ C, p.2 ≠ q.2) (x : ℤ) :
    CR G C q (x, q.2) := by
  rcases le_or_gt q.1 x with h | h
  · have := reach_free hG (C := C) q (1, 0) (by norm_num)
      (fun s hs => hrow _ hs (by simp [line])) (x - q.1).toNat
    convert this using 1; ext <;> simp [line]; omega
  · have := reach_free hG (C := C) q (-1, 0) (by norm_num)
      (fun s hs => hrow _ hs (by simp [line])) (q.1 - x).toNat
    convert this using 1; ext <;> simp [line]; omega

/-- **Every complement point reaches a horizontal neighbour of the curve.** -/
theorem reach_edge_cell {n : ℕ} [NeZero n] (c : Fin n → ℤ × ℤ) {G : SimpleGraph (ℤ × ℤ)}
    (hG : ∀ x y, G4.Adj x y → G.Adj x y) (q : ℤ × ℤ) (hq : q ∉ Set.range c) :
    ∃ j, CR G (Set.range c) q ((c j).1 - 1, (c j).2) ∨
      CR G (Set.range c) q ((c j).1 + 1, (c j).2) := by
  -- walking right from `r` until the curve is hit
  have goR : ∀ r, r ∉ Set.range c → ∀ j, (c j).2 = r.2 → r.1 < (c j).1 →
      ∃ j', CR G (Set.range c) r ((c j').1 - 1, (c j').2) := by
    intro r hr j h1 h2
    obtain ⟨s, hs, j', hj'⟩ := hit_line hG (C := Set.range c) r (1, 0) (by norm_num) hr
      ((c j).1 - r.1).toNat ⟨j, by ext <;> simp [line] <;> omega⟩
    refine ⟨j', ?_⟩
    convert hs using 1
    have := congrArg Prod.fst hj'; have := congrArg Prod.snd hj'
    ext <;> simp [line] at * <;> omega
  have goL : ∀ r, r ∉ Set.range c → ∀ j, (c j).2 = r.2 → (c j).1 < r.1 →
      ∃ j', CR G (Set.range c) r ((c j').1 + 1, (c j').2) := by
    intro r hr j h1 h2
    obtain ⟨s, hs, j', hj'⟩ := hit_line hG (C := Set.range c) r (-1, 0) (by norm_num) hr
      (r.1 - (c j).1).toNat ⟨j, by ext <;> simp [line] <;> omega⟩
    refine ⟨j', ?_⟩
    convert hs using 1
    have := congrArg Prod.fst hj'; have := congrArg Prod.snd hj'
    ext <;> simp [line] at * <;> omega
  by_cases hR : ∃ j, (c j).2 = q.2 ∧ q.1 < (c j).1
  · obtain ⟨j, h1, h2⟩ := hR
    obtain ⟨j', h⟩ := goR q hq j h1 h2
    exact ⟨j', Or.inl h⟩
  by_cases hL : ∃ j, (c j).2 = q.2 ∧ (c j).1 < q.1
  · obtain ⟨j, h1, h2⟩ := hL
    obtain ⟨j', h⟩ := goL q hq j h1 h2
    exact ⟨j', Or.inr h⟩
  push Not at hR hL
  have hrow : ∀ p ∈ Set.range c, p.2 ≠ q.2 := by
    rintro p ⟨j, rfl⟩ h
    have := hR j h; have := hL j h
    exact hq ⟨j, Prod.ext (by omega) h⟩
  have h1 := row_reach hG q hrow (bnd c + 1)
  have hcol : ∀ p ∈ Set.range c, p.1 ≠ (bnd c + 1, q.2).1 := by
    rintro p ⟨j, rfl⟩ h
    have := (bnd_spec c j).1; rw [abs_le] at this; simp at h; omega
  have h2 := col_reach hG _ hcol (c 0).2
  have hm : ((bnd c + 1, q.2).1, (c 0).2) ∉ Set.range c := by
    rintro ⟨j, hj⟩; exact hcol _ ⟨j, rfl⟩ (by rw [hj])
  obtain ⟨j', h3⟩ := goL _ hm 0 rfl (by
    have := (bnd_spec c 0).1; rw [abs_le] at this; simp; omega)
  exact ⟨j', Or.inr (h1.trans (h2.trans h3))⟩


/-! ## Index arithmetic on `Fin n` -/

/-- `addN i k = i + 1 + ⋯ + 1` (`k` times). -/
def addN {n : ℕ} [NeZero n] (i : Fin n) : ℕ → Fin n
  | 0 => i
  | k + 1 => addN i k + 1

theorem addN_val {n : ℕ} [NeZero n] (i : Fin n) (k : ℕ) : (addN i k).val = (i.val + k) % n := by
  induction k with
  | zero => simp [addN, Nat.mod_eq_of_lt i.isLt]
  | succ k ih =>
    simp only [addN, Fin.val_add, ih, Fin.val_one']
    rw [← add_assoc, Nat.add_mod (↑i + k) 1]

theorem addN_ne {n : ℕ} [NeZero n] (i : Fin n) {a b : ℕ} (hab : a ≠ b) (ha : a < n)
    (hb : b < n) : addN i a ≠ addN i b := by
  intro h
  have h' := congrArg Fin.val h
  rw [addN_val, addN_val] at h'
  have := Nat.ModEq.add_left_cancel' i.val h'
  unfold Nat.ModEq at this
  rw [Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at this
  exact hab this

theorem addN_zero_val {n : ℕ} [NeZero n] (i : Fin n) : addN 0 i.val = i := by
  ext; rw [addN_val]; simp [Nat.mod_eq_of_lt i.isLt]

/-! ## The eight neighbours of a lattice point -/

/-- The eight neighbour offsets, in counterclockwise order starting east. -/
def ring : Fin 8 → ℤ × ℤ := ![(1, 0), (1, 1), (0, 1), (-1, 1), (-1, 0), (-1, -1), (0, -1), (1, -1)]

/-- Inverse of `ring` on the eight offsets. -/
def offIdx (d : ℤ × ℤ) : Fin 8 :=
  if d = (1, 0) then 0 else if d = (1, 1) then 1 else if d = (0, 1) then 2 else
  if d = (-1, 1) then 3 else if d = (-1, 0) then 4 else if d = (-1, -1) then 5 else
  if d = (0, -1) then 6 else 7

theorem offIdx_ring : ∀ k : Fin 8, offIdx (ring k) = k := by decide

theorem ring_inj {k m : Fin 8} (h : ring k = ring m) : k = m := by
  rw [← offIdx_ring k, h, offIdx_ring]

theorem offIdx_neg : ∀ k : Fin 8, offIdx (-ring k) = k + 4 := by decide

theorem G8_ring {p q : ℤ × ℤ} (h : G8.Adj p q) : q = p + ring (offIdx (q - p)) := by
  obtain ⟨p1, p2⟩ := p; obtain ⟨q1, q2⟩ := q
  simp only [G8_adj, abs_eq_max_neg] at h
  have h1 : q1 - p1 = -1 ∨ q1 - p1 = 0 ∨ q1 - p1 = 1 := by omega
  have h2 : q2 - p2 = -1 ∨ q2 - p2 = 0 ∨ q2 - p2 = 1 := by omega
  rcases h1 with h1 | h1 | h1 <;> rcases h2 with h2 | h2 | h2 <;>
    simp [Prod.mk_sub_mk, h1, h2, offIdx, ring, Prod.ext_iff] <;> omega

theorem G4_offIdx_even {p q : ℤ × ℤ} (h : G4.Adj p q) : (offIdx (q - p)).val % 2 = 0 := by
  obtain ⟨p1, p2⟩ := p; obtain ⟨q1, q2⟩ := q
  simp only [G4_adj, abs_eq_max_neg] at h
  have h1 : (q1 - p1 = -1 ∧ q2 - p2 = 0) ∨ (q1 - p1 = 1 ∧ q2 - p2 = 0) ∨
    (q1 - p1 = 0 ∧ q2 - p2 = -1) ∨ (q1 - p1 = 0 ∧ q2 - p2 = 1) := by omega
  rcases h1 with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
    simp [Prod.mk_sub_mk, h1, h2, offIdx]

theorem ring_G8 : ∀ k : Fin 8, max |(ring k).1| |(ring k).2| = 1 := by decide
theorem ring_G4 : ∀ k : Fin 8, k.val % 2 = 0 → |(ring k).1| + |(ring k).2| = 1 := by decide

theorem G8_add_ring (p : ℤ × ℤ) (k : Fin 8) : G8.Adj p (p + ring k) := by
  rw [G8_adj]; simpa [abs_neg] using ring_G8 k

theorem G4_add_ring (p : ℤ × ℤ) (k : Fin 8) (hk : k.val % 2 = 0) : G4.Adj p (p + ring k) := by
  rw [G4_adj]; simpa [abs_neg] using ring_G4 k hk

theorem G4_add_iff (p u v : ℤ × ℤ) : G4.Adj (p + u) (p + v) ↔ G4.Adj u v := by
  simp [G4_adj, add_sub_add_left_eq_sub]

theorem G8_add_iff (p u v : ℤ × ℤ) : G8.Adj (p + u) (p + v) ↔ G8.Adj u v := by
  simp [G8_adj, add_sub_add_left_eq_sub]

theorem near_add_iff (p u v : ℤ × ℤ) : Near (p + u) (p + v) ↔ Near u v := by
  simp [Near, add_sub_add_left_eq_sub]

theorem G8_iff_near (u v : ℤ × ℤ) : G8.Adj u v ↔ Near u v ∧ u ≠ v := by
  obtain ⟨u1, u2⟩ := u; obtain ⟨v1, v2⟩ := v
  simp only [G8_adj, Near, abs_eq_max_neg, ne_eq, Prod.mk.injEq]
  omega

/-! ## Arcs of the neighbour ring -/

/-- `k` lies strictly between `b` and `a` going counterclockwise from `b`. -/
def arcL (b a k : Fin 8) : Prop := k ≠ b ∧ k ≠ a ∧ (k - b).val < (a - b).val

instance (b a k : Fin 8) : Decidable (arcL b a k) := by unfold arcL; infer_instance

theorem link8L : ∀ α β δ : Fin 8, ¬ Near (ring α) (ring β) → ¬ Near (ring β + ring δ) 0 →
    ∃ k m, arcL β α k ∧ arcL δ (β + 4) m ∧ ring k = ring β + ring m := by decide
theorem link8R : ∀ α β δ : Fin 8, ¬ Near (ring α) (ring β) → ¬ Near (ring β + ring δ) 0 →
    ∃ k m, arcL α β k ∧ arcL (β + 4) δ m ∧ ring k = ring β + ring m := by decide

/-- For a 4-curve, the guaranteed complement cells of an arc: its edge cells, or its corner
when the arc is a single corner. -/
def Side4 (b a k : Fin 8) : Prop := arcL b a k ∧ (k.val % 2 = 0 ∨ (a - b).val = 2)

instance (b a k : Fin 8) : Decidable (Side4 b a k) := by unfold Side4; infer_instance

theorem link4L : ∀ α β δ : Fin 8, α.val % 2 = 0 → β.val % 2 = 0 → δ.val % 2 = 0 → α ≠ β →
    δ ≠ β + 4 → ∃ k m, Side4 β α k ∧ Side4 δ (β + 4) m ∧ Near (ring k) (ring β + ring m) := by
  decide
theorem link4R : ∀ α β δ : Fin 8, α.val % 2 = 0 → β.val % 2 = 0 → δ.val % 2 = 0 → α ≠ β →
    δ ≠ β + 4 → ∃ k m, Side4 α β k ∧ Side4 (β + 4) δ m ∧ Near (ring k) (ring β + ring m) := by
  decide

/-- The representative cell of a 4-curve side. -/
def rep4 (b a : Fin 8) : Fin 8 := if (a - b).val = 2 then b + 1 else b + 2

theorem side4_rep : ∀ b a : Fin 8, b.val % 2 = 0 → a.val % 2 = 0 → a ≠ b →
    Side4 b a (rep4 b a) := by decide
theorem side4_conn : ∀ b a k : Fin 8, b.val % 2 = 0 → a.val % 2 = 0 → Side4 b a k →
    k = rep4 b a ∨ (Near (ring k) (ring (rep4 b a)) ∧ k ≠ rep4 b a) := by decide
theorem side4_corner : ∀ b a k : Fin 8, b.val % 2 = 0 → a.val % 2 = 0 → Side4 b a k →
    k.val % 2 ≠ 0 → |(ring k - ring a).1| + |(ring k - ring a).2| = 1 ∧
      |(ring k - ring b).1| + |(ring k - ring b).2| = 1 := by decide
theorem arc_first : ∀ b a k : Fin 8, arcL b a k → arcL b a (b + 1) := by decide
theorem arc_pred : ∀ b a k : Fin 8, arcL b a k → k ≠ b + 1 →
    arcL b a (k - 1) ∧ (k - 1 - b).val + 1 = (k - b).val := by decide
theorem ring_unit : ∀ k : Fin 8,
    |(ring k - ring (k - 1)).1| + |(ring k - ring (k - 1)).2| = 1 := by decide
theorem arc8_even : ∀ α β : Fin 8, ¬ Near (ring α) (ring β) →
    ∃ k, arcL β α k ∧ k.val % 2 = 0 := by decide
theorem arc_cover : ∀ α β k : Fin 8, α ≠ β → k ≠ α → k ≠ β → arcL β α k ∨ arcL α β k := by
  decide
theorem ring_ne_zero : ∀ k : Fin 8, ring k ≠ 0 := by decide
theorem ring4 : ring 4 = (-1, 0) := rfl
theorem ring0 : ring 0 = (1, 0) := rfl


theorem near_comm {u v : ℤ × ℤ} : Near u v ↔ Near v u := by unfold Near; omega

/-! ## Elementary consequences of simplicity -/

section CurveFacts

variable {G : SimpleGraph (ℤ × ℤ)} {n : ℕ} [NeZero n] {c : Fin n → ℤ × ℤ}

theorem curve_adj_succ (hc : IsSimpleClosedCurve G c) (i : Fin n) : G.Adj (c i) (c (i + 1)) :=
  (hc.2 i (i + 1)).2 (Or.inl rfl)

theorem curve_nbr (hc : IsSimpleClosedCurve G c) (i j : Fin n) (h : G.Adj (c (i + 1)) (c j)) :
    j = i ∨ j = i + 1 + 1 := by
  rcases (hc.2 _ _).1 h with h | h
  · exact Or.inr h
  · exact Or.inl (add_right_cancel h).symm

theorem curve_nonadj2 (hc : IsSimpleClosedCurve G c) (hn : 4 ≤ n) (i : Fin n) :
    ¬ G.Adj (c i) (c (i + 1 + 1)) := by
  intro h
  rcases (hc.2 _ _).1 h with h | h
  · exact addN_ne i (a := 2) (b := 1) (by omega) (by omega) (by omega) h
  · exact addN_ne i (a := 0) (b := 3) (by omega) (by omega) (by omega) h

theorem curve_ne2 (hc : IsSimpleClosedCurve G c) (hn : 3 ≤ n) (i : Fin n) :
    c i ≠ c (i + 1 + 1) := fun h =>
  addN_ne i (a := 0) (b := 2) (by omega) (by omega) (by omega) (hc.1 h)

/-- Offset (ring index) of the predecessor `c i` seen from `c (i+1)`. -/
def αo (c : Fin n → ℤ × ℤ) (i : Fin n) : Fin 8 := offIdx (c i - c (i + 1))
/-- Offset (ring index) of the successor `c (i+2)` seen from `c (i+1)`. -/
def βo (c : Fin n → ℤ × ℤ) (i : Fin n) : Fin 8 := offIdx (c (i + 1 + 1) - c (i + 1))

variable (hcons : ∀ i, G8.Adj (c i) (c (i + 1)))
include hcons

theorem c_pred (i : Fin n) : c i = c (i + 1) + ring (αo c i) := G8_ring (hcons i).symm

theorem c_succ (i : Fin n) : c (i + 1 + 1) = c (i + 1) + ring (βo c i) := G8_ring (hcons (i + 1))

theorem αo_succ (i : Fin n) : αo c (i + 1) = βo c i + 4 := by
  unfold αo
  have : c (i + 1) - c (i + 1 + 1) = -ring (βo c i) := by
    rw [c_succ hcons i]; abel
  rw [this, offIdx_neg]

theorem αo_ne_βo (hc : IsSimpleClosedCurve G c) (hn : 3 ≤ n) (i : Fin n) : αo c i ≠ βo c i := by
  intro h
  apply curve_ne2 hc hn i
  rw [c_pred hcons i, c_succ hcons i, h]

end CurveFacts

/-! ## Chains along arcs -/

theorem arc_chain {G : SimpleGraph (ℤ × ℤ)} (hG : ∀ x y, G4.Adj x y → G.Adj x y)
    (C : Set (ℤ × ℤ)) (p : ℤ × ℤ) (b a : Fin 8)
    (hfree : ∀ k, arcL b a k → p + ring k ∉ C) :
    ∀ k, arcL b a k → CR G C (p + ring k) (p + ring (b + 1)) := by
  suffices h : ∀ m k, (k - b).val = m → arcL b a k → CR G C (p + ring k) (p + ring (b + 1)) from
    fun k hk => h _ k rfl hk
  intro m
  induction m with
  | zero =>
    intro k hk harc
    exact absurd (sub_eq_zero.mp (Fin.ext hk)) harc.1
  | succ m ih =>
    intro k hk harc
    by_cases hb : k = b + 1
    · subst hb; exact Relation.ReflTransGen.refl
    · obtain ⟨h1, h2⟩ := arc_pred b a k harc hb
      refine Relation.ReflTransGen.head ⟨hfree k harc, hfree _ h1, hG _ _ ?_⟩
        (ih (k - 1) (by omega) h1)
      rw [G4_add_iff, G4_adj]
      simpa using ring_unit k


/-! ## Local sides of a simple closed 8-curve -/

section Eight

variable {n : ℕ} [NeZero n] {c : Fin n → ℤ × ℤ}

/-- The left (`s = true`) / right (`s = false`) arc of the neighbour ring of `c (i+1)`,
cut by the two curve neighbours `c i` and `c (i+2)`. -/
def arc8 (c : Fin n → ℤ × ℤ) (i : Fin n) (s : Bool) (k : Fin 8) : Prop :=
  if s then arcL (βo c i) (αo c i) k else arcL (αo c i) (βo c i) k

/-- Representative cell of a side. -/
def rep8 (c : Fin n → ℤ × ℤ) (i : Fin n) (s : Bool) : ℤ × ℤ :=
  c (i + 1) + ring (if s then βo c i + 1 else αo c i + 1)

theorem arc8_ne {i : Fin n} {s : Bool} {k : Fin 8} (h : arc8 c i s k) :
    k ≠ αo c i ∧ k ≠ βo c i := by
  cases s <;> simp only [arc8, Bool.false_eq_true, ite_false, ite_true] at h
  · exact ⟨h.1, h.2.1⟩
  · exact ⟨h.2.1, h.1⟩

variable (hc : IsSimpleClosedCurve G8 c) (hn : 4 ≤ n)
include hc

theorem ring_notin8 {i : Fin n} {k : Fin 8} (hα : k ≠ αo c i) (hβ : k ≠ βo c i) :
    c (i + 1) + ring k ∉ Set.range c := by
  rintro ⟨j, hj⟩
  have hadj : G8.Adj (c (i + 1)) (c j) := hj ▸ G8_add_ring _ _
  rcases curve_nbr hc i j hadj with rfl | rfl
  · exact hα (ring_inj (add_left_cancel (hj.symm.trans (c_pred (curve_adj_succ hc) j))))
  · exact hβ (ring_inj (add_left_cancel (hj.symm.trans (c_succ (curve_adj_succ hc) i))))

theorem arc8_reach (i : Fin n) (s : Bool) (k : Fin 8) (h : arc8 c i s k) :
    CR G4 (Set.range c) (c (i + 1) + ring k) (rep8 c i s) := by
  have hfree : ∀ k, arc8 c i s k → c (i + 1) + ring k ∉ Set.range c := fun k hk =>
    ring_notin8 hc (arc8_ne hk).1 (arc8_ne hk).2
  cases s
  · exact arc_chain (fun _ _ h => h) _ _ _ _ hfree k h
  · exact arc_chain (fun _ _ h => h) _ _ _ _ hfree k h

include hn

theorem not_near_ab (i : Fin n) : ¬ Near (ring (αo c i)) (ring (βo c i)) := by
  intro h
  have h' : Near (c i) (c (i + 1 + 1)) := by
    rw [c_pred (curve_adj_succ hc) i, c_succ (curve_adj_succ hc) i, near_add_iff]; exact h
  exact curve_nonadj2 hc hn i ((G8_iff_near _ _).2 ⟨h', curve_ne2 hc (by omega) i⟩)

theorem not_near_pd (i : Fin n) : ¬ Near (ring (βo c i) + ring (βo c (i + 1))) 0 := by
  intro h
  have h' : Near (c (i + 1 + 1 + 1)) (c (i + 1)) := by
    rw [c_succ (curve_adj_succ hc) (i + 1), c_succ (curve_adj_succ hc) i, add_assoc]
    have := (near_add_iff (c (i + 1)) (ring (βo c i) + ring (βo c (i + 1))) 0).2 h
    rwa [add_zero] at this
  exact curve_nonadj2 hc hn (i + 1)
    ((G8_iff_near _ _).2 ⟨near_comm.1 h', curve_ne2 hc (by omega) (i + 1)⟩)

theorem side8_adj (i : Fin n) (s : Bool) :
    ∃ x, x ∉ Set.range c ∧ G4.Adj (c (i + 1)) x ∧ CR G4 (Set.range c) x (rep8 c i s) := by
  have hab := not_near_ab hc hn i
  have hba : ¬ Near (ring (βo c i)) (ring (αo c i)) := fun h => hab (near_comm.1 h)
  obtain ⟨k, hk, hev⟩ : ∃ k, arc8 c i s k ∧ k.val % 2 = 0 := by
    cases s
    · simpa [arc8] using arc8_even (βo c i) (αo c i) hba
    · simpa [arc8] using arc8_even (αo c i) (βo c i) hab
  exact ⟨_, ring_notin8 hc (arc8_ne hk).1 (arc8_ne hk).2, G4_add_ring _ _ hev,
    arc8_reach hc i s k hk⟩

theorem side8_link (i : Fin n) (s : Bool) :
    CR G4 (Set.range c) (rep8 c i s) (rep8 c (i + 1) s) := by
  have hcons := curve_adj_succ hc
  have hab := not_near_ab hc hn i
  have hpd := not_near_pd hc hn i
  have hα := αo_succ hcons i
  obtain ⟨k, m, hk, hm, hkm⟩ : ∃ k m, arc8 c i s k ∧ arc8 c (i + 1) s m ∧
      ring k = ring (βo c i) + ring m := by
    cases s
    · obtain ⟨k, m, h1, h2, h3⟩ := link8R _ _ _ hab hpd
      exact ⟨k, m, by simpa [arc8] using h1, by simpa [arc8, hα] using h2, h3⟩
    · obtain ⟨k, m, h1, h2, h3⟩ := link8L _ _ _ hab hpd
      exact ⟨k, m, by simpa [arc8] using h1, by simpa [arc8, hα] using h2, h3⟩
  have hy : c (i + 1) + ring k = c (i + 1 + 1) + ring m := by
    rw [hkm, c_succ hcons i, add_assoc]
  refine (CR_symm (arc8_reach hc i s k hk)).trans ?_
  rw [hy]
  exact arc8_reach hc (i + 1) s m hm

theorem side8_cover (i : Fin n) (k : Fin 8) (hk : c (i + 1) + ring k ∉ Set.range c) :
    ∃ s, CR G4 (Set.range c) (c (i + 1) + ring k) (rep8 c i s) := by
  have hcons := curve_adj_succ hc
  have hα : k ≠ αo c i := by
    rintro rfl; exact hk ⟨i, c_pred hcons i⟩
  have hβ : k ≠ βo c i := by
    rintro rfl; exact hk ⟨i + 1 + 1, c_succ hcons i⟩
  rcases arc_cover _ _ k (αo_ne_βo hcons hc (by omega) i) hα hβ with h | h
  · exact ⟨true, arc8_reach hc i true k (by simpa [arc8] using h)⟩
  · exact ⟨false, arc8_reach hc i false k (by simpa [arc8] using h)⟩

end Eight


/-! ## Local sides of a simple closed 4-curve -/

section Four

variable {n : ℕ} [NeZero n] {c : Fin n → ℤ × ℤ}

/-- Guaranteed complement cells on the left (`s = true`) / right side of `c (i+1)`. -/
def side4 (c : Fin n → ℤ × ℤ) (i : Fin n) (s : Bool) (k : Fin 8) : Prop :=
  if s then Side4 (βo c i) (αo c i) k else Side4 (αo c i) (βo c i) k

/-- Representative cell of a side. -/
def rep4c (c : Fin n → ℤ × ℤ) (i : Fin n) (s : Bool) : ℤ × ℤ :=
  c (i + 1) + ring (if s then rep4 (βo c i) (αo c i) else rep4 (αo c i) (βo c i))

variable (hc : IsSimpleClosedCurve G4 c) (hn : 8 ≤ n)
include hc hn

omit hn in
theorem αo_even4 (i : Fin n) : (αo c i).val % 2 = 0 :=
  G4_offIdx_even (curve_adj_succ hc i).symm

omit hn in
theorem βo_even4 (i : Fin n) : (βo c i).val % 2 = 0 :=
  G4_offIdx_even (curve_adj_succ hc (i + 1))

theorem side4_notin (i : Fin n) (s : Bool) (k : Fin 8) (h : side4 c i s k) :
    c (i + 1) + ring k ∉ Set.range c := by
  have hcons : ∀ i, G8.Adj (c i) (c (i + 1)) := fun i => G4_le_G8 (curve_adj_succ hc i)
  have hne : k ≠ αo c i ∧ k ≠ βo c i := by
    cases s <;> simp only [side4, Bool.false_eq_true, ite_false, ite_true, Side4, arcL] at h
    · exact ⟨h.1.1, h.1.2.1⟩
    · exact ⟨h.1.2.1, h.1.1⟩
  rintro ⟨j, hj⟩
  by_cases hev : k.val % 2 = 0
  · have hadj : G4.Adj (c (i + 1)) (c j) := hj ▸ G4_add_ring _ _ hev
    rcases curve_nbr hc i j hadj with rfl | rfl
    · exact hne.1 (ring_inj (add_left_cancel (hj.symm.trans (c_pred hcons j))))
    · exact hne.2 (ring_inj (add_left_cancel (hj.symm.trans (c_succ hcons i))))
  · have hcorner : G4.Adj (c j) (c i) ∧ G4.Adj (c j) (c (i + 1 + 1)) := by
      rw [hj, c_pred hcons i, c_succ hcons i, G4_add_iff, G4_add_iff, G4_adj, G4_adj]
      cases s <;> simp only [side4, Bool.false_eq_true, ite_false, ite_true] at h
      · obtain ⟨h1, h2⟩ := side4_corner _ _ k (αo_even4 hc i) (βo_even4 hc i) h hev
        exact ⟨by simpa using h2, by simpa using h1⟩
      · obtain ⟨h1, h2⟩ := side4_corner _ _ k (βo_even4 hc i) (αo_even4 hc i) h hev
        exact ⟨by simpa using h1, by simpa using h2⟩
    by_cases hj1 : j = i + 1
    · subst hj1
      exact ring_ne_zero k (by simpa using hj.symm)
    rcases (hc.2 _ _).1 hcorner.1 with h1 | h1 <;> rcases (hc.2 _ _).1 hcorner.2 with h2 | h2
    · exact hj1 (add_right_cancel h2).symm
    · rw [h2] at h1
      exact addN_ne i (a := 0) (b := 4) (by omega) (by omega) (by omega) h1
    · exact hj1 h1
    · exact hj1 h1

theorem side4_reach (i : Fin n) (s : Bool) (k : Fin 8) (h : side4 c i s k) :
    CR G8 (Set.range c) (c (i + 1) + ring k) (rep4c c i s) := by
  have hrep : side4 c i s (if s then rep4 (βo c i) (αo c i) else rep4 (αo c i) (βo c i)) := by
    cases s <;> simp only [side4, Bool.false_eq_true, ite_false, ite_true]
    · exact side4_rep _ _ (αo_even4 hc i) (βo_even4 hc i)
        (αo_ne_βo (fun i => G4_le_G8 (curve_adj_succ hc i)) hc (by omega) i).symm
    · exact side4_rep _ _ (βo_even4 hc i) (αo_even4 hc i)
        (αo_ne_βo (fun i => G4_le_G8 (curve_adj_succ hc i)) hc (by omega) i)
  have hcases : k = (if s then rep4 (βo c i) (αo c i) else rep4 (αo c i) (βo c i)) ∨
      (Near (ring k) (ring (if s then rep4 (βo c i) (αo c i) else rep4 (αo c i) (βo c i))) ∧
        k ≠ (if s then rep4 (βo c i) (αo c i) else rep4 (αo c i) (βo c i))) := by
    cases s <;> simp only [side4, Bool.false_eq_true, ite_false, ite_true] at h ⊢
    · exact side4_conn _ _ k (αo_even4 hc i) (βo_even4 hc i) h
    · exact side4_conn _ _ k (βo_even4 hc i) (αo_even4 hc i) h
  rcases hcases with h1 | ⟨h1, h2⟩
  · rw [rep4c, ← h1]
  · refine CR_step (side4_notin hc hn i s k h) (side4_notin hc hn i s _ hrep) ?_
    rw [rep4c, G8_add_iff, G8_iff_near]
    exact ⟨h1, fun h => h2 (ring_inj h)⟩

theorem side4_adj (i : Fin n) (s : Bool) :
    ∃ x, x ∉ Set.range c ∧ G8.Adj (c (i + 1)) x ∧ CR G8 (Set.range c) x (rep4c c i s) := by
  have hrep : side4 c i s (if s then rep4 (βo c i) (αo c i) else rep4 (αo c i) (βo c i)) := by
    cases s <;> simp only [side4, Bool.false_eq_true, ite_false, ite_true]
    · exact side4_rep _ _ (αo_even4 hc i) (βo_even4 hc i)
        (αo_ne_βo (fun i => G4_le_G8 (curve_adj_succ hc i)) hc (by omega) i).symm
    · exact side4_rep _ _ (βo_even4 hc i) (αo_even4 hc i)
        (αo_ne_βo (fun i => G4_le_G8 (curve_adj_succ hc i)) hc (by omega) i)
  exact ⟨rep4c c i s, side4_notin hc hn i s _ hrep, G8_add_ring _ _,
    Relation.ReflTransGen.refl⟩

theorem side4_link (i : Fin n) (s : Bool) :
    CR G8 (Set.range c) (rep4c c i s) (rep4c c (i + 1) s) := by
  have hcons : ∀ i, G8.Adj (c i) (c (i + 1)) := fun i => G4_le_G8 (curve_adj_succ hc i)
  have hα := αo_succ hcons i
  have hab := αo_ne_βo hcons hc (by omega) i
  have hδ : βo c (i + 1) ≠ βo c i + 4 := by
    rw [← hα]; exact (αo_ne_βo hcons hc (by omega) (i + 1)).symm
  obtain ⟨k, m, hk, hm, hkm⟩ : ∃ k m, side4 c i s k ∧ side4 c (i + 1) s m ∧
      Near (ring k) (ring (βo c i) + ring m) := by
    cases s
    · obtain ⟨k, m, h1, h2, h3⟩ := link4R _ _ _ (αo_even4 hc i) (βo_even4 hc i)
        (βo_even4 hc (i + 1)) hab hδ
      exact ⟨k, m, by simpa [side4] using h1, by simpa [side4, hα] using h2, h3⟩
    · obtain ⟨k, m, h1, h2, h3⟩ := link4L _ _ _ (αo_even4 hc i) (βo_even4 hc i)
        (βo_even4 hc (i + 1)) hab hδ
      exact ⟨k, m, by simpa [side4] using h1, by simpa [side4, hα] using h2, h3⟩
  have hy : c (i + 1 + 1) + ring m = c (i + 1) + (ring (βo c i) + ring m) := by
    rw [c_succ hcons i, add_assoc]
  have h1 := side4_notin hc hn i s k hk
  have h2 := side4_notin hc hn (i + 1) s m hm
  refine (CR_symm (side4_reach hc hn i s k hk)).trans (Relation.ReflTransGen.trans ?_
    (side4_reach hc hn (i + 1) s m hm))
  by_cases heq : c (i + 1) + ring k = c (i + 1 + 1) + ring m
  · rw [heq]
  · refine CR_step h1 h2 ?_
    rw [G8_iff_near, hy, near_add_iff]
    exact ⟨hkm, by rwa [← hy]⟩

theorem side4_cover (i : Fin n) (k : Fin 8) (hev : k.val % 2 = 0)
    (hk : c (i + 1) + ring k ∉ Set.range c) :
    ∃ s, CR G8 (Set.range c) (c (i + 1) + ring k) (rep4c c i s) := by
  have hcons : ∀ i, G8.Adj (c i) (c (i + 1)) := fun i => G4_le_G8 (curve_adj_succ hc i)
  have hα : k ≠ αo c i := by
    rintro rfl; exact hk ⟨i, c_pred hcons i⟩
  have hβ : k ≠ βo c i := by
    rintro rfl; exact hk ⟨i + 1 + 1, c_succ hcons i⟩
  rcases arc_cover _ _ k (αo_ne_βo hcons hc (by omega) i) hα hβ with h | h
  · exact ⟨true, side4_reach hc hn i true k (by simp [side4, Side4, h, hev])⟩
  · exact ⟨false, side4_reach hc hn i false k (by simp [side4, Side4, h, hev])⟩

end Four


/-! ## The parity far away and next to the top of the curve -/

section Parity

variable {n : ℕ} [NeZero n] {c : Fin n → ℤ × ℤ}

theorem par_zero_row (c : Fin n → ℤ × ℤ) (q : ℤ × ℤ) (h : ∀ j, (c j).2 ≠ q.2) :
    par c q = 0 := by
  unfold par
  refine Finset.sum_eq_zero (fun i _ => ?_)
  simp only [ite_eq_right_iff]
  rintro (⟨h1, -, -⟩ | ⟨h1, -, -⟩)
  · exact absurd h1 (h i)
  · exact absurd h1 (h (i + 1))

theorem par_one_of_edge (hinj : Function.Injective c) (hn : 4 ≤ n) (q : ℤ × ℤ) (i : Fin n)
    (w : ℤ × ℤ) (hw : c i = w ∨ c (i + 1 + 1) = w)
    (hcross : ∀ i', Cross q (c i') (c (i' + 1)) ↔
      ((c i' = c (i + 1) ∧ c (i' + 1) = w) ∨ (c i' = w ∧ c (i' + 1) = c (i + 1)))) :
    par c q = 1 := by
  have key : ∃ e, ∀ i', Cross q (c i') (c (i' + 1)) ↔ i' = e := by
    rcases hw with hw | hw
    · refine ⟨i, fun i' => ?_⟩
      rw [hcross]; constructor
      · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
        · have := hinj h1; subst this
          rw [← hw] at h2
          exact absurd (hinj h2) (addN_ne i (a := 2) (b := 0) (by omega) (by omega) (by omega))
        · exact hinj (h1.trans hw.symm)
      · rintro rfl; exact Or.inr ⟨hw, rfl⟩
    · refine ⟨i + 1, fun i' => ?_⟩
      rw [hcross]; constructor
      · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
        · exact hinj h1
        · rw [← hw] at h1; have := hinj h1; subst this
          exact absurd (hinj h2) (addN_ne i (a := 3) (b := 1) (by omega) (by omega) (by omega))
      · rintro rfl; exact Or.inl ⟨rfl, hw⟩
  obtain ⟨e, he⟩ := key
  unfold par
  simp only [he]
  simp

theorem exists_top (c : Fin n → ℤ × ℤ) :
    ∃ i, (∀ j, (c j).2 ≤ (c (i + 1)).2) ∧ ∀ j, (c j).2 = (c (i + 1)).2 → (c j).1 ≤ (c (i + 1)).1 := by
  obtain ⟨i1, -, h1⟩ := Finset.exists_max_image Finset.univ (fun j => (c j).2)
    Finset.univ_nonempty
  obtain ⟨i0, hi0, h0⟩ := (Finset.univ.filter (fun j => (c j).2 = (c i1).2)).exists_max_image
    (fun j => (c j).1) ⟨i1, by simp⟩
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi0 h0
  refine ⟨i0 - 1, ?_, ?_⟩ <;> rw [sub_add_cancel]
  · exact fun j => hi0 ▸ h1 j (Finset.mem_univ _)
  · exact fun j hj => h0 j (hj.trans hi0)

/-- A point of parity one next to a simple closed 8-curve. -/
theorem par_witness8 (hc : IsSimpleClosedCurve G8 c) (hn : 4 ≤ n) :
    ∃ q, q ∉ Set.range c ∧ par c q = 1 := by
  obtain ⟨i, htop1, htop2⟩ := exists_top c
  have ha := (curve_adj_succ hc i)
  have hb := curve_adj_succ hc (i + 1)
  have hab : ¬ Near (c i) (c (i + 1 + 1)) := fun h =>
    curve_nonadj2 hc hn i ((G8_iff_near _ _).2 ⟨h, curve_ne2 hc (by omega) i⟩)
  have t1 := htop1 i; have t2 := htop2 i; have t3 := htop1 (i + 1 + 1)
  have t4 := htop2 (i + 1 + 1)
  rw [G8_adj] at ha hb; simp only [abs_eq_max_neg] at ha hb; unfold Near at hab
  have hq : ((c (i + 1)).1, (c (i + 1)).2 - 1) ∉ Set.range c := by
    rintro ⟨j, hj⟩
    have hadj : G8.Adj (c (i + 1)) (c j) := by rw [hj, G8_adj]; simp
    rcases curve_nbr hc i j hadj with rfl | rfl
    · have := Prod.ext_iff.mp hj; simp only at this; omega
    · have := Prod.ext_iff.mp hj; simp only at this; omega
  have hqa : ¬ ((c i).1 = (c (i + 1)).1 ∧ (c i).2 = (c (i + 1)).2 - 1) :=
    fun h => hq ⟨i, Prod.ext h.1 h.2⟩
  have hqb : ¬ ((c (i + 1 + 1)).1 = (c (i + 1)).1 ∧ (c (i + 1 + 1)).2 = (c (i + 1)).2 - 1) :=
    fun h => hq ⟨i + 1 + 1, Prod.ext h.1 h.2⟩
  refine ⟨_, hq, par_one_of_edge hc.1 hn _ i ((c (i + 1)).1 + 1, (c (i + 1)).2 - 1) ?_ ?_⟩
  · have : ((c i).1 = (c (i + 1)).1 + 1 ∧ (c i).2 = (c (i + 1)).2 - 1) ∨
        ((c (i + 1 + 1)).1 = (c (i + 1)).1 + 1 ∧ (c (i + 1 + 1)).2 = (c (i + 1)).2 - 1) := by
      omega
    rcases this with h | h
    · exact Or.inl (Prod.ext h.1 h.2)
    · exact Or.inr (Prod.ext h.1 h.2)
  · intro i'
    have e := curve_adj_succ hc i'
    rw [G8_adj] at e; simp only [abs_eq_max_neg] at e
    have u1 := htop1 i'; have u2 := htop2 i'; have v1 := htop1 (i' + 1)
    have v2 := htop2 (i' + 1)
    simp only [Cross, Prod.ext_iff]
    omega

/-- The corner cell between two perpendicular curve neighbours of a 4-curve is not on it. -/
theorem corner4 (hc : IsSimpleClosedCurve G4 c) (hn : 5 ≤ n) (i j : Fin n)
    (h1 : G4.Adj (c j) (c i)) (h2 : G4.Adj (c j) (c (i + 1 + 1))) : j = i + 1 := by
  by_contra hj1
  rcases (hc.2 _ _).1 h1 with h1 | h1 <;> rcases (hc.2 _ _).1 h2 with h2 | h2
  · exact hj1 (add_right_cancel h2).symm
  · rw [h2] at h1
    exact addN_ne i (a := 0) (b := 4) (by omega) (by omega) (by omega) h1
  · exact hj1 h1
  · exact hj1 h1

/-- A point of parity one next to a simple closed 4-curve. -/
theorem par_witness4 (hc : IsSimpleClosedCurve G4 c) (hn : 8 ≤ n) :
    ∃ q, q ∉ Set.range c ∧ par c q = 1 := by
  obtain ⟨i, htop1, htop2⟩ := exists_top c
  have ha := (curve_adj_succ hc i)
  have hb := curve_adj_succ hc (i + 1)
  have hab := curve_ne2 hc (by omega) i
  have hab' : ¬ ((c i).1 = (c (i + 1 + 1)).1 ∧ (c i).2 = (c (i + 1 + 1)).2) :=
    fun h => hab (Prod.ext h.1 h.2)
  have t1 := htop1 i; have t2 := htop2 i; have t3 := htop1 (i + 1 + 1)
  have t4 := htop2 (i + 1 + 1)
  rw [G4_adj] at ha hb; simp only [abs_eq_max_neg] at ha hb
  have hq : ((c (i + 1)).1 - 1, (c (i + 1)).2 - 1) ∉ Set.range c := by
    rintro ⟨j, hj⟩
    have hj1 := corner4 hc (by omega) i j (by rw [hj, G4_adj]; simp only [abs_eq_max_neg]; omega)
      (by rw [hj, G4_adj]; simp only [abs_eq_max_neg]; omega)
    subst hj1
    have := Prod.ext_iff.mp hj; simp only at this; omega
  refine ⟨_, hq, par_one_of_edge hc.1 (by omega) _ i ((c (i + 1)).1, (c (i + 1)).2 - 1) ?_ ?_⟩
  · have : ((c i).1 = (c (i + 1)).1 ∧ (c i).2 = (c (i + 1)).2 - 1) ∨
        ((c (i + 1 + 1)).1 = (c (i + 1)).1 ∧ (c (i + 1 + 1)).2 = (c (i + 1)).2 - 1) := by
      omega
    rcases this with h | h
    · exact Or.inl (Prod.ext h.1 h.2)
    · exact Or.inr (Prod.ext h.1 h.2)
  · intro i'
    have e := curve_adj_succ hc i'
    rw [G4_adj] at e; simp only [abs_eq_max_neg] at e
    have u1 := htop1 i'; have u2 := htop2 i'; have v1 := htop1 (i' + 1)
    have v2 := htop2 (i' + 1)
    simp only [Cross, Prod.ext_iff]
    omega

end Parity


/-! ## Assembly -/

section Assembly

variable {n : ℕ} [NeZero n] {c : Fin n → ℤ × ℤ} {G : SimpleGraph (ℤ × ℤ)}

theorem reach_of_CR {C : Set (ℤ × ℤ)} {x y : ℤ × ℤ} (h : CR G C x y) (hx : x ∉ C) :
    (G.induce Cᶜ).Reachable ⟨x, hx⟩ ⟨y, CR_mem h hx⟩ := by
  induction h with
  | refl => rfl
  | tail hxy hs ih =>
    exact ih.trans (SimpleGraph.Adj.reachable (SimpleGraph.induce_adj.2 hs.2.2))

theorem CR_of_reach {C : Set (ℤ × ℤ)} {u v : ↥Cᶜ} (h : (G.induce Cᶜ).Reachable u v) :
    CR G C u.1 v.1 := by
  obtain ⟨w⟩ := h
  induction w with
  | nil => exact Relation.ReflTransGen.refl
  | @cons a b d hadj _ ih =>
    exact Relation.ReflTransGen.head ⟨a.2, b.2, SimpleGraph.induce_adj.1 hadj⟩ ih

/-- **Abstract assembly.** Parity invariance, a parity-one point, two families of side
cells linked consecutively around the curve, and the fact that every horizontal neighbour of
the curve lies on one of the two sides, together give the Jordan conclusion. -/
theorem assemble (hG : ∀ x y, G4.Adj x y → G.Adj x y)
    (hstep : ∀ x y, (∀ i, c i ≠ x) → (∀ i, c i ≠ y) → G.Adj x y → par c x = par c y)
    (rep : Fin n → Bool → ℤ × ℤ)
    (hlink : ∀ i s, CR G (Set.range c) (rep i s) (rep (i + 1) s))
    (hcover : ∀ i (k : Fin 8), (k = 0 ∨ k = 4) → c (i + 1) + ring k ∉ Set.range c →
      ∃ s, CR G (Set.range c) (c (i + 1) + ring k) (rep i s))
    (hside : ∀ i s, ∃ x, x ∉ Set.range c ∧ G.Adj (c (i + 1)) x ∧
      CR G (Set.range c) x (rep i s))
    (hq1 : ∃ q, q ∉ Set.range c ∧ par c q = 1) :
    ∃ I O : (G.induce (Set.range c)ᶜ).ConnectedComponent,
      I ≠ O ∧ (∀ K, K = I ∨ K = O) ∧ I.supp.Finite ∧ O.supp.Infinite ∧
      ∀ j, (∃ v ∈ I.supp, G.Adj (c j) v) ∧ (∃ v ∈ O.supp, G.Adj (c j) v) := by
  set C := Set.range c with hCdef
  have hchain : ∀ i s, CR G C (rep i s) (rep 0 s) := by
    intro i s
    have : ∀ k : ℕ, CR G C (rep (addN 0 k) s) (rep 0 s) := by
      intro k
      induction k with
      | zero => exact Relation.ReflTransGen.refl
      | succ k ih => exact (CR_symm (hlink (addN 0 k) s)).trans ih
    rw [← addN_zero_val i]; exact this _
  have htwo : ∀ q, q ∉ C → ∃ s, CR G C q (rep 0 s) := by
    intro q hq
    obtain ⟨j, hj | hj⟩ := reach_edge_cell c hG q hq
    · have e : ((c j).1 - 1, (c j).2) = c ((j - 1) + 1) + ring 4 := by
        rw [sub_add_cancel, ring4]; ext <;> simp; ring
      rw [e] at hj
      obtain ⟨s, hs⟩ := hcover (j - 1) 4 (Or.inr rfl) (CR_mem hj hq)
      exact ⟨s, hj.trans (hs.trans (hchain _ s))⟩
    · have e : ((c j).1 + 1, (c j).2) = c ((j - 1) + 1) + ring 0 := by
        rw [sub_add_cancel, ring0]; ext <;> simp
      rw [e] at hj
      obtain ⟨s, hs⟩ := hcover (j - 1) 0 (Or.inl rfl) (CR_mem hj hq)
      exact ⟨s, hj.trans (hs.trans (hchain _ s))⟩
  have hpar : ∀ {x y}, CR G C x y → par c x = par c y := fun h => par_of_CR c G hstep h
  obtain ⟨q1, hq1, hp1⟩ := hq1
  set B := bnd c with hB
  let far : ℕ → ℤ × ℤ := fun t => (0, B + 1 + t)
  have hfarC : ∀ t, far t ∉ C := by
    rintro t ⟨j, hj⟩
    have := (bnd_spec c j).2; rw [hj, abs_le] at this; simp only [far] at this; omega
  have hfar0 : ∀ t, par c (far t) = 0 := fun t => par_zero_row c _ (fun j hj => by
    have := (bnd_spec c j).2; rw [abs_le] at this; simp only [far] at hj; omega)
  have hdiff : par c (rep 0 true) ≠ par c (rep 0 false) := by
    intro heq
    have hall : ∀ s, par c (rep 0 s) = par c (rep 0 true) := by
      intro s; cases s
      · exact heq.symm
      · rfl
    obtain ⟨s3, h3⟩ := htwo q1 hq1
    obtain ⟨s4, h4⟩ := htwo (far 0) (hfarC 0)
    have e3 := hpar h3; have e4 := hpar h4
    rw [hall, hp1] at e3; rw [hall, hfar0] at e4
    rw [← e3] at e4; exact zero_ne_one e4
  have hsame : ∀ x y, x ∉ C → y ∉ C → par c x = par c y → CR G C x y := by
    intro x y hx hy hxy
    obtain ⟨s1, h1⟩ := htwo x hx; obtain ⟨s2, h2⟩ := htwo y hy
    by_cases hs : s1 = s2
    · subst hs; exact h1.trans (CR_symm h2)
    · exfalso
      have := (hpar h1).symm.trans (hxy.trans (hpar h2))
      cases s1 <;> cases s2 <;> simp at hs
      · exact hdiff this.symm
      · exact hdiff this
  have hcolpar : ∀ x, x ∉ C → (∀ j, (c j).1 ≠ x.1) → par c x = 0 := by
    intro x hx h
    have := hpar (col_reach hG (C := C) x (by rintro p ⟨j, rfl⟩; exact h j) (B + 1))
    rw [this]
    exact par_zero_row c _ (fun j hj => by
      have := (bnd_spec c j).2; rw [abs_le] at this; simp only at hj; omega)
  have hbox : ∀ x, x ∉ C → par c x = 1 → x ∈ Set.Icc (-B) B ×ˢ Set.Icc (-B) B := by
    intro x hx h1
    have hrow : ¬ (∀ j, (c j).2 ≠ x.2) := fun h => by
      rw [par_zero_row c x h] at h1; exact zero_ne_one h1
    push Not at hrow
    obtain ⟨j, hj⟩ := hrow
    have hjb := (bnd_spec c j).2; rw [abs_le] at hjb
    simp only [Set.mem_prod, Set.mem_Icc]
    refine ⟨⟨?_, ?_⟩, by omega, by omega⟩
    · by_contra hlt
      have := hcolpar x hx (fun j' hj' => by
        have := (bnd_spec c j').1; rw [abs_le] at this; omega)
      rw [this] at h1; exact zero_ne_one h1
    · by_contra hlt
      have := hcolpar x hx (fun j' hj' => by
        have := (bnd_spec c j').1; rw [abs_le] at this; omega)
      rw [this] at h1; exact zero_ne_one h1
  have hI : ∀ (v : ↥Cᶜ), par c v.1 = 1 →
      (G.induce Cᶜ).connectedComponentMk v = (G.induce Cᶜ).connectedComponentMk ⟨q1, hq1⟩ :=
    fun v hv => SimpleGraph.ConnectedComponent.sound
      (reach_of_CR (hsame _ _ v.2 hq1 (hv.trans hp1.symm)) v.2)
  have hO : ∀ (v : ↥Cᶜ), par c v.1 = 0 →
      (G.induce Cᶜ).connectedComponentMk v =
        (G.induce Cᶜ).connectedComponentMk ⟨far 0, hfarC 0⟩ :=
    fun v hv => SimpleGraph.ConnectedComponent.sound
      (reach_of_CR (hsame _ _ v.2 (hfarC 0) (hv.trans (hfar0 0).symm)) v.2)
  have h01 : ∀ z : ZMod 2, z = 0 ∨ z = 1 := by decide
  refine ⟨(G.induce Cᶜ).connectedComponentMk ⟨q1, hq1⟩,
    (G.induce Cᶜ).connectedComponentMk ⟨far 0, hfarC 0⟩, ?_, ?_, ?_, ?_, ?_⟩
  · intro h
    have := hpar (CR_of_reach (SimpleGraph.ConnectedComponent.exact h))
    rw [hp1, hfar0] at this; exact one_ne_zero this
  · intro K
    induction K using SimpleGraph.ConnectedComponent.ind with
    | h v =>
      rcases h01 (par c v.1) with h | h
      · exact Or.inr (hO v h)
      · exact Or.inl (hI v h)
  · have hsub : ((G.induce Cᶜ).connectedComponentMk ⟨q1, hq1⟩).supp ⊆
        Subtype.val ⁻¹' (Set.Icc (-B) B ×ˢ Set.Icc (-B) B) := by
      intro v hv
      rw [SimpleGraph.ConnectedComponent.mem_supp_iff, SimpleGraph.ConnectedComponent.eq] at hv
      have := hpar (CR_of_reach hv); rw [hp1] at this
      exact hbox v.1 v.2 this
    exact (((Set.finite_Icc _ _).prod (Set.finite_Icc _ _)).preimage
      Subtype.val_injective.injOn).subset hsub
  · refine Set.infinite_of_injective_forall_mem (f := fun t : ℕ => (⟨far t, hfarC t⟩ : ↥Cᶜ))
      ?_ ?_
    · intro t t' h
      have := congrArg (fun v : ↥Cᶜ => v.1.2) h
      simp only [far] at this; omega
    · intro t
      rw [SimpleGraph.ConnectedComponent.mem_supp_iff]
      exact hO _ (hfar0 t)
  · intro j
    obtain ⟨x1, hx1, ha1, hr1⟩ := hside (j - 1) true
    obtain ⟨x2, hx2, ha2, hr2⟩ := hside (j - 1) false
    rw [sub_add_cancel] at ha1 ha2
    have p1 := (hpar hr1).trans (hpar (hchain _ true))
    have p2 := (hpar hr2).trans (hpar (hchain _ false))
    rcases h01 (par c x1) with h | h
    · have h' : par c x2 = 1 := by
        rcases h01 (par c x2) with h'' | h''
        · exact absurd (p1.symm.trans (h.trans (h''.symm.trans p2))) hdiff
        · exact h''
      exact ⟨⟨⟨x2, hx2⟩, hI ⟨x2, hx2⟩ h', ha2⟩, ⟨⟨x1, hx1⟩, hO ⟨x1, hx1⟩ h, ha1⟩⟩
    · have h' : par c x2 = 0 := by
        rcases h01 (par c x2) with h'' | h''
        · exact h''
        · exact absurd (p1.symm.trans (h.trans (h''.symm.trans p2))) hdiff
      exact ⟨⟨⟨x1, hx1⟩, hI ⟨x1, hx1⟩ h, ha1⟩, ⟨⟨x2, hx2⟩, hO ⟨x2, hx2⟩ h', ha2⟩⟩

end Assembly


/-! ## The digital Jordan curve theorem (Rosenfeld) -/

/-- **Digital Jordan curve theorem, 8-curve case.** Let `c` be a simple closed 8-curve with
`n ≥ 4` points. Then the complement of its point set, with 4-adjacency, has exactly two
connected components `I` (finite, the inside) and `O` (infinite, the outside), and every
point of the curve is 4-adjacent to a point of each. -/
theorem digital_jordan_8 {n : ℕ} [NeZero n] (c : Fin n → ℤ × ℤ)
    (hc : IsSimpleClosedCurve G8 c) (hn : 4 ≤ n) :
    ∃ I O : (G4.induce (Set.range c)ᶜ).ConnectedComponent,
      I ≠ O ∧ (∀ K, K = I ∨ K = O) ∧ I.supp.Finite ∧ O.supp.Infinite ∧
      ∀ j, (∃ v ∈ I.supp, G4.Adj (c j) v) ∧ (∃ v ∈ O.supp, G4.Adj (c j) v) :=
  assemble (fun _ _ h => h)
    (fun x y hx hy h => par_step4 c (fun i => near_of_G8 (curve_adj_succ hc i)) x y hx hy h)
    (rep8 c) (side8_link hc hn) (fun i k _ hk => side8_cover hc hn i k hk)
    (side8_adj hc hn) (par_witness8 hc hn)

/-- **Digital Jordan curve theorem, 4-curve case.** Let `c` be a simple closed 4-curve with
`n ≥ 8` points. Then the complement of its point set, with 8-adjacency, has exactly two
connected components `I` (finite, the inside) and `O` (infinite, the outside), and every
point of the curve is 8-adjacent to a point of each. -/
theorem digital_jordan_4 {n : ℕ} [NeZero n] (c : Fin n → ℤ × ℤ)
    (hc : IsSimpleClosedCurve G4 c) (hn : 8 ≤ n) :
    ∃ I O : (G8.induce (Set.range c)ᶜ).ConnectedComponent,
      I ≠ O ∧ (∀ K, K = I ∨ K = O) ∧ I.supp.Finite ∧ O.supp.Infinite ∧
      ∀ j, (∃ v ∈ I.supp, G8.Adj (c j) v) ∧ (∃ v ∈ O.supp, G8.Adj (c j) v) :=
  assemble (fun _ _ h => G4_le_G8 h)
    (fun x y hx hy h => par_step8 c (curve_adj_succ hc) x y hx hy h)
    (rep4c c) (side4_link hc hn)
    (fun i k hk0 hk => side4_cover hc hn i k (by rcases hk0 with rfl | rfl <;> decide) hk)
    (side4_adj hc hn) (par_witness4 hc hn)

theorem card_two_of {V : Type*} {I O : V} (hIO : I ≠ O) (h : ∀ K, K = I ∨ K = O) :
    Nat.card V = 2 :=
  Nat.card_eq_two_iff.2 ⟨I, O, hIO, Set.eq_univ_of_forall fun K => by
    rcases h K with rfl | rfl <;> simp⟩

/-- The complement of a simple closed 8-curve (`n ≥ 4`) has exactly two 4-components. -/
theorem digital_jordan_8_card {n : ℕ} [NeZero n] (c : Fin n → ℤ × ℤ)
    (hc : IsSimpleClosedCurve G8 c) (hn : 4 ≤ n) :
    Nat.card (G4.induce (Set.range c)ᶜ).ConnectedComponent = 2 := by
  obtain ⟨I, O, h1, h2, -⟩ := digital_jordan_8 c hc hn
  exact card_two_of h1 h2

/-- The complement of a simple closed 4-curve (`n ≥ 8`) has exactly two 8-components. -/
theorem digital_jordan_4_card {n : ℕ} [NeZero n] (c : Fin n → ℤ × ℤ)
    (hc : IsSimpleClosedCurve G4 c) (hn : 8 ≤ n) :
    Nat.card (G8.induce (Set.range c)ᶜ).ConnectedComponent = 2 := by
  obtain ⟨I, O, h1, h2, -⟩ := digital_jordan_4 c hc hn
  exact card_two_of h1 h2


/-! ## Sanity checks: the hypotheses are satisfiable -/

/-- The diamond `(0,1),(1,0),(0,-1),(-1,0)` is a simple closed 8-curve with four points. -/
example : IsSimpleClosedCurve G8 (![(0, 1), (1, 0), (0, -1), (-1, 0)] : Fin 4 → ℤ × ℤ) := by
  unfold IsSimpleClosedCurve; decide

/-- The boundary of the `3 × 3` square is a simple closed 4-curve with eight points. -/
example : IsSimpleClosedCurve G4
    (![(0, 0), (1, 0), (2, 0), (2, 1), (2, 2), (1, 2), (0, 2), (0, 1)] : Fin 8 → ℤ × ℤ) := by
  unfold IsSimpleClosedCurve; decide

end QE.DigitalJordan
