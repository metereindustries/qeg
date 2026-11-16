-- SPDX-License-Identifier: MIT
-- Copyright 2026 Metere Industries, Inc. Author: Alfredo Metere.
-- Quasi-Euclidean Granular Geometry. Any derivative work must carry this notice:
--   This work is derivative of the Quasi-Euclidean Granular Geometry book
--   authored by Alfredo Metere. Copyright 2026 Metere Industries, Inc.
--   All rights reserved
-- See LICENSE.md and NOTICE.

import QuasiEuclidean.ChA_NSA

/-!
# Nonstandard-analysis infrastructure: internal sets, internal functions,
hyperfinite sets, overspill, saturation

Mathlib provides the ultrapower `ℝ* = Hyperreal = Germ (hyperfilter ℕ) ℝ` and Łoś's
theorem for first-order structures, but not the internal-set calculus of
nonstandard analysis.  This file builds it, for the ultrapower `Ult α = α^ℕ/U` of an
arbitrary type `α` over the hyperfilter `U = hyperfilter ℕ` (a free, hence countably
incomplete, ultrafilter).  `Ult ℝ` is definitionally `ℝ*` and `Ult ℕ` is the type of
hypernaturals `ℕ*`.

## Main definitions (API)

* `Ult α` : the ultrapower `α^ℕ/U`; `(u : Ult α)` for `u : ℕ → α` is the class `[u n]`.
* `internal A : Set (Ult α)` for `A : ℕ → Set α` : the internal set `[A n]`;
  `mem_internal : (u : Ult α) ∈ internal A ↔ ∀ᶠ n, u n ∈ A n`.
* `IsInternal S` : `S = internal A` for some `A`.
* `starSet S = internal (fun _ => S)` : the star-extension `*S` of a standard set.
* `ifun F : Ult α → Ult β` for `F : ℕ → α → β` : the internal function `[F n]`;
  `ifun_coe : ifun F u = [F n (u n)]`; `starFun f = ifun (fun _ => f)`.
* `IsHyperfinite S` : `S = internal (fun n => ↑(A n))` with `A n : Finset α`.
* `icard A : Ult ℕ` : `[#A n]`; `hcard S : Ult ℕ` : the internal cardinality of a
  hyperfinite set (`hcard_internal`).
* `hsum A F : ℝ*` : the hyperfinite sum `[∑_{x ∈ A n} F n x]`.
* `IsUnlimited ν` for `ν : Ult ℕ` : `ν > m` for every standard `m`.

## Main results

* Boolean algebra: `internal_inter`, `internal_union`, `internal_compl`,
  `internal_diff`, `internal_univ`, `internal_empty`, closure lemmas `IsInternal.*`;
  `internal_subset_iff`, `internal_eq_iff`, `internal_nonempty_iff`.
* Images and preimages: `ifun_image_internal`, `ifun_preimage_internal`.
* Internal cardinality: `hcard_internal`, `icard_congr`, `hcard_union_of_disjoint`
  (additivity), `hcard_union_add_hcard_inter`, `hcard_mono`, `hcard_empty`,
  `hcard_starSet_finset`; hyperfinite sums `hsum_congr`, `hsum_add`, `hsum_union`.
* `overspill_internal`, `overspill_segment`, `underspill_internal`,
  `underspill_real` (an internal set containing every positive infinitesimal contains
  a standard `r > 0`).
* `countable_saturation_internal` (finite intersection property form) and
  `saturation_decreasing` (a decreasing sequence of nonempty internal sets has
  nonempty intersection).
* `extension_of_sequences` : every standard sequence in an internal set extends to an
  internal hypersequence `Ult ℕ → Ult α` in that set.
* `exists_max_hyperfinite` : an internal real function attains its maximum on a
  nonempty hyperfinite set (`hval g c = [g n (c n)] ∈ ℝ*`).

## Transfer (Łoś), conservativity, internal definition principle

* `diagonalEmbedding L M U` : for any first-order language `L` and structure `M`, the
  diagonal map `M → M^ι/U` is an elementary embedding (Łoś,
  `FirstOrder.Language.Ultraproduct.realize_formula_cast`);
  `elementarilyEquivalent_ultrapower`.
* `realLang` : a function symbol for every `ℝ^k → ℝ`, a relation symbol for every
  `R ⊆ ℝ^k`; `realStructure` on `ℝ`, `hyperStructure` on `ℝ*` (the ultrapower
  structure, `RPow = ℝ*` definitionally).
* `starEmbedding : realLang.ElementaryEmbedding ℝ ℝ*`, `transfer`, `los_hyperreal`,
  `conservative`, `elementarilyEquivalent_real_hyperreal`, `semantic_conservativity`.
* `funMap_hyperreal`, `relMap_hyperreal`, `realisation_agrees` : the ultrapower
  interpretation is Mathlib's `Hyperreal` arithmetic and order, `starFun`, `starSet`.
* `iLang` : symbols for all internal functions/relations (sequences `F n`, `R n`);
  `Coord n` is coordinate `n`; `iStructure` on `Ult ℝ`; `los_iLang`;
  `internal_definition_principle`, `isInternal_definable`; `internalRel`,
  `internalFunSym` name an internal set / function.

## Metric spaces, S-continuity, lattices

* `hdist : Ult X → Ult X → ℝ*` and `Near x y` (infinitesimal `hdist`) for a metric
  space `X`; `near_coe_iff`, `near_const_iff_tendsto`, `Near.symm`, `Near.trans`.
* `isCompact_iff_near` (Robinson), `exists_near_of_isFinite` (proper spaces),
  `modulus_internal`, `shadow_of_S_continuous` (shadow of an S-continuous internal
  function is continuous), `starFun_near_of_continuousWithinAt`.
* One dimension: `hfun F : ℝ* → ℝ*`, `lattice ε = 2ε·ℤ*`, `latIcc ε a b`,
  `latIcc_eq_internal`, `latIcc_hyperfinite`, `exists_latIcc_near`,
  `shadow_lattice_function`, `shadow_lattice_converse`.
* `n` dimensions: `coordG`, `latN`, `cellN`, `latBox`, `robinson_open_lattice`,
  `robinson_compact_lattice`, `robinson_continuity_lattice`.

All results are Lebesgue-free.
-/

open Filter

noncomputable section

namespace QE.NSA

/-- The ultrapower `α^ℕ/U` over the hyperfilter of `ℕ`.  `Ult ℝ = ℝ*`. -/
abbrev Ult (α : Type*) : Type _ := Germ (hyperfilter ℕ : Filter ℕ) α

/-- `ℝ*` is the ultrapower `Ult ℝ`, definitionally. -/
theorem ult_real_eq : Ult ℝ = ℝ* := rfl

variable {α β γ : Type*}

/-! ## Internal sets -/

section InternalSets

/-- The internal set `[A n] ⊆ Ult α` presented by a sequence of sets. -/
def internal (A : ℕ → Set α) : Set (Ult α) :=
  {x | ∃ u : ℕ → α, (u : Ult α) = x ∧ ∀ᶠ n in (hyperfilter ℕ : Filter ℕ), u n ∈ A n}

/-- Membership in an internal set (Łoś for atomic membership). -/
theorem mem_internal (A : ℕ → Set α) (u : ℕ → α) :
    (u : Ult α) ∈ internal A ↔ ∀ᶠ n in (hyperfilter ℕ : Filter ℕ), u n ∈ A n := by
  constructor
  · rintro ⟨v, hv, hvA⟩
    have heq : ∀ᶠ n in (hyperfilter ℕ : Filter ℕ), v n = u n := Germ.coe_eq.1 hv
    filter_upwards [heq, hvA] with n h1 h2
    rwa [← h1]
  · intro h; exact ⟨u, rfl, h⟩

theorem exists_rep (x : Ult α) : ∃ u : ℕ → α, (u : Ult α) = x := Quot.exists_rep x

/-- A set of `Ult α` is internal if it is presented by a sequence of sets. -/
def IsInternal (S : Set (Ult α)) : Prop := ∃ A : ℕ → Set α, S = internal A

theorem isInternal_internal (A : ℕ → Set α) : IsInternal (internal A) := ⟨A, rfl⟩

/-- The star-extension `*S` of a standard set. -/
def starSet (S : Set α) : Set (Ult α) := internal (fun _ => S)

theorem mem_starSet (S : Set α) (u : ℕ → α) :
    (u : Ult α) ∈ starSet S ↔ ∀ᶠ n in (hyperfilter ℕ : Filter ℕ), u n ∈ S :=
  mem_internal _ u

theorem const_mem_starSet (S : Set α) (a : α) : ((a : α) : Ult α) ∈ starSet S ↔ a ∈ S := by
  show ((fun _ => a : ℕ → α) : Ult α) ∈ starSet S ↔ a ∈ S
  rw [mem_starSet]; exact eventually_const

theorem internal_congr {A B : ℕ → Set α}
    (h : ∀ᶠ n in (hyperfilter ℕ : Filter ℕ), A n = B n) : internal A = internal B := by
  ext x
  obtain ⟨u, rfl⟩ := exists_rep x
  rw [mem_internal, mem_internal]
  constructor <;> intro h' <;> filter_upwards [h, h'] with n h1 h2
  · rwa [← h1]
  · rwa [h1]

theorem internal_univ : internal (fun _ => (Set.univ : Set α)) = Set.univ := by
  ext x; obtain ⟨u, rfl⟩ := exists_rep x
  simp [mem_internal]

theorem internal_empty : internal (fun _ => (∅ : Set α)) = ∅ := by
  ext x; obtain ⟨u, rfl⟩ := exists_rep x
  simp only [mem_internal, Set.mem_empty_iff_false, eventually_false_iff_eq_bot]
  exact iff_of_false (NeBot.ne inferInstance) id

theorem internal_inter (A B : ℕ → Set α) :
    internal (fun n => A n ∩ B n) = internal A ∩ internal B := by
  ext x; obtain ⟨u, rfl⟩ := exists_rep x
  simp only [Set.mem_inter_iff, mem_internal]
  exact eventually_and

theorem internal_compl (A : ℕ → Set α) :
    internal (fun n => (A n)ᶜ) = (internal A)ᶜ := by
  ext x; obtain ⟨u, rfl⟩ := exists_rep x
  simp only [Set.mem_compl_iff, mem_internal]
  exact Ultrafilter.eventually_not

theorem internal_union (A B : ℕ → Set α) :
    internal (fun n => A n ∪ B n) = internal A ∪ internal B := by
  ext x; obtain ⟨u, rfl⟩ := exists_rep x
  simp only [Set.mem_union, mem_internal]
  exact Ultrafilter.eventually_or

theorem internal_diff (A B : ℕ → Set α) :
    internal (fun n => A n \ B n) = internal A \ internal B := by
  rw [Set.sdiff_eq, ← internal_compl, ← internal_inter]; rfl

theorem IsInternal.inter {S T : Set (Ult α)} (hS : IsInternal S) (hT : IsInternal T) :
    IsInternal (S ∩ T) := by
  obtain ⟨A, rfl⟩ := hS; obtain ⟨B, rfl⟩ := hT
  exact ⟨_, (internal_inter A B).symm⟩

theorem IsInternal.union {S T : Set (Ult α)} (hS : IsInternal S) (hT : IsInternal T) :
    IsInternal (S ∪ T) := by
  obtain ⟨A, rfl⟩ := hS; obtain ⟨B, rfl⟩ := hT
  exact ⟨_, (internal_union A B).symm⟩

theorem IsInternal.compl {S : Set (Ult α)} (hS : IsInternal S) : IsInternal Sᶜ := by
  obtain ⟨A, rfl⟩ := hS
  exact ⟨_, (internal_compl A).symm⟩

theorem IsInternal.diff {S T : Set (Ult α)} (hS : IsInternal S) (hT : IsInternal T) :
    IsInternal (S \ T) := by
  obtain ⟨A, rfl⟩ := hS; obtain ⟨B, rfl⟩ := hT
  exact ⟨_, (internal_diff A B).symm⟩

theorem isInternal_univ : IsInternal (Set.univ : Set (Ult α)) := ⟨_, internal_univ.symm⟩

theorem isInternal_empty : IsInternal (∅ : Set (Ult α)) := ⟨_, internal_empty.symm⟩

theorem isInternal_starSet (S : Set α) : IsInternal (starSet S) := ⟨_, rfl⟩

/-- Nonemptiness of an internal set is decided coordinatewise. -/
theorem internal_nonempty_iff (A : ℕ → Set α) :
    (internal A).Nonempty ↔ ∀ᶠ n in (hyperfilter ℕ : Filter ℕ), (A n).Nonempty := by
  constructor
  · rintro ⟨x, hx⟩
    obtain ⟨u, rfl⟩ := exists_rep x
    filter_upwards [(mem_internal A u).1 hx] with n hn using ⟨u n, hn⟩
  · intro h
    obtain ⟨n₀, hn₀⟩ := h.exists
    obtain ⟨a₀, -⟩ := hn₀
    classical
    let u : ℕ → α := fun n => if hn : (A n).Nonempty then hn.some else a₀
    refine ⟨u, (mem_internal A u).2 ?_⟩
    filter_upwards [h] with n hn
    simp only [u, hn, ↓reduceDIte]
    exact hn.some_mem

theorem internal_eq_empty_iff (A : ℕ → Set α) :
    internal A = ∅ ↔ ∀ᶠ n in (hyperfilter ℕ : Filter ℕ), A n = ∅ := by
  rw [← Set.not_nonempty_iff_eq_empty, internal_nonempty_iff, ← Ultrafilter.eventually_not]
  simp only [Set.not_nonempty_iff_eq_empty]

/-- Inclusion of internal sets is decided coordinatewise (this uses that the
hyperfilter is an ultrafilter). -/
theorem internal_subset_iff (A B : ℕ → Set α) :
    internal A ⊆ internal B ↔ ∀ᶠ n in (hyperfilter ℕ : Filter ℕ), A n ⊆ B n := by
  constructor
  · intro h
    have h0 : internal (fun n => A n \ B n) = ∅ := by
      rw [internal_diff]; exact Set.sdiff_eq_empty.2 h
    filter_upwards [(internal_eq_empty_iff _).1 h0] with n hn
    exact Set.sdiff_eq_empty.1 hn
  · intro h x hx
    obtain ⟨u, rfl⟩ := exists_rep x
    rw [mem_internal] at hx ⊢
    filter_upwards [h, hx] with n h1 h2 using h1 h2

theorem internal_eq_iff (A B : ℕ → Set α) :
    internal A = internal B ↔ ∀ᶠ n in (hyperfilter ℕ : Filter ℕ), A n = B n := by
  refine ⟨fun h => ?_, internal_congr⟩
  have h1 := (internal_subset_iff A B).1 h.le
  have h2 := (internal_subset_iff B A).1 h.ge
  filter_upwards [h1, h2] with n a b using Set.Subset.antisymm a b

end InternalSets

/-! ## Internal functions -/

section InternalFunctions

/-- The internal function `[F n] : Ult α → Ult β` presented by a sequence of
functions: `[u n] ↦ [F n (u n)]`. -/
def ifun (F : ℕ → α → β) (x : Ult α) : Ult β :=
  Germ.map₂ (fun (g : α → β) (a : α) => g a) (F : Ult (α → β)) x

@[simp] theorem ifun_coe (F : ℕ → α → β) (u : ℕ → α) :
    ifun F (u : Ult α) = ((fun n => F n (u n) : ℕ → β) : Ult β) := rfl

/-- A function `Ult α → Ult β` is internal if it is `ifun F` for some `F`. -/
def IsInternalFun (g : Ult α → Ult β) : Prop := ∃ F : ℕ → α → β, g = ifun F

/-- The star-extension `*f` of a standard function. -/
def starFun (f : α → β) : Ult α → Ult β := ifun (fun _ => f)

theorem starFun_eq_map (f : α → β) : starFun f = Germ.map f := by
  funext x; obtain ⟨u, rfl⟩ := exists_rep x; rfl

theorem starFun_const (f : α → β) (a : α) : starFun f (a : Ult α) = ((f a : β) : Ult β) := rfl

theorem ifun_congr {F G : ℕ → α → β} (h : ∀ᶠ n in (hyperfilter ℕ : Filter ℕ), F n = G n) :
    ifun F = ifun G := by
  funext x; obtain ⟨u, rfl⟩ := exists_rep x
  simp only [ifun_coe]
  exact Germ.coe_eq.2 (by filter_upwards [h] with n hn; rw [hn])

theorem ifun_comp (F : ℕ → α → β) (G : ℕ → β → γ) :
    ifun G ∘ ifun F = ifun (fun n => G n ∘ F n) := by
  funext x; obtain ⟨u, rfl⟩ := exists_rep x; rfl

/-- Preimages of internal sets under internal functions are internal. -/
theorem ifun_preimage_internal (F : ℕ → α → β) (B : ℕ → Set β) :
    ifun F ⁻¹' internal B = internal (fun n => F n ⁻¹' B n) := by
  ext x; obtain ⟨u, rfl⟩ := exists_rep x
  simp only [Set.mem_preimage, ifun_coe, mem_internal]

/-- Images of internal sets under internal functions are internal. -/
theorem ifun_image_internal (F : ℕ → α → β) (A : ℕ → Set α) :
    ifun F '' internal A = internal (fun n => F n '' A n) := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    obtain ⟨u, rfl⟩ := exists_rep x
    rw [mem_internal] at hx
    rw [ifun_coe, mem_internal]
    filter_upwards [hx] with n hn using ⟨u n, hn, rfl⟩
  · intro hy
    obtain ⟨v, rfl⟩ := exists_rep y
    rw [mem_internal] at hy
    obtain ⟨n₀, a₀, -, -⟩ := hy.exists
    classical
    let u : ℕ → α := fun n => if h : v n ∈ F n '' A n then h.choose else a₀
    refine ⟨u, (mem_internal A u).2 ?_, ?_⟩
    · filter_upwards [hy] with n hn
      simp only [u, hn, ↓reduceDIte]
      exact hn.choose_spec.1
    · rw [ifun_coe]
      refine Germ.coe_eq.2 ?_
      filter_upwards [hy] with n hn
      simp only [u, hn, ↓reduceDIte]
      exact hn.choose_spec.2

theorem IsInternal.preimage {S : Set (Ult β)} (hS : IsInternal S) (F : ℕ → α → β) :
    IsInternal (ifun F ⁻¹' S) := by
  obtain ⟨B, rfl⟩ := hS; exact ⟨_, ifun_preimage_internal F B⟩

theorem IsInternal.image {S : Set (Ult α)} (hS : IsInternal S) (F : ℕ → α → β) :
    IsInternal (ifun F '' S) := by
  obtain ⟨A, rfl⟩ := hS; exact ⟨_, ifun_image_internal F A⟩

/-- The set where two internal functions agree is internal. -/
theorem setOf_ifun_eq (F G : ℕ → α → β) :
    {x | ifun F x = ifun G x} = internal (fun n => {a | F n a = G n a}) := by
  ext x; obtain ⟨u, rfl⟩ := exists_rep x
  simp only [Set.mem_ofPred_eq, ifun_coe, mem_internal]
  exact Germ.coe_eq

/-- Two internal functions agree on an internal set iff they agree coordinatewise on
it for `U`-almost every coordinate. -/
theorem ifun_eqOn_internal_iff (F G : ℕ → α → β) (A : ℕ → Set α) :
    (∀ x ∈ internal A, ifun F x = ifun G x) ↔
      ∀ᶠ n in (hyperfilter ℕ : Filter ℕ), ∀ a ∈ A n, F n a = G n a := by
  have : (∀ x ∈ internal A, ifun F x = ifun G x) ↔
      internal A ⊆ internal (fun n => {a | F n a = G n a}) := by
    rw [← setOf_ifun_eq]; rfl
  rw [this, internal_subset_iff]; rfl

end InternalFunctions

/-! ## Hyperfinite sets and internal cardinality -/

section Hyperfinite

/-- The internal set presented by a sequence of finite sets. -/
def hfin (A : ℕ → Finset α) : Set (Ult α) := internal (fun n => (A n : Set α))

/-- A hyperfinite set: an internal set `[A n]` with every `A n` finite. -/
def IsHyperfinite (S : Set (Ult α)) : Prop := ∃ A : ℕ → Finset α, S = hfin A

theorem IsHyperfinite.isInternal {S : Set (Ult α)} (h : IsHyperfinite S) : IsInternal S := by
  obtain ⟨A, rfl⟩ := h; exact ⟨_, rfl⟩

/-- The internal cardinality `[#A n] ∈ ℕ*` of a presentation by finite sets. -/
def icard (A : ℕ → Finset α) : Ult ℕ := ((fun n => (A n).card : ℕ → ℕ) : Ult ℕ)

theorem hfin_eq_iff (A B : ℕ → Finset α) :
    hfin A = hfin B ↔ ∀ᶠ n in (hyperfilter ℕ : Filter ℕ), A n = B n := by
  unfold hfin; rw [internal_eq_iff]; simp only [Finset.coe_inj]

/-- The internal cardinality depends only on the hyperfinite set, not on its
presentation. -/
theorem icard_congr {A B : ℕ → Finset α} (h : hfin A = hfin B) : icard A = icard B := by
  refine Germ.coe_eq.2 ?_
  filter_upwards [(hfin_eq_iff A B).1 h] with n hn; rw [hn]

open Classical in
/-- The internal cardinality of a hyperfinite set (`0` on non-hyperfinite sets, a
junk value). -/
noncomputable def hcard (S : Set (Ult α)) : Ult ℕ :=
  if h : IsHyperfinite S then icard h.choose else 0

theorem hcard_hfin (A : ℕ → Finset α) : hcard (hfin A) = icard A := by
  have h : IsHyperfinite (hfin A) := ⟨A, rfl⟩
  simp only [hcard, h, ↓reduceDIte]
  exact icard_congr h.choose_spec.symm

theorem hcard_internal (A : ℕ → Finset α) :
    hcard (internal (fun n => (A n : Set α))) = icard A := hcard_hfin A

theorem hfin_union [DecidableEq α] (A B : ℕ → Finset α) :
    hfin (fun n => A n ∪ B n) = hfin A ∪ hfin B := by
  unfold hfin; rw [← internal_union]; simp only [Finset.coe_union]

theorem hfin_inter [DecidableEq α] (A B : ℕ → Finset α) :
    hfin (fun n => A n ∩ B n) = hfin A ∩ hfin B := by
  unfold hfin; rw [← internal_inter]; simp only [Finset.coe_inter]

theorem hfin_sdiff [DecidableEq α] (A B : ℕ → Finset α) :
    hfin (fun n => A n \ B n) = hfin A \ hfin B := by
  unfold hfin; rw [← internal_diff]; simp only [Finset.coe_sdiff]

theorem IsHyperfinite.union {S T : Set (Ult α)} (hS : IsHyperfinite S) (hT : IsHyperfinite T) :
    IsHyperfinite (S ∪ T) := by
  classical
  obtain ⟨A, rfl⟩ := hS; obtain ⟨B, rfl⟩ := hT
  exact ⟨_, (hfin_union A B).symm⟩

/-- An internal subset of a hyperfinite set is hyperfinite. -/
theorem IsHyperfinite.subset {S T : Set (Ult α)} (hT : IsHyperfinite T) (hS : IsInternal S)
    (h : S ⊆ T) : IsHyperfinite S := by
  classical
  obtain ⟨B, rfl⟩ := hT; obtain ⟨A, rfl⟩ := hS
  have hsub := (internal_subset_iff _ _).1 h
  refine ⟨fun n => (B n).filter (· ∈ A n), ?_⟩
  unfold hfin
  apply internal_congr
  filter_upwards [hsub] with n hn
  ext a; simp only [Finset.coe_filter, Set.mem_ofPred_eq]
  exact ⟨fun ha => ⟨hn ha, ha⟩, fun ha => ha.2⟩

theorem IsHyperfinite.inter_internal {S T : Set (Ult α)} (hS : IsHyperfinite S)
    (hT : IsInternal T) : IsHyperfinite (S ∩ T) :=
  hS.subset (hS.isInternal.inter hT) Set.inter_subset_left

theorem IsHyperfinite.diff_internal {S T : Set (Ult α)} (hS : IsHyperfinite S)
    (hT : IsInternal T) : IsHyperfinite (S \ T) :=
  hS.subset (hS.isInternal.diff hT) Set.sdiff_subset

/-- An internal set whose coordinates are `U`-almost all finite is hyperfinite. -/
theorem isHyperfinite_of_eventually_finite (A : ℕ → Set α)
    (h : ∀ᶠ n in (hyperfilter ℕ : Filter ℕ), (A n).Finite) : IsHyperfinite (internal A) := by
  classical
  refine ⟨fun n => if hn : (A n).Finite then hn.toFinset else ∅, ?_⟩
  unfold hfin; apply internal_congr
  filter_upwards [h] with n hn
  simp [hn]

theorem hcard_empty : hcard (∅ : Set (Ult α)) = 0 := by
  have : (∅ : Set (Ult α)) = hfin (fun _ => (∅ : Finset α)) := by
    unfold hfin; simp only [Finset.coe_empty]; exact internal_empty.symm
  rw [this, hcard_hfin]; rfl

/-- **Additivity of internal cardinality** on disjoint hyperfinite sets. -/
theorem hcard_union_of_disjoint {S T : Set (Ult α)} (hS : IsHyperfinite S)
    (hT : IsHyperfinite T) (hd : Disjoint S T) : hcard (S ∪ T) = hcard S + hcard T := by
  classical
  obtain ⟨A, rfl⟩ := hS; obtain ⟨B, rfl⟩ := hT
  rw [← hfin_union, hcard_hfin, hcard_hfin, hcard_hfin]
  have h0 : hfin (fun n => A n ∩ B n) = hfin (fun _ => ∅) := by
    rw [hfin_inter, Set.disjoint_iff_inter_eq_empty.1 hd]
    unfold hfin; simp only [Finset.coe_empty]; exact internal_empty.symm
  have hev := (hfin_eq_iff _ _).1 h0
  refine Germ.coe_eq.2 ?_
  filter_upwards [hev] with n hn
  exact Finset.card_union_of_disjoint (Finset.disjoint_iff_inter_eq_empty.2 hn)

/-- Inclusion–exclusion for internal cardinality. -/
theorem hcard_union_add_hcard_inter {S T : Set (Ult α)} (hS : IsHyperfinite S)
    (hT : IsHyperfinite T) : hcard (S ∪ T) + hcard (S ∩ T) = hcard S + hcard T := by
  classical
  obtain ⟨A, rfl⟩ := hS; obtain ⟨B, rfl⟩ := hT
  rw [← hfin_union, ← hfin_inter, hcard_hfin, hcard_hfin, hcard_hfin, hcard_hfin]
  exact Germ.coe_eq.2 (Eventually.of_forall fun n => Finset.card_union_add_card_inter _ _)

/-- Monotonicity of internal cardinality. -/
theorem hcard_mono {S T : Set (Ult α)} (hS : IsHyperfinite S) (hT : IsHyperfinite T)
    (h : S ⊆ T) : hcard S ≤ hcard T := by
  obtain ⟨A, rfl⟩ := hS; obtain ⟨B, rfl⟩ := hT
  rw [hcard_hfin, hcard_hfin]
  have hsub := (internal_subset_iff _ _).1 h
  refine Germ.coe_le.2 ?_
  filter_upwards [hsub] with n hn
  exact Finset.card_le_card (by exact_mod_cast hn)

/-- Internal cardinality of a difference. -/
theorem hcard_diff_add {S T : Set (Ult α)} (hS : IsHyperfinite S) (hT : IsInternal T) :
    hcard (S \ T) + hcard (S ∩ T) = hcard S := by
  have h1 := hcard_union_of_disjoint (hS.diff_internal hT) (hS.inter_internal hT)
    (Set.disjoint_sdiff_inter)
  rw [Set.sdiff_union_inter] at h1
  exact h1.symm

/-- A standard finite set has standard internal cardinality. -/
theorem hcard_starSet_finset (s : Finset α) :
    hcard (starSet (s : Set α)) = ((s.card : ℕ) : Ult ℕ) := by
  have : starSet (s : Set α) = hfin (fun _ => s) := rfl
  rw [this, hcard_hfin]; rfl

/-- The hyperfinite sum `∑_{x ∈ [A n]} [F n] x = [∑_{x ∈ A n} F n x] ∈ ℝ*`. -/
def hsum (A : ℕ → Finset α) (F : ℕ → α → ℝ) : ℝ* :=
  Hyperreal.ofSeq (fun n => ∑ x ∈ A n, F n x)

/-- The hyperfinite sum depends only on the hyperfinite set and on the values of the
internal function on it. -/
theorem hsum_congr {A B : ℕ → Finset α} {F G : ℕ → α → ℝ} (hAB : hfin A = hfin B)
    (hFG : ∀ x ∈ hfin A, ifun F x = ifun G x) : hsum A F = hsum B G := by
  have h1 := (hfin_eq_iff A B).1 hAB
  have h2 := (ifun_eqOn_internal_iff F G _).1 hFG
  refine Germ.coe_eq.2 ?_
  filter_upwards [h1, h2] with n hn hn'
  rw [← hn]
  exact Finset.sum_congr rfl (fun x hx => hn' x (by exact_mod_cast hx))

theorem hsum_add (A : ℕ → Finset α) (F G : ℕ → α → ℝ) :
    hsum A (fun n x => F n x + G n x) = hsum A F + hsum A G := by
  unfold hsum; simp only [Finset.sum_add_distrib]; rfl

theorem hsum_const_mul (A : ℕ → Finset α) (F : ℕ → α → ℝ) (c : ℕ → ℝ) :
    hsum A (fun n x => c n * F n x) = Hyperreal.ofSeq c * hsum A F := by
  unfold hsum; simp only [← Finset.mul_sum]; rfl

/-- Hyperfinite sums are additive over disjoint unions. -/
theorem hsum_union [DecidableEq α] (A B : ℕ → Finset α) (F : ℕ → α → ℝ)
    (hd : Disjoint (hfin A) (hfin B)) :
    hsum (fun n => A n ∪ B n) F = hsum A F + hsum B F := by
  have h0 : hfin (fun n => A n ∩ B n) = hfin (fun _ => ∅) := by
    rw [hfin_inter, Set.disjoint_iff_inter_eq_empty.1 hd]
    unfold hfin; simp only [Finset.coe_empty]; exact internal_empty.symm
  have hev := (hfin_eq_iff _ _).1 h0
  refine Germ.coe_eq.2 ?_
  filter_upwards [hev] with n hn
  exact Finset.sum_union (Finset.disjoint_iff_inter_eq_empty.2 hn)

/-- The internal cardinality, cast to `ℝ*`, is the hyperfinite sum of `1`. -/
theorem hsum_one (A : ℕ → Finset α) :
    hsum A (fun _ _ => 1) = Germ.map (fun k : ℕ => (k : ℝ)) (icard A) := by
  unfold hsum icard; simp only [Finset.sum_const, nsmul_eq_mul, mul_one]; rfl

end Hyperfinite

/-! ## Infinitesimal and finite hyperreals in coordinates -/

section HyperCoord

/-- `|[w n]| = [|w n|]`. -/
theorem abs_ofSeq (w : ℕ → ℝ) :
    |Hyperreal.ofSeq w| = Hyperreal.ofSeq (fun n => |w n|) := by
  show |((w : ℕ → ℝ) : Germ ((hyperfilter ℕ : Ultrafilter ℕ) : Filter ℕ) ℝ)| = _
  rw [Germ.abs_def, Germ.map_coe]; rfl

theorem ofSeq_lt_const {w : ℕ → ℝ} {r : ℝ} :
    Hyperreal.ofSeq w < (r : ℝ*) ↔ ∀ᶠ n in (hyperfilter ℕ : Filter ℕ), w n < r :=
  Hyperreal.ofSeq_lt_ofSeq (g := fun _ => r)

theorem ofSeq_le_const {w : ℕ → ℝ} {r : ℝ} :
    Hyperreal.ofSeq w ≤ (r : ℝ*) ↔ ∀ᶠ n in (hyperfilter ℕ : Filter ℕ), w n ≤ r :=
  Hyperreal.ofSeq_le_ofSeq (g := fun _ => r)

/-- A hyperreal `[w n]` is infinitesimal iff `|w n| < r` for `U`-almost every `n`, for
every standard `r > 0`. -/
theorem isInfinitesimal_ofSeq_iff (w : ℕ → ℝ) :
    IsInfinitesimal (Hyperreal.ofSeq w) ↔
      ∀ r : ℝ, 0 < r → ∀ᶠ n in (hyperfilter ℕ : Filter ℕ), |w n| < r := by
  rw [hyper_isInfinitesimal_iff]
  simp only [abs_ofSeq, ofSeq_lt_const]

/-- A hyperreal is finite iff it is bounded by a standard real. -/
theorem isFinite_iff_abs_le (x : ℝ*) : IsFinite x ↔ ∃ r : ℝ, |x| ≤ (r : ℝ*) := by
  unfold IsFinite
  rw [← ArchimedeanClass.mk_one, ArchimedeanClass.mk_le_mk]
  constructor
  · rintro ⟨n, hn⟩
    refine ⟨n, ?_⟩
    have hn' : |x| ≤ (n : ℝ*) := by simpa using hn
    exact_mod_cast hn'
  · rintro ⟨r, hr⟩
    obtain ⟨n, hn⟩ := exists_nat_ge r
    refine ⟨n, ?_⟩
    simp only [abs_one, nsmul_eq_mul, mul_one]
    have h2 : ((r : ℝ) : ℝ*) ≤ ((n : ℝ) : ℝ*) := Hyperreal.coe_le_coe.2 hn
    exact_mod_cast hr.trans h2

theorem isFinite_ofSeq_iff (w : ℕ → ℝ) :
    IsFinite (Hyperreal.ofSeq w) ↔ ∃ r : ℝ, ∀ᶠ n in (hyperfilter ℕ : Filter ℕ), |w n| ≤ r := by
  rw [isFinite_iff_abs_le]; simp only [abs_ofSeq, ofSeq_le_const]

/-- An infinitesimal is smaller in absolute value than every standard positive real. -/
theorem IsInfinitesimal.abs_lt {x : ℝ*} (hx : IsInfinitesimal x) {r : ℝ} (hr : 0 < r) :
    |x| < (r : ℝ*) := (hyper_isInfinitesimal_iff x).1 hx r hr

theorem isInfinitesimal_of_abs_lt {x : ℝ*} (h : ∀ r : ℝ, 0 < r → |x| < (r : ℝ*)) :
    IsInfinitesimal x := (hyper_isInfinitesimal_iff x).2 h

/-- A standard real that is infinitesimal is `0`. -/
theorem coe_eq_zero_of_isInfinitesimal {r : ℝ} (h : IsInfinitesimal (r : ℝ*)) : r = 0 := by
  by_contra hr
  have := h.abs_lt (abs_pos.2 hr)
  rw [← Hyperreal.coe_abs, Hyperreal.coe_lt_coe] at this
  exact lt_irrefl _ this

/-- If a standard real is below `η + δ` with `δ` infinitesimal (and `η` standard), it
is at most `η`. -/
theorem le_of_lt_add_infinitesimal {r η : ℝ} {δ : ℝ*} (hδ : IsInfinitesimal δ)
    (h : (r : ℝ*) < η + δ) : r ≤ η := by
  by_contra hc
  push Not at hc
  have h1 := hδ.abs_lt (sub_pos.2 hc)
  have h2 : (r - η : ℝ*) < δ := by linarith
  have h3 : δ ≤ |δ| := le_abs_self δ
  rw [Hyperreal.coe_sub] at h1
  linarith

end HyperCoord

/-! ## Hypernaturals, overspill and underspill -/

section Spill

/-- A hypernatural is unlimited (infinite) if it exceeds every standard natural. -/
def IsUnlimited (ν : Ult ℕ) : Prop := ∀ m : ℕ, (Germ.const m : Ult ℕ) < ν

theorem const_mem_internal (A : ℕ → Set α) (a : α) :
    (Germ.const a : Ult α) ∈ internal A ↔ ∀ᶠ n in (hyperfilter ℕ : Filter ℕ), a ∈ A n :=
  mem_internal A (fun _ => a)

/-- **Overspill**, strong form: an internal set of hypernaturals that contains every
standard natural contains an initial segment `[0, ν]` with `ν` unlimited. -/
theorem overspill_segment (S : Set (Ult ℕ)) (hS : IsInternal S)
    (h : ∀ m : ℕ, (Germ.const m : Ult ℕ) ∈ S) :
    ∃ ν, IsUnlimited ν ∧ ∀ μ ≤ ν, μ ∈ S := by
  classical
  obtain ⟨A, rfl⟩ := hS
  have h' : ∀ m : ℕ, ∀ᶠ n in (hyperfilter ℕ : Filter ℕ), m ∈ A n :=
    fun m => (const_mem_internal A m).1 (h m)
  let P : ℕ → ℕ → Prop := fun n m => ∀ j ≤ m, j ∈ A n
  let f : ℕ → ℕ := fun n => Nat.findGreatest (P n) n
  have key : ∀ k : ℕ, ∀ᶠ n in (hyperfilter ℕ : Filter ℕ), P n k ∧ k ≤ n := by
    intro k
    have hall : ∀ᶠ n in (hyperfilter ℕ : Filter ℕ), ∀ j ∈ Finset.range (k + 1), j ∈ A n :=
      (Filter.eventually_all_finset _).2 (fun j _ => h' j)
    filter_upwards [hall, eventually_ge k] with n hn hkn
    exact ⟨fun j hj => hn j (by simpa [Nat.lt_succ_iff] using hj), hkn⟩
  refine ⟨(f : Ult ℕ), fun m => ?_, fun μ hμ => ?_⟩
  · refine Germ.coe_lt.2 ?_
    filter_upwards [key (m + 1)] with n hn
    exact Nat.lt_of_lt_of_le (Nat.lt_succ_self m) (Nat.le_findGreatest hn.2 hn.1)
  · obtain ⟨g, rfl⟩ := exists_rep μ
    rw [mem_internal]
    have hle : ∀ᶠ n in (hyperfilter ℕ : Filter ℕ), g n ≤ f n := Germ.coe_le.1 hμ
    filter_upwards [hle, key 0] with n h1 h2
    exact Nat.findGreatest_spec (P := P n) h2.2 h2.1 (g n) h1

/-- **Overspill.** An internal set of hypernaturals that contains every standard
natural contains an unlimited hypernatural. -/
theorem overspill_internal (S : Set (Ult ℕ)) (hS : IsInternal S)
    (h : ∀ m : ℕ, (Germ.const m : Ult ℕ) ∈ S) : ∃ ν ∈ S, IsUnlimited ν := by
  obtain ⟨ν, hν, hseg⟩ := overspill_segment S hS h
  exact ⟨ν, hseg ν le_rfl, hν⟩

/-- **Underspill.** An internal set of hypernaturals that contains every unlimited
hypernatural contains a standard natural. -/
theorem underspill_internal (S : Set (Ult ℕ)) (hS : IsInternal S)
    (h : ∀ ν, IsUnlimited ν → ν ∈ S) : ∃ m : ℕ, (Germ.const m : Ult ℕ) ∈ S := by
  by_contra hne
  push Not at hne
  obtain ⟨ν, hν, hinf⟩ := overspill_internal Sᶜ hS.compl hne
  exact hν (h ν hinf)

/-- The internal function `k ↦ 1/(k+1)` from `ℕ*` to `ℝ*`. -/
def recipSucc : Ult ℕ → ℝ* := ifun (fun _ (k : ℕ) => (1 : ℝ) / ((k : ℝ) + 1))

theorem recipSucc_pos_infinitesimal {ν : Ult ℕ} (hν : IsUnlimited ν) :
    0 < recipSucc ν ∧ IsInfinitesimal (recipSucc ν) := by
  obtain ⟨g, rfl⟩ := exists_rep ν
  refine ⟨Germ.coe_pos.2 (Eventually.of_forall fun n => by positivity), ?_⟩
  show IsInfinitesimal (Hyperreal.ofSeq (fun n => (1 : ℝ) / ((g n : ℝ) + 1)))
  rw [isInfinitesimal_ofSeq_iff]
  intro r hr
  obtain ⟨m, hm⟩ := exists_nat_gt (1 / r)
  have hlt : ∀ᶠ n in (hyperfilter ℕ : Filter ℕ), m < g n := Germ.coe_lt.1 (hν m)
  filter_upwards [hlt] with n hn
  have hgn : (1 / r : ℝ) < (g n : ℝ) + 1 := by
    have : (m : ℝ) < g n := by exact_mod_cast hn
    linarith
  rw [abs_of_pos (by positivity)]
  rw [div_lt_iff₀ (by positivity)]
  rw [div_lt_iff₀ hr] at hgn
  linarith

/-- **Underspill for hyperreals.** An internal subset of `ℝ*` that contains every
positive infinitesimal contains a standard positive real. -/
theorem underspill_real (S : Set ℝ*) (hS : IsInternal (S : Set (Ult ℝ)))
    (h : ∀ δ : ℝ*, 0 < δ → IsInfinitesimal δ → δ ∈ S) :
    ∃ r : ℝ, 0 < r ∧ (r : ℝ*) ∈ S := by
  have hT : IsInternal (recipSucc ⁻¹' S) := hS.preimage _
  obtain ⟨m, hm⟩ := underspill_internal _ hT (fun ν hν =>
    h _ (recipSucc_pos_infinitesimal hν).1 (recipSucc_pos_infinitesimal hν).2)
  exact ⟨1 / ((m : ℝ) + 1), by positivity, hm⟩

end Spill

/-! ## Countable saturation -/

section Saturation

/-- **Countable (`ℵ₁`-) saturation**: a countable family of internal sets with the
finite intersection property has a common element. -/
theorem countable_saturation_internal (S : ℕ → Set (Ult α)) (hS : ∀ k, IsInternal (S k))
    (hfip : ∀ K : ℕ, ∃ x, ∀ k ≤ K, x ∈ S k) : ∃ x, ∀ k, x ∈ S k := by
  choose A hA using hS
  obtain ⟨x₀, -⟩ := hfip 0
  obtain ⟨u₀, -⟩ := exists_rep x₀
  have : Nonempty α := ⟨u₀ 0⟩
  have hfip' : ∀ K : ℕ, ∃ f : ℕ → α, ∀ k ≤ K,
      ∀ᶠ n in (hyperfilter ℕ : Filter ℕ), f n ∈ A k n := by
    intro K
    obtain ⟨x, hx⟩ := hfip K
    obtain ⟨f, rfl⟩ := exists_rep x
    refine ⟨f, fun k hk => ?_⟩
    have := hx k hk; rw [hA k] at this; exact (mem_internal _ f).1 this
  obtain ⟨g, hg⟩ := countable_saturation A hfip'
  exact ⟨(g : Ult α), fun k => by rw [hA k]; exact (mem_internal _ g).2 (hg k)⟩

/-- **Countable saturation**, decreasing form: a decreasing sequence of nonempty
internal sets has nonempty intersection. -/
theorem saturation_decreasing (S : ℕ → Set (Ult α)) (hS : ∀ k, IsInternal (S k))
    (hne : ∀ k, (S k).Nonempty) (hanti : Antitone S) : (⋂ k, S k).Nonempty := by
  obtain ⟨x, hx⟩ := countable_saturation_internal S hS (fun K =>
    ⟨(hne K).some, fun k hk => hanti hk (hne K).some_mem⟩)
  exact ⟨x, Set.mem_iInter.2 hx⟩

/-- **Extension of sequences.** Every standard sequence `(x k)_{k ∈ ℕ}` of elements of
an internal set `A` extends to an internal hypersequence `X : ℕ* → Ult α` (an
internal function `ifun X`) with values in `A`.  Proof: saturation applied to the
decreasing internal sets `S_k` of internal sequences in `A` that agree with `x` up
to `k`. -/
theorem extension_of_sequences (A : Set (Ult α)) (hA : IsInternal A) (x : ℕ → Ult α)
    (hx : ∀ k, x k ∈ A) :
    ∃ X : ℕ → ℕ → α, (∀ k : ℕ, ifun X (Germ.const k) = x k) ∧ ∀ ν : Ult ℕ, ifun X ν ∈ A := by
  obtain ⟨B, rfl⟩ := hA
  choose u hu using fun k => exists_rep (x k)
  have hxB : ∀ k, ∀ᶠ n in (hyperfilter ℕ : Filter ℕ), u k n ∈ B n := fun k => by
    have := hx k; rw [← hu k] at this; exact (mem_internal B _).1 this
  -- internal sets of internal sequences
  let C : ℕ → ℕ → Set (ℕ → α) := fun k n => {σ | (∀ j ≤ k, σ j = u j n) ∧ ∀ i, σ i ∈ B n}
  let S : ℕ → Set (Ult (ℕ → α)) := fun k => internal (C k)
  have hne : ∀ k, (S k).Nonempty := by
    intro k
    refine (internal_nonempty_iff _).2 ?_
    have hall : ∀ᶠ n in (hyperfilter ℕ : Filter ℕ), ∀ j ∈ Finset.range (k + 1), u j n ∈ B n :=
      (Filter.eventually_all_finset _).2 (fun j _ => hxB j)
    filter_upwards [hall] with n hn
    refine ⟨fun i => u (min i k) n, fun j hj => by simp only [min_eq_left hj], fun i => ?_⟩
    exact hn _ (Finset.mem_range.2 (Nat.lt_succ_of_le (min_le_right i k)))
  have hanti : Antitone S := by
    refine antitone_nat_of_succ_le (fun k => ?_)
    refine (internal_subset_iff _ _).2 (Eventually.of_forall fun n σ hσ => ?_)
    exact ⟨fun j hj => hσ.1 j (Nat.le_succ_of_le hj), hσ.2⟩
  obtain ⟨s, hs⟩ := saturation_decreasing S (fun k => isInternal_internal _) hne hanti
  obtain ⟨X, rfl⟩ := exists_rep s
  have hX : ∀ k, ∀ᶠ n in (hyperfilter ℕ : Filter ℕ), X n ∈ C k n := fun k =>
    (mem_internal _ X).1 (Set.mem_iInter.1 hs k)
  refine ⟨X, fun k => ?_, fun ν => ?_⟩
  · rw [← hu k]
    show ((fun n => X n k : ℕ → α) : Ult α) = (u k : Ult α)
    refine Germ.coe_eq.2 ?_
    filter_upwards [hX k] with n hn using hn.1 k le_rfl
  · obtain ⟨g, rfl⟩ := exists_rep ν
    rw [ifun_coe, mem_internal]
    filter_upwards [hX 0] with n hn using hn.2 (g n)

end Saturation

/-! ## Transfer via Łoś's theorem -/

section Transfer

open FirstOrder FirstOrder.Language Structure

/-- **The diagonal embedding of a structure into its ultrapower is elementary**
(Łoś's theorem, `FirstOrder.Language.Ultraproduct.realize_formula_cast`, for
constant families). -/
def diagonalEmbedding (L : FirstOrder.Language) (M : Type*) [L.Structure M] [Nonempty M] {ι : Type*}
    (U : Ultrafilter ι) : L.ElementaryEmbedding M ((U : Filter ι).Product fun _ => M) where
  toFun m := ((fun _ => m : ι → M) : (U : Filter ι).Product fun _ => M)
  map_formula' := by
    intro n φ x
    exact (Ultraproduct.realize_formula_cast (M := fun _ : ι => M) (u := U) φ
      (fun i _ => x i)).trans eventually_const

/-- A structure and its ultrapowers are elementarily equivalent. -/
theorem elementarilyEquivalent_ultrapower (L : FirstOrder.Language) (M : Type*) [L.Structure M]
    [Nonempty M] {ι : Type*} (U : Ultrafilter ι) :
    L.ElementarilyEquivalent M ((U : Filter ι).Product fun _ => M) :=
  (diagonalEmbedding L M U).elementarilyEquivalent

/-- The first-order language of the reals with a function symbol for **every**
function `ℝ^k → ℝ` and a relation symbol for **every** relation `R ⊆ ℝ^k`. -/
def realLang : FirstOrder.Language.{0, 0} := ⟨fun k => (Fin k → ℝ) → ℝ, fun k => Set (Fin k → ℝ)⟩

/-- The standard interpretation of `realLang` in `ℝ`. -/
instance realStructure : realLang.Structure ℝ where
  funMap := fun {k} (f : (Fin k → ℝ) → ℝ) x => f x
  RelMap := fun {k} (R : Set (Fin k → ℝ)) x => x ∈ R

/-- The ultrapower `ℝ^ℕ/U` as Mathlib's `Filter.Product`; it is definitionally `ℝ*`. -/
abbrev RPow : Type := ((hyperfilter ℕ : Ultrafilter ℕ) : Filter ℕ).Product fun _ : ℕ => ℝ

theorem rpow_eq_hyperreal : RPow = ℝ* := rfl

/-- The interpretation of `realLang` in `ℝ*`: the ultrapower structure. -/
instance hyperStructure : realLang.Structure ℝ* := inferInstanceAs (realLang.Structure RPow)

/-- **The diagonal embedding `ℝ → ℝ*`, `r ↦ [r, r, …]`, is an elementary embedding**
for the full language `realLang`. -/
def starEmbedding : realLang.ElementaryEmbedding ℝ ℝ* :=
  diagonalEmbedding realLang ℝ (hyperfilter ℕ)

theorem starEmbedding_apply (r : ℝ) : starEmbedding r = (r : ℝ*) := rfl

/-- **Łoś's theorem for `ℝ*`**: a `realLang`-formula holds at `([a i n])_i` iff it holds
at `(a i n)_i` for `U`-almost every `n`. -/
theorem los_hyperreal {β : Type*} (φ : realLang.Formula β) (a : β → ℕ → ℝ) :
    φ.Realize (fun i => Hyperreal.ofSeq (a i)) ↔
      ∀ᶠ n in (hyperfilter ℕ : Filter ℕ), φ.Realize (fun i => a i n) :=
  Ultraproduct.realize_formula_cast (M := fun _ : ℕ => ℝ) (u := hyperfilter ℕ) φ a

/-- **Transfer.** A `realLang`-formula holds in `ℝ*` at standard arguments iff it
holds in `ℝ`. -/
theorem transfer {k : ℕ} (φ : realLang.Formula (Fin k)) (x : Fin k → ℝ) :
    φ.Realize (fun i => (x i : ℝ*)) ↔ φ.Realize x :=
  starEmbedding.map_formula φ x

/-- `ℝ` and `ℝ*` are elementarily equivalent in the full language `realLang`. -/
theorem elementarilyEquivalent_real_hyperreal : realLang.ElementarilyEquivalent ℝ ℝ* :=
  starEmbedding.elementarilyEquivalent

/-- **Semantic conservativity**: a `realLang`-sentence is true in `ℝ*` iff it is true
in `ℝ`. -/
theorem conservative (φ : realLang.Sentence) : ℝ* ⊨ φ ↔ ℝ ⊨ φ :=
  (starEmbedding.map_sentence φ).symm

/-- **Semantic conservativity of `ℝ*` over `ℝ`** (combined statement): every
`realLang`-sentence has the same truth value in `ℝ` and in `ℝ*`, and more generally every
`realLang`-formula has the same truth value at standard arguments (the diagonal
embedding is elementary). -/
theorem semantic_conservativity :
    (∀ φ : realLang.Sentence, ℝ* ⊨ φ ↔ ℝ ⊨ φ) ∧
    (∀ (k : ℕ) (φ : realLang.Formula (Fin k)) (x : Fin k → ℝ),
      φ.Realize (fun i => (x i : ℝ*)) ↔ φ.Realize x) ∧
    realLang.ElementarilyEquivalent ℝ ℝ* :=
  ⟨conservative, fun _ φ x => transfer φ x, elementarilyEquivalent_real_hyperreal⟩

/-- The interpretation of a function symbol in `ℝ*` is its star-extension, computed
coordinatewise. -/
theorem funMap_hyperreal {k : ℕ} (f : (Fin k → ℝ) → ℝ) (a : Fin k → ℕ → ℝ) :
    funMap (L := realLang) f (fun i => Hyperreal.ofSeq (a i)) =
      Hyperreal.ofSeq (fun n => f (fun i => a i n)) :=
  Ultraproduct.funMap_cast (M := fun _ : ℕ => ℝ) (u := hyperfilter ℕ) (L := realLang) f a

/-- The interpretation of a relation symbol in `ℝ*` is its star-extension (an internal
relation), computed coordinatewise. -/
theorem relMap_hyperreal {k : ℕ} (R : Set (Fin k → ℝ)) (a : Fin k → ℕ → ℝ) :
    RelMap (L := realLang) R (fun i => Hyperreal.ofSeq (a i)) ↔
      ∀ᶠ n in (hyperfilter ℕ : Filter ℕ), (fun i => a i n) ∈ R :=
  relMap_quotient_mk' (s := ((hyperfilter ℕ : Ultrafilter ℕ) : Filter ℕ).productSetoid
    fun _ : ℕ => ℝ) (L := realLang) R a

theorem vec2_ofSeq (a b : ℕ → ℝ) :
    ![Hyperreal.ofSeq a, Hyperreal.ofSeq b] = fun i => Hyperreal.ofSeq (![a, b] i) := by
  funext i; fin_cases i <;> rfl

theorem vec1_ofSeq (a : ℕ → ℝ) :
    ![Hyperreal.ofSeq a] = fun i => Hyperreal.ofSeq (![a] i) := by
  funext i; fin_cases i; rfl

/-- **The ultrapower realisation agrees with Mathlib's `Hyperreal` operations**:
addition, multiplication, negation, inversion, standard constants, the order, the
star-extension of unary functions and of sets. -/
theorem realisation_agrees (x y : ℝ*) (c : ℝ) (f : ℝ → ℝ) (S : Set ℝ) :
    funMap (L := realLang) (fun v : Fin 2 → ℝ => v 0 + v 1) ![x, y] = x + y ∧
    funMap (L := realLang) (fun v : Fin 2 → ℝ => v 0 * v 1) ![x, y] = x * y ∧
    funMap (L := realLang) (fun v : Fin 1 → ℝ => -v 0) ![x] = -x ∧
    funMap (L := realLang) (fun v : Fin 1 → ℝ => (v 0)⁻¹) ![x] = x⁻¹ ∧
    funMap (L := realLang) (fun _ : Fin 0 → ℝ => c) ![] = (c : ℝ*) ∧
    funMap (L := realLang) (fun v : Fin 1 → ℝ => f (v 0)) ![x] = starFun f x ∧
    (RelMap (L := realLang) {v : Fin 2 → ℝ | v 0 ≤ v 1} ![x, y] ↔ x ≤ y) ∧
    (RelMap (L := realLang) {v : Fin 2 → ℝ | v 0 < v 1} ![x, y] ↔ x < y) ∧
    (RelMap (L := realLang) {v : Fin 1 → ℝ | v 0 ∈ S} ![x] ↔ x ∈ starSet S) := by
  obtain ⟨a, rfl⟩ := Hyperreal.ofSeq_surjective x
  obtain ⟨b, rfl⟩ := Hyperreal.ofSeq_surjective y
  have h0 : (![] : Fin 0 → ℝ*) = fun i => Hyperreal.ofSeq (Fin.elim0 i) := funext (fun i => i.elim0)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [vec2_ofSeq, funMap_hyperreal]; rfl
  · rw [vec2_ofSeq, funMap_hyperreal]; rfl
  · rw [vec1_ofSeq, funMap_hyperreal]; rfl
  · rw [vec1_ofSeq, funMap_hyperreal]; rfl
  · rw [h0, funMap_hyperreal]; rfl
  · rw [vec1_ofSeq, funMap_hyperreal]; rfl
  · rw [vec2_ofSeq, relMap_hyperreal, Hyperreal.ofSeq_le_ofSeq]; rfl
  · rw [vec2_ofSeq, relMap_hyperreal, Hyperreal.ofSeq_lt_ofSeq]; rfl
  · rw [vec1_ofSeq, relMap_hyperreal]
    exact (mem_starSet S a).symm

/-! ### The internal definition principle

The language `iLang` has a symbol for every *internal* function and relation: a
function symbol of arity `k` is a sequence `F : ℕ → (ℝ^k → ℝ)` and a relation symbol
a sequence `R : ℕ → Set ℝ^k`.  Its interpretation in coordinate `n` is
`(F n, R n)`, and in `ℝ*` (the ultraproduct of the coordinate structures) it is the
internal function `[F n]` and the internal relation `[R n]`.  Internal sets and
internal elements (`0`-ary function symbols) are thus available as parameters. -/

/-- The language of internal functions and relations on `ℝ*`. -/
def iLang : FirstOrder.Language.{0, 0} := ⟨fun k => ℕ → (Fin k → ℝ) → ℝ, fun k => ℕ → Set (Fin k → ℝ)⟩

/-- Coordinate `n` of the ultraproduct: `ℝ` with the `n`-th interpretation. -/
def Coord (_n : ℕ) : Type := ℝ

instance coordStructure (n : ℕ) : iLang.Structure (Coord n) where
  funMap := fun {k} (F : ℕ → (Fin k → ℝ) → ℝ) x => F n x
  RelMap := fun {k} (R : ℕ → Set (Fin k → ℝ)) x => x ∈ R n

instance (n : ℕ) : Nonempty (Coord n) := ⟨(0 : ℝ)⟩

/-- `ℝ* = Ult ℝ` as the ultraproduct of the coordinate `iLang`-structures. -/
instance iStructure : iLang.Structure (Ult ℝ) :=
  inferInstanceAs (iLang.Structure (((hyperfilter ℕ : Ultrafilter ℕ) : Filter ℕ).Product Coord))

/-- In `ℝ*`, a function symbol `F` of `iLang` is the internal function `[F n]`. -/
theorem funMap_iLang {k : ℕ} (F : ℕ → (Fin k → ℝ) → ℝ) (a : Fin k → ℕ → ℝ) :
    funMap (L := iLang) F (fun i => (a i : Ult ℝ)) =
      ((fun n => F n (fun i => a i n) : ℕ → ℝ) : Ult ℝ) :=
  Ultraproduct.funMap_cast (M := Coord) (u := hyperfilter ℕ) (L := iLang) F a

/-- In `ℝ*`, a relation symbol `R` of `iLang` is the internal relation `[R n]`. -/
theorem relMap_iLang {k : ℕ} (R : ℕ → Set (Fin k → ℝ)) (a : Fin k → ℕ → ℝ) :
    RelMap (L := iLang) R (fun i => (a i : Ult ℝ)) ↔
      ∀ᶠ n in (hyperfilter ℕ : Filter ℕ), (fun i => a i n) ∈ R n :=
  relMap_quotient_mk' (s := ((hyperfilter ℕ : Ultrafilter ℕ) : Filter ℕ).productSetoid Coord)
    (L := iLang) R a

theorem vec1_coe (a : ℕ → ℝ) : ![(a : Ult ℝ)] = fun i => ((![a] i : ℕ → ℝ) : Ult ℝ) := by
  funext i; fin_cases i; rfl

/-- Every internal set `[B n] ⊆ ℝ*` is named by a unary relation symbol of `iLang`. -/
def internalRel (B : ℕ → Set ℝ) : iLang.Relations 1 :=
  (fun n => {v : Fin 1 → ℝ | v 0 ∈ B n} : ℕ → Set (Fin 1 → ℝ))

theorem relMap_internalRel (B : ℕ → Set ℝ) (x : Ult ℝ) :
    RelMap (L := iLang) (internalRel B) ![x] ↔ x ∈ internal B := by
  obtain ⟨a, rfl⟩ := exists_rep x
  rw [vec1_coe]
  exact (relMap_iLang (k := 1) (fun n => {v : Fin 1 → ℝ | v 0 ∈ B n}) _).trans
    (mem_internal B a).symm

/-- Every internal function `[F n] : ℝ* → ℝ*` is named by a unary function symbol. -/
def internalFunSym (F : ℕ → ℝ → ℝ) : iLang.Functions 1 :=
  (fun n (v : Fin 1 → ℝ) => F n (v 0) : ℕ → (Fin 1 → ℝ) → ℝ)

theorem funMap_internalFunSym (F : ℕ → ℝ → ℝ) (x : Ult ℝ) :
    funMap (L := iLang) (internalFunSym F) ![x] = ifun F x := by
  obtain ⟨a, rfl⟩ := exists_rep x
  rw [vec1_coe]
  exact funMap_iLang (k := 1) (fun n (v : Fin 1 → ℝ) => F n (v 0)) _

/-- **Łoś's theorem for the internal language**: an `iLang`-formula holds in `ℝ*` at
`([a i n])_i` iff it holds in coordinate `n` at `(a i n)_i` for `U`-almost every `n`. -/
theorem los_iLang {β : Type*} (φ : iLang.Formula β) (a : β → ℕ → ℝ) :
    φ.Realize (fun i => (a i : Ult ℝ)) ↔
      ∀ᶠ n in (hyperfilter ℕ : Filter ℕ), φ.Realize (M := Coord n) (fun i => a i n) :=
  Ultraproduct.realize_formula_cast (M := Coord) (u := hyperfilter ℕ) φ a

/-- **Internal definition principle.** Let `φ(x, p₁, …, p_m)` be a first-order formula
of `iLang` (so it may mention any internal sets, relations and functions as symbols)
and let `p_j = [q j n]` be internal parameters.  Then `{x ∈ ℝ* : φ(x, p)}` is the
internal set `[{r : φ_n(r, q n)}]`, where `φ_n` is `φ` read in coordinate `n`. -/
theorem internal_definition_principle {m : ℕ} (φ : iLang.Formula (Fin (m + 1)))
    (q : Fin m → ℕ → ℝ) :
    {x : Ult ℝ | φ.Realize (Fin.cons x (fun j => (q j : Ult ℝ)) : Fin (m + 1) → Ult ℝ)} =
      internal (fun n => {r : ℝ | φ.Realize (M := Coord n)
        (Fin.cons r (fun j => q j n) : Fin (m + 1) → ℝ)}) := by
  ext x
  obtain ⟨u, rfl⟩ := exists_rep x
  have h1 : (Fin.cons (u : Ult ℝ) (fun j => (q j : Ult ℝ)) : Fin (m + 1) → Ult ℝ) =
      fun i => (((Fin.cons u q : Fin (m + 1) → ℕ → ℝ) i : ℕ → ℝ) : Ult ℝ) := by
    funext i; refine Fin.cases rfl (fun j => rfl) i
  have h2 : ∀ n, (Fin.cons (u n) (fun j => q j n) : Fin (m + 1) → ℝ) =
      fun i => (Fin.cons u q : Fin (m + 1) → ℕ → ℝ) i n := by
    intro n; funext i; refine Fin.cases rfl (fun j => rfl) i
  rw [Set.mem_ofPred_eq, h1, los_iLang, mem_internal]
  simp only [Set.mem_ofPred_eq, h2]

/-- **Internal definition principle**, closure form: for an internal `B ⊆ ℝ*` and
internal parameters `p`, the set `{x ∈ B : φ(x, p)}` is internal. -/
theorem isInternal_definable {m : ℕ} (φ : iLang.Formula (Fin (m + 1))) (p : Fin m → Ult ℝ)
    (B : Set (Ult ℝ)) (hB : IsInternal B) :
    IsInternal (B ∩ {x : Ult ℝ | φ.Realize (Fin.cons x p : Fin (m + 1) → Ult ℝ)}) := by
  choose q hq using fun j => exists_rep (p j)
  have hp : p = fun j => (q j : Ult ℝ) := funext fun j => (hq j).symm
  subst hp
  refine hB.inter ?_
  rw [internal_definition_principle φ q]
  exact isInternal_internal _

end Transfer

/-! ## Infinitesimal nearness in the ultrapower of a metric space -/

section Metric

open Topology

variable {X Y : Type*} [MetricSpace X] [MetricSpace Y]

/-- The `ℝ*`-valued distance on `Ult X`: `hdist [u n] [v n] = [dist (u n) (v n)]`. -/
def hdist (x y : Ult X) : ℝ* := Germ.map₂ dist x y

theorem hdist_coe (u v : ℕ → X) :
    hdist (u : Ult X) (v : Ult X) = Hyperreal.ofSeq (fun n => dist (u n) (v n)) := rfl

theorem hdist_const (a b : X) :
    hdist (Germ.const a : Ult X) (Germ.const b) = ((dist a b : ℝ) : ℝ*) := rfl

theorem hdist_nonneg (x y : Ult X) : 0 ≤ hdist x y := by
  obtain ⟨u, rfl⟩ := exists_rep x; obtain ⟨v, rfl⟩ := exists_rep y
  rw [hdist_coe]
  exact Hyperreal.ofSeq_le_ofSeq.2 (Eventually.of_forall fun n => dist_nonneg)

theorem hdist_comm (x y : Ult X) : hdist x y = hdist y x := by
  obtain ⟨u, rfl⟩ := exists_rep x; obtain ⟨v, rfl⟩ := exists_rep y
  rw [hdist_coe, hdist_coe]; simp only [dist_comm]

theorem hdist_triangle (x y z : Ult X) : hdist x z ≤ hdist x y + hdist y z := by
  obtain ⟨u, rfl⟩ := exists_rep x; obtain ⟨v, rfl⟩ := exists_rep y
  obtain ⟨w, rfl⟩ := exists_rep z
  rw [hdist_coe, hdist_coe, hdist_coe]
  exact Hyperreal.ofSeq_le_ofSeq.2 (Eventually.of_forall fun n => dist_triangle _ _ _)

/-- Infinitesimal nearness `x ≈ y` in `Ult X`. -/
def Near (x y : Ult X) : Prop := IsInfinitesimal (hdist x y)

theorem near_coe_iff (u v : ℕ → X) :
    Near (u : Ult X) (v : Ult X) ↔
      ∀ r : ℝ, 0 < r → ∀ᶠ n in (hyperfilter ℕ : Filter ℕ), dist (u n) (v n) < r := by
  unfold Near; rw [hdist_coe, isInfinitesimal_ofSeq_iff]
  simp only [abs_dist]

/-- `[u n] ≈ a` for standard `a` iff `u → a` along the ultrafilter. -/
theorem near_const_iff_tendsto (u : ℕ → X) (a : X) :
    Near (u : Ult X) (Germ.const a) ↔ Tendsto u (hyperfilter ℕ : Filter ℕ) (𝓝 a) := by
  rw [Metric.tendsto_nhds]
  exact near_coe_iff u (fun _ => a)

theorem near_refl (x : Ult X) : Near x x := by
  obtain ⟨u, rfl⟩ := exists_rep x
  rw [near_coe_iff]; intro r hr; simp [hr]

theorem Near.symm {x y : Ult X} (h : Near x y) : Near y x := by
  unfold Near at *; rwa [hdist_comm]

theorem Near.trans {x y z : Ult X} (h1 : Near x y) (h2 : Near y z) : Near x z := by
  unfold Near at *
  refine (h1.add h2).of_abs_le ?_
  rw [abs_of_nonneg (hdist_nonneg _ _), abs_of_nonneg (add_nonneg (hdist_nonneg _ _)
    (hdist_nonneg _ _))]
  exact hdist_triangle _ _ _

/-- Two standard points are infinitely close only if they are equal. -/
theorem near_const_const {a b : X} (h : Near (Germ.const a : Ult X) (Germ.const b)) : a = b := by
  unfold Near at h; rw [hdist_const] at h
  exact dist_eq_zero.1 (coe_eq_zero_of_isInfinitesimal h)

theorem near_of_hdist_le {x y : Ult X} {δ : ℝ*} (hδ : IsInfinitesimal δ) (h : hdist x y ≤ δ) :
    Near x y := by
  unfold Near
  refine hδ.of_abs_le ?_
  rw [abs_of_nonneg (hdist_nonneg _ _)]
  exact h.trans (le_abs_self δ)

theorem Near.hdist_lt {x y : Ult X} (h : Near x y) {r : ℝ} (hr : 0 < r) :
    hdist x y < (r : ℝ*) := by
  have := IsInfinitesimal.abs_lt h hr
  rwa [abs_of_nonneg (hdist_nonneg _ _)] at this

/-- **Robinson's characterisation of compactness.** A standard set `K` of a metric space
is compact iff every point of `*K` is infinitely close to a point of `K`. -/
theorem isCompact_iff_near (K : Set X) :
    IsCompact K ↔ ∀ y ∈ starSet K, ∃ x ∈ K, Near y (Germ.const x) := by
  constructor
  · intro hK y hy
    obtain ⟨u, rfl⟩ := exists_rep y
    rw [mem_starSet] at hy
    obtain ⟨x, hx, hle⟩ := hK.ultrafilter_le_nhds (Ultrafilter.map u (hyperfilter ℕ))
      (by rw [Ultrafilter.coe_map, Filter.le_principal_iff]; exact hy)
    refine ⟨x, hx, (near_const_iff_tendsto u x).2 ?_⟩
    rw [Ultrafilter.coe_map] at hle; exact hle
  · intro H
    rw [isCompact_iff_isSeqCompact]
    intro u hu
    obtain ⟨x, hx, hnear⟩ := H (u : Ult X)
      ((mem_starSet K u).2 (Eventually.of_forall hu))
    rw [near_const_iff_tendsto] at hnear
    refine ⟨x, hx, MapClusterPt.tendsto_subseq ?_⟩
    have h1 : Filter.map u (hyperfilter ℕ) ≤ 𝓝 x := hnear
    have h2 : Filter.map u (hyperfilter ℕ) ≤ Filter.map u atTop :=
      Filter.map_mono Nat.hyperfilter_le_atTop
    exact Filter.NeBot.mono (by infer_instance) (le_inf h1 h2)

/-- In a proper metric space, a point at finite distance from a standard point is
near-standard. -/
theorem exists_near_of_isFinite [ProperSpace Y] (y : Ult Y) (y₀ : Y)
    (h : IsFinite (hdist y (Germ.const y₀))) : ∃ b : Y, Near y (Germ.const b) := by
  obtain ⟨B, hB⟩ := (isFinite_iff_abs_le _).1 h
  obtain ⟨w, rfl⟩ := exists_rep y
  rw [abs_of_nonneg (hdist_nonneg _ _)] at hB
  have hB' : Hyperreal.ofSeq (fun n => dist (w n) y₀) ≤ (B : ℝ*) := hB
  have hmem : (w : Ult Y) ∈ starSet (Metric.closedBall y₀ B) := by
    rw [mem_starSet]
    filter_upwards [ofSeq_le_const.1 hB'] with n hn using hn
  obtain ⟨b, -, hb⟩ := (isCompact_iff_near _).1 (isCompact_closedBall y₀ B) _ hmem
  exact ⟨b, hb⟩

/-- The internal set of moduli of continuity: for an internal domain `[D n]`, an
internal map `[F n]` and a standard `η`, the set of `δ` such that
`0 < δ → ∀ c c' ∈ D, hdist c c' ≤ δ → hdist (F c) (F c') < η` is internal (a
hand-made instance of the internal definition principle). -/
theorem modulus_internal (D : ℕ → Set X) (F : ℕ → X → Y) (η : ℝ) :
    ({δ : ℝ* | 0 < δ → ∀ c ∈ internal D, ∀ c' ∈ internal D,
        hdist c c' ≤ δ → hdist (ifun F c) (ifun F c') < (η : ℝ*)} : Set ℝ*) =
      internal (fun n => {d : ℝ | 0 < d → ∀ x ∈ D n, ∀ x' ∈ D n,
        dist x x' ≤ d → dist (F n x) (F n x') < η}) := by
  ext δ
  obtain ⟨w, rfl⟩ := Hyperreal.ofSeq_surjective δ
  rw [Set.mem_ofPred_eq]
  change _ ↔ ((w : ℕ → ℝ) : Ult ℝ) ∈ internal _
  rw [mem_internal]
  constructor
  · intro h
    by_contra hne
    rw [← Ultrafilter.eventually_not] at hne
    have hne' : ∀ᶠ n in (hyperfilter ℕ : Filter ℕ), 0 < w n ∧ ∃ p : X × X, p.1 ∈ D n ∧
        p.2 ∈ D n ∧ dist p.1 p.2 ≤ w n ∧ η ≤ dist (F n p.1) (F n p.2) := by
      filter_upwards [hne] with n hn
      simp only [not_imp, not_forall, not_lt] at hn
      obtain ⟨h0, x, hx, x', hx', h1, h2⟩ := hn
      exact ⟨h0, (x, x'), hx, hx', h1, h2⟩
    obtain ⟨n₀, -, p₀, -⟩ := hne'.exists
    classical
    let P : ℕ → X × X := fun n => if hp : ∃ p : X × X, p.1 ∈ D n ∧
        p.2 ∈ D n ∧ dist p.1 p.2 ≤ w n ∧ η ≤ dist (F n p.1) (F n p.2) then hp.choose else p₀
    have hP : ∀ᶠ n in (hyperfilter ℕ : Filter ℕ), (P n).1 ∈ D n ∧
        (P n).2 ∈ D n ∧ dist (P n).1 (P n).2 ≤ w n ∧ η ≤ dist (F n (P n).1) (F n (P n).2) := by
      filter_upwards [hne'] with n hn
      simp only [P, hn.2, ↓reduceDIte]
      exact hn.2.choose_spec
    have hpos : (0 : ℝ*) < Hyperreal.ofSeq w :=
      Hyperreal.ofSeq_lt_ofSeq.2 (by filter_upwards [hne'] with n hn using hn.1)
    have hlt := h hpos (fun n => (P n).1 : ℕ → X)
      ((mem_internal D _).2 (by filter_upwards [hP] with n hn using hn.1))
      (fun n => (P n).2 : ℕ → X)
      ((mem_internal D _).2 (by filter_upwards [hP] with n hn using hn.2.1))
      (by rw [hdist_coe]; exact Hyperreal.ofSeq_le_ofSeq.2
            (by filter_upwards [hP] with n hn using hn.2.2.1))
    rw [ifun_coe, ifun_coe, hdist_coe, ofSeq_lt_const] at hlt
    obtain ⟨n, h1, h2⟩ := (hlt.and hP).exists
    exact absurd h2.2.2.2 (not_le.2 h1)
  · intro h hpos c hc c' hc' hle
    obtain ⟨u, rfl⟩ := exists_rep c
    obtain ⟨v, rfl⟩ := exists_rep c'
    rw [mem_internal] at hc hc'
    rw [hdist_coe] at hle
    rw [ifun_coe, ifun_coe, hdist_coe, ofSeq_lt_const]
    have hpos' : ∀ᶠ n in (hyperfilter ℕ : Filter ℕ), 0 < w n := Hyperreal.ofSeq_lt_ofSeq.1 hpos
    filter_upwards [h, hc, hc', Hyperreal.ofSeq_le_ofSeq.1 hle, hpos'] with n h1 h2 h3 h4 h5
    exact h1 h5 (u n) h2 (v n) h3 h4

/-- **Shadows of S-continuous internal functions** (general form).  Let `K` be a
subset of a metric space `X`, `D ⊆ Ult X` an internal set such that every point
of `K` is infinitely close to a point of `D`, and `F = [F n]` an internal function
with values in a proper metric space `Y` that is finite at every point of `D` and
S-continuous on `D` (`c ≈ c'` in `D` implies `F c ≈ F c'`).  Then there is a
continuous `f : K → Y` with `F c ≈ f x` whenever `c ∈ D`, `x ∈ K` and `c ≈ x`. -/
theorem shadow_of_S_continuous [ProperSpace Y] (K : Set X)
    (D : Set (Ult X)) (hD : IsInternal D)
    (hdense : ∀ x ∈ K, ∃ c ∈ D, Near c (Germ.const x))
    (F : ℕ → X → Y) (y₀ : Y) (hfin : ∀ c ∈ D, IsFinite (hdist (ifun F c) (Germ.const y₀)))
    (hS : ∀ c ∈ D, ∀ c' ∈ D, Near c c' → Near (ifun F c) (ifun F c')) :
    ∃ f : X → Y, ContinuousOn f K ∧
      ∀ c ∈ D, ∀ x ∈ K, Near c (Germ.const x) → Near (ifun F c) (Germ.const (f x)) := by
  classical
  -- the chosen lattice points and the shadow function
  have hc : ∀ x, ∃ c, x ∈ K → c ∈ D ∧ Near c (Germ.const x) := by
    intro x
    by_cases hx : x ∈ K
    · obtain ⟨c, hcD, hcx⟩ := hdense x hx; exact ⟨c, fun _ => ⟨hcD, hcx⟩⟩
    · exact ⟨Germ.const x, fun h => absurd h hx⟩
  choose c hcspec using hc
  have hb : ∀ x, ∃ b : Y, x ∈ K → Near (ifun F (c x)) (Germ.const b) := by
    intro x
    by_cases hx : x ∈ K
    · obtain ⟨b, hb⟩ := exists_near_of_isFinite _ y₀ (hfin _ (hcspec x hx).1)
      exact ⟨b, fun _ => hb⟩
    · exact ⟨y₀, fun h => absurd h hx⟩
  choose f hf using hb
  have key : ∀ c' ∈ D, ∀ x ∈ K, Near c' (Germ.const x) →
      Near (ifun F c') (Germ.const (f x)) := by
    intro c' hc' x hx hnear
    have h1 : Near c' (c x) := hnear.trans (hcspec x hx).2.symm
    exact (hS c' hc' (c x) (hcspec x hx).1 h1).trans (hf x hx)
  refine ⟨f, ?_, key⟩
  -- uniform modulus of continuity via underspill
  have hmod : ∀ η : ℝ, 0 < η → ∃ r : ℝ, 0 < r ∧ ∀ x ∈ K, ∀ x' ∈ K, dist x x' < r →
      dist (f x) (f x') ≤ η := by
    intro η hη
    obtain ⟨Dn, rfl⟩ := hD
    have hT := modulus_internal Dn F η
    obtain ⟨r, hr, hrT⟩ := underspill_real _ ⟨_, hT⟩ (by
      intro δ hδ hinf
      show 0 < δ → _
      intro _ c₁ hc₁ c₂ hc₂ hle
      exact (hS c₁ hc₁ c₂ hc₂ (near_of_hdist_le hinf hle)).hdist_lt hη)
    refine ⟨r, hr, fun x hx x' hx' hxx' => ?_⟩
    have hg : 0 < r - dist x x' := sub_pos.2 hxx'
    have hcx := (hcspec x hx).2
    have hcx' := (hcspec x' hx').2
    have hle : hdist (c x) (c x') ≤ (r : ℝ*) := by
      have t1 := hdist_triangle (c x) (Germ.const x) (c x')
      have t2 := hdist_triangle (Germ.const x : Ult X) (Germ.const x') (c x')
      have e1 := hcx.hdist_lt (half_pos hg)
      have e2 := hcx'.hdist_lt (half_pos hg)
      rw [hdist_comm (c x') _] at e2
      rw [hdist_const] at t2
      have : ((r : ℝ) : ℝ*) = ((dist x x' : ℝ) : ℝ*) + (((r - dist x x') / 2 : ℝ) : ℝ*) +
          (((r - dist x x') / 2 : ℝ) : ℝ*) := by
        rw [← Hyperreal.coe_add, ← Hyperreal.coe_add]; congr 1; ring
      rw [this]
      linarith
    have hlt := hrT (Hyperreal.coe_pos.2 hr) (c x) (hcspec x hx).1 (c x') (hcspec x' hx').1 hle
    -- compare the standard distance with the internal one
    have n1 := (hf x hx).symm
    have n2 := hf x' hx'
    have hsum : IsInfinitesimal (hdist (Germ.const (f x) : Ult Y) (ifun F (c x)) +
        hdist (ifun F (c x')) (Germ.const (f x'))) := n1.add n2
    have tri : ((dist (f x) (f x') : ℝ) : ℝ*) < (η : ℝ*) +
        (hdist (Germ.const (f x) : Ult Y) (ifun F (c x)) +
          hdist (ifun F (c x')) (Germ.const (f x'))) := by
      rw [← hdist_const]
      have t1 := hdist_triangle (Germ.const (f x) : Ult Y) (ifun F (c x)) (Germ.const (f x'))
      have t2 := hdist_triangle (ifun F (c x)) (ifun F (c x')) (Germ.const (f x'))
      linarith
    exact le_of_lt_add_infinitesimal hsum tri
  rw [Metric.continuousOn_iff]
  intro x hx η hη
  obtain ⟨r, hr, hmod'⟩ := hmod (η / 2) (half_pos hη)
  exact ⟨r, hr, fun x' hx' hd => lt_of_le_of_lt (hmod' x' hx' x hx hd) (half_lt_self hη)⟩

/-- Every point of `D ⊆ *K` (with `K` compact) has a standard part in `K`. -/
theorem exists_near_of_mem_starSet {K : Set X} (hK : IsCompact K) {c : Ult X}
    (hc : c ∈ starSet K) : ∃ x ∈ K, Near c (Germ.const x) :=
  (isCompact_iff_near K).1 hK c hc

end Metric

/-! ## Internal functions on the hyperfinite lattice of `[a,b]` (Chapter 6) -/

section Lattice

open ArchimedeanClass

/-- An internal function `[F n]` viewed as a map `ℝ* → ℝ*`. -/
def hfun (F : ℕ → ℝ → ℝ) : ℝ* → ℝ* := fun x => ifun F x

theorem hfun_ofSeq (F : ℕ → ℝ → ℝ) (u : ℕ → ℝ) :
    hfun F (Hyperreal.ofSeq u) = Hyperreal.ofSeq (fun n => F n (u n)) := rfl

/-- The lattice `𝕃 = 2ε·ℤ* ⊆ ℝ*` of granule `ε`. -/
def lattice (ε : ℝ*) : Set ℝ* :=
  {x | ∃ K : ℕ → ℤ, x = 2 * ε * Hyperreal.ofSeq (fun n => (K n : ℝ))}

/-- The lattice points in `[a, b]`. -/
def latIcc (ε : ℝ*) (a b : ℝ) : Set ℝ* := {x | x ∈ lattice ε ∧ (a : ℝ*) ≤ x ∧ x ≤ (b : ℝ*)}

/-- `𝕃 ∩ [a,b]` is the internal set `[{2 e n k : k ∈ ℤ} ∩ [a,b]]`; it is hyperfinite. -/
theorem latIcc_eq_internal (e : ℕ → ℝ) (a b : ℝ) :
    (latIcc (Hyperreal.ofSeq e) a b : Set ℝ*) =
      internal (fun n => {x : ℝ | (∃ k : ℤ, x = 2 * e n * k) ∧ a ≤ x ∧ x ≤ b}) := by
  ext x
  obtain ⟨u, rfl⟩ := Hyperreal.ofSeq_surjective x
  change _ ↔ ((u : ℕ → ℝ) : Ult ℝ) ∈ internal _
  rw [mem_internal]
  constructor
  · rintro ⟨⟨K, hK⟩, ha, hb⟩
    have hK' : ∀ᶠ n in (hyperfilter ℕ : Filter ℕ), u n = 2 * e n * K n := Germ.coe_eq.1 hK
    filter_upwards [hK', Hyperreal.ofSeq_le_ofSeq.1 ha, Hyperreal.ofSeq_le_ofSeq.1 hb]
      with n h1 h2 h3
    exact ⟨⟨K n, h1⟩, h2, h3⟩
  · intro h
    classical
    let K : ℕ → ℤ := fun n => if hk : ∃ k : ℤ, u n = 2 * e n * k then hk.choose else 0
    refine ⟨⟨K, Germ.coe_eq.2 ?_⟩, Hyperreal.ofSeq_le_ofSeq.2 ?_, Hyperreal.ofSeq_le_ofSeq.2 ?_⟩
    · filter_upwards [h] with n hn
      simp only [K, hn.1, ↓reduceDIte]
      exact hn.1.choose_spec
    · filter_upwards [h] with n hn using hn.2.1
    · filter_upwards [h] with n hn using hn.2.2

/-- The lattice points of `[a,b]` form a hyperfinite set. -/
theorem latIcc_hyperfinite (e : ℕ → ℝ) (he : 0 < Hyperreal.ofSeq e) (a b : ℝ) :
    IsHyperfinite (latIcc (Hyperreal.ofSeq e) a b : Set (Ult ℝ)) := by
  rw [latIcc_eq_internal]
  refine isHyperfinite_of_eventually_finite _ ?_
  have he' : ∀ᶠ n in (hyperfilter ℕ : Filter ℕ), 0 < e n :=
    Hyperreal.ofSeq_lt_ofSeq.1 he
  filter_upwards [he'] with n hn
  refine ((Set.finite_Icc ⌈a / (2 * e n)⌉ ⌊b / (2 * e n)⌋).image
    (fun k : ℤ => 2 * e n * k)).subset ?_
  rintro x ⟨⟨k, rfl⟩, h1, h2⟩
  have h2e : 0 < 2 * e n := by positivity
  refine ⟨k, ⟨Int.ceil_le.2 ?_, Int.le_floor.2 ?_⟩, rfl⟩
  · rw [div_le_iff₀ h2e]; linarith
  · rw [le_div_iff₀ h2e]; linarith

theorem isInfinitesimal_abs_iff (x : ℝ*) : IsInfinitesimal |x| ↔ IsInfinitesimal x := by
  unfold IsInfinitesimal; rw [ArchimedeanClass.mk_abs]

theorem isFinite_abs_iff (x : ℝ*) : IsFinite |x| ↔ IsFinite x := by
  unfold IsFinite; rw [ArchimedeanClass.mk_abs]

/-- On `ℝ* = Ult ℝ`, `hdist x y = |x - y|`. -/
theorem hdist_real (x y : ℝ*) : hdist (X := ℝ) x y = |x - y| := by
  obtain ⟨u, rfl⟩ := Hyperreal.ofSeq_surjective x
  obtain ⟨v, rfl⟩ := Hyperreal.ofSeq_surjective y
  show Hyperreal.ofSeq (fun n => dist (u n) (v n)) = |Hyperreal.ofSeq (fun n => u n - v n)|
  rw [abs_ofSeq]; rfl

theorem near_real_iff (x y : ℝ*) : Near (X := ℝ) x y ↔ IsInfinitesimal (x - y) := by
  unfold Near; rw [hdist_real, isInfinitesimal_abs_iff]

/-- A standard function continuous within `K` at `x₀` maps points of `*K` near `x₀` to
points near `f x₀`. -/
theorem starFun_near_of_continuousWithinAt {X Y : Type*} [MetricSpace X] [MetricSpace Y]
    (f : X → Y) (K : Set X) (x₀ : X) (hf : ContinuousWithinAt f K x₀) (c : Ult X)
    (hc : c ∈ starSet K) (hnear : Near c (Germ.const x₀)) :
    Near (starFun f c) (Germ.const (f x₀)) := by
  obtain ⟨u, rfl⟩ := exists_rep c
  rw [mem_starSet] at hc
  rw [near_const_iff_tendsto] at hnear
  have hu : Tendsto u (hyperfilter ℕ : Filter ℕ) (nhdsWithin x₀ K) :=
    tendsto_nhdsWithin_iff.2 ⟨hnear, hc⟩
  exact (near_const_iff_tendsto (fun n => f (u n)) (f x₀)).2 (hf.tendsto.comp hu)

theorem latIcc_subset_starSet (ε : ℝ*) (a b : ℝ) :
    (latIcc ε a b : Set (Ult ℝ)) ⊆ starSet (Set.Icc a b) := by
  intro x hx
  obtain ⟨u, rfl⟩ := exists_rep x
  refine (mem_starSet _ u).2 ?_
  obtain ⟨-, ha, hb⟩ := hx
  filter_upwards [Hyperreal.ofSeq_le_ofSeq.1 ha, Hyperreal.ofSeq_le_ofSeq.1 hb] with n h1 h2
  exact ⟨h1, h2⟩

/-- A lattice point `2 e n K n` within one step `2 e n` of `r` is infinitely close to
`r`. -/
theorem lattice_point_near (e : ℕ → ℝ) (hinf : IsInfinitesimal (Hyperreal.ofSeq e)) (r : ℝ)
    (K : ℕ → ℤ) (hK : ∀ᶠ n in (hyperfilter ℕ : Filter ℕ), |2 * e n * K n - r| ≤ 2 * e n) :
    IsInfinitesimal (Hyperreal.ofSeq (fun n => 2 * e n * K n) - (r : ℝ*)) := by
  show IsInfinitesimal (Hyperreal.ofSeq (fun n => 2 * e n * K n - r))
  rw [isInfinitesimal_ofSeq_iff] at hinf ⊢
  intro t ht
  filter_upwards [hK, hinf (t / 3) (by positivity)] with n h1 h2
  have : e n < t / 3 := lt_of_le_of_lt (le_abs_self _) h2
  linarith

/-- Every standard point of `[a,b]` (`a < b`) is infinitely close to a lattice point
of `[a,b]`. -/
theorem exists_latIcc_near (ε : ℝ*) (hε0 : 0 < ε) (hε : IsInfinitesimal ε) {a b : ℝ}
    (hab : a < b) {r : ℝ} (hr : r ∈ Set.Icc a b) :
    ∃ c ∈ latIcc ε a b, IsInfinitesimal (c - (r : ℝ*)) := by
  obtain ⟨e, rfl⟩ := Hyperreal.ofSeq_surjective ε
  have he : ∀ᶠ n in (hyperfilter ℕ : Filter ℕ), 0 < e n := Hyperreal.ofSeq_lt_ofSeq.1 hε0
  have hsmall : ∀ t : ℝ, 0 < t → ∀ᶠ n in (hyperfilter ℕ : Filter ℕ), e n < t := by
    intro t ht
    filter_upwards [(isInfinitesimal_ofSeq_iff e).1 hε t ht] with n hn
    exact lt_of_le_of_lt (le_abs_self _) hn
  by_cases har : a < r
  · -- round down
    let K : ℕ → ℤ := fun n => ⌊r / (2 * e n)⌋
    have hK : ∀ᶠ n in (hyperfilter ℕ : Filter ℕ),
        2 * e n * K n ≤ r ∧ r - 2 * e n < 2 * e n * K n := by
      filter_upwards [he] with n hn
      have h2e : 0 < 2 * e n := by positivity
      have h1 := Int.floor_le (r / (2 * e n))
      have h2 := Int.lt_floor_add_one (r / (2 * e n))
      rw [le_div_iff₀ h2e] at h1
      rw [div_lt_iff₀ h2e] at h2
      exact ⟨by simp only [K]; linarith, by simp only [K]; linarith⟩
    refine ⟨Hyperreal.ofSeq (fun n => 2 * e n * K n), ⟨⟨K, rfl⟩, ?_, ?_⟩,
      lattice_point_near e hε r K ?_⟩
    · refine Hyperreal.ofSeq_le_ofSeq.2 ?_
      filter_upwards [hK, hsmall ((r - a) / 2) (by linarith)] with n h1 h2
      show a ≤ 2 * e n * K n
      linarith [h1.2]
    · refine Hyperreal.ofSeq_le_ofSeq.2 ?_
      filter_upwards [hK] with n h1
      show 2 * e n * K n ≤ b
      linarith [h1.1, hr.2]
    · filter_upwards [hK] with n h1
      rw [abs_le]; constructor <;> linarith [h1.1, h1.2]
  · -- `r = a < b`: round up
    have hrb : r < b := by
      have : r = a := le_antisymm (not_lt.1 har) hr.1
      rw [this]; exact hab
    let K : ℕ → ℤ := fun n => ⌈r / (2 * e n)⌉
    have hK : ∀ᶠ n in (hyperfilter ℕ : Filter ℕ),
        r ≤ 2 * e n * K n ∧ 2 * e n * K n < r + 2 * e n := by
      filter_upwards [he] with n hn
      have h2e : 0 < 2 * e n := by positivity
      have h1 := Int.le_ceil (r / (2 * e n))
      have h2 := Int.ceil_lt_add_one (r / (2 * e n))
      rw [div_le_iff₀ h2e] at h1
      have h2' := mul_lt_mul_of_pos_right h2 h2e
      rw [add_mul, div_mul_cancel₀ _ h2e.ne', one_mul] at h2'
      exact ⟨by simp only [K]; linarith, by simp only [K]; linarith⟩
    refine ⟨Hyperreal.ofSeq (fun n => 2 * e n * K n), ⟨⟨K, rfl⟩, ?_, ?_⟩,
      lattice_point_near e hε r K ?_⟩
    · refine Hyperreal.ofSeq_le_ofSeq.2 ?_
      filter_upwards [hK] with n h1
      show a ≤ 2 * e n * K n
      linarith [h1.1, hr.1]
    · refine Hyperreal.ofSeq_le_ofSeq.2 ?_
      filter_upwards [hK, hsmall ((b - r) / 2) (by linarith)] with n h1 h2
      show 2 * e n * K n ≤ b
      linarith [h1.2]
    · filter_upwards [hK] with n h1
      rw [abs_le]; constructor <;> linarith [h1.1, h1.2]

/-- **Shadows of S-continuous lattice functions** (Chapter 6).  Let `ε` be a positive
infinitesimal, `a < b` standard, and `F = [F n]` an internal function that is finite
at every lattice point of `[a,b]` and S-continuous there (`x ≈ y ⇒ F x ≈ F y`).  Then
there is a continuous `f : [a,b] → ℝ` such that `f r = st F(c)` for every lattice point
`c ∈ [a,b]` with `c ≈ r` (such `c` exist by `exists_latIcc_near`), and
`F x ≈ f(st x)` for every lattice point `x ∈ [a,b]`. -/
theorem shadow_lattice_function (ε : ℝ*) (hε0 : 0 < ε) (hε : IsInfinitesimal ε) {a b : ℝ}
    (hab : a < b) (F : ℕ → ℝ → ℝ)
    (hS : ∀ x ∈ latIcc ε a b, ∀ y ∈ latIcc ε a b, IsInfinitesimal (x - y) →
      IsInfinitesimal (hfun F x - hfun F y))
    (hfin : ∀ x ∈ latIcc ε a b, IsFinite (hfun F x)) :
    ∃ f : ℝ → ℝ, ContinuousOn f (Set.Icc a b) ∧
      (∀ r ∈ Set.Icc a b, ∀ c ∈ latIcc ε a b, IsInfinitesimal (c - (r : ℝ*)) →
        f r = stdPart (hfun F c)) ∧
      (∀ x ∈ latIcc ε a b, IsInfinitesimal (hfun F x - (f (stdPart x) : ℝ*))) := by
  obtain ⟨e, rfl⟩ := Hyperreal.ofSeq_surjective ε
  have hD : IsInternal (latIcc (Hyperreal.ofSeq e) a b : Set (Ult ℝ)) :=
    ⟨_, latIcc_eq_internal e a b⟩
  have hdense : ∀ x ∈ Set.Icc a b, ∃ c ∈ (latIcc (Hyperreal.ofSeq e) a b : Set (Ult ℝ)),
      Near c (Germ.const x) := by
    intro x hx
    obtain ⟨c, hc, hcx⟩ := exists_latIcc_near _ hε0 hε hab hx
    exact ⟨c, hc, (near_real_iff c x).2 hcx⟩
  have hfin' : ∀ c ∈ (latIcc (Hyperreal.ofSeq e) a b : Set (Ult ℝ)),
      IsFinite (hdist (ifun F c) (Germ.const (0 : ℝ))) := by
    intro c hc
    have : hdist (ifun F c) (Germ.const (0 : ℝ)) = |hfun F c - 0| := hdist_real _ _
    rw [this, sub_zero, isFinite_abs_iff]
    exact hfin c hc
  have hS' : ∀ c ∈ (latIcc (Hyperreal.ofSeq e) a b : Set (Ult ℝ)),
      ∀ c' ∈ (latIcc (Hyperreal.ofSeq e) a b : Set (Ult ℝ)),
      Near c c' → Near (ifun F c) (ifun F c') := by
    intro c hc c' hc' h
    exact (near_real_iff (hfun F c) (hfun F c')).2
      (hS c hc c' hc' ((near_real_iff c c').1 h))
  obtain ⟨f, hcont, hkey⟩ := shadow_of_S_continuous (Set.Icc a b) _ hD hdense F 0 hfin' hS'
  have hkey' : ∀ c ∈ latIcc (Hyperreal.ofSeq e) a b, ∀ r ∈ Set.Icc a b,
      IsInfinitesimal (c - (r : ℝ*)) → IsInfinitesimal (hfun F c - (f r : ℝ*)) := by
    intro c hc r hr h
    exact (near_real_iff (hfun F c) (f r)).1 (hkey c hc r hr ((near_real_iff c r).2 h))
  refine ⟨f, hcont, fun r hr c hc h => (stdPart_unique (hkey' c hc r hr h)).symm, ?_⟩
  intro x hx
  obtain ⟨-, ha, hb⟩ := id hx
  have hxfin : IsFinite x := by
    rw [isFinite_iff_abs_le]
    refine ⟨|a| + |b|, abs_le.2 ⟨?_, ?_⟩⟩
    · have : ((-(|a| + |b|) : ℝ) : ℝ*) ≤ (a : ℝ*) :=
        Hyperreal.coe_le_coe.2 (by linarith [neg_abs_le a, abs_nonneg b])
      rw [Hyperreal.coe_neg] at this; linarith
    · have : (b : ℝ*) ≤ ((|a| + |b| : ℝ) : ℝ*) :=
        Hyperreal.coe_le_coe.2 (by linarith [le_abs_self b, abs_nonneg a])
      linarith
  have hs : stdPart x ∈ Set.Icc a b := by
    constructor
    · have := stdPart_mono (coe_isFinite a) hxfin ha
      rwa [Hyperreal.stdPart_coe] at this
    · have := stdPart_mono hxfin (coe_isFinite b) hb
      rwa [Hyperreal.stdPart_coe] at this
  exact hkey' x hx (stdPart x) hs (isInfinitesimal_sub_stdPart hxfin)

/-- **Converse**: every function continuous on `[a,b]` arises from `F = *f` restricted
to the lattice: `*f` is finite and S-continuous on `𝕃 ∩ [a,b]` and
`st (*f c) = f r` whenever `c ≈ r`. -/
theorem shadow_lattice_converse (ε : ℝ*) {a b : ℝ} (f : ℝ → ℝ)
    (hf : ContinuousOn f (Set.Icc a b)) :
    (∀ x ∈ latIcc ε a b, ∀ y ∈ latIcc ε a b, IsInfinitesimal (x - y) →
      IsInfinitesimal (hfun (fun _ => f) x - hfun (fun _ => f) y)) ∧
    (∀ x ∈ latIcc ε a b, IsFinite (hfun (fun _ => f) x)) ∧
    (∀ r ∈ Set.Icc a b, ∀ c ∈ latIcc ε a b, IsInfinitesimal (c - (r : ℝ*)) →
      stdPart (hfun (fun _ => f) c) = f r) := by
  have hnear : ∀ c ∈ latIcc ε a b, ∀ r ∈ Set.Icc a b, IsInfinitesimal (c - (r : ℝ*)) →
      IsInfinitesimal (hfun (fun _ => f) c - (f r : ℝ*)) := by
    intro c hc r hr h
    exact (near_real_iff _ _).1 (starFun_near_of_continuousWithinAt f _ r (hf r hr) c
      (latIcc_subset_starSet ε a b hc) ((near_real_iff c r).2 h))
  have hst : ∀ c ∈ latIcc ε a b, ∃ r ∈ Set.Icc a b, IsInfinitesimal (c - (r : ℝ*)) := by
    intro c hc
    obtain ⟨r, hr, h⟩ := exists_near_of_mem_starSet isCompact_Icc
      (latIcc_subset_starSet ε a b hc)
    exact ⟨r, hr, (near_real_iff c r).1 h⟩
  refine ⟨fun x hx y hy hxy => ?_, fun x hx => ?_, fun r hr c hc h => stdPart_unique (hnear c hc r hr h)⟩
  · obtain ⟨r, hr, hxr⟩ := hst x hx
    have hyr : IsInfinitesimal (y - (r : ℝ*)) := by
      have := hxr.sub hxy; rwa [show x - (r : ℝ*) - (x - y) = y - r by ring] at this
    have := (hnear x hx r hr hxr).sub (hnear y hy r hr hyr)
    rwa [show hfun (fun _ => f) x - (f r : ℝ*) - (hfun (fun _ => f) y - (f r : ℝ*)) =
      hfun (fun _ => f) x - hfun (fun _ => f) y by ring] at this
  · obtain ⟨r, hr, hxr⟩ := hst x hx
    have h := (hnear x hx r hr hxr).isFinite.add (coe_isFinite (f r))
    rwa [sub_add_cancel] at h

end Lattice

/-! ## Maxima of internal functions on hyperfinite sets -/

section Maxima

/-- A real-valued internal function `[g n]`, viewed as `ℝ*`-valued. -/
def hval (g : ℕ → α → ℝ) (c : Ult α) : ℝ* := ifun g c

theorem hval_coe (g : ℕ → α → ℝ) (u : ℕ → α) :
    hval g (u : Ult α) = Hyperreal.ofSeq (fun m => g m (u m)) := rfl

/-- **An internal function attains its maximum on a nonempty hyperfinite set.** -/
theorem exists_max_hyperfinite (A : ℕ → Set α)
    (hfin : ∀ᶠ m in (hyperfilter ℕ : Filter ℕ), (A m).Finite) (hne : (internal A).Nonempty)
    (g : ℕ → α → ℝ) : ∃ c₀ ∈ internal A, ∀ c ∈ internal A, hval g c ≤ hval g c₀ := by
  classical
  have hne' := (internal_nonempty_iff A).1 hne
  obtain ⟨m₀, a₀, -⟩ := hne'.exists
  let w : ℕ → α := fun m => if h : (A m).Finite ∧ (A m).Nonempty then
    (Set.exists_max_image (A m) (g m) h.1 h.2).choose else a₀
  have hw : ∀ᶠ m in (hyperfilter ℕ : Filter ℕ), w m ∈ A m ∧ ∀ b ∈ A m, g m b ≤ g m (w m) := by
    filter_upwards [hfin, hne'] with m h1 h2
    simp only [w, h1, h2, and_self, ↓reduceDIte]
    exact (Set.exists_max_image (A m) (g m) h1 h2).choose_spec
  refine ⟨w, (mem_internal A w).2 (hw.mono fun m h => h.1), fun c hc => ?_⟩
  obtain ⟨u, rfl⟩ := exists_rep c
  rw [mem_internal] at hc
  rw [hval_coe, hval_coe]
  exact Hyperreal.ofSeq_le_ofSeq.2 (by filter_upwards [hw, hc] with m h1 h2 using h1.2 _ h2)

end Maxima

/-! ## Robinson's characterisations on the lattice of `ℝⁿ` (Chapter 10)

Points of `ℝ*ⁿ` are elements of `Ult (Fin d → ℝ)`, with the `ℝ*`-valued sup-distance
`hdist`.  The lattice `𝕃ⁿ` consists of the points all of whose coordinates lie in
`2ε·ℤ*`, and the cell of a lattice point `c` is `c + [-ε, ε)ⁿ`. -/

section LatticeN

open ArchimedeanClass

variable {d p : ℕ}

/-- The `i`-th coordinate `ℝ*ⁿ → ℝ*`. -/
def coordG (i : Fin d) (y : Ult (Fin d → ℝ)) : ℝ* := Germ.map (fun v => v i) y

theorem coordG_coe (i : Fin d) (v : ℕ → Fin d → ℝ) :
    coordG i (v : Ult (Fin d → ℝ)) = Hyperreal.ofSeq (fun m => v m i) := rfl

/-- The lattice `𝕃ⁿ = (2ε·ℤ*)ⁿ`. -/
def latN (ε : ℝ*) : Set (Ult (Fin d → ℝ)) := {c | ∀ i, coordG i c ∈ lattice ε}

/-- The Voronoi cell `c + [-ε, ε)ⁿ` of a lattice point (an internal set). -/
def cellN (ε : ℝ*) (c : Ult (Fin d → ℝ)) : Set (Ult (Fin d → ℝ)) :=
  {y | ∀ i, coordG i c - ε ≤ coordG i y ∧ coordG i y < coordG i c + ε}

/-- The lattice points of the box `[-R, R]ⁿ` (the closed sup-ball of radius `R`). -/
def latBox (ε : ℝ*) (R : ℝ) : Set (Ult (Fin d → ℝ)) :=
  latN ε ∩ starSet (Metric.closedBall (0 : Fin d → ℝ) R)

theorem mem_lattice_ofSeq (e u : ℕ → ℝ) :
    Hyperreal.ofSeq u ∈ lattice (Hyperreal.ofSeq e) ↔
      ∀ᶠ m in (hyperfilter ℕ : Filter ℕ), ∃ k : ℤ, u m = 2 * e m * k := by
  constructor
  · rintro ⟨K, hK⟩
    have hK' : ∀ᶠ m in (hyperfilter ℕ : Filter ℕ), u m = 2 * e m * K m := Germ.coe_eq.1 hK
    filter_upwards [hK'] with m hm using ⟨K m, hm⟩
  · intro h
    classical
    let K : ℕ → ℤ := fun m => if hk : ∃ k : ℤ, u m = 2 * e m * k then hk.choose else 0
    refine ⟨K, Germ.coe_eq.2 ?_⟩
    filter_upwards [h] with m hm
    simp only [K, hm, ↓reduceDIte]
    exact hm.choose_spec

theorem mem_latN_coe (e : ℕ → ℝ) (v : ℕ → Fin d → ℝ) :
    (v : Ult (Fin d → ℝ)) ∈ latN (Hyperreal.ofSeq e) ↔
      ∀ᶠ m in (hyperfilter ℕ : Filter ℕ), ∀ i, ∃ k : ℤ, v m i = 2 * e m * k := by
  simp only [latN, Set.mem_ofPred_eq, coordG_coe, mem_lattice_ofSeq]
  exact Filter.eventually_all.symm

theorem latN_eq_internal (e : ℕ → ℝ) :
    (latN (Hyperreal.ofSeq e) : Set (Ult (Fin d → ℝ))) =
      internal (fun m => {y : Fin d → ℝ | ∀ i, ∃ k : ℤ, y i = 2 * e m * k}) := by
  ext c; obtain ⟨v, rfl⟩ := exists_rep c
  rw [mem_latN_coe, mem_internal]; rfl

theorem mem_cellN_coe (e : ℕ → ℝ) (v w : ℕ → Fin d → ℝ) :
    (w : Ult (Fin d → ℝ)) ∈ cellN (Hyperreal.ofSeq e) (v : Ult (Fin d → ℝ)) ↔
      ∀ᶠ m in (hyperfilter ℕ : Filter ℕ), ∀ i, v m i - e m ≤ w m i ∧ w m i < v m i + e m := by
  rw [Filter.eventually_all]
  refine forall_congr' fun i => ?_
  rw [eventually_and]
  show Hyperreal.ofSeq (fun m => v m i - e m) ≤ Hyperreal.ofSeq (fun m => w m i) ∧
      Hyperreal.ofSeq (fun m => w m i) < Hyperreal.ofSeq (fun m => v m i + e m) ↔ _
  rw [Hyperreal.ofSeq_le_ofSeq, Hyperreal.ofSeq_lt_ofSeq]

theorem latBox_eq_internal (e : ℕ → ℝ) (R : ℝ) :
    (latBox (Hyperreal.ofSeq e) R : Set (Ult (Fin d → ℝ))) =
      internal (fun m => {y : Fin d → ℝ | (∀ i, ∃ k : ℤ, y i = 2 * e m * k) ∧
        y ∈ Metric.closedBall 0 R}) := by
  unfold latBox starSet; rw [latN_eq_internal, ← internal_inter]; rfl

theorem eventually_small {e : ℕ → ℝ} (hε : IsInfinitesimal (Hyperreal.ofSeq e)) {t : ℝ}
    (ht : 0 < t) : ∀ᶠ m in (hyperfilter ℕ : Filter ℕ), e m < t := by
  filter_upwards [(isInfinitesimal_ofSeq_iff e).1 hε t ht] with m hm
  exact lt_of_le_of_lt (le_abs_self _) hm

/-- A point of the cell of `c` is within `ε` of `c`. -/
theorem hdist_le_of_mem_cellN {e : ℕ → ℝ} (he : 0 < Hyperreal.ofSeq e)
    {c y : Ult (Fin d → ℝ)} (hy : y ∈ cellN (Hyperreal.ofSeq e) c) :
    hdist y c ≤ Hyperreal.ofSeq e := by
  obtain ⟨v, rfl⟩ := exists_rep c; obtain ⟨w, rfl⟩ := exists_rep y
  rw [mem_cellN_coe] at hy
  rw [hdist_coe]
  refine Hyperreal.ofSeq_le_ofSeq.2 ?_
  filter_upwards [hy, Hyperreal.ofSeq_lt_ofSeq.1 he] with m h1 h2
  refine (dist_pi_le_iff h2.le).2 fun i => ?_
  rw [Real.dist_eq, abs_le]
  constructor <;> linarith [(h1 i).1, (h1 i).2]

theorem near_of_mem_cellN {ε : ℝ*} (hε0 : 0 < ε) (hε : IsInfinitesimal ε)
    {c y : Ult (Fin d → ℝ)} (hy : y ∈ cellN ε c) : Near y c := by
  obtain ⟨e, rfl⟩ := Hyperreal.ofSeq_surjective ε
  exact near_of_hdist_le hε (hdist_le_of_mem_cellN hε0 hy)

/-- Snapping to the cell: `2ek - e ≤ t < 2ek + e` for `k = ⌊(t + e)/(2e)⌋`. -/
theorem snap_bounds {e : ℝ} (he : 0 < e) (t : ℝ) :
    2 * e * ⌊(t + e) / (2 * e)⌋ - e ≤ t ∧ t < 2 * e * ⌊(t + e) / (2 * e)⌋ + e := by
  have h2e : 0 < 2 * e := by positivity
  have h1 := Int.floor_le ((t + e) / (2 * e))
  have h2 := Int.lt_floor_add_one ((t + e) / (2 * e))
  rw [le_div_iff₀ h2e] at h1
  rw [div_lt_iff₀ h2e] at h2
  constructor <;> nlinarith

/-- Rounding toward zero: `|2ek| ≤ |t|` and `|2ek - t| < 2e`. -/
theorem towardZero_bounds {e : ℝ} (he : 0 < e) (t : ℝ) :
    |2 * e * (if 0 ≤ t then ⌊t / (2 * e)⌋ else ⌈t / (2 * e)⌉)| ≤ |t| ∧
      |2 * e * (if 0 ≤ t then ⌊t / (2 * e)⌋ else ⌈t / (2 * e)⌉) - t| < 2 * e := by
  have h2e : 0 < 2 * e := by positivity
  split_ifs with ht
  · have h1 := Int.floor_le (t / (2 * e))
    have h2 := Int.lt_floor_add_one (t / (2 * e))
    have h0 : (0 : ℝ) ≤ ⌊t / (2 * e)⌋ := by exact_mod_cast Int.floor_nonneg.2 (by positivity)
    rw [le_div_iff₀ h2e] at h1
    rw [div_lt_iff₀ h2e] at h2
    rw [abs_of_nonneg (by positivity), abs_of_nonneg ht, abs_lt]
    constructor
    · nlinarith
    · constructor <;> nlinarith
  · push Not at ht
    have h1 := Int.le_ceil (t / (2 * e))
    have h2 := Int.ceil_lt_add_one (t / (2 * e))
    have h0 : (⌈t / (2 * e)⌉ : ℝ) ≤ 0 := by
      exact_mod_cast Int.ceil_le.2 (by simpa using (div_neg_of_neg_of_pos ht h2e).le)
    rw [div_le_iff₀ h2e] at h1
    have h2' := mul_lt_mul_of_pos_right h2 h2e
    rw [add_mul, div_mul_cancel₀ _ h2e.ne', one_mul] at h2'
    rw [abs_of_nonpos (by nlinarith), abs_of_neg ht, abs_lt]
    constructor
    · nlinarith
    · constructor <;> nlinarith

/-- **Robinson's characterisation of open sets, on the lattice.** A standard
`E ⊆ ℝⁿ` is open iff for every standard `x ∈ E`, every lattice point `c ≈ x` has its
whole cell inside `*E`. -/
theorem robinson_open_lattice (ε : ℝ*) (hε0 : 0 < ε) (hε : IsInfinitesimal ε)
    (E : Set (Fin d → ℝ)) :
    IsOpen E ↔ ∀ x ∈ E, ∀ c ∈ latN ε, Near c (Germ.const x) → cellN ε c ⊆ starSet E := by
  obtain ⟨e, rfl⟩ := Hyperreal.ofSeq_surjective ε
  have he' : ∀ᶠ m in (hyperfilter ℕ : Filter ℕ), 0 < e m := Hyperreal.ofSeq_lt_ofSeq.1 hε0
  constructor
  · intro hE x hx c _ hcx y hy
    obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 hE x hx
    obtain ⟨v, rfl⟩ := exists_rep c
    obtain ⟨w, rfl⟩ := exists_rep y
    have hd := hdist_le_of_mem_cellN hε0 hy
    rw [hdist_coe] at hd
    refine (mem_starSet E w).2 ?_
    filter_upwards [(near_coe_iff v (fun _ => x)).1 hcx (r / 2) (half_pos hr),
      Hyperreal.ofSeq_le_ofSeq.1 hd, eventually_small hε (half_pos hr)] with m h1 h2 h3
    apply hball
    rw [Metric.mem_ball]
    linarith [dist_triangle (w m) (v m) x]
  · intro H
    rw [Metric.isOpen_iff]
    intro x hx
    by_contra hne
    push Not at hne
    have hy : ∀ m, ∃ y, dist y x < (if 0 < e m then e m else 1) ∧ y ∉ E := by
      intro m
      have hpos : 0 < (if 0 < e m then e m else 1) := by split_ifs with h <;> simp [h]
      obtain ⟨y, hy1, hy2⟩ := Set.not_subset.1 (hne _ hpos)
      exact ⟨y, hy1, hy2⟩
    choose y hy1 hy2 using hy
    let v : ℕ → Fin d → ℝ := fun m i => 2 * e m * ⌊(y m i + e m) / (2 * e m)⌋
    have hv : (v : Ult (Fin d → ℝ)) ∈ latN (Hyperreal.ofSeq e) :=
      (mem_latN_coe e v).2 (Eventually.of_forall fun m i => ⟨_, rfl⟩)
    have hcell : (y : Ult (Fin d → ℝ)) ∈ cellN (Hyperreal.ofSeq e) (v : Ult (Fin d → ℝ)) :=
      (mem_cellN_coe e v y).2 (by
        filter_upwards [he'] with m hm i
        exact snap_bounds hm (y m i))
    have hnear : Near (v : Ult (Fin d → ℝ)) (Germ.const x) := by
      refine (near_coe_iff v (fun _ => x)).2 fun r hr => ?_
      filter_upwards [he', eventually_small hε (show 0 < r / 3 by positivity)] with m h1 h2
      have hvy : dist (v m) (y m) ≤ e m := by
        refine (dist_pi_le_iff h1.le).2 fun i => ?_
        have := snap_bounds h1 (y m i)
        rw [Real.dist_eq, abs_le]; constructor <;> linarith [this.1, this.2]
      have hyx : dist (y m) x < e m := by have := hy1 m; simp only [h1, ↓reduceIte] at this; exact this
      linarith [dist_triangle (v m) (y m) x]
    have hsub := H x hx _ hv hnear hcell
    obtain ⟨m, hm⟩ := ((mem_starSet E y).1 hsub).exists
    exact hy2 m hm

/-- **Robinson's characterisation of compact sets, on the lattice.** A standard
`E ⊆ ℝⁿ` is compact iff every lattice point whose cell meets `*E` is near-standard
with standard part in `E`. -/
theorem robinson_compact_lattice (ε : ℝ*) (hε0 : 0 < ε) (hε : IsInfinitesimal ε)
    (E : Set (Fin d → ℝ)) :
    IsCompact E ↔ ∀ c ∈ latN ε, (cellN ε c ∩ starSet E).Nonempty →
      ∃ x ∈ E, Near c (Germ.const x) := by
  constructor
  · rintro hE c - ⟨y, hyc, hyE⟩
    obtain ⟨x, hx, hyx⟩ := (isCompact_iff_near E).1 hE y hyE
    exact ⟨x, hx, (near_of_mem_cellN hε0 hε hyc).symm.trans hyx⟩
  · intro H
    rw [isCompact_iff_near]
    intro y hy
    obtain ⟨e, rfl⟩ := Hyperreal.ofSeq_surjective ε
    have he' : ∀ᶠ m in (hyperfilter ℕ : Filter ℕ), 0 < e m := Hyperreal.ofSeq_lt_ofSeq.1 hε0
    obtain ⟨w, rfl⟩ := exists_rep y
    let v : ℕ → Fin d → ℝ := fun m i => 2 * e m * ⌊(w m i + e m) / (2 * e m)⌋
    have hv : (v : Ult (Fin d → ℝ)) ∈ latN (Hyperreal.ofSeq e) :=
      (mem_latN_coe e v).2 (Eventually.of_forall fun m i => ⟨_, rfl⟩)
    have hcell : (w : Ult (Fin d → ℝ)) ∈ cellN (Hyperreal.ofSeq e) (v : Ult (Fin d → ℝ)) :=
      (mem_cellN_coe e v w).2 (by
        filter_upwards [he'] with m hm i
        exact snap_bounds hm (w m i))
    obtain ⟨x, hx, hcx⟩ := H _ hv ⟨_, hcell, hy⟩
    exact ⟨x, hx, (near_of_mem_cellN hε0 hε hcell).trans hcx⟩

theorem hdist_ifun_starFun (F : ℕ → (Fin d → ℝ) → (Fin p → ℝ)) (f : (Fin d → ℝ) → (Fin p → ℝ))
    (c : Ult (Fin d → ℝ)) :
    hdist (ifun F c) (starFun f c) = hval (fun m y => dist (F m y) (f y)) c := by
  obtain ⟨v, rfl⟩ := exists_rep c; rfl

/-- **Robinson's characterisation of continuity, on the lattice.** Let `ε` be a positive
infinitesimal, `R ≥ 0` standard, and `F = [F n]` an internal function on the lattice
points of `[-R,R]ⁿ` with values in `ℝ*ᵖ`, finitely bounded and S-continuous.  Then
there is a continuous `f : [-R,R]ⁿ → ℝᵖ` with `F c ≈ f x` whenever `c ≈ x` (that is,
`f (st c) = st F(c)`), and `max_c |F c - *f c|` is attained and infinitesimal. -/
theorem robinson_continuity_lattice (ε : ℝ*) (hε0 : 0 < ε) (hε : IsInfinitesimal ε)
    {R : ℝ} (hR : 0 ≤ R) (F : ℕ → (Fin d → ℝ) → (Fin p → ℝ))
    (hbdd : ∃ B : ℝ, ∀ c ∈ latBox ε R, hdist (ifun F c) (Germ.const 0) ≤ (B : ℝ*))
    (hS : ∀ c ∈ latBox ε R, ∀ c' ∈ latBox ε R, Near c c' → Near (ifun F c) (ifun F c')) :
    ∃ f : (Fin d → ℝ) → (Fin p → ℝ), ContinuousOn f (Metric.closedBall 0 R) ∧
      (∀ c ∈ latBox ε R, ∀ x ∈ Metric.closedBall 0 R, Near c (Germ.const x) →
        Near (ifun F c) (Germ.const (f x))) ∧
      ∃ c₀ ∈ latBox ε R, (∀ c ∈ latBox ε R,
          hdist (ifun F c) (starFun f c) ≤ hdist (ifun F c₀) (starFun f c₀)) ∧
        IsInfinitesimal (hdist (ifun F c₀) (starFun f c₀)) := by
  obtain ⟨e, rfl⟩ := Hyperreal.ofSeq_surjective ε
  have he' : ∀ᶠ m in (hyperfilter ℕ : Filter ℕ), 0 < e m := Hyperreal.ofSeq_lt_ofSeq.1 hε0
  have hD : IsInternal (latBox (Hyperreal.ofSeq e) R : Set (Ult (Fin d → ℝ))) :=
    ⟨_, latBox_eq_internal e R⟩
  have hdense : ∀ x ∈ Metric.closedBall (0 : Fin d → ℝ) R,
      ∃ c ∈ latBox (Hyperreal.ofSeq e) R, Near c (Germ.const x) := by
    intro x hx
    have hxi : ∀ i, |x i| ≤ R := by
      intro i
      have := (dist_pi_le_iff hR).1 (Metric.mem_closedBall.1 hx) i
      simpa [Real.dist_eq] using this
    let v : ℕ → Fin d → ℝ := fun m i =>
      2 * e m * (if 0 ≤ x i then ⌊x i / (2 * e m)⌋ else ⌈x i / (2 * e m)⌉)
    refine ⟨v, ⟨(mem_latN_coe e v).2 (Eventually.of_forall fun m i => ⟨_, rfl⟩), ?_⟩, ?_⟩
    · refine (mem_starSet _ v).2 ?_
      filter_upwards [he'] with m hm
      rw [Metric.mem_closedBall]
      refine (dist_pi_le_iff hR).2 fun i => ?_
      rw [Pi.zero_apply, Real.dist_eq, sub_zero]
      exact (towardZero_bounds hm (x i)).1.trans (hxi i)
    · refine (near_coe_iff v (fun _ => x)).2 fun r hr => ?_
      filter_upwards [he', eventually_small hε (show 0 < r / 2 by positivity)] with m h1 h2
      refine (dist_pi_lt_iff hr).2 fun i => ?_
      rw [Real.dist_eq]
      have := (towardZero_bounds h1 (x i)).2
      show |v m i - x i| < r
      linarith
  have hfin : ∀ c ∈ latBox (Hyperreal.ofSeq e) R,
      IsFinite (hdist (ifun F c) (Germ.const (0 : Fin p → ℝ))) := by
    obtain ⟨B, hB⟩ := hbdd
    intro c hc
    exact (isFinite_iff_abs_le _).2 ⟨B, by rw [abs_of_nonneg (hdist_nonneg _ _)]; exact hB c hc⟩
  obtain ⟨f, hcont, hkey⟩ := shadow_of_S_continuous (Metric.closedBall 0 R) _ hD hdense F 0
    hfin hS
  refine ⟨f, hcont, hkey, ?_⟩
  -- the maximum over the hyperfinite domain
  have hfinite : ∀ᶠ m in (hyperfilter ℕ : Filter ℕ), {y : Fin d → ℝ |
      (∀ i, ∃ k : ℤ, y i = 2 * e m * k) ∧ y ∈ Metric.closedBall 0 R}.Finite := by
    filter_upwards [he'] with m hm
    have h2e : 0 < 2 * e m := by positivity
    refine ((Set.Finite.pi (t := fun _ : Fin d => Set.Icc ⌈-R / (2 * e m)⌉ ⌊R / (2 * e m)⌋)
      (fun _ => Set.finite_Icc _ _)).image (fun k : Fin d → ℤ => fun i => 2 * e m * k i)).subset ?_
    rintro y ⟨hy, hyR⟩
    choose k hk using hy
    have hyi : ∀ i, |y i| ≤ R := by
      intro i
      have := (dist_pi_le_iff hR).1 (Metric.mem_closedBall.1 hyR) i
      simpa [Real.dist_eq] using this
    refine ⟨k, fun i _ => ⟨Int.ceil_le.2 ?_, Int.le_floor.2 ?_⟩, funext fun i => (hk i).symm⟩
    · have := (abs_le.1 (hyi i)).1; rw [hk i] at this
      rw [div_le_iff₀ h2e]; linarith
    · have := (abs_le.1 (hyi i)).2; rw [hk i] at this
      rw [le_div_iff₀ h2e]; linarith
  have hne : (internal (fun m => {y : Fin d → ℝ | (∀ i, ∃ k : ℤ, y i = 2 * e m * k) ∧
      y ∈ Metric.closedBall 0 R})).Nonempty := by
    refine ⟨((fun _ _ => 0 : ℕ → Fin d → ℝ) : Ult (Fin d → ℝ)), (mem_internal _ _).2 ?_⟩
    exact Eventually.of_forall fun m => ⟨fun i => ⟨0, by simp⟩, by
      show dist (0 : Fin d → ℝ) 0 ≤ R
      rw [dist_self]; exact hR⟩
  obtain ⟨c₀, hc₀, hmax⟩ := exists_max_hyperfinite _ hfinite hne (fun m y => dist (F m y) (f y))
  rw [← latBox_eq_internal] at hc₀ hmax
  refine ⟨c₀, hc₀, fun c hc => ?_, ?_⟩
  · rw [hdist_ifun_starFun, hdist_ifun_starFun]; exact hmax c hc
  · obtain ⟨x₀, hx₀, hnear⟩ := exists_near_of_mem_starSet (isCompact_closedBall 0 R) hc₀.2
    have h1 := hkey c₀ hc₀ x₀ hx₀ hnear
    have h2 := starFun_near_of_continuousWithinAt f _ x₀ (hcont x₀ hx₀) c₀ hc₀.2 hnear
    exact h1.trans h2.symm

end LatticeN

end QE.NSA

end
