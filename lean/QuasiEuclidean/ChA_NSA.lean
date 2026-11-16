-- SPDX-License-Identifier: MIT
-- Copyright 2026 Metere Industries, Inc. Author: Alfredo Metere.
-- Quasi-Euclidean Granular Geometry. Any derivative work must carry this notice:
--   This work is derivative of the Quasi-Euclidean Granular Geometry book
--   authored by Alfredo Metere. Copyright 2026 Metere Industries, Inc.
--   All rights reserved
-- See LICENSE.md and NOTICE.

import QuasiEuclidean.Basic

/-!
# Appendix A: a primer on nonstandard analysis (formal part)

Machine-checked companions to Appendix A of the book.

* Łoś's theorem (a thin wrapper around Mathlib's
  `FirstOrder.Language.Ultraproduct.sentence_realize`) and the transfer
  principle for ultrapowers `M^ℕ/U` of a single structure.
* Infinitesimal and finite elements of an arbitrary linearly ordered field,
  defined through Mathlib's `ArchimedeanClass.mk`, with their closure
  properties; standard part (`ArchimedeanClass.stdPart`).
* Concrete facts about Mathlib's `Hyperreal`: `ε` is infinitesimal, `ω` is
  infinite, the field `ℝ*` is not Archimedean.
* Internal subsets of `ℝ*` presented by sequences of sets, and the
  countable saturation (`ℵ₁`-saturation) of the ultrapower over `ℕ`.
* Overspill for internal sets of hypernaturals.
-/

open ArchimedeanClass Filter

namespace QE.NSA

/-! ## Łoś's theorem and transfer -/

section Los
open FirstOrder FirstOrder.Language

universe w x

/-- **Łoś's theorem.** A first-order sentence holds in an ultraproduct iff it
holds in `U`-almost every factor. -/
theorem los {α : Type w} {M : α → Type x} (U : Ultrafilter α) {L : Language}
    [∀ a, L.Structure (M a)] [∀ a, Nonempty (M a)] (φ : L.Sentence) :
    (U : Filter α).Product M ⊨ φ ↔ ∀ᶠ a in (U : Filter α), M a ⊨ φ :=
  Ultraproduct.sentence_realize φ

/-- **Transfer for ultrapowers.** A sentence holds in the ultrapower `M^α/U`
iff it holds in `M`. -/
theorem transfer_ultrapower {α : Type w} (M : Type x) (U : Ultrafilter α)
    {L : Language} [L.Structure M] [Nonempty M] (φ : L.Sentence) :
    (U : Filter α).Product (fun _ : α => M) ⊨ φ ↔ M ⊨ φ := by
  rw [los U φ]
  exact Filter.eventually_const

end Los

/-! ## Infinitesimals in an ordered field -/

section Field
variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-- `x` is infinitesimal: `n·|x| < 1` for every natural `n`. -/
def IsInfinitesimal (x : K) : Prop := 0 < mk x

/-- `x` is finite (limited): bounded by a natural number. -/
def IsFinite (x : K) : Prop := 0 ≤ mk x

/-- Characterisation of infinitesimals without valuations. -/
theorem isInfinitesimal_iff (x : K) :
    IsInfinitesimal x ↔ ∀ n : ℕ, (n : K) * |x| < 1 := by
  unfold IsInfinitesimal
  rw [← mk_one, mk_lt_mk]
  simp [nsmul_eq_mul]

theorem isInfinitesimal_zero : IsInfinitesimal (0 : K) := by
  unfold IsInfinitesimal; simp

theorem IsInfinitesimal.neg {x : K} (hx : IsInfinitesimal x) : IsInfinitesimal (-x) := by
  unfold IsInfinitesimal at *; rwa [mk_neg]

theorem IsInfinitesimal.add {x y : K} (hx : IsInfinitesimal x) (hy : IsInfinitesimal y) :
    IsInfinitesimal (x + y) :=
  lt_of_lt_of_le (lt_min hx hy) (min_le_mk_add x y)

theorem IsInfinitesimal.sub {x y : K} (hx : IsInfinitesimal x) (hy : IsInfinitesimal y) :
    IsInfinitesimal (x - y) := by
  rw [sub_eq_add_neg]; exact hx.add hy.neg

/-- finite × infinitesimal is infinitesimal. -/
theorem IsInfinitesimal.mul_finite {x y : K} (hx : IsInfinitesimal x) (hy : IsFinite y) :
    IsInfinitesimal (x * y) := by
  unfold IsInfinitesimal IsFinite at *
  rw [mk_mul]
  exact lt_of_lt_of_le hx (le_add_of_nonneg_right hy)

theorem IsInfinitesimal.mul {x y : K} (hx : IsInfinitesimal x) (hy : IsInfinitesimal y) :
    IsInfinitesimal (x * y) := hx.mul_finite hy.le

/-- Natural multiples of an infinitesimal are infinitesimal (e.g. `2ε·k`). -/
theorem IsInfinitesimal.nat_mul {x : K} (hx : IsInfinitesimal x) (k : ℕ) :
    IsInfinitesimal ((k : K) * x) := by
  rw [mul_comm]; exact hx.mul_finite (mk_natCast_nonneg k)

theorem IsInfinitesimal.int_mul {x : K} (hx : IsInfinitesimal x) (k : ℤ) :
    IsInfinitesimal ((k : K) * x) := by
  rw [mul_comm]; exact hx.mul_finite (mk_intCast_nonneg k)

theorem IsInfinitesimal.isFinite {x : K} (hx : IsInfinitesimal x) : IsFinite x := hx.le

theorem IsFinite.add {x y : K} (hx : IsFinite x) (hy : IsFinite y) : IsFinite (x + y) :=
  le_trans (le_min hx hy) (min_le_mk_add x y)

theorem IsFinite.mul {x y : K} (hx : IsFinite x) (hy : IsFinite y) : IsFinite (x * y) := by
  unfold IsFinite at *; rw [mk_mul]; exact add_nonneg hx hy

/-- An element squeezed by an infinitesimal is infinitesimal. -/
theorem IsInfinitesimal.of_abs_le {x y : K} (hy : IsInfinitesimal y) (h : |x| ≤ |y|) :
    IsInfinitesimal x :=
  lt_of_lt_of_le hy (mk_le_mk_of_abs h)

/-- The reciprocal of a nonzero infinitesimal is infinite. -/
theorem IsInfinitesimal.inv_infinite {x : K} (hx : IsInfinitesimal x) (h0 : x ≠ 0) :
    mk x⁻¹ < 0 := by
  unfold IsInfinitesimal at hx
  have hne : mk x ≠ ⊤ := by rw [Ne, mk_eq_top_iff]; exact h0
  have h := (LinearOrderedAddCommGroupWithTop.sub_lt_sub_iff_left_of_ne_top hne).2 hx
  rw [LinearOrderedAddCommGroupWithTop.sub_self_eq_zero_of_ne_top hne, zero_sub] at h
  rw [inv_eq_one_div, mk_div, mk_one, zero_sub]
  exact h

/-! ### Standard part -/

/-- The standard part of an infinitesimal is `0`. -/
theorem stdPart_of_infinitesimal {x : K} (hx : IsInfinitesimal x) : stdPart x = 0 :=
  stdPart_eq_zero.2 (ne_of_gt hx)

/-- Adding an infinitesimal does not change the standard part. -/
theorem stdPart_add_infinitesimal {x δ : K} (hδ : IsInfinitesimal δ) :
    stdPart (x + δ) = stdPart x :=
  stdPart_add_eq_left hδ

/-- Infinitely close elements have the same standard part. -/
theorem stdPart_eq_of_sub_infinitesimal {x y : K} (h : IsInfinitesimal (x - y)) :
    stdPart x = stdPart y := by
  have : x = y + (x - y) := by ring
  rw [this, stdPart_add_infinitesimal h]

theorem stdPart_add' {x y : K} (hx : IsFinite x) (hy : IsFinite y) :
    stdPart (x + y) = stdPart x + stdPart y := stdPart_add hx hy

theorem stdPart_mul' {x y : K} (hx : IsFinite x) (hy : IsFinite y) :
    stdPart (x * y) = stdPart x * stdPart y := stdPart_mul hx hy

theorem stdPart_mono {x y : K} (hx : IsFinite x) (hy : IsFinite y) (h : x ≤ y) :
    stdPart x ≤ stdPart y := stdPart_monotoneOn hx hy h

/-- The standard part is an order-preserving ring homomorphism on finite
elements that kills infinitesimals (combined statement). -/
theorem stdPart_properties {x y : K} (hx : IsFinite x) (hy : IsFinite y) :
    stdPart (x + y) = stdPart x + stdPart y ∧ stdPart (x * y) = stdPart x * stdPart y ∧
      (x ≤ y → stdPart x ≤ stdPart y) ∧ (IsInfinitesimal (x - y) → stdPart x = stdPart y) :=
  ⟨stdPart_add hx hy, stdPart_mul hx hy, stdPart_mono hx hy, stdPart_eq_of_sub_infinitesimal⟩

/-- Arithmetic of infinitesimals (combined statement): infinitesimals are
closed under sums and under products with finite elements, finite elements
are closed under sums and products, and nonzero infinitesimals have infinite
reciprocals. -/
theorem infinitesimal_arith :
    (∀ x y : K, IsInfinitesimal x → IsInfinitesimal y → IsInfinitesimal (x + y)) ∧
    (∀ x y : K, IsInfinitesimal x → IsFinite y → IsInfinitesimal (x * y)) ∧
    (∀ x y : K, IsFinite x → IsFinite y → IsFinite (x + y) ∧ IsFinite (x * y)) ∧
    (∀ x : K, IsInfinitesimal x → x ≠ 0 → mk x⁻¹ < 0) :=
  ⟨fun _ _ hx hy => hx.add hy, fun _ _ hx hy => hx.mul_finite hy,
    fun _ _ hx hy => ⟨hx.add hy, hx.mul hy⟩, fun _ hx h0 => hx.inv_infinite h0⟩

end Field

/-! ## The hyperreals -/

section Hyper
open Hyperreal

/-- In `ℝ*`, infinitesimal means smaller in absolute value than every
standard positive real. -/
theorem hyper_isInfinitesimal_iff (x : ℝ*) :
    IsInfinitesimal x ↔ ∀ r : ℝ, 0 < r → |x| < (r : ℝ*) := by
  rw [isInfinitesimal_iff]
  constructor
  · intro h r hr
    obtain ⟨n, hn⟩ := exists_nat_gt (1 / r)
    have hn0 : (0 : ℝ) < n := lt_trans (by positivity) hn
    have h1 := h n
    have hrn : (1 : ℝ*) < (n : ℝ*) * (r : ℝ*) := by
      have : (1 : ℝ) < n * r := by
        rw [div_lt_iff₀ hr] at hn; linarith
      have h2 := Hyperreal.coe_lt_coe.2 this
      push_cast at h2
      exact h2
    have hnpos : (0 : ℝ*) < (n : ℝ*) := by exact_mod_cast hn0
    by_contra hc; push Not at hc
    have : (n : ℝ*) * (r : ℝ*) ≤ (n : ℝ*) * |x| := mul_le_mul_of_nonneg_left hc hnpos.le
    linarith
  · intro h n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp
    have hn' : (0 : ℝ) < n := by exact_mod_cast hn
    have h1 := h (1 / n) (by positivity)
    have hnpos : (0 : ℝ*) < (n : ℝ*) := by exact_mod_cast hn
    have : (n : ℝ*) * |x| < (n : ℝ*) * ((1 / n : ℝ) : ℝ*) := mul_lt_mul_of_pos_left h1 hnpos
    have e : (n : ℝ*) * ((1 / n : ℝ) : ℝ*) = 1 := by
      rw [Hyperreal.coe_div, Hyperreal.coe_one]
      have : ((n : ℝ) : ℝ*) = (n : ℝ*) := by norm_cast
      rw [this]; field_simp
    linarith

/-- Mathlib's `ε = ω⁻¹` is a positive infinitesimal. -/
theorem epsilon_isInfinitesimal : IsInfinitesimal Hyperreal.epsilon :=
  Hyperreal.archimedeanClassMk_epsilon_pos

/-- `ε` lies strictly below every standard positive real. -/
theorem epsilon_lt_pos (r : ℝ) (hr : 0 < r) : Hyperreal.epsilon < (r : ℝ*) :=
  Hyperreal.epsilon_lt_of_pos hr

/-- `ω` is larger than every standard natural number. -/
theorem nat_lt_omega (n : ℕ) : (n : ℝ*) < Hyperreal.omega := by
  have := Hyperreal.coe_lt_omega (n : ℝ)
  exact_mod_cast this

/-- `ω` is infinite. -/
theorem omega_infinite : mk Hyperreal.omega < 0 := Hyperreal.archimedeanClassMk_omega_neg

/-- Standard reals are finite. -/
theorem coe_isFinite (r : ℝ) : IsFinite (r : ℝ*) := Hyperreal.archimedeanClassMk_coe_nonneg r

/-- **Failure of the Archimedean property** in `ℝ*`. -/
theorem not_archimedean : ¬ Archimedean ℝ* := by
  intro h
  obtain ⟨n, hn⟩ := Archimedean.arch Hyperreal.omega (show (0 : ℝ*) < 1 by norm_num)
  rw [nsmul_eq_mul, mul_one] at hn
  exact absurd hn (not_le.2 (nat_lt_omega n))

/-- The standard part of `r + ε·k` is `r`, for standard `r` and integer `k`
(a granular shift of a standard number is invisible to the shadow). -/
theorem stdPart_coe_add_eps (r : ℝ) (k : ℤ) :
    stdPart ((r : ℝ*) + (k : ℝ*) * Hyperreal.epsilon) = r := by
  rw [stdPart_add_infinitesimal (epsilon_isInfinitesimal.int_mul k)]
  exact Hyperreal.stdPart_coe r

/-- **Existence of the standard part.** Every finite hyperreal is infinitely
close to the standard real `st x`. -/
theorem isInfinitesimal_sub_stdPart {x : ℝ*} (hx : IsFinite x) :
    IsInfinitesimal (x - (stdPart x : ℝ*)) :=
  mk_sub_stdPart_pos Hyperreal.coeRingHom hx

/-- **Uniqueness of the standard part.** -/
theorem stdPart_unique {x : ℝ*} {r : ℝ} (h : IsInfinitesimal (x - (r : ℝ*))) :
    stdPart x = r := by
  rw [stdPart_eq_of_sub_infinitesimal h, Hyperreal.stdPart_coe]

/-- `ℝ*` is a non-Archimedean field (combined statement): `ω` exceeds every
natural number, `ε` is a positive infinitesimal below every positive real,
and the Archimedean property fails. -/
theorem hyperreal_nonarchimedean :
    (∀ n : ℕ, (n : ℝ*) < Hyperreal.omega) ∧ IsInfinitesimal Hyperreal.epsilon ∧
    0 < Hyperreal.epsilon ∧ (∀ r : ℝ, 0 < r → Hyperreal.epsilon < (r : ℝ*)) ∧
    ¬ Archimedean ℝ* :=
  ⟨nat_lt_omega, epsilon_isInfinitesimal, Hyperreal.epsilon_pos, epsilon_lt_pos,
    not_archimedean⟩

/-- Characterisation of infinitesimals (combined statement). -/
theorem infinitesimal_char :
    (∀ x : ℝ*, IsInfinitesimal x ↔ ∀ n : ℕ, (n : ℝ*) * |x| < 1) ∧
    (∀ x : ℝ*, IsInfinitesimal x ↔ ∀ r : ℝ, 0 < r → |x| < (r : ℝ*)) :=
  ⟨isInfinitesimal_iff, hyper_isInfinitesimal_iff⟩

/-- **Standard part theorem** (combined): existence, uniqueness, and the
homomorphism/monotonicity properties. -/
theorem stdPart_theorem :
    (∀ x : ℝ*, IsFinite x → IsInfinitesimal (x - (stdPart x : ℝ*))) ∧
    (∀ (x : ℝ*) (r : ℝ), IsInfinitesimal (x - (r : ℝ*)) → stdPart x = r) ∧
    (∀ x y : ℝ*, IsFinite x → IsFinite y →
      stdPart (x + y) = stdPart x + stdPart y ∧ stdPart (x * y) = stdPart x * stdPart y ∧
      (x ≤ y → stdPart x ≤ stdPart y) ∧ (IsInfinitesimal (x - y) → stdPart x = stdPart y)) :=
  ⟨fun _ hx => isInfinitesimal_sub_stdPart hx, fun _ _ h => stdPart_unique h,
    fun _ _ hx hy => stdPart_properties hx hy⟩

/-- Granular shifts are invisible to the shadow (combined). -/
theorem stdPart_shift :
    (∀ (r : ℝ) (k : ℤ), stdPart ((r : ℝ*) + (k : ℝ*) * Hyperreal.epsilon) = r) ∧
    (∀ x δ : ℝ*, IsInfinitesimal δ → stdPart (x + δ) = stdPart x) :=
  ⟨stdPart_coe_add_eps, fun _ _ h => stdPart_add_infinitesimal h⟩

end Hyper

/-! ## Internal sets, countable saturation, overspill -/

section Saturation

/-- Eventually (along the hyperfilter) `n ≥ k`. -/
theorem eventually_ge (k : ℕ) : ∀ᶠ n in (hyperfilter ℕ : Filter ℕ), k ≤ n := by
  have : ∀ᶠ n in (cofinite : Filter ℕ), k ≤ n := by
    rw [Nat.cofinite_eq_atTop]; exact eventually_ge_atTop k
  exact hyperfilter_le_cofinite this

/-- **Countable saturation of the ultrapower over `ℕ`** (`ℵ₁`-saturation),
in sequence form.  Internal sets are presented by sequences of sets `B k n`
(`k` indexes the internal set, `n` the ultrapower coordinate).  If every
finite subfamily has a common element (in the ultrapower), the whole
countable family has a common element. -/
theorem countable_saturation {α : Type*} [Nonempty α] (B : ℕ → ℕ → Set α)
    (hfip : ∀ K : ℕ, ∃ f : ℕ → α, ∀ k ≤ K, ∀ᶠ n in (hyperfilter ℕ : Filter ℕ), f n ∈ B k n) :
    ∃ g : ℕ → α, ∀ k, ∀ᶠ n in (hyperfilter ℕ : Filter ℕ), g n ∈ B k n := by
  classical
  -- `P n K` : the first `K+1` sets have a common point in coordinate `n`.
  let P : ℕ → ℕ → Prop := fun n K => ∃ y : α, ∀ k ≤ K, y ∈ B k n
  let Kn : ℕ → ℕ := fun n => Nat.findGreatest (P n) n
  let g : ℕ → α := fun n => if h : P n (Kn n) then Classical.choose h else Classical.arbitrary α
  refine ⟨g, fun k => ?_⟩
  obtain ⟨f, hf⟩ := hfip k
  have hall : ∀ᶠ n in (hyperfilter ℕ : Filter ℕ), ∀ j ∈ Finset.range (k + 1), f n ∈ B j n :=
    (Filter.eventually_all_finset _).2 (fun j hj => hf j (by simpa [Nat.lt_succ_iff] using hj))
  filter_upwards [hall, eventually_ge k] with n hn hkn
  have hPk : P n k := ⟨f n, fun j hj => hn j (by simpa [Nat.lt_succ_iff] using hj)⟩
  have hspec : P n (Kn n) := Nat.findGreatest_spec hkn hPk
  have hle : k ≤ Kn n := Nat.le_findGreatest hkn hPk
  simp only [g, hspec, ↓reduceDIte]
  exact Classical.choose_spec hspec k hle

/-- The internal subset of `ℝ*` presented by a sequence of sets `B n ⊆ ℝ`
(the ultraproduct `∏ B n / U`). -/
def internalSet (B : ℕ → Set ℝ) : Set ℝ* :=
  {x | ∃ f : ℕ → ℝ, Hyperreal.ofSeq f = x ∧ ∀ᶠ n in (hyperfilter ℕ : Filter ℕ), f n ∈ B n}

/-- Membership in an internal set does not depend on the representative. -/
theorem mem_internalSet_iff (B : ℕ → Set ℝ) (f : ℕ → ℝ) :
    Hyperreal.ofSeq f ∈ internalSet B ↔ ∀ᶠ n in (hyperfilter ℕ : Filter ℕ), f n ∈ B n := by
  constructor
  · rintro ⟨g, hg, hgB⟩
    have heq : ∀ᶠ n in (hyperfilter ℕ : Filter ℕ), g n = f n := Filter.Germ.coe_eq.1 hg
    filter_upwards [heq, hgB] with n h1 h2
    rwa [← h1]
  · intro h; exact ⟨f, rfl, h⟩

/-- **Countable saturation for internal subsets of `ℝ*`.** A countable family
of internal sets with the finite intersection property has nonempty
intersection. -/
theorem internal_countable_saturation (B : ℕ → ℕ → Set ℝ)
    (hfip : ∀ K : ℕ, ∃ x : ℝ*, ∀ k ≤ K, x ∈ internalSet (B k)) :
    ∃ x : ℝ*, ∀ k, x ∈ internalSet (B k) := by
  have hfip' : ∀ K : ℕ, ∃ f : ℕ → ℝ, ∀ k ≤ K,
      ∀ᶠ n in (hyperfilter ℕ : Filter ℕ), f n ∈ B k n := by
    intro K
    obtain ⟨x, hx⟩ := hfip K
    obtain ⟨f, rfl⟩ := Hyperreal.ofSeq_surjective x
    exact ⟨f, fun k hk => (mem_internalSet_iff _ f).1 (hx k hk)⟩
  obtain ⟨g, hg⟩ := countable_saturation B hfip'
  exact ⟨Hyperreal.ofSeq g, fun k => (mem_internalSet_iff _ g).2 (hg k)⟩

/-- Internal sets form a Boolean algebra: set difference is computed
coordinatewise (this uses that the hyperfilter is an *ultra*filter). -/
theorem internalSet_diff (A C : ℕ → Set ℝ) :
    internalSet (fun n => A n \ C n) = internalSet A \ internalSet C := by
  ext x
  obtain ⟨f, rfl⟩ := Hyperreal.ofSeq_surjective x
  simp only [Set.mem_sdiff, mem_internalSet_iff]
  rw [← Ultrafilter.eventually_not, ← Filter.eventually_and]

/-- **The key lemma behind Loeb measure.** If an internal set is covered by a
countable family of internal sets, it is already covered by finitely many of
them.  Consequently a countable disjoint union of nonempty internal sets is
never internal, and `st ∘ ν` is (vacuously) countably additive on the
internal algebra. -/
theorem internal_cover_finite (A : ℕ → Set ℝ) (C : ℕ → ℕ → Set ℝ)
    (hcov : internalSet A ⊆ ⋃ k, internalSet (C k)) :
    ∃ K : ℕ, internalSet A ⊆ ⋃ k ∈ Finset.range (K + 1), internalSet (C k) := by
  by_contra hne
  push Not at hne
  have hfip : ∀ K : ℕ, ∃ x : ℝ*, ∀ k ≤ K, x ∈ internalSet (fun n => A n \ C k n) := by
    intro K
    obtain ⟨x, hxA, hxC⟩ := Set.not_subset.1 (hne K)
    refine ⟨x, fun k hk => ?_⟩
    rw [internalSet_diff]
    refine ⟨hxA, fun hxk => hxC ?_⟩
    exact Set.mem_biUnion (Finset.mem_range.2 (Nat.lt_succ_of_le hk)) hxk
  obtain ⟨x, hx⟩ := internal_countable_saturation (fun k n => A n \ C k n) hfip
  have hxA : x ∈ internalSet A := by
    have := hx 0; rw [internalSet_diff] at this; exact this.1
  obtain ⟨k, hk⟩ := Set.mem_iUnion.1 (hcov hxA)
  have := hx k; rw [internalSet_diff] at this; exact this.2 hk

/-- **Overspill.** Let `A = ∏ A n / U` be an internal set of hypernaturals
(presented by `A n ⊆ ℕ`).  If `A` contains every standard natural number,
then it contains an infinite hypernatural, i.e. an element `[f]` exceeding
every standard real. -/
theorem overspill (A : ℕ → Set ℕ)
    (h : ∀ m : ℕ, ∀ᶠ n in (hyperfilter ℕ : Filter ℕ), m ∈ A n) :
    ∃ f : ℕ → ℕ, (∀ᶠ n in (hyperfilter ℕ : Filter ℕ), f n ∈ A n) ∧
      ∀ r : ℝ, (r : ℝ*) < Hyperreal.ofSeq (fun n => (f n : ℝ)) := by
  classical
  let P : ℕ → ℕ → Prop := fun n m => ∀ j ≤ m, j ∈ A n
  let f : ℕ → ℕ := fun n => Nat.findGreatest (P n) n
  -- for every standard `k`, eventually `[0,k] ⊆ A n` and `k ≤ n`
  have key : ∀ k : ℕ, ∀ᶠ n in (hyperfilter ℕ : Filter ℕ), P n k ∧ k ≤ n := by
    intro k
    have hall : ∀ᶠ n in (hyperfilter ℕ : Filter ℕ), ∀ j ∈ Finset.range (k + 1), j ∈ A n :=
      (Filter.eventually_all_finset _).2 (fun j _ => h j)
    filter_upwards [hall, eventually_ge k] with n hn hkn
    exact ⟨fun j hj => hn j (by simpa [Nat.lt_succ_iff] using hj), hkn⟩
  refine ⟨f, ?_, ?_⟩
  · filter_upwards [key 0] with n hn
    exact Nat.findGreatest_spec hn.2 hn.1 (f n) le_rfl
  · intro r
    obtain ⟨k, hk⟩ := exists_nat_gt r
    have : ∀ᶠ n in (hyperfilter ℕ : Filter ℕ), r < (f n : ℝ) := by
      filter_upwards [key k] with n hn
      have : k ≤ f n := Nat.le_findGreatest hn.2 hn.1
      exact lt_of_lt_of_le hk (by exact_mod_cast this)
    exact Hyperreal.ofSeq_lt_ofSeq.2 this

/-- **Underspill** (for hypernaturals). If an internal set of hypernaturals
contains every infinite hypernatural, it contains a standard one. -/
theorem underspill (A : ℕ → Set ℕ)
    (h : ∀ f : ℕ → ℕ, (∀ r : ℝ, (r : ℝ*) < Hyperreal.ofSeq (fun n => (f n : ℝ))) →
      ∀ᶠ n in (hyperfilter ℕ : Filter ℕ), f n ∈ A n) :
    ∃ m : ℕ, ∀ᶠ n in (hyperfilter ℕ : Filter ℕ), m ∈ A n := by
  by_contra hne
  push Not at hne
  have hc : ∀ m : ℕ, ∀ᶠ n in (hyperfilter ℕ : Filter ℕ), m ∈ (A n)ᶜ := fun m => hne m
  obtain ⟨f, hf, hinf⟩ := overspill (fun n => (A n)ᶜ) hc
  have h2 := h f hinf
  obtain ⟨n, h1, h3⟩ := (hf.and h2).exists
  exact h1 h3

/-- **The standard natural numbers form an external set**: no internal subset
of `ℝ*` consists exactly of the standard naturals. -/
theorem standard_naturals_external (B : ℕ → Set ℝ) :
    internalSet B ≠ Set.range (fun m : ℕ => ((m : ℝ) : ℝ*)) := by
  intro hB
  have hstd : ∀ m : ℕ, ∀ᶠ n in (hyperfilter ℕ : Filter ℕ), m ∈ {j : ℕ | (j : ℝ) ∈ B n} := by
    intro m
    have hm : ((m : ℝ) : ℝ*) ∈ internalSet B := by rw [hB]; exact ⟨m, rfl⟩
    exact (mem_internalSet_iff B (fun _ => (m : ℝ))).1 hm
  obtain ⟨f, hf, hinf⟩ := overspill _ hstd
  have hmem : Hyperreal.ofSeq (fun n => (f n : ℝ)) ∈ internalSet B :=
    (mem_internalSet_iff B _).2 hf
  rw [hB] at hmem
  obtain ⟨m, hm⟩ := hmem
  have := hinf m
  simp only at hm
  rw [hm] at this
  exact lt_irrefl _ this

/-- **The monad of `0` (the set of infinitesimals) is external.** -/
theorem infinitesimals_external (B : ℕ → Set ℝ) :
    internalSet B ≠ {x : ℝ* | IsInfinitesimal x} := by
  intro hB
  -- `S = {m : 1/(m+1) ∉ B}` contains every standard `m`
  have hstd : ∀ m : ℕ, ∀ᶠ n in (hyperfilter ℕ : Filter ℕ),
      m ∈ {j : ℕ | (1 / ((j : ℝ) + 1)) ∉ B n} := by
    intro m
    have hnot : ((1 / ((m : ℝ) + 1) : ℝ) : ℝ*) ∉ internalSet B := by
      rw [hB]
      intro hI
      have h0 : (1 / ((m : ℝ) + 1) : ℝ) ≠ 0 := by positivity
      have := Hyperreal.archimedeanClassMk_coe h0
      have hI' : 0 < ArchimedeanClass.mk (((1 / ((m : ℝ) + 1) : ℝ) : ℝ*)) := hI
      rw [this] at hI'
      exact lt_irrefl _ hI'
    have := (not_congr (mem_internalSet_iff B (fun _ => (1 / ((m : ℝ) + 1) : ℝ)))).1 hnot
    exact Ultrafilter.eventually_not.2 this
  obtain ⟨f, hf, hinf⟩ := overspill _ hstd
  -- but `1/(ν+1)` is infinitesimal for the infinite `ν = [f]`
  set g : ℕ → ℝ := fun n => 1 / ((f n : ℝ) + 1) with hg
  have hnotin : Hyperreal.ofSeq g ∉ internalSet B := by
    rw [mem_internalSet_iff]
    intro hin
    obtain ⟨n, h1, h2⟩ := (hf.and hin).exists
    exact h1 h2
  apply hnotin
  rw [hB]
  show IsInfinitesimal (Hyperreal.ofSeq g)
  rw [hyper_isInfinitesimal_iff]
  intro r hr
  have hpos : (0 : ℝ*) < Hyperreal.ofSeq g := by
    apply Hyperreal.ofSeq_lt_ofSeq.2
    exact Filter.Eventually.of_forall (fun n => by simp only [hg]; positivity)
  rw [abs_of_pos hpos]
  have hev : ∀ᶠ n in (hyperfilter ℕ : Filter ℕ), g n < r := by
    have h1 := hinf (1 / r)
    have h1' : ∀ᶠ n in (hyperfilter ℕ : Filter ℕ), 1 / r < (f n : ℝ) := Hyperreal.ofSeq_lt_ofSeq.1 h1
    filter_upwards [h1'] with n hn
    simp only [hg]
    rw [div_lt_iff₀ (by positivity)]
    rw [div_lt_iff₀ hr] at hn
    nlinarith
  exact Hyperreal.ofSeq_lt_ofSeq.2 hev

/-- **A hyperfinite set containing every standard natural number**: the
internal set `∏ {0,…,n} / U = {0,…,ω}`. -/
theorem hyperfinite_contains_standard (m : ℕ) :
    ∀ᶠ n in (hyperfilter ℕ : Filter ℕ), m ∈ Finset.range (n + 1) := by
  filter_upwards [eventually_ge m] with n hn
  simpa [Finset.mem_range, Nat.lt_succ_iff] using hn

/-- Externality of `ℕ` and of the monad of `0` (combined). -/
theorem externality (B : ℕ → Set ℝ) :
    internalSet B ≠ Set.range (fun m : ℕ => ((m : ℝ) : ℝ*)) ∧
    internalSet B ≠ {x : ℝ* | IsInfinitesimal x} :=
  ⟨standard_naturals_external B, infinitesimals_external B⟩

end Saturation

/-! ## Hyperfinite sums: exact granular computations -/

section Sums
variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

theorem sum_range_cast_mul_two (N : ℕ) :
    (∑ k ∈ Finset.range N, (k : K)) * 2 = (N : K) * ((N : K) - 1) := by
  induction N with
  | zero => simp
  | succ n ih => rw [Finset.sum_range_succ, add_mul, ih]; push_cast; ring

/-- **The granular Riemann sum of `x` on `[0,1)`.** With `2εN = 1`,
`∑_{x ∈ [0,1) ∩ 𝕃} x · 2ε = 1/2 - ε` exactly; its shadow is `∫₀¹ x dx = 1/2`. -/
theorem granular_sum_id_Ico (ε : K) (N : ℕ) (hN : 2 * ε * N = 1) :
    ∑ k ∈ Finset.range N, (2 * ε * k) * (2 * ε) = 1 / 2 - ε := by
  have h : ∑ k ∈ Finset.range N, (2 * ε * k) * (2 * ε)
      = (2 * ε) ^ 2 * ((∑ k ∈ Finset.range N, (k : K)) * 2) / 2 := by
    rw [Finset.sum_mul, Finset.mul_sum, Finset.sum_div]
    refine Finset.sum_congr rfl (fun k _ => by ring)
  rw [h, sum_range_cast_mul_two]
  have : (2 * ε) ^ 2 * ((N : K) * ((N : K) - 1)) = (2 * ε * N) * (2 * ε * N) - 2 * ε * (2 * ε * N) := by ring
  rw [this, hN]; ring

/-- The same sum over the closed interval `[0,1] ∩ 𝕃`: `1/2 + ε`. -/
theorem granular_sum_id_Icc (ε : K) (N : ℕ) (hN : 2 * ε * N = 1) :
    ∑ k ∈ Finset.range (N + 1), (2 * ε * k) * (2 * ε) = 1 / 2 + ε := by
  rw [Finset.sum_range_succ, granular_sum_id_Ico ε N hN, hN]; ring

/-- Internal cardinality of the symmetric lattice `{-M,…,M}` is `2M+1`. -/
theorem card_symm_lattice (M : ℕ) : (Finset.Icc (-(M : ℤ)) M).card = 2 * M + 1 := by
  rw [Int.card_Icc]; omega

end Sums

end QE.NSA
