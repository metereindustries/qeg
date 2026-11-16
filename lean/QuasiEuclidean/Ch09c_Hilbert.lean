-- SPDX-License-Identifier: MIT
-- Copyright 2026 Metere Industries, Inc. Author: Alfredo Metere.
-- Quasi-Euclidean Granular Geometry. Any derivative work must carry this notice:
--   This work is derivative of the Quasi-Euclidean Granular Geometry book
--   authored by Alfredo Metere. Copyright 2026 Metere Industries, Inc.
--   All rights reserved
-- See LICENSE.md and NOTICE.

import QuasiEuclidean.Basic
import QuasiEuclidean.Ch02_Hyper
import QuasiEuclidean.ChA_NSA

/-!
# Chapter 9c: Hilbert's axioms and the granular plane

Formal counterparts of the chapter on Hilbert's *Grundlagen der Geometrie*
(`ch:hilbert`).

* `HilbertPlane P`: Hilbert's axiom groups I (incidence), II (order, with
  Pasch), III (congruence of segments and of angles, with the side-angle-side
  axiom) and IV (parallels), stated for undefined "things" `P` exactly as in
  the *Grundlagen*; the continuity axioms V.1 (Archimedes) and Dedekind's
  axiom are predicates `Archimedes`, `Dedekind` on such a plane.
* `cartesian F hP`: the Cartesian plane over any Pythagorean ordered field is
  a model of I–IV.  Hence the plane `ℝ* × ℝ*` of centres of the granular
  geometry is a Hilbert plane (`cartesian_hyperreal`).
* `archimedes_iff`: V.1 holds in the Cartesian plane over `F` iff `F` is an
  Archimedean field; `dedekind_iff`: Dedekind's axiom holds iff `F` is
  Dedekind complete, hence iff `F ≃+*o ℝ` (`dedekind_real`).
* Euclid's first definition ("a point is that which has no part") is made
  precise as the absence of negligible segments, and shown equivalent to
  V.1 (`noPart_iff_archimedean`); the granular plane has a negligible
  segment, the granule (`granule_negligible`), while satisfying I–IV.
* The shadow map `sh : ℝ* × ℝ* → ℝ × ℝ` preserves lines, betweenness and
  congruence, is onto, and identifies exactly the points at infinitesimal
  distance; a granular point `ball(c, ε)` has distinct points with the same
  shadow (`point_has_parts`): the classical point is the shadow of the
  granular point.
* Hilbert's completeness: an Archimedean Cartesian plane embeds in `ℝ²`, and
  `ℝ²` admits no proper Archimedean extension; without V.1 every ordered
  field has a proper ordered extension (`exists_proper_extension`), so
  completeness without Archimedes is unsatisfiable, as Hilbert noted.
* Transfer: the granular plane and the real plane satisfy the same sentences
  of Tarski's first-order language of betweenness and congruence
  (`tarski_transfer`); V.1 and Dedekind's axiom are therefore not elementary
  (`archimedes_not_elementary`).
-/

set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000

namespace QE.Hilbert

/-! ## The Cartesian plane over an ordered field -/

section Plane
variable {F : Type*} [Field F] [LinearOrder F] [IsStrictOrderedRing F]

/-- Points of the Cartesian plane. -/
abbrev Pt (F : Type*) := F × F

/-- The cross product of two vectors (twice the signed area). -/
def cr (u v : Pt F) : F := u.1 * v.2 - u.2 * v.1

/-- The inner product of two vectors. -/
def ip (u v : Pt F) : F := u.1 * v.1 + u.2 * v.2

/-- Squared distance. -/
def q (A B : Pt F) : F := (A.1 - B.1) ^ 2 + (A.2 - B.2) ^ 2

/-- Lines: zero sets of non-degenerate affine functionals. -/
def IsLine (L : Set (Pt F)) : Prop :=
  ∃ a b c : F, (a ≠ 0 ∨ b ≠ 0) ∧ L = {p | a * p.1 + b * p.2 + c = 0}

/-- Strict betweenness: `B` lies between `A` and `C`. -/
def Btw (A B C : Pt F) : Prop :=
  A ≠ C ∧ ∃ t : F, 0 < t ∧ t < 1 ∧ B.1 = A.1 + t * (C.1 - A.1) ∧ B.2 = A.2 + t * (C.2 - A.2)

/-- Congruence of segments. -/
def Cong (A B C D : Pt F) : Prop := q A B = q C D

/-- Congruence of angles `∠BAC ≅ ∠B'A'C'`: equality of cosines, written
without square roots (equal squares and equal signs of the inner products
after cross-multiplication by the squared lengths). -/
def AngCong (B A C B' A' C' : Pt F) : Prop :=
  ip (B - A) (C - A) ^ 2 * (q A' B' * q A' C') = ip (B' - A') (C' - A') ^ 2 * (q A B * q A C) ∧
  0 ≤ ip (B - A) (C - A) * ip (B' - A') (C' - A')

theorem q_comm (A B : Pt F) : q A B = q B A := by unfold q; ring

theorem q_nonneg (A B : Pt F) : 0 ≤ q A B := by unfold q; positivity

theorem q_eq_zero_iff (A B : Pt F) : q A B = 0 ↔ A = B := by
  unfold q
  constructor
  · intro h
    have h1 : A.1 - B.1 = 0 := by nlinarith [sq_nonneg (A.1 - B.1), sq_nonneg (A.2 - B.2)]
    have h2 : A.2 - B.2 = 0 := by nlinarith [sq_nonneg (A.1 - B.1), sq_nonneg (A.2 - B.2)]
    exact Prod.ext (by linarith) (by linarith)
  · rintro rfl; ring

theorem q_pos_of_ne {A B : Pt F} (h : A ≠ B) : 0 < q A B :=
  lt_of_le_of_ne (q_nonneg A B) (fun h0 => h ((q_eq_zero_iff A B).1 h0.symm))

theorem q_eq_ip (A B : Pt F) : q A B = ip (B - A) (B - A) := by
  simp only [q, ip, Prod.fst_sub, Prod.snd_sub]; ring

/-- Lagrange's identity in the plane. -/
theorem lagrange (u v : Pt F) : ip u v ^ 2 + cr u v ^ 2 = ip u u * ip v v := by
  simp only [ip, cr]; ring

theorem cr_eq_zero_of_ne {u : Pt F} (hu : u ≠ 0) {v : Pt F} (h : cr u v = 0) :
    ∃ s : F, v = (s * u.1, s * u.2) := by
  have hu' : u.1 ≠ 0 ∨ u.2 ≠ 0 := by
    by_contra hc; push_neg at hc; exact hu (Prod.ext hc.1 hc.2)
  simp only [cr] at h
  rcases hu' with h1 | h2
  · refine ⟨v.1 / u.1, Prod.ext ?_ ?_⟩
    · simp; field_simp
    · simp; field_simp; linarith
  · refine ⟨v.2 / u.2, Prod.ext ?_ ?_⟩
    · simp; field_simp; linarith
    · simp; field_simp

/-- The line through two distinct points. -/
def lineThrough (A B : Pt F) : Set (Pt F) := {p | cr (B - A) (p - A) = 0}

theorem isLine_lineThrough {A B : Pt F} (h : A ≠ B) : IsLine (lineThrough A B) := by
  refine ⟨B.2 - A.2, -(B.1 - A.1), -((B.2 - A.2) * A.1 - (B.1 - A.1) * A.2), ?_, ?_⟩
  · by_contra hc; push_neg at hc
    exact h (Prod.ext (by linarith [hc.2]) (by linarith [hc.1])).symm
  · ext p; simp only [lineThrough, cr, Set.mem_setOf_eq, Prod.fst_sub, Prod.snd_sub]
    constructor <;> intro h <;> linarith

theorem left_mem_lineThrough (A B : Pt F) : A ∈ lineThrough A B := by
  simp [lineThrough, cr]

theorem right_mem_lineThrough (A B : Pt F) : B ∈ lineThrough A B := by
  simp [lineThrough, cr]; ring

/-- Membership in a line containing two distinct points `A ≠ B` is the
vanishing of the cross product with `B - A`. -/
theorem mem_line_iff {L : Set (Pt F)} (hL : IsLine L) {A B : Pt F} (hA : A ∈ L) (hB : B ∈ L)
    (hAB : A ≠ B) (p : Pt F) : p ∈ L ↔ cr (B - A) (p - A) = 0 := by
  obtain ⟨a, b, c, hab, rfl⟩ := hL
  simp only [Set.mem_setOf_eq] at hA hB ⊢
  simp only [cr, Prod.fst_sub, Prod.snd_sub]
  constructor
  · intro hp
    have e1 : a * ((B.1 - A.1) * (p.2 - A.2) - (B.2 - A.2) * (p.1 - A.1)) = 0 := by
      linear_combination (p.2 - A.2) * hB - (p.2 - A.2) * hA - (B.2 - A.2) * hp + (B.2 - A.2) * hA
    have e2 : b * ((B.1 - A.1) * (p.2 - A.2) - (B.2 - A.2) * (p.1 - A.1)) = 0 := by
      linear_combination (B.1 - A.1) * hp - (B.1 - A.1) * hA - (p.1 - A.1) * hB + (p.1 - A.1) * hA
    rcases hab with ha | hb
    · exact (mul_eq_zero.1 e1).resolve_left ha
    · exact (mul_eq_zero.1 e2).resolve_left hb
  · intro hc
    have hu : (B.1 - A.1 ≠ 0) ∨ (B.2 - A.2 ≠ 0) := by
      by_contra h; push_neg at h
      exact hAB (Prod.ext (by linarith [h.1]) (by linarith [h.2]))
    have e1 : (B.1 - A.1) * (a * p.1 + b * p.2 + c) = 0 := by
      linear_combination (B.1 - A.1) * hA + b * hc + (p.1 - A.1) * hB - (p.1 - A.1) * hA
    have e2 : (B.2 - A.2) * (a * p.1 + b * p.2 + c) = 0 := by
      linear_combination (B.2 - A.2) * hA - a * hc + (p.2 - A.2) * hB - (p.2 - A.2) * hA
    rcases hu with h1 | h2
    · exact (mul_eq_zero.1 e1).resolve_left h1
    · exact (mul_eq_zero.1 e2).resolve_left h2

/-- A line is determined by two of its points (Hilbert I.2). -/
theorem line_unique {L L' : Set (Pt F)} (hL : IsLine L) (hL' : IsLine L') {A B : Pt F}
    (hAB : A ≠ B) (hA : A ∈ L) (hB : B ∈ L) (hA' : A ∈ L') (hB' : B ∈ L') : L = L' := by
  ext p
  rw [mem_line_iff hL hA hB hAB, mem_line_iff hL' hA' hB' hAB]

theorem lineThrough_eq {L : Set (Pt F)} (hL : IsLine L) {A B : Pt F} (hAB : A ≠ B)
    (hA : A ∈ L) (hB : B ∈ L) : L = lineThrough A B :=
  line_unique hL (isLine_lineThrough hAB) hAB hA hB (left_mem_lineThrough A B)
    (right_mem_lineThrough A B)

/-- Points of the line through `A ≠ P` are the affine combinations `A + s (P - A)`. -/
theorem mem_lineThrough_iff {A P : Pt F} (hAP : A ≠ P) (p : Pt F) :
    p ∈ lineThrough A P ↔ ∃ s : F, p.1 = A.1 + s * (P.1 - A.1) ∧ p.2 = A.2 + s * (P.2 - A.2) := by
  constructor
  · intro hp
    have hu : P - A ≠ 0 := fun h => hAP (by
      have := congrArg (· + A) h; simpa using this.symm)
    obtain ⟨s, hs⟩ := cr_eq_zero_of_ne hu hp
    refine ⟨s, ?_, ?_⟩
    · have := congrArg Prod.fst hs; simp at this; linarith
    · have := congrArg Prod.snd hs; simp at this; linarith
  · rintro ⟨s, h1, h2⟩
    simp only [lineThrough, cr, Set.mem_setOf_eq, Prod.fst_sub, Prod.snd_sub, h1, h2]; ring

/-- Collinearity. -/
def Col (A B C : Pt F) : Prop := ∃ L, IsLine L ∧ A ∈ L ∧ B ∈ L ∧ C ∈ L

theorem col_iff (A B C : Pt F) : Col A B C ↔ cr (B - A) (C - A) = 0 := by
  constructor
  · rintro ⟨L, hL, hA, hB, hC⟩
    by_cases hAB : A = B
    · subst hAB; simp [cr]
    · exact (mem_line_iff hL hA hB hAB C).1 hC
  · intro h
    by_cases hAB : A = B
    · subst hAB
      by_cases hAC : A = C
      · subst hAC
        exact ⟨lineThrough A (A + (1, 0)), isLine_lineThrough (by simp),
          left_mem_lineThrough _ _, left_mem_lineThrough _ _, left_mem_lineThrough _ _⟩
      · exact ⟨lineThrough A C, isLine_lineThrough hAC, left_mem_lineThrough _ _,
          left_mem_lineThrough _ _, right_mem_lineThrough _ _⟩
    · exact ⟨lineThrough A B, isLine_lineThrough hAB, left_mem_lineThrough _ _,
        right_mem_lineThrough _ _, h⟩

/-! ### Group I: incidence -/

theorem I1 (A B : Pt F) (h : A ≠ B) : ∃ L, IsLine L ∧ A ∈ L ∧ B ∈ L :=
  ⟨lineThrough A B, isLine_lineThrough h, left_mem_lineThrough A B, right_mem_lineThrough A B⟩

theorem I2 (A B : Pt F) (L L' : Set (Pt F)) (h : A ≠ B) (hL : IsLine L) (hL' : IsLine L')
    (hA : A ∈ L) (hB : B ∈ L) (hA' : A ∈ L') (hB' : B ∈ L') : L = L' :=
  line_unique hL hL' h hA hB hA' hB'

theorem I3a (L : Set (Pt F)) (hL : IsLine L) : ∃ A B : Pt F, A ≠ B ∧ A ∈ L ∧ B ∈ L := by
  obtain ⟨a, b, c, hab, rfl⟩ := hL
  rcases hab with ha | hb
  · refine ⟨(-c / a, 0), (-(c + b) / a, 1), ?_, ?_, ?_⟩
    · intro h; have := congrArg Prod.snd h; simp at this
    · simp; field_simp; ring
    · simp; field_simp; ring
  · refine ⟨(0, -c / b), (1, -(c + a) / b), ?_, ?_, ?_⟩
    · intro h; have := congrArg Prod.fst h; simp at this
    · simp; field_simp; ring
    · simp; field_simp; ring

theorem I3b : ∃ A B C : Pt F, ∀ L, IsLine L → ¬ (A ∈ L ∧ B ∈ L ∧ C ∈ L) := by
  refine ⟨(0, 0), (1, 0), (0, 1), ?_⟩
  rintro L ⟨a, b, c, hab, rfl⟩ ⟨h1, h2, h3⟩
  simp at h1 h2 h3
  rcases hab with ha | hb
  · exact ha (by linarith)
  · exact hb (by linarith)

/-! ### Group II: order -/

theorem II1 (A B C : Pt F) (h : Btw A B C) :
    A ≠ B ∧ B ≠ C ∧ A ≠ C ∧ Btw C B A ∧ Col A B C := by
  obtain ⟨hAC, t, ht0, ht1, h1, h2⟩ := h
  have hne : C.1 - A.1 ≠ 0 ∨ C.2 - A.2 ≠ 0 := by
    by_contra hc; push_neg at hc
    exact hAC (Prod.ext (by linarith [hc.1]) (by linarith [hc.2]))
  refine ⟨?_, ?_, hAC, ⟨hAC.symm, 1 - t, by linarith, by linarith, by rw [h1]; ring,
    by rw [h2]; ring⟩, ?_⟩
  · intro hAB
    rw [← hAB] at h1 h2
    rcases hne with hc | hc
    · exact hc (by
        have : t * (C.1 - A.1) = 0 := by linarith
        exact (mul_eq_zero.1 this).resolve_left ht0.ne')
    · exact hc (by
        have : t * (C.2 - A.2) = 0 := by linarith
        exact (mul_eq_zero.1 this).resolve_left ht0.ne')
  · intro hBC
    rw [hBC] at h1 h2
    rcases hne with hc | hc
    · exact hc (by
        have : (1 - t) * (C.1 - A.1) = 0 := by linarith
        exact (mul_eq_zero.1 this).resolve_left (by linarith))
    · exact hc (by
        have : (1 - t) * (C.2 - A.2) = 0 := by linarith
        exact (mul_eq_zero.1 this).resolve_left (by linarith))
  · rw [col_iff]; simp only [cr, Prod.fst_sub, Prod.snd_sub, h1, h2]; ring

theorem II2 (A C : Pt F) (h : A ≠ C) : ∃ B, Btw A C B := by
  refine ⟨(2 * C.1 - A.1, 2 * C.2 - A.2), ?_, 1 / 2, by norm_num, by norm_num, ?_, ?_⟩
  · intro hc
    exact h (Prod.ext (by have := congrArg Prod.fst hc; simp at this; linarith)
      (by have := congrArg Prod.snd hc; simp at this; linarith))
  · simp; ring
  · simp; ring

theorem II3 (A B C : Pt F) (h : Btw A B C) : ¬ Btw B A C ∧ ¬ Btw A C B := by
  obtain ⟨hAC, t, ht0, ht1, h1, h2⟩ := h
  have hne : C.1 - A.1 ≠ 0 ∨ C.2 - A.2 ≠ 0 := by
    by_contra hc; push_neg at hc
    exact hAC (Prod.ext (by linarith [hc.1]) (by linarith [hc.2]))
  constructor
  · rintro ⟨-, s, hs0, hs1, g1, g2⟩
    -- A = B + s (C - B) with B = A + t (C - A): (t + s (1 - t)) (C - A) = 0
    have e1 : (t + s * (1 - t)) * (C.1 - A.1) = 0 := by
      rw [h1] at g1; linear_combination -g1
    have e2 : (t + s * (1 - t)) * (C.2 - A.2) = 0 := by
      rw [h2] at g2; linear_combination -g2
    have hpos : 0 < t + s * (1 - t) := by nlinarith
    rcases hne with hc | hc
    · exact hc ((mul_eq_zero.1 e1).resolve_left hpos.ne')
    · exact hc ((mul_eq_zero.1 e2).resolve_left hpos.ne')
  · rintro ⟨-, s, hs0, hs1, g1, g2⟩
    -- C = A + s (B - A) = A + s t (C - A): (1 - s t)(C - A) = 0
    have e1 : (1 - s * t) * (C.1 - A.1) = 0 := by
      rw [h1] at g1; linear_combination g1
    have e2 : (1 - s * t) * (C.2 - A.2) = 0 := by
      rw [h2] at g2; linear_combination g2
    have hpos : 0 < 1 - s * t := by nlinarith
    rcases hne with hc | hc
    · exact hc ((mul_eq_zero.1 e1).resolve_left hpos.ne')
    · exact hc ((mul_eq_zero.1 e2).resolve_left hpos.ne')

/-- The affine functional of a line, evaluated along a segment. -/
theorem affine_along {a b c : F} {A B X : Pt F} {t : F}
    (h1 : X.1 = A.1 + t * (B.1 - A.1)) (h2 : X.2 = A.2 + t * (B.2 - A.2)) :
    a * X.1 + b * X.2 + c = (1 - t) * (a * A.1 + b * A.2 + c) + t * (a * B.1 + b * B.2 + c) := by
  rw [h1, h2]; ring

/-- A segment whose endpoints have affine values of opposite signs crosses the line. -/
theorem crossing {a b c : F} {A B : Pt F} (hA : a * A.1 + b * A.2 + c ≠ 0)
    (hneg : (a * A.1 + b * A.2 + c) * (a * B.1 + b * B.2 + c) < 0) :
    ∃ X, a * X.1 + b * X.2 + c = 0 ∧ Btw A X B := by
  set φA := a * A.1 + b * A.2 + c with hφA
  set φB := a * B.1 + b * B.2 + c with hφB
  have hAB : A ≠ B := by
    rintro rfl; exact absurd hneg (not_lt.2 (mul_self_nonneg φA))
  have hd : φA - φB ≠ 0 := by
    intro h; have : φA = φB := by linarith
    rw [this] at hneg; exact absurd hneg (not_lt.2 (mul_self_nonneg φB))
  set t := φA / (φA - φB) with ht
  have hB : φB ≠ 0 := by rintro h; rw [h, mul_zero] at hneg; exact lt_irrefl _ hneg
  have ht0 : 0 < t := by
    rw [ht]
    rcases lt_or_gt_of_ne hA with h | h
    · have : φB > 0 := by nlinarith
      exact div_pos_of_neg_of_neg h (by linarith)
    · have : φB < 0 := by nlinarith
      exact div_pos h (by linarith)
  have ht1 : t < 1 := by
    rw [ht, div_lt_one_iff]
    rcases lt_or_gt_of_ne hA with h | h
    · have : φB > 0 := by nlinarith
      right; right; exact ⟨by linarith, by linarith⟩
    · have : φB < 0 := by nlinarith
      left; exact ⟨by linarith, by linarith⟩
  refine ⟨(A.1 + t * (B.1 - A.1), A.2 + t * (B.2 - A.2)), ?_, ⟨hAB, t, ht0, ht1, rfl, rfl⟩⟩
  have := affine_along (a := a) (b := b) (c := c) (A := A) (B := B)
    (X := (A.1 + t * (B.1 - A.1), A.2 + t * (B.2 - A.2))) (t := t) rfl rfl
  rw [this, ← hφA, ← hφB, ht]
  field_simp
  ring

/-- **Pasch's axiom** (Hilbert II.4). -/
theorem II4 (A B C : Pt F) (L : Set (Pt F)) (hL : IsLine L) (hcol : ¬ Col A B C)
    (hA : A ∉ L) (hB : B ∉ L) (hC : C ∉ L) (hX : ∃ X ∈ L, Btw A X B) :
    (∃ Y ∈ L, Btw A Y C) ∨ (∃ Y ∈ L, Btw B Y C) := by
  obtain ⟨a, b, c, hab, rfl⟩ := hL
  simp only [Set.mem_setOf_eq] at hA hB hC
  obtain ⟨X, hXL, hAC', t, ht0, ht1, h1, h2⟩ := hX
  simp only [Set.mem_setOf_eq] at hXL
  have hX' := affine_along (a := a) (b := b) (c := c) h1 h2
  rw [hXL] at hX'
  set φA := a * A.1 + b * A.2 + c
  set φB := a * B.1 + b * B.2 + c
  set φC := a * C.1 + b * C.2 + c
  have hAB : φA * φB < 0 := by
    have e : (1 - t) * φA = -(t * φB) := by linarith
    have e2 : t * (φA * φB) = -((1 - t) * φA ^ 2) := by linear_combination φA * e
    have hA2 : 0 < φA ^ 2 := lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 hA))
    have hneg : t * (φA * φB) < 0 := by rw [e2]; nlinarith
    by_contra hc; push_neg at hc
    exact absurd hneg (not_lt.2 (mul_nonneg ht0.le hc))
  rcases lt_or_gt_of_ne (mul_ne_zero hA hC) with h | h
  · left
    obtain ⟨Y, hY, hbtw⟩ := crossing hA h
    exact ⟨Y, hY, hbtw⟩
  · right
    have : φB * φC < 0 := by
      by_contra hc; push_neg at hc
      nlinarith [mul_neg_of_neg_of_pos hAB h, mul_nonneg (sq_nonneg φA) hc]
    obtain ⟨Y, hY, hbtw⟩ := crossing hB this
    exact ⟨Y, hY, hbtw⟩


/-! ### Group III: congruence of segments -/

/-- An ordered field is *Pythagorean* when every sum of two squares is a square. -/
def Pythagorean (F : Type*) [Field F] : Prop := ∀ x y : F, ∃ z : F, z ^ 2 = x ^ 2 + y ^ 2

theorem Pythagorean.sqrt_q (hP : Pythagorean F) (A B : Pt F) :
    ∃ r : F, 0 ≤ r ∧ r ^ 2 = q A B := by
  obtain ⟨z, hz⟩ := hP (A.1 - B.1) (A.2 - B.2)
  exact ⟨|z|, abs_nonneg z, by rw [sq_abs, hz]; rfl⟩

/-- `P` lies on the ray from `A` through `B`. -/
def OnRay (A B P : Pt F) : Prop :=
  ∃ s : F, 0 < s ∧ P.1 = A.1 + s * (B.1 - A.1) ∧ P.2 = A.2 + s * (B.2 - A.2)

theorem q_param {A B P : Pt F} {s : F} (h1 : P.1 = A.1 + s * (B.1 - A.1))
    (h2 : P.2 = A.2 + s * (B.2 - A.2)) : q A P = s ^ 2 * q A B := by
  simp only [q, h1, h2]; ring

theorem q_param' {A B P : Pt F} {s : F} (h1 : P.1 = A.1 + s * (B.1 - A.1))
    (h2 : P.2 = A.2 + s * (B.2 - A.2)) : q P B = (1 - s) ^ 2 * q A B := by
  simp only [q, h1, h2]; ring

theorem sqrt_pos_of_ne {A B : Pt F} (hAB : A ≠ B) {r : F} (hr0 : 0 ≤ r) (hr : r ^ 2 = q A B) :
    0 < r := by
  refine lt_of_le_of_ne hr0 fun h => ?_
  have hq := q_pos_of_ne hAB
  rw [← h] at hr
  norm_num at hr
  linarith

/-- **Segment transport** (Hilbert III.1): on the ray from `A'` through `B''` there is
exactly one point `B'` with `A'B' ≅ AB`. -/
theorem III1 (hP : Pythagorean F) (A B A' B'' : Pt F) (hAB : A ≠ B) (hA' : A' ≠ B'') :
    ∃! B', OnRay A' B'' B' ∧ Cong A B A' B' := by
  obtain ⟨r, hr0, hr⟩ := hP.sqrt_q A B
  obtain ⟨r', hr'0, hr'⟩ := hP.sqrt_q A' B''
  have hr1 := sqrt_pos_of_ne hAB hr0 hr
  have hr2 := sqrt_pos_of_ne hA' hr'0 hr'
  have hr2' := hr2.ne'
  set B' : Pt F := (A'.1 + (r / r') * (B''.1 - A'.1), A'.2 + (r / r') * (B''.2 - A'.2)) with hB'
  have hB'1 : B'.1 = A'.1 + (r / r') * (B''.1 - A'.1) := rfl
  have hB'2 : B'.2 = A'.2 + (r / r') * (B''.2 - A'.2) := rfl
  refine ⟨B', ⟨⟨r / r', div_pos hr1 hr2, hB'1, hB'2⟩, ?_⟩, ?_⟩
  · show q A B = q A' B'
    rw [q_param hB'1 hB'2, ← hr, ← hr']
    field_simp
  · rintro P ⟨⟨s, hs, h1, h2⟩, hc⟩
    have e : s ^ 2 * q A' B'' = (r / r') ^ 2 * q A' B'' := by
      rw [← q_param h1 h2, ← hc, ← hr, ← hr']
      field_simp
    have hs' : s = r / r' := by
      have hq := q_pos_of_ne hA'
      have : s ^ 2 = (r / r') ^ 2 := mul_right_cancel₀ hq.ne' e
      exact (sq_eq_sq₀ hs.le (div_pos hr1 hr2).le).1 this
    ext <;> simp [h1, h2, hs', hB']

theorem III2 (A B A' B' A'' B'' : Pt F) (h1 : Cong A' B' A B) (h2 : Cong A'' B'' A B) :
    Cong A' B' A'' B'' :=
  h1.trans h2.symm

theorem cong_swap (A B : Pt F) : Cong A B B A := q_comm A B

theorem cong_refl (A B : Pt F) : Cong A B A B := rfl

/-- **Addition of segments** (Hilbert III.3). -/
theorem III3 (A B C A' B' C' : Pt F) (h : Btw A B C) (h' : Btw A' B' C')
    (h1 : Cong A B A' B') (h2 : Cong B C B' C') : Cong A C A' C' := by
  obtain ⟨hAC, t, ht0, ht1, e1, e2⟩ := h
  obtain ⟨hAC', t', ht0', ht1', e1', e2'⟩ := h'
  have Q := q_pos_of_ne hAC
  have Q' := q_pos_of_ne hAC'
  unfold Cong at h1 h2 ⊢
  rw [q_param e1 e2, q_param e1' e2'] at h1
  rw [q_param' e1 e2, q_param' e1' e2'] at h2
  have key : (t * (1 - t') - t' * (1 - t)) *
      ((t * (1 - t') + t' * (1 - t)) * (q A C * q A' C')) = 0 := by
    linear_combination ((1 - t') ^ 2 * q A' C') * h1 - (t' ^ 2 * q A' C') * h2
  have h1t : 0 < 1 - t := by linarith
  have h1t' : 0 < 1 - t' := by linarith
  have hpos : 0 < (t * (1 - t') + t' * (1 - t)) * (q A C * q A' C') :=
    mul_pos (add_pos (mul_pos ht0 h1t') (mul_pos ht0' h1t)) (mul_pos Q Q')
  have h0 : t * (1 - t') - t' * (1 - t) = 0 := (mul_eq_zero.1 key).resolve_right hpos.ne'
  have htt : t = t' := by linarith
  subst htt
  exact mul_left_cancel₀ (pow_ne_zero 2 ht0.ne') h1

/-! ### Group IV: parallels -/

/-- The parallel to the line `{a x + b y + c = 0}` through `A`. -/
def parallelThrough (a b : F) (A : Pt F) : Set (Pt F) :=
  {p | a * (p.1 - A.1) + b * (p.2 - A.2) = 0}

theorem isLine_parallelThrough {a b : F} (hab : a ≠ 0 ∨ b ≠ 0) (A : Pt F) :
    IsLine (parallelThrough a b A) :=
  ⟨a, b, -(a * A.1 + b * A.2), hab, by
    ext p; simp only [parallelThrough, Set.mem_ofPred_eq]; constructor <;> intro h <;> linarith⟩

theorem self_mem_parallelThrough (a b : F) (A : Pt F) : A ∈ parallelThrough a b A := by
  simp [parallelThrough]

/-- Every line through `A` missing `L = {a x + b y + c = 0}` is the parallel through `A`. -/
theorem parallel_eq {a b c : F} (hab : a ≠ 0 ∨ b ≠ 0) {A : Pt F} (hA : a * A.1 + b * A.2 + c ≠ 0)
    {M : Set (Pt F)} (hM : IsLine M) (hAM : A ∈ M)
    (hdisj : ∀ X : Pt F, a * X.1 + b * X.2 + c = 0 → X ∉ M) : M = parallelThrough a b A := by
  obtain ⟨P₁, P₂, hne, hP₁, hP₂⟩ := I3a M hM
  obtain ⟨P, hPM, hPA⟩ : ∃ P ∈ M, P ≠ A := by
    by_cases h : P₁ = A
    · exact ⟨P₂, hP₂, fun h2 => hne (h.trans h2.symm)⟩
    · exact ⟨P₁, hP₁, h⟩
  have hMl : M = lineThrough A P := lineThrough_eq hM hPA.symm hAM hPM
  have hd : a * (P.1 - A.1) + b * (P.2 - A.2) = 0 := by
    by_contra hd
    apply hdisj (A.1 + (-(a * A.1 + b * A.2 + c) / (a * (P.1 - A.1) + b * (P.2 - A.2))) * (P.1 - A.1),
      A.2 + (-(a * A.1 + b * A.2 + c) / (a * (P.1 - A.1) + b * (P.2 - A.2))) * (P.2 - A.2))
    · simp only
      field_simp
      ring
    · rw [hMl, mem_lineThrough_iff hPA.symm]
      exact ⟨_, rfl, rfl⟩
  rw [hMl]
  exact line_unique (isLine_lineThrough hPA.symm) (isLine_parallelThrough hab A) hPA.symm
    (left_mem_lineThrough _ _) (right_mem_lineThrough _ _) (self_mem_parallelThrough a b A) hd

/-- **Euclid's axiom** (Hilbert IV): through a point off a line there is at most one
line not meeting it. -/
theorem IV (L : Set (Pt F)) (A : Pt F) (M M' : Set (Pt F)) (hL : IsLine L) (hA : A ∉ L)
    (hM : IsLine M) (hM' : IsLine M') (hAM : A ∈ M) (hAM' : A ∈ M')
    (hd : ∀ X, X ∈ L → X ∉ M) (hd' : ∀ X, X ∈ L → X ∉ M') : M = M' := by
  obtain ⟨a, b, c, hab, rfl⟩ := hL
  have hA' : a * A.1 + b * A.2 + c ≠ 0 := hA
  rw [parallel_eq hab hA' hM hAM (fun X hX => hd X hX),
    parallel_eq hab hA' hM' hAM' (fun X hX => hd' X hX)]

/-- Playfair's form: the parallel exists. -/
theorem parallel_exists (L : Set (Pt F)) (hL : IsLine L) (A : Pt F) (hA : A ∉ L) :
    ∃ M, IsLine M ∧ A ∈ M ∧ ∀ X, X ∈ L → X ∉ M := by
  obtain ⟨a, b, c, hab, rfl⟩ := hL
  refine ⟨parallelThrough a b A, isLine_parallelThrough hab A, self_mem_parallelThrough a b A, ?_⟩
  intro X hX hXM
  apply hA
  simp only [parallelThrough, Set.mem_ofPred_eq] at hX hXM ⊢
  linarith

/-! ### Group III: congruence of angles -/

/-- Same side of a line: neither point on it and no point of the line between them. -/
def SameSide (L : Set (Pt F)) (P Q : Pt F) : Prop := P ∉ L ∧ Q ∉ L ∧ ¬ ∃ X ∈ L, Btw P X Q

theorem no_cross_of_same_sign {a b c : F} {P Q X : Pt F} {t : F} (ht0 : 0 < t) (ht1 : t < 1)
    (h1 : X.1 = P.1 + t * (Q.1 - P.1)) (h2 : X.2 = P.2 + t * (Q.2 - P.2))
    (hX : a * X.1 + b * X.2 + c = 0) (hP : a * P.1 + b * P.2 + c ≠ 0)
    (hpos : 0 < (a * P.1 + b * P.2 + c) * (a * Q.1 + b * Q.2 + c)) : False := by
  have e := affine_along (a := a) (b := b) (c := c) h1 h2
  rw [hX] at e
  set φP := a * P.1 + b * P.2 + c
  set φQ := a * Q.1 + b * Q.2 + c
  have e2 : t * (φP * φQ) = -((1 - t) * φP ^ 2) := by linear_combination (-φP) * e
  have hA2 : 0 < φP ^ 2 := lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 hP))
  linarith [mul_pos ht0 hpos, mul_pos (sub_pos.2 ht1) hA2]

/-- Two points are on the same side of `{a x + b y + c = 0}` iff their affine values have
the same sign. -/
theorem sameSide_iff (a b c : F) (P Q : Pt F) :
    SameSide {p : Pt F | a * p.1 + b * p.2 + c = 0} P Q ↔
      0 < (a * P.1 + b * P.2 + c) * (a * Q.1 + b * Q.2 + c) := by
  constructor
  · rintro ⟨hP, hQ, hX⟩
    simp only [Set.mem_ofPred_eq] at hP hQ
    rcases lt_trichotomy 0 ((a * P.1 + b * P.2 + c) * (a * Q.1 + b * Q.2 + c)) with h | h | h
    · exact h
    · exact absurd (mul_eq_zero.1 h.symm) (by push_neg; exact ⟨hP, hQ⟩)
    · obtain ⟨X, hXL, hb⟩ := crossing hP h
      exact absurd ⟨X, hXL, hb⟩ hX
  · intro h
    have hP : a * P.1 + b * P.2 + c ≠ 0 := fun h0 => by
      rw [h0, zero_mul] at h; exact lt_irrefl _ h
    have hQ : a * Q.1 + b * Q.2 + c ≠ 0 := fun h0 => by
      rw [h0, mul_zero] at h; exact lt_irrefl _ h
    refine ⟨hP, hQ, ?_⟩
    rintro ⟨X, hXL, -, t, ht0, ht1, h1, h2⟩
    exact no_cross_of_same_sign ht0 ht1 h1 h2 hXL hP h

theorem lineThrough_eq_setOf (A B : Pt F) :
    lineThrough A B = {p : Pt F | (-(B.2 - A.2)) * p.1 + (B.1 - A.1) * p.2 +
      ((B.2 - A.2) * A.1 - (B.1 - A.1) * A.2) = 0} := by
  ext p
  simp only [lineThrough, cr, Set.mem_ofPred_eq, Prod.fst_sub, Prod.snd_sub]
  constructor <;> intro h <;> linarith

theorem sameSide_lineThrough_iff (A B P Q : Pt F) :
    SameSide (lineThrough A B) P Q ↔ 0 < cr (B - A) (P - A) * cr (B - A) (Q - A) := by
  rw [lineThrough_eq_setOf, sameSide_iff]
  have e1 : (-(B.2 - A.2)) * P.1 + (B.1 - A.1) * P.2 + ((B.2 - A.2) * A.1 - (B.1 - A.1) * A.2) =
      cr (B - A) (P - A) := by
    simp only [cr, Prod.fst_sub, Prod.snd_sub]; ring
  have e2 : (-(B.2 - A.2)) * Q.1 + (B.1 - A.1) * Q.2 + ((B.2 - A.2) * A.1 - (B.1 - A.1) * A.2) =
      cr (B - A) (Q - A) := by
    simp only [cr, Prod.fst_sub, Prod.snd_sub]; ring
  rw [e1, e2]

theorem eq_of_sq_eq_of_mul_nonneg {x y : F} (h : x ^ 2 = y ^ 2) (h2 : 0 ≤ x * y) : x = y := by
  have : (x - y) * (x + y) = 0 := by linear_combination h
  rcases mul_eq_zero.1 this with h3 | h3
  · linarith
  · have hy : y = -x := by linarith
    subst hy
    have hx : x = 0 := by nlinarith [sq_nonneg x]
    simp [hx]

theorem ne₁₂_of_not_col {A B C : Pt F} (h : ¬ Col A B C) : A ≠ B := by
  rintro rfl; apply h; rw [col_iff]; simp [cr]

theorem ne₁₃_of_not_col {A B C : Pt F} (h : ¬ Col A B C) : A ≠ C := by
  rintro rfl; apply h; rw [col_iff]; simp [cr]

theorem ne₂₃_of_not_col {A B C : Pt F} (h : ¬ Col A B C) : B ≠ C := by
  rintro rfl; apply h; rw [col_iff]; simp only [cr]; ring

theorem ip_self_pos {A B : Pt F} (h : A ≠ B) : 0 < ip (B - A) (B - A) := by
  rw [← q_eq_ip]; exact q_pos_of_ne h

/-- A vector parallel to `P - A` with positive inner product points along the ray. -/
theorem onRay_of_parallel {A P Q : Pt F} (hAP : A ≠ P) (hcr : cr (P - A) (Q - A) = 0)
    (hip : 0 < ip (P - A) (Q - A)) : OnRay A P Q := by
  have hU := ip_self_pos hAP
  refine ⟨ip (P - A) (Q - A) / ip (P - A) (P - A), div_pos hip hU, ?_, ?_⟩
  · have : Q.1 - A.1 = ip (P - A) (Q - A) * (P.1 - A.1) / ip (P - A) (P - A) := by
      rw [eq_div_iff hU.ne']
      simp only [ip, cr, Prod.fst_sub, Prod.snd_sub] at hcr ⊢
      linear_combination (-(P.2 - A.2)) * hcr
    rw [div_mul_eq_mul_div]; linarith
  · have : Q.2 - A.2 = ip (P - A) (Q - A) * (P.2 - A.2) / ip (P - A) (P - A) := by
      rw [eq_div_iff hU.ne']
      simp only [ip, cr, Prod.fst_sub, Prod.snd_sub] at hcr ⊢
      linear_combination (P.1 - A.1) * hcr
    rw [div_mul_eq_mul_div]; linarith

/-- **Laying off an angle** (Hilbert III.4): given a proper angle `∠BAC`, a ray `A'B''` and a
side of its line (marked by `D'`), there is a ray `A'C'` on that side with
`∠B''A'C' ≅ ∠BAC`, and it is unique. -/
theorem III4 (B A C B'' A' D' : Pt F) (h : ¬ Col A B C) (h' : ¬ Col A' B'' D') :
    ∃ C', ¬ Col A' B'' C' ∧ SameSide (lineThrough A' B'') C' D' ∧ AngCong B A C B'' A' C' ∧
      ∀ C'', ¬ Col A' B'' C'' → SameSide (lineThrough A' B'') C'' D' →
        AngCong B A C B'' A' C'' → OnRay A' C' C'' := by
  have hA'B := ne₁₂_of_not_col h'
  rw [col_iff] at h h'
  set i := ip (B - A) (C - A) with hi
  set k := cr (B - A) (C - A) with hk
  set φD := cr (B'' - A') (D' - A') with hφD
  have hk0 : k ≠ 0 := h
  have hφD0 : φD ≠ 0 := h'
  have hU := ip_self_pos hA'B
  set U := ip (B'' - A') (B'' - A') with hUdef
  have hL : q A B * q A C = i ^ 2 + k ^ 2 := by
    rw [q_eq_ip, q_eq_ip, ← lagrange]
  set σ : F := if 0 < k * φD then 1 else -1 with hσ
  have hσ2 : σ ^ 2 = 1 := by rw [hσ]; split_ifs <;> norm_num
  have hσk : 0 < σ * k * φD := by
    rw [hσ]; split_ifs with hc
    · simpa using hc
    · push_neg at hc
      have hne : k * φD ≠ 0 := mul_ne_zero hk0 hφD0
      have := lt_of_le_of_ne hc hne
      linarith
  -- the laid-off point
  set C' : Pt F := (A'.1 + (i * (B''.1 - A'.1) - σ * k * (B''.2 - A'.2)),
    A'.2 + (i * (B''.2 - A'.2) + σ * k * (B''.1 - A'.1))) with hC'
  have hv1 : C'.1 - A'.1 = i * (B''.1 - A'.1) - σ * k * (B''.2 - A'.2) := by rw [hC']; ring
  have hv2 : C'.2 - A'.2 = i * (B''.2 - A'.2) + σ * k * (B''.1 - A'.1) := by rw [hC']; ring
  have hcr' : cr (B'' - A') (C' - A') = σ * k * U := by
    rw [hUdef]; simp only [cr, ip, Prod.fst_sub, Prod.snd_sub, hv1, hv2]; ring
  have hip' : ip (B'' - A') (C' - A') = i * U := by
    rw [hUdef]; simp only [ip, Prod.fst_sub, Prod.snd_sub, hv1, hv2]; ring
  have hqC' : q A' C' = (i ^ 2 + σ ^ 2 * k ^ 2) * U := by
    rw [hUdef]; simp only [q, ip, Prod.fst_sub, Prod.snd_sub]
    rw [show A'.1 - C'.1 = -(C'.1 - A'.1) by ring, show A'.2 - C'.2 = -(C'.2 - A'.2) by ring,
      hv1, hv2]
    ring
  have hqB'' : q A' B'' = U := by rw [hUdef, q_eq_ip]
  have hA'C' : A' ≠ C' := by
    intro hc
    have : cr (B'' - A') (C' - A') = 0 := by rw [← hc]; simp [cr]
    rw [hcr'] at this
    exact absurd this (mul_ne_zero (mul_ne_zero (by rw [hσ]; split_ifs <;> norm_num) hk0) hU.ne')
  refine ⟨C', ?_, ?_, ⟨?_, ?_⟩, ?_⟩
  · rw [col_iff, hcr']
    exact mul_ne_zero (mul_ne_zero (by rw [hσ]; split_ifs <;> norm_num) hk0) hU.ne'
  · rw [sameSide_lineThrough_iff, hcr']
    have : σ * k * U * φD = (σ * k * φD) * U := by ring
    rw [this]; exact mul_pos hσk hU
  · rw [hqB'', hqC', hip', hL]
    linear_combination (i ^ 2 * U ^ 2 * k ^ 2) * hσ2
  · rw [hip']
    have : i * (i * U) = i ^ 2 * U := by ring
    rw [this]; positivity
  · intro C'' hcol hside hang
    rw [col_iff] at hcol
    rw [sameSide_lineThrough_iff] at hside
    obtain ⟨he, hs⟩ := hang
    rw [hqB'', hL] at he
    set I := ip (B'' - A') (C'' - A') with hI
    set K := cr (B'' - A') (C'' - A') with hK
    have hLag : I ^ 2 + K ^ 2 = U * q A' C'' := by
      rw [hUdef, q_eq_ip, hI, hK, lagrange]
    -- i² K² = I² k²
    have hsq : (i * K) ^ 2 = (σ * k * I) ^ 2 := by
      have e1 : i ^ 2 * (I ^ 2 + K ^ 2) = I ^ 2 * (i ^ 2 + k ^ 2) := by
        rw [hLag]; linear_combination he
      linear_combination e1 - (k ^ 2 * I ^ 2) * hσ2
    have hσkK : 0 < σ * k * K := by
      have hφ2 : 0 < φD ^ 2 := lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 hφD0))
      have hprod : 0 < (σ * k * K) * φD ^ 2 := by
        have e : (σ * k * K) * φD ^ 2 = (K * φD) * (σ * k * φD) := by ring
        rw [e]; exact mul_pos hside hσk
      exact pos_of_mul_pos_left hprod hφ2.le
    have hsign : 0 ≤ (i * K) * (σ * k * I) := by
      have : (i * K) * (σ * k * I) = (i * I) * (σ * k * K) := by ring
      rw [this]; exact mul_nonneg hs hσkK.le
    have hpar : i * K = σ * k * I := eq_of_sq_eq_of_mul_nonneg hsq hsign
    apply onRay_of_parallel hA'C'
    · have : cr (C' - A') (C'' - A') = i * K - σ * k * I := by
        simp only [cr, ip, Prod.fst_sub, Prod.snd_sub, hv1, hv2, hI, hK]; ring
      rw [this, hpar]; ring
    · have : ip (C' - A') (C'' - A') = i * I + σ * k * K := by
        simp only [ip, cr, Prod.fst_sub, Prod.snd_sub, hv1, hv2, hI, hK]; ring
      rw [this]
      have : 0 ≤ i * I := hs
      linarith

/-- Every angle is congruent to itself (part of Hilbert III.4). -/
theorem angCong_refl (B A C : Pt F) : AngCong B A C B A C := ⟨rfl, mul_self_nonneg _⟩

/-- **Side–angle–side** (Hilbert III.5). -/
theorem III5 (A B C A' B' C' : Pt F) (h : ¬ Col A B C) (h' : ¬ Col A' B' C')
    (h1 : Cong A B A' B') (h2 : Cong A C A' C') (h3 : AngCong B A C B' A' C') :
    AngCong A B C A' B' C' := by
  have hAB := ne₁₂_of_not_col h
  have hAC := ne₁₃_of_not_col h
  unfold Cong at h1 h2
  obtain ⟨he, hs⟩ := h3
  have hqq : q A B * q A C = q A' B' * q A' C' := by rw [h1, h2]
  have hpos : 0 < q A B * q A C := mul_pos (q_pos_of_ne hAB) (q_pos_of_ne hAC)
  have hi : ip (B - A) (C - A) = ip (B' - A') (C' - A') := by
    apply eq_of_sq_eq_of_mul_nonneg _ hs
    rw [← hqq] at he
    exact mul_right_cancel₀ hpos.ne' he
  have e1 : ip (A - B) (C - B) = q A B - ip (B - A) (C - A) := by
    simp only [ip, q, Prod.fst_sub, Prod.snd_sub]; ring
  have e1' : ip (A' - B') (C' - B') = q A' B' - ip (B' - A') (C' - A') := by
    simp only [ip, q, Prod.fst_sub, Prod.snd_sub]; ring
  have e3 : q B C = q A B + q A C - 2 * ip (B - A) (C - A) := by
    simp only [q, ip, Prod.fst_sub, Prod.snd_sub]; ring
  have e3' : q B' C' = q A' B' + q A' C' - 2 * ip (B' - A') (C' - A') := by
    simp only [q, ip, Prod.fst_sub, Prod.snd_sub]; ring
  unfold AngCong
  rw [e1, e1', q_comm B A, q_comm B' A', e3, e3', h1, h2, hi]
  exact ⟨rfl, mul_self_nonneg _⟩

/-- The ray from `A` through `C ≠ A`, in Hilbert's terms. -/
theorem onRay_iff {A C : Pt F} (hAC : A ≠ C) (P : Pt F) :
    OnRay A C P ↔ (P = C ∨ Btw A P C ∨ Btw A C P) := by
  constructor
  · rintro ⟨s, hs, h1, h2⟩
    rcases lt_trichotomy s 1 with hlt | heq | hgt
    · exact Or.inr (Or.inl ⟨hAC, s, hs, hlt, h1, h2⟩)
    · subst heq; left; ext <;> simp [h1, h2]
    · right; right
      have hAP : A ≠ P := by
        intro hAP
        rw [← hAP] at h1 h2
        apply hAC
        have hs0 : s ≠ 0 := hs.ne'
        ext
        · have : s * (C.1 - A.1) = 0 := by linarith
          have := (mul_eq_zero.1 this).resolve_left hs0; linarith
        · have : s * (C.2 - A.2) = 0 := by linarith
          have := (mul_eq_zero.1 this).resolve_left hs0; linarith
      refine ⟨hAP, 1 / s, by positivity, ?_, ?_, ?_⟩
      · rw [div_lt_one hs]; exact hgt
      · rw [h1]; field_simp; ring
      · rw [h2]; field_simp; ring
  · rintro (rfl | ⟨-, t, ht0, ht1, h1, h2⟩ | ⟨hAP, t, ht0, ht1, h1, h2⟩)
    · exact ⟨1, one_pos, by ring, by ring⟩
    · exact ⟨t, ht0, h1, h2⟩
    · refine ⟨1 / t, by positivity, ?_, ?_⟩
      · rw [h1]; field_simp; ring
      · rw [h2]; field_simp; ring

end Plane

/-! ## Hilbert's axioms for undefined things -/

/-- **Hilbert's plane**: three kinds of undefined things (points `P`, lines as sets of
points, and the relations *between*, *congruent* for segments and for angles) subject to
the axiom groups I (incidence), II (order), III (congruence) and IV (parallels) of the
*Grundlagen der Geometrie*, stated for a plane.  Collinearity, rays and sides are
expressed through the primitives exactly as Hilbert does. -/
structure HilbertPlane (P : Type*) where
  /-- The lines. -/
  Line : Set P → Prop
  /-- `Btw A B C`: `B` lies between `A` and `C`. -/
  Btw : P → P → P → Prop
  /-- `Cong A B C D`: the segment `AB` is congruent to `CD`. -/
  Cong : P → P → P → P → Prop
  /-- `AngCong B A C B' A' C'`: the angle `∠BAC` is congruent to `∠B'A'C'`. -/
  AngCong : P → P → P → P → P → P → Prop
  /-- I.1: two distinct points lie on a line. -/
  I1 : ∀ A B, A ≠ B → ∃ L, Line L ∧ A ∈ L ∧ B ∈ L
  /-- I.2: two distinct points lie on at most one line. -/
  I2 : ∀ A B L L', A ≠ B → Line L → Line L' → A ∈ L → B ∈ L → A ∈ L' → B ∈ L' → L = L'
  /-- I.3a: every line has two distinct points. -/
  I3a : ∀ L, Line L → ∃ A B, A ≠ B ∧ A ∈ L ∧ B ∈ L
  /-- I.3b: there are three points not on one line. -/
  I3b : ∃ A B C, ∀ L, Line L → ¬ (A ∈ L ∧ B ∈ L ∧ C ∈ L)
  /-- II.1: if `B` is between `A` and `C`, the three points are distinct and collinear, and
  `B` is between `C` and `A`. -/
  II1 : ∀ A B C, Btw A B C → A ≠ B ∧ B ≠ C ∧ A ≠ C ∧ Btw C B A ∧
    ∃ L, Line L ∧ A ∈ L ∧ B ∈ L ∧ C ∈ L
  /-- II.2: for `A ≠ C` there is `B` with `C` between `A` and `B`. -/
  II2 : ∀ A C, A ≠ C → ∃ B, Btw A C B
  /-- II.3: of three points at most one is between the other two. -/
  II3 : ∀ A B C, Btw A B C → ¬ Btw B A C ∧ ¬ Btw A C B
  /-- II.4 (Pasch): a line entering a triangle through one side leaves it through another. -/
  II4 : ∀ A B C L, Line L → (¬ ∃ M, Line M ∧ A ∈ M ∧ B ∈ M ∧ C ∈ M) →
    A ∉ L → B ∉ L → C ∉ L → (∃ X ∈ L, Btw A X B) →
    (∃ Y ∈ L, Btw A Y C) ∨ (∃ Y ∈ L, Btw B Y C)
  /-- III.1: a segment can be laid off on a given ray in exactly one way. -/
  III1 : ∀ A B A' B'', A ≠ B → A' ≠ B'' →
    ∃! B', (B' = B'' ∨ Btw A' B' B'' ∨ Btw A' B'' B') ∧ Cong A B A' B'
  /-- III.2: two segments congruent to a third are congruent. -/
  III2 : ∀ A B A' B' A'' B'', Cong A' B' A B → Cong A'' B'' A B → Cong A' B' A'' B''
  /-- III.2 (segments are unordered and congruent to themselves). -/
  III2' : ∀ A B, Cong A B B A ∧ Cong A B A B
  /-- III.3: addition of segments. -/
  III3 : ∀ A B C A' B' C', Btw A B C → Btw A' B' C' → Cong A B A' B' → Cong B C B' C' →
    Cong A C A' C'
  /-- III.4: an angle can be laid off on a given ray, on a given side of its line, in
  exactly one way. -/
  III4 : ∀ B A C B'' A' D', (¬ ∃ L, Line L ∧ A ∈ L ∧ B ∈ L ∧ C ∈ L) →
    (¬ ∃ L, Line L ∧ A' ∈ L ∧ B'' ∈ L ∧ D' ∈ L) →
    ∃ C', (¬ ∃ L, Line L ∧ A' ∈ L ∧ B'' ∈ L ∧ C' ∈ L) ∧
      (∀ L, Line L → A' ∈ L → B'' ∈ L → C' ∉ L ∧ D' ∉ L ∧ ¬ ∃ X ∈ L, Btw C' X D') ∧
      AngCong B A C B'' A' C' ∧
      ∀ C'', (¬ ∃ L, Line L ∧ A' ∈ L ∧ B'' ∈ L ∧ C'' ∈ L) →
        (∀ L, Line L → A' ∈ L → B'' ∈ L → C'' ∉ L ∧ D' ∉ L ∧ ¬ ∃ X ∈ L, Btw C'' X D') →
        AngCong B A C B'' A' C'' → (C'' = C' ∨ Btw A' C'' C' ∨ Btw A' C' C'')
  /-- III.4: every angle is congruent to itself. -/
  III4' : ∀ B A C, AngCong B A C B A C
  /-- III.5 (side–angle–side). -/
  III5 : ∀ A B C A' B' C', (¬ ∃ L, Line L ∧ A ∈ L ∧ B ∈ L ∧ C ∈ L) →
    (¬ ∃ L, Line L ∧ A' ∈ L ∧ B' ∈ L ∧ C' ∈ L) →
    Cong A B A' B' → Cong A C A' C' → AngCong B A C B' A' C' → AngCong A B C A' B' C'
  /-- IV (Euclid's axiom): through a point off a line there is at most one line not meeting
  it. -/
  IV : ∀ L A M M', Line L → A ∉ L → Line M → Line M' → A ∈ M → A ∈ M' →
    (∀ X, X ∈ L → X ∉ M) → (∀ X, X ∈ L → X ∉ M') → M = M'

section Model
variable {F : Type*} [Field F] [LinearOrder F] [IsStrictOrderedRing F]

theorem col_self_left (A C : Pt F) : Col A A C := by rw [col_iff]; simp [cr]

/-- **The Cartesian plane over a Pythagorean ordered field is a Hilbert plane**: it
satisfies the axiom groups I–IV. -/
noncomputable def cartesian (hP : Pythagorean F) : HilbertPlane (Pt F) where
  Line := IsLine
  Btw := Btw
  Cong := Cong
  AngCong := AngCong
  I1 := I1
  I2 := I2
  I3a := I3a
  I3b := I3b
  II1 := II1
  II2 := II2
  II3 := II3
  II4 := II4
  III1 := fun A B A' B'' hAB hA' => by
    obtain ⟨B', ⟨hray, hc⟩, huniq⟩ := III1 hP A B A' B'' hAB hA'
    exact ⟨B', ⟨(onRay_iff hA' B').1 hray, hc⟩,
      fun P hP' => huniq P ⟨(onRay_iff hA' P).2 hP'.1, hP'.2⟩⟩
  III2 := III2
  III2' := fun A B => ⟨cong_swap A B, cong_refl A B⟩
  III3 := III3
  III4 := fun B A C B'' A' D' h h' => by
    have hA'B : A' ≠ B'' := ne₁₂_of_not_col h'
    obtain ⟨C', hcol, hside, hang, huniq⟩ := III4 B A C B'' A' D' h h'
    have hA'C' : A' ≠ C' := ne₁₃_of_not_col hcol
    refine ⟨C', hcol, ?_, hang, ?_⟩
    · intro L hL hA hB
      rw [lineThrough_eq hL hA'B hA hB]
      exact hside
    · intro C'' hcol'' hside'' hang''
      have := huniq C'' hcol''
        (hside'' _ (isLine_lineThrough hA'B) (left_mem_lineThrough _ _)
          (right_mem_lineThrough _ _)) hang''
      exact (onRay_iff hA'C' C'').1 this
  III4' := angCong_refl
  III5 := III5
  IV := IV

end Model

/-! ## Continuity: Archimedes and Dedekind -/

namespace HilbertPlane
variable {P : Type*} (H : HilbertPlane P)

/-- **Hilbert's axiom V.1 (Archimedes).** Let `A₁` lie between `A` and `B`, and let
`A₂, A₃, …` continue the chain, each `A_{i+1}` lying between `A_i` and `A_{i+2}` with all
steps `A_iA_{i+1} ≅ A_{i+1}A_{i+2}` congruent. Then some `A_n` lies beyond `B`. -/
def Archimedes : Prop :=
  ∀ (A B : P) (S : ℕ → P), S 0 = A → H.Btw A (S 1) B →
    (∀ i, H.Btw (S i) (S (i + 1)) (S (i + 2))) →
    (∀ i, H.Cong (S i) (S (i + 1)) (S (i + 1)) (S (i + 2))) →
    ∃ n, H.Btw A B (S n)

/-- **Dedekind's axiom** for a line (over I–III it is equivalent to Hilbert's V.1 + V.2):
if the points of a line are split into two nonempty parts neither of which has a point
between two points of the other, some point `O` separates them. -/
def Dedekind : Prop :=
  ∀ L, H.Line L → ∀ S T : Set P, S ∪ T = L → Disjoint S T → S.Nonempty → T.Nonempty →
    (∀ P₁ ∈ S, ∀ P₂ ∈ S, ∀ Q ∈ T, ¬ H.Btw P₁ Q P₂) →
    (∀ Q₁ ∈ T, ∀ Q₂ ∈ T, ∀ P ∈ S, ¬ H.Btw Q₁ P Q₂) →
    ∃ O ∈ L, ∀ P ∈ S, ∀ Q ∈ T, P ≠ O → Q ≠ O → H.Btw P O Q

end HilbertPlane

section Continuity
variable {F : Type*} [Field F] [LinearOrder F] [IsStrictOrderedRing F]

/-- A congruent step beyond `Y` from `X` lands at `2Y - X`. -/
theorem chain_step {X Y Z : Pt F} (hb : Btw X Y Z) (hc : Cong X Y Y Z) :
    Z.1 = 2 * Y.1 - X.1 ∧ Z.2 = 2 * Y.2 - X.2 := by
  obtain ⟨hXZ, t, ht0, ht1, e1, e2⟩ := hb
  unfold Cong at hc
  rw [q_param e1 e2, q_param' e1 e2] at hc
  have Q := q_pos_of_ne hXZ
  have ht : t = 1 / 2 := by
    have : (t - (1 - t)) * q X Z = 0 := by linear_combination hc
    have := (mul_eq_zero.1 this).resolve_right Q.ne'
    linarith
  subst ht
  constructor
  · rw [e1]; ring
  · rw [e2]; ring

/-- A chain of congruent steps is an arithmetic progression. -/
theorem chain_eq {A D : Pt F} {S : ℕ → Pt F} (h0 : S 0 = A)
    (h1 : S 1 = (A.1 + D.1, A.2 + D.2))
    (hb : ∀ i, Btw (S i) (S (i + 1)) (S (i + 2)))
    (hc : ∀ i, Cong (S i) (S (i + 1)) (S (i + 1)) (S (i + 2))) (n : ℕ) :
    (S n).1 = A.1 + n * D.1 ∧ (S n).2 = A.2 + n * D.2 := by
  have key : ∀ n : ℕ, ((S n).1 = A.1 + n * D.1 ∧ (S n).2 = A.2 + n * D.2) ∧
      ((S (n + 1)).1 = A.1 + (n + 1 : ℕ) * D.1 ∧ (S (n + 1)).2 = A.2 + (n + 1 : ℕ) * D.2) := by
    intro n
    induction n with
    | zero => exact ⟨by simp [h0], by simp [h1]⟩
    | succ n ih =>
      refine ⟨ih.2, ?_⟩
      obtain ⟨e1, e2⟩ := chain_step (hb n) (hc n)
      rw [show n + 1 + 1 = n + 2 by ring, e1, e2, ih.1.1, ih.1.2, ih.2.1, ih.2.2]
      push_cast
      constructor <;> ring
  exact (key n).1

/-- **V.1 is the Archimedean property of the coordinate field.** -/
theorem archimedes_iff (hP : Pythagorean F) : (cartesian hP).Archimedes ↔ Archimedean F := by
  constructor
  · intro h
    rw [archimedean_iff_nat_lt]
    intro x
    by_cases hx : x ≤ 1
    · exact ⟨2, by push_cast; linarith⟩
    · push_neg at hx
      have hx0 : 0 < x := by linarith
      have hbtw : Btw ((0, 0) : Pt F) (((1 : ℕ) : F), 0) (x, 0) := by
        refine ⟨?_, 1 / x, by positivity, ?_, ?_, ?_⟩
        · intro h; have := congrArg Prod.fst h; simp only at this; linarith
        · rw [div_lt_one hx0]; exact hx
        · show ((1 : ℕ) : F) = 0 + 1 / x * (x - 0)
          rw [Nat.cast_one]; field_simp; ring
        · show (0 : F) = 0 + 1 / x * (0 - 0)
          ring
      have hcb : ∀ i : ℕ, Btw (((i : ℕ) : F), (0 : F)) (((i + 1 : ℕ) : F), 0)
          (((i + 2 : ℕ) : F), 0) := by
        intro i
        refine ⟨?_, 1 / 2, by norm_num, by norm_num, ?_, ?_⟩
        · intro h
          have := congrArg Prod.fst h
          simp only at this
          norm_cast at this
          omega
        · show ((i + 1 : ℕ) : F) = (i : F) + 1 / 2 * (((i + 2 : ℕ) : F) - (i : F))
          push_cast; ring
        · show (0 : F) = 0 + 1 / 2 * (0 - 0)
          ring
      have hcc : ∀ i : ℕ, Cong (((i : ℕ) : F), (0 : F)) (((i + 1 : ℕ) : F), 0)
          (((i + 1 : ℕ) : F), 0) (((i + 2 : ℕ) : F), 0) := by
        intro i; simp only [Cong, q]; push_cast; ring
      obtain ⟨n, hn⟩ := h (0, 0) (x, 0) (fun i => ((i : F), 0)) (by simp) hbtw hcb hcc
      change Btw _ _ _ at hn
      obtain ⟨-, t, ht0, ht1, e1, -⟩ := hn
      simp only [sub_zero, zero_add] at e1
      refine ⟨n, ?_⟩
      have hn0 : (0 : F) ≤ n := Nat.cast_nonneg n
      nlinarith
  · intro hF A B S h0 h1 hb hc
    change Btw A (S 1) B at h1
    change ∀ i, Btw (S i) (S (i + 1)) (S (i + 2)) at hb
    change ∀ i, Cong (S i) (S (i + 1)) (S (i + 1)) (S (i + 2)) at hc
    change ∃ n, Btw A B (S n)
    have hchain := chain_eq h0 (A := A) (D := ((S 1).1 - A.1, (S 1).2 - A.2))
      (by ext <;> simp) hb hc
    obtain ⟨hAB, t, ht0, ht1, e1, e2⟩ := h1
    obtain ⟨n, hn⟩ := exists_nat_gt (1 / t)
    have hnt : 1 < (n : F) * t := by rwa [div_lt_iff₀ ht0] at hn
    have hnt0 : 0 < (n : F) * t := by linarith
    have hn0 : (n : F) ≠ 0 := fun h => by rw [h, zero_mul] at hnt0; exact lt_irrefl _ hnt0
    have hS : (S n).1 = A.1 + n * t * (B.1 - A.1) ∧ (S n).2 = A.2 + n * t * (B.2 - A.2) := by
      obtain ⟨f1, f2⟩ := hchain n
      rw [f1, f2, e1, e2]; constructor <;> ring
    refine ⟨n, ?_, 1 / (n * t), by positivity, (div_lt_one hnt0).2 hnt, ?_, ?_⟩
    · intro hAS
      apply hAB
      have g1 := congrArg Prod.fst hAS
      have g2 := congrArg Prod.snd hAS
      rw [hS.1] at g1; rw [hS.2] at g2
      have k1 : (n : F) * t * (B.1 - A.1) = 0 := by linarith
      have k2 : (n : F) * t * (B.2 - A.2) = 0 := by linarith
      have := (mul_eq_zero.1 k1).resolve_left hnt0.ne'
      have := (mul_eq_zero.1 k2).resolve_left hnt0.ne'
      ext <;> linarith
    · rw [hS.1]; field_simp; ring
    · rw [hS.2]; field_simp; ring

/-! ### Euclid's first definition as a theorem -/

/-- A segment `AB` is *negligible* against `CD` when no standard multiple of it reaches
`CD`: `n · |AB| < |CD|` for every `n ∈ ℕ`. -/
def Negligible (A B C D : Pt F) : Prop := A ≠ B ∧ ∀ n : ℕ, (n : F) ^ 2 * q A B < q C D

/-- **Euclid's Definition 1, made precise.** "A point is that which has no part": there is
no nonzero segment negligible against another, i.e. every segment has a standard scale. -/
def NoPart (F : Type*) [Field F] [LinearOrder F] [IsStrictOrderedRing F] : Prop :=
  ∀ A B C D : Pt F, ¬ Negligible A B C D

/-- Euclid's Definition 1 is exactly the Archimedean property of the coordinate field. -/
theorem noPart_iff_archimedean : NoPart F ↔ Archimedean F := by
  constructor
  · intro h
    rw [archimedean_iff_nat_lt]
    intro x
    by_contra hx
    push_neg at hx
    have h0 : (0 : F) ≤ x := by simpa using hx 0
    apply h (0, 0) (1, 0) (0, 0) (x + 1, 0)
    refine ⟨by simp, fun n => ?_⟩
    have := hx n
    simp only [q]
    nlinarith
  · rintro hF A B C D ⟨hAB, hn⟩
    have hq := q_pos_of_ne hAB
    obtain ⟨n, hn'⟩ := exists_nat_gt (q C D / q A B)
    have h1 : q C D < n * q A B := by rwa [div_lt_iff₀ hq] at hn'
    have h2 := hn n
    rcases Nat.eq_zero_or_pos n with rfl | hpos
    · simp at h1; linarith [q_nonneg C D]
    · have h1le : (1 : F) ≤ n := by exact_mod_cast hpos
      nlinarith [mul_le_mul_of_nonneg_right h1le hq.le]

/-- Euclid's Definition 1 is Hilbert's axiom V.1, for Cartesian planes. -/
theorem noPart_iff_archimedes (hP : Pythagorean F) : NoPart F ↔ (cartesian hP).Archimedes := by
  rw [noPart_iff_archimedean, archimedes_iff]

/-! ### Dedekind's axiom and completeness of the coordinate field -/

/-- The point `A + s w`. -/
def par (A w : Pt F) (s : F) : Pt F := (A.1 + s * w.1, A.2 + s * w.2)

theorem par_injective {A w : Pt F} (hw : w ≠ (0, 0)) : Function.Injective (par A w) := by
  intro s₁ s₂ h
  have hw' : w.1 ≠ 0 ∨ w.2 ≠ 0 := by
    by_contra hc; push_neg at hc; exact hw (Prod.ext hc.1 hc.2)
  have h1 := congrArg Prod.fst h
  have h2 := congrArg Prod.snd h
  simp only [par] at h1 h2
  rcases hw' with hw1 | hw2
  · exact mul_right_cancel₀ hw1 (by linarith)
  · exact mul_right_cancel₀ hw2 (by linarith)

/-- Betweenness along a parametrised line is betweenness of the parameters. -/
theorem btw_par {A w : Pt F} (hw : w ≠ (0, 0)) (s₁ s s₂ : F) :
    Btw (par A w s₁) (par A w s) (par A w s₂) ↔ (s₁ < s ∧ s < s₂) ∨ (s₂ < s ∧ s < s₁) := by
  have hw' : w.1 ≠ 0 ∨ w.2 ≠ 0 := by
    by_contra hc; push_neg at hc; exact hw (Prod.ext hc.1 hc.2)
  constructor
  · rintro ⟨hne, t, ht0, ht1, e1, e2⟩
    simp only [par] at e1 e2
    have h12 : s₁ ≠ s₂ := fun h => hne (by rw [h])
    have hs : s = s₁ + t * (s₂ - s₁) := by
      rcases hw' with hw1 | hw2
      · have : (s - s₁ - t * (s₂ - s₁)) * w.1 = 0 := by linear_combination e1
        have := (mul_eq_zero.1 this).resolve_right hw1; linarith
      · have : (s - s₁ - t * (s₂ - s₁)) * w.2 = 0 := by linear_combination e2
        have := (mul_eq_zero.1 this).resolve_right hw2; linarith
    rcases lt_or_gt_of_ne h12 with h | h
    · left
      constructor <;> nlinarith [mul_pos ht0 (sub_pos.2 h), mul_pos (sub_pos.2 ht1) (sub_pos.2 h)]
    · right
      constructor <;> nlinarith [mul_pos ht0 (sub_pos.2 h), mul_pos (sub_pos.2 ht1) (sub_pos.2 h)]
  · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
    · have hd : s₂ - s₁ ≠ 0 := by intro h; linarith
      refine ⟨fun h => ?_, (s - s₁) / (s₂ - s₁), div_pos (by linarith) (by linarith),
        (div_lt_one (by linarith)).2 (by linarith), ?_, ?_⟩
      · have := par_injective hw h; linarith
      · simp only [par]; field_simp; ring
      · simp only [par]; field_simp; ring
    · have hd : s₂ - s₁ ≠ 0 := by intro h; linarith
      refine ⟨fun h => ?_, (s - s₁) / (s₂ - s₁), div_pos_of_neg_of_neg (by linarith) (by linarith),
        (div_lt_one_of_neg (by linarith)).2 (by linarith), ?_, ?_⟩
      · have := par_injective hw h; linarith
      · simp only [par]; field_simp; ring
      · simp only [par]; field_simp; ring

theorem mem_lineThrough_par {A B : Pt F} (hAB : A ≠ B) (p : Pt F) :
    p ∈ lineThrough A B ↔ ∃ s, p = par A (B.1 - A.1, B.2 - A.2) s := by
  rw [mem_lineThrough_iff hAB]
  constructor
  · rintro ⟨s, h1, h2⟩; exact ⟨s, Prod.ext h1 h2⟩
  · rintro ⟨s, rfl⟩; exact ⟨s, rfl, rfl⟩

/-- Two complementary convex subsets of a linearly ordered field are separated. -/
theorem separated_of_convex {S' T' : Set F} (hS : S'.Nonempty) (hT : T'.Nonempty)
    (hdisj : ∀ s ∈ S', s ∉ T')
    (hcS : ∀ s₁ ∈ S', ∀ s₂ ∈ S', ∀ t ∈ T', ¬ ((s₁ < t ∧ t < s₂) ∨ (s₂ < t ∧ t < s₁)))
    (hcT : ∀ t₁ ∈ T', ∀ t₂ ∈ T', ∀ s ∈ S', ¬ ((t₁ < s ∧ s < t₂) ∨ (t₂ < s ∧ s < t₁))) :
    (∀ s ∈ S', ∀ t ∈ T', s < t) ∨ (∀ s ∈ S', ∀ t ∈ T', t < s) := by
  obtain ⟨s₀, hs₀⟩ := hS
  obtain ⟨t₀, ht₀⟩ := hT
  have hne : s₀ ≠ t₀ := fun h => hdisj s₀ hs₀ (h ▸ ht₀)
  rcases lt_or_gt_of_ne hne with h | h
  · left
    intro s hs t ht
    by_contra hc; push_neg at hc
    have hts : t < s := lt_of_le_of_ne hc (fun e => hdisj s hs (e ▸ ht))
    rcases lt_trichotomy t₀ s with h1 | h1 | h1
    · exact hcS s₀ hs₀ s hs t₀ ht₀ (Or.inl ⟨h, h1⟩)
    · exact hdisj s hs (h1 ▸ ht₀)
    · exact hcT t ht t₀ ht₀ s hs (Or.inl ⟨hts, h1⟩)
  · right
    intro s hs t ht
    by_contra hc; push_neg at hc
    have hst : s < t := lt_of_le_of_ne hc (fun e => hdisj s hs (e ▸ ht))
    rcases lt_trichotomy s t₀ with h1 | h1 | h1
    · exact hcS s hs s₀ hs₀ t₀ ht₀ (Or.inl ⟨h1, h⟩)
    · exact hdisj s hs (h1 ▸ ht₀)
    · exact hcT t₀ ht₀ t ht s hs (Or.inl ⟨h1, hst⟩)

/-- Completeness of the field gives Dedekind's axiom for the Cartesian plane. -/
theorem dedekind_of_complete (hP : Pythagorean F)
    (hc : ∀ X : Set F, X.Nonempty → BddAbove X → ∃ x, IsLUB X x) : (cartesian hP).Dedekind := by
  intro L hL S T hST hdisj hS hT hcS hcT
  change IsLine L at hL
  change ∀ P₁ ∈ S, ∀ P₂ ∈ S, ∀ Q ∈ T, ¬ Btw P₁ Q P₂ at hcS
  change ∀ Q₁ ∈ T, ∀ Q₂ ∈ T, ∀ P ∈ S, ¬ Btw Q₁ P Q₂ at hcT
  change ∃ O ∈ L, ∀ P ∈ S, ∀ Q ∈ T, P ≠ O → Q ≠ O → Btw P O Q
  obtain ⟨A, B, hAB, hA, hB⟩ := I3a L hL
  have hLeq : L = lineThrough A B := lineThrough_eq hL hAB hA hB
  set w : Pt F := (B.1 - A.1, B.2 - A.2) with hw
  have hw0 : w ≠ (0, 0) := by
    intro h
    apply hAB
    have h1 := congrArg Prod.fst h
    have h2 := congrArg Prod.snd h
    simp only [hw] at h1 h2
    exact Prod.ext (by linarith) (by linarith)
  have hmem : ∀ p, p ∈ L ↔ ∃ s, p = par A w s := by
    intro p; rw [hLeq, mem_lineThrough_par hAB]
  have hSL : S ⊆ L := hST ▸ Set.subset_union_left
  have hTL : T ⊆ L := hST ▸ Set.subset_union_right
  set S' : Set F := {s | par A w s ∈ S} with hS'
  set T' : Set F := {s | par A w s ∈ T} with hT'
  have hS'ne : S'.Nonempty := by
    obtain ⟨p, hp⟩ := hS
    obtain ⟨s, rfl⟩ := (hmem p).1 (hSL hp)
    exact ⟨s, hp⟩
  have hT'ne : T'.Nonempty := by
    obtain ⟨p, hp⟩ := hT
    obtain ⟨s, rfl⟩ := (hmem p).1 (hTL hp)
    exact ⟨s, hp⟩
  have hdisj' : ∀ s ∈ S', s ∉ T' := fun s hs ht => Set.disjoint_left.1 hdisj hs ht
  have hcS' : ∀ s₁ ∈ S', ∀ s₂ ∈ S', ∀ t ∈ T', ¬ ((s₁ < t ∧ t < s₂) ∨ (s₂ < t ∧ t < s₁)) :=
    fun s₁ hs₁ s₂ hs₂ t ht hlt => hcS _ hs₁ _ hs₂ _ ht ((btw_par hw0 s₁ t s₂).2 hlt)
  have hcT' : ∀ t₁ ∈ T', ∀ t₂ ∈ T', ∀ s ∈ S', ¬ ((t₁ < s ∧ s < t₂) ∨ (t₂ < s ∧ s < t₁)) :=
    fun t₁ ht₁ t₂ ht₂ s hs hlt => hcT _ ht₁ _ ht₂ _ hs ((btw_par hw0 t₁ s t₂).2 hlt)
  rcases separated_of_convex hS'ne hT'ne hdisj' hcS' hcT' with hlt | hgt
  · obtain ⟨t₀, ht₀⟩ := hT'ne
    obtain ⟨σ, hσ⟩ := hc S' hS'ne ⟨t₀, fun s hs => (hlt s hs t₀ ht₀).le⟩
    refine ⟨par A w σ, (hmem _).2 ⟨σ, rfl⟩, ?_⟩
    intro P hP Q hQ hPO hQO
    obtain ⟨s, rfl⟩ := (hmem P).1 (hSL hP)
    obtain ⟨t, rfl⟩ := (hmem Q).1 (hTL hQ)
    have hs : s ∈ S' := hP
    have ht : t ∈ T' := hQ
    have hsσ : s < σ := lt_of_le_of_ne (hσ.1 hs) (fun h => hPO (by rw [h]))
    have hσt : σ < t :=
      lt_of_le_of_ne (hσ.2 (fun s hs => (hlt s hs t ht).le)) (fun h => hQO (by rw [h]))
    exact (btw_par hw0 s σ t).2 (Or.inl ⟨hsσ, hσt⟩)
  · obtain ⟨s₀, hs₀⟩ := hS'ne
    obtain ⟨τ, hτ⟩ := hc T' hT'ne ⟨s₀, fun t ht => (hgt s₀ hs₀ t ht).le⟩
    refine ⟨par A w τ, (hmem _).2 ⟨τ, rfl⟩, ?_⟩
    intro P hP Q hQ hPO hQO
    obtain ⟨s, rfl⟩ := (hmem P).1 (hSL hP)
    obtain ⟨t, rfl⟩ := (hmem Q).1 (hTL hQ)
    have hs : s ∈ S' := hP
    have ht : t ∈ T' := hQ
    have htτ : t < τ := lt_of_le_of_ne (hτ.1 ht) (fun h => hQO (by rw [h]))
    have hτs : τ < s :=
      lt_of_le_of_ne (hτ.2 (fun t ht => (hgt s hs t ht).le)) (fun h => hPO (by rw [h]))
    exact (btw_par hw0 s τ t).2 (Or.inr ⟨htτ, hτs⟩)

/-- The `x`-axis. -/
def xAxis : Set (Pt F) := {p | p.2 = 0}

theorem isLine_xAxis : IsLine (xAxis (F := F)) :=
  ⟨0, 1, 0, Or.inr one_ne_zero, by ext p; simp [xAxis]⟩

/-- The lower part of the `x`-axis cut by `X`. -/
def dedS (X : Set F) : Set (Pt F) := {p | p.2 = 0 ∧ ∃ x ∈ X, p.1 ≤ x}

/-- The upper part of the `x`-axis cut by `X`. -/
def dedT (X : Set F) : Set (Pt F) := {p | p.2 = 0 ∧ ∀ x ∈ X, x < p.1}

theorem mem_dedS {X : Set F} {p : Pt F} : p ∈ dedS X ↔ p.2 = 0 ∧ ∃ x ∈ X, p.1 ≤ x := Iff.rfl

theorem mem_dedT {X : Set F} {p : Pt F} : p ∈ dedT X ↔ p.2 = 0 ∧ ∀ x ∈ X, x < p.1 := Iff.rfl

/-- Dedekind's axiom for the Cartesian plane gives completeness of the field. -/
theorem complete_of_dedekind (hP : Pythagorean F) (hd : (cartesian hP).Dedekind) :
    ∀ X : Set F, X.Nonempty → BddAbove X → ∃ x, IsLUB X x := by
  rintro X ⟨x₀, hx₀⟩ ⟨b, hb⟩
  have hbX : ∀ x ∈ X, x ≤ b := fun x hx => hb hx
  have hd' := hd xAxis isLine_xAxis (dedS X) (dedT X)
  change (dedS X ∪ dedT X = xAxis) → Disjoint (dedS X) (dedT X) → (dedS X).Nonempty →
    (dedT X).Nonempty →
    (∀ P₁ ∈ dedS X, ∀ P₂ ∈ dedS X, ∀ Q ∈ dedT X, ¬ Btw P₁ Q P₂) →
    (∀ Q₁ ∈ dedT X, ∀ Q₂ ∈ dedT X, ∀ P ∈ dedS X, ¬ Btw Q₁ P Q₂) →
    ∃ O ∈ xAxis, ∀ P ∈ dedS X, ∀ Q ∈ dedT X, P ≠ O → Q ≠ O → Btw P O Q at hd'
  have hunion : dedS X ∪ dedT X = xAxis := by
    ext p
    simp only [Set.mem_union, mem_dedS, mem_dedT, xAxis, Set.mem_ofPred_eq]
    constructor
    · rintro (⟨h, -⟩ | ⟨h, -⟩) <;> exact h
    · intro h
      by_cases hx : ∃ x ∈ X, p.1 ≤ x
      · exact Or.inl ⟨h, hx⟩
      · push_neg at hx; exact Or.inr ⟨h, hx⟩
  have hdisj : Disjoint (dedS X) (dedT X) := by
    rw [Set.disjoint_left]
    rintro p ⟨-, x, hx, hpx⟩ ⟨-, hT⟩
    exact absurd hpx (not_le.2 (hT x hx))
  have hSne : (dedS X).Nonempty := ⟨(x₀, 0), rfl, x₀, hx₀, le_rfl⟩
  have hTne : (dedT X).Nonempty :=
    ⟨(b + 1, 0), rfl, fun y hy => by show y < b + 1; linarith [hbX y hy]⟩
  have hcS : ∀ P₁ ∈ dedS X, ∀ P₂ ∈ dedS X, ∀ Q ∈ dedT X, ¬ Btw P₁ Q P₂ := by
    rintro P₁ ⟨-, x₁, hx₁, hP₁⟩ P₂ ⟨-, x₂, hx₂, hP₂⟩ Q ⟨-, hQT⟩ ⟨-, t, ht0, ht1, e1, -⟩
    have h1 := hQT x₁ hx₁
    have h2 := hQT x₂ hx₂
    nlinarith [mul_pos (sub_pos.2 ht1) (sub_pos.2 (lt_of_le_of_lt hP₁ h1)),
      mul_pos ht0 (sub_pos.2 (lt_of_le_of_lt hP₂ h2))]
  have hcT : ∀ Q₁ ∈ dedT X, ∀ Q₂ ∈ dedT X, ∀ P ∈ dedS X, ¬ Btw Q₁ P Q₂ := by
    rintro Q₁ ⟨-, hQ₁⟩ Q₂ ⟨-, hQ₂⟩ P ⟨-, x, hx, hPx⟩ ⟨-, t, ht0, ht1, e1, -⟩
    have h1 := hQ₁ x hx
    have h2 := hQ₂ x hx
    nlinarith [mul_pos (sub_pos.2 ht1) (sub_pos.2 (lt_of_le_of_lt hPx h1)),
      mul_pos ht0 (sub_pos.2 (lt_of_le_of_lt hPx h2))]
  obtain ⟨O, -, hO⟩ := hd' hunion hdisj hSne hTne hcS hcT
  refine ⟨O.1, fun x hx => ?_, fun b' hb' => ?_⟩
  · by_contra hc; push_neg at hc
    have hPS : ((x, 0) : Pt F) ∈ dedS X := ⟨rfl, x, hx, le_rfl⟩
    have hPO : ((x, 0) : Pt F) ≠ O := fun h => by
      rw [← h] at hc; exact lt_irrefl _ hc
    obtain ⟨Q, hQT, hQO, hQ1⟩ : ∃ Q ∈ dedT X, Q ≠ O ∧ x < Q.1 := by
      by_cases h1 : ((b + 1, 0) : Pt F) = O
      · refine ⟨(b + 2, 0), ⟨rfl, fun y hy => by show y < b + 2; linarith [hbX y hy]⟩, ?_,
          by show x < b + 2; linarith [hbX x hx]⟩
        intro h2
        rw [← h1] at h2
        have := congrArg Prod.fst h2
        dsimp only at this
        linarith
      · exact ⟨(b + 1, 0), ⟨rfl, fun y hy => by show y < b + 1; linarith [hbX y hy]⟩, h1,
          by show x < b + 1; linarith [hbX x hx]⟩
    obtain ⟨-, t, ht0, ht1, e1, -⟩ := hO _ hPS Q hQT hPO hQO
    dsimp only at e1
    nlinarith [mul_pos ht0 (sub_pos.2 hQ1)]
  · by_contra hc; push_neg at hc
    have hQT : (((b' + O.1) / 2, 0) : Pt F) ∈ dedT X :=
      ⟨rfl, fun y hy => by have := hb' hy; show y < (b' + O.1) / 2; linarith⟩
    have hQO : (((b' + O.1) / 2, 0) : Pt F) ≠ O := fun h => by
      have := congrArg Prod.fst h; dsimp only at this; linarith
    obtain ⟨P, hPS, hPO, hP1⟩ : ∃ P ∈ dedS X, P ≠ O ∧ P.1 < (b' + O.1) / 2 := by
      have hx₀b := hb' hx₀
      by_cases h1 : ((x₀ - 1, 0) : Pt F) = O
      · refine ⟨(x₀ - 2, 0), ⟨rfl, x₀, hx₀, by show x₀ - 2 ≤ x₀; linarith⟩, ?_,
          by show x₀ - 2 < (b' + O.1) / 2; linarith⟩
        intro h2
        rw [← h1] at h2
        have := congrArg Prod.fst h2
        dsimp only at this
        linarith
      · exact ⟨(x₀ - 1, 0), ⟨rfl, x₀, hx₀, by show x₀ - 1 ≤ x₀; linarith⟩, h1,
          by show x₀ - 1 < (b' + O.1) / 2; linarith⟩
    obtain ⟨-, t, ht0, ht1, e1, -⟩ := hO P hPS _ hQT hPO hQO
    dsimp only at e1
    nlinarith [mul_pos (sub_pos.2 ht1) (sub_pos.2 hP1)]

/-- **Dedekind's axiom is completeness of the coordinate field.** -/
theorem dedekind_iff (hP : Pythagorean F) :
    (cartesian hP).Dedekind ↔ ∀ X : Set F, X.Nonempty → BddAbove X → ∃ x, IsLUB X x :=
  ⟨complete_of_dedekind hP, dedekind_of_complete hP⟩

/-- A linearly ordered field in which every nonempty bounded set has a least upper bound is a
conditionally complete linear order. -/
noncomputable def ccloOfLUB (hc : ∀ X : Set F, X.Nonempty → BddAbove X → ∃ x, IsLUB X x) :
    ConditionallyCompleteLinearOrder F := by
  classical
  letI : SupSet F :=
    ⟨fun X => if h : X.Nonempty ∧ BddAbove X then Classical.choose (hc X h.1 h.2) else 0⟩
  have hsup : ∀ X : Set F, BddAbove X → X.Nonempty → IsLUB X (sSup X) := fun X hb hn => by
    show IsLUB X (if h : X.Nonempty ∧ BddAbove X then Classical.choose (hc X h.1 h.2) else 0)
    rw [dif_pos ⟨hn, hb⟩]
    exact Classical.choose_spec (hc X hn hb)
  exact { conditionallyCompleteLatticeOfLatticeOfsSup F hsup, (inferInstance : LinearOrder F) with
    csSup_of_not_bddAbove := fun X hX => by
      show (if h : X.Nonempty ∧ BddAbove X then Classical.choose (hc X h.1 h.2) else 0) =
        (if h : (∅ : Set F).Nonempty ∧ BddAbove (∅ : Set F) then Classical.choose (hc ∅ h.1 h.2)
          else 0)
      rw [dif_neg (fun h => hX h.2), dif_neg (fun h => Set.not_nonempty_empty h.1)]
    csInf_of_not_bddBelow := fun X hX => by
      show (if h : (lowerBounds X).Nonempty ∧ BddAbove (lowerBounds X) then
          Classical.choose (hc _ h.1 h.2) else 0) =
        (if h : (lowerBounds (∅ : Set F)).Nonempty ∧ BddAbove (lowerBounds (∅ : Set F)) then
          Classical.choose (hc _ h.1 h.2) else 0)
      rw [dif_neg (fun h => hX h.1), dif_neg (fun h => ?_)]
      have h2 := h.2
      rw [lowerBounds_empty] at h2
      exact not_bddAbove_univ h2 }

/-- **Hilbert's completeness, Cartesian form.** A Cartesian plane satisfying Dedekind's axiom
(equivalently V.1 and V.2) has coordinate field isomorphic to `ℝ`: the Euclidean plane is
`ℝ²`, and nothing else. -/
theorem dedekind_real (hP : Pythagorean F) (hd : (cartesian hP).Dedekind) :
    Nonempty (F ≃+*o ℝ) := by
  letI i := ccloOfLUB (complete_of_dedekind hP hd)
  exact ⟨@ConditionallyCompleteLinearOrderedField.inducedOrderRingIso F ℝ _ i
    ‹IsStrictOrderedRing F› _ _ _⟩

/-- An Archimedean Cartesian plane embeds in `ℝ²`: the coordinate field embeds in `ℝ` as an
ordered field. -/
theorem archimedean_embeds [Archimedean F] : ∃ ι : F →+*o ℝ, Function.Injective ι :=
  ⟨ConditionallyCompleteLinearOrderedField.inducedOrderRingHom F ℝ,
    (ConditionallyCompleteLinearOrderedField.inducedOrderRingHom F ℝ : F →+* ℝ).injective⟩

/-- **`ℝ` is maximal among Archimedean ordered fields** (Hilbert's completeness axiom V.2 as
a theorem about `ℝ²`): an ordered-field embedding of `ℝ` into an Archimedean field is onto. -/
theorem real_maximal {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    [Archimedean K] (ι : ℝ →+*o K) : Function.Surjective ι := by
  let j : K →+*o ℝ := ConditionallyCompleteLinearOrderedField.inducedOrderRingHom K ℝ
  have hj : Function.Injective j := (j : K →+* ℝ).injective
  letI := ConditionallyCompleteLinearOrderedField.uniqueOrderRingHom ℝ ℝ
  have huniq : j.comp ι = OrderRingHom.id ℝ := Subsingleton.elim _ _
  intro x
  refine ⟨j x, hj ?_⟩
  change (j.comp ι) (j x) = j x
  rw [huniq, OrderRingHom.id_apply]

/-- The ultrapower of `F` along an ultrafilter extending the order filter. -/
abbrev Ext (F : Type*) [Field F] [LinearOrder F] [IsStrictOrderedRing F] : Type _ :=
  Filter.Germ (↑(Ultrafilter.of (Filter.atTop : Filter F)) : Filter F) F

/-- **Every ordered field has a proper ordered-field extension**: without Archimedes, an
axiom of completeness (maximality) cannot be satisfied. The extension `Ext F` is an ordered
field containing `F` through the constant embedding, and it has an element above all of
`F`. -/
theorem exists_proper_extension : ∃ ω : Ext F, ∀ x : F, (↑x : Ext F) < ω := by
  haveI : (Filter.atTop : Filter F).NeBot := Filter.atTop_neBot
  refine ⟨(↑(fun y : F => y) : Ext F), fun x => ?_⟩
  change (↑(fun _ : F => x) : Ext F) < ↑(fun y : F => y)
  rw [Filter.Germ.coe_lt]
  exact (Filter.eventually_gt_atTop x).filter_mono (Ultrafilter.of_le _)

theorem ext_isStrictOrderedRing : IsStrictOrderedRing (Ext F) := inferInstance

end Continuity

/-! ## The granular plane -/

section Hyper
open Hyperreal QE.NSA Filter

theorem hyperreal_sqrt (x : ℝ*) (hx : 0 ≤ x) : ∃ z : ℝ*, z ^ 2 = x := by
  obtain ⟨f, rfl⟩ := ofSeq_surjective x
  refine ⟨ofSeq (fun n => Real.sqrt (f n)), ?_⟩
  have h : ∀ᶠ n in (hyperfilter ℕ : Filter ℕ), 0 ≤ f n :=
    ofSeq_le_ofSeq.1 (show ofSeq (fun _ => (0 : ℝ)) ≤ ofSeq f from hx)
  have e : ofSeq (fun n => Real.sqrt (f n)) * ofSeq (fun n => Real.sqrt (f n)) =
      ofSeq (fun n => Real.sqrt (f n) * Real.sqrt (f n)) := rfl
  rw [sq, e]
  exact Filter.Germ.coe_eq.mpr (h.mono fun n hn => by
    show Real.sqrt (f n) * Real.sqrt (f n) = f n
    rw [← sq, Real.sq_sqrt hn])

/-- The hyperreals form a Pythagorean field. -/
theorem hyperreal_pythagorean : Pythagorean ℝ* := fun x y =>
  hyperreal_sqrt (x ^ 2 + y ^ 2) (by positivity)

theorem real_pythagorean : Pythagorean ℝ := fun x y =>
  ⟨Real.sqrt (x ^ 2 + y ^ 2), Real.sq_sqrt (by positivity)⟩

/-- **The granular plane is a Hilbert plane**: the centres `ℝ* × ℝ*` satisfy I–IV. -/
noncomputable def granularPlane : HilbertPlane (Pt ℝ*) := cartesian hyperreal_pythagorean

/-- The Euclidean plane `ℝ²`. -/
noncomputable def euclideanPlane : HilbertPlane (Pt ℝ) := cartesian real_pythagorean

theorem euclidean_archimedes : euclideanPlane.Archimedes :=
  (archimedes_iff _).2 inferInstance

/-- **V.1 fails in the granular plane.** -/
theorem granular_not_archimedes : ¬ granularPlane.Archimedes := fun h =>
  not_archimedean ((archimedes_iff _).1 h)

theorem euclidean_dedekind : euclideanPlane.Dedekind :=
  dedekind_of_complete _ (fun X hn hb => ⟨sSup X, isLUB_csSup hn hb⟩)

/-- **Dedekind's axiom fails in the granular plane.** -/
theorem granular_not_dedekind : ¬ granularPlane.Dedekind := by
  intro h
  have hs : IsStrictOrderedRing ℝ* := inferInstance
  letI i := ccloOfLUB (complete_of_dedekind _ h)
  exact not_archimedean (@ConditionallyCompleteLinearOrderedField.to_archimedean ℝ* _ i hs)

/-- **The granule is a negligible segment**: no standard multiple of the segment from a
centre to a neighbouring pole of its point reaches the unit segment. This is the precise
sense in which a granular point has a part. -/
theorem granule_negligible :
    Negligible ((0 : ℝ*), (0 : ℝ*)) (Hyperreal.epsilon, 0) (0, 0) (1, 0) := by
  refine ⟨?_, fun n => ?_⟩
  · intro h
    have := congrArg Prod.fst h
    simp only at this
    exact Hyperreal.epsilon_ne_zero this.symm
  · have e1 : q ((0 : ℝ*), (0 : ℝ*)) (Hyperreal.epsilon, 0) = Hyperreal.epsilon ^ 2 := by
      simp [q]
    have e2 : q ((0 : ℝ*), (0 : ℝ*)) (1, 0) = 1 := by simp [q]
    rw [e1, e2]
    have h := QE.Hyper.nat_mul_epsilon_lt_one n
    have h0 : 0 ≤ (n : ℝ*) * Hyperreal.epsilon := by
      have := Hyperreal.epsilon_pos.le; positivity
    calc (n : ℝ*) ^ 2 * Hyperreal.epsilon ^ 2 = ((n : ℝ*) * Hyperreal.epsilon) ^ 2 := by ring
      _ < 1 := by nlinarith

theorem noPart_real : NoPart ℝ := noPart_iff_archimedean.2 inferInstance

/-- **Euclid's Definition 1 fails in the granular plane**: a point has a part. -/
theorem not_noPart_hyperreal : ¬ NoPart ℝ* := fun h => h _ _ _ _ granule_negligible

/-- Hypernatural numbers: germs of sequences of natural numbers. -/
def IsHypernat (N : ℝ*) : Prop := ∃ f : ℕ → ℕ, N = ofSeq (fun n => (f n : ℝ))

/-- **Internal Archimedes.** With hypernatural multiples, the Archimedean property holds in
`ℝ*`, by transfer: V.1 is true *internally* in the granular plane and false externally. -/
theorem internal_archimedes (x y : ℝ*) (hx : 0 < x) : ∃ N : ℝ*, IsHypernat N ∧ y < N * x := by
  obtain ⟨f, rfl⟩ := ofSeq_surjective x
  obtain ⟨g, rfl⟩ := ofSeq_surjective y
  refine ⟨ofSeq (fun n => ((⌈|g n| / |f n|⌉₊ + 1 : ℕ) : ℝ)),
    ⟨fun n => ⌈|g n| / |f n|⌉₊ + 1, rfl⟩, ?_⟩
  have hpos : ∀ᶠ n in (hyperfilter ℕ : Filter ℕ), 0 < f n :=
    ofSeq_lt_ofSeq.1 (show ofSeq (fun _ => (0 : ℝ)) < ofSeq f from hx)
  change ofSeq g < ofSeq (fun n => ((⌈|g n| / |f n|⌉₊ + 1 : ℕ) : ℝ) * f n)
  rw [ofSeq_lt_ofSeq]
  refine hpos.mono fun n hn => ?_
  set c := ⌈|g n| / |f n|⌉₊ with hc
  have h1 : |g n| / |f n| ≤ c := Nat.le_ceil _
  rw [abs_of_pos hn] at h1
  have h2 : |g n| ≤ c * f n := by rwa [div_le_iff₀ hn] at h1
  push_cast
  calc g n ≤ |g n| := le_abs_self _
    _ ≤ c * f n := h2
    _ < (c + 1) * f n := by nlinarith

/-! ### The shadow map -/

/-- The shadow (standard part) of a point of the granular plane. -/
noncomputable def sh (p : Pt ℝ*) : Pt ℝ :=
  (ArchimedeanClass.stdPart p.1, ArchimedeanClass.stdPart p.2)

/-- Points with finite coordinates. -/
def IsFinitePt (p : Pt ℝ*) : Prop := IsFinite p.1 ∧ IsFinite p.2

theorem sh_coe (r : Pt ℝ) : sh ((r.1 : ℝ*), (r.2 : ℝ*)) = r := by
  simp [sh, Hyperreal.stdPart_coe]

/-- The shadow map is onto: every classical point is the shadow of a granular point. -/
theorem sh_surjective : Function.Surjective sh := fun r =>
  ⟨((r.1 : ℝ*), (r.2 : ℝ*)), sh_coe r⟩

theorem isFinitePt_coe (r : Pt ℝ) : IsFinitePt ((r.1 : ℝ*), (r.2 : ℝ*)) :=
  ⟨coe_isFinite r.1, coe_isFinite r.2⟩

/-- Two finite points have the same shadow iff they are infinitely close. -/
theorem sh_eq_iff {p p' : Pt ℝ*} (hp : IsFinitePt p) (hp' : IsFinitePt p') :
    sh p = sh p' ↔ IsInfinitesimal (p.1 - p'.1) ∧ IsInfinitesimal (p.2 - p'.2) := by
  constructor
  · intro h
    have h1 := congrArg Prod.fst h
    have h2 := congrArg Prod.snd h
    simp only [sh] at h1 h2
    constructor
    · have a := isInfinitesimal_sub_stdPart hp.1
      have b := isInfinitesimal_sub_stdPart hp'.1
      rw [h1] at a
      have e : p.1 - p'.1 = (p.1 - (ArchimedeanClass.stdPart p'.1 : ℝ*)) -
          (p'.1 - (ArchimedeanClass.stdPart p'.1 : ℝ*)) := by ring
      rw [e]; exact a.sub b
    · have a := isInfinitesimal_sub_stdPart hp.2
      have b := isInfinitesimal_sub_stdPart hp'.2
      rw [h2] at a
      have e : p.2 - p'.2 = (p.2 - (ArchimedeanClass.stdPart p'.2 : ℝ*)) -
          (p'.2 - (ArchimedeanClass.stdPart p'.2 : ℝ*)) := by ring
      rw [e]; exact a.sub b
  · rintro ⟨h1, h2⟩
    simp only [sh]
    exact Prod.ext (stdPart_eq_of_sub_infinitesimal h1) (stdPart_eq_of_sub_infinitesimal h2)

/-- The whole granular point `ball(c, ε)` has the shadow of its centre. -/
theorem sh_eq_of_mem_ball {c p : Pt ℝ*} (h1 : |p.1 - c.1| ≤ Hyperreal.epsilon)
    (h2 : |p.2 - c.2| ≤ Hyperreal.epsilon) : sh p = sh c := by
  have hε : |Hyperreal.epsilon| = Hyperreal.epsilon := abs_of_pos Hyperreal.epsilon_pos
  have e1 : IsInfinitesimal (p.1 - c.1) := epsilon_isInfinitesimal.of_abs_le (by rwa [hε])
  have e2 : IsInfinitesimal (p.2 - c.2) := epsilon_isInfinitesimal.of_abs_le (by rwa [hε])
  simp only [sh]
  exact Prod.ext (stdPart_eq_of_sub_infinitesimal e1) (stdPart_eq_of_sub_infinitesimal e2)

/-- **A granular point has parts.** The centre `c` and the pole `c + (ε, 0)` of the point
`ball(c, ε)` are distinct granular points with the same shadow: the classical point is
the shadow of the granular point, and "has no part" because the shadow identifies them. -/
theorem point_has_parts (c : Pt ℝ*) :
    ∃ p : Pt ℝ*, p ≠ c ∧ |p.1 - c.1| ≤ Hyperreal.epsilon ∧ |p.2 - c.2| ≤ Hyperreal.epsilon ∧
      sh p = sh c := by
  have hε : |Hyperreal.epsilon| = Hyperreal.epsilon := abs_of_pos Hyperreal.epsilon_pos
  refine ⟨(c.1 + Hyperreal.epsilon, c.2), ?_, ?_, ?_, ?_⟩
  · intro h
    have := congrArg Prod.fst h
    simp only at this
    exact Hyperreal.epsilon_ne_zero (by linarith)
  · simp only [add_sub_cancel_left, hε, le_refl]
  · simp only [sub_self, abs_zero]; exact Hyperreal.epsilon_pos.le
  · exact sh_eq_of_mem_ball (by simp only [add_sub_cancel_left, hε, le_refl])
      (by simp only [sub_self, abs_zero]; exact Hyperreal.epsilon_pos.le)

theorem isFinite_of_mem_Icc {t : ℝ*} (h0 : 0 ≤ t) (h1 : t ≤ 1) : IsFinite t := by
  have h : |t| ≤ |(1 : ℝ*)| := by rw [abs_of_nonneg h0, abs_one]; exact h1
  have := ArchimedeanClass.mk_le_mk_of_abs h
  rwa [ArchimedeanClass.mk_one] at this

theorem isFinite_sub {x y : ℝ*} (hx : IsFinite x) (hy : IsFinite y) : IsFinite (x - y) := by
  have hy' : IsFinite (-y) := by
    unfold IsFinite at hy ⊢; rwa [ArchimedeanClass.mk_neg]
  rw [sub_eq_add_neg]; exact hx.add hy'

/-- **The shadow preserves betweenness** (weakly): if `B` is between `A` and `C` then the
shadow of `B` is on the segment from the shadow of `A` to that of `C`. -/
theorem sh_btw {A B C : Pt ℝ*} (hA : IsFinitePt A) (hB : IsFinitePt B) (hC : IsFinitePt C)
    (h : Btw A B C) :
    ∃ t : ℝ, 0 ≤ t ∧ t ≤ 1 ∧ (sh B).1 = (sh A).1 + t * ((sh C).1 - (sh A).1) ∧
      (sh B).2 = (sh A).2 + t * ((sh C).2 - (sh A).2) := by
  obtain ⟨-, t, ht0, ht1, e1, e2⟩ := h
  have htf : IsFinite t := isFinite_of_mem_Icc ht0.le ht1.le
  refine ⟨ArchimedeanClass.stdPart t, ?_, ?_, ?_, ?_⟩
  · have := stdPart_mono (coe_isFinite 0) htf (by simpa using ht0.le)
    simpa [Hyperreal.stdPart_coe] using this
  · have := stdPart_mono htf (coe_isFinite 1) (by simpa using ht1.le)
    simpa [Hyperreal.stdPart_coe] using this
  · simp only [sh]
    rw [e1, ArchimedeanClass.stdPart_add hA.1 (htf.mul (isFinite_sub hC.1 hA.1)),
      stdPart_mul' htf (isFinite_sub hC.1 hA.1), ArchimedeanClass.stdPart_sub hC.1 hA.1]
  · simp only [sh]
    rw [e2, ArchimedeanClass.stdPart_add hA.2 (htf.mul (isFinite_sub hC.2 hA.2)),
      stdPart_mul' htf (isFinite_sub hC.2 hA.2), ArchimedeanClass.stdPart_sub hC.2 hA.2]

theorem stdPart_q {A B : Pt ℝ*} (hA : IsFinitePt A) (hB : IsFinitePt B) :
    ArchimedeanClass.stdPart (q A B) = q (sh A) (sh B) := by
  have h1 : IsFinite (A.1 - B.1) := isFinite_sub hA.1 hB.1
  have h2 : IsFinite (A.2 - B.2) := isFinite_sub hA.2 hB.2
  simp only [q, sh, sq]
  rw [ArchimedeanClass.stdPart_add (h1.mul h1) (h2.mul h2), stdPart_mul' h1 h1,
    stdPart_mul' h2 h2, ArchimedeanClass.stdPart_sub hA.1 hB.1,
    ArchimedeanClass.stdPart_sub hA.2 hB.2]

/-- **The shadow preserves congruence.** -/
theorem sh_cong {A B C D : Pt ℝ*} (hA : IsFinitePt A) (hB : IsFinitePt B) (hC : IsFinitePt C)
    (hD : IsFinitePt D) (h : Cong A B C D) : Cong (sh A) (sh B) (sh C) (sh D) := by
  unfold Cong at h ⊢
  rw [← stdPart_q hA hB, ← stdPart_q hC hD, h]

/-- **The shadow preserves lines**: a finite point of an internal line with finite
coefficients lies on the shadow line. -/
theorem sh_line {a b c : ℝ*} {p : Pt ℝ*} (ha : IsFinite a) (hb : IsFinite b) (hc : IsFinite c)
    (hp : IsFinitePt p) (h : a * p.1 + b * p.2 + c = 0) :
    ArchimedeanClass.stdPart a * (sh p).1 + ArchimedeanClass.stdPart b * (sh p).2 +
      ArchimedeanClass.stdPart c = 0 := by
  have := congrArg ArchimedeanClass.stdPart h
  rw [ArchimedeanClass.stdPart_zero, ArchimedeanClass.stdPart_add ((ha.mul hp.1).add (hb.mul hp.2)) hc,
    ArchimedeanClass.stdPart_add (ha.mul hp.1) (hb.mul hp.2), stdPart_mul' ha hp.1,
    stdPart_mul' hb hp.2] at this
  simpa [sh] using this

end Hyper

/-! ## Tarski's first-order language and transfer -/

section Tarski
open FirstOrder FirstOrder.Language Hyperreal Filter

/-- The relation symbols of Tarski's language: betweenness (ternary) and equidistance
(4-ary). -/
inductive TRel : ℕ → Type
  | btw : TRel 3
  | cong : TRel 4

/-- Tarski's language of elementary geometry: no function symbols, the relations `B` and
`≡`. -/
def tarski : Language := ⟨fun _ => Empty, TRel⟩

variable {F : Type*} [Field F] [LinearOrder F] [IsStrictOrderedRing F]

/-- The Cartesian plane over `F` as a structure for Tarski's language. -/
instance tarskiStructure : tarski.Structure (Pt F) where
  funMap := fun f _ => Empty.elim f
  RelMap := fun {n} r x =>
    match n, r, x with
    | _, TRel.btw, x => Btw (x 0) (x 1) (x 2)
    | _, TRel.cong, x => Cong (x 0) (x 1) (x 2) (x 3)

/-- The point of the hyperreal plane given by a sequence of real points. -/
noncomputable def ptOfSeq (a : ℕ → Pt ℝ) : Pt ℝ* :=
  (ofSeq fun n => (a n).1, ofSeq fun n => (a n).2)

theorem ptOfSeq_eq_iff (a b : ℕ → Pt ℝ) :
    ptOfSeq a = ptOfSeq b ↔ ∀ᶠ n in (hyperfilter ℕ : Filter ℕ), a n = b n := by
  constructor
  · intro h
    have h1 : ofSeq (fun n => (a n).1) = ofSeq (fun n => (b n).1) := congrArg Prod.fst h
    have h2 : ofSeq (fun n => (a n).2) = ofSeq (fun n => (b n).2) := congrArg Prod.snd h
    exact ((Filter.Germ.coe_eq.mp h1).and (Filter.Germ.coe_eq.mp h2)).mono
      fun n hn => Prod.ext hn.1 hn.2
  · intro h
    exact Prod.ext (Filter.Germ.coe_eq.mpr (h.mono fun n hn => congrArg Prod.fst hn))
      (Filter.Germ.coe_eq.mpr (h.mono fun n hn => congrArg Prod.snd hn))

theorem btw_ofSeq_iff (a b c : ℕ → Pt ℝ) :
    Btw (ptOfSeq a) (ptOfSeq b) (ptOfSeq c) ↔
      ∀ᶠ n in (hyperfilter ℕ : Filter ℕ), Btw (a n) (b n) (c n) := by
  constructor
  · rintro ⟨hne, t, ht0, ht1, e1, e2⟩
    obtain ⟨τ, rfl⟩ := ofSeq_surjective t
    have hne' : ∀ᶠ n in (hyperfilter ℕ : Filter ℕ), a n ≠ c n :=
      Ultrafilter.eventually_not.mpr fun h => hne ((ptOfSeq_eq_iff a c).2 h)
    have h0 : ∀ᶠ n in (hyperfilter ℕ : Filter ℕ), 0 < τ n :=
      ofSeq_lt_ofSeq.1 (show ofSeq (fun _ => (0 : ℝ)) < ofSeq τ from ht0)
    have h1 : ∀ᶠ n in (hyperfilter ℕ : Filter ℕ), τ n < 1 :=
      ofSeq_lt_ofSeq.1 (show ofSeq τ < ofSeq (fun _ => (1 : ℝ)) from ht1)
    have f1 : ∀ᶠ n in (hyperfilter ℕ : Filter ℕ),
        (b n).1 = (a n).1 + τ n * ((c n).1 - (a n).1) :=
      Filter.Germ.coe_eq.mp (show ofSeq (fun n => (b n).1) =
        ofSeq (fun n => (a n).1 + τ n * ((c n).1 - (a n).1)) from e1)
    have f2 : ∀ᶠ n in (hyperfilter ℕ : Filter ℕ),
        (b n).2 = (a n).2 + τ n * ((c n).2 - (a n).2) :=
      Filter.Germ.coe_eq.mp (show ofSeq (fun n => (b n).2) =
        ofSeq (fun n => (a n).2 + τ n * ((c n).2 - (a n).2)) from e2)
    exact (((hne'.and h0).and h1).and (f1.and f2)).mono
      fun n ⟨⟨⟨hn, h0⟩, h1⟩, g1, g2⟩ => ⟨hn, τ n, h0, h1, g1, g2⟩
  · intro h
    classical
    let τ : ℕ → ℝ := fun n =>
      if hn : ∃ t : ℝ, 0 < t ∧ t < 1 ∧ (b n).1 = (a n).1 + t * ((c n).1 - (a n).1) ∧
          (b n).2 = (a n).2 + t * ((c n).2 - (a n).2) then Classical.choose hn else 0
    have hτ : ∀ᶠ n in (hyperfilter ℕ : Filter ℕ), 0 < τ n ∧ τ n < 1 ∧
        (b n).1 = (a n).1 + τ n * ((c n).1 - (a n).1) ∧
        (b n).2 = (a n).2 + τ n * ((c n).2 - (a n).2) := by
      refine h.mono fun n hn => ?_
      obtain ⟨-, t, ht0, ht1, g1, g2⟩ := hn
      have hex : ∃ t : ℝ, 0 < t ∧ t < 1 ∧ (b n).1 = (a n).1 + t * ((c n).1 - (a n).1) ∧
          (b n).2 = (a n).2 + t * ((c n).2 - (a n).2) := ⟨t, ht0, ht1, g1, g2⟩
      simp only [τ, dif_pos hex]
      exact Classical.choose_spec hex
    refine ⟨fun heq => ?_, ofSeq τ, ?_, ?_, ?_, ?_⟩
    · have := (ptOfSeq_eq_iff a c).1 heq
      have hfalse : ∀ᶠ n in (hyperfilter ℕ : Filter ℕ), False :=
        (this.and h).mono fun n ⟨h1, h2⟩ => h2.1 h1
      exact (Ultrafilter.neBot _).ne (Filter.eventually_false_iff_eq_bot.1 hfalse)
    · exact ofSeq_lt_ofSeq.2 (hτ.mono fun n hn => hn.1)
    · exact ofSeq_lt_ofSeq.2 (hτ.mono fun n hn => hn.2.1)
    · exact Filter.Germ.coe_eq.mpr (hτ.mono fun n hn => hn.2.2.1)
    · exact Filter.Germ.coe_eq.mpr (hτ.mono fun n hn => hn.2.2.2)

theorem cong_ofSeq_iff (a b c d : ℕ → Pt ℝ) :
    Cong (ptOfSeq a) (ptOfSeq b) (ptOfSeq c) (ptOfSeq d) ↔
      ∀ᶠ n in (hyperfilter ℕ : Filter ℕ), Cong (a n) (b n) (c n) (d n) :=
  show ofSeq (fun n => q (a n) (b n)) = ofSeq (fun n => q (c n) (d n)) ↔ _ from
    Filter.Germ.coe_eq

/-- From the ultrapower of the real plane to the hyperreal plane. -/
noncomputable def toHyperPlane :
    (↑(hyperfilter ℕ) : Filter ℕ).Product (fun _ : ℕ => Pt ℝ) → Pt ℝ* :=
  Quotient.lift ptOfSeq fun f g (h : ∀ᶠ n in (hyperfilter ℕ : Filter ℕ), f n = g n) =>
    (ptOfSeq_eq_iff f g).2 h

theorem toHyperPlane_mk (f : ℕ → Pt ℝ) :
    toHyperPlane (↑f : (↑(hyperfilter ℕ) : Filter ℕ).Product (fun _ : ℕ => Pt ℝ)) =
      ptOfSeq f := rfl

theorem toHyperPlane_bijective : Function.Bijective toHyperPlane := by
  constructor
  · intro x y
    refine Quotient.inductionOn₂ x y fun f g h => ?_
    exact Quotient.sound ((ptOfSeq_eq_iff f g).1 h)
  · rintro ⟨x, y⟩
    obtain ⟨f, rfl⟩ := ofSeq_surjective x
    obtain ⟨g, rfl⟩ := ofSeq_surjective y
    exact ⟨(↑(fun n => ((f n, g n) : Pt ℝ)) : (↑(hyperfilter ℕ) : Filter ℕ).Product
      (fun _ : ℕ => Pt ℝ)), rfl⟩

/-- **The ultrapower of the real plane is the hyperreal plane**, as structures for Tarski's
language. -/
noncomputable def hyperEquiv :
    (↑(hyperfilter ℕ) : Filter ℕ).Product (fun _ : ℕ => Pt ℝ) ≃[tarski] Pt ℝ* where
  toEquiv := Equiv.ofBijective _ toHyperPlane_bijective
  map_fun' := fun {_} f _ => Empty.elim f
  map_rel' := by
    intro n r x
    obtain ⟨y, hy⟩ : ∃ y : Fin n → (ℕ → Pt ℝ),
        ∀ i, (↑(y i) : (↑(hyperfilter ℕ) : Filter ℕ).Product (fun _ : ℕ => Pt ℝ)) = x i :=
      ⟨fun i => (x i).out, fun i => Quotient.out_eq _⟩
    have hx : x = fun i => (↑(y i) : (↑(hyperfilter ℕ) : Filter ℕ).Product (fun _ : ℕ => Pt ℝ)) :=
      funext fun i => (hy i).symm
    subst hx
    have key := relMap_quotient_mk' ((↑(hyperfilter ℕ) : Filter ℕ).productSetoid
      fun _ : ℕ => Pt ℝ) r y
    refine Iff.trans ?_ key.symm
    cases r with
    | btw => exact btw_ofSeq_iff (y 0) (y 1) (y 2)
    | cong => exact cong_ofSeq_iff (y 0) (y 1) (y 2) (y 3)

/-- **Transfer for elementary geometry.** The granular plane `ℝ* × ℝ*` and the Euclidean
plane `ℝ × ℝ` satisfy the same sentences of Tarski's first-order language of betweenness
and congruence. -/
theorem tarski_transfer (φ : tarski.Sentence) : (Pt ℝ*) ⊨ φ ↔ (Pt ℝ) ⊨ φ :=
  (StrongHomClass.realize_sentence hyperEquiv φ).symm.trans
    (QE.NSA.transfer_ultrapower (Pt ℝ) (hyperfilter ℕ) φ)

/-- **Archimedes' axiom is not elementary**: no sentence of Tarski's language expresses V.1
in both the Euclidean and the granular plane. The dimensionlessness of the point is not a
first-order property of geometry. -/
theorem archimedes_not_elementary :
    ¬ ∃ φ : tarski.Sentence, ((Pt ℝ) ⊨ φ ↔ euclideanPlane.Archimedes) ∧
      ((Pt ℝ*) ⊨ φ ↔ granularPlane.Archimedes) := by
  rintro ⟨φ, h1, h2⟩
  exact granular_not_archimedes (h2.1 ((tarski_transfer φ).2 (h1.2 euclidean_archimedes)))

/-- **Dedekind's axiom is not elementary.** -/
theorem dedekind_not_elementary :
    ¬ ∃ φ : tarski.Sentence, ((Pt ℝ) ⊨ φ ↔ euclideanPlane.Dedekind) ∧
      ((Pt ℝ*) ⊨ φ ↔ granularPlane.Dedekind) := by
  rintro ⟨φ, h1, h2⟩
  exact granular_not_dedekind (h2.1 ((tarski_transfer φ).2 (h1.2 euclidean_dedekind)))

end Tarski

end QE.Hilbert
