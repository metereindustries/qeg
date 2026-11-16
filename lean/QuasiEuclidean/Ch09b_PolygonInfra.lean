-- SPDX-License-Identifier: MIT
-- Copyright 2026 Metere Industries, Inc. Author: Alfredo Metere.
-- Quasi-Euclidean Granular Geometry. Any derivative work must carry this notice:
--   This work is derivative of the Quasi-Euclidean Granular Geometry book
--   authored by Alfredo Metere. Copyright 2026 Metere Industries, Inc.
--   All rights reserved
-- See LICENSE.md and NOTICE.

import QuasiEuclidean.Basic

/-!
# Chapter 9, infrastructure: convex polygons and their parallel bodies

Mathlib has no theory of polygons or of Minkowski sums of polygons with discs;
we build what the Steiner formula needs.

* A **convex polygon** is given by its vertices `v₀, …, v_{m-1}` (`m ≥ 3`) in
  counter-clockwise order, every vertex other than the endpoints of an edge lying
  strictly to the left of that edge. Its region `K` is the intersection of the
  closed left half-planes of the edges, and equals the convex hull of the
  vertices (`K_eq_convexHull`).
* Nearest-point certificates: `p` is the nearest point of `K` to `x` iff
  `⟪x - p, y - p⟫ ≤ 0` for all `y ∈ K`.
* The parallel body `K + B̄(0,r)` is the disjoint union of `K`, one rectangle
  `eᵢ × (0,r]` over each edge, and one circular sector at each vertex; the
  sectors, translated to the origin, tile the punctured disc.
* **Steiner formula**: `vol(K + B̄(0,r)) = vol K + P r + π r²`.

This is a *shadow* (classical comparison) result: it is about Lebesgue measure.

The second part of the file (namespace `QE.Pick`, Lebesgue-free) proves Pick's
theorem for every simple lattice polygon, with the granular interior defined by the
winding number, and the anisotropic Steiner form of Pick.
-/

namespace QE.Polygon

open MeasureTheory Metric Finset
open scoped Pointwise

noncomputable section

/-- The Euclidean plane. -/
abbrev E2 := EuclideanSpace ℝ (Fin 2)

/-- The planar cross product (signed area of the parallelogram). -/
def cross (a b : E2) : ℝ := a 0 * b 1 - a 1 * b 0

/-- Rotation by `-π/2`: the outward normal of an edge traversed counter-clockwise. -/
def rotR (a : E2) : E2 := WithLp.toLp 2 ![a 1, -a 0]

@[simp] lemma rotR_apply_zero (a : E2) : rotR a 0 = a 1 := by simp [rotR]
@[simp] lemma rotR_apply_one (a : E2) : rotR a 1 = -a 0 := by simp [rotR]

lemma inner_eq (a b : E2) : inner ℝ a b = a 0 * b 0 + a 1 * b 1 := by
  simp [PiLp.inner_apply, Fin.sum_univ_two]
  ring

lemma norm_sq_eq (a : E2) : ‖a‖ ^ 2 = a 0 ^ 2 + a 1 ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, inner_eq]; ring

lemma ext2 {a b : E2} (h0 : a 0 = b 0) (h1 : a 1 = b 1) : a = b := by
  ext i; fin_cases i <;> simp [h0, h1]

/-- Lagrange-type identity used throughout:
`[a,b] ⟪w,u⟫ = ⟪w,b⟫ [a,u] - ⟪w,a⟫ [b,u]`. -/
lemma lagrange (a b w u : E2) :
    cross a b * inner ℝ w u = inner ℝ w b * cross a u - inner ℝ w a * cross b u := by
  simp only [inner_eq, cross]; ring

/-- Orthogonal decomposition along `d` and its normal `rotR d`. -/
lemma decomp (d u : E2) : ‖d‖ ^ 2 • u = inner ℝ u d • d + inner ℝ u (rotR d) • rotR d := by
  rw [norm_sq_eq]
  apply ext2 <;> simp [inner_eq] <;> ring

lemma inner_rotR (a u : E2) : inner ℝ (rotR a) u = - cross a u := by
  simp [inner_eq, cross]; ring

lemma inner_rotR' (u a : E2) : inner ℝ u (rotR a) = - cross a u := by
  rw [real_inner_comm, inner_rotR]

lemma cross_rotR_self (a : E2) : cross a (rotR a) = -‖a‖ ^ 2 := by
  rw [norm_sq_eq]; simp [cross]; ring

lemma norm_rotR (a : E2) : ‖rotR a‖ = ‖a‖ := by
  have h : ‖rotR a‖ ^ 2 = ‖a‖ ^ 2 := by rw [norm_sq_eq, norm_sq_eq]; simp; ring
  exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp h

lemma cross_add_right (a b c : E2) : cross a (b + c) = cross a b + cross a c := by
  simp [cross]; ring
lemma cross_sub_right (a b c : E2) : cross a (b - c) = cross a b - cross a c := by
  simp [cross]; ring
lemma cross_smul_right (a b : E2) (t : ℝ) : cross a (t • b) = t * cross a b := by
  simp [cross]; ring
lemma cross_self (a : E2) : cross a a = 0 := by simp [cross]; ring
lemma cross_anti (a b : E2) : cross a b = - cross b a := by simp [cross]; ring

/-- Two vectors orthogonal to both of two independent vectors vanish. -/
lemma eq_zero_of_cross {a b u : E2} (hab : cross a b ≠ 0) (ha : cross a u = 0)
    (hb : cross b u = 0) : u = 0 := by
  apply ext2
  · have := lagrange a b (WithLp.toLp 2 ![1, 0]) u
    simp [inner_eq, ha, hb] at this
    simpa using this.resolve_left hab
  · have := lagrange a b (WithLp.toLp 2 ![0, 1]) u
    simp [inner_eq, ha, hb] at this
    simpa using this.resolve_left hab

lemma eq_zero_of_inner {a b u : E2} (hab : cross a b ≠ 0) (ha : inner ℝ u a = 0)
    (hb : inner ℝ u b = 0) : u = 0 := by
  have h1 : cross a (rotR u) = 0 := by
    have := inner_rotR' a u; rw [real_inner_comm] at ha; simp [cross] at this ⊢
    rw [inner_eq] at ha; linarith
  have h2 : cross b (rotR u) = 0 := by
    rw [real_inner_comm, inner_eq] at hb; simp [cross]; linarith
  have := eq_zero_of_cross hab h1 h2
  apply ext2
  · have := congrArg (fun z : E2 => z 1) this; simpa using this
  · have := congrArg (fun z : E2 => z 0) this; simpa using this

/-! ## Convex polygons -/

/-- A convex polygon with `m ≥ 3` vertices in counter-clockwise order: every
vertex other than the two endpoints of an edge lies strictly to the left of
that edge. -/
structure ConvexPolygon (m : ℕ) [NeZero m] where
  v : Fin m → E2
  three : 3 ≤ m
  left : ∀ i j : Fin m, j ≠ i → j ≠ i + 1 → 0 < cross (v (i + 1) - v i) (v j - v i)

variable {m : ℕ} [NeZero m] (P : ConvexPolygon m)

namespace ConvexPolygon

/-- Edge vector `dᵢ = v_{i+1} - vᵢ`. -/
def d (i : Fin m) : E2 := P.v (i + 1) - P.v i

/-- The region of the polygon: the intersection of the closed left
half-planes of its edges. -/
def K : Set E2 := {x | ∀ i, 0 ≤ cross (P.d i) (x - P.v i)}

/-- Edge length. -/
def len (i : Fin m) : ℝ := ‖P.d i‖

/-- Perimeter. -/
def perimeter : ℝ := ∑ i, P.len i

include P in
lemma one_ne_zero' : (1 : Fin m) ≠ 0 := by
  have h3 := P.three
  intro h
  have := congrArg Fin.val h
  rw [Fin.val_one', Fin.val_zero, Nat.mod_eq_of_lt (by omega)] at this
  omega

include P in
lemma two_ne_zero' : (1 + 1 : Fin m) ≠ 0 := by
  have h3 := P.three
  intro h
  have := congrArg Fin.val h
  rw [Fin.val_add, Fin.val_one', Nat.mod_eq_of_lt (by omega : 1 < m), Fin.val_zero,
    Nat.mod_eq_of_lt (by omega : 1 + 1 < m)] at this
  omega

include P in
lemma succ_ne (i : Fin m) : i + 1 ≠ i := by
  intro h; apply P.one_ne_zero'; simpa using congrArg (· - i) h

include P in
lemma succ_succ_ne (i : Fin m) : i + 1 + 1 ≠ i := by
  intro h; apply P.two_ne_zero'
  have e : (1 + 1 : Fin m) = (i + 1 + 1) - i := by abel
  rw [e, h, sub_self]

include P in
lemma pred_ne (i : Fin m) : i - 1 ≠ i := by
  intro h; apply P.one_ne_zero'
  have := congrArg (fun z => i - z) h
  simp only [sub_sub_cancel, sub_self] at this
  exact this

include P in
lemma succ_ne_pred (i : Fin m) : i + 1 ≠ i - 1 := by
  intro h; apply P.two_ne_zero'
  have e : (1 + 1 : Fin m) = (i + 1) - (i - 1) := by abel
  rw [e, h, sub_self]

lemma d_pred (i : Fin m) : P.d (i - 1) = P.v i - P.v (i - 1) := by
  simp [d]

/-- Consecutive edges turn left. -/
lemma cross_d_pos (i : Fin m) : 0 < cross (P.d (i - 1)) (P.d i) := by
  have h := P.left (i - 1) (i + 1) (P.succ_ne_pred i) (by simpa using P.succ_ne i)
  rw [sub_add_cancel] at h
  have e : P.v (i + 1) - P.v (i - 1) = P.d (i - 1) + P.d i := by
    simp [d]
  rw [e, cross_add_right, ← P.d_pred, cross_self, zero_add] at h
  exact h

lemma cross_d_succ_pos (i : Fin m) : 0 < cross (P.d i) (P.d (i + 1)) := by
  simpa using P.cross_d_pos (i + 1)

lemma d_ne_zero (i : Fin m) : P.d i ≠ 0 := by
  intro h; have := P.cross_d_pos i; rw [h] at this; simp [cross] at this

lemma len_pos (i : Fin m) : 0 < P.len i := norm_pos_iff.mpr (P.d_ne_zero i)

/-- A vertex on the line of edge `i` is one of its endpoints. -/
lemma mem_edge_line {i j : Fin m} (h : cross (P.d i) (P.v j - P.v i) = 0) :
    j = i ∨ j = i + 1 := by
  by_contra hc
  push Not at hc
  have := P.left i j hc.1 hc.2
  rw [← d] at this
  linarith

lemma v_injective : Function.Injective P.v := by
  intro i j h
  by_contra hij
  rcases P.mem_edge_line (i := i) (j := j) (by rw [h, sub_self]; simp [cross]) with e | e
  · exact hij e.symm
  · apply P.d_ne_zero i; rw [d, ← e, h, sub_self]

lemma vertex_mem (j : Fin m) : P.v j ∈ P.K := by
  intro i
  by_cases h1 : j = i
  · subst h1; simp [cross]
  by_cases h2 : j = i + 1
  · subst h2; rw [← d, cross_self]
  exact (P.left i j h1 h2).le

lemma K_nonempty : P.K.Nonempty := ⟨P.v 0, P.vertex_mem 0⟩

lemma cross_affine (a b c : E2) (t : ℝ) :
    cross a ((1 - t) • b + t • c) = (1 - t) * cross a b + t * cross a c := by
  simp [cross]; ring

lemma K_convex : Convex ℝ P.K := by
  intro x hx y hy s t hs ht hst i
  have e : s • x + t • y - P.v i = s • (x - P.v i) + t • (y - P.v i) := by
    rw [smul_sub, smul_sub, sub_add_sub_comm, ← add_smul, hst, one_smul]
  rw [e]
  have := hx i; have := hy i
  simp only [cross, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul] at *
  nlinarith

lemma K_closed : IsClosed P.K := by
  have : P.K = ⋂ i, {x : E2 | 0 ≤ cross (P.d i) (x - P.v i)} := by ext; simp [K]
  rw [this]
  refine isClosed_iInter (fun i => isClosed_le continuous_const ?_)
  unfold cross
  fun_prop

/-! ## `K` is the convex hull of the vertices -/

lemma cramer (a b X : E2) : cross a b • X = cross X b • a + cross a X • b := by
  apply ext2 <;> simp [cross] <;> ring

lemma nat_ivt (f : ℕ → ℝ) (a b : ℕ) (hab : a < b) (ha : 0 ≤ f a) (hb : f b ≤ 0) :
    ∃ n, a ≤ n ∧ n < b ∧ 0 ≤ f n ∧ f (n + 1) ≤ 0 := by
  induction b with
  | zero => omega
  | succ b ih =>
    by_cases h : f b ≤ 0
    · rcases Nat.lt_succ_iff_lt_or_eq.mp hab with h' | h'
      · obtain ⟨n, h1, h2, h3, h4⟩ := ih h' h
        exact ⟨n, h1, by omega, h3, h4⟩
      · subst h'; exact ⟨a, le_rfl, by omega, ha, hb⟩
    · exact ⟨b, by omega, by omega, (not_le.mp h).le, hb⟩

open Fin.NatCast in
/-- The region `K` is the convex hull of the vertices: the definition of a
convex polygon by its vertices and by its edge half-planes agree. -/
theorem K_eq_convexHull : P.K = convexHull ℝ (Set.range P.v) := by
  apply le_antisymm
  · intro x hx
    have hm := P.three
    set g : ℕ → ℝ := fun n => cross (P.v (n : Fin m) - P.v 0) (x - P.v 0) with hg
    have g1 : 0 ≤ g 1 := by
      have := hx 0; simp only [d, zero_add] at this
      simpa [hg] using this
    have gm : g (m - 1) ≤ 0 := by
      have := hx ((m - 1 : ℕ) : Fin m)
      have e : ((m - 1 : ℕ) : Fin m) + 1 = 0 := by
        rw [← Nat.cast_succ, Nat.succ_eq_add_one, Nat.sub_add_cancel (by omega),
          Fin.natCast_self]
      simp only [d, e] at this
      have e2 : x - P.v ((m - 1 : ℕ) : Fin m) =
          (x - P.v 0) + (P.v 0 - P.v ((m - 1 : ℕ) : Fin m)) := by abel
      rw [e2, cross_add_right, cross_self, add_zero, cross_anti] at this
      simp only [hg]
      have e3 : P.v 0 - P.v ((m - 1 : ℕ) : Fin m) = -(P.v ((m - 1 : ℕ) : Fin m) - P.v 0) := by
        abel
      rw [e3] at this
      simp [cross] at this ⊢
      linarith
    obtain ⟨n, hn1, hn2, hgn, hgn1⟩ := nat_ivt g 1 (m - 1) (by omega) g1 gm
    set a := P.v (n : Fin m) - P.v 0
    set b := P.v ((n + 1 : ℕ) : Fin m) - P.v 0
    set X := x - P.v 0
    have hcast : ((n + 1 : ℕ) : Fin m) = (n : Fin m) + 1 := by push_cast; rfl
    have hne0 : (0 : Fin m) ≠ (n : Fin m) := by
      intro h
      have := congrArg Fin.val h
      rw [Fin.val_zero, Fin.val_natCast, Nat.mod_eq_of_lt (by omega)] at this
      omega
    have hne1 : (0 : Fin m) ≠ (n : Fin m) + 1 := by
      rw [← hcast]
      intro h
      have := congrArg Fin.val h
      rw [Fin.val_zero, Fin.val_natCast, Nat.mod_eq_of_lt (by omega)] at this
      omega
    have hc : 0 < cross a b := by
      have := P.left (n : Fin m) 0 hne0 hne1
      rw [← hcast] at this
      have e : cross (P.v ((n + 1 : ℕ) : Fin m) - P.v (n : Fin m)) (P.v 0 - P.v (n : Fin m)) =
          cross a b := by simp only [a, b, cross, PiLp.sub_apply]; ring
      linarith
    have hedge : 0 ≤ cross (b - a) (X - a) := by
      have := hx (n : Fin m)
      simp only [d] at this
      rw [← hcast] at this
      have e1 : b - a = P.v ((n + 1 : ℕ) : Fin m) - P.v (n : Fin m) := by
        simp only [a, b]; abel
      have e2 : X - a = x - P.v (n : Fin m) := by simp only [X, a]; abel
      rw [e1, e2]; exact this
    set lam := cross X b / cross a b
    set mu := cross a X / cross a b
    have hXb : 0 ≤ cross X b := by
      have := hgn1; simp only [hg] at this
      rw [cross_anti]; linarith
    have hlam : 0 ≤ lam := div_nonneg hXb hc.le
    have hmu : 0 ≤ mu := div_nonneg hgn hc.le
    have hsum : 0 ≤ 1 - lam - mu := by
      have e : cross (b - a) (X - a) = cross a b * (1 - lam - mu) := by
        simp only [lam, mu]; field_simp; simp only [cross, PiLp.sub_apply]; ring
      rw [e] at hedge
      exact nonneg_of_mul_nonneg_right (by linarith) hc
    have hx' : x = (1 - lam - mu) • P.v 0 + lam • P.v (n : Fin m) +
        mu • P.v ((n + 1 : ℕ) : Fin m) := by
      have hcr := cramer a b X
      have : X = lam • a + mu • b := by
        apply smul_right_injective E2 hc.ne'
        simp only [smul_add, smul_smul, lam, mu, mul_div_cancel₀ _ hc.ne']
        exact hcr
      have e : x = P.v 0 + X := by simp [X]
      rw [e, this]; simp only [a, b, smul_sub, sub_smul, one_smul]; abel
    rw [hx']
    have := (convex_convexHull ℝ (Set.range P.v)).sum_mem (t := Finset.univ)
      (w := ![1 - lam - mu, lam, mu]) (z := ![P.v 0, P.v (n : Fin m), P.v ((n + 1 : ℕ) : Fin m)])
      (by intro i _; fin_cases i <;> simp [hsum, hlam, hmu])
      (by simp [Fin.sum_univ_three]; ring)
      (by intro i _; fin_cases i <;> exact subset_convexHull ℝ _ ⟨_, rfl⟩)
    simpa [Fin.sum_univ_three] using this
  · exact convexHull_min (Set.range_subset_iff.mpr P.vertex_mem) P.K_convex

/-! ## Nearest points -/

/-- `p` is the nearest point of `K` to `x`, in variational form. -/
def IsNear (p x : E2) : Prop := p ∈ P.K ∧ ∀ y ∈ P.K, inner ℝ (x - p) (y - p) ≤ 0

lemma IsNear.unique {p q x : E2} (hp : P.IsNear p x) (hq : P.IsNear q x) : p = q := by
  have h1 := hp.2 q hq.1
  have h2 := hq.2 p hp.1
  simp only [inner_eq, PiLp.sub_apply] at h1 h2
  apply ext2 <;> nlinarith [sq_nonneg (p 0 - q 0), sq_nonneg (p 1 - q 1)]

lemma IsNear.eq_of_mem {p x : E2} (hp : P.IsNear p x) (hx : x ∈ P.K) : x = p := by
  have h := hp.2 x hx
  simp only [inner_eq, PiLp.sub_apply] at h
  apply ext2 <;> nlinarith [sq_nonneg (x 0 - p 0), sq_nonneg (x 1 - p 1)]

lemma IsNear.norm_le {p x : E2} (hp : P.IsNear p x) {y : E2} (hy : y ∈ P.K) :
    ‖x - p‖ ≤ ‖x - y‖ := by
  have h := hp.2 y hy
  have e1 := norm_sq_eq (x - p)
  have e2 := norm_sq_eq (x - y)
  simp only [inner_eq, PiLp.sub_apply] at h e1 e2
  have : ‖x - p‖ ^ 2 ≤ ‖x - y‖ ^ 2 := by
    rw [e1, e2]; nlinarith [sq_nonneg (y 0 - p 0), sq_nonneg (y 1 - p 1)]
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp this

lemma exists_near (x : E2) : ∃ p, P.IsNear p x := by
  obtain ⟨p, hp, hmin⟩ := exists_norm_eq_iInf_of_complete_convex P.K_nonempty
    P.K_closed.isComplete P.K_convex x
  exact ⟨p, hp, (norm_eq_iInf_iff_real_inner_le_zero P.K_convex hp).mp hmin⟩

/-- A vector in the closed normal cone at `vₖ` is maximised over `K` at `vₖ`. -/
lemma inner_le_of_cone {k : Fin m} {w : E2} (h1 : inner ℝ w (P.d k) ≤ 0)
    (h2 : 0 ≤ inner ℝ w (P.d (k - 1))) {y : E2} (hy : y ∈ P.K) :
    inner ℝ w (y - P.v k) ≤ 0 := by
  have hc := P.cross_d_pos k
  have hL := lagrange (P.d (k - 1)) (P.d k) w (y - P.v k)
  have ha : cross (P.d (k - 1)) (y - P.v k) = cross (P.d (k - 1)) (y - P.v (k - 1)) := by
    rw [show y - P.v k = (y - P.v (k - 1)) - P.d (k - 1) by rw [d_pred]; abel,
      cross_sub_right, cross_self, sub_zero]
  have hk1 := hy (k - 1)
  have hk := hy k
  rw [ha] at hL
  by_contra hcon
  push Not at hcon
  have : 0 < cross (P.d (k - 1)) (P.d k) * inner ℝ w (y - P.v k) := mul_pos hc hcon
  nlinarith [mul_nonpos_of_nonpos_of_nonneg h1 hk1, mul_nonneg h2 hk]

/-- A point of `K` on the line of edge `i` lies on the edge. -/
lemma edge_of_line {i : Fin m} {y : E2} (hy : y ∈ P.K) (hl : cross (P.d i) (y - P.v i) = 0) :
    0 ≤ inner ℝ (y - P.v i) (P.d i) ∧ inner ℝ (y - P.v i) (P.d i) ≤ ‖P.d i‖ ^ 2 := by
  have hdec := decomp (P.d i) (y - P.v i)
  rw [inner_rotR', hl, neg_zero, zero_smul, add_zero] at hdec
  -- constraint `i - 1`
  have hpre := hy (i - 1)
  have hsuc := hy (i + 1)
  have c1 := P.cross_d_pos i
  have c2 := P.cross_d_succ_pos i
  have e1 : y - P.v (i - 1) = (y - P.v i) + P.d (i - 1) := by rw [d_pred]; abel
  have e2 : y - P.v (i + 1) = (y - P.v i) - P.d i := by simp [d]
  rw [e1, cross_add_right, cross_self, add_zero] at hpre
  rw [e2, cross_sub_right] at hsuc
  have h1 : ‖P.d i‖ ^ 2 * cross (P.d (i - 1)) (y - P.v i) =
      inner ℝ (y - P.v i) (P.d i) * cross (P.d (i - 1)) (P.d i) := by
    rw [← cross_smul_right, hdec, cross_smul_right]
  have h2 : ‖P.d i‖ ^ 2 * cross (P.d (i + 1)) (y - P.v i) =
      inner ℝ (y - P.v i) (P.d i) * cross (P.d (i + 1)) (P.d i) := by
    rw [← cross_smul_right, hdec, cross_smul_right]
  have hcs : cross (P.d (i + 1)) (P.d i) = - cross (P.d i) (P.d (i + 1)) := cross_anti _ _
  have hL := P.len_pos i
  have hL2 : 0 < ‖P.d i‖ ^ 2 := by unfold len at hL; positivity
  have hdd : cross (P.d (i + 1)) (P.d i) * ‖P.d i‖ ^ 2 = cross (P.d (i + 1)) (P.d i) *
      inner ℝ (P.d i) (P.d i) := by rw [real_inner_self_eq_norm_sq]
  constructor
  · by_contra hcon; push Not at hcon
    nlinarith [mul_nonneg hL2.le hpre, mul_neg_of_neg_of_pos hcon c1]
  · by_contra hcon; push Not at hcon
    nlinarith [mul_nonneg hL2.le hsuc, mul_pos (sub_pos.mpr hcon) c2]

/-! ## The pieces of the parallel body -/

/-- The parallel body `K + B̄(0,r)` (Minkowski sum with the closed disc). -/
def body (r : ℝ) : Set E2 := P.K + closedBall (0 : E2) r

/-- The rectangle over edge `i`: points at normal height in `(0, r]` above the
half-open edge `[vᵢ, v_{i+1})`. -/
def rect (r : ℝ) (i : Fin m) : Set E2 :=
  {x | 0 ≤ inner ℝ (x - P.v i) (P.d i) ∧ inner ℝ (x - P.v i) (P.d i) < ‖P.d i‖ ^ 2 ∧
    0 < inner ℝ (x - P.v i) (rotR (P.d i)) ∧ inner ℝ (x - P.v i) (rotR (P.d i)) ≤ r * ‖P.d i‖}

/-- The half-open normal cone at vertex `i`. -/
def cone (i : Fin m) : Set E2 := {w | inner ℝ w (P.d i) < 0 ∧ 0 ≤ inner ℝ w (P.d (i - 1))}

/-- The circular sector at vertex `i`. -/
def sector (r : ℝ) (i : Fin m) : Set E2 := {x | x - P.v i ∈ P.cone i ∧ ‖x - P.v i‖ ≤ r}

/-- The foot of `x` on the line of edge `i`. -/
def foot (i : Fin m) (x : E2) : E2 :=
  P.v i + (inner ℝ (x - P.v i) (P.d i) / ‖P.d i‖ ^ 2) • P.d i

lemma sq_len_pos (i : Fin m) : 0 < ‖P.d i‖ ^ 2 := by
  have := P.len_pos i; unfold len at this; positivity

lemma sub_foot (i : Fin m) (x : E2) :
    x - P.foot i x = (inner ℝ (x - P.v i) (rotR (P.d i)) / ‖P.d i‖ ^ 2) • rotR (P.d i) := by
  have hdec := decomp (P.d i) (x - P.v i)
  have hL := (P.sq_len_pos i).ne'
  have : x - P.foot i x = (x - P.v i) - (inner ℝ (x - P.v i) (P.d i) / ‖P.d i‖ ^ 2) • P.d i := by
    simp only [foot]; abel
  rw [this]
  apply smul_right_injective E2 hL
  dsimp only
  rw [smul_sub (‖P.d i‖ ^ 2) (x - P.v i), smul_smul, smul_smul, mul_div_cancel₀ _ hL,
    mul_div_cancel₀ _ hL, hdec]
  abel

lemma foot_mem {r : ℝ} {i : Fin m} {x : E2} (hx : x ∈ P.rect r i) : P.foot i x ∈ P.K := by
  obtain ⟨h1, h2, -, -⟩ := hx
  set t := inner ℝ (x - P.v i) (P.d i) / ‖P.d i‖ ^ 2
  have hL := P.sq_len_pos i
  have ht0 : 0 ≤ t := div_nonneg h1 hL.le
  have ht1 : t ≤ 1 := (div_le_one hL).mpr h2.le
  have := P.K_convex (P.vertex_mem i) (P.vertex_mem (i + 1)) (sub_nonneg.mpr ht1) ht0
    (by ring)
  convert this using 1
  show P.v i + t • P.d i = _
  rw [d, smul_sub, sub_smul, one_smul]; abel

lemma near_rect {r : ℝ} {i : Fin m} {x : E2} (hx : x ∈ P.rect r i) :
    P.IsNear (P.foot i x) x := by
  refine ⟨P.foot_mem hx, fun y hy => ?_⟩
  rw [sub_foot, inner_smul_left]
  have hb := hx.2.2.1
  have : inner ℝ (rotR (P.d i)) (y - P.foot i x) = - cross (P.d i) (y - P.v i) := by
    rw [inner_rotR]
    simp only [foot]
    rw [show y - (P.v i + (inner ℝ (x - P.v i) (P.d i) / ‖P.d i‖ ^ 2) • P.d i) =
      (y - P.v i) - (inner ℝ (x - P.v i) (P.d i) / ‖P.d i‖ ^ 2) • P.d i by abel,
      cross_sub_right, cross_smul_right, cross_self, mul_zero, sub_zero]
  rw [this]
  simp only [conj_trivial]
  have := hy i
  have : 0 ≤ inner ℝ (x - P.v i) (rotR (P.d i)) / ‖P.d i‖ ^ 2 :=
    div_nonneg hb.le (P.sq_len_pos i).le
  nlinarith

lemma near_sector {r : ℝ} {i : Fin m} {x : E2} (hx : x ∈ P.sector r i) :
    P.IsNear (P.v i) x :=
  ⟨P.vertex_mem i, fun _ hy => P.inner_le_of_cone hx.1.1.le hx.1.2 hy⟩

/-! ## Disjointness -/

lemma rect_not_mem_K {r : ℝ} {i : Fin m} {x : E2} (hx : x ∈ P.rect r i) : x ∉ P.K := by
  intro hK
  have := hK i
  have hb := hx.2.2.1
  rw [inner_rotR'] at hb
  linarith

lemma sector_not_mem_K {r : ℝ} {i : Fin m} {x : E2} (hx : x ∈ P.sector r i) : x ∉ P.K := by
  intro hK
  have := IsNear.eq_of_mem P (P.near_sector hx) hK
  have h := hx.1.1
  rw [this, sub_self, inner_zero_left] at h
  exact lt_irrefl _ h

lemma inner_sub_foot_d (i : Fin m) (x : E2) : inner ℝ (x - P.foot i x) (P.d i) = 0 := by
  rw [sub_foot, inner_smul_left, inner_rotR, cross_self]; simp

lemma rect_disjoint {r : ℝ} {i j : Fin m} (hij : i ≠ j) : Disjoint (P.rect r i) (P.rect r j) := by
  rw [Set.disjoint_left]
  intro x hi hj
  have hp := IsNear.unique P (P.near_rect hi) (P.near_rect hj)
  set p := P.foot i x
  have hwi := P.inner_sub_foot_d i x
  have hwj := P.inner_sub_foot_d j x
  rw [← hp] at hwj
  have hw : x - p ≠ 0 := by
    intro h
    have e := P.sub_foot i x
    rw [show x - P.foot i x = x - p from rfl, h] at e
    rcases smul_eq_zero.mp e.symm with h' | h'
    · have := div_pos hi.2.2.1 (P.sq_len_pos i); linarith
    · exact P.d_ne_zero i (by rw [← norm_eq_zero, ← norm_rotR, h', norm_zero])
  have hcross : cross (P.d i) (P.d j) = 0 := by
    by_contra hc
    exact hw (eq_zero_of_inner hc hwi hwj)
  -- the two feet coincide, so `vⱼ - vᵢ` is parallel to `dᵢ`
  have hpi : p - P.v i = (inner ℝ (x - P.v i) (P.d i) / ‖P.d i‖ ^ 2) • P.d i := by
    simp only [p, foot]; abel
  have hpj : p - P.v j = (inner ℝ (x - P.v j) (P.d j) / ‖P.d j‖ ^ 2) • P.d j := by
    rw [hp]; simp only [foot]; abel
  have h1 : cross (P.d i) (P.v j - P.v i) = 0 := by
    rw [show P.v j - P.v i = (p - P.v i) - (p - P.v j) by abel, hpi, hpj, cross_sub_right,
      cross_smul_right, cross_smul_right, cross_self, hcross]; ring
  have h2 : cross (P.d j) (P.v i - P.v j) = 0 := by
    rw [show P.v i - P.v j = (p - P.v j) - (p - P.v i) by abel, hpi, hpj, cross_sub_right,
      cross_smul_right, cross_smul_right, cross_self, cross_anti, hcross]; ring
  rcases P.mem_edge_line h1 with e | e
  · exact hij e.symm
  rcases P.mem_edge_line h2 with e' | e'
  · exact hij e'
  rw [e] at e'
  exact P.succ_succ_ne i e'.symm

lemma rect_sector_disjoint {r : ℝ} (i j : Fin m) :
    Disjoint (P.rect r i) (P.sector r j) := by
  rw [Set.disjoint_left]
  intro x hi hj
  have hp := IsNear.unique P (P.near_rect hi) (P.near_sector hj)
  have hpi : P.v j - P.v i = (inner ℝ (x - P.v i) (P.d i) / ‖P.d i‖ ^ 2) • P.d i := by
    rw [← hp]; simp only [foot]; abel
  have h1 : cross (P.d i) (P.v j - P.v i) = 0 := by
    rw [hpi, cross_smul_right, cross_self, mul_zero]
  rcases P.mem_edge_line h1 with e | e
  · subst e
    exact absurd hi.1 (not_le.mpr hj.1.1)
  · subst e
    have hL := P.sq_len_pos i
    have : (1 - inner ℝ (x - P.v i) (P.d i) / ‖P.d i‖ ^ 2) • P.d i = 0 := by
      rw [sub_smul, one_smul, ← hpi]; simp [d]
    rcases smul_eq_zero.mp this with h | h
    · have : inner ℝ (x - P.v i) (P.d i) = ‖P.d i‖ ^ 2 := by
        rw [sub_eq_zero, eq_div_iff hL.ne'] at h; linarith
      exact absurd this (ne_of_lt hi.2.1)
    · exact P.d_ne_zero i h

lemma sector_disjoint {r : ℝ} {i j : Fin m} (hij : i ≠ j) :
    Disjoint (P.sector r i) (P.sector r j) := by
  rw [Set.disjoint_left]
  intro x hi hj
  exact hij (P.v_injective (IsNear.unique P (P.near_sector hi) (P.near_sector hj)))

lemma K_rect_disjoint (r : ℝ) (i : Fin m) : Disjoint P.K (P.rect r i) :=
  Set.disjoint_left.mpr fun _ hK hx => P.rect_not_mem_K hx hK

lemma K_sector_disjoint (r : ℝ) (i : Fin m) : Disjoint P.K (P.sector r i) :=
  Set.disjoint_left.mpr fun _ hK hx => P.sector_not_mem_K hx hK

/-! ## Covering -/

lemma eq_d_of_line {i : Fin m} {u : E2} (hl : cross (P.d i) u = 0)
    (hs : inner ℝ u (P.d i) = ‖P.d i‖ ^ 2) : u = P.d i := by
  have hdec := decomp (P.d i) u
  rw [inner_rotR', hl, neg_zero, zero_smul, add_zero, hs] at hdec
  exact smul_right_injective E2 (P.sq_len_pos i).ne' hdec

lemma mem_body_iff {r : ℝ} {x : E2} : x ∈ P.body r ↔ ∃ y ∈ P.K, ‖x - y‖ ≤ r := by
  constructor
  · rintro ⟨y, hy, z, hz, rfl⟩
    exact ⟨y, hy, by simpa using hz⟩
  · rintro ⟨y, hy, h⟩
    exact ⟨y, hy, x - y, by simpa using h, add_sub_cancel y x⟩

lemma rect_subset_body {r : ℝ} (i : Fin m) : P.rect r i ⊆ P.body r := by
  intro x hx
  rw [mem_body_iff]
  refine ⟨P.foot i x, P.foot_mem hx, ?_⟩
  rw [sub_foot, norm_smul, norm_rotR, Real.norm_eq_abs,
    abs_of_pos (div_pos hx.2.2.1 (P.sq_len_pos i))]
  have hL := P.len_pos i
  unfold len at hL
  rw [div_mul_eq_mul_div, div_le_iff₀ (P.sq_len_pos i)]
  nlinarith [hx.2.2.2]

lemma sector_subset_body {r : ℝ} (i : Fin m) : P.sector r i ⊆ P.body r := fun _ hx =>
  (P.mem_body_iff).mpr ⟨P.v i, P.vertex_mem i, hx.2⟩

lemma K_subset_body {r : ℝ} (hr : 0 ≤ r) : P.K ⊆ P.body r := fun x hx =>
  (P.mem_body_iff).mpr ⟨x, hx, by simpa using hr⟩

lemma inner_rotR_le {w : E2} {r : ℝ} (hw : ‖w‖ ≤ r) (j : Fin m) :
    inner ℝ w (rotR (P.d j)) ≤ r * ‖P.d j‖ := by
  calc inner ℝ w (rotR (P.d j)) ≤ ‖w‖ * ‖rotR (P.d j)‖ := real_inner_le_norm _ _
    _ = ‖w‖ * ‖P.d j‖ := by rw [norm_rotR]
    _ ≤ r * ‖P.d j‖ := mul_le_mul_of_nonneg_right hw (norm_nonneg _)

/-- **Covering**: every point of the parallel body lies in `K`, in an edge
rectangle, or in a vertex sector. -/
lemma body_subset (r : ℝ) :
    P.body r ⊆ P.K ∪ ((⋃ i, P.rect r i) ∪ ⋃ i, P.sector r i) := by
  intro x hx
  by_cases hK : x ∈ P.K
  · exact Or.inl hK
  right
  obtain ⟨y, hy, hxy⟩ := (P.mem_body_iff).mp hx
  obtain ⟨p, hp⟩ := P.exists_near x
  have hwr : ‖x - p‖ ≤ r := (IsNear.norm_le P hp hy).trans hxy
  set w := x - p with hwdef
  have hw0 : w ≠ 0 := fun h => hK (by rw [sub_eq_zero.mp h]; exact hp.1)
  obtain ⟨k, -, hk⟩ := Finset.exists_max_image univ (fun j => inner ℝ w (P.v j)) univ_nonempty
  have h1 : inner ℝ w (P.d k) ≤ 0 := by
    rw [d, inner_sub_right]; linarith [hk (k + 1) (mem_univ _)]
  have h2 : 0 ≤ inner ℝ w (P.d (k - 1)) := by
    rw [d_pred, inner_sub_right]; linarith [hk (k - 1) (mem_univ _)]
  set u := p - P.v k with hudef
  have hu0 : inner ℝ w u = 0 := by
    refine le_antisymm (P.inner_le_of_cone h1 h2 hp.1) ?_
    have := hp.2 (P.v k) (P.vertex_mem k)
    rw [show P.v k - p = -u by rw [hudef]; abel, inner_neg_right] at this
    linarith
  have hc := P.cross_d_pos k
  have hLg := lagrange (P.d (k - 1)) (P.d k) w u
  have ha : 0 ≤ cross (P.d (k - 1)) u := by
    have := hp.1 (k - 1)
    rwa [show p - P.v (k - 1) = u + P.d (k - 1) by rw [hudef, d_pred]; abel,
      cross_add_right, cross_self, add_zero] at this
  have hb : 0 ≤ cross (P.d k) u := hp.1 k
  rw [hu0, mul_zero] at hLg
  have hA : inner ℝ w (P.d k) * cross (P.d (k - 1)) u = 0 := by
    nlinarith [mul_nonpos_of_nonpos_of_nonneg h1 ha, mul_nonneg h2 hb]
  have hB : inner ℝ w (P.d (k - 1)) * cross (P.d k) u = 0 := by
    nlinarith [mul_nonpos_of_nonpos_of_nonneg h1 ha, mul_nonneg h2 hb]
  have hxv : x - P.v k = w + u := by rw [hwdef, hudef]; abel
  -- the vertex case
  have vert : inner ℝ w (P.d k) < 0 → u = 0 → x ∈ (⋃ i, P.rect r i) ∪ ⋃ i, P.sector r i := by
    intro hlt hu
    rw [hu, add_zero] at hxv
    refine Or.inr (Set.mem_iUnion.mpr ⟨k, ⟨?_, ?_⟩, ?_⟩)
    · rw [hxv]; exact hlt
    · rw [hxv]; exact h2
    · rw [hxv]; exact hwr
  rcases h1.lt_or_eq with h1' | h1'
  · have hla : cross (P.d (k - 1)) u = 0 := (mul_eq_zero.mp hA).resolve_left h1'.ne
    rcases h2.lt_or_eq with h2' | h2'
    · have hlb : cross (P.d k) u = 0 := (mul_eq_zero.mp hB).resolve_left h2'.ne'
      exact vert h1' (eq_zero_of_cross hc.ne' hla hlb)
    · -- `p` lies on the line of edge `k - 1`
      set j := k - 1 with hj
      have hpj : p - P.v j = u + P.d j := by rw [hudef, hj, d_pred]; abel
      have hline : cross (P.d j) (p - P.v j) = 0 := by
        rw [hpj, cross_add_right, cross_self, add_zero]; exact hla
      obtain ⟨s0, s1⟩ := P.edge_of_line hp.1 hline
      rcases s1.lt_or_eq with s1' | s1'
      · refine Or.inl (Set.mem_iUnion.mpr ⟨j, ?_, ?_, ?_, ?_⟩)
        · rw [show x - P.v j = w + (p - P.v j) by rw [hwdef]; abel, inner_add_left,
            ← h2', zero_add]; exact s0
        · rw [show x - P.v j = w + (p - P.v j) by rw [hwdef]; abel, inner_add_left,
            ← h2', zero_add]; exact s1'
        · rw [show x - P.v j = w + (p - P.v j) by rw [hwdef]; abel, inner_add_left,
            inner_rotR' (p - P.v j), hline, neg_zero, add_zero]
          have hL2 := lagrange (P.d (k - 1)) (P.d k) w (rotR (P.d (k - 1)))
          rw [cross_rotR_self, ← h2', zero_mul, sub_zero] at hL2
          have := P.sq_len_pos (k - 1)
          by_contra hcon; push Not at hcon
          nlinarith [mul_nonpos_of_nonneg_of_nonpos hc.le hcon, mul_pos (neg_pos.mpr h1') this]
        · rw [show x - P.v j = w + (p - P.v j) by rw [hwdef]; abel, inner_add_left,
            inner_rotR' (p - P.v j), hline, neg_zero, add_zero]
          exact P.inner_rotR_le hwr j
      · have hpd := P.eq_d_of_line hline s1'
        apply vert h1'
        rw [hpd] at hpj
        have : u = 0 := by
          have := congrArg (· - P.d j) hpj; simpa using this.symm
        exact this
  · -- `⟪w, dₖ⟫ = 0`
    have h2' : 0 < inner ℝ w (P.d (k - 1)) := by
      rcases h2.lt_or_eq with h | h
      · exact h
      · exact absurd (eq_zero_of_inner hc.ne' h.symm h1') hw0
    have hlb : cross (P.d k) u = 0 := (mul_eq_zero.mp hB).resolve_left h2'.ne'
    obtain ⟨s0, s1⟩ := P.edge_of_line hp.1 hlb
    rcases s1.lt_or_eq with s1' | s1'
    · refine Or.inl (Set.mem_iUnion.mpr ⟨k, ?_, ?_, ?_, ?_⟩)
      · rw [hxv, inner_add_left, h1', zero_add]; exact s0
      · rw [hxv, inner_add_left, h1', zero_add]; exact s1'
      · rw [hxv, inner_add_left, inner_rotR' u, hlb, neg_zero, add_zero]
        have hL2 := lagrange (P.d (k - 1)) (P.d k) w (rotR (P.d k))
        rw [cross_rotR_self, h1', zero_mul, zero_sub] at hL2
        have := P.sq_len_pos k
        by_contra hcon; push Not at hcon
        nlinarith [mul_nonpos_of_nonneg_of_nonpos hc.le hcon, mul_pos h2' this]
      · rw [hxv, inner_add_left, inner_rotR' u, hlb, neg_zero, add_zero]
        exact P.inner_rotR_le hwr k
    · -- `p = v_{k+1}`
      have hud := P.eq_d_of_line hlb s1'
      have hp1 : p = P.v (k + 1) := by
        have := hud; rw [hudef, d] at this
        exact sub_left_injective this
      have hxv1 : x - P.v (k + 1) = w := by rw [hwdef, hp1]
      have h3 : inner ℝ w (P.d (k + 1)) ≤ 0 := by
        have := hp.2 (P.v (k + 1 + 1)) (P.vertex_mem _)
        rwa [hp1, ← d, ← hp1] at this
      have h3' : inner ℝ w (P.d (k + 1)) < 0 := by
        rcases h3.lt_or_eq with h | h
        · exact h
        · exact absurd (eq_zero_of_inner (P.cross_d_succ_pos k).ne' h1' h) hw0
      refine Or.inr (Set.mem_iUnion.mpr ⟨k + 1, ⟨?_, ?_⟩, ?_⟩)
      · rw [hxv1]; exact h3'
      · rw [hxv1, add_sub_cancel_right, h1']
      · rw [hxv1]; exact hwr

/-- **Decomposition of the parallel body.** -/
lemma body_eq {r : ℝ} (hr : 0 ≤ r) :
    P.body r = P.K ∪ ((⋃ i, P.rect r i) ∪ ⋃ i, P.sector r i) := by
  refine (P.body_subset r).antisymm (Set.union_subset (P.K_subset_body hr)
    (Set.union_subset ?_ ?_))
  · exact Set.iUnion_subset fun i => P.rect_subset_body i
  · exact Set.iUnion_subset fun i => P.sector_subset_body i

/-! ## The normal cones tile the plane -/

include P in
lemma pred_pred_ne (i : Fin m) : i - 1 - 1 ≠ i := by
  intro h; apply P.two_ne_zero'
  have e : (1 + 1 : Fin m) = i - (i - 1 - 1) := by abel
  rw [e, h, sub_self]

lemma cone_pred {w : E2} {i j : Fin m} (hi : w ∈ P.cone i) (hj : w ∈ P.cone j) (hij : i ≠ j) :
    j = i - 1 := by
  have a := P.inner_le_of_cone hi.1.le hi.2 (P.vertex_mem j)
  have b := P.inner_le_of_cone hj.1.le hj.2 (P.vertex_mem i)
  have e : inner ℝ w (P.v j - P.v i) = 0 := by
    rw [show P.v i - P.v j = -(P.v j - P.v i) by abel, inner_neg_right] at b
    linarith
  have hL := lagrange (P.d (i - 1)) (P.d i) w (P.v j - P.v i)
  have ha : 0 ≤ cross (P.d (i - 1)) (P.v j - P.v i) := by
    have := P.vertex_mem j (i - 1)
    rwa [show P.v j - P.v (i - 1) = (P.v j - P.v i) + P.d (i - 1) by rw [d_pred]; abel,
      cross_add_right, cross_self, add_zero] at this
  have hb : 0 ≤ cross (P.d i) (P.v j - P.v i) := P.vertex_mem j i
  rw [e, mul_zero] at hL
  have hA : cross (P.d (i - 1)) (P.v j - P.v i) = 0 := by
    have : inner ℝ w (P.d i) * cross (P.d (i - 1)) (P.v j - P.v i) = 0 := by
      nlinarith [mul_nonpos_of_nonpos_of_nonneg hi.1.le ha, mul_nonneg hi.2 hb]
    exact (mul_eq_zero.mp this).resolve_left hi.1.ne
  have hl : cross (P.d (i - 1)) (P.v j - P.v (i - 1)) = 0 := by
    rwa [show P.v j - P.v (i - 1) = (P.v j - P.v i) + P.d (i - 1) by rw [d_pred]; abel,
      cross_add_right, cross_self, add_zero]
  rcases P.mem_edge_line hl with h | h
  · exact h
  · rw [sub_add_cancel] at h; exact absurd h.symm hij

lemma cone_disjoint {i j : Fin m} (hij : i ≠ j) : Disjoint (P.cone i) (P.cone j) := by
  rw [Set.disjoint_left]
  intro w hi hj
  have h1 := P.cone_pred hi hj hij
  have h2 := P.cone_pred hj hi (Ne.symm hij)
  rw [h1] at h2
  exact P.pred_pred_ne i h2.symm

lemma cone_cover {w : E2} (hw : w ≠ 0) : ∃ i, w ∈ P.cone i := by
  obtain ⟨k, -, hk⟩ := Finset.exists_max_image univ (fun j => inner ℝ w (P.v j)) univ_nonempty
  have h1 : inner ℝ w (P.d k) ≤ 0 := by
    rw [d, inner_sub_right]; linarith [hk (k + 1) (mem_univ _)]
  have h2 : 0 ≤ inner ℝ w (P.d (k - 1)) := by
    rw [d_pred, inner_sub_right]; linarith [hk (k - 1) (mem_univ _)]
  rcases h1.lt_or_eq with h | h
  · exact ⟨k, h, h2⟩
  · refine ⟨k + 1, ?_, by rw [add_sub_cancel_right, h]⟩
    have h3 : inner ℝ w (P.d (k + 1)) ≤ 0 := by
      have := hk (k + 1 + 1) (mem_univ _)
      have e : inner ℝ w (P.v (k + 1)) = inner ℝ w (P.v k) := by
        have := h; rw [d, inner_sub_right] at this; linarith
      rw [d, inner_sub_right]; linarith
    rcases h3.lt_or_eq with h' | h'
    · exact h'
    · exact absurd (eq_zero_of_inner (P.cross_d_succ_pos k).ne' h h') hw

lemma zero_not_mem_cone (i : Fin m) : (0 : E2) ∉ P.cone i := fun h => by
  have := h.1; simp at this

lemma iUnion_cone_ball (r : ℝ) :
    (⋃ i, P.cone i ∩ closedBall (0 : E2) r) = closedBall (0 : E2) r \ {0} := by
  ext w
  simp only [Set.mem_iUnion, Set.mem_inter_iff, Set.mem_sdiff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨i, hi, hb⟩
    exact ⟨hb, fun h => P.zero_not_mem_cone i (h ▸ hi)⟩
  · rintro ⟨hb, h0⟩
    obtain ⟨i, hi⟩ := P.cone_cover h0
    exact ⟨i, hi, hb⟩

/-! ## Volumes -/

lemma measurable_inner_sub (c a : E2) : Measurable fun x : E2 => inner ℝ (x - c) a :=
  Continuous.measurable (by fun_prop)

lemma measurableSet_rect (r : ℝ) (i : Fin m) : MeasurableSet (P.rect r i) := by
  have e : P.rect r i = {x | 0 ≤ inner ℝ (x - P.v i) (P.d i)} ∩
      ({x | inner ℝ (x - P.v i) (P.d i) < ‖P.d i‖ ^ 2} ∩
      ({x | 0 < inner ℝ (x - P.v i) (rotR (P.d i))} ∩
      {x | inner ℝ (x - P.v i) (rotR (P.d i)) ≤ r * ‖P.d i‖})) := by
    ext x; simp [rect]
  rw [e]
  exact (measurableSet_le measurable_const (measurable_inner_sub _ _)).inter
    ((measurableSet_lt (measurable_inner_sub _ _) measurable_const).inter
    ((measurableSet_lt measurable_const (measurable_inner_sub _ _)).inter
    (measurableSet_le (measurable_inner_sub _ _) measurable_const)))

lemma measurableSet_cone (i : Fin m) : MeasurableSet (P.cone i) := by
  have e : P.cone i = {w | inner ℝ w (P.d i) < 0} ∩ {w | 0 ≤ inner ℝ w (P.d (i - 1))} := by
    ext; simp [cone]
  rw [e]
  have h1 : Measurable fun w : E2 => inner ℝ w (P.d i) := Continuous.measurable (by fun_prop)
  have h2 : Measurable fun w : E2 => inner ℝ w (P.d (i - 1)) :=
    Continuous.measurable (by fun_prop)
  exact (measurableSet_lt h1 measurable_const).inter (measurableSet_le measurable_const h2)

lemma sector_eq_preimage (r : ℝ) (i : Fin m) :
    P.sector r i = (fun x => x + -P.v i) ⁻¹' (P.cone i ∩ closedBall (0 : E2) r) := by
  ext x; simp [sector, sub_eq_add_neg, dist_eq_norm]

lemma measurableSet_sector (r : ℝ) (i : Fin m) : MeasurableSet (P.sector r i) := by
  rw [sector_eq_preimage]
  exact ((P.measurableSet_cone i).inter measurableSet_closedBall).preimage
    (measurable_id.add_const _)

lemma volume_sector (r : ℝ) (i : Fin m) :
    volume (P.sector r i) = volume (P.cone i ∩ closedBall (0 : E2) r) := by
  rw [sector_eq_preimage, measure_preimage_add_right]

/-- The sectors, translated to the origin, tile the closed disc. -/
lemma sum_volume_sector (r : ℝ) :
    ∑ i, volume (P.sector r i) = ENNReal.ofReal r ^ 2 * ENNReal.ofReal Real.pi := by
  simp_rw [volume_sector]
  have h := measure_iUnion (μ := volume) (f := fun i => P.cone i ∩ closedBall (0 : E2) r)
    (fun i j hij => (P.cone_disjoint hij).mono Set.inter_subset_left Set.inter_subset_left)
    (fun i => (P.measurableSet_cone i).inter measurableSet_closedBall)
  rw [tsum_fintype] at h
  rw [← h, iUnion_cone_ball, measure_sdiff_null (measure_singleton _),
    EuclideanSpace.volume_closedBall_fin_two]

/-- The volume of the edge rectangle is `ℓᵢ r`. -/
lemma volume_rect (r : ℝ) (i : Fin m) :
    volume (P.rect r i) = ENNReal.ofReal (P.len i * r) := by
  set dd := P.d i
  set L := ‖dd‖
  have hL : 0 < L := P.len_pos i
  set R0 : Set E2 := {u | 0 ≤ inner ℝ u dd ∧ inner ℝ u dd < L ^ 2 ∧
    0 < inner ℝ u (rotR dd) ∧ inner ℝ u (rotR dd) ≤ r * L}
  have e1 : P.rect r i = (fun x => x + -P.v i) ⁻¹' R0 := by
    ext x; simp [rect, R0, sub_eq_add_neg, dd, L]
  have hR0 : MeasurableSet R0 := by
    have : MeasurableSet ((fun x => x + -P.v i) ⁻¹' R0) := e1 ▸ P.measurableSet_rect r i
    have e2 : R0 = (fun x => x + P.v i) ⁻¹' ((fun x => x + -P.v i) ⁻¹' R0) := by
      ext x; simp
    rw [e2]; exact this.preimage (measurable_id.add_const _)
  rw [e1, measure_preimage_add_right]
  -- transfer to `Fin 2 → ℝ`
  rw [← (PiLp.volume_preserving_toLp (Fin 2)).measure_preimage hR0.nullMeasurableSet]
  set M : Matrix (Fin 2) (Fin 2) ℝ := !![dd 0, dd 1; dd 1, -dd 0]
  set box : Set (Fin 2 → ℝ) := Set.pi Set.univ ![Set.Ico 0 (L ^ 2), Set.Ioc 0 (r * L)]
  have e3 : (WithLp.toLp 2 : (Fin 2 → ℝ) → E2) ⁻¹' R0 = (Matrix.toLin' M) ⁻¹' box := by
    ext y
    simp only [Set.mem_preimage, R0, box, Set.mem_pi, Set.mem_univ, true_implies,
      Fin.forall_fin_two, Matrix.toLin'_apply, Matrix.mulVec, dotProduct, M,
      Fin.sum_univ_two, inner_eq, rotR_apply_zero, rotR_apply_one, Set.mem_ofPred_eq]
    simp [Set.mem_Ico, Set.mem_Ioc]
    constructor
    · rintro ⟨a, b, c, d⟩; refine ⟨⟨by linarith, by linarith⟩, by linarith, by linarith⟩
    · rintro ⟨⟨a, b⟩, c, d⟩; refine ⟨by linarith, by linarith, by linarith, by linarith⟩
  have hdet : LinearMap.det (Matrix.toLin' M) = -L ^ 2 := by
    rw [LinearMap.det_toLin', Matrix.det_fin_two_of]
    have := norm_sq_eq dd
    simp only [L] at this ⊢
    rw [this]; ring
  have hdet0 : LinearMap.det (Matrix.toLin' M) ≠ 0 := by
    rw [hdet]; exact neg_ne_zero.mpr (pow_pos hL 2).ne'
  rw [e3, MeasureTheory.Measure.addHaar_preimage_linearMap _ hdet0, volume_pi_pi,
    Fin.prod_univ_two]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Real.volume_Ico, Real.volume_Ioc,
    sub_zero, hdet]
  rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (abs_nonneg _)]
  congr 1
  rw [abs_inv, abs_neg, abs_of_pos (pow_pos hL 2)]
  simp only [len, dd, L]
  field_simp

/-- **Steiner formula for convex polygons.** For every `r ≥ 0`,
`vol(K + B̄(0,r)) = vol K + P r + π r²`. -/
theorem steiner {r : ℝ} (hr : 0 ≤ r) :
    volume (P.body r) =
      volume P.K + ENNReal.ofReal (P.perimeter * r) + ENNReal.ofReal (Real.pi * r ^ 2) := by
  rw [P.body_eq hr]
  have hU1 : MeasurableSet (⋃ i, P.rect r i) := MeasurableSet.iUnion (P.measurableSet_rect r)
  have hU2 : MeasurableSet (⋃ i, P.sector r i) :=
    MeasurableSet.iUnion (P.measurableSet_sector r)
  rw [measure_union _ (hU1.union hU2), measure_union _ hU2, measure_iUnion, measure_iUnion,
    tsum_fintype, tsum_fintype, sum_volume_sector]
  · simp_rw [P.volume_rect r]
    rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ => mul_nonneg (P.len_pos i).le hr),
      ← Finset.sum_mul, add_assoc, ← ENNReal.ofReal_pow hr,
      ← ENNReal.ofReal_mul (by positivity)]
    simp only [perimeter]
    ring_nf
  · intro i j hij; exact P.sector_disjoint hij
  · exact P.measurableSet_sector r
  · intro i j hij; exact P.rect_disjoint hij
  · exact P.measurableSet_rect r
  · rw [Set.disjoint_iUnion_left]
    intro i; rw [Set.disjoint_iUnion_right]; intro j
    exact P.rect_sector_disjoint i j
  · rw [Set.disjoint_union_right, Set.disjoint_iUnion_right, Set.disjoint_iUnion_right]
    exact ⟨fun i => P.K_rect_disjoint r i, fun i => P.K_sector_disjoint r i⟩

end ConvexPolygon

end

end QE.Polygon

/-!
# Pick's theorem for simple lattice polygons

Combinatorial (granular) interior via the winding number, gluing along diagonals,
and induction on the number of vertices. Lebesgue-free.
-/


/-!
# Pick's theorem: shared definitions

Lattice polygons, their boundary, the combinatorial winding number (rightward
horizontal ray, half-open rule), the shoelace sum, and the lattice counts.
-/

namespace QE.Pick

open Finset

/-- Points of the plane. -/
abbrev Pt := ℝ × ℝ

/-- Planar cross product. -/
def cross (a b : Pt) : ℝ := a.1 * b.2 - a.2 * b.1

/-- A lattice point as a point of the plane. -/
def toPt (q : ℤ × ℤ) : Pt := ((q.1 : ℝ), (q.2 : ℝ))

/-- Integer cross product. -/
def crossZ (a b : ℤ × ℤ) : ℤ := a.1 * b.2 - a.2 * b.1

/-- Strict lexicographic order on lattice points. -/
def lexlt (a b : ℤ × ℤ) : Prop := a.1 < b.1 ∨ (a.1 = b.1 ∧ a.2 < b.2)

/-- The closed segment `[a, b]`. -/
def seg (a b : Pt) : Set Pt := {p | ∃ t : ℝ, 0 ≤ t ∧ t ≤ 1 ∧ p = a + t • (b - a)}

/-- The closed triangle with vertices `a, b, c`. -/
def tri (a b c : Pt) : Set Pt :=
  {p | ∃ s t : ℝ, 0 ≤ s ∧ 0 ≤ t ∧ s + t ≤ 1 ∧ p = a + s • (b - a) + t • (c - a)}

/-- `d` lies strictly inside the (convex) cone spanned by the non-parallel vectors
`a` and `b`. -/
def inOpenCone (a b d : Pt) : Prop :=
  0 < cross a d * cross a b ∧ 0 < cross d b * cross a b

/-- Signed contribution of the oriented edge `a → b` to the winding number at `p`:
`+1` if the edge goes up across the rightward horizontal ray from `p`, `-1` if it
goes down, with the half-open rule `[low, high)` for the heights. -/
noncomputable def hit (a b p : Pt) : ℤ :=
  (if a.2 ≤ p.2 ∧ p.2 < b.2 ∧ 0 < cross (b - a) (p - a) then 1 else 0) -
  (if b.2 ≤ p.2 ∧ p.2 < a.2 ∧ cross (b - a) (p - a) < 0 then 1 else 0)

/-- A transversal direction to the segment `[a, b]`: vertical for horizontal
segments, horizontal otherwise. -/
noncomputable def transv (a b : Pt) : Pt := if a.2 = b.2 then (0, 1) else (1, 0)

/-- A closed lattice polygonal path (a cycle of `n` lattice vertices, indexed
periodically by `ℕ`). -/
structure Cycle where
  n : ℕ
  pos : 0 < n
  v : ℕ → ℤ × ℤ
  per : ∀ i, v (i + n) = v i

namespace Cycle

variable (C : Cycle)

/-- Vertex `i` as a point of the plane. -/
def V (i : ℕ) : Pt := toPt (C.v i)

/-- Edge `i`, the segment `[V i, V (i+1)]`. -/
def edge (i : ℕ) : Set Pt := seg (C.V i) (C.V (i + 1))

/-- The boundary: the union of the edges. -/
def bd : Set Pt := {p | ∃ i < C.n, p ∈ C.edge i}

/-- The combinatorial winding number of the cycle around `p`. -/
noncomputable def wind (p : Pt) : ℤ := ∑ i ∈ range C.n, hit (C.V i) (C.V (i + 1)) p

/-- Twice the signed area (shoelace sum). -/
def shoe : ℤ := ∑ i ∈ range C.n, crossZ (C.v i) (C.v (i + 1))

/-- The granular (combinatorial) interior: points off the boundary around which
the boundary winds. -/
def int : Set Pt := {p | p ∉ C.bd ∧ C.wind p ≠ 0}

lemma range_nonempty : (range C.n).Nonempty := ⟨0, by simp [C.pos]⟩

def xmin : ℤ := (range C.n).inf' C.range_nonempty (fun i => (C.v i).1)
def xmax : ℤ := (range C.n).sup' C.range_nonempty (fun i => (C.v i).1)
def ymin : ℤ := (range C.n).inf' C.range_nonempty (fun i => (C.v i).2)
def ymax : ℤ := (range C.n).sup' C.range_nonempty (fun i => (C.v i).2)

/-- The bounding box of the vertices, as a finite set of lattice points. -/
def box : Finset (ℤ × ℤ) := Icc C.xmin C.xmax ×ˢ Icc C.ymin C.ymax

/-- Number of lattice points on the boundary. -/
noncomputable def B : ℕ := by
  classical exact (C.box.filter (fun q => toPt q ∈ C.bd)).card

/-- Number of lattice points in the interior. -/
noncomputable def I : ℕ := by
  classical exact (C.box.filter (fun q => toPt q ∈ C.int)).card

/-- The rotated cycle `v r, v (r+1), …`. -/
def rot (r : ℕ) : Cycle where
  n := C.n
  pos := C.pos
  v := fun i => C.v (i + r)
  per := fun i => by rw [show i + C.n + r = (i + r) + C.n by ring, C.per]

/-- The sub-cycle `v 0, …, v k` (closed by the chord `v k → v 0`). -/
def left (k : ℕ) : Cycle where
  n := k + 1
  pos := Nat.succ_pos k
  v := fun i => C.v (i % (k + 1))
  per := fun i => by simp

/-- The sub-cycle `v k, …, v n = v 0` (closed by the chord `v 0 → v k`). -/
def right (k : ℕ) : Cycle where
  n := C.n - k + 1
  pos := Nat.succ_pos _
  v := fun i => C.v (k + i % (C.n - k + 1))
  per := fun i => by simp

end Cycle

/-- A simple closed lattice polygon: at least three distinct vertices, and two
distinct edges meet only in the common vertex of consecutive edges. -/
structure LPoly extends Cycle where
  three : 3 ≤ n
  inj : ∀ i j, i < n → j < n → v i = v j → i = j
  simple : ∀ i j, i < n → j < n → i ≠ j → ∀ p,
    p ∈ seg (toPt (v i)) (toPt (v (i + 1))) → p ∈ seg (toPt (v j)) (toPt (v (j + 1))) →
      (j = (i + 1) % n ∧ p = toPt (v (i + 1))) ∨ (i = (j + 1) % n ∧ p = toPt (v (j + 1)))

/-- Reachability inside a set `S` by finite chains of segments contained in `S`. -/
def Reach (S : Set Pt) : Pt → Pt → Prop := Relation.ReflTransGen (fun x y => seg x y ⊆ S)

end QE.Pick


namespace QE.Pick
open Finset

lemma wA_cross_sub (a b p : Pt) : cross (a - b) (p - b) = - cross (b - a) (p - a) := by
  simp only [cross, Prod.fst_sub, Prod.snd_sub]; ring

lemma wA_hit_swap (a b p : Pt) : hit b a p = - hit a b p := by
  unfold hit
  rw [wA_cross_sub]
  have h1 : (0 < -cross (b - a) (p - a)) ↔ cross (b - a) (p - a) < 0 := by constructor <;> intro h <;> linarith
  have h2 : (-cross (b - a) (p - a) < 0) ↔ 0 < cross (b - a) (p - a) := by constructor <;> intro h <;> linarith
  simp only [h1, h2]; ring

lemma wA_seg_symm (a b : Pt) : seg a b = seg b a := by
  ext x; simp only [seg, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨t, h0, h1, rfl⟩; exact ⟨1 - t, by linarith, by linarith, by ext <;> simp <;> ring⟩
  · rintro ⟨t, h0, h1, rfl⟩; exact ⟨1 - t, by linarith, by linarith, by ext <;> simp <;> ring⟩

lemma wA_seg_eq (a b : Pt) : seg a b = (fun θ : ℝ => a + θ • (b - a)) '' Set.Icc 0 1 := by
  ext x; simp only [seg, Set.mem_ofPred_eq, Set.mem_image, Set.mem_Icc]
  constructor
  · rintro ⟨t, h0, h1, rfl⟩; exact ⟨t, ⟨h0, h1⟩, rfl⟩
  · rintro ⟨t, ⟨h0, h1⟩, rfl⟩; exact ⟨t, h0, h1, rfl⟩

lemma wA_seg_closed (a b : Pt) : IsClosed (seg a b) := by
  rw [wA_seg_eq]
  exact (isCompact_Icc.image (by fun_prop)).isClosed

lemma wA_left_mem (a b : Pt) : a ∈ seg a b := ⟨0, le_refl _, zero_le_one, by simp⟩
lemma wA_right_mem (a b : Pt) : b ∈ seg a b := ⟨1, zero_le_one, le_refl _, by simp⟩


noncomputable def wA_str (a b : Pt) (y : ℝ) : ℤ := (if a.2 ≤ y then 1 else 0) - (if b.2 ≤ y then 1 else 0)

/-- the point of the line `ab` at height `y`. -/
noncomputable def wA_E (a b : Pt) (y : ℝ) : Pt := a + ((y - a.2) / (b.2 - a.2)) • (b - a)

lemma wA_E_snd {a b : Pt} (h : a.2 ≠ b.2) (y : ℝ) : (wA_E a b y).2 = y := by
  have : b.2 - a.2 ≠ 0 := sub_ne_zero.mpr (Ne.symm h)
  simp only [wA_E, Prod.snd_add, Prod.smul_snd, Prod.snd_sub, smul_eq_mul]
  field_simp; ring

lemma wA_E_mem {a b : Pt} (h : a.2 ≠ b.2) {y : ℝ} (h1 : min a.2 b.2 ≤ y) (h2 : y ≤ max a.2 b.2) :
    wA_E a b y ∈ seg a b := by
  refine ⟨(y - a.2) / (b.2 - a.2), ?_, ?_, rfl⟩
  · rcases lt_or_gt_of_ne h with h | h
    · rw [min_eq_left h.le] at h1; exact div_nonneg (by linarith) (by linarith)
    · rw [min_eq_right h.le] at h1; rw [max_eq_left h.le] at h2
      exact div_nonneg_of_nonpos (by linarith) (by linarith)
  · rcases lt_or_gt_of_ne h with h | h
    · rw [max_eq_right h.le] at h2; rw [div_le_one (by linarith)]; linarith
    · rw [min_eq_right h.le] at h1; rw [div_le_one_of_neg (by linarith)]; linarith

lemma wA_E_cross {a b : Pt} (h : a.2 ≠ b.2) (p : Pt) :
    cross (b - a) (p - a) = (b.2 - a.2) * ((wA_E a b p.2).1 - p.1) := by
  have : b.2 - a.2 ≠ 0 := sub_ne_zero.mpr (Ne.symm h)
  simp only [wA_E, cross, Prod.fst_add, Prod.smul_fst, Prod.fst_sub, Prod.snd_sub, smul_eq_mul]
  field_simp; ring

lemma wA_hit_ne_zero {a b p : Pt} (h : hit a b p ≠ 0) :
    ∃ x ∈ seg a b, x.2 = p.2 ∧ p.1 < x.1 := by
  unfold hit at h
  by_cases hab : a.2 = b.2
  · exfalso; apply h
    rw [if_neg (by rintro ⟨h1, h2, -⟩; linarith), if_neg (by rintro ⟨h1, h2, -⟩; linarith)]; simp
  refine ⟨wA_E a b p.2, ?_, wA_E_snd hab _, ?_⟩
  · by_cases c1 : a.2 ≤ p.2 ∧ p.2 < b.2
    · exact wA_E_mem hab (by simp [c1.1]) (by simp [c1.2.le])
    by_cases c2 : b.2 ≤ p.2 ∧ p.2 < a.2
    · exact wA_E_mem hab (by simp [c2.1]) (by simp [c2.2.le])
    exfalso; apply h
    rw [if_neg (by rintro ⟨h1, h2, -⟩; exact c1 ⟨h1, h2⟩), if_neg (by rintro ⟨h1, h2, -⟩; exact c2 ⟨h1, h2⟩)]
    simp
  · have hc := wA_E_cross hab p
    by_contra hx; push_neg at hx
    apply h
    rw [if_neg (by rintro ⟨h1, h2, h3⟩; rw [hc] at h3; nlinarith),
      if_neg (by rintro ⟨h1, h2, h3⟩; rw [hc] at h3; nlinarith)]; simp

lemma wA_hit_eq_str {a b p : Pt} (h : ∀ x ∈ seg a b, x.2 = p.2 → p.1 < x.1) :
    hit a b p = wA_str a b p.2 := by
  unfold hit wA_str
  by_cases hab : a.2 = b.2
  · rw [hab, if_neg, if_neg] <;> simp <;> intros <;> linarith
  have hc := wA_E_cross hab p
  by_cases c1 : a.2 ≤ p.2 ∧ p.2 < b.2
  · have hx := h _ (wA_E_mem hab (by simp [c1.1]) (by simp [c1.2.le])) (wA_E_snd hab _)
    rw [if_pos ⟨c1.1, c1.2, by rw [hc]; nlinarith⟩, if_neg (by rintro ⟨h1, h2, -⟩; linarith),
      if_pos c1.1, if_neg (by linarith)]
  by_cases c2 : b.2 ≤ p.2 ∧ p.2 < a.2
  · have hx := h _ (wA_E_mem hab (by simp [c2.1]) (by simp [c2.2.le])) (wA_E_snd hab _)
    rw [if_neg (by rintro ⟨h1, h2, -⟩; linarith), if_pos ⟨c2.1, c2.2, by rw [hc]; nlinarith⟩,
      if_neg (by linarith), if_pos c2.1]
  rw [if_neg (by rintro ⟨h1, h2, -⟩; exact c1 ⟨h1, h2⟩), if_neg (by rintro ⟨h1, h2, -⟩; exact c2 ⟨h1, h2⟩)]
  by_cases d1 : a.2 ≤ p.2 <;> by_cases d2 : b.2 ≤ p.2 <;> simp [d1, d2]
  all_goals first | exact (c1 ⟨d1, lt_of_not_ge d2⟩).elim | exact (c2 ⟨d2, lt_of_not_ge d1⟩).elim

/-- segment point between two points on a common row. -/
lemma wA_mem_seg_row {p q x : Pt} (h1 : p.2 = q.2) (h2 : x.2 = p.2) (h3 : min p.1 q.1 ≤ x.1)
    (h4 : x.1 ≤ max p.1 q.1) : x ∈ seg p q := by
  by_cases hpq : p.1 = q.1
  · refine ⟨0, le_refl _, zero_le_one, ?_⟩
    have : x.1 = p.1 := by rw [hpq, min_self] at h3; rw [hpq, max_self] at h4; rw [hpq]; linarith
    ext <;> simp [this, h2]
  refine ⟨(x.1 - p.1) / (q.1 - p.1), ?_, ?_, ?_⟩
  · rcases lt_or_gt_of_ne hpq with h | h
    · rw [min_eq_left h.le] at h3; exact div_nonneg (by linarith) (by linarith)
    · rw [min_eq_right h.le] at h3; rw [max_eq_left h.le] at h4
      exact div_nonneg_of_nonpos (by linarith) (by linarith)
  · rcases lt_or_gt_of_ne hpq with h | h
    · rw [max_eq_right h.le] at h4; rw [div_le_one (by linarith)]; linarith
    · rw [min_eq_right h.le] at h3; rw [div_le_one_of_neg (by linarith)]; linarith
  · have : q.1 - p.1 ≠ 0 := sub_ne_zero.mpr (Ne.symm hpq)
    ext
    · simp only [Prod.fst_add, Prod.smul_fst, Prod.fst_sub, smul_eq_mul]; field_simp; ring
    · simp only [Prod.snd_add, Prod.smul_snd, Prod.snd_sub, smul_eq_mul, h2, h1]; ring

lemma wA_hit_up {a b : Pt} (h : a.2 < b.2) (p : Pt) :
    hit a b p = if a.2 ≤ p.2 ∧ p.2 < b.2 ∧ 0 < cross (b - a) (p - a) then 1 else 0 := by
  unfold hit
  have : ¬(b.2 ≤ p.2 ∧ p.2 < a.2 ∧ cross (b - a) (p - a) < 0) := by
    rintro ⟨h1, h2, -⟩; linarith
  rw [if_neg this]; simp

lemma wA_hit_flat {a b : Pt} (h : a.2 = b.2) (p : Pt) : hit a b p = 0 := by
  unfold hit
  have h1 : ¬(b.2 ≤ p.2 ∧ p.2 < a.2 ∧ cross (b - a) (p - a) < 0) := by
    rintro ⟨h1, h2, -⟩; linarith
  have h2 : ¬(a.2 ≤ p.2 ∧ p.2 < b.2 ∧ 0 < cross (b - a) (p - a)) := by
    rintro ⟨h1, h2, -⟩; linarith
  rw [if_neg h1, if_neg h2]; simp

lemma wA_edge_row {a b p q : Pt} (hpq : p.2 = q.2) (hd : ∀ x ∈ seg p q, x ∉ seg a b) :
    hit a b p = hit a b q := by
  by_contra hne
  have key : ∀ a b : Pt, a.2 ≤ b.2 → (∀ x ∈ seg p q, x ∉ seg a b) → hit a b p ≠ hit a b q → False := by
    intro a b hab hd hne
    rcases eq_or_lt_of_le hab with hab' | hab'
    · exact hne (by rw [wA_hit_flat hab', wA_hit_flat hab'])
    apply hne
    rw [wA_hit_up hab', wA_hit_up hab', ← hpq]
    have hab'' : a.2 ≠ b.2 := hab'.ne
    have hc := wA_E_cross hab'' p
    have hc' := wA_E_cross hab'' q
    rw [← hpq] at hc'
    by_cases c1 : a.2 ≤ p.2 ∧ p.2 < b.2
    · have hm := wA_E_mem hab'' (y := p.2) (by simp [c1.1]) (by simp [c1.2.le])
      have hD : 0 < b.2 - a.2 := by linarith [c1.1, c1.2]
      set E := wA_E a b p.2
      have hE := wA_E_snd hab'' p.2
      rw [hc, hc']
      by_cases e1 : p.1 < E.1 <;> by_cases e2 : q.1 < E.1
      · rw [if_pos ⟨c1.1, c1.2, by nlinarith⟩, if_pos ⟨c1.1, c1.2, by nlinarith⟩]
      · exact (hd E (wA_mem_seg_row hpq hE (by simp; left; linarith) (by simp; right; linarith)) hm).elim
      · exact (hd E (wA_mem_seg_row hpq hE (by simp; right; linarith) (by simp; left; linarith)) hm).elim
      · rw [if_neg (by rintro ⟨-, -, h⟩; nlinarith), if_neg (by rintro ⟨-, -, h⟩; nlinarith)]
    · rw [if_neg (by rintro ⟨h1, h2, -⟩; exact c1 ⟨h1, h2⟩), if_neg (by rintro ⟨h1, h2, -⟩; exact c1 ⟨h1, h2⟩)]
  rcases le_total a.2 b.2 with h | h
  · exact key a b h hd hne
  · refine key b a h (by rw [wA_seg_symm b a]; exact hd) ?_
    rw [wA_hit_swap a b, wA_hit_swap a b]; intro h'; exact hne (neg_inj.mp h')

/-- indicator of the region `R` swept by the segment `pq`. -/
noncomputable def wA_ind (p q x : Pt) : ℤ :=
  if p.2 < x.2 ∧ x.2 ≤ q.2 ∧ cross (q - p) (x - p) < 0 then 1 else 0

lemma wA_no_zero {a b p q x : Pt} (hpq : p.2 < q.2) (hd : ∀ y ∈ seg p q, y ∉ seg a b)
    (hx : x ∈ seg a b) (h1 : p.2 ≤ x.2) (h2 : x.2 ≤ q.2) : cross (q - p) (x - p) ≠ 0 := by
  intro h0
  apply hd x _ hx
  have hD : q.2 - p.2 ≠ 0 := by linarith
  have hD' : 0 < q.2 - p.2 := by linarith
  refine ⟨(x.2 - p.2) / (q.2 - p.2), div_nonneg (by linarith) hD'.le,
    (div_le_one hD').mpr (by linarith), ?_⟩
  simp only [cross, Prod.fst_sub, Prod.snd_sub] at h0
  ext
  · simp only [Prod.fst_add, Prod.smul_fst, Prod.fst_sub, smul_eq_mul]
    field_simp; linarith
  · simp only [Prod.snd_add, Prod.smul_snd, Prod.snd_sub, smul_eq_mul]
    field_simp; ring

lemma wA_edge_up {a b p q : Pt} (hab : a.2 < b.2) (hpq : p.2 < q.2)
    (hd : ∀ y ∈ seg p q, y ∉ seg a b) :
    hit a b p - hit a b q = wA_ind p q b - wA_ind p q a := by
  set g : Pt → ℝ := fun x => cross (q - p) (x - p) with hg
  set H : ℝ → ℝ := fun y => (b.2 - y) * g a + (y - a.2) * g b with hH
  have Hp : H p.2 = -(q.2 - p.2) * cross (b - a) (p - a) := by
    simp only [hH, hg, cross, Prod.fst_sub, Prod.snd_sub]; ring
  have Hq : H q.2 = -(q.2 - p.2) * cross (b - a) (q - a) := by
    simp only [hH, hg, cross, Prod.fst_sub, Prod.snd_sub]; ring
  have Ha : H a.2 = (b.2 - a.2) * g a := by simp only [hH]; ring
  have Hb : H b.2 = (b.2 - a.2) * g b := by simp only [hH]; ring
  have hab' : a.2 ≠ b.2 := hab.ne
  have Hz : ∀ y, a.2 ≤ y → y ≤ b.2 → p.2 ≤ y → y ≤ q.2 → H y ≠ 0 := by
    intro y h1 h2 h3 h4 h0
    have hm := wA_E_mem hab' (y := y) (by simp [h1]) (by simp [h2])
    have he := wA_E_snd hab' y
    have key : g (wA_E a b y) * (b.2 - a.2) = H y := by
      have : b.2 - a.2 ≠ 0 := by linarith
      simp only [hH, hg, wA_E, cross, Prod.fst_sub, Prod.snd_sub, Prod.fst_add, Prod.snd_add,
        Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
      field_simp; ring
    exact wA_no_zero hpq hd hm (by rw [he]; exact h3) (by rw [he]; exact h4)
      (by have := key; rw [h0] at this; simpa [sub_ne_zero.mpr hab'.symm] using this)
  have Hcont : Continuous H := by simp only [hH]; fun_prop
  have Hs : ∀ y1 y2, a.2 ≤ y1 → y1 ≤ b.2 → p.2 ≤ y1 → y1 ≤ q.2 →
      a.2 ≤ y2 → y2 ≤ b.2 → p.2 ≤ y2 → y2 ≤ q.2 → H y1 < 0 → H y2 < 0 := by
    intro y1 y2 h1 h2 h3 h4 h5 h6 h7 h8 hy1
    by_contra hy2; push_neg at hy2
    have hmem : (0:ℝ) ∈ Set.uIcc (H y1) (H y2) := Set.mem_uIcc.mpr (Or.inl ⟨hy1.le, hy2⟩)
    obtain ⟨y, hy, hy0⟩ := intermediate_value_uIcc Hcont.continuousOn hmem
    rcases Set.mem_uIcc.mp hy with ⟨k1, k2⟩ | ⟨k1, k2⟩
    · exact Hz y (by linarith) (by linarith) (by linarith) (by linarith) hy0
    · exact Hz y (by linarith) (by linarith) (by linarith) (by linarith) hy0
  set c := max a.2 p.2 with hc
  have hJ : ∀ y, a.2 ≤ y → y ≤ b.2 → p.2 ≤ y → y ≤ q.2 → (H y < 0 ↔ H c < 0) := by
    intro y h1 h2 h3 h4
    have c1 : a.2 ≤ c := le_max_left _ _
    have c2 : p.2 ≤ c := le_max_right _ _
    have c3 : c ≤ y := max_le h1 h3
    exact ⟨Hs y c h1 h2 h3 h4 c1 (by linarith) c2 (by linarith),
      Hs c y c1 (by linarith) c2 (by linarith) h1 h2 h3 h4⟩
  have hqp : 0 < q.2 - p.2 := by linarith
  have i1 : (a.2 ≤ p.2 ∧ p.2 < b.2 ∧ 0 < cross (b - a) (p - a)) ↔
      (a.2 ≤ p.2 ∧ p.2 < b.2 ∧ H c < 0) := by
    constructor
    · rintro ⟨h1, h2, h3⟩
      refine ⟨h1, h2, (hJ p.2 h1 h2.le le_rfl hpq.le).mp ?_⟩
      rw [Hp]; nlinarith
    · rintro ⟨h1, h2, h3⟩
      refine ⟨h1, h2, ?_⟩
      have := (hJ p.2 h1 h2.le le_rfl hpq.le).mpr h3
      rw [Hp] at this; nlinarith
  have i2 : (a.2 ≤ q.2 ∧ q.2 < b.2 ∧ 0 < cross (b - a) (q - a)) ↔
      (a.2 ≤ q.2 ∧ q.2 < b.2 ∧ H c < 0) := by
    constructor
    · rintro ⟨h1, h2, h3⟩
      refine ⟨h1, h2, (hJ q.2 h1 h2.le hpq.le le_rfl).mp ?_⟩
      rw [Hq]; nlinarith
    · rintro ⟨h1, h2, h3⟩
      refine ⟨h1, h2, ?_⟩
      have := (hJ q.2 h1 h2.le hpq.le le_rfl).mpr h3
      rw [Hq] at this; nlinarith
  have hba : 0 < b.2 - a.2 := by linarith
  have i3 : (p.2 < b.2 ∧ b.2 ≤ q.2 ∧ cross (q - p) (b - p) < 0) ↔
      (p.2 < b.2 ∧ b.2 ≤ q.2 ∧ H c < 0) := by
    constructor
    · rintro ⟨h1, h2, h3⟩
      refine ⟨h1, h2, (hJ b.2 hab.le le_rfl h1.le h2).mp ?_⟩
      rw [Hb]; exact mul_neg_of_pos_of_neg hba h3
    · rintro ⟨h1, h2, h3⟩
      refine ⟨h1, h2, ?_⟩
      have := (hJ b.2 hab.le le_rfl h1.le h2).mpr h3
      rw [Hb] at this; by_contra hh; push_neg at hh; nlinarith
  have i4 : (p.2 < a.2 ∧ a.2 ≤ q.2 ∧ cross (q - p) (a - p) < 0) ↔
      (p.2 < a.2 ∧ a.2 ≤ q.2 ∧ H c < 0) := by
    constructor
    · rintro ⟨h1, h2, h3⟩
      refine ⟨h1, h2, (hJ a.2 le_rfl hab.le h1.le h2).mp ?_⟩
      rw [Ha]; exact mul_neg_of_pos_of_neg hba h3
    · rintro ⟨h1, h2, h3⟩
      refine ⟨h1, h2, ?_⟩
      have := (hJ a.2 le_rfl hab.le h1.le h2).mpr h3
      rw [Ha] at this; by_contra hh; push_neg at hh; nlinarith
  rw [wA_hit_up hab, wA_hit_up hab]
  unfold wA_ind
  simp only [i1, i2, i3, i4]
  have e1 : b.2 ≤ q.2 ↔ ¬ q.2 < b.2 := not_lt.symm
  have e2 : p.2 < a.2 ↔ ¬ a.2 ≤ p.2 := not_le.symm
  by_cases z : H c < 0 <;> simp only [z, and_true, and_false, if_false] <;>
    by_cases A1 : a.2 ≤ p.2 <;> by_cases A2 : p.2 < b.2 <;> by_cases A3 : a.2 ≤ q.2 <;>
    by_cases A4 : q.2 < b.2 <;> simp [e1, e2, A1, A2, A3, A4] <;> linarith

lemma wA_edge_flat {a b p q : Pt} (hab : a.2 = b.2) (hpq : p.2 < q.2)
    (hd : ∀ y ∈ seg p q, y ∉ seg a b) :
    hit a b p - hit a b q = wA_ind p q b - wA_ind p q a := by
  rw [wA_hit_flat hab, wA_hit_flat hab]
  unfold wA_ind
  rw [← hab]
  by_cases hh : p.2 < a.2 ∧ a.2 ≤ q.2
  · set φ : ℝ → ℝ := fun t => cross (q - p) (a + t • (b - a) - p) with hφ
    have hcont : Continuous φ := by simp only [hφ, cross]; fun_prop
    have hz : ∀ t, 0 ≤ t → t ≤ 1 → φ t ≠ 0 := by
      intro t h0 h1
      have hm : a + t • (b - a) ∈ seg a b := ⟨t, h0, h1, rfl⟩
      have h2 : (a + t • (b - a)).2 = a.2 := by simp [hab]
      exact wA_no_zero hpq hd hm (by rw [h2]; exact hh.1.le) (by rw [h2]; exact hh.2)
    have h0 : φ 0 = cross (q - p) (a - p) := by simp [hφ]
    have h1 : φ 1 = cross (q - p) (b - p) := by simp [hφ]
    have key : φ 0 < 0 ↔ φ 1 < 0 := by
      constructor
      · intro h; by_contra h'; push_neg at h'
        obtain ⟨t, ht, ht0⟩ := intermediate_value_uIcc (a := (0:ℝ)) (b := 1) hcont.continuousOn
          (Set.mem_uIcc.mpr (Or.inl ⟨h.le, h'⟩))
        rw [Set.uIcc_of_le zero_le_one] at ht
        exact hz t ht.1 ht.2 ht0
      · intro h; by_contra h'; push_neg at h'
        obtain ⟨t, ht, ht0⟩ := intermediate_value_uIcc (a := (0:ℝ)) (b := 1) hcont.continuousOn
          (Set.mem_uIcc.mpr (Or.inr ⟨h.le, h'⟩))
        rw [Set.uIcc_of_le zero_le_one] at ht
        exact hz t ht.1 ht.2 ht0
    rw [h0, h1] at key
    simp only [hh, true_and, key, sub_self]
  · simp only [← and_assoc, hh, false_and, if_false]

lemma wA_edge {a b p q : Pt} (hpq : p.2 < q.2) (hd : ∀ y ∈ seg p q, y ∉ seg a b) :
    hit a b p - hit a b q = wA_ind p q b - wA_ind p q a := by
  rcases lt_trichotomy a.2 b.2 with h | h | h
  · exact wA_edge_up h hpq hd
  · exact wA_edge_flat h hpq hd
  · have := wA_edge_up h hpq (by rw [wA_seg_symm b a]; exact hd)
    rw [wA_hit_swap a b, wA_hit_swap a b] at this; linarith

lemma wA_seg_param {a b x : Pt} (hx : x ∈ seg a b) :
    ∃ t : ℝ, 0 ≤ t ∧ t ≤ 1 ∧ x.1 = a.1 + t * (b.1 - a.1) ∧ x.2 = a.2 + t * (b.2 - a.2) := by
  obtain ⟨t, h0, h1, rfl⟩ := hx
  exact ⟨t, h0, h1, by simp, by simp⟩

lemma wA_lex_seg {a b p x : Pt} (ha : p.1 < a.1 ∨ (p.1 = a.1 ∧ p.2 < a.2))
    (hb : p.1 < b.1 ∨ (p.1 = b.1 ∧ p.2 < b.2)) (hx : x ∈ seg a b) (hx2 : x.2 = p.2) :
    p.1 < x.1 := by
  obtain ⟨t, h0, h1, e1, e2⟩ := wA_seg_param hx
  rw [e1]
  rcases ha with ha | ⟨ha, ha'⟩ <;> rcases hb with hb | ⟨hb, hb'⟩
  · rcases le_total a.1 b.1 with hab | hab
    · nlinarith [mul_nonneg h0 (sub_nonneg.mpr hab)]
    · nlinarith [mul_nonneg (sub_nonneg.mpr h1) (sub_nonneg.mpr hab)]
  · rcases eq_or_lt_of_le h1 with ht | ht
    · subst ht; rw [e2] at hx2; linarith
    · nlinarith
  · rcases eq_or_lt_of_le h0 with ht | ht
    · subst ht; rw [e2] at hx2; linarith
    · nlinarith
  · exfalso
    rcases le_total a.2 b.2 with hab | hab
    · nlinarith [mul_nonneg h0 (sub_nonneg.mpr hab)]
    · nlinarith [mul_nonneg (sub_nonneg.mpr h1) (sub_nonneg.mpr hab)]

set_option maxHeartbeats 4000000 in
lemma wA_vf (U1 U2 W1 W2 d1 d2 s X Y A : ℝ)
    (hX : X = W1*d2 - W2*d1) (hY : Y = U1*d2 - U2*d1) (hA : A = U1*W2 - U2*W1)
    (hX0 : X ≠ 0) (hY0 : Y ≠ 0) (hA0 : A ≠ 0)
    (hU : 0 < U1 ∨ (U1 = 0 ∧ 0 < U2)) (hW : 0 < W1 ∨ (W1 = 0 ∧ 0 < W2))
    (hs1 : 0 ≤ s ↔ 0 ≤ d2)
    (hsW : 0 < W2 → s < W2) (hsW' : W2 < 0 → W2 < s)
    (hsU : 0 < U2 → s < U2) (hsU' : U2 < 0 → U2 < s) :
    ((if 0 ≤ s ∧ s < W2 ∧ 0 < X then (1:ℤ) else 0) - (if W2 ≤ s ∧ s < 0 ∧ X < 0 then 1 else 0)
      - ((if 0 ≤ s then 1 else 0) - (if W2 ≤ s then 1 else 0))) +
    ((if U2 ≤ s ∧ s < 0 ∧ Y < 0 then 1 else 0) - (if 0 ≤ s ∧ s < U2 ∧ 0 < Y then 1 else 0)
      - ((if U2 ≤ s then 1 else 0) - (if 0 ≤ s then 1 else 0))) =
    (if 0 < Y * A ∧ 0 < (-X) * A then (if 0 < -A then 1 else -1) else 0) := by
  have P1 : A * d2 + X * U2 - Y * W2 = 0 := by rw [hX, hY, hA]; ring
  have P2 : A * d1 + X * U1 - Y * W1 = 0 := by rw [hX, hY, hA]; ring
  have r1 : s < 0 ↔ ¬ 0 ≤ s := not_le.symm
  have r2 : W2 ≤ s ↔ ¬ s < W2 := not_lt.symm
  have r3 : X < 0 ↔ ¬ 0 < X := ⟨fun h h' => by linarith, fun h => lt_of_le_of_ne (not_lt.mp h) hX0⟩
  have r4 : U2 ≤ s ↔ ¬ s < U2 := not_lt.symm
  have r5 : Y < 0 ↔ ¬ 0 < Y := ⟨fun h h' => by linarith, fun h => lt_of_le_of_ne (not_lt.mp h) hY0⟩
  have r8 : 0 < -A ↔ ¬ 0 < A := ⟨fun h h' => by linarith, fun h => by
    have := lt_of_le_of_ne (not_lt.mp h) hA0; linarith⟩
  have r6 : 0 < Y * A ↔ (0 < Y ↔ 0 < A) := by
    constructor
    · intro h; constructor
      · intro hy; by_contra ha; nlinarith [lt_of_le_of_ne (not_lt.mp ha) hA0]
      · intro ha; by_contra hy; nlinarith [lt_of_le_of_ne (not_lt.mp hy) hY0]
    · intro h; by_cases hy : 0 < Y
      · exact mul_pos hy (h.mp hy)
      · have hy' := lt_of_le_of_ne (not_lt.mp hy) hY0
        have ha : ¬ 0 < A := fun ha => hy (h.mpr ha)
        have ha' := lt_of_le_of_ne (not_lt.mp ha) hA0
        nlinarith
  have r7 : 0 < (-X) * A ↔ (0 < X ↔ ¬ 0 < A) := by
    constructor
    · intro h; constructor
      · intro hx ha; nlinarith
      · intro ha; by_contra hx; nlinarith [lt_of_le_of_ne (not_lt.mp hx) hX0, lt_of_le_of_ne (not_lt.mp ha) hA0]
    · intro h; by_cases hx : 0 < X
      · have ha' := lt_of_le_of_ne (not_lt.mp (h.mp hx)) hA0; nlinarith
      · have hx' := lt_of_le_of_ne (not_lt.mp hx) hX0
        have ha : 0 < A := by by_contra ha; exact hx (h.mpr ha)
        nlinarith
  simp only [r1, r2, r3, r4, r5, r6, r7, r8]
  have hX' := hX0; have hY' := hY0; have hA' := hA0
  by_cases p1 : 0 ≤ s <;> by_cases p2 : s < W2 <;> by_cases p3 : 0 < X <;> by_cases p4 : s < U2 <;>
    by_cases p5 : 0 < Y <;> by_cases p6 : 0 < A <;> simp [p1, p2, p3, p4, p5, p6] <;>
  all_goals (try replace p6 : A < 0 := lt_of_le_of_ne (not_lt.mp p6) hA0)
  all_goals (try replace p5 : Y < 0 := lt_of_le_of_ne (not_lt.mp p5) hY0)
  all_goals (try replace p3 : X < 0 := lt_of_le_of_ne (not_lt.mp p3) hX0)
  all_goals (rcases le_or_gt 0 d2 with q | q)
  all_goals (try have q' := hs1.mpr q)
  all_goals (try have q'' : s < 0 := by by_contra h; exact absurd (hs1.mp (not_lt.mp h)) (not_le.mpr q))
  all_goals (rcases lt_trichotomy W2 0 with w|w|w <;> rcases lt_trichotomy U2 0 with u|u|u)
  all_goals (try have := hsW w)
  all_goals (try have := hsW' w)
  all_goals (try have := hsU u)
  all_goals (try have := hsU' u)
  all_goals (rcases hU with hU | ⟨hU1, hU2⟩ <;> rcases hW with hW | ⟨hW1, hW2⟩)
  all_goals (try linarith)
  all_goals (try nlinarith [P1, P2])

open Classical in
lemma wA_vertex (v U W δ : Pt) (t : ℝ) (ht : 0 < t)
    (hU : 0 < U.1 ∨ (U.1 = 0 ∧ 0 < U.2)) (hW : 0 < W.1 ∨ (W.1 = 0 ∧ 0 < W.2))
    (hpar : cross U W ≠ 0) (ha : cross U δ ≠ 0) (hb : cross W δ ≠ 0)
    (hsW : 0 < W.2 → t * δ.2 < W.2) (hsW' : W.2 < 0 → W.2 < t * δ.2)
    (hsU : 0 < U.2 → t * δ.2 < U.2) (hsU' : U.2 < 0 → U.2 < t * δ.2) :
    (hit v (v + W) (v + t • δ) - wA_str v (v + W) (v + t • δ).2) +
      (hit (v + U) v (v + t • δ) - wA_str (v + U) v (v + t • δ).2) =
    if inOpenCone U W δ then (if 0 < cross W U then 1 else -1) else 0 := by
  have key := wA_vf U.1 U.2 W.1 W.2 δ.1 δ.2 (t * δ.2) (cross W δ) (cross U δ) (cross U W)
    (by simp [cross]) (by simp [cross]) (by simp [cross]) hb ha hpar hU hW
    (by constructor <;> intro h <;> nlinarith) hsW hsW' hsU hsU'
  have e1 : cross (v + W - v) (v + t • δ - v) = t * cross W δ := by
    simp only [cross, Prod.fst_sub, Prod.snd_sub, Prod.fst_add, Prod.snd_add, Prod.smul_fst,
      Prod.smul_snd, smul_eq_mul]; ring
  have e2 : cross (v - (v + U)) (v + t • δ - (v + U)) = -(t * cross U δ) := by
    simp only [cross, Prod.fst_sub, Prod.snd_sub, Prod.fst_add, Prod.snd_add, Prod.smul_fst,
      Prod.smul_snd, smul_eq_mul]; ring
  have e3 : cross δ W = - cross W δ := by simp only [cross]; ring
  have e4 : cross W U = - cross U W := by simp only [cross]; ring
  have m1 : 0 < t * cross W δ ↔ 0 < cross W δ := mul_pos_iff_of_pos_left ht
  have m2 : t * cross W δ < 0 ↔ cross W δ < 0 := by
    constructor <;> intro h <;> nlinarith
  have m3 : 0 < -(t * cross U δ) ↔ cross U δ < 0 := by
    constructor <;> intro h <;> nlinarith
  have m4 : -(t * cross U δ) < 0 ↔ 0 < cross U δ := by
    constructor <;> intro h <;> nlinarith
  unfold hit wA_str inOpenCone
  rw [e1, e2, e3, e4]
  simp only [m1, m2, m3, m4]
  simp only [Prod.snd_add, Prod.smul_snd, smul_eq_mul, le_add_iff_nonneg_right, add_lt_add_iff_left,
    add_le_add_iff_left, add_lt_iff_neg_left]
  convert key

namespace Cycle
variable (C : Cycle)

lemma wA_v_add_mul (j k : ℕ) : C.v (j + C.n * k) = C.v j := by
  induction k with
  | zero => simp
  | succ k ih => rw [show j + C.n * (k + 1) = (j + C.n * k) + C.n by ring, C.per, ih]

lemma wA_v_mod (i : ℕ) : C.v i = C.v (i % C.n) := by
  conv_lhs => rw [← Nat.mod_add_div i C.n]
  exact C.wA_v_add_mul _ _

lemma wA_V_n : C.V C.n = C.V 0 := by
  simp only [V]; rw [show C.n = 0 + C.n by simp, C.per]

lemma wA_isClosed_edges (P : ℕ → Prop) : IsClosed {x | ∃ j < C.n, P j ∧ x ∈ C.edge j} := by
  have : {x | ∃ j < C.n, P j ∧ x ∈ C.edge j} = ⋃ j ∈ {j | j < C.n ∧ P j}, C.edge j := by
    ext x; simp [and_assoc]
  rw [this]
  exact Set.Finite.isClosed_biUnion ((Set.finite_lt_nat C.n).subset (fun j hj => hj.1))
    (fun j _ => wA_seg_closed _ _)

theorem bd_isClosed : IsClosed C.bd := by
  have := C.wA_isClosed_edges (fun _ => True)
  simpa [bd] using this

lemma wA_telescope (f : Pt → ℤ) : ∑ i ∈ range C.n, (f (C.V (i + 1)) - f (C.V i)) = 0 := by
  rw [Finset.sum_range_sub (fun i => f (C.V i)), wA_V_n]; simp

theorem wind_eq_of_seg {p q : Pt} (h : ∀ x ∈ seg p q, x ∉ C.bd) : C.wind p = C.wind q := by
  have hd : ∀ i < C.n, ∀ x ∈ seg p q, x ∉ C.edge i := fun i hi x hx hx' => h x hx ⟨i, hi, hx'⟩
  have main : ∀ p q : Pt, p.2 < q.2 → (∀ i < C.n, ∀ x ∈ seg p q, x ∉ C.edge i) →
      C.wind p = C.wind q := by
    intro p q hpq hd
    have : C.wind p - C.wind q = 0 := by
      unfold wind
      rw [← Finset.sum_sub_distrib, ← C.wA_telescope (wA_ind p q)]
      apply Finset.sum_congr rfl
      intro i hi
      exact wA_edge hpq (hd i (Finset.mem_range.mp hi))
    linarith
  rcases lt_trichotomy p.2 q.2 with hpq | hpq | hpq
  · exact main p q hpq hd
  · unfold wind
    apply Finset.sum_congr rfl
    intro i hi
    exact wA_edge_row hpq (hd i (Finset.mem_range.mp hi))
  · exact (main q p hpq (by intro i hi; rw [wA_seg_symm]; exact hd i hi)).symm


lemma wA_V_mod (i : ℕ) : C.V i = C.V (i % C.n) := by
  simp only [V]; rw [C.wA_v_mod i]

lemma wA_sum_str (y : ℝ) : ∑ i ∈ range C.n, wA_str (C.V i) (C.V (i + 1)) y = 0 := by
  have := C.wA_telescope (fun x => if x.2 ≤ y then 1 else 0)
  unfold wA_str
  have h2 : ∑ i ∈ range C.n, ((if (C.V i).2 ≤ y then (1:ℤ) else 0) - if (C.V (i + 1)).2 ≤ y then 1 else 0)
      = - ∑ i ∈ range C.n, ((if (C.V (i + 1)).2 ≤ y then (1:ℤ) else 0) - if (C.V i).2 ≤ y then 1 else 0) := by
    rw [← Finset.sum_neg_distrib]; apply Finset.sum_congr rfl; intros; ring
  rw [h2, this]; simp


theorem wind_eq_zero_of_lex {p : Pt}
    (h : ∀ i < C.n, p.1 < (C.V i).1 ∨ (p.1 = (C.V i).1 ∧ p.2 < (C.V i).2)) :
    C.wind p = 0 := by
  have h' : ∀ i, p.1 < (C.V i).1 ∨ (p.1 = (C.V i).1 ∧ p.2 < (C.V i).2) := by
    intro i; rw [C.wA_V_mod i]; exact h _ (Nat.mod_lt _ C.pos)
  unfold wind
  rw [← C.wA_sum_str p.2]
  apply Finset.sum_congr rfl
  intro i _
  exact wA_hit_eq_str (fun x hx hx2 => wA_lex_seg (h' i) (h' (i + 1)) hx hx2)

lemma wA_V_bounds (i : ℕ) : (C.xmin : ℝ) ≤ (C.V i).1 ∧ (C.V i).1 ≤ C.xmax ∧
    (C.ymin : ℝ) ≤ (C.V i).2 ∧ (C.V i).2 ≤ C.ymax := by
  rw [C.wA_V_mod i]
  have hm : i % C.n ∈ range C.n := Finset.mem_range.mpr (Nat.mod_lt _ C.pos)
  simp only [V, toPt]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> norm_cast
  · exact Finset.inf'_le _ hm
  · exact Finset.le_sup' (fun i => (C.v i).1) hm
  · exact Finset.inf'_le _ hm
  · exact Finset.le_sup' (fun i => (C.v i).2) hm

lemma wA_bd_bounds {x : Pt} (h : x ∈ C.bd) : (C.xmin : ℝ) ≤ x.1 ∧ x.1 ≤ C.xmax ∧
    (C.ymin : ℝ) ≤ x.2 ∧ x.2 ≤ C.ymax := by
  obtain ⟨i, -, hx⟩ := h
  obtain ⟨t, h0, h1, e1, e2⟩ := wA_seg_param hx
  have A := C.wA_V_bounds i
  have B := C.wA_V_bounds (i + 1)
  rw [e1, e2]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> nlinarith

theorem mem_box_of_bd {q : ℤ × ℤ} (h : toPt q ∈ C.bd) : q ∈ C.box := by
  have := C.wA_bd_bounds h
  simp only [toPt] at this
  obtain ⟨h1, h2, h3, h4⟩ := this
  simp only [box, Finset.mem_product, Finset.mem_Icc]
  exact ⟨⟨by exact_mod_cast h1, by exact_mod_cast h2⟩, by exact_mod_cast h3, by exact_mod_cast h4⟩

theorem mem_box_of_int {q : ℤ × ℤ} (h : toPt q ∈ C.int) : q ∈ C.box := by
  by_contra hq
  apply h.2
  simp only [box, Finset.mem_product, Finset.mem_Icc, not_and_or, not_le] at hq
  set p := toPt q with hp
  rcases hq with (h1 | h1) | (h1 | h1)
  · apply C.wind_eq_zero_of_lex
    intro i _
    left; have := (C.wA_V_bounds i).1
    have : (q.1 : ℝ) < C.xmin := by exact_mod_cast h1
    simp only [hp, toPt]; linarith
  all_goals
    unfold wind
    apply Finset.sum_eq_zero
    intro i hi
    by_contra hne
    obtain ⟨x, hx, hx2, hx1⟩ := wA_hit_ne_zero hne
    have B := C.wA_bd_bounds ⟨i, Finset.mem_range.mp hi, hx⟩
    simp only [hp, toPt] at hx2 hx1
  · have : (C.xmax : ℝ) < q.1 := by exact_mod_cast h1
    linarith
  · have : (q.2 : ℝ) < C.ymin := by exact_mod_cast h1
    linarith
  · have : (C.ymax : ℝ) < q.2 := by exact_mod_cast h1
    linarith

lemma wA_ball_avoid (P : ℕ → Prop) (d : Pt) (hd : ∀ j < C.n, P j → d ∉ C.edge j) :
    ∃ ε > 0, ∀ x : Pt, dist x d < ε → ∀ j < C.n, P j → x ∉ C.edge j := by
  have hK := (C.wA_isClosed_edges P).isOpen_compl
  have hdK : d ∈ {x | ∃ j < C.n, P j ∧ x ∈ C.edge j}ᶜ := by
    rintro ⟨j, hj, hp, hx⟩; exact hd j hj hp hx
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hK d hdK
  refine ⟨ε, hε, fun x hx j hj hp hxj => ?_⟩
  exact hball (Metric.mem_ball.mpr hx) ⟨j, hj, hp, hxj⟩

lemma wA_cross_seg {a b x : Pt} (hx : x ∈ seg a b) : cross (b - a) (x - a) = 0 := by
  obtain ⟨t, -, -, rfl⟩ := hx
  simp only [cross, Prod.fst_sub, Prod.snd_sub, Prod.fst_add, Prod.snd_add, Prod.smul_fst,
    Prod.smul_snd, smul_eq_mul]; ring

theorem wind_jump {i : ℕ} (hi : i < C.n) {d : Pt} (hd : d ∈ C.edge i) (hd0 : d ≠ C.V i)
    (hd1 : d ≠ C.V (i + 1)) (hoth : ∀ j < C.n, j ≠ i → d ∉ C.edge j) :
    ∃ δ > 0, ∀ t : ℝ, 0 < t → t < δ →
      d + t • transv (C.V i) (C.V (i + 1)) ∉ C.bd ∧
      d - t • transv (C.V i) (C.V (i + 1)) ∉ C.bd ∧
      (∀ x ∈ seg (d - t • transv (C.V i) (C.V (i + 1))) (d + t • transv (C.V i) (C.V (i + 1))),
        x ∈ C.bd → x = d) ∧
      (C.wind (d + t • transv (C.V i) (C.V (i + 1))) -
          C.wind (d - t • transv (C.V i) (C.V (i + 1))) = 1 ∨
        C.wind (d + t • transv (C.V i) (C.V (i + 1))) -
          C.wind (d - t • transv (C.V i) (C.V (i + 1))) = -1) := by
  obtain ⟨ε, hε, hball⟩ := C.wA_ball_avoid (fun j => j ≠ i) d hoth
  have hdseg : d ∈ seg (C.V i) (C.V (i + 1)) := hd
  set a := C.V i with ha
  set b := C.V (i + 1) with hb
  have hdseg' := hdseg
  obtain ⟨τ, hτ0, hτ1, hdτ⟩ := hdseg'
  have hτ0' : τ ≠ 0 := by rintro rfl; apply hd0; rw [hdτ]; simp
  have hτ1' : τ ≠ 1 := by rintro rfl; apply hd1; rw [hdτ]; simp
  have hτa : 0 < τ := lt_of_le_of_ne hτ0 (Ne.symm hτ0')
  have hτb : τ < 1 := lt_of_le_of_ne hτ1 hτ1'
  have hd1' : d.1 = a.1 + τ * (b.1 - a.1) := by rw [hdτ]; simp
  have hd2' : d.2 = a.2 + τ * (b.2 - a.2) := by rw [hdτ]; simp
  have hab_ne : a ≠ b := by
    intro h; apply hd0; rw [hdτ, ← h]; simp
  set e := transv a b with he_def
  have he : (a.2 = b.2 ∧ e = (0, 1)) ∨ (a.2 ≠ b.2 ∧ e = (1, 0)) := by
    by_cases h : a.2 = b.2
    · left; exact ⟨h, by rw [he_def, transv, if_pos h]⟩
    · right; exact ⟨h, by rw [he_def, transv, if_neg h]⟩
  have hcr : cross (b - a) e ≠ 0 := by
    rcases he with ⟨h, he⟩ | ⟨h, he⟩
    · rw [he]; simp only [cross, Prod.fst_sub, Prod.snd_sub]
      intro h'
      apply hab_ne; ext
      · linarith
      · exact h
    · rw [he]; simp only [cross, Prod.fst_sub, Prod.snd_sub]
      intro h'; apply h; linarith
  refine ⟨ε, hε, fun t ht0 htε => ?_⟩
  have hparam : ∀ x ∈ seg (d - t • e) (d + t • e), ∃ s : ℝ, 0 ≤ s ∧ s ≤ 1 ∧
      x = d + ((2 * s - 1) * t) • e := by
    rintro x ⟨s, h0, h1, rfl⟩
    refine ⟨s, h0, h1, ?_⟩
    ext <;> simp <;> ring
  have hfar : ∀ j < C.n, j ≠ i → ∀ x ∈ seg (d - t • e) (d + t • e), x ∉ C.edge j := by
    intro j hj hji x hx
    apply hball x _ j hj hji
    obtain ⟨s, h0, h1, rfl⟩ := hparam x hx
    rw [Prod.dist_eq, Real.dist_eq, Real.dist_eq, max_lt_iff]
    rcases he with ⟨-, he⟩ | ⟨-, he⟩ <;> rw [he] <;> simp <;> rw [abs_of_pos ht0] <;>
      (have : |2 * s - 1| ≤ 1 := abs_le.mpr ⟨by linarith, by linarith⟩) <;> constructor <;> nlinarith
  have hmain : ∀ x ∈ seg (d - t • e) (d + t • e), x ∈ C.bd → x = d := by
    intro x hx ⟨k, hk, hxk⟩
    by_cases hki : k = i
    · subst hki
      obtain ⟨s, h0, h1, hxs⟩ := hparam x hx
      have c1 := wA_cross_seg hxk
      have c2 := wA_cross_seg hdseg
      have : cross (b - a) (x - a) = cross (b - a) (d - a) + ((2 * s - 1) * t) * cross (b - a) e := by
        rw [hxs]; simp only [cross, Prod.fst_sub, Prod.snd_sub, Prod.fst_add, Prod.snd_add,
          Prod.smul_fst, Prod.smul_snd, smul_eq_mul]; ring
      rw [c1, c2] at this
      have h0' : (2 * s - 1) * t = 0 := by
        rcases mul_eq_zero.mp (show ((2 * s - 1) * t) * cross (b - a) e = 0 by linarith) with h | h
        · exact h
        · exact absurd h hcr
      rw [hxs, h0']; simp
    · exact absurd hxk (hfar k hk hki x hx)
  have he0 : e ≠ 0 := by
    rcases he with ⟨-, he⟩ | ⟨-, he⟩ <;> rw [he] <;> simp
  have hpm : d + t • e ≠ d := by
    intro h; apply he0
    have : t • e = 0 := by simpa using h
    exact (smul_eq_zero.mp this).resolve_left ht0.ne'
  have hmm : d - t • e ≠ d := by
    intro h; apply he0
    have : t • e = 0 := by simpa using h
    exact (smul_eq_zero.mp this).resolve_left ht0.ne'
  refine ⟨fun h => hpm (hmain _ (wA_right_mem _ _) h), fun h => hmm (hmain _ (wA_left_mem _ _) h),
    hmain, ?_⟩
  have c2 := wA_cross_seg hdseg
  have hdiff : C.wind (d + t • e) - C.wind (d - t • e) =
      ∑ j ∈ range C.n, (hit (C.V j) (C.V (j + 1)) (d + t • e) - hit (C.V j) (C.V (j + 1)) (d - t • e)) := by
    unfold wind; rw [Finset.sum_sub_distrib]
  have hir : i ∈ range C.n := Finset.mem_range.mpr hi
  rcases he with ⟨hab, he⟩ | ⟨hab, he⟩
  · -- horizontal edge, vertical transversal
    have hpq : (d - t • e).2 < (d + t • e).2 := by rw [he]; simp; linarith
    have hT := C.wA_telescope (wA_ind (d - t • e) (d + t • e))
    have hsum : ∑ j ∈ range C.n, ((hit (C.V j) (C.V (j + 1)) (d - t • e) - hit (C.V j) (C.V (j + 1)) (d + t • e))
        - (wA_ind (d - t • e) (d + t • e) (C.V (j + 1)) - wA_ind (d - t • e) (d + t • e) (C.V j))) =
        -(wA_ind (d - t • e) (d + t • e) b - wA_ind (d - t • e) (d + t • e) a) := by
      rw [Finset.sum_eq_single_of_mem i hir]
      · rw [wA_hit_flat hab, wA_hit_flat hab]; ring
      · intro j hj hji
        rw [wA_edge hpq (fun y hy => hfar j (Finset.mem_range.mp hj) hji y hy)]; ring
    rw [Finset.sum_sub_distrib, hT] at hsum
    have hw : C.wind (d + t • e) - C.wind (d - t • e) =
        wA_ind (d - t • e) (d + t • e) b - wA_ind (d - t • e) (d + t • e) a := by
      rw [hdiff, ← neg_inj, ← Finset.sum_neg_distrib]
      rw [show (∑ j ∈ range C.n, -(hit (C.V j) (C.V (j + 1)) (d + t • e) - hit (C.V j) (C.V (j + 1)) (d - t • e))) =
        ∑ j ∈ range C.n, (hit (C.V j) (C.V (j + 1)) (d - t • e) - hit (C.V j) (C.V (j + 1)) (d + t • e)) from
        Finset.sum_congr rfl (fun j _ => by ring)]
      linarith
    rw [hw]
    have hd2 : d.2 = a.2 := by rw [hd2', hab]; ring
    have key : ∀ x : Pt, x.2 = a.2 →
        ((d - t • e).2 < x.2 ∧ x.2 ≤ (d + t • e).2 ∧ cross (d + t • e - (d - t • e)) (x - (d - t • e)) < 0
          ↔ d.1 < x.1) := by
      intro x hx
      rw [he]; simp only [cross, Prod.fst_sub, Prod.snd_sub, Prod.fst_add, Prod.snd_add, Prod.smul_fst,
        Prod.smul_snd, smul_eq_mul, hx, hd2]
      constructor
      · rintro ⟨-, -, h⟩; nlinarith
      · intro h; refine ⟨by linarith, by linarith, by nlinarith⟩
    unfold wA_ind
    rw [if_congr (key b hab.symm) rfl rfl, if_congr (key a rfl) rfl rfl]
    have ha1 : a.1 ≠ b.1 := fun h => hab_ne (Prod.ext h hab)
    rcases lt_or_gt_of_ne ha1 with h | h
    · rw [if_pos (by nlinarith), if_neg (by nlinarith)]; simp
    · rw [if_neg (by nlinarith), if_pos (by nlinarith)]; simp
  · -- non-horizontal edge, horizontal transversal
    have hrow : (d + t • e).2 = (d - t • e).2 := by rw [he]; simp
    rw [hdiff, Finset.sum_eq_single_of_mem i hir]
    · have hcp : cross (b - a) (d + t • e - a) = -(t * (b.2 - a.2)) := by
        rw [he]; simp only [cross, Prod.fst_sub, Prod.snd_sub, Prod.fst_add, Prod.snd_add,
          Prod.smul_fst, Prod.smul_snd, smul_eq_mul] at c2 ⊢; linear_combination c2
      have hcm : cross (b - a) (d - t • e - a) = t * (b.2 - a.2) := by
        rw [he]; simp only [cross, Prod.fst_sub, Prod.snd_sub, Prod.fst_add, Prod.snd_add,
          Prod.smul_fst, Prod.smul_snd, smul_eq_mul] at c2 ⊢; linear_combination c2
      have hp2 : (d + t • e).2 = d.2 := by rw [he]; simp
      have hm2 : (d - t • e).2 = d.2 := by rw [he]; simp
      rcases lt_or_gt_of_ne hab with h | h
      · rw [wA_hit_up h, wA_hit_up h, hcp, hcm, hp2, hm2,
          if_neg (by rintro ⟨-, -, h'⟩; nlinarith), if_pos ⟨by nlinarith, by nlinarith, by nlinarith⟩]
        right; rfl
      · rw [wA_hit_swap b a, wA_hit_swap b a, wA_hit_up h, wA_hit_up h, wA_cross_sub a b (d + t • e), wA_cross_sub a b (d - t • e),
          hcp, hcm, hp2, hm2,
          if_neg (by rintro ⟨-, -, h'⟩; nlinarith), if_pos ⟨by nlinarith, by nlinarith, by nlinarith⟩]
        left; rfl
    · intro j hj hji
      rw [wA_edge_row hrow (fun y hy => by
        rw [wA_seg_symm] at hy; exact hfar j (Finset.mem_range.mp hj) hji y hy)]; ring

open Classical in
theorem wind_near_vertex (h0 : ∀ j, 0 < j → j < C.n → lexlt (C.v 0) (C.v j))
    (hnot : ∀ j, 0 < j → j + 1 < C.n → C.V 0 ∉ C.edge j)
    (hpar : cross (C.V (C.n - 1) - C.V 0) (C.V 1 - C.V 0) ≠ 0)
    (δ : Pt) (hδa : cross (C.V (C.n - 1) - C.V 0) δ ≠ 0) (hδb : cross (C.V 1 - C.V 0) δ ≠ 0) :
    ∃ t0 > 0, ∀ t : ℝ, 0 < t → t < t0 →
      C.V 0 + t • δ ∉ C.bd ∧
      C.wind (C.V 0 + t • δ) =
        if inOpenCone (C.V (C.n - 1) - C.V 0) (C.V 1 - C.V 0) δ then
          (if 0 < cross (C.V 1 - C.V 0) (C.V (C.n - 1) - C.V 0) then 1 else -1)
        else 0 := by
  have hn1 : C.n ≠ 1 := by intro h; apply hpar; rw [h]; simp [cross]
  have hn2 : C.n ≠ 2 := by intro h; apply hpar; rw [h]; simp only [cross]; ring
  have hn3 : 3 ≤ C.n := by have := C.pos; omega
  have hlex : ∀ j, 0 < j → j < C.n → (C.V 0).1 < (C.V j).1 ∨
      ((C.V 0).1 = (C.V j).1 ∧ (C.V 0).2 < (C.V j).2) := by
    intro j hj hjn
    rcases h0 j hj hjn with h | ⟨h1, h2⟩
    · left; simp only [V, toPt]; exact_mod_cast h
    · right; simp only [V, toPt]; exact ⟨by exact_mod_cast h1, by exact_mod_cast h2⟩
  have hxge : ∀ j, (C.V 0).1 ≤ (C.V j).1 := by
    intro j
    rw [C.wA_V_mod j]
    rcases Nat.eq_zero_or_pos (j % C.n) with h | h
    · rw [h]
    · rcases hlex _ h (Nat.mod_lt _ C.pos) with h' | h'
      · exact h'.le
      · exact h'.1.le
  have hxseg : ∀ j, ∀ x ∈ C.edge j, (C.V 0).1 ≤ x.1 := by
    intro j x hx
    obtain ⟨s, hs0, hs1, e1, -⟩ := wA_seg_param hx
    have := hxge j; have := hxge (j + 1)
    rw [e1]; nlinarith
  set v := C.V 0 with hv
  set u := C.V (C.n - 1) with hu
  set w := C.V 1 with hw
  have hUlex : 0 < (u - v).1 ∨ ((u - v).1 = 0 ∧ 0 < (u - v).2) := by
    rcases hlex (C.n - 1) (by omega) (by omega) with h | ⟨h1, h2⟩
    · left; simp only [Prod.fst_sub]; linarith
    · right; simp only [Prod.fst_sub, Prod.snd_sub]; constructor <;> linarith
  have hWlex : 0 < (w - v).1 ∨ ((w - v).1 = 0 ∧ 0 < (w - v).2) := by
    rcases hlex 1 (by omega) (by omega) with h | ⟨h1, h2⟩
    · left; simp only [Prod.fst_sub]; linarith
    · right; simp only [Prod.fst_sub, Prod.snd_sub]; constructor <;> linarith
  obtain ⟨ε, hε, hball⟩ := C.wA_ball_avoid (fun j => 0 < j ∧ j + 1 < C.n) v
    (fun j _ hj => hnot j hj.1 hj.2)
  set M := |δ.1| + |δ.2| + 1 with hM
  have hM0 : 0 < M := by positivity
  set cW : ℝ := if (w - v).2 = 0 then 1 else |(w - v).2| / M with hcW
  set cU : ℝ := if (u - v).2 = 0 then 1 else |(u - v).2| / M with hcU
  have hcW0 : 0 < cW := by
    rw [hcW]; split_ifs with h
    · exact one_pos
    · exact div_pos (abs_pos.mpr h) hM0
  have hcU0 : 0 < cU := by
    rw [hcU]; split_ifs with h
    · exact one_pos
    · exact div_pos (abs_pos.mpr h) hM0
  refine ⟨min (ε / M) (min cW cU), lt_min (div_pos hε hM0) (lt_min hcW0 hcU0), ?_⟩
  intro t ht0 htt
  have ht1 : t * M < ε := by
    have := lt_of_lt_of_le htt (min_le_left _ _); rwa [lt_div_iff₀ hM0] at this
  have hd1 : t * |δ.1| < ε := by
    have : t * |δ.1| ≤ t * M := by apply mul_le_mul_of_nonneg_left _ ht0.le; rw [hM]; linarith [abs_nonneg δ.2]
    linarith
  have hd2 : t * |δ.2| < ε := by
    have : t * |δ.2| ≤ t * M := by apply mul_le_mul_of_nonneg_left _ ht0.le; rw [hM]; linarith [abs_nonneg δ.1]
    linarith
  have hδ2M : t * |δ.2| ≤ t * M := by
    apply mul_le_mul_of_nonneg_left _ ht0.le; rw [hM]; linarith [abs_nonneg δ.1]
  have hsmall : ∀ r : ℝ, r ≠ 0 → t < |r| / M → t * |δ.2| < |r| := by
    intro r _ h; rw [lt_div_iff₀ hM0] at h; linarith
  have htW : (w - v).2 ≠ 0 → t * |δ.2| < |(w - v).2| := by
    intro h; apply hsmall _ h
    have := lt_of_lt_of_le htt (le_trans (min_le_right _ _) (min_le_left _ _))
    rwa [hcW, if_neg h] at this
  have htU : (u - v).2 ≠ 0 → t * |δ.2| < |(u - v).2| := by
    intro h; apply hsmall _ h
    have := lt_of_lt_of_le htt (le_trans (min_le_right _ _) (min_le_right _ _))
    rwa [hcU, if_neg h] at this
  have hab1 : |t * δ.2| = t * |δ.2| := by rw [abs_mul, abs_of_pos ht0]
  have hsW : 0 < (w - v).2 → t * δ.2 < (w - v).2 := by
    intro h; have := htW h.ne'; rw [abs_of_pos h] at this
    linarith [le_abs_self (t * δ.2)]
  have hsW' : (w - v).2 < 0 → (w - v).2 < t * δ.2 := by
    intro h; have := htW h.ne; rw [abs_of_neg h] at this
    linarith [neg_abs_le (t * δ.2)]
  have hsU : 0 < (u - v).2 → t * δ.2 < (u - v).2 := by
    intro h; have := htU h.ne'; rw [abs_of_pos h] at this
    linarith [le_abs_self (t * δ.2)]
  have hsU' : (u - v).2 < 0 → (u - v).2 < t * δ.2 := by
    intro h; have := htU h.ne; rw [abs_of_neg h] at this
    linarith [neg_abs_le (t * δ.2)]
  set p := v + t • δ with hp
  have hdist : ∀ x : Pt, v.1 ≤ x.1 → x.1 ≤ p.1 → x.2 = p.2 → dist x v < ε := by
    intro x h1 h2 h3
    rw [Prod.dist_eq, Real.dist_eq, Real.dist_eq, max_lt_iff]
    have e1 : p.1 = v.1 + t * δ.1 := by simp [hp]
    have e2 : p.2 = v.2 + t * δ.2 := by simp [hp]
    constructor
    · rw [abs_of_nonneg (by linarith)]
      have : t * δ.1 ≤ t * |δ.1| := mul_le_mul_of_nonneg_left (le_abs_self _) ht0.le
      linarith
    · rw [h3, e2, show v.2 + t * δ.2 - v.2 = t * δ.2 by ring, hab1]; exact hd2
  have hn0 : C.n - 1 + 1 = C.n := by omega
  have hVn : C.V (C.n - 1 + 1) = v := by rw [hn0, wA_V_n]
  have hV1 : C.V (0 + 1) = w := by simp [hw]
  constructor
  · rintro ⟨k, hk, hxk⟩
    by_cases hk0 : k = 0
    · subst hk0
      have := wA_cross_seg hxk
      rw [hV1] at this
      have e : cross (w - v) (p - v) = t * cross (w - v) δ := by
        simp only [hp, cross, Prod.fst_sub, Prod.snd_sub, Prod.fst_add, Prod.snd_add, Prod.smul_fst,
          Prod.smul_snd, smul_eq_mul]; ring
      rw [e] at this
      rcases mul_eq_zero.mp this with h | h
      · linarith
      · exact hδb h
    by_cases hkn : k = C.n - 1
    · subst hkn
      have := wA_cross_seg hxk
      rw [hVn] at this
      have e : cross (v - u) (p - u) = -(t * cross (u - v) δ) := by
        simp only [hp, cross, Prod.fst_sub, Prod.snd_sub, Prod.fst_add, Prod.snd_add, Prod.smul_fst,
          Prod.smul_snd, smul_eq_mul]; ring
      rw [e, neg_eq_zero] at this
      rcases mul_eq_zero.mp this with h | h
      · linarith
      · exact hδa h
    · have : dist p v < ε := by
        rw [hp, Prod.dist_eq, Real.dist_eq, Real.dist_eq, max_lt_iff]
        simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul,
          add_sub_cancel_left]
        rw [abs_mul, abs_mul, abs_of_pos ht0]; exact ⟨hd1, hd2⟩
      exact hball p this k hk ⟨by omega, by omega⟩ hxk
  · unfold wind
    rw [show (∑ i ∈ range C.n, hit (C.V i) (C.V (i + 1)) p) =
        ∑ i ∈ range C.n, (hit (C.V i) (C.V (i + 1)) p - wA_str (C.V i) (C.V (i + 1)) p.2) by
      rw [Finset.sum_sub_distrib, C.wA_sum_str]; ring]
    rw [Finset.sum_eq_add_of_mem 0 (C.n - 1) (Finset.mem_range.mpr C.pos)
      (Finset.mem_range.mpr (by omega)) (by omega)]
    · rw [hV1, hVn]
      have key := wA_vertex v (u - v) (w - v) δ t ht0 hUlex hWlex hpar hδa hδb hsW hsW' hsU hsU'
      rw [show v + (w - v) = w by abel, show v + (u - v) = u by abel] at key
      exact key
    · intro j hj ⟨hj0, hjn⟩
      have hjn' := Finset.mem_range.mp hj
      rw [wA_hit_eq_str, sub_self]
      intro x hx hx2
      by_contra hcon; push_neg at hcon
      exact hball x (hdist x (hxseg j x hx) hcon hx2) j hjn' ⟨by omega, by omega⟩ hx

end Cycle
end QE.Pick


/-! Task B: lattice triangles (the base case of Pick's theorem). -/

namespace QE.Pick
open Finset

lemma tB_index (a b : ℤ × ℤ) (hD : crossZ a b ≠ 0) :
    Nat.card ((ℤ × ℤ) ⧸ Submodule.span ℤ (Set.range ![a, b])) = (crossZ a b).natAbs := by
  have hli : LinearIndependent ℤ ![a, b] := by
    rw [LinearIndependent.pair_iff]
    intro s t hst
    have h1 := congrArg Prod.fst hst
    have h2 := congrArg Prod.snd hst
    simp at h1 h2
    unfold crossZ at hD
    have e1 : s * (a.1 * b.2 - a.2 * b.1) = 0 := by linear_combination b.2 * h1 - b.1 * h2
    have e2 : t * (a.1 * b.2 - a.2 * b.1) = 0 := by linear_combination (-a.2) * h1 + a.1 * h2
    exact ⟨(mul_eq_zero.mp e1).resolve_right hD, (mul_eq_zero.mp e2).resolve_right hD⟩
  rw [← Submodule.natAbs_det_basis_change (Module.Basis.finTwoProd ℤ) _ (Module.Basis.span hli)]
  congr 1
  rw [Module.Basis.det_apply, Matrix.det_fin_two]
  simp [Module.Basis.toMatrix_apply, Module.Basis.span_apply, crossZ]; ring

def tB_m (o a b q : ℤ × ℤ) : ℤ := Int.sign (crossZ a b) * crossZ (q - o) b
def tB_n (o a b q : ℤ × ℤ) : ℤ := Int.sign (crossZ a b) * crossZ a (q - o)
def tB_N (a b : ℤ × ℤ) : ℤ := Int.sign (crossZ a b) * crossZ a b

lemma tB_N_pos (a b : ℤ × ℤ) (hD : crossZ a b ≠ 0) : 0 < tB_N a b := by
  unfold tB_N; rw [Int.sign_mul_self_eq_natAbs]; exact_mod_cast Int.natAbs_pos.mpr hD

def tB_par (o a b q : ℤ × ℤ) : Prop :=
  0 ≤ tB_m o a b q ∧ tB_m o a b q < tB_N a b ∧ 0 ≤ tB_n o a b q ∧ tB_n o a b q < tB_N a b

lemma tB_m_lin (o a b q : ℤ × ℤ) (i j : ℤ) :
    tB_m o a b (q + i • a + j • b) = tB_m o a b q + i * tB_N a b := by
  simp only [tB_m, tB_N, crossZ, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd,
    Prod.fst_sub, Prod.snd_sub, smul_eq_mul]; ring

lemma tB_n_lin (o a b q : ℤ × ℤ) (i j : ℤ) :
    tB_n o a b (q + i • a + j • b) = tB_n o a b q + j * tB_N a b := by
  simp only [tB_n, tB_N, crossZ, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd,
    Prod.fst_sub, Prod.snd_sub, smul_eq_mul]; ring

lemma tB_par_card (o a b : ℤ × ℤ) (hD : crossZ a b ≠ 0) (S : Finset (ℤ × ℤ))
    [DecidablePred (tB_par o a b)]
    (hS : ∀ q, tB_par o a b q → q ∈ S) :
    ((S.filter (tB_par o a b)).card : ℤ) = tB_N a b := by
  have hN := tB_N_pos a b hD
  have key : Nat.card {q // q ∈ S.filter (tB_par o a b)} =
      Nat.card ((ℤ × ℤ) ⧸ Submodule.span ℤ (Set.range ![a, b])) := by
    apply Nat.card_congr
    refine Equiv.ofBijective (fun q => Submodule.Quotient.mk q.1) ⟨?_, ?_⟩
    · rintro ⟨q, hq⟩ ⟨q', hq'⟩ h
      simp only [Submodule.Quotient.eq] at h
      obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℤ).mp h
      simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one] at hc
      have hq2 : q = q' + c 0 • a + c 1 • b := by rw [add_assoc, hc]; abel
      have p1 := (mem_filter.mp hq).2
      have p2 := (mem_filter.mp hq').2
      unfold tB_par at p1 p2
      rw [hq2, tB_m_lin, tB_n_lin] at p1
      have e0 : c 0 = 0 := by
        rcases lt_trichotomy (c 0) 0 with h | h | h
        · nlinarith
        · exact h
        · nlinarith
      have e1 : c 1 = 0 := by
        rcases lt_trichotomy (c 1) 0 with h | h | h
        · nlinarith
        · exact h
        · nlinarith
      apply Subtype.ext
      simp [hq2, e0, e1]
    · intro x
      obtain ⟨q, rfl⟩ := Submodule.Quotient.mk_surjective _ x
      set i := tB_m o a b q / tB_N a b
      set j := tB_n o a b q / tB_N a b
      have hp : tB_par o a b (q + (-i) • a + (-j) • b) := by
        unfold tB_par
        rw [tB_m_lin, tB_n_lin]
        have h1 := Int.emod_def (tB_m o a b q) (tB_N a b)
        have h2 := Int.emod_def (tB_n o a b q) (tB_N a b)
        have h3 := Int.emod_nonneg (tB_m o a b q) hN.ne'
        have h4 := Int.emod_nonneg (tB_n o a b q) hN.ne'
        have h5 := Int.emod_lt_of_pos (tB_m o a b q) hN
        have h6 := Int.emod_lt_of_pos (tB_n o a b q) hN
        refine ⟨?_, ?_, ?_, ?_⟩ <;> nlinarith
      refine ⟨⟨_, mem_filter.mpr ⟨hS _ hp, hp⟩⟩, ?_⟩
      simp only [Submodule.Quotient.eq]
      rw [Submodule.mem_span_range_iff_exists_fun]
      refine ⟨![-i, -j], ?_⟩
      simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]; abel
  rw [Nat.card_eq_finsetCard] at key
  rw [key, tB_index a b hD]
  unfold tB_N; rw [Int.sign_mul_self_eq_natAbs]

def tB_cl (o a b q : ℤ × ℤ) : Prop :=
  0 ≤ tB_m o a b q ∧ 0 ≤ tB_n o a b q ∧ tB_m o a b q + tB_n o a b q ≤ tB_N a b
def tB_in (o a b q : ℤ × ℤ) : Prop :=
  0 < tB_m o a b q ∧ 0 < tB_n o a b q ∧ tB_m o a b q + tB_n o a b q < tB_N a b

lemma tB_m_refl (o a b q : ℤ × ℤ) : tB_m o a b (o + o + a + b - q) = tB_N a b - tB_m o a b q := by
  simp only [tB_m, tB_N, crossZ, Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub]; ring

lemma tB_n_refl (o a b q : ℤ × ℤ) : tB_n o a b (o + o + a + b - q) = tB_N a b - tB_n o a b q := by
  simp only [tB_n, tB_N, crossZ, Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub]; ring

lemma tB_refl_refl (o a b q : ℤ × ℤ) : o + o + a + b - (o + o + a + b - q) = q := by abel

lemma tB_mn_inj (o a b : ℤ × ℤ) (hD : crossZ a b ≠ 0) {q q' : ℤ × ℤ}
    (h1 : tB_m o a b q = tB_m o a b q') (h2 : tB_n o a b q = tB_n o a b q') : q = q' := by
  have hs : Int.sign (crossZ a b) ≠ 0 := fun h => hD (Int.sign_eq_zero_iff_zero.mp h)
  unfold tB_m at h1; unfold tB_n at h2
  have h1' := mul_left_cancel₀ hs h1
  have h2' := mul_left_cancel₀ hs h2
  unfold crossZ at h1' h2' hD
  simp only [Prod.fst_sub, Prod.snd_sub] at h1' h2'
  have e1 : (a.1 * b.2 - a.2 * b.1) * (q.1 - q'.1) = 0 := by
    linear_combination a.1 * h1' + b.1 * h2'
  have e2 : (a.1 * b.2 - a.2 * b.1) * (q.2 - q'.2) = 0 := by
    linear_combination a.2 * h1' + b.2 * h2'
  have := (mul_eq_zero.mp e1).resolve_left hD
  have := (mul_eq_zero.mp e2).resolve_left hD
  ext <;> linarith

open Classical in
lemma tB_count (o a b : ℤ × ℤ) (hD : crossZ a b ≠ 0) (S : Finset (ℤ × ℤ))
    (hS : ∀ q, tB_par o a b q → q ∈ S) (hS2 : ∀ q, tB_cl o a b q → q ∈ S) :
    tB_N a b + 2 = ((S.filter (tB_cl o a b)).card : ℤ) + (S.filter (tB_in o a b)).card := by
  have hN := tB_N_pos a b hD
  have hP := tB_par_card o a b hD S hS
  rw [← card_filter_add_card_filter_not
    (fun q => tB_m o a b q + tB_n o a b q ≤ tB_N a b)] at hP
  rw [filter_filter, filter_filter] at hP
  have hma : tB_m o a b (o + a) = tB_N a b := by
    simp only [tB_m, tB_N, add_sub_cancel_left]
  have hna : tB_n o a b (o + a) = 0 := by
    simp only [tB_n, add_sub_cancel_left, crossZ]; ring
  have hmb : tB_m o a b (o + b) = 0 := by
    simp only [tB_m, add_sub_cancel_left, crossZ]; ring
  have hnb : tB_n o a b (o + b) = tB_N a b := by
    simp only [tB_n, tB_N, add_sub_cancel_left]
  have hab : o + a ≠ o + b := by
    intro h
    have := add_left_cancel h
    apply hD; rw [this]; unfold crossZ; ring
  have h1 : S.filter (fun q => tB_par o a b q ∧ tB_m o a b q + tB_n o a b q ≤ tB_N a b) =
      (S.filter (tB_cl o a b)) \ {o + a, o + b} := by
    ext q
    simp only [mem_filter, mem_sdiff, mem_insert, mem_singleton]
    simp only [tB_par, tB_cl]
    constructor
    · rintro ⟨hq, ⟨h1, h2, h3, h4⟩, h5⟩
      refine ⟨⟨hq, h1, h3, h5⟩, ?_⟩
      rintro (rfl | rfl)
      · omega
      · omega
    · rintro ⟨⟨hq, h1, h3, h5⟩, hne⟩
      refine ⟨hq, ⟨h1, ?_, h3, ?_⟩, h5⟩
      · by_contra hc
        exact hne (Or.inl (tB_mn_inj o a b hD (by omega) (by omega)))
      · by_contra hc
        exact hne (Or.inr (tB_mn_inj o a b hD (by omega) (by omega)))
  have hsub : ({o + a, o + b} : Finset (ℤ × ℤ)) ⊆ S.filter (tB_cl o a b) := by
    intro q hq
    simp only [mem_insert, mem_singleton] at hq
    have : tB_cl o a b q := by
      rcases hq with rfl | rfl <;> (unfold tB_cl; omega)
    exact mem_filter.mpr ⟨hS2 _ this, this⟩
  have hc1 := card_sdiff_add_card_eq_card hsub
  rw [card_pair hab] at hc1
  have h2 : (S.filter (fun q => tB_par o a b q ∧ ¬ tB_m o a b q + tB_n o a b q ≤ tB_N a b)).card =
      (S.filter (tB_in o a b)).card := by
    refine card_bij' (fun q _ => o + o + a + b - q) (fun q _ => o + o + a + b - q) ?_ ?_ ?_ ?_
    · intro q hq
      simp only [mem_filter] at hq ⊢
      simp only [tB_par, tB_in, tB_m_refl, tB_n_refl] at hq ⊢
      obtain ⟨_, ⟨h1, h2, h3, h4⟩, h5⟩ := hq
      have hc : tB_cl o a b (o + o + a + b - q) := by
        unfold tB_cl; rw [tB_m_refl, tB_n_refl]; omega
      exact ⟨hS2 _ hc, by omega, by omega, by omega⟩
    · intro q hq
      simp only [mem_filter] at hq ⊢
      simp only [tB_par, tB_in, tB_m_refl, tB_n_refl] at hq ⊢
      obtain ⟨_, h1, h2, h3⟩ := hq
      have hc : tB_par o a b (o + o + a + b - q) := by
        unfold tB_par; rw [tB_m_refl, tB_n_refl]; omega
      exact ⟨hS _ hc, ⟨by omega, by omega, by omega, by omega⟩, by omega⟩
    · intro q _; exact tB_refl_refl o a b q
    · intro q _; exact tB_refl_refl o a b q
  rw [h1, h2] at hP
  push_cast at hP
  omega

lemma tB_core (a b c y D x1 x2 x3 : ℝ) (hab : a ≤ b) (hbc : b ≤ c) (hac : a < c) (hD : D ≠ 0)
    (hs : x1 + x2 + x3 = D) (hy : y * D = x2 * a + x3 * b + x1 * c) :
    ((0 < x1 * D ∧ 0 < x2 * D ∧ 0 < x3 * D) →
      ((if a ≤ y ∧ y < b ∧ 0 < x1 then 1 else 0) - (if b ≤ y ∧ y < a ∧ x1 < 0 then 1 else 0) +
       ((if b ≤ y ∧ y < c ∧ 0 < x2 then 1 else 0) - (if c ≤ y ∧ y < b ∧ x2 < 0 then 1 else 0)) +
       ((if c ≤ y ∧ y < a ∧ 0 < x3 then 1 else 0) - (if a ≤ y ∧ y < c ∧ x3 < 0 then 1 else 0)) : ℤ)
        = if 0 < D then 1 else -1) ∧
    ((x1 * D < 0 ∨ x2 * D < 0 ∨ x3 * D < 0) →
      ((if a ≤ y ∧ y < b ∧ 0 < x1 then 1 else 0) - (if b ≤ y ∧ y < a ∧ x1 < 0 then 1 else 0) +
       ((if b ≤ y ∧ y < c ∧ 0 < x2 then 1 else 0) - (if c ≤ y ∧ y < b ∧ x2 < 0 then 1 else 0)) +
       ((if c ≤ y ∧ y < a ∧ 0 < x3 then 1 else 0) - (if a ≤ y ∧ y < c ∧ x3 < 0 then 1 else 0)) : ℤ)
        = 0) := by
  have n1 : ¬ (b ≤ y ∧ y < a ∧ x1 < 0) := fun h => by linarith [h.1, h.2.1]
  have n2 : ¬ (c ≤ y ∧ y < b ∧ x2 < 0) := fun h => by linarith [h.1, h.2.1]
  have n3 : ¬ (c ≤ y ∧ y < a ∧ 0 < x3) := fun h => by linarith [h.1, h.2.1]
  simp only [n1, n2, n3, ite_false]
  have e1 : (y - a) * D = x3 * (b - a) + x1 * (c - a) := by linear_combination hy + a * hs
  have e2 : (b - y) * D = x2 * (b - a) + x1 * (b - c) := by linear_combination -hy - b * hs
  have e3 : (c - y) * D = x2 * (c - a) + x3 * (c - b) := by linear_combination -hy - c * hs
  have hba : 0 ≤ b - a := by linarith
  have hcb : 0 ≤ c - b := by linarith
  have hca : 0 < c - a := by linarith
  rcases lt_or_gt_of_ne hD with hD | hD
  · have hnD : ¬ 0 < D := by linarith
    simp only [hnD, ite_false]
    constructor
    · rintro ⟨h1, h2, h3⟩
      have p1 : x1 < 0 := by nlinarith
      have p2 : x2 < 0 := by nlinarith
      have p3 : x3 < 0 := by nlinarith
      have ya : a ≤ y := by nlinarith
      have yc : y < c := by nlinarith
      have q1 : ¬ 0 < x1 := by linarith
      have q2 : ¬ 0 < x2 := by linarith
      simp [q1, q2, ya, yc, p3]
    · intro h
      have h' : 0 < x1 ∨ 0 < x2 ∨ 0 < x3 := by
        rcases h with h | h | h
        · left; nlinarith
        · right; left; nlinarith
        · right; right; nlinarith
      rcases lt_or_ge y a with ya | ya
      · have : ¬ a ≤ y := by linarith
        have : ¬ b ≤ y := by linarith
        simp [*]
      rcases lt_or_ge y b with yb | yb
      · have : ¬ b ≤ y := by linarith
        have yc : y < c := by linarith
        have hab' : 0 < b - a := by linarith
        by_cases q1 : 0 < x1
        · have : x3 < 0 := by
            by_contra hc; rw [not_lt] at hc; nlinarith
          simp [*]
        · have : ¬ x3 < 0 := by
            intro hc
            have : 0 < x2 := by
              rcases h' with h' | h' | h'
              · exact absurd h' q1
              · exact h'
              · linarith
            nlinarith
          simp [*]
      rcases lt_or_ge y c with yc | yc
      · have : ¬ y < b := by linarith
        have hbc' : 0 < c - b := by linarith
        by_cases q2 : 0 < x2
        · have : x3 < 0 := by
            by_contra hc; rw [not_lt] at hc; nlinarith
          simp [*]
        · have : ¬ x3 < 0 := by
            intro hc
            have : 0 < x1 := by
              rcases h' with h' | h' | h'
              · exact h'
              · exact absurd h' q2
              · linarith
            nlinarith
          simp [*]
      · have : ¬ y < b := by linarith
        have : ¬ y < c := by linarith
        simp [*]
  · simp only [hD, ite_true]
    constructor
    · rintro ⟨h1, h2, h3⟩
      have p1 : 0 < x1 := by nlinarith
      have p2 : 0 < x2 := by nlinarith
      have p3 : 0 < x3 := by nlinarith
      have ya : a ≤ y := by nlinarith
      have yc : y < c := by nlinarith
      have q3 : ¬ x3 < 0 := by linarith
      by_cases yb : y < b
      · have : ¬ b ≤ y := by linarith
        simp [*]
      · have : b ≤ y := by linarith
        simp [*]
    · intro h
      have h' : x1 < 0 ∨ x2 < 0 ∨ x3 < 0 := by
        rcases h with h | h | h
        · left; nlinarith
        · right; left; nlinarith
        · right; right; nlinarith
      rcases lt_or_ge y a with ya | ya
      · have : ¬ a ≤ y := by linarith
        have : ¬ b ≤ y := by linarith
        simp [*]
      rcases lt_or_ge y b with yb | yb
      · have : ¬ b ≤ y := by linarith
        have yc : y < c := by linarith
        have hab' : 0 < b - a := by linarith
        by_cases q1 : 0 < x1
        · have : x3 < 0 := by
            by_contra hc; rw [not_lt] at hc
            have : x2 < 0 := by
              rcases h' with h' | h' | h'
              · linarith
              · exact h'
              · linarith
            nlinarith
          simp [*]
        · have : ¬ x3 < 0 := by
            intro hc; nlinarith
          simp [*]
      rcases lt_or_ge y c with yc | yc
      · have : ¬ y < b := by linarith
        have hbc' : 0 < c - b := by linarith
        by_cases q2 : 0 < x2
        · have : x3 < 0 := by
            by_contra hc; rw [not_lt] at hc
            have : x1 < 0 := by
              rcases h' with h' | h' | h'
              · exact h'
              · linarith
              · linarith
            nlinarith
          simp [*]
        · have : ¬ x3 < 0 := by
            intro hc; nlinarith
          simp [*]
      · have : ¬ y < b := by linarith
        have : ¬ y < c := by linarith
        simp [*]

/-- The winding statement for a triangle `A B C` at `p`. -/
def tB_Q (A B C p : Pt) : Prop :=
  cross (B - A) (C - A) ≠ 0 →
  ((0 < cross (B - A) (p - A) * cross (B - A) (C - A) ∧
      0 < cross (C - B) (p - B) * cross (B - A) (C - A) ∧
      0 < cross (A - C) (p - C) * cross (B - A) (C - A)) →
    hit A B p + hit B C p + hit C A p = if 0 < cross (B - A) (C - A) then 1 else -1) ∧
  ((cross (B - A) (p - A) * cross (B - A) (C - A) < 0 ∨
      cross (C - B) (p - B) * cross (B - A) (C - A) < 0 ∨
      cross (A - C) (p - C) * cross (B - A) (C - A) < 0) →
    hit A B p + hit B C p + hit C A p = 0)

lemma tB_Q_sorted (A B C p : Pt) (hab : A.2 ≤ B.2) (hbc : B.2 ≤ C.2) : tB_Q A B C p := by
  intro hD
  have hac : A.2 < C.2 := by
    rcases lt_or_eq_of_le hab with h | h
    · linarith
    rcases lt_or_eq_of_le hbc with h' | h'
    · linarith
    exfalso; apply hD; simp only [cross, Prod.fst_sub, Prod.snd_sub]; rw [h, h']; ring
  have hs : cross (B - A) (p - A) + cross (C - B) (p - B) + cross (A - C) (p - C) =
      cross (B - A) (C - A) := by
    simp only [cross, Prod.fst_sub, Prod.snd_sub]; ring
  have hy : p.2 * cross (B - A) (C - A) = cross (C - B) (p - B) * A.2 +
      cross (A - C) (p - C) * B.2 + cross (B - A) (p - A) * C.2 := by
    simp only [cross, Prod.fst_sub, Prod.snd_sub]; ring
  have := tB_core A.2 B.2 C.2 p.2 _ _ _ _ hab hbc hac hD hs hy
  unfold hit
  exact this

lemma tB_hit_swap (a b p : Pt) : hit b a p = - hit a b p := by
  unfold hit
  have h : cross (a - b) (p - b) = - cross (b - a) (p - a) := by
    simp only [cross, Prod.fst_sub, Prod.snd_sub]; ring
  rw [h]
  simp only [neg_pos, neg_lt_zero]
  ring

lemma tB_Q_rot {A B C p : Pt} (h : tB_Q B C A p) : tB_Q A B C p := by
  intro hD
  have e : cross (C - B) (A - B) = cross (B - A) (C - A) := by
    simp only [cross, Prod.fst_sub, Prod.snd_sub]; ring
  have hF : hit B C p + hit C A p + hit A B p = hit A B p + hit B C p + hit C A p := by ring
  have h' := h (by rw [e]; exact hD)
  rw [e, hF] at h'
  obtain ⟨h1, h2⟩ := h'
  exact ⟨fun ⟨a1, a2, a3⟩ => h1 ⟨a2, a3, a1⟩,
    fun hh => h2 (by rcases hh with hh | hh | hh <;> tauto)⟩

lemma tB_Q_refl {A B C p : Pt} (h : tB_Q A C B p) : tB_Q A B C p := by
  intro hD
  have e : cross (C - A) (B - A) = - cross (B - A) (C - A) := by
    simp only [cross, Prod.fst_sub, Prod.snd_sub]; ring
  have e1 : cross (C - A) (p - A) = - cross (A - C) (p - C) := by
    simp only [cross, Prod.fst_sub, Prod.snd_sub]; ring
  have e2 : cross (B - C) (p - C) = - cross (C - B) (p - B) := by
    simp only [cross, Prod.fst_sub, Prod.snd_sub]; ring
  have e3 : cross (A - B) (p - B) = - cross (B - A) (p - A) := by
    simp only [cross, Prod.fst_sub, Prod.snd_sub]; ring
  have hF : hit A C p + hit C B p + hit B A p = -(hit A B p + hit B C p + hit C A p) := by
    rw [tB_hit_swap A C, tB_hit_swap C B, tB_hit_swap B A]; ring
  have h' := h (by rw [e]; exact neg_ne_zero.mpr hD)
  rw [e, e1, e2, e3, hF] at h'
  simp only [neg_mul_neg] at h'
  obtain ⟨h1, h2⟩ := h'
  constructor
  · rintro ⟨a1, a2, a3⟩
    have := h1 ⟨a3, a2, a1⟩
    rcases lt_or_gt_of_ne hD with hd | hd
    · rw [if_pos (by linarith)] at this; rw [if_neg (by linarith)]; omega
    · rw [if_neg (by linarith)] at this; rw [if_pos hd]; omega
  · intro hh
    have := h2 (by rcases hh with hh | hh | hh <;> tauto)
    omega

lemma tB_Q_all (A B C p : Pt) : tB_Q A B C p := by
  rcases le_total A.2 B.2 with h1 | h1 <;> rcases le_total B.2 C.2 with h2 | h2 <;>
    rcases le_total A.2 C.2 with h3 | h3
  all_goals first
    | exact tB_Q_sorted A B C p h1 h2
    | exact tB_Q_refl (tB_Q_sorted A C B p h3 h2)
    | exact tB_Q_rot (tB_Q_refl (tB_Q_sorted B A C p h1 h3))
    | exact tB_Q_rot (tB_Q_sorted B C A p h2 h3)
    | exact tB_Q_rot (tB_Q_rot (tB_Q_sorted C A B p h3 h1))
    | exact tB_Q_rot (tB_Q_rot (tB_Q_refl (tB_Q_sorted C B A p h2 h1)))

lemma tB_cramer (A B C p : Pt) (hD : cross (B - A) (C - A) ≠ 0) :
    p = A + (cross (A - C) (p - C) / cross (B - A) (C - A)) • (B - A) +
      (cross (B - A) (p - A) / cross (B - A) (C - A)) • (C - A) := by
  have hD' := hD
  simp only [cross, Prod.fst_sub, Prod.snd_sub] at hD'
  ext
  · simp only [cross, Prod.fst_add, Prod.fst_sub, Prod.snd_sub, Prod.smul_fst, smul_eq_mul]
    field_simp
    ring
  · simp only [cross, Prod.snd_add, Prod.fst_sub, Prod.snd_sub, Prod.smul_snd, smul_eq_mul]
    field_simp
    ring

lemma tB_sum3 (A B C p : Pt) : cross (B - A) (p - A) + cross (C - B) (p - B) + cross (A - C) (p - C) =
    cross (B - A) (C - A) := by
  simp only [cross, Prod.fst_sub, Prod.snd_sub]; ring

lemma tB_div_nonneg {x D : ℝ} (hD : D ≠ 0) (h : 0 ≤ x * D) : 0 ≤ x / D := by
  have : x / D = (x * D) / (D * D) := by field_simp
  rw [this]; exact div_nonneg h (mul_self_nonneg D)

lemma tB_tri_iff (A B C p : Pt) (hD : cross (B - A) (C - A) ≠ 0) :
    p ∈ tri A B C ↔ (0 ≤ cross (B - A) (p - A) * cross (B - A) (C - A) ∧
      0 ≤ cross (C - B) (p - B) * cross (B - A) (C - A) ∧
      0 ≤ cross (A - C) (p - C) * cross (B - A) (C - A)) := by
  constructor
  · rintro ⟨s, t, hs, ht, hst, rfl⟩
    have e1 : cross (B - A) (A + s • (B - A) + t • (C - A) - A) = t * cross (B - A) (C - A) := by
      simp only [cross, Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub, Prod.smul_fst,
        Prod.smul_snd, smul_eq_mul]; ring
    have e2 : cross (C - B) (A + s • (B - A) + t • (C - A) - B) =
        (1 - s - t) * cross (B - A) (C - A) := by
      simp only [cross, Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub, Prod.smul_fst,
        Prod.smul_snd, smul_eq_mul]; ring
    have e3 : cross (A - C) (A + s • (B - A) + t • (C - A) - C) = s * cross (B - A) (C - A) := by
      simp only [cross, Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub, Prod.smul_fst,
        Prod.smul_snd, smul_eq_mul]; ring
    rw [e1, e2, e3]
    have := mul_self_nonneg (cross (B - A) (C - A))
    refine ⟨?_, ?_, ?_⟩ <;> rw [mul_assoc] <;> apply mul_nonneg <;> linarith
  · rintro ⟨h1, h2, h3⟩
    refine ⟨_, _, tB_div_nonneg hD h3, tB_div_nonneg hD h1, ?_, tB_cramer A B C p hD⟩
    have h2' := tB_div_nonneg hD h2
    have hs := tB_sum3 A B C p
    have : cross (C - B) (p - B) / cross (B - A) (C - A) =
        1 - cross (A - C) (p - C) / cross (B - A) (C - A) -
          cross (B - A) (p - A) / cross (B - A) (C - A) := by
      field_simp; linarith
    linarith

lemma tB_seg_iff (A B C p : Pt) (hD : cross (B - A) (C - A) ≠ 0) :
    p ∈ seg A B ↔ (cross (B - A) (p - A) = 0 ∧
      0 ≤ cross (C - B) (p - B) * cross (B - A) (C - A) ∧
      0 ≤ cross (A - C) (p - C) * cross (B - A) (C - A)) := by
  constructor
  · rintro ⟨u, hu0, hu1, rfl⟩
    have e1 : cross (B - A) (A + u • (B - A) - A) = 0 := by
      simp only [cross, Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub, Prod.smul_fst,
        Prod.smul_snd, smul_eq_mul]; ring
    have e2 : cross (C - B) (A + u • (B - A) - B) = (1 - u) * cross (B - A) (C - A) := by
      simp only [cross, Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub, Prod.smul_fst,
        Prod.smul_snd, smul_eq_mul]; ring
    have e3 : cross (A - C) (A + u • (B - A) - C) = u * cross (B - A) (C - A) := by
      simp only [cross, Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub, Prod.smul_fst,
        Prod.smul_snd, smul_eq_mul]; ring
    rw [e1, e2, e3]
    have := mul_self_nonneg (cross (B - A) (C - A))
    refine ⟨rfl, ?_, ?_⟩ <;> rw [mul_assoc] <;> apply mul_nonneg <;> linarith
  · rintro ⟨h1, h2, h3⟩
    refine ⟨_, tB_div_nonneg hD h3, ?_, ?_⟩
    · have h2' := tB_div_nonneg hD h2
      have hs := tB_sum3 A B C p
      have : cross (C - B) (p - B) / cross (B - A) (C - A) =
          1 - cross (A - C) (p - C) / cross (B - A) (C - A) := by
        field_simp; linarith
      linarith
    · have := tB_cramer A B C p hD
      rw [h1, zero_div, zero_smul, add_zero] at this
      exact this

lemma tB_left_mem (a b : Pt) : a ∈ seg a b := ⟨0, le_refl _, zero_le_one, by simp⟩
lemma tB_right_mem (a b : Pt) : b ∈ seg a b := ⟨1, zero_le_one, le_refl _, by simp⟩

lemma tB_v3 (T : LPoly) (h3 : T.n = 3) : T.v 3 = T.v 0 := by
  have := T.per 0; rw [h3] at this; simpa using this

lemma tB_V3 (T : LPoly) (h3 : T.n = 3) : T.V 3 = T.V 0 := by
  simp only [Cycle.V]; rw [tB_v3 T h3]

lemma tB_wind (T : LPoly) (h3 : T.n = 3) (p : Pt) :
    T.wind p = hit (T.V 0) (T.V 1) p + hit (T.V 1) (T.V 2) p + hit (T.V 2) (T.V 0) p := by
  unfold Cycle.wind; rw [h3]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, Nat.reduceAdd]
  rw [tB_V3 T h3]

lemma tB_bd_iff (T : LPoly) (h3 : T.n = 3) (p : Pt) : p ∈ T.bd ↔
    (p ∈ seg (T.V 0) (T.V 1) ∨ p ∈ seg (T.V 1) (T.V 2) ∨ p ∈ seg (T.V 2) (T.V 0)) := by
  unfold Cycle.bd Cycle.edge
  rw [Set.mem_ofPred_eq, h3]
  constructor
  · rintro ⟨i, hi, h⟩
    interval_cases i
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · rw [tB_V3 T h3] at h; exact Or.inr (Or.inr h)
  · rintro (h | h | h)
    · exact ⟨0, by norm_num, h⟩
    · exact ⟨1, by norm_num, h⟩
    · exact ⟨2, by norm_num, by rw [tB_V3 T h3]; exact h⟩

lemma tB_bd3_iff (A B C p : Pt) (hD : cross (B - A) (C - A) ≠ 0) :
    (p ∈ seg A B ∨ p ∈ seg B C ∨ p ∈ seg C A) ↔
    ((0 ≤ cross (B - A) (p - A) * cross (B - A) (C - A) ∧
      0 ≤ cross (C - B) (p - B) * cross (B - A) (C - A) ∧
      0 ≤ cross (A - C) (p - C) * cross (B - A) (C - A)) ∧
      (cross (B - A) (p - A) = 0 ∨ cross (C - B) (p - B) = 0 ∨ cross (A - C) (p - C) = 0)) := by
  have e1 : cross (C - B) (A - B) = cross (B - A) (C - A) := by
    simp only [cross, Prod.fst_sub, Prod.snd_sub]; ring
  have e2 : cross (A - C) (B - C) = cross (B - A) (C - A) := by
    simp only [cross, Prod.fst_sub, Prod.snd_sub]; ring
  have s1 := tB_seg_iff A B C p hD
  have s2 := tB_seg_iff B C A p (by rw [e1]; exact hD)
  have s3 := tB_seg_iff C A B p (by rw [e2]; exact hD)
  rw [e1] at s2; rw [e2] at s3
  rw [s1, s2, s3]
  constructor
  · rintro (⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩)
    · exact ⟨⟨by rw [h1]; simp, h2, h3⟩, Or.inl h1⟩
    · exact ⟨⟨h3, by rw [h1]; simp, h2⟩, Or.inr (Or.inl h1)⟩
    · exact ⟨⟨h2, h3, by rw [h1]; simp⟩, Or.inr (Or.inr h1)⟩
  · rintro ⟨⟨h1, h2, h3⟩, h | h | h⟩
    · exact Or.inl ⟨h, h2, h3⟩
    · exact Or.inr (Or.inl ⟨h, h3, h1⟩)
    · exact Or.inr (Or.inr ⟨h, h1, h2⟩)

/-- (B0) A simple lattice polygon with three vertices is a non-degenerate triangle. -/
theorem tri_nondeg (T : LPoly) (h3 : T.n = 3) :
    cross (T.V 1 - T.V 0) (T.V 2 - T.V 0) ≠ 0 := by
  intro hD
  have hinj : ∀ i j, i < 3 → j < 3 → T.V i = T.V j → i = j := by
    intro i j hi hj h
    apply T.inj i j (by omega) (by omega)
    simp only [Cycle.V, toPt, Prod.mk.injEq, Int.cast_inj] at h
    exact Prod.ext h.1 h.2
  have h01 : T.V 0 ≠ T.V 1 := fun h => by
    have := hinj 0 1 (by norm_num) (by norm_num) h; omega
  have h02 : T.V 0 ≠ T.V 2 := fun h => by
    have := hinj 0 2 (by norm_num) (by norm_num) h; omega
  have h12 : T.V 1 ≠ T.V 2 := fun h => by
    have := hinj 1 2 (by norm_num) (by norm_num) h; omega
  have s01 : ∀ p, p ∈ seg (T.V 0) (T.V 1) → p ∈ seg (T.V 1) (T.V 2) → p = T.V 1 := by
    intro p hp hq
    have := T.simple 0 1 (by omega) (by omega) (by norm_num) p hp hq
    rw [h3] at this
    rcases this with ⟨_, h⟩ | ⟨h, _⟩
    · exact h
    · norm_num at h
  have s12 : ∀ p, p ∈ seg (T.V 1) (T.V 2) → p ∈ seg (T.V 2) (T.V 0) → p = T.V 2 := by
    intro p hp hq
    rw [← tB_V3 T h3] at hq
    have := T.simple 1 2 (by omega) (by omega) (by norm_num) p hp hq
    rw [h3] at this
    rcases this with ⟨_, h⟩ | ⟨h, _⟩
    · exact h
    · norm_num at h
  have s20 : ∀ p, p ∈ seg (T.V 2) (T.V 0) → p ∈ seg (T.V 0) (T.V 1) → p = T.V 0 := by
    intro p hp hq
    rw [← tB_V3 T h3] at hp
    have := T.simple 2 0 (by omega) (by omega) (by norm_num) p hp hq
    rw [h3] at this
    rcases this with ⟨_, h⟩ | ⟨h, _⟩
    · rw [← tB_V3 T h3]; exact h
    · norm_num at h
  generalize T.V 0 = A at *
  generalize T.V 1 = B at *
  generalize T.V 2 = C at *
  obtain ⟨l, hl⟩ : ∃ l : ℝ, C = A + l • (B - A) := by
    simp only [cross, Prod.fst_sub, Prod.snd_sub] at hD
    by_cases hu : B.1 - A.1 = 0
    · have hu2 : B.2 - A.2 ≠ 0 := by
        intro h; apply h01; ext <;> linarith
      have hw1 : C.1 - A.1 = 0 := by
        rw [hu] at hD
        have : (B.2 - A.2) * (C.1 - A.1) = 0 := by linarith
        exact (mul_eq_zero.mp this).resolve_left hu2
      refine ⟨(C.2 - A.2) / (B.2 - A.2), ?_⟩
      ext
      · simp only [Prod.fst_add, Prod.smul_fst, Prod.fst_sub, smul_eq_mul]; rw [hu]; linarith
      · simp only [Prod.snd_add, Prod.smul_snd, Prod.snd_sub, smul_eq_mul]; field_simp; ring
    · refine ⟨(C.1 - A.1) / (B.1 - A.1), ?_⟩
      ext
      · simp only [Prod.fst_add, Prod.smul_fst, Prod.fst_sub, smul_eq_mul]; field_simp; ring
      · simp only [Prod.snd_add, Prod.smul_snd, Prod.snd_sub, smul_eq_mul]; field_simp
        linarith
  subst hl
  have hl0 : l ≠ 0 := by rintro rfl; apply h02; simp
  have hl1 : l ≠ 1 := by rintro rfl; apply h12; simp
  rcases lt_or_gt_of_ne hl0 with hneg | hpos
  · -- A lies on [B, C]
    apply h02 (s12 A ?_ (tB_right_mem _ _))
    refine ⟨1 / (1 - l), by apply div_nonneg <;> linarith, ?_, ?_⟩
    · rw [div_le_one (by linarith)]; linarith
    · have : (1 - l) ≠ 0 := by linarith
      ext <;> simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, Prod.fst_sub,
        Prod.snd_sub, smul_eq_mul] <;> field_simp <;> ring
  rcases lt_or_gt_of_ne hl1 with hlt | hgt
  · apply h12 (s01 _ ⟨l, hpos.le, hlt.le, rfl⟩ (tB_right_mem _ _)).symm
  · apply h01 (s20 B ?_ (tB_right_mem _ _)).symm
    refine ⟨(l - 1) / l, by apply div_nonneg <;> linarith, ?_, ?_⟩
    · rw [div_le_one (by linarith)]; linarith
    · have : l ≠ 0 := hl0
      ext <;> simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, Prod.fst_sub,
        Prod.snd_sub, smul_eq_mul] <;> field_simp <;> ring

lemma tB_shoe (T : LPoly) (h3 : T.n = 3) :
    T.shoe = crossZ (T.v 1 - T.v 0) (T.v 2 - T.v 0) := by
  unfold Cycle.shoe; rw [h3]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, Nat.reduceAdd]
  rw [tB_v3 T h3]; simp only [crossZ, Prod.fst_sub, Prod.snd_sub]; ring

lemma tB_crossZ_cast (u w z : ℤ × ℤ) :
    cross (toPt u - toPt w) (toPt z - toPt w) = ((crossZ (u - w) (z - w) : ℤ) : ℝ) := by
  simp only [cross, crossZ, toPt, Prod.fst_sub, Prod.snd_sub]; push_cast; ring

lemma tB_shoe_real (T : LPoly) (h3 : T.n = 3) :
    (T.shoe : ℝ) = cross (T.V 1 - T.V 0) (T.V 2 - T.V 0) := by
  rw [tB_shoe T h3]; simp only [Cycle.V]; rw [tB_crossZ_cast]

theorem tri_shoe_sign (T : LPoly) (h3 : T.n = 3) :
    Int.sign T.shoe = 1 ∨ Int.sign T.shoe = -1 := by
  have hD := tri_nondeg T h3
  have : T.shoe ≠ 0 := by intro h; apply hD; rw [← tB_shoe_real T h3, h]; simp
  rcases lt_or_gt_of_ne this with h | h
  · right; exact Int.sign_eq_neg_one_of_neg h
  · left; exact Int.sign_eq_one_of_pos h

lemma tB_sign_eq (T : LPoly) (h3 : T.n = 3) :
    Int.sign T.shoe = if 0 < cross (T.V 1 - T.V 0) (T.V 2 - T.V 0) then 1 else -1 := by
  have hD := tri_nondeg T h3
  rw [← tB_shoe_real T h3] at hD ⊢
  rcases lt_or_gt_of_ne hD with h | h
  · have h' : T.shoe < 0 := by exact_mod_cast h
    rw [Int.sign_eq_neg_one_of_neg h', if_neg (by linarith)]
  · have h' : 0 < T.shoe := by exact_mod_cast h
    rw [Int.sign_eq_one_of_pos h', if_pos h]

/-- (B1) Outside the closed triangle the winding number vanishes. -/
theorem tri_wind_out (T : LPoly) (h3 : T.n = 3) {p : Pt}
    (hp : p ∉ tri (T.V 0) (T.V 1) (T.V 2)) : T.wind p = 0 := by
  have hD := tri_nondeg T h3
  rw [tB_tri_iff _ _ _ _ hD] at hp
  rw [tB_wind T h3]
  apply ((tB_Q_all _ _ _ p) hD).2
  by_contra hc
  simp only [not_or, not_lt] at hc
  exact hp ⟨hc.1, hc.2.1, hc.2.2⟩

lemma tB_pos_of (A B C p : Pt) (hD : cross (B - A) (C - A) ≠ 0) (htri : p ∈ tri A B C)
    (hb : ¬ (p ∈ seg A B ∨ p ∈ seg B C ∨ p ∈ seg C A)) :
    0 < cross (B - A) (p - A) * cross (B - A) (C - A) ∧
      0 < cross (C - B) (p - B) * cross (B - A) (C - A) ∧
      0 < cross (A - C) (p - C) * cross (B - A) (C - A) := by
  rw [tB_tri_iff _ _ _ _ hD] at htri
  rw [tB_bd3_iff _ _ _ _ hD] at hb
  obtain ⟨h1, h2, h3⟩ := htri
  refine ⟨lt_of_le_of_ne h1 (Ne.symm (mul_ne_zero ?_ hD)),
    lt_of_le_of_ne h2 (Ne.symm (mul_ne_zero ?_ hD)),
    lt_of_le_of_ne h3 (Ne.symm (mul_ne_zero ?_ hD))⟩
  · exact fun h => hb ⟨⟨h1, h2, h3⟩, Or.inl h⟩
  · exact fun h => hb ⟨⟨h1, h2, h3⟩, Or.inr (Or.inl h)⟩
  · exact fun h => hb ⟨⟨h1, h2, h3⟩, Or.inr (Or.inr h)⟩

/-- (B2) Inside the open triangle the winding number is the orientation sign. -/
theorem tri_wind_in (T : LPoly) (h3 : T.n = 3) {p : Pt}
    (hp : p ∈ tri (T.V 0) (T.V 1) (T.V 2)) (hb : p ∉ T.bd) : T.wind p = Int.sign T.shoe := by
  have hD := tri_nondeg T h3
  rw [tB_bd_iff T h3] at hb
  rw [tB_wind T h3, tB_sign_eq T h3]
  exact ((tB_Q_all _ _ _ p) hD).1 (tB_pos_of _ _ _ _ hD hp hb)

/-- (B3) The boundary lies in the closed triangle. -/
theorem tri_bd_sub (T : LPoly) (h3 : T.n = 3) : T.bd ⊆ tri (T.V 0) (T.V 1) (T.V 2) := by
  intro p hp
  have hD := tri_nondeg T h3
  rw [tB_bd_iff T h3, tB_bd3_iff _ _ _ _ hD] at hp
  rw [tB_tri_iff _ _ _ _ hD]
  exact hp.1

lemma tB_int_iff (T : LPoly) (h3 : T.n = 3) (p : Pt) : p ∈ T.int ↔
    (0 < cross (T.V 1 - T.V 0) (p - T.V 0) * cross (T.V 1 - T.V 0) (T.V 2 - T.V 0) ∧
      0 < cross (T.V 2 - T.V 1) (p - T.V 1) * cross (T.V 1 - T.V 0) (T.V 2 - T.V 0) ∧
      0 < cross (T.V 0 - T.V 2) (p - T.V 2) * cross (T.V 1 - T.V 0) (T.V 2 - T.V 0)) := by
  have hD := tri_nondeg T h3
  constructor
  · rintro ⟨hb, hw⟩
    by_cases htri : p ∈ tri (T.V 0) (T.V 1) (T.V 2)
    · rw [tB_bd_iff T h3] at hb
      exact tB_pos_of _ _ _ _ hD htri hb
    · exact absurd (tri_wind_out T h3 htri) hw
  · intro h
    refine ⟨?_, ?_⟩
    · rw [tB_bd_iff T h3, tB_bd3_iff _ _ _ _ hD]
      rintro ⟨_, h' | h' | h'⟩
      · rw [h', zero_mul] at h; exact lt_irrefl _ h.1
      · rw [h', zero_mul] at h; exact lt_irrefl _ h.2.1
      · rw [h', zero_mul] at h; exact lt_irrefl _ h.2.2
    · show T.wind p ≠ 0
      rw [tB_wind T h3, ((tB_Q_all _ _ _ p) hD).1 h]
      split_ifs <;> norm_num

lemma tB_conv (a b t : ℝ) (ha : 0 < a) (hb : 0 < b) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    0 < (1 - t) * a + t * b := by
  rcases eq_or_lt_of_le ht0 with h | h
  · rw [← h]; linarith
  · have := mul_pos h hb
    have := mul_nonneg (by linarith : (0:ℝ) ≤ 1 - t) ha.le
    linarith

lemma tB_cross_lin (u w p q : Pt) (D t : ℝ) :
    cross u (p + t • (q - p) - w) * D = (1 - t) * (cross u (p - w) * D) + t * (cross u (q - w) * D) := by
  simp only [cross, Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub, Prod.smul_fst,
    Prod.smul_snd, smul_eq_mul]; ring

/-- (B4) The interior is connected by segments. -/
theorem tri_conn (T : LPoly) (h3 : T.n = 3) {p q : Pt} (hp : p ∈ T.int) (hq : q ∈ T.int) :
    Reach T.int p q := by
  apply Relation.ReflTransGen.single
  rintro z ⟨t, ht0, ht1, rfl⟩
  rw [tB_int_iff T h3] at hp hq ⊢
  rw [tB_cross_lin, tB_cross_lin, tB_cross_lin]
  exact ⟨tB_conv _ _ _ hp.1 hq.1 ht0 ht1, tB_conv _ _ _ hp.2.1 hq.2.1 ht0 ht1,
    tB_conv _ _ _ hp.2.2 hq.2.2 ht0 ht1⟩

lemma tB_mem_box (T : LPoly) (h3 : T.n = 3) (q : ℤ × ℤ)
    (h : toPt q ∈ tri (T.V 0) (T.V 1) (T.V 2)) : q ∈ T.box := by
  obtain ⟨s, t, hs, ht, hst, he⟩ := h
  have hx : (q.1 : ℝ) = (1 - s - t) * (T.v 0).1 + s * (T.v 1).1 + t * (T.v 2).1 := by
    have := congrArg Prod.fst he
    simp only [toPt, Cycle.V, Prod.fst_add, Prod.fst_sub, Prod.smul_fst, smul_eq_mul] at this
    rw [this]; ring
  have hy : (q.2 : ℝ) = (1 - s - t) * (T.v 0).2 + s * (T.v 1).2 + t * (T.v 2).2 := by
    have := congrArg Prod.snd he
    simp only [toPt, Cycle.V, Prod.snd_add, Prod.snd_sub, Prod.smul_snd, smul_eq_mul] at this
    rw [this]; ring
  have m : ∀ i, i < 3 → i ∈ range T.n := fun i hi => mem_range.mpr (by omega)
  have a0 : (T.xmin : ℝ) ≤ (T.v 0).1 := by exact_mod_cast Finset.inf'_le _ (m 0 (by norm_num))
  have a1 : (T.xmin : ℝ) ≤ (T.v 1).1 := by exact_mod_cast Finset.inf'_le _ (m 1 (by norm_num))
  have a2 : (T.xmin : ℝ) ≤ (T.v 2).1 := by exact_mod_cast Finset.inf'_le _ (m 2 (by norm_num))
  have b0' : (T.v 0).1 ≤ T.xmax := Finset.le_sup' (fun i => (T.v i).1) (m 0 (by norm_num))
  have b0 : ((T.v 0).1 : ℝ) ≤ T.xmax := by exact_mod_cast b0'
  have b1' : (T.v 1).1 ≤ T.xmax := Finset.le_sup' (fun i => (T.v i).1) (m 1 (by norm_num))
  have b1 : ((T.v 1).1 : ℝ) ≤ T.xmax := by exact_mod_cast b1'
  have b2' : (T.v 2).1 ≤ T.xmax := Finset.le_sup' (fun i => (T.v i).1) (m 2 (by norm_num))
  have b2 : ((T.v 2).1 : ℝ) ≤ T.xmax := by exact_mod_cast b2'
  have c0 : (T.ymin : ℝ) ≤ (T.v 0).2 := by exact_mod_cast Finset.inf'_le _ (m 0 (by norm_num))
  have c1 : (T.ymin : ℝ) ≤ (T.v 1).2 := by exact_mod_cast Finset.inf'_le _ (m 1 (by norm_num))
  have c2 : (T.ymin : ℝ) ≤ (T.v 2).2 := by exact_mod_cast Finset.inf'_le _ (m 2 (by norm_num))
  have d0' : (T.v 0).2 ≤ T.ymax := Finset.le_sup' (fun i => (T.v i).2) (m 0 (by norm_num))
  have d0 : ((T.v 0).2 : ℝ) ≤ T.ymax := by exact_mod_cast d0'
  have d1' : (T.v 1).2 ≤ T.ymax := Finset.le_sup' (fun i => (T.v i).2) (m 1 (by norm_num))
  have d1 : ((T.v 1).2 : ℝ) ≤ T.ymax := by exact_mod_cast d1'
  have d2' : (T.v 2).2 ≤ T.ymax := Finset.le_sup' (fun i => (T.v i).2) (m 2 (by norm_num))
  have d2 : ((T.v 2).2 : ℝ) ≤ T.ymax := by exact_mod_cast d2'
  have hr : 0 ≤ 1 - s - t := by linarith
  have e1 : (T.xmin : ℝ) ≤ q.1 := by
    rw [hx]; nlinarith [mul_le_mul_of_nonneg_left a0 hr,
      mul_le_mul_of_nonneg_left a1 hs, mul_le_mul_of_nonneg_left a2 ht]
  have e2 : (q.1 : ℝ) ≤ T.xmax := by
    rw [hx]; nlinarith [mul_le_mul_of_nonneg_left b0 hr,
      mul_le_mul_of_nonneg_left b1 hs, mul_le_mul_of_nonneg_left b2 ht]
  have e3 : (T.ymin : ℝ) ≤ q.2 := by
    rw [hy]; nlinarith [mul_le_mul_of_nonneg_left c0 hr,
      mul_le_mul_of_nonneg_left c1 hs, mul_le_mul_of_nonneg_left c2 ht]
  have e4 : (q.2 : ℝ) ≤ T.ymax := by
    rw [hy]; nlinarith [mul_le_mul_of_nonneg_left d0 hr,
      mul_le_mul_of_nonneg_left d1 hs, mul_le_mul_of_nonneg_left d2 ht]
  unfold Cycle.box
  rw [mem_product, mem_Icc, mem_Icc]
  exact ⟨⟨by exact_mod_cast e1, by exact_mod_cast e2⟩, ⟨by exact_mod_cast e3, by exact_mod_cast e4⟩⟩

lemma tB_sgn (D : ℤ) (hD : D ≠ 0) (l : ℤ) :
    (0 < (l : ℝ) * (D : ℝ) ↔ 0 < Int.sign D * l) ∧ (0 ≤ (l : ℝ) * (D : ℝ) ↔ 0 ≤ Int.sign D * l) ∧
      ((l : ℝ) = 0 ↔ Int.sign D * l = 0) := by
  have c1 : (0 < (l : ℝ) * (D : ℝ) ↔ 0 < l * D) := by norm_cast
  have c2 : (0 ≤ (l : ℝ) * (D : ℝ) ↔ 0 ≤ l * D) := by norm_cast
  have c3 : ((l : ℝ) = 0 ↔ l = 0) := by norm_cast
  rw [c1, c2, c3]
  rcases lt_or_gt_of_ne hD with h | h
  · rw [Int.sign_eq_neg_one_of_neg h]
    refine ⟨⟨fun hh => by nlinarith, fun hh => by nlinarith⟩,
      ⟨fun hh => by nlinarith, fun hh => by nlinarith⟩, ⟨fun hh => by omega, fun hh => by omega⟩⟩
  · rw [Int.sign_eq_one_of_pos h]
    refine ⟨⟨fun hh => by nlinarith, fun hh => by nlinarith⟩,
      ⟨fun hh => by nlinarith, fun hh => by nlinarith⟩, ⟨fun hh => by omega, fun hh => by omega⟩⟩

lemma tB_lat (T : LPoly) (q : ℤ × ℤ) :
    cross (T.V 1 - T.V 0) (toPt q - T.V 0) = ((crossZ (T.v 1 - T.v 0) (q - T.v 0) : ℤ) : ℝ) ∧
    cross (T.V 2 - T.V 1) (toPt q - T.V 1) =
      ((crossZ (T.v 1 - T.v 0) (T.v 2 - T.v 0) - crossZ (T.v 1 - T.v 0) (q - T.v 0) -
        crossZ (q - T.v 0) (T.v 2 - T.v 0) : ℤ) : ℝ) ∧
    cross (T.V 0 - T.V 2) (toPt q - T.V 2) = ((crossZ (q - T.v 0) (T.v 2 - T.v 0) : ℤ) : ℝ) ∧
    cross (T.V 1 - T.V 0) (T.V 2 - T.V 0) = ((crossZ (T.v 1 - T.v 0) (T.v 2 - T.v 0) : ℤ) : ℝ) := by
  simp only [Cycle.V, cross, crossZ, toPt, Prod.fst_sub, Prod.snd_sub]
  push_cast
  refine ⟨by ring, by ring, by ring, by ring⟩

/-- (B5) **Pick's theorem for lattice triangles**, signed form. -/
theorem tri_pick (T : LPoly) (h3 : T.n = 3) :
    T.shoe = Int.sign T.shoe * (2 * (T.I : ℤ) + T.B - 2) := by
  classical
  have hDR := tri_nondeg T h3
  have hDZ : crossZ (T.v 1 - T.v 0) (T.v 2 - T.v 0) ≠ 0 := by
    intro h; apply hDR; rw [(tB_lat T (0, 0)).2.2.2, h]; simp
  have hsg := tB_sgn _ hDZ
  have key : ∀ q : ℤ × ℤ,
      (toPt q ∈ tri (T.V 0) (T.V 1) (T.V 2) ↔ tB_cl (T.v 0) (T.v 1 - T.v 0) (T.v 2 - T.v 0) q) ∧
      (toPt q ∈ T.int ↔ tB_in (T.v 0) (T.v 1 - T.v 0) (T.v 2 - T.v 0) q) ∧
      (toPt q ∈ T.bd ↔ tB_cl (T.v 0) (T.v 1 - T.v 0) (T.v 2 - T.v 0) q ∧ ¬ tB_in (T.v 0) (T.v 1 - T.v 0) (T.v 2 - T.v 0) q) := by
    intro q
    obtain ⟨l1, l2, l3, l4⟩ := tB_lat T q
    rw [tB_tri_iff _ _ _ _ hDR, tB_int_iff T h3, tB_bd_iff T h3, tB_bd3_iff _ _ _ _ hDR]
    simp only [l1, l2, l3, l4, (hsg _).1, (hsg _).2.1, (hsg _).2.2]
    unfold tB_cl tB_in tB_m tB_n tB_N
    simp only [mul_sub]
    generalize (crossZ (T.v 1 - T.v 0) (T.v 2 - T.v 0)).sign * crossZ (T.v 1 - T.v 0) (q - T.v 0) = X
    generalize (crossZ (T.v 1 - T.v 0) (T.v 2 - T.v 0)).sign * crossZ (q - T.v 0) (T.v 2 - T.v 0) = Y
    generalize (crossZ (T.v 1 - T.v 0) (T.v 2 - T.v 0)).sign * crossZ (T.v 1 - T.v 0) (T.v 2 - T.v 0) = Z
    omega
  have hbox : ∀ q, tB_cl (T.v 0) (T.v 1 - T.v 0) (T.v 2 - T.v 0) q → q ∈ T.box :=
    fun q h => tB_mem_box T h3 q ((key q).1.2 h)
  have hincl : ∀ q, tB_in (T.v 0) (T.v 1 - T.v 0) (T.v 2 - T.v 0) q →
      tB_cl (T.v 0) (T.v 1 - T.v 0) (T.v 2 - T.v 0) q := by
    intro q h; unfold tB_in at h; unfold tB_cl; omega
  have hS2 : ∀ q, tB_cl (T.v 0) (T.v 1 - T.v 0) (T.v 2 - T.v 0) q →
      q ∈ T.box ∪ T.box.image (fun q => T.v 0 + T.v 0 + (T.v 1 - T.v 0) + (T.v 2 - T.v 0) - q) :=
    fun q h => mem_union_left _ (hbox q h)
  have hS : ∀ q, tB_par (T.v 0) (T.v 1 - T.v 0) (T.v 2 - T.v 0) q →
      q ∈ T.box ∪ T.box.image (fun q => T.v 0 + T.v 0 + (T.v 1 - T.v 0) + (T.v 2 - T.v 0) - q) := by
    intro q hq
    unfold tB_par at hq
    by_cases hle : tB_m (T.v 0) (T.v 1 - T.v 0) (T.v 2 - T.v 0) q +
        tB_n (T.v 0) (T.v 1 - T.v 0) (T.v 2 - T.v 0) q ≤ tB_N (T.v 1 - T.v 0) (T.v 2 - T.v 0)
    · exact hS2 q ⟨hq.1, hq.2.2.1, hle⟩
    · apply mem_union_right
      refine mem_image.mpr ⟨_, hbox _ ?_, tB_refl_refl _ _ _ q⟩
      unfold tB_cl; rw [tB_m_refl, tB_n_refl]; omega
  have hc := tB_count _ _ _ hDZ _ hS hS2
  have hI : T.I = ((T.box ∪ T.box.image
      (fun q => T.v 0 + T.v 0 + (T.v 1 - T.v 0) + (T.v 2 - T.v 0) - q)).filter
        (tB_in (T.v 0) (T.v 1 - T.v 0) (T.v 2 - T.v 0))).card := by
    unfold Cycle.I
    congr 1
    ext q
    simp only [mem_filter, mem_union]
    rw [(key q).2.1]
    constructor
    · rintro ⟨hq, h⟩; exact ⟨Or.inl hq, h⟩
    · rintro ⟨_, h⟩; exact ⟨hbox q (hincl q h), h⟩
  have hB : T.B = ((T.box ∪ T.box.image
      (fun q => T.v 0 + T.v 0 + (T.v 1 - T.v 0) + (T.v 2 - T.v 0) - q)).filter
        (fun q => tB_cl (T.v 0) (T.v 1 - T.v 0) (T.v 2 - T.v 0) q ∧
          ¬ tB_in (T.v 0) (T.v 1 - T.v 0) (T.v 2 - T.v 0) q)).card := by
    unfold Cycle.B
    congr 1
    ext q
    simp only [mem_filter, mem_union]
    rw [(key q).2.2]
    constructor
    · rintro ⟨hq, h⟩; exact ⟨Or.inl hq, h⟩
    · rintro ⟨_, h⟩; exact ⟨hbox q h.1, h⟩
  have hsplit := card_filter_add_card_filter_not
    (s := (T.box ∪ T.box.image
      (fun q => T.v 0 + T.v 0 + (T.v 1 - T.v 0) + (T.v 2 - T.v 0) - q)).filter
        (tB_cl (T.v 0) (T.v 1 - T.v 0) (T.v 2 - T.v 0)))
    (tB_in (T.v 0) (T.v 1 - T.v 0) (T.v 2 - T.v 0))
  rw [filter_filter, filter_filter] at hsplit
  rw [filter_congr (p := fun q => tB_cl (T.v 0) (T.v 1 - T.v 0) (T.v 2 - T.v 0) q ∧
      tB_in (T.v 0) (T.v 1 - T.v 0) (T.v 2 - T.v 0) q)
      (q := tB_in (T.v 0) (T.v 1 - T.v 0) (T.v 2 - T.v 0))
      (fun q _ => ⟨fun h => h.2, fun h => ⟨hincl q h, h⟩⟩)] at hsplit
  rw [← hI, ← hB] at hsplit
  rw [← hsplit, ← hI] at hc
  push_cast at hc
  rw [tB_shoe T h3]
  unfold tB_N at hc
  rcases lt_or_gt_of_ne hDZ with h | h
  · rw [Int.sign_eq_neg_one_of_neg h] at hc ⊢; linarith
  · rw [Int.sign_eq_one_of_pos h] at hc ⊢; linarith

lemma tB_seg_box (a b q : ℤ × ℤ) (h : toPt q ∈ seg (toPt a) (toPt b)) :
    q ∈ Icc (min a.1 b.1) (max a.1 b.1) ×ˢ Icc (min a.2 b.2) (max a.2 b.2) := by
  obtain ⟨t, ht0, ht1, he⟩ := h
  have hx : (q.1 : ℝ) = a.1 + t * (b.1 - a.1) := by
    have := congrArg Prod.fst he
    simpa [toPt] using this
  have hy : (q.2 : ℝ) = a.2 + t * (b.2 - a.2) := by
    have := congrArg Prod.snd he
    simpa [toPt] using this
  have k1 : ((min a.1 b.1 : ℤ) : ℝ) ≤ q.1 ∧ (q.1 : ℝ) ≤ ((max a.1 b.1 : ℤ) : ℝ) := by
    push_cast
    rcases le_total (a.1 : ℝ) b.1 with h | h
    · rw [min_eq_left h, max_eq_right h]; constructor <;> nlinarith
    · rw [min_eq_right h, max_eq_left h]; constructor <;> nlinarith
  have k2 : ((min a.2 b.2 : ℤ) : ℝ) ≤ q.2 ∧ (q.2 : ℝ) ≤ ((max a.2 b.2 : ℤ) : ℝ) := by
    push_cast
    rcases le_total (a.2 : ℝ) b.2 with h | h
    · rw [min_eq_left h, max_eq_right h]; constructor <;> nlinarith
    · rw [min_eq_right h, max_eq_left h]; constructor <;> nlinarith
  rw [mem_product, mem_Icc, mem_Icc]
  exact ⟨⟨by exact_mod_cast k1.1, by exact_mod_cast k1.2⟩,
    ⟨by exact_mod_cast k2.1, by exact_mod_cast k2.2⟩⟩

open Classical in
/-- (B6) Lattice points on a lattice segment: `gcd(|Δx|,|Δy|) + 1`. -/
theorem seg_lattice_card (a b : ℤ × ℤ) :
    ((Icc (min a.1 b.1) (max a.1 b.1) ×ˢ Icc (min a.2 b.2) (max a.2 b.2)).filter
      (fun q => toPt q ∈ seg (toPt a) (toPt b))).card =
      Int.gcd (b.1 - a.1) (b.2 - a.2) + 1 := by
  set g := Int.gcd (b.1 - a.1) (b.2 - a.2) with hg
  rcases Nat.eq_zero_or_pos g with h0 | hpos
  · rw [h0]
    obtain ⟨hx, hy⟩ := Int.gcd_eq_zero_iff.mp h0
    have hab : b = a := Prod.ext (by omega) (by omega)
    subst hab
    rw [card_eq_one]
    refine ⟨b, ?_⟩
    ext q
    simp only [mem_filter, mem_singleton, min_self, max_self, mem_product, mem_Icc]
    constructor
    · rintro ⟨⟨⟨h1, h2⟩, h3, h4⟩, _⟩; exact Prod.ext (by omega) (by omega)
    · rintro rfl; exact ⟨⟨⟨le_refl _, le_refl _⟩, le_refl _, le_refl _⟩, tB_left_mem _ _⟩
  · have hgR : (g : ℝ) ≠ 0 := by exact_mod_cast hpos.ne'
    obtain ⟨ex, hex⟩ := Int.gcd_dvd_left (b.1 - a.1) (b.2 - a.2)
    obtain ⟨ey, hey⟩ := Int.gcd_dvd_right (b.1 - a.1) (b.2 - a.2)
    rw [← hg] at hex hey
    have hexR : ((b.1 : ℝ) - a.1) = g * ex := by exact_mod_cast hex
    have heyR : ((b.2 : ℝ) - a.2) = g * ey := by exact_mod_cast hey
    have hne : ex ≠ 0 ∨ ey ≠ 0 := by
      by_contra hc
      simp only [not_or, not_not] at hc
      rw [hc.1, mul_zero] at hex; rw [hc.2, mul_zero] at hey
      have := Int.gcd_eq_zero_iff.mpr ⟨hex, hey⟩
      omega
    let f : ℕ → ℤ × ℤ := fun k => (a.1 + k * ex, a.2 + k * ey)
    have himg : ((Icc (min a.1 b.1) (max a.1 b.1) ×ˢ Icc (min a.2 b.2) (max a.2 b.2)).filter
        (fun q => toPt q ∈ seg (toPt a) (toPt b))) = (range (g + 1)).image f := by
      ext q
      simp only [mem_filter, mem_image, mem_range]
      constructor
      · rintro ⟨_, t, ht0, ht1, he⟩
        have h1 : (q.1 : ℝ) - a.1 = t * (g * ex) := by
          have := congrArg Prod.fst he
          simp [toPt] at this; rw [this, ← hexR]; ring
        have h2 : (q.2 : ℝ) - a.2 = t * (g * ey) := by
          have := congrArg Prod.snd he
          simp [toPt] at this; rw [this, ← heyR]; ring
        have hbez := Int.gcd_eq_gcd_ab (b.1 - a.1) (b.2 - a.2)
        rw [← hg] at hbez
        set u := Int.gcdA (b.1 - a.1) (b.2 - a.2)
        set w := Int.gcdB (b.1 - a.1) (b.2 - a.2)
        set k : ℤ := (q.1 - a.1) * u + (q.2 - a.2) * w with hk
        have hbezR : (g : ℝ) = (g * ex) * u + (g * ey) * w := by
          rw [← hexR, ← heyR]; exact_mod_cast hbez
        have hkR : (k : ℝ) = t * g := by
          rw [hk]; push_cast; linear_combination (u : ℝ) * h1 + (w : ℝ) * h2 - t * hbezR
        have hk0 : 0 ≤ k := by
          have : (0 : ℝ) ≤ k := by rw [hkR]; positivity
          exact_mod_cast this
        have hkg : k ≤ g := by
          have : (k : ℝ) ≤ g := by rw [hkR]; nlinarith [(Nat.cast_nonneg g : (0:ℝ) ≤ g)]
          exact_mod_cast this
        refine ⟨k.toNat, by omega, ?_⟩
        have hkk : ((k.toNat : ℕ) : ℤ) = k := Int.toNat_of_nonneg hk0
        have t_eq : t = k / g := by rw [hkR]; field_simp
        apply Prod.ext
        · simp only [f, hkk]
          have : (q.1 : ℝ) = a.1 + k * ex := by
            rw [t_eq] at h1; field_simp at h1; linarith
          exact_mod_cast this.symm
        · simp only [f, hkk]
          have : (q.2 : ℝ) = a.2 + k * ey := by
            rw [t_eq] at h2; field_simp at h2; linarith
          exact_mod_cast this.symm
      · rintro ⟨k, hk, rfl⟩
        have hs : toPt (f k) ∈ seg (toPt a) (toPt b) := by
          refine ⟨k / g, by positivity, ?_, ?_⟩
          · rw [div_le_one (by positivity)]; exact_mod_cast (by omega : k ≤ g)
          · apply Prod.ext
            · simp only [f, toPt, Prod.fst_add, Prod.smul_fst, Prod.fst_sub, smul_eq_mul]
              push_cast; rw [hexR]; field_simp
            · simp only [f, toPt, Prod.snd_add, Prod.smul_snd, Prod.snd_sub, smul_eq_mul]
              push_cast; rw [heyR]; field_simp
        exact ⟨tB_seg_box a b _ hs, hs⟩
    rw [himg, card_image_of_injOn, card_range]
    intro k _ k' _ hkk
    simp only [f, Prod.mk.injEq] at hkk
    obtain ⟨e1, e2⟩ := hkk
    rcases hne with h | h
    · have : (k : ℤ) * ex = k' * ex := by linarith
      exact_mod_cast mul_right_cancel₀ h this
    · have : (k : ℤ) * ey = k' * ey := by linarith
      exact_mod_cast mul_right_cancel₀ h this

end QE.Pick


namespace QE.Pick
open Finset

noncomputable def dC_al (u v w p : Pt) : ℝ := cross (p - v) (w - v) / cross (u - v) (w - v)
noncomputable def dC_be (u v w p : Pt) : ℝ := cross (u - v) (p - v) / cross (u - v) (w - v)

lemma dC_al_aff (u v w p q : Pt) (t : ℝ) :
    dC_al u v w (p + t • (q - p)) = dC_al u v w p + t * (dC_al u v w q - dC_al u v w p) := by
  simp only [dC_al, cross, Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub,
    Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
  ring

lemma dC_be_aff (u v w p q : Pt) (t : ℝ) :
    dC_be u v w (p + t • (q - p)) = dC_be u v w p + t * (dC_be u v w q - dC_be u v w p) := by
  simp only [dC_be, cross, Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub,
    Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
  ring

lemma dC_recon (u v w p : Pt) (hD : cross (u - v) (w - v) ≠ 0) :
    p = v + dC_al u v w p • (u - v) + dC_be u v w p • (w - v) := by
  have hD' : (u.1 - v.1) * (w.2 - v.2) - (u.2 - v.2) * (w.1 - v.1) ≠ 0 := hD
  simp only [dC_al, dC_be, cross]
  ext <;> simp only [Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub,
    Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
  · linear_combination (v.1 - p.1) * mul_inv_cancel₀ hD'
  · linear_combination (v.2 - p.2) * mul_inv_cancel₀ hD'

lemma dC_lin (u v w : Pt) (hD : cross (u - v) (w - v) ≠ 0) (x y : ℝ) :
    dC_al u v w (v + x • (u - v) + y • (w - v)) = x ∧
    dC_be u v w (v + x • (u - v) + y • (w - v)) = y := by
  have hD' : (u.1 - v.1) * (w.2 - v.2) - (u.2 - v.2) * (w.1 - v.1) ≠ 0 := hD
  simp only [dC_al, dC_be, cross, Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub,
    Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
  constructor <;> rw [div_eq_iff hD'] <;> ring

lemma dC_eq_of (u v w p q : Pt) (hD : cross (u - v) (w - v) ≠ 0)
    (h1 : dC_al u v w p = dC_al u v w q) (h2 : dC_be u v w p = dC_be u v w q) : p = q := by
  calc p = _ := dC_recon u v w p hD
    _ = _ := by rw [h1, h2]
    _ = q := (dC_recon u v w q hD).symm

lemma dC_vals (u v w : Pt) (hD : cross (u - v) (w - v) ≠ 0) :
    dC_al u v w u = 1 ∧ dC_be u v w u = 0 ∧ dC_al u v w w = 0 ∧ dC_be u v w w = 1 ∧
    dC_al u v w v = 0 ∧ dC_be u v w v = 0 := by
  refine ⟨div_self hD, ?_, ?_, div_self hD, ?_, ?_⟩ <;>
    simp only [dC_al, dC_be, cross, Prod.fst_sub, Prod.snd_sub] <;> ring

lemma dC_tri_iff (u v w p : Pt) (hD : cross (u - v) (w - v) ≠ 0) :
    p ∈ tri u v w ↔ 0 ≤ dC_al u v w p ∧ 0 ≤ dC_be u v w p ∧
      dC_al u v w p + dC_be u v w p ≤ 1 := by
  constructor
  · rintro ⟨s, t, hs, ht, hst, rfl⟩
    have e : u + s • (v - u) + t • (w - u) = v + (1 - s - t) • (u - v) + t • (w - v) := by
      ext <;> simp <;> ring
    rw [e, (dC_lin u v w hD _ _).1, (dC_lin u v w hD _ _).2]
    refine ⟨by linarith, ht, by linarith⟩
  · rintro ⟨h1, h2, h3⟩
    refine ⟨1 - dC_al u v w p - dC_be u v w p, dC_be u v w p, by linarith, h2, by linarith, ?_⟩
    conv_lhs => rw [dC_recon u v w p hD]
    ext <;> simp <;> ring

lemma dC_seg_param {a b p : Pt} (hp : p ∈ seg a b) (f : Pt → ℝ)
    (hf : ∀ (x y : Pt) (t : ℝ), f (x + t • (y - x)) = f x + t * (f y - f x)) :
    ∃ t, 0 ≤ t ∧ t ≤ 1 ∧ p = a + t • (b - a) ∧ f p = f a + t * (f b - f a) := by
  obtain ⟨t, h0, h1, rfl⟩ := hp
  exact ⟨t, h0, h1, rfl, hf a b t⟩

lemma dC_left_mem (a b : Pt) : a ∈ seg a b := ⟨0, le_refl _, zero_le_one, by simp⟩
lemma dC_right_mem (a b : Pt) : b ∈ seg a b := ⟨1, zero_le_one, le_refl _, by simp⟩

lemma dC_sub_seg {a b p : Pt} (hp : p ∈ seg a b) (r : ℝ) (hr0 : 0 ≤ r) (hr1 : r ≤ 1) :
    p + r • (a - p) ∈ seg a b ∧ p + r • (b - p) ∈ seg a b := by
  obtain ⟨t, h0, h1, rfl⟩ := hp
  constructor
  · refine ⟨t - r * t, by nlinarith, by nlinarith, ?_⟩
    ext <;> simp <;> ring
  · refine ⟨t + r * (1 - t), by nlinarith, by nlinarith, ?_⟩
    ext <;> simp <;> ring

/-- per-index exit parameter -/
noncomputable def dC_ri (a b : ℝ) : ℝ := if b < 0 then a / (a - b) else 1

lemma dC_ri_props (a b : ℝ) (ha : 0 ≤ a) :
    0 ≤ dC_ri a b ∧ dC_ri a b ≤ 1 ∧
    (∀ r, 0 ≤ r → r ≤ dC_ri a b → 0 ≤ a + r * (b - a)) ∧
    (b < 0 → a + dC_ri a b * (b - a) = 0 ∧ dC_ri a b < 1) ∧
    (¬ b < 0 → dC_ri a b = 1) := by
  unfold dC_ri
  split_ifs with hb
  · have hpos : 0 < a - b := by linarith
    refine ⟨div_nonneg ha hpos.le, (div_le_one hpos).2 (by linarith), ?_, ?_, fun h => absurd hb h⟩
    · intro r hr0 hr1
      rw [le_div_iff₀ hpos] at hr1
      nlinarith
    · intro _
      refine ⟨?_, (div_lt_one hpos).2 (by linarith)⟩
      field_simp
      ring
  · refine ⟨zero_le_one, le_refl _, ?_, fun h => absurd h hb, fun _ => rfl⟩
    intro r hr0 hr1
    have hb := not_lt.mp hb
    nlinarith

lemma dC_exit (a1 a2 a3 b1 b2 b3 : ℝ) (h1 : 0 ≤ a1) (h2 : 0 ≤ a2) (h3 : 0 ≤ a3)
    (hb : b1 < 0 ∨ b2 < 0 ∨ b3 < 0) :
    ∃ r, 0 ≤ r ∧ r ≤ 1 ∧ 0 ≤ a1 + r * (b1 - a1) ∧ 0 ≤ a2 + r * (b2 - a2) ∧
      0 ≤ a3 + r * (b3 - a3) ∧
      ((b1 < 0 ∧ a1 + r * (b1 - a1) = 0) ∨ (b2 < 0 ∧ a2 + r * (b2 - a2) = 0) ∨
        (b3 < 0 ∧ a3 + r * (b3 - a3) = 0)) := by
  obtain ⟨p0, p1, p2, p3, p4⟩ := dC_ri_props a1 b1 h1
  obtain ⟨q0, q1, q2, q3, q4⟩ := dC_ri_props a2 b2 h2
  obtain ⟨s0, s1, s2, s3, s4⟩ := dC_ri_props a3 b3 h3
  obtain ⟨r, hr⟩ : ∃ r, r = min (dC_ri a1 b1) (min (dC_ri a2 b2) (dC_ri a3 b3)) := ⟨_, rfl⟩
  have r1 : r ≤ dC_ri a1 b1 := hr ▸ min_le_left _ _
  have r2 : r ≤ dC_ri a2 b2 := hr ▸ le_trans (min_le_right _ _) (min_le_left _ _)
  have r3 : r ≤ dC_ri a3 b3 := hr ▸ le_trans (min_le_right _ _) (min_le_right _ _)
  have r0 : 0 ≤ r := hr ▸ le_min p0 (le_min q0 s0)
  have rlt : r < 1 := by
    rcases hb with hb | hb | hb
    · exact lt_of_le_of_lt r1 (p3 hb).2
    · exact lt_of_le_of_lt r2 (q3 hb).2
    · exact lt_of_le_of_lt r3 (s3 hb).2
  refine ⟨r, r0, rlt.le, p2 r r0 r1, q2 r r0 r2, s2 r r0 r3, ?_⟩
  rcases min_choice (dC_ri a1 b1) (min (dC_ri a2 b2) (dC_ri a3 b3)) with e | e
  · rw [← hr] at e
    by_cases hb1 : b1 < 0
    · exact Or.inl ⟨hb1, by rw [e]; exact (p3 hb1).1⟩
    · rw [p4 hb1] at e; linarith
  · rcases min_choice (dC_ri a2 b2) (dC_ri a3 b3) with e' | e'
    · have e : r = dC_ri a2 b2 := hr.trans (e.trans e')
      by_cases hb2 : b2 < 0
      · exact Or.inr (Or.inl ⟨hb2, by rw [e]; exact (q3 hb2).1⟩)
      · rw [q4 hb2] at e; linarith
    · have e : r = dC_ri a3 b3 := hr.trans (e.trans e')
      by_cases hb3 : b3 < 0
      · exact Or.inr (Or.inr ⟨hb3, by rw [e]; exact (s3 hb3).1⟩)
      · rw [s4 hb3] at e; linarith



lemma dC_ivt (A B c : ℝ) (h : (A ≤ c ∧ c ≤ B) ∨ (B ≤ c ∧ c ≤ A)) :
    ∃ s, 0 ≤ s ∧ s ≤ 1 ∧ A + s * (B - A) = c := by
  by_cases hAB : A = B
  · refine ⟨0, le_refl _, zero_le_one, ?_⟩
    subst hAB; rcases h with h | h <;> linarith [h.1, h.2]
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · have hpos : 0 < B - A := lt_of_le_of_ne (by linarith) (fun h => hAB (by linarith))
    refine ⟨(c - A) / (B - A), div_nonneg (by linarith) hpos.le,
      (div_le_one hpos).2 (by linarith), ?_⟩
    field_simp; ring
  · have hpos : 0 < A - B := lt_of_le_of_ne (by linarith) (fun h => hAB (by linarith))
    refine ⟨(A - c) / (A - B), div_nonneg (by linarith) hpos.le,
      (div_le_one hpos).2 (by linarith), ?_⟩
    field_simp; ring

lemma dC_par (a b : Pt) (ha : 0 < a.1 ∨ (a.1 = 0 ∧ 0 < a.2)) (hb : 0 < b.1 ∨ (b.1 = 0 ∧ 0 < b.2))
    (hc : cross a b = 0) :
    (∃ t : ℝ, 0 ≤ t ∧ t ≤ 1 ∧ b = t • a) ∨ (∃ t : ℝ, 0 ≤ t ∧ t ≤ 1 ∧ a = t • b) := by
  unfold cross at hc
  rcases ha with ha | ⟨ha1, ha2⟩ <;> rcases hb with hb | ⟨hb1, hb2⟩
  · by_cases h : b.1 ≤ a.1
    · left
      refine ⟨b.1 / a.1, div_nonneg hb.le ha.le, (div_le_one ha).2 h, ?_⟩
      ext <;> simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul] <;> field_simp <;> linarith
    · right
      refine ⟨a.1 / b.1, div_nonneg ha.le hb.le, (div_le_one hb).2 (by linarith), ?_⟩
      ext <;> simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul] <;> field_simp <;> linarith
  · rw [hb1] at hc
    have : a.1 * b.2 = 0 := by linarith
    exact absurd this (mul_pos ha hb2).ne'
  · rw [ha1] at hc
    have : a.2 * b.1 = 0 := by linarith
    exact absurd this (mul_pos ha2 hb).ne'
  · by_cases h : b.2 ≤ a.2
    · left
      refine ⟨b.2 / a.2, div_nonneg hb2.le ha2.le, (div_le_one ha2).2 h, ?_⟩
      ext <;> simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul, ha1, hb1] <;> field_simp <;> simp
    · right
      refine ⟨a.2 / b.2, div_nonneg ha2.le hb2.le, (div_le_one hb2).2 (by linarith), ?_⟩
      ext <;> simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul, ha1, hb1] <;> field_simp <;> simp

lemma dC_lexpos (a b : ℤ × ℤ) (h : lexlt a b) :
    0 < (toPt b - toPt a).1 ∨ ((toPt b - toPt a).1 = 0 ∧ 0 < (toPt b - toPt a).2) := by
  simp only [toPt, Prod.fst_sub, Prod.snd_sub]
  rcases h with h | ⟨h1, h2⟩
  · left; exact sub_pos.2 (by exact_mod_cast h)
  · right; exact ⟨by rw [h1]; ring, sub_pos.2 (by exact_mod_cast h2)⟩

lemma dC_toPt_inj {a b : ℤ × ℤ} (h : toPt a = toPt b) : a = b := by
  simp only [toPt, Prod.mk.injEq, Int.cast_inj] at h
  exact Prod.ext h.1 h.2

lemma dC_inj (P : LPoly) (i j : ℕ) (hi : i < P.n) (hj : j < P.n) (h : P.V i = P.V j) : i = j :=
  P.inj i j hi hj (dC_toPt_inj h)

lemma dC_vn (P : LPoly) : P.V P.n = P.V 0 := by
  show toPt (P.v P.n) = toPt (P.v 0)
  have := P.per 0
  rw [zero_add] at this
  rw [this]

lemma dC_edge_last (P : LPoly) : P.edge (P.n - 1) = seg (P.V (P.n - 1)) (P.V 0) := by
  have : P.n - 1 + 1 = P.n := by have := P.three; omega
  show seg (P.V (P.n - 1)) (P.V (P.n - 1 + 1)) = _
  rw [this, dC_vn]

lemma dC_simple (P : LPoly) (i j : ℕ) (hi : i < P.n) (hj : j < P.n) (hij : i ≠ j) (p : Pt)
    (h1 : p ∈ P.edge i) (h2 : p ∈ P.edge j) :
    (j = (i + 1) % P.n ∧ p = P.V (i + 1)) ∨ (i = (j + 1) % P.n ∧ p = P.V (j + 1)) :=
  P.simple i j hi hj hij p h1 h2

lemma dC_e0_last (P : LPoly) (p : Pt) (h1 : p ∈ P.edge 0) (h2 : p ∈ P.edge (P.n - 1)) :
    p = P.V 0 := by
  have hn := P.three
  rcases dC_simple P 0 (P.n - 1) (by omega) (by omega) (by omega) p h1 h2 with ⟨h, _⟩ | ⟨_, h⟩
  · rw [Nat.mod_eq_of_lt (by omega)] at h; omega
  · rw [h, show P.n - 1 + 1 = P.n by omega, dC_vn]

lemma dC_sub_uv (P : LPoly) (j : ℕ) (hj : j < P.n) (hj0 : j ≠ 0) (hj1 : j ≠ P.n - 1) (q : Pt)
    (hq : q ∈ P.edge j) (hq' : q ∈ P.edge (P.n - 1)) : j = P.n - 2 ∧ q = P.V (P.n - 1) := by
  have hn := P.three
  rcases dC_simple P j (P.n - 1) hj (by omega) hj1 q hq hq' with ⟨h, h'⟩ | ⟨h, _⟩
  · rw [Nat.mod_eq_of_lt (by omega)] at h
    refine ⟨by omega, ?_⟩
    rw [h', show j + 1 = P.n - 1 by omega]
  · rw [show P.n - 1 + 1 = P.n by omega, Nat.mod_self] at h; omega

lemma dC_sub_vw (P : LPoly) (j : ℕ) (hj : j < P.n) (hj0 : j ≠ 0) (hj1 : j ≠ P.n - 1) (q : Pt)
    (hq : q ∈ P.edge j) (hq' : q ∈ P.edge 0) : j = 1 ∧ q = P.V 1 := by
  have hn := P.three
  rcases dC_simple P j 0 hj (by omega) hj0 q hq hq' with ⟨h, _⟩ | ⟨h, h'⟩
  · rw [Nat.mod_eq_of_lt (by omega)] at h; omega
  · rw [Nat.mod_eq_of_lt (by omega)] at h
    exact ⟨h, h'⟩

theorem lexmin_nondeg (P : LPoly) (h0 : ∀ j, 0 < j → j < P.n → lexlt (P.v 0) (P.v j)) :
    cross (P.V (P.n - 1) - P.V 0) (P.V 1 - P.V 0) ≠ 0 := by
  intro hc
  have hn := P.three
  have ha := dC_lexpos _ _ (h0 (P.n - 1) (by omega) (by omega))
  have hb := dC_lexpos _ _ (h0 1 (by omega) (by omega))
  rcases dC_par _ _ ha hb hc with ⟨t, ht0, ht1, ht⟩ | ⟨t, ht0, ht1, ht⟩
  · have hw : P.V 1 ∈ P.edge (P.n - 1) := by
      rw [dC_edge_last]
      refine ⟨1 - t, by linarith, by linarith, ?_⟩
      have e : P.V 1 = P.V 0 + t • (P.V (P.n - 1) - P.V 0) := by
        rw [← sub_eq_iff_eq_add']; exact ht
      rw [e]; ext <;> simp <;> ring
    have := dC_e0_last P _ (dC_right_mem (P.V 0) (P.V 1)) hw
    exact absurd (dC_inj P 1 0 (by omega) (by omega) this) (by norm_num)
  · have hu : P.V (P.n - 1) ∈ P.edge 0 := by
      refine ⟨t, ht0, ht1, ?_⟩
      rw [← sub_eq_iff_eq_add']; exact ht
    have := dC_e0_last P _ hu (dC_left_mem _ _)
    have := dC_inj P (P.n - 1) 0 (by omega) (by omega) this
    omega



lemma dC_cvx (A B X t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (h : X = A + t * (B - A)) :
    X ≤ A ∨ X ≤ B := by
  by_contra hc
  simp only [not_or, not_le] at hc
  rcases ht0.lt_or_eq with ht | ht
  · nlinarith [mul_lt_mul_of_pos_left hc.2 ht, mul_le_mul_of_nonneg_left hc.1.le (sub_nonneg.2 ht1)]
  · subst ht; linarith

lemma dC_hE (P : LPoly) (hD : cross (P.V (P.n - 1) - P.V 0) (P.V 1 - P.V 0) ≠ 0)
    (j : ℕ) (hj : j < P.n) (hj0 : j ≠ 0) (hj1 : j ≠ P.n - 1) (q : Pt) (hq : q ∈ P.edge j)
    (hqT : q ∈ tri (P.V (P.n - 1)) (P.V 0) (P.V 1)) :
    (dC_al (P.V (P.n - 1)) (P.V 0) (P.V 1) q = 0 → j = 1 ∧ q = P.V 1) ∧
    (dC_be (P.V (P.n - 1)) (P.V 0) (P.V 1) q = 0 → j = P.n - 2 ∧ q = P.V (P.n - 1)) := by
  obtain ⟨h1, h2, h3⟩ := (dC_tri_iff _ _ _ q hD).1 hqT
  have hr := dC_recon _ _ _ q hD
  constructor
  · intro ha
    apply dC_sub_vw P j hj hj0 hj1 q hq
    refine ⟨dC_be (P.V (P.n - 1)) (P.V 0) (P.V 1) q, h2, by linarith, ?_⟩
    rw [ha, zero_smul, add_zero] at hr
    exact hr
  · intro hb
    apply dC_sub_uv P j hj hj0 hj1 q hq
    rw [dC_edge_last]
    refine ⟨1 - dC_al (P.V (P.n - 1)) (P.V 0) (P.V 1) q, by linarith, by linarith, ?_⟩
    rw [hb, zero_smul, add_zero] at hr
    calc q = _ := hr
      _ = _ := by ext <;> simp <;> ring

lemma dC_key (u v w : Pt) (hD : cross (u - v) (w - v) ≠ 0) (E : Set Pt)
    (hE : ∀ q ∈ E, q ∈ tri u v w → dC_al u v w q = 0 ∨ dC_be u v w q = 0 → q = u ∨ q = w)
    (p y : Pt) (hpy : ∀ r : ℝ, 0 ≤ r → r ≤ 1 → p + r • (y - p) ∈ E) (hpT : p ∈ tri u v w)
    (ha : 0 < dC_al u v w p) (hb : 0 < dC_be u v w p) (hy : y ∉ tri u v w)
    (hH : 1 - dC_al u v w p - dC_be u v w p ≤ 1 - dC_al u v w y - dC_be u v w y)
    (hH' : 0 < 1 - dC_al u v w p - dC_be u v w p ∨
      1 - dC_al u v w p - dC_be u v w p < 1 - dC_al u v w y - dC_be u v w y) : False := by
  obtain ⟨au, bu, aw, bw, -, -⟩ := dC_vals u v w hD
  obtain ⟨p1, p2, p3⟩ := (dC_tri_iff u v w p hD).1 hpT
  have hy' : dC_al u v w y < 0 ∨ dC_be u v w y < 0 ∨
      1 - dC_al u v w y - dC_be u v w y < 0 := by
    by_contra hc
    simp only [not_or, not_lt] at hc
    exact hy ((dC_tri_iff u v w y hD).2 ⟨hc.1, hc.2.1, by linarith [hc.2.2]⟩)
  obtain ⟨r, r0, r1, g1, g2, g3, hcase⟩ := dC_exit _ _ _ _ _ _ p1 p2
    (by linarith : (0:ℝ) ≤ 1 - dC_al u v w p - dC_be u v w p) hy'
  have qa := dC_al_aff u v w p y r
  have qb := dC_be_aff u v w p y r
  have hqT : p + r • (y - p) ∈ tri u v w :=
    (dC_tri_iff u v w _ hD).2 ⟨by rw [qa]; exact g1, by rw [qb]; exact g2, by
      rw [qa, qb]; linarith⟩
  have fin : dC_al u v w (p + r • (y - p)) = 0 ∨ dC_be u v w (p + r • (y - p)) = 0 → False := by
    intro hab
    have Hq0 : 1 - dC_al u v w (p + r • (y - p)) - dC_be u v w (p + r • (y - p)) = 0 := by
      rcases hE _ (hpy r r0 r1) hqT hab with h | h <;> rw [h] <;> simp [au, bu, aw, bw]
    rw [qa, qb] at Hq0 hab
    rcases hH' with h | h
    · nlinarith
    · have hr0 : r = 0 := by nlinarith
      subst hr0
      rcases hab with h | h <;> linarith
  rcases hcase with ⟨-, h⟩ | ⟨-, h⟩ | ⟨h, -⟩
  · exact fin (Or.inl (by rw [qa]; exact h))
  · exact fin (Or.inr (by rw [qb]; exact h))
  · linarith

theorem diag_exists (P : LPoly) (h4 : 4 ≤ P.n)
    (h0 : ∀ j, 0 < j → j < P.n → lexlt (P.v 0) (P.v j)) :
    ((∀ p ∈ tri (P.V (P.n - 1)) (P.V 0) (P.V 1), p ≠ P.V (P.n - 1) → p ≠ P.V 1 →
        ∀ j < P.n, p ∈ P.edge j → j = P.n - 1 ∨ j = 0) ∧
      (∀ x ∈ seg (P.V (P.n - 1)) (P.V 1), x ∈ P.bd → x = P.V (P.n - 1) ∨ x = P.V 1)) ∨
    (∃ k, 2 ≤ k ∧ k + 2 ≤ P.n ∧
      (∀ x ∈ seg (P.V 0) (P.V k), x ∈ P.bd → x = P.V 0 ∨ x = P.V k) ∧
      inOpenCone (P.V (P.n - 1) - P.V 0) (P.V 1 - P.V 0) (P.V k - P.V 0)) := by
  classical
  have hD := lexmin_nondeg P h0
  have hEj : ∀ j, j < P.n → j ≠ 0 → j ≠ P.n - 1 → ∀ q ∈ P.edge j,
      q ∈ tri (P.V (P.n - 1)) (P.V 0) (P.V 1) →
      dC_al (P.V (P.n - 1)) (P.V 0) (P.V 1) q = 0 ∨ dC_be (P.V (P.n - 1)) (P.V 0) (P.V 1) q = 0 →
      q = P.V (P.n - 1) ∨ q = P.V 1 := by
    intro j hj hj0 hj1 q hq hqT hab
    rcases hab with h | h
    · exact Or.inr ((dC_hE P hD j hj hj0 hj1 q hq hqT).1 h).2
    · exact Or.inl ((dC_hE P hD j hj hj0 hj1 q hq hqT).2 h).2
  have hHaff : ∀ (x y : Pt) (t : ℝ),
      (fun q => 1 - dC_al (P.V (P.n - 1)) (P.V 0) (P.V 1) q - dC_be (P.V (P.n - 1)) (P.V 0) (P.V 1) q)
        (x + t • (y - x)) =
      (fun q => 1 - dC_al (P.V (P.n - 1)) (P.V 0) (P.V 1) q - dC_be (P.V (P.n - 1)) (P.V 0) (P.V 1) q) x +
        t * ((fun q => 1 - dC_al (P.V (P.n - 1)) (P.V 0) (P.V 1) q -
          dC_be (P.V (P.n - 1)) (P.V 0) (P.V 1) q) y -
        (fun q => 1 - dC_al (P.V (P.n - 1)) (P.V 0) (P.V 1) q -
          dC_be (P.V (P.n - 1)) (P.V 0) (P.V 1) q) x) := by
    intro x y t
    simp only [dC_al_aff, dC_be_aff]; ring
  set u := P.V (P.n - 1) with hu
  set v := P.V 0 with hv
  set w := P.V 1 with hw
  obtain ⟨au, bu, aw, bw, av, bv⟩ := dC_vals u v w hD
  have hseg_i : ∀ j, j < P.n → ∀ p ∈ P.edge j, ∀ i, (i = j ∨ i = j + 1) →
      ∀ r : ℝ, 0 ≤ r → r ≤ 1 → p + r • (P.V i - p) ∈ P.edge j := by
    intro j _ p hp i hi r r0 r1
    rcases hi with rfl | rfl
    · exact (dC_sub_seg hp r r0 r1).1
    · exact (dC_sub_seg hp r r0 r1).2
  let Zs := (range P.n).filter (fun k => k ≠ 0 ∧ k ≠ 1 ∧ k ≠ P.n - 1 ∧ P.V k ∈ tri u v w)
  by_cases hZ : Zs.Nonempty
  · right
    obtain ⟨k, hk, hmax⟩ := Zs.exists_max_image
      (fun k => 1 - dC_al u v w (P.V k) - dC_be u v w (P.V k)) hZ
    simp only [Zs, Finset.mem_filter, Finset.mem_range] at hk hmax
    obtain ⟨hkn, hk0, hk1, hkl, hkT⟩ := hk
    have hzT := (dC_tri_iff u v w (P.V k) hD).1 hkT
    have hzk : P.V k ∈ P.edge k := dC_left_mem _ _
    have haz : 0 < dC_al u v w (P.V k) := by
      rcases hzT.1.lt_or_eq with h | h
      · exact h
      · exact absurd ((dC_hE P hD k hkn hk0 hkl _ hzk hkT).1 h.symm).1 hk1
    have hbz : 0 < dC_be u v w (P.V k) := by
      rcases hzT.2.1.lt_or_eq with h | h
      · exact h
      · exact absurd (dC_inj P k (P.n - 1) hkn (by omega)
          ((dC_hE P hD k hkn hk0 hkl _ hzk hkT).2 h.symm).2) hkl
    refine ⟨k, by omega, by omega, ?_, ?_⟩
    · intro x hx hxbd
      obtain ⟨j, hj, hxe⟩ := hxbd
      by_contra hne
      simp only [not_or] at hne
      obtain ⟨s, hs0, hs1, rfl⟩ := hx
      have hs0' : s ≠ 0 := by rintro rfl; apply hne.1; simp
      have hs1' : s ≠ 1 := by rintro rfl; apply hne.2; simp
      have hs0'' : 0 < s := lt_of_le_of_ne hs0 (Ne.symm hs0')
      have hs1'' : s < 1 := lt_of_le_of_ne hs1 hs1'
      have hax : dC_al u v w (v + s • (P.V k - v)) = s * dC_al u v w (P.V k) := by
        rw [dC_al_aff, av]; ring
      have hbx : dC_be u v w (v + s • (P.V k - v)) = s * dC_be u v w (P.V k) := by
        rw [dC_be_aff, bv]; ring
      have hxT : v + s • (P.V k - v) ∈ tri u v w := (dC_tri_iff u v w _ hD).2
        ⟨by rw [hax]; positivity, by rw [hbx]; positivity, by rw [hax, hbx]; nlinarith⟩
      have hj1 : j ≠ P.n - 1 := by
        rintro rfl
        rw [dC_edge_last] at hxe
        obtain ⟨t, -, -, ht⟩ := hxe
        have e : dC_be u v w (v + s • (P.V k - v)) = 0 := by
          rw [ht, dC_be_aff, bu, bv]; ring
        rw [hbx] at e
        nlinarith
      have hj0 : j ≠ 0 := by
        rintro rfl
        obtain ⟨t, -, -, ht⟩ := hxe
        have e : dC_al u v w (v + s • (P.V k - v)) = 0 := by
          rw [ht, dC_al_aff, av, aw]; ring
        rw [hax] at e
        nlinarith
      obtain ⟨t, ht0, ht1, -, hHt⟩ := dC_seg_param hxe (fun q => 1 - dC_al u v w q - dC_be u v w q) hHaff
      try simp only at hHt
      have key : ∀ i, (i = j ∨ i = j + 1) →
          1 - dC_al u v w (v + s • (P.V k - v)) - dC_be u v w (v + s • (P.V k - v)) ≤
            1 - dC_al u v w (P.V i) - dC_be u v w (P.V i) → False := by
        intro i hi hHi
        have hin : i < P.n := by omega
        have hi0 : i ≠ 0 := by omega
        by_cases hiT : P.V i ∈ tri u v w
        · by_cases hi1 : i = 1
          · rw [hi1, ← hw, aw, bw, hax, hbx] at hHi; nlinarith
          by_cases hil : i = P.n - 1
          · rw [hil, ← hu, au, bu, hax, hbx] at hHi; nlinarith
          have := hmax i ⟨hin, hi0, hi1, hil, hiT⟩
          rw [hax, hbx] at hHi
          nlinarith
        · refine dC_key u v w hD (P.edge j) (hEj j hj hj0 hj1) _ (P.V i)
            (hseg_i j hj _ hxe i hi) hxT (by rw [hax]; positivity) (by rw [hbx]; positivity)
            hiT hHi (Or.inl ?_)
          rw [hax, hbx]; nlinarith
      rcases dC_cvx _ _ _ t ht0 ht1 hHt with h | h
      · exact key j (Or.inl rfl) h
      · exact key (j + 1) (Or.inr rfl) h
    · have hD' : cross (u - v) (w - v) ≠ 0 := hD
      have e1 : cross (u - v) (P.V k - v) = dC_be u v w (P.V k) * cross (u - v) (w - v) := by
        unfold dC_be; field_simp
      have e2 : cross (P.V k - v) (w - v) = dC_al u v w (P.V k) * cross (u - v) (w - v) := by
        unfold dC_al; field_simp
      have hsq : 0 < cross (u - v) (w - v) * cross (u - v) (w - v) := mul_self_pos.2 hD'
      refine ⟨?_, ?_⟩
      · rw [e1, mul_assoc]; positivity
      · rw [e2, mul_assoc]; positivity
  · left
    have hZ' : ∀ i, i < P.n → i ≠ 0 → i ≠ 1 → i ≠ P.n - 1 → P.V i ∉ tri u v w := by
      intro i hi h0 h1 h2 hT
      exact hZ ⟨i, by simp only [Zs, Finset.mem_filter, Finset.mem_range]; exact ⟨hi, h0, h1, h2, hT⟩⟩
    have hvert : ∀ i, i < P.n → i ≠ 0 → P.V i ∈ tri u v w → P.V i = u ∨ P.V i = w := by
      intro i hi h0 hT
      by_cases h1 : i = 1
      · right; rw [h1]
      by_cases h2 : i = P.n - 1
      · left; rw [h2]
      exact absurd hT (hZ' i hi h0 h1 h2)
    have part1 : ∀ p ∈ tri u v w, p ≠ u → p ≠ w → ∀ j < P.n, p ∈ P.edge j →
        j = P.n - 1 ∨ j = 0 := by
      intro p hpT hpu hpw j hj hpe
      by_contra hc
      simp only [not_or] at hc
      obtain ⟨hj1, hj0⟩ := hc
      have hTp := (dC_tri_iff u v w p hD).1 hpT
      have hap : 0 < dC_al u v w p := lt_of_le_of_ne hTp.1
        (fun h => (hEj j hj hj0 hj1 p hpe hpT (Or.inl h.symm)).elim hpu hpw)
      have hbp : 0 < dC_be u v w p := lt_of_le_of_ne hTp.2.1
        (fun h => (hEj j hj hj0 hj1 p hpe hpT (Or.inr h.symm)).elim hpu hpw)
      obtain ⟨t, ht0, ht1, hpt, hHt⟩ := dC_seg_param hpe (fun q => 1 - dC_al u v w q - dC_be u v w q) hHaff
      try simp only at hHt
      have hHend : ∀ i, (i = j ∨ i = j + 1) → P.V i ∈ tri u v w →
          1 - dC_al u v w (P.V i) - dC_be u v w (P.V i) = 0 := by
        intro i hi hiT
        rcases hvert i (by omega) (by omega) hiT with h | h <;> rw [h] <;> simp [au, bu, aw, bw]
      have hA : 1 - dC_al u v w p - dC_be u v w p = 0 := by
        by_contra hne
        have hpos : 0 < 1 - dC_al u v w p - dC_be u v w p :=
          lt_of_le_of_ne (by linarith [hTp.2.2]) (Ne.symm hne)
        have hh : ∀ i, (i = j ∨ i = j + 1) → 1 - dC_al u v w p - dC_be u v w p ≤
            1 - dC_al u v w (P.V i) - dC_be u v w (P.V i) → False := by
          intro i hi hge
          by_cases hiT : P.V i ∈ tri u v w
          · rw [hHend i hi hiT] at hge; linarith
          · exact dC_key u v w hD (P.edge j) (hEj j hj hj0 hj1) p (P.V i)
              (hseg_i j hj p hpe i hi) hpT hap hbp hiT hge (Or.inl hpos)
        rcases dC_cvx _ _ _ t ht0 ht1 hHt with h | h
        · exact hh j (Or.inl rfl) h
        · exact hh (j + 1) (Or.inr rfl) h
      have hB : ∀ i, (i = j ∨ i = j + 1) → 1 - dC_al u v w (P.V i) - dC_be u v w (P.V i) ≤ 0 := by
        intro i hi
        by_contra hgt
        rw [not_le] at hgt
        by_cases hiT : P.V i ∈ tri u v w
        · rw [hHend i hi hiT] at hgt; linarith
        · exact dC_key u v w hD (P.edge j) (hEj j hj hj0 hj1) p (P.V i)
            (hseg_i j hj p hpe i hi) hpT hap hbp hiT (by linarith) (Or.inr (by linarith))
      have hp_vert : ∀ i, (i = j ∨ i = j + 1) → p = P.V i → False := by
        intro i hi he
        rcases hvert i (by omega) (by omega) (he ▸ hpT) with h | h
        · exact hpu (he.trans h)
        · exact hpw (he.trans h)
      have hC1 : 1 - dC_al u v w (P.V j) - dC_be u v w (P.V j) = 0 := by
        by_contra hne
        have hlt := lt_of_le_of_ne (hB j (Or.inl rfl)) hne
        have hB2 := hB (j + 1) (Or.inr rfl)
        have : t = 1 := by nlinarith
        apply hp_vert (j + 1) (Or.inr rfl)
        rw [hpt, this]; simp
      have hC2 : 1 - dC_al u v w (P.V (j + 1)) - dC_be u v w (P.V (j + 1)) = 0 := by
        by_contra hne
        have hlt := lt_of_le_of_ne (hB (j + 1) (Or.inr rfl)) hne
        have : t = 0 := by nlinarith
        apply hp_vert j (Or.inl rfl)
        rw [hpt, this]; simp
      have hαp : dC_al u v w p = dC_al u v w (P.V j) +
          t * (dC_al u v w (P.V (j + 1)) - dC_al u v w (P.V j)) := by
        rw [hpt, dC_al_aff]
      have hαend : ∀ i, (i = j ∨ i = j + 1) →
          1 - dC_al u v w (P.V i) - dC_be u v w (P.V i) = 0 →
          dC_al u v w (P.V i) ≤ 0 ∨ 1 ≤ dC_al u v w (P.V i) := by
        intro i hi hH0
        by_cases hiT : P.V i ∈ tri u v w
        · rcases hvert i (by omega) (by omega) hiT with h | h
          · right; rw [h, au]
          · left; rw [h, aw]
        · rw [dC_tri_iff u v w _ hD] at hiT
          by_contra hc
          simp only [not_or, not_le] at hc
          exact hiT ⟨hc.1.le, by linarith, by linarith⟩
      have e1 := hαend j (Or.inl rfl) hC1
      have e2 := hαend (j + 1) (Or.inr rfl) hC2
      have hp1 : dC_al u v w p < 1 := by linarith
      have hfind : ∀ c : ℝ, (dC_al u v w (P.V j) ≤ c ∧ c ≤ dC_al u v w (P.V (j + 1))) ∨
          (dC_al u v w (P.V (j + 1)) ≤ c ∧ c ≤ dC_al u v w (P.V j)) →
          ∃ q ∈ P.edge j, dC_al u v w q = c ∧ 1 - dC_al u v w q - dC_be u v w q = 0 := by
        intro c hc
        obtain ⟨s, s0, s1, hs⟩ := dC_ivt _ _ c hc
        refine ⟨P.V j + s • (P.V (j + 1) - P.V j), ⟨s, s0, s1, rfl⟩, ?_, ?_⟩
        · rw [dC_al_aff]; exact hs
        · have := hHaff (P.V j) (P.V (j + 1)) s
          simp only at this
          rw [this, hC1, hC2]; ring
      have mixed : (dC_al u v w (P.V j) ≤ 0 ∧ 1 ≤ dC_al u v w (P.V (j + 1))) ∨
          (dC_al u v w (P.V (j + 1)) ≤ 0 ∧ 1 ≤ dC_al u v w (P.V j)) := by
        rcases e1 with e1 | e1 <;> rcases e2 with e2 | e2
        · exfalso; nlinarith
        · exact Or.inl ⟨e1, e2⟩
        · exact Or.inr ⟨e2, e1⟩
        · exfalso; nlinarith
      obtain ⟨q1, hq1e, hq1a, hq1H⟩ := hfind 1 (by
        rcases mixed with h | h
        · exact Or.inl ⟨by linarith, h.2⟩
        · exact Or.inr ⟨by linarith, h.2⟩)
      obtain ⟨q0, hq0e, hq0a, hq0H⟩ := hfind 0 (by
        rcases mixed with h | h
        · exact Or.inl ⟨h.1, by linarith⟩
        · exact Or.inr ⟨h.1, by linarith⟩)
      have hq1T : q1 ∈ tri u v w := (dC_tri_iff u v w q1 hD).2 ⟨by linarith, by linarith, by linarith⟩
      have hq0T : q0 ∈ tri u v w := (dC_tri_iff u v w q0 hD).2 ⟨by linarith, by linarith, by linarith⟩
      have r1 := ((dC_hE P hD j hj hj0 hj1 q1 hq1e hq1T).2 (by linarith)).1
      have r0 := ((dC_hE P hD j hj hj0 hj1 q0 hq0e hq0T).1 hq0a).1
      omega
    refine ⟨part1, ?_⟩
    intro x hx hxbd
    by_contra hne
    simp only [not_or] at hne
    obtain ⟨j, hj, hxe⟩ := hxbd
    obtain ⟨t, ht0, ht1, rfl⟩ := hx
    have hax : dC_al u v w (u + t • (w - u)) = 1 - t := by rw [dC_al_aff, au, aw]; ring
    have hbx : dC_be u v w (u + t • (w - u)) = t := by rw [dC_be_aff, bu, bw]; ring
    have hxT : u + t • (w - u) ∈ tri u v w := (dC_tri_iff u v w _ hD).2
      ⟨by rw [hax]; linarith, by rw [hbx]; linarith, by rw [hax, hbx]; linarith⟩
    rcases part1 _ hxT hne.1 hne.2 j hj hxe with rfl | rfl
    · rw [dC_edge_last] at hxe
      obtain ⟨t', -, -, ht'⟩ := hxe
      have e : dC_be u v w (u + t • (w - u)) = 0 := by rw [ht', dC_be_aff, bu, bv]; ring
      rw [hbx] at e
      apply hne.1; rw [e]; simp
    · obtain ⟨t', -, -, ht'⟩ := hxe
      have e : dC_al u v w (u + t • (w - u)) = 0 := by rw [ht', dC_al_aff, av, aw]; ring
      rw [hax] at e
      have : t = 1 := by linarith
      apply hne.2; rw [this]; simp

end QE.Pick


/-! Task D: rotation, splitting along a diagonal, and lattice-point bookkeeping. -/

namespace QE.Pick
open Finset

lemma sD_per_mod {α : Type*} (f : ℕ → α) (n : ℕ) (h : ∀ i, f (i + n) = f i) (m : ℕ) :
    f m = f (m % n) := by
  have key : ∀ q a, f (a + n * q) = f a := by
    intro q
    induction q with
    | zero => intro a; simp
    | succ q ih => intro a; rw [Nat.mul_succ, ← Nat.add_assoc, h, ih]
  conv_lhs => rw [← Nat.mod_add_div m n]
  exact key _ _

lemma sD_sum_shift (f : ℕ → ℤ) (n : ℕ) (h : ∀ i, f (i + n) = f i) (r : ℕ) :
    ∑ i ∈ range n, f (i + r) = ∑ i ∈ range n, f i := by
  induction r with
  | zero => simp
  | succ r ih =>
    have e : ∑ i ∈ range n, f (i + (r + 1)) = ∑ i ∈ range n, f ((i + 1) + r) := by
      apply sum_congr rfl; intro i _; congr 1; omega
    have h1 := Finset.sum_range_succ (fun i => f (i + r)) n
    have h2 := Finset.sum_range_succ' (fun i => f (i + r)) n
    have h3 : f (n + r) = f (0 + r) := by rw [zero_add, add_comm, h]
    rw [e, ← ih]
    linarith

lemma sD_exists_pre (n r j : ℕ) (hn : 0 < n) (hj : j < n) : ∃ i < n, (i + r) % n = j := by
  refine ⟨(j + n * r - r) % n, Nat.mod_lt _ hn, ?_⟩
  rw [Nat.mod_add_mod]
  have : r ≤ n * r := Nat.le_mul_of_pos_left r hn
  rw [show j + n * r - r + r = j + n * r by omega, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hj]

lemma sD_inf'_shift {α : Type*} [LinearOrder α] (f : ℕ → α) (n : ℕ) (h : ∀ i, f (i + n) = f i)
    (r : ℕ) (H1 H2 : (range n).Nonempty) :
    (range n).inf' H1 (fun i => f (i + r)) = (range n).inf' H2 f := by
  have hn : 0 < n := by obtain ⟨x, hx⟩ := H1; simp at hx; omega
  apply le_antisymm
  · apply Finset.le_inf'
    intro j hj
    rw [mem_range] at hj
    obtain ⟨i, hi, hij⟩ := sD_exists_pre n r j hn hj
    have : f j = f (i + r) := by rw [sD_per_mod f n h (i + r), hij]
    rw [this]
    exact Finset.inf'_le (fun i => f (i + r)) (mem_range.mpr hi)
  · apply Finset.le_inf'
    intro i _
    rw [sD_per_mod f n h (i + r)]
    exact Finset.inf'_le f (mem_range.mpr (Nat.mod_lt _ hn))

lemma sD_sup'_shift {α : Type*} [LinearOrder α] (f : ℕ → α) (n : ℕ) (h : ∀ i, f (i + n) = f i)
    (r : ℕ) (H1 H2 : (range n).Nonempty) :
    (range n).sup' H1 (fun i => f (i + r)) = (range n).sup' H2 f := by
  have hn : 0 < n := by obtain ⟨x, hx⟩ := H1; simp at hx; omega
  apply le_antisymm
  · apply Finset.sup'_le
    intro i _
    rw [sD_per_mod f n h (i + r)]
    exact Finset.le_sup' f (mem_range.mpr (Nat.mod_lt _ hn))
  · apply Finset.sup'_le
    intro j hj
    rw [mem_range] at hj
    obtain ⟨i, hi, hij⟩ := sD_exists_pre n r j hn hj
    have : f j = f (i + r) := by rw [sD_per_mod f n h (i + r), hij]
    rw [this]
    exact Finset.le_sup' (fun i => f (i + r)) (mem_range.mpr hi)

lemma sD_seg_symm (a b : Pt) : seg a b = seg b a := by
  ext p
  constructor
  · rintro ⟨t, h0, h1, rfl⟩
    exact ⟨1 - t, by linarith, by linarith, by module⟩
  · rintro ⟨t, h0, h1, rfl⟩
    exact ⟨1 - t, by linarith, by linarith, by module⟩

lemma sD_left_mem_seg (a b : Pt) : a ∈ seg a b := ⟨0, le_refl _, zero_le_one, by simp⟩
lemma sD_right_mem_seg (a b : Pt) : b ∈ seg a b := ⟨1, zero_le_one, le_refl _, by simp⟩

lemma sD_toPt_inj {a b : ℤ × ℤ} (h : toPt a = toPt b) : a = b := by
  simp only [toPt, Prod.mk.injEq, Int.cast_inj] at h
  exact Prod.ext h.1 h.2

lemma sD_hit_symm (a b p : Pt) : hit b a p = - hit a b p := by
  have hY : cross (a - b) (p - b) = - cross (b - a) (p - a) := by
    simp only [cross, Prod.fst_sub, Prod.snd_sub]; ring
  simp only [hit, hY, neg_pos, neg_lt_zero]
  ring

namespace Cycle
variable (C : Cycle)

/-- Lattice points of the boundary inside a window `W`. -/
noncomputable def Bc (W : Finset (ℤ × ℤ)) : ℕ := by
  classical exact (W.filter (fun q => toPt q ∈ C.bd)).card

/-- Lattice points of the interior inside a window `W`. -/
noncomputable def Ic (W : Finset (ℤ × ℤ)) : ℕ := by
  classical exact (W.filter (fun q => toPt q ∈ C.int)).card

lemma sD_V_per (i : ℕ) : C.V (i + C.n) = C.V i := by simp only [V, C.per]

lemma sD_edge_per (i : ℕ) : C.edge (i + C.n) = C.edge i := by
  simp only [edge, show i + C.n + 1 = (i + 1) + C.n by omega, sD_V_per]

/-! ### Rotation -/

theorem rot_V (r i : ℕ) : (C.rot r).V i = C.V (i + r) := rfl

lemma sD_rot_edge (r i : ℕ) : (C.rot r).edge i = C.edge (i + r) := by
  simp only [edge, rot_V, show i + 1 + r = i + r + 1 by omega]

theorem rot_bd (r : ℕ) : (C.rot r).bd = C.bd := by
  ext p
  constructor
  · rintro ⟨i, hi, hp⟩
    rw [sD_rot_edge, sD_per_mod C.edge C.n C.sD_edge_per] at hp
    exact ⟨_, Nat.mod_lt _ C.pos, hp⟩
  · rintro ⟨j, hj, hp⟩
    obtain ⟨i, hi, hij⟩ := sD_exists_pre C.n r j C.pos hj
    refine ⟨i, hi, ?_⟩
    rw [sD_rot_edge, sD_per_mod C.edge C.n C.sD_edge_per, hij]
    exact hp

theorem rot_wind (r : ℕ) (p : Pt) : (C.rot r).wind p = C.wind p := by
  unfold wind
  have := sD_sum_shift (fun i => hit (C.V i) (C.V (i + 1)) p) C.n
    (fun i => by simp only [show i + C.n + 1 = (i + 1) + C.n by omega, sD_V_per]) r
  rw [← this]
  apply sum_congr rfl
  intro i _
  simp only [rot_V, show i + 1 + r = i + r + 1 by omega]

theorem rot_shoe (r : ℕ) : (C.rot r).shoe = C.shoe := by
  unfold shoe
  have := sD_sum_shift (fun i => crossZ (C.v i) (C.v (i + 1))) C.n
    (fun i => by simp only [show i + C.n + 1 = (i + 1) + C.n by omega, C.per]) r
  rw [← this]
  apply sum_congr rfl
  intro i _
  show crossZ (C.v (i + r)) (C.v (i + 1 + r)) = _
  rw [show i + 1 + r = i + r + 1 by omega]

theorem rot_int (r : ℕ) : (C.rot r).int = C.int := by
  ext p
  simp only [int, Set.mem_ofPred_eq, rot_bd, rot_wind]

theorem rot_box (r : ℕ) : (C.rot r).box = C.box := by
  have hper1 : ∀ i, (C.v (i + C.n)).1 = (C.v i).1 := fun i => by rw [C.per]
  have hper2 : ∀ i, (C.v (i + C.n)).2 = (C.v i).2 := fun i => by rw [C.per]
  have e1 : (C.rot r).xmin = C.xmin := sD_inf'_shift (fun i => (C.v i).1) C.n hper1 r _ _
  have e2 : (C.rot r).xmax = C.xmax := sD_sup'_shift (fun i => (C.v i).1) C.n hper1 r _ _
  have e3 : (C.rot r).ymin = C.ymin := sD_inf'_shift (fun i => (C.v i).2) C.n hper2 r _ _
  have e4 : (C.rot r).ymax = C.ymax := sD_sup'_shift (fun i => (C.v i).2) C.n hper2 r _ _
  simp only [box, e1, e2, e3, e4]

theorem rot_B (r : ℕ) : (C.rot r).B = C.B := by
  unfold B; rw [rot_box]; congr 1; ext q; simp only [mem_filter, rot_bd]

theorem rot_I (r : ℕ) : (C.rot r).I = C.I := by
  unfold I; rw [rot_box]; congr 1; ext q; simp only [mem_filter, rot_int]

/-! ### Splitting along the chord `[v 0, v k]` -/

lemma sD_left_v (k i : ℕ) (hi : i ≤ k) : (C.left k).v i = C.v i := by
  show C.v (i % (k + 1)) = C.v i
  rw [Nat.mod_eq_of_lt (by omega)]

lemma sD_left_v_succ (k : ℕ) : (C.left k).v (k + 1) = C.v 0 := by
  show C.v ((k + 1) % (k + 1)) = C.v 0
  rw [Nat.mod_self]

lemma sD_right_v (k i : ℕ) (hi : i ≤ C.n - k) : (C.right k).v i = C.v (k + i) := by
  show C.v (k + i % (C.n - k + 1)) = C.v (k + i)
  rw [Nat.mod_eq_of_lt (by omega)]

lemma sD_right_v_succ (k : ℕ) : (C.right k).v (C.n - k + 1) = C.v k := by
  show C.v (k + (C.n - k + 1) % (C.n - k + 1)) = C.v k
  rw [Nat.mod_self, Nat.add_zero]

lemma sD_v_n : C.v C.n = C.v 0 := by
  have := C.per 0; rwa [Nat.zero_add] at this

lemma sD_V_n : C.V C.n = C.V 0 := by simp only [V, sD_v_n]

theorem left_V (k i : ℕ) (hi : i ≤ k) : (C.left k).V i = C.V i := by
  simp only [V, sD_left_v C k i hi]
theorem left_V_succ (k : ℕ) : (C.left k).V (k + 1) = C.V 0 := by
  simp only [V, sD_left_v_succ]
theorem right_V (k i : ℕ) (hk : k ≤ C.n) (hi : i ≤ C.n - k) : (C.right k).V i = C.V (k + i) := by
  simp only [V, sD_right_v C k i hi]
theorem right_V_succ (k : ℕ) (hk : k ≤ C.n) : (C.right k).V (C.n - k + 1) = C.V k := by
  simp only [V, sD_right_v_succ]
theorem left_edge (k i : ℕ) (hi : i < k) : (C.left k).edge i = C.edge i := by
  simp only [edge, left_V C k i (by omega), left_V C k (i + 1) (by omega)]
theorem right_edge (k i : ℕ) (hk : k ≤ C.n) (hi : i < C.n - k) :
    (C.right k).edge i = C.edge (k + i) := by
  simp only [edge, right_V C k i hk (by omega), right_V C k (i + 1) hk (by omega)]
  rfl

lemma sD_left_edge_last (k : ℕ) : (C.left k).edge k = seg (C.V k) (C.V 0) := by
  simp only [edge, left_V C k k le_rfl, left_V_succ]

lemma sD_right_edge_last (k : ℕ) (hk : k ≤ C.n) :
    (C.right k).edge (C.n - k) = seg (C.V 0) (C.V k) := by
  simp only [edge, right_V C k (C.n - k) hk le_rfl, right_V_succ C k hk,
    show k + (C.n - k) = C.n by omega, sD_V_n]

lemma sD_sum_split (f : ℕ → ℤ) (k : ℕ) (hk : k ≤ C.n) :
    ∑ i ∈ range C.n, f i = ∑ i ∈ range k, f i + ∑ i ∈ range (C.n - k), f (k + i) := by
  rw [← Finset.sum_range_add]
  congr 2
  omega

/-- The two pieces wind around every point as much as the whole. -/
theorem wind_left_add_right (k : ℕ) (hk : k ≤ C.n) (p : Pt) :
    C.wind p = (C.left k).wind p + (C.right k).wind p := by
  unfold wind
  rw [C.sD_sum_split _ k hk]
  have hl : (C.left k).n = k + 1 := rfl
  have hr : (C.right k).n = C.n - k + 1 := rfl
  rw [hl, hr, sum_range_succ, sum_range_succ, left_V C k k le_rfl, left_V_succ,
    right_V C k (C.n - k) hk le_rfl, right_V_succ C k hk, show k + (C.n - k) = C.n by omega,
    sD_V_n]
  have e1 : ∑ x ∈ range k, hit ((C.left k).V x) ((C.left k).V (x + 1)) p =
      ∑ i ∈ range k, hit (C.V i) (C.V (i + 1)) p := by
    apply sum_congr rfl; intro i hi; rw [mem_range] at hi
    rw [left_V C k i (by omega), left_V C k (i + 1) (by omega)]
  have e2 : ∑ x ∈ range (C.n - k), hit ((C.right k).V x) ((C.right k).V (x + 1)) p =
      ∑ i ∈ range (C.n - k), hit (C.V (k + i)) (C.V (k + i + 1)) p := by
    apply sum_congr rfl; intro i hi; rw [mem_range] at hi
    rw [right_V C k i hk (by omega), right_V C k (i + 1) hk (by omega)]
    rfl
  rw [e1, e2, sD_hit_symm (C.V k) (C.V 0)]
  ring

theorem shoe_left_add_right (k : ℕ) (hk : k ≤ C.n) :
    C.shoe = (C.left k).shoe + (C.right k).shoe := by
  unfold shoe
  rw [C.sD_sum_split _ k hk]
  have hl : (C.left k).n = k + 1 := rfl
  have hr : (C.right k).n = C.n - k + 1 := rfl
  rw [hl, hr, sum_range_succ, sum_range_succ, sD_left_v C k k le_rfl, sD_left_v_succ,
    sD_right_v C k (C.n - k) le_rfl, sD_right_v_succ C k, show k + (C.n - k) = C.n by omega,
    sD_v_n]
  have e1 : ∑ x ∈ range k, crossZ ((C.left k).v x) ((C.left k).v (x + 1)) =
      ∑ i ∈ range k, crossZ (C.v i) (C.v (i + 1)) := by
    apply sum_congr rfl; intro i hi; rw [mem_range] at hi
    rw [sD_left_v C k i (by omega), sD_left_v C k (i + 1) (by omega)]
  have e2 : ∑ x ∈ range (C.n - k), crossZ ((C.right k).v x) ((C.right k).v (x + 1)) =
      ∑ i ∈ range (C.n - k), crossZ (C.v (k + i)) (C.v (k + i + 1)) := by
    apply sum_congr rfl; intro i hi; rw [mem_range] at hi
    rw [sD_right_v C k i (by omega), sD_right_v C k (i + 1) (by omega)]
    rfl
  rw [e1, e2]
  have : crossZ (C.v k) (C.v 0) + crossZ (C.v 0) (C.v k) = 0 := by
    simp only [crossZ]; ring
  linarith

theorem bd_left_union_right (k : ℕ) (hk : k ≤ C.n) :
    (C.left k).bd ∪ (C.right k).bd = C.bd ∪ seg (C.V 0) (C.V k) := by
  ext p
  constructor
  · rintro (⟨i, hi, hp⟩ | ⟨i, hi, hp⟩)
    · change i < k + 1 at hi
      by_cases h : i < k
      · rw [left_edge C k i h] at hp
        exact Or.inl ⟨i, by omega, hp⟩
      · have : i = k := by omega
        rw [this, sD_left_edge_last, sD_seg_symm] at hp
        exact Or.inr hp
    · change i < C.n - k + 1 at hi
      by_cases h : i < C.n - k
      · rw [right_edge C k i hk h] at hp
        exact Or.inl ⟨k + i, by omega, hp⟩
      · have : i = C.n - k := by omega
        rw [this, sD_right_edge_last C k hk] at hp
        exact Or.inr hp
  · rintro (⟨i, hi, hp⟩ | hp)
    · by_cases h : i < k
      · rw [← left_edge C k i h] at hp
        exact Or.inl ⟨i, show i < k + 1 by omega, hp⟩
      · have e : C.edge i = (C.right k).edge (i - k) := by
          rw [right_edge C k (i - k) hk (by omega), show k + (i - k) = i by omega]
        rw [e] at hp
        exact Or.inr ⟨i - k, show i - k < C.n - k + 1 by omega, hp⟩
    · rw [← sD_right_edge_last C k hk] at hp
      exact Or.inr ⟨C.n - k, show C.n - k < C.n - k + 1 by omega, hp⟩

theorem seg_subset_bd_left (k : ℕ) : seg (C.V 0) (C.V k) ⊆ (C.left k).bd := by
  intro p hp
  rw [sD_seg_symm, ← sD_left_edge_last] at hp
  exact ⟨k, show k < k + 1 by omega, hp⟩

theorem seg_subset_bd_right (k : ℕ) (hk : k ≤ C.n) : seg (C.V 0) (C.V k) ⊆ (C.right k).bd := by
  intro p hp
  rw [← sD_right_edge_last C k hk] at hp
  exact ⟨C.n - k, show C.n - k < C.n - k + 1 by omega, hp⟩

end Cycle
end QE.Pick

namespace QE.Pick
open Finset

lemma sD_simple_of_lt (C : Cycle)
    (H : ∀ i j, i < j → j < C.n → ∀ p, p ∈ C.edge i → p ∈ C.edge j →
      (j = (i + 1) % C.n ∧ p = C.V (i + 1)) ∨ (i = (j + 1) % C.n ∧ p = C.V (j + 1))) :
    ∀ i j, i < C.n → j < C.n → i ≠ j → ∀ p,
      p ∈ seg (toPt (C.v i)) (toPt (C.v (i + 1))) → p ∈ seg (toPt (C.v j)) (toPt (C.v (j + 1))) →
        (j = (i + 1) % C.n ∧ p = toPt (C.v (i + 1))) ∨ (i = (j + 1) % C.n ∧ p = toPt (C.v (j + 1))) := by
  intro i j hi hj hij p h1 h2
  rcases Nat.lt_or_gt_of_ne hij with h | h
  · exact H i j h hj p h1 h2
  · exact (H j i h hi p h2 h1).symm

namespace LPoly
variable (P : LPoly)

lemma sD_vertex_on_edge {m i : ℕ} (hm : m < P.n) (hi : i < P.n) (h : P.V m ∈ P.edge i) :
    i = m ∨ m = (i + 1) % P.n := by
  by_cases him : i = m
  · exact Or.inl him
  right
  have hm' : P.V m ∈ seg (toPt (P.v m)) (toPt (P.v (m + 1))) := sD_left_mem_seg _ _
  rcases P.simple i m hi hm him (P.V m) h hm' with ⟨h1, _⟩ | ⟨h1, h2⟩
  · exact h1
  · exfalso
    have e := sD_toPt_inj h2
    rw [sD_per_mod P.v P.n P.per (m + 1)] at e
    have e2 := P.inj m ((m + 1) % P.n) hm (Nat.mod_lt _ (by omega)) e
    have := P.three
    rcases Nat.lt_or_ge (m + 1) P.n with h3 | h3
    · rw [Nat.mod_eq_of_lt h3] at e2; omega
    · rw [show m + 1 = P.n by omega, Nat.mod_self] at e2; omega

lemma sD_rot_inj (r : ℕ) : ∀ i j, i < (P.toCycle.rot r).n → j < (P.toCycle.rot r).n →
    (P.toCycle.rot r).v i = (P.toCycle.rot r).v j → i = j := by
  intro i j hi hj h
  change P.v (i + r) = P.v (j + r) at h
  change i < P.n at hi
  change j < P.n at hj
  rw [sD_per_mod P.v P.n P.per (i + r), sD_per_mod P.v P.n P.per (j + r)] at h
  have h2 := P.inj _ _ (Nat.mod_lt _ (by omega)) (Nat.mod_lt _ (by omega)) h
  have h3 := Nat.ModEq.add_right_cancel' (n := P.n) (a := i) (b := j) r h2
  rwa [Nat.ModEq, Nat.mod_eq_of_lt hi, Nat.mod_eq_of_lt hj] at h3

lemma sD_v_succ_mod (r i : ℕ) : P.v (i + 1 + r) = P.v ((i + r) % P.n + 1) := by
  rw [sD_per_mod P.v P.n P.per (i + 1 + r), sD_per_mod P.v P.n P.per ((i + r) % P.n + 1),
    Nat.mod_add_mod, show i + 1 + r = i + r + 1 by omega]

lemma sD_rot_simple (r : ℕ) : ∀ i j, i < (P.toCycle.rot r).n → j < (P.toCycle.rot r).n → i ≠ j →
    ∀ p, p ∈ seg (toPt ((P.toCycle.rot r).v i)) (toPt ((P.toCycle.rot r).v (i + 1))) →
      p ∈ seg (toPt ((P.toCycle.rot r).v j)) (toPt ((P.toCycle.rot r).v (j + 1))) →
      (j = (i + 1) % (P.toCycle.rot r).n ∧ p = toPt ((P.toCycle.rot r).v (i + 1))) ∨
        (i = (j + 1) % (P.toCycle.rot r).n ∧ p = toPt ((P.toCycle.rot r).v (j + 1))) := by
  intro i j hi hj hij p h1 h2
  change i < P.n at hi
  change j < P.n at hj
  change p ∈ seg (toPt (P.v (i + r))) (toPt (P.v (i + 1 + r))) at h1
  change p ∈ seg (toPt (P.v (j + r))) (toPt (P.v (j + 1 + r))) at h2
  change (j = (i + 1) % P.n ∧ p = toPt (P.v (i + 1 + r))) ∨
    (i = (j + 1) % P.n ∧ p = toPt (P.v (j + 1 + r)))
  have hn : 0 < P.n := P.pos
  rw [sD_per_mod P.v P.n P.per (i + r), sD_v_succ_mod] at h1
  rw [sD_per_mod P.v P.n P.per (j + r), sD_v_succ_mod] at h2
  rw [sD_v_succ_mod, sD_v_succ_mod]
  have hij' : (i + r) % P.n ≠ (j + r) % P.n := by
    intro h
    have h3 := Nat.ModEq.add_right_cancel' (n := P.n) (a := i) (b := j) r h
    rw [Nat.ModEq, Nat.mod_eq_of_lt hi, Nat.mod_eq_of_lt hj] at h3
    exact hij h3
  rcases P.simple _ _ (Nat.mod_lt _ hn) (Nat.mod_lt _ hn) hij' p h1 h2 with ⟨h, hp⟩ | ⟨h, hp⟩
  · refine Or.inl ⟨?_, hp⟩
    have h4 : (j + r) % P.n = (i + 1 + r) % P.n := by
      rw [h, Nat.mod_add_mod, show i + 1 + r = i + r + 1 by omega]
    have h3 := Nat.ModEq.add_right_cancel' (n := P.n) (a := j) (b := i + 1) r h4
    rwa [Nat.ModEq, Nat.mod_eq_of_lt hj] at h3
  · refine Or.inr ⟨?_, hp⟩
    have h4 : (i + r) % P.n = (j + 1 + r) % P.n := by
      rw [h, Nat.mod_add_mod, show j + 1 + r = j + r + 1 by omega]
    have h3 := Nat.ModEq.add_right_cancel' (n := P.n) (a := i) (b := j + 1) r h4
    rwa [Nat.ModEq, Nat.mod_eq_of_lt hi] at h3

/-- The rotated polygon. -/
def rot (P : LPoly) (r : ℕ) : LPoly where
  toCycle := P.toCycle.rot r
  three := P.three
  inj := P.sD_rot_inj r
  simple := P.sD_rot_simple r

theorem rot_toCycle (r : ℕ) : (P.rot r).toCycle = P.toCycle.rot r := rfl

/-- A chord meeting the boundary only at its endpoints. -/
def IsDiag (k : ℕ) : Prop :=
  2 ≤ k ∧ k + 2 ≤ P.n ∧ ∀ x ∈ seg (P.V 0) (P.V k), x ∈ P.bd → x = P.V 0 ∨ x = P.V k

lemma sD_left_inj (k : ℕ) (hk : P.IsDiag k) : ∀ i j, i < (P.toCycle.left k).n →
    j < (P.toCycle.left k).n → (P.toCycle.left k).v i = (P.toCycle.left k).v j → i = j := by
  intro i j hi hj h
  change i < k + 1 at hi
  change j < k + 1 at hj
  rw [P.toCycle.sD_left_v k i (by omega), P.toCycle.sD_left_v k j (by omega)] at h
  exact P.inj i j (by have := hk.2.1; omega) (by have := hk.2.1; omega) h

lemma sD_left_simple (k : ℕ) (hk : P.IsDiag k) : ∀ i j, i < (P.toCycle.left k).n →
    j < (P.toCycle.left k).n → i ≠ j → ∀ p,
    p ∈ seg (toPt ((P.toCycle.left k).v i)) (toPt ((P.toCycle.left k).v (i + 1))) →
      p ∈ seg (toPt ((P.toCycle.left k).v j)) (toPt ((P.toCycle.left k).v (j + 1))) →
      (j = (i + 1) % (P.toCycle.left k).n ∧ p = toPt ((P.toCycle.left k).v (i + 1))) ∨
        (i = (j + 1) % (P.toCycle.left k).n ∧ p = toPt ((P.toCycle.left k).v (j + 1))) := by
  apply sD_simple_of_lt
  intro i j hij hj p h1 h2
  obtain ⟨hk2, hkn, hd⟩ := hk
  change j < k + 1 at hj
  change (j = (i + 1) % (k + 1) ∧ p = (P.toCycle.left k).V (i + 1)) ∨
    (i = (j + 1) % (k + 1) ∧ p = (P.toCycle.left k).V (j + 1))
  have hi : i < k := by omega
  rw [Cycle.left_edge _ _ _ hi] at h1
  rw [Cycle.left_V _ _ _ (by omega : i + 1 ≤ k)]
  by_cases hjk : j < k
  · rw [Cycle.left_edge _ _ _ hjk] at h2
    rw [Cycle.left_V _ _ _ (by omega : j + 1 ≤ k)]
    have := P.simple i j (by omega) (by omega) (by omega) p h1 h2
    rw [Nat.mod_eq_of_lt (by omega : i + 1 < k + 1), Nat.mod_eq_of_lt (by omega : j + 1 < k + 1)]
    rwa [Nat.mod_eq_of_lt (by omega : i + 1 < P.n), Nat.mod_eq_of_lt (by omega : j + 1 < P.n)]
      at this
  · have hjk' : j = k := by omega
    rw [hjk'] at h2 ⊢
    rw [Cycle.sD_left_edge_last, sD_seg_symm] at h2
    rw [Cycle.left_V_succ]
    have hpb : p ∈ P.bd := ⟨i, by omega, h1⟩
    rcases hd p h2 hpb with rfl | rfl
    · rcases P.sD_vertex_on_edge (m := 0) (by omega) (by omega) h1 with h | h
      · right; rw [h, Nat.mod_self]; exact ⟨rfl, rfl⟩
      · rw [Nat.mod_eq_of_lt (by omega : i + 1 < P.n)] at h; omega
    · rcases P.sD_vertex_on_edge (m := k) (by omega) (by omega) h1 with h | h
      · omega
      · rw [Nat.mod_eq_of_lt (by omega : i + 1 < P.n)] at h
        left
        refine ⟨?_, by rw [h]⟩
        rw [Nat.mod_eq_of_lt (by omega)]; omega

/-- The piece `v 0, …, v k`. -/
def leftP (k : ℕ) (hk : P.IsDiag k) : LPoly where
  toCycle := P.toCycle.left k
  three := by change 3 ≤ k + 1; have := hk.1; omega
  inj := P.sD_left_inj k hk
  simple := P.sD_left_simple k hk

lemma sD_right_inj (k : ℕ) (hk : P.IsDiag k) : ∀ i j, i < (P.toCycle.right k).n →
    j < (P.toCycle.right k).n → (P.toCycle.right k).v i = (P.toCycle.right k).v j → i = j := by
  intro i j hi hj h
  change i < P.n - k + 1 at hi
  change j < P.n - k + 1 at hj
  obtain ⟨hk2, hkn, _⟩ := hk
  rw [P.toCycle.sD_right_v k i (by omega), P.toCycle.sD_right_v k j (by omega),
    sD_per_mod P.v P.n P.per (k + i), sD_per_mod P.v P.n P.per (k + j)] at h
  have h2 := P.inj _ _ (Nat.mod_lt _ P.pos) (Nat.mod_lt _ P.pos) h
  rcases Nat.lt_or_ge (k + i) P.n with h3 | h3 <;> rcases Nat.lt_or_ge (k + j) P.n with h4 | h4
  · rw [Nat.mod_eq_of_lt h3, Nat.mod_eq_of_lt h4] at h2; omega
  · rw [Nat.mod_eq_of_lt h3, show k + j = P.n by omega, Nat.mod_self] at h2; omega
  · rw [Nat.mod_eq_of_lt h4, show k + i = P.n by omega, Nat.mod_self] at h2; omega
  · omega

lemma sD_right_simple (k : ℕ) (hk : P.IsDiag k) : ∀ i j, i < (P.toCycle.right k).n →
    j < (P.toCycle.right k).n → i ≠ j → ∀ p,
    p ∈ seg (toPt ((P.toCycle.right k).v i)) (toPt ((P.toCycle.right k).v (i + 1))) →
      p ∈ seg (toPt ((P.toCycle.right k).v j)) (toPt ((P.toCycle.right k).v (j + 1))) →
      (j = (i + 1) % (P.toCycle.right k).n ∧ p = toPt ((P.toCycle.right k).v (i + 1))) ∨
        (i = (j + 1) % (P.toCycle.right k).n ∧ p = toPt ((P.toCycle.right k).v (j + 1))) := by
  apply sD_simple_of_lt
  intro i j hij hj p h1 h2
  obtain ⟨hk2, hkn, hd⟩ := hk
  have hk : k ≤ P.n := by omega
  change j < P.n - k + 1 at hj
  change (j = (i + 1) % (P.n - k + 1) ∧ p = (P.toCycle.right k).V (i + 1)) ∨
    (i = (j + 1) % (P.n - k + 1) ∧ p = (P.toCycle.right k).V (j + 1))
  have hi : i < P.n - k := by omega
  rw [Cycle.right_edge _ _ _ hk hi] at h1
  rw [Cycle.right_V _ _ _ hk (by omega : i + 1 ≤ P.n - k)]
  by_cases hjk : j < P.n - k
  · rw [Cycle.right_edge _ _ _ hk hjk] at h2
    rw [Cycle.right_V _ _ _ hk (by omega : j + 1 ≤ P.n - k)]
    have := P.simple (k + i) (k + j) (by omega) (by omega) (by omega) p h1 h2
    rw [Nat.mod_eq_of_lt (by omega : i + 1 < P.n - k + 1)]
    rcases this with ⟨h, hp⟩ | ⟨h, hp⟩
    · rw [Nat.mod_eq_of_lt (by omega : k + i + 1 < P.n)] at h
      exact Or.inl ⟨by omega, hp⟩
    · exfalso
      rcases Nat.lt_or_ge (k + j + 1) P.n with h3 | h3
      · rw [Nat.mod_eq_of_lt h3] at h; omega
      · rw [show k + j + 1 = P.n by omega, Nat.mod_self] at h; omega
  · have hjk' : j = P.n - k := by omega
    rw [hjk'] at h2 ⊢
    rw [Cycle.sD_right_edge_last _ _ hk] at h2
    rw [Cycle.right_V_succ _ _ hk]
    have hpb : p ∈ P.bd := ⟨k + i, by omega, h1⟩
    rcases hd p h2 hpb with rfl | rfl
    · rcases P.sD_vertex_on_edge (m := 0) (by omega) (by omega) h1 with h | h
      · omega
      · have h5 : k + i + 1 = P.n := by
          rcases Nat.lt_or_ge (k + i + 1) P.n with h3 | h3
          · rw [Nat.mod_eq_of_lt h3] at h; omega
          · omega
        left
        refine ⟨by rw [Nat.mod_eq_of_lt (by omega)]; omega, ?_⟩
        rw [show k + (i + 1) = P.n by omega, Cycle.sD_V_n]
    · rcases P.sD_vertex_on_edge (m := k) (by omega) (by omega) h1 with h | h
      · right
        refine ⟨?_, rfl⟩
        rw [Nat.mod_self]; omega
      · exfalso
        rcases Nat.lt_or_ge (k + i + 1) P.n with h3 | h3
        · rw [Nat.mod_eq_of_lt h3] at h; omega
        · rw [show k + i + 1 = P.n by omega, Nat.mod_self] at h; omega

/-- The piece `v k, …, v n = v 0`. -/
def rightP (k : ℕ) (hk : P.IsDiag k) : LPoly where
  toCycle := P.toCycle.right k
  three := by change 3 ≤ P.n - k + 1; have := hk.2.1; omega
  inj := P.sD_right_inj k hk
  simple := P.sD_right_simple k hk

theorem leftP_toCycle (k : ℕ) (hk : P.IsDiag k) : (P.leftP k hk).toCycle = P.toCycle.left k :=
  rfl
theorem rightP_toCycle (k : ℕ) (hk : P.IsDiag k) :
    (P.rightP k hk).toCycle = P.toCycle.right k := rfl

/-- The two pieces share exactly the diagonal. -/
theorem bd_left_inter_right (k : ℕ) (hk : P.IsDiag k) :
    (P.toCycle.left k).bd ∩ (P.toCycle.right k).bd = seg (P.V 0) (P.V k) := by
  obtain ⟨hk2, hkn, hd⟩ := hk
  have hk : k ≤ P.n := by omega
  apply Set.Subset.antisymm
  · rintro p ⟨⟨i, hi, h1⟩, ⟨j, hj, h2⟩⟩
    change i < k + 1 at hi
    change j < P.n - k + 1 at hj
    by_cases hik : i < k
    · by_cases hjk : j < P.n - k
      · rw [Cycle.left_edge _ _ _ hik] at h1
        rw [Cycle.right_edge _ _ _ hk hjk] at h2
        rcases P.simple i (k + j) (by omega) (by omega) (by omega) p h1 h2 with ⟨h, hp⟩ | ⟨h, hp⟩
        · rw [Nat.mod_eq_of_lt (by omega : i + 1 < P.n)] at h
          rw [hp, show i + 1 = k by omega]
          exact sD_right_mem_seg _ _
        · rcases Nat.lt_or_ge (k + j + 1) P.n with h3 | h3
          · rw [Nat.mod_eq_of_lt h3] at h; omega
          · have e : toPt (P.v (k + j + 1)) = P.V 0 := by
              rw [show k + j + 1 = P.n by omega]; exact P.toCycle.sD_V_n
            rw [hp, e]
            exact sD_left_mem_seg _ _
      · rw [show j = P.n - k by omega, Cycle.sD_right_edge_last _ _ hk] at h2
        exact h2
    · rw [show i = k by omega, Cycle.sD_left_edge_last, sD_seg_symm] at h1
      exact h1
  · intro p hp
    exact ⟨P.toCycle.seg_subset_bd_left k hp, P.toCycle.seg_subset_bd_right k hk hp⟩

/-- A point of the open diagonal lies on no edge of a piece other than the diagonal. -/
theorem diag_only_left (k : ℕ) (hk : P.IsDiag k) {d : Pt} (hd : d ∈ seg (P.V 0) (P.V k))
    (h0 : d ≠ P.V 0) (h1 : d ≠ P.V k) :
    ∀ j < k + 1, j ≠ k → d ∉ (P.toCycle.left k).edge j := by
  intro j hj hjk h
  rw [Cycle.left_edge _ _ _ (by omega)] at h
  rcases hk.2.2 d hd ⟨j, by have := hk.2.1; omega, h⟩ with h2 | h2
  · exact h0 h2
  · exact h1 h2

theorem diag_only_right (k : ℕ) (hk : P.IsDiag k) {d : Pt} (hd : d ∈ seg (P.V 0) (P.V k))
    (h0 : d ≠ P.V 0) (h1 : d ≠ P.V k) :
    ∀ j < P.n - k + 1, j ≠ P.n - k → d ∉ (P.toCycle.right k).edge j := by
  intro j hj hjk h
  rw [Cycle.right_edge _ _ _ (by have := hk.2.1; omega) (by omega)] at h
  rcases hk.2.2 d hd ⟨k + j, by omega, h⟩ with h2 | h2
  · exact h0 h2
  · exact h1 h2

lemma sD_V0_bd : P.V 0 ∈ P.bd := ⟨0, P.pos, sD_left_mem_seg _ _⟩

lemma sD_Vk_bd (k : ℕ) (hk : k < P.n) : P.V k ∈ P.bd := ⟨k, hk, sD_left_mem_seg _ _⟩

lemma sD_v0_ne_vk (k : ℕ) (hk : P.IsDiag k) : P.v 0 ≠ P.v k := by
  intro h
  have := P.inj 0 k P.pos (by have := hk.2.1; omega) h
  have := hk.1
  omega

/-- Boundary count: `B = B₁ + B₂ - 2c + 2`, `c` the number of lattice points on the diagonal. -/
theorem Bc_split (k : ℕ) (hk : P.IsDiag k) (W : Finset (ℤ × ℤ))
    (hW : ∀ q : ℤ × ℤ, toPt q ∈ P.bd ∪ seg (P.V 0) (P.V k) → q ∈ W) :
    P.toCycle.Bc W + 2 * (by classical exact (W.filter (fun q => toPt q ∈ seg (P.V 0) (P.V k))).card) =
      (P.toCycle.left k).Bc W + (P.toCycle.right k).Bc W + 2 := by
  classical
  unfold Cycle.Bc
  have hkn : k < P.n := by have := hk.2.1; omega
  have hk' : k ≤ P.n := by omega
  set FP := W.filter (fun q => toPt q ∈ P.bd)
  set FL := W.filter (fun q => toPt q ∈ (P.toCycle.left k).bd)
  set FR := W.filter (fun q => toPt q ∈ (P.toCycle.right k).bd)
  set S := W.filter (fun q => toPt q ∈ seg (P.V 0) (P.V k))
  have hU : FL ∪ FR = FP ∪ S := by
    ext q
    have h := Set.ext_iff.mp (P.toCycle.bd_left_union_right k hk') (toPt q)
    simp only [Set.mem_union] at h
    simp only [FL, FR, FP, S, mem_union, mem_filter]
    tauto
  have hI : FL ∩ FR = S := by
    ext q
    have h := Set.ext_iff.mp (P.bd_left_inter_right k hk) (toPt q)
    simp only [Set.mem_inter_iff] at h
    simp only [FL, FR, S, mem_inter, mem_filter]
    tauto
  have hPS : FP ∩ S = {P.v 0, P.v k} := by
    ext q
    simp only [FP, S, mem_inter, mem_filter, mem_insert, mem_singleton]
    constructor
    · rintro ⟨⟨_, h1⟩, _, h2⟩
      rcases hk.2.2 _ h2 h1 with h | h
      · exact Or.inl (sD_toPt_inj h)
      · exact Or.inr (sD_toPt_inj h)
    · rintro (rfl | rfl)
      · have h1 : toPt (P.v 0) ∈ P.bd := P.sD_V0_bd
        have h2 : toPt (P.v 0) ∈ seg (P.V 0) (P.V k) := sD_left_mem_seg _ _
        exact ⟨⟨hW _ (Or.inl h1), h1⟩, hW _ (Or.inl h1), h2⟩
      · have h1 : toPt (P.v k) ∈ P.bd := P.sD_Vk_bd k hkn
        have h2 : toPt (P.v k) ∈ seg (P.V 0) (P.V k) := sD_right_mem_seg _ _
        exact ⟨⟨hW _ (Or.inl h1), h1⟩, hW _ (Or.inl h1), h2⟩
  have c1 := card_union_add_card_inter FL FR
  have c2 := card_union_add_card_inter FP S
  rw [hU, hI] at c1
  rw [hPS, card_pair (P.sD_v0_ne_vk k hk)] at c2
  have : #S = #(W.filter (fun q => toPt q ∈ seg (P.V 0) (P.V k))) := by
    congr 1
  omega

/-- Interior count: `I = I₁ + I₂ + (c - 2)`, given the decomposition of the interior. -/
theorem Ic_split (k : ℕ) (hk : P.IsDiag k) (W : Finset (ℤ × ℤ))
    (hW : ∀ q : ℤ × ℤ, toPt q ∈ P.bd ∪ seg (P.V 0) (P.V k) → q ∈ W)
    (h1 : ∀ p, p ∉ P.bd → p ∉ seg (P.V 0) (P.V k) →
      (p ∈ P.int ↔ p ∈ (P.toCycle.left k).int ∨ p ∈ (P.toCycle.right k).int))
    (h2 : Disjoint (P.toCycle.left k).int (P.toCycle.right k).int)
    (h3 : ∀ p ∈ seg (P.V 0) (P.V k), p ≠ P.V 0 → p ≠ P.V k → p ∈ P.int)
    (h4 : ∀ p ∈ P.bd, p ∉ (P.toCycle.left k).int) (h5 : ∀ p ∈ P.bd, p ∉ (P.toCycle.right k).int) :
    P.toCycle.Ic W + 2 =
      (P.toCycle.left k).Ic W + (P.toCycle.right k).Ic W +
        (by classical exact (W.filter (fun q => toPt q ∈ seg (P.V 0) (P.V k))).card) := by
  classical
  unfold Cycle.Ic
  have hkn : k < P.n := by have := hk.2.1; omega
  have hk' : k ≤ P.n := by omega
  set FP := W.filter (fun q => toPt q ∈ P.int)
  set FL := W.filter (fun q => toPt q ∈ (P.toCycle.left k).int)
  set FR := W.filter (fun q => toPt q ∈ (P.toCycle.right k).int)
  set S := W.filter (fun q => toPt q ∈ seg (P.V 0) (P.V k))
  have hb0 : toPt (P.v 0) ∈ P.bd := P.sD_V0_bd
  have hbk : toPt (P.v k) ∈ P.bd := P.sD_Vk_bd k hkn
  have hL : ∀ p, p ∈ (P.toCycle.left k).int → p ∉ seg (P.V 0) (P.V k) :=
    fun p hp hs => hp.1 (P.toCycle.seg_subset_bd_left k hs)
  have hR : ∀ p, p ∈ (P.toCycle.right k).int → p ∉ seg (P.V 0) (P.V k) :=
    fun p hp hs => hp.1 (P.toCycle.seg_subset_bd_right k hk' hs)
  have hD1 : Disjoint FP {P.v 0, P.v k} := by
    rw [Finset.disjoint_left]
    intro q hq hq'
    simp only [FP, mem_filter] at hq
    simp only [mem_insert, mem_singleton] at hq'
    rcases hq' with rfl | rfl
    · exact hq.2.1 hb0
    · exact hq.2.1 hbk
  have hD2 : Disjoint FL FR := by
    rw [Finset.disjoint_left]
    intro q hq hq'
    simp only [FL, FR, mem_filter] at hq hq'
    exact Set.disjoint_left.mp h2 hq.2 hq'.2
  have hD3 : Disjoint (FL ∪ FR) S := by
    rw [Finset.disjoint_left]
    intro q hq hq'
    simp only [FL, FR, S, mem_union, mem_filter] at hq hq'
    rcases hq with hq | hq
    · exact hL _ hq.2 hq'.2
    · exact hR _ hq.2 hq'.2
  have hE : FP ∪ {P.v 0, P.v k} = (FL ∪ FR) ∪ S := by
    ext q
    simp only [FP, FL, FR, S, mem_union, mem_filter, mem_insert, mem_singleton]
    constructor
    · rintro (⟨hq, hp⟩ | rfl | rfl)
      · by_cases hs : toPt q ∈ seg (P.V 0) (P.V k)
        · exact Or.inr ⟨hq, hs⟩
        · rcases (h1 _ hp.1 hs).mp hp with h | h
          · exact Or.inl (Or.inl ⟨hq, h⟩)
          · exact Or.inl (Or.inr ⟨hq, h⟩)
      · exact Or.inr ⟨hW _ (Or.inl hb0), sD_left_mem_seg _ _⟩
      · exact Or.inr ⟨hW _ (Or.inl hbk), sD_right_mem_seg _ _⟩
    · rintro ((⟨hq, hp⟩ | ⟨hq, hp⟩) | ⟨hq, hs⟩)
      · exact Or.inl ⟨hq, (h1 _ (fun hb => h4 _ hb hp) (hL _ hp)).mpr (Or.inl hp)⟩
      · exact Or.inl ⟨hq, (h1 _ (fun hb => h5 _ hb hp) (hR _ hp)).mpr (Or.inr hp)⟩
      · by_cases e0 : toPt q = P.V 0
        · exact Or.inr (Or.inl (sD_toPt_inj e0))
        · by_cases ek : toPt q = P.V k
          · exact Or.inr (Or.inr (sD_toPt_inj ek))
          · exact Or.inl ⟨hq, h3 _ hs e0 ek⟩
  have c := congrArg Finset.card hE
  rw [card_union_of_disjoint hD1, card_union_of_disjoint hD3, card_union_of_disjoint hD2,
    card_pair (P.sD_v0_ne_vk k hk)] at c
  have : #S = #(W.filter (fun q => toPt q ∈ seg (P.V 0) (P.V k))) := by
    congr 1
  omega

end LPoly
end QE.Pick


/-! Pick's theorem: gluing along a diagonal and the main induction. -/

namespace QE.Pick
open Finset

/-! ### Generic helpers -/

lemma mn_seg_symm (a b : Pt) : seg a b = seg b a := by
  ext p; constructor
  · rintro ⟨t, h0, h1, rfl⟩
    exact ⟨1 - t, by linarith, by linarith, by ext <;> simp <;> ring⟩
  · rintro ⟨t, h0, h1, rfl⟩
    exact ⟨1 - t, by linarith, by linarith, by ext <;> simp <;> ring⟩

lemma mn_left_mem (a b : Pt) : a ∈ seg a b := ⟨0, le_rfl, zero_le_one, by simp⟩
lemma mn_right_mem (a b : Pt) : b ∈ seg a b := ⟨1, zero_le_one, le_rfl, by simp⟩

/-- Sub-segments. -/
lemma mn_seg_sub_left {a b x : Pt} (hx : x ∈ seg a b) : seg a x ⊆ seg a b := by
  obtain ⟨t, ht0, ht1, rfl⟩ := hx
  rintro p ⟨s, hs0, hs1, rfl⟩
  refine ⟨s * t, mul_nonneg hs0 ht0, by nlinarith, ?_⟩
  ext <;> simp <;> ring

lemma mn_seg_sub_right {a b x : Pt} (hx : x ∈ seg a b) : seg x b ⊆ seg a b := by
  rw [mn_seg_symm a b] at hx ⊢; rw [mn_seg_symm x b]; exact mn_seg_sub_left hx

lemma mn_seg_sub {a b x y : Pt} (hx : x ∈ seg a b) (hy : y ∈ seg a b) : seg x y ⊆ seg a b := by
  obtain ⟨s, hs0, hs1, rfl⟩ := hx
  obtain ⟨t, ht0, ht1, rfl⟩ := hy
  rintro p ⟨r, hr0, hr1, rfl⟩
  refine ⟨s + r * (t - s), ?_, ?_, ?_⟩
  · nlinarith
  · nlinarith
  · ext <;> simp <;> ring

lemma mn_reach_mono {S S' : Set Pt} (h : S ⊆ S') {p q : Pt} (hr : Reach S p q) : Reach S' p q := by
  induction hr with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hyz ih => exact ih.tail (hyz.trans h)

lemma mn_reach_symm {S : Set Pt} {p q : Pt} (hr : Reach S p q) : Reach S q p := by
  induction hr with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hyz ih => exact Relation.ReflTransGen.head (by rwa [mn_seg_symm]) ih

lemma mn_reach_single {S : Set Pt} {p q : Pt} (h : seg p q ⊆ S) : Reach S p q :=
  Relation.ReflTransGen.single h

lemma mn_wind_eq_of_reach (C : Cycle) {S : Set Pt} (hS : ∀ x ∈ S, x ∉ C.bd) {p q : Pt}
    (hr : Reach S p q) : C.wind p = C.wind q := by
  induction hr with
  | refl => rfl
  | tail _ hyz ih => exact ih.trans (C.wind_eq_of_seg (fun x hx => hS x (hyz hx)))

lemma Cycle.mn_v_mod (C : Cycle) (m : ℕ) : C.v (m % C.n) = C.v m := by
  conv_rhs => rw [← Nat.mod_add_div m C.n]
  induction m / C.n with
  | zero => simp
  | succ q ih => rw [Nat.mul_succ, ← add_assoc, C.per, ih]

lemma Cycle.mn_V_mod (C : Cycle) (m : ℕ) : C.V (m % C.n) = C.V m := by
  simp [Cycle.V, C.mn_v_mod]

/-- A vertex lies only on its two edges. -/
lemma LPoly.mn_vertex_edge (P : LPoly) {i j : ℕ} (hi : i < P.n) (hj : j < P.n)
    (h : P.V i ∈ P.edge j) : j = i ∨ (j + 1) % P.n = i := by
  by_contra hc
  push Not at hc
  have hn := P.three
  rcases P.simple i j hi hj (Ne.symm hc.1) (P.V i) (mn_left_mem _ _) h with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · have : P.v i = P.v ((i + 1) % P.n) := by
      rw [P.toCycle.mn_v_mod]; exact congrArg (fun p : Pt => p) h2 |> fun h => by
        simpa [Cycle.V, toPt, Prod.ext_iff] using h
    have := P.inj i ((i + 1) % P.n) hi (Nat.mod_lt _ (by omega)) this
    rcases Nat.lt_or_ge (i + 1) P.n with h' | h'
    · rw [Nat.mod_eq_of_lt h'] at this; omega
    · have h'' : (i + 1) % P.n = 0 := by rw [show i + 1 = P.n by omega, Nat.mod_self]
      omega
  · exact hc.2 h1.symm

/-! ### Boxes and counts -/

lemma Cycle.mn_box_sub {L C : Cycle} (h : ∀ i < L.n, ∃ j < C.n, L.v i = C.v j) : L.box ⊆ C.box := by
  intro q hq
  simp only [Cycle.box, mem_product, mem_Icc] at hq ⊢
  have key : ∀ i < L.n, C.xmin ≤ (L.v i).1 ∧ (L.v i).1 ≤ C.xmax ∧
      C.ymin ≤ (L.v i).2 ∧ (L.v i).2 ≤ C.ymax := by
    intro i hi
    obtain ⟨j, hj, e⟩ := h i hi
    rw [e]
    have hj' : j ∈ range C.n := mem_range.mpr hj
    exact ⟨inf'_le _ hj', le_sup' (fun i => (C.v i).1) hj', inf'_le _ hj',
      le_sup' (fun i => (C.v i).2) hj'⟩
  have h1 : C.xmin ≤ L.xmin := le_inf' _ _ (fun i hi => (key i (mem_range.mp hi)).1)
  have h2 : L.xmax ≤ C.xmax := sup'_le _ _ (fun i hi => (key i (mem_range.mp hi)).2.1)
  have h3 : C.ymin ≤ L.ymin := le_inf' _ _ (fun i hi => (key i (mem_range.mp hi)).2.2.1)
  have h4 : L.ymax ≤ C.ymax := sup'_le _ _ (fun i hi => (key i (mem_range.mp hi)).2.2.2)
  exact ⟨⟨h1.trans hq.1.1, hq.1.2.trans h2⟩, ⟨h3.trans hq.2.1, hq.2.2.trans h4⟩⟩

lemma Cycle.mn_B_eq_Bc (C : Cycle) {W : Finset (ℤ × ℤ)} (hW : C.box ⊆ W) : C.B = C.Bc W := by
  classical
  simp only [Cycle.B, Cycle.Bc]
  congr 1
  ext q
  simp only [mem_filter]
  exact ⟨fun h => ⟨hW h.1, h.2⟩, fun h => ⟨C.mem_box_of_bd h.2, h.2⟩⟩

lemma Cycle.mn_I_eq_Ic (C : Cycle) {W : Finset (ℤ × ℤ)} (hW : C.box ⊆ W) : C.I = C.Ic W := by
  classical
  simp only [Cycle.I, Cycle.Ic]
  congr 1
  ext q
  simp only [mem_filter]
  exact ⟨fun h => ⟨hW h.1, h.2⟩, fun h => ⟨C.mem_box_of_int h.2, h.2⟩⟩

lemma Cycle.mn_left_box (C : Cycle) {k : ℕ} (hk : k < C.n) : (C.left k).box ⊆ C.box :=
  Cycle.mn_box_sub (fun i _ => ⟨i % (k + 1), by
    have := Nat.mod_lt i (by omega : 0 < k + 1); omega, rfl⟩)

lemma Cycle.mn_right_box (C : Cycle) (k : ℕ) : (C.right k).box ⊆ C.box :=
  Cycle.mn_box_sub (fun i _ => ⟨(k + i % (C.n - k + 1)) % C.n, Nat.mod_lt _ C.pos,
    (C.mn_v_mod _).symm⟩)

lemma mn_norm_transv (a b : Pt) : ‖transv a b‖ = 1 := by
  unfold transv; split_ifs <;> simp

lemma mn_transv_symm (a b : Pt) : transv a b = transv b a := by
  unfold transv; simp only [eq_comm]

/-- An endpoint of a segment lies on a sub-segment only as one of its ends. -/
lemma mn_endpoint_extreme {a b x y : Pt} (hab : a ≠ b) (hx : x ∈ seg a b) (hy : y ∈ seg a b)
    (h : a ∈ seg x y) : a = x ∨ a = y := by
  obtain ⟨s, hs0, hs1, rfl⟩ := hx
  obtain ⟨t, ht0, ht1, rfl⟩ := hy
  obtain ⟨r, hr0, hr1, hr⟩ := h
  have hba : b - a ≠ 0 := sub_ne_zero.mpr hab.symm
  have key : ((1 - r) * s + r * t) • (b - a) = 0 := by
    have h := hr
    rw [eq_comm, ← sub_eq_zero] at h
    rw [← h]; module
  have hz : (1 - r) * s + r * t = 0 := (smul_eq_zero.mp key).resolve_right hba
  have h1 : (1 - r) * s = 0 := by nlinarith [mul_nonneg (sub_nonneg.mpr hr1) hs0, mul_nonneg hr0 ht0]
  have h2 : r * t = 0 := by nlinarith [mul_nonneg (sub_nonneg.mpr hr1) hs0, mul_nonneg hr0 ht0]
  rcases mul_eq_zero.mp h1 with h | h
  · have hr' : r = 1 := by linarith
    subst hr'
    have : t = 0 := by simpa using h2
    right; simp [this]
  · left; simp [h]

lemma mn_endpoint_extreme' {a b x y : Pt} (hab : a ≠ b) (hx : x ∈ seg a b) (hy : y ∈ seg a b)
    (h : b ∈ seg x y) : b = x ∨ b = y := by
  rw [mn_seg_symm a b] at hx hy
  exact mn_endpoint_extreme (Ne.symm hab) hx hy h

/-! ### The invariant and the gluing step -/

/-- The inductive invariant: winding numbers in `{0, ε}`, connected interior, and the
signed Pick identity. -/
def Good (P : LPoly) : Prop :=
  ∃ ε : ℤ, (ε = 1 ∨ ε = -1) ∧
    (∀ p, p ∉ P.bd → P.wind p = 0 ∨ P.wind p = ε) ∧
    (∀ p q, p ∈ P.int → q ∈ P.int → Reach P.int p q) ∧
    P.shoe = ε * (2 * (P.I : ℤ) + P.B - 2)

/-- **Gluing.** If the two pieces of a polygon cut along a diagonal satisfy the invariant
and lie on opposite sides of the diagonal, the polygon satisfies the invariant. -/
theorem good_glue (P : LPoly) (k : ℕ) (hk : P.IsDiag k)
    (g1 : Good (P.leftP k hk)) (g2 : Good (P.rightP k hk))
    (NO1 : ∀ p ∈ (P.toCycle.left k).int, p ∉ (P.toCycle.right k).bd)
    (NO2 : ∀ p ∈ (P.toCycle.right k).int, p ∉ (P.toCycle.left k).bd)
    (NO3 : Disjoint (P.toCycle.left k).int (P.toCycle.right k).int) : Good P := by
  classical
  set L := P.toCycle.left k with hLdef
  set R := P.toCycle.right k with hRdef
  have eL : (P.leftP k hk).toCycle = L := P.leftP_toCycle k hk
  have eR : (P.rightP k hk).toCycle = R := P.rightP_toCycle k hk
  obtain ⟨ε1, hε1, F1, C1, S1⟩ := g1
  obtain ⟨ε2, hε2, F2, C2, S2⟩ := g2
  simp only [eL] at F1 C1 S1
  simp only [eR] at F2 C2 S2
  obtain ⟨hk2, hkn, hD⟩ := hk
  have hkle : k ≤ P.n := by omega
  set D := seg (P.V 0) (P.V k) with hDdef
  -- the two endpoints of the diagonal are distinct
  have hV0k : P.V 0 ≠ P.V k := by
    intro h
    have : P.v 0 = P.v k := by simpa [Cycle.V, toPt, Prod.ext_iff] using h
    have := P.inj 0 k P.toCycle.pos (by omega) this; omega
  -- a point of the open diagonal
  set d : Pt := P.V 0 + (1 / 2 : ℝ) • (P.V k - P.V 0) with hd
  have hdD : d ∈ D := ⟨1 / 2, by norm_num, by norm_num, rfl⟩
  have hd0 : d ≠ P.V 0 := by
    intro h; apply hV0k
    rw [Prod.ext_iff] at h ⊢
    simp only [hd, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, Prod.fst_sub,
      Prod.snd_sub, smul_eq_mul] at h
    constructor <;> linarith [h.1, h.2]
  have hdk : d ≠ P.V k := by
    intro h; apply hV0k
    rw [Prod.ext_iff] at h ⊢
    simp only [hd, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, Prod.fst_sub,
      Prod.snd_sub, smul_eq_mul] at h
    constructor <;> linarith [h.1, h.2]
  have hkL : k < L.n := by simp [hLdef, Cycle.left]
  have hkR : P.n - k < R.n := by simp [hRdef, Cycle.right]
  have hLk : L.V k = P.V k := P.toCycle.left_V k k le_rfl
  have hLk1 : L.V (k + 1) = P.V 0 := P.toCycle.left_V_succ k
  have hVn : P.V P.n = P.V 0 := by
    simp only [Cycle.V]; rw [show P.n = 0 + P.n by ring, P.toCycle.per]
  have hRk : R.V (P.n - k) = P.V 0 := by
    rw [hRdef, P.toCycle.right_V k (P.n - k) hkle le_rfl, Nat.add_sub_cancel' hkle, hVn]
  have hRk1 : R.V (P.n - k + 1) = P.V k := P.toCycle.right_V_succ k hkle
  set τ := transv (P.V 0) (P.V k) with hτ
  -- jumps of the two pieces across the diagonal
  obtain ⟨δ1, hδ1, J1⟩ := L.wind_jump hkL (d := d)
    (by show d ∈ seg (L.V k) (L.V (k + 1)); rw [hLk, hLk1, mn_seg_symm]; exact hdD)
    (by rw [hLk]; exact hdk) (by rw [hLk1]; exact hd0)
    (P.diag_only_left k ⟨hk2, hkn, hD⟩ hdD hd0 hdk)
  obtain ⟨δ2, hδ2, J2⟩ := R.wind_jump hkR (d := d)
    (by show d ∈ seg (R.V (P.n - k)) (R.V (P.n - k + 1)); rw [hRk, hRk1]; exact hdD)
    (by rw [hRk]; exact hd0) (by rw [hRk1]; exact hdk)
    (P.diag_only_right k ⟨hk2, hkn, hD⟩ hdD hd0 hdk)
  rw [hLk, hLk1, mn_transv_symm, ← hτ] at J1
  rw [hRk, hRk1, ← hτ] at J2
  -- a ball around `d` avoiding the boundary of `P`
  have hdP : d ∉ P.bd := fun h => by rcases hD d hdD h with h' | h' <;> contradiction
  obtain ⟨ε3, hε3, hball⟩ := Metric.isOpen_iff.mp P.toCycle.bd_isClosed.isOpen_compl d hdP
  set t := min (min δ1 δ2) ε3 / 2 with ht
  have ht0 : 0 < t := by positivity
  have ht1 : t < δ1 := by
    have := min_le_left (min δ1 δ2) ε3; have := min_le_left δ1 δ2; linarith
  have ht2 : t < δ2 := by
    have := min_le_left (min δ1 δ2) ε3; have := min_le_right δ1 δ2; linarith
  have ht3 : t < ε3 := by have := min_le_right (min δ1 δ2) ε3; linarith
  set pp := d + t • τ with hpp
  set pm := d - t • τ with hpm
  have hsegP : ∀ x ∈ seg pm pp, x ∉ P.bd := by
    rintro x ⟨s, hs0, hs1, rfl⟩
    apply hball
    rw [Metric.mem_ball, dist_eq_norm]
    have e : pm + s • (pp - pm) - d = ((2 * s - 1) * t) • τ := by
      rw [hpp, hpm]; module
    rw [e, norm_smul, mn_norm_transv, mul_one, Real.norm_eq_abs, abs_mul, abs_of_pos ht0]
    have : |2 * s - 1| ≤ 1 := abs_le.mpr ⟨by linarith, by linarith⟩
    nlinarith
  have hdmid : d ∈ seg pm pp := ⟨1 / 2, by norm_num, by norm_num, by rw [hpp, hpm]; module⟩
  obtain ⟨hppL, hpmL, -, hJL⟩ := J1 t ht0 ht1
  obtain ⟨hppR, hpmR, -, hJR⟩ := J2 t ht0 ht2
  have hwP : P.wind pm = P.wind pp := P.toCycle.wind_eq_of_seg hsegP
  have hsplit := fun p => P.toCycle.wind_left_add_right k hkle p
  have hvalL : (L.wind pp = ε1 ∧ L.wind pm = 0) ∨ (L.wind pp = 0 ∧ L.wind pm = ε1) := by
    rcases F1 pp hppL with h | h <;> rcases F1 pm hpmL with h' | h'
    · rw [h, h'] at hJL; norm_num at hJL
    · exact Or.inr ⟨h, h'⟩
    · exact Or.inl ⟨h, h'⟩
    · rw [h, h'] at hJL; norm_num at hJL
  have hvalR : (R.wind pp = ε2 ∧ R.wind pm = 0) ∨ (R.wind pp = 0 ∧ R.wind pm = ε2) := by
    rcases F2 pp hppR with h | h <;> rcases F2 pm hpmR with h' | h'
    · rw [h, h'] at hJR; norm_num at hJR
    · exact Or.inr ⟨h, h'⟩
    · exact Or.inl ⟨h, h'⟩
    · rw [h, h'] at hJR; norm_num at hJR
  have hne1 : ε1 ≠ 0 := by rcases hε1 with rfl | rfl <;> norm_num
  have hne2 : ε2 ≠ 0 := by rcases hε2 with rfl | rfl <;> norm_num
  have hNO : ∀ p, p ∉ L.bd → p ∉ R.bd → ¬ (L.wind p ≠ 0 ∧ R.wind p ≠ 0) := by
    rintro p h1 h2 ⟨w1, w2⟩
    exact Set.disjoint_left.mp NO3 ⟨h1, w1⟩ ⟨h2, w2⟩
  -- orientation consistency and the sides of the diagonal
  have hside : ε1 = ε2 ∧ P.wind pp = ε1 ∧
      ((pp ∈ L.int ∧ pm ∈ R.int) ∨ (pp ∈ R.int ∧ pm ∈ L.int)) := by
    rcases hvalL with ⟨a1, a2⟩ | ⟨a1, a2⟩ <;> rcases hvalR with ⟨b1, b2⟩ | ⟨b1, b2⟩
    · exact absurd ⟨by rw [a1]; exact hne1, by rw [b1]; exact hne2⟩ (hNO pp hppL hppR)
    · have e1 := hsplit pp; have e2 := hsplit pm
      rw [a1, b1] at e1; rw [a2, b2] at e2
      refine ⟨by linarith, by linarith, Or.inl ⟨⟨hppL, by rw [a1]; exact hne1⟩,
        ⟨hpmR, by rw [b2]; exact hne2⟩⟩⟩
    · have e1 := hsplit pp; have e2 := hsplit pm
      rw [a1, b1] at e1; rw [a2, b2] at e2
      refine ⟨by linarith, by linarith, Or.inr ⟨⟨hppR, by rw [b1]; exact hne2⟩,
        ⟨hpmL, by rw [a2]; exact hne1⟩⟩⟩
    · exact absurd ⟨by rw [a2]; exact hne1, by rw [b2]; exact hne2⟩ (hNO pm hpmL hpmR)
  obtain ⟨hε12, hwpp, hsides⟩ := hside
  subst hε12
  set ε := ε1
  have hbdU := P.toCycle.bd_left_union_right k hkle
  have hoff : ∀ p, p ∉ P.bd → p ∉ D → p ∉ L.bd ∧ p ∉ R.bd := by
    intro p h1 h2
    have : p ∉ L.bd ∪ R.bd := by rw [hbdU]; exact fun h => h.elim h1 h2
    exact ⟨fun h => this (Or.inl h), fun h => this (Or.inr h)⟩
  have hDbd : ∀ x ∈ D, x ∉ P.bd → x ≠ P.V 0 ∧ x ≠ P.V k := by
    intro x _ hx
    have h0 : P.V 0 ∈ P.bd := ⟨0, P.toCycle.pos, mn_left_mem _ _⟩
    have hk' : P.V k ∈ P.bd := ⟨k, by omega, mn_left_mem _ _⟩
    exact ⟨fun h => hx (h ▸ h0), fun h => hx (h ▸ hk')⟩
  -- the open diagonal avoids the boundary and has winding number `ε`
  have hDseg : ∀ x ∈ D, x ∉ P.bd → ∀ y ∈ seg x d, y ∉ P.bd := by
    intro x hx hxb y hy hyb
    have hyD : y ∈ D := mn_seg_sub hx hdD hy
    rcases hD y hyD hyb with h | h
    · rcases mn_endpoint_extreme hV0k hx hdD (h ▸ hy) with h' | h'
      · exact (hDbd x hx hxb).1 h'.symm
      · exact hd0 h'.symm
    · rcases mn_endpoint_extreme' hV0k hx hdD (h ▸ hy) with h' | h'
      · exact (hDbd x hx hxb).2 h'.symm
      · exact hdk h'.symm
  have hwd : P.wind d = ε := by
    rw [← hwpp]
    exact P.toCycle.wind_eq_of_seg (fun x hx => hsegP x (mn_seg_sub_right hdmid hx))
  have hwD : ∀ x ∈ D, x ∉ P.bd → P.wind x = ε := by
    intro x hx hxb
    rw [← hwd]; exact P.toCycle.wind_eq_of_seg (hDseg x hx hxb)
  -- winding numbers of `P`
  have hF : ∀ p, p ∉ P.bd → P.wind p = 0 ∨ P.wind p = ε := by
    intro p hp
    by_cases hpD : p ∈ D
    · exact Or.inr (hwD p hpD hp)
    · obtain ⟨h1, h2⟩ := hoff p hp hpD
      rw [hsplit p]
      rcases F1 p h1 with a | a <;> rcases F2 p h2 with b | b
      · left; rw [a, b]; rfl
      · right; rw [a, b]; ring
      · right; rw [a, b]; ring
      · exact absurd ⟨by rw [a]; exact hne1, by rw [b]; exact hne1⟩ (hNO p h1 h2)
  have hεne : ε ≠ 0 := hne1
  -- interiors
  have hLsub : L.int ⊆ P.int := by
    intro p ⟨h1, h2⟩
    have hR : p ∉ R.bd := NO1 p ⟨h1, h2⟩
    have hpb : p ∉ P.bd := fun h => by
      have : p ∈ L.bd ∪ R.bd := by rw [hbdU]; exact Or.inl h
      exact this.elim h1 hR
    refine ⟨hpb, ?_⟩
    rw [hsplit p]
    rcases F2 p hR with b | b
    · rw [b, add_zero]; exact h2
    · exact absurd ⟨h2, by rw [b]; exact hne1⟩ (hNO p h1 hR)
  have hRsub : R.int ⊆ P.int := by
    intro p ⟨h1, h2⟩
    have hL : p ∉ L.bd := NO2 p ⟨h1, h2⟩
    have hpb : p ∉ P.bd := fun h => by
      have : p ∈ L.bd ∪ R.bd := by rw [hbdU]; exact Or.inl h
      exact this.elim hL h1
    refine ⟨hpb, ?_⟩
    rw [hsplit p]
    rcases F1 p hL with a | a
    · rw [a, zero_add]; exact h2
    · exact absurd ⟨by rw [a]; exact hne1, h2⟩ (hNO p hL h1)
  have hInt1 : ∀ p, p ∉ P.bd → p ∉ D → (p ∈ P.int ↔ p ∈ L.int ∨ p ∈ R.int) := by
    intro p hp hpD
    obtain ⟨h1, h2⟩ := hoff p hp hpD
    constructor
    · rintro ⟨-, hw⟩
      rw [hsplit p] at hw
      by_contra hc; push Not at hc
      have a : L.wind p = 0 := by by_contra h; exact hc.1 ⟨h1, h⟩
      have b : R.wind p = 0 := by by_contra h; exact hc.2 ⟨h2, h⟩
      rw [a, b] at hw; exact hw rfl
    · rintro (h | h)
      · exact hLsub h
      · exact hRsub h
  have hDint : ∀ p ∈ D, p ≠ P.V 0 → p ≠ P.V k → p ∈ P.int := by
    intro p hp h0 h1
    have hpb : p ∉ P.bd := fun h => by rcases hD p hp h with h' | h' <;> contradiction
    exact ⟨hpb, by rw [hwD p hp hpb]; exact hεne⟩
  -- connectivity
  have hsegint : seg pm pp ⊆ P.int := by
    intro x hx
    refine ⟨hsegP x hx, ?_⟩
    rw [P.toCycle.wind_eq_of_seg (fun y hy => hsegP y (mn_seg_sub_right hx hy)), hwpp]
    exact hεne
  have hpp_int : pp ∈ P.int := hsegint (mn_right_mem _ _)
  have hpm_reach : Reach P.int pm pp := mn_reach_single hsegint
  have hto : ∀ x ∈ P.int, Reach P.int x pp := by
    intro x hx
    by_cases hxD : x ∈ D
    · obtain ⟨h0, hk'⟩ := hDbd x hxD hx.1
      have h1 : seg x d ⊆ P.int := by
        intro y hy
        have hyD : y ∈ D := mn_seg_sub hxD hdD hy
        refine ⟨hDseg x hxD hx.1 y hy, ?_⟩
        rw [hwD y hyD (hDseg x hxD hx.1 y hy)]; exact hεne
      have h2 : seg d pp ⊆ P.int := fun y hy => hsegint (mn_seg_sub_right hdmid hy)
      exact (mn_reach_single h1).trans (mn_reach_single h2)
    · rcases (hInt1 x hx.1 hxD).mp hx with h | h
      · rcases hsides with ⟨a, b⟩ | ⟨a, b⟩
        · exact mn_reach_mono hLsub (C1 x pp h a)
        · exact (mn_reach_mono hLsub (C1 x pm h b)).trans hpm_reach
      · rcases hsides with ⟨a, b⟩ | ⟨a, b⟩
        · exact (mn_reach_mono hRsub (C2 x pm h b)).trans hpm_reach
        · exact mn_reach_mono hRsub (C2 x pp h a)
  have hConn : ∀ p q, p ∈ P.int → q ∈ P.int → Reach P.int p q := fun p q hp hq =>
    (hto p hp).trans (mn_reach_symm (hto q hq))
  -- Pick
  have hkD : P.IsDiag k := ⟨hk2, hkn, hD⟩
  set W := P.box with hW
  have hLW : L.box ⊆ W := P.toCycle.mn_left_box (by omega)
  have hRW : R.box ⊆ W := P.toCycle.mn_right_box k
  have hWcov : ∀ q : ℤ × ℤ, toPt q ∈ P.bd ∪ D → q ∈ W := by
    intro q hq
    rcases hq with h | h
    · exact P.toCycle.mem_box_of_bd h
    · exact hLW (L.mem_box_of_bd (P.toCycle.seg_subset_bd_left k h))
  have hB := P.Bc_split k hkD W hWcov
  have hI := P.Ic_split k hkD W hWcov hInt1 NO3 hDint
    (fun p hp hpi => by
      have : p ∈ L.bd ∪ R.bd := by rw [hbdU]; exact Or.inl hp
      rcases this with h | h
      · exact hpi.1 h
      · exact NO1 p hpi h)
    (fun p hp hpi => by
      have : p ∈ L.bd ∪ R.bd := by rw [hbdU]; exact Or.inl hp
      rcases this with h | h
      · exact NO2 p hpi h
      · exact hpi.1 h)
  rw [← P.toCycle.mn_B_eq_Bc le_rfl, ← L.mn_B_eq_Bc hLW, ← R.mn_B_eq_Bc hRW] at hB
  rw [← P.toCycle.mn_I_eq_Ic le_rfl, ← L.mn_I_eq_Ic hLW, ← R.mn_I_eq_Ic hRW] at hI
  refine ⟨ε, hε1, hF, hConn, ?_⟩
  rw [P.toCycle.shoe_left_add_right k hkle]
  change L.shoe + R.shoe = _
  rw [S1, S2]
  have hB' := congrArg (Nat.cast : ℕ → ℤ) hB
  have hI' := congrArg (Nat.cast : ℕ → ℤ) hI
  push_cast at hB' hI'
  linear_combination (-ε) * hB' + (-2 * ε) * hI'

/-! ### Rotation, base case, lexicographic minimum -/

theorem good_rot (P : LPoly) (r : ℕ) (h : Good (P.rot r)) : Good P := by
  obtain ⟨ε, hε, F, C, S⟩ := h
  have e := P.rot_toCycle r
  simp only [e, Cycle.rot_bd, Cycle.rot_wind, Cycle.rot_int, Cycle.rot_shoe, Cycle.rot_B,
    Cycle.rot_I] at F C S
  exact ⟨ε, hε, F, C, S⟩

theorem good_tri (T : LPoly) (h3 : T.n = 3) : Good T := by
  refine ⟨Int.sign T.shoe, tri_shoe_sign T h3, ?_, fun p q hp hq => tri_conn T h3 hp hq,
    tri_pick T h3⟩
  intro p hp
  by_cases hT : p ∈ tri (T.V 0) (T.V 1) (T.V 2)
  · exact Or.inr (tri_wind_in T h3 hT hp)
  · exact Or.inl (tri_wind_out T h3 hT)

lemma mn_lexlt_irrefl (a : ℤ × ℤ) : ¬ lexlt a a := by
  unfold lexlt; omega

lemma mn_lexlt_trichotomy (a b : ℤ × ℤ) : lexlt a b ∨ a = b ∨ lexlt b a := by
  unfold lexlt
  rcases lt_trichotomy a.1 b.1 with h | h | h
  · exact Or.inl (Or.inl h)
  · rcases lt_trichotomy a.2 b.2 with h' | h' | h'
    · exact Or.inl (Or.inr ⟨h, h'⟩)
    · exact Or.inr (Or.inl (Prod.ext h h'))
    · exact Or.inr (Or.inr (Or.inr ⟨h.symm, h'⟩))
  · exact Or.inr (Or.inr (Or.inl h))

/-- A polygon has a lexicographically smallest vertex. -/
lemma LPoly.mn_exists_lexmin (P : LPoly) :
    ∃ r < P.n, ∀ j < P.n, j ≠ r → lexlt (P.v r) (P.v j) := by
  obtain ⟨r, hr, hmin⟩ := Finset.exists_min_image (range P.n) (fun i => toLex (P.v i))
    P.toCycle.range_nonempty
  refine ⟨r, mem_range.mp hr, fun j hj hjr => ?_⟩
  have h := hmin j (mem_range.mpr hj)
  have hne : P.v r ≠ P.v j := fun e => hjr (P.inj j r hj (mem_range.mp hr) e.symm)
  rcases mn_lexlt_trichotomy (P.v r) (P.v j) with h' | h' | h'
  · exact h'
  · exact absurd h' hne
  · exfalso
    have : toLex (P.v j) < toLex (P.v r) := by
      rcases h' with h' | ⟨h1, h2⟩
      · exact (Prod.Lex.toLex_lt_toLex).mpr (Or.inl h')
      · exact (Prod.Lex.toLex_lt_toLex).mpr (Or.inr ⟨h1, h2⟩)
    exact absurd h (not_le.mpr this)

lemma LPoly.mn_rot_lexmin (P : LPoly) {r : ℕ} (hr : r < P.n)
    (hmin : ∀ j < P.n, j ≠ r → lexlt (P.v r) (P.v j)) :
    ∀ j, 0 < j → j < (P.rot r).n → lexlt ((P.rot r).v 0) ((P.rot r).v j) := by
  intro j hj0 hj
  have e := P.rot_toCycle r
  have hn : (P.rot r).n = P.n := by rw [show (P.rot r).n = (P.rot r).toCycle.n from rfl, e]; rfl
  have hv : ∀ i, (P.rot r).v i = P.v (i + r) := by
    intro i; rw [show (P.rot r).v i = (P.rot r).toCycle.v i from rfl, e]; rfl
  rw [hv, hv, zero_add, ← P.toCycle.mn_v_mod (j + r)]
  rw [hn] at hj
  apply hmin _ (Nat.mod_lt _ P.toCycle.pos)
  intro h
  have : (j + r) % P.n = r % P.n := by rw [h, Nat.mod_eq_of_lt hr]
  have := Nat.ModEq.add_right_cancel' r (show j + r ≡ 0 + r [MOD P.n] by
    simpa [Nat.ModEq] using this)
  have := Nat.mod_eq_of_lt hj
  simp [Nat.ModEq] at *
  omega

/-! ### Cone sign lemmas -/

lemma mn_cross_add (a b c : Pt) : cross a (b + c) = cross a b + cross a c := by
  unfold cross; simp; ring
lemma mn_cross_add_left (a b c : Pt) : cross (a + b) c = cross a c + cross b c := by
  unfold cross; simp; ring
lemma mn_cross_anti (a b : Pt) : cross a b = - cross b a := by unfold cross; ring
lemma mn_cross_self (a : Pt) : cross a a = 0 := by unfold cross; ring

section cones
variable {du dw dz : Pt} (h : inOpenCone du dw dz)
include h

lemma mn_cone_X : cross du dz ≠ 0 := fun e => by have := h.1; rw [e] at this; simp at this
lemma mn_cone_Y : cross dz dw ≠ 0 := fun e => by have := h.2; rw [e] at this; simp at this
lemma mn_cone_A : cross du dw ≠ 0 := fun e => by have := h.1; rw [e] at this; simp at this
lemma mn_cone_XY : 0 < cross du dz * cross dz dw := by
  have h1 := h.1; have h2 := h.2
  have := mul_pos h1 h2
  have hA := mn_cone_A h
  nlinarith [sq_pos_of_ne_zero hA]

lemma mn_cone_not1 : ¬ inOpenCone dz dw du := by
  rintro ⟨h1, -⟩
  rw [mn_cross_anti dz du] at h1
  nlinarith [mn_cone_XY h]
lemma mn_cone_not2 : ¬ inOpenCone du dz dw := by
  rintro ⟨-, h2⟩
  rw [mn_cross_anti dw dz] at h2
  nlinarith [mn_cone_XY h]
lemma mn_cone_sum : inOpenCone dz dw (dw + dz) := by
  have hY := mn_cone_Y h
  constructor
  · rw [mn_cross_add, mn_cross_self, add_zero]; exact mul_self_pos.mpr hY
  · rw [mn_cross_add_left, mn_cross_self, zero_add]; exact mul_self_pos.mpr hY
lemma mn_cone_not3 : ¬ inOpenCone du dz (dw + dz) := by
  rintro ⟨-, h2⟩
  rw [mn_cross_add_left, mn_cross_self, add_zero, mn_cross_anti dw dz] at h2
  nlinarith [mn_cone_XY h]
lemma mn_cone_AX : cross du (dw + dz) ≠ 0 := by
  rw [mn_cross_add]
  have h1 := h.1; have h2 := h.2; have hA := mn_cone_A h
  intro e
  have : cross du dz = - cross du dw := by linarith
  rw [this] at h1; nlinarith [sq_pos_of_ne_zero hA]
end cones

lemma Cycle.mn_V_per (C : Cycle) (i : ℕ) : C.V (i + C.n) = C.V i := by
  simp [Cycle.V, C.per]

/-- Transport of the winding number along a piece of an edge whose only boundary points are
the edge's endpoints. -/
lemma mn_edge_transport (Q : LPoly) (C : Cycle) {j : ℕ} {x y : Pt}
    (hx : x ∈ Q.edge j) (hy : y ∈ Q.edge j)
    (hbad : ∀ z ∈ Q.edge j, z ∈ C.bd → z = Q.V j ∨ z = Q.V (j + 1))
    (hx0 : x ≠ Q.V j) (hx1 : x ≠ Q.V (j + 1)) (hyb : y ∉ C.bd) : C.wind x = C.wind y := by
  have hne : Q.V j ≠ Q.V (j + 1) := fun e => hx0 (by
    obtain ⟨t, -, -, rfl⟩ := hx; rw [← e]; simp)
  apply C.wind_eq_of_seg
  intro z hz hzb
  have hzE : z ∈ Q.edge j := mn_seg_sub hx hy hz
  rcases hbad z hzE hzb with e | e
  · rcases mn_endpoint_extreme hne hx hy (e ▸ hz) with e' | e'
    · exact hx0 e'.symm
    · exact hyb (e' ▸ e ▸ hzb)
  · rcases mn_endpoint_extreme' hne hx hy (e ▸ hz) with e' | e'
    · exact hx1 e'.symm
    · exact hyb (e' ▸ e ▸ hzb)

/-! ### The two cases of the induction step -/

theorem good_case_diag (Q : LPoly) (h0 : ∀ j, 0 < j → j < Q.n → lexlt (Q.v 0) (Q.v j))
    (k : ℕ) (hk : Q.IsDiag k)
    (hcone : inOpenCone (Q.V (Q.n - 1) - Q.V 0) (Q.V 1 - Q.V 0) (Q.V k - Q.V 0))
    (gL : Good (Q.leftP k hk)) (gR : Good (Q.rightP k hk)) : Good Q := by
  classical
  obtain ⟨hk2, hkn, hD⟩ := id hk
  have hkle : k ≤ Q.n := by omega
  set L := Q.toCycle.left k with hLdef
  set R := Q.toCycle.right k with hRdef
  set R' := R.rot (Q.n - k) with hR'def
  set du := Q.V (Q.n - 1) - Q.V 0 with hdu
  set dw := Q.V 1 - Q.V 0 with hdw
  set dz := Q.V k - Q.V 0 with hdz
  have hA : cross du dw ≠ 0 := lexmin_nondeg Q h0
  have hVn : Q.V Q.n = Q.V 0 := by
    have := Q.toCycle.mn_V_per 0; rwa [zero_add] at this
  -- vertices of the pieces
  have hLv : ∀ j ≤ k, L.v j = Q.v j := by
    intro j hj; show Q.v (j % (k + 1)) = Q.v j; rw [Nat.mod_eq_of_lt (by omega)]
  have hLV : ∀ j ≤ k, L.V j = Q.V j := fun j hj => by simp [Cycle.V, hLv j hj]
  have hmod : ∀ j, 0 < j → j < Q.n - k + 1 → (j + (Q.n - k)) % (Q.n - k + 1) = j - 1 := by
    intro j hj0 hj
    rw [show j + (Q.n - k) = (j - 1) + (Q.n - k + 1) by omega, Nat.add_mod_right,
      Nat.mod_eq_of_lt (by omega)]
  have hR'v0 : R'.v 0 = Q.v 0 := by
    show Q.v (k + (0 + (Q.n - k)) % (Q.n - k + 1)) = Q.v 0
    rw [zero_add, Nat.mod_eq_of_lt (by omega), Nat.add_sub_cancel' hkle]
    have := Q.per 0; rwa [zero_add] at this
  have hR'v : ∀ j, 0 < j → j < Q.n - k + 1 → R'.v j = Q.v (k + j - 1) := by
    intro j hj0 hj
    show Q.v (k + (j + (Q.n - k)) % (Q.n - k + 1)) = _
    rw [hmod j hj0 hj]; congr 1; omega
  have hR'V0 : R'.V 0 = Q.V 0 := by simp [Cycle.V, hR'v0]
  have hR'V : ∀ j, 0 < j → j < Q.n - k + 1 → R'.V j = Q.V (k + j - 1) := fun j h1 h2 => by
    simp [Cycle.V, hR'v j h1 h2]
  have hR'n : R'.n = Q.n - k + 1 := rfl
  -- the vertex lemma, specialised
  have hvert := fun {i j : ℕ} (hi : i < Q.n) (hj : j < Q.n) (h : Q.V i ∈ Q.edge j) =>
    Q.mn_vertex_edge hi hj h
  -- local data at v₀ for both pieces
  have h0L : ∀ j, 0 < j → j < L.n → lexlt (L.v 0) (L.v j) := by
    intro j hj0 hj
    have hj' : j ≤ k := by simp [hLdef, Cycle.left] at hj; omega
    rw [hLv 0 (by omega), hLv j hj']; exact h0 j hj0 (by omega)
  have hnotL : ∀ j, 0 < j → j + 1 < L.n → L.V 0 ∉ L.edge j := by
    intro j hj0 hj hmem
    have hj' : j + 1 < k + 1 := by simpa [hLdef, Cycle.left] using hj
    rw [hLV 0 (by omega), Q.toCycle.left_edge k j (by omega)] at hmem
    rcases hvert Q.toCycle.pos (by omega) hmem with h | h
    · omega
    · rw [Nat.mod_eq_of_lt (by omega)] at h; omega
  have hLn1 : L.V (L.n - 1) = Q.V k := by
    rw [show L.n - 1 = k by simp [hLdef, Cycle.left]]; exact hLV k le_rfl
  have hL1 : L.V 1 = Q.V 1 := hLV 1 (by omega)
  have hL0 : L.V 0 = Q.V 0 := hLV 0 (by omega)
  have hparL : cross (L.V (L.n - 1) - L.V 0) (L.V 1 - L.V 0) ≠ 0 := by
    rw [hLn1, hL1, hL0]; exact mn_cone_Y hcone
  have h0R : ∀ j, 0 < j → j < R'.n → lexlt (R'.v 0) (R'.v j) := by
    intro j hj0 hj
    rw [hR'v0, hR'v j hj0 hj]; exact h0 _ (by omega) (by rw [hR'n] at hj; omega)
  have hR'edge : ∀ j, 0 < j → j + 1 < R'.n → R'.edge j = Q.edge (k + j - 1) := by
    intro j hj0 hj
    show seg (R'.V j) (R'.V (j + 1)) = seg (Q.V (k + j - 1)) (Q.V (k + j - 1 + 1))
    rw [hR'V j hj0 (by omega), hR'V (j + 1) (by omega) (by omega)]
    congr 2; omega
  have hnotR : ∀ j, 0 < j → j + 1 < R'.n → R'.V 0 ∉ R'.edge j := by
    intro j hj0 hj hmem
    rw [hR'V0, hR'edge j hj0 hj] at hmem
    rw [hR'n] at hj
    rcases hvert Q.toCycle.pos (by omega) hmem with h | h
    · omega
    · rw [Nat.mod_eq_of_lt (by omega)] at h; omega
  have hR'n1 : R'.V (R'.n - 1) = Q.V (Q.n - 1) := by
    rw [hR'n, show Q.n - k + 1 - 1 = Q.n - k by omega, hR'V _ (by omega) (by omega)]
    congr 1; omega
  have hR'1 : R'.V 1 = Q.V k := by rw [hR'V 1 (by omega) (by omega)]; congr 1
  have hparR : cross (R'.V (R'.n - 1) - R'.V 0) (R'.V 1 - R'.V 0) ≠ 0 := by
    rw [hR'n1, hR'1, hR'V0]; exact mn_cone_X hcone
  have hR'bd : R'.bd = R.bd := R.rot_bd _
  have hR'w : ∀ p, R'.wind p = R.wind p := R.rot_wind _
  -- evaluations near v₀
  obtain ⟨ta0, hta0, Ha⟩ := L.wind_near_vertex h0L hnotL hparL du
    (by rw [hLn1, hL0]; rw [mn_cross_anti]; exact neg_ne_zero.mpr (mn_cone_X hcone))
    (by rw [hL1, hL0]; rw [mn_cross_anti]; exact neg_ne_zero.mpr hA)
  obtain ⟨tb0, htb0, Hb⟩ := R'.wind_near_vertex h0R hnotR hparR dw
    (by rw [hR'n1, hR'V0]; exact hA) (by rw [hR'1, hR'V0]; exact mn_cone_Y hcone)
  obtain ⟨tc0, htc0, Hc⟩ := L.wind_near_vertex h0L hnotL hparL (dw + dz)
    (by rw [hLn1, hL0]; rw [mn_cross_add, mn_cross_self, add_zero]; exact mn_cone_Y hcone)
    (by rw [hL1, hL0]; rw [mn_cross_add, mn_cross_self, zero_add, mn_cross_anti];
        exact neg_ne_zero.mpr (mn_cone_Y hcone))
  obtain ⟨td0, htd0, Hd⟩ := R'.wind_near_vertex h0R hnotR hparR (dw + dz)
    (by rw [hR'n1, hR'V0]; exact mn_cone_AX hcone)
    (by rw [hR'1, hR'V0]; rw [mn_cross_add, mn_cross_self, add_zero]; exact mn_cone_Y hcone)
  set ta := min ta0 1 / 2 with hta
  have ta_pos : 0 < ta := by positivity
  have ta_lt : ta < ta0 := by have := min_le_left ta0 1; linarith
  have ta_lt1 : ta < 1 := by have := min_le_right ta0 1; linarith
  set tb := min tb0 1 / 2 with htb
  have tb_pos : 0 < tb := by positivity
  have tb_lt : tb < tb0 := by have := min_le_left tb0 1; linarith
  have tb_lt1 : tb < 1 := by have := min_le_right tb0 1; linarith
  set tc := min tc0 td0 / 2 with htc
  have tc_pos : 0 < tc := by positivity
  have tc_lt : tc < tc0 := by have := min_le_left tc0 td0; linarith
  have tc_lt' : tc < td0 := by have := min_le_right tc0 td0; linarith
  obtain ⟨xa_bd, xa_w⟩ := Ha ta ta_pos ta_lt
  obtain ⟨xb_bd, xb_w⟩ := Hb tb tb_pos tb_lt
  obtain ⟨q_bdL, q_wL⟩ := Hc tc tc_pos tc_lt
  obtain ⟨q_bdR, q_wR⟩ := Hd tc tc_pos tc_lt'
  rw [hLn1, hL1, hL0, if_neg (mn_cone_not1 hcone)] at xa_w
  rw [hR'n1, hR'1, hR'V0, if_neg (mn_cone_not2 hcone)] at xb_w
  rw [hLn1, hL1, hL0, if_pos (mn_cone_sum hcone)] at q_wL
  rw [hR'n1, hR'1, hR'V0, if_neg (mn_cone_not3 hcone)] at q_wR
  simp only [hR'V0, hR'bd] at xb_bd q_bdR
  simp only [hR'V0, hR'w] at xb_w q_wR
  -- the edges of the pieces
  have hLk : L.edge k = seg (Q.V 0) (Q.V k) := by
    show seg (L.V k) (L.V (k + 1)) = _
    rw [hLV k le_rfl, Q.toCycle.left_V_succ, mn_seg_symm]
  have hRk : R.edge (Q.n - k) = seg (Q.V 0) (Q.V k) := by
    show seg (R.V (Q.n - k)) (R.V (Q.n - k + 1)) = _
    rw [Q.toCycle.right_V k (Q.n - k) hkle le_rfl, Nat.add_sub_cancel' hkle, hVn,
      Q.toCycle.right_V_succ k hkle]
  have memL : ∀ z, z ∈ L.bd → z ∈ seg (Q.V 0) (Q.V k) ∨ ∃ i < k, z ∈ Q.edge i := by
    rintro z ⟨i, hi, hz⟩
    have hi' : i < k + 1 := hi
    rcases Nat.lt_or_ge i k with h | h
    · exact Or.inr ⟨i, h, by rwa [Q.toCycle.left_edge k i h] at hz⟩
    · have : i = k := by omega
      subst this; exact Or.inl (by rwa [hLk] at hz)
  have memR : ∀ z, z ∈ R.bd → z ∈ seg (Q.V 0) (Q.V k) ∨ ∃ j, k ≤ j ∧ j < Q.n ∧ z ∈ Q.edge j := by
    rintro z ⟨m, hm, hz⟩
    have hm' : m < Q.n - k + 1 := hm
    rcases Nat.lt_or_ge m (Q.n - k) with h | h
    · exact Or.inr ⟨k + m, by omega, by omega, by rwa [Q.toCycle.right_edge k m hkle h] at hz⟩
    · have : m = Q.n - k := by omega
      subst this; exact Or.inl (by rwa [hRk] at hz)
  have DsubL : seg (Q.V 0) (Q.V k) ⊆ L.bd := Q.toCycle.seg_subset_bd_left k
  have DsubR : seg (Q.V 0) (Q.V k) ⊆ R.bd := Q.toCycle.seg_subset_bd_right k hkle
  have hQbd : ∀ j < Q.n, ∀ z ∈ Q.edge j, z ∈ Q.bd := fun j hj z hz => ⟨j, hj, hz⟩
  have hinj : ∀ i j, i < Q.n → j < Q.n → Q.V i = Q.V j → i = j := by
    intro i j hi hj h
    exact Q.inj i j hi hj (by simpa [Cycle.V, toPt, Prod.ext_iff] using h)
  have hn1 : Q.V (Q.n - 1 + 1) = Q.V 0 := by rw [Nat.sub_add_cancel (by omega), hVn]
  -- boundary points of `L` on the far edges are endpoints
  have badL : ∀ j, k ≤ j → j < Q.n → ∀ z ∈ Q.edge j, z ∈ L.bd →
      z = Q.V j ∨ z = Q.V (j + 1) := by
    intro j hkj hj z hz hzL
    rcases memL z hzL with hzD | ⟨i, hi, hzi⟩
    · rcases hD z hzD (hQbd j hj z hz) with e | e
      · rw [e] at hz ⊢
        rcases hvert Q.toCycle.pos hj hz with h | h
        · omega
        · right
          have : j + 1 = Q.n := by
            by_contra hc; rw [Nat.mod_eq_of_lt (by omega)] at h; omega
          rw [this, hVn]
      · rw [e] at hz ⊢
        rcases hvert (by omega) hj hz with h | h
        · left; rw [h]
        · exfalso
          rcases Nat.lt_or_ge (j + 1) Q.n with h' | h'
          · rw [Nat.mod_eq_of_lt h'] at h; omega
          · rw [show j + 1 = Q.n by omega, Nat.mod_self] at h; omega
    · rcases Q.simple i j (by omega) hj (by omega) z hzi hz with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · rw [Nat.mod_eq_of_lt (by omega)] at h1
        left; rw [h2]; show Q.V (i + 1) = Q.V j; rw [h1]
      · right; exact h2
  have badR : ∀ i < k, ∀ z ∈ Q.edge i, z ∈ R.bd → z = Q.V i ∨ z = Q.V (i + 1) := by
    intro i hi z hz hzR
    rcases memR z hzR with hzD | ⟨j, hkj, hj, hzj⟩
    · rcases hD z hzD (hQbd i (by omega) z hz) with e | e
      · rw [e] at hz ⊢
        rcases hvert Q.toCycle.pos (by omega) hz with h | h
        · left; rw [h]
        · rw [Nat.mod_eq_of_lt (by omega)] at h; omega
      · rw [e] at hz ⊢
        rcases hvert (by omega) (by omega) hz with h | h
        · omega
        · right; rw [Nat.mod_eq_of_lt (by omega)] at h; rw [h]
    · rcases Q.simple i j (by omega) hj (by omega) z hz hzj with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · right; exact h2
      · left
        rcases Nat.lt_or_ge (j + 1) Q.n with h' | h'
        · rw [Nat.mod_eq_of_lt h'] at h1; omega
        · have hj1 : j + 1 = Q.n := by omega
          rw [hj1, Nat.mod_self] at h1
          rw [h2]; show Q.V (j + 1) = Q.V i; rw [hj1, hVn, h1]
  have hVL : ∀ m, k < m → m < Q.n → Q.V m ∉ L.bd := by
    intro m hkm hm hmL
    rcases memL _ hmL with hzD | ⟨i, hi, hzi⟩
    · rcases hD _ hzD (hQbd m hm _ (mn_left_mem _ _)) with e | e
      · have := hinj m 0 hm Q.toCycle.pos e; omega
      · have := hinj m k hm (by omega) e; omega
    · rcases hvert hm (by omega) hzi with h | h
      · omega
      · rw [Nat.mod_eq_of_lt (by omega)] at h; omega
  have hVR : ∀ m, 0 < m → m < k → Q.V m ∉ R.bd := by
    intro m hm0 hmk hmR
    rcases memR _ hmR with hzD | ⟨j, hkj, hj, hzj⟩
    · rcases hD _ hzD (hQbd m (by omega) _ (mn_left_mem _ _)) with e | e
      · have := hinj m 0 (by omega) Q.toCycle.pos e; omega
      · have := hinj m k (by omega) (by omega) e; omega
    · rcases hvert (by omega) hj hzj with h | h
      · omega
      · rcases Nat.lt_or_ge (j + 1) Q.n with h' | h'
        · rw [Nat.mod_eq_of_lt h'] at h; omega
        · rw [show j + 1 = Q.n by omega, Nat.mod_self] at h; omega
  have hdu0 : du ≠ 0 := fun e => hA (by rw [e]; simp [cross])
  have hdw0 : dw ≠ 0 := fun e => hA (by rw [e]; simp [cross])
  have xa_bd' : Q.V 0 + ta • du ∉ L.bd := by simpa [hL0] using xa_bd
  have xa_mem : Q.V 0 + ta • du ∈ Q.edge (Q.n - 1) := by
    refine ⟨1 - ta, by linarith, by linarith, ?_⟩
    show _ = Q.V (Q.n - 1) + (1 - ta) • (Q.V (Q.n - 1 + 1) - Q.V (Q.n - 1))
    rw [hn1, hdu]; module
  have xa_ne0 : Q.V 0 + ta • du ≠ Q.V (Q.n - 1) := by
    intro e
    apply hdu0
    have : (1 - ta) • du = 0 := by
      rw [hdu] at e ⊢; linear_combination (norm := module) (-1 : ℝ) • e
    exact (smul_eq_zero.mp this).resolve_left (by linarith)
  have xa_ne1 : Q.V 0 + ta • du ≠ Q.V (Q.n - 1 + 1) := by
    rw [hn1]; intro e; apply hdu0
    have : ta • du = 0 := by simpa using e
    exact (smul_eq_zero.mp this).resolve_left ta_pos.ne'
  have xb_mem : Q.V 0 + tb • dw ∈ Q.edge 0 := ⟨tb, tb_pos.le, tb_lt1.le, by rw [hdw]⟩
  have xb_ne0 : Q.V 0 + tb • dw ≠ Q.V 0 := by
    intro e; apply hdw0
    have : tb • dw = 0 := by simpa using e
    exact (smul_eq_zero.mp this).resolve_left tb_pos.ne'
  have xb_ne1 : Q.V 0 + tb • dw ≠ Q.V (0 + 1) := by
    intro e; apply hdw0
    have : (1 - tb) • dw = 0 := by
      rw [zero_add] at e; rw [hdw] at e ⊢
      linear_combination (norm := module) (-1 : ℝ) • e
    exact (smul_eq_zero.mp this).resolve_left (by linarith)
  -- winding of `L` vanishes on the far vertices
  have chainL : ∀ d m, m + d = Q.n - 1 → k < m → L.wind (Q.V m) = 0 := by
    intro d
    induction d with
    | zero =>
      intro m hm hkm
      simp only [add_zero] at hm; subst hm
      rw [← xa_w]
      exact (mn_edge_transport Q L xa_mem (mn_left_mem _ _) (badL _ (by omega) (by omega))
        xa_ne0 xa_ne1 (hVL _ hkm (by omega))).symm
    | succ d ih =>
      intro m hm hkm
      rw [← ih (m + 1) (by omega) (by omega)]
      apply L.wind_eq_of_seg
      intro x hx hxL
      rcases badL m (by omega) (by omega) x hx hxL with e | e
      · exact hVL m hkm (by omega) (e ▸ hxL)
      · exact hVL (m + 1) (by omega) (by omega) (e ▸ hxL)
  have chainL' : ∀ m, k < m → m < Q.n → L.wind (Q.V m) = 0 := fun m h1 h2 =>
    chainL (Q.n - 1 - m) m (by omega) h1
  have chainR : ∀ m, 0 < m → m < k → R.wind (Q.V m) = 0 := by
    intro m
    induction m with
    | zero => intro h; omega
    | succ m ih =>
      intro _ hmk
      rcases Nat.eq_zero_or_pos m with hm0 | hm0
      · subst hm0
        rw [← xb_w]
        exact (mn_edge_transport Q R xb_mem (mn_right_mem _ _) (badR 0 (by omega))
          xb_ne0 xb_ne1 (hVR 1 (by omega) hmk)).symm
      · rw [← ih hm0 (by omega)]
        symm
        apply R.wind_eq_of_seg
        intro x hx hxR
        rcases badR m (by omega) x hx hxR with e | e
        · exact hVR m hm0 (by omega) (e ▸ hxR)
        · exact hVR (m + 1) (by omega) hmk (e ▸ hxR)
  have hV0D : Q.V 0 ∈ seg (Q.V 0) (Q.V k) := mn_left_mem _ _
  have hVkD : Q.V k ∈ seg (Q.V 0) (Q.V k) := mn_right_mem _ _
  have NO1 : ∀ p ∈ L.int, p ∉ R.bd := by
    rintro p ⟨hpL, hpw⟩ hpR
    apply hpw
    rcases memR p hpR with hpD | ⟨j, hkj, hj, hpj⟩
    · exact absurd (DsubL hpD) hpL
    by_cases e0 : p = Q.V j
    · rcases Nat.lt_or_ge k j with h | h
      · rw [e0]; exact chainL' j h hj
      · have : j = k := by omega
        subst this; exact absurd (DsubL (e0 ▸ hVkD)) hpL
    by_cases e1 : p = Q.V (j + 1)
    · by_cases hj1 : j + 1 < Q.n
      · rw [e1]; exact chainL' (j + 1) (by omega) hj1
      · have : j + 1 = Q.n := by omega
        rw [this, hVn] at e1; exact absurd (DsubL (e1 ▸ hV0D)) hpL
    by_cases hj1 : j + 1 < Q.n
    · rw [mn_edge_transport Q L hpj (mn_right_mem _ _) (badL j hkj hj) e0 e1
        (hVL (j + 1) (by omega) hj1)]
      exact chainL' (j + 1) (by omega) hj1
    · rw [mn_edge_transport Q L hpj (mn_left_mem _ _) (badL j hkj hj) e0 e1
        (hVL j (by omega) hj)]
      exact chainL' j (by omega) hj
  have NO2 : ∀ p ∈ R.int, p ∉ L.bd := by
    rintro p ⟨hpR, hpw⟩ hpL
    apply hpw
    rcases memL p hpL with hpD | ⟨i, hi, hpi⟩
    · exact absurd (DsubR hpD) hpR
    by_cases e0 : p = Q.V i
    · rcases Nat.eq_zero_or_pos i with h | h
      · subst h; exact absurd (DsubR (e0 ▸ hV0D)) hpR
      · rw [e0]; exact chainR i h hi
    by_cases e1 : p = Q.V (i + 1)
    · by_cases hi1 : i + 1 < k
      · rw [e1]; exact chainR (i + 1) (by omega) hi1
      · have : i + 1 = k := by omega
        rw [this] at e1; exact absurd (DsubR (e1 ▸ hVkD)) hpR
    rcases Nat.eq_zero_or_pos i with h | h
    · subst h
      rw [mn_edge_transport Q R hpi (mn_right_mem _ _) (badR 0 hi) e0 e1
        (hVR 1 (by omega) (by omega))]
      exact chainR 1 (by omega) (by omega)
    · rw [mn_edge_transport Q R hpi (mn_left_mem _ _) (badR i hi) e0 e1 (hVR i h hi)]
      exact chainR i h hi
  have eL : (Q.leftP k hk).toCycle = L := Q.leftP_toCycle k hk
  obtain ⟨ε1, -, -, C1, -⟩ := id gL
  simp only [eL] at C1
  have hqL : Q.V 0 + tc • (dw + dz) ∈ L.int := by
    refine ⟨by simpa [hL0] using q_bdL, ?_⟩
    rw [q_wL]; split_ifs <;> norm_num
  have NO3 : Disjoint L.int R.int := by
    rw [Set.disjoint_left]
    rintro p hpL ⟨-, hpw⟩
    apply hpw
    rw [mn_wind_eq_of_reach R (fun x hx => NO1 x hx) (C1 p _ hpL hqL)]
    exact q_wR
  exact good_glue Q k hk gL gR NO1 NO2 NO3

lemma Cycle.mn_edge_mod (C : Cycle) (m : ℕ) : C.edge (m % C.n) = C.edge m := by
  show seg (C.V (m % C.n)) (C.V (m % C.n + 1)) = seg (C.V m) (C.V (m + 1))
  rw [C.mn_V_mod]
  rw [← C.mn_V_mod (m % C.n + 1), ← C.mn_V_mod (m + 1), Nat.add_mod, Nat.mod_mod,
    ← Nat.add_mod]

/-- Barycentric coordinates in a non-degenerate triangle are unique. -/
lemma mn_bary_unique {a b c : Pt} (h : cross (b - a) (c - a) ≠ 0) {s t s' t' : ℝ}
    (e : a + s • (b - a) + t • (c - a) = a + s' • (b - a) + t' • (c - a)) : s = s' ∧ t = t' := by
  rw [Prod.ext_iff] at e
  simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, Prod.fst_sub,
    Prod.snd_sub, smul_eq_mul] at e
  unfold cross at h
  simp only [Prod.fst_sub, Prod.snd_sub] at h
  obtain ⟨e1, e2⟩ := e
  constructor
  · have : (s - s') * ((b.1 - a.1) * (c.2 - a.2) - (b.2 - a.2) * (c.1 - a.1)) = 0 := by
      linear_combination (c.2 - a.2) * e1 - (c.1 - a.1) * e2
    have := (mul_eq_zero.mp this).resolve_right h; linarith
  · have : (t - t') * ((b.1 - a.1) * (c.2 - a.2) - (b.2 - a.2) * (c.1 - a.1)) = 0 := by
      linear_combination -(b.2 - a.2) * e1 + (b.1 - a.1) * e2
    have := (mul_eq_zero.mp this).resolve_right h; linarith

/-- In a non-degenerate triangle `a b c`, the segment from the apex `b` to a point off the
side `[a, c]` stays off that side. -/
lemma mn_seg_apex {a b c x y : Pt} (h : cross (b - a) (c - a) ≠ 0) (hx : x ∈ tri a b c)
    (hxs : x ∉ seg a c) (hy : y ∈ seg b x) : y ∈ tri a b c ∧ y ∉ seg a c := by
  obtain ⟨s, t, hs, ht, hst, rfl⟩ := hx
  have hs0 : 0 < s := by
    rcases hs.lt_or_eq with h' | h'
    · exact h'
    · exfalso; apply hxs
      refine ⟨t, ht, by linarith, ?_⟩
      rw [← h']; simp
  obtain ⟨r, hr0, hr1, rfl⟩ := hy
  have e : b + r • (a + s • (b - a) + t • (c - a) - b) =
      a + (1 - r + r * s) • (b - a) + (r * t) • (c - a) := by module
  rw [e]
  refine ⟨⟨1 - r + r * s, r * t, by nlinarith, by positivity, by nlinarith, rfl⟩, ?_⟩
  rintro ⟨τ, hτ0, hτ1, hτ⟩
  have := mn_bary_unique h (s := 1 - r + r * s) (t := r * t) (s' := 0) (t' := τ)
    (by rw [hτ]; simp)
  nlinarith [this.1]

lemma mn_tri_left (a b c : Pt) : a ∈ tri a b c := ⟨0, 0, le_rfl, le_rfl, by norm_num, by simp⟩
lemma mn_tri_mid (a b c : Pt) : b ∈ tri a b c := ⟨1, 0, zero_le_one, le_rfl, by norm_num, by simp⟩

theorem good_case_ear (Q : LPoly) (h4 : 4 ≤ Q.n)
    (h0 : ∀ j, 0 < j → j < Q.n → lexlt (Q.v 0) (Q.v j))
    (hear : (∀ p ∈ tri (Q.V (Q.n - 1)) (Q.V 0) (Q.V 1), p ≠ Q.V (Q.n - 1) → p ≠ Q.V 1 →
        ∀ j < Q.n, p ∈ Q.edge j → j = Q.n - 1 ∨ j = 0) ∧
      (∀ x ∈ seg (Q.V (Q.n - 1)) (Q.V 1), x ∈ Q.bd → x = Q.V (Q.n - 1) ∨ x = Q.V 1))
    (ih : ∀ P : LPoly, P.n < Q.n → Good P) : Good Q := by
  classical
  set Q2 := Q.rot (Q.n - 1) with hQ2
  have e2 : Q2.toCycle = Q.toCycle.rot (Q.n - 1) := Q.rot_toCycle _
  have hQ2n : Q2.n = Q.n := by rw [show Q2.n = Q2.toCycle.n from rfl, e2]; rfl
  have hQ2V : ∀ i, Q2.V i = Q.V (i + (Q.n - 1)) := by
    intro i; rw [show Q2.V i = Q2.toCycle.V i from rfl, e2, Cycle.rot_V]
  have hQ2bd : Q2.bd = Q.bd := by rw [show Q2.bd = Q2.toCycle.bd from rfl, e2, Cycle.rot_bd]
  have hQ2edge : ∀ j, Q2.edge j = Q.edge ((j + (Q.n - 1)) % Q.n) := by
    intro j
    rw [Q.toCycle.mn_edge_mod]
    show seg (Q2.V j) (Q2.V (j + 1)) = seg (Q.V (j + (Q.n - 1))) (Q.V (j + (Q.n - 1) + 1))
    rw [hQ2V, hQ2V]; congr 2; ring_nf
  have hu : Q2.V 0 = Q.V (Q.n - 1) := by rw [hQ2V, zero_add]
  have hv : Q2.V 1 = Q.V 0 := by
    rw [hQ2V, show 1 + (Q.n - 1) = 0 + Q.n by omega, Q.toCycle.mn_V_per]
  have hw : Q2.V 2 = Q.V 1 := by
    rw [hQ2V, show 2 + (Q.n - 1) = 1 + Q.n by omega, Q.toCycle.mn_V_per]
  have hk : Q2.IsDiag 2 := by
    refine ⟨le_rfl, by omega, ?_⟩
    intro x hx hxb
    rw [hu, hw] at hx ⊢; rw [hQ2bd] at hxb
    exact hear.2 x hx hxb
  set Lc := Q2.toCycle.left 2 with hLc
  set Rc := Q2.toCycle.right 2 with hRc
  have eL : (Q2.leftP 2 hk).toCycle = Lc := Q2.leftP_toCycle 2 hk
  have eR : (Q2.rightP 2 hk).toCycle = Rc := Q2.rightP_toCycle 2 hk
  have hL3 : (Q2.leftP 2 hk).n = 3 := by
    rw [show (Q2.leftP 2 hk).n = (Q2.leftP 2 hk).toCycle.n from rfl, eL]; rfl
  have gL : Good (Q2.leftP 2 hk) := good_tri _ hL3
  have gR : Good (Q2.rightP 2 hk) := ih _ (by
    rw [show (Q2.rightP 2 hk).n = (Q2.rightP 2 hk).toCycle.n from rfl, eR]
    show Q2.n - 2 + 1 < Q.n; omega)
  -- the triangle
  set u := Q.V (Q.n - 1)
  set v := Q.V 0
  set w := Q.V 1
  have hLV : ∀ i ≤ 2, (Q2.leftP 2 hk).V i = Q2.V i := by
    intro i hi
    rw [show (Q2.leftP 2 hk).V i = (Q2.leftP 2 hk).toCycle.V i from rfl, eL]
    exact Q2.toCycle.left_V 2 i hi
  have hT : tri ((Q2.leftP 2 hk).V 0) ((Q2.leftP 2 hk).V 1) ((Q2.leftP 2 hk).V 2) =
      tri u v w := by rw [hLV 0 (by omega), hLV 1 (by omega), hLV 2 le_rfl, hu, hv, hw]
  have Tout := fun p (hp : p ∉ tri u v w) =>
    (show Lc.wind p = 0 by
      have := tri_wind_out (Q2.leftP 2 hk) hL3 (p := p) (by rw [hT]; exact hp)
      rwa [show (Q2.leftP 2 hk).wind p = (Q2.leftP 2 hk).toCycle.wind p from rfl, eL] at this)
  have Tbd : Lc.bd ⊆ tri u v w := by
    have := tri_bd_sub (Q2.leftP 2 hk) hL3
    rwa [hT, show (Q2.leftP 2 hk).bd = (Q2.leftP 2 hk).toCycle.bd from rfl, eL] at this
  -- non-degeneracy
  have hnd0 := lexmin_nondeg Q h0
  have hnd : cross (v - u) (w - u) ≠ 0 := by
    intro e; apply hnd0
    have : cross (v - u) (w - u) = - cross (u - v) (w - v) := by unfold cross; simp; ring
    linarith
  -- the boundary of the rest meets the triangle only on `[u, w]`
  have hDsub : seg u w ⊆ Rc.bd := by
    have := Q2.toCycle.seg_subset_bd_right 2 (by rw [show Q2.toCycle.n = Q2.n from rfl]; omega)
    rwa [show Q2.toCycle.V 0 = Q2.V 0 from rfl, show Q2.toCycle.V 2 = Q2.V 2 from rfl,
      hu, hw] at this
  have hDsubL : seg u w ⊆ Lc.bd := by
    have := Q2.toCycle.seg_subset_bd_left 2
    rwa [show Q2.toCycle.V 0 = Q2.V 0 from rfl, show Q2.toCycle.V 2 = Q2.V 2 from rfl,
      hu, hw] at this
  have memR : ∀ z ∈ Rc.bd, z ∈ seg u w ∨ ∃ i, i + 2 < Q.n ∧ z ∈ Q.edge (i + 1) := by
    rintro z ⟨m, hm, hz⟩
    have hm' : m < Q2.n - 2 + 1 := hm
    rw [hQ2n] at hm'
    rcases Nat.lt_or_ge m (Q.n - 2) with h | h
    · rw [Q2.toCycle.right_edge 2 m (by rw [show Q2.toCycle.n = Q2.n from rfl]; omega)
        (by rw [show Q2.toCycle.n = Q2.n from rfl]; omega)] at hz
      rw [show Q2.toCycle.edge (2 + m) = Q2.edge (2 + m) from rfl, hQ2edge,
        show (2 + m + (Q.n - 1)) % Q.n = m + 1 by
          rw [show 2 + m + (Q.n - 1) = (m + 1) + Q.n by omega, Nat.add_mod_right,
            Nat.mod_eq_of_lt (by omega)]] at hz
      exact Or.inr ⟨m, by omega, hz⟩
    · have hm2 : m = Q2.n - 2 := by rw [hQ2n]; omega
      subst hm2
      left
      have := Q2.toCycle.right_V 2 (Q2.n - 2) (by rw [show Q2.toCycle.n = Q2.n from rfl]; omega)
        le_rfl
      have h1 := Q2.toCycle.right_V_succ 2 (by rw [show Q2.toCycle.n = Q2.n from rfl]; omega)
      have hz' : z ∈ seg (Rc.V (Q2.n - 2)) (Rc.V (Q2.n - 2 + 1)) := hz
      rw [this, h1, show 2 + (Q2.n - 2) = 0 + Q2.n by omega] at hz'
      rw [show Q2.toCycle.V (0 + Q2.n) = Q2.V (0 + Q2.toCycle.n) from rfl,
        Q2.toCycle.mn_V_per, show Q2.toCycle.V 0 = Q2.V 0 from rfl,
        show Q2.toCycle.V 2 = Q2.V 2 from rfl, hu, hw] at hz'
      exact hz'
  have TR : ∀ z ∈ tri u v w, z ∈ Rc.bd → z ∈ seg u w := by
    intro z hzT hzR
    rcases memR z hzR with h | ⟨i, hi, hz⟩
    · exact h
    · by_cases hzu : z = u
      · rw [hzu]; exact mn_left_mem _ _
      by_cases hzw : z = w
      · rw [hzw]; exact mn_right_mem _ _
      rcases hear.1 z hzT hzu hzw (i + 1) (by omega) hz with h | h <;> omega
  -- winding of the rest vanishes on the triangle off `[u, w]`
  have hvR : v ∉ Rc.bd := by
    intro hvR
    have := TR v (mn_tri_mid _ _ _) hvR
    apply hnd
    obtain ⟨t, -, -, ht⟩ := this
    rw [ht]; unfold cross; simp; ring
  have hwv : Rc.wind v = 0 := by
    apply Rc.wind_eq_zero_of_lex
    intro i hi
    have hi' : i < Q2.n - 2 + 1 := hi
    rw [hQ2n] at hi'
    have e := Q2.toCycle.right_V 2 i (by rw [show Q2.toCycle.n = Q2.n from rfl]; omega)
      (by rw [show Q2.toCycle.n = Q2.n from rfl]; omega)
    rw [show Rc.V i = Q2.toCycle.V (2 + i) from e, show Q2.toCycle.V (2 + i) = Q2.V (2 + i) from rfl,
      hQ2V, show 2 + i + (Q.n - 1) = (i + 1) + Q.n by omega, Q.toCycle.mn_V_per]
    have := h0 (i + 1) (by omega) (by omega)
    unfold lexlt at this
    simp only [v, Cycle.V, toPt]
    rcases this with h | ⟨h1, h2⟩
    · left; exact_mod_cast h
    · right; exact ⟨by exact_mod_cast h1, by exact_mod_cast h2⟩
  have hTw : ∀ x ∈ tri u v w, x ∉ seg u w → Rc.wind x = 0 := by
    intro x hx hxs
    rw [← hwv]; symm
    apply Rc.wind_eq_of_seg
    intro y hy hyR
    obtain ⟨hyT, hys⟩ := mn_seg_apex hnd hx hxs hy
    exact hys (TR y hyT hyR)
  -- non-overlap
  have NO1 : ∀ p ∈ Lc.int, p ∉ Rc.bd := by
    rintro p ⟨hpL, hpw⟩ hpR
    have hpT : p ∈ tri u v w := by by_contra h; exact hpw (Tout p h)
    exact hpL (hDsubL (TR p hpT hpR))
  have NO2 : ∀ p ∈ Rc.int, p ∉ Lc.bd := by
    rintro p ⟨hpR, hpw⟩ hpL
    by_cases hs : p ∈ seg u w
    · exact hpR (hDsub hs)
    · exact hpw (hTw p (Tbd hpL) hs)
  have NO3 : Disjoint Lc.int Rc.int := by
    rw [Set.disjoint_left]
    rintro p ⟨hpL, hpw⟩ ⟨-, hpw'⟩
    have hpT : p ∈ tri u v w := by by_contra h; exact hpw (Tout p h)
    exact hpw' (hTw p hpT (fun h => hpL (hDsubL h)))
  exact good_rot Q (Q.n - 1) (good_glue Q2 2 hk gL gR NO1 NO2 NO3)


/-- **The invariant holds for every simple lattice polygon.** -/
theorem good_all : ∀ (m : ℕ) (P : LPoly), P.n = m → Good P := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro P hm
    rcases (show m = 3 ∨ 4 ≤ m by have := P.three; omega) with h3 | h4
    · exact good_tri P (hm.trans h3)
    · obtain ⟨r, hr, hmin⟩ := P.mn_exists_lexmin
      apply good_rot P r
      set Q := P.rot r with hQ
      have hQn : Q.n = P.n := by
        rw [show Q.n = Q.toCycle.n from rfl, hQ, P.rot_toCycle]; rfl
      have h0 := P.mn_rot_lexmin hr hmin
      rw [← hQ] at h0
      have ih' : ∀ P' : LPoly, P'.n < Q.n → Good P' := fun P' hP' =>
        ih P'.n (by omega) P' rfl
      rcases diag_exists Q (by omega) h0 with hear | ⟨k, hk2, hkn, hDk, hcone⟩
      · exact good_case_ear Q (by omega) h0 hear ih'
      · have hk : Q.IsDiag k := ⟨hk2, hkn, hDk⟩
        refine good_case_diag Q h0 k hk hcone (ih' _ ?_) (ih' _ ?_)
        · rw [show (Q.leftP k hk).n = (Q.leftP k hk).toCycle.n from rfl, Q.leftP_toCycle]
          show k + 1 < Q.n; omega
        · rw [show (Q.rightP k hk).n = (Q.rightP k hk).toCycle.n from rfl, Q.rightP_toCycle]
          show Q.n - k + 1 < Q.n; omega


/-! ### Pick's theorem -/

theorem LPoly.good (P : LPoly) : Good P := good_all P.n P rfl

/-- For a simple lattice polygon the winding number of every point off the boundary is
`0` or `±1` (a fixed sign): the granular interior is the set where it is nonzero. -/
theorem LPoly.wind_values (P : LPoly) :
    ∃ ε : ℤ, (ε = 1 ∨ ε = -1) ∧ ∀ p, p ∉ P.bd → P.wind p = 0 ∨ P.wind p = ε := by
  obtain ⟨ε, hε, F, -, -⟩ := P.good
  exact ⟨ε, hε, F⟩

/-- The interior of a simple lattice polygon is connected by polygonal paths. -/
theorem LPoly.int_connected (P : LPoly) {p q : Pt} (hp : p ∈ P.int) (hq : q ∈ P.int) :
    Reach P.int p q := by
  obtain ⟨ε, -, -, C, -⟩ := P.good
  exact C p q hp hq

lemma LPoly.three_le_B (P : LPoly) : 3 ≤ P.B := by
  classical
  have hsub : (range P.n).image P.v ⊆ P.box.filter (fun q => toPt q ∈ P.bd) := by
    intro q hq
    obtain ⟨i, hi, rfl⟩ := mem_image.mp hq
    have hb : toPt (P.v i) ∈ P.bd := ⟨i, mem_range.mp hi, mn_left_mem _ _⟩
    exact mem_filter.mpr ⟨P.toCycle.mem_box_of_bd hb, hb⟩
  have hcard : ((range P.n).image P.v).card = P.n := by
    rw [card_image_of_injOn, card_range]
    intro i hi j hj e
    exact P.inj i j (mem_range.mp hi) (mem_range.mp hj) e
  have := card_le_card hsub
  have h3 := P.three
  simp only [Cycle.B]
  convert le_trans (hcard ▸ h3) this

/-- **Pick's theorem.** For every simple lattice polygon,
`2 I + B - 2 = |shoelace sum| = 2 A`, where `I` counts the lattice points of the
granular interior and `B` those of the boundary. -/
theorem LPoly.pick (P : LPoly) : 2 * (P.I : ℤ) + P.B - 2 = |P.shoe| := by
  obtain ⟨ε, hε, -, -, S⟩ := P.good
  have hB := P.three_le_B
  have hX : (0 : ℤ) ≤ 2 * (P.I : ℤ) + P.B - 2 := by
    have : (3 : ℤ) ≤ P.B := by exact_mod_cast hB
    have : (0 : ℤ) ≤ P.I := by positivity
    linarith
  rw [S, abs_mul]
  rcases hε with rfl | rfl <;> simp [abs_of_nonneg hX]

/-- Pick's theorem in the granular measure: with lattice spacing `2ε` (area `(2ε)²` per
lattice point) and shoelace area `𝒜 = (2ε)² |shoe| / 2`, the closed polygon has granular
area `𝒜 + (2ε)² (B/2 + 1)`, the open one `𝒜 - (2ε)² (B/2 - 1)`. -/
theorem LPoly.pick_mu {K : Type*} [Field K] [CharZero K] (P : LPoly) (ε : K) :
    (2 * ε) ^ 2 * ((P.I : K) + P.B) =
        (2 * ε) ^ 2 * ((|P.shoe| : ℤ) : K) / 2 + (2 * ε) ^ 2 * ((P.B : K) / 2 + 1) ∧
      (2 * ε) ^ 2 * (P.I : K) =
        (2 * ε) ^ 2 * ((|P.shoe| : ℤ) : K) / 2 - (2 * ε) ^ 2 * ((P.B : K) / 2 - 1) ∧
      (2 * ε) ^ 2 * ((P.I : K) + P.B) - (2 * ε) ^ 2 * (P.I : K) = (2 * ε) ^ 2 * P.B := by
  have h := P.pick
  have h' : ((|P.shoe| : ℤ) : K) = 2 * (P.I : K) + P.B - 2 := by
    rw [← h]; push_cast; ring
  refine ⟨?_, ?_, by ring⟩ <;> rw [h'] <;> field_simp <;> ring


/-! ### Boundary points edge by edge, and the anisotropic Steiner form -/

lemma mn_seg_coord {a b q : ℤ × ℤ} (h : toPt q ∈ seg (toPt a) (toPt b)) :
    q ∈ Icc (min a.1 b.1) (max a.1 b.1) ×ˢ Icc (min a.2 b.2) (max a.2 b.2) := by
  obtain ⟨t, ht0, ht1, e⟩ := h
  simp only [toPt, Prod.ext_iff, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd,
    Prod.fst_sub, Prod.snd_sub, smul_eq_mul] at e
  simp only [mem_product, mem_Icc]
  have key : ∀ x y z : ℤ, (z : ℝ) = x + t * (y - x) → min x y ≤ z ∧ z ≤ max x y := by
    intro x y z hz
    have h1 : ((min x y : ℤ) : ℝ) ≤ z := by
      rw [hz]; push_cast
      rcases le_total x y with hxy | hxy
      · rw [min_eq_left (by exact_mod_cast hxy)]; nlinarith [(show (x : ℝ) ≤ y by exact_mod_cast hxy)]
      · rw [min_eq_right (by exact_mod_cast hxy)]; nlinarith [(show (y : ℝ) ≤ x by exact_mod_cast hxy)]
    have h2 : (z : ℝ) ≤ ((max x y : ℤ) : ℝ) := by
      rw [hz]; push_cast
      rcases le_total x y with hxy | hxy
      · rw [max_eq_right (by exact_mod_cast hxy)]; nlinarith [(show (x : ℝ) ≤ y by exact_mod_cast hxy)]
      · rw [max_eq_left (by exact_mod_cast hxy)]; nlinarith [(show (y : ℝ) ≤ x by exact_mod_cast hxy)]
    exact ⟨by exact_mod_cast h1, by exact_mod_cast h2⟩
  exact ⟨key _ _ _ e.1, key _ _ _ e.2⟩

lemma mn_filter_eq {α : Type*} {s t : Finset α} {p : α → Prop} [DecidablePred p]
    (hs : ∀ x, p x → x ∈ s) (ht : ∀ x, p x → x ∈ t) : s.filter p = t.filter p := by
  ext x; simp only [mem_filter]
  exact ⟨fun h => ⟨ht x h.2, h.2⟩, fun h => ⟨hs x h.2, h.2⟩⟩

/-- Twice nothing: the number of lattice points on edge `i`, its end excluded, is the gcd of
the coordinate displacements. -/
lemma LPoly.mn_card_halfopen (P : LPoly) {i : ℕ} (hi : i < P.n) :
    (by classical exact (P.box.filter (fun q => toPt q ∈ P.edge i ∧ toPt q ≠ P.V (i + 1))).card) =
      Int.gcd ((P.v (i + 1)).1 - (P.v i).1) ((P.v (i + 1)).2 - (P.v i).2) := by
  classical
  have h6 := seg_lattice_card (P.v i) (P.v (i + 1))
  have hin : ∀ q, toPt q ∈ P.edge i → q ∈ P.box := fun q h =>
    P.toCycle.mem_box_of_bd ⟨i, hi, h⟩
  have e1 : P.box.filter (fun q => toPt q ∈ P.edge i) =
      (Icc (min (P.v i).1 (P.v (i + 1)).1) (max (P.v i).1 (P.v (i + 1)).1) ×ˢ
        Icc (min (P.v i).2 (P.v (i + 1)).2) (max (P.v i).2 (P.v (i + 1)).2)).filter
        (fun q => toPt q ∈ seg (toPt (P.v i)) (toPt (P.v (i + 1)))) :=
    mn_filter_eq hin (fun q h => mn_seg_coord h)
  have hend : P.v (i + 1) ∈ P.box.filter (fun q => toPt q ∈ P.edge i) :=
    mem_filter.mpr ⟨hin _ (mn_right_mem _ _), mn_right_mem _ _⟩
  have e2 : P.box.filter (fun q => toPt q ∈ P.edge i ∧ toPt q ≠ P.V (i + 1)) =
      (P.box.filter (fun q => toPt q ∈ P.edge i)).erase (P.v (i + 1)) := by
    ext q
    simp only [mem_filter, mem_erase]
    constructor
    · rintro ⟨hq, he, hne⟩
      exact ⟨fun h => hne (by rw [h]; rfl), hq, he⟩
    · rintro ⟨hne, hq, he⟩
      refine ⟨hq, he, fun h => hne ?_⟩
      have : toPt q = toPt (P.v (i + 1)) := h
      simp only [toPt, Prod.ext_iff, Int.cast_inj] at this
      exact Prod.ext this.1 this.2
  have : (P.box.filter (fun q => toPt q ∈ P.edge i ∧ toPt q ≠ P.V (i + 1))).card =
      Int.gcd ((P.v (i + 1)).1 - (P.v i).1) ((P.v (i + 1)).2 - (P.v i).2) := by
    rw [e2, card_erase_of_mem hend, e1]
    convert congrArg (· - 1) h6 using 1
    simp
  convert this

/-- **Boundary points edge by edge**: `B = ∑ᵢ gcd(|Δxᵢ|, |Δyᵢ|)`. -/
theorem LPoly.B_eq_sum_gcd (P : LPoly) :
    P.B = ∑ i ∈ range P.n,
      Int.gcd ((P.v (i + 1)).1 - (P.v i).1) ((P.v (i + 1)).2 - (P.v i).2) := by
  classical
  set F : ℕ → Finset (ℤ × ℤ) := fun i =>
    P.box.filter (fun q => toPt q ∈ P.edge i ∧ toPt q ≠ P.V (i + 1)) with hF
  have hU : P.box.filter (fun q => toPt q ∈ P.bd) = (range P.n).biUnion F := by
    ext q
    simp only [mem_filter, mem_biUnion, mem_range, hF]
    constructor
    · rintro ⟨hq, i, hi, hqi⟩
      by_cases he : toPt q = P.V (i + 1)
      · refine ⟨(i + 1) % P.n, Nat.mod_lt _ P.toCycle.pos, hq, ?_, ?_⟩
        · rw [he, ← P.toCycle.mn_V_mod]; exact mn_left_mem _ _
        · rw [he, ← P.toCycle.mn_V_mod (i + 1)]
          intro h
          have h' : P.v ((i + 1) % P.n) = P.v ((i + 1) % P.n + 1) := by
            simpa [Cycle.V, toPt, Prod.ext_iff] using h
          rw [← P.toCycle.mn_v_mod ((i + 1) % P.n + 1)] at h'
          have hlt := Nat.mod_lt (i + 1) P.toCycle.pos
          have := P.inj _ _ hlt (Nat.mod_lt _ P.toCycle.pos) h'
          have h3 := P.three
          rcases Nat.lt_or_ge ((i + 1) % P.n + 1) P.n with hh | hh
          · rw [Nat.mod_eq_of_lt hh] at this; omega
          · rw [show (i + 1) % P.n + 1 = P.n by omega, Nat.mod_self] at this; omega
      · exact ⟨i, hi, hq, hqi, he⟩
    · rintro ⟨i, hi, hq, hqi, -⟩
      exact ⟨hq, i, hi, hqi⟩
  have hdisj : ∀ i ∈ range P.n, ∀ j ∈ range P.n, i ≠ j → Disjoint (F i) (F j) := by
    intro i hi j hj hij
    rw [Finset.disjoint_left]
    intro q hqi hqj
    simp only [hF, mem_filter] at hqi hqj
    rcases P.simple i j (mem_range.mp hi) (mem_range.mp hj) hij _ hqi.2.1 hqj.2.1 with
      ⟨-, h⟩ | ⟨-, h⟩
    · exact hqi.2.2 h
    · exact hqj.2.2 h
  simp only [Cycle.B]
  rw [hU, card_biUnion hdisj]
  refine sum_congr rfl (fun i hi => ?_)
  have := P.mn_card_halfopen (mem_range.mp hi)
  convert this


/-- Euclidean length of edge `i` in lattice units. -/
noncomputable def LPoly.elen (P : LPoly) (i : ℕ) : ℝ :=
  Real.sqrt ((((P.v (i + 1)).1 - (P.v i).1 : ℤ) : ℝ) ^ 2 + (((P.v (i + 1)).2 - (P.v i).2 : ℤ) : ℝ) ^ 2)

/-- Lattice weight of the direction of the integer vector `(a, b) = g (p, q)`, `(p, q)`
primitive: `w = 1 / √(p² + q²)` (and `0` for the zero vector). -/
noncomputable def latWeight (a b : ℤ) : ℝ :=
  if Int.gcd a b = 0 then 0 else
    1 / Real.sqrt (((a / (Int.gcd a b : ℤ) : ℤ) : ℝ) ^ 2 + ((b / (Int.gcd a b : ℤ) : ℤ) : ℝ) ^ 2)

/-- `w(u) · |Δ| = gcd`: the lattice points of a segment are spaced `√(p²+q²)` apart. -/
lemma latWeight_mul (a b : ℤ) (h : Int.gcd a b ≠ 0) :
    latWeight a b * Real.sqrt ((a : ℝ) ^ 2 + (b : ℝ) ^ 2) = Int.gcd a b := by
  unfold latWeight
  rw [if_neg h]
  set g : ℤ := (Int.gcd a b : ℤ) with hg
  have hg0 : (0 : ℝ) < g := by rw [hg]; exact_mod_cast Nat.pos_of_ne_zero h
  have ha : a = (a / g) * g := (Int.ediv_mul_cancel (Int.gcd_dvd_left ..)).symm
  have hb : b = (b / g) * g := (Int.ediv_mul_cancel (Int.gcd_dvd_right ..)).symm
  set p := a / g; set q := b / g
  have hpq : 0 < ((p : ℝ) ^ 2 + (q : ℝ) ^ 2) := by
    rcases (show p ≠ 0 ∨ q ≠ 0 by
      by_contra hc; push Not at hc; apply h; rw [ha, hb, hc.1, hc.2]; simp) with hp | hq
    · have : (0 : ℝ) < (p : ℝ) ^ 2 := by positivity
      positivity
    · have : (0 : ℝ) < (q : ℝ) ^ 2 := by positivity
      positivity
  have e : (a : ℝ) ^ 2 + (b : ℝ) ^ 2 = ((g : ℝ)) ^ 2 * ((p : ℝ) ^ 2 + (q : ℝ) ^ 2) := by
    rw [ha, hb]; push_cast; ring
  rw [e, Real.sqrt_mul (by positivity), Real.sqrt_sq hg0.le]
  have : Real.sqrt ((p : ℝ) ^ 2 + (q : ℝ) ^ 2) ≠ 0 := (Real.sqrt_pos.mpr hpq).ne'
  field_simp
  rw [hg]; norm_cast

lemma latWeight_le_one (a b : ℤ) : latWeight a b ≤ 1 := by
  unfold latWeight
  split_ifs with h
  · norm_num
  · set p := a / (Int.gcd a b : ℤ); set q := b / (Int.gcd a b : ℤ)
    have ha : a = p * (Int.gcd a b : ℤ) := (Int.ediv_mul_cancel (Int.gcd_dvd_left ..)).symm
    have hb : b = q * (Int.gcd a b : ℤ) := (Int.ediv_mul_cancel (Int.gcd_dvd_right ..)).symm
    have h1 : (1 : ℝ) ≤ (p : ℝ) ^ 2 + (q : ℝ) ^ 2 := by
      have : p ≠ 0 ∨ q ≠ 0 := by
        by_contra hc; push Not at hc; apply h; rw [ha, hb, hc.1, hc.2]; simp
      have : (1 : ℤ) ≤ p ^ 2 + q ^ 2 := by
        rcases this with hp | hq
        · have := Int.one_le_abs hp; nlinarith [sq_nonneg q, sq_abs p]
        · have := Int.one_le_abs hq; nlinarith [sq_nonneg p, sq_abs q]
      exact_mod_cast this
    rw [div_le_one (Real.sqrt_pos.mpr (by linarith))]
    calc (1 : ℝ) = Real.sqrt 1 := Real.sqrt_one.symm
      _ ≤ _ := Real.sqrt_le_sqrt h1

/-- **Anisotropic Steiner form of Pick.** With lattice spacing `2ε`, edge lengths
`ℓᵢ = 2ε |Δᵢ|` and lattice weights `wᵢ`,
`μ(P̄ ∩ Λ) = 𝒜(P) + ε ∑ wᵢ ℓᵢ + (2ε)²`, and
`𝒜 + (2ε)² ≤ μ(P̄ ∩ Λ) ≤ 𝒜 + ε Per(P) + (2ε)²`. -/
theorem LPoly.pick_anisotropic (P : LPoly) (ε : ℝ) :
    (2 * ε) ^ 2 * ((P.I : ℝ) + P.B) =
        (2 * ε) ^ 2 * (|P.shoe| : ℝ) / 2 +
          ε * ∑ i ∈ range P.n, latWeight ((P.v (i + 1)).1 - (P.v i).1) ((P.v (i + 1)).2 - (P.v i).2) *
            (2 * ε * P.elen i) + (2 * ε) ^ 2 ∧
      (2 * ε) ^ 2 * (|P.shoe| : ℝ) / 2 + (2 * ε) ^ 2 ≤ (2 * ε) ^ 2 * ((P.I : ℝ) + P.B) ∧
      (2 * ε) ^ 2 * ((P.I : ℝ) + P.B) ≤
        (2 * ε) ^ 2 * (|P.shoe| : ℝ) / 2 + ε * ∑ i ∈ range P.n, 2 * ε * P.elen i + (2 * ε) ^ 2 := by
  have hpk := (P.pick_mu (K := ℝ) ε).1
  have hcast : (((|P.shoe| : ℤ)) : ℝ) = |(P.shoe : ℝ)| := by push_cast; rfl
  rw [hcast] at hpk
  have hgd : ∀ i ∈ range P.n,
      latWeight ((P.v (i + 1)).1 - (P.v i).1) ((P.v (i + 1)).2 - (P.v i).2) * P.elen i =
        (Int.gcd ((P.v (i + 1)).1 - (P.v i).1) ((P.v (i + 1)).2 - (P.v i).2) : ℝ) := by
    intro i hi
    have hne : Int.gcd ((P.v (i + 1)).1 - (P.v i).1) ((P.v (i + 1)).2 - (P.v i).2) ≠ 0 := by
      intro h0
      rw [Int.gcd_eq_zero_iff] at h0
      have : P.v (i + 1) = P.v i := Prod.ext (by omega) (by omega)
      rw [← P.toCycle.mn_v_mod (i + 1)] at this
      have hi' := mem_range.mp hi
      have := P.inj _ _ (Nat.mod_lt _ P.toCycle.pos) hi' this
      have h3 := P.three
      rcases Nat.lt_or_ge (i + 1) P.n with hh | hh
      · rw [Nat.mod_eq_of_lt hh] at this; omega
      · rw [show i + 1 = P.n by omega, Nat.mod_self] at this; omega
    unfold LPoly.elen
    exact latWeight_mul _ _ hne
  have hB : (P.B : ℝ) = ∑ i ∈ range P.n,
      (Int.gcd ((P.v (i + 1)).1 - (P.v i).1) ((P.v (i + 1)).2 - (P.v i).2) : ℝ) := by
    rw [P.B_eq_sum_gcd]; push_cast; rfl
  have hsum : ε * ∑ i ∈ range P.n, latWeight ((P.v (i + 1)).1 - (P.v i).1)
      ((P.v (i + 1)).2 - (P.v i).2) * (2 * ε * P.elen i) = (2 * ε) ^ 2 * ((P.B : ℝ) / 2) := by
    rw [hB, Finset.mul_sum, Finset.sum_div, Finset.mul_sum]
    refine sum_congr rfl (fun i hi => ?_)
    rw [← hgd i hi]; ring
  have hle : (P.B : ℝ) ≤ ∑ i ∈ range P.n, P.elen i := by
    rw [hB]
    refine sum_le_sum (fun i hi => ?_)
    rw [← hgd i hi]
    have := latWeight_le_one ((P.v (i + 1)).1 - (P.v i).1) ((P.v (i + 1)).2 - (P.v i).2)
    have : 0 ≤ P.elen i := Real.sqrt_nonneg _
    nlinarith
  refine ⟨by rw [hsum, hpk]; ring, ?_, ?_⟩
  · rw [hpk]; have : (0 : ℝ) ≤ P.B := by positivity
    nlinarith [sq_nonneg (2 * ε)]
  · have e : ε * ∑ i ∈ range P.n, 2 * ε * P.elen i = 2 * ε ^ 2 * ∑ i ∈ range P.n, P.elen i := by
      rw [Finset.mul_sum, Finset.mul_sum]; exact sum_congr rfl (fun i _ => by ring)
    rw [hpk, e]
    nlinarith [sq_nonneg ε, mul_le_mul_of_nonneg_left hle (sq_nonneg ε)]

end QE.Pick
