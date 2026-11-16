-- SPDX-License-Identifier: MIT
-- Copyright 2026 Metere Industries, Inc. Author: Alfredo Metere.
-- Quasi-Euclidean Granular Geometry. Any derivative work must carry this notice:
--   This work is derivative of the Quasi-Euclidean Granular Geometry book
--   authored by Alfredo Metere. Copyright 2026 Metere Industries, Inc.
--   All rights reserved
-- See LICENSE.md and NOTICE.

import QuasiEuclidean.Basic

/-!
# Chapter 9: Quasi-Euclidean geometry

Exact finitary facts behind the geometry of thick points and thick lines.
All statements hold for every `ε > 0` (in an ordered field, or in `ℝ` when
trigonometry or Lebesgue measure is involved); the infinitesimal case of the
book is an instance.
-/

set_option linter.unusedSectionVars false

namespace QE.Geometry

section OrderedField
open Finset
variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-- One-dimensional core of incidence: an offset `s` within `r₁` of `x` and
within `r₂` of `y` exists iff `|y - x| ≤ r₁ + r₂`. -/
theorem common_offset_iff (x y r₁ r₂ : K) (h₁ : 0 ≤ r₁) (h₂ : 0 ≤ r₂) :
    (∃ s : K, |x - s| ≤ r₁ ∧ |y - s| ≤ r₂) ↔ |y - x| ≤ r₁ + r₂ := by
  constructor
  · rintro ⟨s, hs₁, hs₂⟩
    calc |y - x| = |(y - s) - (x - s)| := by ring_nf
      _ ≤ |y - s| + |x - s| := abs_sub _ _
      _ ≤ r₁ + r₂ := by linarith
  · intro h
    rcases abs_le.mp h with ⟨hl, hu⟩
    by_cases hxy : x ≤ y
    · refine ⟨min (x + r₁) y, ?_, ?_⟩
      · rw [abs_le]; constructor
        · have := min_le_left (x + r₁) y; linarith
        · rcases min_cases (x + r₁) y with ⟨he, _⟩ | ⟨he, _⟩ <;> rw [he] <;> linarith
      · rw [abs_le]; constructor
        · have := min_le_right (x + r₁) y; linarith
        · rcases min_cases (x + r₁) y with ⟨he, _⟩ | ⟨he, _⟩ <;> rw [he] <;> linarith
    · refine ⟨max (x - r₁) y, ?_, ?_⟩
      · rw [abs_le]; constructor
        · rcases max_cases (x - r₁) y with ⟨he, _⟩ | ⟨he, _⟩ <;> rw [he] <;> linarith
        · have := le_max_left (x - r₁) y; linarith
      · rw [abs_le]; constructor
        · rcases max_cases (x - r₁) y with ⟨he, _⟩ | ⟨he, _⟩ <;> rw [he] <;> linarith
        · have := le_max_right (x - r₁) y; linarith

/-- A line in Hesse normal form `a x + b y = s` (`a² + b² = 1`) meets the
closed ball of radius `ε` about `(c₁, c₂)` iff `|a c₁ + b c₂ - s| ≤ ε`. -/
theorem line_meets_ball_iff (a b s c₁ c₂ ε : K) (hab : a ^ 2 + b ^ 2 = 1)
    (hε : 0 ≤ ε) :
    (∃ x y : K, a * x + b * y = s ∧ (x - c₁) ^ 2 + (y - c₂) ^ 2 ≤ ε ^ 2) ↔
      |a * c₁ + b * c₂ - s| ≤ ε := by
  constructor
  · rintro ⟨x, y, hl, hd⟩
    have key : (a * c₁ + b * c₂ - s) =
        -(a * (x - c₁) + b * (y - c₂)) := by rw [← hl]; ring
    have cs : (a * (x - c₁) + b * (y - c₂)) ^ 2 ≤ ε ^ 2 := by
      nlinarith [sq_nonneg (a * (y - c₂) - b * (x - c₁))]
    rw [key, abs_neg]
    exact abs_le_of_sq_le_sq' cs hε |> fun h => abs_le.mpr h
  · intro h
    set t := s - (a * c₁ + b * c₂) with ht
    refine ⟨c₁ + t * a, c₂ + t * b, ?_, ?_⟩
    · have : a * (c₁ + t * a) + b * (c₂ + t * b) = a * c₁ + b * c₂ + t * (a ^ 2 + b ^ 2) := by
        ring
      rw [this, hab, ht]; ring
    · have e : (c₁ + t * a - c₁) ^ 2 + (c₂ + t * b - c₂) ^ 2 = t ^ 2 := by
        have : (c₁ + t * a - c₁) ^ 2 + (c₂ + t * b - c₂) ^ 2 = t ^ 2 * (a ^ 2 + b ^ 2) := by
          ring
        rw [this, hab, mul_one]
      rw [e]
      have : |t| ≤ ε := by rw [ht, abs_sub_comm]; exact h
      have h0 : 0 ≤ |t| := abs_nonneg t
      calc t ^ 2 = |t| ^ 2 := (sq_abs t).symm
        _ ≤ ε ^ 2 := by nlinarith

/-- Two point-balls of radius `ε` whose centres project (along a unit normal)
to `p` and `q` admit a common incident line with that normal iff
`|q - p| ≤ 2ε`. -/
theorem two_points_common_line (p q ε : K) (hε : 0 ≤ ε) :
    (∃ s : K, |p - s| ≤ ε ∧ |q - s| ≤ ε) ↔ |q - p| ≤ 2 * ε := by
  rw [common_offset_iff p q ε ε hε hε]; constructor <;> intro h <;> linarith

theorem parallel_meet_iff (h Ω ε r m : K) (hh : 0 < h) (hΩ : 0 ≤ Ω) (hε : 0 ≤ ε) (hr : 0 ≤ r) :
    (∃ x y : K, |x| ≤ Ω ∧ |y| ≤ ε ∧ |y - h - m * x| ≤ r) ↔ h - |m| * Ω ≤ ε + r := by
  constructor
  · rintro ⟨x, y, hx, hy, hl⟩
    have e : h = y - (y - h - m * x) - m * x := by ring
    have h1 : |m * x| ≤ |m| * Ω := by rw [abs_mul]; exact mul_le_mul_of_nonneg_left hx (abs_nonneg m)
    have h2 := le_abs_self y
    have h3 := neg_abs_le (y - h - m * x)
    have h4 := neg_abs_le (m * x)
    linarith
  · intro hc
    set u := max (h - |m| * Ω) 0 with hu
    have hu0 : 0 ≤ u := le_max_right _ _
    have huh : u ≤ h := max_le (by nlinarith [abs_nonneg m]) hh.le
    have hulow : h - |m| * Ω ≤ u := le_max_left _ _
    have huer : u ≤ ε + r := max_le hc (by linarith)
    -- choose x with h + m x = u
    obtain ⟨x, hx, hxe⟩ : ∃ x : K, |x| ≤ Ω ∧ h + m * x = u := by
      rcases eq_or_ne m 0 with hm | hm
      · refine ⟨0, by simp [hΩ], ?_⟩
        subst hm
        simp only [abs_zero, zero_mul, sub_zero] at hulow
        simp; linarith
      · refine ⟨(u - h) / m, ?_, by field_simp; ring⟩
        rw [abs_div, div_le_iff₀ (abs_pos.mpr hm)]
        rw [abs_of_nonpos (by linarith)]
        linarith
    refine ⟨x, min u ε, hx, ?_, ?_⟩
    · rw [abs_of_nonneg (le_min hu0 hε)]; exact min_le_right _ _
    · have : min u ε - h - m * x = min u ε - u := by rw [← hxe]; ring
      rw [this, abs_of_nonpos (by linarith [min_le_left u ε])]
      rcases min_cases u ε with ⟨he, _⟩ | ⟨he, _⟩ <;> rw [he] <;> linarith

theorem strips_meet (a b c d s t : K) (hdet : a * d - b * c ≠ 0) :
    ∃ x y : K, a * x + b * y = s ∧ c * x + d * y = t :=
  ⟨(s * d - b * t) / (a * d - b * c), (a * t - s * c) / (a * d - b * c),
    by rw [mul_div_assoc', mul_div_assoc', ← add_div,
          show a * (s * d - b * t) + b * (a * t - s * c) = s * (a * d - b * c) by ring,
          mul_div_cancel_right₀ _ hdet],
    by rw [mul_div_assoc', mul_div_assoc', ← add_div,
          show c * (s * d - b * t) + d * (a * t - s * c) = t * (a * d - b * c) by ring,
          mul_div_cancel_right₀ _ hdet]⟩

theorem snap_error [FloorRing K] (ε x : K) (hε : 0 < ε) :
    |2 * ε * (round (x / (2 * ε)) : K) - x| ≤ ε := by
  have h := abs_sub_round (x / (2 * ε))
  have h2 : 0 < 2 * ε := by linarith
  have : 2 * ε * (round (x / (2 * ε)) : K) - x = -(2 * ε) * (x / (2 * ε) - round (x / (2 * ε))) := by
    field_simp; ring
  rw [this, abs_mul, abs_neg, abs_of_pos h2]
  calc 2 * ε * |x / (2 * ε) - round (x / (2 * ε))| ≤ 2 * ε * (1 / 2) :=
        mul_le_mul_of_nonneg_left h h2.le
    _ = ε := by ring

theorem zeno_dichotomy (n : ℕ) :
    (∑ k ∈ range n, (1 / 2 : K) ^ (k + 1)) + (1 / 2 : K) ^ n = 1 := by
  induction n with
  | zero => simp
  | succ n ih => rw [sum_range_succ]; rw [pow_succ] at *; linarith

theorem achilles (a b g : ℕ) (hab : b < a) :
    ∃ t : ℕ, t ≤ g ∧ g + b * t ≤ a * t ∧ ∀ s < t, a * s < g + b * s := by
  classical
  have hex : ∃ t : ℕ, g + b * t ≤ a * t := ⟨g, by nlinarith⟩
  refine ⟨Nat.find hex, ?_, Nat.find_spec hex, fun s hs => ?_⟩
  · exact Nat.find_min' hex (by nlinarith)
  · have := Nat.find_min hex hs; omega

theorem no_paradoxical_decomposition {α β ι : Type*} [DecidableEq α] [DecidableEq β]
    (B : Finset α) (I : Finset ι) (A : ι → Finset α) (f : ι → α → β)
    (hA : ∀ i ∈ I, A i ⊆ B) (hdisj : (I : Set ι).PairwiseDisjoint A) :
    (I.biUnion (fun i => (A i).image (f i))).card ≤ B.card := by
  calc (I.biUnion (fun i => (A i).image (f i))).card
      ≤ ∑ i ∈ I, ((A i).image (f i)).card := card_biUnion_le
    _ ≤ ∑ i ∈ I, (A i).card := sum_le_sum fun i _ => card_image_le
    _ = (I.biUnion A).card := (card_biUnion hdisj).symm
    _ ≤ B.card := card_le_card (biUnion_subset.mpr hA)

theorem no_doubling {α β ι : Type*} [DecidableEq α] [DecidableEq β]
    (B : Finset α) (I : Finset ι) (A : ι → Finset α) (f : ι → α → β)
    (hA : ∀ i ∈ I, A i ⊆ B) (hdisj : (I : Set ι).PairwiseDisjoint A)
    (C₁ C₂ : Finset β) (hC : Disjoint C₁ C₂) (h₁ : C₁.card = B.card) (h₂ : C₂.card = B.card)
    (hB : 0 < B.card) :
    I.biUnion (fun i => (A i).image (f i)) ≠ C₁ ∪ C₂ := by
  intro h
  have := no_paradoxical_decomposition B I A f hA hdisj
  rw [h, card_union_of_disjoint hC] at this
  omega


/-- Thick lines (tube radius `ε` about `y = 0`, and tube of vertical half-width `r` about
`y = h + m x`) restricted to the box `|x| ≤ Ω` are disjoint iff `|m| Ω + ε + r < h`. -/
theorem parallel_disjoint_iff (h Ω ε r m : K) (hh : 0 < h) (hΩ : 0 ≤ Ω) (hε : 0 ≤ ε)
    (hr : 0 ≤ r) :
    (¬ ∃ x y : K, |x| ≤ Ω ∧ |y| ≤ ε ∧ |y - h - m * x| ≤ r) ↔ |m| * Ω + ε + r < h := by
  rw [parallel_meet_iff h Ω ε r m hh hΩ hε hr, not_le]; constructor <;> intro H <;> linarith

/-- Additivity of the Pick functional `2I + B - 2` under gluing two lattice polygons along a
common boundary chain containing `k` lattice points. -/
theorem pick_glue (I₁ B₁ I₂ B₂ k : ℤ) :
    let I := I₁ + I₂ + (k - 2)
    let B := B₁ + B₂ - 2 * k + 2
    2 * I + B - 2 = (2 * I₁ + B₁ - 2) + (2 * I₂ + B₂ - 2) := by
  simp only; ring

/-- Closed lattice box in `n` dimensions. -/
def closedBox {n : ℕ} (a b : Fin n → ℤ) : Finset (Fin n → ℤ) :=
  Fintype.piFinset fun i => Finset.Icc (a i) (b i)

def openBox {n : ℕ} (a b : Fin n → ℤ) : Finset (Fin n → ℤ) :=
  Fintype.piFinset fun i => Finset.Ioo (a i) (b i)

def halfOpenBox {n : ℕ} (a b : Fin n → ℤ) : Finset (Fin n → ℤ) :=
  Fintype.piFinset fun i => Finset.Ico (a i) (b i)

theorem muN_closedBox {n : ℕ} (ε : K) (a b : Fin n → ℤ) (h : ∀ i, a i ≤ b i) :
    QE.muN n ε (closedBox a b) = ∏ i, ((QE.centre ε (b i) - QE.centre ε (a i)) + 2 * ε) := by
  unfold QE.muN closedBox QE.centre
  rw [Fintype.card_piFinset, Nat.cast_prod, show (2 * ε) ^ n = ∏ _i : Fin n, (2 * ε) by simp, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [Int.card_Icc]
  have hc : (((b i + 1 - a i).toNat : ℕ) : K) = ((b i + 1 - a i : ℤ) : K) := by
    rw [← Int.cast_natCast, Int.toNat_of_nonneg (by linarith [h i])]

  rw [hc]; push_cast; ring

theorem muN_openBox {n : ℕ} (ε : K) (a b : Fin n → ℤ) (h : ∀ i, a i < b i) :
    QE.muN n ε (openBox a b) = ∏ i, ((QE.centre ε (b i) - QE.centre ε (a i)) - 2 * ε) := by
  unfold QE.muN openBox QE.centre
  rw [Fintype.card_piFinset, Nat.cast_prod, show (2 * ε) ^ n = ∏ _i : Fin n, (2 * ε) by simp, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [Int.card_Ioo]
  have hc : (((b i - a i - 1).toNat : ℕ) : K) = ((b i - a i - 1 : ℤ) : K) := by
    rw [← Int.cast_natCast, Int.toNat_of_nonneg (by linarith [h i])]
  rw [hc]; push_cast; ring

theorem muN_halfOpenBox {n : ℕ} (ε : K) (a b : Fin n → ℤ) (h : ∀ i, a i ≤ b i) :
    QE.muN n ε (halfOpenBox a b) = ∏ i, (QE.centre ε (b i) - QE.centre ε (a i)) := by
  unfold QE.muN halfOpenBox QE.centre
  rw [Fintype.card_piFinset, Nat.cast_prod, show (2 * ε) ^ n = ∏ _i : Fin n, (2 * ε) by simp, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [Int.card_Ico]
  have hc : (((b i - a i).toNat : ℕ) : K) = ((b i - a i : ℤ) : K) := by
    rw [← Int.cast_natCast, Int.toNat_of_nonneg (by linarith [h i])]
  rw [hc]; push_cast; ring

/-- Lattice-rectangle counts (Pick for rectangles). -/
theorem card_rect_closed (m n : ℕ) :
    ((range (m + 1)) ×ˢ (range (n + 1))).card = (m + 1) * (n + 1) := by
  simp

theorem card_rect_open (m n : ℕ) :
    ((Ioo 0 m) ×ˢ (Ioo 0 n)).card = (m - 1) * (n - 1) := by
  simp

theorem pick_rectangle (m n : ℕ) (hm : 1 ≤ m) (hn : 1 ≤ n) :
    let C := ((range (m + 1)) ×ˢ (range (n + 1))).card
    let I := ((Ioo 0 m) ×ˢ (Ioo 0 n)).card
    C - I = 2 * (m + n) ∧ 2 * I + (C - I) = 2 * (m * n) + 2 ∧ 2 * C = 2 * (m * n) + (C - I) + 2 := by
  simp only [card_rect_closed, card_rect_open]
  obtain ⟨m, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
  obtain ⟨n, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  refine ⟨?_, ?_, ?_⟩ <;> ring_nf <;> omega

/-- **Cubical Steiner formula as a count identity** (granular, Lebesgue-free).
With side lengths `Lᵢ = 2ε(bᵢ - aᵢ)`, the closed lattice box has exactly
`∏ (Lᵢ/(2ε) + 1)` points, and its content expands in powers of the point
diameter: `μ = ∑_{S ⊆ {1..n}} (2ε)^{|S|} ∏_{i ∉ S} Lᵢ` (volume, then `2ε` times
the half-surface, …, then `(2ε)ⁿ`).  The comparison with the Lebesgue volume of
the `ε`-thickened continuum box is the separate shadow lemma
`closedBox_volume_shadow`. -/
theorem closedBox_eq_thickened {n : ℕ} (ε : K) (hε : ε ≠ 0) (a b : Fin n → ℤ)
    (h : ∀ i, a i ≤ b i) :
    ((closedBox a b).card : K) =
        ∏ i, ((QE.centre ε (b i) - QE.centre ε (a i)) / (2 * ε) + 1) ∧
    QE.muN n ε (closedBox a b) =
      ∑ S ∈ (Finset.univ : Finset (Fin n)).powerset,
        (2 * ε) ^ S.card * ∏ i ∈ Finset.univ \ S, (QE.centre ε (b i) - QE.centre ε (a i)) := by
  have hμ := muN_closedBox ε a b h
  have h2 : (2 * ε) ≠ 0 := mul_ne_zero two_ne_zero hε
  constructor
  · have hpow : (2 * ε) ^ n ≠ 0 := pow_ne_zero _ h2
    unfold QE.muN at hμ
    have hc : ((closedBox a b).card : K) =
        (∏ i, ((QE.centre ε (b i) - QE.centre ε (a i)) + 2 * ε)) / (2 * ε) ^ n := by
      rw [← hμ]; field_simp
    rw [hc, show (2 * ε) ^ n = ∏ _i : Fin n, (2 * ε) by simp, ← Finset.prod_div_distrib]
    refine Finset.prod_congr rfl fun i _ => ?_
    field_simp
  · rw [hμ, show (∏ i, ((QE.centre ε (b i) - QE.centre ε (a i)) + 2 * ε))
        = ∏ i, (2 * ε + (QE.centre ε (b i) - QE.centre ε (a i))) by
          exact Finset.prod_congr rfl fun i _ => add_comm _ _, Finset.prod_add]
    refine Finset.sum_congr rfl fun S _ => ?_
    rw [Finset.prod_const]

/-- Two-dimensional expansion: `μ(closed rectangle) = A + ε P + (2ε)²` with `P` the perimeter. -/
theorem steiner_rect (ε L₁ L₂ : K) :
    (L₁ + 2 * ε) * (L₂ + 2 * ε) = L₁ * L₂ + ε * (2 * (L₁ + L₂)) + (2 * ε) ^ 2 := by ring

/-- Pick for lattice rectangles in measure form:
`μ(closed) = A + (2ε)²(B/2 + 1)` with `B = 2(m+n)` boundary points. -/
theorem pick_rectangle_mu (ε : K) (m n : ℕ) :
    (2 * ε) ^ 2 * (((range (m + 1)) ×ˢ (range (n + 1))).card : K)
      = (2 * ε * m) * (2 * ε * n) + (2 * ε) ^ 2 * ((2 * (m + n) : K) / 2 + 1) := by
  rw [card_rect_closed]; push_cast; ring

end OrderedField

section LatticeCounting
open Finset

/-! ### Intersections of lattice strips: exact counts (Lebesgue-free) -/

lemma abs_lin_le (p q x y X Y : ℤ) (hx : |x| ≤ X) (hy : |y| ≤ Y) :
    |p * x + q * y| ≤ |p| * X + |q| * Y := by
  calc |p * x + q * y| ≤ |p * x| + |q * y| := abs_add_le _ _
    _ = |p| * |x| + |q| * |y| := by rw [abs_mul, abs_mul]
    _ ≤ _ := add_le_add (mul_le_mul_of_nonneg_left hx (abs_nonneg _))
        (mul_le_mul_of_nonneg_left hy (abs_nonneg _))

/-- A box large enough to contain the intersection of the two strips. -/
def stripBox (a b c d : ℤ) (w : ℕ) : ℤ := (|a| + |b| + |c| + |d|) * w

/-- Lattice points `k ∈ ℤ²` of the intersection of the two lattice strips
`|a k₁ + b k₂| ≤ w` and `|c k₁ + d k₂| ≤ w` (integer normals, half-width `w`). -/
def stripPts (a b c d : ℤ) (w : ℕ) : Finset (ℤ × ℤ) :=
  ((Icc (-stripBox a b c d w) (stripBox a b c d w)) ×ˢ
    (Icc (-stripBox a b c d w) (stripBox a b c d w))).filter
    (fun k => |a * k.1 + b * k.2| ≤ w ∧ |c * k.1 + d * k.2| ≤ w)

/-- For non-parallel strips, `stripPts` is exactly the set of lattice points of
the intersection (the bounding box cuts nothing). -/
lemma mem_stripPts (a b c d : ℤ) (w : ℕ) (hD : a * d - b * c ≠ 0) (k : ℤ × ℤ) :
    k ∈ stripPts a b c d w ↔ |a * k.1 + b * k.2| ≤ w ∧ |c * k.1 + d * k.2| ≤ w := by
  unfold stripPts
  rw [mem_filter]
  refine ⟨fun h => h.2, fun h => ⟨?_, h⟩⟩
  have hD1 : 1 ≤ |a * d - b * c| := Int.one_le_abs hD
  have hw : (0 : ℤ) ≤ w := by positivity
  have bnd : ∀ x : ℤ, |(a * d - b * c) * x| ≤ (|a| + |b| + |c| + |d|) * w → |x| ≤ stripBox a b c d w := by
    intro x hx
    unfold stripBox
    rw [abs_mul] at hx
    nlinarith [abs_nonneg x]
  have e1 : (a * d - b * c) * k.1 = d * (a * k.1 + b * k.2) + (-b) * (c * k.1 + d * k.2) := by ring
  have e2 : (a * d - b * c) * k.2 = (-c) * (a * k.1 + b * k.2) + a * (c * k.1 + d * k.2) := by ring
  have b1 := abs_lin_le d (-b) _ _ _ _ h.1 h.2
  have b2 := abs_lin_le (-c) a _ _ _ _ h.1 h.2
  rw [abs_neg] at b1 b2
  have k1 := bnd k.1 (by rw [e1]; nlinarith [abs_nonneg a, abs_nonneg c])
  have k2 := bnd k.2 (by rw [e2]; nlinarith [abs_nonneg b, abs_nonneg d])
  rw [mem_product, mem_Icc, mem_Icc]
  exact ⟨abs_le.mp k1, abs_le.mp k2⟩

lemma card_Icc_sym (t : ℕ) : (Icc (-(t : ℤ)) t).card = 2 * t + 1 := by
  rw [Int.card_Icc]; omega

/-- **Lattice points of two intersecting lattice strips** (granular,
Lebesgue-free).  For integer normals with `D = ad - bc ≠ 0` and half-width
`w`, the number of lattice points in the intersection satisfies
`(2⌊w/|D|⌋ + 1)² ≤ # ≤ (2w + 1)²`.  The upper bound is the injection
`k ↦ (ak₁+bk₂, ck₁+dk₂)` into the `(2w+1)²` admissible value pairs; the lower
bound is the sublattice `D ℤ²` of values, realised by `adj(M) u`. -/
theorem strip_count (a b c d : ℤ) (w : ℕ) (hD : a * d - b * c ≠ 0) :
    (2 * (w / (a * d - b * c).natAbs) + 1) ^ 2 ≤ (stripPts a b c d w).card ∧
    (stripPts a b c d w).card ≤ (2 * w + 1) ^ 2 := by
  set D := a * d - b * c with hDdef
  have hDn : 1 ≤ D.natAbs := by have := Int.natAbs_pos.mpr hD; omega
  constructor
  · set t := w / D.natAbs with ht
    have htw : t * D.natAbs ≤ w := Nat.div_mul_le_self w D.natAbs
    have hcard : (Icc (-(t : ℤ)) t ×ˢ Icc (-(t : ℤ)) t).card = (2 * t + 1) ^ 2 := by
      rw [card_product, card_Icc_sym]; ring
    rw [← hcard]
    refine card_le_card_of_injOn (fun u => (d * u.1 - b * u.2, -c * u.1 + a * u.2)) ?_ ?_
    · intro u hu
      obtain ⟨h1, h2⟩ := mem_product.mp (mem_coe.mp hu)
      have hu1 : |u.1| ≤ t := abs_le.mpr (mem_Icc.mp h1)
      have hu2 : |u.2| ≤ t := abs_le.mpr (mem_Icc.mp h2)
      apply mem_coe.mpr
      rw [mem_stripPts a b c d w hD]
      have htw' : (t : ℤ) * |D| ≤ w := by
        rw [Int.abs_eq_natAbs]; exact_mod_cast htw
      have f1 : a * (d * u.1 - b * u.2) + b * (-c * u.1 + a * u.2) = D * u.1 := by
        rw [hDdef]; ring
      have f2 : c * (d * u.1 - b * u.2) + d * (-c * u.1 + a * u.2) = D * u.2 := by
        rw [hDdef]; ring
      simp only
      rw [f1, f2, abs_mul, abs_mul]
      constructor <;> nlinarith [abs_nonneg D]
    · intro u _ v _ huv
      simp only [Prod.mk.injEq] at huv
      obtain ⟨h1, h2⟩ := huv
      have g1 : D * u.1 = D * v.1 := by rw [hDdef]; linear_combination a * h1 + b * h2
      have g2 : D * u.2 = D * v.2 := by rw [hDdef]; linear_combination c * h1 + d * h2
      exact Prod.ext (mul_left_cancel₀ hD g1) (mul_left_cancel₀ hD g2)
  · have hcard : (Icc (-(w : ℤ)) w ×ˢ Icc (-(w : ℤ)) w).card = (2 * w + 1) ^ 2 := by
      rw [card_product, card_Icc_sym]; ring
    rw [← hcard]
    refine card_le_card_of_injOn (fun k => (a * k.1 + b * k.2, c * k.1 + d * k.2)) ?_ ?_
    · intro k hk
      have := (mem_stripPts a b c d w hD k).mp (mem_coe.mp hk)
      apply mem_coe.mpr
      rw [mem_product, mem_Icc, mem_Icc]
      exact ⟨abs_le.mp this.1, abs_le.mp this.2⟩
    · intro k _ l _ hkl
      simp only [Prod.mk.injEq] at hkl
      obtain ⟨h1, h2⟩ := hkl
      have g1 : D * k.1 = D * l.1 := by rw [hDdef]; linear_combination d * h1 - b * h2
      have g2 : D * k.2 = D * l.2 := by rw [hDdef]; linear_combination (-c) * h1 + a * h2
      exact Prod.ext (mul_left_cancel₀ hD g1) (mul_left_cancel₀ hD g2)

/-- **Unimodular strips: an exact count.**  If `|ad - bc| = 1`, two lattice
strips of half-width `w` meet in exactly `(2w + 1)²` lattice points, i.e.
content `(2ε)²(2w+1)²`, independently of the angle between them. -/
theorem strip_count_unimodular (a b c d : ℤ) (w : ℕ) (hD : |a * d - b * c| = 1) :
    (stripPts a b c d w).card = (2 * w + 1) ^ 2 := by
  have hD0 : a * d - b * c ≠ 0 := by intro h; rw [h] at hD; simp at hD
  have hn : (a * d - b * c).natAbs = 1 := by
    have := Int.natAbs_abs (a * d - b * c); rw [hD] at this; omega
  obtain ⟨h1, h2⟩ := strip_count a b c d w hD0
  rw [hn, Nat.div_one] at h1
  omega

/-- Lattice points on the hypotenuse `b x + a y = a b` of the right triangle with legs `a, b`. -/
theorem card_hypotenuse (a b : ℕ) (ha : 0 < a) (hb : 0 < b) :
    (((range (a + 1)) ×ˢ (range (b + 1))).filter (fun p => b * p.1 + a * p.2 = a * b)).card
      = Nat.gcd a b + 1 := by
  set g := Nat.gcd a b with hg
  have hg0 : 0 < g := Nat.gcd_pos_of_pos_left b ha
  obtain ⟨a', ha'⟩ : g ∣ a := Nat.gcd_dvd_left a b
  obtain ⟨b', hb'⟩ : g ∣ b := Nat.gcd_dvd_right a b
  have hcop : Nat.Coprime a' b' := by
    have := Nat.coprime_div_gcd_div_gcd (m := a) (n := b) hg0
    rw [← hg] at this
    have e1 : a / g = a' := by rw [ha']; exact Nat.mul_div_cancel_left a' hg0
    have e2 : b / g = b' := by rw [hb']; exact Nat.mul_div_cancel_left b' hg0
    rwa [e1, e2] at this
  have ha'0 : 0 < a' := by rcases Nat.eq_zero_or_pos a' with h | h <;> [simp [h] at ha'; exact h]; omega
  have hb'0 : 0 < b' := by rcases Nat.eq_zero_or_pos b' with h | h <;> [simp [h] at hb'; exact h]; omega
  have himg : ((range (a + 1)) ×ˢ (range (b + 1))).filter (fun p => b * p.1 + a * p.2 = a * b)
      = (range (g + 1)).image (fun j => (j * a', (g - j) * b')) := by
    ext ⟨x, y⟩
    simp only [mem_filter, mem_product, mem_range, mem_image, Prod.mk.injEq]
    constructor
    · rintro ⟨⟨hx, hy⟩, he⟩
      -- divide by g
      have he' : b' * x + a' * y = a' * b' * g := by
        rw [ha', hb'] at he
        have : g * (b' * x + a' * y) = g * (a' * b' * g) :=
          calc g * (b' * x + a' * y) = g * b' * x + g * a' * y := by ring
            _ = g * a' * (g * b') := he
            _ = g * (a' * b' * g) := by ring
        exact Nat.eq_of_mul_eq_mul_left hg0 this
      have hdvd : a' ∣ b' * x := by
        have : a' ∣ b' * x + a' * y := ⟨b' * g, by rw [he']; ring⟩
        exact (Nat.dvd_add_right (dvd_mul_right a' y)).mp (by rwa [add_comm] at this)
      obtain ⟨j, rfl⟩ := hcop.dvd_of_dvd_mul_left hdvd
      have hj : j ≤ g := by
        have : a' * j ≤ g * a' := by rw [ha'] at hx; linarith
        nlinarith
      refine ⟨j, by omega, by ring, ?_⟩
      have : a' * y = a' * ((g - j) * b') := by
        have h1 : a' * y = a' * b' * g - b' * (a' * j) := by omega
        rw [h1, Nat.sub_mul, Nat.mul_sub]; ring_nf
      exact (Nat.eq_of_mul_eq_mul_left ha'0 this).symm
    · rintro ⟨j, hj, rfl, rfl⟩
      have hj' : j ≤ g := by omega
      refine ⟨⟨?_, ?_⟩, ?_⟩
      · rw [ha']; nlinarith
      · rw [hb']; have : (g - j) * b' ≤ g * b' := Nat.mul_le_mul_right _ (Nat.sub_le g j); omega
      · rw [ha', hb']
        conv_rhs => rw [show g * a' * (g * b') = g * a' * (((g - j) + j) * b') by
          rw [Nat.sub_add_cancel hj']]
        ring
  rw [himg, card_image_of_injective, card_range]
  intro i j hij
  simp only [Prod.mk.injEq] at hij
  exact Nat.eq_of_mul_eq_mul_right ha'0 hij.1

theorem card_open_hypotenuse (a b : ℕ) (ha : 0 < a) (hb : 0 < b) :
    (((Ioo 0 a) ×ˢ (Ioo 0 b)).filter (fun p => b * p.1 + a * p.2 = a * b)).card + 2
      = Nat.gcd a b + 1 := by
  rw [← card_hypotenuse a b ha hb]
  have hsplit : ((range (a + 1)) ×ˢ (range (b + 1))).filter (fun p => b * p.1 + a * p.2 = a * b)
      = insert (0, b) (insert (a, 0)
          (((Ioo 0 a) ×ˢ (Ioo 0 b)).filter (fun p => b * p.1 + a * p.2 = a * b))) := by
    ext ⟨x, y⟩
    simp only [mem_filter, mem_product, mem_range, mem_Ioo, mem_insert, Prod.mk.injEq]
    constructor
    · rintro ⟨⟨hx, hy⟩, he⟩
      by_cases hx0 : x = 0
      · subst hx0; left; refine ⟨rfl, ?_⟩
        simp at he; omega
      by_cases hy0 : y = 0
      · subst hy0; right; left; refine ⟨?_, rfl⟩
        simp only [mul_zero, add_zero] at he
        exact Nat.eq_of_mul_eq_mul_left hb (he.trans (mul_comm a b))
      right; right
      refine ⟨⟨⟨by omega, ?_⟩, ⟨by omega, ?_⟩⟩, he⟩
      · by_contra hc
        have : x = a := by omega
        subst this; nlinarith [Nat.pos_of_ne_zero hy0]
      · by_contra hc
        have : y = b := by omega
        subst this; nlinarith [Nat.pos_of_ne_zero hx0]
    · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩, he⟩)
      · exact ⟨⟨by omega, by omega⟩, by ring⟩
      · exact ⟨⟨by omega, by omega⟩, by ring⟩
      · exact ⟨⟨by omega, by omega⟩, he⟩
  rw [hsplit, card_insert_of_notMem, card_insert_of_notMem]
  · simp only [mem_filter, mem_product, mem_Ioo]; omega
  · simp only [mem_insert, Prod.mk.injEq, mem_filter, mem_product, mem_Ioo, not_or]; omega

/-- Interior lattice points of the open right triangle: `2 I + gcd(a,b) - 1 = (a-1)(b-1)`. -/
theorem card_open_right_triangle (a b : ℕ) (ha : 0 < a) (hb : 0 < b) :
    2 * (((Ioo 0 a) ×ˢ (Ioo 0 b)).filter (fun p => b * p.1 + a * p.2 < a * b)).card
      + (Nat.gcd a b - 1) = (a - 1) * (b - 1) := by
  set R := (Ioo 0 a) ×ˢ (Ioo 0 b)
  set T := R.filter (fun p => b * p.1 + a * p.2 < a * b)
  set T' := R.filter (fun p => a * b < b * p.1 + a * p.2)
  set D := R.filter (fun p => b * p.1 + a * p.2 = a * b)
  have hR : R.card = (a - 1) * (b - 1) := by simp [R]
  have hpart : R.card = T.card + T'.card + D.card := by
    have h1 : R = (T ∪ T') ∪ D := by
      ext p; simp only [T, T', D, mem_union, mem_filter]; constructor
      · intro h; rcases lt_trichotomy (b * p.1 + a * p.2) (a * b) with h' | h' | h'
        · exact Or.inl (Or.inl ⟨h, h'⟩)
        · exact Or.inr ⟨h, h'⟩
        · exact Or.inl (Or.inr ⟨h, h'⟩)
      · rintro ((⟨h, _⟩ | ⟨h, _⟩) | ⟨h, _⟩) <;> exact h
    rw [h1, card_union_of_disjoint, card_union_of_disjoint]
    · rw [disjoint_filter]; intro p _ h1 h2; omega
    · rw [disjoint_union_left]; constructor <;> (rw [disjoint_filter]; intro p _ h1 h2; omega)
  have hTT' : T'.card = T.card := by
    refine card_nbij' (fun p => (a - p.1, b - p.2)) (fun p => (a - p.1, b - p.2)) ?_ ?_ ?_ ?_
    · rintro ⟨x, y⟩ hp
      simp only [T, T', R, coe_filter, Set.mem_ofPred_eq, mem_product, mem_Ioo] at hp ⊢
      obtain ⟨⟨⟨hx1, hx⟩, ⟨hy1, hy⟩⟩, h⟩ := hp
      refine ⟨⟨⟨by omega, by omega⟩, ⟨by omega, by omega⟩⟩, ?_⟩
      have hx' : x ≤ a := by omega
      have hy' : y ≤ b := by omega
      zify [hx', hy'] at h ⊢; nlinarith
    · rintro ⟨x, y⟩ hp
      simp only [T, T', R, coe_filter, Set.mem_ofPred_eq, mem_product, mem_Ioo] at hp ⊢
      obtain ⟨⟨⟨hx1, hx⟩, ⟨hy1, hy⟩⟩, h⟩ := hp
      refine ⟨⟨⟨by omega, by omega⟩, ⟨by omega, by omega⟩⟩, ?_⟩
      have hx' : x ≤ a := by omega
      have hy' : y ≤ b := by omega
      zify [hx', hy'] at h ⊢; nlinarith
    · rintro ⟨x, y⟩ hp
      simp only [T', R, coe_filter, Set.mem_ofPred_eq, mem_product, mem_Ioo] at hp
      simp only [Prod.mk.injEq]; omega
    · rintro ⟨x, y⟩ hp
      simp only [T, R, coe_filter, Set.mem_ofPred_eq, mem_product, mem_Ioo] at hp
      simp only [Prod.mk.injEq]; omega
  have hD := card_open_hypotenuse a b ha hb
  have hg : 1 ≤ Nat.gcd a b := Nat.gcd_pos_of_pos_left b ha
  rw [hpart, hTT'] at hR
  change D.card + 2 = Nat.gcd a b + 1 at hD
  omega

/-- Pick for lattice right triangles: `2·#T = (a+1)(b+1) + gcd(a,b) + 1`. -/
theorem card_right_triangle (a b : ℕ) (ha : 0 < a) (hb : 0 < b) :
    2 * (((range (a + 1)) ×ˢ (range (b + 1))).filter (fun p => b * p.1 + a * p.2 ≤ a * b)).card
      = (a + 1) * (b + 1) + Nat.gcd a b + 1 := by
  set R := (range (a + 1)) ×ˢ (range (b + 1))
  set T := R.filter (fun p => b * p.1 + a * p.2 ≤ a * b)
  set T' := R.filter (fun p => a * b ≤ b * p.1 + a * p.2)
  have hU : T ∪ T' = R := by
    ext p; simp only [T, T', mem_union, mem_filter]; constructor
    · rintro (⟨h, _⟩ | ⟨h, _⟩) <;> exact h
    · intro h; rcases le_total (b * p.1 + a * p.2) (a * b) with h' | h'
      · exact Or.inl ⟨h, h'⟩
      · exact Or.inr ⟨h, h'⟩
  have hI : T ∩ T' = R.filter (fun p => b * p.1 + a * p.2 = a * b) := by
    ext p; simp only [T, T', mem_inter, mem_filter]; constructor
    · rintro ⟨⟨h, h1⟩, ⟨_, h2⟩⟩; exact ⟨h, le_antisymm h1 h2⟩
    · rintro ⟨h, h1⟩; exact ⟨⟨h, h1.le⟩, ⟨h, h1.ge⟩⟩
  have hTT' : T'.card = T.card := by
    refine card_nbij' (fun p => (a - p.1, b - p.2)) (fun p => (a - p.1, b - p.2)) ?_ ?_ ?_ ?_
    · rintro ⟨x, y⟩ hp
      simp only [T, T', R, coe_filter, Set.mem_ofPred_eq, mem_product, mem_range] at hp ⊢
      obtain ⟨⟨hx, hy⟩, h⟩ := hp
      refine ⟨⟨by omega, by omega⟩, ?_⟩
      have hx' : x ≤ a := by omega
      have hy' : y ≤ b := by omega
      zify [hx', hy'] at h ⊢; nlinarith
    · rintro ⟨x, y⟩ hp
      simp only [T, T', R, coe_filter, Set.mem_ofPred_eq, mem_product, mem_range] at hp ⊢
      obtain ⟨⟨hx, hy⟩, h⟩ := hp
      refine ⟨⟨by omega, by omega⟩, ?_⟩
      have hx' : x ≤ a := by omega
      have hy' : y ≤ b := by omega
      zify [hx', hy'] at h ⊢; nlinarith
    · rintro ⟨x, y⟩ hp
      simp only [T', R, coe_filter, Set.mem_ofPred_eq, mem_product, mem_range] at hp
      simp only [Prod.mk.injEq]; omega
    · rintro ⟨x, y⟩ hp
      simp only [T, R, coe_filter, Set.mem_ofPred_eq, mem_product, mem_range] at hp
      simp only [Prod.mk.injEq]; omega
  have key := card_union_add_card_inter T T'
  rw [hU, hI, card_hypotenuse a b ha hb, hTT'] at key
  have hR : R.card = (a + 1) * (b + 1) := by simp [R]
  rw [hR] at key; omega

/-- Pick's theorem for lattice right triangles with legs `a, b` on the axes:
with `C` the closed count, `I` the interior count and `B = C - I`,
`B = a + b + gcd(a,b)` and `2I + B - 2 = a b` (i.e. `Area = I + B/2 - 1`). -/
theorem pick_right_triangle (a b : ℕ) (ha : 0 < a) (hb : 0 < b) (C I : ℕ)
    (hC : C = (((range (a + 1)) ×ˢ (range (b + 1))).filter
      (fun p => b * p.1 + a * p.2 ≤ a * b)).card)
    (hI : I = (((Ioo 0 a) ×ˢ (Ioo 0 b)).filter (fun p => b * p.1 + a * p.2 < a * b)).card) :
    (C : ℤ) - I = a + b + Nat.gcd a b ∧ 2 * (I : ℤ) + ((C : ℤ) - I) - 2 = a * b := by
  have h1 := card_right_triangle a b ha hb
  have h2 := card_open_right_triangle a b ha hb
  rw [← hC] at h1; rw [← hI] at h2
  have hg : 1 ≤ Nat.gcd a b := Nat.gcd_pos_of_pos_left b ha
  generalize Nat.gcd a b = g at h1 h2 hg ⊢
  obtain ⟨a, rfl⟩ : ∃ k, a = k + 1 := ⟨a - 1, by omega⟩
  obtain ⟨b, rfl⟩ : ∃ k, b = k + 1 := ⟨b - 1, by omega⟩
  simp only [Nat.add_sub_cancel] at h2
  obtain ⟨g, rfl⟩ : ∃ k, g = k + 1 := ⟨g - 1, by omega⟩
  simp only [Nat.add_sub_cancel] at h2
  have h1' : (2 * C : ℤ) = (a + 2) * (b + 2) + (g + 1) + 1 := by exact_mod_cast h1
  have h2' : (2 * I : ℤ) + g = a * b := by exact_mod_cast h2
  push_cast
  constructor <;> nlinarith [h1', h2']

end LatticeCounting

section Fractal
open Real

/-- Number of segments of the `n`-th Koch polygon (each step replaces a segment by 4). -/
def kochSegments : ℕ → ℕ
  | 0 => 1
  | n + 1 => 4 * kochSegments n

theorem kochSegments_eq (n : ℕ) : kochSegments n = 4 ^ n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [kochSegments, ih, pow_succ]; ring

theorem koch_length (n : ℕ) : (kochSegments n : ℝ) * (1 / 3 : ℝ) ^ n = (4 / 3 : ℝ) ^ n := by
  rw [kochSegments_eq]; push_cast; rw [← mul_pow]; norm_num

/-- Self-similar curve made of `N` copies scaled by `s`: at resolution `δ = s^n` the length
`N^n s^n` equals `δ^(1-D)` with similarity dimension `D = log N / log (1/s)`. -/
theorem selfsimilar_length (N s : ℝ) (n : ℕ) (hN : 0 < N) (hs : 0 < s) (hs1 : s < 1) :
    N ^ n * s ^ n = (s ^ n) ^ (1 - Real.log N / Real.log (1 / s)) := by
  have hl : Real.log (1 / s) ≠ 0 := by
    rw [one_div, Real.log_inv]; exact neg_ne_zero.mpr (Real.log_neg hs hs1).ne
  have hsn : 0 < s ^ n := pow_pos hs n
  rw [Real.rpow_def_of_pos hsn, Real.log_pow]
  have : (n : ℝ) * Real.log s * (1 - Real.log N / Real.log (1 / s))
      = n * Real.log N + n * Real.log s := by
    rw [one_div, Real.log_inv] at hl ⊢
    have hl' : Real.log s ≠ 0 := fun h => hl (by rw [h, neg_zero])
    field_simp; ring_nf
  rw [this, Real.exp_add, ← Real.log_pow, ← Real.log_pow, Real.exp_log (pow_pos hN n),
    Real.exp_log hsn]

theorem koch_length_rpow (n : ℕ) :
    (4 / 3 : ℝ) ^ n = ((1 / 3 : ℝ) ^ n) ^ (1 - Real.log 4 / Real.log 3) := by
  have := selfsimilar_length 4 (1 / 3) n (by norm_num) (by norm_num) (by norm_num)
  rw [show (1 : ℝ) / (1 / 3) = 3 by norm_num] at this
  rw [← this, ← mul_pow]; norm_num

/-- Small-angle bounds for the pencil half-width: `t ≤ arcsin t ≤ (π/2) t` on `[0,1]`. -/
theorem arcsin_bounds (t : ℝ) (h0 : 0 ≤ t) (h1 : t ≤ 1) :
    t ≤ Real.arcsin t ∧ Real.arcsin t ≤ π / 2 * t := by
  constructor
  · have hA : Real.arcsin t ∈ Set.Icc (0 : ℝ) (π / 2) :=
      ⟨Real.arcsin_nonneg.mpr h0, Real.arcsin_le_pi_div_two t⟩
    have := Real.sin_le hA.1
    rwa [Real.sin_arcsin (by linarith) h1] at this
  · have hx : π / 2 * t ∈ Set.Icc (-(π / 2)) (π / 2) := by
      constructor
      · nlinarith [Real.pi_pos]
      · nlinarith [Real.pi_pos]
    rw [Real.arcsin_le_iff_le_sin ⟨by linarith, h1⟩ hx]
    have := Real.mul_le_sin (by nlinarith [Real.pi_pos] : 0 ≤ π / 2 * t) hx.2
    have hp : 2 / π * (π / 2 * t) = t := by field_simp
    linarith

/-- Packing densities of the point-spheres: square lattice `π/4`, cubic lattice `π/6`,
hexagonal lattice `π/(2√3)` (Lagrange/Thue), FCC `π/(3√2)` (Kepler; Hales). -/
theorem density_square (ε : ℝ) (hε : 0 < ε) : π * ε ^ 2 / (2 * ε) ^ 2 = π / 4 := by
  field_simp; ring

theorem density_cubic (ε : ℝ) (hε : 0 < ε) : 4 / 3 * π * ε ^ 3 / (2 * ε) ^ 3 = π / 6 := by
  field_simp; ring

/-- Hexagonal packing: one disc of radius `ε` per rhombic cell of area `2√3 ε²`. -/
theorem density_hex (ε : ℝ) (hε : 0 < ε) :
    π * ε ^ 2 / (2 * Real.sqrt 3 * ε ^ 2) = π / (2 * Real.sqrt 3) := by
  have : 0 < Real.sqrt 3 := by positivity
  field_simp

/-- FCC packing: four balls of radius `ε` per cubic cell of side `2√2 ε`. -/
theorem density_fcc (ε : ℝ) (hε : 0 < ε) :
    4 * (4 / 3 * π * ε ^ 3) / (2 * Real.sqrt 2 * ε) ^ 3 = π / (3 * Real.sqrt 2) := by
  have h2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have : 0 < Real.sqrt 2 := by positivity
  field_simp
  rw [h2]; norm_num

theorem hex_beats_square : π / 4 < π / (2 * Real.sqrt 3) := by
  have h3 : Real.sqrt 3 < 2 := by
    rw [show (2:ℝ) = Real.sqrt 4 by rw [show (4:ℝ) = 2^2 by norm_num, Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  have : 0 < Real.sqrt 3 := by positivity
  rw [div_lt_div_iff₀ (by norm_num) (by positivity)]
  nlinarith [Real.pi_pos]

theorem fcc_beats_cubic : π / 6 < π / (3 * Real.sqrt 2) := by
  have h2 : Real.sqrt 2 < 2 := by
    rw [show (2:ℝ) = Real.sqrt 4 by rw [show (4:ℝ) = 2^2 by norm_num, Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  have : 0 < Real.sqrt 2 := by positivity
  rw [div_lt_div_iff₀ (by norm_num) (by positivity)]
  nlinarith [Real.pi_pos]

end Fractal

section Continuum
open Real Set MeasureTheory

/-- **Shadow (classical comparison).** The content of the closed lattice box
equals the Lebesgue volume of the continuum box thickened by `ε` in the
sup-norm (the Voronoi-cell gauge). -/
theorem closedBox_volume_shadow {n : ℕ} (ε : ℝ) (a b : Fin n → ℤ) (h : ∀ i, a i ≤ b i)
    (hε : 0 ≤ ε) :
    QE.muN n ε (closedBox a b) =
      (MeasureTheory.volume (Set.Icc (fun i => QE.centre ε (a i) - ε)
        (fun i => QE.centre ε (b i) + ε))).toReal := by
  rw [muN_closedBox ε a b h, Real.volume_Icc_pi, ENNReal.toReal_prod]
  refine Finset.prod_congr rfl fun i _ => ?_
  have : QE.centre ε (a i) ≤ QE.centre ε (b i) := by
    unfold QE.centre
    have : ((a i : ℤ) : ℝ) ≤ b i := by exact_mod_cast h i
    nlinarith
  rw [ENNReal.toReal_ofReal (by linarith)]; ring

theorem pencil_iff (d ε θ : ℝ) (hd : 0 < d) (hε : 0 ≤ ε) (h2 : 2 * ε ≤ d)
    (hθ : θ ∈ Icc (-(π / 2)) (π / 2)) :
    (∃ s : ℝ, |0 - s| ≤ ε ∧ |d * sin θ - s| ≤ ε) ↔ |θ| ≤ arcsin (2 * ε / d) := by
  have core : (∃ s : ℝ, |0 - s| ≤ ε ∧ |d * sin θ - s| ≤ ε) ↔ |d * sin θ - 0| ≤ ε + ε := by
    constructor
    · rintro ⟨s, h1, h2⟩
      calc |d * sin θ - 0| = |(d * sin θ - s) - (0 - s)| := by ring_nf
        _ ≤ |d * sin θ - s| + |0 - s| := abs_sub _ _
        _ ≤ ε + ε := by linarith
    · intro h
      refine ⟨max (-ε) (min ε (d * sin θ)), ?_, ?_⟩
      · rw [abs_le]; constructor
        · have := min_le_left ε (d * sin θ); have := le_max_left (-ε) (min ε (d * sin θ))
          rcases max_cases (-ε) (min ε (d * sin θ)) with ⟨he, _⟩ | ⟨he, _⟩ <;> rw [he] <;> linarith
        · have := le_max_left (-ε) (min ε (d * sin θ)); linarith
      · rcases abs_le.mp h with ⟨hl, hu⟩
        rw [abs_le]; constructor
        · rcases max_cases (-ε) (min ε (d * sin θ)) with ⟨he, _⟩ | ⟨he, _⟩ <;> rw [he] <;>
          rcases min_cases ε (d * sin θ) with ⟨he', _⟩ | ⟨he', _⟩ <;> (try rw [he']) <;> linarith
        · rcases max_cases (-ε) (min ε (d * sin θ)) with ⟨he, _⟩ | ⟨he, _⟩ <;> rw [he] <;>
          rcases min_cases ε (d * sin θ) with ⟨he', _⟩ | ⟨he', _⟩ <;> (try rw [he']) <;> linarith
  rw [core, sub_zero, abs_mul, abs_of_pos hd]
  have ht : 2 * ε / d ∈ Icc (-1 : ℝ) 1 := by
    constructor
    · have : 0 ≤ 2 * ε / d := by positivity
      linarith
    · rw [div_le_one hd]; exact h2
  have hθ' : -θ ∈ Icc (-(π / 2)) (π / 2) := ⟨by linarith [hθ.2], by linarith [hθ.1]⟩
  rw [abs_le', le_arcsin_iff_sin_le hθ ht, le_arcsin_iff_sin_le hθ' ht, sin_neg,
    le_div_iff₀ hd, le_div_iff₀ hd]
  constructor
  · intro h
    have h1 := le_abs_self (sin θ); have h2 := neg_abs_le (sin θ)
    constructor <;> nlinarith
  · rintro ⟨h1, h2⟩
    rcases abs_cases (sin θ) with ⟨he, _⟩ | ⟨he, _⟩ <;> rw [he] <;> nlinarith

/-- **Shadow (classical comparison).** Lebesgue area of the intersection of two
continuum strips: `(2ε)²/|ad - bc|`.  The granular count is `strip_count`. -/
theorem strip_volume (a b c d ε : ℝ) (hε : 0 ≤ ε) (hdet : a * d - b * c ≠ 0) :
    volume {x : Fin 2 → ℝ | |a * x 0 + b * x 1| ≤ ε ∧ |c * x 0 + d * x 1| ≤ ε} =
      ENNReal.ofReal ((2 * ε) ^ 2 / |a * d - b * c|) := by
  set M : Matrix (Fin 2) (Fin 2) ℝ := !![a, b; c, d]
  have hdetM : LinearMap.det (Matrix.toLin' M) ≠ 0 := by
    rw [LinearMap.det_toLin', Matrix.det_fin_two_of]; exact hdet
  have hS : {x : Fin 2 → ℝ | |a * x 0 + b * x 1| ≤ ε ∧ |c * x 0 + d * x 1| ≤ ε} =
      (Matrix.toLin' M) ⁻¹' (Icc (fun _ => -ε) (fun _ => ε)) := by
    ext x
    simp only [ mem_preimage, mem_Icc, Matrix.toLin'_apply, Pi.le_def,
      Fin.forall_fin_two, M, Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.of_apply,
      Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val',
      Matrix.cons_val_fin_one, abs_le]
    simp only [Set.mem_ofPred_eq]; tauto
  rw [hS, MeasureTheory.Measure.addHaar_preimage_linearMap _ hdetM, Real.volume_Icc_pi,
    LinearMap.det_toLin', Matrix.det_fin_two_of, Fin.prod_univ_two,
    ← ENNReal.ofReal_mul (by linarith : (0:ℝ) ≤ ε - -ε), ← ENNReal.ofReal_mul (abs_nonneg _)]
  congr 1
  rw [abs_inv]; ring


/-- Two touching points (`d = 2ε`): every direction admits a common incident line. -/
theorem touching_pencil_all (ε θ : ℝ) (hε : 0 < ε) (hθ : θ ∈ Icc (-(π / 2)) (π / 2)) :
    ∃ s : ℝ, |0 - s| ≤ ε ∧ |2 * ε * sin θ - s| ≤ ε := by
  rw [pencil_iff (2 * ε) ε θ (by linarith) hε.le le_rfl hθ,
    div_self (by linarith : (2 * ε) ≠ 0), arcsin_one, abs_le]
  exact ⟨hθ.1, hθ.2⟩

/-- **Shadow (classical comparison).** Strip intersection in angle form: two thick lines (strips of width `2ε`) whose unit
normals make the angle `β - α` meet in a parallelogram of area `(2ε)² / |sin(β - α)|`. -/
theorem strip_volume_angle (α β ε : ℝ) (hε : 0 ≤ ε) (hθ : sin (β - α) ≠ 0) :
    volume {x : Fin 2 → ℝ | |cos α * x 0 + sin α * x 1| ≤ ε ∧
        |cos β * x 0 + sin β * x 1| ≤ ε} =
      ENNReal.ofReal ((2 * ε) ^ 2 / |sin (β - α)|) := by
  have e : cos α * sin β - sin α * cos β = sin (β - α) := by rw [sin_sub]; ring
  rw [strip_volume _ _ _ _ ε hε (by rw [e]; exact hθ), e]

noncomputable section

abbrev E2 := EuclideanSpace ℝ (Fin 2)

/-- Lattice points of `ℤ²` in the closed disc of radius `R` (lattice units). -/
def gaussSet (R : ℝ) : Finset (Fin 2 → ℤ) :=
  (Fintype.piFinset fun _ : Fin 2 => Finset.Icc (-⌈R⌉) ⌈R⌉).filter
    (fun k => ((k 0 : ℝ)) ^ 2 + ((k 1 : ℝ)) ^ 2 ≤ R ^ 2)

def latC (k : Fin 2 → ℤ) : E2 := WithLp.toLp 2 (fun i => (k i : ℝ))

/-- Voronoi cell (half-open unit square) of the lattice point `k`. -/
def vcell (k : Fin 2 → ℤ) : Set E2 :=
  (WithLp.ofLp) ⁻¹' (Set.pi univ fun i => Ico ((k i : ℝ) - 1 / 2) ((k i : ℝ) + 1 / 2))

lemma vcell_measurable (k : Fin 2 → ℤ) : MeasurableSet (vcell k) := by
  unfold vcell
  exact (MeasurableSet.univ_pi fun i => measurableSet_Ico).preimage (by fun_prop)

lemma vcell_volume (k : Fin 2 → ℤ) : volume (vcell k) = 1 := by
  unfold vcell
  rw [(PiLp.volume_preserving_ofLp (Fin 2)).measure_preimage
    (MeasurableSet.univ_pi fun i => measurableSet_Ico).nullMeasurableSet, Real.volume_pi_Ico]
  simp only [add_sub_sub_cancel]; norm_num

lemma mem_vcell_iff (k : Fin 2 → ℤ) (x : E2) :
    x ∈ vcell k ↔ ∀ i, (k i : ℝ) - 1 / 2 ≤ x i ∧ x i < (k i : ℝ) + 1 / 2 := by
  simp [vcell, Set.mem_pi]

lemma vcell_eq_floor {k : Fin 2 → ℤ} {x : E2} (hx : x ∈ vcell k) (i : Fin 2) :
    k i = ⌊x i + 1 / 2⌋ := by
  rw [mem_vcell_iff] at hx
  rw [eq_comm, Int.floor_eq_iff]; constructor <;> linarith [(hx i).1, (hx i).2]

lemma vcell_disjoint : (Set.univ : Set (Fin 2 → ℤ)).PairwiseDisjoint vcell := by
  intro k _ l _ hkl
  rw [Function.onFun, Set.disjoint_left]
  intro x hk hl
  apply hkl; funext i; rw [vcell_eq_floor hk i, vcell_eq_floor hl i]

lemma norm_sub_latC_le {k : Fin 2 → ℤ} {x : E2} (hx : x ∈ vcell k) :
    ‖x - latC k‖ ≤ Real.sqrt 2 / 2 := by
  rw [mem_vcell_iff] at hx
  have hsq : ‖x - latC k‖ ^ 2 ≤ (Real.sqrt 2 / 2) ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two, div_pow, Real.sq_sqrt (by norm_num)]
    simp only [latC, PiLp.sub_apply]
    have h0 := hx 0; have h1 := hx 1
    nlinarith [h0.1, h0.2, h1.1, h1.2]
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).mp hsq

lemma norm_latC_sq (k : Fin 2 → ℤ) : ‖latC k‖ ^ 2 = (k 0 : ℝ) ^ 2 + (k 1 : ℝ) ^ 2 := by
  rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two]; rfl

/-- **Shadow (classical comparison).** Gauss's upper bound: `N(R) ≤ π (R + √2/2)²`
(the disc area is the Lebesgue target). -/
theorem gauss_upper (R : ℝ) (hR : 0 ≤ R) :
    ((gaussSet R).card : ℝ) ≤ Real.pi * (R + Real.sqrt 2 / 2) ^ 2 := by
  have hsub : (⋃ k ∈ gaussSet R, vcell k) ⊆ Metric.closedBall (0 : E2) (R + Real.sqrt 2 / 2) := by
    intro x hx
    simp only [mem_iUnion] at hx
    obtain ⟨k, hk, hxk⟩ := hx
    rw [Metric.mem_closedBall, dist_zero_right]
    have hk' : ‖latC k‖ ≤ R := by
      have : ‖latC k‖ ^ 2 ≤ R ^ 2 := by
        rw [norm_latC_sq]; exact (Finset.mem_filter.mp hk).2
      exact (pow_le_pow_iff_left₀ (norm_nonneg _) hR two_ne_zero).mp this
    calc ‖x‖ = ‖(x - latC k) + latC k‖ := by rw [sub_add_cancel]
      _ ≤ ‖x - latC k‖ + ‖latC k‖ := norm_add_le _ _
      _ ≤ R + Real.sqrt 2 / 2 := by linarith [norm_sub_latC_le hxk]
  have hvol : volume (⋃ k ∈ gaussSet R, vcell k) = (gaussSet R).card := by
    rw [measure_biUnion_finset (vcell_disjoint.subset (subset_univ _))
      (fun k _ => vcell_measurable k)]
    simp [vcell_volume]
  have := measure_mono (μ := volume) hsub
  rw [hvol, EuclideanSpace.volume_closedBall_fin_two, ← ENNReal.ofReal_pow (by positivity),
    ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_natCast,
    ENNReal.ofReal_le_ofReal_iff (by positivity)] at this
  linarith

/-- **Shadow (classical comparison).** Gauss's lower bound: `π (R - √2/2)² ≤ N(R)`
for `R ≥ √2/2`. -/
theorem gauss_lower (R : ℝ) (hR : Real.sqrt 2 / 2 ≤ R) :
    Real.pi * (R - Real.sqrt 2 / 2) ^ 2 ≤ ((gaussSet R).card : ℝ) := by
  have hR0 : 0 ≤ R := le_trans (by positivity) hR
  have hsub : Metric.ball (0 : E2) (R - Real.sqrt 2 / 2) ⊆ (⋃ k ∈ gaussSet R, vcell k) := by
    intro x hx
    rw [Metric.mem_ball, dist_zero_right] at hx
    set k : Fin 2 → ℤ := fun i => ⌊x i + 1 / 2⌋
    have hxk : x ∈ vcell k := by
      rw [mem_vcell_iff]; intro i
      constructor
      · have := Int.floor_le (x i + 1 / 2); simp only [k]; linarith
      · have := Int.lt_floor_add_one (x i + 1 / 2); simp only [k]; linarith
    have hn : ‖latC k‖ ≤ R := by
      calc ‖latC k‖ = ‖x - (x - latC k)‖ := by rw [sub_sub_cancel]
        _ ≤ ‖x‖ + ‖x - latC k‖ := norm_sub_le _ _
        _ ≤ R := by linarith [norm_sub_latC_le hxk]
    have hn2 : (k 0 : ℝ) ^ 2 + (k 1 : ℝ) ^ 2 ≤ R ^ 2 := by
      rw [← norm_latC_sq]; exact pow_le_pow_left₀ (norm_nonneg _) hn 2
    simp only [mem_iUnion]
    refine ⟨k, ?_, hxk⟩
    rw [gaussSet, Finset.mem_filter, Fintype.mem_piFinset]
    refine ⟨fun i => ?_, hn2⟩
    have hi : ((k i : ℤ) : ℝ) ^ 2 ≤ R ^ 2 := by
      fin_cases i <;> simp <;> nlinarith [sq_nonneg ((k 0 : ℤ) : ℝ), sq_nonneg ((k 1 : ℤ) : ℝ)]
    have habs : |((k i : ℤ) : ℝ)| ≤ R := abs_le_of_sq_le_sq' hi hR0 |> abs_le.mpr
    have hc := Int.le_ceil R
    rw [Finset.mem_Icc]
    constructor
    · have : -R ≤ ((k i : ℤ) : ℝ) := (abs_le.mp habs).1
      have : ((-⌈R⌉ : ℤ) : ℝ) ≤ ((k i : ℤ) : ℝ) := by push_cast; linarith
      exact_mod_cast this
    · have : ((k i : ℤ) : ℝ) ≤ R := (abs_le.mp habs).2
      have : ((k i : ℤ) : ℝ) ≤ ((⌈R⌉ : ℤ) : ℝ) := by linarith
      exact_mod_cast this
  have hvol : volume (⋃ k ∈ gaussSet R, vcell k) = (gaussSet R).card := by
    rw [measure_biUnion_finset (vcell_disjoint.subset (subset_univ _))
      (fun k _ => vcell_measurable k)]
    simp [vcell_volume]
  have := measure_mono (μ := volume) hsub
  rw [hvol, EuclideanSpace.volume_ball_fin_two, ← ENNReal.ofReal_pow (by linarith),
    ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_natCast,
    ENNReal.ofReal_le_ofReal_iff (by positivity)] at this
  linarith

/-- **Shadow (classical comparison).** The granular estimate of `π` from a disc of
radius `R` granules:
`|N(R)/R² - π| ≤ π (√2/R + 1/(2R²))`. -/
theorem pi_eps_error (R : ℝ) (hR : Real.sqrt 2 / 2 ≤ R) :
    |((gaussSet R).card : ℝ) / R ^ 2 - Real.pi| ≤
      Real.pi * (Real.sqrt 2 / R + 1 / (2 * R ^ 2)) := by
  have hR0 : 0 < R := lt_of_lt_of_le (by positivity) hR
  have hu := gauss_upper R hR0.le
  have hl := gauss_lower R hR
  have h2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hpi := Real.pi_pos
  have hs : 0 < Real.sqrt 2 := by positivity
  have hR2 : 0 < R ^ 2 := by positivity
  set N : ℝ := ((gaussSet R).card : ℝ)
  have hd : |N - Real.pi * R ^ 2| ≤ Real.pi * (Real.sqrt 2 * R + 1 / 2) := by
    rw [abs_le]; constructor <;> nlinarith
  have e1 : N / R ^ 2 - Real.pi = (N - Real.pi * R ^ 2) / R ^ 2 := by field_simp
  have e2 : Real.pi * (Real.sqrt 2 / R + 1 / (2 * R ^ 2)) =
      Real.pi * (Real.sqrt 2 * R + 1 / 2) / R ^ 2 := by field_simp
  rw [e1, e2, abs_div, abs_of_pos hR2]
  exact div_le_div_of_nonneg_right hd hR2.le


/-! ### Gauss's argument between two granulations (Lebesgue-free) -/

lemma mem_gaussSet_iff {R : ℝ} (hR : 0 ≤ R) (k : Fin 2 → ℤ) :
    k ∈ gaussSet R ↔ ((k 0 : ℤ) : ℝ) ^ 2 + ((k 1 : ℤ) : ℝ) ^ 2 ≤ R ^ 2 := by
  constructor
  · intro hk; exact (Finset.mem_filter.mp hk).2
  · intro hn2
    rw [gaussSet, Finset.mem_filter, Fintype.mem_piFinset]
    refine ⟨fun i => ?_, hn2⟩
    have hi : ((k i : ℤ) : ℝ) ^ 2 ≤ R ^ 2 := by
      fin_cases i <;> simp <;> nlinarith [sq_nonneg ((k 0 : ℤ) : ℝ), sq_nonneg ((k 1 : ℤ) : ℝ)]
    have habs : |((k i : ℤ) : ℝ)| ≤ R := abs_le_of_sq_le_sq' hi hR |> abs_le.mpr
    have hc := Int.le_ceil R
    rw [Finset.mem_Icc]
    constructor
    · have : -R ≤ ((k i : ℤ) : ℝ) := (abs_le.mp habs).1
      have : ((-⌈R⌉ : ℤ) : ℝ) ≤ ((k i : ℤ) : ℝ) := by push_cast; linarith
      exact_mod_cast this
    · have : ((k i : ℤ) : ℝ) ≤ R := (abs_le.mp habs).2
      have : ((k i : ℤ) : ℝ) ≤ ((⌈R⌉ : ℤ) : ℝ) := by linarith
      exact_mod_cast this

/-- Triangle inequality in the plane, in squared form (Cauchy–Schwarz). -/
lemma shift_bound (k0 k1 e0 e1 r t : ℝ) (hr : 0 ≤ r) (ht : 0 ≤ t)
    (hk : k0 ^ 2 + k1 ^ 2 ≤ r ^ 2) (he : e0 ^ 2 + e1 ^ 2 ≤ t ^ 2) :
    (k0 + e0) ^ 2 + (k1 + e1) ^ 2 ≤ (r + t) ^ 2 := by
  have hcs : (k0 * e0 + k1 * e1) ^ 2 ≤ (r * t) ^ 2 := by
    have h1 : (k0 * e0 + k1 * e1) ^ 2 ≤ (k0 ^ 2 + k1 ^ 2) * (e0 ^ 2 + e1 ^ 2) := by
      nlinarith [sq_nonneg (k0 * e1 - k1 * e0)]
    have h2 : (k0 ^ 2 + k1 ^ 2) * (e0 ^ 2 + e1 ^ 2) ≤ r ^ 2 * t ^ 2 :=
      mul_le_mul hk he (by positivity) (by positivity)
    nlinarith
  have hdot : k0 * e0 + k1 * e1 ≤ r * t := (abs_le_of_sq_le_sq' hcs (by positivity)).2
  nlinarith

/-- **Gauss's sandwich between two granulations** (granular, Lebesgue-free).
Refine the unit lattice by an integer factor `m`.  Each coarse cell owns
exactly `m²` fine points, all within `√2/2` (coarse units) of its centre;
hence the fine lattice points of the disc of radius `m(R + √2/2)` (fine
units) are at least `m² N(R)`, and those of the disc of radius
`m(R - √2/2)` at most `m² N(R)`.  Dividing by `m²` and letting the fine
lattice become ultrafine is where the area `π R²` enters, as a shadow. -/
theorem gauss_refine (R : ℝ) (hR : 0 ≤ R) (m : ℕ) (hm : 0 < m) :
    m ^ 2 * (gaussSet R).card ≤ (gaussSet (m * (R + Real.sqrt 2 / 2))).card ∧
    (Real.sqrt 2 / 2 ≤ R →
      (gaussSet (m * (R - Real.sqrt 2 / 2))).card ≤ m ^ 2 * (gaussSet R).card) := by
  set c : ℤ := ((m / 2 : ℕ) : ℤ) with hc
  have hmZ : (0 : ℤ) < m := by exact_mod_cast hm
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hs2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hs0 : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  set Ao : Finset (Fin 2 → ℤ) := Fintype.piFinset (fun _ : Fin 2 => Finset.Ico (0 : ℤ) m)
    with hAo
  have hAo_card : Ao.card = m ^ 2 := by
    rw [hAo, Fintype.card_piFinset]; simp
  have hoff : ∀ a : ℤ, 0 ≤ a → a < m → ((a - c : ℤ) : ℝ) ^ 2 ≤ (m : ℝ) ^ 2 / 4 := by
    intro a h0 h1
    have h2 : -(m : ℤ) ≤ 2 * (a - c) ∧ 2 * (a - c) ≤ m := by
      rw [hc]; constructor <;> omega
    have h3 : -(m : ℝ) ≤ 2 * ((a - c : ℤ) : ℝ) := by
      have := h2.1; exact_mod_cast this
    have h4 : 2 * ((a - c : ℤ) : ℝ) ≤ m := by
      have := h2.2; exact_mod_cast this
    nlinarith
  have hoff2 : ∀ e0 e1 : ℝ, e0 ^ 2 ≤ (m : ℝ) ^ 2 / 4 → e1 ^ 2 ≤ (m : ℝ) ^ 2 / 4 →
      e0 ^ 2 + e1 ^ 2 ≤ ((m : ℝ) * (Real.sqrt 2 / 2)) ^ 2 := by
    intro e0 e1 h0 h1; rw [mul_pow, div_pow, hs2]; linarith
  have hAo_mem : ∀ a ∈ Ao, ∀ i, 0 ≤ a i ∧ a i < m := by
    intro a ha i
    have := Fintype.mem_piFinset.mp ha i
    simpa [Finset.mem_Ico] using this
  constructor
  · have hR' : 0 ≤ (m : ℝ) * (R + Real.sqrt 2 / 2) := by positivity
    rw [show m ^ 2 * (gaussSet R).card = (gaussSet R).card * Ao.card by rw [hAo_card, mul_comm],
      ← Finset.card_product]
    refine Finset.card_le_card_of_injOn (fun p => fun i => (m : ℤ) * p.1 i + p.2 i - c) ?_ ?_
    · intro p hp
      obtain ⟨hk, ha⟩ := Finset.mem_product.mp (Finset.mem_coe.mp hp)
      apply Finset.mem_coe.mpr
      rw [mem_gaussSet_iff hR']
      have hk2 := (mem_gaussSet_iff hR p.1).mp hk
      have e0 := hoff _ (hAo_mem _ ha 0).1 (hAo_mem _ ha 0).2
      have e1 := hoff _ (hAo_mem _ ha 1).1 (hAo_mem _ ha 1).2
      have hkm : ((m : ℝ) * (p.1 0 : ℝ)) ^ 2 + ((m : ℝ) * (p.1 1 : ℝ)) ^ 2 ≤ ((m : ℝ) * R) ^ 2 := by
        rw [mul_pow, mul_pow, mul_pow, ← mul_add]
        exact mul_le_mul_of_nonneg_left hk2 (by positivity)
      have key := shift_bound _ _ _ _ _ _ (by positivity) (by positivity) hkm (hoff2 _ _ e0 e1)
      show ((((m : ℤ) * p.1 0 + p.2 0 - c : ℤ)) : ℝ) ^ 2
          + (((m : ℤ) * p.1 1 + p.2 1 - c : ℤ) : ℝ) ^ 2 ≤ ((m : ℝ) * (R + Real.sqrt 2 / 2)) ^ 2
      convert key using 1 <;> push_cast <;> ring
    · intro p hp q hq hpq
      have hpa := hAo_mem _ (Finset.mem_product.mp (Finset.mem_coe.mp hp)).2
      have hqa := hAo_mem _ (Finset.mem_product.mp (Finset.mem_coe.mp hq)).2
      have hcoord : ∀ i, p.1 i = q.1 i ∧ p.2 i = q.2 i := by
        intro i
        have h := congrFun hpq i
        simp only at h
        have e1 := (Int.ediv_emod_unique hmZ).mpr
          ⟨(show p.2 i + m * p.1 i = m * p.1 i + p.2 i by ring), (hpa i).1, (hpa i).2⟩
        have e2 := (Int.ediv_emod_unique hmZ).mpr
          ⟨(show q.2 i + m * q.1 i = m * p.1 i + p.2 i by linarith), (hqa i).1, (hqa i).2⟩
        exact ⟨e1.1.symm.trans e2.1, e1.2.symm.trans e2.2⟩
      exact Prod.ext (funext fun i => (hcoord i).1) (funext fun i => (hcoord i).2)
  · intro hRs
    have hR1 : 0 ≤ (m : ℝ) * (R - Real.sqrt 2 / 2) := by
      have : 0 ≤ R - Real.sqrt 2 / 2 := by linarith
      positivity
    rw [show m ^ 2 * (gaussSet R).card = (gaussSet R).card * Ao.card by rw [hAo_card, mul_comm],
      ← Finset.card_product]
    refine Finset.card_le_card_of_injOn
      (fun j => ((fun i => (j i + c) / (m : ℤ)), (fun i => (j i + c) % (m : ℤ)))) ?_ ?_
    · intro j hj
      have hj2 := (mem_gaussSet_iff hR1 j).mp (Finset.mem_coe.mp hj)
      apply Finset.mem_coe.mpr
      rw [Finset.mem_product]
      have ha : ∀ i, 0 ≤ (j i + c) % (m : ℤ) ∧ (j i + c) % (m : ℤ) < m :=
        fun i => ⟨Int.emod_nonneg _ hmZ.ne', Int.emod_lt_of_pos _ hmZ⟩
      refine ⟨?_, Fintype.mem_piFinset.mpr fun i => Finset.mem_Ico.mpr (ha i)⟩
      rw [mem_gaussSet_iff hR]
      have hdec : ∀ i, ((m : ℝ) * (((j i + c) / (m : ℤ) : ℤ) : ℝ))
          = (j i : ℝ) + -((((j i + c) % (m : ℤ)) - c : ℤ) : ℝ) := by
        intro i
        have := Int.emod_add_mul_ediv (j i + c) m
        have h' : (((m : ℤ) * ((j i + c) / (m : ℤ)) : ℤ) : ℝ)
            = (((j i : ℤ) - (((j i + c) % (m : ℤ)) - c) : ℤ) : ℝ) := by
          congr 1; linarith
        push_cast at h' ⊢; linarith
      have e0 := hoff _ (ha 0).1 (ha 0).2
      have e1 := hoff _ (ha 1).1 (ha 1).2
      have he : (-((((j 0 + c) % (m : ℤ)) - c : ℤ) : ℝ)) ^ 2
          + (-((((j 1 + c) % (m : ℤ)) - c : ℤ) : ℝ)) ^ 2
          ≤ ((m : ℝ) * (Real.sqrt 2 / 2)) ^ 2 := by
        rw [neg_sq, neg_sq]; exact hoff2 _ _ e0 e1
      have key := shift_bound _ _ _ _ _ _ hR1 (by positivity) hj2 he
      rw [← hdec 0, ← hdec 1, show (m : ℝ) * (R - Real.sqrt 2 / 2) + (m : ℝ) * (Real.sqrt 2 / 2)
        = (m : ℝ) * R by ring, mul_pow, mul_pow, mul_pow, ← mul_add] at key
      exact le_of_mul_le_mul_left key (by positivity)
    · intro j _ j' _ h
      have h1 := congrArg Prod.fst h
      have h2 := congrArg Prod.snd h
      funext i
      have a1 := congrFun h1 i
      have a2 := congrFun h2 i
      simp only at a1 a2
      have d1 := Int.emod_add_mul_ediv (j i + c) m
      have d2 := Int.emod_add_mul_ediv (j' i + c) m
      rw [a1, a2] at d1
      linarith

end

end Continuum

section Examples

/-- Thick tangency: the thick line `|y| ≤ ε` and the thick circle of radius `R` centred at
`(0,R)` overlap exactly above the contact segment `x² ≤ 4Rε` (length `4√(Rε)`). -/
theorem tangent_contact_iff {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    (R ε x : K) (hε : 0 ≤ ε) (hR : ε ≤ R) :
    (∃ y : K, |y| ≤ ε ∧ (R - ε) ^ 2 ≤ x ^ 2 + (y - R) ^ 2 ∧ x ^ 2 + (y - R) ^ 2 ≤ (R + ε) ^ 2)
      ↔ x ^ 2 ≤ 4 * R * ε := by
  constructor
  · rintro ⟨y, hy, -, h2⟩
    rcases abs_le.mp hy with ⟨h1, h3⟩
    nlinarith
  · intro h
    refine ⟨ε, by rw [abs_of_nonneg hε], ?_, ?_⟩ <;> nlinarith [sq_nonneg x]

/-- Congruent lattice squares of side 5: axis-parallel versus edge vector `(4,3)`. -/
theorem square_axis_count :
    ((Finset.Icc (0:ℤ) 5 ×ˢ Finset.Icc (0:ℤ) 5)).card = 36 := by decide

theorem square_tilted_count :
    ((Finset.Icc (-3:ℤ) 4 ×ˢ Finset.Icc (0:ℤ) 7).filter (fun p : ℤ × ℤ =>
      0 ≤ 4 * p.1 + 3 * p.2 ∧ 4 * p.1 + 3 * p.2 ≤ 25 ∧
      0 ≤ -3 * p.1 + 4 * p.2 ∧ -3 * p.1 + 4 * p.2 ≤ 25)).card = 28 := by decide

theorem square_tilted_interior :
    ((Finset.Icc (-3:ℤ) 4 ×ˢ Finset.Icc (0:ℤ) 7).filter (fun p : ℤ × ℤ =>
      0 < 4 * p.1 + 3 * p.2 ∧ 4 * p.1 + 3 * p.2 < 25 ∧
      0 < -3 * p.1 + 4 * p.2 ∧ -3 * p.1 + 4 * p.2 < 25)).card = 24 := by decide

theorem square_axis_interior :
    ((Finset.Ioo (0:ℤ) 5 ×ˢ Finset.Ioo (0:ℤ) 5)).card = 16 := by decide

/-- Lattice points on the circle of radius 5: `r₂(25) = 12`. -/
theorem circle5_count :
    ((Finset.Icc (-5:ℤ) 5 ×ˢ Finset.Icc (-5:ℤ) 5).filter
      (fun p : ℤ × ℤ => p.1 ^ 2 + p.2 ^ 2 = 25)).card = 12 := by decide

/-- The closed lattice right triangle with legs 6 and 4 contains 19 lattice points. -/
theorem triangle64_count :
    (((Finset.range 7) ×ˢ (Finset.range 5)).filter
      (fun p : ℕ × ℕ => 4 * p.1 + 6 * p.2 ≤ 6 * 4)).card = 19 := by decide

end Examples

end QE.Geometry
