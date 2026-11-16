-- SPDX-License-Identifier: MIT
-- Copyright 2026 Metere Industries, Inc. Author: Alfredo Metere.
-- Quasi-Euclidean Granular Geometry. Any derivative work must carry this notice:
--   This work is derivative of the Quasi-Euclidean Granular Geometry book
--   authored by Alfredo Metere. Copyright 2026 Metere Industries, Inc.
--   All rights reserved
-- See LICENSE.md and NOTICE.

import QuasiEuclidean.Basic

/-!
# Chapter 10: Granular topology

All statements are exact finitary facts about lattice indices (`ℤ` or `ℕ`),
valid for every resolution `ε > 0`; the hyperfinite case is an instance.

* discrete intermediate value theorem (constructive, exact);
* one-dimensional Sperner lemma (parity of label changes);
* two-dimensional Sperner lemma on the triangulated granular square,
  via an exact discrete Stokes identity;
* discrete Brouwer theorem (approximate fixed point at resolution `δ`);
* Euler characteristic of cubical complexes: grid rectangle `= 1`,
  invariance under elementary collapses, inclusion–exclusion;
* the Khalimsky topology on `ℤ` (odd points open, even points closed);
* connectedness of lattice intervals in the adjacency graph.
-/

namespace QE.Topology

open Finset _root_.Topology

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-! ## Discrete intermediate value theorem -/

/-- **Discrete IVT.** If `f 0 ≤ 0 < f n` there is an index `k < n` with
`f k ≤ 0 < f (k+1)`: the sign changes between two adjacent lattice points.
The witness is the first index where `f` becomes positive (a finite search). -/
theorem discrete_ivt (f : ℕ → K) (n : ℕ) (h0 : f 0 ≤ 0) (hn : 0 < f n) :
    ∃ k < n, f k ≤ 0 ∧ 0 < f (k + 1) := by
  classical
  have hex : ∃ m, 0 < f m := ⟨n, hn⟩
  set m := Nat.find hex with hm
  have hmpos : 0 < f m := Nat.find_spec hex
  have hmn : m ≤ n := Nat.find_min' hex hn
  have hm0 : m ≠ 0 := by
    intro h; rw [h] at hmpos; exact absurd h0 (not_le.mpr hmpos)
  obtain ⟨k, hk⟩ : ∃ k, m = k + 1 := Nat.exists_eq_succ_of_ne_zero hm0
  refine ⟨k, by omega, ?_, hk ▸ hmpos⟩
  have := Nat.find_min hex (show k < Nat.find hex by omega)
  exact not_lt.mp this

/-- Discrete IVT on a lattice interval `[a, a+n]` of `ℤ`. -/
theorem discrete_ivt_int (f : ℤ → K) (a : ℤ) (n : ℕ) (ha : f a ≤ 0)
    (hb : 0 < f (a + n)) :
    ∃ k : ℤ, a ≤ k ∧ k < a + n ∧ f k ≤ 0 ∧ 0 < f (k + 1) := by
  obtain ⟨k, hk, h1, h2⟩ := discrete_ivt (fun j : ℕ => f (a + j)) n (by simpa using ha) hb
  refine ⟨a + k, by omega, by omega, h1, ?_⟩
  simpa [add_assoc] using h2

/-- **Approximate root.** If the jumps of `f` between adjacent points are at
most `δ` and `f 0 ≤ c < f n`, some lattice point has `|f k - c| ≤ δ`. -/
theorem discrete_ivt_approx (f : ℕ → K) (n : ℕ) (c δ : K)
    (hjump : ∀ k < n, |f (k + 1) - f k| ≤ δ) (h0 : f 0 ≤ c) (hn : c < f n) :
    ∃ k < n, |f k - c| ≤ δ := by
  obtain ⟨k, hk, h1, h2⟩ := discrete_ivt (fun j => f j - c) n (by simpa using h0)
    (by simpa using hn)
  refine ⟨k, hk, ?_⟩
  have hj := hjump k hk
  simp only [sub_nonpos, sub_pos] at h1 h2
  rw [abs_le] at hj ⊢
  constructor <;> linarith [hj.1, hj.2]

/-- Jumps bounded by `δ` between neighbours give the chain bound
`|f j - f i| ≤ δ (j - i)`: the finitary content of S-continuity. -/
theorem chain_bound (f : ℕ → K) (δ : K) (hjump : ∀ k, |f (k + 1) - f k| ≤ δ)
    (i m : ℕ) : |f (i + m) - f i| ≤ δ * m := by
  induction m with
  | zero => simp
  | succ m ih =>
    have h := hjump (i + m)
    calc |f (i + (m + 1)) - f i|
        = |(f (i + m + 1) - f (i + m)) + (f (i + m) - f i)| := by
          rw [← add_assoc]; ring_nf
      _ ≤ |f (i + m + 1) - f (i + m)| + |f (i + m) - f i| := abs_add_le _ _
      _ ≤ δ + δ * m := add_le_add h ih
      _ = δ * ((m + 1 : ℕ) : K) := by push_cast; ring

/-! ## One-dimensional Sperner lemma -/

/-- Number of "doors" (adjacent pairs with different labels) in `0, …, n`. -/
def doors (L : ℕ → Bool) (n : ℕ) : ℕ :=
  ((range n).filter (fun k => L k ≠ L (k + 1))).card

/-- The parity of the number of label changes is decided by the endpoints. -/
theorem doors_mod_two (L : ℕ → Bool) (n : ℕ) :
    doors L n % 2 = if L 0 = L n then 0 else 1 := by
  induction n with
  | zero => simp [doors]
  | succ n ih =>
    unfold doors at ih ⊢
    rw [range_add_one, filter_insert]
    by_cases hc : L n ≠ L (n + 1)
    · simp only [hc, ite_true, ne_eq, not_false_eq_true]
      rw [card_insert_of_notMem (by simp)]
      rw [Nat.add_mod, ih]
      cases h0 : L 0 <;> cases h1 : L n <;> cases h2 : L (n + 1) <;> simp_all
    · simp only [hc, ite_false]
      rw [ih]
      have hc' : L n = L (n + 1) := by simpa using hc
      rw [hc']

/-- **Sperner's lemma in dimension one.** If the left end is labelled `false`
and the right end `true`, the number of fully labelled edges is odd. -/
theorem sperner_1d (L : ℕ → Bool) (n : ℕ) (h0 : L 0 = false) (hn : L n = true) :
    Odd (doors L n) := by
  have := doors_mod_two L n
  rw [h0, hn] at this
  simp at this
  exact Nat.odd_iff.mpr this

/-! ## Two-dimensional Sperner lemma on the granular square -/

/-- Oriented door weight: `+1` for an edge labelled `0 → 1`, `-1` for
`1 → 0`, `0` otherwise. -/
def w (a b : Fin 3) : ℤ :=
  if a = 0 ∧ b = 1 then 1 else if a = 1 ∧ b = 0 then -1 else 0

/-- Circulation of the door weight around an oriented triangle. -/
def circ (x y z : Fin 3) : ℤ := w x y + w y z + w z x

/-- A triangle is fully labelled when its three labels are distinct. -/
def full (x y z : Fin 3) : Prop := x ≠ y ∧ y ≠ z ∧ x ≠ z

instance (x y z : Fin 3) : Decidable (full x y z) := by unfold full; infer_instance

theorem w_antisymm : ∀ a b : Fin 3, w a b = - w b a := by decide

/-- The circulation is odd exactly on fully labelled triangles. -/
theorem circ_parity : ∀ x y z : Fin 3,
    (circ x y z - if full x y z then 1 else 0) % 2 = 0 := by decide

/-- The two triangles of the granular square with lower-left corner `(i,j)`,
`T₀ = ((i,j),(i+1,j),(i+1,j+1))` and `T₁ = ((i,j),(i+1,j+1),(i,j+1))`. -/
def tri (L : ℕ → ℕ → Fin 3) (i j : ℕ) : Bool → Fin 3 × Fin 3 × Fin 3
  | false => (L i j, L (i + 1) j, L (i + 1) (j + 1))
  | true => (L i j, L (i + 1) (j + 1), L i (j + 1))

/-- The set of fully labelled triangles of the `n × n` triangulated grid. -/
def fullTriangles (L : ℕ → ℕ → Fin 3) (n : ℕ) : Finset ((ℕ × ℕ) × Bool) :=
  ((range n ×ˢ range n) ×ˢ (univ : Finset Bool)).filter
    (fun p => full (tri L p.1.1 p.1.2 p.2).1 (tri L p.1.1 p.1.2 p.2).2.1
      (tri L p.1.1 p.1.2 p.2).2.2)

/-- **Exact discrete Stokes identity.** The total circulation over all
triangles equals the circulation along the boundary of the square. -/
theorem discrete_stokes (L : ℕ → ℕ → Fin 3) (n : ℕ) :
    (∑ i ∈ range n, ∑ j ∈ range n,
      (circ (L i j) (L (i + 1) j) (L (i + 1) (j + 1))
        + circ (L i j) (L (i + 1) (j + 1)) (L i (j + 1))))
    = (∑ i ∈ range n, w (L i 0) (L (i + 1) 0))
      + (∑ j ∈ range n, w (L n j) (L n (j + 1)))
      - (∑ i ∈ range n, w (L i n) (L (i + 1) n))
      - (∑ j ∈ range n, w (L 0 j) (L 0 (j + 1))) := by
  set h : ℕ → ℕ → ℤ := fun i j => w (L i j) (L (i + 1) j) with hh
  set v : ℕ → ℕ → ℤ := fun i j => w (L i j) (L i (j + 1)) with hv
  have hsq : ∀ i j, circ (L i j) (L (i + 1) j) (L (i + 1) (j + 1))
        + circ (L i j) (L (i + 1) (j + 1)) (L i (j + 1))
      = (h i j - h i (j + 1)) + (v (i + 1) j - v i j) := by
    intro i j
    simp only [circ, hh, hv]
    rw [w_antisymm (L (i + 1) (j + 1)) (L i j), w_antisymm (L i (j + 1)) (L i j),
      w_antisymm (L (i + 1) (j + 1)) (L i (j + 1))]
    ring_nf
  simp_rw [hsq, sum_add_distrib]
  have e1 : ∀ i, ∑ j ∈ range n, (h i j - h i (j + 1)) = h i 0 - h i n :=
    fun i => sum_range_sub' (fun j => h i j) n
  have e2 : ∑ i ∈ range n, ∑ j ∈ range n, (v (i + 1) j - v i j)
      = ∑ j ∈ range n, (v n j - v 0 j) := by
    rw [sum_comm]
    exact sum_congr rfl (fun j _ => sum_range_sub (fun i => v i j) n)
  rw [e2]
  simp_rw [e1]
  rw [sum_sub_distrib, sum_sub_distrib]
  ring

/-- Sum of `circ` over the triangles agrees mod 2 with the number of fully
labelled triangles. -/
theorem circ_sum_parity (L : ℕ → ℕ → Fin 3) (n : ℕ) :
    ((∑ i ∈ range n, ∑ j ∈ range n,
      (circ (L i j) (L (i + 1) j) (L (i + 1) (j + 1))
        + circ (L i j) (L (i + 1) (j + 1)) (L i (j + 1))))
      - ((fullTriangles L n).card : ℤ)) % 2 = 0 := by
  have hcard : ((fullTriangles L n).card : ℤ) =
      ∑ i ∈ range n, ∑ j ∈ range n,
        ((if full (L i j) (L (i + 1) j) (L (i + 1) (j + 1)) then 1 else 0)
        + (if full (L i j) (L (i + 1) (j + 1)) (L i (j + 1)) then 1 else 0) : ℤ) := by
    rw [fullTriangles, card_filter]
    push_cast
    rw [sum_product, sum_product]
    refine sum_congr rfl (fun i _ => sum_congr rfl (fun j _ => ?_))
    simp only [Fintype.sum_bool, tri]
    ring_nf
  rw [hcard, ← sum_sub_distrib]
  apply Int.emod_emod_of_dvd _ (dvd_refl 2) |>.symm.trans
  rw [Int.emod_emod_of_dvd _ (dvd_refl 2)]
  apply Int.emod_eq_zero_of_dvd
  apply dvd_sum
  intro i _
  rw [← sum_sub_distrib]
  apply dvd_sum
  intro j _
  have h1 := circ_parity (L i j) (L (i + 1) j) (L (i + 1) (j + 1))
  have h2 := circ_parity (L i j) (L (i + 1) (j + 1)) (L i (j + 1))
  have : (circ (L i j) (L (i + 1) j) (L (i + 1) (j + 1))
        + circ (L i j) (L (i + 1) (j + 1)) (L i (j + 1)))
      - ((if full (L i j) (L (i + 1) j) (L (i + 1) (j + 1)) then 1 else 0)
        + (if full (L i j) (L (i + 1) (j + 1)) (L i (j + 1)) then 1 else 0))
      = (circ (L i j) (L (i + 1) j) (L (i + 1) (j + 1))
          - if full (L i j) (L (i + 1) j) (L (i + 1) (j + 1)) then 1 else 0)
        + (circ (L i j) (L (i + 1) (j + 1)) (L i (j + 1))
          - if full (L i j) (L (i + 1) (j + 1)) (L i (j + 1)) then 1 else 0) := by ring
  rw [this]
  exact dvd_add (Int.dvd_of_emod_eq_zero h1) (Int.dvd_of_emod_eq_zero h2)

theorem w_bottom : ∀ a b : Fin 3, a ≠ 2 → b ≠ 2 →
    w a b = (if b = 1 then 1 else 0) - (if a = 1 then 1 else 0) := by decide

theorem w_no_one : ∀ a b : Fin 3, a ≠ 1 → b ≠ 1 → w a b = 0 := by decide

theorem w_no_zero : ∀ a b : Fin 3, a ≠ 0 → b ≠ 0 → w a b = 0 := by decide

/-- **Sperner's lemma on the triangulated granular square.** Label the
vertices `(i,j)`, `0 ≤ i,j ≤ n`, by `0,1,2` so that the bottom side uses
only `0,1` with `L(0,0)=0`, `L(n,0)=1`, the right side avoids `0`, and the
top and left sides avoid `1`.  Then the number of fully labelled triangles
is odd (in particular, positive). -/
theorem sperner_2d (L : ℕ → ℕ → Fin 3) (n : ℕ)
    (hB : ∀ i ≤ n, L i 0 ≠ 2) (h00 : L 0 0 = 0) (hn0 : L n 0 = 1)
    (hR : ∀ j ≤ n, L n j ≠ 0) (hT : ∀ i ≤ n, L i n ≠ 1) (hLe : ∀ j ≤ n, L 0 j ≠ 1) :
    Odd (fullTriangles L n).card := by
  have hS := discrete_stokes L n
  have hP := circ_sum_parity L n
  have hb : ∑ i ∈ range n, w (L i 0) (L (i + 1) 0) = 1 := by
    rw [sum_congr rfl (fun i hi => w_bottom _ _ (hB i (by simp at hi; omega))
      (hB (i + 1) (by simp at hi; omega)))]
    rw [sum_range_sub (fun i => (if L i 0 = 1 then (1 : ℤ) else 0)) n]
    simp [hn0, h00]
  have hr : ∑ j ∈ range n, w (L n j) (L n (j + 1)) = 0 :=
    sum_eq_zero (fun j hj => w_no_zero _ _ (hR j (by simp at hj; omega))
      (hR (j + 1) (by simp at hj; omega)))
  have ht : ∑ i ∈ range n, w (L i n) (L (i + 1) n) = 0 :=
    sum_eq_zero (fun i hi => w_no_one _ _ (hT i (by simp at hi; omega))
      (hT (i + 1) (by simp at hi; omega)))
  have hl : ∑ j ∈ range n, w (L 0 j) (L 0 (j + 1)) = 0 :=
    sum_eq_zero (fun j hj => w_no_one _ _ (hLe j (by simp at hj; omega))
      (hLe (j + 1) (by simp at hj; omega)))
  rw [hS, hb, hr, ht, hl] at hP
  have : ((fullTriangles L n).card : ℤ) % 2 = 1 := by omega
  rw [Nat.odd_iff]
  omega

/-- Every label occurs on a fully labelled triangle. -/
theorem full_cover : ∀ x y z : Fin 3, full x y z → ∀ l : Fin 3, l = x ∨ l = y ∨ l = z := by
  decide

/-! ## Discrete Brouwer theorem -/

/-- The Sperner labelling of a displacement field `(d₁,d₂)` on the grid. -/
def brouwerLabel (n : ℕ) (d₁ d₂ : ℕ → ℕ → K) (i j : ℕ) : Fin 3 :=
  if d₂ i j < 0 ∨ j = n then 2 else if d₁ i j < 0 ∨ i = n then 1 else 0

/-- **Discrete Brouwer theorem.** Let `(d₁, d₂)` be the displacement
`F(p) - p` of a self-map of the granular square `{0,…,n}²` (so it points
inward on each side), and suppose the displacement varies by at most `δ`
between neighbouring lattice points.  Then some lattice point has
`0 ≤ d₁ ≤ δ` and `0 ≤ d₂ ≤ δ`: an approximate fixed point, found by a finite
search over the triangles. -/
theorem discrete_brouwer (n : ℕ) (hn : 0 < n) (d₁ d₂ : ℕ → ℕ → K) (δ : K)
    (hLeft : ∀ j ≤ n, 0 ≤ d₁ 0 j) (hRight : ∀ j ≤ n, d₁ n j ≤ 0)
    (hBot : ∀ i ≤ n, 0 ≤ d₂ i 0) (hTop : ∀ i ≤ n, d₂ i n ≤ 0)
    (hcont : ∀ a b c e : ℕ, a ≤ n → b ≤ n → c ≤ n → e ≤ n →
      a ≤ c + 1 → c ≤ a + 1 → b ≤ e + 1 → e ≤ b + 1 →
      |d₁ a b - d₁ c e| ≤ δ ∧ |d₂ a b - d₂ c e| ≤ δ) :
    ∃ i ≤ n, ∃ j ≤ n, 0 ≤ d₁ i j ∧ d₁ i j ≤ δ ∧ 0 ≤ d₂ i j ∧ d₂ i j ≤ δ := by
  classical
  set L := brouwerLabel n d₁ d₂ with hLdef
  have hn0 : n ≠ 0 := by omega
  have hsp := sperner_2d L n
    (by
      intro i hi
      simp only [hLdef, brouwerLabel]
      have := hBot i hi
      split_ifs with h1 h2 <;> first | (exfalso; rcases h1 with h1 | h1 <;> [linarith; omega]) | decide)
    (by
      simp only [hLdef, brouwerLabel]
      have := hBot 0 (by omega); have := hLeft 0 (by omega)
      split_ifs with h1 h2
      · exfalso; rcases h1 with h1 | h1 <;> [linarith; omega]
      · exfalso; rcases h2 with h2 | h2 <;> [linarith; omega]
      · rfl)
    (by
      simp only [hLdef, brouwerLabel]
      have := hBot n le_rfl
      split_ifs with h1 h2
      · exfalso; rcases h1 with h1 | h1 <;> [linarith; omega]
      · rfl
      · exfalso; simp at h2)
    (by
      intro j hj
      simp only [hLdef, brouwerLabel]
      split_ifs with h1 h2
      · decide
      · decide
      · exfalso; simp at h2)
    (by
      intro i hi
      simp only [hLdef, brouwerLabel]
      split_ifs with h1 <;> first | decide | (exfalso; simp at h1))
    (by
      intro j hj
      simp only [hLdef, brouwerLabel]
      have := hLeft j hj
      split_ifs with h1 h2
      · decide
      · exfalso; rcases h2 with h2 | h2 <;> [linarith; omega]
      · decide)
  obtain ⟨⟨⟨i, j⟩, t⟩, hmem⟩ := Finset.card_pos.mp hsp.pos
  simp only [fullTriangles, mem_filter, mem_product, mem_range, mem_univ, and_true] at hmem
  obtain ⟨⟨hi, hj⟩, hfull⟩ := hmem
  -- the four corners of the square
  have key : ∀ l : Fin 3, ∃ a b, a ≤ n ∧ b ≤ n ∧ i ≤ a ∧ a ≤ i + 1 ∧ j ≤ b ∧ b ≤ j + 1 ∧
      L a b = l := by
    intro l
    have hc := full_cover _ _ _ hfull l
    cases t <;> simp only [tri] at hc <;> rcases hc with hc | hc | hc
    all_goals first
      | exact ⟨i, j, by omega, by omega, le_rfl, by omega, le_rfl, by omega, hc.symm⟩
      | exact ⟨i + 1, j, by omega, by omega, by omega, le_rfl, le_rfl, by omega, hc.symm⟩
      | exact ⟨i + 1, j + 1, by omega, by omega, by omega, le_rfl, by omega, le_rfl, hc.symm⟩
      | exact ⟨i, j + 1, by omega, by omega, le_rfl, by omega, by omega, le_rfl, hc.symm⟩
  obtain ⟨a0, b0, ha0, hb0, ga0, ha0', gb0, hb0', h0⟩ := key 0
  obtain ⟨a1, b1, ha1, hb1, ga1, ha1', gb1, hb1', h1⟩ := key 1
  obtain ⟨a2, b2, ha2, hb2, ga2, ha2', gb2, hb2', h2⟩ := key 2
  -- unpack the labels
  have hl0 : 0 ≤ d₁ a0 b0 ∧ 0 ≤ d₂ a0 b0 := by
    simp only [hLdef, brouwerLabel] at h0
    split_ifs at h0 with p q
    · exact absurd h0 (by decide)
    · exact absurd h0 (by decide)
    · push Not at p q; exact ⟨q.1, p.1⟩
  have hl1 : d₁ a1 b1 ≤ 0 := by
    simp only [hLdef, brouwerLabel] at h1
    split_ifs at h1 with p q
    · exact absurd h1 (by decide)
    · rcases q with q | q
      · exact q.le
      · subst q; exact hRight b1 hb1
    · exact absurd h1 (by decide)
  have hl2 : d₂ a2 b2 ≤ 0 := by
    simp only [hLdef, brouwerLabel] at h2
    split_ifs at h2 with p q
    · rcases p with p | p
      · exact p.le
      · subst p; exact hTop a2 ha2
    · exact absurd h2 (by decide)
    · exact absurd h2 (by decide)
  have c01 := (hcont a0 b0 a1 b1 ha0 hb0 ha1 hb1 (by omega) (by omega) (by omega) (by omega)).1
  have c02 := (hcont a0 b0 a2 b2 ha0 hb0 ha2 hb2 (by omega) (by omega) (by omega) (by omega)).2
  rw [abs_le] at c01 c02
  exact ⟨a0, ha0, b0, hb0, hl0.1, by linarith, hl0.2, by linarith⟩

/-! ## Euler characteristic of cubical complexes -/

/-- Elementary cells of the subdivided segment `[0, m]`: vertices `(k,false)`
for `k ≤ m` and edges `(k,true) = [k,k+1]` for `k < m`. -/
def segCells (m : ℕ) : Finset (ℕ × Bool) :=
  (range (m + 1) ×ˢ {false}) ∪ (range m ×ˢ {true})

/-- Dimension of an elementary interval. -/
def dimI (c : ℕ × Bool) : ℕ := if c.2 then 1 else 0

/-- Euler characteristic of a finite set of cells with a dimension function. -/
def euler {α : Type*} (X : Finset α) (dim : α → ℕ) : ℤ := ∑ c ∈ X, (-1 : ℤ) ^ dim c

theorem euler_seg (m : ℕ) : euler (segCells m) dimI = 1 := by
  unfold euler segCells
  rw [sum_union]
  · simp [dimI]
  · rw [disjoint_left]
    intro c h1 h2
    simp only [mem_product, mem_range, mem_singleton] at h1 h2
    rw [h1.2] at h2; simp at h2

/-- Cells of the `m × n` cubical rectangle grid: products of elementary
intervals; the dimension of a product cell is the sum of the dimensions. -/
def rectCells (m n : ℕ) : Finset ((ℕ × Bool) × (ℕ × Bool)) := segCells m ×ˢ segCells n

def dimR (c : (ℕ × Bool) × (ℕ × Bool)) : ℕ := dimI c.1 + dimI c.2

/-- **Euler characteristic of the cubical rectangle is `1`.** -/
theorem euler_rect (m n : ℕ) : euler (rectCells m n) dimR = 1 := by
  unfold euler rectCells dimR
  rw [sum_product]
  simp_rw [pow_add]
  rw [← sum_mul_sum]
  have h1 := euler_seg m
  have h2 := euler_seg n
  unfold euler at h1 h2
  rw [h1, h2]; norm_num

/-- Vertex, edge and face counts of the `m × n` grid give `V - E + F = 1`. -/
theorem grid_VEF (m n : ℕ) :
    ((m + 1) * (n + 1) : ℤ) - (m * (n + 1) + (m + 1) * n) + m * n = 1 := by ring

/-- **Invariance under an elementary collapse.** Removing a pair of distinct
cells whose dimensions differ by one does not change the Euler
characteristic. -/
theorem euler_collapse {α : Type*} [DecidableEq α] (X : Finset α) (dim : α → ℕ)
    (σ τ : α) (hσ : σ ∈ X) (hτ : τ ∈ X) (hne : σ ≠ τ) (hd : dim τ = dim σ + 1) :
    euler ((X.erase τ).erase σ) dim = euler X dim := by
  unfold euler
  have h1 := sum_erase_add X (fun c => (-1 : ℤ) ^ dim c) hτ
  have h2 := sum_erase_add (X.erase τ) (fun c => (-1 : ℤ) ^ dim c)
    (mem_erase.mpr ⟨hne, hσ⟩)
  rw [← h1, ← h2, hd, pow_succ]
  ring

/-- Inclusion–exclusion (Mayer–Vietoris at the level of counts). -/
theorem euler_union {α : Type*} [DecidableEq α] (A B : Finset α) (dim : α → ℕ) :
    euler (A ∪ B) dim = euler A dim + euler B dim - euler (A ∩ B) dim := by
  unfold euler
  have := sum_union_inter (s₁ := A) (s₂ := B) (f := fun c => (-1 : ℤ) ^ dim c)
  linarith

/-- Removing the open cells strictly inside an `a × b` block of the grid
removes `(a-1)(b-1)` vertices, `(a-1)b + a(b-1)` edges and `ab` faces, which
lowers the Euler characteristic by exactly `1`: a granular annulus has
`χ = 0`. -/
theorem open_block_VEF (a b : ℤ) :
    (a - 1) * (b - 1) - ((a - 1) * b + a * (b - 1)) + a * b = 1 := by ring

/-- The boundary of the square `[0,m]×[0,n]` (a cubical circle) has Euler
characteristic `0`: `V - E = 2(m+n) - 2(m+n)`. -/
theorem circle_VE (m n : ℕ) : ((2 * (m + n) : ℕ) : ℤ) - (2 * (m + n) : ℕ) = 0 := by
  simp

/-! ## The Khalimsky topology on `ℤ` -/

/-- The Khalimsky topology: a set is open iff with every even point it
contains both neighbours.  Odd points are open, even points are closed. -/
@[instance_reducible]
def khalimsky : TopologicalSpace ℤ where
  IsOpen U := ∀ x, Even x → x ∈ U → x - 1 ∈ U ∧ x + 1 ∈ U
  isOpen_univ := fun _ _ _ => ⟨trivial, trivial⟩
  isOpen_inter := fun U V hU hV x hx hxUV =>
    ⟨⟨(hU x hx hxUV.1).1, (hV x hx hxUV.2).1⟩, ⟨(hU x hx hxUV.1).2, (hV x hx hxUV.2).2⟩⟩
  isOpen_sUnion := fun S hS x hx hxS => by
    obtain ⟨U, hUS, hxU⟩ := Set.mem_sUnion.mp hxS
    exact ⟨Set.mem_sUnion.mpr ⟨U, hUS, (hS U hUS x hx hxU).1⟩,
      Set.mem_sUnion.mpr ⟨U, hUS, (hS U hUS x hx hxU).2⟩⟩

theorem khal_isOpen_iff (U : Set ℤ) :
    IsOpen[khalimsky] U ↔ ∀ x, Even x → x ∈ U → x - 1 ∈ U ∧ x + 1 ∈ U := Iff.rfl

/-- Odd points are open. -/
theorem khal_isOpen_singleton_odd (x : ℤ) (hx : Odd x) : IsOpen[khalimsky] {x} := by
  intro y hy hyx
  rw [Set.mem_singleton_iff] at hyx; subst hyx
  exact absurd hx (Int.not_odd_iff_even.mpr hy)

/-- Even points are not open. -/
theorem khal_not_isOpen_singleton_even (x : ℤ) (hx : Even x) : ¬ IsOpen[khalimsky] {x} := by
  intro h
  have := (h x hx rfl).1
  simp at this

/-- The smallest open neighbourhood of an even point `x` is `{x-1, x, x+1}`. -/
theorem khal_even_nbhd (x : ℤ) (hx : Even x) (U : Set ℤ) (hU : IsOpen[khalimsky] U)
    (hxU : x ∈ U) : x - 1 ∈ U ∧ x + 1 ∈ U := hU x hx hxU

theorem khal_isOpen_triple (x : ℤ) (hx : Even x) :
    IsOpen[khalimsky] ({x - 1, x, x + 1} : Set ℤ) := by
  intro y hy hyU
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hyU ⊢
  rcases hyU with h | h | h
  · subst h; exfalso
    rcases hx with ⟨k, hk⟩; rcases hy with ⟨l, hl⟩; omega
  · subst h; omega
  · subst h; exfalso
    rcases hx with ⟨k, hk⟩; rcases hy with ⟨l, hl⟩; omega

theorem khal_isClosed_iff (C : Set ℤ) :
    IsClosed[khalimsky] C ↔ ∀ x, Even x → x ∉ C → x - 1 ∉ C ∧ x + 1 ∉ C := by
  rw [← @isOpen_compl_iff ℤ C khalimsky]
  rfl

/-- Even points are closed. -/
theorem khal_isClosed_singleton_even (x : ℤ) (hx : Even x) : IsClosed[khalimsky] {x} := by
  rw [khal_isClosed_iff]
  intro y hy hyx
  simp only [Set.mem_singleton_iff] at hyx ⊢
  rcases hx with ⟨k, hk⟩; rcases hy with ⟨l, hl⟩
  constructor <;> omega

/-- Odd points are not closed. -/
theorem khal_not_isClosed_singleton_odd (x : ℤ) (hx : Odd x) : ¬ IsClosed[khalimsky] {x} := by
  rw [khal_isClosed_iff]
  intro h
  have he : Even (x + 1) := hx.add_one
  have := (h (x + 1) he (by simp)).1
  simp at this

/-- The Khalimsky topology is not discrete (and not `T₁`). -/
theorem khal_not_discrete : ¬ ∀ U : Set ℤ, IsOpen[khalimsky] U :=
  fun h => khal_not_isOpen_singleton_even 0 ⟨0, rfl⟩ (h _)

/-- **Openness of a lattice interval is read off its endpoints.**
`[a,b]` (with `a ≤ b`) is Khalimsky-open iff both endpoints are odd. -/
theorem khal_isOpen_Icc (a b : ℤ) (hab : a ≤ b) :
    IsOpen[khalimsky] (Set.Icc a b) ↔ Odd a ∧ Odd b := by
  rw [khal_isOpen_iff]
  constructor
  · intro h
    constructor
    · by_contra ha
      rw [Int.not_odd_iff_even] at ha
      have := (h a ha ⟨le_rfl, hab⟩).1
      simp at this
    · by_contra hb
      rw [Int.not_odd_iff_even] at hb
      have := (h b hb ⟨hab, le_rfl⟩).2
      simp at this
  · rintro ⟨⟨k, hk⟩, ⟨l, hl⟩⟩ x ⟨m, hm⟩ ⟨hx1, hx2⟩
    simp only [Set.mem_Icc]
    omega

/-- `[a,b]` (with `a ≤ b`) is Khalimsky-closed iff both endpoints are even. -/
theorem khal_isClosed_Icc (a b : ℤ) (hab : a ≤ b) :
    IsClosed[khalimsky] (Set.Icc a b) ↔ Even a ∧ Even b := by
  rw [khal_isClosed_iff]
  constructor
  · intro h
    constructor
    · by_contra ha
      rw [Int.not_even_iff_odd] at ha
      have he : Even (a - 1) := by rcases ha with ⟨k, hk⟩; exact ⟨k, by omega⟩
      have := (h (a - 1) he (by simp)).2
      simp [hab] at this
    · by_contra hb
      rw [Int.not_even_iff_odd] at hb
      have he : Even (b + 1) := hb.add_one
      have := (h (b + 1) he (by simp)).1
      simp [hab] at this
  · rintro ⟨⟨k, hk⟩, ⟨l, hl⟩⟩ x ⟨m, hm⟩ hx
    simp only [Set.mem_Icc, not_and_or, not_le] at hx ⊢
    omega

/-! ## The adjacency graph and digital connectedness -/

/-- The `2ε`-adjacency graph on lattice indices: neighbours differ by one. -/
def adj : SimpleGraph ℤ where
  Adj x y := x + 1 = y ∨ y + 1 = x
  symm := ⟨fun _ _ h => h.symm⟩
  loopless := ⟨fun x h => by rcases h with h | h <;> omega⟩

/-- **Lattice intervals are connected.** The induced adjacency graph on
`[a, b]` is connected. -/
theorem interval_connected (a b : ℤ) (hab : a ≤ b) :
    (adj.induce (Set.Icc a b)).Connected := by
  have ha : a ∈ Set.Icc a b := ⟨le_rfl, hab⟩
  have key : ∀ m : ℕ, ∀ (x : ℤ) (hx : x ∈ Set.Icc a b), x = a + m →
      (adj.induce (Set.Icc a b)).Reachable ⟨a, ha⟩ ⟨x, hx⟩ := by
    intro m
    induction m with
    | zero => intro x hx h; simp at h; subst h; rfl
    | succ m ih =>
      intro x hx h
      have hy : x - 1 ∈ Set.Icc a b := ⟨by omega, by have := hx.2; omega⟩
      refine (ih (x - 1) hy (by push_cast at h; omega)).trans ?_
      apply SimpleGraph.Adj.reachable
      rw [SimpleGraph.induce_adj]
      left; simp
  have : Nonempty (Set.Icc a b) := ⟨⟨a, ha⟩⟩
  refine SimpleGraph.Connected.mk (fun u v => ?_)
  have hu := key (u.1 - a).toNat u.1 u.2 (by have := u.2.1; omega)
  have hv := key (v.1 - a).toNat v.1 v.2 (by have := v.2.1; omega)
  exact hu.symm.trans hv

/-- A set containing two points at distance `≥ 2` but missing a point in
between is disconnected in the adjacency graph: the gap separates it. -/
theorem gap_disconnects (S : Set ℤ) (a c b : ℤ) (hac : a < c) (hcb : c < b)
    (ha : a ∈ S) (hb : b ∈ S) (hc : c ∉ S) :
    ¬ (adj.induce S).Reachable ⟨a, ha⟩ ⟨b, hb⟩ := by
  intro ⟨p⟩
  -- every vertex reachable from `a` stays below `c`
  have : ∀ (u v : S) (q : (adj.induce S).Walk u v), u.1 < c → v.1 < c := by
    intro u v q
    induction q with
    | nil => exact id
    | cons h q ih =>
      intro hu
      apply ih
      rw [SimpleGraph.induce_adj] at h
      rename_i x y _
      rcases h with h | h
      · have : y.1 ≠ c := fun e => hc (e ▸ y.2)
        omega
      · omega
  have := this _ _ p hac
  simp at this; omega

/-! ## Topology from samples at scale `r` -/

/-- Number of clusters of a sorted sample `x 0 ≤ … ≤ x m` at scale `r`:
one plus the number of gaps exceeding `2r` (the `0`-th Betti number of the
union of the balls of radius `r` around the samples). -/
def beta0 (x : ℕ → K) (m : ℕ) (r : K) : ℕ :=
  1 + ((range m).filter (fun i => 2 * r < x (i + 1) - x i)).card

/-- **Persistence of clusters.** `β₀` is non-increasing in the scale. -/
theorem beta0_antitone (x : ℕ → K) (m : ℕ) {r r' : K} (h : r ≤ r') :
    beta0 x m r' ≤ beta0 x m r := by
  unfold beta0
  apply Nat.add_le_add_left
  apply card_le_card
  intro i hi
  simp only [mem_filter] at hi ⊢
  exact ⟨hi.1, by linarith [hi.2]⟩

/-- Once the scale exceeds half of every gap, the sample is one cluster. -/
theorem beta0_eq_one (x : ℕ → K) (m : ℕ) (r : K)
    (h : ∀ i < m, x (i + 1) - x i ≤ 2 * r) : beta0 x m r = 1 := by
  unfold beta0
  rw [Nat.add_eq_left, card_eq_zero, filter_eq_empty_iff]
  intro i hi
  exact not_lt.mpr (h i (mem_range.mp hi))

/-- At a scale below half of the smallest gap, every sample point is its own
cluster. -/
theorem beta0_fine (x : ℕ → K) (m : ℕ) (r : K)
    (h : ∀ i < m, 2 * r < x (i + 1) - x i) : beta0 x m r = m + 1 := by
  unfold beta0
  rw [filter_true_of_mem (fun i hi => h i (mem_range.mp hi)), card_range]
  ring

/-! ## Further topological facts -/

/-- A `T₁` topology on a finite set is discrete: no Hausdorff (or even `T₁`)
topology on the hyperfinite lattice can see anything but single points. -/
theorem t1_finite_discrete (X : Type*) [TopologicalSpace X] [T1Space X] [Finite X] :
    DiscreteTopology X := inferInstance

/-- Shift invariance of Khalimsky-clopen sets. -/
theorem khal_clopen_succ (S : Set ℤ) (ho : IsOpen[khalimsky] S) (hc : IsClosed[khalimsky] S)
    (x : ℤ) : x ∈ S ↔ x + 1 ∈ S := by
  rw [khal_isClosed_iff] at hc
  rcases Int.even_or_odd x with hx | hx
  · constructor
    · intro h; exact (ho x hx h).2
    · intro h; by_contra h'; exact (hc x hx h').2 h
  · have he : Even (x + 1) := hx.add_one
    constructor
    · intro h; by_contra h'; have := (hc (x + 1) he h').1; simp at this; exact this h
    · intro h; have := (ho (x + 1) he h).1; simpa using this

/-- **The Khalimsky line is connected** (whereas `ℤ` with its usual, discrete
topology is totally disconnected). -/
theorem khal_connected : @ConnectedSpace ℤ khalimsky := by
  rw [@connectedSpace_iff_clopen ℤ khalimsky]
  refine ⟨⟨0⟩, fun S hS => ?_⟩
  have hsh := khal_clopen_succ S hS.2 hS.1
  have hall : ∀ x : ℤ, x ∈ S ↔ (0 : ℤ) ∈ S := by
    intro x
    induction x using Int.induction_on with
    | zero => rfl
    | succ k ih => rw [← hsh k, ih]
    | pred k ih => rw [← ih, hsh (-(k : ℤ) - 1)]; simp
  by_cases h0 : (0 : ℤ) ∈ S
  · right; ext x; simp [hall x, h0]
  · left; ext x; simp [hall x, h0]

/-- The reflection `k ↦ n - k` of `{0, …, n}` with `n` odd is
S-continuous but has no fixed lattice point. -/
theorem reflection_no_fixed (n : ℤ) (hn : Odd n) (k : ℤ) : n - k ≠ k := by
  rcases hn with ⟨m, hm⟩; omega

/-- … yet it moves the point `(n-1)/2` by exactly one granule step. -/
theorem reflection_near_fixed (m : ℤ) : (2 * m + 1) - m - m = 1 := by ring

/-! ## Shadows: the classical IVT and Brouwer theorem at every tolerance -/

/-- **Shadow of the discrete IVT.** For a continuous `f` on `[0,1]` with
`f 0 ≤ 0 < f 1` and every tolerance `η > 0`, every sufficiently fine lattice
`{k/n}` contains a point where `|f| ≤ η`, found by the finite search of
`discrete_ivt`. -/
theorem ivt_shadow (f : ℝ → ℝ) (hf : ContinuousOn f (Set.Icc 0 1))
    (h0 : f 0 ≤ 0) (h1 : 0 < f 1) (η : ℝ) (hη : 0 < η) :
    ∃ N : ℕ, ∀ n ≥ N, ∃ k < n, |f (k / n)| ≤ η := by
  have hu := isCompact_Icc.uniformContinuousOn_of_continuous hf
  rw [Metric.uniformContinuousOn_iff] at hu
  obtain ⟨δ, hδ, hδf⟩ := hu η hη
  obtain ⟨N, hN⟩ := exists_nat_gt (1 / δ)
  refine ⟨N + 1, fun n hn => ?_⟩
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hmem : ∀ k : ℕ, k ≤ n → (k / n : ℝ) ∈ Set.Icc (0 : ℝ) 1 := by
    intro k hk
    refine ⟨by positivity, ?_⟩
    rw [div_le_one hnpos]; exact_mod_cast hk
  have := discrete_ivt_approx (fun k : ℕ => f (k / n)) n 0 η
    (by
      intro k hk
      have hd : dist ((k : ℝ) / n) (((k + 1 : ℕ) : ℝ) / n) < δ := by
        rw [Real.dist_eq]
        have : ((k : ℝ) / n) - ((k + 1 : ℕ) : ℝ) / n = -(1 / n) := by
          push_cast; field_simp; ring
        rw [this, abs_neg, abs_of_pos (by positivity)]
        have hNn : (N : ℝ) < n := by exact_mod_cast (show N < n by omega)
        rw [div_lt_iff₀ hnpos]
        rw [div_lt_iff₀ hδ] at hN
        nlinarith
      have := hδf _ (hmem k hk.le) _ (hmem (k + 1) hk) hd
      rw [Real.dist_eq, abs_sub_comm] at this
      exact this.le)
    (by simpa using h0)
    (by
      have : ((n : ℝ) / n) = 1 := div_self hnpos.ne'
      simpa [this] using h1)
  simpa using this

theorem grid_step (n : ℕ) (hn : (0 : ℝ) < n) (a c : ℕ) (h1 : a ≤ c + 1) (h2 : c ≤ a + 1) :
    |(a : ℝ) / n - c / n| ≤ 1 / n := by
  rw [div_sub_div_same, abs_div, abs_of_pos hn]
  apply div_le_div_of_nonneg_right _ hn.le
  rw [abs_le]
  have h1' : (a : ℝ) ≤ c + 1 := by exact_mod_cast h1
  have h2' : (c : ℝ) ≤ a + 1 := by exact_mod_cast h2
  constructor <;> linarith

/-- **Shadow of the discrete Brouwer theorem.** A continuous self-map of the
unit square has, for every tolerance `η > 0`, an `η`-fixed point; it is found
by the finite Sperner search of `discrete_brouwer` on a fine enough lattice. -/
theorem brouwer_shadow (F : ℝ × ℝ → ℝ × ℝ)
    (hF : ContinuousOn F (Set.Icc 0 1 ×ˢ Set.Icc 0 1))
    (hmaps : ∀ p ∈ Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1,
      F p ∈ Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1)
    (η : ℝ) (hη : 0 < η) :
    ∃ p ∈ Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1,
      |(F p).1 - p.1| ≤ η ∧ |(F p).2 - p.2| ≤ η := by
  have hu := (isCompact_Icc.prod isCompact_Icc).uniformContinuousOn_of_continuous hF
  rw [Metric.uniformContinuousOn_iff] at hu
  obtain ⟨δ, hδ, hδf⟩ := hu (η / 2) (by linarith)
  obtain ⟨n, hn⟩ := exists_nat_gt (max (1 / δ) (2 / η))
  have hnpos : (0 : ℝ) < n := lt_of_le_of_lt (le_max_of_le_left (by positivity)) hn
  have hn0 : 0 < n := by exact_mod_cast hnpos
  have hinv1 : 1 / (n : ℝ) < δ := by
    rw [div_lt_iff₀ hnpos]; have := (le_max_left _ _).trans_lt hn
    rw [div_lt_iff₀ hδ] at this; linarith
  have hinv2 : 1 / (n : ℝ) ≤ η / 2 := by
    rw [div_le_iff₀ hnpos]; have := (le_max_right _ _).trans_lt hn
    rw [div_lt_iff₀ hη] at this; linarith
  have hmem1 : ∀ k : ℕ, k ≤ n → (k / n : ℝ) ∈ Set.Icc (0 : ℝ) 1 := by
    intro k hk
    refine ⟨by positivity, ?_⟩
    rw [div_le_one hnpos]; exact_mod_cast hk
  let P : ℕ → ℕ → ℝ × ℝ := fun i j => ((i : ℝ) / n, (j : ℝ) / n)
  have hP : ∀ i j, i ≤ n → j ≤ n → P i j ∈ Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1 :=
    fun i j hi hj => ⟨hmem1 i hi, hmem1 j hj⟩
  have hnn : (n : ℝ) / n = 1 := div_self hnpos.ne'
  obtain ⟨i, hi, j, hj, h1, h2, h3, h4⟩ := discrete_brouwer n hn0
    (fun i j => (F (P i j)).1 - (i : ℝ) / n) (fun i j => (F (P i j)).2 - (j : ℝ) / n) η
    (by intro j hj; have := (hmaps _ (hP 0 j (by omega) hj)).1.1; simpa using this)
    (by intro j hj; have := (hmaps _ (hP n j le_rfl hj)).1.2; simp only [hnn]; linarith)
    (by intro i hi; have := (hmaps _ (hP i 0 hi (by omega))).2.1; simpa using this)
    (by intro i hi; have := (hmaps _ (hP i n hi le_rfl)).2.2; simp only [hnn]; linarith)
    (by
      intro a b c e ha hb hc he h1 h2 h3 h4
      have sa := grid_step n hnpos a c h1 h2
      have sb := grid_step n hnpos b e h3 h4
      have hd : dist (P a b) (P c e) < δ := by
        rw [Prod.dist_eq, Real.dist_eq, Real.dist_eq]
        exact max_lt (sa.trans_lt hinv1) (sb.trans_lt hinv1)
      have hF' := hδf _ (hP a b ha hb) _ (hP c e hc he) hd
      rw [Prod.dist_eq, Real.dist_eq, Real.dist_eq] at hF'
      have f1 := (le_max_left _ _).trans_lt hF'
      have f2 := (le_max_right _ _).trans_lt hF'
      constructor
      · calc |(F (P a b)).1 - (a : ℝ) / n - ((F (P c e)).1 - (c : ℝ) / n)|
            = |((F (P a b)).1 - (F (P c e)).1) - ((a : ℝ) / n - c / n)| := by ring_nf
          _ ≤ |(F (P a b)).1 - (F (P c e)).1| + |(a : ℝ) / n - c / n| := abs_sub _ _
          _ ≤ η := by linarith
      · calc |(F (P a b)).2 - (b : ℝ) / n - ((F (P c e)).2 - (e : ℝ) / n)|
            = |((F (P a b)).2 - (F (P c e)).2) - ((b : ℝ) / n - e / n)| := by ring_nf
          _ ≤ |(F (P a b)).2 - (F (P c e)).2| + |(b : ℝ) / n - e / n| := abs_sub _ _
          _ ≤ η := by linarith)
  refine ⟨P i j, hP i j hi hj, ?_, ?_⟩
  · rw [abs_le]; constructor <;> simp only [P] <;> linarith
  · rw [abs_le]; constructor <;> simp only [P] <;> linarith

/-! ## Exact IVT for digitally continuous integer-valued maps -/

/-- **Exact discrete IVT.** An integer-valued function on `{0,…,n}` whose
values at adjacent points differ by at most one attains every intermediate
integer value exactly. -/
theorem digital_ivt (f : ℕ → ℤ) (n : ℕ) (c : ℤ)
    (hjump : ∀ k < n, |f (k + 1) - f k| ≤ 1) (h0 : f 0 ≤ c) (hn : c ≤ f n) :
    ∃ k ≤ n, f k = c := by
  classical
  have hex : ∃ m, c ≤ f m ∧ m ≤ n := ⟨n, hn, le_rfl⟩
  set m := Nat.find hex with hm
  obtain ⟨hcm, hmn⟩ := Nat.find_spec hex
  rcases Nat.eq_zero_or_pos (Nat.find hex) with h | h
  · refine ⟨0, Nat.zero_le _, ?_⟩
    rw [h] at hcm; exact le_antisymm h0 hcm
  · obtain ⟨k, hk⟩ : ∃ k, Nat.find hex = k + 1 := ⟨Nat.find hex - 1, by omega⟩
    have hlt : f k < c := by
      have := Nat.find_min hex (show k < Nat.find hex by omega)
      push Not at this
      by_contra hc; push Not at hc
      exact absurd (this hc) (by omega)
    have hj := hjump k (by omega)
    rw [abs_le] at hj
    refine ⟨k + 1, by omega, ?_⟩
    rw [hk] at hcm
    omega

/-- The empty configuration and a single point have different Euler
characteristics, `0` and `1`. -/
theorem euler_empty {α : Type*} (dim : α → ℕ) : euler (∅ : Finset α) dim = 0 := by
  simp [euler]

theorem euler_point {α : Type*} (dim : α → ℕ) (σ : α) (h : dim σ = 0) :
    euler {σ} dim = 1 := by
  simp [euler, h]

end QE.Topology
