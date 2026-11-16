-- SPDX-License-Identifier: MIT
-- Copyright 2026 Metere Industries, Inc. Author: Alfredo Metere.
-- Quasi-Euclidean Granular Geometry. Any derivative work must carry this notice:
--   This work is derivative of the Quasi-Euclidean Granular Geometry book
--   authored by Alfredo Metere. Copyright 2026 Metere Industries, Inc.
--   All rights reserved
-- See LICENSE.md and NOTICE.

import QuasiEuclidean.Basic

/-!
# Chapter 7: multivariable granular calculus

Functions on the granular lattice `(2ε)ℤⁿ` are modelled as functions on the
index lattice `Fin n → ℤ` with values in an arbitrary linearly ordered field
`K`.  All results are exact finitary identities or inequalities valid for
every `ε > 0` (or `ε ≠ 0`), hence in particular for an infinitesimal `ε`
(`K := Hyperreal`) and for a physical cut-off (`K := ℝ`, `ε = ℓ_P`).
-/

set_option linter.unusedSectionVars false

namespace QE.Multi

open Finset

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-! ## Partial granular derivatives and the cubical exterior derivative -/

/-- The `i`-th unit index vector. -/
def e {n : ℕ} (i : Fin n) : Fin n → ℤ := Pi.single i 1

/-- Forward partial granular derivative in direction `i`. -/
def pd (ε : K) {n : ℕ} (i : Fin n) (f : (Fin n → ℤ) → K) (x : Fin n → ℤ) : K :=
  (f (x + e i) - f x) / (2 * ε)

/-- Granular partial derivatives commute exactly. -/
theorem pd_comm (ε : K) {n : ℕ} (i j : Fin n) (f : (Fin n → ℤ) → K) (x : Fin n → ℤ) :
    pd ε i (pd ε j f) x = pd ε j (pd ε i f) x := by
  unfold pd
  rw [add_right_comm x (e j) (e i)]
  ring

theorem pd_sub (ε : K) {n : ℕ} (i : Fin n) (f g : (Fin n → ℤ) → K) (x : Fin n → ℤ) :
    pd ε i (fun y => f y - g y) x = pd ε i f x - pd ε i g x := by
  unfold pd; ring

theorem pd_add (ε : K) {n : ℕ} (i : Fin n) (f g : (Fin n → ℤ) → K) (x : Fin n → ℤ) :
    pd ε i (fun y => f y + g y) x = pd ε i f x + pd ε i g x := by
  unfold pd; ring

/-- Exterior derivative of a 0-cochain (the granular gradient). -/
def d0 (ε : K) {n : ℕ} (f : (Fin n → ℤ) → K) : Fin n → (Fin n → ℤ) → K :=
  fun i => pd ε i f

/-- Exterior derivative of a 1-cochain `ω = ∑ ωᵢ dxᵢ`, in components. -/
def d1 (ε : K) {n : ℕ} (ω : Fin n → (Fin n → ℤ) → K) :
    Fin n → Fin n → (Fin n → ℤ) → K :=
  fun i j x => pd ε i (ω j) x - pd ε j (ω i) x

/-- Exterior derivative of a 2-cochain, in components. -/
def d2 (ε : K) {n : ℕ} (η : Fin n → Fin n → (Fin n → ℤ) → K) :
    Fin n → Fin n → Fin n → (Fin n → ℤ) → K :=
  fun i j k x => pd ε i (η j k) x - pd ε j (η i k) x + pd ε k (η i j) x

/-- `d ∘ d = 0` on 0-cochains, in every dimension. -/
theorem d1_d0 (ε : K) {n : ℕ} (f : (Fin n → ℤ) → K) (i j : Fin n) (x : Fin n → ℤ) :
    d1 ε (d0 ε f) i j x = 0 := by
  unfold d1 d0; rw [pd_comm]; ring

/-- `d ∘ d = 0` on 1-cochains, in every dimension. -/
theorem d2_d1 (ε : K) {n : ℕ} (ω : Fin n → (Fin n → ℤ) → K) (i j k : Fin n)
    (x : Fin n → ℤ) : d2 ε (d1 ε ω) i j k x = 0 := by
  unfold d2 d1
  simp only [pd_sub]
  rw [pd_comm ε j i (ω k), pd_comm ε k i (ω j), pd_comm ε k j (ω i)]
  ring

/-! ### Three-dimensional vector calculus -/

/-- Granular gradient in three dimensions. -/
def grad (ε : K) (f : (Fin 3 → ℤ) → K) : Fin 3 → (Fin 3 → ℤ) → K := d0 ε f

/-- Granular curl. -/
def curl (ε : K) (F : Fin 3 → (Fin 3 → ℤ) → K) : Fin 3 → (Fin 3 → ℤ) → K :=
  ![d1 ε F 1 2, d1 ε F 2 0, d1 ε F 0 1]

/-- Granular divergence. -/
def div (ε : K) {n : ℕ} (F : Fin n → (Fin n → ℤ) → K) (x : Fin n → ℤ) : K :=
  ∑ i, pd ε i (F i) x

/-- `curl ∘ grad = 0` exactly. -/
theorem curl_grad (ε : K) (f : (Fin 3 → ℤ) → K) (i : Fin 3) (x : Fin 3 → ℤ) :
    curl ε (grad ε f) i x = 0 := by
  fin_cases i <;> simp [curl, grad, d1_d0]

/-- `div ∘ curl = 0` exactly. -/
theorem div_curl (ε : K) (F : Fin 3 → (Fin 3 → ℤ) → K) (x : Fin 3 → ℤ) :
    div ε (curl ε F) x = 0 := by
  simp only [div, Fin.sum_univ_three, curl]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons]
  unfold d1
  simp only [pd_sub]
  rw [pd_comm ε 1 0 (F 2), pd_comm ε 2 1 (F 0), pd_comm ε 2 0 (F 1)]
  ring


/-! ## Telescoping and the discrete Stokes theorem -/

omit [LinearOrder K] [IsStrictOrderedRing K] in
/-- One-dimensional telescoping along a lattice line. -/
theorem tele (g : ℤ → K) (a : ℤ) (m : ℕ) :
    ∑ i ∈ range m, (g (a + (i : ℤ) + 1) - g (a + i)) = g (a + m) - g a := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [sum_range_succ, ih]; push_cast; ring_nf

theorem vec2_e0 (p q : ℤ) : (![p, q] : Fin 2 → ℤ) + e 0 = ![p + 1, q] := by
  ext i; fin_cases i <;> simp [e]

theorem vec2_e1 (p q : ℤ) : (![p, q] : Fin 2 → ℤ) + e 1 = ![p, q + 1] := by
  ext i; fin_cases i <;> simp [e]

/-- Discrete Green/Stokes theorem on a lattice rectangle
`[a, a+m) × [b, b+n)`: the double granular integral of `∂ₓQ - ∂ᵧP` equals the
circulation of the edge cochain `(P, Q)` around the boundary, exactly. -/
theorem green_rect (ε : K) (hε : ε ≠ 0) (ω : Fin 2 → (Fin 2 → ℤ) → K)
    (a b : ℤ) (m n : ℕ) :
    ∑ i ∈ range m, ∑ j ∈ range n, d1 ε ω 0 1 ![a + i, b + j] * (2 * ε) ^ 2
      = 2 * ε * ((∑ i ∈ range m, (ω 0 ![a + i, b] - ω 0 ![a + i, b + n]))
          + ∑ j ∈ range n, (ω 1 ![a + m, b + j] - ω 1 ![a, b + j])) := by
  have key : ∀ i j : ℤ, d1 ε ω 0 1 ![i, j] * (2 * ε) ^ 2
      = 2 * ε * ((ω 1 ![i + 1, j] - ω 1 ![i, j]) - (ω 0 ![i, j + 1] - ω 0 ![i, j])) := by
    intro i j
    simp only [d1, pd, vec2_e0, vec2_e1]
    field_simp
  simp only [key, ← mul_sum]
  congr 1
  have h1 : ∑ i ∈ range m, ∑ j ∈ range n, (ω 1 ![a + i + 1, b + j] - ω 1 ![a + i, b + j])
      = ∑ j ∈ range n, (ω 1 ![a + m, b + j] - ω 1 ![a, b + j]) := by
    rw [sum_comm]
    refine sum_congr rfl (fun j _ => ?_)
    exact tele (fun t => ω 1 ![t, b + j]) a m
  have h2 : ∀ i : ℕ, ∑ j ∈ range n, (ω 0 ![a + i, b + j + 1] - ω 0 ![a + i, b + j])
      = ω 0 ![a + i, b + n] - ω 0 ![a + i, b] := by
    intro i; exact tele (fun t => ω 0 ![a + i, t]) b n
  have h2' := sum_congr (rfl : range m = range m) (fun i (_ : i ∈ range m) => h2 i)
  simp only [sum_sub_distrib] at h1 h2' ⊢
  linear_combination h1 - h2'

theorem vec3_e0 (p q r : ℤ) : (![p, q, r] : Fin 3 → ℤ) + e 0 = ![p + 1, q, r] := by
  ext i; fin_cases i <;> simp [e]

theorem vec3_e1 (p q r : ℤ) : (![p, q, r] : Fin 3 → ℤ) + e 1 = ![p, q + 1, r] := by
  ext i; fin_cases i <;> simp [e]

theorem vec3_e2 (p q r : ℤ) : (![p, q, r] : Fin 3 → ℤ) + e 2 = ![p, q, r + 1] := by
  ext i; fin_cases i <;> simp [e]

/-- Outward flux of a face cochain `F` through the boundary of the lattice box
`[a,a+l) × [b,b+m) × [c,c+n)` (each face cell weighted by `(2ε)²`). -/
def flux3 (ε : K) (F : Fin 3 → (Fin 3 → ℤ) → K) (a b c : ℤ) (l m n : ℕ) : K :=
  (2 * ε) ^ 2 *
    ((∑ j ∈ range m, ∑ k ∈ range n, (F 0 ![a + l, b + j, c + k] - F 0 ![a, b + j, c + k]))
    + (∑ i ∈ range l, ∑ k ∈ range n, (F 1 ![a + i, b + m, c + k] - F 1 ![a + i, b, c + k]))
    + (∑ i ∈ range l, ∑ j ∈ range m, (F 2 ![a + i, b + j, c + n] - F 2 ![a + i, b + j, c])))

/-- Exact discrete Gauss (divergence) theorem on a lattice box. -/
theorem gauss_box (ε : K) (hε : ε ≠ 0) (F : Fin 3 → (Fin 3 → ℤ) → K)
    (a b c : ℤ) (l m n : ℕ) :
    ∑ i ∈ range l, ∑ j ∈ range m, ∑ k ∈ range n,
        div ε F ![a + i, b + j, c + k] * (2 * ε) ^ 3
      = flux3 ε F a b c l m n := by
  have key : ∀ p q r : ℤ, div ε F ![p, q, r] * (2 * ε) ^ 3
      = (2 * ε) ^ 2 * ((F 0 ![p + 1, q, r] - F 0 ![p, q, r])
          + (F 1 ![p, q + 1, r] - F 1 ![p, q, r]) + (F 2 ![p, q, r + 1] - F 2 ![p, q, r])) := by
    intro p q r
    simp only [div, Fin.sum_univ_three, pd, vec3_e0, vec3_e1, vec3_e2]
    field_simp
  simp only [key, ← mul_sum, flux3]
  congr 1
  have hA : ∑ i ∈ range l, ∑ j ∈ range m, ∑ k ∈ range n,
      (F 0 ![a + i + 1, b + j, c + k] - F 0 ![a + i, b + j, c + k])
      = ∑ j ∈ range m, ∑ k ∈ range n, (F 0 ![a + l, b + j, c + k] - F 0 ![a, b + j, c + k]) := by
    rw [sum_comm]
    refine sum_congr rfl (fun j _ => ?_)
    rw [sum_comm]
    refine sum_congr rfl (fun k _ => ?_)
    exact tele (fun t => F 0 ![t, b + j, c + k]) a l
  have hB : ∑ i ∈ range l, ∑ j ∈ range m, ∑ k ∈ range n,
      (F 1 ![a + i, b + j + 1, c + k] - F 1 ![a + i, b + j, c + k])
      = ∑ i ∈ range l, ∑ k ∈ range n, (F 1 ![a + i, b + m, c + k] - F 1 ![a + i, b, c + k]) := by
    refine sum_congr rfl (fun i _ => ?_)
    rw [sum_comm]
    refine sum_congr rfl (fun k _ => ?_)
    exact tele (fun t => F 1 ![a + i, t, c + k]) b m
  have hC : ∑ i ∈ range l, ∑ j ∈ range m, ∑ k ∈ range n,
      (F 2 ![a + i, b + j, c + k + 1] - F 2 ![a + i, b + j, c + k])
      = ∑ i ∈ range l, ∑ j ∈ range m, (F 2 ![a + i, b + j, c + n] - F 2 ![a + i, b + j, c]) := by
    refine sum_congr rfl (fun i _ => ?_)
    refine sum_congr rfl (fun j _ => ?_)
    exact tele (fun t => F 2 ![a + i, b + j, t]) c n
  simp only [sum_add_distrib, sum_sub_distrib] at hA hB hC ⊢
  linear_combination hA + hB + hC

/-! ## Summation by parts in several variables -/

omit [LinearOrder K] [IsStrictOrderedRing K] in
/-- Abel summation by parts for sequences. -/
theorem abel (F G : ℕ → K) (m : ℕ) :
    ∑ k ∈ range m, F k * (G (k + 1) - G k)
      = F m * G m - F 0 * G 0 - ∑ k ∈ range m, (F (k + 1) - F k) * G (k + 1) := by
  induction m with
  | zero => simp
  | succ m ih => rw [sum_range_succ, sum_range_succ, ih]; ring

omit [LinearOrder K] [IsStrictOrderedRing K] in
theorem line_succ {n : ℕ} (x : Fin n → ℤ) (i : Fin n) (k : ℕ) :
    x + ((k : ℤ) • e i) + e i = x + (((k + 1 : ℕ) : ℤ) • e i) := by
  push_cast; rw [add_smul, one_smul, add_assoc]

/-- Summation by parts in direction `i` over the box `T × [0, m)·eᵢ`
(`T` an arbitrary finite set of base points), with its exact boundary term. -/
theorem sbp (ε : K) (hε : ε ≠ 0) {n : ℕ} (i : Fin n) (f g : (Fin n → ℤ) → K)
    (T : Finset (Fin n → ℤ)) (m : ℕ) :
    ∑ x ∈ T, ∑ k ∈ range m, f (x + (k : ℤ) • e i) * pd ε i g (x + (k : ℤ) • e i) * (2 * ε)
      = ∑ x ∈ T, (f (x + (m : ℤ) • e i) * g (x + (m : ℤ) • e i) - f x * g x)
        - ∑ x ∈ T, ∑ k ∈ range m,
            pd ε i f (x + (k : ℤ) • e i) * g (x + ((k + 1 : ℕ) : ℤ) • e i) * (2 * ε) := by
  rw [← sum_sub_distrib]
  refine sum_congr rfl (fun x _ => ?_)
  have h := abel (fun k => f (x + (k : ℤ) • e i)) (fun k => g (x + (k : ℤ) • e i)) m
  simp only [Nat.cast_zero, zero_smul, add_zero] at h
  have e1 : ∀ k : ℕ, f (x + (k : ℤ) • e i) * pd ε i g (x + (k : ℤ) • e i) * (2 * ε)
      = f (x + (k : ℤ) • e i) * (g (x + ((k + 1 : ℕ) : ℤ) • e i) - g (x + (k : ℤ) • e i)) := by
    intro k; unfold pd; rw [line_succ]; field_simp
  have e2 : ∀ k : ℕ, pd ε i f (x + (k : ℤ) • e i) * g (x + ((k + 1 : ℕ) : ℤ) • e i) * (2 * ε)
      = (f (x + ((k + 1 : ℕ) : ℤ) • e i) - f (x + (k : ℤ) • e i))
          * g (x + ((k + 1 : ℕ) : ℤ) • e i) := by
    intro k; unfold pd; rw [line_succ]; field_simp
  simp only [e1, e2]
  exact h

/-! ## The lattice Laplacian, mean-value property, maximum principle -/

/-- The lattice Laplacian `Δ_ε f(x) = ∑ᵢ (f(x+eᵢ) - 2 f(x) + f(x-eᵢ)) / (2ε)²`. -/
def lap (ε : K) {n : ℕ} (f : (Fin n → ℤ) → K) (x : Fin n → ℤ) : K :=
  ∑ i, (f (x + e i) - 2 * f x + f (x - e i)) / (2 * ε) ^ 2

/-- Sum of `f` over the `2n` nearest neighbours of `x`. -/
def nbr {n : ℕ} (f : (Fin n → ℤ) → K) (x : Fin n → ℤ) : K :=
  ∑ i, (f (x + e i) + f (x - e i))

theorem lap_eq (ε : K) {n : ℕ} (f : (Fin n → ℤ) → K) (x : Fin n → ℤ) :
    lap ε f x = (nbr f x - 2 * n * f x) / (2 * ε) ^ 2 := by
  unfold lap nbr
  rw [← sum_div]
  congr 1
  have : ∀ i : Fin n, f (x + e i) - 2 * f x + f (x - e i) = (f (x + e i) + f (x - e i)) - 2 * f x :=
    fun i => by ring
  simp only [this, sum_sub_distrib, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
  ring

/-- Mean-value property: `f` is discrete harmonic at `x` iff `f(x)` is the
average of its `2n` nearest neighbours. -/
theorem mean_value (ε : K) (hε : ε ≠ 0) {n : ℕ} (hn : n ≠ 0)
    (f : (Fin n → ℤ) → K) (x : Fin n → ℤ) :
    lap ε f x = 0 ↔ f x = nbr f x / (2 * n) := by
  have h2 : (2 * ε) ^ 2 ≠ 0 := pow_ne_zero _ (mul_ne_zero two_ne_zero hε)
  have hn' : (2 * (n : K)) ≠ 0 := mul_ne_zero two_ne_zero (Nat.cast_ne_zero.mpr hn)
  rw [lap_eq, div_eq_zero_iff, eq_div_iff hn']
  constructor
  · rintro (h | h)
    · linear_combination -h
    · exact absurd h h2
  · intro h; left; linear_combination -h

/-- `Δ_ε f(x) ≥ 0` iff `2n f(x) ≤` neighbour sum (sub-mean-value property). -/
theorem lap_nonneg_iff (ε : K) (hε : 0 < ε) {n : ℕ} (f : (Fin n → ℤ) → K) (x : Fin n → ℤ) :
    0 ≤ lap ε f x ↔ 2 * n * f x ≤ nbr f x := by
  have h2 : 0 < (2 * ε) ^ 2 := by positivity
  rw [lap_eq, le_div_iff₀ h2, zero_mul, sub_nonneg]

theorem lap_neg (ε : K) {n : ℕ} (f : (Fin n → ℤ) → K) (x : Fin n → ℤ) :
    lap ε (fun y => -f y) x = -lap ε f x := by
  unfold lap; rw [← sum_neg_distrib]; congr 1; ext i; ring

/-- The lattice boundary of a finite set `Ω`: nearest neighbours of points of
`Ω` that are not in `Ω`. -/
def bdry {n : ℕ} (Ω : Finset (Fin n → ℤ)) : Finset (Fin n → ℤ) :=
  (Ω.biUnion fun x => univ.image (fun i => x + e i) ∪ univ.image (fun i => x - e i)) \ Ω

theorem mem_bdry_plus {n : ℕ} {Ω : Finset (Fin n → ℤ)} {x : Fin n → ℤ} (hx : x ∈ Ω)
    (i : Fin n) (h : x + e i ∉ Ω) : x + e i ∈ bdry Ω := by
  unfold bdry
  refine mem_sdiff.mpr ⟨mem_biUnion.mpr ⟨x, hx, ?_⟩, h⟩
  exact mem_union_left _ (mem_image.mpr ⟨i, mem_univ _, rfl⟩)

theorem mem_bdry_minus {n : ℕ} {Ω : Finset (Fin n → ℤ)} {x : Fin n → ℤ} (hx : x ∈ Ω)
    (i : Fin n) (h : x - e i ∉ Ω) : x - e i ∈ bdry Ω := by
  unfold bdry
  refine mem_sdiff.mpr ⟨mem_biUnion.mpr ⟨x, hx, ?_⟩, h⟩
  exact mem_union_right _ (mem_image.mpr ⟨i, mem_univ _, rfl⟩)

/-- Weak maximum principle for discrete subharmonic functions on an arbitrary
finite lattice region `Ω ⊂ ℤⁿ` (`n ≥ 1`, witnessed by a direction `i₀`):
every value in `Ω` is dominated by some boundary value. -/
theorem max_principle (ε : K) (hε : 0 < ε) {n : ℕ} (i₀ : Fin n)
    (Ω : Finset (Fin n → ℤ)) (f : (Fin n → ℤ) → K)
    (hsub : ∀ x ∈ Ω, 0 ≤ lap ε f x) :
    ∀ x ∈ Ω, ∃ y ∈ bdry Ω, f x ≤ f y := by
  by_contra hcon
  push Not at hcon
  obtain ⟨x₀, hx₀, hlt⟩ := hcon
  obtain ⟨z₀, hz₀, hmax⟩ := Ω.exists_max_image f ⟨x₀, hx₀⟩
  set M := f z₀
  set S := Ω.filter (fun z => f z = M)
  have hS : z₀ ∈ S := mem_filter.mpr ⟨hz₀, rfl⟩
  obtain ⟨z, hzS, hzmax⟩ := S.exists_max_image (fun z => z i₀) ⟨z₀, hS⟩
  obtain ⟨hzΩ, hzM⟩ := mem_filter.mp hzS
  have hb : ∀ y ∈ bdry Ω, f y < M := fun y hy => lt_of_lt_of_le (hlt y hy) (hmax x₀ hx₀)
  have hp : ∀ i, f (z + e i) ≤ M := by
    intro i
    by_cases h : z + e i ∈ Ω
    · exact hmax _ h
    · exact (hb _ (mem_bdry_plus hzΩ i h)).le
  have hm : ∀ i, f (z - e i) ≤ M := by
    intro i
    by_cases h : z - e i ∈ Ω
    · exact hmax _ h
    · exact (hb _ (mem_bdry_minus hzΩ i h)).le
  have hstrict : f (z + e i₀) < M := by
    by_cases h : z + e i₀ ∈ Ω
    · rcases (hmax _ h).lt_or_eq with h' | h'
      · exact h'
      · exfalso
        have := hzmax _ (mem_filter.mpr ⟨h, h'⟩)
        simp [e] at this
    · exact hb _ (mem_bdry_plus hzΩ i₀ h)
  have hsum : nbr f z < ∑ _i : Fin n, (M + M) := by
    unfold nbr
    apply sum_lt_sum
    · intro i _; exact add_le_add (hp i) (hm i)
    · exact ⟨i₀, mem_univ _, add_lt_add_of_lt_of_le hstrict (hm i₀)⟩
  have hl := (lap_nonneg_iff ε hε f z).mp (hsub z hzΩ)
  rw [hzM] at hl
  simp only [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul] at hsum
  linarith

/-- Minimum principle (apply the maximum principle to `-f`). -/
theorem min_principle (ε : K) (hε : 0 < ε) {n : ℕ} (i₀ : Fin n)
    (Ω : Finset (Fin n → ℤ)) (f : (Fin n → ℤ) → K)
    (hsup : ∀ x ∈ Ω, lap ε f x ≤ 0) :
    ∀ x ∈ Ω, ∃ y ∈ bdry Ω, f y ≤ f x := by
  intro x hx
  obtain ⟨y, hy, h⟩ := max_principle ε hε i₀ Ω (fun y => -f y)
    (fun x hx => by rw [lap_neg]; linarith [hsup x hx]) x hx
  exact ⟨y, hy, by linarith⟩

/-- Uniqueness for the discrete Dirichlet problem. -/
theorem dirichlet_unique (ε : K) (hε : 0 < ε) {n : ℕ} (i₀ : Fin n)
    (Ω : Finset (Fin n → ℤ)) (u : (Fin n → ℤ) → K)
    (hharm : ∀ x ∈ Ω, lap ε u x = 0) (hbd : ∀ y ∈ bdry Ω, u y = 0) :
    ∀ x ∈ Ω, u x = 0 := by
  intro x hx
  obtain ⟨y, hy, h1⟩ := max_principle ε hε i₀ Ω u (fun x hx => (hharm x hx).ge) x hx
  obtain ⟨y', hy', h2⟩ := min_principle ε hε i₀ Ω u (fun x hx => (hharm x hx).le) x hx
  rw [hbd y hy] at h1; rw [hbd y' hy'] at h2
  exact le_antisymm h1 h2

/-! ## The lattice Green's function: existence, positivity, finiteness at the source -/

/-- The `n`-dimensional granular delta at `s`: `(2ε)⁻ⁿ` at `s`, `0` elsewhere. -/
def deltaN (ε : K) {n : ℕ} (s x : Fin n → ℤ) : K := if x = s then 1 / (2 * ε) ^ n else 0

/-- Extension by zero of a function on `Ω`. -/
def ext0 {n : ℕ} {Ω : Finset (Fin n → ℤ)} (u : Ω → K) (x : Fin n → ℤ) : K :=
  if h : x ∈ Ω then u ⟨x, h⟩ else 0

theorem lap_add (ε : K) {n : ℕ} (f g : (Fin n → ℤ) → K) (x : Fin n → ℤ) :
    lap ε (fun y => f y + g y) x = lap ε f x + lap ε g x := by
  unfold lap; rw [← sum_add_distrib]; congr 1; ext i; ring

theorem lap_smul (ε : K) {n : ℕ} (c : K) (f : (Fin n → ℤ) → K) (x : Fin n → ℤ) :
    lap ε (fun y => c * f y) x = c * lap ε f x := by
  unfold lap; rw [mul_sum]; congr 1; ext i; ring

/-- The Dirichlet Laplacian `u ↦ -Δ_ε (ext₀ u)` on functions on a finite region. -/
def dirLap (ε : K) {n : ℕ} (Ω : Finset (Fin n → ℤ)) : (Ω → K) →ₗ[K] (Ω → K) where
  toFun u := fun x => -lap ε (ext0 u) x
  map_add' u v := by
    funext x
    have : ext0 (u + v) = fun y => ext0 u y + ext0 v y := by
      funext y; unfold ext0; split_ifs <;> simp
    simp only [this, lap_add, Pi.add_apply]; ring
  map_smul' c u := by
    funext x
    have : ext0 (c • u) = fun y => c * ext0 u y := by
      funext y; unfold ext0; split_ifs <;> simp
    simp only [this, lap_smul, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; ring

/-- Existence and uniqueness for the discrete Dirichlet problem
`-Δ_ε u = ρ` in `Ω`, `u = 0` off `Ω`, for every right-hand side `ρ`. -/
theorem dirichlet_solvable (ε : K) (hε : 0 < ε) {n : ℕ} (i₀ : Fin n)
    (Ω : Finset (Fin n → ℤ)) (ρ : (Fin n → ℤ) → K) :
    ∃ u : (Fin n → ℤ) → K, (∀ x, x ∉ Ω → u x = 0) ∧ ∀ x ∈ Ω, -lap ε u x = ρ x := by
  have hinj : Function.Injective (dirLap ε Ω) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro u hu
    funext ⟨x, hx⟩
    have hz : ∀ y ∈ Ω, lap ε (ext0 u) y = 0 := by
      intro y hy
      have := congrFun hu ⟨y, hy⟩
      simp only [dirLap, LinearMap.coe_mk, AddHom.coe_mk, Pi.zero_apply, neg_eq_zero] at this
      exact this
    have hb : ∀ y ∈ bdry Ω, ext0 u y = 0 := by
      intro y hy
      have : y ∉ Ω := (mem_sdiff.mp hy).2
      simp [ext0, this]
    have := dirichlet_unique ε hε i₀ Ω (ext0 u) hz hb x hx
    simpa [ext0, hx] using this
  obtain ⟨u, hu⟩ := (LinearMap.injective_iff_surjective.mp hinj) (fun x => ρ x)
  refine ⟨ext0 u, fun x hx => by simp [ext0, hx], fun x hx => ?_⟩
  have := congrFun hu ⟨x, hx⟩
  simpa [dirLap] using this

/-- Properties of the Dirichlet Green's function `G` of `-Δ_ε` on a finite
region `Ω` with source `s ∈ Ω`: it is nonnegative, maximal at the source, and
its value at the source is a finite number bounded below by
`(2ε)² / ((2ε)ⁿ · 2n)`. -/
theorem green_props (ε : K) (hε : 0 < ε) {n : ℕ} (i₀ : Fin n)
    (Ω : Finset (Fin n → ℤ)) (s : Fin n → ℤ) (hs : s ∈ Ω) (G : (Fin n → ℤ) → K)
    (hG0 : ∀ x, x ∉ Ω → G x = 0) (hG : ∀ x ∈ Ω, -lap ε G x = deltaN ε s x) :
    (∀ x, 0 ≤ G x) ∧ (∀ x, G x ≤ G s) ∧
      (2 * ε) ^ 2 / (2 * ε) ^ n ≤ 2 * n * G s := by
  have hpos : (0 : K) < 2 * ε := by positivity
  -- nonnegativity: minimum principle
  have hnn : ∀ x, 0 ≤ G x := by
    intro x
    by_cases hx : x ∈ Ω
    · have hsup : ∀ y ∈ Ω, lap ε G y ≤ 0 := by
        intro y hy
        have := hG y hy
        have hd : 0 ≤ deltaN ε s y := by unfold deltaN; split_ifs <;> positivity
        linarith
      obtain ⟨y, hy, h⟩ := min_principle ε hε i₀ Ω G hsup x hx
      rw [hG0 y (mem_sdiff.mp hy).2] at h; exact h
    · rw [hG0 x hx]
  refine ⟨hnn, ?_, ?_⟩
  · intro x
    by_cases hx : x ∈ Ω.erase s
    · have hharm : ∀ y ∈ Ω.erase s, 0 ≤ lap ε G y := by
        intro y hy
        obtain ⟨hne, hyΩ⟩ := mem_erase.mp hy
        have := hG y hyΩ
        simp only [deltaN, hne, ite_false] at this
        linarith
      obtain ⟨y, hy, h⟩ := max_principle ε hε i₀ (Ω.erase s) G hharm x hx
      have hy' : y ∉ Ω.erase s := (mem_sdiff.mp hy).2
      by_cases hys : y = s
      · rw [hys] at h; exact h
      · have : y ∉ Ω := fun h' => hy' (mem_erase.mpr ⟨hys, h'⟩)
        rw [hG0 y this] at h; exact h.trans (hnn s)
    · by_cases hxs : x = s
      · rw [hxs]
      · have : x ∉ Ω := fun h' => hx (mem_erase.mpr ⟨hxs, h'⟩)
        rw [hG0 x this]; exact hnn s
  · have h := hG s hs
    simp only [deltaN, ite_true] at h
    rw [lap_eq] at h
    have hn : 0 ≤ nbr G s := by
      unfold nbr; exact sum_nonneg (fun i _ => add_nonneg (hnn _) (hnn _))
    have h2 : (0 : K) < (2 * ε) ^ 2 := by positivity
    have : (2 * ↑n * G s - nbr G s) = (2 * ε) ^ 2 / (2 * ε) ^ n := by
      field_simp at h ⊢; linarith
    linarith

/-- The granular field `-∇_ε G` of the Green's function is bounded by
`G(s)/(2ε)` everywhere, in particular at the source: the field of a
point-sphere charge is finite. -/
theorem green_field_bound (ε : K) (hε : 0 < ε) {n : ℕ} (G : (Fin n → ℤ) → K)
    (s : Fin n → ℤ) (hnn : ∀ x, 0 ≤ G x) (hmax : ∀ x, G x ≤ G s) (i : Fin n)
    (x : Fin n → ℤ) : |pd ε i G x| ≤ G s / (2 * ε) := by
  have hpos : (0 : K) < 2 * ε := by positivity
  unfold pd
  rw [abs_div, abs_of_pos hpos]
  apply div_le_div_of_nonneg_right _ hpos.le
  rw [abs_le]
  constructor <;> linarith [hnn (x + e i), hnn x, hmax (x + e i), hmax x]

/-! ## Gauss's law for a point-sphere charge -/

omit [LinearOrder K] [IsStrictOrderedRing K] in
theorem sum_indicator_line (a : ℤ) (l : ℕ) :
    ∑ i ∈ range l, (if a + (i : ℤ) = 0 then (1 : K) else 0)
      = if a ≤ 0 ∧ 0 < a + l then 1 else 0 := by
  induction l with
  | zero => simp
  | succ l ih =>
    rw [sum_range_succ, ih]
    push_cast
    by_cases h1 : a ≤ 0 ∧ 0 < a + l
    · have h2 : ¬ (a + l = 0) := by omega
      have h3 : a ≤ 0 ∧ 0 < a + (l + 1) := by omega
      simp [h1, h2, h3]
    · by_cases h2 : a + l = 0
      · have h3 : a ≤ 0 ∧ 0 < a + (l + 1) := by omega
        simp [h2, h3]
      · have h3 : ¬ (a ≤ 0 ∧ 0 < a + (l + 1)) := by omega
        simp only [h1, h2, h3, ite_false, add_zero]

/-- Exact Gauss law on the granular lattice: if the face cochain `F` has
divergence `q δ_ε` (a point-sphere charge at the origin cell), then its flux
through the boundary of *any* lattice box is `q` if the box contains the
origin and `0` otherwise — no limit, no regularisation. -/
theorem gauss_point_charge (ε : K) (hε : ε ≠ 0) (F : Fin 3 → (Fin 3 → ℤ) → K) (q : K)
    (a b c : ℤ) (l m n : ℕ)
    (hF : ∀ i j k : ℕ, i < l → j < m → k < n →
      div ε F ![a + i, b + j, c + k] = q * deltaN ε 0 ![a + i, b + j, c + k]) :
    flux3 ε F a b c l m n
      = if (a ≤ 0 ∧ 0 < a + l) ∧ (b ≤ 0 ∧ 0 < b + m) ∧ (c ≤ 0 ∧ 0 < c + n)
        then q else 0 := by
  rw [← gauss_box ε hε]
  have h2 : (2 * ε) ^ 3 ≠ 0 := pow_ne_zero _ (mul_ne_zero two_ne_zero hε)
  have key : ∀ i j k : ℤ, q * deltaN ε 0 ![i, j, k] * (2 * ε) ^ 3
      = q * ((if i = 0 then 1 else 0) * (if j = 0 then 1 else 0) * (if k = 0 then 1 else 0)) := by
    intro i j k
    unfold deltaN
    have : (![i, j, k] : Fin 3 → ℤ) = 0 ↔ i = 0 ∧ j = 0 ∧ k = 0 := by
      constructor
      · intro h
        exact ⟨congrFun h 0, congrFun h 1, congrFun h 2⟩
      · rintro ⟨rfl, rfl, rfl⟩; ext t; fin_cases t <;> rfl
    by_cases hi : i = 0 <;> by_cases hj : j = 0 <;> by_cases hk : k = 0 <;>
      simp [this, hi, hj, hk, h2]
  have hsum : ∑ i ∈ range l, ∑ j ∈ range m, ∑ k ∈ range n,
        div ε F ![a + i, b + j, c + k] * (2 * ε) ^ 3
      = ∑ i ∈ range l, ∑ j ∈ range m, ∑ k ∈ range n,
        q * ((if a + (i : ℤ) = 0 then 1 else 0) * (if b + (j : ℤ) = 0 then 1 else 0)
          * (if c + (k : ℤ) = 0 then 1 else 0)) := by
    refine sum_congr rfl (fun i hi => sum_congr rfl (fun j hj => sum_congr rfl (fun k hk => ?_)))
    rw [hF i j k (mem_range.mp hi) (mem_range.mp hj) (mem_range.mp hk), key]
  rw [hsum]
  simp only [← mul_sum, ← sum_mul]
  rw [sum_indicator_line, sum_indicator_line, sum_indicator_line]
  by_cases h1 : a ≤ 0 ∧ 0 < a + l <;> by_cases h2 : b ≤ 0 ∧ 0 < b + m <;>
    by_cases h3 : c ≤ 0 ∧ 0 < c + n <;> simp [h1, h2, h3]

/-- The staggered field `Fᵢ(x) = -D⁺ᵢ u(x - eᵢ)` (living on the lower
`i`-face of the cell of `x`) has divergence `-Δ_ε u`. -/
theorem div_field_eq (ε : K) {n : ℕ} (u : (Fin n → ℤ) → K) (x : Fin n → ℤ) :
    div ε (fun i y => -pd ε i u (y - e i)) x = -lap ε u x := by
  unfold div lap pd
  rw [← sum_neg_distrib]
  refine sum_congr rfl (fun i _ => ?_)
  simp only [add_sub_cancel_right, sub_add_cancel]
  ring

/-- Gauss's law for the potential of a point-sphere charge: if
`-Δ_ε u = q δ_ε` on a lattice box, the flux of `-∇_ε u` out of the box is `q`
or `0` according as the origin cell is inside the box or not. -/
theorem gauss_potential (ε : K) (hε : ε ≠ 0) (u : (Fin 3 → ℤ) → K) (q : K)
    (a b c : ℤ) (l m n : ℕ)
    (hu : ∀ i j k : ℕ, i < l → j < m → k < n →
      -lap ε u ![a + i, b + j, c + k] = q * deltaN ε 0 ![a + i, b + j, c + k]) :
    flux3 ε (fun i y => -pd ε i u (y - e i)) a b c l m n
      = if (a ≤ 0 ∧ 0 < a + l) ∧ (b ≤ 0 ∧ 0 < b + m) ∧ (c ≤ 0 ∧ 0 < c + n)
        then q else 0 :=
  gauss_point_charge ε hε _ q a b c l m n
    (fun i j k hi hj hk => by rw [div_field_eq]; exact hu i j k hi hj hk)

/-! ## Change of variables for lattice-preserving maps -/

/-- An integer matrix with unit determinant acts injectively on the lattice. -/
theorem unimodular_injective {n : ℕ} (M : Matrix (Fin n) (Fin n) ℤ) (h : IsUnit M.det) :
    Function.Injective M.mulVec := by
  intro v w hvw
  have := congrArg (M⁻¹).mulVec hvw
  simpa [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ h] using this

/-- Unimodular maps preserve the granular measure exactly (Jacobian `|det M| = 1`). -/
theorem muN_unimodular (ε : K) {n : ℕ} (M : Matrix (Fin n) (Fin n) ℤ) (h : IsUnit M.det)
    (A : Finset (Fin n → ℤ)) : QE.muN n ε (A.image M.mulVec) = QE.muN n ε A := by
  unfold QE.muN
  rw [card_image_of_injective _ (unimodular_injective M h)]

/-- Exact change of variables for granular integrals under a unimodular map. -/
theorem change_of_variables (ε : K) {n : ℕ} (M : Matrix (Fin n) (Fin n) ℤ)
    (h : IsUnit M.det) (A : Finset (Fin n → ℤ)) (f : (Fin n → ℤ) → K) :
    ∑ y ∈ A.image M.mulVec, f y * (2 * ε) ^ n = ∑ x ∈ A, f (M.mulVec x) * (2 * ε) ^ n := by
  rw [sum_image]
  intro x _ y _ hxy
  exact unimodular_injective M h hxy

/-- Jacobian as cell count: the dilation `x ↦ m x` maps the box `[0,L)ⁿ` onto a
set whose lattice hull `[0, mL)ⁿ` contains exactly `|det(m·I)|` times as many
cells as the original box. -/
theorem dilation_cell_count {n : ℕ} (m L : ℕ) :
    (Fintype.piFinset fun _ : Fin n => range (m * L)).card
      = (Matrix.det ((m : ℤ) • (1 : Matrix (Fin n) (Fin n) ℤ))).natAbs
          * (Fintype.piFinset fun _ : Fin n => range L).card := by
  rw [Matrix.det_smul, Matrix.det_one, mul_one, Fintype.card_fin, Int.natAbs_pow,
    Int.natAbs_natCast]
  simp [mul_pow]

/-- Affine lattice-preserving maps `x ↦ M x + b` (`M` unimodular) preserve the
granular measure exactly. -/
theorem muN_affine (ε : K) {n : ℕ} (M : Matrix (Fin n) (Fin n) ℤ) (h : IsUnit M.det)
    (b : Fin n → ℤ) (A : Finset (Fin n → ℤ)) :
    QE.muN n ε (A.image fun x => M.mulVec x + b) = QE.muN n ε A := by
  unfold QE.muN
  rw [card_image_of_injective]
  intro x y hxy
  exact unimodular_injective M h (add_right_cancel hxy)

/-! ## Further identities for the Laplacian -/

/-- `Δ_ε = ∑ᵢ D⁻ᵢ D⁺ᵢ`: the Laplacian is the divergence (backward) of the
gradient (forward). -/
theorem lap_eq_div_grad (ε : K) {n : ℕ} (f : (Fin n → ℤ) → K) (x : Fin n → ℤ) :
    lap ε f x = ∑ i, pd ε i (pd ε i f) (x - e i) := by
  unfold lap pd
  refine sum_congr rfl (fun i _ => ?_)
  rw [sub_add_cancel]
  ring

/-- Exact discrete harmonic polynomials in the plane: with lattice coordinates
`X = 2ε x₀`, `Y = 2ε x₁`, both `XY` and `X² - Y²` satisfy `Δ_ε u = 0`
identically. -/
theorem harmonic_xy (ε : K) (x : Fin 2 → ℤ) :
    lap ε (fun y => (2 * ε * y 0) * (2 * ε * y 1)) x = 0 := by
  unfold lap; simp [Fin.sum_univ_two, e]; ring

theorem harmonic_x2_y2 (ε : K) (hε : ε ≠ 0) (x : Fin 2 → ℤ) :
    lap ε (fun y => (2 * ε * y 0) ^ 2 - (2 * ε * y 1) ^ 2) x = 0 := by
  unfold lap; simp [Fin.sum_univ_two, e]; field_simp; ring

/-- A granular gradient has zero circulation around every lattice rectangle
(exactness of `d f` via Stokes). -/
theorem circulation_grad (ε : K) (hε : ε ≠ 0) (f : (Fin 2 → ℤ) → K) (a b : ℤ) (m n : ℕ) :
    2 * ε * ((∑ i ∈ range m, (d0 ε f 0 ![a + i, b] - d0 ε f 0 ![a + i, b + n]))
          + ∑ j ∈ range n, (d0 ε f 1 ![a + m, b + j] - d0 ε f 1 ![a, b + j])) = 0 := by
  rw [← green_rect ε hε]
  simp [d1_d0]

/-- Field of a point-sphere charge on a cubically symmetric region: if the
`2n` neighbours of the source all carry the same value `c` of the Green's
function, then the potential drop across the source cell and the outward
field on each of its `2n` faces are given exactly by
`2n (G(s) - c) = (2ε)² / (2ε)ⁿ` and `2n · D⁺ᵢ G(s) = -(2ε) / (2ε)ⁿ`.
For `n = 3` the field on each face is `1 / (6 (2ε)²)` per unit charge. -/
theorem green_symmetric_field (ε : K) (hε : 0 < ε) {n : ℕ} (G : (Fin n → ℤ) → K)
    (s : Fin n → ℤ) (c : K) (hc : ∀ i, G (s + e i) = c ∧ G (s - e i) = c)
    (hG : -lap ε G s = deltaN ε s s) (i : Fin n) :
    2 * n * (G s - c) = (2 * ε) ^ 2 / (2 * ε) ^ n ∧
      2 * n * pd ε i G s = -(2 * ε) / (2 * ε) ^ n := by
  have hpos : (0 : K) < 2 * ε := by positivity
  have hnb : nbr G s = 2 * n * c := by
    unfold nbr
    simp only [fun i => (hc i).1, fun i => (hc i).2, sum_const, card_univ,
      Fintype.card_fin, nsmul_eq_mul]
    ring
  simp only [deltaN, ite_true] at hG
  rw [lap_eq, hnb] at hG
  have h1 : 2 * n * (G s - c) = (2 * ε) ^ 2 / (2 * ε) ^ n := by
    field_simp at hG ⊢; linarith
  refine ⟨h1, ?_⟩
  unfold pd
  rw [(hc i).1]
  have h2 : (2 * ε) ^ 2 = (2 * ε) * (2 * ε) := by ring
  rw [h2, mul_div_assoc] at h1
  field_simp
  field_simp at h1
  linarith

/-- Discrete harmonic cubic: `X³ - 3XY²` is exactly harmonic. -/
theorem harmonic_cubic (ε : K) (x : Fin 2 → ℤ) :
    lap ε (fun y => (2 * ε * y 0) ^ 3 - 3 * (2 * ε * y 0) * (2 * ε * y 1) ^ 2) x = 0 := by
  unfold lap; simp [Fin.sum_univ_two, e]; field_simp; ring

/-- Discrete harmonic quartic: `Re z⁴ = X⁴ - 6X²Y² + Y⁴` is *not* lattice
harmonic (`Δ_ε` of it is `4(2ε)²`), but the corrected polynomial
`X⁴ - 6X²Y² + Y⁴ - (2ε)²(X² + Y²)` is exactly harmonic. -/
theorem lap_quartic (ε : K) (x : Fin 2 → ℤ) :
    lap ε (fun y => (2 * ε * y 0) ^ 4 - 6 * (2 * ε * y 0) ^ 2 * (2 * ε * y 1) ^ 2
      + (2 * ε * y 1) ^ 4) x = 4 * (2 * ε) ^ 2 := by
  unfold lap; simp [Fin.sum_univ_two, e]; field_simp; ring

theorem harmonic_quartic (ε : K) (x : Fin 2 → ℤ) :
    lap ε (fun y => (2 * ε * y 0) ^ 4 - 6 * (2 * ε * y 0) ^ 2 * (2 * ε * y 1) ^ 2
      + (2 * ε * y 1) ^ 4 - (2 * ε) ^ 2 * ((2 * ε * y 0) ^ 2 + (2 * ε * y 1) ^ 2)) x = 0 := by
  unfold lap; simp [Fin.sum_univ_two, e]; field_simp; ring

/-- The classical counterexample to the symmetry of mixed partials,
`f(x,y) = xy(x² - y²)/(x² + y²)`, `f(0,0) = 0`: at the lattice origin the
granular quotient `(D⁺ₓ f(0, kh) - D⁺ₓ f(0,0)) / (kh)` equals
`(1 - k²)/(1 + k²)` exactly (`h = 2ε`, `k ≠ 0`); the classical value `-1` is
its shadow for `k` infinite with `kh` infinitesimal. -/
theorem mixed_profile (h k : K) (hh : h ≠ 0) (hk : k ≠ 0) :
    let f : K → K → K := fun x y => if x = 0 ∧ y = 0 then 0 else x * y * (x ^ 2 - y ^ 2) / (x ^ 2 + y ^ 2)
    ((f h (k * h) - f 0 (k * h)) / h - (f h 0 - f 0 0) / h) / (k * h) = (1 - k ^ 2) / (1 + k ^ 2) := by
  intro f
  have h1 : (1 + k ^ 2) ≠ 0 := by positivity
  have hkh : k * h ≠ 0 := mul_ne_zero hk hh
  simp only [f, hh, hkh, and_false, ite_false, and_true, ite_true,
    zero_mul, mul_zero, zero_div]
  · have h2 : h ^ 2 + (k * h) ^ 2 = h ^ 2 * (1 + k ^ 2) := by ring
    rw [h2]
    field_simp
    ring

/-- Zaremba's punctured domain, granular version: the harmonic measure of the
puncture `u = G/G(s)` exists, equals `1` at the puncture-point, `0` outside
`Ω`, lies in `[0,1]`, and is exactly harmonic on `Ω \ {s}`. -/
theorem zaremba (ε : K) (hε : 0 < ε) {n : ℕ} (i₀ : Fin n)
    (Ω : Finset (Fin n → ℤ)) (s : Fin n → ℤ) (hs : s ∈ Ω) (G : (Fin n → ℤ) → K)
    (hG0 : ∀ x, x ∉ Ω → G x = 0) (hG : ∀ x ∈ Ω, -lap ε G x = deltaN ε s x) :
    let u := fun x => G x / G s
    u s = 1 ∧ (∀ x, x ∉ Ω → u x = 0) ∧ (∀ x, 0 ≤ u x ∧ u x ≤ 1) ∧
      ∀ x ∈ Ω.erase s, lap ε u x = 0 := by
  intro u
  obtain ⟨hnn, hmax, hlow⟩ := green_props ε hε i₀ Ω s hs G hG0 hG
  have hpos : 0 < G s := by
    have : 0 < (2 * ε) ^ 2 / (2 * ε) ^ n := by positivity
    have h2n : (0 : K) ≤ 2 * n := by positivity
    by_contra hle
    push Not at hle
    have : G s = 0 := le_antisymm hle (hnn s)
    rw [this, mul_zero] at hlow
    linarith
  refine ⟨div_self hpos.ne', fun x hx => by simp [u, hG0 x hx], fun x => ⟨?_, ?_⟩, ?_⟩
  · exact div_nonneg (hnn x) hpos.le
  · rw [div_le_one hpos]; exact hmax x
  · intro x hx
    obtain ⟨hne, hxΩ⟩ := mem_erase.mp hx
    have h := hG x hxΩ
    simp only [deltaN, hne, ite_false] at h
    have : u = fun y => (1 / G s) * G y := by funext y; simp [u]; ring
    rw [this, lap_smul, show lap ε G x = 0 by linarith, mul_zero]

/-- Granular capacity of a single point-sphere, `cap = 1/G(s)`: it is a
positive finite number bounded by `2n (2ε)ⁿ / (2ε)²` (for `n = 3`: `≤ 12ε`). -/
theorem capacity_bound (ε : K) (hε : 0 < ε) {n : ℕ} (i₀ : Fin n)
    (Ω : Finset (Fin n → ℤ)) (s : Fin n → ℤ) (hs : s ∈ Ω) (G : (Fin n → ℤ) → K)
    (hG0 : ∀ x, x ∉ Ω → G x = 0) (hG : ∀ x ∈ Ω, -lap ε G x = deltaN ε s x) :
    0 < 1 / G s ∧ 1 / G s ≤ 2 * n * (2 * ε) ^ n / (2 * ε) ^ 2 := by
  obtain ⟨hnn, -, hlow⟩ := green_props ε hε i₀ Ω s hs G hG0 hG
  have hq : 0 < (2 * ε) ^ 2 / (2 * ε) ^ n := by positivity
  have hpos : 0 < G s := by
    by_contra hle
    push Not at hle
    have : G s = 0 := le_antisymm hle (hnn s)
    rw [this, mul_zero] at hlow
    linarith
  refine ⟨by positivity, ?_⟩
  have h1 : (0 : K) < (2 * ε) ^ n := by positivity
  have h2 : (0 : K) < (2 * ε) ^ 2 := by positivity
  rw [div_le_div_iff₀ hpos h2, one_mul]
  rw [div_le_iff₀ h1] at hlow
  linarith

/-! ## Closed and exact 1-forms: the granular Poincaré lemma on a quadrant -/

/-- The path-sum potential of a 1-form: along the bottom edge, then up. -/
def potential (ε : K) (ω : Fin 2 → (Fin 2 → ℤ) → K) (x : Fin 2 → ℤ) : K :=
  (∑ t ∈ range (x 0).toNat, ω 0 ![(t : ℤ), 0] * (2 * ε))
    + ∑ t ∈ range (x 1).toNat, ω 1 ![x 0, (t : ℤ)] * (2 * ε)

/-- Granular Poincaré lemma: a closed 1-form (`d ω = 0`) on the lattice
quadrant is exactly the granular gradient of its path-sum potential. -/
theorem poincare (ε : K) (hε : ε ≠ 0) (ω : Fin 2 → (Fin 2 → ℤ) → K)
    (hclosed : ∀ i j : ℕ, d1 ε ω 0 1 ![(i : ℤ), (j : ℤ)] = 0) (i j : ℕ) :
    pd ε 0 (potential ε ω) ![(i : ℤ), (j : ℤ)] = ω 0 ![(i : ℤ), (j : ℤ)] ∧
      pd ε 1 (potential ε ω) ![(i : ℤ), (j : ℤ)] = ω 1 ![(i : ℤ), (j : ℤ)] := by
  have h2 : (2 * ε) ≠ 0 := mul_ne_zero two_ne_zero hε
  constructor
  · unfold pd
    rw [vec2_e0]
    have hc : ∀ t : ℕ, ω 1 ![(i : ℤ) + 1, (t : ℤ)] - ω 1 ![(i : ℤ), (t : ℤ)]
        = ω 0 ![(i : ℤ), (t : ℤ) + 1] - ω 0 ![(i : ℤ), (t : ℤ)] := by
      intro t
      have := hclosed i t
      simp only [d1, pd, vec2_e0, vec2_e1] at this
      field_simp at this
      linear_combination this
    have htel : ∑ t ∈ range j, (ω 0 ![(i : ℤ), ((t + 1 : ℕ) : ℤ)] - ω 0 ![(i : ℤ), (t : ℤ)])
        = ω 0 ![(i : ℤ), (j : ℤ)] - ω 0 ![(i : ℤ), ((0 : ℕ) : ℤ)] :=
      sum_range_sub (fun t : ℕ => ω 0 ![(i : ℤ), (t : ℤ)]) j
    have hsplit : potential ε ω ![(i : ℤ) + 1, (j : ℤ)] - potential ε ω ![(i : ℤ), (j : ℤ)]
        = ω 0 ![(i : ℤ), 0] * (2 * ε)
          + (∑ t ∈ range j, (ω 1 ![(i : ℤ) + 1, (t : ℤ)] - ω 1 ![(i : ℤ), (t : ℤ)])) * (2 * ε) := by
      unfold potential
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Int.toNat_natCast]
      have : ((i : ℤ) + 1).toNat = i + 1 := by omega
      rw [this, sum_range_succ]
      simp only [← sum_mul, sum_sub_distrib]
      ring
    rw [hsplit]
    simp only [hc] at *
    push_cast at htel
    rw [htel]
    field_simp
    ring
  · unfold pd
    rw [vec2_e1]
    unfold potential
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Int.toNat_natCast]
    have : ((j : ℤ) + 1).toNat = j + 1 := by omega
    rw [this, sum_range_succ]
    rw [show ∀ a b c : K, (a + (b + c)) - (a + b) = c from fun a b c => by ring]
    field_simp

/-! ## Ampère's law for a point vortex in the plane -/

/-- The two-dimensional granular delta at the origin. -/
theorem sum_indicator_rect (a b : ℤ) (m n : ℕ) :
    ∑ i ∈ range m, ∑ j ∈ range n,
      ((if a + (i : ℤ) = 0 then (1 : K) else 0) * (if b + (j : ℤ) = 0 then 1 else 0))
      = if (a ≤ 0 ∧ 0 < a + m) ∧ (b ≤ 0 ∧ 0 < b + n) then 1 else 0 := by
  simp only [← mul_sum, ← sum_mul]
  rw [sum_indicator_line, sum_indicator_line]
  by_cases h1 : a ≤ 0 ∧ 0 < a + m <;> by_cases h2 : b ≤ 0 ∧ 0 < b + n <;> simp [h1, h2]

/-- Exact Ampère/Stokes law: if the curl of a planar 1-form is a point
vortex `Γ δ_ε` (density `Γ/(2ε)²` on the origin cell), its circulation around
*every* lattice rectangle is `Γ` or `0` according as the origin cell is
enclosed or not. -/
theorem ampere_point (ε : K) (hε : ε ≠ 0) (ω : Fin 2 → (Fin 2 → ℤ) → K) (Γ : K)
    (a b : ℤ) (m n : ℕ)
    (hω : ∀ i j : ℕ, i < m → j < n →
      d1 ε ω 0 1 ![a + i, b + j] = Γ * deltaN ε 0 ![a + i, b + j]) :
    2 * ε * ((∑ i ∈ range m, (ω 0 ![a + i, b] - ω 0 ![a + i, b + n]))
          + ∑ j ∈ range n, (ω 1 ![a + m, b + j] - ω 1 ![a, b + j]))
      = if (a ≤ 0 ∧ 0 < a + m) ∧ (b ≤ 0 ∧ 0 < b + n) then Γ else 0 := by
  rw [← green_rect ε hε]
  have h2 : (2 * ε) ^ 2 ≠ 0 := pow_ne_zero _ (mul_ne_zero two_ne_zero hε)
  have key : ∀ i j : ℤ, Γ * deltaN ε 0 ![i, j] * (2 * ε) ^ 2
      = Γ * ((if i = 0 then 1 else 0) * (if j = 0 then 1 else 0)) := by
    intro i j
    unfold deltaN
    have : (![i, j] : Fin 2 → ℤ) = 0 ↔ i = 0 ∧ j = 0 := by
      constructor
      · intro h; exact ⟨congrFun h 0, congrFun h 1⟩
      · rintro ⟨rfl, rfl⟩; ext t; fin_cases t <;> rfl
    by_cases hi : i = 0 <;> by_cases hj : j = 0 <;> simp [this, hi, hj, h2]
  have hsum : ∑ i ∈ range m, ∑ j ∈ range n, d1 ε ω 0 1 ![a + i, b + j] * (2 * ε) ^ 2
      = Γ * ∑ i ∈ range m, ∑ j ∈ range n,
        ((if a + (i : ℤ) = 0 then (1 : K) else 0) * (if b + (j : ℤ) = 0 then 1 else 0)) := by
    rw [mul_sum]
    refine sum_congr rfl (fun i hi => ?_)
    rw [mul_sum]
    refine sum_congr rfl (fun j hj => ?_)
    rw [hω i j (mem_range.mp hi) (mem_range.mp hj), key]
  rw [hsum, sum_indicator_rect]
  split_ifs <;> simp

/-! ## Energy identity: self-energy equals field energy -/

omit [LinearOrder K] [IsStrictOrderedRing K] in
/-- Translation invariance of the sum of a finitely supported lattice function. -/
theorem shift_sum {n : ℕ} (g : (Fin n → ℤ) → K) (D S : Finset (Fin n → ℤ))
    (hg : ∀ x, x ∉ D → g x = 0) (hDS : D ⊆ S) (v : Fin n → ℤ)
    (hv : ∀ x ∈ D, x - v ∈ S) :
    ∑ x ∈ S, g (x + v) = ∑ x ∈ S, g x := by
  have h1 : ∑ x ∈ S, g x = ∑ x ∈ D, g x :=
    (sum_subset hDS (fun x _ hx => hg x hx)).symm
  have h2 : ∑ x ∈ S, g (x + v) = ∑ x ∈ D.image (fun y => y - v), g (x + v) := by
    refine (sum_subset ?_ ?_).symm
    · intro x hx
      obtain ⟨y, hy, rfl⟩ := mem_image.mp hx
      exact hv y hy
    · intro x _ hx
      apply hg
      intro hxD
      exact hx (mem_image.mpr ⟨x + v, hxD, by abel⟩)
  rw [h1, h2, sum_image (fun x _ y _ h => by simpa using h)]
  refine sum_congr rfl (fun x _ => ?_)
  rw [sub_add_cancel]

/-- Exact energy identity (discrete Green's first identity): for `u`
supported in a finite region `D`, and any finite `S ⊇ D ∪ (D - eᵢ)`,
`∑ u · (-Δ_ε u) = ∑ |∇_ε u|²`.  Multiplying by `(2ε)ⁿ/2`: the electrostatic
self-energy `½∑ ρ u (2ε)ⁿ` equals the field energy `½∑ |E|² (2ε)ⁿ`. -/
theorem energy_identity (ε : K) {n : ℕ} (u : (Fin n → ℤ) → K)
    (D S : Finset (Fin n → ℤ)) (hu : ∀ x, x ∉ D → u x = 0) (hDS : D ⊆ S)
    (hS : ∀ i, ∀ x ∈ D, x - e i ∈ S) :
    ∑ x ∈ S, u x * (-lap ε u x) = ∑ x ∈ S, ∑ i, (pd ε i u x) ^ 2 := by
  unfold lap pd
  have hper : ∀ i : Fin n,
      ∑ x ∈ S, -(u x * (u (x + e i) - 2 * u x + u (x - e i)))
        = ∑ x ∈ S, (u (x + e i) - u x) ^ 2 := by
    intro i
    have hA : ∑ x ∈ S, u (x + e i) ^ 2 = ∑ x ∈ S, u x ^ 2 :=
      shift_sum (fun x => u x ^ 2) D S (fun x hx => by simp [hu x hx]) hDS (e i) (hS i)
    have hB : ∑ x ∈ S, u (x + e i) * u x = ∑ x ∈ S, u x * u (x - e i) := by
      have := shift_sum (fun x => u x * u (x - e i)) D S (fun x hx => by simp [hu x hx])
        hDS (e i) (hS i)
      simpa using this
    have e1 : ∀ x, -(u x * (u (x + e i) - 2 * u x + u (x - e i)))
        = 2 * u x ^ 2 - u (x + e i) * u x - u x * u (x - e i) := fun x => by ring
    have e2 : ∀ x, (u (x + e i) - u x) ^ 2
        = u (x + e i) ^ 2 + u x ^ 2 - 2 * (u (x + e i) * u x) := fun x => by ring
    simp only [e1, e2, sum_sub_distrib, sum_add_distrib, ← mul_sum]
    rw [hA, hB]; ring
  have L : ∀ x, u x * -∑ i, (u (x + e i) - 2 * u x + u (x - e i)) / (2 * ε) ^ 2
      = ∑ i, -(u x * (u (x + e i) - 2 * u x + u (x - e i))) / (2 * ε) ^ 2 := by
    intro x; rw [mul_neg, mul_sum, ← sum_neg_distrib]; congr 1; ext i; ring
  have R : ∀ x, ∑ i, ((u (x + e i) - u x) / (2 * ε)) ^ 2
      = ∑ i, (u (x + e i) - u x) ^ 2 / (2 * ε) ^ 2 := by
    intro x; congr 1; ext i; rw [div_pow]
  rw [sum_congr rfl (fun x _ => L x), sum_congr rfl (fun x _ => R x), sum_comm, sum_comm (s := S)]
  refine sum_congr rfl (fun i _ => ?_)
  rw [← sum_div, ← sum_div, hper i]

/-! ## Fourier symbol of the lattice Laplacian -/

/-- Plane waves diagonalise the second difference: with `θ = k·(2ε)`,
`e^{iθ(j+1)} - 2e^{iθj} + e^{iθ(j-1)} = -4 sin²(θ/2) e^{iθj}`.  Dividing by
`(2ε)²` and summing over directions, the symbol of `Δ_ε` is
`-(4/(2ε)²) ∑ᵢ sin²(kᵢ ε)`, bounded in modulus by `4n/(2ε)²`. -/
theorem second_diff_symbol (θ : ℂ) (j : ℂ) :
    Complex.exp ((j + 1) * θ * Complex.I) - 2 * Complex.exp (j * θ * Complex.I)
        + Complex.exp ((j - 1) * θ * Complex.I)
      = -4 * Complex.sin (θ / 2) ^ 2 * Complex.exp (j * θ * Complex.I) := by
  have h1 : Complex.exp ((j + 1) * θ * Complex.I)
      = Complex.exp (j * θ * Complex.I) * Complex.exp (θ * Complex.I) := by
    rw [← Complex.exp_add]; ring_nf
  have h2 : Complex.exp ((j - 1) * θ * Complex.I)
      = Complex.exp (j * θ * Complex.I) * Complex.exp (-θ * Complex.I) := by
    rw [← Complex.exp_add]; ring_nf
  have hc : Complex.exp (θ * Complex.I) + Complex.exp (-θ * Complex.I) = 2 * Complex.cos θ :=
    (Complex.two_cos θ).symm
  have hθ : Complex.cos θ = 1 - 2 * Complex.sin (θ / 2) ^ 2 := by
    have h := Complex.cos_two_mul' (θ / 2)
    rw [show 2 * (θ / 2) = θ by ring] at h
    have h' := Complex.sin_sq_add_cos_sq (θ / 2)
    linear_combination h + h'
  rw [h1, h2]
  linear_combination Complex.exp (j * θ * Complex.I) * hc
    + 2 * Complex.exp (j * θ * Complex.I) * hθ

/-! ## Green reciprocity -/

/-- Polarised energy identity: for `u, v` supported in `D` and
`S ⊇ D ∪ (D - eᵢ)`, `∑ u (-Δ_ε v) = ∑ ∇_ε u · ∇_ε v`; in particular the
bilinear form `∑ u (-Δ_ε v)` is symmetric. -/
theorem bilinear_identity (ε : K) {n : ℕ} (u v : (Fin n → ℤ) → K)
    (D S : Finset (Fin n → ℤ)) (hu : ∀ x, x ∉ D → u x = 0)
    (hDS : D ⊆ S) (hS : ∀ i, ∀ x ∈ D, x - e i ∈ S) :
    ∑ x ∈ S, u x * (-lap ε v x) = ∑ x ∈ S, ∑ i, pd ε i u x * pd ε i v x := by
  unfold lap pd
  have hper : ∀ i : Fin n,
      ∑ x ∈ S, -(u x * (v (x + e i) - 2 * v x + v (x - e i)))
        = ∑ x ∈ S, (u (x + e i) - u x) * (v (x + e i) - v x) := by
    intro i
    have hA : ∑ x ∈ S, u (x + e i) * v (x + e i) = ∑ x ∈ S, u x * v x :=
      shift_sum (fun x => u x * v x) D S (fun x hx => by simp [hu x hx]) hDS (e i) (hS i)
    have hB : ∑ x ∈ S, u (x + e i) * v x = ∑ x ∈ S, u x * v (x - e i) := by
      have := shift_sum (fun x => u x * v (x - e i)) D S (fun x hx => by simp [hu x hx])
        hDS (e i) (hS i)
      simpa using this
    have e1 : ∀ x, -(u x * (v (x + e i) - 2 * v x + v (x - e i)))
        = 2 * (u x * v x) - u x * v (x + e i) - u x * v (x - e i) := fun x => by ring
    have e2 : ∀ x, (u (x + e i) - u x) * (v (x + e i) - v x)
        = u (x + e i) * v (x + e i) + u x * v x - u (x + e i) * v x - u x * v (x + e i) :=
      fun x => by ring
    simp only [e1, e2, sum_sub_distrib, sum_add_distrib, ← mul_sum]
    rw [hA, ← hB]; ring
  have L : ∀ x, u x * -∑ i, (v (x + e i) - 2 * v x + v (x - e i)) / (2 * ε) ^ 2
      = ∑ i, -(u x * (v (x + e i) - 2 * v x + v (x - e i))) / (2 * ε) ^ 2 := by
    intro x; rw [mul_neg, mul_sum, ← sum_neg_distrib]; congr 1; ext i; ring
  have R : ∀ x, ∑ i, (u (x + e i) - u x) / (2 * ε) * ((v (x + e i) - v x) / (2 * ε))
      = ∑ i, (u (x + e i) - u x) * (v (x + e i) - v x) / (2 * ε) ^ 2 := by
    intro x; congr 1; ext i; ring
  rw [sum_congr rfl (fun x _ => L x), sum_congr rfl (fun x _ => R x), sum_comm, sum_comm (s := S)]
  refine sum_congr rfl (fun i _ => ?_)
  rw [← sum_div, ← sum_div, hper i]

/-- Green reciprocity `G_D(x, y) = G_D(y, x)` for the Dirichlet Green's
function of a finite region (Maxwell's reciprocity theorem, exact). -/
theorem green_symm (ε : K) (hε : 0 < ε) {n : ℕ} (D S : Finset (Fin n → ℤ))
    (hDS : D ⊆ S) (hS : ∀ i, ∀ x ∈ D, x - e i ∈ S)
    (x y : Fin n → ℤ) (hx : x ∈ D) (hy : y ∈ D) (Gx Gy : (Fin n → ℤ) → K)
    (hGx0 : ∀ z, z ∉ D → Gx z = 0) (hGy0 : ∀ z, z ∉ D → Gy z = 0)
    (hGx : ∀ z ∈ D, -lap ε Gx z = deltaN ε x z) (hGy : ∀ z ∈ D, -lap ε Gy z = deltaN ε y z) :
    Gx y = Gy x := by
  have hpos : (0 : K) < (2 * ε) ^ n := by positivity
  have eval : ∀ (G H : (Fin n → ℤ) → K) (p : Fin n → ℤ), p ∈ D → (∀ z, z ∉ D → G z = 0) →
      (∀ z ∈ D, -lap ε H z = deltaN ε p z) →
      ∑ z ∈ S, G z * (-lap ε H z) = G p / (2 * ε) ^ n := by
    intro G H p hp hG0 hH
    have h1 : ∑ z ∈ S, G z * (-lap ε H z) = ∑ z ∈ D, G z * (-lap ε H z) :=
      (sum_subset hDS (fun z _ hz => by rw [hG0 z hz, zero_mul])).symm
    rw [h1, sum_congr rfl (fun z hz => by rw [hH z hz])]
    unfold deltaN
    simp only [mul_ite, mul_zero]
    simp only [sum_ite_eq', hp, ite_true]
    ring
  have hA := eval Gx Gy y hy hGx0 hGy
  have hB := eval Gy Gx x hx hGy0 hGx
  have hsym := bilinear_identity ε Gx Gy D S hGx0 hDS hS
  have hsym' := bilinear_identity ε Gy Gx D S hGy0 hDS hS
  have : ∑ z ∈ S, ∑ i, pd ε i Gx z * pd ε i Gy z = ∑ z ∈ S, ∑ i, pd ε i Gy z * pd ε i Gx z := by
    refine sum_congr rfl (fun z _ => sum_congr rfl (fun i _ => mul_comm _ _))
  have hfin : Gx y / (2 * ε) ^ n = Gy x / (2 * ε) ^ n := by
    rw [← hA, ← hB, hsym, hsym', this]
  field_simp at hfin
  exact hfin

/-! ## Fubini's paradox -/

/-- The double granular sum of an antisymmetric kernel over a lattice square
vanishes exactly. -/
theorem antisym_sum_zero (g : ℕ → ℕ → K) (hg : ∀ i j, g i j = -g j i) (N : ℕ) :
    ∑ i ∈ range N, ∑ j ∈ range N, g i j = 0 := by
  have h : ∑ i ∈ range N, ∑ j ∈ range N, g i j = -∑ i ∈ range N, ∑ j ∈ range N, g i j := by
    conv_lhs => rw [sum_comm]
    simp only [← sum_neg_distrib]
    exact sum_congr rfl (fun i _ => sum_congr rfl (fun j _ => hg j i))
  linarith

/-- The classical Fubini counterexample `f(x,y) = (x² - y²)/(x² + y²)²` on
the lattice (`f(0,0) := 0`), with lattice coordinates `x = h i`, `y = h j`. -/
def fubiniKernel (h : K) (i j : ℕ) : K :=
  if i = 0 ∧ j = 0 then 0
  else ((h * i) ^ 2 - (h * j) ^ 2) / ((h * i) ^ 2 + (h * j) ^ 2) ^ 2

theorem fubini_double_zero (h : K) (N : ℕ) :
    ∑ i ∈ range N, ∑ j ∈ range N, fubiniKernel h i j * h ^ 2 = 0 := by
  apply antisym_sum_zero
  intro i j
  unfold fubiniKernel
  by_cases hij : i = 0 ∧ j = 0
  · have hji : j = 0 ∧ i = 0 := ⟨hij.2, hij.1⟩
    simp [hij]
  · have hji : ¬ (j = 0 ∧ i = 0) := fun h' => hij ⟨h'.2, h'.1⟩
    simp only [hij, hji, ite_false]
    rw [add_comm ((h * j) ^ 2)]
    ring

/-- The column `x = 0` alone carries `-(1/h) ∑_{j=1}^{N} 1/j²`: after the
outer weight `h` it contributes `-∑ 1/j² ≈ -π²/6`, a standard amount sitting
in a single column of infinitesimal width. -/
theorem fubini_column_zero (h : K) (hh : h ≠ 0) (N : ℕ) :
    ∑ j ∈ range N, fubiniKernel h 0 (j + 1) * h
      = -(1 / h) * ∑ j ∈ range N, 1 / ((j : K) + 1) ^ 2 := by
  rw [mul_sum]
  refine sum_congr rfl (fun j _ => ?_)
  unfold fubiniKernel
  have hj : ((j : K) + 1) ≠ 0 := by positivity
  simp only [Nat.succ_ne_zero, and_false, ite_false, Nat.cast_zero, mul_zero]
  push_cast
  field_simp
  ring

/-! ## Fubini and the representation formula -/

omit [LinearOrder K] [IsStrictOrderedRing K] in
/-- Granular Fubini: iterated granular integrals over a box always agree. -/
theorem fubini_exact (g : ℕ → ℕ → K) (m n : ℕ) :
    ∑ i ∈ range m, ∑ j ∈ range n, g i j = ∑ j ∈ range n, ∑ i ∈ range m, g i j :=
  sum_comm

theorem lap_fsum (ε : K) {n : ℕ} {ι : Type*} (T : Finset ι) (F : ι → (Fin n → ℤ) → K)
    (x : Fin n → ℤ) :
    lap ε (fun y => ∑ s ∈ T, F s y) x = ∑ s ∈ T, lap ε (F s) x := by
  unfold lap
  rw [sum_comm]
  refine sum_congr rfl (fun i _ => ?_)
  rw [← sum_div]
  congr 1
  simp only [sum_add_distrib, sum_sub_distrib, mul_sum]

/-- Representation formula: `u = ∑_{s ∈ D} ρ(s) G_D(·, s) (2ε)ⁿ` solves the
Poisson problem `-Δ_ε u = ρ` on `D` (superposition of point-sphere charges). -/
theorem representation (ε : K) (hε : ε ≠ 0) {n : ℕ} (D : Finset (Fin n → ℤ))
    (G : (Fin n → ℤ) → (Fin n → ℤ) → K)
    (hG : ∀ s ∈ D, ∀ x ∈ D, -lap ε (G s) x = deltaN ε s x) (ρ : (Fin n → ℤ) → K) :
    ∀ x ∈ D, -lap ε (fun y => ∑ s ∈ D, ρ s * (2 * ε) ^ n * G s y) x = ρ x := by
  intro x hx
  have h2 : (2 * ε) ^ n ≠ 0 := pow_ne_zero _ (mul_ne_zero two_ne_zero hε)
  rw [lap_fsum ε D (fun s y => ρ s * (2 * ε) ^ n * G s y), ← sum_neg_distrib]
  have : ∀ s ∈ D, -lap ε (fun y => ρ s * (2 * ε) ^ n * G s y) x
      = ρ s * (2 * ε) ^ n * deltaN ε s x := by
    intro s hs
    rw [lap_smul, ← hG s hs x hx]; ring
  rw [sum_congr rfl this]
  unfold deltaN
  simp only [mul_ite, mul_zero]
  rw [sum_ite_eq D x]
  simp only [hx, ite_true]
  field_simp

/-- The Green's function of the one-point region `D = {s}` is explicit:
`G(s) = (2ε)² / ((2ε)ⁿ · 2n)`, showing that the lower bound of `green_props`
is attained. -/
theorem green_single (ε : K) (hε : ε ≠ 0) {n : ℕ} (hn : n ≠ 0) (s : Fin n → ℤ) :
    let G : (Fin n → ℤ) → K := fun x => if x = s then (2 * ε) ^ 2 / ((2 * ε) ^ n * (2 * n)) else 0;
    -lap ε G s = deltaN ε s s := by
  intro G
  have hp : ∀ i : Fin n, s + e i ≠ s := by
    intro i h
    have := congrFun h i
    simp [e] at this
  have hm : ∀ i : Fin n, s - e i ≠ s := by
    intro i h
    have := congrFun h i
    simp [e] at this
  rw [lap_eq]
  have hnb : nbr G s = 0 := by
    unfold nbr; simp [G, hp, hm]
  rw [hnb]
  simp only [G, deltaN, ite_true]
  have h2 : (2 * ε) ≠ 0 := mul_ne_zero two_ne_zero hε
  have hn' : (n : K) ≠ 0 := Nat.cast_ne_zero.mpr hn
  field_simp
  ring

end QE.Multi
