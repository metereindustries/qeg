-- SPDX-License-Identifier: MIT
-- Copyright 2026 Metere Industries, Inc. Author: Alfredo Metere.
-- Quasi-Euclidean Granular Geometry. Any derivative work must carry this notice:
--   This work is derivative of the Quasi-Euclidean Granular Geometry book
--   authored by Alfredo Metere. Copyright 2026 Metere Industries, Inc.
--   All rights reserved
-- See LICENSE.md and NOTICE.

import QuasiEuclidean.Basic
import QuasiEuclidean.Ch16b_Atom

/-!
# Chapter 16, section "Nonlocality, Decay and Determinism"

Bell–CHSH for local hidden-state models, the singlet value `2√2` and Tsirelson's bound
on `ℂ^m ⊗ ℂ^n`, no-signalling for density matrices, decay as counting (exact survival
law from the gaps of the decay set), granular quantum recurrence for the Cayley step,
isometry of linear evolution and nonlinearity of the Hartree map.  All state spaces are
finite.
-/

open Finset Matrix Complex
open scoped Kronecker

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace QE.Bell

open QE.Atom

/-! ## 1. Bell–CHSH for local granular models -/

/-- **CHSH on four signs.** -/
theorem chsh_signs {a0 a1 b0 b1 : ℝ} (ha0 : a0 = 1 ∨ a0 = -1) (ha1 : a1 = 1 ∨ a1 = -1)
    (hb0 : b0 = 1 ∨ b0 = -1) (hb1 : b1 = 1 ∨ b1 = -1) :
    a0 * b0 + a0 * b1 + a1 * b0 - a1 * b1 = 2 ∨ a0 * b0 + a0 * b1 + a1 * b0 - a1 * b1 = -2 := by
  rcases ha0 with rfl | rfl <;> rcases ha1 with rfl | rfl <;> rcases hb0 with rfl | rfl <;>
    rcases hb1 with rfl | rfl <;> norm_num

/-- CHSH for four numbers in `[-1,1]`. -/
lemma chsh_pointwise {a0 a1 b0 b1 : ℝ} (ha0 : |a0| ≤ 1) (ha1 : |a1| ≤ 1) (hb0 : |b0| ≤ 1)
    (hb1 : |b1| ≤ 1) : |a0 * b0 + a0 * b1 + a1 * b0 - a1 * b1| ≤ 2 := by
  have e : a0 * b0 + a0 * b1 + a1 * b0 - a1 * b1 = a0 * (b0 + b1) + a1 * (b0 - b1) := by ring
  rw [e]
  have h1 : |a0 * (b0 + b1)| ≤ |b0 + b1| := by
    rw [abs_mul]; exact mul_le_of_le_one_left (abs_nonneg _) ha0
  have h2 : |a1 * (b0 - b1)| ≤ |b0 - b1| := by
    rw [abs_mul]; exact mul_le_of_le_one_left (abs_nonneg _) ha1
  have h3 : |b0 + b1| + |b0 - b1| ≤ 2 := by
    rw [abs_le] at hb0 hb1
    rcases abs_cases (b0 + b1) with ⟨h, -⟩ | ⟨h, -⟩ <;>
      rcases abs_cases (b0 - b1) with ⟨h', -⟩ | ⟨h', -⟩ <;> rw [h, h'] <;> linarith
  calc |a0 * (b0 + b1) + a1 * (b0 - b1)| ≤ |a0 * (b0 + b1)| + |a1 * (b0 - b1)| := abs_add_le _ _
    _ ≤ 2 := by linarith

section Local

variable {Λ : Type*} [Fintype Λ]

/-- Correlation `E = ∑_λ w(λ) A(λ) B(λ)` of a local hidden-state model. -/
def corr (w : Λ → ℝ) (A B : Λ → ℝ) : ℝ := ∑ l, w l * A l * B l

/-- The CHSH combination `E₀₀ + E₀₁ + E₁₀ − E₁₁`. -/
def chshVal (w : Λ → ℝ) (A B : Fin 2 → Λ → ℝ) : ℝ :=
  corr w (A 0) (B 0) + corr w (A 0) (B 1) + corr w (A 1) (B 0) - corr w (A 1) (B 1)

/-- **Bell–CHSH inequality** for every finite hidden-state space with weights `w ≥ 0`,
`∑ w = 1`, and local responses with `|A|, |B| ≤ 1`. -/
theorem chsh_local (w : Λ → ℝ) (hw : ∀ l, 0 ≤ w l) (hsum : ∑ l, w l = 1)
    (A B : Fin 2 → Λ → ℝ) (hA : ∀ x l, |A x l| ≤ 1) (hB : ∀ y l, |B y l| ≤ 1) :
    |chshVal w A B| ≤ 2 := by
  have e : chshVal w A B = ∑ l, w l * (A 0 l * B 0 l + A 0 l * B 1 l + A 1 l * B 0 l -
      A 1 l * B 1 l) := by
    simp only [chshVal, corr, ← sum_add_distrib, ← sum_sub_distrib]
    refine sum_congr rfl fun l _ => by ring
  rw [e]
  calc |∑ l, w l * (A 0 l * B 0 l + A 0 l * B 1 l + A 1 l * B 0 l - A 1 l * B 1 l)|
      ≤ ∑ l, |w l * (A 0 l * B 0 l + A 0 l * B 1 l + A 1 l * B 0 l - A 1 l * B 1 l)| :=
        abs_sum_le_sum_abs _ _
    _ ≤ ∑ l, w l * 2 := by
        refine sum_le_sum fun l _ => ?_
        rw [abs_mul, abs_of_nonneg (hw l)]
        exact mul_le_mul_of_nonneg_left (chsh_pointwise (hA 0 l) (hA 1 l) (hB 0 l) (hB 1 l))
          (hw l)
    _ = 2 := by rw [← sum_mul, hsum, one_mul]

/-- **Deterministic ±1 responses** (counting measure is the case `w = 1/|Λ|`). -/
theorem chsh_deterministic (w : Λ → ℝ) (hw : ∀ l, 0 ≤ w l) (hsum : ∑ l, w l = 1)
    (A B : Fin 2 → Λ → ℝ) (hA : ∀ x l, A x l = 1 ∨ A x l = -1)
    (hB : ∀ y l, B y l = 1 ∨ B y l = -1) : |chshVal w A B| ≤ 2 := by
  refine chsh_local w hw hsum A B (fun x l => ?_) (fun y l => ?_)
  · rcases hA x l with h | h <;> simp [h]
  · rcases hB y l with h | h <;> simp [h]

/-- **Counting measure**: `|Λ|·|S| ≤ 2|Λ|` for uniform weights. -/
theorem chsh_counting [Nonempty Λ] (A B : Fin 2 → Λ → ℝ) (hA : ∀ x l, A x l = 1 ∨ A x l = -1)
    (hB : ∀ y l, B y l = 1 ∨ B y l = -1) :
    |chshVal (fun _ => (Fintype.card Λ : ℝ)⁻¹) A B| ≤ 2 := by
  refine chsh_deterministic _ (fun _ => by positivity) ?_ A B hA hB
  rw [sum_const, card_univ, nsmul_eq_mul]
  exact mul_inv_cancel₀ (by exact_mod_cast Fintype.card_ne_zero)

variable {Ωa Ωb : Type*} [Fintype Ωa] [Fintype Ωb]

/-- Correlation of a **stochastic** local model: given the hidden state `λ` and the local
settings, each side draws its own local randomness (`p`, `q`, which may depend on the
local setting and on `λ`) and answers `a`, `b`. -/
def corrSto (w : Λ → ℝ) (p : Λ → Ωa → ℝ) (q : Λ → Ωb → ℝ) (a : Λ → Ωa → ℝ)
    (b : Λ → Ωb → ℝ) : ℝ :=
  ∑ l, ∑ α, ∑ β, w l * p l α * q l β * a l α * b l β

lemma corrSto_eq (w : Λ → ℝ) (p : Λ → Ωa → ℝ) (q : Λ → Ωb → ℝ) (a : Λ → Ωa → ℝ)
    (b : Λ → Ωb → ℝ) :
    corrSto w p q a b = corr w (fun l => ∑ α, p l α * a l α) (fun l => ∑ β, q l β * b l β) := by
  unfold corrSto corr
  refine sum_congr rfl fun l _ => ?_
  rw [mul_assoc, sum_mul_sum, mul_sum]
  refine sum_congr rfl fun α _ => ?_
  rw [mul_sum]; refine sum_congr rfl fun β _ => by ring

lemma avg_abs_le {Ω : Type*} [Fintype Ω] (p : Ω → ℝ) (hp : ∀ α, 0 ≤ p α) (hs : ∑ α, p α = 1)
    (a : Ω → ℝ) (ha : ∀ α, |a α| ≤ 1) : |∑ α, p α * a α| ≤ 1 := by
  calc |∑ α, p α * a α| ≤ ∑ α, |p α * a α| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ α, p α := sum_le_sum fun α _ => by
        rw [abs_mul, abs_of_nonneg (hp α)]; exact mul_le_of_le_one_right (hp α) (ha α)
    _ = 1 := hs

/-- **Stochastic local responses reduce to the deterministic bound.** -/
theorem chsh_stochastic (w : Λ → ℝ) (hw : ∀ l, 0 ≤ w l) (hsum : ∑ l, w l = 1)
    (p : Fin 2 → Λ → Ωa → ℝ) (q : Fin 2 → Λ → Ωb → ℝ)
    (hp : ∀ x l α, 0 ≤ p x l α) (hps : ∀ x l, ∑ α, p x l α = 1)
    (hq : ∀ y l β, 0 ≤ q y l β) (hqs : ∀ y l, ∑ β, q y l β = 1)
    (a : Fin 2 → Λ → Ωa → ℝ) (b : Fin 2 → Λ → Ωb → ℝ)
    (ha : ∀ x l α, |a x l α| ≤ 1) (hb : ∀ y l β, |b y l β| ≤ 1) :
    |corrSto w (p 0) (q 0) (a 0) (b 0) + corrSto w (p 0) (q 1) (a 0) (b 1) +
      corrSto w (p 1) (q 0) (a 1) (b 0) - corrSto w (p 1) (q 1) (a 1) (b 1)| ≤ 2 := by
  simp only [corrSto_eq]
  exact chsh_local w hw hsum (fun x l => ∑ α, p x l α * a x l α)
    (fun y l => ∑ β, q y l β * b y l β)
    (fun x l => avg_abs_le _ (hp x l) (hps x l) _ (ha x l))
    (fun y l => avg_abs_le _ (hq y l) (hqs y l) _ (hb y l))

end Local

/-! ## Norms, Cauchy–Schwarz and the triangle inequality on `ℂ^ι` -/

section Norm

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The Euclidean norm `‖φ‖ = √(∑ |φ(x)|²)`. -/
noncomputable def nrm (φ : ι → ℂ) : ℝ := Real.sqrt (nsq φ)

lemma nrm_eq (φ : ι → ℂ) : nrm φ = ‖(WithLp.toLp 2 φ : EuclideanSpace ℂ ι)‖ := by
  rw [EuclideanSpace.norm_eq]; rfl

lemma nrm_nonneg (φ : ι → ℂ) : 0 ≤ nrm φ := Real.sqrt_nonneg _

lemma nrm_sq (φ : ι → ℂ) : nrm φ ^ 2 = nsq φ := Real.sq_sqrt (nsq_nonneg φ)

lemma nrm_add_le (u v : ι → ℂ) : nrm (u + v) ≤ nrm u + nrm v := by
  simp only [nrm_eq, WithLp.toLp_add]; exact norm_add_le _ _

lemma nrm_sub_le (u v : ι → ℂ) : nrm (u - v) ≤ nrm u + nrm v := by
  simp only [nrm_eq, WithLp.toLp_sub]; exact norm_sub_le _ _

/-- **Cauchy–Schwarz**: `|⟨u, v⟩| ≤ ‖u‖ ‖v‖`. -/
lemma cauchy_schwarz (u v : ι → ℂ) : ‖star u ⬝ᵥ v‖ ≤ nrm u * nrm v := by
  have h := norm_inner_le_norm (𝕜 := ℂ) (WithLp.toLp 2 u : EuclideanSpace ℂ ι)
    (WithLp.toLp 2 v)
  rw [EuclideanSpace.inner_toLp_toLp, dotProduct_comm] at h
  rw [nrm_eq, nrm_eq]; exact h

lemma nrm_unitary {U : Matrix ι ι ℂ} (hU : Uᴴ * U = 1) (v : ι → ℂ) :
    nrm (U *ᵥ v) = nrm v := by rw [nrm, nrm, unitary_nsq hU]

end Norm

/-! ## 2. The quantum value: singlet and Tsirelson's bound -/

section Tsirelson

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

lemma kron_sub (A : Matrix ι ι ℂ) (B C : Matrix κ κ ℂ) : A ⊗ₖ (B - C) = A ⊗ₖ B - A ⊗ₖ C := by
  ext ⟨i, k⟩ ⟨j, l⟩; simp [kroneckerMap_apply, mul_sub]

lemma sub_kron (A B : Matrix ι ι ℂ) (C : Matrix κ κ ℂ) : (A - B) ⊗ₖ C = A ⊗ₖ C - B ⊗ₖ C := by
  ext ⟨i, k⟩ ⟨j, l⟩; simp [kroneckerMap_apply, sub_mul]

/-- The CHSH operator `S = A₀⊗B₀ + A₀⊗B₁ + A₁⊗B₀ − A₁⊗B₁` on `ℂ^ι ⊗ ℂ^κ`. -/
def chshOp (A0 A1 : Matrix ι ι ℂ) (B0 B1 : Matrix κ κ ℂ) : Matrix (ι × κ) (ι × κ) ℂ :=
  A0 ⊗ₖ B0 + A0 ⊗ₖ B1 + A1 ⊗ₖ B0 - A1 ⊗ₖ B1

/-- **`S² = 4 − [A₀,A₁] ⊗ [B₀,B₁]`** when the four observables square to `1`. -/
theorem chshOp_sq {A0 A1 : Matrix ι ι ℂ} {B0 B1 : Matrix κ κ ℂ} (hA0 : A0 * A0 = 1)
    (hA1 : A1 * A1 = 1) (hB0 : B0 * B0 = 1) (hB1 : B1 * B1 = 1) :
    chshOp A0 A1 B0 B1 * chshOp A0 A1 B0 B1 =
      (4 : ℂ) • (1 : Matrix (ι × κ) (ι × κ) ℂ) - (A0 * A1 - A1 * A0) ⊗ₖ (B0 * B1 - B1 * B0) := by
  unfold chshOp
  simp only [add_mul, mul_add, sub_mul, mul_sub, ← mul_kronecker_mul, hA0, hA1, hB0, hB1,
    kronecker_add, add_kronecker, kron_sub, sub_kron]
  rw [← one_kronecker_one (α := ℂ) (m := ι) (n := κ)]
  module

lemma isHermitian_kronecker {A : Matrix ι ι ℂ} {B : Matrix κ κ ℂ} (hA : A.IsHermitian)
    (hB : B.IsHermitian) : (A ⊗ₖ B).IsHermitian := by
  unfold IsHermitian; rw [conjTranspose_kronecker, hA.eq, hB.eq]

lemma chshOp_isHermitian {A0 A1 : Matrix ι ι ℂ} {B0 B1 : Matrix κ κ ℂ} (hA0 : A0.IsHermitian)
    (hA1 : A1.IsHermitian) (hB0 : B0.IsHermitian) (hB1 : B1.IsHermitian) :
    (chshOp A0 A1 B0 B1).IsHermitian :=
  (((isHermitian_kronecker hA0 hB0).add (isHermitian_kronecker hA0 hB1)).add
    (isHermitian_kronecker hA1 hB0)).sub (isHermitian_kronecker hA1 hB1)

lemma unitary_kron_one {A : Matrix ι ι ℂ} (hA : Aᴴ * A = 1) :
    (A ⊗ₖ (1 : Matrix κ κ ℂ))ᴴ * (A ⊗ₖ (1 : Matrix κ κ ℂ)) = 1 := by
  rw [conjTranspose_kronecker, ← mul_kronecker_mul, hA, conjTranspose_one, one_mul,
    one_kronecker_one]

lemma unitary_one_kron {B : Matrix κ κ ℂ} (hB : Bᴴ * B = 1) :
    ((1 : Matrix ι ι ℂ) ⊗ₖ B)ᴴ * ((1 : Matrix ι ι ℂ) ⊗ₖ B) = 1 := by
  rw [conjTranspose_kronecker, ← mul_kronecker_mul, hB, conjTranspose_one, one_mul,
    one_kronecker_one]

/-- A Hermitian involution is unitary. -/
lemma herm_inv_unitary {A : Matrix ι ι ℂ} (hA : A.IsHermitian) (h2 : A * A = 1) :
    Aᴴ * A = 1 := by rw [hA.eq, h2]

/-- `‖[A₀,A₁]⊗1 φ‖ ≤ 2‖φ‖` for unitary `A₀, A₁`. -/
lemma comm_kron_one_le {A0 A1 : Matrix ι ι ℂ} (h0 : A0ᴴ * A0 = 1) (h1 : A1ᴴ * A1 = 1)
    (φ : ι × κ → ℂ) : nrm (((A0 * A1 - A1 * A0) ⊗ₖ (1 : Matrix κ κ ℂ)) *ᵥ φ) ≤ 2 * nrm φ := by
  have e : (A0 * A1 - A1 * A0) ⊗ₖ (1 : Matrix κ κ ℂ) =
      (A0 ⊗ₖ (1 : Matrix κ κ ℂ)) * (A1 ⊗ₖ 1) - (A1 ⊗ₖ 1) * (A0 ⊗ₖ 1) := by
    rw [← mul_kronecker_mul, ← mul_kronecker_mul, one_mul, sub_kron]
  rw [e, sub_mulVec, ← mulVec_mulVec, ← mulVec_mulVec]
  refine (nrm_sub_le _ _).trans ?_
  rw [nrm_unitary (unitary_kron_one h0), nrm_unitary (unitary_kron_one h1),
    nrm_unitary (unitary_kron_one h1), nrm_unitary (unitary_kron_one h0)]
  linarith

lemma one_kron_comm_le {B0 B1 : Matrix κ κ ℂ} (h0 : B0ᴴ * B0 = 1) (h1 : B1ᴴ * B1 = 1)
    (φ : ι × κ → ℂ) : nrm (((1 : Matrix ι ι ℂ) ⊗ₖ (B0 * B1 - B1 * B0)) *ᵥ φ) ≤ 2 * nrm φ := by
  have e : (1 : Matrix ι ι ℂ) ⊗ₖ (B0 * B1 - B1 * B0) =
      ((1 : Matrix ι ι ℂ) ⊗ₖ B0) * (1 ⊗ₖ B1) - (1 ⊗ₖ B1) * (1 ⊗ₖ B0) := by
    rw [← mul_kronecker_mul, ← mul_kronecker_mul, one_mul, kron_sub]
  rw [e, sub_mulVec, ← mulVec_mulVec, ← mulVec_mulVec]
  refine (nrm_sub_le _ _).trans ?_
  rw [nrm_unitary (unitary_one_kron h0), nrm_unitary (unitary_one_kron h1),
    nrm_unitary (unitary_one_kron h1), nrm_unitary (unitary_one_kron h0)]
  linarith

/-- **Tsirelson's bound** on `ℂ^ι ⊗ ℂ^κ`: for Hermitian `A_x, B_y` with `A_x² = B_y² = 1`,
`|⟨ψ, S ψ⟩| ≤ 2√2 ‖ψ‖²` for every `ψ`. -/
theorem tsirelson {A0 A1 : Matrix ι ι ℂ} {B0 B1 : Matrix κ κ ℂ}
    (hA0 : A0.IsHermitian) (hA1 : A1.IsHermitian) (hB0 : B0.IsHermitian) (hB1 : B1.IsHermitian)
    (sA0 : A0 * A0 = 1) (sA1 : A1 * A1 = 1) (sB0 : B0 * B0 = 1) (sB1 : B1 * B1 = 1)
    (ψ : ι × κ → ℂ) : ‖form (chshOp A0 A1 B0 B1) ψ‖ ≤ 2 * Real.sqrt 2 * nsq ψ := by
  set S := chshOp A0 A1 B0 B1
  set K := (A0 * A1 - A1 * A0) ⊗ₖ (B0 * B1 - B1 * B0)
  have hS := chshOp_isHermitian hA0 hA1 hB0 hB1
  -- ‖Kψ‖ ≤ 4‖ψ‖
  have hK : nrm (K *ᵥ ψ) ≤ 4 * nrm ψ := by
    have e : K = ((A0 * A1 - A1 * A0) ⊗ₖ (1 : Matrix κ κ ℂ)) *
        ((1 : Matrix ι ι ℂ) ⊗ₖ (B0 * B1 - B1 * B0)) := by
      rw [← mul_kronecker_mul, mul_one, one_mul]
    rw [e, ← mulVec_mulVec]
    refine (comm_kron_one_le (herm_inv_unitary hA0 sA0) (herm_inv_unitary hA1 sA1) _).trans ?_
    have := one_kron_comm_le (ι := ι) (herm_inv_unitary hB0 sB0) (herm_inv_unitary hB1 sB1) ψ
    linarith
  -- ‖Sψ‖² = ⟨ψ, S²ψ⟩ = 4‖ψ‖² − ⟨ψ, Kψ⟩
  have hSS : ((nsq (S *ᵥ ψ) : ℝ) : ℂ) = 4 * (nsq ψ : ℂ) - form K ψ := by
    rw [← star_dot_self, star_mulVec_dot, mulVec_mulVec, hS.eq, chshOp_sq sA0 sA1 sB0 sB1]
    simp only [sub_mulVec, smul_mulVec, one_mulVec, dotProduct_sub, dotProduct_smul,
      star_dot_self, smul_eq_mul]
    rfl
  have hle : nsq (S *ᵥ ψ) ≤ 8 * nsq ψ := by
    have h1 : nsq (S *ᵥ ψ) = 4 * nsq ψ - (form K ψ).re := by
      have := congrArg Complex.re hSS
      simpa using this
    have h2 : |(form K ψ).re| ≤ 4 * nsq ψ := by
      refine (Complex.abs_re_le_norm _).trans ?_
      refine (cauchy_schwarz ψ (K *ᵥ ψ)).trans ?_
      calc nrm ψ * nrm (K *ᵥ ψ) ≤ nrm ψ * (4 * nrm ψ) :=
            mul_le_mul_of_nonneg_left hK (nrm_nonneg ψ)
        _ = 4 * nsq ψ := by rw [← nrm_sq]; ring
    rw [h1]; linarith [neg_abs_le (form K ψ).re]
  have hCS : ‖form S ψ‖ ^ 2 ≤ 8 * nsq ψ ^ 2 := by
    have h := cauchy_schwarz ψ (S *ᵥ ψ)
    have h' : ‖form S ψ‖ ^ 2 ≤ (nrm ψ * nrm (S *ᵥ ψ)) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) h 2
    rw [mul_pow, nrm_sq, nrm_sq] at h'
    nlinarith [nsq_nonneg ψ]
  have h8 : (2 * Real.sqrt 2 * nsq ψ) ^ 2 = 8 * nsq ψ ^ 2 := by
    rw [mul_pow, mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]; ring
  have hnn : 0 ≤ 2 * Real.sqrt 2 * nsq ψ := by have := nsq_nonneg ψ; positivity
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) hnn (by norm_num : (2 : ℕ) ≠ 0)).mp
    (h8 ▸ hCS)

end Tsirelson

/-! ### The singlet attains `2√2` -/

section Singlet

/-- `c = 1/√2`. -/
noncomputable def cS : ℂ := ((Real.sqrt 2)⁻¹ : ℝ)

lemma cS_sq : cS * cS = 1 / 2 := by
  unfold cS
  rw [← ofReal_mul, ← mul_inv, Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  push_cast; ring

lemma star_cS : star cS = cS := by unfold cS; simp [Complex.star_def]

lemma conj_cS : (starRingEnd ℂ) cS = cS := by unfold cS; exact Complex.conj_ofReal _

/-- Pauli `σ_z`. -/
def sigZ : Matrix (Fin 2) (Fin 2) ℂ := !![1, 0; 0, -1]
/-- Pauli `σ_x`. -/
def sigX : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; 1, 0]
/-- `B₀ = −(σ_z + σ_x)/√2`. -/
noncomputable def obsB0 : Matrix (Fin 2) (Fin 2) ℂ := !![-cS, -cS; -cS, cS]
/-- `B₁ = (σ_x − σ_z)/√2`. -/
noncomputable def obsB1 : Matrix (Fin 2) (Fin 2) ℂ := !![-cS, cS; cS, cS]

/-- The singlet `(|01⟩ − |10⟩)/√2` on the four-point lattice `Fin 2 × Fin 2`. -/
noncomputable def singlet : Fin 2 × Fin 2 → ℂ := fun p =>
  if p = (0, 1) then cS else if p = (1, 0) then -cS else 0

lemma singlet_form (P Q : Matrix (Fin 2) (Fin 2) ℂ) :
    form (P ⊗ₖ Q) singlet =
      (1 / 2) * (P 0 0 * Q 1 1 - P 0 1 * Q 1 0 - P 1 0 * Q 0 1 + P 1 1 * Q 0 0) := by
  have h := cS_sq
  simp [form, singlet, dotProduct, mulVec, Fintype.sum_prod_type, Fin.sum_univ_two,
    kroneckerMap_apply, star_cS, conj_cS]
  linear_combination (P 0 0 * Q 1 1 - P 0 1 * Q 1 0 - P 1 0 * Q 0 1 + P 1 1 * Q 0 0) * h

lemma singlet_nsq : nsq singlet = 1 := by
  have h : ((nsq singlet : ℝ) : ℂ) = 1 := by
    rw [← star_dot_self]
    simp [singlet, dotProduct, Fintype.sum_prod_type, Fin.sum_univ_two, star_cS, conj_cS]
    linear_combination 2 * cS_sq
  exact_mod_cast h

lemma fin2_herm {a b c d : ℂ} (ha : star a = a) (hd : star d = d) (hb : star b = c)
    (hc : star c = b) : (!![a, b; c, d] : Matrix (Fin 2) (Fin 2) ℂ).IsHermitian := by
  unfold IsHermitian
  ext i j; fin_cases i <;> fin_cases j
  · simpa [conjTranspose_apply] using ha
  · simpa [conjTranspose_apply] using hc
  · simpa [conjTranspose_apply] using hb
  · simpa [conjTranspose_apply] using hd

lemma sq_fin2 {a b c d : ℂ} (h00 : a * a + b * c = 1) (h01 : a * b + b * d = 0)
    (h10 : c * a + d * c = 0) (h11 : c * b + d * d = 1) :
    (!![a, b; c, d] : Matrix (Fin 2) (Fin 2) ℂ) * !![a, b; c, d] = 1 := by
  rw [mul_fin_two, one_fin_two, h00, h01, h10, h11]

/-- **The four observables are Hermitian and square to `1`.** -/
theorem singlet_observables :
    sigZ.IsHermitian ∧ sigX.IsHermitian ∧ obsB0.IsHermitian ∧ obsB1.IsHermitian ∧
    sigZ * sigZ = 1 ∧ sigX * sigX = 1 ∧ obsB0 * obsB0 = 1 ∧ obsB1 * obsB1 = 1 := by
  have h := cS_sq
  have hn : star (-cS) = -cS := by rw [star_neg, star_cS]
  refine ⟨fin2_herm (by simp) (by simp) (by simp) (by simp),
    fin2_herm (by simp) (by simp) (by simp) (by simp),
    fin2_herm hn star_cS hn hn, fin2_herm hn star_cS star_cS star_cS, ?_, ?_, ?_, ?_⟩
  · exact sq_fin2 (by ring) (by ring) (by ring) (by ring)
  · exact sq_fin2 (by ring) (by ring) (by ring) (by ring)
  · exact sq_fin2 (by linear_combination 2 * h) (by ring) (by ring) (by linear_combination 2 * h)
  · exact sq_fin2 (by linear_combination 2 * h) (by ring) (by ring) (by linear_combination 2 * h)

/-- **The singlet value `S = 2√2`.** -/
theorem singlet_chsh : nsq singlet = 1 ∧
    form (chshOp sigZ sigX obsB0 obsB1) singlet = ((2 * Real.sqrt 2 : ℝ) : ℂ) := by
  refine ⟨singlet_nsq, ?_⟩
  unfold chshOp
  rw [form_sub, form_add, form_add, singlet_form, singlet_form, singlet_form, singlet_form]
  simp [sigZ, sigX, obsB0, obsB1]
  have h2 : (Real.sqrt 2 : ℂ) * Real.sqrt 2 = 2 := by
    rw [← ofReal_mul, Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 2)]; push_cast; ring
  have hc : cS * (Real.sqrt 2 : ℂ) = 1 := by
    unfold cS; rw [← ofReal_mul, inv_mul_cancel₀ (by positivity)]; simp
  linear_combination (2 * (Real.sqrt 2 : ℂ)) * hc - 2 * cS * h2

/-- **The singlet violates the local bound and saturates Tsirelson's bound.** -/
theorem singlet_violation :
    2 < (form (chshOp sigZ sigX obsB0 obsB1) singlet).re ∧
    ‖form (chshOp sigZ sigX obsB0 obsB1) singlet‖ = 2 * Real.sqrt 2 * nsq singlet := by
  obtain ⟨h1, h2⟩ := singlet_chsh
  rw [h2, h1, Complex.ofReal_re, Complex.norm_real, Real.norm_eq_abs, mul_one,
    abs_of_nonneg (by positivity)]
  refine ⟨?_, rfl⟩
  have : (1 : ℝ) < Real.sqrt 2 := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  linarith

end Singlet

/-! ## 3. No-signalling -/

section NoSignal

open scoped ComplexOrder

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]

lemma kron_sum (P : Matrix ι ι ℂ) (Q : β → Matrix κ κ ℂ) :
    ∑ b, P ⊗ₖ Q b = P ⊗ₖ ∑ b, Q b := by
  ext ⟨i, k⟩ ⟨j, l⟩; simp [kroneckerMap_apply, Matrix.sum_apply, mul_sum]

lemma sum_kron (P : α → Matrix ι ι ℂ) (Q : Matrix κ κ ℂ) :
    ∑ a, P a ⊗ₖ Q = (∑ a, P a) ⊗ₖ Q := by
  ext ⟨i, k⟩ ⟨j, l⟩; simp [kroneckerMap_apply, Matrix.sum_apply, sum_mul]

/-- **No-signalling.**  For every matrix `ρ` (in particular every density matrix), every
operator `P` on the first factor and two complete families `{Q_b}`, `{Q'_c}` on the second,
`∑_b Tr(ρ(P⊗Q_b)) = ∑_c Tr(ρ(P⊗Q'_c)) = Tr(ρ(P⊗1))`, and symmetrically. -/
theorem no_signalling (ρ : Matrix (ι × κ) (ι × κ) ℂ) (P : Matrix ι ι ℂ)
    (Q : β → Matrix κ κ ℂ) (Q' : γ → Matrix κ κ ℂ) (hQ : ∑ b, Q b = 1) (hQ' : ∑ c, Q' c = 1) :
    ∑ b, (ρ * (P ⊗ₖ Q b)).trace = (ρ * (P ⊗ₖ 1)).trace ∧
    ∑ c, (ρ * (P ⊗ₖ Q' c)).trace = (ρ * (P ⊗ₖ 1)).trace := by
  constructor
  · rw [← trace_sum, ← mul_sum, kron_sum, hQ]
  · rw [← trace_sum, ← mul_sum, kron_sum, hQ']

theorem no_signalling_left (ρ : Matrix (ι × κ) (ι × κ) ℂ) (Q : Matrix κ κ ℂ)
    (P : α → Matrix ι ι ℂ) (hP : ∑ a, P a = 1) :
    ∑ a, (ρ * (P a ⊗ₖ Q)).trace = (ρ * (1 ⊗ₖ Q)).trace := by
  rw [← trace_sum, ← mul_sum, sum_kron, hP]

/-- **The joint outcome probabilities form a probability distribution**: for `ρ ⪰ 0` and
projective measurements, `Tr(ρ(P_a⊗Q_b)) ≥ 0` and `∑_{a,b} Tr(ρ(P_a⊗Q_b)) = Tr ρ`. -/
theorem joint_prob (ρ : Matrix (ι × κ) (ι × κ) ℂ) (hρ : ρ.PosSemidef)
    (P : α → Matrix ι ι ℂ) (Q : β → Matrix κ κ ℂ)
    (hPh : ∀ a, (P a).IsHermitian) (hP2 : ∀ a, P a * P a = P a)
    (hQh : ∀ b, (Q b).IsHermitian) (hQ2 : ∀ b, Q b * Q b = Q b)
    (hP : ∑ a, P a = 1) (hQ : ∑ b, Q b = 1) :
    (∀ a b, 0 ≤ (ρ * (P a ⊗ₖ Q b)).trace) ∧
    ∑ a, ∑ b, (ρ * (P a ⊗ₖ Q b)).trace = ρ.trace := by
  constructor
  · intro a b
    set Pr := P a ⊗ₖ Q b
    have hPr : Prᴴ = Pr := isHermitian_kronecker (hPh a) (hQh b)
    have hPr2 : Pr * Pr = Pr := by
      simp only [Pr]; rw [← mul_kronecker_mul, hP2, hQ2]
    have e : (ρ * Pr).trace = (Prᴴ * ρ * Pr).trace := by
      rw [hPr, ← hPr2, ← Matrix.mul_assoc, trace_mul_comm, ← Matrix.mul_assoc, hPr2]
    rw [e]; exact (hρ.conjTranspose_mul_mul_same Pr).trace_nonneg
  · simp only [(no_signalling ρ _ Q Q hQ hQ).1]
    rw [no_signalling_left ρ 1 P hP, one_kronecker_one, Matrix.mul_one]

end NoSignal

/-! ## 4. Decay as counting -/

section Decay

variable {X : Type*} [Fintype X] [DecidableEq X] (T : Equiv.Perm X) (A : Finset X)

/-- Every state reaches the decay set. -/
def Reaches : Prop := ∀ x, ∃ n, (T ^ n) x ∈ A

lemma perm_pow_inv_apply (n : ℕ) (x : X) : (T ^ n) (((T⁻¹) ^ n) x) = x := by
  rw [← Equiv.Perm.mul_apply, inv_pow, mul_inv_cancel, Equiv.Perm.one_apply]

lemma inv_pow_pow_apply (n : ℕ) (x : X) : ((T⁻¹) ^ n) ((T ^ n) x) = x := by
  rw [← Equiv.Perm.mul_apply, inv_pow, inv_mul_cancel, Equiv.Perm.one_apply]

lemma inv_pow_sub (s t : ℕ) (x : X) (hs : s ≤ t) :
    ((T⁻¹) ^ s) ((T ^ t) x) = (T ^ (t - s)) x := by
  obtain ⟨r, rfl⟩ := Nat.exists_eq_add_of_le hs
  rw [pow_add, Equiv.Perm.mul_apply, inv_pow_pow_apply, Nat.add_sub_cancel_left]

variable {T A}

lemma back_exists (h : Reaches T A) (x : X) : ∃ s, ((T⁻¹) ^ (s + 1)) x ∈ A := by
  obtain ⟨n, hn⟩ := h x
  have ho : 0 < orderOf T := orderOf_pos T
  refine ⟨orderOf T * (n + 1) - n - 1, ?_⟩
  have hle : n + 1 ≤ orderOf T * (n + 1) := Nat.le_mul_of_pos_left _ ho
  have e : orderOf T * (n + 1) - n - 1 + 1 + n = orderOf T * (n + 1) := by omega
  have h1 : T ^ (orderOf T * (n + 1)) = 1 := by rw [pow_mul, pow_orderOf_eq_one, one_pow]
  have h2 : (T⁻¹) ^ (orderOf T * (n + 1) - n - 1 + 1) = T ^ n := by
    rw [inv_pow, inv_eq_iff_mul_eq_one, ← pow_add, e, h1]
  rw [h2]; exact hn

/-- First-entry (decay) time `τ(x) = min{t ≥ 0 : Tᵗx ∈ A}`. -/
noncomputable def tau (h : Reaches T A) (x : X) : ℕ := Nat.find (h x)

/-- The gap ending at `x`: `g(x) = min{s ≥ 1 : T⁻ˢx ∈ A}` (for `x ∈ A`, the distance back
to the previous decay state; the return time of `x` under `T⁻¹`). -/
noncomputable def gap (h : Reaches T A) (x : X) : ℕ := Nat.find (back_exists h x) + 1

/-- **Exactly `#{b ∈ A : g(b) > t}` states decay at time `t`.** -/
theorem card_tau_eq (h : Reaches T A) (t : ℕ) :
    (univ.filter fun x => tau h x = t).card = (A.filter fun b => t < gap h b).card := by
  refine Finset.card_bij' (fun x _ => (T ^ t) x) (fun b _ => ((T⁻¹) ^ t) b) ?_ ?_ ?_ ?_
  · intro x hx
    simp only [mem_filter, mem_univ, true_and] at hx ⊢
    have hA : (T ^ t) x ∈ A := hx ▸ Nat.find_spec (h x)
    refine ⟨hA, ?_⟩
    unfold gap
    rw [Nat.lt_add_one_iff, Nat.le_find_iff]
    intro m hm
    rw [inv_pow_sub T (m + 1) t x (by omega)]
    have : t - (m + 1) < tau h x := by rw [hx]; omega
    exact Nat.find_min (h x) this
  · intro b hb
    simp only [mem_filter, mem_univ, true_and] at hb ⊢
    obtain ⟨hbA, hg⟩ := hb
    unfold gap at hg
    rw [Nat.lt_add_one_iff, Nat.le_find_iff] at hg
    unfold tau
    rw [Nat.find_eq_iff]
    refine ⟨by rw [perm_pow_inv_apply]; exact hbA, fun n hn => ?_⟩
    have e : (T ^ n) (((T⁻¹) ^ t) b) = ((T⁻¹) ^ (t - n - 1 + 1)) b := by
      rw [show t - n - 1 + 1 = t - n by omega]
      obtain ⟨r, rfl⟩ := Nat.exists_eq_add_of_le hn.le
      rw [pow_add, Equiv.Perm.mul_apply, perm_pow_inv_apply, Nat.add_sub_cancel_left]
    rw [e]; exact hg _ (by omega)
  · intro x _; exact inv_pow_pow_apply T t x
  · intro b _; exact perm_pow_inv_apply T t b

lemma card_ge_fiber {α : Type*} (s : Finset α) (f : α → ℕ) (L t : ℕ)
    (hL : ∀ x ∈ s, f x < L) :
    (s.filter fun x => t ≤ f x).card =
      ∑ u ∈ (range L).filter (t ≤ ·), (s.filter fun x => f x = u).card := by
  rw [card_eq_sum_card_fiberwise (f := f) (t := (range L).filter (t ≤ ·))]
  · refine sum_congr rfl fun u hu => ?_
    congr 1; ext x; simp only [mem_filter]
    constructor
    · rintro ⟨⟨hx, _⟩, rfl⟩; exact ⟨hx, rfl⟩
    · rintro ⟨hx, rfl⟩; exact ⟨⟨hx, (mem_filter.mp hu).2⟩, rfl⟩
  · intro x hx
    simp only [coe_filter, Set.mem_ofPred_eq, mem_filter, mem_range] at hx ⊢
    exact ⟨hL x hx.1, hx.2⟩

lemma bounds (h : Reaches T A) :
    (∀ x ∈ (univ : Finset X), tau h x < univ.sup (tau h) + A.sup (gap h) + 1) ∧
    (∀ b ∈ A, gap h b ≤ univ.sup (tau h) + A.sup (gap h) + 1) := by
  constructor
  · intro x hx; have := le_sup (f := tau h) hx; omega
  · intro b hb; have := le_sup (f := gap h) hb; omega

/-- **Exact survival law.**  `#{x : τ(x) ≥ t} = ∑_{b ∈ A} (g(b) − t)₊`. -/
theorem survival (h : Reaches T A) (t : ℕ) :
    (univ.filter fun x => t ≤ tau h x).card = ∑ b ∈ A, (gap h b - t) := by
  obtain ⟨hτ, hg⟩ := bounds h
  set L := univ.sup (tau h) + A.sup (gap h) + 1
  rw [card_ge_fiber _ _ L t hτ]
  simp_rw [card_tau_eq h, card_filter]
  rw [sum_comm]
  refine sum_congr rfl fun b hb => ?_
  rw [← card_filter]
  have : ((range L).filter (t ≤ ·)).filter (fun u => u < gap h b) = Ico t (gap h b) := by
    ext u; simp only [mem_filter, mem_range, mem_Ico]
    have := hg b hb; omega
  rw [this, Nat.card_Ico]

/-- **Kac's lemma for the gaps** (the case `t = 0`): `∑_{b∈A} g(b) = |X|`. -/
theorem gap_sum (h : Reaches T A) : ∑ b ∈ A, gap h b = Fintype.card X := by
  calc ∑ b ∈ A, gap h b = ∑ b ∈ A, (gap h b - 0) := by simp
    _ = (univ.filter fun x => 0 ≤ tau h x).card := (survival h 0).symm
    _ = Fintype.card X := by simp

/-- **Mean decay time**: `2 ∑ₓ τ(x) = ∑_{b∈A} g(b)(g(b) − 1)`. -/
theorem tau_sum (h : Reaches T A) :
    (∑ x, tau h x) * 2 = ∑ b ∈ A, gap h b * (gap h b - 1) := by
  obtain ⟨hτ, hg⟩ := bounds h
  set L := univ.sup (tau h) + A.sup (gap h) + 1
  rw [← sum_fiberwise_of_maps_to (g := tau h) (t := range L)
    (fun x hx => mem_range.mpr (hτ x hx))]
  have e1 : ∀ u ∈ range L, ∑ x ∈ univ.filter (fun x => tau h x = u), tau h x =
      u * (A.filter fun b => u < gap h b).card := by
    intro u _
    rw [sum_congr rfl (fun x hx => (mem_filter.mp hx).2), sum_const, card_tau_eq h,
      smul_eq_mul, mul_comm]
  rw [sum_congr rfl e1]
  simp_rw [card_filter, mul_sum]
  rw [sum_comm, sum_mul]
  refine sum_congr rfl fun b hb => ?_
  rw [← sum_range_id_mul_two]
  congr 1
  simp_rw [mul_ite, mul_one, mul_zero]
  rw [← sum_filter]
  congr 1
  ext u; simp only [mem_filter, mem_range]
  have := hg b hb; omega

/-- **Equal gaps give the linear law.**  If every gap equals `g`, then
`#{τ ≥ t} = |A|(g − t)₊` and `|A| g = |X|`. -/
theorem survival_equal_gaps (h : Reaches T A) (g : ℕ) (hg : ∀ b ∈ A, gap h b = g) (t : ℕ) :
    (univ.filter fun x => t ≤ tau h x).card = A.card * (g - t) ∧
    A.card * g = Fintype.card X := by
  constructor
  · rw [survival h t, sum_congr rfl (fun b hb => by rw [hg b hb]), sum_const, smul_eq_mul]
  · rw [← gap_sum h, sum_congr rfl (fun b hb => hg b hb), sum_const, smul_eq_mul]

/-- The linear law as a survival fraction: `S(t) = (1 − t/g)₊`. -/
theorem linear_law (h : Reaches T A) (g : ℕ) (hg : ∀ b ∈ A, gap h b = g) (hg0 : 0 < g)
    (hA : 0 < A.card) (t : ℕ) :
    ((univ.filter fun x => t ≤ tau h x).card : ℝ) / Fintype.card X =
      max 0 (1 - (t : ℝ) / g) := by
  obtain ⟨h1, h2⟩ := survival_equal_gaps h g hg t
  rw [h1, ← h2]
  have hg' : (0 : ℝ) < g := by exact_mod_cast hg0
  have hA' : (0 : ℝ) < A.card := by exact_mod_cast hA
  rcases le_or_gt t g with ht | ht
  · rw [Nat.cast_mul, Nat.cast_mul, Nat.cast_sub ht]
    have : 0 ≤ 1 - (t : ℝ) / g := by
      rw [sub_nonneg, div_le_one hg']; exact_mod_cast ht
    rw [max_eq_right this]; field_simp
  · rw [Nat.sub_eq_zero_of_le ht.le]
    have : 1 - (t : ℝ) / g < 0 := by
      rw [sub_neg, one_lt_div hg']; exact_mod_cast ht
    rw [max_eq_left this.le]; simp

/-! ### The regular register: the rotation `x ↦ x + 1` on `ℤ/M` -/

section Rotation

variable {M : ℕ} [NeZero M]

/-- The rotation register. -/
def rot : Equiv.Perm (ZMod M) := Equiv.addRight 1

lemma rot_pow (n : ℕ) (x : ZMod M) : ((rot (M := M)) ^ n) x = x + n := by
  induction n generalizing x with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, Equiv.Perm.mul_apply, ih]
    simp [rot]; ring

lemma rot_inv_pow (n : ℕ) (x : ZMod M) : (((rot (M := M))⁻¹) ^ n) x = x - n := by
  have : x = ((rot (M := M)) ^ n) (x - n) := by rw [rot_pow]; ring
  conv_lhs => rw [this]
  exact inv_pow_pow_apply _ n _

/-- Decay set: the multiples of `g` (for `g ∣ M`), i.e. equally spaced decay states. -/
def evenSet (g : ℕ) (hd : g ∣ M) : Finset (ZMod M) :=
  univ.filter fun x => ZMod.castHom hd (ZMod g) x = 0

lemma rot_reaches (g : ℕ) (hd : g ∣ M) : Reaches (rot (M := M)) (evenSet g hd) := by
  intro x
  refine ⟨(-x).val, ?_⟩
  rw [rot_pow, ZMod.natCast_zmod_val, add_neg_cancel, evenSet, mem_filter]
  exact ⟨mem_univ _, map_zero _⟩

lemma rot_gap (g : ℕ) (hd : g ∣ M) (hg : 0 < g) (b : ZMod M) (hb : b ∈ evenSet g hd) :
    gap (rot_reaches g hd) b = g := by
  unfold gap
  have hb' : ZMod.castHom hd (ZMod g) b = 0 := (mem_filter.mp hb).2
  have key : ∀ s : ℕ, (((rot (M := M))⁻¹) ^ (s + 1)) b ∈ evenSet g hd ↔ g ∣ s + 1 := by
    intro s
    rw [rot_inv_pow, evenSet, mem_filter]
    simp only [mem_univ, true_and, map_sub, hb', map_natCast, zero_sub, neg_eq_zero]
    exact CharP.cast_eq_zero_iff (ZMod g) g (s + 1)
  have : Nat.find (back_exists (rot_reaches g hd) b) = g - 1 := by
    rw [Nat.find_eq_iff, key]
    refine ⟨by rw [Nat.sub_add_cancel hg], fun n hn => ?_⟩
    rw [key]; intro hdv
    have := Nat.le_of_dvd (by omega) hdv; omega
  rw [this]; omega

/-- **The regular register decays linearly.**  For the rotation of `ℤ/M` and the equally
spaced decay set of spacing `g ∣ M`: every gap is `g`, `#{τ ≥ t} = |A|(g − t)₊`,
`|A| g = M`, and `S(t) = (1 − t/g)₊`. -/
theorem rotation_linear (g : ℕ) (hd : g ∣ M) (hg : 0 < g) (t : ℕ) :
    (∀ b ∈ evenSet g hd, gap (rot_reaches g hd) b = g) ∧
    (univ.filter fun x => t ≤ tau (rot_reaches g hd) x).card =
      (evenSet g hd).card * (g - t) ∧
    (evenSet g hd).card * g = M ∧
    ((univ.filter fun x => t ≤ tau (rot_reaches g hd) x).card : ℝ) / M =
      max 0 (1 - (t : ℝ) / g) := by
  have hgap := rot_gap (M := M) g hd hg
  obtain ⟨h1, h2⟩ := survival_equal_gaps (rot_reaches g hd) g hgap t
  rw [ZMod.card] at h2
  have hA : 0 < (evenSet g hd).card := by
    rcases Nat.eq_zero_or_pos (evenSet g hd).card with h0 | h0
    · rw [h0, zero_mul] at h2; exact absurd h2.symm (NeZero.ne M)
    · exact h0
  have h4 := linear_law (rot_reaches g hd) g hgap hg hA t
  rw [ZMod.card] at h4
  exact ⟨hgap, h1, h2, h4⟩

end Rotation

/-! ### Reading the gap histogram off the decay curve; the geometric law -/

section Geometric

variable {ι : Type*} [DecidableEq ι] (s : Finset ι) (g : ι → ℕ)

/-- `F(t) = F(t+1) + #{gaps > t}`. -/
lemma surv_step (t : ℕ) :
    ∑ i ∈ s, (g i - t) = ∑ i ∈ s, (g i - (t + 1)) + (s.filter fun i => t < g i).card := by
  have key : ∀ n : ℕ, n - t = n - (t + 1) + (if t < n then 1 else 0) := by
    intro n
    by_cases h : t < n
    · rw [if_pos h]; omega
    · rw [if_neg h]; omega
  rw [card_filter, ← sum_add_distrib]
  refine sum_congr rfl fun i _ => ?_
  show g i - t = g i - (t + 1) + (if t < g i then 1 else 0)
  exact key (g i)

/-- `#{gaps > t} = #{gaps > t+1} + #{gaps = t+1}`. -/
lemma tail_step (t : ℕ) :
    (s.filter fun i => t < g i).card =
      (s.filter fun i => t + 1 < g i).card + (s.filter fun i => g i = t + 1).card := by
  rw [← card_union_of_disjoint]
  · congr 1; ext i; simp only [mem_filter, mem_union]
    constructor
    · rintro ⟨hi, h⟩
      rcases Nat.lt_or_ge (t + 1) (g i) with h' | h'
      · exact Or.inl ⟨hi, h'⟩
      · exact Or.inr ⟨hi, by omega⟩
    · rintro (⟨hi, h⟩ | ⟨hi, h⟩) <;> exact ⟨hi, by omega⟩
  · rw [disjoint_filter]; intro i _ h1 h2; omega

/-- The second difference of the survival count is the gap histogram:
`F(t) − 2F(t+1) + F(t+2) = #{gaps = t+1}` (written without subtraction). -/
theorem histogram_second_difference (t : ℕ) :
    ∑ i ∈ s, (g i - t) + ∑ i ∈ s, (g i - (t + 2)) =
      2 * ∑ i ∈ s, (g i - (t + 1)) + (s.filter fun i => g i = t + 1).card := by
  have h1 := surv_step s g t
  have h2 := surv_step s g (t + 1)
  have h3 := tail_step s g t
  rw [show t + 1 + 1 = t + 2 by ring] at h2
  omega

/-- **The exact geometric law on finite data.**  Let `0 ≤ q < 1`, `p = 1 − q`, `T ∈ ℕ`.
If exactly `k p q^{j−1}` gaps have length `j` for `1 ≤ j ≤ T`, and the gaps longer than `T`
number `k q^T` with total excess `∑ (g − T) = k q^T / p`, then for every `t ≤ T`
`#{τ ≥ t} = ∑ (g − t)₊ = (k/p) qᵗ`. -/
theorem geometric_law (T : ℕ) (k q : ℝ) (hq : q < 1)
    (hj : ∀ j, 1 ≤ j → j ≤ T → ((s.filter fun i => g i = j).card : ℝ) = k * (1 - q) * q ^ (j - 1))
    (htail : ((s.filter fun i => T < g i).card : ℝ) = k * q ^ T)
    (hexc : ((∑ i ∈ s.filter (fun i => T < g i), (g i - T) : ℕ) : ℝ) = k * q ^ T / (1 - q)) :
    ∀ t ≤ T, ((∑ i ∈ s, (g i - t) : ℕ) : ℝ) = k / (1 - q) * q ^ t := by
  have hp : (1 - q) ≠ 0 := by linarith
  -- the tail counts are geometric
  have hcount : ∀ d, d ≤ T → ((s.filter fun i => T - d < g i).card : ℝ) = k * q ^ (T - d) := by
    intro d
    induction d with
    | zero => intro _; simpa using htail
    | succ d ih =>
      intro hd
      have e := tail_step s g (T - (d + 1))
      rw [show T - (d + 1) + 1 = T - d by omega] at e
      rw [e]; push_cast
      rw [ih (by omega), hj (T - d) (by omega) (by omega),
        show T - d - 1 = T - (d + 1) by omega, show T - d = T - (d + 1) + 1 by omega, pow_succ]
      ring
  have hFT : ((∑ i ∈ s, (g i - T) : ℕ) : ℝ) = k * q ^ T / (1 - q) := by
    rw [← hexc, sum_filter]
    congr 1
    refine sum_congr rfl fun i _ => ?_
    split_ifs <;> omega
  have main : ∀ d, d ≤ T → ((∑ i ∈ s, (g i - (T - d)) : ℕ) : ℝ) = k / (1 - q) * q ^ (T - d) := by
    intro d
    induction d with
    | zero => intro _; simp only [Nat.sub_zero]; rw [hFT]; field_simp
    | succ d ih =>
      intro hd
      have e := surv_step s g (T - (d + 1))
      rw [show T - (d + 1) + 1 = T - d by omega] at e
      rw [e, Nat.cast_add, ih (by omega), hcount (d + 1) hd,
        show T - d = T - (d + 1) + 1 by omega, pow_succ]
      field_simp; ring
  intro t ht
  have := main (T - t) (by omega)
  rwa [show T - (T - t) = t by omega] at this

/-- **Half-life**: `q^{ln 2 / (−ln q)} = 1/2` for `0 < q < 1`. -/
theorem half_life (q : ℝ) (h0 : 0 < q) (h1 : q < 1) :
    q ^ (Real.log 2 / -Real.log q) = 1 / 2 := by
  have hl : Real.log q ≠ 0 := (Real.log_neg h0 h1).ne
  rw [Real.rpow_def_of_pos h0, show Real.log q * (Real.log 2 / -Real.log q) = -Real.log 2 by
    field_simp, Real.exp_neg, Real.exp_log (by norm_num)]
  norm_num

end Geometric

end Decay

/-! ## 5. Granular quantum recurrence -/

section Recurrence

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {A : Matrix ι ι ℂ}

/-- The eigenvalue `(1 − iλ)/(1 + iλ)` of the Cayley step. -/
noncomputable def cphase (l : ℝ) : ℂ := (1 - I * l) / (1 + I * l)

lemma one_add_I_mul_ne (l : ℝ) : (1 + I * l : ℂ) ≠ 0 := by
  intro h; have := congrArg Complex.re h; simp at this

lemma norm_cphase (l : ℝ) : ‖cphase l‖ = 1 := by
  unfold cphase
  rw [norm_div, div_eq_one_iff_eq (by simpa using one_add_I_mul_ne l)]
  have : (1 - I * l : ℂ) = (starRingEnd ℂ) (1 + I * l) := by simp [map_add, map_mul]; ring
  rw [this, Complex.norm_conj]

lemma cphase_mul (l : ℝ) : cphase l * (1 + I * l) = 1 - I * l := by
  unfold cphase; field_simp [one_add_I_mul_ne l]

/-- **The Cayley step in the eigenbasis**: `U = V diag((1 − iλⱼ)/(1 + iλⱼ)) V*`. -/
theorem cayley_spectral (hA : A.IsHermitian) :
    cayley A = (hA.eigenvectorUnitary : Matrix ι ι ℂ) *
      diagonal (fun j => cphase (hA.eigenvalues j)) * (hA.eigenvectorUnitary : Matrix ι ι ℂ)ᴴ := by
  set V := (hA.eigenvectorUnitary : Matrix ι ι ℂ)
  set Dl := diagonal (fun j => ((hA.eigenvalues j : ℝ) : ℂ))
  set Du := diagonal (fun j => cphase (hA.eigenvalues j))
  have hVV : Vᴴ * V = 1 := evU_star_mul hA
  have hVV' : V * Vᴴ = 1 := evU_mul_star hA
  have hVVY : ∀ Y : Matrix ι ι ℂ, Vᴴ * (V * Y) = Y := fun Y => by
    rw [← Matrix.mul_assoc, hVV, Matrix.one_mul]
  have hAV : A = V * Dl * Vᴴ := by
    conv_lhs => rw [hA.spectral_theorem, Unitary.conjStarAlgAut_apply]
    rw [star_eq_conjTranspose]; rfl
  have key : Du + I • (Dl * Du) = 1 - I • Dl := by
    simp only [Du, Dl, diagonal_mul_diagonal]
    ext i j
    by_cases hij : i = j
    · subst hij
      simp [diagonal_apply, one_apply]
      have := cphase_mul (hA.eigenvalues i)
      linear_combination this
    · simp [diagonal_apply, one_apply, hij]
  have lhs : (1 + I • A) * (V * Du * Vᴴ) = V * (Du + I • (Dl * Du)) * Vᴴ := by
    rw [hAV]
    simp only [Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul,
      Matrix.mul_assoc, Matrix.one_mul, hVVY]
  have rhs : 1 - I • A = V * (1 - I • Dl) * Vᴴ := by
    rw [hAV]
    simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.smul_mul, Matrix.mul_smul,
      Matrix.mul_assoc, Matrix.mul_one, hVV']
  exact (cayley_unitary hA).1.mul_left_cancel (by rw [cayley_step hA, lhs, key, ← rhs])

lemma cayley_pow_spectral (hA : A.IsHermitian) (t : ℕ) :
    cayley A ^ t = (hA.eigenvectorUnitary : Matrix ι ι ℂ) *
      diagonal (fun j => cphase (hA.eigenvalues j) ^ t) *
        (hA.eigenvectorUnitary : Matrix ι ι ℂ)ᴴ := by
  set V := (hA.eigenvectorUnitary : Matrix ι ι ℂ)
  have hVV : Vᴴ * V = 1 := evU_star_mul hA
  have hVV' : V * Vᴴ = 1 := evU_mul_star hA
  induction t with
  | zero => simp [hVV']
  | succ t ih =>
    rw [pow_succ, ih, cayley_spectral hA]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc Vᴴ V, hVV, Matrix.one_mul, ← Matrix.mul_assoc (diagonal _),
      diagonal_mul_diagonal]
    simp only [pow_succ]
    rfl

/-- Box index of a point of the unit circle on a grid of `N` arcs. -/
noncomputable def box (N : ℕ) (z : ℂ) : ℕ :=
  min ⌊(Complex.arg z + Real.pi) / (2 * Real.pi) * N⌋₊ (N - 1)

lemma box_lt (N : ℕ) (hN : 1 ≤ N) (z : ℂ) : box N z < N := by
  unfold box; omega

lemma frac_bounds (N : ℕ) (z : ℂ) :
    0 ≤ (Complex.arg z + Real.pi) / (2 * Real.pi) * N ∧
      (Complex.arg z + Real.pi) / (2 * Real.pi) * N ≤ N := by
  have h1 := Complex.neg_pi_lt_arg z
  have h2 := Complex.arg_le_pi z
  have hpi := Real.pi_pos
  have hN : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  constructor
  · apply mul_nonneg _ hN; apply div_nonneg <;> linarith
  · have : (Complex.arg z + Real.pi) / (2 * Real.pi) ≤ 1 := by
      rw [div_le_one (by positivity)]; linarith
    calc (Complex.arg z + Real.pi) / (2 * Real.pi) * N ≤ 1 * N :=
          mul_le_mul_of_nonneg_right this hN
      _ = N := one_mul _

lemma same_box_close (N : ℕ) (hN : 1 ≤ N) (x y : ℝ) (hx0 : 0 ≤ x) (hxN : x ≤ N)
    (hy0 : 0 ≤ y) (hyN : y ≤ N) (h : min ⌊x⌋₊ (N - 1) = min ⌊y⌋₊ (N - 1)) : |x - y| ≤ 1 := by
  have ax := Nat.floor_le hx0
  have bx := Nat.lt_floor_add_one x
  have ay := Nat.floor_le hy0
  have by' := Nat.lt_floor_add_one y
  have hN1 : ((N - 1 : ℕ) : ℝ) = (N : ℝ) - 1 := by rw [Nat.cast_sub hN]; simp
  rw [abs_le]
  rcases le_or_gt (N - 1) ⌊x⌋₊ with hx | hx <;> rcases le_or_gt (N - 1) ⌊y⌋₊ with hy | hy
  · have hx' : ((N - 1 : ℕ) : ℝ) ≤ ⌊x⌋₊ := by exact_mod_cast hx
    have hy' : ((N - 1 : ℕ) : ℝ) ≤ ⌊y⌋₊ := by exact_mod_cast hy
    constructor <;> linarith
  · rw [min_eq_right hx, min_eq_left hy.le] at h; omega
  · rw [min_eq_left hx.le, min_eq_right hy] at h; omega
  · rw [min_eq_left hx.le, min_eq_left hy.le] at h
    rw [h] at ax bx
    constructor <;> linarith

lemma unit_close (N : ℕ) (hN : 1 ≤ N) (z w : ℂ) (hz : ‖z‖ = 1) (hw : ‖w‖ = 1)
    (h : box N z = box N w) : ‖z - w‖ ≤ 2 * Real.pi / N := by
  have hpi := Real.pi_pos
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  obtain ⟨hx0, hxN⟩ := frac_bounds N z
  obtain ⟨hy0, hyN⟩ := frac_bounds N w
  have hc := same_box_close N hN _ _ hx0 hxN hy0 hyN h
  have harg : |Complex.arg z - Complex.arg w| ≤ 2 * Real.pi / N := by
    have e : (Complex.arg z + Real.pi) / (2 * Real.pi) * N -
        (Complex.arg w + Real.pi) / (2 * Real.pi) * N =
        (Complex.arg z - Complex.arg w) * (N / (2 * Real.pi)) := by field_simp; ring
    have hNp : (0 : ℝ) < N / (2 * Real.pi) := div_pos hNr (by positivity)
    rw [e, abs_mul, abs_of_pos hNp] at hc
    rw [le_div_iff₀ hNr]
    calc |Complex.arg z - Complex.arg w| * N
        = |Complex.arg z - Complex.arg w| * (N / (2 * Real.pi)) * (2 * Real.pi) := by
          rw [mul_assoc, div_mul_cancel₀ _ (by positivity)]
      _ ≤ 1 * (2 * Real.pi) := by gcongr
      _ = 2 * Real.pi := one_mul _
  have ez : z = Complex.exp (Complex.arg z * I) := by
    conv_lhs => rw [← norm_mul_exp_arg_mul_I z]
    rw [hz]; simp
  have ew : w = Complex.exp (Complex.arg w * I) := by
    conv_lhs => rw [← norm_mul_exp_arg_mul_I w]
    rw [hw]; simp
  have : z - w = Complex.exp (Complex.arg w * I) *
      (Complex.exp (I * ((Complex.arg z - Complex.arg w : ℝ) : ℂ)) - 1) := by
    rw [mul_sub, ← Complex.exp_add, mul_one]
    conv_lhs => rw [ez, ew]
    congr 2; push_cast; ring
  rw [this, norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul]
  refine (Real.norm_exp_I_mul_ofReal_sub_one_le).trans ?_
  rw [Real.norm_eq_abs]; exact harg

/-- **Granular quantum recurrence.**  For every Hermitian `A` on `ℂ^d` and every `N ≥ 1`
there is a time `1 ≤ t ≤ N^d` with `‖Uᵗψ − ψ‖² ≤ (2π/N)² ‖ψ‖²` for **every** `ψ`,
where `U` is the Cayley step of `A`. -/
theorem recurrence (hA : A.IsHermitian) (N : ℕ) (hN : 1 ≤ N) :
    ∃ t : ℕ, 1 ≤ t ∧ t ≤ N ^ Fintype.card ι ∧
      ∀ ψ : ι → ℂ, nsq ((cayley A ^ t) *ᵥ ψ - ψ) ≤ (2 * Real.pi / N) ^ 2 * nsq ψ := by
  let F : Fin (N ^ Fintype.card ι + 1) → (ι → Fin N) :=
    fun t j => ⟨box N (cphase (hA.eigenvalues j) ^ (t : ℕ)), box_lt N hN _⟩
  have hcard : Fintype.card (ι → Fin N) < Fintype.card (Fin (N ^ Fintype.card ι + 1)) := by
    simp
  obtain ⟨t1, t2, hne, heq⟩ := Fintype.exists_ne_map_eq_of_card_lt F hcard
  -- WLOG t1 < t2
  have hboth : ∀ a b : Fin (N ^ Fintype.card ι + 1), a < b → F a = F b →
      ∃ t : ℕ, 1 ≤ t ∧ t ≤ N ^ Fintype.card ι ∧
        ∀ j, ‖cphase (hA.eigenvalues j) ^ t - 1‖ ≤ 2 * Real.pi / N := by
    intro a b hab hF
    refine ⟨(b : ℕ) - a, by omega, by omega, fun j => ?_⟩
    have hj := congrArg (fun f => (f j : ℕ)) hF
    simp only [F] at hj
    have hu : ‖cphase (hA.eigenvalues j)‖ = 1 := norm_cphase _
    have hclose := unit_close N hN _ _ (by rw [norm_pow, hu, one_pow])
      (by rw [norm_pow, hu, one_pow]) hj.symm
    have e : cphase (hA.eigenvalues j) ^ (b : ℕ) - cphase (hA.eigenvalues j) ^ (a : ℕ) = cphase (hA.eigenvalues j) ^ (a : ℕ) * (cphase (hA.eigenvalues j) ^ ((b : ℕ) - a) - 1) := by
      rw [mul_sub, ← pow_add, Nat.add_sub_cancel' hab.le, mul_one]
    rw [e, norm_mul, norm_pow, hu, one_pow, one_mul] at hclose
    exact hclose
  obtain ⟨t, ht1, htN, hu⟩ : ∃ t : ℕ, 1 ≤ t ∧ t ≤ N ^ Fintype.card ι ∧
      ∀ j, ‖cphase (hA.eigenvalues j) ^ t - 1‖ ≤ 2 * Real.pi / N := by
    rcases lt_or_gt_of_ne hne with h | h
    · exact hboth t1 t2 h heq
    · exact hboth t2 t1 h heq.symm
  refine ⟨t, ht1, htN, fun ψ => ?_⟩
  have hVV' := evU_mul_star hA
  have hψ : ψ = (hA.eigenvectorUnitary : Matrix ι ι ℂ) *ᵥ
      ((hA.eigenvectorUnitary : Matrix ι ι ℂ)ᴴ *ᵥ ψ) := by
    rw [mulVec_mulVec, hVV', one_mulVec]
  have hD : diagonal (fun j => cphase (hA.eigenvalues j) ^ t - 1) =
      diagonal (fun j => cphase (hA.eigenvalues j) ^ t) - 1 := by
    rw [← diagonal_one, ← diagonal_sub]
  have e : (cayley A ^ t) *ᵥ ψ - ψ = (hA.eigenvectorUnitary : Matrix ι ι ℂ) *ᵥ
      (diagonal (fun j => cphase (hA.eigenvalues j) ^ t - 1) *ᵥ
        ((hA.eigenvectorUnitary : Matrix ι ι ℂ)ᴴ *ᵥ ψ)) := by
    rw [cayley_pow_spectral hA t, hD, sub_mulVec, mulVec_sub, one_mulVec, ← mulVec_mulVec,
      ← mulVec_mulVec, ← hψ]
  rw [e, unitary_nsq (evU_star_mul hA), spectral_nsq hA ψ, mul_sum]
  unfold nsq
  refine sum_le_sum fun j _ => ?_
  rw [mulVec_diagonal, norm_mul, mul_pow]
  have := hu j
  have h0 : 0 ≤ ‖cphase (hA.eigenvalues j) ^ t - 1‖ := norm_nonneg _
  exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ h0 this 2) (by positivity)

/-- **The survival amplitude returns**: `|⟨ψ, Uᵗψ⟩ − ‖ψ‖²| ≤ (2π/N)‖ψ‖²`. -/
theorem recurrence_amplitude (hA : A.IsHermitian) (N : ℕ) (hN : 1 ≤ N) :
    ∃ t : ℕ, 1 ≤ t ∧ t ≤ N ^ Fintype.card ι ∧
      ∀ ψ : ι → ℂ, ‖star ψ ⬝ᵥ ((cayley A ^ t) *ᵥ ψ) - (nsq ψ : ℂ)‖ ≤
        2 * Real.pi / N * nsq ψ := by
  obtain ⟨t, h1, h2, h⟩ := recurrence hA N hN
  refine ⟨t, h1, h2, fun ψ => ?_⟩
  have hc : 0 ≤ 2 * Real.pi / N := by positivity
  rw [← star_dot_self, ← dotProduct_sub]
  refine (cauchy_schwarz ψ _).trans ?_
  have hn : nrm ((cayley A ^ t) *ᵥ ψ - ψ) ≤ 2 * Real.pi / N * nrm ψ := by
    unfold nrm
    rw [← Real.sqrt_sq hc, ← Real.sqrt_mul (sq_nonneg _)]
    exact Real.sqrt_le_sqrt (h ψ)
  calc nrm ψ * nrm ((cayley A ^ t) *ᵥ ψ - ψ) ≤ nrm ψ * (2 * Real.pi / N * nrm ψ) :=
        mul_le_mul_of_nonneg_left hn (nrm_nonneg ψ)
    _ = 2 * Real.pi / N * nsq ψ := by rw [← nrm_sq]; ring

end Recurrence

/-! ## 6. Linear in the state: isometry, zero Lyapunov exponent; the Hartree map -/

section Linear

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {A : Matrix ι ι ℂ}

lemma unitary_pow {U : Matrix ι ι ℂ} (hU : Uᴴ * U = 1) (t : ℕ) : (U ^ t)ᴴ * U ^ t = 1 := by
  induction t with
  | zero => simp
  | succ t ih =>
    rw [pow_succ, conjTranspose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc ((U ^ t)ᴴ), ih,
      Matrix.one_mul, hU]

/-- **Exact evolution is an isometry**: `‖Uᵗψ − Uᵗφ‖ = ‖ψ − φ‖` for all states and all
`t`, for every Hermitian `A` on every finite configuration space. -/
theorem evolution_isometry (hA : A.IsHermitian) (ψ φ : ι → ℂ) (t : ℕ) :
    nrm ((cayley A ^ t) *ᵥ ψ - (cayley A ^ t) *ᵥ φ) = nrm (ψ - φ) := by
  rw [← mulVec_sub, nrm_unitary (unitary_pow (cayley_unitary hA).2.1 t)]

/-- **The Hilbert-space Lyapunov exponent is exactly zero**:
`(1/t) log(‖Uᵗψ − Uᵗφ‖/‖ψ − φ‖) = 0` for all `ψ, φ` and all `t`. -/
theorem lyapunov_zero (hA : A.IsHermitian) (ψ φ : ι → ℂ) (t : ℕ) :
    (1 / (t : ℝ)) * Real.log (nrm ((cayley A ^ t) *ᵥ ψ - (cayley A ^ t) *ᵥ φ) / nrm (ψ - φ))
      = 0 := by
  rw [evolution_isometry hA]
  by_cases h : nrm (ψ - φ) = 0
  · simp [h]
  · simp [div_self h]

variable {Γ : Type*} [Fintype Γ] [DecidableEq Γ] [AddCommGroup Γ]

/-- Hartree mean field `m_φ(x) = ∑_y V(x − y) |φ(y)|²`. -/
noncomputable def meanField (V : Γ → ℝ) (φ : Γ → ℂ) (x : Γ) : ℝ := ∑ y, V (x - y) * ‖φ y‖ ^ 2

/-- The Hartree one-body Hamiltonian `h[φ] = h₀ + m_φ`. -/
noncomputable def hartreeH (h0 : Matrix Γ Γ ℂ) (V : Γ → ℝ) (φ : Γ → ℂ) : Matrix Γ Γ ℂ :=
  h0 + diagonal (fun x => (meanField V φ x : ℂ))

/-- The Hartree vector field `φ ↦ h[φ] φ`. -/
noncomputable def hartreeF (h0 : Matrix Γ Γ ℂ) (V : Γ → ℝ) (φ : Γ → ℂ) : Γ → ℂ :=
  hartreeH h0 V φ *ᵥ φ

lemma meanField_smul (V : Γ → ℝ) (c : ℂ) (φ : Γ → ℂ) (x : Γ) :
    meanField V (c • φ) x = ‖c‖ ^ 2 * meanField V φ x := by
  unfold meanField; rw [mul_sum]
  refine sum_congr rfl fun y _ => ?_
  simp [norm_mul, mul_pow]; ring

/-- **The Hartree field is cubic**: `F(cφ) = c h₀φ + c|c|² m_φ φ`. -/
theorem hartree_cubic (h0 : Matrix Γ Γ ℂ) (V : Γ → ℝ) (c : ℂ) (φ : Γ → ℂ) :
    hartreeF h0 V (c • φ) =
      c • (h0 *ᵥ φ) + (c * ((‖c‖ ^ 2 : ℝ) : ℂ)) • (diagonal (fun x => (meanField V φ x : ℂ)) *ᵥ φ) := by
  ext x
  simp only [hartreeF, hartreeH, add_mulVec, mulVec_smul, Pi.add_apply, Pi.smul_apply,
    mulVec_diagonal, meanField_smul, smul_eq_mul]
  push_cast; ring

lemma meanField_single (V : Γ → ℝ) (x : Γ) (c : ℂ) :
    meanField V (Pi.single x c) x = V 0 * ‖c‖ ^ 2 := by
  unfold meanField
  rw [sum_eq_single x]
  · simp
  · intro y _ hy; simp [Pi.single_apply, hy]
  · simp

/-- **The Hartree map is not additive**: if `V(0) ≠ 0`, then for `φ₁ = φ₂ = δₓ`,
`F(φ₁ + φ₂) ≠ F(φ₁) + F(φ₂)`. -/
theorem hartree_not_additive (h0 : Matrix Γ Γ ℂ) (V : Γ → ℝ) (hV : V 0 ≠ 0) (x : Γ) :
    hartreeF h0 V (Pi.single x 1 + Pi.single x 1) ≠
      hartreeF h0 V (Pi.single x 1) + hartreeF h0 V (Pi.single x 1) := by
  intro heq
  have e2 : (Pi.single x (1 : ℂ) + Pi.single x 1 : Γ → ℂ) = (2 : ℂ) • Pi.single x 1 := by
    rw [two_smul]
  have e1 : (Pi.single x (1 : ℂ) : Γ → ℂ) = (1 : ℂ) • Pi.single x 1 := by rw [one_smul]
  rw [e2] at heq
  conv_rhs at heq => rw [e1]
  rw [hartree_cubic, hartree_cubic] at heq
  have hx := congrFun heq x
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, mulVec_diagonal, meanField_single,
    Pi.single_eq_same] at hx
  have : ((V 0 : ℝ) : ℂ) = 0 := by
    norm_num at hx
    linear_combination hx / 6
  exact hV (by exact_mod_cast this)

/-- The Hartree step with the hopping switched off: the Cayley step of `(τ/2) m_φ`. -/
noncomputable def hartreeStep0 (τ : ℝ) (V : Γ → ℝ) (φ : Γ → ℂ) : Γ → ℂ :=
  cayley (diagonal fun x => ((τ / 2 * meanField V φ x : ℝ) : ℂ)) *ᵥ φ

lemma cayley_diagonal (d : Γ → ℝ) :
    cayley (diagonal fun x => ((d x : ℝ) : ℂ)) = diagonal fun x => cphase (d x) := by
  have hH : (diagonal fun x => ((d x : ℝ) : ℂ)).IsHermitian := by
    unfold IsHermitian; ext i j
    by_cases h : i = j
    · subst h; simp [conjTranspose_apply]
    · simp [conjTranspose_apply, diagonal_apply, h, Ne.symm h]
  have e1 : (1 : Matrix Γ Γ ℂ) + I • diagonal (fun x => ((d x : ℝ) : ℂ)) =
      diagonal (fun x => 1 + I * d x) := by
    ext i j; by_cases h : i = j
    · subst h; simp [diagonal_apply, one_apply]
    · simp [diagonal_apply, one_apply, h]
  have e2 : (1 : Matrix Γ Γ ℂ) - I • diagonal (fun x => ((d x : ℝ) : ℂ)) =
      diagonal (fun x => 1 - I * d x) := by
    ext i j; by_cases h : i = j
    · subst h; simp [diagonal_apply, one_apply]
    · simp [diagonal_apply, one_apply, h]
  refine (cayley_unitary hH).1.mul_left_cancel ?_
  rw [cayley_step hH, e1, e2, diagonal_mul_diagonal]
  congr 1; funext x
  have := cphase_mul (d x)
  linear_combination (-1 : ℂ) * this

lemma cphase_ne (a k : ℝ) (ha : a ≠ 0) (hk : k ≠ 1) : cphase (k * a) ≠ cphase a := by
  intro h
  unfold cphase at h
  rw [div_eq_div_iff (one_add_I_mul_ne _) (one_add_I_mul_ne _)] at h
  have him := congrArg Complex.im h
  simp [Complex.mul_im, Complex.mul_re] at him
  have : a * (1 - k) = 0 := by linarith
  rcases mul_eq_zero.mp this with h1 | h1
  · exact ha h1
  · exact hk (by linarith)

/-- **The Hartree step is not additive**: for `τ ≠ 0`, `V(0) ≠ 0`, and `φ₁ = φ₂ = δₓ`,
the step of `φ₁ + φ₂` differs from the sum of the steps. -/
theorem hartree_step_not_additive (τ : ℝ) (hτ : τ ≠ 0) (V : Γ → ℝ) (hV : V 0 ≠ 0) (x : Γ) :
    hartreeStep0 τ V (Pi.single x 1 + Pi.single x 1) ≠
      hartreeStep0 τ V (Pi.single x 1) + hartreeStep0 τ V (Pi.single x 1) := by
  have key : ∀ c : ℂ, hartreeStep0 τ V (Pi.single x c) x =
      cphase (τ / 2 * (V 0 * ‖c‖ ^ 2)) * c := by
    intro c
    simp only [hartreeStep0, cayley_diagonal, mulVec_diagonal, meanField_single,
      Pi.single_eq_same]
  have ha : τ / 2 * V 0 ≠ 0 := mul_ne_zero (div_ne_zero hτ two_ne_zero) hV
  intro heq
  have hx := congrFun heq x
  rw [← Pi.single_add, Pi.add_apply, key, key] at hx
  have h2 : ‖(1 + 1 : ℂ)‖ ^ 2 = 4 := by norm_num
  rw [h2, norm_one, one_pow, mul_one, mul_one] at hx
  apply cphase_ne (τ / 2 * V 0) 4 ha (by norm_num)
  rw [show (4 : ℝ) * (τ / 2 * V 0) = τ / 2 * (V 0 * 4) by ring]
  linear_combination hx / 2

end Linear

end QE.Bell
