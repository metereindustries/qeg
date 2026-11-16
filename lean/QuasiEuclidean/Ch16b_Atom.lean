-- SPDX-License-Identifier: MIT
-- Copyright 2026 Metere Industries, Inc. Author: Alfredo Metere.
-- Quasi-Euclidean Granular Geometry. Any derivative work must carry this notice:
--   This work is derivative of the Quasi-Euclidean Granular Geometry book
--   authored by Alfredo Metere. Copyright 2026 Metere Industries, Inc.
--   All rights reserved
-- See LICENSE.md and NOTICE.

import QuasiEuclidean.Basic
import QuasiEuclidean.Ch07_Multi
import QuasiEuclidean.Ch16_Phys

/-!
# Chapter 16, section "The Atom": Schrödinger's equation and the Copenhagen
interpretation on the granular lattice

All state spaces are finite-dimensional (`ι → ℂ` with `ι` finite).
-/

open Finset Matrix Complex

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace QE.Atom

/-! ## Squared norms and expectation forms -/

section Forms

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Squared norm `‖φ‖² = ∑ₓ |φ(x)|²`. -/
noncomputable def nsq (φ : ι → ℂ) : ℝ := ∑ x, ‖φ x‖ ^ 2

/-- Expectation form `⟨φ, A φ⟩`. -/
noncomputable def form (A : Matrix ι ι ℂ) (φ : ι → ℂ) : ℂ := star φ ⬝ᵥ (A *ᵥ φ)

lemma nsq_nonneg (φ : ι → ℂ) : 0 ≤ nsq φ := sum_nonneg fun _ _ => by positivity

lemma star_dot_self (φ : ι → ℂ) : star φ ⬝ᵥ φ = (nsq φ : ℂ) := by
  unfold nsq dotProduct; push_cast; congr 1; ext x
  simp [Complex.conj_mul']

lemma nsq_eq_zero {φ : ι → ℂ} (h : nsq φ = 0) : φ = 0 := by
  ext x
  have := (sum_eq_zero_iff_of_nonneg (fun y _ => by positivity)).mp h x (mem_univ x)
  simpa using this

lemma form_one (φ : ι → ℂ) : form 1 φ = (nsq φ : ℂ) := by
  simp [form, star_dot_self]

lemma form_add (A B : Matrix ι ι ℂ) (φ : ι → ℂ) : form (A + B) φ = form A φ + form B φ := by
  simp [form, add_mulVec, dotProduct_add]

lemma form_sub (A B : Matrix ι ι ℂ) (φ : ι → ℂ) : form (A - B) φ = form A φ - form B φ := by
  simp [form, sub_mulVec, dotProduct_sub]

lemma form_smul (c : ℂ) (A : Matrix ι ι ℂ) (φ : ι → ℂ) : form (c • A) φ = c * form A φ := by
  simp [form, smul_mulVec, dotProduct_smul]

lemma form_sum {J : Type*} (s : Finset J) (A : J → Matrix ι ι ℂ) (φ : ι → ℂ) :
    form (∑ j ∈ s, A j) φ = ∑ j ∈ s, form (A j) φ := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [form]
  | insert a s ha ih => rw [sum_insert ha, sum_insert ha, form_add, ih]

/-- `star (M v) ⬝ w = star v ⬝ (Mᴴ w)`. -/
lemma star_mulVec_dot (M : Matrix ι ι ℂ) (v w : ι → ℂ) :
    star (M *ᵥ v) ⬝ᵥ w = star v ⬝ᵥ (Mᴴ *ᵥ w) := by
  rw [star_mulVec, dotProduct_mulVec]

lemma form_conjTranspose (A : Matrix ι ι ℂ) (φ : ι → ℂ) :
    form Aᴴ φ = (starRingEnd ℂ) (form A φ) := by
  unfold form
  rw [← star_mulVec_dot, dotProduct_comm]
  simp [dotProduct, map_sum, mul_comm]

/-- The expectation of a Hermitian matrix is real. -/
lemma form_herm_im {A : Matrix ι ι ℂ} (hA : A.IsHermitian) (φ : ι → ℂ) :
    (form A φ).im = 0 := by
  have h := form_conjTranspose A φ
  rw [hA.eq] at h
  have := congrArg Complex.im h
  simp at this; linarith

lemma form_single (A : Matrix ι ι ℂ) (x : ι) : form A (Pi.single x 1) = A x x := by
  simp [form, mulVec_single_one, dotProduct, Pi.single_apply]

lemma nsq_single (x : ι) : nsq (Pi.single x (1 : ℂ)) = 1 := by
  unfold nsq; rw [sum_eq_single x] <;> simp [Pi.single_apply]

/-- A unitary (`Uᴴ U = 1`) preserves inner products. -/
lemma unitary_dot {U : Matrix ι ι ℂ} (hU : Uᴴ * U = 1) (v w : ι → ℂ) :
    star (U *ᵥ v) ⬝ᵥ (U *ᵥ w) = star v ⬝ᵥ w := by
  rw [star_mulVec_dot, mulVec_mulVec, hU, one_mulVec]

lemma unitary_nsq {U : Matrix ι ι ℂ} (hU : Uᴴ * U = 1) (v : ι → ℂ) :
    nsq (U *ᵥ v) = nsq v := by
  have h := unitary_dot hU v v
  rw [star_dot_self, star_dot_self] at h
  exact_mod_cast h

end Forms

lemma nsq_add_le {ι : Type*} [Fintype ι] (u v : ι → ℂ) :
    nsq (u + v) ≤ 2 * nsq u + 2 * nsq v := by
  unfold nsq; rw [mul_sum, mul_sum, ← sum_add_distrib]
  refine sum_le_sum fun x _ => ?_
  have h := norm_add_le (u x) (v x)
  have h0 : 0 ≤ ‖u x + v x‖ := norm_nonneg _
  simp only [Pi.add_apply]
  nlinarith [sq_nonneg (‖u x‖ - ‖v x‖), norm_nonneg (u x), norm_nonneg (v x)]

lemma nsq_smul {ι : Type*} [Fintype ι] (c : ℂ) (v : ι → ℂ) :
    nsq (c • v) = ‖c‖ ^ 2 * nsq v := by
  unfold nsq; rw [mul_sum]; refine sum_congr rfl fun x _ => ?_
  simp [norm_mul, mul_pow]

lemma nsq_neg {ι : Type*} [Fintype ι] (v : ι → ℂ) : nsq (-v) = nsq v := by
  unfold nsq; simp

/-! ## Hermitian matrices: ground state and norm bound (spectral theorem) -/

section Spectral

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {A : Matrix ι ι ℂ}

lemma evU_star_mul (hA : A.IsHermitian) :
    (hA.eigenvectorUnitary : Matrix ι ι ℂ)ᴴ * (hA.eigenvectorUnitary : Matrix ι ι ℂ) = 1 := by
  rw [← star_eq_conjTranspose]; exact Unitary.coe_star_mul_self _

lemma evU_mul_star (hA : A.IsHermitian) :
    (hA.eigenvectorUnitary : Matrix ι ι ℂ) * (hA.eigenvectorUnitary : Matrix ι ι ℂ)ᴴ = 1 := by
  rw [← star_eq_conjTranspose]; exact Unitary.coe_mul_star_self _

lemma spectral_mulVec (hA : A.IsHermitian) (φ : ι → ℂ) :
    A *ᵥ φ = (hA.eigenvectorUnitary : Matrix ι ι ℂ) *ᵥ
      (diagonal (fun j => (hA.eigenvalues j : ℂ)) *ᵥ
        ((hA.eigenvectorUnitary : Matrix ι ι ℂ)ᴴ *ᵥ φ)) := by
  conv_lhs => rw [hA.spectral_theorem, Unitary.conjStarAlgAut_apply]
  rw [mulVec_mulVec, mulVec_mulVec, star_eq_conjTranspose]
  rfl

/-- In the eigenbasis the form is `∑ λⱼ |wⱼ|²`. -/
lemma spectral_form (hA : A.IsHermitian) (φ : ι → ℂ) :
    form A φ = ∑ j, (hA.eigenvalues j : ℂ) *
      ((‖((hA.eigenvectorUnitary : Matrix ι ι ℂ)ᴴ *ᵥ φ) j‖ ^ 2 : ℝ) : ℂ) := by
  have hφ : φ = (hA.eigenvectorUnitary : Matrix ι ι ℂ) *ᵥ
      ((hA.eigenvectorUnitary : Matrix ι ι ℂ)ᴴ *ᵥ φ) := by
    rw [mulVec_mulVec, evU_mul_star hA, one_mulVec]
  have key : form A φ = star ((hA.eigenvectorUnitary : Matrix ι ι ℂ)ᴴ *ᵥ φ) ⬝ᵥ
      (diagonal (fun j => (hA.eigenvalues j : ℂ)) *ᵥ
        ((hA.eigenvectorUnitary : Matrix ι ι ℂ)ᴴ *ᵥ φ)) := by
    unfold form
    rw [spectral_mulVec hA φ]
    conv_lhs => arg 1; rw [hφ]
    rw [unitary_dot (evU_star_mul hA)]
  rw [key]
  generalize ((hA.eigenvectorUnitary : Matrix ι ι ℂ)ᴴ *ᵥ φ) = w
  simp only [dotProduct, mulVec_diagonal, Pi.star_apply]
  refine sum_congr rfl fun j _ => ?_
  have := Complex.conj_mul' (w j)
  simp only [RCLike.star_def] at *
  push_cast
  rw [← this]; ring

lemma spectral_nsq (hA : A.IsHermitian) (φ : ι → ℂ) :
    nsq φ = ∑ j, ‖((hA.eigenvectorUnitary : Matrix ι ι ℂ)ᴴ *ᵥ φ) j‖ ^ 2 := by
  have h := unitary_nsq (evU_star_mul hA) ((hA.eigenvectorUnitary : Matrix ι ι ℂ)ᴴ *ᵥ φ)
  rw [mulVec_mulVec, evU_mul_star hA, one_mulVec] at h
  rw [h]; rfl

lemma spectral_nsq_mulVec (hA : A.IsHermitian) (φ : ι → ℂ) :
    nsq (A *ᵥ φ) = ∑ j, hA.eigenvalues j ^ 2 *
      ‖((hA.eigenvectorUnitary : Matrix ι ι ℂ)ᴴ *ᵥ φ) j‖ ^ 2 := by
  rw [spectral_mulVec hA φ, unitary_nsq (evU_star_mul hA)]
  unfold nsq; refine sum_congr rfl fun j _ => ?_
  rw [mulVec_diagonal, norm_mul, mul_pow]; simp

lemma eigenvector_nsq (hA : A.IsHermitian) (j : ι) :
    nsq (⇑(hA.eigenvectorBasis j)) = 1 := by
  rw [← hA.eigenvectorUnitary_mulVec, unitary_nsq (evU_star_mul hA), nsq_single]

lemma eigenvalue_eq_form (hA : A.IsHermitian) (j : ι) :
    hA.eigenvalues j = (form A ⇑(hA.eigenvectorBasis j)).re := by
  rw [hA.eigenvalues_eq j]; rfl

/-- **Ground state.**  A Hermitian matrix on a nonempty finite index set has a
normalised eigenvector whose eigenvalue `E₀` minimises the Rayleigh quotient:
`E₀ ‖φ‖² ≤ ⟨φ, A φ⟩` for every `φ`, and every expectation is real. -/
theorem ground_state [Nonempty ι] (hA : A.IsHermitian) :
    ∃ (E₀ : ℝ) (ψ₀ : ι → ℂ), nsq ψ₀ = 1 ∧ A *ᵥ ψ₀ = (E₀ : ℂ) • ψ₀ ∧
      (∀ φ, E₀ * nsq φ ≤ (form A φ).re) ∧ (∀ φ, (form A φ).im = 0) := by
  obtain ⟨j₀, -, hj₀⟩ := Finset.exists_min_image univ hA.eigenvalues univ_nonempty
  refine ⟨hA.eigenvalues j₀, ⇑(hA.eigenvectorBasis j₀), eigenvector_nsq hA j₀, ?_, ?_,
    form_herm_im hA⟩
  · rw [hA.mulVec_eigenvectorBasis j₀, Complex.coe_smul]
  · intro φ
    rw [spectral_nsq hA φ, spectral_form hA φ, mul_sum]
    rw [Complex.re_sum]
    refine sum_le_sum fun j _ => ?_
    have := hj₀ j (mem_univ j)
    rw [← Complex.ofReal_mul, Complex.ofReal_re]
    exact mul_le_mul_of_nonneg_right this (by positivity)

/-- **Norm bound from form bounds.**  If `-C‖φ‖² ≤ ⟨φ,Aφ⟩ ≤ K‖φ‖²` for all `φ`,
then `‖Aφ‖² ≤ max(C,K)² ‖φ‖²`. -/
theorem norm_bound_of_form (hA : A.IsHermitian) {C K : ℝ}
    (hlo : ∀ φ, -C * nsq φ ≤ (form A φ).re) (hhi : ∀ φ, (form A φ).re ≤ K * nsq φ)
    (φ : ι → ℂ) : nsq (A *ᵥ φ) ≤ (max C K) ^ 2 * nsq φ := by
  rw [spectral_nsq_mulVec hA φ, spectral_nsq hA φ, mul_sum]
  refine sum_le_sum fun j _ => ?_
  have h1 := hlo ⇑(hA.eigenvectorBasis j)
  have h2 := hhi ⇑(hA.eigenvectorBasis j)
  rw [eigenvector_nsq, ← eigenvalue_eq_form] at h1 h2
  have : hA.eigenvalues j ^ 2 ≤ (max C K) ^ 2 := by
    apply sq_le_sq'
    · have := le_max_left C K; linarith
    · have := le_max_right C K; linarith
  exact mul_le_mul_of_nonneg_right this (by positivity)

end Spectral

/-! ## Lattice operators on a finite region (Dirichlet) -/

section Lattice

variable {Γ : Type*} [AddCommGroup Γ] [DecidableEq Γ] (S : Finset Γ)

/-- Hopping by the displacement `d` inside the finite region `S`; hops that
leave `S` are dropped (Dirichlet condition). -/
def hop (d : Γ) : Matrix S S ℂ := fun x y => if (y : Γ) = x + d then 1 else 0

lemma hop_conjTranspose (d : Γ) : (hop S d)ᴴ = hop S (-d) := by
  ext x y
  simp only [hop, conjTranspose_apply]
  by_cases h : (x : Γ) = y + d
  · have h' : (y : Γ) = x + -d := by rw [h]; abel
    simp [h']
  · have h' : ¬ (y : Γ) = x + -d := by
      intro h'; apply h; rw [h']; abel
    simp [h, h']

/-- Schur test: a kernel whose rows and columns have `ℓ¹` norm `≤ 1` has
`|∑ₓ φ̄(x) ∑_y M(x,y) φ(y)| ≤ ‖φ‖²`. -/
lemma schur_sum {ι : Type*} [Fintype ι] (M : ι → ι → ℂ)
    (hr : ∀ x, ∑ y, ‖M x y‖ ≤ 1) (hc : ∀ y, ∑ x, ‖M x y‖ ≤ 1) (φ : ι → ℂ) :
    ‖∑ x, star (φ x) * ∑ y, M x y * φ y‖ ≤ nsq φ := by
  set a : ι → ℝ := fun x => ‖φ x‖ ^ 2
  have step : ‖∑ x, star (φ x) * ∑ y, M x y * φ y‖ ≤
      ∑ x, ∑ y, (‖M x y‖ * (a x / 2) + ‖M x y‖ * (a y / 2)) := by
    refine (norm_sum_le _ _).trans (sum_le_sum fun x _ => ?_)
    rw [norm_mul, norm_star]
    calc ‖φ x‖ * ‖∑ y, M x y * φ y‖ ≤ ‖φ x‖ * ∑ y, ‖M x y * φ y‖ :=
          mul_le_mul_of_nonneg_left (norm_sum_le _ _) (norm_nonneg _)
      _ = ∑ y, ‖M x y‖ * (‖φ x‖ * ‖φ y‖) := by
          rw [mul_sum]; refine sum_congr rfl fun y _ => ?_; rw [norm_mul]; ring
      _ ≤ _ := by
          refine sum_le_sum fun y _ => ?_
          have := sq_nonneg (‖φ x‖ - ‖φ y‖)
          have hM := norm_nonneg (M x y)
          simp only [a]
          nlinarith [mul_nonneg hM this]
  refine step.trans ?_
  simp only [sum_add_distrib]
  have e1 : ∑ x, ∑ y, ‖M x y‖ * (a x / 2) = (∑ x, a x * ∑ y, ‖M x y‖) / 2 := by
    rw [sum_div]; refine sum_congr rfl fun x _ => ?_
    rw [mul_sum, sum_div]; refine sum_congr rfl fun y _ => ?_; ring
  have e2 : ∑ x, ∑ y, ‖M x y‖ * (a y / 2) = (∑ y, a y * ∑ x, ‖M x y‖) / 2 := by
    rw [sum_comm, sum_div]; refine sum_congr rfl fun y _ => ?_
    rw [mul_sum, sum_div]; refine sum_congr rfl fun x _ => ?_; ring
  rw [e1, e2]
  have h1 : ∑ x, a x * ∑ y, ‖M x y‖ ≤ nsq φ :=
    sum_le_sum fun x _ => mul_le_of_le_one_right (by positivity) (hr x)
  have h2 : ∑ y, a y * ∑ x, ‖M x y‖ ≤ nsq φ :=
    sum_le_sum fun y _ => mul_le_of_le_one_right (by positivity) (hc y)
  linarith

lemma hop_row (d : Γ) (x : S) : ∑ y, ‖hop S d x y‖ ≤ 1 := by
  simp only [hop, apply_ite norm, norm_one, norm_zero]
  rw [sum_boole]
  have : (univ.filter fun y : S => (y : Γ) = x + d).card ≤ 1 := by
    rw [Finset.card_le_one]
    intro a ha b hb
    simp only [mem_filter] at ha hb
    exact Subtype.ext (ha.2.trans hb.2.symm)
  exact_mod_cast this

lemma hop_col (d : Γ) (y : S) : ∑ x, ‖hop S d x y‖ ≤ 1 := by
  simp only [hop, apply_ite norm, norm_one, norm_zero]
  rw [sum_boole]
  have : (univ.filter fun x : S => (y : Γ) = x + d).card ≤ 1 := by
    rw [Finset.card_le_one]
    intro a ha b hb
    simp only [mem_filter] at ha hb
    exact Subtype.ext (add_right_cancel (ha.2.symm.trans hb.2))
  exact_mod_cast this

lemma hop_form_le (d : Γ) (φ : S → ℂ) : ‖form (hop S d) φ‖ ≤ nsq φ :=
  schur_sum (fun x y => hop S d x y) (hop_row S d) (hop_col S d) φ

/-- `(a/ħ)²·(−Δ)` along the displacement `d`: `2 − T_d − T_{−d}`. -/
def lapK (d : Γ) : Matrix S S ℂ := (2 : ℂ) • 1 - hop S d - hop S (-d)

lemma lapK_isHermitian (d : Γ) : (lapK S d).IsHermitian := by
  unfold lapK IsHermitian
  rw [conjTranspose_sub, conjTranspose_sub, conjTranspose_smul, conjTranspose_one,
    hop_conjTranspose, hop_conjTranspose, neg_neg]
  simp only [star_ofNat]; abel

lemma form_lapK (d : Γ) (φ : S → ℂ) :
    form (lapK S d) φ = ((2 * nsq φ - 2 * (form (hop S d) φ).re : ℝ) : ℂ) := by
  unfold lapK
  rw [form_sub, form_sub, form_smul, form_one, ← hop_conjTranspose, form_conjTranspose]
  have := Complex.add_conj (form (hop S d) φ)
  push_cast at this ⊢
  linear_combination -this

/-- **The lattice Laplacian is bounded.**  `0 ≤ ⟨φ,(2−T_d−T_{−d})φ⟩ ≤ 4‖φ‖²`, and the
form is real. -/
theorem lapK_bounds (d : Γ) (φ : S → ℂ) :
    (form (lapK S d) φ).im = 0 ∧ 0 ≤ (form (lapK S d) φ).re ∧
      (form (lapK S d) φ).re ≤ 4 * nsq φ := by
  rw [form_lapK]
  simp only [Complex.ofReal_im, Complex.ofReal_re, true_and]
  have h := (Complex.abs_re_le_norm (form (hop S d) φ)).trans (hop_form_le S d φ)
  rw [abs_le] at h
  constructor <;> linarith [h.1, h.2]

lemma lapK_diag (d : Γ) (hd : d ≠ 0) (x : S) : lapK S d x x = 2 := by
  have h1 : ¬ ((x : Γ) = x + d) := by
    intro h; apply hd; have := congrArg (· - (x : Γ)) h; simp at this; exact this.symm
  have h2 : ¬ ((x : Γ) = x + -d) := by
    intro h; apply hd; have := congrArg (· - (x : Γ)) h; simp at this
    exact this
  simp [lapK, hop, h1, h2, one_apply]

variable {J : Type*} [Fintype J]

/-- Kinetic energy `∑ⱼ cⱼ (2 − T_{dⱼ} − T_{−dⱼ})`. -/
noncomputable def kin (c : J → ℝ) (d : J → Γ) : Matrix S S ℂ :=
  ∑ j, ((c j : ℝ) : ℂ) • lapK S (d j)

/-- Multiplication by a real potential. -/
noncomputable def pot (V : Γ → ℝ) : Matrix S S ℂ := diagonal fun x => ((V x : ℝ) : ℂ)

/-- The Hamiltonian `H = kin + V`. -/
noncomputable def ham (c : J → ℝ) (d : J → Γ) (V : Γ → ℝ) : Matrix S S ℂ :=
  kin S c d + pot S V

lemma kin_isHermitian (c : J → ℝ) (d : J → Γ) : (kin S c d).IsHermitian := by
  unfold kin IsHermitian
  rw [conjTranspose_sum]
  refine sum_congr rfl fun j _ => ?_
  rw [conjTranspose_smul, (lapK_isHermitian S (d j)).eq, Complex.star_def, Complex.conj_ofReal]

lemma pot_isHermitian (V : Γ → ℝ) : (pot S V).IsHermitian := by
  unfold pot IsHermitian
  rw [diagonal_conjTranspose]; congr 1; ext x; simp

lemma ham_isHermitian (c : J → ℝ) (d : J → Γ) (V : Γ → ℝ) : (ham S c d V).IsHermitian :=
  (kin_isHermitian S c d).add (pot_isHermitian S V)

lemma form_kin (c : J → ℝ) (d : J → Γ) (φ : S → ℂ) :
    form (kin S c d) φ = ∑ j, ((c j : ℝ) : ℂ) * form (lapK S (d j)) φ := by
  unfold kin; rw [form_sum]; simp only [form_smul]

lemma form_pot (V : Γ → ℝ) (φ : S → ℂ) :
    form (pot S V) φ = ((∑ x : S, V (x : Γ) * ‖φ x‖ ^ 2 : ℝ) : ℂ) := by
  unfold form pot
  simp only [dotProduct, mulVec_diagonal, Pi.star_apply]
  push_cast
  refine sum_congr rfl fun x _ => ?_
  have := Complex.conj_mul' (φ x)
  simp only [RCLike.star_def] at *
  rw [← this]; ring

/-- **Kinetic bounds.**  For `cⱼ ≥ 0`: `0 ≤ ⟨φ, kin φ⟩ ≤ 4 (∑ cⱼ) ‖φ‖²`, real. -/
theorem kin_bounds (c : J → ℝ) (hc : ∀ j, 0 ≤ c j) (d : J → Γ) (φ : S → ℂ) :
    (form (kin S c d) φ).im = 0 ∧ 0 ≤ (form (kin S c d) φ).re ∧
      (form (kin S c d) φ).re ≤ 4 * (∑ j, c j) * nsq φ := by
  rw [form_kin, Complex.im_sum, Complex.re_sum]
  refine ⟨sum_eq_zero fun j _ => ?_, sum_nonneg fun j _ => ?_, ?_⟩
  · simp [(lapK_bounds S (d j) φ).1]
  · simp only [Complex.re_ofReal_mul]
    exact mul_nonneg (hc j) (lapK_bounds S (d j) φ).2.1
  · rw [mul_assoc, sum_mul, mul_sum]
    refine sum_le_sum fun j _ => ?_
    simp only [Complex.re_ofReal_mul]
    have := (lapK_bounds S (d j) φ).2.2
    nlinarith [hc j]

/-- **Stability.**  If `V ≥ −C` pointwise, then `⟨φ, Hφ⟩ ≥ −C ‖φ‖²` (and it is real). -/
theorem ham_lower (c : J → ℝ) (hc : ∀ j, 0 ≤ c j) (d : J → Γ) (V : Γ → ℝ) (C : ℝ)
    (hV : ∀ x, -C ≤ V x) (φ : S → ℂ) :
    (form (ham S c d V) φ).im = 0 ∧ -C * nsq φ ≤ (form (ham S c d V) φ).re := by
  refine ⟨form_herm_im (ham_isHermitian S c d V) φ, ?_⟩
  unfold ham; rw [form_add, Complex.add_re, form_pot, Complex.ofReal_re]
  have hk := (kin_bounds S c hc d φ).2.1
  have : -C * nsq φ ≤ ∑ x : S, V (x : Γ) * ‖φ x‖ ^ 2 := by
    unfold nsq; rw [mul_sum]
    exact sum_le_sum fun x _ => mul_le_mul_of_nonneg_right (hV x) (by positivity)
  linarith

theorem ham_upper (c : J → ℝ) (hc : ∀ j, 0 ≤ c j) (d : J → Γ) (V : Γ → ℝ)
    (hV : ∀ x, V x ≤ 0) (φ : S → ℂ) :
    (form (ham S c d V) φ).re ≤ 4 * (∑ j, c j) * nsq φ := by
  unfold ham; rw [form_add, Complex.add_re, form_pot, Complex.ofReal_re]
  have hk := (kin_bounds S c hc d φ).2.2
  have : ∑ x : S, V (x : Γ) * ‖φ x‖ ^ 2 ≤ 0 :=
    sum_nonpos fun x _ => mul_nonpos_of_nonpos_of_nonneg (hV x) (by positivity)
  linarith

/-- The kinetic energy of a site-localised state is `2 ∑ cⱼ` (all `dⱼ ≠ 0`). -/
theorem kin_basis (c : J → ℝ) (d : J → Γ) (hd : ∀ j, d j ≠ 0) (x : S) :
    form (kin S c d) (Pi.single x 1) = ((2 * ∑ j, c j : ℝ) : ℂ) := by
  rw [form_single]
  simp only [kin, Matrix.sum_apply, Matrix.smul_apply, lapK_diag S _ (hd _), smul_eq_mul]
  push_cast; rw [mul_sum]; refine sum_congr rfl fun j _ => ?_; ring

end Lattice

/-! ## The atom: electron and nucleus as two point-spheres -/

section AtomDef

variable {n : ℕ}

/-- Configuration lattice of the atom: (electron site, nucleus site). -/
abbrev Conf (n : ℕ) := (Fin n → ℤ) × (Fin n → ℤ)

/-- Displacements: one lattice step of the electron or of the nucleus. -/
def atomDisp : Fin n ⊕ Fin n → Conf n
  | Sum.inl i => (QE.Multi.e i, 0)
  | Sum.inr i => (0, QE.Multi.e i)

/-- Hopping amplitudes `ħ²/(2 m a²)` (electron) and `ħ²/(2 M a²)` (nucleus). -/
noncomputable def atomCoef (ħ m M a : ℝ) : Fin n ⊕ Fin n → ℝ
  | Sum.inl _ => ħ ^ 2 / (2 * m * a ^ 2)
  | Sum.inr _ => ħ ^ 2 / (2 * M * a ^ 2)

/-- Coulomb attraction through a lattice Green's function `G`:
`V(xₑ, x_N) = −(Z e²/ε₀) G(xₑ − x_N)`. -/
noncomputable def atomPot (Z e ε₀ : ℝ) (G : (Fin n → ℤ) → ℝ) : Conf n → ℝ :=
  fun p => -(Z * e ^ 2 / ε₀) * G (p.1 - p.2)

/-- The atomic Hamiltonian on a finite region `S` of configurations (Dirichlet). -/
noncomputable def atomH (S : Finset (Conf n)) (ħ m M a Z e ε₀ : ℝ) (G : (Fin n → ℤ) → ℝ) :
    Matrix S S ℂ :=
  ham S (atomCoef ħ m M a) atomDisp (atomPot Z e ε₀ G)

/-- The free (kinetic) part `H₀ = −(ħ²/2m)Δₑ − (ħ²/2M)Δ_N`. -/
noncomputable def atomH0 (S : Finset (Conf n)) (ħ m M a : ℝ) : Matrix S S ℂ :=
  kin S (atomCoef ħ m M a) atomDisp

lemma atomDisp_ne (j : Fin n ⊕ Fin n) : atomDisp j ≠ 0 := by
  cases j with
  | inl i =>
    intro h; have := congrArg (fun p => p.1 i) h
    simp [atomDisp, QE.Multi.e] at this
  | inr i =>
    intro h; have := congrArg (fun p => p.2 i) h
    simp [atomDisp, QE.Multi.e] at this

lemma atomCoef_nonneg {ħ m M a : ℝ} (hm : 0 < m) (hM : 0 < M) (j : Fin n ⊕ Fin n) :
    0 ≤ atomCoef ħ m M a j := by
  cases j <;> simp only [atomCoef] <;> positivity

/-- `∑ⱼ cⱼ = n ħ²/(2 μ a²)` with the reduced mass `μ = mM/(m+M)`. -/
lemma atomCoef_sum {ħ m M a : ℝ} (hm : 0 < m) (hM : 0 < M) (ha : a ≠ 0) :
    ∑ j, atomCoef (n := n) ħ m M a j = n * ħ ^ 2 / (2 * (m * M / (m + M)) * a ^ 2) := by
  rw [Fintype.sum_sum_type]
  simp only [atomCoef, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
  field_simp
  ring

/-- **(a) Kinetic bounds of the atom.**  `0 ≤ ⟨ψ,H₀ψ⟩ ≤ (2nħ²/(μa²)) ‖ψ‖²`. -/
theorem atom_kinetic_bounds (S : Finset (Conf n)) {ħ m M a : ℝ} (hm : 0 < m) (hM : 0 < M)
    (ha : a ≠ 0) (ψ : S → ℂ) :
    (form (atomH0 S ħ m M a) ψ).im = 0 ∧ 0 ≤ (form (atomH0 S ħ m M a) ψ).re ∧
      (form (atomH0 S ħ m M a) ψ).re ≤
        2 * n * ħ ^ 2 / ((m * M / (m + M)) * a ^ 2) * nsq ψ := by
  obtain ⟨h1, h2, h3⟩ := kin_bounds S _ (atomCoef_nonneg hm hM) atomDisp ψ
  refine ⟨h1, h2, ?_⟩
  rw [atomCoef_sum hm hM ha] at h3
  have e : 4 * (↑n * ħ ^ 2 / (2 * (m * M / (m + M)) * a ^ 2)) =
      2 * n * ħ ^ 2 / ((m * M / (m + M)) * a ^ 2) := by ring
  rw [e] at h3; exact h3

/-- **(b) Stability of the atom.**  If `G ≤ G(0)` and `Z e²/ε₀ ≥ 0`, then
`⟨ψ,Hψ⟩ ≥ −(Z e² G(0)/ε₀) ‖ψ‖²`. -/
theorem atom_stable (S : Finset (Conf n)) {ħ m M a Z e ε₀ : ℝ} (hm : 0 < m) (hM : 0 < M)
    (hZ : 0 ≤ Z) (hε₀ : 0 < ε₀) (G : (Fin n → ℤ) → ℝ) (hG : ∀ r, G r ≤ G 0) (ψ : S → ℂ) :
    (form (atomH S ħ m M a Z e ε₀ G) ψ).im = 0 ∧
      -(Z * e ^ 2 * G 0 / ε₀) * nsq ψ ≤ (form (atomH S ħ m M a Z e ε₀ G) ψ).re := by
  apply ham_lower S _ (atomCoef_nonneg hm hM) atomDisp _ _
  intro p
  simp only [atomPot]
  have hk : 0 ≤ Z * e ^ 2 / ε₀ := by positivity
  have := mul_le_mul_of_nonneg_left (hG (p.1 - p.2)) hk
  have e1 : Z * e ^ 2 * G 0 / ε₀ = Z * e ^ 2 / ε₀ * G 0 := by ring
  rw [e1]; linarith

/-- The Dirichlet Green's function of `thm:multi-green-origin` (source at the origin)
satisfies the hypotheses of `atom_stable`; the atom is bounded below by
`−Z e² G_D(0,0)/ε₀`. -/
theorem atom_stable_green (S : Finset (Conf n)) {ħ m M a Z e ε₀ ε : ℝ} (hm : 0 < m)
    (hM : 0 < M) (hZ : 0 ≤ Z) (hε₀ : 0 < ε₀) (hε : 0 < ε) (i₀ : Fin n)
    (D : Finset (Fin n → ℤ)) (h0 : (0 : Fin n → ℤ) ∈ D) (G : (Fin n → ℤ) → ℝ)
    (hG0 : ∀ x, x ∉ D → G x = 0) (hG : ∀ x ∈ D, -QE.Multi.lap ε G x = QE.Multi.deltaN ε 0 x)
    (ψ : S → ℂ) :
    (form (atomH S ħ m M a Z e ε₀ G) ψ).im = 0 ∧
      -(Z * e ^ 2 * G 0 / ε₀) * nsq ψ ≤ (form (atomH S ħ m M a Z e ε₀ G) ψ).re ∧
      0 ≤ G 0 := by
  obtain ⟨hnn, hmax, -⟩ := QE.Multi.green_props ε hε i₀ D 0 h0 G hG0 hG
  obtain ⟨h1, h2⟩ := atom_stable S hm hM hZ hε₀ G hmax ψ
  exact ⟨h1, h2, hnn 0⟩

lemma atomPot_nonpos {Z e ε₀ : ℝ} (hZ : 0 ≤ Z) (hε₀ : 0 < ε₀) (G : (Fin n → ℤ) → ℝ)
    (hG : ∀ r, 0 ≤ G r) (p : Conf n) : atomPot Z e ε₀ G p ≤ 0 := by
  simp only [atomPot]
  have : 0 ≤ Z * e ^ 2 / ε₀ := by positivity
  nlinarith [hG (p.1 - p.2)]

/-- **(c) The ground state of the atom exists**: `H` is Hermitian, its lowest
eigenvalue `E₀` is attained by a normalised state, `E₀ ≥ −Z e² G(0)/ε₀`, and
`E₀ ‖φ‖² ≤ ⟨φ,Hφ⟩` for all `φ`. -/
theorem atom_ground_state (S : Finset (Conf n)) (hS : S.Nonempty) {ħ m M a Z e ε₀ : ℝ}
    (hm : 0 < m) (hM : 0 < M) (hZ : 0 ≤ Z) (hε₀ : 0 < ε₀) (G : (Fin n → ℤ) → ℝ)
    (hG : ∀ r, G r ≤ G 0) :
    (atomH S ħ m M a Z e ε₀ G).IsHermitian ∧
    ∃ (E₀ : ℝ) (ψ₀ : S → ℂ), nsq ψ₀ = 1 ∧
      atomH S ħ m M a Z e ε₀ G *ᵥ ψ₀ = (E₀ : ℂ) • ψ₀ ∧
      -(Z * e ^ 2 * G 0 / ε₀) ≤ E₀ ∧
      ∀ φ, E₀ * nsq φ ≤ (form (atomH S ħ m M a Z e ε₀ G) φ).re := by
  have hH := ham_isHermitian S (atomCoef ħ m M a) atomDisp (atomPot Z e ε₀ G)
  have : Nonempty S := hS.coe_sort
  obtain ⟨E₀, ψ₀, hn, hev, hmin, -⟩ := ground_state hH
  refine ⟨hH, E₀, ψ₀, hn, hev, ?_, hmin⟩
  have h := (atom_stable (ħ := ħ) (a := a) (e := e) S hm hM hZ hε₀ G hG ψ₀).2
  have hf : form (atomH S ħ m M a Z e ε₀ G) ψ₀ = (E₀ : ℂ) * (nsq ψ₀ : ℂ) := by
    unfold form; rw [show atomH S ħ m M a Z e ε₀ G = ham S _ _ _ from rfl, hev,
      dotProduct_smul, star_dot_self, smul_eq_mul]
  rw [hf, hn] at h
  simpa using h

/-- **Operator-norm bound of the atom.**  `‖Hψ‖ ≤ h ‖ψ‖` with
`h = max(Z e² G(0)/ε₀, 2nħ²/(μa²))`. -/
theorem atom_norm_bound (S : Finset (Conf n)) {ħ m M a Z e ε₀ : ℝ}
    (hm : 0 < m) (hM : 0 < M) (ha : a ≠ 0) (hZ : 0 ≤ Z) (hε₀ : 0 < ε₀)
    (G : (Fin n → ℤ) → ℝ) (hG : ∀ r, G r ≤ G 0) (hG' : ∀ r, 0 ≤ G r) (ψ : S → ℂ) :
    nsq (atomH S ħ m M a Z e ε₀ G *ᵥ ψ) ≤
      (max (Z * e ^ 2 * G 0 / ε₀) (2 * n * ħ ^ 2 / ((m * M / (m + M)) * a ^ 2))) ^ 2 * nsq ψ := by
  apply norm_bound_of_form (ham_isHermitian S _ _ _)
  · intro φ; exact (atom_stable (ħ := ħ) (a := a) (e := e) S hm hM hZ hε₀ G hG φ).2
  · intro φ
    have h := ham_upper S (atomCoef ħ m M a) (atomCoef_nonneg hm hM) atomDisp (atomPot Z e ε₀ G)
      (atomPot_nonpos (e := e) hZ hε₀ G hG') φ
    rw [atomCoef_sum hm hM ha] at h
    have he4 : 4 * (↑n * ħ ^ 2 / (2 * (m * M / (m + M)) * a ^ 2)) =
        2 * n * ħ ^ 2 / ((m * M / (m + M)) * a ^ 2) := by ring
    rw [he4] at h; exact h

/-- **Joint position measurement.**  In a site-localised state of both charges the
energy is exactly `n ħ²/(μ a²) + V(xₑ − x_N)`: the kinetic part is finite. -/
theorem atom_basis_energy (S : Finset (Conf n)) {ħ m M a Z e ε₀ : ℝ} (hm : 0 < m)
    (hM : 0 < M) (ha : a ≠ 0) (G : (Fin n → ℤ) → ℝ) (x : S) :
    form (atomH0 S ħ m M a) (Pi.single x 1) = ((n * ħ ^ 2 / ((m * M / (m + M)) * a ^ 2) : ℝ) : ℂ) ∧
    form (atomH S ħ m M a Z e ε₀ G) (Pi.single x 1) =
      ((n * ħ ^ 2 / ((m * M / (m + M)) * a ^ 2) + atomPot Z e ε₀ G x : ℝ) : ℂ) := by
  have hk : form (atomH0 S ħ m M a) (Pi.single x 1) =
      ((n * ħ ^ 2 / ((m * M / (m + M)) * a ^ 2) : ℝ) : ℂ) := by
    unfold atomH0
    rw [kin_basis S _ _ atomDisp_ne x, atomCoef_sum hm hM ha]
    congr 1
    have hμ : 0 < m * M / (m + M) := by positivity
    field_simp
  refine ⟨hk, ?_⟩
  unfold atomH ham
  rw [form_add, show kin S (atomCoef ħ m M a) atomDisp = atomH0 S ħ m M a from rfl, hk,
    form_single]
  simp [pot]

end AtomDef

/-! ## Exact two-body reduction on the periodic lattice -/

section TwoBody

variable {N : ℕ} [NeZero N]

/-- Two-body Hamiltonian on the ring `ℤ/N`: electron hopping `tₑ`, nucleus hopping
`t_N`, pair potential `V(xₑ − x_N)`. -/
def H2 (te tN : ℂ) (V : ZMod N → ℂ) (ψ : ZMod N → ZMod N → ℂ) : ZMod N → ZMod N → ℂ :=
  fun xe xN => te * (2 * ψ xe xN - ψ (xe + 1) xN - ψ (xe - 1) xN)
    + tN * (2 * ψ xe xN - ψ xe (xN + 1) - ψ xe (xN - 1)) + V (xe - xN) * ψ xe xN

/-- Joint translation of both particles by one site. -/
def Tjoint (ψ : ZMod N → ZMod N → ℂ) : ZMod N → ZMod N → ℂ :=
  fun xe xN => ψ (xe + 1) (xN + 1)

/-- `H` commutes with the joint translation. -/
theorem H2_translate (te tN : ℂ) (V : ZMod N → ℂ) (ψ : ZMod N → ZMod N → ℂ) :
    H2 te tN V (Tjoint ψ) = Tjoint (H2 te tN V ψ) := by
  funext xe xN
  simp only [H2, Tjoint]
  have e1 : xe - 1 + 1 = xe + 1 - 1 := by ring
  have e2 : xN - 1 + 1 = xN + 1 - 1 := by ring
  have e3 : xe + 1 - (xN + 1) = xe - xN := by ring
  rw [e1, e2, e3]

lemma pow_val_add {ω : ℂ} (hω : ω ^ N = 1) (a b : ZMod N) :
    ω ^ (a + b).val = ω ^ a.val * ω ^ b.val := by
  rw [ZMod.val_add, QE.Phys.pow_mod_of_pow_eq_one hω, pow_add]

lemma pow_val_one {ω : ℂ} (hω : ω ^ N = 1) : ω ^ (1 : ZMod N).val = ω := by
  rw [ZMod.val_one_eq_one_mod, QE.Phys.pow_mod_of_pow_eq_one hω, pow_one]

lemma ne_zero_of_pow {ω : ℂ} (hω : ω ^ N = 1) : ω ≠ 0 := by
  intro h; rw [h, zero_pow (NeZero.ne N)] at hω; exact zero_ne_one hω

lemma pow_val_sub_one {ω : ℂ} (hω : ω ^ N = 1) (a : ZMod N) :
    ω ^ (a - 1).val = ω⁻¹ * ω ^ a.val := by
  have h := pow_val_add hω (a - 1) 1
  rw [sub_add_cancel, pow_val_one hω] at h
  rw [h]; field_simp [ne_zero_of_pow hω]

/-- Bloch ansatz `ψ(xₑ,x_N) = ω^{x_N} φ(xₑ − x_N)` with `ω = e^{iθ}`, `ω^N = 1`. -/
def bloch (ω : ℂ) (φ : ZMod N → ℂ) : ZMod N → ZMod N → ℂ :=
  fun xe xN => ω ^ xN.val * φ (xe - xN)

/-- Relative Hamiltonian at total quasi-momentum `ω = e^{iθ}`: hopping
`tₑ + t_N ω^{∓1}`. -/
noncomputable def Hrel (te tN ω : ℂ) (V : ZMod N → ℂ) (φ : ZMod N → ℂ) : ZMod N → ℂ :=
  fun r => 2 * (te + tN) * φ r - (te + tN * ω⁻¹) * φ (r + 1) - (te + tN * ω) * φ (r - 1)
    + V r * φ r

/-- **Exact two-body reduction.**  `H (ω^{x_N} φ(xₑ−x_N)) = ω^{x_N} (H_ω φ)(xₑ−x_N)`. -/
theorem bloch_reduction (te tN : ℂ) (V : ZMod N → ℂ) {ω : ℂ} (hω : ω ^ N = 1)
    (φ : ZMod N → ℂ) (xe xN : ZMod N) :
    H2 te tN V (bloch ω φ) xe xN = ω ^ xN.val * Hrel te tN ω V φ (xe - xN) := by
  simp only [H2, bloch, Hrel]
  have e1 : xe + 1 - xN = xe - xN + 1 := by ring
  have e2 : xe - 1 - xN = xe - xN - 1 := by ring
  have e3 : xe - (xN + 1) = xe - xN - 1 := by ring
  have e4 : xe - (xN - 1) = xe - xN + 1 := by ring
  rw [e1, e2, e3, e4, pow_val_add hω, pow_val_one hω, pow_val_sub_one hω]
  have := ne_zero_of_pow hω
  field_simp
  ring

/-- Bloch states are eigenstates of the joint translation: `Tψ = ω ψ`. -/
theorem bloch_translation {ω : ℂ} (hω : ω ^ N = 1) (φ : ZMod N → ℂ) :
    Tjoint (bloch ω φ) = ω • bloch ω φ := by
  funext xe xN
  simp only [Tjoint, bloch, Pi.smul_apply, smul_eq_mul]
  rw [pow_val_add hω, pow_val_one hω, show xe + 1 - (xN + 1) = xe - xN by ring]; ring

/-- One-body lattice Hamiltonian with hopping `t`. -/
def H1 (t : ℂ) (V : ZMod N → ℂ) (φ : ZMod N → ℂ) : ZMod N → ℂ :=
  fun r => t * (2 * φ r - φ (r + 1) - φ (r - 1)) + V r * φ r

/-- At zero total momentum the relative motion is a one-body problem with hopping
`tₑ + t_N`. -/
theorem bloch_zero (te tN : ℂ) (V : ZMod N → ℂ) (φ : ZMod N → ℂ) :
    Hrel te tN 1 V φ = H1 (te + tN) V φ := by
  funext r; simp only [Hrel, H1, inv_one, mul_one]; ring

/-- **The reduced mass appears exactly.** `ħ²/(2ma²) + ħ²/(2Ma²) = ħ²/(2μa²)`. -/
theorem reduced_mass (ħ m M a : ℝ) (hm : 0 < m) (hM : 0 < M) (ha : a ≠ 0) :
    ħ ^ 2 / (2 * m * a ^ 2) + ħ ^ 2 / (2 * M * a ^ 2) =
      ħ ^ 2 / (2 * (m * M / (m + M)) * a ^ 2) := by
  field_simp; ring

/-- `|tₑ + t_N e^{iθ}|² = (tₑ + t_N)² − 4 tₑ t_N sin²(θ/2)`. -/
theorem hopping_normSq (te tN θ : ℝ) :
    Complex.normSq ((te : ℂ) + tN * Complex.exp (θ * Complex.I)) =
      (te + tN) ^ 2 - 4 * te * tN * Real.sin (θ / 2) ^ 2 := by
  rw [Complex.normSq_apply]
  simp only [Complex.add_re, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.mul_re, Complex.mul_im, Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im]
  have hc : Real.cos θ = 1 - 2 * Real.sin (θ / 2) ^ 2 := by
    have h2 := Real.cos_two_mul (θ / 2)
    rw [show 2 * (θ / 2) = θ by ring] at h2
    have := Real.sin_sq_add_cos_sq (θ / 2)
    linarith
  have hp := Real.sin_sq_add_cos_sq θ
  linear_combination tN ^ 2 * hp + 2 * te * tN * hc

/-- **The internal hopping depends on the total momentum.**  For `tₑ, t_N > 0`,
`|tₑ + t_N e^{iθ}| ≤ tₑ + t_N`, with equality iff `θ ∈ 2πℤ`. -/
theorem hopping_le (te tN θ : ℝ) (he : 0 < te) (hN : 0 < tN) :
    ‖(te : ℂ) + tN * Complex.exp (θ * Complex.I)‖ ≤ te + tN ∧
      (‖(te : ℂ) + tN * Complex.exp (θ * Complex.I)‖ = te + tN ↔
        ∃ k : ℤ, θ = 2 * Real.pi * k) := by
  have hsq : ‖(te : ℂ) + tN * Complex.exp (θ * Complex.I)‖ ^ 2 =
      (te + tN) ^ 2 - 4 * te * tN * Real.sin (θ / 2) ^ 2 := by
    rw [Complex.sq_norm, hopping_normSq]
  have h0 := norm_nonneg ((te : ℂ) + tN * Complex.exp (θ * Complex.I))
  have hs := sq_nonneg (Real.sin (θ / 2))
  have hpos : 0 < te + tN := by linarith
  constructor
  · nlinarith [mul_pos he hN]
  · constructor
    · intro h
      rw [h] at hsq
      have : Real.sin (θ / 2) ^ 2 = 0 := by
        have := mul_pos he hN; nlinarith
      have hs0 : Real.sin (θ / 2) = 0 := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp this
      obtain ⟨k, hk⟩ := Real.sin_eq_zero_iff.mp hs0
      exact ⟨k, by linarith⟩
    · rintro ⟨k, hk⟩
      have : Real.sin (θ / 2) = 0 := by
        rw [hk, show 2 * Real.pi * (k : ℝ) / 2 = (k : ℝ) * Real.pi by ring]
        exact Real.sin_int_mul_pi k
      rw [this] at hsq
      have hsq' : ‖(te : ℂ) + tN * Complex.exp (θ * Complex.I)‖ ^ 2 = (te + tN) ^ 2 := by
        rw [hsq]; ring
      exact (pow_left_inj₀ h0 hpos.le two_ne_zero).mp hsq'

/-- **Infinitely heavy nucleus.**  With `t_N = 0` the relative Hamiltonian does not
depend on the total momentum (fixed-nucleus limit). -/
theorem heavy_nucleus (te ω : ℂ) (V : ZMod N → ℂ) :
    Hrel te 0 ω V = H1 te V := by
  funext φ r; simp only [Hrel, H1, zero_mul, add_zero]; ring

end TwoBody

/-! ## Copenhagen on the lattice: position, Born rule, Cayley evolution -/

section Copenhagen

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **Position eigenbasis.**  The position operator `diag(X)` has the site states
`δₓ` as normalised, mutually orthogonal eigenvectors, and `⟨δₓ, ψ⟩ = ψ(x)`. -/
theorem position_eigen (X : ι → ℂ) (x y : ι) (ψ : ι → ℂ) :
    diagonal X *ᵥ Pi.single x 1 = X x • Pi.single x 1 ∧
    nsq (Pi.single x (1 : ℂ)) = 1 ∧
    star (Pi.single x (1 : ℂ)) ⬝ᵥ Pi.single y 1 = (if x = y then 1 else 0) ∧
    star (Pi.single x (1 : ℂ)) ⬝ᵥ ψ = ψ x := by
  refine ⟨?_, nsq_single x, ?_, ?_⟩
  · ext z; by_cases h : z = x
    · subst h; simp [mulVec_diagonal]
    · simp [mulVec_diagonal, Pi.single_apply, h]
  · by_cases h : x = y
    · subst h; simp [dotProduct, Pi.single_apply]
    · simp only [h, ite_false, dotProduct, Pi.star_apply]
      refine sum_eq_zero fun z _ => ?_
      by_cases hz : z = x
      · subst hz; simp [Pi.single_apply, h]
      · simp [Pi.single_apply, hz]
  · simp [dotProduct, Pi.single_apply]

/-- Born probability of a set of sites: a count of squared amplitudes. -/
noncomputable def prob (ψ : ι → ℂ) (A : Finset ι) : ℝ := ∑ x ∈ A, ‖ψ x‖ ^ 2

/-- **Born rule as counting.**  Probabilities are nonnegative, additive over disjoint
sets of sites, the probability of the site `x` is `|ψ(x)|²`, and the total is `‖ψ‖²`. -/
theorem born_rule (ψ : ι → ℂ) (A B : Finset ι) (hAB : Disjoint A B) (x : ι) :
    0 ≤ prob ψ A ∧ prob ψ (A ∪ B) = prob ψ A + prob ψ B ∧
    prob ψ {x} = ‖star (Pi.single x (1 : ℂ)) ⬝ᵥ ψ‖ ^ 2 ∧ prob ψ univ = nsq ψ := by
  refine ⟨sum_nonneg fun _ _ => by positivity, sum_union hAB, ?_, rfl⟩
  rw [(position_eigen (fun _ => 0) x x ψ).2.2.2]; simp [prob]

lemma one_add_I_injective {A : Matrix ι ι ℂ} (hA : A.IsHermitian) :
    Function.Injective (1 + Complex.I • A).mulVec := by
  have key : ∀ u, (1 + Complex.I • A) *ᵥ u = 0 → u = 0 := by
    intro u hu
    have h := congrArg (fun v => star u ⬝ᵥ v) hu
    simp only [add_mulVec, one_mulVec, smul_mulVec, dotProduct_add, dotProduct_smul,
      star_dot_self, dotProduct_zero, smul_eq_mul] at h
    have hre := congrArg Complex.re h
    have him := form_herm_im hA u
    simp only [form] at him
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
      Complex.I_im, zero_mul, one_mul, him, Complex.zero_re] at hre
    exact nsq_eq_zero (by linarith)
  intro v w hvw
  have := key (v - w) (by rw [mulVec_sub, hvw, sub_self])
  exact sub_eq_zero.mp this

lemma isUnit_det_one_add_I {A : Matrix ι ι ℂ} (hA : A.IsHermitian) :
    IsUnit (1 + Complex.I • A).det :=
  (isUnit_iff_isUnit_det _).mp (mulVec_injective_iff_isUnit.mp (one_add_I_injective hA))

/-- The Cayley (Crank–Nicolson) step `U = (1 − iA)(1 + iA)⁻¹`, with `A = τH/(2ħ)`. -/
noncomputable def cayley (A : Matrix ι ι ℂ) : Matrix ι ι ℂ :=
  (1 - Complex.I • A) * (1 + Complex.I • A)⁻¹

lemma cayley_comm (A : Matrix ι ι ℂ) :
    (1 + Complex.I • A) * (1 - Complex.I • A) = (1 - Complex.I • A) * (1 + Complex.I • A) := by
  simp only [add_mul, mul_add, sub_mul, mul_sub, one_mul, mul_one]; abel

/-- **The Cayley step solves the symmetric-difference equation**:
`(1 + iA) U = 1 − iA`, i.e. `iħ(ψ' − ψ)/τ = H(ψ' + ψ)/2`. -/
theorem cayley_step {A : Matrix ι ι ℂ} (hA : A.IsHermitian) :
    (1 + Complex.I • A) * cayley A = 1 - Complex.I • A := by
  unfold cayley
  rw [← mul_assoc, cayley_comm, mul_assoc, mul_nonsing_inv _ (isUnit_det_one_add_I hA),
    mul_one]

/-- **Unitarity of the Cayley step for every Hermitian `H`.**  `1 + iA` is invertible
and `Uᴴ U = 1`; hence `‖Uψ‖ = ‖ψ‖` and the Born probabilities keep total `1`. -/
theorem cayley_unitary {A : Matrix ι ι ℂ} (hA : A.IsHermitian) :
    IsUnit (1 + Complex.I • A) ∧ (cayley A)ᴴ * cayley A = 1 ∧
      ∀ ψ, nsq (cayley A *ᵥ ψ) = nsq ψ := by
  have hB := isUnit_det_one_add_I hA
  have hC' : IsUnit (1 + Complex.I • (-A)).det := isUnit_det_one_add_I hA.neg
  have eC : (1 : Matrix ι ι ℂ) + Complex.I • (-A) = 1 - Complex.I • A := by
    rw [smul_neg, ← sub_eq_add_neg]
  rw [eC] at hC'
  have hstar : star Complex.I = -Complex.I := by simp [Complex.star_def]
  have hBH : (1 + Complex.I • A)ᴴ = 1 - Complex.I • A := by
    rw [conjTranspose_add, conjTranspose_one, conjTranspose_smul, hA.eq, hstar, neg_smul,
      ← sub_eq_add_neg]
  have hU : (cayley A)ᴴ * cayley A = 1 := by
    unfold cayley
    rw [conjTranspose_mul, conjTranspose_nonsing_inv, hBH, conjTranspose_sub, conjTranspose_one,
      conjTranspose_smul, hA.eq, hstar, neg_smul, sub_neg_eq_add]
    calc (1 - Complex.I • A)⁻¹ * (1 + Complex.I • A) * ((1 - Complex.I • A) * (1 + Complex.I • A)⁻¹)
        = (1 - Complex.I • A)⁻¹ * ((1 + Complex.I • A) * (1 - Complex.I • A)) *
            (1 + Complex.I • A)⁻¹ := by simp only [mul_assoc]
      _ = (1 - Complex.I • A)⁻¹ * (1 - Complex.I • A) * ((1 + Complex.I • A) *
            (1 + Complex.I • A)⁻¹) := by rw [cayley_comm]; simp only [mul_assoc]
      _ = 1 := by rw [nonsing_inv_mul _ hC', mul_nonsing_inv _ hB, one_mul]
  exact ⟨(isUnit_iff_isUnit_det _).mpr hB, hU, unitary_nsq hU⟩

/-- **The contact density is a number.**  For a two-particle state on `ι × ι`,
`∑ₓ |ψ(x,x)|² ≤ ‖ψ‖²`. -/
theorem contact_density_le (ψ : ι × ι → ℂ) :
    ∑ x, ‖ψ (x, x)‖ ^ 2 ≤ nsq ψ := by
  unfold nsq
  have : ∑ x, ‖ψ (x, x)‖ ^ 2 = ∑ p ∈ univ.image (fun x : ι => (x, x)), ‖ψ p‖ ^ 2 := by
    rw [sum_image]; intro a _ b _ h; exact (Prod.mk.inj h).1
  rw [this]
  exact sum_le_sum_of_subset_of_nonneg (subset_univ _) (fun _ _ _ => by positivity)

end Copenhagen

/-! ## No dynamical collapse; freezing -/

section NoCollapse

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **No collapse by injective dynamics.**  An injective linear map on `ℂ^ι` cannot
send every state to a multiple of a single site state once there are two sites. -/
theorem no_collapse (L : (ι → ℂ) →ₗ[ℂ] (ι → ℂ)) (hL : Function.Injective L) {x y : ι}
    (hxy : x ≠ y) : ∃ v, ∀ (z : ι) (c : ℂ), L v ≠ c • Pi.single z 1 := by
  obtain ⟨v, hv⟩ := (LinearMap.injective_iff_surjective.mp hL) (Pi.single x 1 + Pi.single y 1)
  refine ⟨v, fun z c h => ?_⟩
  rw [hv] at h
  by_cases hzx : z = x
  · subst hzx
    have := congrFun h y
    simp [Pi.single_apply, hxy, Ne.symm hxy] at this
  · have := congrFun h x
    simp [Pi.single_apply, hxy, Ne.symm hxy, hzx, Ne.symm hzx] at this

/-- **Rank of a collapse map.**  A linear map sending every vector to a multiple of
some site state has rank `≤ 1`. -/
theorem collapse_rank_le_one (L : (ι → ℂ) →ₗ[ℂ] (ι → ℂ))
    (hL : ∀ v, ∃ (z : ι) (c : ℂ), L v = c • (Pi.single z (1 : ℂ) : ι → ℂ)) :
    Module.finrank ℂ (LinearMap.range L) ≤ 1 := by
  by_cases hι : Nonempty ι
  swap
  · have : IsEmpty ι := not_nonempty_iff.mp hι
    calc Module.finrank ℂ (LinearMap.range L) ≤ Module.finrank ℂ (ι → ℂ) :=
          Submodule.finrank_le _
      _ = 0 := by simp
      _ ≤ 1 := zero_le_one
  obtain ⟨z₁⟩ := hι
  have hline : ∃ z₀ : ι, ∀ v, ∃ c : ℂ, L v = c • (Pi.single z₀ (1 : ℂ) : ι → ℂ) := by
    by_cases h0 : ∀ v, L v = 0
    · exact ⟨z₁, fun v => ⟨0, by simp [h0 v]⟩⟩
    · push Not at h0
      obtain ⟨v₀, hv₀⟩ := h0
      obtain ⟨z₀, c₀, hc₀⟩ := hL v₀
      have hc₀0 : c₀ ≠ 0 := by rintro rfl; apply hv₀; rw [hc₀, zero_smul]
      refine ⟨z₀, fun v => ?_⟩
      obtain ⟨y, c, hc⟩ := hL v
      by_cases hcy : c = 0
      · exact ⟨0, by rw [hc, hcy, zero_smul, zero_smul]⟩
      by_cases hy : y = z₀
      · exact ⟨c, by rw [hc, hy]⟩
      exfalso
      obtain ⟨w, d, hd⟩ := hL (v₀ + v)
      rw [map_add, hc₀, hc] at hd
      by_cases hw : w = z₀
      · subst hw
        have := congrFun hd y
        simp [Pi.single_apply, hy, hcy] at this
      · have := congrFun hd z₀
        simp [Pi.single_apply, hy, Ne.symm hy, hw, Ne.symm hw, hc₀0] at this
  obtain ⟨z₀, hz₀⟩ := hline
  have hle : LinearMap.range L ≤ Submodule.span ℂ {(Pi.single z₀ (1 : ℂ) : ι → ℂ)} := by
    intro w hw
    obtain ⟨v, hv⟩ := LinearMap.mem_range.mp hw
    obtain ⟨c, hc⟩ := hz₀ v
    rw [← hv, hc]
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)
  calc Module.finrank ℂ (LinearMap.range L)
      ≤ Module.finrank ℂ (Submodule.span ℂ {(Pi.single z₀ (1 : ℂ) : ι → ℂ)}) :=
        Submodule.finrank_mono hle
    _ = 1 := finrank_span_singleton (by
        intro h; have := congrFun h z₀; simp at this)
    _ ≤ 1 := le_refl _

/-- **No unitary collapse.**  No unitary matrix (in particular no Cayley step of any
Hamiltonian) maps every state to a multiple of a site state when there are two sites. -/
theorem no_unitary_collapse {U : Matrix ι ι ℂ} (hU : Uᴴ * U = 1) {x y : ι} (hxy : x ≠ y) :
    ¬ ∀ v, ∃ (z : ι) (c : ℂ), U *ᵥ v = c • Pi.single z 1 := by
  intro h
  have hinj : Function.Injective (Matrix.mulVecLin U) := by
    intro v w hvw
    have := congrArg (fun u => Uᴴ *ᵥ u) hvw
    simpa [mulVec_mulVec, hU] using this
  obtain ⟨v, hv⟩ := no_collapse (Matrix.mulVecLin U) hinj hxy
  obtain ⟨z, c, hz⟩ := h v
  exact hv z c hz

/-- **Freezing, not collapse.**  If `H` is diagonal in position, the Cayley evolution
preserves `|ψ(x)|²` at every site and every step. -/
theorem frozen (V : ι → ℝ) (ψ : ι → ℂ) (k : ℕ) (x : ι) :
    ‖((cayley (diagonal fun y => ((V y : ℝ) : ℂ))) ^ k *ᵥ ψ) x‖ = ‖ψ x‖ := by
  set c : ι → ℂ := fun y => (1 - Complex.I * (V y : ℂ)) / (1 + Complex.I * (V y : ℂ))
  have hne : ∀ y, (1 + Complex.I * (V y : ℂ)) ≠ 0 := by
    intro y h
    have := congrArg Complex.re h
    simp at this
  have hB : (1 : Matrix ι ι ℂ) + Complex.I • diagonal (fun y => ((V y : ℝ) : ℂ)) =
      diagonal (fun y => 1 + Complex.I * (V y : ℂ)) := by
    ext i j; by_cases h : i = j
    · subst h; simp [diagonal_apply_eq]
    · simp [diagonal_apply_ne _ h, one_apply_ne h]
  have hC : (1 : Matrix ι ι ℂ) - Complex.I • diagonal (fun y => ((V y : ℝ) : ℂ)) =
      diagonal (fun y => 1 - Complex.I * (V y : ℂ)) := by
    ext i j; by_cases h : i = j
    · subst h; simp [diagonal_apply_eq]
    · simp [diagonal_apply_ne _ h, one_apply_ne h]
  have hU : cayley (diagonal fun y => ((V y : ℝ) : ℂ)) = diagonal c := by
    have hdet := isUnit_det_one_add_I (A := diagonal fun y => ((V y : ℝ) : ℂ))
      (by rw [IsHermitian, diagonal_conjTranspose]; congr 1; ext y; simp)
    unfold cayley
    have hDB : diagonal c * diagonal (fun y => 1 + Complex.I * (V y : ℂ)) =
        diagonal (fun y => 1 - Complex.I * (V y : ℂ)) := by
      rw [diagonal_mul_diagonal]; congr 1; ext y; simp only [c]; field_simp [hne y]
    rw [hC, ← hDB, ← hB, mul_assoc, mul_nonsing_inv _ hdet, mul_one]
  have hc1 : ∀ y, ‖c y‖ = 1 := by
    intro y
    have := QE.Phys.cayley_unitary (2 * V y)
    simp only [c]
    have e : ((2 * V y : ℝ) : ℂ) / 2 = (V y : ℂ) := by push_cast; ring
    rw [e] at this; exact this
  rw [hU, diagonal_pow, mulVec_diagonal, norm_mul, Pi.pow_apply, norm_pow, hc1, one_pow,
    one_mul]

end NoCollapse

/-! ## Granular Zeno bound -/

section Zeno

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Coordinate projection onto a set of sites. -/
def proj (P : Finset ι) (ψ : ι → ℂ) : ι → ℂ := fun x => if x ∈ P then ψ x else 0

lemma nsq_split (P : Finset ι) (φ : ι → ℂ) :
    nsq φ = nsq (proj P φ) + nsq (φ - proj P φ) := by
  unfold nsq proj; rw [← sum_add_distrib]
  refine sum_congr rfl fun x _ => ?_
  by_cases h : x ∈ P <;> simp [h]

/-- **Leakage bound.**  If `‖Aφ‖ ≤ a‖φ‖` for all `φ` and `Pψ = ψ`, then
`‖(1−P)Uψ‖² ≤ (2a)² ‖ψ‖²` for the Cayley step `U` of `A`. -/
theorem zeno_leak {A : Matrix ι ι ℂ} (hA : A.IsHermitian) {a : ℝ}
    (hbd : ∀ v, nsq (A *ᵥ v) ≤ a ^ 2 * nsq v) (P : Finset ι) (ψ : ι → ℂ)
    (hP : proj P ψ = ψ) :
    nsq (cayley A *ᵥ ψ - proj P (cayley A *ᵥ ψ)) ≤ (2 * a) ^ 2 * nsq ψ := by
  set φ := cayley A *ᵥ ψ
  have hφ : nsq φ = nsq ψ := (cayley_unitary hA).2.2 ψ
  -- (1 + iA) φ = (1 - iA) ψ
  have hstep : (1 + Complex.I • A) *ᵥ φ = (1 - Complex.I • A) *ᵥ ψ := by
    simp only [φ, mulVec_mulVec, cayley_step hA]
  have hdiff : φ - ψ = -(Complex.I • (A *ᵥ (φ + ψ))) := by
    simp only [add_mulVec, sub_mulVec, one_mulVec, smul_mulVec] at hstep
    rw [mulVec_add, smul_add]
    linear_combination (exp := 1) hstep
  have h1 : nsq (φ - ψ) ≤ (2 * a) ^ 2 * nsq ψ := by
    rw [hdiff, nsq_neg, nsq_smul, Complex.norm_I, one_pow, one_mul]
    calc nsq (A *ᵥ (φ + ψ)) ≤ a ^ 2 * nsq (φ + ψ) := hbd _
      _ ≤ a ^ 2 * (2 * nsq φ + 2 * nsq ψ) :=
          mul_le_mul_of_nonneg_left (nsq_add_le φ ψ) (sq_nonneg a)
      _ = (2 * a) ^ 2 * nsq ψ := by rw [hφ]; ring
  refine le_trans ?_ h1
  unfold nsq; refine sum_le_sum fun x _ => ?_
  simp only [proj, Pi.sub_apply]
  by_cases hx : x ∈ P
  · simp [hx]
  · have : ψ x = 0 := by
      have := congrFun hP x; simp only [proj, hx, ite_false] at this; exact this.symm
    simp [hx, this]

/-- One measure-and-evolve step keeps at least `1 − (2a)²` of the norm. -/
theorem zeno_step {A : Matrix ι ι ℂ} (hA : A.IsHermitian) {a : ℝ}
    (hbd : ∀ v, nsq (A *ᵥ v) ≤ a ^ 2 * nsq v) (P : Finset ι) (ψ : ι → ℂ)
    (hP : proj P ψ = ψ) :
    (1 - (2 * a) ^ 2) * nsq ψ ≤ nsq (proj P (cayley A *ᵥ ψ)) := by
  have h := zeno_leak hA hbd P ψ hP
  have hs := nsq_split P (cayley A *ᵥ ψ)
  rw [(cayley_unitary hA).2.2 ψ] at hs
  linarith

lemma proj_proj (P : Finset ι) (φ : ι → ℂ) : proj P (proj P φ) = proj P φ := by
  funext x; by_cases h : x ∈ P <;> simp [proj, h]

/-- **Granular Zeno bound.**  `N` repeated measure-and-evolve steps keep
`‖(PU)^N ψ‖² ≥ (1 − (2a)²)^N ‖ψ‖² ≥ (1 − N(2a)²) ‖ψ‖²` when `2a ≤ 1`. -/
theorem zeno_iterate {A : Matrix ι ι ℂ} (hA : A.IsHermitian) {a : ℝ} (ha : 0 ≤ a)
    (hx : 2 * a ≤ 1) (hbd : ∀ v, nsq (A *ᵥ v) ≤ a ^ 2 * nsq v) (P : Finset ι)
    (ψ : ι → ℂ) (hP : proj P ψ = ψ) (N : ℕ) :
    (1 - (2 * a) ^ 2) ^ N * nsq ψ ≤
        nsq ((fun φ => proj P (cayley A *ᵥ φ))^[N] ψ) ∧
      1 - N * (2 * a) ^ 2 ≤ (1 - (2 * a) ^ 2) ^ N := by
  have hx2 : 0 ≤ 1 - (2 * a) ^ 2 := by nlinarith
  refine ⟨?_, ?_⟩
  · have inv : ∀ k, proj P ((fun φ => proj P (cayley A *ᵥ φ))^[k] ψ) =
        (fun φ => proj P (cayley A *ᵥ φ))^[k] ψ := by
      intro k; cases k with
      | zero => simpa using hP
      | succ k => rw [Function.iterate_succ_apply']; exact proj_proj P _
    induction N with
    | zero => simp
    | succ k ih =>
      rw [Function.iterate_succ_apply', pow_succ]
      have := zeno_step hA hbd P _ (inv k)
      calc (1 - (2 * a) ^ 2) ^ k * (1 - (2 * a) ^ 2) * nsq ψ
          = (1 - (2 * a) ^ 2) * ((1 - (2 * a) ^ 2) ^ k * nsq ψ) := by ring
        _ ≤ (1 - (2 * a) ^ 2) * nsq ((fun φ => proj P (cayley A *ᵥ φ))^[k] ψ) :=
            mul_le_mul_of_nonneg_left ih hx2
        _ ≤ _ := this
  · have := one_add_mul_le_pow (a := -(2 * a) ^ 2) (by nlinarith) N
    simpa [sub_eq_add_neg] using this

/-- **Zeno bound for a Hamiltonian.**  With `‖Hψ‖ ≤ h‖ψ‖` and `x = τh/ħ ≤ 1`, the
Cayley step `U` of `τH/(2ħ)` satisfies `‖(1−P)Uψ‖² ≤ x²‖ψ‖²` and
`‖(PU)^N ψ‖² ≥ (1 − x²)^N ‖ψ‖²`. -/
theorem zeno_hamiltonian {H : Matrix ι ι ℂ} (hH : H.IsHermitian) {h τ ħ : ℝ}
    (hh : 0 ≤ h) (hτ : 0 ≤ τ) (hħ : 0 < ħ) (hbd : ∀ v, nsq (H *ᵥ v) ≤ h ^ 2 * nsq v)
    (hx : τ * h / ħ ≤ 1) (P : Finset ι) (ψ : ι → ℂ) (hP : proj P ψ = ψ) (N : ℕ) :
    let U := cayley (((τ / (2 * ħ) : ℝ) : ℂ) • H)
    nsq (U *ᵥ ψ - proj P (U *ᵥ ψ)) ≤ (τ * h / ħ) ^ 2 * nsq ψ ∧
      (1 - (τ * h / ħ) ^ 2) ^ N * nsq ψ ≤ nsq ((fun φ => proj P (U *ᵥ φ))^[N] ψ) := by
  intro U
  set A := ((τ / (2 * ħ) : ℝ) : ℂ) • H
  have hA : A.IsHermitian := by
    unfold IsHermitian; rw [conjTranspose_smul, hH.eq, Complex.star_def, Complex.conj_ofReal]
  set a := τ / (2 * ħ) * h
  have ha : 0 ≤ a := by positivity
  have h2a : 2 * a = τ * h / ħ := by simp only [a]; field_simp
  have hbdA : ∀ v, nsq (A *ᵥ v) ≤ a ^ 2 * nsq v := by
    intro v
    rw [smul_mulVec, nsq_smul, Complex.norm_real, Real.norm_eq_abs, sq_abs]
    calc (τ / (2 * ħ)) ^ 2 * nsq (H *ᵥ v) ≤ (τ / (2 * ħ)) ^ 2 * (h ^ 2 * nsq v) :=
          mul_le_mul_of_nonneg_left (hbd v) (sq_nonneg _)
      _ = a ^ 2 * nsq v := by simp only [a]; ring
  rw [← h2a]
  exact ⟨zeno_leak hA hbdA P ψ hP, (zeno_iterate hA ha (by rw [h2a]; exact hx) hbdA P ψ hP N).1⟩

end Zeno

/-- **Zeno bound for the atom.**  The hypothesis of `zeno_hamiltonian` holds for the
atom with `h = max(Z e² G(0)/ε₀, 2nħ²/(μa²))`. -/
theorem atom_zeno {n : ℕ} (S : Finset (Conf n)) {ħ m M a Z e ε₀ τ : ℝ}
    (hm : 0 < m) (hM : 0 < M) (ha : a ≠ 0) (hZ : 0 ≤ Z) (hε₀ : 0 < ε₀) (hħ : 0 < ħ)
    (hτ : 0 ≤ τ) (G : (Fin n → ℤ) → ℝ) (hG : ∀ r, G r ≤ G 0) (hG' : ∀ r, 0 ≤ G r)
    (hx : τ * max (Z * e ^ 2 * G 0 / ε₀) (2 * n * ħ ^ 2 / ((m * M / (m + M)) * a ^ 2)) / ħ ≤ 1)
    (P : Finset S) (ψ : S → ℂ) (hP : proj P ψ = ψ) (N : ℕ) :
    nsq (cayley (((τ / (2 * ħ) : ℝ) : ℂ) • atomH S ħ m M a Z e ε₀ G) *ᵥ ψ -
        proj P (cayley (((τ / (2 * ħ) : ℝ) : ℂ) • atomH S ħ m M a Z e ε₀ G) *ᵥ ψ)) ≤
      (τ * max (Z * e ^ 2 * G 0 / ε₀) (2 * n * ħ ^ 2 / ((m * M / (m + M)) * a ^ 2)) / ħ) ^ 2 *
        nsq ψ ∧
    (1 - (τ * max (Z * e ^ 2 * G 0 / ε₀) (2 * n * ħ ^ 2 / ((m * M / (m + M)) * a ^ 2)) / ħ) ^ 2)
        ^ N * nsq ψ ≤
      nsq ((fun φ => proj P (cayley (((τ / (2 * ħ) : ℝ) : ℂ) • atomH S ħ m M a Z e ε₀ G) *ᵥ φ))^[N]
        ψ) := by
  have hh : 0 ≤ max (Z * e ^ 2 * G 0 / ε₀) (2 * n * ħ ^ 2 / ((m * M / (m + M)) * a ^ 2)) :=
    le_trans (div_nonneg (mul_nonneg (mul_nonneg hZ (sq_nonneg e)) (hG' 0)) hε₀.le)
      (le_max_left _ _)
  exact zeno_hamiltonian (ham_isHermitian S _ _ _) hh hτ hħ
    (atom_norm_bound S hm hM ha hZ hε₀ G hG hG') hx P ψ hP N

/-! ## Lattice spontaneous collapse (GRW) -/

section GRW

variable {N : ℕ} [NeZero N]

/-- Overlap of the collapse profile with its shift: `c = ∑ⱼ √(g(j) g(j+1))`. -/
noncomputable def overlap (g : ZMod N → ℝ) : ℝ := ∑ j, Real.sqrt (g j * g (j + 1))

/-- Collapse (jump) operator centred at `k`: multiplication by `√g(x − k)`. -/
noncomputable def jump (g : ZMod N → ℝ) (k : ZMod N) (ψ : ZMod N → ℂ) : ZMod N → ℂ :=
  fun x => (Real.sqrt (g (x - k)) : ℂ) * ψ x

/-- Free lattice Hamiltonian on the ring, hopping `t`. -/
def H0 (t : ℝ) (ψ : ZMod N → ℂ) : ZMod N → ℂ :=
  fun x => (t : ℂ) * (2 * ψ x - ψ (x + 1) - ψ (x - 1))

/-- The same with the hopping multiplied by `c`. -/
def H0c (t c : ℝ) (ψ : ZMod N → ℂ) : ZMod N → ℂ :=
  fun x => (t : ℂ) * (2 * ψ x - c * ψ (x + 1) - c * ψ (x - 1))

lemma sum_sub_left (f : ZMod N → ℝ) (x : ZMod N) : ∑ k, f (x - k) = ∑ j, f j :=
  Equiv.sum_comp (Equiv.subLeft x) f

/-- **Collapse centres are counted.**  `∑ₖ ‖Lₖψ‖² = ‖ψ‖²`. -/
theorem grw_complete (g : ZMod N → ℝ) (hg : ∀ x, 0 ≤ g x) (h1 : ∑ x, g x = 1)
    (ψ : ZMod N → ℂ) : ∑ k, nsq (jump g k ψ) = nsq ψ := by
  unfold nsq jump
  rw [sum_comm]
  refine sum_congr rfl fun x _ => ?_
  simp only [norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs,
    Real.sq_sqrt (hg _)]
  rw [← sum_mul, sum_sub_left g x, h1, one_mul]

/-- **Collapse sandwich.**  `∑ₖ Lₖ H₀ Lₖ` is `H₀` with its hopping multiplied by the
overlap `c`. -/
theorem grw_sandwich (g : ZMod N → ℝ) (hg : ∀ x, 0 ≤ g x) (h1 : ∑ x, g x = 1) (t : ℝ)
    (ψ : ZMod N → ℂ) (x : ZMod N) :
    ∑ k, jump g k (H0 t (jump g k ψ)) x = H0c t (overlap g) ψ x := by
  simp only [jump, H0, H0c]
  have hsq : ∀ u, 0 ≤ u → (Real.sqrt u : ℂ) * (Real.sqrt u : ℂ) = (u : ℂ) := by
    intro u hu; rw [← Complex.ofReal_mul, Real.mul_self_sqrt hu]
  have hmul : ∀ u v, 0 ≤ u →
      (Real.sqrt u : ℂ) * (Real.sqrt v : ℂ) = (Real.sqrt (u * v) : ℂ) := by
    intro u v hu; rw [Real.sqrt_mul hu, Complex.ofReal_mul]
  have pt : ∀ k, (Real.sqrt (g (x - k)) : ℂ) * ((t : ℂ) *
      (2 * ((Real.sqrt (g (x - k)) : ℂ) * ψ x)
        - (Real.sqrt (g (x + 1 - k)) : ℂ) * ψ (x + 1)
        - (Real.sqrt (g (x - 1 - k)) : ℂ) * ψ (x - 1)))
      = (t : ℂ) * ((g (x - k) : ℂ) * (2 * ψ x)
        - (Real.sqrt (g (x - k) * g (x + 1 - k)) : ℂ) * ψ (x + 1)
        - (Real.sqrt (g (x - k) * g (x - 1 - k)) : ℂ) * ψ (x - 1)) := by
    intro k
    rw [← hsq _ (hg (x - k)), ← hmul _ _ (hg (x - k)), ← hmul _ _ (hg (x - k))]; ring
  rw [sum_congr rfl fun k _ => pt k, ← mul_sum]
  congr 1
  simp only [sum_sub_distrib, ← sum_mul]
  have A1 : ∑ k, (g (x - k) : ℂ) = 1 := by
    rw [← Complex.ofReal_sum, sum_sub_left g x, h1, Complex.ofReal_one]
  have A2 : ∑ k, (Real.sqrt (g (x - k) * g (x + 1 - k)) : ℂ) = (overlap g : ℂ) := by
    rw [← Complex.ofReal_sum]; congr 1; unfold overlap
    rw [← sum_sub_left (fun j => Real.sqrt (g j * g (j + 1))) x]
    refine sum_congr rfl fun k _ => ?_
    rw [show x + 1 - k = x - k + 1 by ring]
  have A3 : ∑ k, (Real.sqrt (g (x - k) * g (x - 1 - k)) : ℂ) = (overlap g : ℂ) := by
    rw [← Complex.ofReal_sum]; congr 1; unfold overlap
    rw [← sum_sub_left (fun j => Real.sqrt (g j * g (j + 1))) (x - 1)]
    refine sum_congr rfl fun k _ => ?_
    rw [show x - 1 - k + 1 = x - k by ring, mul_comm]
  rw [A1, A2, A3]; ring

lemma sum_shift_add (f : ZMod N → ℝ) (c : ZMod N) : ∑ x, f (x + c) = ∑ x, f x :=
  Equiv.sum_comp (Equiv.addRight c) f

/-- `c ∈ [0, 1]`. -/
theorem overlap_bounds (g : ZMod N → ℝ) (hg : ∀ x, 0 ≤ g x) (h1 : ∑ x, g x = 1) :
    0 ≤ overlap g ∧ overlap g ≤ 1 := by
  refine ⟨sum_nonneg fun _ _ => Real.sqrt_nonneg _, ?_⟩
  have hb : ∀ j, Real.sqrt (g j * g (j + 1)) ≤ (g j + g (j + 1)) / 2 := by
    intro j
    rw [Real.sqrt_le_iff]
    refine ⟨by linarith [hg j, hg (j + 1)], ?_⟩
    nlinarith [sq_nonneg (g j - g (j + 1))]
  calc overlap g ≤ ∑ j, (g j + g (j + 1)) / 2 := sum_le_sum fun j _ => hb j
    _ = 1 := by
      rw [← sum_div, sum_add_distrib, sum_shift_add g 1, h1]; norm_num

/-- A collapse profile of width one granule (`g = δ₀`, `N ≥ 2`) has overlap `0`:
the collapse is a projective position measurement. -/
theorem overlap_delta (hN : 1 < N) :
    overlap (fun x : ZMod N => if x = 0 then (1 : ℝ) else 0) = 0 := by
  have h10 : (1 : ZMod N) ≠ 0 := by
    intro h
    have := congrArg ZMod.val h
    rw [ZMod.val_one_eq_one_mod, Nat.mod_eq_of_lt hN, ZMod.val_zero] at this
    exact one_ne_zero this
  unfold overlap
  refine sum_eq_zero fun j _ => ?_
  by_cases hj : j = 0
  · subst hj; simp [h10]
  · simp [hj]

/-- Hopping expectation `⟨ψ, (T + T⁻¹) ψ⟩`. -/
noncomputable def hopExp (ψ : ZMod N → ℂ) : ℂ := ∑ x, star (ψ x) * (ψ (x + 1) + ψ (x - 1))

lemma hopExp_le (ψ : ZMod N → ℂ) : ‖hopExp ψ‖ ≤ 2 * nsq ψ := by
  unfold hopExp
  refine (norm_sum_le _ _).trans ?_
  have hpt : ∀ x, ‖star (ψ x) * (ψ (x + 1) + ψ (x - 1))‖ ≤
      ‖ψ x‖ ^ 2 + ‖ψ (x + 1)‖ ^ 2 / 2 + ‖ψ (x - 1)‖ ^ 2 / 2 := by
    intro x
    rw [norm_mul, norm_star]
    have := norm_add_le (ψ (x + 1)) (ψ (x - 1))
    have h0 := norm_nonneg (ψ x)
    nlinarith [sq_nonneg (‖ψ x‖ - ‖ψ (x + 1)‖), sq_nonneg (‖ψ x‖ - ‖ψ (x - 1)‖),
      mul_le_mul_of_nonneg_left this h0]
  refine (sum_le_sum fun x _ => hpt x).trans (le_of_eq ?_)
  rw [sum_add_distrib, sum_add_distrib, ← sum_div, ← sum_div,
    sum_shift_add (fun y => ‖ψ y‖ ^ 2) 1]
  have : ∑ x, ‖ψ (x - 1)‖ ^ 2 = ∑ x, ‖ψ x‖ ^ 2 := by
    simpa [sub_eq_add_neg] using sum_shift_add (fun y => ‖ψ y‖ ^ 2) (-1)
  rw [this]; unfold nsq; ring

/-- **Energy injected by one collapse.**  `⟨ψ, ∑ₖ Lₖ H₀ Lₖ ψ⟩ − ⟨ψ, H₀ ψ⟩ = (1 − c) t ⟨ψ,(T+T⁻¹)ψ⟩`,
and its modulus is at most `2(1 − c) t ‖ψ‖²` (`= (1−c) ħ²/(ma²) ‖ψ‖²` for
`t = ħ²/(2ma²)`). -/
theorem grw_energy (g : ZMod N → ℝ) (hg : ∀ x, 0 ≤ g x) (h1 : ∑ x, g x = 1) (t : ℝ)
    (ht : 0 ≤ t) (ψ : ZMod N → ℂ) :
    (∑ x, star (ψ x) * ∑ k, jump g k (H0 t (jump g k ψ)) x) - ∑ x, star (ψ x) * H0 t ψ x
        = (((1 - overlap g) * t : ℝ) : ℂ) * hopExp ψ ∧
      ‖(∑ x, star (ψ x) * ∑ k, jump g k (H0 t (jump g k ψ)) x) - ∑ x, star (ψ x) * H0 t ψ x‖
        ≤ (1 - overlap g) * (2 * t) * nsq ψ := by
  have he : (∑ x, star (ψ x) * ∑ k, jump g k (H0 t (jump g k ψ)) x) -
      ∑ x, star (ψ x) * H0 t ψ x = (((1 - overlap g) * t : ℝ) : ℂ) * hopExp ψ := by
    simp only [grw_sandwich g hg h1 t ψ]
    rw [← sum_sub_distrib, hopExp, mul_sum]
    refine sum_congr rfl fun x _ => ?_
    simp only [H0, H0c]; push_cast; ring
  refine ⟨he, ?_⟩
  rw [he, norm_mul, Complex.norm_real, Real.norm_eq_abs]
  have hc := overlap_bounds g hg h1
  rw [abs_of_nonneg (mul_nonneg (by linarith [hc.2]) ht)]
  have := hopExp_le ψ
  have h0 : 0 ≤ (1 - overlap g) * t := mul_nonneg (by linarith [hc.2]) ht
  calc (1 - overlap g) * t * ‖hopExp ψ‖ ≤ (1 - overlap g) * t * (2 * nsq ψ) :=
        mul_le_mul_of_nonneg_left this h0
    _ = _ := by ring

end GRW

end QE.Atom
