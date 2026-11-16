-- SPDX-License-Identifier: MIT
-- Copyright 2026 Metere Industries, Inc. Author: Alfredo Metere.
-- Quasi-Euclidean Granular Geometry. Any derivative work must carry this notice:
--   This work is derivative of the Quasi-Euclidean Granular Geometry book
--   authored by Alfredo Metere. Copyright 2026 Metere Industries, Inc.
--   All rights reserved
-- See LICENSE.md and NOTICE.

import QuasiEuclidean.Basic
import QuasiEuclidean.Ch07_Multi

/-!
# Chapter 16 — Physical consequences

The granule is instantiated as the Planck length (or the smallest resolvable
length in the problem).  All statements are exact identities or inequalities
for every positive value of the granule (and of the physical constants), so
they apply with `ε = ℓ_P` literally.
-/

open Real Finset Filter Topology Complex

namespace QE.Phys

/-! ## The vacuum is a state -/

/-- Occupation-number amplitudes of a single mode. -/
abbrev Amp := ℕ → ℂ

/-- The Fock vacuum `|0⟩`. -/
noncomputable def vac : Amp := fun n => if n = 0 then 1 else 0

/-- The one-quantum state `|1⟩`. -/
noncomputable def one : Amp := fun n => if n = 1 then 1 else 0

/-- Number operator. -/
noncomputable def numOp (ψ : Amp) : Amp := fun n => (n : ℂ) * ψ n

/-- Annihilation operator `(aψ)(n) = √(n+1) ψ(n+1)`. -/
noncomputable def ann (ψ : Amp) : Amp := fun n => ((Real.sqrt (n + 1) : ℝ) : ℂ) * ψ (n + 1)

/-- Creation operator `(a†ψ)(n) = √n ψ(n-1)` (and `0` at `n = 0`). -/
noncomputable def cre (ψ : Amp) : Amp :=
  fun n => if n = 0 then 0 else ((Real.sqrt n : ℝ) : ℂ) * ψ (n - 1)

/-- Squared norm truncated to the first `M+1` occupation numbers. -/
noncomputable def nsq (M : ℕ) (ψ : Amp) : ℝ := ∑ n ∈ Finset.range (M + 1), ‖ψ n‖ ^ 2

/-- **The vacuum is a unit vector, not the zero vector.**  It is annihilated by
`a` and has number eigenvalue `0`, but `|0⟩ ≠ 0`; it has norm one (in every
truncation), is orthogonal to `|1⟩`, and `a†|0⟩ = |1⟩`. -/
theorem vacuum_is_state (M : ℕ) :
    vac ≠ 0 ∧ nsq M vac = 1 ∧ nsq M (0 : Amp) = 0 ∧ ann vac = 0 ∧ numOp vac = 0 ∧
    cre vac = one ∧ ∑ n ∈ Finset.range (M + 2), (starRingEnd ℂ) (vac n) * one n = 0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro h; have := congrFun h 0; simp [vac] at this
  · unfold nsq; rw [Finset.sum_eq_single 0]
    · simp [vac]
    · intro b _ hb; simp [vac, hb]
    · simp
  · simp [nsq]
  · funext n; simp [ann, vac]
  · funext n; by_cases h : n = 0 <;> simp [numOp, vac, h]
  · funext n
    by_cases h0 : n = 0
    · simp [cre, one, h0]
    · by_cases h1 : n = 1
      · subst h1; simp [cre, vac, one]
      · have : n - 1 ≠ 0 := by omega
        simp [cre, vac, one, h0, h1, this]
  · apply Finset.sum_eq_zero; intro n _
    by_cases h : n = 0 <;> simp [vac, one, h]

/-- The canonical commutation relation `[a, a†] = 1` holds exactly on the
full (untruncated) occupation-number sequence space. -/
theorem ccr_ladder (ψ : Amp) : ann (cre ψ) - cre (ann ψ) = ψ := by
  funext n
  simp only [ann, cre, Pi.sub_apply]
  have h1 : (n + 1 : ℕ) ≠ 0 := by omega
  simp only [Nat.add_sub_cancel, h1, ↓reduceIte]
  have hs1 : ((Real.sqrt ((n : ℝ) + 1) : ℝ) : ℂ) * ((Real.sqrt (((n + 1 : ℕ) : ℝ)) : ℝ) : ℂ)
      = (n : ℂ) + 1 := by
    rw [show (((n + 1 : ℕ) : ℝ)) = (n : ℝ) + 1 by push_cast; ring, ← Complex.ofReal_mul,
      Real.mul_self_sqrt (by positivity)]
    push_cast; ring
  by_cases h0 : n = 0
  · subst h0; simp
  · simp only [h0, ↓reduceIte]
    have hs2 : ((Real.sqrt (n : ℝ) : ℝ) : ℂ) * ((Real.sqrt (((n - 1 : ℕ) : ℝ) + 1) : ℝ) : ℂ)
        = (n : ℂ) := by
      rw [← Complex.ofReal_mul]
      have : (((n - 1 : ℕ) : ℝ) + 1) = n := by
        rw [Nat.cast_sub (by omega)]; push_cast; ring
      rw [this, Real.mul_self_sqrt (by positivity)]; push_cast; ring
    have e : n - 1 + 1 = n := by omega
    rw [e]
    calc ((Real.sqrt ((n : ℝ) + 1) : ℝ) : ℂ) * (((Real.sqrt (((n + 1 : ℕ) : ℝ)) : ℝ) : ℂ) * ψ n)
          - ((Real.sqrt (n : ℝ) : ℝ) : ℂ) * (((Real.sqrt (((n - 1 : ℕ) : ℝ) + 1) : ℝ) : ℂ) * ψ n)
        = (((Real.sqrt ((n : ℝ) + 1) : ℝ) : ℂ) * ((Real.sqrt (((n + 1 : ℕ) : ℝ)) : ℝ) : ℂ)) * ψ n
          - (((Real.sqrt (n : ℝ) : ℝ) : ℂ) * ((Real.sqrt (((n - 1 : ℕ) : ℝ) + 1) : ℝ) : ℂ)) * ψ n := by
          ring
      _ = ψ n := by rw [hs1, hs2]; ring

/-- The vacuum–one-quantum qubit `(|0⟩ + |1⟩)/√2` is normalised, and a
number measurement on it yields `0` or `1` with probability `1/2` each:
the outcome "vacuum" is one of the two values of a fair bit. -/
theorem vacuum_qubit (M : ℕ) (hM : 1 ≤ M) :
    let φ : Amp := fun n => ((Real.sqrt 2)⁻¹ : ℂ) * (vac n + one n)
    nsq M φ = 1 ∧ ‖φ 0‖ ^ 2 = 1 / 2 ∧ ‖φ 1‖ ^ 2 = 1 / 2 ∧
    Real.binEntropy (1 / 2) = Real.log 2 := by
  intro φ
  have h0 : ‖φ 0‖ ^ 2 = 1 / 2 := by
    simp only [φ, vac, one]; simp
  have h1 : ‖φ 1‖ ^ 2 = 1 / 2 := by
    simp only [φ, vac, one]; simp
  refine ⟨?_, h0, h1, by rw [one_div]; exact Real.binEntropy_two_inv⟩
  unfold nsq
  have hz : ∀ n ∈ Finset.range (M + 1), n ≠ 0 → n ≠ 1 → ‖φ n‖ ^ 2 = 0 := by
    intro n _ hn0 hn1; simp [φ, vac, one, hn0, hn1]
  rw [← Finset.sum_subset (s₁ := {0, 1}) (by
      intro n hn; simp at hn; simp; omega) (fun n hn hn' => by
      simp at hn'; exact hz n hn hn'.1 hn'.2)]
  rw [Finset.sum_pair (by norm_num), h0, h1]; norm_num

/-- The occupation register: `M` fermionic modes have `2^M` Fock states, the
vacuum (all occupation numbers zero) being one of them. -/
theorem fermion_register (M : ℕ) :
    Fintype.card (Fin M → Fin 2) = 2 ^ M ∧ (fun _ => 0 : Fin M → Fin 2) ∈ (Finset.univ) := by
  simp

/-- The field register: a periodic box of `N³` sites has `N³` modes; with each
mode truncated at `M` quanta, the Fock basis has `(M+1)^{N³}` states, the vacuum
(all modes reading `0`) among them. -/
theorem field_register (N M : ℕ) :
    Fintype.card (Fin N × Fin N × Fin N) = N ^ 3 ∧
    Fintype.card ((Fin N × Fin N × Fin N) → Fin (M + 1)) = (M + 1) ^ (N ^ 3) ∧
    (fun _ => 0 : (Fin N × Fin N × Fin N) → Fin (M + 1)) ∈ Finset.univ := by
  refine ⟨?_, ?_, Finset.mem_univ _⟩
  · simp; ring
  · simp; ring_nf

/-! ## No canonical commutation relation in finite dimensions -/

/-- **No finite-dimensional CCR** (Wintner–Wielandt trace argument): there are
no `n × n` complex matrices with `XP - PX = iħ·1`, for `n ≥ 1`, `ħ ≠ 0`. -/
theorem no_finite_ccr (n : ℕ) (hn : 0 < n) (X P : Matrix (Fin n) (Fin n) ℂ) (ħ : ℝ)
    (hħ : ħ ≠ 0) : X * P - P * X ≠ (Complex.I * ħ) • (1 : Matrix (Fin n) (Fin n) ℂ) := by
  intro h
  have ht := congrArg Matrix.trace h
  rw [Matrix.trace_sub, Matrix.trace_mul_comm X P, sub_self, Matrix.trace_smul,
    Matrix.trace_one, Fintype.card_fin, smul_eq_mul] at ht
  have hn' : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
  have : Complex.I * (ħ : ℂ) * n ≠ 0 :=
    mul_ne_zero (mul_ne_zero Complex.I_ne_zero (by exact_mod_cast hħ)) hn'
  exact this ht.symm

/-! ## Weyl form: clock and shift -/

lemma pow_mod_of_pow_eq_one {ω : ℂ} {N : ℕ} (h : ω ^ N = 1) (m : ℕ) : ω ^ (m % N) = ω ^ m := by
  conv_rhs => rw [← Nat.div_add_mod m N, pow_add, pow_mul, h, one_pow, one_mul]

/-- Clock operator on `ℂ^{ZMod N}`. -/
noncomputable def clock (N : ℕ) [NeZero N] (ω : ℂ) (ψ : ZMod N → ℂ) : ZMod N → ℂ :=
  fun k => ω ^ k.val * ψ k

/-- Shift operator on `ℂ^{ZMod N}`. -/
def shiftZ (N : ℕ) (ψ : ZMod N → ℂ) : ZMod N → ℂ := fun k => ψ (k + 1)

/-- **Weyl relation** `V U = ω U V` for clock and shift, `ω^N = 1`: the
exponentiated CCR survives in finite dimension. -/
theorem weyl_relation (N : ℕ) [NeZero N] (ω : ℂ) (hω : ω ^ N = 1) (ψ : ZMod N → ℂ) :
    shiftZ N (clock N ω ψ) = fun k => ω * clock N ω (shiftZ N ψ) k := by
  funext k
  simp only [shiftZ, clock]
  rw [ZMod.val_add, pow_mod_of_pow_eq_one hω, pow_add, ZMod.val_one_eq_one_mod,
    pow_mod_of_pow_eq_one hω, pow_one]
  ring

/-! ## Lattice position and momentum -/

variable (ε ħ : ℝ)

/-- Lattice position `(Xψ)(k) = 2εk ψ(k)`. -/
noncomputable def posX (ψ : ℤ → ℂ) : ℤ → ℂ := fun k => ((2 * ε * k : ℝ) : ℂ) * ψ k

/-- Forward-difference momentum `P_ε = -iħ D⁺`. -/
noncomputable def momF (ψ : ℤ → ℂ) : ℤ → ℂ :=
  fun k => -Complex.I * ħ * (ψ (k + 1) - ψ k) / (2 * ε)

/-- Symmetric lattice momentum `P° = -iħ (ψ(k+1) - ψ(k-1)) / (4ε)`. -/
noncomputable def momC (ψ : ℤ → ℂ) : ℤ → ℂ :=
  fun k => -Complex.I * ħ * (ψ (k + 1) - ψ (k - 1)) / (4 * ε)

/-- Shift `(Sψ)(k) = ψ(k+1)`. -/
def shL (ψ : ℤ → ℂ) : ℤ → ℂ := fun k => ψ (k + 1)

/-- Averaging ("cosine") operator `Cψ(k) = (ψ(k+1) + ψ(k-1))/2`. -/
noncomputable def cosOp (ψ : ℤ → ℂ) : ℤ → ℂ := fun k => (ψ (k + 1) + ψ (k - 1)) / 2

/-- **Lattice commutator** `[X, P_ε] = iħ S` exactly. -/
theorem comm_forward (hε : ε ≠ 0) (ψ : ℤ → ℂ) :
    posX ε (momF ε ħ ψ) - momF ε ħ (posX ε ψ) = fun k => Complex.I * ħ * shL ψ k := by
  funext k
  simp only [posX, momF, shL, Pi.sub_apply]
  have hε' : (ε : ℂ) ≠ 0 := by exact_mod_cast hε
  push_cast
  field_simp
  ring

/-- Equivalent form `[X, P_ε] = iħ - 2ε P_ε`. -/
theorem comm_forward' (hε : ε ≠ 0) (ψ : ℤ → ℂ) :
    posX ε (momF ε ħ ψ) - momF ε ħ (posX ε ψ)
      = fun k => Complex.I * ħ * ψ k - 2 * ε * momF ε ħ ψ k := by
  rw [comm_forward ε ħ hε]
  funext k
  simp only [shL, momF]
  have hε' : (ε : ℂ) ≠ 0 := by exact_mod_cast hε
  field_simp
  ring_nf

/-- **Symmetric lattice commutator** `[X, P°] = iħ C`. -/
theorem comm_central (hε : ε ≠ 0) (ψ : ℤ → ℂ) :
    posX ε (momC ε ħ ψ) - momC ε ħ (posX ε ψ) = fun k => Complex.I * ħ * cosOp ψ k := by
  funext k
  simp only [posX, momC, cosOp, Pi.sub_apply]
  have hε' : (ε : ℂ) ≠ 0 := by exact_mod_cast hε
  push_cast
  field_simp
  ring

/-- **Exact lattice "Pythagoras"**: `C² + (2ε/ħ)² (P°)² = 1` as operators;
`C` plays the role of `cos`, `(2ε/ħ) P°` of `sin`. -/
theorem cos_sin_identity (hε : ε ≠ 0) (hħ : ħ ≠ 0) (ψ : ℤ → ℂ) (k : ℤ) :
    cosOp (cosOp ψ) k + ((2 * ε / ħ : ℝ) : ℂ) ^ 2 * momC ε ħ (momC ε ħ ψ) k = ψ k := by
  simp only [cosOp, momC]
  have e1 : k + 1 - 1 = k := by ring
  have e2 : k - 1 + 1 = k := by ring
  rw [e1, e2]
  have hε' : (ε : ℂ) ≠ 0 := by exact_mod_cast hε
  have hħ' : (ħ : ℂ) ≠ 0 := by exact_mod_cast hħ
  push_cast
  field_simp
  ring_nf
  rw [Complex.I_sq]; ring

/-- Plane waves diagonalise the symmetric momentum and `C`:
`P° e^{iθk} = (ħ/2ε) sin θ · e^{iθk}`, `C e^{iθk} = cos θ · e^{iθk}`. -/
theorem plane_wave (hε : ε ≠ 0) (θ : ℝ) :
    (momC ε ħ (fun k => Complex.exp (θ * k * Complex.I))
        = fun k : ℤ => ((ħ / (2 * ε) * Real.sin θ : ℝ) : ℂ) * Complex.exp (θ * k * Complex.I)) ∧
    (cosOp (fun k => Complex.exp (θ * k * Complex.I))
        = fun k : ℤ => ((Real.cos θ : ℝ) : ℂ) * Complex.exp (θ * k * Complex.I)) := by
  have hε' : (ε : ℂ) ≠ 0 := by exact_mod_cast hε
  have ep : ∀ k : ℤ, Complex.exp (θ * ((k + 1 : ℤ) : ℂ) * Complex.I)
      = Complex.exp (θ * k * Complex.I) * Complex.exp (θ * Complex.I) := by
    intro k; rw [← Complex.exp_add]; congr 1; push_cast; ring
  have em : ∀ k : ℤ, Complex.exp (θ * ((k - 1 : ℤ) : ℂ) * Complex.I)
      = Complex.exp (θ * k * Complex.I) * Complex.exp (-(θ * Complex.I)) := by
    intro k; rw [← Complex.exp_add]; congr 1; push_cast; ring
  constructor
  · funext k
    simp only [momC]
    rw [ep, em]
    push_cast
    rw [Complex.sin]
    field_simp
    ring_nf
  · funext k
    simp only [cosOp]
    rw [ep, em]
    push_cast
    rw [Complex.cos]
    ring_nf

/-- A lattice position eigenstate has `⟨C⟩ = 0`, so the lattice uncertainty
bound `ΔX ΔP° ≥ (ħ/2)|⟨C⟩|` is consistent with `ΔX = 0`. -/
theorem position_eigen_cos (j : ℤ) :
    cosOp (fun k => if k = j then (1 : ℂ) else 0) j = 0 := by
  simp [cosOp]

/-! ## Self-energy of a point-sphere charge -/

/-- **Shadow (classical continuum approximation).** Field energy outside a
charged sphere of radius `ε`, computed with the continuum Coulomb field:
`(ε₀/2) ∫_ε^∞ E² 4πr² dr = q²/(8π ε₀ ε)`. -/
theorem shell_self_energy (q ε₀ ε : ℝ) (hε₀ : 0 < ε₀) (hε : 0 < ε) :
    ε₀ / 2 * ∫ r in Set.Ioi ε, (q / (4 * π * ε₀ * r ^ 2)) ^ 2 * (4 * π * r ^ 2)
      = q ^ 2 / (8 * π * ε₀ * ε) := by
  have hπ : 0 < π := Real.pi_pos
  have hcongr : ∫ r in Set.Ioi ε, (q / (4 * π * ε₀ * r ^ 2)) ^ 2 * (4 * π * r ^ 2)
      = ∫ r in Set.Ioi ε, (q ^ 2 / (4 * π * ε₀ ^ 2)) * r ^ (-2 : ℝ) := by
    apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
    intro r hr
    have hr0 : 0 < r := lt_trans hε hr
    simp only
    rw [Real.rpow_neg hr0.le, Real.rpow_two]
    field_simp
  rw [hcongr, MeasureTheory.integral_const_mul,
    integral_Ioi_rpow_of_lt (by norm_num : (-2 : ℝ) < -1) hε]
  rw [show (-2 : ℝ) + 1 = -1 by norm_num, Real.rpow_neg_one]
  field_simp
  ring

/-- **Shadow (classical continuum approximation).** Field energy inside a
uniformly charged continuum ball of radius `ε`: `q²/(40π ε₀ ε)`. -/
theorem ball_interior_energy (q ε₀ ε : ℝ) (hε₀ : 0 < ε₀) (hε : 0 < ε) :
    ε₀ / 2 * ∫ r in (0:ℝ)..ε, (q * r / (4 * π * ε₀ * ε ^ 3)) ^ 2 * (4 * π * r ^ 2)
      = q ^ 2 / (40 * π * ε₀ * ε) := by
  have hπ : 0 < π := Real.pi_pos
  have hf : (fun r : ℝ => (q * r / (4 * π * ε₀ * ε ^ 3)) ^ 2 * (4 * π * r ^ 2))
      = fun r => (q ^ 2 / (4 * π * ε₀ ^ 2 * ε ^ 6)) * r ^ 4 := by
    funext r; field_simp
  rw [hf, intervalIntegral.integral_const_mul, integral_pow]
  field_simp
  norm_num; ring

/-- Total self-energy of a uniformly charged ball of radius `ε`:
`3q²/(20π ε₀ ε)`; with `q²/(4πε₀) = αħc` and `ε = ℓ_P` the shell value is
`αħc/(2ℓ_P)`. -/
theorem ball_self_energy (q ε₀ ε : ℝ) (hε₀ : 0 < ε₀) (hε : 0 < ε) :
    q ^ 2 / (8 * π * ε₀ * ε) + q ^ 2 / (40 * π * ε₀ * ε) = 3 * q ^ 2 / (20 * π * ε₀ * ε) := by
  have hπ : 0 < π := Real.pi_pos
  field_simp; ring

/-- **Granular self-energy of a point-sphere charge** (Lebesgue-free).  Let
`G` be the Dirichlet Green's function of `-Δ_ε` on a finite region `Ω ∋ s`
(`-Δ_ε G = δ^s`, `G = 0` off `Ω`), so that the potential of a charge `q` on
the point `s` is `φ = q G / ε₀`.  The field energy, a finite lattice sum
`(ε₀/2) ∑ₓ ∑ᵢ |∂ᵢφ|² (2ε)ⁿ`, equals `q² G(s) / (2 ε₀)` exactly, and is bounded
below by `q² (2ε)² / ((2ε)ⁿ 4 n ε₀)`. -/
theorem lattice_self_energy (ε : ℝ) (hε : 0 < ε) {n : ℕ} (i₀ : Fin n)
    (Ω S : Finset (Fin n → ℤ)) (s : Fin n → ℤ) (hs : s ∈ Ω) (G : (Fin n → ℤ) → ℝ)
    (hG0 : ∀ x, x ∉ Ω → G x = 0) (hG : ∀ x ∈ Ω, -QE.Multi.lap ε G x = QE.Multi.deltaN ε s x)
    (hΩS : Ω ⊆ S) (hS : ∀ i, ∀ x ∈ Ω, x - QE.Multi.e i ∈ S) (q ε₀ : ℝ) (hε₀ : 0 < ε₀) :
    ε₀ / 2 * ∑ x ∈ S, ∑ i, (q / ε₀ * QE.Multi.pd ε i G x) ^ 2 * (2 * ε) ^ n
        = q ^ 2 * G s / (2 * ε₀) ∧
    q ^ 2 * (2 * ε) ^ 2 / ((2 * ε) ^ n * (4 * n * ε₀))
        ≤ ε₀ / 2 * ∑ x ∈ S, ∑ i, (q / ε₀ * QE.Multi.pd ε i G x) ^ 2 * (2 * ε) ^ n := by
  obtain ⟨-, -, hlow⟩ := QE.Multi.green_props ε hε i₀ Ω s hs G hG0 hG
  have hE := QE.Multi.energy_identity ε G Ω S hG0 hΩS hS
  have h2 : (0 : ℝ) < 2 * ε := by linarith
  have hpow : (0 : ℝ) < (2 * ε) ^ n := by positivity
  have hL : ∑ x ∈ S, G x * (-QE.Multi.lap ε G x) = G s / (2 * ε) ^ n := by
    rw [Finset.sum_eq_single s]
    · rw [hG s hs]; simp [QE.Multi.deltaN]; ring
    · intro x _ hxs
      by_cases hxΩ : x ∈ Ω
      · rw [hG x hxΩ]; simp [QE.Multi.deltaN, hxs]
      · rw [hG0 x hxΩ, zero_mul]
    · intro h; exact absurd (hΩS hs) h
  have hrow : ∀ x, ∑ i, (q / ε₀ * QE.Multi.pd ε i G x) ^ 2 * (2 * ε) ^ n
      = (q / ε₀) ^ 2 * (2 * ε) ^ n * ∑ i, (QE.Multi.pd ε i G x) ^ 2 := by
    intro x; rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro i _; ring
  have hU : ε₀ / 2 * ∑ x ∈ S, ∑ i, (q / ε₀ * QE.Multi.pd ε i G x) ^ 2 * (2 * ε) ^ n
      = q ^ 2 * G s / (2 * ε₀) := by
    simp only [hrow]
    rw [← Finset.mul_sum, ← hE, hL]
    field_simp
  refine ⟨hU, ?_⟩
  rw [hU]
  have hn : (0 : ℝ) < n := by
    have : 0 < n := Fin.pos i₀
    exact_mod_cast this
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  have hq : 0 ≤ q ^ 2 := sq_nonneg q
  have hlow' : (2 * ε) ^ 2 ≤ 2 * n * G s * (2 * ε) ^ n := by
    rwa [div_le_iff₀ hpow] at hlow
  nlinarith [mul_le_mul_of_nonneg_left hlow' (by positivity : 0 ≤ q ^ 2 * (2 * ε₀))]

/-- In three dimensions: the granular self-energy is at least `q² / (24 ε₀ ε)`,
for every finite region (attained for the one-point region). -/
theorem lattice_self_energy_3d (ε : ℝ) (hε : 0 < ε) (Ω S : Finset (Fin 3 → ℤ))
    (s : Fin 3 → ℤ) (hs : s ∈ Ω) (G : (Fin 3 → ℤ) → ℝ)
    (hG0 : ∀ x, x ∉ Ω → G x = 0) (hG : ∀ x ∈ Ω, -QE.Multi.lap ε G x = QE.Multi.deltaN ε s x)
    (hΩS : Ω ⊆ S) (hS : ∀ i, ∀ x ∈ Ω, x - QE.Multi.e i ∈ S) (q ε₀ : ℝ) (hε₀ : 0 < ε₀) :
    q ^ 2 / (24 * ε₀ * ε)
      ≤ ε₀ / 2 * ∑ x ∈ S, ∑ i, (q / ε₀ * QE.Multi.pd ε i G x) ^ 2 * (2 * ε) ^ 3 := by
  have h := (lattice_self_energy ε hε (0 : Fin 3) Ω S s hs G hG0 hG hΩS hS q ε₀ hε₀).2
  have e : q ^ 2 * (2 * ε) ^ 2 / ((2 * ε) ^ 3 * (4 * ((3 : ℕ) : ℝ) * ε₀)) = q ^ 2 / (24 * ε₀ * ε) := by
    push_cast; field_simp; ring
  rw [e] at h; exact h

/-- The granular lower bound in Planck units: with `q²/(4πε₀) = αħc`,
`q²/(24 ε₀ ℓ) = (π/6) αħc/ℓ`. -/
theorem lattice_self_energy_planck (q ε₀ ℓ α ħ c : ℝ) (hε₀ : 0 < ε₀) (hℓ : 0 < ℓ)
    (hα : q ^ 2 / (4 * π * ε₀) = α * ħ * c) :
    q ^ 2 / (24 * ε₀ * ℓ) = π / 6 * (α * ħ * c / ℓ) := by
  have hπ : 0 < π := Real.pi_pos
  rw [← hα]; field_simp; ring

theorem shell_planck (q ε₀ ℓ α ħ c : ℝ) (hε₀ : 0 < ε₀) (hℓ : 0 < ℓ)
    (hα : q ^ 2 / (4 * π * ε₀) = α * ħ * c) :
    q ^ 2 / (8 * π * ε₀ * ℓ) = α * ħ * c / (2 * ℓ) := by
  have hπ : 0 < π := Real.pi_pos
  rw [← hα]; field_simp; ring

/-! ## Zero-point energy with the Planck cutoff -/

/-- **Shadow (classical continuum approximation).** Spherical-cutoff
zero-point energy density of a massless scalar:
`∫₀^K (4πk²/(2π)³)(ħck/2) dk = ħ c K⁴ /(16 π²)`. -/
theorem zpe_density (ħ c K : ℝ) :
    ∫ k in (0:ℝ)..K, (4 * π * k ^ 2 / (2 * π) ^ 3) * (ħ * c * k / 2)
      = ħ * c * K ^ 4 / (16 * π ^ 2) := by
  have hπ : 0 < π := Real.pi_pos
  have hf : (fun k : ℝ => (4 * π * k ^ 2 / (2 * π) ^ 3) * (ħ * c * k / 2))
      = fun k => (ħ * c / (4 * π ^ 2)) * k ^ 3 := by
    funext k; field_simp; ring
  rw [hf, intervalIntegral.integral_const_mul, integral_pow]
  field_simp; ring

/-- With the cutoff at the lattice Brillouin zone `K = π / a`, `a = 2ℓ_P`:
`ρ = π² ħ c / (256 ℓ_P⁴)`. -/
theorem zpe_planck (ħ c ℓ : ℝ) (hℓ : 0 < ℓ) :
    ħ * c * (π / (2 * ℓ)) ^ 4 / (16 * π ^ 2) = π ^ 2 * ħ * c / (256 * ℓ ^ 4) := by
  have hπ : 0 < π := Real.pi_pos
  field_simp; ring

/-- Lattice dispersion `ω(θ) = (2c/a) √(Σᵢ sin² θᵢ)` on the cubic lattice. -/
noncomputable def omegaLat (c a : ℝ) (θ : Fin 3 → ℝ) : ℝ :=
  2 * c / a * Real.sqrt (∑ i, Real.sin (θ i) ^ 2)

/-- The lattice zero-point energy is a finite sum, nonnegative and bounded by
`#modes · √3 ħ c / a`. -/
theorem zpe_lattice_bound {ι : Type*} (modes : Finset ι) (θ : ι → Fin 3 → ℝ)
    (ħ c a : ℝ) (hħ : 0 ≤ ħ) (hc : 0 ≤ c) (ha : 0 < a) :
    0 ≤ ∑ m ∈ modes, ħ * omegaLat c a (θ m) / 2 ∧
    ∑ m ∈ modes, ħ * omegaLat c a (θ m) / 2 ≤ modes.card * (Real.sqrt 3 * ħ * c / a) := by
  have hle : ∀ m, omegaLat c a (θ m) ≤ 2 * c / a * Real.sqrt 3 := by
    intro m
    unfold omegaLat
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    apply Real.sqrt_le_sqrt
    have : ∀ i, Real.sin (θ m i) ^ 2 ≤ 1 := fun i => Real.sin_sq_le_one _
    calc ∑ i, Real.sin (θ m i) ^ 2 ≤ ∑ _i : Fin 3, (1 : ℝ) := Finset.sum_le_sum fun i _ => this i
      _ = 3 := by simp
  have hnn : ∀ m, 0 ≤ omegaLat c a (θ m) := fun m => by unfold omegaLat; positivity
  constructor
  · exact Finset.sum_nonneg fun m _ => by have := hnn m; positivity
  · calc ∑ m ∈ modes, ħ * omegaLat c a (θ m) / 2
        ≤ ∑ _m ∈ modes, ħ * (2 * c / a * Real.sqrt 3) / 2 :=
          Finset.sum_le_sum fun m _ => by
            have := hle m
            have := mul_le_mul_of_nonneg_left this hħ
            linarith
      _ = modes.card * (Real.sqrt 3 * ħ * c / a) := by
          rw [Finset.sum_const, nsmul_eq_mul]; field_simp

lemma sum_cos_roots (N : ℕ) (hN : 2 ≤ N) :
    ∑ j ∈ Finset.range N, Real.cos (2 * π * j / N) = 0 := by
  have hζ := Complex.isPrimitiveRoot_exp N (by omega)
  have h0 := hζ.geom_sum_eq_zero (by omega)
  have hj : ∀ j : ℕ, (Complex.exp (2 * π * Complex.I / N)) ^ j
      = Complex.exp (((2 * π * j / N : ℝ)) * Complex.I) := by
    intro j; rw [← Complex.exp_nat_mul]; congr 1; push_cast; ring
  have h1 := congrArg Complex.re h0
  rw [Complex.re_sum] at h1
  simp only [hj, Complex.exp_ofReal_mul_I_re, Complex.zero_re] at h1
  exact h1

/-- `∑_{j<N} sin²(πj/N) = N/2` for `N ≥ 2` (a finite trigonometric sum). -/
lemma sum_sin_sq_modes (N : ℕ) (hN : 2 ≤ N) :
    ∑ j ∈ Finset.range N, Real.sin (π * j / N) ^ 2 = N / 2 := by
  have h : ∀ j : ℕ, Real.sin (π * j / N) ^ 2 = 1 / 2 - Real.cos (2 * π * j / N) / 2 := by
    intro j; rw [Real.sin_sq_eq_half_sub, show 2 * (π * j / N) = 2 * π * j / N by ring]
  simp only [h, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range, ← Finset.sum_div,
    sum_cos_roots N hN, nsmul_eq_mul]
  ring

lemma omegaLat_term_bounds (ħ c a : ℝ) (hħ : 0 ≤ ħ) (hc : 0 ≤ c) (ha : 0 < a) (θ : Fin 3 → ℝ) :
    ħ * c / (a * Real.sqrt 3) * (∑ i, Real.sin (θ i) ^ 2) ≤ ħ * omegaLat c a θ / 2 ∧
    ħ * omegaLat c a θ / 2 ≤ Real.sqrt 3 * ħ * c / a := by
  set S := ∑ i, Real.sin (θ i) ^ 2 with hS
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun i _ => sq_nonneg _
  have hS3 : S ≤ 3 := by
    have : ∀ i, Real.sin (θ i) ^ 2 ≤ 1 := fun i => Real.sin_sq_le_one _
    calc S ≤ ∑ _i : Fin 3, (1 : ℝ) := Finset.sum_le_sum fun i _ => this i
      _ = 3 := by simp
  have h3 : 0 < Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num)
  have hsq : Real.sqrt S ≤ Real.sqrt 3 := Real.sqrt_le_sqrt hS3
  have hss : Real.sqrt S ^ 2 = S := Real.sq_sqrt hS0
  have key : S ≤ Real.sqrt S * Real.sqrt 3 := by nlinarith [Real.sqrt_nonneg S]
  have hω : ħ * omegaLat c a θ / 2 = ħ * c * Real.sqrt S / a := by
    unfold omegaLat; rw [← hS]; field_simp
  rw [hω]
  constructor
  · rw [div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) ha]
    have : ħ * c * Real.sqrt S * (a * Real.sqrt 3) = a * (ħ * c * (Real.sqrt S * Real.sqrt 3)) := by
      ring
    rw [this]
    have := mul_le_mul_of_nonneg_left key (by positivity : 0 ≤ ħ * c)
    nlinarith
  · rw [div_le_div_iff_of_pos_right ha]
    have := mul_le_mul_of_nonneg_left hsq (by positivity : 0 ≤ ħ * c)
    linarith

/-- **Zero-point energy of the periodic lattice box** (granular, Lebesgue-free).
A massless lattice scalar on the periodic cubic box of `N³` sites, spacing
`a`, has exactly `N³` modes, `θ = π m / N` for `m ∈ {0,…,N-1}³`, with
`ω = (2c/a)(∑ sin² θᵢ)^{1/2}`.  Its zero-point energy, a finite sum over the
Brillouin zone, satisfies `√3 ħ c N³ / (2a) ≤ E₀ ≤ √3 ħ c N³ / a`; the energy
density `E₀ / (Na)³` lies in `[√3 ħc/(2a⁴), √3 ħc/a⁴]`. -/
theorem zpe_box (N : ℕ) (hN : 2 ≤ N) (ħ c a : ℝ) (hħ : 0 ≤ ħ) (hc : 0 ≤ c) (ha : 0 < a) :
    Real.sqrt 3 * ħ * c * N ^ 3 / (2 * a) ≤
      ∑ m₁ ∈ Finset.range N, ∑ m₂ ∈ Finset.range N, ∑ m₃ ∈ Finset.range N,
        ħ * omegaLat c a ![π * m₁ / N, π * m₂ / N, π * m₃ / N] / 2 ∧
    ∑ m₁ ∈ Finset.range N, ∑ m₂ ∈ Finset.range N, ∑ m₃ ∈ Finset.range N,
        ħ * omegaLat c a ![π * m₁ / N, π * m₂ / N, π * m₃ / N] / 2
      ≤ N ^ 3 * (Real.sqrt 3 * ħ * c / a) := by
  set f : ℕ → ℝ := fun j => Real.sin (π * j / N) ^ 2 with hf
  have hsum := sum_sin_sq_modes N hN
  have h3 : 0 < Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num)
  have h33 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  constructor
  · calc Real.sqrt 3 * ħ * c * N ^ 3 / (2 * a)
        = ∑ m₁ ∈ Finset.range N, ∑ m₂ ∈ Finset.range N, ∑ m₃ ∈ Finset.range N,
            ħ * c / (a * Real.sqrt 3) * (f m₁ + f m₂ + f m₃) := by
          simp only [← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_const,
            Finset.card_range, nsmul_eq_mul]
          simp only [hf] at hsum ⊢
          rw [hsum]
          field_simp
          rw [h33]; ring
      _ ≤ _ := by
          apply Finset.sum_le_sum; intro m₁ _
          apply Finset.sum_le_sum; intro m₂ _
          apply Finset.sum_le_sum; intro m₃ _
          have := (omegaLat_term_bounds ħ c a hħ hc ha ![π * m₁ / N, π * m₂ / N, π * m₃ / N]).1
          simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
            Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] at this
          simpa [hf, add_assoc] using this
  · calc _ ≤ ∑ _m₁ ∈ Finset.range N, ∑ _m₂ ∈ Finset.range N, ∑ _m₃ ∈ Finset.range N,
            Real.sqrt 3 * ħ * c / a := by
          apply Finset.sum_le_sum; intro m₁ _
          apply Finset.sum_le_sum; intro m₂ _
          apply Finset.sum_le_sum; intro m₃ _
          exact (omegaLat_term_bounds ħ c a hħ hc ha _).2
      _ = _ := by simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; ring

/-- The classical spherical-cutoff estimate with `K = π/a` compared with the
lattice bounds: `ħ c K⁴/(16π²) = (π²/16) ħc/a⁴` (pure algebra). -/
theorem zpe_shadow_value (ħ c a : ℝ) (ha : a ≠ 0) :
    ħ * c * (π / a) ^ 4 / (16 * π ^ 2) = π ^ 2 / 16 * (ħ * c / a ^ 4) := by
  have hπ : 0 < π := Real.pi_pos
  field_simp

/-- Free lattice dispersion: the discrete Laplacian acts on plane waves by
`ψ(k+1) - 2ψ(k) + ψ(k-1) = -4 sin²(θ/2) ψ(k)`, so the band
`E(θ) = (2ħ²/ma²) sin²(θ/2)` is bounded by `2ħ²/(ma²)`. -/
theorem laplacian_plane_wave (θ : ℝ) (k : ℤ) :
    Complex.exp (θ * ((k + 1 : ℤ) : ℂ) * Complex.I) - 2 * Complex.exp (θ * k * Complex.I)
      + Complex.exp (θ * ((k - 1 : ℤ) : ℂ) * Complex.I)
      = ((-4 * Real.sin (θ / 2) ^ 2 : ℝ) : ℂ) * Complex.exp (θ * k * Complex.I) := by
  have h := congrFun (plane_wave 1 1 one_ne_zero θ).2 k
  simp only [cosOp] at h
  have hc : Real.cos θ = 1 - 2 * Real.sin (θ / 2) ^ 2 := by
    have h2 := Real.cos_sq_add_sin_sq (θ / 2)
    have : Real.cos θ = Real.cos (2 * (θ / 2)) := by ring_nf
    rw [this, Real.cos_two_mul]; nlinarith
  have h' : Complex.exp (θ * ((k + 1 : ℤ) : ℂ) * Complex.I)
      + Complex.exp (θ * ((k - 1 : ℤ) : ℂ) * Complex.I)
      = 2 * (((Real.cos θ : ℝ) : ℂ) * Complex.exp (θ * k * Complex.I)) := by
    rw [← h]; ring
  rw [show Complex.exp (θ * ((k + 1 : ℤ) : ℂ) * Complex.I) - 2 * Complex.exp (θ * k * Complex.I)
      + Complex.exp (θ * ((k - 1 : ℤ) : ℂ) * Complex.I)
      = (Complex.exp (θ * ((k + 1 : ℤ) : ℂ) * Complex.I)
      + Complex.exp (θ * ((k - 1 : ℤ) : ℂ) * Complex.I)) - 2 * Complex.exp (θ * k * Complex.I) by ring,
    h', hc]
  push_cast; ring

theorem band_bound (θ ħ m a : ℝ) (hm : 0 < m) (ha : a ≠ 0) :
    0 ≤ 2 * ħ ^ 2 / (m * a ^ 2) * Real.sin (θ / 2) ^ 2 ∧
    2 * ħ ^ 2 / (m * a ^ 2) * Real.sin (θ / 2) ^ 2 ≤ 2 * ħ ^ 2 / (m * a ^ 2) := by
  have hpos : 0 ≤ 2 * ħ ^ 2 / (m * a ^ 2) := by positivity
  exact ⟨by positivity, by
    have := Real.sin_sq_le_one (θ / 2)
    calc 2 * ħ ^ 2 / (m * a ^ 2) * Real.sin (θ / 2) ^ 2 ≤ 2 * ħ ^ 2 / (m * a ^ 2) * 1 :=
          mul_le_mul_of_nonneg_left this hpos
      _ = _ := mul_one _⟩

/-- **Doubler**: the symmetric lattice momentum annihilates the nonzero
staggered wave `(-1)^k = e^{iπk}` at the zone edge, as well as constants. -/
theorem doubler (hε : ε ≠ 0) :
    momC ε ħ (fun k => Complex.exp (π * k * Complex.I)) = 0 ∧
    momC ε ħ (fun _ => (1 : ℂ)) = 0 ∧
    (fun k : ℤ => Complex.exp (π * k * Complex.I)) ≠ 0 := by
  refine ⟨?_, ?_, ?_⟩
  · rw [(plane_wave ε ħ hε π).1]; funext k; simp [Real.sin_pi]
  · funext k; simp [momC]
  · intro h; have := congrFun h 0; simp at this

/-! ## The Planck point -/

/-- With `ℓ_P = √(ħG/c³)` and `m_P = √(ħc/G)`: the reduced Compton wavelength
of `m_P` and the gravitational radius `G m_P / c²` (half its Schwarzschild
radius) both equal `ℓ_P`. -/
theorem planck_point (ħ G c : ℝ) (hħ : 0 < ħ) (hG : 0 < G) (hc : 0 < c) :
    ħ / (Real.sqrt (ħ * c / G) * c) = Real.sqrt (ħ * G / c ^ 3) ∧
    G * Real.sqrt (ħ * c / G) / c ^ 2 = Real.sqrt (ħ * G / c ^ 3) := by
  have hm : 0 < Real.sqrt (ħ * c / G) := Real.sqrt_pos.mpr (by positivity)
  have hl : 0 < Real.sqrt (ħ * G / c ^ 3) := Real.sqrt_pos.mpr (by positivity)
  have sm := Real.sq_sqrt (show 0 ≤ ħ * c / G by positivity)
  have sl := Real.sq_sqrt (show 0 ≤ ħ * G / c ^ 3 by positivity)
  constructor
  · have lhs_pos : 0 < ħ / (Real.sqrt (ħ * c / G) * c) := by positivity
    have : (ħ / (Real.sqrt (ħ * c / G) * c)) ^ 2 = Real.sqrt (ħ * G / c ^ 3) ^ 2 := by
      rw [sl, div_pow, mul_pow, sm]; field_simp
    exact (pow_left_inj₀ lhs_pos.le hl.le two_ne_zero).mp this
  · have lhs_pos : 0 < G * Real.sqrt (ħ * c / G) / c ^ 2 := by positivity
    have : (G * Real.sqrt (ħ * c / G) / c ^ 2) ^ 2 = Real.sqrt (ħ * G / c ^ 3) ^ 2 := by
      rw [sl, div_pow, mul_pow, sm]; field_simp
    exact (pow_left_inj₀ lhs_pos.le hl.le two_ne_zero).mp this

/-! ## Rayleigh–Jeans with the granular cutoff -/

/-- **Shadow (classical continuum approximation).** Classical equipartition
with two polarisations and the cutoff `|k| ≤ K`:
`∫₀^K (k²/π²) k_B T dk = K³ k_B T / (3π²)` — finite, but not Planck's law. -/
theorem rayleigh_jeans_cutoff (kT K : ℝ) :
    ∫ k in (0:ℝ)..K, (2 * (4 * π * k ^ 2) / (2 * π) ^ 3) * kT = K ^ 3 * kT / (3 * π ^ 2) := by
  have hπ : 0 < π := Real.pi_pos
  have hf : (fun k : ℝ => (2 * (4 * π * k ^ 2) / (2 * π) ^ 3) * kT)
      = fun k => (kT / π ^ 2) * k ^ 2 := by
    funext k; field_simp; ring
  rw [hf, intervalIntegral.integral_const_mul, integral_pow]
  field_simp; norm_num; ring

/-- **Equipartition on the lattice** (granular, Lebesgue-free).  The periodic
box of `N³` sites, spacing `a`, carries exactly `2N³` electromagnetic modes
(two polarisations per Brillouin-zone wave vector); classical equipartition,
`k_B T` per mode, gives the energy density `2 k_B T / a³` exactly. -/
theorem rj_lattice (N : ℕ) (hN : N ≠ 0) (kT a : ℝ) (ha : a ≠ 0) :
    (∑ _m₁ ∈ Finset.range N, ∑ _m₂ ∈ Finset.range N, ∑ _m₃ ∈ Finset.range N, 2 * kT)
      / ((N : ℝ) * a) ^ 3 = 2 * kT / a ^ 3 := by
  have hN' : (N : ℝ) ≠ 0 := by exact_mod_cast hN
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  field_simp

/-- The continuum (spherical-cutoff) estimate with `K = π/a` is exactly `π/6`
of the lattice count: the ball `|k| ≤ π/a` fills the fraction `π/6` of the
Brillouin cube `[-π/a, π/a]³` (pure algebra). -/
theorem rj_shadow_ratio (kT a : ℝ) (ha : a ≠ 0) :
    (π / a) ^ 3 * kT / (3 * π ^ 2) = π / 6 * (2 * kT / a ^ 3) := by
  have hπ : 0 < π := Real.pi_pos
  field_simp; ring

/-! ## Granular time and unitarity -/

/-- One forward-difference (explicit Euler) step of `iħ ψ' = E ψ` with time
granule `τ` multiplies the amplitude by `1 - iτE/ħ`, of modulus
`√(1 + (τE/ħ)²) > 1` for `E ≠ 0`: the naive granular time derivative is not
unitary. -/
theorem euler_step_norm (x : ℝ) :
    ‖(1 : ℂ) - Complex.I * x‖ ^ 2 = 1 + x ^ 2 := by
  rw [Complex.sq_norm, Complex.normSq_apply]; simp; ring

theorem euler_not_unitary (x : ℝ) (hx : x ≠ 0) : 1 < ‖(1 : ℂ) - Complex.I * x‖ := by
  have h := euler_step_norm x
  have hx2 : 0 < x ^ 2 := by positivity
  have h0 : 0 ≤ ‖(1 : ℂ) - Complex.I * x‖ := norm_nonneg _
  nlinarith

/-- The symmetric (Cayley / Crank–Nicolson) granular step
`(1 - iτE/2ħ)/(1 + iτE/2ħ)` has modulus exactly `1`: granular time evolution
with the symmetric difference is exactly unitary. -/
theorem cayley_unitary (x : ℝ) :
    ‖((1 : ℂ) - Complex.I * (x / 2)) / ((1 : ℂ) + Complex.I * (x / 2))‖ = 1 := by
  have hn : ‖(1 : ℂ) + Complex.I * (x / 2)‖ ≠ 0 := by
    intro h
    have : ‖(1 : ℂ) + Complex.I * (x / 2)‖ ^ 2 = 1 + (x / 2) ^ 2 := by
      rw [Complex.sq_norm, Complex.normSq_apply]; simp; ring
    rw [h] at this; nlinarith [sq_nonneg (x / 2)]
  rw [norm_div, div_eq_one_iff_eq hn]
  have e1 : ‖(1 : ℂ) - Complex.I * (x / 2)‖ ^ 2 = ‖(1 : ℂ) + Complex.I * (x / 2)‖ ^ 2 := by
    rw [Complex.sq_norm, Complex.sq_norm, Complex.normSq_apply, Complex.normSq_apply]; simp
  exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp e1

/-- **First law at one nat per cell.**  For a Schwarzschild hole of mass `M`,
`A = 16π G² M² / c⁴`, `S = k_B A/(4ℓ_P²)` with `ℓ_P² = ħG/c³`, and
`T_H = ħ c³/(8π G M k_B)`, one has `T_H · dS/dM = c²`. -/
theorem first_law (ħ G c k M : ℝ) (hħ : 0 < ħ) (hG : 0 < G) (hc : 0 < c) (hk : 0 < k)
    (hM : 0 < M) :
    (ħ * c ^ 3 / (8 * π * G * M * k)) * (k * (32 * π * G ^ 2 * M / c ^ 4) / (4 * (ħ * G / c ^ 3)))
      = c ^ 2 := by
  have hπ : 0 < π := Real.pi_pos
  field_simp
  ring

/-! ## Exact Casimir energy of a lattice string -/

/-- Dirichlet modes of the lattice string with `N` interior sites:
`ψ_j(k) = sin(jπk/(N+1))` vanishes at both ends and satisfies
`ψ(k+1) - 2ψ(k) + ψ(k-1) = -4 sin²(θ/2) ψ(k)`, `θ = jπ/(N+1)`. -/
theorem dirichlet_mode (N j : ℕ) (k : ℝ) :
    let θ := j * π / (N + 1)
    Real.sin (θ * 0) = 0 ∧ Real.sin (θ * (N + 1)) = 0 ∧
    Real.sin (θ * (k + 1)) - 2 * Real.sin (θ * k) + Real.sin (θ * (k - 1))
      = -4 * Real.sin (θ / 2) ^ 2 * Real.sin (θ * k) := by
  intro θ
  refine ⟨by simp, ?_, ?_⟩
  · have : θ * (N + 1) = (j : ℕ) * π := by
      simp only [θ]; field_simp
    rw [this]; exact Real.sin_nat_mul_pi j
  · have hc : Real.cos θ = 1 - 2 * Real.sin (θ / 2) ^ 2 := by
      have : Real.cos θ = Real.cos (2 * (θ / 2)) := by ring_nf
      rw [this, Real.cos_two_mul]; nlinarith [Real.cos_sq_add_sin_sq (θ / 2)]
    have e1 : θ * (k + 1) = θ * k + θ := by ring
    have e2 : θ * (k - 1) = θ * k - θ := by ring
    rw [e1, e2, Real.sin_add, Real.sin_sub, hc]; ring

lemma sin_sum_telescope (x : ℝ) (N : ℕ) :
    2 * Real.sin (x / 2) * ∑ j ∈ Finset.range N, Real.sin ((j + 1 : ℝ) * x)
      = Real.cos (x / 2) - Real.cos ((N + 1 / 2 : ℝ) * x) := by
  induction N with
  | zero => simp; ring_nf
  | succ n ih =>
    rw [Finset.sum_range_succ, mul_add, ih]
    have h : 2 * Real.sin (x / 2) * Real.sin (((n : ℕ) + 1 : ℝ) * x)
        = Real.cos ((n + 1 / 2 : ℝ) * x) - Real.cos ((((n + 1 : ℕ) : ℝ) + 1 / 2) * x) := by
      have a1 : (n + 1 / 2 : ℝ) * x = ((n : ℝ) + 1) * x - x / 2 := by ring
      have a2 : ((((n + 1 : ℕ) : ℝ) + 1 / 2)) * x = ((n : ℝ) + 1) * x + x / 2 := by push_cast; ring
      rw [a1, a2, Real.cos_sub, Real.cos_add]; ring
    rw [h]; ring

/-- **Exact zero-point energy of a lattice string** of `N` interior sites,
spacing `a`, Dirichlet ends, modes `ω_j = (2c/a) sin(jπ/(2(N+1)))`:
`E₀ = Σ ħω_j/2 = (ħc/2a)(cot(π/(4(N+1))) - 1)`. -/
theorem casimir_string (N : ℕ) (ħ c a : ℝ) (ha : a ≠ 0) :
    ∑ j ∈ Finset.range N, ħ / 2 * (2 * c / a * Real.sin ((j + 1 : ℝ) * (π / (2 * (N + 1)))))
      = ħ * c / (2 * a) * (Real.cos (π / (4 * (N + 1))) / Real.sin (π / (4 * (N + 1))) - 1) := by
  set x := π / (2 * (N + 1)) with hx
  have hN : (0 : ℝ) < N + 1 := by positivity
  have hs : 0 < Real.sin (x / 2) := by
    apply Real.sin_pos_of_pos_of_lt_pi
    · simp only [x]; positivity
    · simp only [x]
      rw [div_div, div_lt_iff₀ (by positivity)]
      nlinarith [Real.pi_pos, (by exact_mod_cast Nat.zero_le N : (0:ℝ) ≤ N)]
  have hx4 : π / (4 * (N + 1)) = x / 2 := by simp only [x]; field_simp; ring
  have hend : Real.cos ((N + 1 / 2 : ℝ) * x) = Real.sin (x / 2) := by
    have : (N + 1 / 2 : ℝ) * x = π / 2 - x / 2 := by simp only [x]; field_simp; ring
    rw [this, Real.cos_pi_div_two_sub]
  have tel := sin_sum_telescope x N
  rw [hend] at tel
  rw [hx4, ← Finset.mul_sum, ← Finset.mul_sum]
  have : ∑ j ∈ Finset.range N, Real.sin ((j + 1 : ℝ) * x)
      = (Real.cos (x / 2) - Real.sin (x / 2)) / (2 * Real.sin (x / 2)) := by
    field_simp; linarith
  rw [this]; field_simp

/-! ## Horizon cell counting -/

/-- `A/(4ℓ_P²)` is exactly the number of cells of side `2ℓ_P` (the point
diameter) on an area `A`; one nat per cell, i.e. `1/ln 2 > 1` bits per cell. -/
theorem horizon_cells (A ℓ : ℝ) :
    A / (4 * ℓ ^ 2) = A / (2 * ℓ) ^ 2 ∧ 1 < 1 / Real.log 2 ∧ 1 / Real.log 2 < 3 / 2 := by
  have h1 := Real.log_two_lt_d9
  have h2 := Real.log_two_gt_d9
  have hl : 0 < Real.log 2 := Real.log_pos (by norm_num)
  refine ⟨by ring, ?_, ?_⟩
  · rw [lt_div_iff₀ hl]; linarith
  · rw [div_lt_div_iff₀ hl (by norm_num)]; linarith

/-! ## Gibbs paradox: configurations are sets -/

/-- Ordered placements of `N` distinguishable particles in `M` cells
(`M^{\underline N}`) overcount the set-configurations by exactly `N!`. -/
theorem gibbs_count (M N : ℕ) : M.descFactorial N = N.factorial * M.choose N :=
  Nat.descFactorial_eq_factorial_mul_choose M N

/-- The set of `N`-point configurations in `M` cells has `C(M,N)` elements. -/
theorem config_card (M N : ℕ) :
    ((Finset.range M).powersetCard N).card = M.choose N := by
  simp

/-- Log-concavity step for binomial coefficients. -/
lemma choose_step (M a b : ℕ) (hab : a + 1 < b + 1) (hab' : a + 1 ≤ b) :
    M.choose a * M.choose (b + 1) ≤ M.choose (a + 1) * M.choose b := by
  by_cases hb : M < b + 1
  · rw [Nat.choose_eq_zero_of_lt hb]; simp
  push Not at hb
  have h1 := Nat.choose_succ_right_eq M a
  have h2 := Nat.choose_succ_right_eq M b
  -- multiply the target by (a+1)(b+1) > 0
  have hpos : 0 < (a + 1) * (b + 1) := by positivity
  refine Nat.le_of_mul_le_mul_right ?_ hpos
  obtain ⟨t, rfl⟩ : ∃ t, M = b + 1 + t := ⟨M - (b + 1), by omega⟩
  obtain ⟨s, rfl⟩ : ∃ s, b = a + 1 + s := ⟨b - (a + 1), by omega⟩
  have e1 : a + 1 + s + 1 + t - a = s + t + 2 := by omega
  have e2 : a + 1 + s + 1 + t - (a + 1 + s) = t + 1 := by omega
  rw [e1] at h1; rw [e2] at h2
  set x := (a + 1 + s + 1 + t).choose a
  set y := (a + 1 + s + 1 + t).choose (a + 1)
  set z := (a + 1 + s + 1 + t).choose (a + 1 + s)
  set w := (a + 1 + s + 1 + t).choose (a + 1 + s + 1)
  -- y (a+1) = x (s+t+2),  w (b+1) = z (t+1)
  calc x * w * ((a + 1) * (a + 1 + s + 1))
      = x * (w * (a + 1 + s + 1)) * (a + 1) := by ring
    _ = x * (z * (t + 1)) * (a + 1) := by rw [h2]
    _ ≤ x * (z * (s + t + 2)) * (a + 1 + s + 1) := by
        have : (t + 1) * (a + 1) ≤ (s + t + 2) * (a + 1 + s + 1) := by nlinarith
        calc x * (z * (t + 1)) * (a + 1) = x * z * ((t + 1) * (a + 1)) := by ring
          _ ≤ x * z * ((s + t + 2) * (a + 1 + s + 1)) := Nat.mul_le_mul_left _ this
          _ = x * (z * (s + t + 2)) * (a + 1 + s + 1) := by ring
    _ = (x * (s + t + 2)) * z * (a + 1 + s + 1) := by ring
    _ = (y * (a + 1)) * z * (a + 1 + s + 1) := by rw [h1]
    _ = y * z * ((a + 1) * (a + 1 + s + 1)) := by ring

/-- `C(M,i) C(M,2N-i) ≤ C(M,N)²` for `i ≤ N`. -/
lemma choose_pair_le (M N : ℕ) : ∀ d ≤ N, M.choose (N - d) * M.choose (N + d) ≤ M.choose N ^ 2 := by
  intro d
  induction d with
  | zero => intro _; simp [sq]
  | succ d ih =>
    intro hd
    have := ih (by omega)
    have step := choose_step M (N - (d + 1)) (N + d) (by omega) (by omega)
    have e1 : N - (d + 1) + 1 = N - d := by omega
    rw [e1] at step
    calc M.choose (N - (d + 1)) * M.choose (N + (d + 1))
        = M.choose (N - (d + 1)) * M.choose (N + d + 1) := by rw [← add_assoc]
      _ ≤ M.choose (N - d) * M.choose (N + d) := step
      _ ≤ M.choose N ^ 2 := this

/-- **No Gibbs paradox for set-configurations**: merging two equal boxes of
`M` cells with `N` identical particles each changes the configuration count by
a factor between `1` and `2N+1` (sub-extensive), whereas ordered counting
(`M^N`) would give the spurious factor `2^{2N}`. -/
theorem gibbs_mixing (M N : ℕ) :
    M.choose N ^ 2 ≤ (2 * M).choose (2 * N) ∧
    (2 * M).choose (2 * N) ≤ (2 * N + 1) * M.choose N ^ 2 ∧
    (2 * M) ^ (2 * N) = 2 ^ (2 * N) * (M ^ N) ^ 2 := by
  have hv := Nat.add_choose_eq M M (2 * N)
  rw [← two_mul M] at hv
  refine ⟨?_, ?_, ?_⟩
  · rw [hv, sq]
    have hmem : (N, N) ∈ Finset.HasAntidiagonal.antidiagonal (2 * N) := by
      rw [Finset.HasAntidiagonal.mem_antidiagonal]; ring
    exact Finset.single_le_sum (f := fun ij : ℕ × ℕ => M.choose ij.1 * M.choose ij.2)
      (fun _ _ => Nat.zero_le _) hmem
  · rw [hv]
    have hb : ∀ ij ∈ Finset.HasAntidiagonal.antidiagonal (2 * N), M.choose ij.1 * M.choose ij.2 ≤ M.choose N ^ 2 := by
      intro ij hij
      rw [Finset.HasAntidiagonal.mem_antidiagonal] at hij
      rcases le_total ij.1 N with h | h
      · have := choose_pair_le M N (N - ij.1) (by omega)
        have e1 : N - (N - ij.1) = ij.1 := by omega
        have e2 : N + (N - ij.1) = ij.2 := by omega
        rwa [e1, e2] at this
      · have := choose_pair_le M N (N - ij.2) (by omega)
        have e1 : N - (N - ij.2) = ij.2 := by omega
        have e2 : N + (N - ij.2) = ij.1 := by omega
        rw [e1, e2] at this; linarith [Nat.mul_comm (M.choose ij.1) (M.choose ij.2)]
    have := Finset.sum_le_card_nsmul _ _ _ hb
    rw [Finset.Nat.card_antidiagonal, smul_eq_mul] at this
    exact this
  · rw [mul_pow, ← pow_mul, mul_comm N 2]

/-! ## The δ potential on the lattice -/

/-- Granular delta: `δ_ε(k) = [k = 0]/(2ε)`; its granular integral against any
`f` is exactly `f(0)`, and `δ_ε²` is an ordinary function. -/
theorem delta_sift (ε : ℝ) (hε : ε ≠ 0) (f : ℤ → ℝ) (n : ℕ) :
    ∑ k ∈ Finset.Icc (-(n : ℤ)) n, (if k = 0 then 1 / (2 * ε) else 0) * f k * (2 * ε) = f 0 := by
  rw [Finset.sum_eq_single 0]
  · simp; field_simp
  · intro b _ hb; simp [hb]
  · intro h; simp at h

/-- **Exact bound state of the lattice δ well.**  On the lattice of spacing
`a`, `H = -(ħ²/2m) Δ_a - (g/a)[k=0]`.  If `0 < r` and `r² + 2κ r = 1` with
`κ = m g a/ħ²`, then `ψ(k) = r^{|k|}` satisfies `Hψ = Eψ` with
`E = -(ħ²/2ma²)(r + 1/r - 2)`. -/
theorem delta_bound_state (ħ m g a r : ℝ) (hħ : ħ ≠ 0) (hm : m ≠ 0) (ha : a ≠ 0) (hr : 0 < r)
    (hrk : r ^ 2 + 2 * (m * g * a / ħ ^ 2) * r = 1) (k : ℤ) :
    -(ħ ^ 2 / (2 * m)) * ((r ^ (k + 1).natAbs - 2 * r ^ k.natAbs + r ^ (k - 1).natAbs) / a ^ 2)
      - (if k = 0 then g / a * r ^ k.natAbs else 0)
      = -(ħ ^ 2 / (2 * m * a ^ 2)) * (r + 1 / r - 2) * r ^ k.natAbs := by
  have hr0 : r ≠ 0 := hr.ne'
  rcases lt_trichotomy k 0 with hk | hk | hk
  · obtain ⟨j, hj⟩ : ∃ j : ℕ, k.natAbs = j + 1 := ⟨k.natAbs - 1, by omega⟩
    have e1 : (k + 1).natAbs = j := by omega
    have e2 : (k - 1).natAbs = j + 2 := by omega
    rw [e1, e2, hj]; simp only [hk.ne, ↓reduceIte]
    field_simp
    ring
  · subst hk
    simp
    have e : g = (1 - r ^ 2) * ħ ^ 2 / (2 * m * a * r) := by
      field_simp; field_simp at hrk; linarith
    rw [e]
    field_simp
    ring
  · obtain ⟨j, hj⟩ : ∃ j : ℕ, k.natAbs = j + 1 := ⟨k.natAbs - 1, by omega⟩
    have e1 : (k + 1).natAbs = j + 2 := by omega
    have e2 : (k - 1).natAbs = j := by omega
    rw [e1, e2, hj]; simp only [hk.ne', ↓reduceIte]
    field_simp
    ring

/-- The bound state exists for every attractive coupling: `r = √(1+κ²) - κ`
solves `r² + 2κr = 1` with `0 < r < 1`. -/
theorem delta_root (κ : ℝ) (hκ : 0 < κ) :
    let r := Real.sqrt (1 + κ ^ 2) - κ
    0 < r ∧ r < 1 ∧ r ^ 2 + 2 * κ * r = 1 := by
  intro r
  have hs : Real.sqrt (1 + κ ^ 2) ^ 2 = 1 + κ ^ 2 := Real.sq_sqrt (by positivity)
  have hs0 : 0 ≤ Real.sqrt (1 + κ ^ 2) := Real.sqrt_nonneg _
  have hsk : κ < Real.sqrt (1 + κ ^ 2) := by nlinarith
  have hs1 : Real.sqrt (1 + κ ^ 2) < 1 + κ := by nlinarith
  refine ⟨by simp only [r]; linarith, by simp only [r]; linarith, ?_⟩
  simp only [r]; nlinarith [hs]

end QE.Phys
