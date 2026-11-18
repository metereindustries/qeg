-- SPDX-License-Identifier: MIT
-- Copyright 2026 Metere Industries, Inc. Author: Alfredo Metere.
-- Quasi-Euclidean Granular Geometry. Any derivative work must carry this notice:
--   This work is derivative of the Quasi-Euclidean Granular Geometry book
--   authored by Alfredo Metere. Copyright 2026 Metere Industries, Inc.
--   All rights reserved
-- See LICENSE.md and NOTICE.

import QuasiEuclidean.Basic
import QuasiEuclidean.Ch02_Hyper
import QuasiEuclidean.Ch06_Analysis
import QuasiEuclidean.Ch07_Multi
import QuasiEuclidean.Ch08_ODE

/-!
# Chapter "Point Sources and Conservation Laws"

Densities of charged point-spheres (sifting, dipoles, the jump across a charged sheet),
the granular continuity equation (local balance on a window, a point charge hopping one
cell, global conservation on the periodic lattice), conservation of Gauss's law under a
granular Ampère–Maxwell step, Newton's third law and the absence of self-force for the
reflection-symmetric derivative (and the self-force of the one-sided one), and the
frequency-space delta `δ_T` with `δ_T(0) = T/(2π)` and `δ_T² = δ_T(0) δ_T`.
-/

open Finset

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace QE.Src

open QE.Multi

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-! ## 1. Densities of point-spheres -/

/-- The density of finitely many charged point-spheres: charge `q a` sits on the
point-sphere of index `x a`. -/
def density (ε : K) {n : ℕ} {ι : Type*} (P : Finset ι) (x : ι → Fin n → ℤ) (q : ι → K)
    (y : Fin n → ℤ) : K :=
  ∑ a ∈ P, q a * deltaN ε (x a) y

/-- **Sifting for a configuration of point charges.** On any window that contains the
charges, the granular integral of `ρ φ` is `∑ q_a φ(x_a)`, exactly. -/
theorem density_pair (ε : K) (hε : ε ≠ 0) {n : ℕ} {ι : Type*} (P : Finset ι)
    (x : ι → Fin n → ℤ) (q : ι → K) (W : Finset (Fin n → ℤ)) (hW : ∀ a ∈ P, x a ∈ W)
    (φ : (Fin n → ℤ) → K) :
    ∑ y ∈ W, density ε P x q y * φ y * (2 * ε) ^ n = ∑ a ∈ P, q a * φ (x a) := by
  have h2 : (2 * ε) ^ n ≠ 0 := pow_ne_zero _ (mul_ne_zero two_ne_zero hε)
  unfold density
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a ha => ?_
  rw [Finset.sum_eq_single (x a)]
  · rw [deltaN, if_pos rfl]
    field_simp
  · intro y _ hy
    simp [deltaN, hy]
  · intro h
    exact absurd (hW a ha) h

/-- **Total charge.** The granular integral of the density is the sum of the charges. -/
theorem density_total (ε : K) (hε : ε ≠ 0) {n : ℕ} {ι : Type*} (P : Finset ι)
    (x : ι → Fin n → ℤ) (q : ι → K) (W : Finset (Fin n → ℤ)) (hW : ∀ a ∈ P, x a ∈ W) :
    ∑ y ∈ W, density ε P x q y * (2 * ε) ^ n = ∑ a ∈ P, q a := by
  have := density_pair ε hε P x q W hW (fun _ => 1)
  simpa using this

/-- **A physical dipole.** Charges `q` and `-q` on neighbouring point-spheres `a + e i`
and `a`. Its pairing with any `φ` is the dipole moment `p = 2εq` times the forward
partial derivative of `φ` at `a`, exactly. -/
theorem dipole_pair (ε : K) (hε : ε ≠ 0) {n : ℕ} (i : Fin n) (a : Fin n → ℤ) (q : K)
    (W : Finset (Fin n → ℤ)) (ha : a ∈ W) (hb : a + e i ∈ W) (φ : (Fin n → ℤ) → K) :
    ∑ y ∈ W, (q * deltaN ε (a + e i) y - q * deltaN ε a y) * φ y * (2 * ε) ^ n
      = (2 * ε * q) * pd ε i φ a := by
  have h2 : (2 * ε) ^ n ≠ 0 := pow_ne_zero _ (mul_ne_zero two_ne_zero hε)
  have one : ∀ s ∈ W, ∑ y ∈ W, q * deltaN ε s y * φ y * (2 * ε) ^ n = q * φ s := by
    intro s hs
    rw [Finset.sum_eq_single s]
    · rw [deltaN, if_pos rfl]
      field_simp
    · intro y _ hy
      simp [deltaN, hy]
    · intro h
      exact absurd hs h
  simp_rw [sub_mul]
  rw [Finset.sum_sub_distrib, one _ hb, one _ ha]
  unfold pd
  field_simp

/-! ## 2. The jump across a charged sheet -/

/-- Forward difference on the one-dimensional lattice. -/
def dp (ε : K) (u : ℤ → K) (k : ℤ) : K := (u (k + 1) - u k) / (2 * ε)

/-- Backward difference on the one-dimensional lattice. -/
def dm (ε : K) (u : ℤ → K) (k : ℤ) : K := (u k - u (k - 1)) / (2 * ε)

/-- **Jump condition.** If `-Δu = σ δ` at the point-sphere `k` (a sheet of surface charge
`σ`), the field `E = -Du` on the face right of `k` exceeds the field on the face left of
`k` by exactly `σ`. -/
theorem sheet_jump (ε : K) (hε : ε ≠ 0) (u : ℤ → K) (σ : K) (k : ℤ)
    (h : -(dp ε (dm ε u) k) = σ / (2 * ε)) :
    (-(dp ε u k)) - (-(dm ε u k)) = σ := by
  have h2 : (2 : K) * ε ≠ 0 := mul_ne_zero two_ne_zero hε
  unfold dp dm at *
  rw [show k + 1 - 1 = k by ring] at h
  field_simp at h ⊢
  linarith

/-! ## 3. The granular continuity equation -/

/-- One time step `τ` of the continuity equation on the one-dimensional lattice. `J k` is
the flux (charge per unit time) through the face between the point-spheres `k - 1` and
`k`. -/
def contStep (ε τ : K) (ρ J : ℤ → K) (k : ℤ) : K := ρ k - τ / (2 * ε) * (J (k + 1) - J k)

/-- **Local conservation on a window.** The charge in the window `a, …, a+m-1` changes
by exactly what flows through its two end faces, for every flux. -/
theorem continuity_window (ε τ : K) (hε : ε ≠ 0) (ρ J : ℤ → K) (a : ℤ) (m : ℕ) :
    ∑ j ∈ range m, contStep ε τ ρ J (a + j) * (2 * ε)
      = ∑ j ∈ range m, ρ (a + j) * (2 * ε) - τ * (J (a + m) - J a) := by
  have h2 : (2 : K) * ε ≠ 0 := mul_ne_zero two_ne_zero hε
  have tel : ∑ j ∈ range m, (J (a + j + 1) - J (a + j)) = J (a + m) - J a := by
    have := Finset.sum_range_sub (fun j : ℕ => J (a + j)) m
    simpa [add_assoc] using this
  unfold contStep
  have : ∀ j ∈ range m, (ρ (a + j) - τ / (2 * ε) * (J (a + j + 1) - J (a + j))) * (2 * ε)
      = ρ (a + j) * (2 * ε) - τ * (J (a + j + 1) - J (a + j)) := by
    intro j _
    field_simp
  rw [Finset.sum_congr rfl this, Finset.sum_sub_distrib, ← Finset.mul_sum, tel]

/-- **Global conservation.** If no charge flows through the end faces of the window, the
total charge in it is the same after the step. -/
theorem continuity_closed (ε τ : K) (hε : ε ≠ 0) (ρ J : ℤ → K) (a : ℤ) (m : ℕ)
    (hJ : J (a + m) = J a) :
    ∑ j ∈ range m, contStep ε τ ρ J (a + j) * (2 * ε) = ∑ j ∈ range m, ρ (a + j) * (2 * ε) := by
  rw [continuity_window ε τ hε, hJ, sub_self, mul_zero, sub_zero]

/-- **A point charge hopping one cell is an exact solution.** The density `q δ_{k₀}` with
the flux `q/τ` through the single face between `k₀` and `k₀ + 1` becomes `q δ_{k₀+1}`
after one step, exactly. -/
theorem hop (ε τ : K) (hε : ε ≠ 0) (hτ : τ ≠ 0) (q : K) (k₀ k : ℤ) :
    contStep ε τ (fun j => if j = k₀ then q / (2 * ε) else 0)
        (fun j => if j = k₀ + 1 then q / τ else 0) k
      = if k = k₀ + 1 then q / (2 * ε) else 0 := by
  have h2 : (2 : K) * ε ≠ 0 := mul_ne_zero two_ne_zero hε
  unfold contStep
  dsimp only
  by_cases h1 : k = k₀
  · subst h1
    have : k ≠ k + 1 := by omega
    simp only [this, if_false, if_true, eq_self_iff_true]
    field_simp
    ring
  · by_cases h3 : k = k₀ + 1
    · subst h3
      have : k₀ + 1 + 1 ≠ k₀ + 1 := by omega
      simp only [h1, this, if_false, if_true, eq_self_iff_true]
      field_simp
      ring
    · have : k + 1 ≠ k₀ + 1 := fun h => h1 (by omega)
      simp [h1, h3, this]

/-- Forward divergence on the periodic lattice `(ℤ/Nℤ)ⁿ`. -/
def divT (ε : K) {n N : ℕ} (J : Fin n → (Fin n → ZMod N) → K) (x : Fin n → ZMod N) : K :=
  ∑ i, (J i (x + Pi.single i 1) - J i x) / (2 * ε)

/-- **Global conservation on the periodic lattice, in every dimension.** For every flux
field `J`, one step of `ρ ↦ ρ - τ div J` leaves the total charge unchanged. -/
theorem torus_charge (ε τ : K) {n N : ℕ} [NeZero N] (ρ : (Fin n → ZMod N) → K)
    (J : Fin n → (Fin n → ZMod N) → K) :
    ∑ x, (ρ x - τ * divT ε J x) = ∑ x, ρ x := by
  have h0 : ∑ x, divT ε J x = 0 := by
    unfold divT
    rw [Finset.sum_comm]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [← Finset.sum_div, Finset.sum_sub_distrib]
    have : ∑ x : Fin n → ZMod N, J i (x + Pi.single i 1) = ∑ x, J i x :=
      Fintype.sum_equiv (Equiv.addRight (Pi.single i 1 : Fin n → ZMod N)) _ _
        (fun _ => rfl)
    rw [this, sub_self, zero_div]
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum, h0, mul_zero, sub_zero]

/-! ## 4. Charge conservation keeps Gauss's law -/

/-- **Gauss's law is conserved.** Under one granular Ampère–Maxwell step
`E ↦ E + τ (curl B - J)` and one continuity step `ρ ↦ ρ - τ div J`, the defect
`div E - ρ` does not change, at any point-sphere. If Gauss's law holds at one time, it
holds at all times, exactly. -/
theorem gauss_preserved (ε τ : K) (E B J : Fin 3 → (Fin 3 → ℤ) → K) (ρ : (Fin 3 → ℤ) → K)
    (x : Fin 3 → ℤ) :
    div ε (fun i y => E i y + τ * (curl ε B i y - J i y)) x - (ρ x - τ * div ε J x)
      = div ε E x - ρ x := by
  have hlin : div ε (fun i y => E i y + τ * (curl ε B i y - J i y)) x
      = div ε E x + τ * (div ε (curl ε B) x - div ε J x) := by
    simp only [div, pd]
    rw [mul_sub, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib,
      ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  rw [hlin, div_curl]
  ring

/-! ## 5. Newton's third law and the self-force -/

/-- Central (reflection-symmetric) partial difference of a kernel along axis `i`. -/
def cd (ε : K) {n : ℕ} (i : Fin n) (G : (Fin n → ℤ) → K) (k : Fin n → ℤ) : K :=
  (G (k + e i) - G (k - e i)) / (2 * (2 * ε))

/-- **No self-force.** For an even kernel the central difference vanishes at the origin. -/
theorem cd_self (ε : K) {n : ℕ} (i : Fin n) (G : (Fin n → ℤ) → K) (hG : ∀ k, G (-k) = G k) :
    cd ε i G 0 = 0 := by
  unfold cd
  rw [zero_add, zero_sub, hG, sub_self, zero_div]

/-- For an even kernel the central difference is odd. -/
theorem cd_neg (ε : K) {n : ℕ} (i : Fin n) (G : (Fin n → ℤ) → K) (hG : ∀ k, G (-k) = G k)
    (k : Fin n → ℤ) : cd ε i G (-k) = -cd ε i G k := by
  unfold cd
  rw [show -k + e i = -(k - e i) by abel, show -k - e i = -(k + e i) by abel, hG, hG]
  ring

/-- **Radial differences give central forces.** If the kernel satisfies
`G(k + eᵢ) - G(k - eᵢ) = -kᵢ h(k)` for one function `h` and every axis, its central
difference is `-kᵢ h(k)/(2·2ε)`, proportional to `kᵢ`. -/
theorem cd_radial (ε : K) {n : ℕ} (i : Fin n) (G h : (Fin n → ℤ) → K)
    (hG : ∀ (k : Fin n → ℤ) (i : Fin n), G (k + e i) - G (k - e i) = -((k i : ℤ) : K) * h k)
    (k : Fin n → ℤ) : cd ε i G k = -(((k i : ℤ) : K) * h k) / (2 * (2 * ε)) := by
  unfold cd
  rw [hG k i]
  ring

/-- **The pair force of a radial-difference kernel is central**: the force of `b` on `a`
along every axis `i` is the same multiple `λ_ab` of the separation `(xₐ - x_b)ᵢ`. -/
theorem pair_force_central (ε : K) {n N : ℕ} (i : Fin n) (G h : (Fin n → ℤ) → K)
    (hG : ∀ (k : Fin n → ℤ) (i : Fin n), G (k + e i) - G (k - e i) = -((k i : ℤ) : K) * h k)
    (x : Fin N → Fin n → ℤ) (q : Fin N → K) (a b : Fin N) :
    -q a * (q b * cd ε i G (x a - x b))
      = (q a * q b * h (x a - x b) / (2 * (2 * ε))) * (((x a i - x b i : ℤ)) : K) := by
  rw [cd_radial ε i G h hG]
  simp only [Pi.sub_apply]
  ring

/-- The force along axis `i` on point-sphere `a` from all point-spheres (itself included)
through the kernel `G`, with the central difference. -/
def force (ε : K) {n N : ℕ} (i : Fin n) (G : (Fin n → ℤ) → K) (x : Fin N → Fin n → ℤ)
    (q : Fin N → K) (a : Fin N) : K :=
  -q a * ∑ b, q b * cd ε i G (x a - x b)

/-- **Newton's third law, summed.** For an even kernel the total force vanishes exactly. -/
theorem total_force_zero (ε : K) {n N : ℕ} (i : Fin n) (G : (Fin n → ℤ) → K)
    (hG : ∀ k, G (-k) = G k) (x : Fin N → Fin n → ℤ) (q : Fin N → K) :
    ∑ a, force ε i G x q a = 0 := by
  set S := ∑ a, ∑ b, q a * q b * cd ε i G (x a - x b) with hSdef
  have hS : S = -S := by
    have hswap : S = ∑ a, ∑ b, q b * q a * cd ε i G (x b - x a) := Finset.sum_comm
    conv_lhs => rw [hswap]
    rw [hSdef, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [show x b - x a = -(x a - x b) by abel, cd_neg ε i G hG]
    ring
  have hF : ∑ a, force ε i G x q a = -S := by
    unfold force
    rw [hSdef, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun b _ => ?_
    ring
  rw [hF]
  linarith

/-- **Momentum is conserved exactly.** One step `p ↦ p + τ F` of the momenta leaves the
total momentum unchanged, for every configuration. -/
theorem momentum_conserved (ε τ : K) {n N : ℕ} (i : Fin n) (G : (Fin n → ℤ) → K)
    (hG : ∀ k, G (-k) = G k) (x : Fin N → Fin n → ℤ) (q p : Fin N → K) :
    ∑ a, (p a + τ * force ε i G x q a) = ∑ a, p a := by
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, total_force_zero ε i G hG, mul_zero,
    add_zero]

/-- **The one-sided derivative makes a point charge push itself.** For the lattice
Green's function of a point-sphere (`-ΔG = δ` at `s`, equal values `c` on the `2n`
neighbours), the central difference at `s` vanishes, but the forward difference does not:
`2n ∂ᵢ⁺G(s) = -(2ε)^{1-n}`. -/
theorem self_force_forward_vs_central (ε : K) (hε : 0 < ε) {n : ℕ} (G : (Fin n → ℤ) → K)
    (s : Fin n → ℤ) (c : K) (hc : ∀ i, G (s + e i) = c ∧ G (s - e i) = c)
    (hG : -lap ε G s = deltaN ε s s) (i : Fin n) :
    cd ε i G s = 0 ∧ pd ε i G s ≠ 0 := by
  refine ⟨?_, ?_⟩
  · unfold cd
    rw [(hc i).1, (hc i).2, sub_self, zero_div]
  · obtain ⟨_, h⟩ := green_symmetric_field ε hε G s c hc hG i
    intro hp
    rw [hp, mul_zero] at h
    have : (0 : K) < 2 * ε / (2 * ε) ^ n := by positivity
    rw [neg_div] at h
    linarith

/-- **The value of the one-sided self-force.** With the force law of `force` but the
forward quotient, a single point-sphere of charge `q` at the source of `G` would feel
`-q² ∂ᵢ⁺G(s)`, and `2n` times this is `q² (2ε)^{1-n}`: a definite push along `+eᵢ`. -/
theorem forward_self_force (ε : K) (hε : 0 < ε) {n : ℕ} (G : (Fin n → ℤ) → K)
    (s : Fin n → ℤ) (c : K) (hc : ∀ i, G (s + e i) = c ∧ G (s - e i) = c)
    (hG : -lap ε G s = deltaN ε s s) (i : Fin n) (q : K) :
    2 * n * (-(q * q) * pd ε i G s) = q ^ 2 * (2 * ε / (2 * ε) ^ n) := by
  obtain ⟨_, h⟩ := green_symmetric_field ε hε G s c hc hG i
  have : 2 * (n : K) * (-(q * q) * pd ε i G s) = -(q * q) * (2 * n * pd ε i G s) := by ring
  rw [this, h]
  ring

end QE.Src

/-! ## 6. The delta in frequency space -/

namespace QE.Src

open Finset

/-- The frequency-space delta of an observation time `T = Nτ`, sampled at the frequency
lattice `ω_m = 2πm/T`: `δ_T(ω_m) = (1/2π) ∑_t e^{i ω_m t} τ`. -/
noncomputable def deltaT (N : ℕ) [NeZero N] (τ : ℝ) (m : ZMod N) : ℂ :=
  ((τ / (2 * Real.pi) : ℝ) : ℂ) * ∑ t : ZMod N, QE.Analysis.e (t * m)

/-- **`δ_T` is the granular delta of the frequency lattice**: it is `T/(2π)` at `ω = 0`
and `0` at every other frequency of the lattice. -/
theorem deltaT_eq (N : ℕ) [NeZero N] (τ : ℝ) (m : ZMod N) :
    deltaT N τ m = if m = 0 then (((N : ℝ) * τ / (2 * Real.pi) : ℝ) : ℂ) else 0 := by
  unfold deltaT
  rw [QE.Analysis.sum_e_mul]
  split_ifs
  · push_cast
    ring
  · simp

/-- **Its total mass is one**: summed against the frequency spacing `Δω = 2π/(Nτ)`. -/
theorem deltaT_total (N : ℕ) [NeZero N] (τ : ℝ) (hτ : τ ≠ 0) :
    ∑ m : ZMod N, deltaT N τ m * (((2 * Real.pi / ((N : ℝ) * τ)) : ℝ) : ℂ) = 1 := by
  have hN : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  simp_rw [deltaT_eq]
  rw [Finset.sum_eq_single (0 : ZMod N)]
  · rw [if_pos rfl, ← Complex.ofReal_mul]
    rw [show (N : ℝ) * τ / (2 * Real.pi) * (2 * Real.pi / ((N : ℝ) * τ)) = 1 by
      field_simp]
    simp
  · intro m _ hm
    simp [hm]
  · intro h
    exact absurd (Finset.mem_univ _) h

/-- **The square of the frequency delta**: `δ_T² = δ_T(0) · δ_T`, with `δ_T(0) = T/(2π)`.
This is the identity `[2πδ(ω)]² = T · 2πδ(ω)` behind Fermi's golden rule, exact. -/
theorem deltaT_sq (N : ℕ) [NeZero N] (τ : ℝ) (m : ZMod N) :
    deltaT N τ m ^ 2 = deltaT N τ 0 * deltaT N τ m := by
  rw [deltaT_eq, deltaT_eq N τ 0, if_pos rfl]
  split_ifs <;> ring

end QE.Src

/-! ## 7. Angular momentum: an exact balance and conservation in the shadow -/

namespace QE.Src

open Finset

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-- The cross product on `K³`. -/
def cross (u v : Fin 3 → K) : Fin 3 → K :=
  ![u 1 * v 2 - u 2 * v 1, u 2 * v 0 - u 0 * v 2, u 0 * v 1 - u 1 * v 0]

/-- Total angular momentum `∑ₐ xₐ × pₐ`, component `j`. -/
def angMom {N : ℕ} (x p : Fin N → Fin 3 → K) (j : Fin 3) : K := ∑ a, cross (x a) (p a) j

theorem cross_self_smul (c : K) (u v : Fin 3 → K) (j : Fin 3) :
    cross (fun i => u i + c * v i) v j = cross u v j := by
  fin_cases j <;> simp [cross] <;> ring

theorem cross_add_left (u w v : Fin 3 → K) (j : Fin 3) :
    cross (fun i => u i + w i) v j = cross u v j + cross w v j := by
  fin_cases j <;> simp [cross] <;> ring

theorem cross_add_smul_right (u v w : Fin 3 → K) (c : K) (j : Fin 3) :
    cross u (fun i => v i + c * w i) j = cross u v j + c * cross u w j := by
  fin_cases j <;> simp [cross] <;> ring

theorem cross_sum_right {N : ℕ} (u : Fin 3 → K) (F : Fin N → Fin 3 → K) (j : Fin 3) :
    cross u (fun i => ∑ b, F b i) j = ∑ b, cross u (F b) j := by
  fin_cases j <;> simp [cross, Finset.mul_sum, Finset.sum_sub_distrib]

theorem cross_neg_right (u v : Fin 3 → K) (j : Fin 3) :
    cross u (fun i => -v i) j = -cross u v j := by
  fin_cases j <;> simp [cross] <;> ring

theorem cross_sub_left (u w v : Fin 3 → K) (j : Fin 3) :
    cross (fun i => u i - w i) v j = cross u v j - cross w v j := by
  fin_cases j <;> simp [cross] <;> ring

theorem cross_central (u η : Fin 3 → K) (c : K) (j : Fin 3) :
    cross u (fun i => c * u i + η i) j = cross u η j := by
  fin_cases j <;> simp [cross] <;> ring

/-- **Internal torques pair up.** For antisymmetric pair forces,
`∑ₐ∑_b xₐ × F_ab = ½ ∑ₐ∑_b (xₐ - x_b) × F_ab`. -/
theorem torque_pairs {N : ℕ} (x : Fin N → Fin 3 → K) (F : Fin N → Fin N → Fin 3 → K)
    (hF : ∀ a b i, F a b i = -F b a i) (j : Fin 3) :
    ∑ a, ∑ b, cross (x a) (F a b) j
      = (1 / 2) * ∑ a, ∑ b, cross (fun i => x a i - x b i) (F a b) j := by
  set S := ∑ a, ∑ b, cross (x a) (F a b) j with hS
  have hswap : S = -∑ a, ∑ b, cross (x b) (F a b) j := by
    rw [hS, Finset.sum_comm, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun b _ => ?_
    have : F b a = fun i => -F a b i := funext fun i => by rw [hF a b i, neg_neg]
    rw [this, cross_neg_right]
  have hdiff : ∑ a, ∑ b, cross (fun i => x a i - x b i) (F a b) j
      = S - ∑ a, ∑ b, cross (x b) (F a b) j := by
    rw [hS, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun b _ => cross_sub_left _ _ _ j
  rw [hdiff]
  linarith

/-- **Exact angular-momentum balance of one kick–drift step.** Kick
`p'ₐ = pₐ + τ ∑_b F_ab` with antisymmetric pair forces, then drift
`x'ₐ = xₐ + (τ/mₐ) p'ₐ + rₐ`, where `rₐ` is any residual (for example the rounding of the
new position to a lattice point). Then, exactly,
`L' - L = (τ/2) ∑ₐ∑_b (xₐ - x_b) × F_ab + ∑ₐ rₐ × p'ₐ`. -/
theorem angMom_step {N : ℕ} (τ : K) (m : Fin N → K) (x r p : Fin N → Fin 3 → K)
    (F : Fin N → Fin N → Fin 3 → K) (hF : ∀ a b i, F a b i = -F b a i) (j : Fin 3) :
    angMom (fun a i => x a i + τ / m a * (p a i + τ * ∑ b, F a b i) + r a i)
        (fun a i => p a i + τ * ∑ b, F a b i) j - angMom x p j
      = τ / 2 * ∑ a, ∑ b, cross (fun i => x a i - x b i) (F a b) j
        + ∑ a, cross (r a) (fun i => p a i + τ * ∑ b, F a b i) j := by
  have h1 : ∀ a, cross (fun i => x a i + τ / m a * (p a i + τ * ∑ b, F a b i) + r a i)
      (fun i => p a i + τ * ∑ b, F a b i) j
      = cross (x a) (p a) j + τ * ∑ b, cross (x a) (F a b) j
        + cross (r a) (fun i => p a i + τ * ∑ b, F a b i) j := by
    intro a
    rw [cross_add_left (fun i => x a i + τ / m a * (p a i + τ * ∑ b, F a b i)) (r a),
      cross_self_smul (τ / m a) (x a) (fun i => p a i + τ * ∑ b, F a b i),
      cross_add_smul_right, cross_sum_right]
  unfold angMom
  simp_rw [h1]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, torque_pairs x F hF j]
  ring

/-- `|a b - c d| ≤ 2UV` from `|a|,|c| ≤ U` and `|b|,|d| ≤ V`. -/
theorem abs_two_terms (a b c d U V : K) (ha : |a| ≤ U) (hb : |b| ≤ V) (hc : |c| ≤ U)
    (hd : |d| ≤ V) : |a * b - c * d| ≤ 2 * U * V := by
  have hU : 0 ≤ U := le_trans (abs_nonneg a) ha
  calc |a * b - c * d| ≤ |a * b| + |c * d| := abs_sub _ _
    _ = |a| * |b| + |c| * |d| := by rw [abs_mul, abs_mul]
    _ ≤ U * V + U * V := add_le_add (mul_le_mul ha hb (abs_nonneg _) hU)
        (mul_le_mul hc hd (abs_nonneg _) hU)
    _ = 2 * U * V := by ring

theorem cross_abs_le (u v : Fin 3 → K) (U V : K) (hu : ∀ i, |u i| ≤ U) (hv : ∀ i, |v i| ≤ V)
    (j : Fin 3) : |cross u v j| ≤ 2 * U * V := by
  fin_cases j <;> simp only [cross] <;> simp <;> exact abs_two_terms _ _ _ _ U V (hu _) (hv _) (hu _) (hv _)

/-- **The per-step bound.** If every pair force is central up to a defect `η_ab`
(`F_ab = λ_ab (xₐ - x_b) + η_ab`), with `|xₐ - x_b| ≤ R`, `|η_ab| ≤ δ`, `|rₐ| ≤ ρ` and
`|p'ₐ| ≤ P` componentwise, one step changes each component of the angular momentum by at
most `τ N² R δ + 2 N ρ P`. -/
theorem angMom_step_bound {N : ℕ} (τ : K) (hτ : 0 ≤ τ) (m : Fin N → K)
    (x r p : Fin N → Fin 3 → K) (lam : Fin N → Fin N → K) (η : Fin N → Fin N → Fin 3 → K)
    (hF : ∀ a b i, lam a b * (x a i - x b i) + η a b i = -(lam b a * (x b i - x a i) + η b a i))
    (R δ ρ P : K) (hR : ∀ a b i, |x a i - x b i| ≤ R) (hη : ∀ a b i, |η a b i| ≤ δ)
    (hr : ∀ a i, |r a i| ≤ ρ)
    (hP : ∀ a i, |p a i + τ * ∑ b, (lam a b * (x a i - x b i) + η a b i)| ≤ P) (j : Fin 3) :
    |angMom (fun a i => x a i + τ / m a * (p a i + τ * ∑ b, (lam a b * (x a i - x b i) + η a b i))
          + r a i)
        (fun a i => p a i + τ * ∑ b, (lam a b * (x a i - x b i) + η a b i)) j - angMom x p j|
      ≤ τ * N ^ 2 * R * δ + 2 * N * ρ * P := by
  rw [angMom_step τ m x r p (fun a b i => lam a b * (x a i - x b i) + η a b i) hF j]
  have hc : ∀ a b, cross (fun i => x a i - x b i) (fun i => lam a b * (x a i - x b i) + η a b i) j
      = cross (fun i => x a i - x b i) (η a b) j := fun a b =>
    cross_central (fun i => x a i - x b i) (η a b) (lam a b) j
  simp_rw [hc]
  have b1 : |∑ a, ∑ b, cross (fun i => x a i - x b i) (η a b) j| ≤ N ^ 2 * (2 * R * δ) := by
    calc |∑ a, ∑ b, cross (fun i => x a i - x b i) (η a b) j|
        ≤ ∑ a, |∑ b, cross (fun i => x a i - x b i) (η a b) j| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ a : Fin N, ∑ b : Fin N, |cross (fun i => x a i - x b i) (η a b) j| :=
          Finset.sum_le_sum fun a _ => Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ a : Fin N, ∑ b : Fin N, 2 * R * δ :=
          Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun b _ =>
            cross_abs_le _ _ R δ (hR a b) (hη a b) j
      _ = N ^ 2 * (2 * R * δ) := by simp [Finset.sum_const, Finset.card_univ]; ring
  have b2 : |∑ a, cross (r a) (fun i => p a i + τ * ∑ b, (lam a b * (x a i - x b i) + η a b i)) j|
      ≤ N * (2 * ρ * P) := by
    calc _ ≤ ∑ a, |cross (r a) (fun i => p a i + τ * ∑ b, (lam a b * (x a i - x b i) + η a b i)) j| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ a : Fin N, 2 * ρ * P :=
          Finset.sum_le_sum fun a _ => cross_abs_le _ _ ρ P (hr a) (hP a) j
      _ = N * (2 * ρ * P) := by simp [Finset.sum_const, Finset.card_univ]
  calc _ ≤ |τ / 2 * ∑ a, ∑ b, cross (fun i => x a i - x b i) (η a b) j|
        + |∑ a, cross (r a) (fun i => p a i + τ * ∑ b, (lam a b * (x a i - x b i) + η a b i)) j| :=
        abs_add_le _ _
    _ ≤ τ / 2 * (N ^ 2 * (2 * R * δ)) + N * (2 * ρ * P) := by
        rw [abs_mul, abs_of_nonneg (by positivity : (0 : K) ≤ τ / 2)]
        exact add_le_add (mul_le_mul_of_nonneg_left b1 (by positivity)) b2
    _ = τ * N ^ 2 * R * δ + 2 * N * ρ * P := by ring

/-- **Nearby positions, nearby angular momentum.** If every position is moved by at most
`ρ` per component (for example to the nearest lattice point), the angular momentum changes
by at most `2 N ρ P`, where `P` bounds the momenta. -/
theorem angMom_close {N : ℕ} (x X p : Fin N → Fin 3 → K) (ρ P : K)
    (hx : ∀ a i, |x a i - X a i| ≤ ρ) (hp : ∀ a i, |p a i| ≤ P) (j : Fin 3) :
    |angMom x p j - angMom X p j| ≤ N * (2 * ρ * P) := by
  unfold angMom
  rw [← Finset.sum_sub_distrib]
  calc _ ≤ ∑ a, |cross (x a) (p a) j - cross (X a) (p a) j| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ a, |cross (fun i => x a i - X a i) (p a) j| := by
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [cross_sub_left]
    _ ≤ ∑ a : Fin N, 2 * ρ * P :=
        Finset.sum_le_sum fun a _ => cross_abs_le _ _ ρ P (hx a) (hp a) j
    _ = N * (2 * ρ * P) := by simp [Finset.sum_const, Finset.card_univ]

/-- **Exactly central forces leave only the rounding.** If every pair force is parallel to
the separation, `F_ab = λ_ab (xₐ - x_b)`, the change of angular momentum in a kick–drift step
is exactly `∑ₐ rₐ × p'ₐ`: with no residual, angular momentum is conserved exactly. -/
theorem angMom_central_step {N : ℕ} (τ : K) (m : Fin N → K) (x r p : Fin N → Fin 3 → K)
    (lam : Fin N → Fin N → K)
    (hF : ∀ a b i, lam a b * (x a i - x b i) = -(lam b a * (x b i - x a i))) (j : Fin 3) :
    angMom (fun a i => x a i + τ / m a * (p a i + τ * ∑ b, lam a b * (x a i - x b i)) + r a i)
        (fun a i => p a i + τ * ∑ b, lam a b * (x a i - x b i)) j - angMom x p j
      = ∑ a, cross (r a) (fun i => p a i + τ * ∑ b, lam a b * (x a i - x b i)) j := by
  rw [angMom_step τ m x r p (fun a b i => lam a b * (x a i - x b i)) hF j]
  have h0 : ∀ a b, cross (fun i => x a i - x b i) (fun i => lam a b * (x a i - x b i)) j = 0 := by
    intro a b
    fin_cases j <;> simp [cross] <;> ring
  simp_rw [h0]
  simp

/-- Telescoping: steps of size at most `B` add up to at most `k B`. -/
theorem drift_le {L : ℕ → K} {B : K} (k : ℕ) (h : ∀ t < k, |L (t + 1) - L t| ≤ B) :
    |L k - L 0| ≤ k * B := by
  induction k with
  | zero => simp
  | succ k ih =>
    have h1 := ih fun t ht => h t (Nat.lt_succ_of_lt ht)
    have h2 := h k (Nat.lt_succ_self k)
    calc |L (k + 1) - L 0| = |(L (k + 1) - L k) + (L k - L 0)| := by ring_nf
      _ ≤ |L (k + 1) - L k| + |L k - L 0| := abs_add_le _ _
      _ ≤ B + k * B := add_le_add h2 h1
      _ = ((k + 1 : ℕ) : K) * B := by push_cast; ring

end QE.Src

namespace QE.Src

open QE.Hyper

theorem isFinite_mul {x y : ℝ*} (hx : IsFinite x) (hy : IsFinite y) : IsFinite (x * y) := by
  unfold IsFinite at *
  rw [ArchimedeanClass.mk_mul]
  exact add_nonneg hx hy

theorem isFinite_natCast (n : ℕ) : IsFinite (n : ℝ*) := by
  have := isFinite_intCast (n : ℤ)
  simpa using this

/-- **Angular momentum is conserved in the shadow.** Let a granular dynamics on `ℝ*` run
`K` steps of length `τ > 0` within a finite time `T` (`Kτ ≤ T`), and let each step change a
component `L` of the angular momentum by at most `τ N² R δ + 2 N ρ P`
(`angMom_step_bound`), with `N, R, P, T` finite, the centrality defect `δ` infinitesimal and
the rounding `ρ` infinitesimal compared with the tick (`ρ/τ` infinitesimal). Then
`L_K - L_0` is infinitesimal. -/
theorem angMom_shadow (N : ℕ) (T R P δ ρ τ : ℝ*) (k : ℕ) (L : ℕ → ℝ*) (hτ : 0 < τ)
    (hkT : (k : ℝ*) * τ ≤ T) (hR : 0 ≤ R) (hP : 0 ≤ P) (hδ0 : 0 ≤ δ) (hρ0 : 0 ≤ ρ)
    (hstep : ∀ t < k, |L (t + 1) - L t| ≤ τ * N ^ 2 * R * δ + 2 * N * ρ * P)
    (hT : IsFinite T) (hRf : IsFinite R) (hPf : IsFinite P)
    (hδ : Infinitesimal δ) (hρ : Infinitesimal (ρ / τ)) :
    Infinitesimal (L k - L 0) := by
  have hd := drift_le k hstep
  have hN0 : (0 : ℝ*) ≤ N := Nat.cast_nonneg N
  have hk0 : (0 : ℝ*) ≤ k := Nat.cast_nonneg k
  have hkρ : (k : ℝ*) * ρ ≤ T * (ρ / τ) := by
    have : (k : ℝ*) * ρ = ((k : ℝ*) * τ) * (ρ / τ) := by field_simp
    rw [this]
    exact mul_le_mul_of_nonneg_right hkT (div_nonneg hρ0 hτ.le)
  have hbound : |L k - L 0| ≤ |δ * (T * N ^ 2 * R) + (ρ / τ) * (2 * N * P * T)| := by
    refine le_trans hd (le_trans ?_ (le_abs_self _))
    have e1 : (k : ℝ*) * (τ * N ^ 2 * R * δ + 2 * N * ρ * P)
        = ((k : ℝ*) * τ) * (N ^ 2 * R * δ) + ((k : ℝ*) * ρ) * (2 * N * P) := by ring
    have e2 : δ * (T * N ^ 2 * R) + (ρ / τ) * (2 * N * P * T)
        = T * (N ^ 2 * R * δ) + (T * (ρ / τ)) * (2 * N * P) := by ring
    rw [e1, e2]
    exact add_le_add (mul_le_mul_of_nonneg_right hkT (by positivity))
      (mul_le_mul_of_nonneg_right hkρ (by positivity))
  refine Infinitesimal.of_abs_le ?_ hbound
  have hNf := isFinite_natCast N
  refine Infinitesimal.add (Infinitesimal.mul_finite hδ ?_) (Infinitesimal.mul_finite hρ ?_)
  · exact isFinite_mul (isFinite_mul hT (by simpa [pow_two] using isFinite_mul hNf hNf)) hRf
  · refine isFinite_mul (isFinite_mul (isFinite_mul ?_ hNf) hPf) hT
    simpa using isFinite_natCast 2

/-- An infinitesimal is below one half in absolute value. -/
theorem two_abs_lt_one {a : ℝ*} (ha : Infinitesimal a) : 2 * |a| < 1 := by
  unfold Infinitesimal at ha
  have h0 : ArchimedeanClass.mk (1 : ℝ*) < ArchimedeanClass.mk a := by simpa using ha
  have := (ArchimedeanClass.mk_lt_mk.mp h0) 2
  simpa [two_smul, two_mul] using this

/-- **Energy in the shadow.** Along symplectic Euler for the oscillator, with an
`εω < 1/2` over any ordered field, the true energy after `k` steps differs from the
initial one by at most `4εω E₀`, for every `k`. `energy_shadow` reads this over `ℝ*`. -/
theorem energy_shadow_bound {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    (ε ω : K) (z₀ : K × K) (k : ℕ) (hε : 0 ≤ ε) (hω : 0 ≤ ω)
    (ha : ε * ω < 1 / 2) :
    |QE.ODE.energy ω (QE.ODE.sympOsc ε ω z₀ k) - QE.ODE.energy ω z₀|
      ≤ 4 * (ε * ω) * QE.ODE.energy ω z₀ := by
  have ha0 : 0 ≤ ε * ω := mul_nonneg hε hω
  have hE0 : 0 ≤ QE.ODE.energy ω z₀ := by simp only [QE.ODE.energy]; positivity
  have hEk : 0 ≤ QE.ODE.energy ω (QE.ODE.sympOsc ε ω z₀ k) := by
    simp only [QE.ODE.energy]; positivity
  have h1 := QE.ODE.sympOsc_energy_bounded ε ω hε hω z₀ k
  have h2 : (1 - ε * ω) * QE.ODE.energy ω z₀
      ≤ (1 + ε * ω) * QE.ODE.energy ω (QE.ODE.sympOsc ε ω z₀ k) := by
    have u := (QE.ODE.modEnergy_bounds ε ω hε hω z₀).1
    have v := (QE.ODE.modEnergy_bounds ε ω hε hω (QE.ODE.sympOsc ε ω z₀ k)).2
    rw [QE.ODE.sympOsc_modEnergy] at v
    linarith
  set a := ε * ω
  set E0 := QE.ODE.energy ω z₀
  set Ek := QE.ODE.energy ω (QE.ODE.sympOsc ε ω z₀ k)
  have hk3 : Ek ≤ 3 * E0 := by nlinarith [mul_le_mul_of_nonneg_right ha.le hEk]
  have haEk : a * Ek ≤ a * (3 * E0) := mul_le_mul_of_nonneg_left hk3 ha0
  rw [abs_le]
  constructor <;> nlinarith [mul_nonneg ha0 hE0]

theorem energy_shadow (ε ω : ℝ*) (z₀ : ℝ* × ℝ*) (k : ℕ) (hε : 0 ≤ ε) (hω : 0 ≤ ω)
    (hεi : Infinitesimal ε) (hωf : IsFinite ω) (hE : IsFinite (QE.ODE.energy ω z₀)) :
    Infinitesimal (QE.ODE.energy ω (QE.ODE.sympOsc ε ω z₀ k) - QE.ODE.energy ω z₀) := by
  have hai : Infinitesimal (ε * ω) := Infinitesimal.mul_finite hεi hωf
  have ha2 := two_abs_lt_one hai
  rw [abs_of_nonneg (mul_nonneg hε hω)] at ha2
  have hb := energy_shadow_bound ε ω z₀ k hε hω (by linarith)
  have hE0 : 0 ≤ QE.ODE.energy ω z₀ := by simp only [QE.ODE.energy]; positivity
  refine Infinitesimal.of_abs_le ?_ (le_trans hb (le_abs_self _))
  have h4 : IsFinite (4 : ℝ*) := by simpa using isFinite_natCast 4
  have e : 4 * (ε * ω) * QE.ODE.energy ω z₀ = (ε * ω) * (4 * QE.ODE.energy ω z₀) := by ring
  rw [e]
  exact Infinitesimal.mul_finite hai (isFinite_mul h4 hE)

end QE.Src
