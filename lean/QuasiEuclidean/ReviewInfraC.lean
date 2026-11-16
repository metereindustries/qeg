-- SPDX-License-Identifier: MIT
-- Copyright 2026 Metere Industries, Inc. Author: Alfredo Metere.
-- Quasi-Euclidean Granular Geometry. Any derivative work must carry this notice:
--   This work is derivative of the Quasi-Euclidean Granular Geometry book
--   authored by Alfredo Metere. Copyright 2026 Metere Industries, Inc.
--   All rights reserved
-- See LICENSE.md and NOTICE.

import QuasiEuclidean.Ch02_Hyper
import QuasiEuclidean.Ch06_Analysis
import QuasiEuclidean.Ch07_Multi
import QuasiEuclidean.Ch09_Geometry
import QuasiEuclidean.Ch10_Topology

/-!
# Review infrastructure C (chapters 6–10)

Lemmas that close the gaps between printed statements and their Lean constants in
chapters 6 (real analysis), 7 (multivariable), 9 (geometry) and 10 (topology).
All results here are Lebesgue-free.
-/

set_option linter.unusedSectionVars false

/-! ## Chapter 6: shadows in a closed interval -/

namespace QE.Analysis

open Filter
open Hyperreal (ofSeq ofSeq_surjective)

/-- The transferred snap `⌊x⌉_ε` on `ℝ*`: the germ of the level-wise snaps. -/
noncomputable def hsnap (ε x : ℝ*) : ℝ* := Filter.Germ.map₂ QE.Hyper.snap ε x

theorem hsnap_ofSeq (e u : ℕ → ℝ) :
    hsnap (ofSeq e) (ofSeq u) = ofSeq (fun n => QE.Hyper.snap (e n) (u n)) := rfl

/-- The shadow is unique: `x ≃ r` and `x ≃ s` force `r = s`. -/
theorem nearSt_unique {x : ℝ*} {r s : ℝ} (hr : NearSt x r) (hs : NearSt x s) : r = s := by
  obtain ⟨u, rfl⟩ := ofSeq_surjective x
  rw [nearSt_ofSeq] at hr hs
  exact tendsto_nhds_unique hr hs

/-- The snap of a standard real is a lattice point `2ε k`, `k ∈ ℤ*`. -/
theorem hsnap_mem_lattice (ε : ℝ*) (r : ℝ) :
    ∃ k : ℕ → ℤ, hsnap ε (r : ℝ*) = 2 * ε * ofSeq (fun n => (k n : ℝ)) := by
  obtain ⟨e, rfl⟩ := ofSeq_surjective ε
  refine ⟨fun n => QE.Hyper.snapIdx (e n) r, ?_⟩
  rfl

/-- For a positive infinitesimal `ε`, `⌊r⌉_ε ≃ r`: snapping is a right inverse of `st`. -/
theorem hsnap_near (ε : ℝ*) (hε0 : 0 < ε) (hε : Infinitesimal ε) (r : ℝ) :
    NearSt (hsnap ε (r : ℝ*)) r := by
  obtain ⟨e, rfl⟩ := ofSeq_surjective ε
  have hpos : ∀ᶠ n in hyperfilter ℕ, 0 < e n := Hyperreal.ofSeq_lt_ofSeq.1 hε0
  have he : Tendsto e (hyperfilter ℕ) (nhds 0) := hε
  show Tendsto (fun n => QE.Hyper.snap (e n) r) (hyperfilter ℕ) (nhds r)
  rw [tendsto_iff_dist_tendsto_zero]
  refine squeeze_zero' (Eventually.of_forall fun n => dist_nonneg) ?_ (by simpa using he.abs)
  filter_upwards [hpos] with n hn
  have h := QE.Hyper.snap_mem_cell hn r
  rw [Real.dist_eq, abs_le]
  constructor <;> linarith [h.1, h.2, abs_nonneg (e n), le_abs_self (e n)]

/-- **`thm:analysis-shadow-Icc` in full.** (i) every `x ∈ *[a,b]` has a shadow in
`[a,b]`; (ii) in particular every lattice point `2εk ∈ *[a,b]` has one; (iii) for a
positive infinitesimal `ε` the snap of `r ∈ [a,b]` is a lattice point whose (unique)
shadow is `r`, i.e. `st ∘ ⌊·⌉_ε = id` on `[a,b]`. -/
theorem shadow_Icc_full {a b : ℝ} :
    (∀ x : ℝ*, InStar (Set.Icc a b) x → ∃ r ∈ Set.Icc a b, NearSt x r) ∧
    (∀ (ε : ℝ*) (k : ℕ → ℤ), InStar (Set.Icc a b) (2 * ε * ofSeq (fun n => (k n : ℝ))) →
      ∃ r ∈ Set.Icc a b, NearSt (2 * ε * ofSeq (fun n => (k n : ℝ))) r) ∧
    (∀ ε : ℝ*, 0 < ε → Infinitesimal ε → ∀ r ∈ Set.Icc a b,
      (∃ k : ℕ → ℤ, hsnap ε (r : ℝ*) = 2 * ε * ofSeq (fun n => (k n : ℝ))) ∧
      NearSt (hsnap ε (r : ℝ*)) r ∧ ∀ s : ℝ, NearSt (hsnap ε (r : ℝ*)) s → s = r) :=
  ⟨fun x hx => shadow_Icc x hx, fun _ _ hx => shadow_Icc _ hx,
    fun ε hε0 hε r _ => ⟨hsnap_mem_lattice ε r, hsnap_near ε hε0 hε r,
      fun _ hs => nearSt_unique hs (hsnap_near ε hε0 hε r)⟩⟩

end QE.Analysis

/-! ## Chapter 7: uniqueness for Dirichlet, Zaremba and the representation formula;
the plane-wave symbol of the Laplacian -/

namespace QE.Multi

open Finset

section Uniq
variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

theorem lap_sub_fun (ε : K) {n : ℕ} (f g : (Fin n → ℤ) → K) (x : Fin n → ℤ) :
    lap ε (fun y => f y - g y) x = lap ε f x - lap ε g x := by
  unfold lap; rw [← sum_sub_distrib]; congr 1; ext i; ring

/-- Two solutions of the Dirichlet problem (zero off `Ω`, same `-Δ_ε` on `Ω`) coincide. -/
theorem dirichlet_eq_of_solutions (ε : K) (hε : 0 < ε) {n : ℕ} (i₀ : Fin n)
    (Ω : Finset (Fin n → ℤ)) (u v : (Fin n → ℤ) → K)
    (hu0 : ∀ x, x ∉ Ω → u x = 0) (hv0 : ∀ x, x ∉ Ω → v x = 0)
    (huv : ∀ x ∈ Ω, lap ε u x = lap ε v x) : u = v := by
  have h := dirichlet_unique ε hε i₀ Ω (fun y => u y - v y)
    (fun x hx => by rw [lap_sub_fun, huv x hx, sub_self])
    (fun y hy => by
      have : y ∉ Ω := (mem_sdiff.mp hy).2
      simp [hu0 y this, hv0 y this])
  funext x
  by_cases hx : x ∈ Ω
  · exact sub_eq_zero.mp (h x hx)
  · rw [hu0 x hx, hv0 x hx]

/-- **`thm:multi-dirichlet-exist` in full**: existence *and uniqueness*. -/
theorem dirichlet_exists_unique (ε : K) (hε : 0 < ε) {n : ℕ} (i₀ : Fin n)
    (Ω : Finset (Fin n → ℤ)) (ρ : (Fin n → ℤ) → K) :
    ∃! u : (Fin n → ℤ) → K, (∀ x, x ∉ Ω → u x = 0) ∧ ∀ x ∈ Ω, -lap ε u x = ρ x := by
  obtain ⟨u, hu0, hu⟩ := dirichlet_solvable ε hε i₀ Ω ρ
  refine ⟨u, ⟨hu0, hu⟩, fun v ⟨hv0, hv⟩ => ?_⟩
  exact dirichlet_eq_of_solutions ε hε i₀ Ω v u hv0 hu0
    (fun x hx => by have := hv x hx; have := hu x hx; linarith)

/-- Uniqueness for the punctured (Zaremba) problem: `u(s) = 1`, `u = 0` off `Ω`,
`Δ_ε u = 0` on `Ω ∖ {s}`. -/
theorem zaremba_unique (ε : K) (hε : 0 < ε) {n : ℕ} (i₀ : Fin n)
    (Ω : Finset (Fin n → ℤ)) (s : Fin n → ℤ) (u v : (Fin n → ℤ) → K)
    (hus : u s = 1) (hu0 : ∀ x, x ∉ Ω → u x = 0) (hu : ∀ x ∈ Ω.erase s, lap ε u x = 0)
    (hvs : v s = 1) (hv0 : ∀ x, x ∉ Ω → v x = 0) (hv : ∀ x ∈ Ω.erase s, lap ε v x = 0) :
    u = v := by
  have h := dirichlet_unique ε hε i₀ (Ω.erase s) (fun y => u y - v y)
    (fun x hx => by rw [lap_sub_fun, hu x hx, hv x hx, sub_self])
    (fun y hy => by
      have hy' : y ∉ Ω.erase s := (mem_sdiff.mp hy).2
      by_cases hys : y = s
      · simp [hys, hus, hvs]
      · have : y ∉ Ω := fun h => hy' (mem_erase.mpr ⟨hys, h⟩)
        simp [hu0 y this, hv0 y this])
  funext x
  by_cases hxs : x = s
  · rw [hxs, hus, hvs]
  by_cases hx : x ∈ Ω
  · exact sub_eq_zero.mp (h x (mem_erase.mpr ⟨hxs, hx⟩))
  · rw [hu0 x hx, hv0 x hx]

/-- **`thm:multi-zaremba` in full**: `u = G/G(s)` has the stated properties *and* is
the unique solution of the punctured problem. -/
theorem zaremba_full (ε : K) (hε : 0 < ε) {n : ℕ} (i₀ : Fin n)
    (Ω : Finset (Fin n → ℤ)) (s : Fin n → ℤ) (hs : s ∈ Ω) (G : (Fin n → ℤ) → K)
    (hG0 : ∀ x, x ∉ Ω → G x = 0) (hG : ∀ x ∈ Ω, -lap ε G x = deltaN ε s x) :
    let u := fun x => G x / G s
    (u s = 1 ∧ (∀ x, x ∉ Ω → u x = 0) ∧ (∀ x, 0 ≤ u x ∧ u x ≤ 1) ∧
      ∀ x ∈ Ω.erase s, lap ε u x = 0) ∧
    ∀ v : (Fin n → ℤ) → K, v s = 1 → (∀ x, x ∉ Ω → v x = 0) →
      (∀ x ∈ Ω.erase s, lap ε v x = 0) → v = u := by
  intro u
  have hz := zaremba ε hε i₀ Ω s hs G hG0 hG
  refine ⟨hz, fun v hvs hv0 hv => ?_⟩
  exact zaremba_unique ε hε i₀ Ω s v u hvs hv0 hv hz.1 hz.2.1 hz.2.2.2

/-- **`thm:multi-representation` in full**: with `G_D(·,s)` the Dirichlet Green's
function (zero off `D`), `u = ∑_{s∈D} ρ(s)(2ε)ⁿ G_D(·,s)` solves `-Δ_ε u = ρ` on `D`,
vanishes off `D`, and is the unique such function. -/
theorem representation_full (ε : K) (hε : 0 < ε) {n : ℕ} (i₀ : Fin n)
    (D : Finset (Fin n → ℤ)) (G : (Fin n → ℤ) → (Fin n → ℤ) → K)
    (hG0 : ∀ s ∈ D, ∀ y, y ∉ D → G s y = 0)
    (hG : ∀ s ∈ D, ∀ x ∈ D, -lap ε (G s) x = deltaN ε s x) (ρ : (Fin n → ℤ) → K) :
    let u := fun y => ∑ s ∈ D, ρ s * (2 * ε) ^ n * G s y
    (∀ x ∈ D, -lap ε u x = ρ x) ∧ (∀ y, y ∉ D → u y = 0) ∧
    ∀ v : (Fin n → ℤ) → K, (∀ y, y ∉ D → v y = 0) → (∀ x ∈ D, -lap ε v x = ρ x) → v = u := by
  intro u
  have h1 := representation ε hε.ne' D G hG ρ
  have h2 : ∀ y, y ∉ D → u y = 0 := fun y hy =>
    sum_eq_zero fun s hs => by rw [hG0 s hs y hy, mul_zero]
  refine ⟨h1, h2, fun v hv0 hv => ?_⟩
  exact dirichlet_eq_of_solutions ε hε i₀ D v u hv0 h2
    (fun x hx => by have := hv x hx; have := h1 x hx; linarith)

end Uniq

section Symbol

open Complex

/-- The complex lattice Laplacian on index functions (`x ↦ 2ε x` on `(2εℤ)ⁿ`). -/
noncomputable def lapC (ε : ℝ) {n : ℕ} (f : (Fin n → ℤ) → ℂ) (x : Fin n → ℤ) : ℂ :=
  ∑ i, (f (x + e i) - 2 * f x + f (x - e i)) / ((2 * ε : ℝ) : ℂ) ^ 2

/-- The plane wave `e_k(x) = exp(i k·x)` restricted to the lattice `x = 2ε m`. -/
noncomputable def planeWave (ε : ℝ) {n : ℕ} (k : Fin n → ℝ) (m : Fin n → ℤ) : ℂ :=
  Complex.exp ((∑ j, ((k j * (2 * ε * m j) : ℝ) : ℂ)) * Complex.I)

/-- The symbol `λ(k) = (4/(2ε)²) ∑ sin²(kᵢ ε)`. -/
noncomputable def symbolLam (ε : ℝ) {n : ℕ} (k : Fin n → ℝ) : ℝ :=
  4 / (2 * ε) ^ 2 * ∑ i, Real.sin (k i * ε) ^ 2

theorem planeWave_shift (ε : ℝ) {n : ℕ} (k : Fin n → ℝ) (m : Fin n → ℤ) (i : Fin n) (s : ℤ) :
    planeWave ε k (m + s • e i) =
      planeWave ε k m * Complex.exp (((k i * (2 * ε * s)) : ℝ) * Complex.I) := by
  unfold planeWave
  rw [← Complex.exp_add, ← Complex.ofReal_sum, ← Complex.ofReal_sum]
  have hsum : ∑ j, k j * (2 * ε * (((m + s • e i) j : ℤ) : ℝ))
      = ∑ j, k j * (2 * ε * (m j : ℝ)) + k i * (2 * ε * s) := by
    have : ∀ j, k j * (2 * ε * (((m + s • e i) j : ℤ) : ℝ))
        = k j * (2 * ε * (m j : ℝ)) + (if j = i then k i * (2 * ε * s) else 0) := by
      intro j
      by_cases h : j = i
      · subst h; simp [e]; ring
      · simp [e, h]
    simp only [this, sum_add_distrib, sum_ite_eq', mem_univ, ite_true]
  rw [hsum]; push_cast; congr 1; ring

/-- **`thm:multi-symbol`, plane-wave part**: `Δ_ε e_k = -λ(k) e_k`, and for real `k`,
`0 ≤ λ(k) ≤ 4n/(2ε)²`. -/
theorem lapC_planeWave (ε : ℝ) (hε : ε ≠ 0) {n : ℕ} (k : Fin n → ℝ) (m : Fin n → ℤ) :
    lapC ε (planeWave ε k) m = -(symbolLam ε k : ℂ) * planeWave ε k m := by
  unfold lapC symbolLam
  have h2 : ((2 * ε : ℝ) : ℂ) ≠ 0 := by exact_mod_cast mul_ne_zero two_ne_zero hε
  have key : ∀ i, planeWave ε k (m + e i) - 2 * planeWave ε k m + planeWave ε k (m - e i)
      = -4 * ((Real.sin (k i * ε) ^ 2 : ℝ) : ℂ) * planeWave ε k m := by
    intro i
    have hp := planeWave_shift ε k m i 1
    have hm := planeWave_shift ε k m i (-1)
    simp only [one_smul, neg_smul] at hp hm
    rw [← sub_eq_add_neg] at hm
    rw [hp, hm]
    set θ : ℝ := k i * (2 * ε)
    have hθ1 : ((k i * (2 * ε * ((1 : ℤ) : ℝ))) : ℝ) = θ := by simp [θ]
    have hθ2 : ((k i * (2 * ε * ((-1 : ℤ) : ℝ))) : ℝ) = -θ := by simp [θ]
    rw [hθ1, hθ2]
    have hc : Complex.exp ((θ : ℂ) * Complex.I) + Complex.exp (((-θ : ℝ) : ℂ) * Complex.I)
        = 2 * Complex.cos θ := by
      rw [Complex.two_cos]; push_cast; ring_nf
    have hcos : Complex.cos (θ : ℂ) = 1 - 2 * Complex.sin ((k i * ε : ℝ) : ℂ) ^ 2 := by
      have h := Complex.cos_two_mul' ((k i * ε : ℝ) : ℂ)
      have : (θ : ℂ) = 2 * ((k i * ε : ℝ) : ℂ) := by simp [θ]; ring
      rw [this, h, Complex.cos_sq', ]; ring
    push_cast at hc hcos ⊢
    linear_combination (planeWave ε k m) * hc + 2 * planeWave ε k m * hcos
  simp only [key]
  have h2' : (2 * (ε : ℂ)) ≠ 0 := by exact_mod_cast mul_ne_zero two_ne_zero hε
  push_cast
  rw [Finset.mul_sum, ← Finset.sum_neg_distrib, Finset.sum_mul]
  refine sum_congr rfl fun i _ => ?_
  field_simp

theorem symbolLam_bounds (ε : ℝ) (hε : 0 < ε) {n : ℕ} (k : Fin n → ℝ) :
    0 ≤ symbolLam ε k ∧ symbolLam ε k ≤ 4 * n / (2 * ε) ^ 2 := by
  unfold symbolLam
  have hs : ∑ i, Real.sin (k i * ε) ^ 2 ≤ n := by
    calc ∑ i, Real.sin (k i * ε) ^ 2 ≤ ∑ _i : Fin n, (1 : ℝ) :=
          sum_le_sum fun i _ => Real.sin_sq_le_one _
      _ = n := by simp
  have h0 : 0 ≤ ∑ i, Real.sin (k i * ε) ^ 2 := sum_nonneg fun i _ => sq_nonneg _
  have hp : 0 < 4 / (2 * ε) ^ 2 := by positivity
  refine ⟨mul_nonneg hp.le h0, ?_⟩
  calc 4 / (2 * ε) ^ 2 * ∑ i, Real.sin (k i * ε) ^ 2 ≤ 4 / (2 * ε) ^ 2 * n :=
        mul_le_mul_of_nonneg_left hs hp.le
    _ = 4 * n / (2 * ε) ^ 2 := by ring

/-- `thm:multi-symbol` in one statement (scalar identity, plane waves, bounds). -/
theorem symbol_full (ε : ℝ) (hε : 0 < ε) {n : ℕ} (k : Fin n → ℝ) :
    (∀ θ j : ℂ, Complex.exp ((j + 1) * θ * Complex.I) - 2 * Complex.exp (j * θ * Complex.I)
        + Complex.exp ((j - 1) * θ * Complex.I)
      = -4 * Complex.sin (θ / 2) ^ 2 * Complex.exp (j * θ * Complex.I)) ∧
    (∀ m, lapC ε (planeWave ε k) m = -(symbolLam ε k : ℂ) * planeWave ε k m) ∧
    0 ≤ symbolLam ε k ∧ symbolLam ε k ≤ 4 * n / (2 * ε) ^ 2 :=
  ⟨second_diff_symbol, lapC_planeWave ε hε.ne' k, symbolLam_bounds ε hε k⟩

end Symbol

end QE.Multi

/-! ## Chapter 9: the rhombus of two thick lines; gluing counts for Pick -/

namespace QE.Geometry

open Real Finset

section Rhombus

/-- Euclidean length of a vector of `ℝ²` (as `Fin 2 → ℝ`). -/
noncomputable def elen (v : Fin 2 → ℝ) : ℝ := Real.sqrt (v 0 ^ 2 + v 1 ^ 2)

/-- The inverse of `x ↦ (u_α·x, u_β·x)` for unit normals `u_α, u_β` (Cramer's rule). -/
noncomputable def rhombL (α β σ τ : ℝ) : Fin 2 → ℝ :=
  ![(σ * sin β - τ * sin α) / sin (β - α), (τ * cos α - σ * cos β) / sin (β - α)]

theorem rhombL_spec (α β σ τ : ℝ) (hθ : sin (β - α) ≠ 0) :
    cos α * rhombL α β σ τ 0 + sin α * rhombL α β σ τ 1 = σ ∧
    cos β * rhombL α β σ τ 0 + sin β * rhombL α β σ τ 1 = τ := by
  have e : sin (β - α) = sin β * cos α - cos β * sin α := sin_sub β α
  simp only [rhombL, Matrix.cons_val_zero, Matrix.cons_val_one]
  constructor
  · field_simp; rw [e]; ring
  · field_simp; rw [e]; ring

theorem rhombL_sub (α β σ τ σ' τ' : ℝ) :
    rhombL α β σ τ - rhombL α β σ' τ' = rhombL α β (σ - σ') (τ - τ') := by
  ext i; fin_cases i <;> simp [rhombL] <;> ring

/-- The strip intersection is the image of the square `[-ε,ε]²` under `rhombL`:
the parallelogram with vertices `rhombL(±ε, ±ε)`. -/
theorem strip_eq_parallelogram (α β ε : ℝ) (hθ : sin (β - α) ≠ 0) :
    {x : Fin 2 → ℝ | |cos α * x 0 + sin α * x 1| ≤ ε ∧ |cos β * x 0 + sin β * x 1| ≤ ε} =
      {x | ∃ σ τ : ℝ, |σ| ≤ ε ∧ |τ| ≤ ε ∧ x = rhombL α β σ τ} := by
  ext x
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨_, _, h1, h2, ?_⟩
    have e : sin (β - α) = sin β * cos α - cos β * sin α := sin_sub β α
    ext i; fin_cases i
    · simp only [rhombL, Matrix.cons_val_zero, Fin.zero_eta]
      field_simp; rw [e]; ring_nf
    · simp only [rhombL, Matrix.cons_val_one, Matrix.cons_val_zero, Fin.mk_one]
      field_simp; rw [e]; ring
  · rintro ⟨σ, τ, h1, h2, rfl⟩
    obtain ⟨e1, e2⟩ := rhombL_spec α β σ τ hθ
    exact ⟨by rw [e1]; exact h1, by rw [e2]; exact h2⟩

theorem half_angle_facts {θ : ℝ} (h0 : 0 < θ) (hπ : θ < π) :
    0 < sin (θ / 2) ∧ 0 < cos (θ / 2) ∧ sin θ = 2 * sin (θ / 2) * cos (θ / 2) ∧
    cos θ = 1 - 2 * sin (θ / 2) ^ 2 := by
  have hs : 0 < sin (θ / 2) := sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)
  have hc : 0 < cos (θ / 2) := cos_pos_of_mem_Ioo ⟨by linarith, by linarith⟩
  have h2 : θ = 2 * (θ / 2) := by ring
  refine ⟨hs, hc, ?_, ?_⟩
  · conv_lhs => rw [h2]
    exact sin_two_mul _
  · conv_lhs => rw [h2]
    rw [cos_two_mul]; nlinarith [sin_sq_add_cos_sq (θ / 2)]

/-- **`thm:geometry-strips`, rhombus part.** For unit normals at angle `θ = β - α ∈ (0,π)`
the intersection of the two thick lines of half-width `ε` is the parallelogram with
vertices `rhombL(±ε,±ε)`; all four sides have length `2ε/sin θ` (a rhombus), and the
diagonals have lengths `2ε/cos(θ/2)` and `2ε/sin(θ/2)`. -/
theorem strip_rhombus (α β ε : ℝ) (hε : 0 ≤ ε) (h0 : 0 < β - α) (hπ : β - α < π) :
    {x : Fin 2 → ℝ | |cos α * x 0 + sin α * x 1| ≤ ε ∧ |cos β * x 0 + sin β * x 1| ≤ ε} =
      {x | ∃ σ τ : ℝ, |σ| ≤ ε ∧ |τ| ≤ ε ∧ x = rhombL α β σ τ} ∧
    (∀ τ, elen (rhombL α β ε τ - rhombL α β (-ε) τ) = 2 * ε / sin (β - α)) ∧
    (∀ σ, elen (rhombL α β σ ε - rhombL α β σ (-ε)) = 2 * ε / sin (β - α)) ∧
    elen (rhombL α β ε ε - rhombL α β (-ε) (-ε)) = 2 * ε / cos ((β - α) / 2) ∧
    elen (rhombL α β ε (-ε) - rhombL α β (-ε) ε) = 2 * ε / sin ((β - α) / 2) := by
  obtain ⟨hs, hc, hsin, hcos⟩ := half_angle_facts h0 hπ
  set θ := β - α with hθdef
  have hS : 0 < sin θ := by rw [hsin]; positivity
  have e : sin θ = sin β * cos α - cos β * sin α := sin_sub β α
  have ec : cos θ = cos β * cos α + sin β * sin α := cos_sub β α
  have pa := sin_sq_add_cos_sq α
  have pb := sin_sq_add_cos_sq β
  have key : ∀ σ τ : ℝ, (rhombL α β σ τ 0) ^ 2 + (rhombL α β σ τ 1) ^ 2
      = (σ ^ 2 + τ ^ 2 - 2 * σ * τ * cos θ) / sin θ ^ 2 := by
    intro σ τ
    simp only [rhombL, Matrix.cons_val_zero, Matrix.cons_val_one]
    rw [← hθdef, ec]
    field_simp
    linear_combination σ ^ 2 * pb + τ ^ 2 * pa
  have len : ∀ σ τ : ℝ, ∀ L : ℝ, 0 ≤ L →
      (σ ^ 2 + τ ^ 2 - 2 * σ * τ * cos θ) / sin θ ^ 2 = L ^ 2 →
      elen (rhombL α β σ τ) = L := by
    intro σ τ L hL h
    unfold elen; rw [key, h, Real.sqrt_sq hL]
  refine ⟨strip_eq_parallelogram α β ε hS.ne', fun τ => ?_, fun σ => ?_, ?_, ?_⟩
  · rw [rhombL_sub, sub_self]
    refine len _ _ _ (by positivity) ?_
    field_simp; ring
  · rw [rhombL_sub, sub_self]
    refine len _ _ _ (by positivity) ?_
    field_simp; ring
  · rw [rhombL_sub]
    refine len _ _ _ (by positivity) ?_
    rw [hsin, hcos]; field_simp; ring
  · rw [rhombL_sub]
    refine len _ _ _ (by positivity) ?_
    rw [hsin, hcos]; field_simp
    nlinarith [sin_sq_add_cos_sq (θ / 2)]

end Rhombus

section Glue

/-- **`lem:geometry-pick-glue`, the counts.** Let the lattice points of `P₁, P₂, P` be
split into interior and boundary points, and let `C` be the common boundary path with
`k = #C ≥ 2` points and distinct endpoints `p, q`.  Assume the incidences that
"`P = P₁ ∪ P₂` with disjoint interiors, glued along `C`" means: the boundaries meet
exactly in `C`; the boundary of `P` is `(B₁ ∪ B₂) ∖ (C ∖ {p,q})`; the interior of `P`
is `I₁ ∪ I₂ ∪ (C ∖ {p,q})`; each interior is disjoint from its own boundary, and the two interiors are disjoint.
Then `I = I₁ + I₂ + (k - 2)` and `B = B₁ + B₂ - 2k + 2`, so `2I + B - 2` is additive. -/
theorem pick_glue_counts {α : Type*} [DecidableEq α]
    (I₁ B₁ I₂ B₂ I B C : Finset α) (p q : α) (hpq : p ≠ q) (hp : p ∈ C) (hq : q ∈ C)
    (hC : B₁ ∩ B₂ = C)
    (hB : B = (B₁ ∪ B₂) \ (C \ {p, q}))
    (hI : I = I₁ ∪ I₂ ∪ (C \ {p, q}))
    (h11 : Disjoint I₁ B₁) (h22 : Disjoint I₂ B₂)
    (hII : Disjoint I₁ I₂) :
    (I.card : ℤ) = I₁.card + I₂.card + (C.card - 2) ∧
    (B.card : ℤ) = B₁.card + B₂.card - 2 * C.card + 2 ∧
    2 * (I.card : ℤ) + B.card - 2 = (2 * I₁.card + B₁.card - 2) + (2 * I₂.card + B₂.card - 2) := by
  have hCB1 : C ⊆ B₁ := hC ▸ inter_subset_left
  have hCB2 : C ⊆ B₂ := hC ▸ inter_subset_right
  have hpqC : ({p, q} : Finset α) ⊆ C := by
    intro x hx; simp only [mem_insert, mem_singleton] at hx; rcases hx with rfl | rfl <;> assumption
  have hC0 : (C \ {p, q}).card = C.card - 2 := by
    rw [card_sdiff_of_subset hpqC, card_pair hpq]
  have hC2 : 2 ≤ C.card := by
    have := card_le_card hpqC; rwa [card_pair hpq] at this
  -- boundary
  have hsub : C \ {p, q} ⊆ B₁ ∪ B₂ := fun x hx => mem_union_left _ (hCB1 (mem_sdiff.1 hx).1)
  have hBc : B.card = (B₁ ∪ B₂).card - (C.card - 2) := by
    rw [hB, card_sdiff_of_subset hsub, hC0]
  have hU := card_union_add_card_inter B₁ B₂
  rw [hC] at hU
  -- interior
  have d1 : Disjoint (I₁ ∪ I₂) (C \ {p, q}) := by
    rw [disjoint_union_left]
    exact ⟨disjoint_of_subset_right (fun x hx => hCB1 (mem_sdiff.1 hx).1) h11,
      disjoint_of_subset_right (fun x hx => hCB2 (mem_sdiff.1 hx).1) h22⟩
  have hIc : I.card = I₁.card + I₂.card + (C.card - 2) := by
    rw [hI, card_union_of_disjoint d1, card_union_of_disjoint hII, hC0]
  have hle : C.card - 2 ≤ (B₁ ∪ B₂).card := by
    have := card_le_card (fun x hx => mem_union_left _ (hCB1 hx) : C ⊆ B₁ ∪ B₂)
    omega
  refine ⟨?_, ?_, ?_⟩
  · rw [hIc]; push_cast [Nat.cast_sub hC2]; ring
  · rw [hBc]; push_cast [Nat.cast_sub hle, Nat.cast_sub hC2]; omega
  · rw [hIc, hBc]; push_cast [Nat.cast_sub hle, Nat.cast_sub hC2]; omega

end Glue

section StripAsymptotic

open Finset

/-- Integers in a real interval: `|#([⌈α⌉, ⌊β⌋] ∩ ℤ) - (β - α)| ≤ 1`. -/
lemma card_Icc_ceil_floor_bound {α β : ℝ} (h : α ≤ β) :
    |((Icc ⌈α⌉ ⌊β⌋).card : ℝ) - (β - α)| ≤ 1 := by
  rw [Int.card_Icc]
  have f1 := Int.floor_le β
  have f2 := Int.lt_floor_add_one β
  have c1 := Int.le_ceil α
  have c2 := Int.ceil_lt_add_one α
  have hnn : (0 : ℤ) ≤ ⌊β⌋ + 1 - ⌈α⌉ := by
    have : ((⌈α⌉ : ℤ) : ℝ) < ⌊β⌋ + 2 := by linarith
    have : ⌈α⌉ < ⌊β⌋ + 2 := by exact_mod_cast this
    omega
  have hc : (((⌊β⌋ + 1 - ⌈α⌉).toNat : ℕ) : ℝ) = ((⌊β⌋ : ℝ) + 1 - ⌈α⌉) := by
    rw [← Int.cast_natCast, Int.toNat_of_nonneg hnn]; push_cast; ring
  rw [hc, abs_le]
  constructor <;> linarith

/-- Fibre membership: for `s > 0`, `|t + s u| ≤ w ↔ u ∈ [⌈(-w-t)/s⌉, ⌊(w-t)/s⌋]`. -/
lemma mem_fibre_iff (s t w u : ℤ) (hs : 0 < s) :
    u ∈ Icc ⌈((-w - t : ℤ) : ℝ) / s⌉ ⌊((w - t : ℤ) : ℝ) / s⌋ ↔ |t + s * u| ≤ w := by
  have hs' : (0 : ℝ) < s := by exact_mod_cast hs
  rw [mem_Icc, Int.ceil_le, Int.le_floor, div_le_iff₀ hs', le_div_iff₀ hs', abs_le]
  constructor
  · rintro ⟨h1, h2⟩
    have h1' : (-w - t : ℤ) ≤ u * s := by exact_mod_cast h1
    have h2' : u * s ≤ (w - t : ℤ) := by exact_mod_cast h2
    constructor <;> linarith
  · rintro ⟨h1, h2⟩
    constructor
    · have : (-w - t : ℤ) ≤ u * s := by linarith
      exact_mod_cast this
    · have : u * s ≤ (w - t : ℤ) := by linarith
      exact_mod_cast this

/-- The triangular strip set `{u : |g u₁| ≤ w, |r u₁ + s u₂| ≤ w}` as a sigma finset. -/
noncomputable def triPts (g r s : ℤ) (w : ℕ) : Finset (Σ _ : ℤ, ℤ) :=
  (Icc (-((w : ℤ) / g)) ((w : ℤ) / g)).sigma fun u₁ =>
    Icc ⌈((-(w : ℤ) - r * u₁ : ℤ) : ℝ) / s⌉ ⌊(((w : ℤ) - r * u₁ : ℤ) : ℝ) / s⌋

lemma mem_triPts (g r s : ℤ) (w : ℕ) (hg : 0 < g) (hs : 0 < s) (u : Σ _ : ℤ, ℤ) :
    u ∈ triPts g r s w ↔ |g * u.1| ≤ w ∧ |r * u.1 + s * u.2| ≤ w := by
  unfold triPts
  rw [mem_sigma, mem_fibre_iff s (r * u.1) w u.2 hs]
  refine and_congr ?_ Iff.rfl
  rw [mem_Icc, abs_le]
  constructor
  · rintro ⟨h1, h2⟩
    have e1 := (Int.le_ediv_iff_mul_le hg).1 h2
    have e2 := (Int.le_ediv_iff_mul_le hg).1 (show -u.1 ≤ (w : ℤ) / g by linarith)
    constructor <;> linarith
  · rintro ⟨h1, h2⟩
    constructor
    · have := (Int.le_ediv_iff_mul_le hg).2 (show -u.1 * g ≤ (w : ℤ) by linarith)
      linarith
    · exact (Int.le_ediv_iff_mul_le hg).2 (by linarith)

lemma card_triPts_bound (g r s : ℤ) (w : ℕ) (hg : 0 < g) (hs : 0 < s) :
    |((triPts g r s w).card : ℝ) - (2 * (w : ℝ) + 1) ^ 2 / ((g : ℝ) * s)| ≤ 3 * (2 * (w : ℝ) + 1) := by
  unfold triPts
  rw [card_sigma]
  set q : ℤ := (w : ℤ) / g with hq
  have hg' : (0 : ℝ) < g := by exact_mod_cast hg
  have hs' : (0 : ℝ) < s := by exact_mod_cast hs
  have hg1 : (1 : ℝ) ≤ g := by exact_mod_cast hg
  have hs1 : (1 : ℝ) ≤ s := by exact_mod_cast hs
  have hq0 : 0 ≤ q := Int.ediv_nonneg (by positivity) hg.le
  -- each fibre has `2w/s ± 1` points
  have hfib : ∀ u₁ : ℤ, |((Icc ⌈((-(w : ℤ) - r * u₁ : ℤ) : ℝ) / s⌉
      ⌊(((w : ℤ) - r * u₁ : ℤ) : ℝ) / s⌋).card : ℝ) - 2 * w / s| ≤ 1 := by
    intro u₁
    have hle : ((-(w : ℤ) - r * u₁ : ℤ) : ℝ) / s ≤ (((w : ℤ) - r * u₁ : ℤ) : ℝ) / s := by
      apply div_le_div_of_nonneg_right _ hs'.le; push_cast; linarith [(Nat.cast_nonneg w : (0 : ℝ) ≤ w)]
    have := card_Icc_ceil_floor_bound hle
    have e : (((w : ℤ) - r * u₁ : ℤ) : ℝ) / s - ((-(w : ℤ) - r * u₁ : ℤ) : ℝ) / s = 2 * w / s := by
      push_cast; field_simp; ring
    rwa [e] at this
  have hn : ((Icc (-q) q).card : ℝ) = 2 * q + 1 := by
    rw [Int.card_Icc]
    have : (q + 1 - -q).toNat = (2 * q + 1).toNat := by congr 1; ring
    rw [this, ← Int.cast_natCast, Int.toNat_of_nonneg (by omega)]; push_cast; ring
  have hsum : |(∑ u₁ ∈ Icc (-q) q, ((Icc ⌈((-(w : ℤ) - r * u₁ : ℤ) : ℝ) / s⌉
      ⌊(((w : ℤ) - r * u₁ : ℤ) : ℝ) / s⌋).card : ℝ)) - (2 * q + 1) * (2 * w / s)|
      ≤ 2 * q + 1 := by
    rw [← hn, ← nsmul_eq_mul, ← sum_const, ← sum_sub_distrib]
    calc _ ≤ ∑ u₁ ∈ Icc (-q) q, |((Icc ⌈((-(w : ℤ) - r * u₁ : ℤ) : ℝ) / s⌉
          ⌊(((w : ℤ) - r * u₁ : ℤ) : ℝ) / s⌋).card : ℝ) - 2 * w / s| := abs_sum_le_sum_abs _ _
      _ ≤ ∑ _u₁ ∈ Icc (-q) q, (1 : ℝ) := sum_le_sum fun u₁ _ => hfib u₁
      _ = _ := by simp
  push_cast at hsum ⊢
  -- `q` is `w/g` up to rounding
  have hq1 : (q : ℝ) * g ≤ w := by
    have : q * g ≤ (w : ℤ) := Int.ediv_mul_le _ hg.ne'
    exact_mod_cast this
  have hq2 : (w : ℝ) + 1 ≤ (q + 1) * g := by
    have : (w : ℤ) < (q + 1) * g := Int.lt_mul_ediv_self_add hg |>.trans_eq (by ring)
    have : (w : ℤ) + 1 ≤ (q + 1) * g := this
    exact_mod_cast this
  have hw : (0 : ℝ) ≤ w := by positivity
  have hqw : (q : ℝ) ≤ w := by nlinarith
  -- assemble
  have h2q : |(2 * (q : ℝ) + 1) - (2 * w + 1) / g| ≤ 1 := by
    have u1 : (2 * (w : ℝ) + 1) / g ≤ 2 * q + 2 := by rw [div_le_iff₀ hg']; nlinarith
    have u2 : 2 * (q : ℝ) ≤ (2 * w + 1) / g := by rw [le_div_iff₀ hg']; nlinarith
    rw [abs_le]; constructor <;> linarith
  have hsplit : (∑ u₁ ∈ Icc (-q) q, ((Icc ⌈((-(w : ℝ) - r * u₁)) / s⌉
      ⌊(((w : ℝ) - r * u₁)) / s⌋).card : ℝ)) - (2 * w + 1) ^ 2 / (g * s)
      = ((∑ u₁ ∈ Icc (-q) q, ((Icc ⌈((-(w : ℝ) - r * u₁)) / s⌉
      ⌊(((w : ℝ) - r * u₁)) / s⌋).card : ℝ)) - (2 * q + 1) * (2 * w / s))
        + ((2 * q + 1) - (2 * w + 1) / g) * (2 * w / s) - (2 * w + 1) / (g * s) := by
    field_simp; ring
  rw [hsplit]
  have hA : |((2 * (q : ℝ) + 1) - (2 * w + 1) / g) * (2 * w / s)| ≤ 2 * w := by
    rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 2 * w / s)]
    calc _ ≤ 1 * (2 * (w : ℝ) / (s : ℝ)) := mul_le_mul_of_nonneg_right h2q (by positivity)
      _ ≤ 2 * w := by rw [one_mul]; exact div_le_self (by positivity : (0 : ℝ) ≤ 2 * w) hs1
  have hB : (2 * (w : ℝ) + 1) / (g * s) ≤ 2 * w + 1 := by
    rw [div_le_iff₀ (by positivity)]; nlinarith [mul_le_mul hg1 hs1 zero_le_one hg'.le]
  have hB0 : 0 ≤ (2 * (w : ℝ) + 1) / (g * s) := by positivity
  calc _ ≤ |(∑ u₁ ∈ Icc (-q) q, ((Icc ⌈((-(w : ℝ) - r * u₁)) / s⌉
      ⌊(((w : ℝ) - r * u₁)) / s⌋).card : ℝ)) - (2 * q + 1) * (2 * w / s)|
        + |((2 * (q : ℝ) + 1) - (2 * w + 1) / g) * (2 * w / s)|
        + |(2 * (w : ℝ) + 1) / (g * s)| :=
          (abs_sub _ _).trans (add_le_add_left (abs_add_le _ _) _)
    _ ≤ (2 * q + 1) + 2 * w + (2 * w + 1) := by
        rw [abs_of_nonneg hB0]; linarith
    _ ≤ 3 * (2 * w + 1) := by linarith

/-- Unimodular change of variables: the strip intersection for `M` and the triangular
one for `M U` (Hermite form `[[g,0],[r,s]]`) have the same number of lattice points. -/
lemma card_stripPts_eq_triPts (a b c d g a' b' x y σ : ℤ) (w : ℕ) (hD : a * d - b * c ≠ 0)
    (ha : a = g * a') (hb : b = g * b') (hxy : a' * x + b' * y = 1) (hσ : σ * σ = 1)
    (hg : 0 < g) (hs : 0 < σ * (d * a' - c * b')) :
    (stripPts a b c d w).card = (triPts g (c * x + d * y) (σ * (d * a' - c * b')) w).card := by
  refine Finset.card_nbij' (fun k => (⟨a' * k.1 + b' * k.2, σ * (-y * k.1 + x * k.2)⟩ : Σ _ : ℤ, ℤ))
    (fun u => (x * u.1 - σ * b' * u.2, y * u.1 + σ * a' * u.2)) ?_ ?_ ?_ ?_
  · intro k hk
    have hk' := (mem_stripPts a b c d w hD k).1 (Finset.mem_coe.1 hk)
    refine Finset.mem_coe.2 ((mem_triPts _ _ _ w hg hs _).2 ⟨?_, ?_⟩)
    · have : g * (a' * k.1 + b' * k.2) = a * k.1 + b * k.2 := by rw [ha, hb]; ring
      simpa only [this] using hk'.1
    · have : (c * x + d * y) * (a' * k.1 + b' * k.2) +
          σ * (d * a' - c * b') * (σ * (-y * k.1 + x * k.2)) = c * k.1 + d * k.2 := by
        linear_combination (c * k.1 + d * k.2) * hxy + (d * a' - c * b') * (-y * k.1 + x * k.2) * hσ
      simpa only [this] using hk'.2
  · intro u hu
    have hu' := (mem_triPts _ _ _ w hg hs u).1 (Finset.mem_coe.1 hu)
    refine Finset.mem_coe.2 ((mem_stripPts a b c d w hD _).2 ⟨?_, ?_⟩)
    · have : a * (x * u.1 - σ * b' * u.2) + b * (y * u.1 + σ * a' * u.2) = g * u.1 := by
        rw [ha, hb]; linear_combination g * u.1 * hxy
      simp only; rw [this]; exact hu'.1
    · have : c * (x * u.1 - σ * b' * u.2) + d * (y * u.1 + σ * a' * u.2)
          = (c * x + d * y) * u.1 + σ * (d * a' - c * b') * u.2 := by ring
      simp only; rw [this]; exact hu'.2
  · intro k _
    simp only
    ext
    · linear_combination k.1 * hxy - b' * (-y * k.1 + x * k.2) * hσ
    · linear_combination k.2 * hxy + a' * (-y * k.1 + x * k.2) * hσ
  · intro u _
    simp only
    refine Sigma.ext ?_ (heq_of_eq ?_)
    · simp only; linear_combination u.1 * hxy
    · simp only; linear_combination σ * σ * u.2 * hxy + u.2 * hσ

/-- **Exact count of `S_w` up to `O(w)`** (the remark after
`thm:geometry-strips-count`): for `D = ad - bc ≠ 0`,
`|#S_w - (2w+1)²/|D|| ≤ 3(2w+1)`. -/
theorem strip_count_asymptotic (a b c d : ℤ) (w : ℕ) (hD : a * d - b * c ≠ 0) :
    |((stripPts a b c d w).card : ℝ) - (2 * (w : ℝ) + 1) ^ 2 / abs ((a * d - b * c : ℤ) : ℝ)|
      ≤ 3 * (2 * (w : ℝ) + 1) := by
  set g : ℤ := (Int.gcd a b : ℤ) with hgdef
  have hab : a ≠ 0 ∨ b ≠ 0 := by
    by_contra h; push Not at h; apply hD; rw [h.1, h.2]; ring
  have hg : 0 < g := by
    have : 0 < Int.gcd a b := Int.gcd_pos_iff.2 hab
    rw [hgdef]; exact_mod_cast this
  obtain ⟨a', ha⟩ : g ∣ a := Int.gcd_dvd_left a b
  obtain ⟨b', hb⟩ : g ∣ b := Int.gcd_dvd_right a b
  have hbez : g = a * Int.gcdA a b + b * Int.gcdB a b := Int.gcd_eq_gcd_ab a b
  obtain ⟨x, hx⟩ : ∃ x, x = Int.gcdA a b := ⟨_, rfl⟩
  obtain ⟨y, hy⟩ : ∃ y, y = Int.gcdB a b := ⟨_, rfl⟩
  rw [← hx, ← hy] at hbez
  have hxy : a' * x + b' * y = 1 := by
    have : g * (a' * x + b' * y) = g * 1 := by
      rw [mul_one]
      calc g * (a' * x + b' * y) = a * x + b * y := by rw [ha, hb]; ring
        _ = g := hbez.symm
    exact mul_left_cancel₀ hg.ne' this
  set s₀ := d * a' - c * b' with hs₀
  have hDs : a * d - b * c = g * s₀ := by rw [ha, hb, hs₀]; ring
  have hs₀0 : s₀ ≠ 0 := by intro h; apply hD; rw [hDs, h, mul_zero]
  obtain ⟨σ, hσ, hs⟩ : ∃ σ : ℤ, σ * σ = 1 ∧ σ * s₀ = |s₀| := by
    rcases lt_or_gt_of_ne hs₀0 with h | h
    · exact ⟨-1, by norm_num, by rw [abs_of_neg h]; ring⟩
    · exact ⟨1, by norm_num, by rw [abs_of_pos h]; ring⟩
  have hspos : 0 < σ * s₀ := by rw [hs]; exact abs_pos.2 hs₀0
  rw [card_stripPts_eq_triPts a b c d g a' b' x y σ w hD ha hb hxy hσ hg hspos]
  have hgs : abs ((a * d - b * c : ℤ) : ℝ) = (g : ℝ) * ((σ * s₀ : ℤ) : ℝ) := by
    rw [hDs, hs]; push_cast; rw [abs_mul, abs_of_pos (by exact_mod_cast hg : (0 : ℝ) < g)]
  rw [hgs]
  exact card_triPts_bound g _ _ w hg hspos

end StripAsymptotic

end QE.Geometry

/-! ## Chapter 10: Brouwer as a shadow, for every admissible `n` and for infinite `n` -/

namespace QE.Topology

open Filter _root_.Topology

/-- **`thm:topology-brouwer-shadow`, search part.** If `δ` is a modulus of uniform
continuity of `F` for `η/2` in the sup-distance of `ℝ × ℝ`, then for *every*
`n > max(1/δ, 2/η)` the Sperner search on `{0,1/n,…,1}²` returns a lattice vertex `p`
with `0 ≤ F₁(p) - p₁ ≤ η` and `0 ≤ F₂(p) - p₂ ≤ η`. -/
theorem brouwer_search_any_n (F : ℝ × ℝ → ℝ × ℝ)
    (hmaps : ∀ p ∈ Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1,
      F p ∈ Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1)
    (η δ : ℝ) (hη : 0 < η) (hδ : 0 < δ)
    (hδf : ∀ p ∈ Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1,
      ∀ q ∈ Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1, dist p q < δ → dist (F p) (F q) < η / 2)
    (n : ℕ) (hn : max (1 / δ) (2 / η) < n) :
    ∃ i ≤ n, ∃ j ≤ n,
      0 ≤ (F ((i : ℝ) / n, (j : ℝ) / n)).1 - (i : ℝ) / n ∧
      (F ((i : ℝ) / n, (j : ℝ) / n)).1 - (i : ℝ) / n ≤ η ∧
      0 ≤ (F ((i : ℝ) / n, (j : ℝ) / n)).2 - (j : ℝ) / n ∧
      (F ((i : ℝ) / n, (j : ℝ) / n)).2 - (j : ℝ) / n ≤ η := by
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
  exact ⟨i, hi, j, hj, h1, h2, h3, h4⟩

/-- **`thm:topology-brouwer-shadow`, infinite `n`.** Let `n = [N]` be an infinite
hypernatural (`N → ∞` along the ultrafilter). (i) There are lattice vertices
`p = [(iₖ/Nₖ, jₖ/Nₖ)]` of mesh `1/n` with `|F(p) - p| ≤ η` for every standard `η > 0`
(as the search of `brouwer_search_any_n` provides at every level beyond the threshold).
(ii) For any such vertex the standard part `q = st p` exists, lies in the square, and is
a fixed point: `F q = q`. -/
theorem brouwer_infinite_grid (F : ℝ × ℝ → ℝ × ℝ)
    (hF : ContinuousOn F (Set.Icc 0 1 ×ˢ Set.Icc 0 1))
    (hmaps : ∀ p ∈ Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1,
      F p ∈ Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1)
    (N : ℕ → ℕ) (hN : Tendsto N (hyperfilter ℕ : Filter ℕ) atTop) :
    (∃ i j : ℕ → ℕ, (∀ k, i k ≤ N k ∧ j k ≤ N k) ∧
      ∀ η : ℝ, 0 < η → ∀ᶠ k in (hyperfilter ℕ : Filter ℕ),
        |(F ((i k : ℝ) / N k, (j k : ℝ) / N k)).1 - (i k : ℝ) / N k| ≤ η ∧
        |(F ((i k : ℝ) / N k, (j k : ℝ) / N k)).2 - (j k : ℝ) / N k| ≤ η) ∧
    (∀ i j : ℕ → ℕ, (∀ k, i k ≤ N k ∧ j k ≤ N k) →
      (∀ η : ℝ, 0 < η → ∀ᶠ k in (hyperfilter ℕ : Filter ℕ),
        |(F ((i k : ℝ) / N k, (j k : ℝ) / N k)).1 - (i k : ℝ) / N k| ≤ η ∧
        |(F ((i k : ℝ) / N k, (j k : ℝ) / N k)).2 - (j k : ℝ) / N k| ≤ η) →
      ∃ q ∈ Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1,
        Tendsto (fun k => ((i k : ℝ) / N k, (j k : ℝ) / N k)) (hyperfilter ℕ : Filter ℕ) (𝓝 q) ∧
        F q = q) := by
  classical
  set S := Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1 with hS
  have hmem : ∀ (n a : ℕ), a ≤ n → ((a : ℝ) / n) ∈ Set.Icc (0 : ℝ) 1 := by
    intro n a ha
    refine ⟨by positivity, ?_⟩
    rcases Nat.eq_zero_or_pos n with h | h
    · subst h; simp
    · rw [div_le_one (by exact_mod_cast h)]; exact_mod_cast ha
  -- defect of a grid vertex
  let D : ℕ → ℕ × ℕ → ℝ := fun n ij =>
    max |(F ((ij.1 : ℝ) / n, (ij.2 : ℝ) / n)).1 - (ij.1 : ℝ) / n|
        |(F ((ij.1 : ℝ) / n, (ij.2 : ℝ) / n)).2 - (ij.2 : ℝ) / n|
  have hne : ∀ n : ℕ, (Finset.range (n + 1) ×ˢ Finset.range (n + 1)).Nonempty :=
    fun n => ⟨(0, 0), by simp⟩
  choose m hm hmin using fun n => Finset.exists_min_image _ (D n) (hne n)
  refine ⟨⟨fun k => (m (N k)).1, fun k => (m (N k)).2, fun k => ?_, ?_⟩, ?_⟩
  · have := hm (N k); simp only [Finset.mem_product, Finset.mem_range] at this
    exact ⟨by simp only; omega, by simp only; omega⟩
  · intro η hη
    have hu := (isCompact_Icc.prod isCompact_Icc).uniformContinuousOn_of_continuous hF
    rw [Metric.uniformContinuousOn_iff] at hu
    obtain ⟨δ, hδ, hδf⟩ := hu (η / 2) (by linarith)
    obtain ⟨n₀, hn₀⟩ := exists_nat_gt (max (1 / δ) (2 / η))
    filter_upwards [hN.eventually_ge_atTop n₀] with k hk
    have hlt : max (1 / δ) (2 / η) < (N k : ℝ) :=
      hn₀.trans_le (by exact_mod_cast hk)
    obtain ⟨i, hi, j, hj, h1, h2, h3, h4⟩ :=
      brouwer_search_any_n F hmaps η δ hη hδ (fun p hp q hq h => hδf p hp q hq h) (N k) hlt
    have hD : D (N k) (i, j) ≤ η := by
      simp only [D]
      refine max_le ?_ ?_ <;> rw [abs_le] <;> constructor <;> linarith
    have := (hmin (N k) (i, j) (by simp [Finset.mem_product]; omega)).trans hD
    simp only [D] at this
    exact ⟨(le_max_left _ _).trans this, (le_max_right _ _).trans this⟩
  · intro i j hij hdef
    let p : ℕ → ℝ × ℝ := fun k => ((i k : ℝ) / N k, (j k : ℝ) / N k)
    have hpS : ∀ k, p k ∈ S := fun k => ⟨hmem _ _ (hij k).1, hmem _ _ (hij k).2⟩
    obtain ⟨q, hq, hle⟩ := (isCompact_Icc.prod isCompact_Icc).ultrafilter_le_nhds
      (Ultrafilter.map p (hyperfilter ℕ))
      (by rw [Ultrafilter.coe_map, Filter.le_principal_iff]; exact Filter.mem_map.2 (Filter.univ_mem' hpS))
    rw [Ultrafilter.coe_map] at hle
    have hp : Tendsto p (hyperfilter ℕ : Filter ℕ) (𝓝 q) := hle
    have hpw : Tendsto p (hyperfilter ℕ : Filter ℕ) (𝓝[S] q) :=
      tendsto_nhdsWithin_iff.2 ⟨hp, Eventually.of_forall hpS⟩
    have hFp : Tendsto (fun k => F (p k)) (hyperfilter ℕ : Filter ℕ) (𝓝 (F q)) :=
      (hF q hq).tendsto.comp hpw
    have hz : ∀ (g : ℕ → ℝ), (∀ η : ℝ, 0 < η → ∀ᶠ k in (hyperfilter ℕ : Filter ℕ), |g k| ≤ η) →
        Tendsto g (hyperfilter ℕ : Filter ℕ) (𝓝 0) := by
      intro g hg
      rw [Metric.tendsto_nhds]
      intro η hη
      filter_upwards [hg (η / 2) (by linarith)] with k hk
      rw [Real.dist_eq, sub_zero]; linarith
    have t1 := hz _ (fun η hη => (hdef η hη).mono fun k hk => hk.1)
    have t2 := hz _ (fun η hη => (hdef η hη).mono fun k hk => hk.2)
    have l1 : Tendsto (fun k => (F (p k)).1 - (p k).1) (hyperfilter ℕ : Filter ℕ)
        (𝓝 ((F q).1 - q.1)) :=
      ((continuous_fst.tendsto _).comp hFp).sub ((continuous_fst.tendsto _).comp hp)
    have l2 : Tendsto (fun k => (F (p k)).2 - (p k).2) (hyperfilter ℕ : Filter ℕ)
        (𝓝 ((F q).2 - q.2)) :=
      ((continuous_snd.tendsto _).comp hFp).sub ((continuous_snd.tendsto _).comp hp)
    have e1 := tendsto_nhds_unique l1 t1
    have e2 := tendsto_nhds_unique l2 t2
    exact ⟨q, hq, hp, Prod.ext (by linarith) (by linarith)⟩

end QE.Topology
