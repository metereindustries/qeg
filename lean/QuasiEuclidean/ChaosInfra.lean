-- SPDX-License-Identifier: MIT
-- Copyright 2026 Metere Industries, Inc. Author: Alfredo Metere.
-- Quasi-Euclidean Granular Geometry. Any derivative work must carry this notice:
--   This work is derivative of the Quasi-Euclidean Granular Geometry book
--   authored by Alfredo Metere. Copyright 2026 Metere Industries, Inc.
--   All rights reserved
-- See LICENSE.md and NOTICE.

import QuasiEuclidean.NSA_Loeb
import QuasiEuclidean.OpenSto
import QuasiEuclidean.BerryEsseenInfra

/-!
# Infrastructure for the chaos shadow theorems (`thm:stoch-chaos-shadow`, `thm:stoch-chaos-lifting`)

The Walsh chaos of an internal functional of Anderson's walk is compared with the
Wiener–Itô chaos of Brownian motion.  Everything is built from finite coin spaces and the Loeb
measure of `QuasiEuclidean.NSA_Loeb`.

* **Calculus and coins** (`QE.Chaos.Calc`): iterated directional derivatives `dirD` and central
  differences `cds`, the regularity class `DBnd`, their symmetry, Taylor bounds; the Walsh
  coefficients of a cylinder functional (`coeff_walk`), the block Lindeberg comparison, and the
  granular kernel estimate `kernel_coin_bound` (coarse coins against fine block sums).
* **Hypercontractivity** (`QE.Chaos.Bon`): Bonami's inequality `E F⁴ ≤ 9^d (E F²)²` for Boolean
  functions of degree `≤ d`, and the Lindeberg invariance principle for multilinear polynomials
  (`invariance4_coins`, `invariance3_coins`).
* **Loeb integration** (`QE.Chaos.Loeb`): S-integrability `SInt`, `st E X = ∫ st X dL`
  (`st_iE_eq_integral`), Fatou, the `L²` identities, the walk transfer and the identification of
  the laws with Mathlib's Brownian motion (`integral_brownian_eq`).
* **Density** (`QE.Chaos.Dense`): exponentials of increments are dense in `L²` of the path
  σ-algebra (`ae_eq_zero_of_orthogonal_exp`), via complex moment generating functions and
  Cramér–Wold.
* **Discrete exponential** (`QE.Chaos.DExp`): Newton's identities, homogenised Hermite
  polynomials `heH`, `st e_m = heH_m(a, s)/m!`, `st ∏(1+x_j) = exp(a - s/2)`, coin moments.
* **Wiener chaos** (`QE.Chaos.Wiener`): step functions, `I₁`, exponentials, the chaos `chaos m`
  (closed span of `He_m(I₁ h)`, `‖h‖ = 1`), its projection `Pi m`, the projection of an
  exponential (`Pi_expo`), density in the path σ-algebra (`mem_expoSpan`) and the chaos
  decomposition (`tendsto_chaosSum`).
* **Lifting** (`QE.Chaos.Lift`): the Gaussian facts on the Loeb space (`gaussFacts_loeb`) and the
  lifting theorem `chaos_lifting`.
* **Shadow theorem** (`QE.Chaos.Shadow`): (i) `chaos_kernel_shadow`; (ii) `chaos_L2_shadow` and
  its lattice forms; (iii) `law_chaos_gauss4`, `law_chaos_gauss3`, `chaos_law_shadow4`,
  `chaos_law_comb4`; (iv) `chaos_tail_discrete_levels`, `chaos_tail_classical`,
  `chaos_total_bound`, `chaos_total_tendsto`, `chaos_total_rate`.

The coin-world estimates are Lebesgue-free; the statements about Brownian motion, Gaussian
laws and `L²` of the Loeb measure are shadow results.
-/


set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

noncomputable section

namespace QE.Chaos

open Finset

/-! ## Common: uniform averages on finite product spaces (shared by all parts) -/

/-- Uniform average of a real function on a finite type. -/
def avg {β : Type*} [Fintype β] (f : β → ℝ) : ℝ := (∑ b, f b) / Fintype.card β

section Avg

variable {β γ : Type*} [Fintype β] [Fintype γ]

theorem avg_add (f g : β → ℝ) : avg (fun b => f b + g b) = avg f + avg g := by
  unfold avg; rw [sum_add_distrib, add_div]

theorem avg_sub (f g : β → ℝ) : avg (fun b => f b - g b) = avg f - avg g := by
  unfold avg; rw [sum_sub_distrib, sub_div]

theorem avg_const_mul (c : ℝ) (f : β → ℝ) : avg (fun b => c * f b) = c * avg f := by
  unfold avg; rw [← mul_sum, mul_div_assoc]

theorem avg_mul_const (c : ℝ) (f : β → ℝ) : avg (fun b => f b * c) = avg f * c := by
  unfold avg; rw [← sum_mul, div_mul_eq_mul_div]

theorem avg_neg (f : β → ℝ) : avg (fun b => -f b) = -avg f := by
  unfold avg; rw [sum_neg_distrib, neg_div]

theorem avg_sum {ι : Type*} (s : Finset ι) (f : ι → β → ℝ) :
    avg (fun b => ∑ i ∈ s, f i b) = ∑ i ∈ s, avg (f i) := by
  unfold avg; rw [sum_comm, sum_div]

theorem avg_const [Nonempty β] (c : ℝ) : avg (fun _ : β => c) = c := by
  unfold avg
  rw [sum_const, card_univ, nsmul_eq_mul]
  have : (Fintype.card β : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  field_simp

theorem avg_mono {f g : β → ℝ} (h : ∀ b, f b ≤ g b) : avg f ≤ avg g := by
  unfold avg
  exact div_le_div_of_nonneg_right (sum_le_sum fun b _ => h b) (Nat.cast_nonneg _)

theorem avg_nonneg {f : β → ℝ} (h : ∀ b, 0 ≤ f b) : 0 ≤ avg f := by
  unfold avg; exact div_nonneg (sum_nonneg fun b _ => h b) (Nat.cast_nonneg _)

theorem abs_avg_le (f : β → ℝ) : |avg f| ≤ avg (fun b => |f b|) := by
  unfold avg
  rw [abs_div, Nat.abs_cast]
  exact div_le_div_of_nonneg_right (abs_sum_le_sum_abs _ _) (Nat.cast_nonneg _)

theorem avg_le_of_le [Nonempty β] {f : β → ℝ} {c : ℝ} (h : ∀ b, f b ≤ c) : avg f ≤ c := by
  calc avg f ≤ avg (fun _ : β => c) := avg_mono h
    _ = c := avg_const c

theorem abs_avg_le_of_le [Nonempty β] {f : β → ℝ} {c : ℝ} (h : ∀ b, |f b| ≤ c) : |avg f| ≤ c :=
  (abs_avg_le f).trans (avg_le_of_le h)

theorem avg_comp_equiv (e : β ≃ γ) (f : γ → ℝ) : avg (fun b => f (e b)) = avg f := by
  unfold avg
  rw [Fintype.card_congr e, Equiv.sum_comp e f]

/-- The uniform average on the coin space is the Walsh expectation. -/
theorem avg_eq_E {n : ℕ} (f : (Fin n → Bool) → ℝ) : avg f = QE.OpenSto.Walsh.E f := by
  unfold avg QE.OpenSto.Walsh.E
  simp [Fintype.card_fun, Fintype.card_bool]

end Avg

section Product

variable {ι β : Type*} [Fintype ι] [DecidableEq ι] [Fintype β]

/-- Re-randomising one coordinate does not change the average. -/
theorem avg_update (j : ι) (F : (ι → β) → ℝ) :
    avg F = avg (fun ω => avg (fun b => F (Function.update ω j b))) := by
  classical
  unfold avg
  rw [← sum_div]
  congr 1
  rcases isEmpty_or_nonempty β with hβ | hβ
  · have : IsEmpty (ι → β) := by
      rw [isEmpty_fun]; exact ⟨⟨j⟩, hβ⟩
    simp
  have hc : (Fintype.card β : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  rw [eq_div_iff hc]
  let e := Equiv.piSplitAt j (fun _ : ι => β)
  have hupd : ∀ (a b : β) (r : {i // i ≠ j} → β),
      Function.update (e.symm (a, r)) j b = e.symm (b, r) := by
    intro a b r
    funext i
    by_cases h : i = j
    · subst h; simp [e, Equiv.piSplitAt]
    · simp [e, Equiv.piSplitAt, Function.update_of_ne h, h]
  rw [← Equiv.sum_comp e.symm, ← Equiv.sum_comp e.symm]
  rw [Fintype.sum_prod_type, Fintype.sum_prod_type]
  simp_rw [hupd]
  rw [sum_const, card_univ, nsmul_eq_mul, mul_comm, sum_comm]

/-- The average of a product of functions of distinct coordinates is the product
of the averages (independence of coordinates). -/
theorem avg_prod (f : ι → β → ℝ) :
    avg (fun ω : ι → β => ∏ i, f i (ω i)) = ∏ i, avg (f i) := by
  unfold avg
  rw [← Fintype.prod_sum, Fintype.card_fun, Nat.cast_pow, prod_div_distrib, prod_const,
    card_univ]

/-- **Marginals.** If every fibre of `φ : β → γ` has the same size, then averaging a
function of `φ ∘ ω` over `ω : ι → β` is averaging over `ι → γ`. -/
theorem avg_comp_fibre {γ : Type*} [Fintype γ] [DecidableEq γ] (φ : β → γ) {k : ℕ} (hk0 : 0 < k)
    (hk : ∀ c, (univ.filter (fun b => φ b = c)).card = k) (f : (ι → γ) → ℝ) :
    avg (fun ω : ι → β => f (fun i => φ (ω i))) = avg f := by
  classical
  unfold avg
  have hβ : Fintype.card β = k * Fintype.card γ := by
    rw [← card_univ, ← card_univ (α := γ), card_eq_sum_card_fiberwise (f := φ) (t := univ)
      (fun _ _ => mem_univ _)]
    simp_rw [hk]; rw [sum_const, card_univ, smul_eq_mul, mul_comm]
  have hfib : ∀ η : ι → γ, (univ.filter (fun ω : ι → β => (fun i => φ (ω i)) = η)).card =
      k ^ Fintype.card ι := by
    intro η
    have : univ.filter (fun ω : ι → β => (fun i => φ (ω i)) = η) =
        Fintype.piFinset (fun i => univ.filter (fun b => φ b = η i)) := by
      ext ω; simp [Fintype.mem_piFinset, funext_iff]
    rw [this, Fintype.card_piFinset]; simp_rw [hk]; rw [prod_const, card_univ]
  have hsum : ∑ ω : ι → β, f (fun i => φ (ω i)) =
      (k : ℝ) ^ Fintype.card ι * ∑ η, f η := by
    rw [← sum_fiberwise (s := univ) (g := fun ω : ι → β => fun i => φ (ω i))]
    rw [mul_sum]; apply sum_congr rfl; intro η _
    rw [sum_congr rfl (fun ω hω => by rw [(mem_filter.mp hω).2]), sum_const, hfib,
      nsmul_eq_mul]; push_cast; ring
  rw [hsum, Fintype.card_fun, Fintype.card_fun, hβ]
  push_cast
  rw [mul_pow]
  have : ((k : ℝ)) ^ Fintype.card ι ≠ 0 := pow_ne_zero _ (by exact_mod_cast hk0.ne')
  field_simp

end Product

section Blocks

/-- Blocks of coins: `Fin n → Fin q → Bool ≃ Fin (n*q) → Bool`, coin `r` of block `j`
being the fine coin `q j + r`. -/
def unblock (n q : ℕ) : (Fin n → Fin q → Bool) ≃ (Fin (n * q) → Bool) :=
  (Equiv.curry (Fin n) (Fin q) Bool).symm.trans (Equiv.arrowCongr finProdFinEquiv (Equiv.refl Bool))

theorem unblock_apply (n q : ℕ) (ω : Fin n → Fin q → Bool) (j : Fin n) (r : Fin q) :
    unblock n q ω (finProdFinEquiv (j, r)) = ω j r := by
  simp [unblock, Equiv.arrowCongr_apply]

theorem finProdFinEquiv_val {n q : ℕ} (j : Fin n) (r : Fin q) :
    ((finProdFinEquiv (j, r) : Fin (n * q)) : ℕ) = r + q * j := rfl

/-- The coin expectation on `n q` coins is the block average. -/
theorem E_eq_avg_unblock (n q : ℕ) (f : (Fin (n * q) → Bool) → ℝ) :
    QE.OpenSto.Walsh.E f = avg (fun ω => f (unblock n q ω)) := by
  rw [avg_comp_equiv, avg_eq_E]

/-- The first coin of each block is a uniform coin on `Fin n → Bool`. -/
theorem avg_first_coin (n q : ℕ) (hq : 0 < q) (f : (Fin n → Bool) → ℝ) :
    avg (fun ω : Fin n → Fin q → Bool => f (fun j => ω j ⟨0, hq⟩)) = QE.OpenSto.Walsh.E f := by
  classical
  rw [← avg_eq_E]
  refine avg_comp_fibre (fun b : Fin q → Bool => b ⟨0, hq⟩) (k := 2 ^ (q - 1)) (by positivity) ?_ f
  intro c
  -- the fibre `{b | b 0 = c}` is in bijection with `Fin (q-1) → Bool`
  obtain ⟨q', rfl⟩ : ∃ q', q = q' + 1 := ⟨q - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  have : (univ.filter (fun b : Fin (q' + 1) → Bool => b ⟨0, hq⟩ = c)) =
      (univ : Finset (Fin q' → Bool)).map ⟨fun r => Fin.cons c r, fun x y h => by
        simpa using congrArg Fin.tail h⟩ := by
    ext b
    simp only [mem_filter, mem_univ, true_and, mem_map, Function.Embedding.coeFn_mk]
    constructor
    · intro h; exact ⟨Fin.tail b, by rw [← h]; exact Fin.cons_self_tail b⟩
    · rintro ⟨r, rfl⟩; rfl
  rw [this, card_map, card_univ, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]

end Blocks

end QE.Chaos

/-! # Part A. Calculus of directional derivatives and the coin-world kernel comparison -/


namespace QE.Chaos.Calc

open Finset

/-! ## Part A.1: directional derivatives and central differences -/

section Calculus

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Iterated directional derivative `∂_{w₁} ⋯ ∂_{w_k} F` (outermost first). -/
def dirD : List E → (E → ℝ) → E → ℝ
  | [], F => F
  | w :: ws, F => fun x => fderiv ℝ (dirD ws F) x w

@[simp] theorem dirD_nil (F : E → ℝ) : dirD [] F = F := rfl

theorem dirD_cons (w : E) (ws : List E) (F : E → ℝ) :
    dirD (w :: ws) F = fun x => fderiv ℝ (dirD ws F) x w := rfl

theorem dirD_append (l₁ l₂ : List E) (F : E → ℝ) : dirD (l₁ ++ l₂) F = dirD l₁ (dirD l₂ F) := by
  induction l₁ with
  | nil => rfl
  | cons w ws ih => simp only [List.cons_append, dirD_cons, ih]

theorem contDiff_dirD {F : E → ℝ} : ∀ (ws : List E) (k : ℕ),
    ContDiff ℝ ((k + ws.length : ℕ) : WithTop ℕ∞) F → ContDiff ℝ k (dirD ws F)
  | [], k, h => by simpa using h
  | w :: ws, k, h => by
    have e : k + (w :: ws).length = (k + 1) + ws.length := by simp; omega
    have h1 : ContDiff ℝ (((k + 1) + ws.length : ℕ) : WithTop ℕ∞) F := by rw [← e]; exact h
    have h2 := contDiff_dirD ws (k + 1) h1
    have h3 : ContDiff ℝ k (fderiv ℝ (dirD ws F)) := h2.fderiv_right (by norm_cast)
    exact h3.clm_apply contDiff_const

theorem contDiff_dirD' {F : E → ℝ} {r : ℕ} (hF : ContDiff ℝ r F) (ws : List E) (k : ℕ)
    (hk : k + ws.length ≤ r) : ContDiff ℝ k (dirD ws F) :=
  contDiff_dirD ws k (hF.of_le (by exact_mod_cast hk))

/-- The vector of a list. -/
def lvec (ws : List E) : Fin ws.length → E := fun i => ws.get i

theorem dirD_eq_iteratedFDeriv {F : E → ℝ} : ∀ (ws : List E), ContDiff ℝ ws.length F →
    ∀ x, dirD ws F x = iteratedFDeriv ℝ ws.length F x (lvec ws)
  | [], _, x => by simp [lvec]
  | w :: ws, hF, x => by
    have hF' : ContDiff ℝ ws.length F := hF.of_le (by norm_cast <;> simp)
    have ih : dirD ws F = fun y => iteratedFDeriv ℝ ws.length F y (lvec ws) :=
      funext (dirD_eq_iteratedFDeriv ws hF')
    have hd : DifferentiableAt ℝ (iteratedFDeriv ℝ ws.length F) x :=
      (hF.differentiable_iteratedFDeriv (by norm_cast <;> simp)) x
    rw [dirD_cons]; simp only
    rw [ih, fderiv_continuousMultilinear_apply_const_apply hd]
    show _ = iteratedFDeriv ℝ (ws.length + 1) F x (lvec (w :: ws))
    rw [iteratedFDeriv_succ_apply_left]
    congr 1

/-- Bounded directional derivatives up to order `r`, in the form used below. -/
def DBnd (h : E → ℝ) (r : ℕ) (N : ℕ → ℝ) : Prop :=
  ContDiff ℝ r h ∧ (∀ k ≤ r, 0 ≤ N k) ∧
    ∀ ws : List E, ws.length ≤ r → ∀ x, |dirD ws h x| ≤ N ws.length * (ws.map (‖·‖)).prod

theorem list_prod_norm (ws : List E) : (ws.map (‖·‖)).prod = ∏ i, ‖lvec ws i‖ := by
  rw [← List.prod_ofFn]
  congr 1
  apply List.ext_get <;> simp [lvec]

theorem dBnd_of_iteratedFDeriv {h : E → ℝ} {r : ℕ} {N : ℕ → ℝ} (hh : ContDiff ℝ r h)
    (hb : ∀ k ≤ r, ∀ x, ‖iteratedFDeriv ℝ k h x‖ ≤ N k) : DBnd h r N := by
  refine ⟨hh, fun k hk => (norm_nonneg _).trans (hb k hk 0), fun ws hws x => ?_⟩
  rw [dirD_eq_iteratedFDeriv ws (hh.of_le (by exact_mod_cast hws)), list_prod_norm]
  calc |iteratedFDeriv ℝ ws.length h x (lvec ws)|
      = ‖iteratedFDeriv ℝ ws.length h x (lvec ws)‖ := (Real.norm_eq_abs _).symm
    _ ≤ ‖iteratedFDeriv ℝ ws.length h x‖ * ∏ i, ‖lvec ws i‖ := ContinuousMultilinearMap.le_opNorm _ _
    _ ≤ N ws.length * ∏ i, ‖lvec ws i‖ :=
        mul_le_mul_of_nonneg_right (hb _ hws x) (prod_nonneg fun _ _ => norm_nonneg _)

theorem fderiv_apply_const_apply {G : E → ℝ} {x : E} (hc : DifferentiableAt ℝ (fderiv ℝ G) x)
    (a b : E) : fderiv ℝ (fun y => fderiv ℝ G y b) x a = fderiv ℝ (fderiv ℝ G) x a b := by
  rw [fderiv_clm_apply hc (differentiableAt_const b)]
  simp

theorem dirD_swap {G : E → ℝ} (hG : ContDiff ℝ 2 G) (a b : E) :
    dirD [a, b] G = dirD [b, a] G := by
  funext x
  have hd : DifferentiableAt ℝ (fderiv ℝ G) x :=
    ((hG.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)) x
  simp only [dirD_cons, dirD_nil]
  rw [fderiv_apply_const_apply hd, fderiv_apply_const_apply hd]
  exact (hG.contDiffAt.isSymmSndFDerivAt (by simp [minSmoothness_of_isRCLikeNormedField])) a b

theorem dirD_perm {g : E → ℝ} {r : ℕ} (hg : ContDiff ℝ r g) {l₁ l₂ : List E}
    (h : l₁.Perm l₂) (hl : l₁.length ≤ r) : dirD l₁ g = dirD l₂ g := by
  induction h with
  | nil => rfl
  | cons x _ ih =>
    rw [dirD_cons, dirD_cons, ih (by simp at hl; omega)]
  | swap x y l =>
    have h2 : ContDiff ℝ 2 (dirD l g) := contDiff_dirD' hg l 2 (by simp at hl; omega)
    have := dirD_swap h2 y x
    rw [show y :: x :: l = [y, x] ++ l from rfl, show x :: y :: l = [x, y] ++ l from rfl,
      dirD_append, dirD_append, this]
  | trans h₁ _ ih₁ ih₂ => rw [ih₁ hl, ih₂ (h₁.length_eq ▸ hl)]

theorem dBnd_dirD {g : E → ℝ} {m r : ℕ} {N : ℕ → ℝ} (hg : DBnd g (m + r) N) {vs : List E}
    (hvs : vs.length = m) (hv : ∀ v ∈ vs, ‖v‖ ≤ 1) : DBnd (dirD vs g) r (fun k => N (m + k)) := by
  obtain ⟨hc, hN, hb⟩ := hg
  refine ⟨contDiff_dirD' hc vs r (by omega), fun k hk => hN _ (by omega), fun ws hws x => ?_⟩
  rw [← dirD_append]
  have := hb (ws ++ vs) (by simp <;> omega) x
  rw [List.map_append, List.prod_append, List.length_append, hvs, Nat.add_comm] at this
  refine this.trans ?_
  have h1 : (vs.map (‖·‖)).prod ≤ 1 := by
    rw [list_prod_norm]
    exact Finset.prod_le_one₀ (fun _ _ => norm_nonneg _) (fun i _ => hv _ (List.get_mem _ _))
  have h0 : 0 ≤ (ws.map (‖·‖)).prod := by
    rw [list_prod_norm]; exact prod_nonneg fun _ _ => norm_nonneg _
  have hN' : 0 ≤ N (m + ws.length) := hN _ (by omega)
  calc N (m + ws.length) * ((ws.map (‖·‖)).prod * (vs.map (‖·‖)).prod)
      ≤ N (m + ws.length) * ((ws.map (‖·‖)).prod * 1) := by gcongr
    _ = _ := by ring

theorem prod_norm_le_one {ws : List E} (hw : ∀ w ∈ ws, ‖w‖ ≤ 1) : (ws.map (‖·‖)).prod ≤ 1 := by
  rw [list_prod_norm]
  exact Finset.prod_le_one₀ (fun _ _ => norm_nonneg _) (fun i _ => hw _ (List.get_mem _ _))

theorem prod_norm_nonneg (ws : List E) : 0 ≤ (ws.map (‖·‖)).prod := by
  rw [list_prod_norm]; exact prod_nonneg fun _ _ => norm_nonneg _

theorem abs_dirD_le_unit {g : E → ℝ} {r : ℕ} {N : ℕ → ℝ} (hg : DBnd g r N) {ws : List E}
    (hws : ws.length ≤ r) (hw : ∀ w ∈ ws, ‖w‖ ≤ 1) (x : E) : |dirD ws g x| ≤ N ws.length := by
  have h := hg.2.2 ws hws x
  have hN := hg.2.1 _ hws
  calc |dirD ws g x| ≤ N ws.length * (ws.map (‖·‖)).prod := h
    _ ≤ N ws.length * 1 := mul_le_mul_of_nonneg_left (prod_norm_le_one hw) hN
    _ = _ := mul_one _

theorem continuous_dirD {g : E → ℝ} {r : ℕ} (hg : ContDiff ℝ r g) {ws : List E}
    (hws : ws.length ≤ r) : Continuous (dirD ws g) :=
  (contDiff_dirD' hg ws 0 (by omega)).continuous

/-! ### The line through `y` in direction `w` -/

theorem hasDerivAt_line {G : E → ℝ} (hG : Differentiable ℝ G) (y w : E) (s : ℝ) :
    HasDerivAt (fun s : ℝ => G (y + s • w)) (fderiv ℝ G (y + s • w) w) s := by
  have h1 : HasDerivAt (fun s : ℝ => y + s • w) w s := by
    simpa using ((hasDerivAt_id s).smul_const w).const_add y
  exact (hG (y + s • w)).hasFDerivAt.comp_hasDerivAt s h1

theorem iteratedDeriv_line {G : E → ℝ} (y w : E) : ∀ k : ℕ, ContDiff ℝ k G →
    iteratedDeriv k (fun s : ℝ => G (y + s • w)) = fun s => dirD (List.replicate k w) G (y + s • w)
  | 0, _ => by simp
  | k + 1, hG => by
    rw [iteratedDeriv_succ, iteratedDeriv_line y w k (hG.of_le (by norm_cast; omega))]
    funext s
    have hd : Differentiable ℝ (dirD (List.replicate k w) G) :=
      (contDiff_dirD' hG _ 1 (by simp <;> omega)).differentiable (by norm_num)
    rw [(hasDerivAt_line hd y w s).deriv, List.replicate_succ, dirD_cons]

/-- Taylor's formula with Lagrange remainder, in the form used here. -/
theorem taylor1D {φ : ℝ → ℝ} {n : ℕ} (hφ : ContDiff ℝ (n + 1) φ) {A : ℝ}
    (hA : ∀ s, |iteratedDeriv (n + 1) φ s| ≤ A) (s : ℝ) :
    |φ s - ∑ k ∈ range (n + 1), iteratedDeriv k φ 0 * s ^ k / k.factorial| ≤
      A * |s| ^ (n + 1) / (n + 1).factorial := by
  rcases eq_or_ne s 0 with rfl | hs
  · rw [sum_eq_single 0]
    · have hA0 : 0 ≤ A := (abs_nonneg _).trans (hA 0)
      simp
    · intro k _ hk; simp [zero_pow hk]
    · simp
  obtain ⟨x', -, hx'⟩ := taylor_mean_remainder_lagrange_iteratedDeriv (x₀ := 0) (x := s)
    (Ne.symm hs) hφ.contDiffOn
  rw [taylor_within_apply] at hx'
  have hu : UniqueDiffOn ℝ (Set.uIcc 0 s) := uniqueDiffOn_uIcc (Ne.symm hs)
  have heq : ∀ k ∈ range (n + 1), ((k.factorial : ℝ)⁻¹ * (s - 0) ^ k) •
      iteratedDerivWithin k φ (Set.uIcc 0 s) 0 = iteratedDeriv k φ 0 * s ^ k / k.factorial := by
    intro k hk
    rw [iteratedDerivWithin_eq_iteratedDeriv hu
      ((hφ.of_le (by norm_cast; simp at hk; omega)).contDiffAt) Set.left_mem_uIcc]
    simp only [sub_zero, smul_eq_mul]; ring
  rw [sum_congr rfl heq, sub_zero] at hx'
  rw [hx', abs_div, abs_mul, abs_pow, Nat.abs_cast]
  gcongr
  exact hA x'

theorem line_taylor {h : E → ℝ} {n : ℕ} {N : ℕ → ℝ} (hh : DBnd h (n + 1) N) (y w : E) (s : ℝ) :
    |h (y + s • w) - ∑ k ∈ range (n + 1), dirD (List.replicate k w) h y * s ^ k / k.factorial| ≤
      N (n + 1) * ‖w‖ ^ (n + 1) * |s| ^ (n + 1) / (n + 1).factorial := by
  have hc : ContDiff ℝ (n + 1) (fun s : ℝ => h (y + s • w)) :=
    hh.1.comp (contDiff_const.add (contDiff_id.smul contDiff_const))
  have hA : ∀ s, |iteratedDeriv (n + 1) (fun s : ℝ => h (y + s • w)) s| ≤ N (n + 1) * ‖w‖ ^ (n + 1) := by
    intro s
    rw [iteratedDeriv_line y w (n + 1) (by exact_mod_cast hh.1)]
    have := hh.2.2 (List.replicate (n + 1) w) (by simp) (y + s • w)
    simpa [List.map_replicate, List.prod_replicate] using this
  have := taylor1D hc hA s
  have e : ∀ k ∈ range (n + 1), iteratedDeriv k (fun s : ℝ => h (y + s • w)) 0 * s ^ k / k.factorial =
      dirD (List.replicate k w) h y * s ^ k / k.factorial := by
    intro k hk
    rw [iteratedDeriv_line y w k (hh.1.of_le (by norm_cast; simp at hk; omega))]
    simp
  rw [sum_congr rfl e] at this
  simpa using this

/-! ### Central differences -/

/-- Central difference `(F(x + c v) - F(x - c v)) / (2c)`. -/
def cd (c : ℝ) (v : E) (F : E → ℝ) : E → ℝ := fun x => (F (x + c • v) - F (x - c • v)) / (2 * c)

/-- Iterated central differences. -/
def cds (c : ℝ) : List E → (E → ℝ) → E → ℝ
  | [], F => F
  | v :: vs, F => cd c v (cds c vs F)

@[simp] theorem cds_nil (c : ℝ) (F : E → ℝ) : cds c [] F = F := rfl

theorem cds_cons (c : ℝ) (v : E) (vs : List E) (F : E → ℝ) :
    cds c (v :: vs) F = cd c v (cds c vs F) := rfl

theorem contDiff_cd {k : WithTop ℕ∞} {F : E → ℝ} (hF : ContDiff ℝ k F) (c : ℝ) (v : E) :
    ContDiff ℝ k (cd c v F) := by
  unfold cd
  exact ((hF.comp (contDiff_id.add contDiff_const)).sub
    (hF.comp (contDiff_id.sub contDiff_const))).div_const _

theorem contDiff_cds {k : WithTop ℕ∞} {F : E → ℝ} (hF : ContDiff ℝ k F) (c : ℝ) :
    ∀ vs : List E, ContDiff ℝ k (cds c vs F)
  | [] => hF
  | v :: vs => contDiff_cd (contDiff_cds hF c vs) c v

theorem fderiv_cd {F : E → ℝ} (hF : Differentiable ℝ F) (c : ℝ) (v x w : E) :
    fderiv ℝ (cd c v F) x w = cd c v (fun y => fderiv ℝ F y w) x := by
  have h1 : HasFDerivAt (fun x => F (x + c • v)) (fderiv ℝ F (x + c • v)) x :=
    (hasFDerivAt_comp_add_right (c • v)).mpr (hF _).hasFDerivAt
  have h2' : HasFDerivAt (fun x => F (x + -(c • v))) (fderiv ℝ F (x + -(c • v))) x :=
    (hasFDerivAt_comp_add_right (-(c • v))).mpr (hF _).hasFDerivAt
  have h2 : HasFDerivAt (fun x => F (x - c • v)) (fderiv ℝ F (x - c • v)) x := by
    simpa only [← sub_eq_add_neg] using h2'
  have h3 : HasFDerivAt (fun x => (2 * c)⁻¹ * (F (x + c • v) - F (x - c • v)))
      ((2 * c)⁻¹ • (fderiv ℝ F (x + c • v) - fderiv ℝ F (x - c • v))) x :=
    (h1.sub h2).const_mul (2 * c)⁻¹
  have e : cd c v F = fun x => (2 * c)⁻¹ * (F (x + c • v) - F (x - c • v)) := by
    funext y; unfold cd; ring
  rw [e, h3.fderiv]
  simp only [smul_apply, sub_apply, smul_eq_mul, cd]
  ring

theorem dirD_cd {F : E → ℝ} (c : ℝ) (v : E) : ∀ ws : List E, ContDiff ℝ ws.length F →
    dirD ws (cd c v F) = cd c v (dirD ws F)
  | [], _ => rfl
  | w :: ws, hF => by
    have hF' : ContDiff ℝ ws.length F := hF.of_le (by norm_cast <;> simp)
    rw [dirD_cons, dirD_cd c v ws hF']
    funext x
    have hd : Differentiable ℝ (dirD ws F) :=
      (contDiff_dirD' hF ws 1 (by simp <;> omega)).differentiable (by norm_num)
    rw [fderiv_cd hd]
    rfl

theorem dirD_cds {F : E → ℝ} (c : ℝ) (ws : List E) (hF : ContDiff ℝ ws.length F) :
    ∀ vs : List E, dirD ws (cds c vs F) = cds c vs (dirD ws F)
  | [] => rfl
  | v :: vs => by
    rw [cds_cons, dirD_cd c v ws (contDiff_cds hF c vs), dirD_cds c ws hF vs, cds_cons]

theorem cd_mvt {F : E → ℝ} (hF : Differentiable ℝ F) {c : ℝ} (hc : 0 < c) (v x : E) :
    ∃ ξ : ℝ, cd c v F x = fderiv ℝ F (x + ξ • v) v := by
  have hφ : ∀ s, HasDerivAt (fun s : ℝ => F (x + s • v)) (fderiv ℝ F (x + s • v) v) s :=
    hasDerivAt_line hF x v
  obtain ⟨ξ, -, hξ⟩ := exists_hasDerivAt_eq_slope (fun s : ℝ => F (x + s • v))
    (fun s => fderiv ℝ F (x + s • v) v) (show -c < c by linarith)
    (fun s _ => (hφ s).continuousAt.continuousWithinAt) (fun s _ => hφ s)
  refine ⟨ξ, ?_⟩
  rw [hξ]
  unfold cd
  have e : x + (-c) • v = x - c • v := by rw [neg_smul, sub_eq_add_neg]
  rw [e]; congr 1; ring

theorem abs_cd_le {F : E → ℝ} (hF : Differentiable ℝ F) {c : ℝ} (hc : 0 < c) (v : E) {A : ℝ}
    (hA : ∀ y, |fderiv ℝ F y v| ≤ A) (x : E) : |cd c v F x| ≤ A := by
  obtain ⟨ξ, hξ⟩ := cd_mvt hF hc v x
  rw [hξ]; exact hA _

theorem cds_shift {c : ℝ} (hc : 0 < c) : ∀ (vs : List E) {F : E → ℝ}, ContDiff ℝ vs.length F →
    ∀ x, ∃ z, cds c vs F x = dirD vs F z
  | [], _, _, x => ⟨x, rfl⟩
  | v :: vs, F, hF, x => by
    have hF1 : ContDiff ℝ 1 F := hF.of_le (by norm_cast <;> simp)
    have hd : Differentiable ℝ (cds c vs F) :=
      (contDiff_cds hF1 c vs).differentiable (by norm_num)
    obtain ⟨ξ, hξ⟩ := cd_mvt hd hc v x
    have hG : ContDiff ℝ vs.length (dirD [v] F) := contDiff_dirD' hF [v] _ (by simp <;> omega)
    obtain ⟨z, hz⟩ := cds_shift hc vs hG (x + ξ • v)
    refine ⟨z, ?_⟩
    rw [cds_cons, hξ]
    have e1 : fderiv ℝ (cds c vs F) (x + ξ • v) v = dirD [v] (cds c vs F) (x + ξ • v) := rfl
    rw [e1, dirD_cds c [v] (by simpa using hF1), hz, ← dirD_append]
    rw [dirD_perm hF (List.perm_append_singleton v vs) (by simp)]

theorem abs_cds_le {g : E → ℝ} {m : ℕ} {N : ℕ → ℝ} (hg : DBnd g m N) {vs : List E}
    (hvs : vs.length = m) (hv : ∀ v ∈ vs, ‖v‖ ≤ 1) {c : ℝ} (hc : 0 < c) (x : E) :
    |cds c vs g x| ≤ N m := by
  obtain ⟨z, hz⟩ := cds_shift hc vs (hvs ▸ hg.1) x
  rw [hz, ← hvs]; exact abs_dirD_le_unit hg (by omega) hv z

theorem abs_cd_sub_fderiv_le {F : E → ℝ} (hF : ContDiff ℝ 3 F) {c : ℝ} (hc : 0 < c) (v : E)
    {A : ℝ} (hA : ∀ y, |dirD [v, v, v] F y| ≤ A) (x : E) :
    |cd c v F x - fderiv ℝ F x v| ≤ c ^ 2 / 6 * A := by
  have hφ : ContDiff ℝ (2 + 1) (fun s : ℝ => F (x + s • v)) :=
    hF.comp (contDiff_const.add (contDiff_id.smul contDiff_const))
  have hA' : ∀ s, |iteratedDeriv (2 + 1) (fun s : ℝ => F (x + s • v)) s| ≤ A := by
    intro s; rw [iteratedDeriv_line x v 3 hF]; exact hA _
  have e : ∀ k ∈ range (2 + 1), ∀ s : ℝ, iteratedDeriv k (fun s : ℝ => F (x + s • v)) 0 * s ^ k /
      k.factorial = dirD (List.replicate k v) F x * s ^ k / k.factorial := by
    intro k hk s
    rw [iteratedDeriv_line x v k (hF.of_le (by norm_cast; simp at hk; omega))]
    simp
  have h1 := taylor1D hφ hA' c
  have h2 := taylor1D hφ hA' (-c)
  rw [sum_congr rfl (fun k hk => e k hk c)] at h1
  rw [sum_congr rfl (fun k hk => e k hk (-c))] at h2
  simp only [sum_range_succ, sum_range_zero, List.replicate, dirD_nil, dirD_cons] at h1 h2
  have e2 : x + (-c) • v = x - c • v := by rw [neg_smul, sub_eq_add_neg]
  rw [e2] at h2
  have hcabs : |c| = c := abs_of_pos hc
  have hcabs' : |-c| = c := by rw [abs_neg, hcabs]
  rw [hcabs] at h1; rw [hcabs'] at h2
  unfold cd
  set a := F (x + c • v); set b := F (x - c • v)
  set d1 := fderiv ℝ F x v
  set d2 := fderiv ℝ (fun x => fderiv ℝ F x v) x v
  have hc2 : (0 : ℝ) < 2 * c := by linarith
  rw [div_sub' (by positivity), abs_div, abs_of_pos hc2, div_le_iff₀ hc2]
  have key : a - b - 2 * c * d1 = (a - (F x + d1 * c / 1 + d2 * c ^ 2 / 2)) -
      (b - (F x + d1 * (-c) / 1 + d2 * (-c) ^ 2 / 2)) := by ring
  simp only [Nat.factorial, Nat.cast_one, Nat.succ_eq_add_one, zero_add, mul_one, pow_zero,
    div_one, pow_one] at h1 h2
  rw [key]
  calc |(a - (F x + d1 * c / 1 + d2 * c ^ 2 / 2)) - (b - (F x + d1 * (-c) / 1 + d2 * (-c) ^ 2 / 2))|
      ≤ |a - (F x + d1 * c / 1 + d2 * c ^ 2 / 2)| + |b - (F x + d1 * (-c) / 1 + d2 * (-c) ^ 2 / 2)| :=
        abs_sub _ _
    _ ≤ A * c ^ 3 / 6 + A * c ^ 3 / 6 := by
        gcongr
        · convert h1 using 2; norm_num
        · convert h2 using 2; norm_num
    _ = c ^ 2 / 6 * A * (2 * c) := by ring

theorem DBnd.of_eq {g : E → ℝ} {r r' : ℕ} {N : ℕ → ℝ} (h : DBnd g r N) (e : r = r') : DBnd g r' N :=
  e ▸ h

/-- **Central differences versus derivatives**:
`|δ_{v₁} ⋯ δ_{v_m} g - ∂_{v₁} ⋯ ∂_{v_m} g| ≤ m c² N_{m+2} / 6` for unit directions. -/
theorem abs_cds_sub_dirD_le {c : ℝ} (hc : 0 < c) : ∀ (vs : List E) {g : E → ℝ} {N : ℕ → ℝ},
    DBnd g (vs.length + 2) N → (∀ v ∈ vs, ‖v‖ ≤ 1) → ∀ x,
    |cds c vs g x - dirD vs g x| ≤ vs.length * c ^ 2 / 6 * N (vs.length + 2)
  | [], g, N, hg, _, x => by simp
  | v :: vs, g, N, hg, hv, x => by
    have hvs : ∀ w ∈ vs, ‖w‖ ≤ 1 := fun w hw => hv w (List.mem_cons_of_mem v hw)
    have hv1 : ‖v‖ ≤ 1 := hv v List.mem_cons_self
    have hlen : (v :: vs).length = vs.length + 1 := rfl
    have hgC : ContDiff ℝ (vs.length + 3 : ℕ) g := by
      have := hg.1; rw [hlen] at this; exact this
    -- the derivative of g in direction v
    have hg' : DBnd (dirD [v] g) (vs.length + 2) (fun k => N (1 + k)) :=
      dBnd_dirD (m := 1) (hg.of_eq (by simp <;> omega)) (by simp) (by simpa using hv1)
    have ih := abs_cds_sub_dirD_le hc vs hg' hvs
    set H : E → ℝ := fun y => cds c vs g y - dirD vs g y with hH
    have hdc : Differentiable ℝ (cds c vs g) :=
      (contDiff_cds (hgC.of_le (by norm_cast; omega) : ContDiff ℝ 1 g) c vs).differentiable
        (by norm_num)
    have hdd : Differentiable ℝ (dirD vs g) :=
      (contDiff_dirD' hgC vs 1 (by omega)).differentiable (by norm_num)
    have hHd : Differentiable ℝ H := hdc.sub hdd
    have split : cds c (v :: vs) g x - dirD (v :: vs) g x =
        cd c v H x + (cd c v (dirD vs g) x - fderiv ℝ (dirD vs g) x v) := by
      rw [cds_cons, dirD_cons]; simp only [cd, hH]; ring
    rw [split]
    -- first term: by the mean value theorem and the induction hypothesis
    have hA : |cd c v H x| ≤ vs.length * c ^ 2 / 6 * N (1 + (vs.length + 2)) := by
      apply abs_cd_le hHd hc v
      intro y
      have e1 : fderiv ℝ H y v = cds c vs (dirD [v] g) y - dirD vs (dirD [v] g) y := by
        rw [hH, fderiv_fun_sub (hdc y) (hdd y)]
        simp only [ContinuousLinearMap.sub_apply]
        have a1 : fderiv ℝ (cds c vs g) y v = dirD [v] (cds c vs g) y := rfl
        have a2 : fderiv ℝ (dirD vs g) y v = dirD (v :: vs) g y := rfl
        rw [a1, a2, dirD_cds c [v] (by simpa using (hgC.of_le (by norm_cast; omega) :
          ContDiff ℝ 1 g)), ← dirD_append,
          dirD_perm hgC (List.perm_append_singleton v vs).symm (by simp)]
      rw [e1]; exact ih y
    -- second term: third-order Taylor along `v`
    have hB : |cd c v (dirD vs g) x - fderiv ℝ (dirD vs g) x v| ≤
        c ^ 2 / 6 * N (vs.length + 3) := by
      apply abs_cd_sub_fderiv_le (contDiff_dirD' hgC vs 3 (by omega)) hc v
      intro y
      rw [← dirD_append]
      have := abs_dirD_le_unit hg (ws := [v, v, v] ++ vs) (by simp <;> omega) (by
        intro w hw
        simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hw
        rcases hw with (rfl | rfl | rfl) | hw
        · exact hv1
        · exact hv1
        · exact hv1
        · exact hvs w hw) y
      simpa [Nat.add_comm, Nat.add_left_comm] using this
    have e2 : 1 + (vs.length + 2) = (v :: vs).length + 2 := by simp; omega
    have e3 : vs.length + 3 = (v :: vs).length + 2 := by simp
    rw [e2] at hA; rw [e3] at hB
    calc |cd c v H x + (cd c v (dirD vs g) x - fderiv ℝ (dirD vs g) x v)|
        ≤ |cd c v H x| + |cd c v (dirD vs g) x - fderiv ℝ (dirD vs g) x v| := abs_add_le _ _
      _ ≤ vs.length * c ^ 2 / 6 * N ((v :: vs).length + 2) + c ^ 2 / 6 * N ((v :: vs).length + 2) :=
          add_le_add hA hB
      _ = (v :: vs).length * c ^ 2 / 6 * N ((v :: vs).length + 2) := by
          rw [hlen]; push_cast; ring

end Calculus

end QE.Chaos.Calc

namespace QE.Chaos.Calc

open Finset QE.OpenSto.Walsh

/-! ## Part A.2: algebra of central differences, and the walk -/

section CdAlg

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem cd_comm (c : ℝ) (v w : E) (F : E → ℝ) : cd c v (cd c w F) = cd c w (cd c v F) := by
  funext x
  simp only [cd]
  have e1 : x + c • v + c • w = x + c • w + c • v := add_right_comm _ _ _
  have e2 : x + c • v - c • w = x - c • w + c • v := add_sub_right_comm _ _ _
  have e3 : x - c • v + c • w = x + c • w - c • v := sub_add_eq_add_sub _ _ _
  have e4 : x - c • v - c • w = x - c • w - c • v := sub_right_comm _ _ _
  rw [e1, e2, e3, e4]; ring

theorem cds_perm (c : ℝ) (F : E → ℝ) {l₁ l₂ : List E} (h : l₁.Perm l₂) :
    cds c l₁ F = cds c l₂ F := by
  induction h with
  | nil => rfl
  | cons x _ ih => rw [cds_cons, cds_cons, ih]
  | swap x y l => rw [cds_cons, cds_cons, cds_cons, cds_cons, cd_comm]
  | trans _ _ ih₁ ih₂ => rw [ih₁, ih₂]

theorem cds_append_singleton (c : ℝ) (w : E) (F : E → ℝ) :
    ∀ vs : List E, cds c (vs ++ [w]) F = cds c vs (cd c w F)
  | [] => rfl
  | v :: vs => by rw [List.cons_append, cds_cons, cds_append_singleton c w F vs, cds_cons]

theorem cd_const_mul (c a : ℝ) (v : E) (H : E → ℝ) :
    cd c v (fun y => a * H y) = fun y => a * cd c v H y := by
  funext y; simp only [cd]; ring

theorem cds_const_mul (c a : ℝ) (H : E → ℝ) :
    ∀ vs : List E, cds c vs (fun y => a * H y) = fun y => a * cds c vs H y
  | [] => rfl
  | v :: vs => by rw [cds_cons, cds_const_mul c a H vs, cd_const_mul, cds_cons]

end CdAlg

section Walk

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] {n : ℕ}

/-- The walk `∑_{j ∉ S} c ξ_j v_j` with the coins in `S` removed. -/
def walkVec (c : ℝ) (v : Fin n → V) (S : Finset (Fin n)) (ω : Fin n → Bool) : V :=
  ∑ j ∈ univ \ S, (c * (sgn (ω j) : ℝ)) • v j

theorem walkVec_insert (c : ℝ) (v : Fin n → V) {S : Finset (Fin n)} {i : Fin n} (hi : i ∉ S)
    (ω : Fin n → Bool) :
    walkVec c v S ω = walkVec c v (insert i S) ω + (c * (sgn (ω i) : ℝ)) • v i := by
  unfold walkVec
  have e : univ \ S = insert i (univ \ insert i S) := by
    ext j; by_cases h : j = i <;> simp [h, hi]
  rw [e, sum_insert (by simp), add_comm]

theorem walkVec_update (c : ℝ) (v : Fin n → V) (S : Finset (Fin n)) (i : Fin n) (b : Bool)
    (ω : Fin n → Bool) : walkVec c v (insert i S) (Function.update ω i b) = walkVec c v (insert i S) ω := by
  unfold walkVec
  apply sum_congr rfl; intro j hj
  have : j ≠ i := by intro h; subst h; simp at hj
  rw [Function.update_of_ne this]

theorem D_walk (c : ℝ) (hc : c ≠ 0) (v : Fin n → V) (H : V → ℝ) {S : Finset (Fin n)} {i : Fin n}
    (hi : i ∉ S) :
    D i (fun ω => H (walkVec c v S ω)) = fun ω => c * cd c (v i) H (walkVec c v (insert i S) ω) := by
  funext ω
  unfold D cd
  dsimp only
  rw [walkVec_insert c v hi, walkVec_insert c v hi, walkVec_update, walkVec_update]
  simp only [Function.update_self, sgn_true, sgn_false, mul_one, mul_neg, neg_smul,
    ← sub_eq_add_neg]
  field_simp

theorem DS_walk (c : ℝ) (hc : c ≠ 0) (v : Fin n → V) :
    ∀ (l : List (Fin n)) (S : Finset (Fin n)) (H : V → ℝ), l.Nodup → (∀ a ∈ l, a ∉ S) →
    DS l (fun ω => H (walkVec c v S ω)) =
      fun ω => c ^ l.length * cds c (l.map v) H (walkVec c v (S ∪ l.toFinset) ω)
  | [], S, H, _, _ => by funext ω; simp [DS]
  | a :: l, S, H, hl, hS => by
    have ha : a ∉ S := hS a List.mem_cons_self
    have hl' : l.Nodup := (List.nodup_cons.mp hl).2
    have hal : a ∉ l := (List.nodup_cons.mp hl).1
    have hS' : ∀ b ∈ l, b ∉ insert a S := by
      intro b hb hb'
      rcases mem_insert.mp hb' with rfl | h
      · exact hal hb
      · exact hS b (List.mem_cons_of_mem a hb) h
    show DS l (D a (fun ω => H (walkVec c v S ω))) = _
    rw [D_walk c hc v H ha, DS_walk c hc v l (insert a S) (fun y => c * cd c (v a) H y) hl' hS']
    funext ω
    rw [cds_const_mul, ← cds_append_singleton,
      cds_perm c H (List.perm_append_singleton (v a) (l.map v))]
    have e : insert a S ∪ l.toFinset = S ∪ (a :: l).toFinset := by
      rw [List.toFinset_cons, insert_union, union_insert]
    rw [e, List.map_cons, List.length_cons, pow_succ]; ring

/-- **Discrete Stroock formula for a function of the walk**:
`ĉ_S(g(W)) = c^m E[δ_{v_S} g(W^{(S)})]`. -/
theorem coeff_walk (c : ℝ) (hc : c ≠ 0) (v : Fin n → V) (g : V → ℝ) (l : List (Fin n))
    (hl : l.Nodup) :
    coeff (fun ω => g (walkVec c v ∅ ω)) l.toFinset =
      c ^ l.length * E (fun ω => cds c (l.map v) g (walkVec c v l.toFinset ω)) := by
  rw [stroock l hl, DS_walk c hc v l ∅ g hl (by simp), E_smul]
  simp

end Walk

end QE.Chaos.Calc

namespace QE.Chaos.Calc

open Finset QE.OpenSto.Walsh

/-! ## Part A.3: Lindeberg replacement and the second-order step -/

section Lindeberg

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem DBnd.mono {h : E → ℝ} {r r' : ℕ} {N : ℕ → ℝ} (hh : DBnd h r N) (hr : r' ≤ r) :
    DBnd h r' N :=
  ⟨hh.1.of_le (by exact_mod_cast hr), fun k hk => hh.2.1 k (hk.trans hr),
    fun ws hws x => hh.2.2 ws (hws.trans hr) x⟩

theorem avg_line_taylor {h : E → ℝ} {M : ℕ → ℝ} (hh : DBnd h 4 M) (y a : E) (ha : ‖a‖ ≤ 1)
    {β : Type*} [Fintype β] [Nonempty β] (f : β → ℝ) :
    |avg (fun b => h (y + f b • a)) - ∑ k ∈ range 4,
        dirD (List.replicate k a) h y / k.factorial * avg (fun b => f b ^ k)| ≤
      M 4 / 24 * avg (fun b => f b ^ 4) := by
  have hM : 0 ≤ M 4 := hh.2.1 4 le_rfl
  have hR : ∀ s, |h (y + s • a) - ∑ k ∈ range 4, dirD (List.replicate k a) h y * s ^ k /
      k.factorial| ≤ M 4 / 24 * s ^ 4 := by
    intro s
    have := line_taylor (n := 3) hh y a s
    have ha4 : ‖a‖ ^ 4 ≤ 1 := pow_le_one₀ (norm_nonneg _) ha
    have h4 : |s| ^ 4 = s ^ 4 := by rw [pow_abs, abs_of_nonneg (by positivity)]
    calc _ ≤ M (3 + 1) * ‖a‖ ^ (3 + 1) * |s| ^ (3 + 1) / (3 + 1).factorial := this
      _ ≤ M 4 * 1 * s ^ 4 / 24 := by
          norm_num [Nat.factorial, h4]
          gcongr
          exact mul_le_of_le_one_right hM ha4
      _ = M 4 / 24 * s ^ 4 := by ring
  have e : ∑ k ∈ range 4, dirD (List.replicate k a) h y / k.factorial * avg (fun b => f b ^ k) =
      avg (fun b => ∑ k ∈ range 4, dirD (List.replicate k a) h y * f b ^ k / k.factorial) := by
    rw [avg_sum]
    apply sum_congr rfl; intro k _
    rw [← avg_const_mul]; congr 1; funext b; ring
  rw [e, ← avg_sub]
  refine (abs_avg_le _).trans ?_
  rw [← avg_const_mul]
  exact avg_mono fun b => hR (f b)

/-- **One Lindeberg step**: two scalar laws with the same moments of order `≤ 3`,
inserted along a unit direction, change the average of `h` by at most
`N₄ (E X⁴ + E Z⁴) / 24`. -/
theorem avg_moment_match {h : E → ℝ} {M : ℕ → ℝ} (hh : DBnd h 4 M) (y a : E) (ha : ‖a‖ ≤ 1)
    {β₁ β₂ : Type*} [Fintype β₁] [Nonempty β₁] [Fintype β₂] [Nonempty β₂]
    (f₁ : β₁ → ℝ) (f₂ : β₂ → ℝ)
    (hm : ∀ k, 1 ≤ k → k ≤ 3 → avg (fun b => f₁ b ^ k) = avg (fun b => f₂ b ^ k)) :
    |avg (fun b => h (y + f₁ b • a)) - avg (fun b => h (y + f₂ b • a))| ≤
      M 4 / 24 * (avg (fun b => f₁ b ^ 4) + avg (fun b => f₂ b ^ 4)) := by
  have h1 := avg_line_taylor hh y a ha f₁
  have h2 := avg_line_taylor hh y a ha f₂
  have hPeq : ∑ k ∈ range 4, dirD (List.replicate k a) h y / k.factorial * avg (fun b => f₁ b ^ k) =
      ∑ k ∈ range 4, dirD (List.replicate k a) h y / k.factorial * avg (fun b => f₂ b ^ k) := by
    apply sum_congr rfl; intro k hk
    rcases Nat.eq_zero_or_pos k with rfl | hk0
    · simp [avg_const]
    · rw [hm k hk0 (by simp at hk; omega)]
  rw [hPeq] at h1
  set P := ∑ k ∈ range 4, dirD (List.replicate k a) h y / k.factorial * avg (fun b => f₂ b ^ k)
  have := abs_sub_le (avg (fun b => h (y + f₁ b • a))) P (avg (fun b => h (y + f₂ b • a)))
  rw [abs_sub_comm P] at this
  rw [mul_add]
  linarith

end Lindeberg

end QE.Chaos.Calc

namespace QE.Chaos.Calc

open Finset QE.OpenSto.Walsh

/-! ## Part A.4: block Lindeberg, orthogonality, the second-order step -/

section Blocks2

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- **Lindeberg's replacement over blocks.** -/
theorem lindeberg_blocks {β : Type*} [Fintype β] [Nonempty β] {n : ℕ} {h : V → ℝ}
    {M : ℕ → ℝ} (hh : DBnd h 4 M) (a : Fin n → V) (ha : ∀ j, ‖a j‖ ≤ 1) (X Z : β → ℝ)
    (hm : ∀ k, 1 ≤ k → k ≤ 3 → avg (fun b => X b ^ k) = avg (fun b => Z b ^ k)) :
    |avg (fun ω : Fin n → β => h (∑ j, X (ω j) • a j)) -
      avg (fun ω : Fin n → β => h (∑ j, Z (ω j) • a j))| ≤
      n * (M 4 / 24 * (avg (fun b => X b ^ 4) + avg (fun b => Z b ^ 4))) := by
  classical
  set B := M 4 / 24 * (avg (fun b => X b ^ 4) + avg (fun b => Z b ^ 4))
  let H : ℕ → (Fin n → β) → V := fun k ω =>
    ∑ j : Fin n, (if (j : ℕ) < k then Z (ω j) else X (ω j)) • a j
  have h0 : (fun ω : Fin n → β => h (∑ j, X (ω j) • a j)) = fun ω => h (H 0 ω) := by
    funext ω; simp [H]
  have hn' : (fun ω : Fin n → β => h (∑ j, Z (ω j) • a j)) = fun ω => h (H n ω) := by
    funext ω; simp only [H]; congr 1; apply sum_congr rfl; intro j _; simp [j.isLt]
  rw [h0, hn']
  have step : ∀ k < n, |avg (fun ω => h (H k ω)) - avg (fun ω => h (H (k + 1) ω))| ≤ B := by
    intro k hk
    set j0 : Fin n := ⟨k, hk⟩
    let y : (Fin n → β) → V := fun ω =>
      ∑ j ∈ (univ : Finset (Fin n)).erase j0, (if (j : ℕ) < k then Z (ω j) else X (ω j)) • a j
    have hy : ∀ ω b, y (Function.update ω j0 b) = y ω := by
      intro ω b; simp only [y]
      apply sum_congr rfl; intro j hj
      rw [Function.update_of_ne (ne_of_mem_erase hj)]
    have hHk : ∀ ω, H k ω = y ω + X (ω j0) • a j0 := by
      intro ω; simp only [H, y]
      rw [← add_sum_erase _ _ (mem_univ j0), add_comm]
      simp [j0]
    have hHk1 : ∀ ω, H (k + 1) ω = y ω + Z (ω j0) • a j0 := by
      intro ω; simp only [H, y]
      rw [← add_sum_erase _ _ (mem_univ j0), add_comm]
      congr 1
      · apply sum_congr rfl; intro j hj
        have : (j : ℕ) ≠ k := fun h => ne_of_mem_erase hj (Fin.ext h)
        have e : ((j : ℕ) < k + 1) ↔ ((j : ℕ) < k) := by omega
        simp only [e]
      · simp [j0]
    rw [avg_update j0 (fun ω => h (H k ω)), avg_update j0 (fun ω => h (H (k + 1) ω)), ← avg_sub]
    refine (abs_avg_le _).trans (avg_le_of_le fun ω => ?_)
    simp only [hHk, hHk1, hy, Function.update_self]
    exact avg_moment_match hh (y ω) (a j0) (ha j0) X Z hm
  have tele : avg (fun ω => h (H 0 ω)) - avg (fun ω => h (H n ω)) =
      ∑ k ∈ range n, (avg (fun ω => h (H k ω)) - avg (fun ω => h (H (k + 1) ω))) := by
    rw [sum_range_sub']
  rw [tele]
  calc |∑ k ∈ range n, (avg (fun ω => h (H k ω)) - avg (fun ω => h (H (k + 1) ω)))|
      ≤ ∑ k ∈ range n, |avg (fun ω => h (H k ω)) - avg (fun ω => h (H (k + 1) ω))| :=
        abs_sum_le_sum_abs _ _
    _ ≤ ∑ _k ∈ range n, B := sum_le_sum fun k hk => step k (mem_range.mp hk)
    _ = n * B := by rw [sum_const, card_range, nsmul_eq_mul]

/-- Coins are orthonormal. -/
theorem E_sq_lin {N : ℕ} (α : Fin N → ℝ) :
    E (fun ω : Fin N → Bool => (∑ i, α i * (sgn (ω i) : ℝ)) ^ 2) = ∑ i, α i ^ 2 := by
  have : (fun ω : Fin N → Bool => (∑ i, α i * (sgn (ω i) : ℝ)) ^ 2) =
      fun ω => ∑ i, ∑ j, (α i * α j) * ((chi {i} ω : ℝ) * chi {j} ω) := by
    funext ω; rw [sq, sum_mul_sum]
    apply sum_congr rfl; intro i _; apply sum_congr rfl; intro j _
    simp [chi]; ring
  rw [this, E_sum]
  simp_rw [E_sum, E_smul, E_chi_mul]
  apply sum_congr rfl; intro i _
  rw [sum_eq_single i]
  · simp [sq]
  · intro j _ hj; simp [Ne.symm hj]
  · simp

/-- **The second-order step.**  Adding a mean-zero perturbation linear in the coins
changes `E h` by the cross term plus the second-order remainder. -/
theorem dstep {N : ℕ} {h : V → ℝ} {M : ℕ → ℝ} (hh : DBnd h 2 M) {c : ℝ} (hc : 0 < c)
    (w e : Fin N → V) :
    |E (fun ω => h (walkVec c w ∅ ω + ∑ i, (c * (sgn (ω i) : ℝ)) • e i)) -
        E (fun ω => h (walkVec c w ∅ ω))| ≤
      c ^ 2 * M 2 * ∑ i, ‖w i‖ * ‖e i‖ +
        M 2 / 2 * E (fun ω : Fin N → Bool => ‖∑ i, (c * (sgn (ω i) : ℝ)) • e i‖ ^ 2) := by
  set Y := fun ω => walkVec c w ∅ ω
  set D := fun ω : Fin N → Bool => ∑ i, (c * (sgn (ω i) : ℝ)) • e i
  have hM : 0 ≤ M 2 := hh.2.1 2 le_rfl
  -- pointwise second-order Taylor
  have hR : ∀ ω, |h (Y ω + D ω) - h (Y ω) - fderiv ℝ h (Y ω) (D ω)| ≤ M 2 / 2 * ‖D ω‖ ^ 2 := by
    intro ω
    have := line_taylor (n := 1) (hh.of_eq (by norm_num)) (Y ω) (D ω) 1
    simp only [one_smul, sum_range_succ, sum_range_zero, List.replicate, dirD_nil, dirD_cons,
      zero_add, pow_zero, mul_one, Nat.factorial, Nat.cast_one, div_one, pow_one, abs_one,
      one_pow] at this
    convert this using 1
    · congr 1; ring
    · norm_num; ring
  -- the linear term
  have hlin : |E (fun ω => fderiv ℝ h (Y ω) (D ω))| ≤ c ^ 2 * M 2 * ∑ i, ‖w i‖ * ‖e i‖ := by
    have e1 : (fun ω => fderiv ℝ h (Y ω) (D ω)) =
        fun ω => ∑ i, c * (fderiv ℝ h (Y ω) (e i) * (sgn (ω i) : ℝ) * 1) := by
      funext ω; simp only [D, map_sum, map_smul, smul_eq_mul]
      apply sum_congr rfl; intro i _; ring
    rw [e1, E_sum, mul_sum]
    refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun i _ => ?_)
    rw [E_smul, E_sgn_mul i (fun ω => fderiv ℝ h (Y ω) (e i)) (fun _ => 1) (fun _ _ => rfl)]
    set G : V → ℝ := fun z => dirD [e i] h z
    have hG : (fun ω => fderiv ℝ h (Y ω) (e i)) = fun ω => G (walkVec c w ∅ ω) := rfl
    rw [hG, D_walk c hc.ne' w G (Finset.notMem_empty i)]
    have hGd : Differentiable ℝ G :=
      (contDiff_dirD' hh.1 [e i] 1 (by simp)).differentiable (by norm_num)
    have hb : ∀ z, |cd c (w i) G z| ≤ M 2 * (‖w i‖ * ‖e i‖) := by
      intro z
      refine abs_cd_le hGd hc (w i) (fun y => ?_) z
      have := hh.2.2 [w i, e i] (by simp) y
      simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one,
        List.length_cons, List.length_nil] at this
      exact this
    rw [abs_mul, abs_of_pos hc]
    have : |E (fun ω => c * cd c (w i) G (walkVec c w (insert i ∅) ω) * 1)| ≤
        c * (M 2 * (‖w i‖ * ‖e i‖)) := by
      have hc0 : 0 ≤ c * (M 2 * (‖w i‖ * ‖e i‖)) := by positivity
      rw [← avg_eq_E]
      refine abs_avg_le_of_le fun ω => ?_
      rw [mul_one, abs_mul, abs_of_pos hc]
      exact mul_le_mul_of_nonneg_left (hb _) hc.le
    calc c * |E (fun ω => c * cd c (w i) G (walkVec c w (insert i ∅) ω) * 1)|
        ≤ c * (c * (M 2 * (‖w i‖ * ‖e i‖))) := mul_le_mul_of_nonneg_left this hc.le
      _ = _ := by ring
  have hsplit : E (fun ω => h (Y ω + D ω)) - E (fun ω => h (Y ω)) =
      E (fun ω => fderiv ℝ h (Y ω) (D ω)) +
        E (fun ω => h (Y ω + D ω) - h (Y ω) - fderiv ℝ h (Y ω) (D ω)) := by
    simp only [← avg_eq_E]
    rw [← avg_sub, ← avg_add]; congr 1; funext ω; ring
  show |E (fun ω => h (Y ω + D ω)) - E (fun ω => h (Y ω))| ≤ _
  rw [hsplit]
  refine (abs_add_le _ _).trans (add_le_add hlin ?_)
  simp only [← avg_eq_E]
  refine (abs_avg_le _).trans ?_
  rw [← avg_const_mul]
  exact avg_mono hR

end Blocks2

end QE.Chaos.Calc

namespace QE.Chaos.Calc

open Finset QE.OpenSto.Walsh

/-! ## Part A.5: the cell vectors and the kernel comparison -/

section Kernel

variable {p : ℕ}

/-- The direction of the cell `j` of the lattice `T/n · ℤ`: `(1[j < k_l])_l`, `k_l = ⌊t_l n/T⌋`. -/
def cellVec (T : ℝ) (n : ℕ) (t : Fin p → ℝ) (j : ℕ) : Fin p → ℝ :=
  fun l => if j < QE.NSA.walkIdx T n (t l) then 1 else 0

/-- The Anderson walk at the times `t_l`, on `N` coins: `W(t_l) = √(T/N) ∑_{i < k_l} ξ_i`. -/
def fineWalk (T : ℝ) (N : ℕ) (t : Fin p → ℝ) (ω : Fin N → Bool) : Fin p → ℝ :=
  fun l => √(T / N) * ∑ i ∈ univ.filter (fun i : Fin N => (i : ℕ) < QE.NSA.walkIdx T N (t l)),
    (sgn (ω i) : ℝ)

theorem cellVec_mem (T : ℝ) (n : ℕ) (t : Fin p → ℝ) (j : ℕ) (l : Fin p) :
    cellVec T n t j l = 0 ∨ cellVec T n t j l = 1 := by
  unfold cellVec; split_ifs <;> simp

theorem norm_cellVec_le (T : ℝ) (n : ℕ) (t : Fin p → ℝ) (j : ℕ) : ‖cellVec T n t j‖ ≤ 1 := by
  refine (pi_norm_le_iff_of_nonneg zero_le_one).2 fun l => ?_
  rcases cellVec_mem T n t j l with h | h <;> simp [h]

theorem fineWalk_eq_walkVec (T : ℝ) (N : ℕ) (t : Fin p → ℝ) :
    fineWalk T N t = walkVec √(T / N) (fun i : Fin N => cellVec T N t i) ∅ := by
  funext ω l
  simp only [fineWalk, walkVec, sdiff_empty, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
    cellVec, sum_filter, mul_sum]
  apply sum_congr rfl; intro i _
  split_ifs <;> simp

/-- Block of a fine coin. -/
def blk {n q : ℕ} (i : Fin (n * q)) : Fin n := (finProdFinEquiv.symm i).1

/-- Position of a fine coin in its block. -/
def bpos {n q : ℕ} (i : Fin (n * q)) : Fin q := (finProdFinEquiv.symm i).2

theorem val_blk {n q : ℕ} (i : Fin (n * q)) : (i : ℕ) = bpos i + q * blk i := by
  conv_lhs => rw [← finProdFinEquiv.apply_symm_apply i]
  rfl

theorem blk_finProd {n q : ℕ} (j : Fin n) (r : Fin q) : blk (finProdFinEquiv (j, r)) = j := by
  simp [blk]

theorem sum_blk {n q : ℕ} (f : Fin n → ℝ) : ∑ i : Fin (n * q), f (blk i) = q * ∑ j, f j := by
  rw [← Equiv.sum_comp finProdFinEquiv, Fintype.sum_prod_type]
  simp only [blk_finProd, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [mul_sum]

theorem idx_bounds {T : ℝ} (hT : 0 < T) {n q : ℕ} (hn : 0 < n) (hq : 0 < q) {t : ℝ}
    (ht : 0 ≤ t) :
    q * QE.NSA.walkIdx T n t ≤ QE.NSA.walkIdx T (n * q) t ∧
      QE.NSA.walkIdx T (n * q) t < q * QE.NSA.walkIdx T n t + q := by
  unfold QE.NSA.walkIdx
  set x := t / (T / n)
  have hx0 : 0 ≤ x := div_nonneg ht (by positivity)
  have hnr : (0 : ℝ) < n := by exact_mod_cast hn
  have hqr : (0 : ℝ) < q := by exact_mod_cast hq
  have hx : t / (T / ((n * q : ℕ) : ℝ)) = x * q := by
    simp only [x]; push_cast; field_simp
  rw [hx]
  constructor
  · apply Nat.le_floor
    push_cast
    have := Nat.floor_le hx0
    nlinarith
  · rw [Nat.floor_lt (by positivity)]
    push_cast
    have := Nat.lt_floor_add_one x
    nlinarith

theorem cell_agree {T : ℝ} (hT : 0 < T) {n q : ℕ} (hn : 0 < n) (hq : 0 < q)
    (t : Fin p → ℝ) (ht : ∀ l, 0 ≤ t l) (i : Fin (n * q)) (l : Fin p)
    (hb : (blk i : ℕ) ≠ QE.NSA.walkIdx T n (t l)) :
    cellVec T (n * q) t i l = cellVec T n t (blk i) l := by
  obtain ⟨h1, h2⟩ := idx_bounds hT hn hq (ht l)
  have hi := val_blk i
  have hr := (bpos i).isLt
  set k := QE.NSA.walkIdx T n (t l)
  set K := QE.NSA.walkIdx T (n * q) (t l)
  set j := (blk i : ℕ)
  unfold cellVec
  rcases Nat.lt_or_gt_of_ne hb with hjk | hjk
  · have : q * (j + 1) ≤ q * k := Nat.mul_le_mul_left _ hjk
    rw [if_pos (by rw [mul_add] at this; omega), if_pos hjk]
  · have : q * (k + 1) ≤ q * j := Nat.mul_le_mul_left _ hjk
    rw [if_neg (by rw [mul_add] at this; omega), if_neg (by omega)]

variable {T : ℝ} {n q : ℕ}

/-- The perturbation coefficients of the fine walk relative to the block walk. -/
def eVec (T : ℝ) (n q : ℕ) (t : Fin p → ℝ) (S : Finset (Fin n)) (U : Finset (Fin (n * q)))
    (i : Fin (n * q)) : Fin p → ℝ :=
  (if i ∈ U then 0 else cellVec T (n * q) t i) - (if blk i ∈ S then 0 else cellVec T n t (blk i))

theorem eVec_prop (hT : 0 < T) (hn : 0 < n) (hq : 0 < q) (t : Fin p → ℝ) (ht : ∀ l, 0 ≤ t l)
    (S : Finset (Fin n)) (U : Finset (Fin (n * q))) (hU : ∀ i ∈ U, blk i ∈ S)
    (i : Fin (n * q)) (l : Fin p) :
    |eVec T n q t S U i l| ≤ 1 ∧
      (eVec T n q t S U i l ≠ 0 → blk i ∈ S ∨ (blk i : ℕ) = QE.NSA.walkIdx T n (t l)) := by
  unfold eVec
  by_cases hS : blk i ∈ S
  · simp only [hS, if_true, sub_zero]
    refine ⟨?_, fun _ => by simp [hS]⟩
    split_ifs
    · simp
    · rcases cellVec_mem T (n * q) t i l with h | h <;> simp [h]
  · have hiU : i ∉ U := fun h => hS (hU i h)
    simp only [hS, hiU, if_false, Pi.sub_apply]
    by_cases hb : (blk i : ℕ) = QE.NSA.walkIdx T n (t l)
    · refine ⟨?_, fun _ => Or.inr hb⟩
      rcases cellVec_mem T (n * q) t i l with h | h <;>
        rcases cellVec_mem T n t (blk i) l with h' | h' <;> simp [h, h']
    · rw [cell_agree hT hn hq t ht i l hb]; simp

theorem eVec_norm_le (hT : 0 < T) (hn : 0 < n) (hq : 0 < q) (t : Fin p → ℝ) (ht : ∀ l, 0 ≤ t l)
    (S : Finset (Fin n)) (U : Finset (Fin (n * q))) (hU : ∀ i ∈ U, blk i ∈ S) (i : Fin (n * q)) :
    ‖eVec T n q t S U i‖ ≤ 1 :=
  (pi_norm_le_iff_of_nonneg zero_le_one).2 fun l => by
    rw [Real.norm_eq_abs]; exact (eVec_prop hT hn hq t ht S U hU i l).1

theorem wVec_norm_le (t : Fin p → ℝ) (S : Finset (Fin n)) (j : Fin n) :
    ‖(if j ∈ S then 0 else cellVec T n t j)‖ ≤ 1 := by
  split_ifs
  · simp
  · exact norm_cellVec_le T n t j

/-- Pointwise count for the cross term. -/
theorem cross_le (hT : 0 < T) (hn : 0 < n) (hq : 0 < q) (t : Fin p → ℝ) (ht : ∀ l, 0 ≤ t l)
    (S : Finset (Fin n)) (U : Finset (Fin (n * q))) (hU : ∀ i ∈ U, blk i ∈ S) (i : Fin (n * q)) :
    ‖(if blk i ∈ S then 0 else cellVec T n t (blk i))‖ * ‖eVec T n q t S U i‖ ≤
      ∑ l, (if (blk i : ℕ) = QE.NSA.walkIdx T n (t l) then (1 : ℝ) else 0) := by
  have hR : 0 ≤ ∑ l, (if (blk i : ℕ) = QE.NSA.walkIdx T n (t l) then (1 : ℝ) else 0) :=
    sum_nonneg fun l _ => by split_ifs <;> norm_num
  by_cases hS : blk i ∈ S
  · simp [hS, hR]
  by_cases hex : ∃ l, (blk i : ℕ) = QE.NSA.walkIdx T n (t l)
  · obtain ⟨l, hl⟩ := hex
    have h1 : (1 : ℝ) ≤ ∑ l, (if (blk i : ℕ) = QE.NSA.walkIdx T n (t l) then (1 : ℝ) else 0) := by
      have := single_le_sum (f := fun l => if (blk i : ℕ) = QE.NSA.walkIdx T n (t l)
        then (1 : ℝ) else 0) (fun l _ => by split_ifs <;> norm_num) (mem_univ l)
      simpa [hl] using this
    calc _ ≤ 1 * 1 := mul_le_mul (wVec_norm_le t S (blk i))
            (eVec_norm_le hT hn hq t ht S U hU i) (norm_nonneg _) zero_le_one
      _ ≤ _ := by linarith
  · push Not at hex
    have he : eVec T n q t S U i = 0 := by
      funext l
      by_contra hne
      rcases (eVec_prop hT hn hq t ht S U hU i l).2 hne with h | h
      · exact hS h
      · exact hex l h
    simp [he, hR]

/-- Pointwise count for the variance term. -/
theorem sq_e_le (hT : 0 < T) (hn : 0 < n) (hq : 0 < q) (t : Fin p → ℝ) (ht : ∀ l, 0 ≤ t l)
    (S : Finset (Fin n)) (U : Finset (Fin (n * q))) (hU : ∀ i ∈ U, blk i ∈ S) (i : Fin (n * q))
    (l : Fin p) :
    eVec T n q t S U i l ^ 2 ≤ (if blk i ∈ S then (1 : ℝ) else 0) +
      (if (blk i : ℕ) = QE.NSA.walkIdx T n (t l) then 1 else 0) := by
  obtain ⟨h1, h2⟩ := eVec_prop hT hn hq t ht S U hU i l
  by_cases h0 : eVec T n q t S U i l = 0
  · rw [h0]; split_ifs <;> norm_num
  · have hsq : eVec T n q t S U i l ^ 2 ≤ 1 := by
      rw [← sq_abs]; nlinarith [abs_nonneg (eVec T n q t S U i l)]
    rcases h2 h0 with h | h
    · rw [if_pos h]; split_ifs <;> linarith
    · rw [if_pos h]; split_ifs <;> linarith

theorem sum_ind_eq_le (k : ℕ) : ∑ j : Fin n, (if (j : ℕ) = k then (1 : ℝ) else 0) ≤ 1 := by
  rw [sum_boole]
  have : (univ.filter (fun j : Fin n => (j : ℕ) = k)).card ≤ 1 :=
    card_le_one.mpr fun a ha b hb => Fin.ext ((mem_filter.mp ha).2.trans (mem_filter.mp hb).2.symm)
  exact_mod_cast this

theorem norm_sq_le_sum_sq (x : Fin p → ℝ) : ‖x‖ ^ 2 ≤ ∑ l, x l ^ 2 := by
  have h : ‖x‖ ≤ √(∑ l, x l ^ 2) := by
    refine (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).2 fun l => ?_
    rw [Real.norm_eq_abs]
    apply Real.abs_le_sqrt
    exact single_le_sum (f := fun l => x l ^ 2) (fun l _ => sq_nonneg _) (mem_univ l)
  calc ‖x‖ ^ 2 ≤ (√(∑ l, x l ^ 2)) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h 2
    _ = _ := Real.sq_sqrt (sum_nonneg fun l _ => sq_nonneg _)

end Kernel

end QE.Chaos.Calc

namespace QE.Chaos.Calc

open Finset QE.OpenSto.Walsh

/-! ## Part A.6: moments of a coin and of a block sum; the kernel comparison -/

section Moments

theorem avg_sgn {q : ℕ} (r0 : Fin q) : avg (fun b : Fin q → Bool => (sgn (b r0) : ℝ)) = 0 := by
  rw [avg_eq_E]
  have := E_chi (K := ℝ) ({r0} : Finset (Fin q))
  simpa [chi] using this

theorem sgn_sq' (b : Bool) : (sgn b : ℝ) ^ 2 = 1 := by rw [sq, sgn_mul_self]

theorem avg_coin_moments {q : ℕ} (r0 : Fin q) (c : ℝ) :
    avg (fun b : Fin q → Bool => (c * (sgn (b r0) : ℝ)) ^ 1) = 0 ∧
    avg (fun b : Fin q → Bool => (c * (sgn (b r0) : ℝ)) ^ 2) = c ^ 2 ∧
    avg (fun b : Fin q → Bool => (c * (sgn (b r0) : ℝ)) ^ 3) = 0 ∧
    avg (fun b : Fin q → Bool => (c * (sgn (b r0) : ℝ)) ^ 4) = c ^ 4 := by
  have e2 : ∀ b : Fin q → Bool, (c * (sgn (b r0) : ℝ)) ^ 2 = c ^ 2 := by
    intro b; rw [mul_pow, sgn_sq', mul_one]
  have e3 : ∀ b : Fin q → Bool, (c * (sgn (b r0) : ℝ)) ^ 3 = c ^ 3 * sgn (b r0) := by
    intro b; rw [mul_pow, show (sgn (b r0) : ℝ) ^ 3 = (sgn (b r0) : ℝ) ^ 2 * sgn (b r0) by ring,
      sgn_sq', one_mul]
  have e4 : ∀ b : Fin q → Bool, (c * (sgn (b r0) : ℝ)) ^ 4 = c ^ 4 := by
    intro b; rw [mul_pow, show (sgn (b r0) : ℝ) ^ 4 = ((sgn (b r0) : ℝ) ^ 2) ^ 2 by ring, sgn_sq',
      one_pow, mul_one]
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp only [pow_one]; rw [avg_const_mul, avg_sgn, mul_zero]
  · simp only [e2]; exact avg_const _
  · simp only [e3]; rw [avg_const_mul, avg_sgn, mul_zero]
  · simp only [e4]; exact avg_const _

theorem avg_blockSum_pow {q : ℕ} (c : ℝ) (k : ℕ) :
    avg (fun b : Fin q → Bool => (c * (QE.Prob.S b : ℝ)) ^ k) =
      c ^ k * (∑ b : Fin q → Bool, (QE.Prob.S b : ℝ) ^ k) / 2 ^ q := by
  unfold avg
  simp only [mul_pow, ← mul_sum, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]
  push_cast; ring

theorem avg_block_moments {q : ℕ} (hq : 0 < q) (c : ℝ) :
    avg (fun b : Fin q → Bool => (c * (QE.Prob.S b : ℝ)) ^ 1) = 0 ∧
    avg (fun b : Fin q → Bool => (c * (QE.Prob.S b : ℝ)) ^ 2) = c ^ 2 * q ∧
    avg (fun b : Fin q → Bool => (c * (QE.Prob.S b : ℝ)) ^ 3) = 0 ∧
    avg (fun b : Fin q → Bool => (c * (QE.Prob.S b : ℝ)) ^ 4) = c ^ 4 * (3 * q ^ 2 - 2 * q) := by
  have h2 : (2 : ℝ) ^ q ≠ 0 := pow_ne_zero _ two_ne_zero
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [avg_blockSum_pow]; simp only [pow_one]; rw [QE.Prob.sum_S]; simp
  · rw [avg_blockSum_pow, QE.Prob.sum_S_sq]; field_simp
  · rw [avg_blockSum_pow, QE.Prob.BE.sum_S_cube]; simp
  · rw [avg_blockSum_pow, QE.Prob.BE.sum_S_four]; field_simp

end Moments

section Core

variable {p : ℕ}

/-- **The kernel comparison, core form.**  Coarse coins on the cells of `T/n · ℤ` versus
the fine walk on `n q` coins (with the coins of `U` removed, all lying in the blocks of `S`),
for a test function with bounded derivatives up to order 4. -/
theorem kernel_core {T : ℝ} (hT : 0 < T) {n q : ℕ} (hn : 0 < n) (hq : 0 < q)
    (t : Fin p → ℝ) (ht : ∀ l, 0 ≤ t l) {h : (Fin p → ℝ) → ℝ} {M : ℕ → ℝ} (hh : DBnd h 4 M)
    (S : Finset (Fin n)) (U : Finset (Fin (n * q))) (hU : ∀ i ∈ U, blk i ∈ S) :
    |E (fun η : Fin n → Bool => h (walkVec √(T / n) (fun j : Fin n => cellVec T n t j) S η)) -
      E (fun ω : Fin (n * q) → Bool =>
        h (walkVec √(T / ((n * q : ℕ) : ℝ)) (fun i : Fin (n * q) => cellVec T (n * q) t i) U ω))| ≤
      (T / 6 * M 4 + p * (S.card + 3) / 2 * M 2) * (T / n) := by
  classical
  set c := √(T / n) with hc_def
  set c' := √(T / ((n * q : ℕ) : ℝ)) with hc'_def
  have hnr : (0 : ℝ) < n := by exact_mod_cast hn
  have hqr : (0 : ℝ) < q := by exact_mod_cast hq
  have hτ : 0 < T / n := div_pos hT hnr
  have hc : 0 < c := Real.sqrt_pos.mpr hτ
  have hc' : 0 < c' := Real.sqrt_pos.mpr (div_pos hT (by positivity))
  have hc2 : c ^ 2 = T / n := Real.sq_sqrt hτ.le
  have hc'2 : c' ^ 2 * q = T / n := by
    rw [hc'_def, Real.sq_sqrt (div_pos hT (by positivity)).le]; push_cast; field_simp
  have hM4 : 0 ≤ M 4 := hh.2.1 4 le_rfl
  have hM2 : 0 ≤ M 2 := hh.2.1 2 (by norm_num)
  let a : Fin n → (Fin p → ℝ) := fun j => if j ∈ S then 0 else cellVec T n t j
  have ha : ∀ j, ‖a j‖ ≤ 1 := fun j => wVec_norm_le t S j
  set r0 : Fin q := ⟨0, hq⟩
  let X : (Fin q → Bool) → ℝ := fun b => c * (sgn (b r0) : ℝ)
  let Z : (Fin q → Bool) → ℝ := fun b => c' * (QE.Prob.S b : ℝ)
  -- Step A: the coarse side as a block average
  have hA : E (fun η : Fin n → Bool => h (walkVec c (fun j : Fin n => cellVec T n t j) S η)) =
      avg (fun ω : Fin n → Fin q → Bool => h (∑ j, X (ω j) • a j)) := by
    rw [← avg_first_coin n q hq]
    congr 1; funext ω; congr 1
    unfold walkVec
    rw [show (univ : Finset (Fin n)) \ S = univ.filter (· ∉ S) by ext; simp, sum_filter]
    apply sum_congr rfl; intro j _
    by_cases hj : j ∈ S <;> simp [a, X, hj, r0]
  -- Step C: the block-sum side as a fine expectation
  let w : Fin (n * q) → (Fin p → ℝ) := fun i => a (blk i)
  have hC : avg (fun ω : Fin n → Fin q → Bool => h (∑ j, Z (ω j) • a j)) =
      E (fun ω : Fin (n * q) → Bool => h (walkVec c' w ∅ ω)) := by
    rw [E_eq_avg_unblock n q]
    congr 1; funext ω; congr 1
    unfold walkVec
    rw [sdiff_empty, ← Equiv.sum_comp finProdFinEquiv, Fintype.sum_prod_type]
    apply sum_congr rfl; intro j _
    simp only [w, blk_finProd, unblock_apply, Z, QE.Prob.S]
    rw [mul_sum, sum_smul]
    rfl
  -- Step B: Lindeberg
  obtain ⟨x1, x2, x3, x4⟩ := avg_coin_moments r0 c
  obtain ⟨z1, z2, z3, z4⟩ := avg_block_moments hq c'
  have hm : ∀ k, 1 ≤ k → k ≤ 3 → avg (fun b => X b ^ k) = avg (fun b => Z b ^ k) := by
    intro k hk1 hk3
    interval_cases k
    · exact x1.trans z1.symm
    · rw [show avg (fun b => X b ^ 2) = c ^ 2 from x2, show avg (fun b => Z b ^ 2) = c' ^ 2 * q
        from z2, hc2, hc'2]
    · exact x3.trans z3.symm
  have hB := lindeberg_blocks hh a ha X Z hm
  rw [show avg (fun b => X b ^ 4) = c ^ 4 from x4,
    show avg (fun b => Z b ^ 4) = c' ^ 4 * (3 * q ^ 2 - 2 * q) from z4] at hB
  have hB' : (n : ℝ) * (M 4 / 24 * (c ^ 4 + c' ^ 4 * (3 * q ^ 2 - 2 * q))) ≤
      T / 6 * M 4 * (T / n) := by
    have e1 : c ^ 4 = (T / n) ^ 2 := by rw [show c ^ 4 = (c ^ 2) ^ 2 by ring, hc2]
    have e2 : c' ^ 4 * (3 * q ^ 2 - 2 * q) = (T / n) ^ 2 * (3 - 2 / q) := by
      rw [← hc'2]; field_simp
    rw [e1, e2]
    have : (T / n) ^ 2 * (3 - 2 / q) ≤ 3 * (T / n) ^ 2 := by
      have : 0 ≤ 2 / (q : ℝ) := by positivity
      nlinarith [sq_nonneg (T / n)]
    calc (n : ℝ) * (M 4 / 24 * ((T / n) ^ 2 + (T / n) ^ 2 * (3 - 2 / q)))
        ≤ n * (M 4 / 24 * ((T / n) ^ 2 + 3 * (T / n) ^ 2)) := by gcongr
      _ = T / 6 * M 4 * (T / n) := by field_simp; ring
  -- Step D: the second-order step on the fine coins
  let e : Fin (n * q) → (Fin p → ℝ) := eVec T n q t S U
  have hfine : ∀ ω : Fin (n * q) → Bool,
      walkVec c' (fun i : Fin (n * q) => cellVec T (n * q) t i) U ω =
        walkVec c' w ∅ ω + ∑ i, (c' * (sgn (ω i) : ℝ)) • e i := by
    intro ω
    unfold walkVec
    rw [sdiff_empty, ← sum_add_distrib,
      show (univ : Finset (Fin (n * q))) \ U = univ.filter (· ∉ U) by ext; simp, sum_filter]
    apply sum_congr rfl; intro i _
    simp only [e, eVec, w, a, ← smul_add]
    by_cases hi : i ∈ U <;> simp [hi]
  have hD := dstep (hh.mono (by norm_num)) hc' w e
  simp only [← hfine] at hD
  -- bound the cross term
  have hcross : ∑ i, ‖w i‖ * ‖e i‖ ≤ p * q := by
    calc ∑ i, ‖w i‖ * ‖e i‖ ≤ ∑ i : Fin (n * q), ∑ l : Fin p,
          (if (blk i : ℕ) = QE.NSA.walkIdx T n (t l) then (1 : ℝ) else 0) :=
          sum_le_sum fun i _ => cross_le hT hn hq t ht S U hU i
      _ = ∑ l : Fin p, ∑ i : Fin (n * q),
          (if (blk i : ℕ) = QE.NSA.walkIdx T n (t l) then (1 : ℝ) else 0) := sum_comm
      _ = ∑ l : Fin p, (q : ℝ) * ∑ j : Fin n,
          (if (j : ℕ) = QE.NSA.walkIdx T n (t l) then (1 : ℝ) else 0) := by
          apply sum_congr rfl; intro l _
          exact sum_blk (fun j : Fin n => if (j : ℕ) = QE.NSA.walkIdx T n (t l) then (1 : ℝ) else 0)
      _ ≤ ∑ _l : Fin p, (q : ℝ) * 1 :=
          sum_le_sum fun l _ => mul_le_mul_of_nonneg_left (sum_ind_eq_le _) hqr.le
      _ = p * q := by simp
  -- bound the variance term
  have hvar : E (fun ω : Fin (n * q) → Bool => ‖∑ i, (c' * (sgn (ω i) : ℝ)) • e i‖ ^ 2) ≤
      p * (c' ^ 2 * ((S.card + 1) * q)) := by
    rw [← avg_eq_E]
    calc avg (fun ω : Fin (n * q) → Bool => ‖∑ i, (c' * (sgn (ω i) : ℝ)) • e i‖ ^ 2)
        ≤ avg (fun ω : Fin (n * q) → Bool => ∑ l, (∑ i, (c' * e i l) * (sgn (ω i) : ℝ)) ^ 2) := by
          apply avg_mono; intro ω
          refine (norm_sq_le_sum_sq _).trans (le_of_eq ?_)
          apply sum_congr rfl; intro l _
          congr 1
          rw [Finset.sum_apply]
          apply sum_congr rfl; intro i _
          simp only [Pi.smul_apply, smul_eq_mul]; ring
      _ = ∑ l, ∑ i, (c' * e i l) ^ 2 := by
          rw [avg_sum]; apply sum_congr rfl; intro l _
          rw [avg_eq_E, E_sq_lin]
      _ ≤ ∑ _l : Fin p, c' ^ 2 * ((S.card + 1) * q) := by
          apply sum_le_sum; intro l _
          calc ∑ i, (c' * e i l) ^ 2 = c' ^ 2 * ∑ i, e i l ^ 2 := by
                rw [mul_sum]; apply sum_congr rfl; intro i _; ring
            _ ≤ c' ^ 2 * ∑ i : Fin (n * q), ((if blk i ∈ S then (1 : ℝ) else 0) +
                (if (blk i : ℕ) = QE.NSA.walkIdx T n (t l) then 1 else 0)) := by
                gcongr with i
                exact sq_e_le hT hn hq t ht S U hU i l
            _ ≤ c' ^ 2 * ((S.card + 1) * q) := by
                gcongr
                rw [sum_add_distrib,
                  sum_blk (fun j : Fin n => if j ∈ S then (1 : ℝ) else 0),
                  sum_blk (fun j : Fin n => if (j : ℕ) = QE.NSA.walkIdx T n (t l) then (1 : ℝ) else 0),
                  sum_boole]
                have := sum_ind_eq_le (n := n) (QE.NSA.walkIdx T n (t l))
                simp only [filter_mem_eq_inter, univ_inter]
                nlinarith
      _ = p * (c' ^ 2 * ((S.card + 1) * q)) := by simp
  have hD' : |E (fun ω : Fin (n * q) → Bool =>
        h (walkVec c' (fun i : Fin (n * q) => cellVec T (n * q) t i) U ω)) -
      E (fun ω : Fin (n * q) → Bool => h (walkVec c' w ∅ ω))| ≤
      p * (S.card + 3) / 2 * M 2 * (T / n) := by
    refine hD.trans ?_
    calc c' ^ 2 * M 2 * ∑ i, ‖w i‖ * ‖e i‖ + M 2 / 2 *
          E (fun ω : Fin (n * q) → Bool => ‖∑ i, (c' * (sgn (ω i) : ℝ)) • e i‖ ^ 2)
        ≤ c' ^ 2 * M 2 * (p * q) + M 2 / 2 * (p * (c' ^ 2 * ((S.card + 1) * q))) := by
          gcongr
      _ = p * (S.card + 3) / 2 * M 2 * (c' ^ 2 * q) := by ring
      _ = _ := by rw [hc'2]
  rw [hA, ← hC] at *
  calc _ ≤ |avg (fun ω : Fin n → Fin q → Bool => h (∑ j, X (ω j) • a j)) -
          avg (fun ω : Fin n → Fin q → Bool => h (∑ j, Z (ω j) • a j))| +
        |avg (fun ω : Fin n → Fin q → Bool => h (∑ j, Z (ω j) • a j)) -
          E (fun ω : Fin (n * q) → Bool =>
            h (walkVec c' (fun i : Fin (n * q) => cellVec T (n * q) t i) U ω))| := abs_sub_le _ _ _
    _ ≤ T / 6 * M 4 * (T / n) + p * (S.card + 3) / 2 * M 2 * (T / n) := by
        refine add_le_add (hB.trans hB') ?_
        rw [hC, abs_sub_comm]; exact hD'
    _ = _ := by ring

end Core

end QE.Chaos.Calc

namespace QE.Chaos.Calc

open Finset QE.OpenSto.Walsh

/-! ## Part A.7: the kernel bounds -/

section Final

variable {p : ℕ}

theorem abs_E_sub_le {N : ℕ} {f g : (Fin N → Bool) → ℝ} {B : ℝ} (h : ∀ ω, |f ω - g ω| ≤ B) :
    |E f - E g| ≤ B := by
  rw [← avg_eq_E, ← avg_eq_E, ← avg_sub]
  exact abs_avg_le_of_le h

/-- The constant of the kernel bound (`thm:stoch-chaos-shadow`(i)). -/
def Cker (p m : ℕ) (T : ℝ) (N : ℕ → ℝ) : ℝ :=
  (m / 6 + p * (m + 3) / 2) * N (m + 2) + T / 6 * N (m + 4)

theorem norm_mem_map_cellVec_le {T : ℝ} {n : ℕ} {t : Fin p → ℝ} {l : List ℕ} :
    ∀ x ∈ l.map (fun j => cellVec T n t j), ‖x‖ ≤ 1 := by
  intro x hx
  obtain ⟨j, -, rfl⟩ := List.mem_map.mp hx
  exact norm_cellVec_le T n t j

/-- **Kernel comparison (granular, exact for every `n`, `q`).**  The discrete kernel
`E[δ_{v_{j₁}} ⋯ δ_{v_{j_m}} g(W^{(S)})]` of the Anderson walk on `n` coins versus the averaged
derivative `E[∂_{v_{j₁}} ⋯ ∂_{v_{j_m}} g(W_{nq}(t))]` along the walk on `n q` coins. -/
theorem kernel_coin_bound {m n q : ℕ} (hn : 0 < n) (hq : 0 < q) {T : ℝ} (hT : 0 < T)
    (t : Fin p → ℝ) (ht0 : ∀ l, 0 ≤ t l) {g : (Fin p → ℝ) → ℝ} {N : ℕ → ℝ}
    (hg : DBnd g (m + 4) N) (l : List (Fin n)) (hl : l.Nodup) (hlen : l.length = m) :
    |E (fun ω : Fin n → Bool => cds √(T / n) (l.map (fun j : Fin n => cellVec T n t j)) g
        (walkVec √(T / n) (fun j : Fin n => cellVec T n t j) l.toFinset ω)) -
      E (fun ω : Fin (n * q) → Bool =>
        dirD (l.map (fun j : Fin n => cellVec T n t j)) g (fineWalk T (n * q) t ω))| ≤
      Cker p m T N * (T / n) := by
  set vs := l.map (fun j : Fin n => cellVec T n t j)
  have hvs : vs.length = m := by simp [vs, hlen]
  have hv : ∀ x ∈ vs, ‖x‖ ≤ 1 := by
    intro x hx
    obtain ⟨j, -, rfl⟩ := List.mem_map.mp hx
    exact norm_cellVec_le T n t j
  have hdb : DBnd (dirD vs g) 4 (fun k => N (m + k)) := dBnd_dirD hg hvs hv
  have hnr : (0 : ℝ) < n := by exact_mod_cast hn
  have hc : 0 < √(T / n) := Real.sqrt_pos.mpr (div_pos hT hnr)
  have hc2 : √(T / n) ^ 2 = T / n := Real.sq_sqrt (div_pos hT hnr).le
  have h1 : |E (fun ω : Fin n → Bool => cds √(T / n) vs g
        (walkVec √(T / n) (fun j : Fin n => cellVec T n t j) l.toFinset ω)) -
      E (fun ω : Fin n → Bool => dirD vs g
        (walkVec √(T / n) (fun j : Fin n => cellVec T n t j) l.toFinset ω))| ≤
      m * (T / n) / 6 * N (m + 2) := by
    apply abs_E_sub_le; intro ω
    have := abs_cds_sub_dirD_le hc vs (g := g) (N := N)
      ((hg.mono (r' := m + 2) (by omega)).of_eq (by omega)) hv
      (walkVec √(T / n) (fun j : Fin n => cellVec T n t j) l.toFinset ω)
    rw [hvs, hc2] at this; exact this
  have h2 := kernel_core hT hn hq t ht0 hdb l.toFinset ∅ (by simp)
  rw [List.toFinset_card_of_nodup hl, hlen, ← fineWalk_eq_walkVec] at h2
  calc _ ≤ m * (T / n) / 6 * N (m + 2) + (T / 6 * N (m + 4) + p * (m + 3) / 2 * N (m + 2)) * (T / n) :=
        (abs_sub_le _ _ _).trans (add_le_add h1 h2)
    _ = Cker p m T N * (T / n) := by unfold Cker; ring

/-- **Fine-kernel comparison.**  The same with the fine discrete kernel
`E[δ^{fine}_{v_U} g(W_{nq}^{(U)})]` (step `√(T/(nq))`), where `U` takes one fine coin in each
block of `l`, at positions where the fine direction equals the coarse one. -/
theorem kernel_coin_bound_fine {m n q : ℕ} (hn : 0 < n) (hq : 0 < q) {T : ℝ} (hT : 0 < T)
    (t : Fin p → ℝ) (ht0 : ∀ l, 0 ≤ t l) {g : (Fin p → ℝ) → ℝ} {N : ℕ → ℝ}
    (hg : DBnd g (m + 4) N) (l : List (Fin n)) (hl : l.Nodup) (hlen : l.length = m)
    (U : List (Fin (n * q))) (hUl : U.map blk = l)
    (hUv : U.map (fun i : Fin (n * q) => cellVec T (n * q) t i) =
      l.map (fun j : Fin n => cellVec T n t j)) :
    |E (fun ω : Fin n → Bool => cds √(T / n) (l.map (fun j : Fin n => cellVec T n t j)) g
        (walkVec √(T / n) (fun j : Fin n => cellVec T n t j) l.toFinset ω)) -
      E (fun ω : Fin (n * q) → Bool =>
        cds √(T / ((n * q : ℕ) : ℝ)) (U.map (fun i : Fin (n * q) => cellVec T (n * q) t i)) g
          (walkVec √(T / ((n * q : ℕ) : ℝ)) (fun i : Fin (n * q) => cellVec T (n * q) t i)
            U.toFinset ω))| ≤
      (Cker p m T N + m / 6 * N (m + 2)) * (T / n) := by
  rw [hUv]
  set vs := l.map (fun j : Fin n => cellVec T n t j)
  have hvs : vs.length = m := by simp [vs, hlen]
  have hv : ∀ x ∈ vs, ‖x‖ ≤ 1 := by
    intro x hx
    obtain ⟨j, -, rfl⟩ := List.mem_map.mp hx
    exact norm_cellVec_le T n t j
  have hdb : DBnd (dirD vs g) 4 (fun k => N (m + k)) := dBnd_dirD hg hvs hv
  have hnr : (0 : ℝ) < n := by exact_mod_cast hn
  have hqr : (0 : ℝ) < q := by exact_mod_cast hq
  have hNq : (0 : ℝ) < ((n * q : ℕ) : ℝ) := by positivity
  have hc : 0 < √(T / n) := Real.sqrt_pos.mpr (div_pos hT hnr)
  have hc2 : √(T / n) ^ 2 = T / n := Real.sq_sqrt (div_pos hT hnr).le
  have hc' : 0 < √(T / ((n * q : ℕ) : ℝ)) := Real.sqrt_pos.mpr (div_pos hT hNq)
  have hc'2 : √(T / ((n * q : ℕ) : ℝ)) ^ 2 ≤ T / n := by
    rw [Real.sq_sqrt (div_pos hT hNq).le]
    apply div_le_div_of_nonneg_left hT.le hnr
    push_cast; nlinarith [show (1 : ℝ) ≤ q by exact_mod_cast hq]
  have hN2 : 0 ≤ N (m + 2) := hg.2.1 _ (by omega)
  have hg2 : DBnd g (vs.length + 2) N := (hg.mono (r' := m + 2) (by omega)).of_eq (by omega)
  have h1 : |E (fun ω : Fin n → Bool => cds √(T / n) vs g
        (walkVec √(T / n) (fun j : Fin n => cellVec T n t j) l.toFinset ω)) -
      E (fun ω : Fin n → Bool => dirD vs g
        (walkVec √(T / n) (fun j : Fin n => cellVec T n t j) l.toFinset ω))| ≤
      m * (T / n) / 6 * N (m + 2) := by
    apply abs_E_sub_le; intro ω
    have := abs_cds_sub_dirD_le hc vs hg2 hv
      (walkVec √(T / n) (fun j : Fin n => cellVec T n t j) l.toFinset ω)
    rw [hvs, hc2] at this; exact this
  have h3 : |E (fun ω : Fin (n * q) → Bool => dirD vs g
        (walkVec √(T / ((n * q : ℕ) : ℝ)) (fun i : Fin (n * q) => cellVec T (n * q) t i)
          U.toFinset ω)) -
      E (fun ω : Fin (n * q) → Bool => cds √(T / ((n * q : ℕ) : ℝ)) vs g
        (walkVec √(T / ((n * q : ℕ) : ℝ)) (fun i : Fin (n * q) => cellVec T (n * q) t i)
          U.toFinset ω))| ≤ m * (T / n) / 6 * N (m + 2) := by
    apply abs_E_sub_le; intro ω
    rw [abs_sub_comm]
    have := abs_cds_sub_dirD_le hc' vs hg2 hv
      (walkVec √(T / ((n * q : ℕ) : ℝ)) (fun i : Fin (n * q) => cellVec T (n * q) t i)
          U.toFinset ω)
    rw [hvs] at this
    refine this.trans ?_
    gcongr
  have hU : ∀ i ∈ U.toFinset, blk i ∈ l.toFinset := by
    intro i hi
    rw [List.mem_toFinset] at hi ⊢
    rw [← hUl]; exact List.mem_map_of_mem hi
  have h2 := kernel_core hT hn hq t ht0 hdb l.toFinset U.toFinset hU
  rw [List.toFinset_card_of_nodup hl, hlen] at h2
  calc _ ≤ m * (T / n) / 6 * N (m + 2) + (T / 6 * N (m + 4) + p * (m + 3) / 2 * N (m + 2)) * (T / n)
          + m * (T / n) / 6 * N (m + 2) := by
        refine (abs_sub_le _ _ _).trans (add_le_add h1 ((abs_sub_le _ _ _).trans
          (add_le_add h2 h3)) |>.trans (le_of_eq ?_))
        ring
    _ = (Cker p m T N + m / 6 * N (m + 2)) * (T / n) := by unfold Cker; ring

end Final

end QE.Chaos.Calc

/-! # Part B. Boolean hypercontractivity and the invariance principle -/


namespace QE.Chaos.Bon

open Finset QE.OpenSto.Walsh QE.Chaos

/-! ## Boolean degree, defined recursively through the first coin -/

/-- Even part in the first coin. -/
def cA {N : ℕ} (F : (Fin (N + 1) → Bool) → ℝ) : (Fin N → Bool) → ℝ :=
  fun ω => (F (Fin.cons true ω) + F (Fin.cons false ω)) / 2

/-- Odd part in the first coin. -/
def cB {N : ℕ} (F : (Fin (N + 1) → Bool) → ℝ) : (Fin N → Bool) → ℝ :=
  fun ω => (F (Fin.cons true ω) - F (Fin.cons false ω)) / 2

theorem cons_true {N : ℕ} (F : (Fin (N + 1) → Bool) → ℝ) (ω : Fin N → Bool) :
    F (Fin.cons true ω) = cA F ω + cB F ω := by unfold cA cB; ring

theorem cons_false {N : ℕ} (F : (Fin (N + 1) → Bool) → ℝ) (ω : Fin N → Bool) :
    F (Fin.cons false ω) = cA F ω - cB F ω := by unfold cA cB; ring

/-- `F` is a multilinear polynomial of degree `≤ d` in the coins. -/
def IsDeg : (N : ℕ) → ((Fin N → Bool) → ℝ) → ℕ → Prop
  | 0, _, _ => True
  | N + 1, F, d => IsDeg N (cA F) d ∧ IsDeg N (cB F) (d - 1) ∧ (d = 0 → ∀ ω, cB F ω = 0)

theorem isDeg_succ {N : ℕ} (F : (Fin (N + 1) → Bool) → ℝ) (d : ℕ) :
    IsDeg (N + 1) F d ↔ IsDeg N (cA F) d ∧ IsDeg N (cB F) (d - 1) ∧ (d = 0 → ∀ ω, cB F ω = 0) :=
  Iff.rfl

theorem IsDeg.congr {N : ℕ} {F G : (Fin N → Bool) → ℝ} {d : ℕ} (h : IsDeg N F d)
    (hFG : ∀ ω, F ω = G ω) : IsDeg N G d := by
  have : F = G := funext hFG
  subst this; exact h

theorem IsDeg.mono : ∀ {N : ℕ} {F : (Fin N → Bool) → ℝ} {d e : ℕ}, IsDeg N F d → d ≤ e →
    IsDeg N F e
  | 0, _, _, _, _, _ => trivial
  | N + 1, F, d, e, ⟨hA, hB, h0⟩, hde =>
    ⟨IsDeg.mono hA hde, IsDeg.mono hB (Nat.sub_le_sub_right hde 1), fun he => h0 (by omega)⟩

theorem isDeg_const : ∀ (N : ℕ) (c : ℝ) (d : ℕ), IsDeg N (fun _ => c) d
  | 0, _, _ => trivial
  | N + 1, c, d => by
    refine ⟨(isDeg_const N c d).congr fun ω => ?_, (isDeg_const N 0 _).congr fun ω => ?_,
      fun _ ω => ?_⟩ <;> simp [cA, cB]

theorem isDeg_zero_of {N : ℕ} {F : (Fin N → Bool) → ℝ} (h : ∀ ω, F ω = 0) (d : ℕ) :
    IsDeg N F d := (isDeg_const N 0 d).congr fun ω => (h ω).symm

theorem IsDeg.add : ∀ {N : ℕ} {F G : (Fin N → Bool) → ℝ} {d : ℕ}, IsDeg N F d → IsDeg N G d →
    IsDeg N (fun ω => F ω + G ω) d
  | 0, _, _, _, _, _ => trivial
  | N + 1, F, G, d, ⟨hA, hB, h0⟩, ⟨hA', hB', h0'⟩ =>
    ⟨(hA.add hA').congr fun ω => by simp [cA]; ring,
     (hB.add hB').congr fun ω => by simp [cB]; ring,
     fun hd ω => by
      have := h0 hd ω; have := h0' hd ω
      simp only [cB] at *; linarith⟩

theorem IsDeg.mul : ∀ {N : ℕ} {F G : (Fin N → Bool) → ℝ} {d e : ℕ}, IsDeg N F d → IsDeg N G e →
    IsDeg N (fun ω => F ω * G ω) (d + e)
  | 0, _, _, _, _, _, _ => trivial
  | N + 1, F, G, d, e, ⟨hA, hB, h0⟩, ⟨hA', hB', h0'⟩ => by
    refine ⟨?_, ?_, ?_⟩
    · have h1 := hA.mul hA'
      have h2 := (hB.mul hB').mono (show d - 1 + (e - 1) ≤ d + e by omega)
      refine (h1.add h2).congr fun ω => ?_
      simp only [cA, cB]; ring
    · have t1 : IsDeg N (fun ω => cA F ω * cB G ω) (d + e - 1) := by
        rcases Nat.eq_zero_or_pos e with he | he
        · exact isDeg_zero_of (fun ω => by rw [h0' he ω, mul_zero]) _
        · exact (hA.mul hB').mono (by omega)
      have t2 : IsDeg N (fun ω => cB F ω * cA G ω) (d + e - 1) := by
        rcases Nat.eq_zero_or_pos d with hd | hd
        · exact isDeg_zero_of (fun ω => by rw [h0 hd ω, zero_mul]) _
        · exact (hB.mul hA').mono (by omega)
      refine (t1.add t2).congr fun ω => ?_
      simp only [cA, cB]; ring
    · intro hde ω
      have a := h0 (by omega) ω
      have b := h0' (by omega) ω
      have : cB (fun ω => F ω * G ω) ω = cA F ω * cB G ω + cB F ω * cA G ω := by
        simp only [cA, cB]; ring
      rw [this, a, b]; ring

theorem IsDeg.const_mul {N : ℕ} {F : (Fin N → Bool) → ℝ} {d : ℕ} (h : IsDeg N F d) (c : ℝ) :
    IsDeg N (fun ω => c * F ω) d :=
  ((isDeg_const N c 0).mul h).congr (fun _ => rfl) |>.mono (by omega)

theorem isDeg_sum {N : ℕ} {ι : Type*} (s : Finset ι) (f : ι → (Fin N → Bool) → ℝ) (d : ℕ)
    (h : ∀ i ∈ s, IsDeg N (f i) d) : IsDeg N (fun ω => ∑ i ∈ s, f i ω) d := by
  classical
  induction s using Finset.induction_on with
  | empty => exact isDeg_zero_of (fun ω => by simp) d
  | insert a s ha ih =>
    refine ((h a (mem_insert_self a s)).add (ih fun i hi => h i (mem_insert_of_mem hi))).congr
      fun ω => ?_
    rw [sum_insert ha]

theorem isDeg_prod {N : ℕ} {ι : Type*} (s : Finset ι) (f : ι → (Fin N → Bool) → ℝ) (d : ι → ℕ)
    (h : ∀ i ∈ s, IsDeg N (f i) (d i)) : IsDeg N (fun ω => ∏ i ∈ s, f i ω) (∑ i ∈ s, d i) := by
  classical
  induction s using Finset.induction_on with
  | empty => exact (isDeg_const N 1 0).congr fun ω => by simp
  | insert a s ha ih =>
    refine (((h a (mem_insert_self a s)).mul (ih fun i hi => h i (mem_insert_of_mem hi))).congr
      fun ω => ?_).mono (by rw [sum_insert ha])
    rw [prod_insert ha]

/-- A coin has degree `1`. -/
theorem isDeg_coin : ∀ {N : ℕ} (i : Fin N), IsDeg N (fun ω => (sgn (ω i) : ℝ)) 1
  | 0, i => i.elim0
  | N + 1, i => by
    refine Fin.cases ?_ (fun i' => ?_) i
    · refine ⟨isDeg_zero_of (fun ω => by simp [cA]) 1, (isDeg_const N 1 0).congr fun ω => ?_,
        fun h => absurd h one_ne_zero⟩
      simp [cB]
    · refine ⟨(isDeg_coin i').congr fun ω => ?_, isDeg_zero_of (fun ω => by simp [cB]) _,
        fun h => absurd h one_ne_zero⟩
      simp [cA]

/-- Characters: `deg χ_S ≤ |S|`. -/
theorem isDeg_chi {N : ℕ} (S : Finset (Fin N)) : IsDeg N (fun ω => (chi S ω : ℝ)) S.card := by
  have := isDeg_prod S (fun i ω => (sgn (ω i) : ℝ)) (fun _ => 1) (fun i _ => isDeg_coin i)
  simpa [chi] using this

/-- Walsh-coefficient degree implies the recursive degree. -/
theorem isDeg_of_coeff {N : ℕ} (F : (Fin N → Bool) → ℝ) (d : ℕ)
    (hF : ∀ S : Finset (Fin N), d < S.card → coeff F S = 0) : IsDeg N F d := by
  refine (isDeg_sum univ (fun S ω => coeff F S * chi S ω) d fun S _ => ?_).congr
    fun ω => (walsh_expansion F ω).symm
  by_cases h : S.card ≤ d
  · exact ((isDeg_chi S).const_mul _).mono h
  · exact isDeg_zero_of (fun ω => by rw [hF S (by omega), zero_mul]) d

/-! ## Bonami's hypercontractive inequality -/

theorem avg_succ {N : ℕ} (G : (Fin (N + 1) → Bool) → ℝ) :
    avg G = (avg (fun ω => G (Fin.cons true ω)) + avg (fun ω => G (Fin.cons false ω))) / 2 := by
  unfold avg
  rw [QE.Prob.sum_cons, Fintype.sum_bool]
  simp only [Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]
  push_cast
  rw [pow_succ]
  field_simp

theorem avg_mul_sq_le {β : Type*} [Fintype β] (f g : β → ℝ) :
    avg (fun b => f b * g b) ^ 2 ≤ avg (fun b => f b ^ 2) * avg (fun b => g b ^ 2) := by
  unfold avg
  rw [div_pow, div_mul_div_comm, ← sq]
  exact div_le_div_of_nonneg_right (sum_mul_sq_le_sq_mul_sq _ _ _) (sq_nonneg _)

theorem pow_three_mul_pow (d : ℕ) : (3 : ℝ) ^ (d + 1) * 3 ^ d = 3 * 9 ^ d := by
  rw [show (9 : ℝ) = 3 ^ 2 by norm_num, ← pow_mul, pow_succ]; ring_nf

/-- **Bonami's lemma** (hypercontractivity `L² → L⁴` for coin polynomials):
`E F⁴ ≤ 9^d (E F²)²` when `F` has degree `≤ d`. -/
theorem bonami_avg : ∀ (N : ℕ) (F : (Fin N → Bool) → ℝ) (d : ℕ), IsDeg N F d →
    avg (fun ω => F ω ^ 4) ≤ 9 ^ d * avg (fun ω => F ω ^ 2) ^ 2
  | 0, F, d, _ => by
    have hu : ∀ ω : Fin 0 → Bool, ω = default := fun ω => Subsingleton.elim _ _
    unfold avg
    simp only [Fintype.card_fun, Fintype.card_fin, pow_zero, Nat.cast_one, div_one]
    rw [Fintype.sum_unique, Fintype.sum_unique]
    have : (1 : ℝ) ≤ 9 ^ d := one_le_pow₀ (by norm_num)
    nlinarith [pow_two_nonneg (F default ^ 2)]
  | N + 1, F, d, ⟨hA, hB, h0⟩ => by
    set A := cA F
    set B := cB F
    have e4 : avg (fun ω => F ω ^ 4) =
        avg (fun ω => A ω ^ 4) + 6 * avg (fun ω => A ω ^ 2 * B ω ^ 2) + avg (fun ω => B ω ^ 4) := by
      rw [avg_succ]; simp_rw [cons_true, cons_false]
      rw [← avg_add]
      have : (fun ω => (A ω + B ω) ^ 4 + (A ω - B ω) ^ 4) =
          fun ω => 2 * (A ω ^ 4 + 6 * (A ω ^ 2 * B ω ^ 2) + B ω ^ 4) := by funext ω; ring
      rw [this, avg_const_mul, avg_add, avg_add, avg_const_mul]; ring
    have e2 : avg (fun ω => F ω ^ 2) = avg (fun ω => A ω ^ 2) + avg (fun ω => B ω ^ 2) := by
      rw [avg_succ]; simp_rw [cons_true, cons_false]
      rw [← avg_add]
      have : (fun ω => (A ω + B ω) ^ 2 + (A ω - B ω) ^ 2) =
          fun ω => 2 * (A ω ^ 2 + B ω ^ 2) := by funext ω; ring
      rw [this, avg_const_mul, avg_add]; ring
    have hα : 0 ≤ avg (fun ω => A ω ^ 2) := avg_nonneg fun _ => sq_nonneg _
    have hβ : 0 ≤ avg (fun ω => B ω ^ 2) := avg_nonneg fun _ => sq_nonneg _
    rw [e4, e2]
    rcases Nat.eq_zero_or_pos d with hd | hd
    · have hB0 : ∀ ω, B ω = 0 := h0 hd
      simp only [hB0]
      have := bonami_avg N A d hA
      simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero, add_zero,
        avg_const] at this ⊢
      linarith
    · obtain ⟨d', rfl⟩ : ∃ d', d = d' + 1 := ⟨d - 1, by omega⟩
      have iA := bonami_avg N A (d' + 1) hA
      have iB := bonami_avg N B d' (by simpa using hB)
      set α := avg (fun ω => A ω ^ 2)
      set β := avg (fun ω => B ω ^ 2)
      have hu : (0 : ℝ) ≤ 9 ^ d' := by positivity
      have cs := avg_mul_sq_le (fun ω => A ω ^ 2) (fun ω => B ω ^ 2)
      simp only [← pow_mul] at cs
      have hcs : avg (fun ω => A ω ^ 2 * B ω ^ 2) ≤ 3 * 9 ^ d' * (α * β) := by
        have hb : 0 ≤ 3 * 9 ^ d' * (α * β) := by positivity
        refine (abs_le_of_sq_le_sq' ?_ hb).2
        calc avg (fun ω => A ω ^ 2 * B ω ^ 2) ^ 2
            ≤ avg (fun ω => A ω ^ 4) * avg (fun ω => B ω ^ 4) := cs
          _ ≤ (9 ^ (d' + 1) * α ^ 2) * (9 ^ d' * β ^ 2) :=
              mul_le_mul iA iB (avg_nonneg fun _ => by positivity) (by positivity)
          _ = (3 * 9 ^ d' * (α * β)) ^ 2 := by rw [pow_succ]; ring
      have h9 : (9 : ℝ) ^ (d' + 1) = 9 * 9 ^ d' := by rw [pow_succ]; ring
      rw [h9] at iA ⊢
      nlinarith [mul_nonneg hu (sq_nonneg β), mul_nonneg hu (mul_nonneg hα hβ)]

/-- **Bonami's lemma**, with the Walsh expectation. -/
theorem bonami {N : ℕ} (F : (Fin N → Bool) → ℝ) {d : ℕ} (hF : IsDeg N F d) :
    E (fun ω => F ω ^ 4) ≤ 9 ^ d * E (fun ω => F ω ^ 2) ^ 2 := by
  rw [← avg_eq_E, ← avg_eq_E]; exact bonami_avg N F d hF

/-- Eighth moment: `E F⁸ ≤ 9^{4d} (E F²)⁴`. -/
theorem avg_eight_le {N : ℕ} (F : (Fin N → Bool) → ℝ) {d : ℕ} (hF : IsDeg N F d) :
    avg (fun ω => F ω ^ 8) ≤ 9 ^ (4 * d) * avg (fun ω => F ω ^ 2) ^ 4 := by
  have h2 : IsDeg N (fun ω => F ω ^ 2) (d + d) := (hF.mul hF).congr fun ω => by ring
  have b1 := bonami_avg N _ _ h2
  have b2 := bonami_avg N F d hF
  have e : (fun ω => F ω ^ 8) = fun ω => (F ω ^ 2) ^ 4 := by funext ω; ring
  have e' : (fun ω => (F ω ^ 2) ^ 2) = fun ω => F ω ^ 4 := by funext ω; ring
  rw [e]; rw [e'] at b1
  have h4 : 0 ≤ avg (fun ω => F ω ^ 4) := avg_nonneg fun _ => by positivity
  calc avg (fun ω => (F ω ^ 2) ^ 4) ≤ 9 ^ (d + d) * avg (fun ω => F ω ^ 4) ^ 2 := b1
    _ ≤ 9 ^ (d + d) * (9 ^ d * avg (fun ω => F ω ^ 2) ^ 2) ^ 2 := by
        gcongr
    _ = 9 ^ (4 * d) * avg (fun ω => F ω ^ 2) ^ 4 := by ring

end QE.Chaos.Bon

namespace QE.Chaos.Bon

open Finset QE.OpenSto.Walsh QE.Chaos

/-! ## Multilinear polynomials -/

/-- Multilinear polynomial with coefficients `a`, evaluated at `x`. -/
def mlEval {n : ℕ} (a : Finset (Fin n) → ℝ) (x : Fin n → ℝ) : ℝ := ∑ S, a S * ∏ i ∈ S, x i

/-- Influence of coordinate `j`. -/
def infl {n : ℕ} (a : Finset (Fin n) → ℝ) (j : Fin n) : ℝ := ∑ S ∈ univ.filter (j ∈ ·), a S ^ 2

theorem infl_nonneg {n : ℕ} (a : Finset (Fin n) → ℝ) (j : Fin n) : 0 ≤ infl a j :=
  sum_nonneg fun _ _ => sq_nonneg _

/-- Degree of `a`: `a S = 0` whenever `d < |S|`. -/
def DegLe {n : ℕ} (a : Finset (Fin n) → ℝ) (d : ℕ) : Prop := ∀ S, d < S.card → a S = 0

theorem isDeg_mlEval {N n : ℕ} (a : Finset (Fin n) → ℝ) {d : ℕ} (ha : DegLe a d)
    (Y : Fin n → (Fin N → Bool) → ℝ) (hY : ∀ j, IsDeg N (Y j) 1) :
    IsDeg N (fun η => mlEval a (fun j => Y j η)) d := by
  refine isDeg_sum univ (fun S η => a S * ∏ i ∈ S, Y i η) d fun S _ => ?_
  by_cases h : S.card ≤ d
  · have := (isDeg_prod S Y (fun _ => 1) fun i _ => hY i).const_mul (a S)
    simp only [sum_const, smul_eq_mul, mul_one] at this
    exact this.mono h
  · exact isDeg_zero_of (fun η => by rw [ha S (by omega), zero_mul]) d

/-! ## Block variables on `Ω = Fin n → Fin q → Bool` -/

/-- Centred, normalised block variables of coin-degree one. -/
structure BlockVar (n q : ℕ) (X : Fin n → (Fin q → Bool) → ℝ) : Prop where
  mean : ∀ j, avg (X j) = 0
  var : ∀ j, avg (fun b => X j b ^ 2) = 1
  deg : ∀ j, IsDeg (n * q) (fun η => X j ((unblock n q).symm η j)) 1

theorem unblock_symm_apply (n q : ℕ) (η : Fin (n * q) → Bool) (j : Fin n) (r : Fin q) :
    (unblock n q).symm η j r = η (finProdFinEquiv (j, r)) := by
  rw [← unblock_apply n q ((unblock n q).symm η) j r, Equiv.apply_symm_apply]

theorem avg_prod_sets {n q : ℕ} (X : Fin n → (Fin q → Bool) → ℝ) (h0 : ∀ j, avg (X j) = 0)
    (h2 : ∀ j, avg (fun b => X j b ^ 2) = 1) (S T : Finset (Fin n)) :
    avg (fun ω : Fin n → Fin q → Bool => (∏ i ∈ S, X i (ω i)) * ∏ i ∈ T, X i (ω i)) =
      if S = T then 1 else 0 := by
  have e : ∀ ω : Fin n → Fin q → Bool, (∏ i ∈ S, X i (ω i)) * ∏ i ∈ T, X i (ω i) =
      ∏ i, (fun i b => (if i ∈ S then X i b else 1) * (if i ∈ T then X i b else 1)) i (ω i) := by
    intro ω
    rw [prod_mul_distrib, prod_ite_mem, prod_ite_mem, univ_inter, univ_inter]
  rw [show (fun ω : Fin n → Fin q → Bool => (∏ i ∈ S, X i (ω i)) * ∏ i ∈ T, X i (ω i)) =
      fun ω => ∏ i, (fun i b => (if i ∈ S then X i b else 1) * (if i ∈ T then X i b else 1)) i (ω i)
      from funext e]
  have hp := avg_prod (ι := Fin n) (β := Fin q → Bool)
    (fun i b => (if i ∈ S then X i b else 1) * (if i ∈ T then X i b else 1))
  refine Eq.trans (by convert hp using 2) ?_
  split_ifs with hST
  · subst hST
    apply prod_eq_one; intro i _
    by_cases hi : i ∈ S
    · simp only [hi, ite_true]; simpa [sq] using h2 i
    · simp only [hi, ite_false, mul_one]; exact avg_const 1
  · obtain ⟨i, hi⟩ : ∃ i, (i ∈ S ∧ i ∉ T) ∨ (i ∉ S ∧ i ∈ T) := by
      by_contra hc
      apply hST; ext i
      by_cases h1 : i ∈ S <;> by_cases h2 : i ∈ T <;> simp_all
    apply prod_eq_zero (mem_univ i)
    rcases hi with ⟨h1, h2'⟩ | ⟨h1, h2'⟩
    · simp only [h1, h2', ite_true, ite_false, mul_one]; exact h0 i
    · simp only [h1, h2', ite_true, ite_false, one_mul]; exact h0 i

/-- Orthonormality: `E[Q_a Q_b] = ∑ a_S b_S`. -/
theorem avg_mlEval_mul {n q : ℕ} (X : Fin n → (Fin q → Bool) → ℝ) (h0 : ∀ j, avg (X j) = 0)
    (h2 : ∀ j, avg (fun b => X j b ^ 2) = 1) (a b : Finset (Fin n) → ℝ) :
    avg (fun ω : Fin n → Fin q → Bool => mlEval a (fun j => X j (ω j)) * mlEval b (fun j => X j (ω j))) =
      ∑ S, a S * b S := by
  unfold mlEval
  simp_rw [sum_mul_sum]
  rw [avg_sum]; simp_rw [avg_sum]
  have : ∀ S T : Finset (Fin n), avg (fun ω : Fin n → Fin q → Bool =>
      (a S * ∏ i ∈ S, X i (ω i)) * (b T * ∏ i ∈ T, X i (ω i))) = if S = T then a S * b S else 0 := by
    intro S T
    have e : (fun ω : Fin n → Fin q → Bool => (a S * ∏ i ∈ S, X i (ω i)) * (b T * ∏ i ∈ T, X i (ω i)))
        = fun ω => (a S * b T) * ((∏ i ∈ S, X i (ω i)) * ∏ i ∈ T, X i (ω i)) := by
      funext ω; ring
    rw [e, avg_const_mul, avg_prod_sets X h0 h2]
    split_ifs with h <;> simp [h]
  simp_rw [this, sum_ite_eq, mem_univ, ite_true]

theorem avg_mlEval_sq {n q : ℕ} (X : Fin n → (Fin q → Bool) → ℝ) (h0 : ∀ j, avg (X j) = 0)
    (h2 : ∀ j, avg (fun b => X j b ^ 2) = 1) (a : Finset (Fin n) → ℝ) :
    avg (fun ω : Fin n → Fin q → Bool => mlEval a (fun j => X j (ω j)) ^ 2) = ∑ S, a S ^ 2 := by
  simp_rw [sq]; exact avg_mlEval_mul X h0 h2 a a

/-- Transfer of an average on blocks to the `n q` fine coins. -/
theorem avg_block_eq {n q : ℕ} (f : (Fin n → Fin q → Bool) → ℝ) :
    avg f = avg (fun η => f ((unblock n q).symm η)) := (avg_comp_equiv _ f).symm

theorem isDeg_hyb {n q : ℕ} {X : Fin n → (Fin q → Bool) → ℝ} (hX : BlockVar n q X)
    (a : Finset (Fin n) → ℝ) {d : ℕ} (ha : DegLe a d) :
    IsDeg (n * q) (fun η => mlEval a (fun j => X j ((unblock n q).symm η j))) d :=
  isDeg_mlEval a ha (fun j η => X j ((unblock n q).symm η j)) hX.deg

/-- **Bonami for block polynomials.** -/
theorem bonami_block {n q : ℕ} {X : Fin n → (Fin q → Bool) → ℝ} (hX : BlockVar n q X)
    (a : Finset (Fin n) → ℝ) {d : ℕ} (ha : DegLe a d) :
    avg (fun ω : Fin n → Fin q → Bool => mlEval a (fun j => X j (ω j)) ^ 4) ≤ 9 ^ d * (∑ S, a S ^ 2) ^ 2 := by
  rw [← avg_mlEval_sq X hX.mean hX.var a, avg_block_eq, avg_block_eq (fun ω => _ ^ 2)]
  exact bonami_avg _ _ d (isDeg_hyb hX a ha)

/-- Eighth moment of block polynomials. -/
theorem avg_eight_block {n q : ℕ} {X : Fin n → (Fin q → Bool) → ℝ} (hX : BlockVar n q X)
    (a : Finset (Fin n) → ℝ) {d : ℕ} (ha : DegLe a d) :
    avg (fun ω : Fin n → Fin q → Bool => mlEval a (fun j => X j (ω j)) ^ 8) ≤ 9 ^ (4 * d) * (∑ S, a S ^ 2) ^ 4 := by
  rw [← avg_mlEval_sq X hX.mean hX.var a, avg_block_eq, avg_block_eq (fun ω => _ ^ 2)]
  exact avg_eight_le _ (isDeg_hyb hX a ha)

end QE.Chaos.Bon

namespace QE.Chaos.Bon

open Finset QE.OpenSto.Walsh QE.Chaos Set

/-! ## Taylor's theorem in the form used by the swapping argument -/

theorem taylor_abs_le (Ψ : ℝ → ℝ) (k : ℕ) (hΨ : ContDiff ℝ ((k : WithTop ℕ∞) + 1) Ψ) {B : ℝ}
    (hB : ∀ x, |iteratedDeriv (k + 1) Ψ x| ≤ B) (x₀ h : ℝ) :
    |Ψ (x₀ + h) - ∑ i ∈ Finset.range (k + 1), iteratedDeriv i Ψ x₀ * h ^ i / (i.factorial : ℝ)| ≤
      B * |h| ^ (k + 1) / ((k + 1).factorial : ℝ) := by
  by_cases h0 : h = 0
  · subst h0
    rw [sum_range_succ']
    simp
  have hx : x₀ ≠ x₀ + h := by intro e; apply h0; linarith
  obtain ⟨x', -, hx'⟩ := taylor_mean_remainder_lagrange_iteratedDeriv hx hΨ.contDiffOn
  have hT : taylorWithinEval Ψ k (uIcc x₀ (x₀ + h)) x₀ (x₀ + h) =
      ∑ i ∈ Finset.range (k + 1), iteratedDeriv i Ψ x₀ * h ^ i / (i.factorial : ℝ) := by
    rw [taylor_within_apply]
    apply sum_congr rfl; intro i hi
    rw [iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_uIcc hx)
      (hΨ.contDiffAt.of_le ?_) left_mem_uIcc]
    · simp only [smul_eq_mul, add_sub_cancel_left]; ring
    · have := Finset.mem_range.mp hi
      exact_mod_cast (show (i : WithTop ℕ∞) ≤ (k : WithTop ℕ∞) + 1 by
        exact_mod_cast (show i ≤ k + 1 by omega))
  rw [← hT, hx', add_sub_cancel_left, abs_div, abs_mul, abs_pow]
  have hf : (0 : ℝ) < ((k + 1).factorial : ℝ) := by positivity
  rw [abs_of_pos hf]
  gcongr
  exact hB x'

/-- **One Lindeberg swap, fourth order.** Two variables with the same first three moments. -/
theorem swap4 {β : Type*} [Fintype β] [Nonempty β] (Ψ : ℝ → ℝ) (hΨ : ContDiff ℝ 4 Ψ) {B : ℝ}
    (hB : ∀ x, |iteratedDeriv 4 Ψ x| ≤ B) (X Z : β → ℝ) (h1 : avg X = avg Z)
    (h2 : avg (fun b => X b ^ 2) = avg (fun b => Z b ^ 2))
    (h3 : avg (fun b => X b ^ 3) = avg (fun b => Z b ^ 3)) (R D : ℝ) :
    |avg (fun b => Ψ (R + X b * D)) - avg (fun b => Ψ (R + Z b * D))| ≤
      B * D ^ 4 * (avg (fun b => X b ^ 4) + avg (fun b => Z b ^ 4)) / 24 := by
  have hΨ' : ContDiff ℝ (((3 : ℕ) : WithTop ℕ∞) + 1) Ψ := by
    convert hΨ using 2; norm_num
  set c : ℕ → ℝ := fun i => iteratedDeriv i Ψ R
  let P : ℝ → ℝ := fun x => ∑ i ∈ Finset.range 4, c i * (x * D) ^ i / (i.factorial : ℝ)
  have hP : ∀ x, P x = c 0 + (c 1 * D) * x + (c 2 * D ^ 2 / 2) * x ^ 2 + (c 3 * D ^ 3 / 6) * x ^ 3 := by
    intro x; simp only [P, sum_range_succ, sum_range_zero, Nat.factorial]; push_cast; ring
  have hrem : ∀ x, |Ψ (R + x * D) - P x| ≤ B * D ^ 4 * x ^ 4 / 24 := by
    intro x
    have := taylor_abs_le Ψ 3 hΨ' (by simpa using hB) R (x * D)
    simp only [Nat.factorial] at this
    have e : |x * D| ^ (3 + 1) = D ^ 4 * x ^ 4 := by
      rw [show 3 + 1 = 4 by rfl, pow_abs, abs_of_nonneg (by positivity)]; ring
    rw [e] at this
    calc |Ψ (R + x * D) - P x| = _ := rfl
      _ ≤ _ := this
      _ = B * D ^ 4 * x ^ 4 / 24 := by norm_num [Nat.factorial]; ring
  have avgP : ∀ Y : β → ℝ, avg (fun b => P (Y b)) =
      c 0 + (c 1 * D) * avg Y + (c 2 * D ^ 2 / 2) * avg (fun b => Y b ^ 2) +
        (c 3 * D ^ 3 / 6) * avg (fun b => Y b ^ 3) := by
    intro Y
    simp_rw [hP]
    rw [avg_add, avg_add, avg_add, avg_const, avg_const_mul, avg_const_mul, avg_const_mul]
  have eX : avg (fun b => Ψ (R + X b * D)) =
      avg (fun b => Ψ (R + X b * D) - P (X b)) + avg (fun b => P (X b)) := by
    rw [← avg_add]; congr 1; funext b; ring
  have eZ : avg (fun b => Ψ (R + Z b * D)) =
      avg (fun b => Ψ (R + Z b * D) - P (Z b)) + avg (fun b => P (Z b)) := by
    rw [← avg_add]; congr 1; funext b; ring
  rw [eX, eZ, avgP X, avgP Z, h1, h2, h3]
  have bX := (abs_avg_le (fun b => Ψ (R + X b * D) - P (X b))).trans
    (avg_mono fun b => hrem (X b))
  have bZ := (abs_avg_le (fun b => Ψ (R + Z b * D) - P (Z b))).trans
    (avg_mono fun b => hrem (Z b))
  rw [show (fun b => B * D ^ 4 * X b ^ 4 / 24) = fun b => (B * D ^ 4 / 24) * X b ^ 4 from
    funext fun b => by ring, avg_const_mul] at bX
  rw [show (fun b => B * D ^ 4 * Z b ^ 4 / 24) = fun b => (B * D ^ 4 / 24) * Z b ^ 4 from
    funext fun b => by ring, avg_const_mul] at bZ
  calc _ = |avg (fun b => Ψ (R + X b * D) - P (X b)) - avg (fun b => Ψ (R + Z b * D) - P (Z b))| := by
        congr 1; ring
    _ ≤ |avg (fun b => Ψ (R + X b * D) - P (X b))| + |avg (fun b => Ψ (R + Z b * D) - P (Z b))| :=
        abs_sub _ _
    _ ≤ _ := by linarith

/-- **One Lindeberg swap, third order.** -/
theorem swap3 {β : Type*} [Fintype β] [Nonempty β] (Ψ : ℝ → ℝ) (hΨ : ContDiff ℝ 3 Ψ) {B : ℝ}
    (hB : ∀ x, |iteratedDeriv 3 Ψ x| ≤ B) (X Z : β → ℝ) (h1 : avg X = avg Z)
    (h2 : avg (fun b => X b ^ 2) = avg (fun b => Z b ^ 2)) (R D : ℝ) :
    |avg (fun b => Ψ (R + X b * D)) - avg (fun b => Ψ (R + Z b * D))| ≤
      B * |D| ^ 3 * (avg (fun b => |X b| ^ 3) + avg (fun b => |Z b| ^ 3)) / 6 := by
  have hΨ' : ContDiff ℝ (((2 : ℕ) : WithTop ℕ∞) + 1) Ψ := by
    convert hΨ using 2; norm_num
  set c : ℕ → ℝ := fun i => iteratedDeriv i Ψ R
  let P : ℝ → ℝ := fun x => ∑ i ∈ Finset.range 3, c i * (x * D) ^ i / (i.factorial : ℝ)
  have hP : ∀ x, P x = c 0 + (c 1 * D) * x + (c 2 * D ^ 2 / 2) * x ^ 2 := by
    intro x; simp only [P, sum_range_succ, sum_range_zero, Nat.factorial]; push_cast; ring
  have hrem : ∀ x, |Ψ (R + x * D) - P x| ≤ B * |D| ^ 3 * |x| ^ 3 / 6 := by
    intro x
    have := taylor_abs_le Ψ 2 hΨ' (by simpa using hB) R (x * D)
    simp only [Nat.factorial] at this
    have e : |x * D| ^ (2 + 1) = |D| ^ 3 * |x| ^ 3 := by
      rw [abs_mul]; ring
    rw [e] at this
    calc |Ψ (R + x * D) - P x| = _ := rfl
      _ ≤ _ := this
      _ = B * |D| ^ 3 * |x| ^ 3 / 6 := by norm_num [Nat.factorial]; ring
  have avgP : ∀ Y : β → ℝ, avg (fun b => P (Y b)) =
      c 0 + (c 1 * D) * avg Y + (c 2 * D ^ 2 / 2) * avg (fun b => Y b ^ 2) := by
    intro Y
    simp_rw [hP]
    rw [avg_add, avg_add, avg_const, avg_const_mul, avg_const_mul]
  have eX : avg (fun b => Ψ (R + X b * D)) =
      avg (fun b => Ψ (R + X b * D) - P (X b)) + avg (fun b => P (X b)) := by
    rw [← avg_add]; congr 1; funext b; ring
  have eZ : avg (fun b => Ψ (R + Z b * D)) =
      avg (fun b => Ψ (R + Z b * D) - P (Z b)) + avg (fun b => P (Z b)) := by
    rw [← avg_add]; congr 1; funext b; ring
  rw [eX, eZ, avgP X, avgP Z, h1, h2]
  have bX := (abs_avg_le (fun b => Ψ (R + X b * D) - P (X b))).trans
    (avg_mono fun b => hrem (X b))
  have bZ := (abs_avg_le (fun b => Ψ (R + Z b * D) - P (Z b))).trans
    (avg_mono fun b => hrem (Z b))
  rw [show (fun b => B * |D| ^ 3 * |X b| ^ 3 / 6) = fun b => (B * |D| ^ 3 / 6) * |X b| ^ 3 from
    funext fun b => by ring, avg_const_mul] at bX
  rw [show (fun b => B * |D| ^ 3 * |Z b| ^ 3 / 6) = fun b => (B * |D| ^ 3 / 6) * |Z b| ^ 3 from
    funext fun b => by ring, avg_const_mul] at bZ
  calc _ = |avg (fun b => Ψ (R + X b * D) - P (X b)) - avg (fun b => Ψ (R + Z b * D) - P (Z b))| := by
        congr 1; ring
    _ ≤ |avg (fun b => Ψ (R + X b * D) - P (X b))| + |avg (fun b => Ψ (R + Z b * D) - P (Z b))| :=
        abs_sub _ _
    _ ≤ _ := by linarith

end QE.Chaos.Bon

namespace QE.Chaos.Bon

open Finset QE.OpenSto.Walsh QE.Chaos

/-! ## Splitting a multilinear polynomial along one variable -/

/-- Terms not containing `j`. -/
def rest {n : ℕ} (a : Finset (Fin n) → ℝ) (j : Fin n) (S : Finset (Fin n)) : ℝ :=
  if j ∈ S then 0 else a S

/-- The partial derivative `∂_j`: coefficient of `x_j`. -/
def dpart {n : ℕ} (a : Finset (Fin n) → ℝ) (j : Fin n) (S : Finset (Fin n)) : ℝ :=
  if j ∈ S then 0 else a (insert j S)

theorem sum_mem_eq {n : ℕ} (j : Fin n) (g : Finset (Fin n) → ℝ) :
    ∑ S ∈ univ.filter (j ∈ ·), g S = ∑ T ∈ univ.filter (j ∉ ·), g (insert j T) := by
  apply sum_nbij' (fun S => S.erase j) (fun T => insert j T)
  · intro S _; simp
  · intro T _; simp
  · intro S hS; simp only [mem_filter, mem_univ, true_and] at hS; exact insert_erase hS
  · intro T hT; exact erase_insert (by simpa using hT)
  · intro S hS; simp only [mem_filter, mem_univ, true_and] at hS; rw [insert_erase hS]

theorem mlEval_split {n : ℕ} (a : Finset (Fin n) → ℝ) (j : Fin n) (x : Fin n → ℝ) :
    mlEval a x = mlEval (rest a j) x + x j * mlEval (dpart a j) x := by
  unfold mlEval rest dpart
  rw [← sum_filter_add_sum_filter_not univ (j ∈ ·), add_comm, mul_sum]
  congr 1
  · rw [sum_filter]; apply sum_congr rfl; intro S _; split_ifs <;> simp
  · rw [sum_mem_eq, sum_filter]; apply sum_congr rfl; intro T _
    split_ifs with h
    · simp
    · rw [prod_insert h]; ring

theorem infl_eq {n : ℕ} (a : Finset (Fin n) → ℝ) (j : Fin n) :
    infl a j = ∑ T, dpart a j T ^ 2 := by
  unfold infl dpart
  rw [sum_mem_eq, sum_filter]; apply sum_congr rfl; intro T _; split_ifs <;> simp

theorem degLe_dpart {n : ℕ} {a : Finset (Fin n) → ℝ} {d : ℕ} (ha : DegLe a d) (j : Fin n) :
    DegLe (dpart a j) (d - 1) := by
  intro T hT
  unfold dpart; split_ifs with h
  · rfl
  · exact ha _ (by rw [card_insert_of_notMem h]; omega)

theorem mlEval_congr_off {n : ℕ} (c : Finset (Fin n) → ℝ) (j : Fin n)
    (hc : ∀ S, j ∈ S → c S = 0) {x y : Fin n → ℝ} (hxy : ∀ i, i ≠ j → x i = y i) :
    mlEval c x = mlEval c y := by
  unfold mlEval; apply sum_congr rfl; intro S _
  by_cases h : j ∈ S
  · rw [hc S h]; simp
  · congr 1; apply prod_congr rfl; intro i hi
    exact hxy i (fun e => h (e ▸ hi))

theorem rest_mem {n : ℕ} (a : Finset (Fin n) → ℝ) (j : Fin n) : ∀ S, j ∈ S → rest a j S = 0 :=
  fun S h => by simp [rest, h]

theorem dpart_mem {n : ℕ} (a : Finset (Fin n) → ℝ) (j : Fin n) : ∀ S, j ∈ S → dpart a j S = 0 :=
  fun S h => by simp [dpart, h]

/-! ## Hybrids and the invariance principle -/

/-- Hybrid: blocks `j < k` use `Z`, the others `X`. -/
def hyb {n q : ℕ} (X Z : Fin n → (Fin q → Bool) → ℝ) (k : ℕ) (j : Fin n) : (Fin q → Bool) → ℝ :=
  if (j : ℕ) < k then Z j else X j

theorem blockVar_hyb {n q : ℕ} {X Z : Fin n → (Fin q → Bool) → ℝ} (hX : BlockVar n q X)
    (hZ : BlockVar n q Z) (k : ℕ) : BlockVar n q (hyb X Z k) where
  mean j := by unfold hyb; split_ifs; exacts [hZ.mean j, hX.mean j]
  var j := by unfold hyb; split_ifs; exacts [hZ.var j, hX.var j]
  deg j := by unfold hyb; split_ifs; exacts [hZ.deg j, hX.deg j]

/-- The common reduction of one hybrid step. -/
theorem hyb_step_eq {n q : ℕ} (X Z : Fin n → (Fin q → Bool) → ℝ) (a : Finset (Fin n) → ℝ)
    (Ψ : ℝ → ℝ) (j : Fin n) :
    avg (fun ω : Fin n → Fin q → Bool => Ψ (mlEval a (fun i => hyb X Z j i (ω i)))) -
        avg (fun ω : Fin n → Fin q → Bool => Ψ (mlEval a (fun i => hyb X Z (j + 1) i (ω i)))) =
      avg (fun ω : Fin n → Fin q → Bool =>
        avg (fun b => Ψ (mlEval (rest a j) (fun i => hyb X Z j i (ω i)) +
            X j b * mlEval (dpart a j) (fun i => hyb X Z j i (ω i)))) -
        avg (fun b => Ψ (mlEval (rest a j) (fun i => hyb X Z j i (ω i)) +
            Z j b * mlEval (dpart a j) (fun i => hyb X Z j i (ω i))))) := by
  rw [avg_update j (fun ω => Ψ (mlEval a (fun i => hyb X Z j i (ω i)))),
    avg_update j (fun ω => Ψ (mlEval a (fun i => hyb X Z (j + 1) i (ω i)))), ← avg_sub]
  congr 1; funext ω
  have off : ∀ (k : ℕ) (b : Fin q → Bool) (i : Fin n), i ≠ j →
      hyb X Z k i (Function.update ω j b i) = hyb X Z k i (ω i) := by
    intro k b i hi; rw [Function.update_of_ne hi]
  have off' : ∀ (b : Fin q → Bool) (i : Fin n), i ≠ j →
      hyb X Z (j + 1) i (Function.update ω j b i) = hyb X Z j i (ω i) := by
    intro b i hi
    rw [Function.update_of_ne hi]
    unfold hyb
    have : (i : ℕ) ≠ j := fun e => hi (Fin.ext e)
    by_cases h : (i : ℕ) < j
    · rw [if_pos h, if_pos (by omega)]
    · rw [if_neg h, if_neg (by omega)]
  have hXe : (fun b => Ψ (mlEval a (fun i => hyb X Z j i (Function.update ω j b i)))) =
      fun b => Ψ (mlEval (rest a j) (fun i => hyb X Z j i (ω i)) +
            X j b * mlEval (dpart a j) (fun i => hyb X Z j i (ω i))) := by
    funext b
    rw [mlEval_split a j, mlEval_congr_off _ j (rest_mem a j) (fun i hi => off j b i hi),
      mlEval_congr_off _ j (dpart_mem a j) (fun i hi => off j b i hi)]
    simp [hyb]
  have hZe : (fun b => Ψ (mlEval a (fun i => hyb X Z (j + 1) i (Function.update ω j b i)))) =
      fun b => Ψ (mlEval (rest a j) (fun i => hyb X Z j i (ω i)) +
            Z j b * mlEval (dpart a j) (fun i => hyb X Z j i (ω i))) := by
    funext b
    rw [mlEval_split a j, mlEval_congr_off _ j (rest_mem a j) (fun i hi => off' b i hi),
      mlEval_congr_off _ j (dpart_mem a j) (fun i hi => off' b i hi)]
    simp [hyb]
  rw [hXe, hZe]

theorem hyb_zero {n q : ℕ} (X Z : Fin n → (Fin q → Bool) → ℝ) : hyb X Z 0 = X := by
  funext j; simp [hyb]

theorem hyb_n {n q : ℕ} (X Z : Fin n → (Fin q → Bool) → ℝ) : hyb X Z n = Z := by
  funext j; simp [hyb, j.isLt]

/-- Telescoping over the hybrids. -/
theorem telescope {n : ℕ} (f : ℕ → ℝ) (c : Fin n → ℝ) (h : ∀ j : Fin n, |f j - f (j + 1)| ≤ c j) :
    |f 0 - f n| ≤ ∑ j, c j := by
  have e : f 0 - f n = ∑ k ∈ Finset.range n, (f k - f (k + 1)) := by
    rw [sum_range_sub']
  rw [e]
  refine (abs_sum_le_sum_abs _ _).trans ?_
  rw [← Fin.sum_univ_eq_sum_range (fun k => |f k - f (k + 1)|)]
  exact sum_le_sum fun j _ => h j

/-- **Invariance principle (fourth order).** For two families of block variables with the
same first three moments, `|E Ψ(Q(X)) - E Ψ(Q(Z))| ≤ (B/6) 9^{d-1} ∑_j Inf_j(Q)²`. -/
theorem invariance4 {n q : ℕ} {X Z : Fin n → (Fin q → Bool) → ℝ} (hX : BlockVar n q X)
    (hZ : BlockVar n q Z) (h3 : ∀ j, avg (fun b => X j b ^ 3) = avg (fun b => Z j b ^ 3))
    (h4 : ∀ j, avg (fun b => X j b ^ 4) + avg (fun b => Z j b ^ 4) ≤ 4)
    (a : Finset (Fin n) → ℝ) {d : ℕ} (ha : DegLe a d) (Ψ : ℝ → ℝ) (hΨ : ContDiff ℝ 4 Ψ) {B : ℝ}
    (hB : ∀ x, |iteratedDeriv 4 Ψ x| ≤ B) :
    |avg (fun ω : Fin n → Fin q → Bool => Ψ (mlEval a (fun j => X j (ω j)))) -
      avg (fun ω : Fin n → Fin q → Bool => Ψ (mlEval a (fun j => Z j (ω j))))| ≤
      B / 6 * 9 ^ (d - 1) * ∑ j, infl a j ^ 2 := by
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB 0)
  have key := telescope (fun k => avg (fun ω : Fin n → Fin q → Bool =>
      Ψ (mlEval a (fun i => hyb X Z k i (ω i))))) (fun j => B / 6 * 9 ^ (d - 1) * infl a j ^ 2) ?_
  · simp only [hyb_zero, hyb_n] at key
    rw [mul_sum]; exact key
  intro j
  rw [hyb_step_eq]
  set Y := hyb X Z j
  have hY := blockVar_hyb hX hZ j
  refine (abs_avg_le _).trans ?_
  have hpt : ∀ ω : Fin n → Fin q → Bool,
      |avg (fun b => Ψ (mlEval (rest a j) (fun i => Y i (ω i)) +
            X j b * mlEval (dpart a j) (fun i => Y i (ω i)))) -
        avg (fun b => Ψ (mlEval (rest a j) (fun i => Y i (ω i)) +
            Z j b * mlEval (dpart a j) (fun i => Y i (ω i))))| ≤
      B / 6 * mlEval (dpart a j) (fun i => Y i (ω i)) ^ 4 := by
    intro ω
    refine (swap4 Ψ hΨ hB (X j) (Z j) (by rw [hX.mean, hZ.mean]) (by rw [hX.var, hZ.var]) (h3 j)
      _ _).trans ?_
    have := h4 j
    have hD : 0 ≤ mlEval (dpart a j) (fun i => Y i (ω i)) ^ 4 := by positivity
    nlinarith [mul_nonneg hB0 hD]
  refine (avg_mono hpt).trans ?_
  rw [avg_const_mul]
  have hb := bonami_block hY (dpart a j) (degLe_dpart ha j)
  rw [← infl_eq] at hb
  have : (0 : ℝ) ≤ B / 6 := by positivity
  calc B / 6 * avg (fun ω : Fin n → Fin q → Bool => mlEval (dpart a j) (fun i => Y i (ω i)) ^ 4)
      ≤ B / 6 * (9 ^ (d - 1) * infl a j ^ 2) := mul_le_mul_of_nonneg_left hb this
    _ = _ := by ring

/-- **Invariance principle (third order).** -/
theorem invariance3 {n q : ℕ} {X Z : Fin n → (Fin q → Bool) → ℝ} (hX : BlockVar n q X)
    (hZ : BlockVar n q Z) {C : ℝ}
    (h3 : ∀ j, avg (fun b => |X j b| ^ 3) + avg (fun b => |Z j b| ^ 3) ≤ C)
    (a : Finset (Fin n) → ℝ) {d : ℕ} (ha : DegLe a d) (Ψ : ℝ → ℝ) (hΨ : ContDiff ℝ 3 Ψ) {B : ℝ}
    (hB : ∀ x, |iteratedDeriv 3 Ψ x| ≤ B) :
    |avg (fun ω : Fin n → Fin q → Bool => Ψ (mlEval a (fun j => X j (ω j)))) -
      avg (fun ω : Fin n → Fin q → Bool => Ψ (mlEval a (fun j => Z j (ω j))))| ≤
      B / 6 * C * 3 ^ (d - 1) * ∑ j, infl a j * √(infl a j) := by
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB 0)
  have key := telescope (fun k => avg (fun ω : Fin n → Fin q → Bool =>
      Ψ (mlEval a (fun i => hyb X Z k i (ω i)))))
      (fun j => B / 6 * C * 3 ^ (d - 1) * (infl a j * √(infl a j))) ?_
  · simp only [hyb_zero, hyb_n] at key
    rw [mul_sum]; exact key
  intro j
  rw [hyb_step_eq]
  set Y := hyb X Z j
  have hY := blockVar_hyb hX hZ j
  refine (abs_avg_le _).trans ?_
  set D : (Fin n → Fin q → Bool) → ℝ := fun ω => mlEval (dpart a j) (fun i => Y i (ω i))
  have hpt : ∀ ω : Fin n → Fin q → Bool,
      |avg (fun b => Ψ (mlEval (rest a j) (fun i => Y i (ω i)) +
            X j b * mlEval (dpart a j) (fun i => Y i (ω i)))) -
        avg (fun b => Ψ (mlEval (rest a j) (fun i => Y i (ω i)) +
            Z j b * mlEval (dpart a j) (fun i => Y i (ω i))))| ≤
      B / 6 * C * |D ω| ^ 3 := by
    intro ω
    refine (swap3 Ψ hΨ hB (X j) (Z j) (by rw [hX.mean, hZ.mean]) (by rw [hX.var, hZ.var])
      _ _).trans ?_
    have := h3 j
    have hD : 0 ≤ |D ω| ^ 3 := by positivity
    have : B * |D ω| ^ 3 * (avg (fun b => |X j b| ^ 3) + avg (fun b => |Z j b| ^ 3)) ≤
        B * |D ω| ^ 3 * C := mul_le_mul_of_nonneg_left this (by positivity)
    simp only [D] at this hD ⊢
    linarith
  refine (avg_mono hpt).trans ?_
  rw [avg_const_mul]
  have hC : 0 ≤ C := le_trans (add_nonneg (avg_nonneg fun _ => by positivity)
    (avg_nonneg fun _ => by positivity)) (h3 j)
  -- `E|D|³ ≤ √(E D² E D⁴) ≤ 3^{d-1} Inf √Inf`
  have h2 : avg (fun ω => D ω ^ 2) = infl a j := by
    rw [infl_eq]; exact avg_mlEval_sq Y hY.mean hY.var _
  have h4 := bonami_block hY (dpart a j) (degLe_dpart ha j)
  rw [← infl_eq] at h4
  have cs := avg_mul_sq_le (fun ω => |D ω|) (fun ω => D ω ^ 2)
  have hI := infl_nonneg a j
  have e1 : (fun ω => |D ω| * D ω ^ 2) = fun ω => |D ω| ^ 3 := by
    funext ω; rw [← sq_abs (D ω)]; ring
  have e2 : (fun ω => |D ω| ^ 2) = fun ω => D ω ^ 2 := by funext ω; exact sq_abs _
  have e3 : (fun ω => (D ω ^ 2) ^ 2) = fun ω => D ω ^ 4 := by funext ω; ring
  rw [e1, e2, e3, h2] at cs
  have h3' : avg (fun ω => |D ω| ^ 3) ≤ 3 ^ (d - 1) * (infl a j * √(infl a j)) := by
    have hb : 0 ≤ 3 ^ (d - 1) * (infl a j * √(infl a j)) := by positivity
    refine (abs_le_of_sq_le_sq' ?_ hb).2
    calc avg (fun ω => |D ω| ^ 3) ^ 2 ≤ infl a j * avg (fun ω => D ω ^ 4) := cs
      _ ≤ infl a j * (9 ^ (d - 1) * infl a j ^ 2) := mul_le_mul_of_nonneg_left h4 hI
      _ = (3 ^ (d - 1) * (infl a j * √(infl a j))) ^ 2 := by
        rw [mul_pow, mul_pow, Real.sq_sqrt hI, show (9 : ℝ) = 3 ^ 2 by norm_num, ← pow_mul,
          ← pow_mul, mul_comm (d - 1) 2]; ring
  calc B / 6 * C * avg (fun ω => |D ω| ^ 3) ≤ B / 6 * C * (3 ^ (d - 1) * (infl a j * √(infl a j))) :=
        mul_le_mul_of_nonneg_left h3' (by positivity)
    _ = _ := by ring

end QE.Chaos.Bon

namespace QE.Chaos.Bon

open Finset QE.OpenSto.Walsh QE.Chaos

/-! ## The coarse coin and the normalised block sum -/

/-- The coarse coin: the first fine coin of the block. -/
def coarse {q : ℕ} (hq : 0 < q) (b : Fin q → Bool) : ℝ := sgn (b ⟨0, hq⟩)

/-- The normalised block sum `(∑_r ξ_r)/√q`. -/
def fine (q : ℕ) (b : Fin q → Bool) : ℝ := (∑ r, (sgn (b r) : ℝ)) / √q

theorem sgn_sq' (b : Bool) : (sgn b : ℝ) ^ 2 = 1 := by cases b <;> norm_num [sgn]

theorem coarse_mean {q : ℕ} (hq : 0 < q) : avg (coarse hq) = 0 := by
  rw [avg_eq_E]
  have : coarse hq = fun b => (chi {(⟨0, hq⟩ : Fin q)} b : ℝ) := by
    funext b; simp [coarse, chi]
  rw [this, E_chi]; simp

theorem coarse_pow_even {q : ℕ} (hq : 0 < q) (b : Fin q → Bool) (k : ℕ) :
    coarse hq b ^ (2 * k) = 1 := by
  rw [pow_mul, coarse, sgn_sq', one_pow]

theorem coarse_var {q : ℕ} (hq : 0 < q) : avg (fun b => coarse hq b ^ 2) = 1 := by
  simp_rw [show ∀ b, coarse hq b ^ 2 = 1 from fun b => by simpa using coarse_pow_even hq b 1]
  exact avg_const 1

theorem coarse_cube {q : ℕ} (hq : 0 < q) : avg (fun b => coarse hq b ^ 3) = 0 := by
  have : (fun b => coarse hq b ^ 3) = coarse hq := by
    funext b; rw [pow_succ, show coarse hq b ^ 2 = 1 by simpa using coarse_pow_even hq b 1, one_mul]
  rw [this, coarse_mean]

theorem coarse_four {q : ℕ} (hq : 0 < q) : avg (fun b => coarse hq b ^ 4) = 1 := by
  simp_rw [show ∀ b, coarse hq b ^ 4 = 1 from fun b => by simpa using coarse_pow_even hq b 2]
  exact avg_const 1

theorem coarse_abs3 {q : ℕ} (hq : 0 < q) : avg (fun b => |coarse hq b| ^ 3) = 1 := by
  have : ∀ b, |coarse hq b| ^ 3 = 1 := by
    intro b; unfold coarse; cases b ⟨0, hq⟩ <;> norm_num [sgn]
  simp_rw [this]; exact avg_const 1

/-- Power sums of the block walk. -/
theorem avg_blocksum_pow (q k : ℕ) :
    avg (fun b : Fin q → Bool => (∑ r, (sgn (b r) : ℝ)) ^ k) =
      (∑ b : Fin q → Bool, (QE.Prob.S b : ℝ) ^ k) / 2 ^ q := by
  rw [avg_eq_E]; rfl

theorem fine_pow (q k : ℕ) (b : Fin q → Bool) :
    fine q b ^ k = (∑ r, (sgn (b r) : ℝ)) ^ k / √q ^ k := by rw [fine, div_pow]

theorem fine_mean {q : ℕ} (hq : 0 < q) : avg (fine q) = 0 := by
  have : fine q = fun b => (∑ r, (sgn (b r) : ℝ)) ^ 1 * (1 / √q) := by
    funext b; simp [fine, div_eq_mul_inv]
  rw [this, avg_mul_const, avg_blocksum_pow]
  simp [QE.Prob.sum_S]

theorem fine_var {q : ℕ} (hq : 0 < q) : avg (fun b => fine q b ^ 2) = 1 := by
  simp_rw [fine_pow, div_eq_mul_inv]
  rw [avg_mul_const, avg_blocksum_pow, QE.Prob.sum_S_sq, Real.sq_sqrt (Nat.cast_nonneg _)]
  have : (q : ℝ) ≠ 0 := by exact_mod_cast hq.ne'
  field_simp

theorem fine_cube {q : ℕ} (hq : 0 < q) : avg (fun b => fine q b ^ 3) = 0 := by
  simp_rw [fine_pow, div_eq_mul_inv]
  rw [avg_mul_const, avg_blocksum_pow, QE.Prob.BE.sum_S_cube]; simp

theorem fine_four {q : ℕ} (hq : 0 < q) :
    avg (fun b => fine q b ^ 4) = (3 * (q : ℝ) ^ 2 - 2 * q) / (q : ℝ) ^ 2 := by
  simp_rw [fine_pow, div_eq_mul_inv]
  rw [avg_mul_const, avg_blocksum_pow, QE.Prob.BE.sum_S_four]
  have h4 : √(q : ℝ) ^ 4 = (q : ℝ) ^ 2 := by
    rw [show 4 = 2 * 2 by rfl, pow_mul, Real.sq_sqrt (Nat.cast_nonneg _)]
  rw [h4]
  have : (2 : ℝ) ^ q ≠ 0 := by positivity
  field_simp

theorem fine_four_le {q : ℕ} (hq : 0 < q) : avg (fun b => fine q b ^ 4) ≤ 3 := by
  rw [fine_four hq]
  have : (0 : ℝ) < (q : ℝ) ^ 2 := by positivity
  rw [div_le_iff₀ this]
  have : (0 : ℝ) ≤ q := Nat.cast_nonneg _
  nlinarith

theorem fine_abs3_le {q : ℕ} (hq : 0 < q) : avg (fun b => |fine q b| ^ 3) ≤ √3 := by
  have cs := avg_mul_sq_le (fun b => |fine q b|) (fun b => fine q b ^ 2)
  have e1 : (fun b => |fine q b| * fine q b ^ 2) = fun b => |fine q b| ^ 3 := by
    funext b; rw [← sq_abs (fine q b)]; ring
  have e2 : (fun b => |fine q b| ^ 2) = fun b => fine q b ^ 2 := by funext b; exact sq_abs _
  have e3 : (fun b => (fine q b ^ 2) ^ 2) = fun b => fine q b ^ 4 := by funext b; ring
  rw [e1, e2, e3, fine_var hq] at cs
  refine (abs_le_of_sq_le_sq' ?_ (Real.sqrt_nonneg 3)).2
  rw [Real.sq_sqrt (by norm_num)]
  linarith [fine_four_le hq]

theorem isDeg_coarse {n q : ℕ} (hq : 0 < q) (j : Fin n) :
    IsDeg (n * q) (fun η => coarse hq ((unblock n q).symm η j)) 1 :=
  (isDeg_coin (finProdFinEquiv (j, (⟨0, hq⟩ : Fin q)))).congr fun η => by
    simp [coarse, unblock_symm_apply]

theorem isDeg_fine {n q : ℕ} (j : Fin n) :
    IsDeg (n * q) (fun η => fine q ((unblock n q).symm η j)) 1 :=
  ((isDeg_sum univ (fun r η => (sgn (η (finProdFinEquiv (j, r))) : ℝ)) 1
      fun r _ => isDeg_coin _).const_mul (1 / √q)).congr fun η => by
    simp [fine, unblock_symm_apply, div_eq_inv_mul]

theorem blockVar_coarse {n q : ℕ} (hq : 0 < q) : BlockVar n q (fun _ => coarse hq) where
  mean _ := coarse_mean hq
  var _ := coarse_var hq
  deg j := isDeg_coarse hq j

theorem blockVar_fine {n q : ℕ} (hq : 0 < q) : BlockVar n q (fun _ => fine q) where
  mean _ := fine_mean hq
  var _ := fine_var hq
  deg j := isDeg_fine j

/-! ## Bridges to the coin spaces -/

/-- The coarse side is the uniform coin space `Fin n → Bool`. -/
theorem avg_coarse_eq_E {n q : ℕ} (hq : 0 < q) (G : (Fin n → ℝ) → ℝ) :
    avg (fun ω : Fin n → Fin q → Bool => G (fun j => coarse hq (ω j))) =
      E (fun η : Fin n → Bool => G (fun j => sgn (η j))) :=
  avg_first_coin n q hq (fun η => G (fun j => sgn (η j)))

/-- The fine side is the uniform coin space on `n q` coins, blocks of `q` consecutive coins. -/
theorem avg_fine_eq_E {n q : ℕ} (G : (Fin n → ℝ) → ℝ) :
    avg (fun ω : Fin n → Fin q → Bool => G (fun j => fine q (ω j))) =
      E (fun η : Fin (n * q) → Bool =>
        G (fun j => (∑ r : Fin q, (sgn (η (finProdFinEquiv (j, r))) : ℝ)) / √q)) := by
  rw [E_eq_avg_unblock]
  congr 1; funext ω
  simp [fine, unblock_apply]

/-- The Walsh chaos of order `m` is the multilinear polynomial of its coefficients. -/
theorem chaos_eq_mlEval {n : ℕ} (F : (Fin n → Bool) → ℝ) (m : ℕ) (ω : Fin n → Bool) :
    ∑ S ∈ powersetCard m univ, coeff F S * chi S ω =
      mlEval (fun S => if S.card = m then coeff F S else 0) (fun j => sgn (ω j)) := by
  unfold mlEval chi
  rw [powersetCard_eq_filter, powerset_univ, sum_filter]
  apply sum_congr rfl; intro S _
  by_cases h : S.card = m <;> simp [h]

theorem degLe_chaos {n : ℕ} (F : (Fin n → Bool) → ℝ) (m : ℕ) :
    DegLe (fun S : Finset (Fin n) => if S.card = m then coeff F S else 0) m := by
  intro S hS; exact if_neg (by omega)

/-! ## The invariance principle on the coin spaces -/

/-- **Invariance principle, coins vs normalised block sums, fourth order.** -/
theorem invariance4_coins {n q : ℕ} (hq : 0 < q) (a : Finset (Fin n) → ℝ) {d : ℕ}
    (ha : DegLe a d) (Ψ : ℝ → ℝ) (hΨ : ContDiff ℝ 4 Ψ) {B : ℝ}
    (hB : ∀ x, |iteratedDeriv 4 Ψ x| ≤ B) :
    |E (fun η : Fin n → Bool => Ψ (mlEval a (fun j => sgn (η j)))) -
      E (fun η : Fin (n * q) → Bool =>
        Ψ (mlEval a (fun j => (∑ r : Fin q, (sgn (η (finProdFinEquiv (j, r))) : ℝ)) / √q)))| ≤
      B / 6 * 9 ^ (d - 1) * ∑ j, infl a j ^ 2 := by
  rw [← avg_coarse_eq_E hq (fun x => Ψ (mlEval a x)), ← avg_fine_eq_E (fun x => Ψ (mlEval a x))]
  exact invariance4 (blockVar_coarse hq) (blockVar_fine hq)
    (fun _ => by rw [coarse_cube, fine_cube hq])
    (fun _ => by rw [coarse_four]; linarith [fine_four_le hq]) a ha Ψ hΨ hB

/-- **Invariance principle, coins vs normalised block sums, third order.** -/
theorem invariance3_coins {n q : ℕ} (hq : 0 < q) (a : Finset (Fin n) → ℝ) {d : ℕ}
    (ha : DegLe a d) (Ψ : ℝ → ℝ) (hΨ : ContDiff ℝ 3 Ψ) {B : ℝ}
    (hB : ∀ x, |iteratedDeriv 3 Ψ x| ≤ B) :
    |E (fun η : Fin n → Bool => Ψ (mlEval a (fun j => sgn (η j)))) -
      E (fun η : Fin (n * q) → Bool =>
        Ψ (mlEval a (fun j => (∑ r : Fin q, (sgn (η (finProdFinEquiv (j, r))) : ℝ)) / √q)))| ≤
      B / 6 * (1 + √3) * 3 ^ (d - 1) * ∑ j, infl a j * √(infl a j) := by
  rw [← avg_coarse_eq_E hq (fun x => Ψ (mlEval a x)), ← avg_fine_eq_E (fun x => Ψ (mlEval a x))]
  exact invariance3 (blockVar_coarse hq) (blockVar_fine hq)
    (fun _ => by rw [coarse_abs3]; linarith [fine_abs3_le hq]) a ha Ψ hΨ hB

/-! ## Moments of the fine evaluation (for S-integrability) -/

theorem E_fine_sq {n q : ℕ} (hq : 0 < q) (a : Finset (Fin n) → ℝ) :
    E (fun η : Fin (n * q) → Bool =>
        mlEval a (fun j => (∑ r : Fin q, (sgn (η (finProdFinEquiv (j, r))) : ℝ)) / √q) ^ 2) =
      ∑ S, a S ^ 2 := by
  rw [← avg_fine_eq_E (fun x => mlEval a x ^ 2)]
  exact avg_mlEval_sq _ (blockVar_fine hq).mean (blockVar_fine hq).var a

theorem E_fine_four_le {n q : ℕ} (hq : 0 < q) (a : Finset (Fin n) → ℝ) {d : ℕ} (ha : DegLe a d) :
    E (fun η : Fin (n * q) → Bool =>
        mlEval a (fun j => (∑ r : Fin q, (sgn (η (finProdFinEquiv (j, r))) : ℝ)) / √q) ^ 4) ≤
      9 ^ d * (∑ S, a S ^ 2) ^ 2 := by
  rw [← avg_fine_eq_E (fun x => mlEval a x ^ 4)]
  exact bonami_block (blockVar_fine hq) a ha

theorem E_fine_eight_le {n q : ℕ} (hq : 0 < q) (a : Finset (Fin n) → ℝ) {d : ℕ} (ha : DegLe a d) :
    E (fun η : Fin (n * q) → Bool =>
        mlEval a (fun j => (∑ r : Fin q, (sgn (η (finProdFinEquiv (j, r))) : ℝ)) / √q) ^ 8) ≤
      9 ^ (4 * d) * (∑ S, a S ^ 2) ^ 4 := by
  rw [← avg_fine_eq_E (fun x => mlEval a x ^ 8)]
  exact avg_eight_block (blockVar_fine hq) a ha

theorem E_coin_sq {n : ℕ} (a : Finset (Fin n) → ℝ) :
    E (fun η : Fin n → Bool => mlEval a (fun j => sgn (η j)) ^ 2) = ∑ S, a S ^ 2 := by
  rw [← avg_coarse_eq_E one_pos (fun x => mlEval a x ^ 2)]
  exact avg_mlEval_sq _ (blockVar_coarse (n := n) one_pos).mean
    (blockVar_coarse (n := n) one_pos).var a

theorem E_coin_eight_le {n : ℕ} (a : Finset (Fin n) → ℝ) {d : ℕ} (ha : DegLe a d) :
    E (fun η : Fin n → Bool => mlEval a (fun j => sgn (η j)) ^ 8) ≤
      9 ^ (4 * d) * (∑ S, a S ^ 2) ^ 4 := by
  rw [← avg_coarse_eq_E one_pos (fun x => mlEval a x ^ 8)]
  exact avg_eight_block (blockVar_coarse (q := 1) one_pos) a ha

end QE.Chaos.Bon

/-! # Part C. Loeb integration on the hyperfinite coin space -/


namespace QE.Chaos.Loeb

open QE.NSA Filter MeasureTheory ProbabilityTheory ArchimedeanClass Set
open scoped ENNReal Topology NNReal

/-- The internal function on the hyperfinite coin space presented by functions on
`Fin (n k) → Bool`. -/
def coinFun (n : ℕ → ℕ) (f : ∀ k, (Fin (n k) → Bool) → ℝ) : ℕ → (ℕ → Bool) → ℝ :=
  fun k ω => f k (fun i => ω i)

/-- The internal expectation `E F = [E (f k)]`. -/
def iE (n : ℕ → ℕ) (f : ∀ k, (Fin (n k) → Bool) → ℝ) : ℝ* :=
  Hyperreal.ofSeq (fun k => QE.OpenSto.Walsh.E (f k))

/-- The internal random variable `F = [f k]` on `Ult (ℕ → Bool)`. -/
def iF (n : ℕ → ℕ) (f : ∀ k, (Fin (n k) → Bool) → ℝ) : Ult (ℕ → Bool) → ℝ* :=
  ifun (coinFun n f)

/-- **S-integrability**: `E|F|` finite and `E[|F|; |F| > K] ≈ 0` for every infinite `K`. -/
def SInt (n : ℕ → ℕ) (f : ∀ k, (Fin (n k) → Bool) → ℝ) : Prop :=
  IsFinite (iE n (fun k ω => |f k ω|)) ∧
    ∀ K : ℕ → ℝ, (∀ r : ℝ, ∀ᶠ k in hyperfilter ℕ, r < K k) →
      IsInfinitesimal (iE n (fun k ω => if K k < |f k ω| then |f k ω| else 0))


/-- Shorthand for the Loeb measure of the uniform coin measure. -/
abbrev L (n : ℕ → ℕ) : Measure (Ult (ℕ → Bool)) := (coinMeasure n).loeb

instance (n : ℕ → ℕ) : IsProbabilityMeasure (L n) := coinMeasure_isProbability n

section Basic

variable {n : ℕ → ℕ}

open QE.OpenSto.Walsh in
theorem E_eq_avg {N : ℕ} (X : (Fin N → Bool) → ℝ) : E X = QE.Chaos.avg X :=
  (QE.Chaos.avg_eq_E X).symm

theorem iE_add (f g : ∀ k, (Fin (n k) → Bool) → ℝ) :
    iE n (fun k ω => f k ω + g k ω) = iE n f + iE n g := by
  unfold iE; simp_rw [E_eq_avg, QE.Chaos.avg_add]; rfl

theorem iE_sub (f g : ∀ k, (Fin (n k) → Bool) → ℝ) :
    iE n (fun k ω => f k ω - g k ω) = iE n f - iE n g := by
  unfold iE; simp_rw [E_eq_avg, QE.Chaos.avg_sub]; rfl

theorem iE_neg (f : ∀ k, (Fin (n k) → Bool) → ℝ) :
    iE n (fun k ω => -f k ω) = -iE n f := by
  unfold iE; simp_rw [E_eq_avg, QE.Chaos.avg_neg]; rfl

theorem iE_const_mul (c : ℝ) (f : ∀ k, (Fin (n k) → Bool) → ℝ) :
    iE n (fun k ω => c * f k ω) = (c : ℝ*) * iE n f := by
  unfold iE; simp_rw [E_eq_avg, QE.Chaos.avg_const_mul]; rfl

theorem iE_const (c : ℝ) : iE n (fun _ _ => c) = (c : ℝ*) := by
  unfold iE; simp_rw [E_eq_avg, QE.Chaos.avg_const]; rfl

theorem iE_mono {f g : ∀ k, (Fin (n k) → Bool) → ℝ} (h : ∀ k ω, f k ω ≤ g k ω) :
    iE n f ≤ iE n g := by
  unfold iE
  exact Hyperreal.ofSeq_le_ofSeq.2 (Eventually.of_forall fun k => by
    simp_rw [E_eq_avg]; exact QE.Chaos.avg_mono (h k))

theorem iE_mono_ev {f g : ∀ k, (Fin (n k) → Bool) → ℝ}
    (h : ∀ᶠ k in hyperfilter ℕ, ∀ ω, f k ω ≤ g k ω) : iE n f ≤ iE n g := by
  unfold iE
  exact Hyperreal.ofSeq_le_ofSeq.2 (by
    filter_upwards [h] with k hk
    simp_rw [E_eq_avg]; exact QE.Chaos.avg_mono hk)

theorem iE_nonneg {f : ∀ k, (Fin (n k) → Bool) → ℝ} (h : ∀ k ω, 0 ≤ f k ω) : 0 ≤ iE n f := by
  have := iE_mono (n := n) (f := fun _ _ => 0) (g := f) h
  rwa [iE_const] at this

theorem iE_congr {f g : ∀ k, (Fin (n k) → Bool) → ℝ} (h : ∀ k ω, f k ω = g k ω) :
    iE n f = iE n g := by
  have : f = g := funext fun k => funext fun ω => h k ω
  rw [this]

theorem iF_coe (f : ∀ k, (Fin (n k) → Bool) → ℝ) (u : ℕ → ℕ → Bool) :
    iF n f (u : Ult (ℕ → Bool)) = Hyperreal.ofSeq (fun k => f k (fun i => u k i)) := rfl

theorem measurable_iF (f : ∀ k, (Fin (n k) → Bool) → ℝ) : Measurable (iF n f) :=
  measurable_ifun _

theorem measurable_st_iF (f : ∀ k, (Fin (n k) → Bool) → ℝ) :
    Measurable (fun ω => stdPart (iF n f ω)) :=
  measurable_stdPart.comp (measurable_iF f)

open Classical in
/-- The internal set `{F ∈ P}` presented by predicates. -/
def iSet (n : ℕ → ℕ) (P : ∀ k, (Fin (n k) → Bool) → Prop) : Set (Ult (ℕ → Bool)) :=
  internal (fun k => {ω : ℕ → Bool | P k (fun i => ω i)})

open Classical in
/-- Indicator of an internal predicate. -/
def ind (P : ∀ k, (Fin (n k) → Bool) → Prop) : ∀ k, (Fin (n k) → Bool) → ℝ :=
  fun k ω => if P k ω then 1 else 0

theorem coinExt_restrict (N : ℕ) (ω : Fin N → Bool) : (fun i : Fin N => coinExt N ω i) = ω := by
  funext i; simp [coinExt, i.isLt]

open Classical in
theorem mass_iSet (P : ∀ k, (Fin (n k) → Bool) → Prop) :
    (coinMeasure n).mass (iSet n P) = iE n (ind P) := by
  unfold iSet
  rw [HypMeasure.mass_internal]
  unfold HypMeasure.massOf iE
  congr 1; funext k
  rw [coin_seqMass]
  unfold probU QE.OpenSto.Walsh.E ind
  congr 1
  apply Finset.sum_congr rfl; intro ω _
  simp only [Set.mem_ofPred_eq, coinExt_restrict]

theorem iE_ind_nonneg (P : ∀ k, (Fin (n k) → Bool) → Prop) : 0 ≤ iE n (ind P) :=
  iE_nonneg (fun k ω => by unfold ind; split_ifs <;> norm_num)

theorem iE_ind_le_one (P : ∀ k, (Fin (n k) → Bool) → Prop) : iE n (ind P) ≤ 1 := by
  have := iE_mono (n := n) (f := ind P) (g := fun _ _ => 1)
    (fun k ω => by unfold ind; split_ifs <;> norm_num)
  rwa [iE_const] at this

theorem isFinite_of_abs_le {x : ℝ*} {r : ℝ} (h : |x| ≤ (r : ℝ*)) : IsFinite x :=
  (isFinite_iff_abs_le x).2 ⟨r, h⟩

theorem isFinite_of_bounds {x : ℝ*} {a b : ℝ} (h1 : (a : ℝ*) ≤ x) (h2 : x ≤ (b : ℝ*)) :
    IsFinite x := by
  refine isFinite_of_abs_le (r := |a| + |b|) ?_
  rw [abs_le]; constructor
  · rw [← Hyperreal.coe_neg]
    exact le_trans (Hyperreal.coe_le_coe.2 (by linarith [neg_abs_le a, abs_nonneg b])) h1
  · exact le_trans h2 (Hyperreal.coe_le_coe.2 (by linarith [le_abs_self b, abs_nonneg a]))

theorem isFinite_iE_ind (P : ∀ k, (Fin (n k) → Bool) → Prop) : IsFinite (iE n (ind P)) :=
  isFinite_of_bounds (a := 0) (b := 1) (by exact_mod_cast iE_ind_nonneg P)
    (by exact_mod_cast iE_ind_le_one P)

theorem loeb_iSet (P : ∀ k, (Fin (n k) → Bool) → Prop) :
    L n (iSet n P) = ENNReal.ofReal (stdPart (iE n (ind P))) := by
  rw [L, HypMeasure.loeb_internal (coinMeasure n) (S := iSet n P) (isInternal_internal _), mass_iSet,
    stE_of_isFinite (isFinite_iE_ind P)]

theorem loeb_iSet_toReal (P : ∀ k, (Fin (n k) → Bool) → Prop) :
    (L n (iSet n P)).toReal = stdPart (iE n (ind P)) := by
  rw [loeb_iSet, ENNReal.toReal_ofReal (stdPart_nonneg (iE_ind_nonneg P))]

theorem measurableSet_iSet (P : ∀ k, (Fin (n k) → Bool) → Prop) : MeasurableSet (iSet n P) :=
  (isInternal_internal _).measurableSet

open Classical in
theorem iF_ind (P : ∀ k, (Fin (n k) → Bool) → Prop) (ω : Ult (ℕ → Bool)) :
    iF n (ind P) ω = if ω ∈ iSet n P then 1 else 0 := by
  obtain ⟨u, rfl⟩ := exists_rep ω
  rw [iF_coe]
  unfold iSet
  rw [mem_internal]
  split_ifs with h
  · exact Germ.coe_eq.2 (by filter_upwards [h] with k hk; simp [ind, hk])
  · have h' : ∀ᶠ k in hyperfilter ℕ, ¬ P k (fun i => u k i) := by
      rcases (hyperfilter ℕ).em (fun k => P k (fun i => u k i)) with h1 | h1
      · exact absurd h1 h
      · exact h1
    exact Germ.coe_eq.2 (by filter_upwards [h'] with k hk; simp [ind, hk])


theorem iF_le {f g : ∀ k, (Fin (n k) → Bool) → ℝ} (h : ∀ k ω, f k ω ≤ g k ω)
    (ω : Ult (ℕ → Bool)) : iF n f ω ≤ iF n g ω := by
  obtain ⟨u, rfl⟩ := exists_rep ω
  rw [iF_coe, iF_coe]
  exact Hyperreal.ofSeq_le_ofSeq.2 (Eventually.of_forall fun k => h k _)

theorem iF_add (f g : ∀ k, (Fin (n k) → Bool) → ℝ) (ω : Ult (ℕ → Bool)) :
    iF n (fun k ω => f k ω + g k ω) ω = iF n f ω + iF n g ω := by
  obtain ⟨u, rfl⟩ := exists_rep ω; rfl

theorem iF_sub (f g : ∀ k, (Fin (n k) → Bool) → ℝ) (ω : Ult (ℕ → Bool)) :
    iF n (fun k ω => f k ω - g k ω) ω = iF n f ω - iF n g ω := by
  obtain ⟨u, rfl⟩ := exists_rep ω; rfl

theorem iF_neg (f : ∀ k, (Fin (n k) → Bool) → ℝ) (ω : Ult (ℕ → Bool)) :
    iF n (fun k ω => -f k ω) ω = -iF n f ω := by
  obtain ⟨u, rfl⟩ := exists_rep ω; rfl

theorem iF_mul (f g : ∀ k, (Fin (n k) → Bool) → ℝ) (ω : Ult (ℕ → Bool)) :
    iF n (fun k ω => f k ω * g k ω) ω = iF n f ω * iF n g ω := by
  obtain ⟨u, rfl⟩ := exists_rep ω; rfl

theorem iF_sq (f : ∀ k, (Fin (n k) → Bool) → ℝ) (ω : Ult (ℕ → Bool)) :
    iF n (fun k ω => f k ω ^ 2) ω = iF n f ω ^ 2 := by
  obtain ⟨u, rfl⟩ := exists_rep ω; rfl

theorem iF_const (c : ℝ) (ω : Ult (ℕ → Bool)) : iF n (fun _ _ => c) ω = (c : ℝ*) := by
  obtain ⟨u, rfl⟩ := exists_rep ω; rfl

theorem iF_const_mul (c : ℝ) (f : ∀ k, (Fin (n k) → Bool) → ℝ) (ω : Ult (ℕ → Bool)) :
    iF n (fun k ω => c * f k ω) ω = (c : ℝ*) * iF n f ω := by
  obtain ⟨u, rfl⟩ := exists_rep ω; rfl

theorem iF_abs (f : ∀ k, (Fin (n k) → Bool) → ℝ) (ω : Ult (ℕ → Bool)) :
    iF n (fun k ω => |f k ω|) ω = |iF n f ω| := by
  obtain ⟨u, rfl⟩ := exists_rep ω
  rw [iF_coe, iF_coe, abs_ofSeq]

theorem iF_sum {ι : Type*} (s : Finset ι) (f : ι → ∀ k, (Fin (n k) → Bool) → ℝ)
    (ω : Ult (ℕ → Bool)) :
    iF n (fun k ω => ∑ i ∈ s, f i k ω) ω = ∑ i ∈ s, iF n (f i) ω := by
  classical
  induction s using Finset.induction_on with
  | empty => simp only [Finset.sum_empty]; exact iF_const 0 ω
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    rw [iF_add (f a) (fun k ω => ∑ i ∈ s, f i k ω), ih]

theorem iE_sum {ι : Type*} (s : Finset ι) (f : ι → ∀ k, (Fin (n k) → Bool) → ℝ) :
    iE n (fun k ω => ∑ i ∈ s, f i k ω) = ∑ i ∈ s, iE n (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp only [Finset.sum_empty]; exact iE_const 0
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    rw [iE_add (f a) (fun k ω => ∑ i ∈ s, f i k ω), ih]

theorem coe_sum' {ι : Type*} (s : Finset ι) (x : ι → ℝ) :
    ((∑ i ∈ s, x i : ℝ) : ℝ*) = ∑ i ∈ s, (x i : ℝ*) :=
  map_sum Hyperreal.coeRingHom x s

theorem isInfinitesimal_sum {ι : Type*} (s : Finset ι) (x : ι → ℝ*)
    (h : ∀ i ∈ s, IsInfinitesimal (x i)) : IsInfinitesimal (∑ i ∈ s, x i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using isInfinitesimal_zero
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact (h a (Finset.mem_insert_self a s)).add (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem coe_le_stdPart {x : ℝ*} {r : ℝ} (hx : IsFinite x) (h : (r : ℝ*) ≤ x) : r ≤ stdPart x := by
  have := stdPart_mono (coe_isFinite r) hx h
  rwa [Hyperreal.stdPart_coe] at this

theorem stdPart_le_coe {x : ℝ*} {r : ℝ} (hx : IsFinite x) (h : x ≤ (r : ℝ*)) : stdPart x ≤ r := by
  have := stdPart_mono hx (coe_isFinite r) h
  rwa [Hyperreal.stdPart_coe] at this

end Basic

section Bounded

variable {n : ℕ → ℕ}

/-- Counting levels: for `0 ≤ x ≤ M ε`, `x - ε < ε #{j < M | (j+1) ε ≤ x} ≤ x`. -/
theorem level_count {x ε : ℝ} {M : ℕ} (hε : 0 < ε) (hx0 : 0 ≤ x) (hxM : x ≤ M * ε) :
    x - ε ≤ ε * ∑ j ∈ Finset.range M, (if ((j : ℝ) + 1) * ε ≤ x then (1 : ℝ) else 0) ∧
      ε * ∑ j ∈ Finset.range M, (if ((j : ℝ) + 1) * ε ≤ x then (1 : ℝ) else 0) ≤ x := by
  have hy : 0 ≤ x / ε := div_nonneg hx0 hε.le
  set F := ⌊x / ε⌋₊ with hF
  have hFM : F ≤ M := Nat.floor_le_of_le (by rw [div_le_iff₀ hε]; exact hxM)
  have hsum : ∑ j ∈ Finset.range M, (if ((j : ℝ) + 1) * ε ≤ x then (1 : ℝ) else 0) = F := by
    rw [Finset.sum_boole]
    have : (Finset.range M).filter (fun j : ℕ => ((j : ℝ) + 1) * ε ≤ x) = Finset.range F := by
      ext j
      simp only [Finset.mem_filter, Finset.mem_range]
      constructor
      · rintro ⟨-, h⟩
        have : ((j + 1 : ℕ) : ℝ) ≤ x / ε := by rw [le_div_iff₀ hε]; push_cast; exact h
        have := (Nat.le_floor_iff hy).2 this
        omega
      · intro hj
        refine ⟨by omega, ?_⟩
        have h1 : j + 1 ≤ F := hj
        have h2 := (Nat.le_floor_iff hy).1 h1
        push_cast at h2
        rwa [le_div_iff₀ hε] at h2
    rw [this, Finset.card_range]
  rw [hsum]
  have h1 := Nat.floor_le hy
  have h2 := Nat.lt_floor_add_one (x / ε)
  constructor
  · have := mul_lt_mul_of_pos_left h2 hε
    rw [mul_add, mul_div_cancel₀ _ hε.ne', mul_one] at this
    linarith
  · have := mul_le_mul_of_nonneg_left h1 hε.le
    rwa [mul_div_cancel₀ _ hε.ne'] at this

/-- **Bounded case**: for `0 ≤ f ≤ C`, `st E F = ∫ st F dL`. -/
theorem st_iE_of_nonneg_bdd (f : ∀ k, (Fin (n k) → Bool) → ℝ) {C : ℝ}
    (h0 : ∀ k ω, 0 ≤ f k ω) (hC : ∀ k ω, f k ω ≤ C) :
    stdPart (iE n f) = ∫ ω, stdPart (iF n f ω) ∂(L n) := by
  classical
  have hC0 : 0 ≤ C := le_trans (h0 0 (fun _ => true)) (hC 0 _)
  have hFfin : ∀ ω, IsFinite (iF n f ω) := fun ω =>
    isFinite_of_bounds (a := 0) (b := C) (by have := iF_le h0 ω; rwa [iF_const] at this)
      (by have := iF_le hC ω; rwa [iF_const] at this)
  have hEfin : IsFinite (iE n f) :=
    isFinite_of_bounds (a := 0) (b := C) (by have := iE_mono (n := n) h0; rwa [iE_const] at this)
      (by have := iE_mono (n := n) hC; rwa [iE_const] at this)
  have hint : Integrable (fun ω => stdPart (iF n f ω)) (L n) := by
    refine Integrable.of_bound (C := C) (measurable_st_iF f).aestronglyMeasurable
      (Eventually.of_forall fun ω => ?_)
    rw [Real.norm_eq_abs, abs_le]
    constructor
    · have := coe_le_stdPart (hFfin ω) (by have := iF_le h0 ω; rwa [iF_const] at this)
      linarith
    · exact stdPart_le_coe (hFfin ω) (by have := iF_le hC ω; rwa [iF_const] at this)
  -- approximate within `2 δ` for every `δ = (C+1)/M`
  refine eq_of_abs_sub_le_all fun ε hε => ?_
  obtain ⟨M, hM⟩ := exists_nat_gt (2 * (C + 1) / ε)
  have hMpos : (0 : ℝ) < M := lt_of_le_of_lt (by positivity) hM
  set δ := (C + 1) / M with hδ
  have hδ0 : 0 < δ := by positivity
  have hMδ : (M : ℝ) * δ = C + 1 := by rw [hδ]; field_simp
  have hδε : 2 * δ ≤ ε := by
    rw [hδ, mul_div_assoc', div_le_iff₀ hMpos]
    rw [div_lt_iff₀ hε] at hM; linarith
  let P : ℕ → ∀ k, (Fin (n k) → Bool) → Prop := fun j k ω => ((j : ℝ) + 1) * δ ≤ f k ω
  let sF : ∀ k, (Fin (n k) → Bool) → ℝ :=
    fun k ω => δ * ∑ j ∈ Finset.range M, ind (P j) k ω
  have hlev : ∀ k ω, f k ω - δ ≤ sF k ω ∧ sF k ω ≤ f k ω := by
    intro k ω
    have := level_count hδ0 (h0 k ω) (le_trans (hC k ω) (by rw [hMδ]; linarith))
    have e : ∑ j ∈ Finset.range M, ind (P j) k ω =
        ∑ j ∈ Finset.range M, (if ((j : ℝ) + 1) * δ ≤ f k ω then (1 : ℝ) else 0) := by
      apply Finset.sum_congr rfl; intro j _; simp only [ind, P]
    simp only [sF, e]; exact this
  -- the Loeb simple function
  let A : ℕ → Set (Ult (ℕ → Bool)) := fun j => iSet n (P j)
  let σ : Ult (ℕ → Bool) → ℝ := fun ω => δ * ∑ j ∈ Finset.range M, (A j).indicator 1 ω
  have hσ : ∀ ω, iF n sF ω = (σ ω : ℝ*) := by
    intro ω
    simp only [sF, σ]
    rw [iF_const_mul, iF_sum]
    rw [Hyperreal.coe_mul, coe_sum']
    congr 1; apply Finset.sum_congr rfl; intro j _
    rw [iF_ind, Set.indicator_apply]
    split_ifs <;> simp [A]
  have hσint : ∫ ω, σ ω ∂(L n) = δ * ∑ j ∈ Finset.range M, (L n (A j)).toReal := by
    simp only [σ]
    rw [integral_const_mul, integral_finsetSum]
    · congr 1; apply Finset.sum_congr rfl; intro j _
      rw [integral_indicator_one (measurableSet_iSet _)]; rfl
    · intro j _
      exact (integrable_const (1 : ℝ)).indicator (measurableSet_iSet _)
  -- the internal side
  have hEs : IsInfinitesimal (iE n sF - ((∫ ω, σ ω ∂(L n) : ℝ) : ℝ*)) := by
    rw [hσint]
    have : iE n sF = (δ : ℝ*) * ∑ j ∈ Finset.range M, iE n (ind (P j)) := by
      simp only [sF]; rw [iE_const_mul, iE_sum]
    rw [this, Hyperreal.coe_mul, coe_sum', ← mul_sub, ← Finset.sum_sub_distrib]
    refine IsInfinitesimal.mul_finite ?_ (coe_isFinite δ) |> fun h => by rwa [mul_comm] at h
    refine isInfinitesimal_sum _ _ fun j _ => ?_
    rw [loeb_iSet_toReal]
    exact isInfinitesimal_sub_stdPart (isFinite_iE_ind _)
  have hst_s : stdPart (iE n sF) = ∫ ω, σ ω ∂(L n) := stdPart_unique hEs
  have hsfin : IsFinite (iE n sF) := by
    have : iE n sF = (iE n sF - ((∫ ω, σ ω ∂(L n) : ℝ) : ℝ*)) + ((∫ ω, σ ω ∂(L n) : ℝ) : ℝ*) := by ring
    rw [this]; exact hEs.isFinite.add (coe_isFinite _)
  have hE1 : iE n f - (δ : ℝ*) ≤ iE n sF := by
    rw [← iE_const, ← iE_sub]; exact iE_mono fun k ω => (hlev k ω).1
  have hE2 : iE n sF ≤ iE n f := iE_mono fun k ω => (hlev k ω).2
  have hst1 : stdPart (iE n f) - δ ≤ stdPart (iE n sF) := by
    have := stdPart_mono (hEfin.add (isFinite_neg (coe_isFinite δ))) hsfin
      (by rw [← sub_eq_add_neg]; exact hE1)
    rwa [← sub_eq_add_neg, stdPart_sub hEfin (coe_isFinite δ), Hyperreal.stdPart_coe] at this
  have hst2 : stdPart (iE n sF) ≤ stdPart (iE n f) := stdPart_mono hsfin hEfin hE2
  -- the Loeb side
  have hpt : ∀ ω, σ ω ≤ stdPart (iF n f ω) ∧ stdPart (iF n f ω) ≤ σ ω + δ := by
    intro ω
    have h1 : iF n f ω - (δ : ℝ*) ≤ (σ ω : ℝ*) := by
      rw [← hσ, ← iF_const δ ω, ← iF_sub]; exact iF_le (fun k ω => (hlev k ω).1) ω
    have h2 : (σ ω : ℝ*) ≤ iF n f ω := by rw [← hσ]; exact iF_le (fun k ω => (hlev k ω).2) ω
    exact ⟨coe_le_stdPart (hFfin ω) h2,
      stdPart_le_coe (hFfin ω) (by push_cast; linarith)⟩
  have hσi : Integrable σ (L n) := by
    simp only [σ]
    exact (integrable_finsetSum _ fun j _ =>
      (integrable_const (1 : ℝ)).indicator (measurableSet_iSet _)).const_mul δ
  have hI1 : ∫ ω, σ ω ∂(L n) ≤ ∫ ω, stdPart (iF n f ω) ∂(L n) :=
    integral_mono hσi hint fun ω => (hpt ω).1
  have hI2 : ∫ ω, stdPart (iF n f ω) ∂(L n) ≤ ∫ ω, σ ω ∂(L n) + δ := by
    have := integral_mono (g := fun ω => σ ω + δ) hint (hσi.add (integrable_const δ))
      fun ω => (hpt ω).2
    rwa [integral_add hσi (integrable_const δ), integral_const, probReal_univ, one_smul] at this
  rw [abs_le]; constructor <;> linarith


/-- **Bounded case**: for `|f| ≤ C`, `st E F = ∫ st F dL`. -/
theorem st_iE_of_bdd (f : ∀ k, (Fin (n k) → Bool) → ℝ) {C : ℝ} (hC : ∀ k ω, |f k ω| ≤ C) :
    stdPart (iE n f) = ∫ ω, stdPart (iF n f ω) ∂(L n) := by
  have hg := st_iE_of_nonneg_bdd (n := n) (fun k ω => f k ω + C) (C := 2 * C)
    (fun k ω => by linarith [neg_abs_le (f k ω), hC k ω])
    (fun k ω => by linarith [le_abs_self (f k ω), hC k ω])
  have hFfin : ∀ ω, IsFinite (iF n f ω) := fun ω => isFinite_of_abs_le (r := C) (by
    rw [← iF_abs, ← iF_const C ω]; exact iF_le hC ω)
  have hEfin : IsFinite (iE n f) := isFinite_of_abs_le (r := C) (by
    rw [abs_le]; constructor
    · rw [← Hyperreal.coe_neg, ← iE_const]; exact iE_mono fun k ω => by
        linarith [neg_abs_le (f k ω), hC k ω]
    · rw [← iE_const]; exact iE_mono fun k ω => by linarith [le_abs_self (f k ω), hC k ω])
  rw [iE_add, iE_const, stdPart_add hEfin (coe_isFinite C), Hyperreal.stdPart_coe] at hg
  have e : ∀ ω, stdPart (iF n (fun k ω => f k ω + C) ω) = stdPart (iF n f ω) + C := by
    intro ω
    rw [iF_add, iF_const, stdPart_add (hFfin ω) (coe_isFinite C), Hyperreal.stdPart_coe]
  simp_rw [e] at hg
  have hint : Integrable (fun ω => stdPart (iF n f ω)) (L n) := by
    refine Integrable.of_bound (C := C) (measurable_st_iF f).aestronglyMeasurable
      (Eventually.of_forall fun ω => ?_)
    rw [Real.norm_eq_abs, abs_le]
    have h1 : |iF n f ω| ≤ (C : ℝ*) := by rw [← iF_abs, ← iF_const C ω]; exact iF_le hC ω
    rw [abs_le] at h1
    exact ⟨by have := coe_le_stdPart (hFfin ω) (by rw [Hyperreal.coe_neg]; exact h1.1); linarith,
      stdPart_le_coe (hFfin ω) h1.2⟩
  rw [integral_add hint (integrable_const C), integral_const, probReal_univ, one_smul] at hg
  linarith

end Bounded

section Fatou

variable {n : ℕ → ℕ}

theorem iF_min (f : ∀ k, (Fin (n k) → Bool) → ℝ) (c : ℝ) (ω : Ult (ℕ → Bool)) :
    iF n (fun k ω => min (f k ω) c) ω = min (iF n f ω) (c : ℝ*) := by
  obtain ⟨u, rfl⟩ := exists_rep ω
  rw [iF_coe, iF_coe]
  rcases (hyperfilter ℕ).em (fun k => f k (fun i => u k i) ≤ c) with h | h
  · have h1 : Hyperreal.ofSeq (fun k => f k (fun i => u k i)) ≤ (c : ℝ*) :=
      Hyperreal.ofSeq_le_ofSeq.2 h
    rw [min_eq_left h1]
    exact Germ.coe_eq.2 (by filter_upwards [h] with k hk; exact min_eq_left hk)
  · have h1 : (c : ℝ*) ≤ Hyperreal.ofSeq (fun k => f k (fun i => u k i)) :=
      Hyperreal.ofSeq_le_ofSeq.2 (by filter_upwards [h] with k hk; exact (not_le.1 hk).le)
    rw [min_eq_right h1]
    exact Germ.coe_eq.2 (by filter_upwards [h] with k hk; exact min_eq_right (not_le.1 hk).le)

theorem iF_max (f : ∀ k, (Fin (n k) → Bool) → ℝ) (c : ℝ) (ω : Ult (ℕ → Bool)) :
    iF n (fun k ω => max (f k ω) c) ω = max (iF n f ω) (c : ℝ*) := by
  have := iF_min (n := n) (fun k ω => -f k ω) (-c) ω
  rw [iF_neg] at this
  have e1 : (fun k ω => max (f k ω) c) = fun k ω => -(min (-f k ω) (-c)) := by
    funext k ω; rw [min_neg_neg, neg_neg]
  rw [e1, iF_neg, this, Hyperreal.coe_neg, min_neg_neg, neg_neg]

theorem stdPart_min_coe {x : ℝ*} (hx : IsFinite x) (c : ℝ) :
    stdPart (min x (c : ℝ*)) = min (stdPart x) c := by
  rcases le_total x (c : ℝ*) with h | h
  · rw [min_eq_left h, min_eq_left (stdPart_le_coe hx h)]
  · rw [min_eq_right h, min_eq_right (coe_le_stdPart hx h), Hyperreal.stdPart_coe]

theorem stdPart_max_coe {x : ℝ*} (hx : IsFinite x) (c : ℝ) :
    stdPart (max x (c : ℝ*)) = max (stdPart x) c := by
  rcases le_total x (c : ℝ*) with h | h
  · rw [max_eq_right h, max_eq_right (stdPart_le_coe hx h), Hyperreal.stdPart_coe]
  · rw [max_eq_left h, max_eq_left (coe_le_stdPart hx h)]

theorem stdPart_abs (x : ℝ*) : stdPart |x| = |stdPart x| := by
  rcases le_total 0 x with h | h
  · rw [abs_of_nonneg h, abs_of_nonneg (stdPart_nonneg h)]
  · rw [abs_of_nonpos h, abs_of_nonpos (stdPart_nonpos h), stdPart_neg]

theorem min_stdPart_le (x : ℝ*) (c : ℝ) :
    min (stdPart x) c ≤ stdPart (min x (c : ℝ*)) := by
  rcases le_total x (c : ℝ*) with h | h
  · rw [min_eq_left h]; exact min_le_left _ _
  · rw [min_eq_right h, Hyperreal.stdPart_coe]; exact min_le_right _ _

/-- **Fatou's inequality** for nonnegative internal functions. -/
theorem lintegral_st_le (f : ∀ k, (Fin (n k) → Bool) → ℝ) (h0 : ∀ k ω, 0 ≤ f k ω) :
    ∫⁻ ω, ENNReal.ofReal (stdPart (iF n f ω)) ∂(L n) ≤ stE (iE n f) := by
  have hF0 : ∀ ω, 0 ≤ iF n f ω := fun ω => by
    have := iF_le h0 ω; rwa [iF_const] at this
  let g : ℕ → Ult (ℕ → Bool) → ℝ≥0∞ := fun m ω => ENNReal.ofReal (min (stdPart (iF n f ω)) m)
  have hg_meas : ∀ m, Measurable (g m) := fun m =>
    ENNReal.measurable_ofReal.comp ((measurable_st_iF f).min measurable_const)
  have hg_mono : Monotone g := fun a b hab ω =>
    ENNReal.ofReal_le_ofReal (min_le_min_left _ (by exact_mod_cast hab))
  have hsup : ∀ ω, ⨆ m, g m ω = ENNReal.ofReal (stdPart (iF n f ω)) := by
    intro ω
    apply le_antisymm
    · exact iSup_le fun m => ENNReal.ofReal_le_ofReal (min_le_left _ _)
    · obtain ⟨m, hm⟩ := exists_nat_ge (stdPart (iF n f ω))
      exact le_iSup_of_le m (by simp only [g]; rw [min_eq_left hm])
  calc ∫⁻ ω, ENNReal.ofReal (stdPart (iF n f ω)) ∂(L n)
      = ∫⁻ ω, ⨆ m, g m ω ∂(L n) := by simp_rw [hsup]
    _ = ⨆ m, ∫⁻ ω, g m ω ∂(L n) := lintegral_iSup hg_meas hg_mono
    _ ≤ stE (iE n f) := by
      refine iSup_le fun m => ?_
      let fm : ∀ k, (Fin (n k) → Bool) → ℝ := fun k ω => min (f k ω) m
      have hfm0 : ∀ k ω, 0 ≤ fm k ω := fun k ω => le_min (h0 k ω) (Nat.cast_nonneg m)
      have hfmC : ∀ k ω, fm k ω ≤ m := fun k ω => min_le_right _ _
      have hb := st_iE_of_nonneg_bdd fm hfm0 hfmC
      have hfmfin : ∀ ω, IsFinite (iF n fm ω) := fun ω =>
        isFinite_of_bounds (a := 0) (b := m) (by have := iF_le hfm0 ω; rwa [iF_const] at this)
          (by have := iF_le hfmC ω; rwa [iF_const] at this)
      have hint : Integrable (fun ω => stdPart (iF n fm ω)) (L n) := by
        refine Integrable.of_bound (C := m) (measurable_st_iF fm).aestronglyMeasurable
          (Eventually.of_forall fun ω => ?_)
        rw [Real.norm_eq_abs, abs_le]
        exact ⟨by have := stdPart_nonneg (by have := iF_le hfm0 ω; rwa [iF_const] at this :
            (0 : ℝ*) ≤ iF n fm ω); linarith [Nat.cast_nonneg (α := ℝ) m],
          stdPart_le_coe (hfmfin ω) (by have := iF_le hfmC ω; rwa [iF_const] at this)⟩
      calc ∫⁻ ω, g m ω ∂(L n)
          ≤ ∫⁻ ω, ENNReal.ofReal (stdPart (iF n fm ω)) ∂(L n) := by
            refine lintegral_mono fun ω => ENNReal.ofReal_le_ofReal ?_
            simp only [fm]; rw [iF_min]; exact min_stdPart_le _ m
        _ = ENNReal.ofReal (∫ ω, stdPart (iF n fm ω) ∂(L n)) := by
            rw [ofReal_integral_eq_lintegral_ofReal hint (Eventually.of_forall fun ω =>
              stdPart_nonneg (by have := iF_le hfm0 ω; rwa [iF_const] at this))]
        _ = stE (iE n fm) := by
            rw [← hb, stE_of_isFinite (isFinite_of_bounds (a := 0) (b := m)
              (by have := iE_mono (n := n) hfm0; rwa [iE_const] at this)
              (by have := iE_mono (n := n) hfmC; rwa [iE_const] at this))]
        _ ≤ stE (iE n f) := stE_mono (by have := iE_mono (n := n) hfm0; rwa [iE_const] at this)
            (iE_mono fun k ω => min_le_left _ _)


theorem isFinite_iE_of_abs {f : ∀ k, (Fin (n k) → Bool) → ℝ} (hf : IsFinite (iE n (fun k ω => |f k ω|))) :
    IsFinite (iE n f) := by
  obtain ⟨r, hr⟩ := (isFinite_iff_abs_le _).1 hf
  refine isFinite_of_abs_le (r := r) ?_
  rw [abs_le] at hr ⊢
  have h1 : iE n f ≤ iE n (fun k ω => |f k ω|) := iE_mono fun k ω => le_abs_self _
  have h2 : -iE n (fun k ω => |f k ω|) ≤ iE n f := by
    rw [← iE_neg]; exact iE_mono fun k ω => neg_abs_le _
  constructor <;> linarith [hr.1, hr.2]

/-- Markov's inequality and a.e. finiteness. -/
theorem ae_isFinite_of_iE_abs {f : ∀ k, (Fin (n k) → Bool) → ℝ}
    (hf : IsFinite (iE n (fun k ω => |f k ω|))) : ∀ᵐ ω ∂(L n), IsFinite (iF n f ω) := by
  rw [ae_iff]
  set c := stdPart (iE n (fun k ω => |f k ω|))
  have hc0 : 0 ≤ c := stdPart_nonneg (iE_nonneg fun k ω => abs_nonneg _)
  -- `L {|F| ≥ m} ≤ c/m`
  have hA : ∀ m : ℕ, 0 < m → L n {ω | ¬ IsFinite (iF n f ω)} ≤ ENNReal.ofReal (c / m) := by
    intro m hm
    have hm' : (0 : ℝ) < m := by exact_mod_cast hm
    let P : ∀ k, (Fin (n k) → Bool) → Prop := fun k ω => (m : ℝ) ≤ |f k ω|
    have hsub : {ω | ¬ IsFinite (iF n f ω)} ⊆ iSet n P := by
      intro ω hω
      obtain ⟨u, rfl⟩ := exists_rep ω
      have hlt : ((m : ℝ) : ℝ*) < |iF n f (u : Ult (ℕ → Bool))| := by
        by_contra hc; push Not at hc; exact hω (isFinite_of_abs_le hc)
      rw [iF_coe, abs_ofSeq] at hlt
      have := Hyperreal.ofSeq_lt_ofSeq.1 hlt
      show (u : Ult (ℕ → Bool)) ∈ internal _
      rw [mem_internal]
      filter_upwards [this] with k hk using le_of_lt hk
    refine (measure_mono hsub).trans ?_
    rw [loeb_iSet]
    refine ENNReal.ofReal_le_ofReal ?_
    have hle : iE n (ind P) ≤ ((1 / m : ℝ) : ℝ*) * iE n (fun k ω => |f k ω|) := by
      rw [← iE_const_mul]
      refine iE_mono fun k ω => ?_
      simp only [ind, P]
      split_ifs with h
      · rw [one_div, ← div_eq_inv_mul, le_div_iff₀ hm']; linarith
      · exact mul_nonneg (by positivity) (abs_nonneg _)
    have := stdPart_mono (isFinite_iE_ind P) ((coe_isFinite _).mul hf) hle
    rwa [stdPart_mul (coe_isFinite _) hf, Hyperreal.stdPart_coe, one_div, inv_mul_eq_div] at this
  refine le_antisymm (ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_) bot_le
  obtain ⟨m, hm⟩ := exists_nat_gt (c / ε)
  have hm0 : 0 < m := by
    have : (0 : ℝ) < m := lt_of_le_of_lt (div_nonneg hc0 ε.2) hm
    exact_mod_cast this
  refine (hA m hm0).trans ?_
  rw [zero_add, ← ENNReal.ofReal_coe_nnreal]
  refine ENNReal.ofReal_le_ofReal ?_
  have hε' : (0 : ℝ) < ε := hε
  rw [div_lt_iff₀ hε'] at hm
  rw [div_le_iff₀ (by exact_mod_cast hm0)]; linarith

/-- The tail of an S-integrable function is uniformly small beyond a standard level. -/
theorem SInt.tail_small {f : ∀ k, (Fin (n k) → Bool) → ℝ} (hS : SInt n f) {ε : ℝ} (hε : 0 < ε) :
    ∃ m0 : ℕ, ∀ m : ℕ, m0 ≤ m →
      iE n (fun k ω => if (m : ℝ) < |f k ω| then |f k ω| else 0) ≤ (ε : ℝ*) := by
  classical
  let S : Set (Ult ℕ) := internal (fun k => {N : ℕ |
    QE.OpenSto.Walsh.E (fun ω => if (N : ℝ) < |f k ω| then |f k ω| else 0) < ε})
  have hSi : IsInternal S := isInternal_internal _
  have hall : ∀ ν, IsUnlimited ν → ν ∈ S := by
    intro ν hν
    obtain ⟨u, rfl⟩ := exists_rep ν
    have hK : ∀ r : ℝ, ∀ᶠ k in hyperfilter ℕ, r < ((u k : ℕ) : ℝ) := by
      intro r
      have := Germ.coe_lt.1 (hν ⌈r⌉₊)
      filter_upwards [this] with k hk
      exact lt_of_le_of_lt (Nat.le_ceil r) (by exact_mod_cast hk)
    have hinf := hS.2 (fun k => (u k : ℝ)) hK
    unfold iE at hinf
    rw [isInfinitesimal_ofSeq_iff] at hinf
    show (u : Ult ℕ) ∈ internal _
    rw [mem_internal]
    filter_upwards [hinf ε hε] with k hk
    exact lt_of_le_of_lt (le_abs_self _) hk
  obtain ⟨m0, hm0⟩ := underspill_internal S hSi hall
  rw [const_mem_internal] at hm0
  refine ⟨m0, fun m hm => ?_⟩
  refine le_trans (iE_mono (g := fun k ω => if (m0 : ℝ) < |f k ω| then |f k ω| else 0)
    fun k ω => ?_) ?_
  · have : (m0 : ℝ) ≤ m := by exact_mod_cast hm
    split_ifs with h1 h2 <;> first | exact le_rfl | exact abs_nonneg _ | linarith
  · unfold iE
    exact ofSeq_le_const.2 (by filter_upwards [hm0] with k hk using hk.le)

/-- **Integrability** of the standard part of an S-integrable function. -/
theorem SInt.integrable {f : ∀ k, (Fin (n k) → Bool) → ℝ} (hS : SInt n f) :
    Integrable (fun ω => stdPart (iF n f ω)) (L n) := by
  refine ⟨(measurable_st_iF f).aestronglyMeasurable, ?_⟩
  unfold HasFiniteIntegral
  have e : ∀ ω, ‖stdPart (iF n f ω)‖ₑ = ENNReal.ofReal (stdPart (iF n (fun k ω => |f k ω|) ω)) := by
    intro ω; rw [Real.enorm_eq_ofReal_abs, iF_abs, stdPart_abs]
  simp_rw [e]
  exact lt_of_le_of_lt (lintegral_st_le _ fun k ω => abs_nonneg _) (stE_lt_top hS.1)

theorem abs_clamp_le (x m : ℝ) (hm : 0 ≤ m) : |max (min x m) (-m)| ≤ |x| := by
  rcases le_total x m with h1 | h1
  · rw [min_eq_left h1]
    rcases le_total x (-m) with h2 | h2
    · rw [max_eq_right h2, abs_neg, abs_of_nonneg hm, abs_of_nonpos (by linarith)]; linarith
    · rw [max_eq_left h2]
  · rw [min_eq_right h1, max_eq_left (by linarith), abs_of_nonneg hm, abs_of_nonneg (by linarith)]
    exact h1

/-- **Loeb integration of S-integrable functions**: `st E F = ∫ st F dL`. -/
theorem st_iE_eq_integral {f : ∀ k, (Fin (n k) → Bool) → ℝ} (hS : SInt n f) :
    Integrable (fun ω => stdPart (iF n f ω)) (L n) ∧
      stdPart (iE n f) = ∫ ω, stdPart (iF n f ω) ∂(L n) := by
  refine ⟨hS.integrable, ?_⟩
  have hEf := isFinite_iE_of_abs hS.1
  let fm : ℕ → ∀ k, (Fin (n k) → Bool) → ℝ := fun m k ω => max (min (f k ω) m) (-(m : ℝ))
  have hfm_bdd : ∀ m k ω, |fm m k ω| ≤ m := by
    intro m k ω; simp only [fm]; rw [abs_le]
    constructor
    · exact le_max_right _ _
    · exact max_le (min_le_right _ _) (by linarith [Nat.cast_nonneg (α := ℝ) m])
  have hbdd : ∀ m, stdPart (iE n (fm m)) = ∫ ω, stdPart (iF n (fm m) ω) ∂(L n) :=
    fun m => st_iE_of_bdd (fm m) (hfm_bdd m)
  have hEfm : ∀ m, IsFinite (iE n (fm m)) := fun m => isFinite_of_abs_le (r := m) (by
    rw [abs_le]; constructor
    · rw [← Hyperreal.coe_neg, ← iE_const]; exact iE_mono fun k ω => (abs_le.1 (hfm_bdd m k ω)).1
    · rw [← iE_const]; exact iE_mono fun k ω => (abs_le.1 (hfm_bdd m k ω)).2)
  -- internal side converges
  have hdiff : ∀ m k ω, |f k ω - fm m k ω| ≤ if (m : ℝ) < |f k ω| then |f k ω| else 0 := by
    intro m k ω
    simp only [fm]
    split_ifs with h
    · rcases le_total 0 (f k ω) with h0 | h0
      · rw [abs_of_nonneg h0] at h ⊢
        rw [min_eq_right h.le, max_eq_left (by linarith [Nat.cast_nonneg (α := ℝ) m]),
          abs_of_nonneg (by linarith)]
        linarith [Nat.cast_nonneg (α := ℝ) m]
      · rw [abs_of_nonpos h0] at h ⊢
        rw [min_eq_left (by linarith [Nat.cast_nonneg (α := ℝ) m]), max_eq_right (by linarith),
          abs_of_nonpos (by linarith)]
        linarith [Nat.cast_nonneg (α := ℝ) m]
    · push Not at h
      rw [abs_le] at h
      rw [min_eq_left h.2, max_eq_left h.1, sub_self, abs_zero]
  have hT1 : Tendsto (fun m : ℕ => stdPart (iE n (fm m))) atTop (𝓝 (stdPart (iE n f))) := by
    rw [Metric.tendsto_atTop]
    intro ε hε
    obtain ⟨m0, hm0⟩ := hS.tail_small (half_pos hε)
    refine ⟨m0, fun m hm => ?_⟩
    rw [Real.dist_eq, ← stdPart_sub (hEfm m) hEf]
    have hb : |iE n (fm m) - iE n f| ≤ ((ε / 2 : ℝ) : ℝ*) := by
      rw [abs_le]; constructor
      · have : iE n f - iE n (fm m) ≤ ((ε / 2 : ℝ) : ℝ*) := by
          rw [← iE_sub]
          exact le_trans (iE_mono fun k ω => le_trans (le_abs_self _) (hdiff m k ω)) (hm0 m hm)
        linarith
      · rw [← iE_sub]
        refine le_trans (iE_mono fun k ω => ?_) (hm0 m hm)
        exact le_trans (le_abs_self _) (by rw [abs_sub_comm]; exact hdiff m k ω)
    rw [← stdPart_abs]
    refine lt_of_le_of_lt (stdPart_le_coe (isFinite_of_abs_le (by rwa [abs_abs])) hb)
      (half_lt_self hε)
  -- Loeb side converges (dominated convergence)
  have hfin := ae_isFinite_of_iE_abs hS.1
  have hpt : ∀ m ω, IsFinite (iF n f ω) →
      stdPart (iF n (fm m) ω) = max (min (stdPart (iF n f ω)) m) (-(m : ℝ)) := by
    intro m ω hω
    have h1 : iF n (fm m) ω = max (min (iF n f ω) (m : ℝ*)) (((-(m : ℝ)) : ℝ) : ℝ*) := by
      simp only [fm]
      rw [iF_max (fun k ω => min (f k ω) (m : ℝ)), iF_min]; rfl
    have hmin : IsFinite (min (iF n f ω) (m : ℝ*)) := by
      rcases min_choice (iF n f ω) (m : ℝ*) with h | h <;> rw [h]
      · exact hω
      · exact_mod_cast coe_isFinite (m : ℝ)
    rw [h1, stdPart_max_coe hmin]
    have : ((m : ℝ*)) = (((m : ℝ)) : ℝ*) := rfl
    rw [this, stdPart_min_coe hω]
  have hT2 : Tendsto (fun m : ℕ => ∫ ω, stdPart (iF n (fm m) ω) ∂(L n)) atTop
      (𝓝 (∫ ω, stdPart (iF n f ω) ∂(L n))) := by
    refine tendsto_integral_of_dominated_convergence (fun ω => |stdPart (iF n f ω)|)
      (fun m => (measurable_st_iF (fm m)).aestronglyMeasurable) hS.integrable.abs
      (fun m => ?_) ?_
    · filter_upwards [hfin] with ω hω
      rw [hpt m ω hω, Real.norm_eq_abs]
      exact abs_clamp_le _ _ (Nat.cast_nonneg m)
    · filter_upwards [hfin] with ω hω
      refine tendsto_atTop_of_eventually_const (i₀ := ⌈|stdPart (iF n f ω)|⌉₊) fun m hm => ?_
      have hm' : |stdPart (iF n f ω)| ≤ m := le_trans (Nat.le_ceil _) (by exact_mod_cast hm)
      rw [hpt m ω hω, min_eq_left (le_trans (le_abs_self _) hm'),
        max_eq_left (by linarith [neg_abs_le (stdPart (iF n f ω))])]
  simp_rw [hbdd] at hT1
  exact tendsto_nhds_unique hT1 hT2

end Fatou

section Closure

variable {n : ℕ → ℕ}

theorem iE_seq_mul (c : ℕ → ℝ) (f : ∀ k, (Fin (n k) → Bool) → ℝ) :
    iE n (fun k ω => c k * f k ω) = Hyperreal.ofSeq c * iE n f := by
  unfold iE; simp_rw [E_eq_avg, QE.Chaos.avg_const_mul]; rfl

theorem isFinite_of_nonneg_le' {x y : ℝ*} (hx : 0 ≤ x) (h : x ≤ y) (hy : IsFinite y) :
    IsFinite x := isFinite_of_nonneg_of_le hx h hy

theorem isInfinitesimal_of_nonneg_le {x y : ℝ*} (hx : 0 ≤ x) (h : x ≤ y)
    (hy : IsInfinitesimal y) : IsInfinitesimal x :=
  hy.of_abs_le (by rw [abs_of_nonneg hx, abs_of_nonneg (hx.trans h)]; exact h)

theorem unlimited_div {K : ℕ → ℝ} (hK : ∀ r : ℝ, ∀ᶠ k in hyperfilter ℕ, r < K k) {c : ℝ}
    (hc : 0 < c) : ∀ r : ℝ, ∀ᶠ k in hyperfilter ℕ, r < K k / c := by
  intro r
  filter_upwards [hK (r * c)] with k hk
  rwa [lt_div_iff₀ hc]

/-- Domination: `|f| ≤ g` with `g` S-integrable. -/
theorem SInt.mono {f g : ∀ k, (Fin (n k) → Bool) → ℝ} (hg : SInt n g)
    (h : ∀ k ω, |f k ω| ≤ g k ω) : SInt n f := by
  refine ⟨isFinite_of_nonneg_of_le (iE_nonneg fun k ω => abs_nonneg _)
    (iE_mono fun k ω => (h k ω).trans (le_abs_self _)) hg.1, fun K hK => ?_⟩
  refine isInfinitesimal_of_nonneg_le (iE_nonneg fun k ω => by split_ifs <;> simp)
    (iE_mono fun k ω => ?_) (hg.2 K hK)
  have hg' : |f k ω| ≤ |g k ω| := (h k ω).trans (le_abs_self _)
  split_ifs with h1 h2
  · exact hg'
  · exact absurd (lt_of_lt_of_le h1 hg') h2
  · exact abs_nonneg _
  · exact le_rfl

theorem SInt.abs {f : ∀ k, (Fin (n k) → Bool) → ℝ} (hf : SInt n f) :
    SInt n (fun k ω => |f k ω|) := by
  simpa [SInt, abs_abs] using hf

theorem SInt.neg {f : ∀ k, (Fin (n k) → Bool) → ℝ} (hf : SInt n f) :
    SInt n (fun k ω => -f k ω) :=
  hf.abs.mono fun k ω => by rw [abs_neg]

theorem SInt.add {f g : ∀ k, (Fin (n k) → Bool) → ℝ} (hf : SInt n f) (hg : SInt n g) :
    SInt n (fun k ω => f k ω + g k ω) := by
  refine ⟨isFinite_of_nonneg_of_le (iE_nonneg fun k ω => abs_nonneg _)
    (iE_mono (g := fun k ω => |f k ω| + |g k ω|) fun k ω => abs_add_le _ _)
    (by rw [iE_add]; exact hf.1.add hg.1), fun K hK => ?_⟩
  have hK2 := unlimited_div hK (c := 2) two_pos
  have hsum := ((hf.2 _ hK2).add (hg.2 _ hK2))
  rw [← iE_add] at hsum
  have h2 := hsum.mul_finite (coe_isFinite 2)
  rw [mul_comm, ← iE_const_mul] at h2
  refine isInfinitesimal_of_nonneg_le (iE_nonneg fun k ω => by split_ifs <;> simp)
    (iE_mono fun k ω => ?_) h2
  have hfg := abs_add_le (f k ω) (g k ω)
  split_ifs with h1 ha hb hb <;> first
    | (rcases le_total |f k ω| |g k ω| with hc | hc <;> nlinarith [abs_nonneg (f k ω),
        abs_nonneg (g k ω)])

theorem SInt.sub {f g : ∀ k, (Fin (n k) → Bool) → ℝ} (hf : SInt n f) (hg : SInt n g) :
    SInt n (fun k ω => f k ω - g k ω) := by
  simpa [sub_eq_add_neg] using hf.add hg.neg

theorem SInt.const_mul {f : ∀ k, (Fin (n k) → Bool) → ℝ} (hf : SInt n f) (c : ℝ) :
    SInt n (fun k ω => c * f k ω) := by
  -- `|c f| ≤ (|c|+1) |f|`, and S-integrability of `a |f|` for standard `a > 0`
  have ha : (0 : ℝ) < |c| + 1 := by positivity
  have e : ∀ k ω, _root_.abs ((|c| + 1) * |f k ω|) = (|c| + 1) * |f k ω| := fun k ω =>
    abs_of_nonneg (by positivity)
  have key : SInt n (fun k ω => (|c| + 1) * |f k ω|) := by
    refine ⟨?_, fun K hK => ?_⟩
    · simp only [e]; rw [iE_const_mul]; exact (coe_isFinite _).mul hf.1
    · have h2 := (hf.2 _ (unlimited_div hK ha)).mul_finite (coe_isFinite (|c| + 1))
      rw [mul_comm, ← iE_const_mul] at h2
      simp only [e]
      refine isInfinitesimal_of_nonneg_le (iE_nonneg fun k ω => by split_ifs <;> positivity)
        (iE_mono fun k ω => ?_) h2
      split_ifs with h1 h2
      · exact le_refl _
      · exfalso; rw [div_lt_iff₀ ha] at h2; exact h2 (by linarith)
      · positivity
      · simp
  exact key.mono fun k ω => by
    rw [abs_mul]; exact mul_le_mul_of_nonneg_right (by linarith) (abs_nonneg _)

/-- A finite second moment gives S-integrability. -/
theorem SInt_of_sq_finite {f : ∀ k, (Fin (n k) → Bool) → ℝ}
    (h : IsFinite (iE n (fun k ω => f k ω ^ 2))) : SInt n f := by
  refine ⟨isFinite_of_nonneg_of_le (iE_nonneg fun k ω => abs_nonneg _)
    (iE_mono (g := fun k ω => 1 + f k ω ^ 2) fun k ω => by
      nlinarith [abs_nonneg (f k ω), sq_abs (f k ω)])
    (by rw [iE_add, iE_const]; exact (coe_isFinite 1).add h), fun K hK => ?_⟩
  -- `E[|F|; |F| > K] ≤ E F² / K`
  have hKpos : ∀ᶠ k in hyperfilter ℕ, 0 < K k := hK 0
  have hinv : IsInfinitesimal (Hyperreal.ofSeq fun k => 1 / K k) := by
    rw [isInfinitesimal_ofSeq_iff]
    intro r hr
    filter_upwards [hK (1 / r), hKpos] with k hk hk0
    rw [abs_of_pos (by positivity), div_lt_iff₀ hk0]
    rw [div_lt_iff₀ hr] at hk; linarith
  have h2 := hinv.mul_finite h
  rw [← iE_seq_mul] at h2
  refine isInfinitesimal_of_nonneg_le (iE_nonneg fun k ω => by split_ifs <;> simp)
    (iE_mono_ev ?_) h2
  filter_upwards [hKpos] with k hk0 ω
  split_ifs with h1
  · rw [one_div, ← div_eq_inv_mul, le_div_iff₀ hk0, ← sq_abs]
    nlinarith [abs_nonneg (f k ω)]
  · exact mul_nonneg (by positivity) (sq_nonneg _)

theorem SInt_mul_of_sq {f g : ∀ k, (Fin (n k) → Bool) → ℝ} (hf : SInt n (fun k ω => f k ω ^ 2))
    (hg : SInt n (fun k ω => g k ω ^ 2)) : SInt n (fun k ω => f k ω * g k ω) :=
  (hf.add hg).mono fun k ω => by
    rw [abs_mul]; nlinarith [sq_abs (f k ω), sq_abs (g k ω), abs_nonneg (f k ω),
      abs_nonneg (g k ω), sq_nonneg (|f k ω| - |g k ω|)]

theorem SInt.ae_isFinite {f : ∀ k, (Fin (n k) → Bool) → ℝ} (hf : SInt n f) :
    ∀ᵐ ω ∂(L n), IsFinite (iF n f ω) := ae_isFinite_of_iE_abs hf.1

end Closure

section Continuous

/-- **The standard part commutes with continuous functions** of finitely many finite
internal quantities. -/
theorem stdPart_ifun_continuous {α : Type*} {p : ℕ} (X : Fin p → ℕ → α → ℝ)
    (h : (Fin p → ℝ) → ℝ) (hh : Continuous h) (ω : Ult α)
    (hfin : ∀ l, IsFinite (ifun (X l) ω)) :
    stdPart (ifun (fun k a => h (fun l => X l k a)) ω) =
      h (fun l => stdPart (ifun (X l) ω)) := by
  obtain ⟨u, rfl⟩ := exists_rep ω
  set y : Fin p → ℝ := fun l => stdPart (ifun (X l) (u : Ult α))
  refine stdPart_unique ?_
  show IsInfinitesimal (Hyperreal.ofSeq (fun k => h (fun l => X l k (u k)) - h y))
  rw [isInfinitesimal_ofSeq_iff]
  intro r hr
  obtain ⟨δ, hδ, hδh⟩ := Metric.continuous_iff.1 hh y r hr
  have hcoord : ∀ l, ∀ᶠ k in hyperfilter ℕ, |X l k (u k) - y l| < δ := by
    intro l
    have : IsInfinitesimal (Hyperreal.ofSeq (fun k => X l k (u k) - y l)) :=
      isInfinitesimal_sub_stdPart (hfin l)
    rw [isInfinitesimal_ofSeq_iff] at this
    exact this δ hδ
  have hall : ∀ᶠ k in hyperfilter ℕ, ∀ l, |X l k (u k) - y l| < δ :=
    eventually_all.2 hcoord
  filter_upwards [hall] with k hk
  have := hδh (fun l => X l k (u k)) (by
    rw [dist_pi_lt_iff hδ]; intro l; rw [Real.dist_eq]; exact hk l)
  rwa [Real.dist_eq] at this

end Continuous

section Walk

open QE.Prob

variable {n : ℕ → ℕ} {T : ℝ}

/-- The coarse-grained walk vector `(W(t_l))_l` on `N` coins (Walsh signs). -/
def walkVec (T : ℝ) (N : ℕ) {p : ℕ} (t : Fin p → ℝ≥0) (ω : Fin N → Bool) : Fin p → ℝ :=
  fun l => √(T / N) * ∑ i ∈ Finset.univ.filter (fun i : Fin N => (i : ℕ) < walkIdx T N (t l)),
    QE.OpenSto.Walsh.sgn (ω i)

theorem sum_fin_lt_eq_blockSum {N K : ℕ} (hK : K ≤ N) (ω : ℕ → Bool) :
    ∑ i ∈ Finset.univ.filter (fun i : Fin N => (i : ℕ) < K), (QE.OpenSto.Walsh.sgn (ω i) : ℝ) =
      blockSum ω 0 K := by
  unfold blockSum
  rw [Finset.sum_filter, Fin.sum_univ_eq_sum_range (fun i => if i < K then
    (QE.OpenSto.Walsh.sgn (ω i) : ℝ) else 0), ← Finset.sum_filter]
  have : (Finset.range N).filter (· < K) = Finset.Ico 0 K := by
    ext j; simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]; omega
  rw [this]; rfl

theorem eventually_pos_of_unlimited (hn : IsUnlimited ((n : ℕ → ℕ) : Ult ℕ)) :
    ∀ᶠ k in hyperfilter ℕ, 0 < n k := Germ.coe_lt.1 (hn 0)

/-- On the coin space, the internal walk vector is Anderson's walk. -/
theorem coinFun_walkVec (hT : 0 < T) {p : ℕ} (t : Fin p → ℝ≥0) (htT : ∀ l, (t l : ℝ) ≤ T)
    (hn : IsUnlimited ((n : ℕ → ℕ) : Ult ℕ)) (h : (Fin p → ℝ) → ℝ) :
    iF n (fun k ω => h (walkVec T (n k) t ω)) =
      ifun (fun k ω => h (fun l => walkSeq T n (t l) k ω)) := by
  refine ifun_congr ?_
  filter_upwards [eventually_pos_of_unlimited hn] with k hk
  funext ω
  simp only [coinFun, walkVec, walkSeq]
  congr 1; funext l
  simp only [walkVec]
  rw [sum_fin_lt_eq_blockSum (walkIdx_le hT hk (htT l))]

/-- **Walk transfer.** For a bounded continuous `h`, the shadow of the internal expectation
of `h(W(t_1), …, W(t_p))` is the Loeb expectation of `h(b(t_1), …, b(t_p))`. -/
theorem st_E_walk (hT : 0 < T) (hn : IsUnlimited ((n : ℕ → ℕ) : Ult ℕ)) {p : ℕ}
    (t : Fin p → ℝ≥0) (htT : ∀ l, (t l : ℝ) ≤ T) (h : (Fin p → ℝ) → ℝ) (hh : Continuous h)
    {C : ℝ} (hC : ∀ x, |h x| ≤ C) :
    stdPart (Hyperreal.ofSeq fun k =>
        QE.OpenSto.Walsh.E (fun ω : Fin (n k) → Bool => h (walkVec T (n k) t ω))) =
      ∫ ω, h (fun l => andersonB T n (t l) ω) ∂(L n) := by
  have hb := st_iE_of_bdd (n := n) (fun k ω => h (walkVec T (n k) t ω)) (fun k ω => hC _)
  unfold iE at hb
  rw [hb]
  refine integral_congr_ae ?_
  have hfin : ∀ᵐ ω ∂(L n), ∀ l, IsFinite (andersonW T n (t l) ω) :=
    ae_all_iff.2 fun l => ae_isFinite_andersonW hT hn (htT l)
  filter_upwards [hfin] with ω hω
  rw [coinFun_walkVec hT t htT hn h]
  exact stdPart_ifun_continuous (fun l => walkSeq T n (t l)) h hh ω hω

/-- The standard part of the internal walk is `b` almost surely. -/
theorem ae_st_walk (hT : 0 < T) (hn : IsUnlimited ((n : ℕ → ℕ) : Ult ℕ)) {p : ℕ}
    (t : Fin p → ℝ≥0) (htT : ∀ l, (t l : ℝ) ≤ T) (h : (Fin p → ℝ) → ℝ) (hh : Continuous h) :
    ∀ᵐ ω ∂(L n), stdPart (iF n (fun k ω => h (walkVec T (n k) t ω)) ω) =
      h (fun l => andersonB T n (t l) ω) := by
  have hfin : ∀ᵐ ω ∂(L n), ∀ l, IsFinite (andersonW T n (t l) ω) :=
    ae_all_iff.2 fun l => ae_isFinite_andersonW hT hn (htT l)
  filter_upwards [hfin] with ω hω
  rw [coinFun_walkVec hT t htT hn h]
  exact stdPart_ifun_continuous (fun l => walkSeq T n (t l)) h hh ω hω

end Walk

section L2

variable {n : ℕ → ℕ}

/-- Fatou, integrable form: for `h ≥ 0` with finite internal mean, `st h` is integrable
and `∫ st h ≤ st E h`. -/
theorem integral_st_le_of_nonneg {h : ∀ k, (Fin (n k) → Bool) → ℝ} (h0 : ∀ k ω, 0 ≤ h k ω)
    (hfin : IsFinite (iE n h)) :
    Integrable (fun ω => stdPart (iF n h ω)) (L n) ∧
      ∫ ω, stdPart (iF n h ω) ∂(L n) ≤ stdPart (iE n h) := by
  have hF0 : ∀ ω, 0 ≤ stdPart (iF n h ω) := fun ω =>
    stdPart_nonneg (by have := iF_le h0 ω; rwa [iF_const] at this)
  have hlin := lintegral_st_le h h0
  rw [stE_of_isFinite hfin] at hlin
  have hint : Integrable (fun ω => stdPart (iF n h ω)) (L n) := by
    refine ⟨(measurable_st_iF h).aestronglyMeasurable, ?_⟩
    unfold HasFiniteIntegral
    have e : ∀ ω, ‖stdPart (iF n h ω)‖ₑ = ENNReal.ofReal (stdPart (iF n h ω)) := by
      intro ω; rw [Real.enorm_eq_ofReal_abs, abs_of_nonneg (hF0 ω)]
    simp_rw [e]; exact lt_of_le_of_lt hlin ENNReal.ofReal_lt_top
  refine ⟨hint, ?_⟩
  rw [integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall hF0)
    (measurable_st_iF h).aestronglyMeasurable]
  have hst0 : 0 ≤ stdPart (iE n h) := stdPart_nonneg (iE_nonneg h0)
  calc (∫⁻ ω, ENNReal.ofReal (stdPart (iF n h ω)) ∂(L n)).toReal
      ≤ (ENNReal.ofReal (stdPart (iE n h))).toReal :=
        ENNReal.toReal_mono ENNReal.ofReal_ne_top hlin
    _ = stdPart (iE n h) := ENNReal.toReal_ofReal hst0

theorem isFinite_of_sq_isFinite {x : ℝ*} (h : IsFinite (x ^ 2)) : IsFinite x := by
  obtain ⟨r, hr⟩ := (isFinite_iff_abs_le _).1 h
  refine isFinite_of_abs_le (r := 1 + r) ?_
  rw [abs_of_nonneg (sq_nonneg x)] at hr
  push_cast
  nlinarith [abs_nonneg x, sq_abs x]

/-- Fatou in `L²`: `∫ (st F - st G)² ≤ st E (F - G)²` for a.e. finite `F`, `G`. -/
theorem integral_sq_sub_le {f g : ∀ k, (Fin (n k) → Bool) → ℝ}
    (hf : ∀ᵐ ω ∂(L n), IsFinite (iF n f ω)) (hg : ∀ᵐ ω ∂(L n), IsFinite (iF n g ω))
    (hfin : IsFinite (iE n (fun k ω => (f k ω - g k ω) ^ 2))) :
    Integrable (fun ω => (stdPart (iF n f ω) - stdPart (iF n g ω)) ^ 2) (L n) ∧
      ∫ ω, (stdPart (iF n f ω) - stdPart (iF n g ω)) ^ 2 ∂(L n) ≤
        stdPart (iE n (fun k ω => (f k ω - g k ω) ^ 2)) := by
  obtain ⟨hi, hle⟩ := integral_st_le_of_nonneg (n := n)
    (h := fun k ω => (f k ω - g k ω) ^ 2) (fun k ω => sq_nonneg _) hfin
  have hae : (fun ω => stdPart (iF n (fun k ω => (f k ω - g k ω) ^ 2) ω)) =ᵐ[L n]
      fun ω => (stdPart (iF n f ω) - stdPart (iF n g ω)) ^ 2 := by
    filter_upwards [hf, hg] with ω h1 h2
    have e : iF n (fun k ω => (f k ω - g k ω) ^ 2) ω = (iF n f ω - iF n g ω) ^ 2 := by
      rw [iF_sq (fun k ω => f k ω - g k ω), iF_sub]
    rw [e, sq, stdPart_mul ((h1.add (isFinite_neg h2)) |> fun h => by rwa [← sub_eq_add_neg] at h)
      ((h1.add (isFinite_neg h2)) |> fun h => by rwa [← sub_eq_add_neg] at h),
      stdPart_sub h1 h2, sq]
  exact ⟨hi.congr hae, by rwa [← integral_congr_ae hae]⟩

theorem SInt.ae_isFinite_of_sq {f : ∀ k, (Fin (n k) → Bool) → ℝ}
    (hf : SInt n (fun k ω => f k ω ^ 2)) : ∀ᵐ ω ∂(L n), IsFinite (iF n f ω) := by
  filter_upwards [hf.ae_isFinite] with ω hω
  refine isFinite_of_sq_isFinite ?_
  rwa [iF_sq] at hω

/-- **The `L²` identity**: for `F²`, `G²` S-integrable, `∫ st F · st G = st E[F G]`. -/
theorem integral_st_mul {f g : ∀ k, (Fin (n k) → Bool) → ℝ}
    (hf : SInt n (fun k ω => f k ω ^ 2)) (hg : SInt n (fun k ω => g k ω ^ 2)) :
    ∫ ω, stdPart (iF n f ω) * stdPart (iF n g ω) ∂(L n) =
      stdPart (iE n (fun k ω => f k ω * g k ω)) := by
  obtain ⟨-, h⟩ := st_iE_eq_integral (SInt_mul_of_sq hf hg)
  rw [h]
  refine integral_congr_ae ?_
  filter_upwards [hf.ae_isFinite_of_sq, hg.ae_isFinite_of_sq] with ω h1 h2
  rw [iF_mul, stdPart_mul h1 h2]

/-- For `F²` S-integrable, `st F ∈ L²(Loeb)`. -/
theorem memLp_st {f : ∀ k, (Fin (n k) → Bool) → ℝ} (hf : SInt n (fun k ω => f k ω ^ 2)) :
    MemLp (fun ω => stdPart (iF n f ω)) 2 (L n) := by
  rw [memLp_two_iff_integrable_sq (measurable_st_iF f).aestronglyMeasurable]
  refine (st_iE_eq_integral hf).1.congr ?_
  filter_upwards [hf.ae_isFinite_of_sq] with ω h1
  rw [iF_sq, sq, stdPart_mul h1 h1, sq]

theorem integral_st_sq {f : ∀ k, (Fin (n k) → Bool) → ℝ} (hf : SInt n (fun k ω => f k ω ^ 2)) :
    ∫ ω, stdPart (iF n f ω) ^ 2 ∂(L n) = stdPart (iE n (fun k ω => f k ω ^ 2)) := by
  have := integral_st_mul hf hf
  simp_rw [← sq] at this; exact this

end L2

section Law

/-- Telescoping along a finite partition. -/
theorem telescope_fin {M : ℕ} (x : Fin (M + 1) → ℝ) (j : Fin (M + 1)) :
    x j - x 0 = ∑ i ∈ Finset.univ.filter (fun i : Fin M => (i : ℕ) < j),
      (x i.succ - x i.castSucc) := by
  let g : ℕ → ℝ := fun i => if h : i < M + 1 then x ⟨i, h⟩ else 0
  have hsum : ∑ i ∈ Finset.univ.filter (fun i : Fin M => (i : ℕ) < j),
      (x i.succ - x i.castSucc) = ∑ i ∈ Finset.range j, (g (i + 1) - g i) := by
    have hterm : ∀ a : Fin M, (if (a : ℕ) < (j : ℕ) then x a.succ - x a.castSucc else 0) =
        (fun i : ℕ => if i < (j : ℕ) then g (i + 1) - g i else 0) a := by
      intro a
      simp only [g]
      have h1 : (a : ℕ) + 1 < M + 1 := by omega
      have h2 : (a : ℕ) < M + 1 := by omega
      simp only [h1, h2, ↓reduceDIte]; rfl
    rw [Finset.sum_filter, Finset.sum_congr rfl (fun a _ => hterm a),
      Fin.sum_univ_eq_sum_range (fun i : ℕ => if i < (j : ℕ) then g (i + 1) - g i else 0) M,
      ← Finset.sum_filter]
    congr 1; ext i; simp only [Finset.mem_filter, Finset.mem_range]; omega
  rw [hsum, Finset.sum_range_sub]
  simp only [g, j.isLt, Nat.succ_pos M, ↓reduceDIte]
  rfl

theorem nndist_coe_of_le {a b : ℝ≥0} (h : b ≤ a) : nndist a.1 b.1 = a - b := by
  ext
  rw [coe_nndist, Real.dist_eq, NNReal.coe_sub h, abs_of_nonneg (by simp [h])]; rfl

/-- **A law determined by increments.** If `X 0 = 0` a.e. and the increments of `X` along
a partition `s` (with `s 0 = 0`) have law `ν`, the law of `(X (s (j l)))_l` is the image of `ν`
under the partial-sum map. -/
theorem map_eq_of_increments {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {M p : ℕ}
    (X : ℝ≥0 → Ω → ℝ) (hX0 : ∀ᵐ ω ∂μ, X 0 ω = 0) (s : Fin (M + 1) → ℝ≥0) (hs0 : s 0 = 0)
    {ν : Measure (Fin M → ℝ)}
    (hlaw : HasLaw (fun ω (i : Fin M) => X (s i.succ) ω - X (s i.castSucc) ω) ν μ)
    (j : Fin p → Fin (M + 1)) :
    μ.map (fun ω l => X (s (j l)) ω) =
      ν.map (fun δ l => ∑ i ∈ Finset.univ.filter (fun i : Fin M => (i : ℕ) < j l), δ i) := by
  have hae : (fun ω l => X (s (j l)) ω) =ᵐ[μ]
      (fun δ l => ∑ i ∈ Finset.univ.filter (fun i : Fin M => (i : ℕ) < j l), δ i) ∘
        (fun ω (i : Fin M) => X (s i.succ) ω - X (s i.castSucc) ω) := by
    filter_upwards [hX0] with ω hω
    funext l
    simp only [Function.comp]
    rw [← telescope_fin (fun i => X (s i) ω) (j l), hs0, hω, sub_zero]
  rw [Measure.map_congr hae, ← AEMeasurable.map_map_of_aemeasurable _ hlaw.aemeasurable,
    hlaw.map_eq]
  · rw [hlaw.map_eq]
    exact (Measurable.of_eval fun l => Finset.measurable_sum _ fun i _ =>
      measurable_pi_apply i).aemeasurable

/-- A sorted partition through `0` and the times `t l`. -/
theorem exists_partition {p : ℕ} (t : Fin p → ℝ≥0) :
    ∃ (M : ℕ) (s : Fin (M + 1) → ℝ≥0) (j : Fin p → Fin (M + 1)),
      Monotone s ∧ s 0 = 0 ∧ (∀ l, s (j l) = t l) ∧ (∀ i, s i = 0 ∨ ∃ l, s i = t l) := by
  classical
  let U : Finset ℝ≥0 := insert 0 (Finset.univ.image t)
  obtain ⟨M, hM⟩ : ∃ M, U.card = M + 1 :=
    ⟨U.card - 1, by have : 0 < U.card := Finset.card_pos.2 ⟨0, Finset.mem_insert_self _ _⟩; omega⟩
  let e := U.orderEmbOfFin hM
  have hmem : ∀ i, e i ∈ U := fun i => U.orderEmbOfFin_mem hM i
  have hrange : ∀ x ∈ U, ∃ i, e i = x := by
    intro x hx
    have : x ∈ Set.range e := by rw [Finset.range_orderEmbOfFin]; exact hx
    exact this
  have htU : ∀ l, t l ∈ U := fun l =>
    Finset.mem_insert_of_mem (Finset.mem_image_of_mem t (Finset.mem_univ l))
  refine ⟨M, e, fun l => (hrange (t l) (htU l)).choose, e.monotone, ?_, fun l =>
    (hrange (t l) (htU l)).choose_spec, fun i => ?_⟩
  · obtain ⟨i, hi⟩ := hrange 0 (Finset.mem_insert_self _ _)
    exact le_antisymm (hi ▸ e.monotone (Fin.zero_le i)) bot_le
  · have := hmem i
    rcases Finset.mem_insert.1 this with h | h
    · exact Or.inl h
    · obtain ⟨l, -, hl⟩ := Finset.mem_image.1 h
      exact Or.inr ⟨l, hl.symm⟩

variable {n : ℕ → ℕ} {T : ℝ}

/-- **Law identification**: the finite-dimensional laws of any (Mathlib) Brownian motion on
`[0, T]` coincide with those of the Loeb shadow `b = st W` of Anderson's walk. -/
theorem map_brownian_eq_map_andersonB (hT : 0 < T) (hn : IsUnlimited ((n : ℕ → ℕ) : Ult ℕ))
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ}
    (hB : IsPreBrownianReal B P) {p : ℕ} (t : Fin p → ℝ≥0) (htT : ∀ l, (t l : ℝ) ≤ T) :
    P.map (fun ω l => B (t l) ω) = (L n).map (fun ω l => andersonB T n (t l) ω) := by
  have := hB.isGaussianProcess.isProbabilityMeasure
  obtain ⟨M, s, j, hs, hs0, hj, hsv⟩ := exists_partition t
  have hsT : ∀ i, (s i : ℝ) ≤ T := by
    intro i; rcases hsv i with h | ⟨l, h⟩
    · rw [h]; exact hT.le
    · rw [h]; exact htT l
  let ν : Measure (Fin M → ℝ) := Measure.pi fun i => gaussianReal 0 (s i.succ - s i.castSucc)
  -- the Brownian side
  have hlawB : HasLaw (fun ω (i : Fin M) => B (s i.succ) ω - B (s i.castSucc) ω) ν P := by
    refine iIndepFun.hasLaw_pi (X := fun (i : Fin M) ω => B (s i.succ) ω - B (s i.castSucc) ω)
      (fun i => ?_) (hB.hasIndepIncrements M s hs)
    have := hB.hasLaw_sub (s i.succ) (s i.castSucc)
    rwa [nndist_coe_of_le (hs (Fin.castSucc_le_succ i))] at this
  have hlawb : HasLaw (fun ω (i : Fin M) => andersonB T n (s i.succ) ω -
      andersonB T n (s i.castSucc) ω) ν (L n) :=
    andersonB_increments_hasLaw hT hn s hs hsT
  have e1 := map_eq_of_increments B hB.eval_zero_ae_eq_zero s hs0 hlawB j
  have e2 := map_eq_of_increments (μ := L n) (fun t ω => andersonB T n t ω)
    (Eventually.of_forall fun ω => by simpa using andersonB_zero T n ω) s hs0 hlawb j
  simp only [hj] at e1 e2
  rw [e1, e2]

/-- Expectations of functions of `(B(t_l))_l` computed on the Loeb space. -/
theorem integral_brownian_eq (hT : 0 < T) (hn : IsUnlimited ((n : ℕ → ℕ) : Ult ℕ))
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ}
    (hB : IsPreBrownianReal B P) {p : ℕ} (t : Fin p → ℝ≥0) (htT : ∀ l, (t l : ℝ) ≤ T)
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (h : (Fin p → ℝ) → E)
    (hh : StronglyMeasurable h) :
    ∫ ω, h (fun l => B (t l) ω) ∂P = ∫ ω, h (fun l => andersonB T n (t l) ω) ∂(L n) := by
  have hBm : AEMeasurable (fun ω l => B (t l) ω) P :=
    AEMeasurable.of_eval fun l => hB.aemeasurable (t l)
  have hbm : Measurable (fun ω l => andersonB T n (t l) ω) :=
    Measurable.of_eval fun l => measurable_andersonB T n (t l)
  rw [← integral_map hBm hh.aestronglyMeasurable, map_brownian_eq_map_andersonB hT hn hB t htT,
    integral_map hbm.aemeasurable hh.aestronglyMeasurable]

/-- **Standard Gaussian increments on the Loeb space**: for the walk with horizon `T = n₀`,
the unit increments `b(j+1) - b(j)` are i.i.d. `N(0,1)`. -/
theorem hasLaw_unit_increments (hn : IsUnlimited ((n : ℕ → ℕ) : Ult ℕ)) (n₀ : ℕ)
    (hn₀ : 0 < n₀) :
    HasLaw (fun ω (j : Fin n₀) => andersonB n₀ n ((j : ℝ) + 1) ω - andersonB n₀ n j ω)
      (Measure.pi fun _ => gaussianReal 0 1) (L n) := by
  let s : Fin (n₀ + 1) → ℝ≥0 := fun i => (i : ℝ≥0)
  have hs : Monotone s := fun a b h => by simp only [s]; exact_mod_cast h
  have hsT : ∀ i, (s i : ℝ) ≤ (n₀ : ℝ) := fun i => by
    simp only [s, NNReal.coe_natCast]; exact_mod_cast Nat.lt_succ_iff.1 i.isLt
  have h := andersonB_increments_hasLaw (T := (n₀ : ℝ)) (by exact_mod_cast hn₀) hn s hs hsT
  have e1 : ∀ i : Fin n₀, s i.succ - s i.castSucc = 1 := by
    intro i; simp only [s, Fin.val_succ, Fin.val_castSucc]; push_cast
    exact add_tsub_cancel_left _ _
  simp only [e1] at h
  convert h using 3 with ω i
  simp [s]

/-- Any i.i.d. standard Gaussian vector can be replaced by the Loeb one in expectations. -/
theorem integral_iid_gaussian_eq (hn : IsUnlimited ((n : ℕ → ℕ) : Ult ℕ)) (n₀ : ℕ) (hn₀ : 0 < n₀)
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {G : Ω → Fin n₀ → ℝ}
    (hG : HasLaw G (Measure.pi fun _ => gaussianReal 0 1) P)
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (H : (Fin n₀ → ℝ) → E)
    (hH : StronglyMeasurable H) :
    ∫ ω, H (G ω) ∂P =
      ∫ ω, H (fun j => andersonB n₀ n ((j : ℝ) + 1) ω - andersonB n₀ n j ω) ∂(L n) := by
  have h1 := hG.integral_comp hH.aestronglyMeasurable
  have h2 := (hasLaw_unit_increments hn n₀ hn₀).integral_comp hH.aestronglyMeasurable
  simp only [Function.comp_def] at h1 h2
  rw [h1, h2]

end Law

end QE.Chaos.Loeb

/-! # Part D. Density of exponentials of increments -/


namespace QE.Chaos.Dense

open MeasureTheory ProbabilityTheory Finset Complex
open scoped ENNReal NNReal

/-- **Real exponential moments determine a finite measure on `ℝ^r`.** -/
theorem ext_of_exp_moments {r : ℕ} {μ ν : Measure (Fin r → ℝ)} [IsFiniteMeasure μ]
    [IsFiniteMeasure ν]
    (hμ : ∀ a : Fin r → ℝ, Integrable (fun x => Real.exp (∑ i, a i * x i)) μ)
    (h : ∀ a : Fin r → ℝ,
      ∫ x, Real.exp (∑ i, a i * x i) ∂μ = ∫ x, Real.exp (∑ i, a i * x i) ∂ν) : μ = ν := by
  have hL : ∀ (L : StrongDual ℝ (Fin r → ℝ)) (t : ℝ) (x : Fin r → ℝ),
      t * L x = ∑ i, (t * L (fun j => if i = j then 1 else 0)) * x i := by
    intro L t x
    have := LinearMap.pi_apply_eq_sum_univ (L : (Fin r → ℝ) →ₗ[ℝ] ℝ) x
    simp only [ContinuousLinearMap.coe_coe] at this
    rw [this, Finset.mul_sum]
    apply sum_congr rfl; intro i _
    simp only [smul_eq_mul]; ring
  apply Measure.ext_of_charFunDual
  funext L
  have he : ∀ t, (fun x => Real.exp (t * L x)) =
      fun x => Real.exp (∑ i, (t * L (fun j => if i = j then 1 else 0)) * x i) := by
    intro t; funext x; rw [hL L t x]
  have hmgf : mgf L μ = mgf L ν := by
    funext t; simp only [mgf]; rw [he t]; exact h _
  have hint : integrableExpSet L μ = Set.univ := by
    ext t
    simp only [integrableExpSet, Set.mem_univ, iff_true]
    show Integrable (fun x => Real.exp (t * L x)) μ
    rw [he t]; exact hμ _
  have h0 : μ = 0 ↔ ν = 0 := by
    have h1 := h 0
    simp only [Pi.zero_apply, zero_mul, Finset.sum_const_zero, Real.exp_zero,
      integral_const, smul_eq_mul, mul_one] at h1
    rw [← Measure.measure_univ_eq_zero, ← Measure.measure_univ_eq_zero]
    simp only [Measure.real, ENNReal.toReal_eq_toReal_iff' (measure_ne_top μ _)
      (measure_ne_top ν _)] at h1
    rw [h1]
  have := eqOn_complexMGF_of_mgf' hmgf h0 (show Complex.I.re ∈ interior (integrableExpSet L μ) by
    simp [hint])
  simp only [charFunDual_apply, complexMGF] at this ⊢
  simp_rw [mul_comm _ Complex.I]
  exact this

/-! ## Telescoping along a partition -/

theorem tele {k : ℕ} (f : Fin (k + 1) → ℝ) (i : Fin k) :
    f i.succ - f 0 = ∑ l ∈ univ.filter (· ≤ i), (f l.succ - f l.castSucc) := by
  obtain ⟨m, hm⟩ := i
  induction m with
  | zero =>
    have : univ.filter (· ≤ (⟨0, hm⟩ : Fin k)) = {⟨0, hm⟩} := by
      ext l; simp [Fin.le_def, Fin.ext_iff]
    rw [this, sum_singleton]; rfl
  | succ m ih =>
    have hm' : m < k := by omega
    have : univ.filter (· ≤ (⟨m + 1, hm⟩ : Fin k)) =
        insert ⟨m + 1, hm⟩ (univ.filter (· ≤ (⟨m, hm'⟩ : Fin k))) := by
      ext l; simp [Fin.le_def, Fin.ext_iff]; omega
    rw [this, sum_insert (by simp [Fin.le_def]), ← ih hm']
    have e : (Fin.castSucc (⟨m + 1, hm⟩ : Fin k)) = Fin.succ ⟨m, hm'⟩ := by
      ext; simp
    rw [e]; ring

variable {Ω : Type*} [mΩ : MeasurableSpace Ω]

/-- The path of the process on `[0,T]`. -/
def path (b : ℝ → Ω → ℝ) (T : ℝ) (ω : Ω) : Set.Icc (0 : ℝ) T → ℝ := fun t => b t ω

/-- The vector of increments along a partition `s`. -/
def incr (b : ℝ → Ω → ℝ) {r : ℕ} (s : Fin (r + 1) → ℝ) (ω : Ω) : Fin r → ℝ :=
  fun i => b (s i.succ) ω - b (s i.castSucc) ω

/-- The σ-algebra generated by the process on `[0,T]`. -/
def pathSigma (b : ℝ → Ω → ℝ) (T : ℝ) : MeasurableSpace Ω :=
  MeasurableSpace.comap (path b T) MeasurableSpace.pi

theorem measurable_incr {b : ℝ → Ω → ℝ} (hb : ∀ t, Measurable (b t)) {r : ℕ}
    (s : Fin (r + 1) → ℝ) : Measurable (incr b s) :=
  Measurable.of_eval fun _ => (hb _).sub (hb _)

theorem measurable_path {b : ℝ → Ω → ℝ} (hb : ∀ t, Measurable (b t)) (T : ℝ) :
    Measurable (path b T) :=
  Measurable.of_eval fun t => hb t

theorem pathSigma_le {b : ℝ → Ω → ℝ} (hb : ∀ t, Measurable (b t)) (T : ℝ) :
    pathSigma b T ≤ mΩ :=
  (measurable_path hb T).comap_le

/-- Finitely many values of the path are a measurable function of the increments along a
partition of `[0,T]` starting at `0`. -/
theorem exists_partition (b : ℝ → Ω → ℝ) (hb0 : ∀ ω, b 0 ω = 0) {T : ℝ} (hT : 0 ≤ T)
    (J : Finset (Set.Icc (0 : ℝ) T)) :
    ∃ (k : ℕ) (s : Fin (k + 1) → ℝ), Monotone s ∧ s 0 = 0 ∧ (∀ i, s i ∈ Set.Icc 0 T) ∧
      ∃ φ : (Fin k → ℝ) → (J → ℝ), Measurable φ ∧
        ∀ ω, (fun j : J => b (j : Set.Icc (0:ℝ) T) ω) = φ (incr b s ω) := by
  classical
  let iso := J.orderIsoOfFin rfl
  let s : Fin (J.card + 1) → ℝ := Fin.cons 0 (fun i => (((iso i : J) : Set.Icc (0:ℝ) T) : ℝ))
  have hs0 : s 0 = 0 := rfl
  have hsucc : ∀ i, s i.succ = (((iso i : J) : Set.Icc (0:ℝ) T) : ℝ) := fun i => rfl
  have hmem : ∀ i, s i ∈ Set.Icc (0:ℝ) T := by
    intro i
    refine Fin.cases ?_ (fun i => ?_) i
    · rw [hs0]; exact ⟨le_rfl, hT⟩
    · rw [hsucc]; exact ((iso i : J) : Set.Icc (0:ℝ) T).2
  have hmono : Monotone s := by
    intro i j hij
    induction i using Fin.cases with
    | zero => rw [hs0]; exact (hmem j).1
    | succ i' =>
    induction j using Fin.cases with
    | zero => exact absurd hij (by simp [Fin.le_def])
    | succ j' =>
    have hij' := hij
    rw [hsucc, hsucc]
    have : i' ≤ j' := Fin.succ_le_succ_iff.mp hij'
    exact iso.monotone this
  refine ⟨J.card, s, hmono, hs0, hmem,
    fun y j => ∑ l ∈ univ.filter (· ≤ iso.symm j), y l, ?_, ?_⟩
  · exact Measurable.of_eval fun j => Finset.measurable_sum _ fun l _ => measurable_pi_apply l
  · intro ω; funext j
    have h := tele (fun m => b (s m) ω) (iso.symm j)
    simp only [hs0, hb0, sub_zero, hsucc, OrderIso.apply_symm_apply] at h
    rw [h]; rfl

theorem ofReal_max_zero' (r : ℝ) : ENNReal.ofReal (max r 0) = ENNReal.ofReal r := by
  rcases le_total r 0 with h | h
  · rw [max_eq_right h, ENNReal.ofReal_zero, ENNReal.ofReal_eq_zero.2 h]
  · rw [max_eq_left h]

/-- **Density of exponentials of increments.** An `L²` function measurable with respect to the
σ-algebra of the process `b` on `[0,T]` (with `b 0 = 0`) which is orthogonal to every
exponential `exp (∑ aᵢ (b(sᵢ₊₁) - b(sᵢ)))` along every partition `0 = s₀ ≤ ⋯ ≤ s_r ≤ T` is
zero almost everywhere. -/
theorem ae_eq_zero_of_orthogonal_exp {P : Measure Ω} [IsProbabilityMeasure P] {T : ℝ}
    (hT : 0 ≤ T) (b : ℝ → Ω → ℝ) (hb : ∀ t, Measurable (b t)) (hb0 : ∀ ω, b 0 ω = 0)
    {R : Ω → ℝ} (hR : MemLp R 2 P) (hRm : AEStronglyMeasurable[pathSigma b T] R P)
    (hexp : ∀ (r : ℕ) (s : Fin (r + 1) → ℝ), Monotone s → s 0 = 0 → (∀ i, s i ≤ T) →
      ∀ a : Fin r → ℝ, MemLp (fun ω => Real.exp (∑ i, a i * incr b s ω i)) 2 P)
    (horth : ∀ (r : ℕ) (s : Fin (r + 1) → ℝ), Monotone s → s 0 = 0 → (∀ i, s i ≤ T) →
      ∀ a : Fin r → ℝ, ∫ ω, R ω * Real.exp (∑ i, a i * incr b s ω i) ∂P = 0) :
    R =ᵐ[P] 0 := by
  have hm := pathSigma_le hb T
  set R' := hRm.mk R with hR'def
  have hR'm : StronglyMeasurable[pathSigma b T] R' := hRm.stronglyMeasurable_mk
  have hRR' : R =ᵐ[P] R' := hRm.ae_eq_mk
  have hR'meas : Measurable R' := (hR'm.mono hm).measurable
  have hR'2 : MemLp R' 2 P := hR.ae_eq hRR'
  have hR'int : Integrable R' P := hR'2.integrable one_le_two
  have horth' : ∀ (r : ℕ) (s : Fin (r + 1) → ℝ), Monotone s → s 0 = 0 → (∀ i, s i ≤ T) →
      ∀ a : Fin r → ℝ, ∫ ω, R' ω * Real.exp (∑ i, a i * incr b s ω i) ∂P = 0 := by
    intro r s h1 h2 h3 a
    rw [← horth r s h1 h2 h3 a]
    refine integral_congr_ae ?_
    filter_upwards [hRR'] with ω hω; rw [hω]
  -- the positive and negative parts as finite measures
  let fp : Ω → ℝ≥0 := fun ω => (R' ω).toNNReal
  let fn : Ω → ℝ≥0 := fun ω => (-R' ω).toNNReal
  have hfp : Measurable fp := hR'meas.real_toNNReal
  have hfn : Measurable fn := hR'meas.neg.real_toNNReal
  let μp := P.withDensity (fun ω => (fp ω : ℝ≥0∞))
  let μn := P.withDensity (fun ω => (fn ω : ℝ≥0∞))
  haveI : IsFiniteMeasure μp := isFiniteMeasure_withDensity_ofReal hR'int.2
  haveI : IsFiniteMeasure μn := isFiniteMeasure_withDensity_ofReal hR'int.neg.2
  -- equality of the laws of the increments
  have hlaw : ∀ (k : ℕ) (s : Fin (k + 1) → ℝ), Monotone s → s 0 = 0 → (∀ i, s i ≤ T) →
      μp.map (incr b s) = μn.map (incr b s) := by
    intro k s h1 h2 h3
    have hΔ := measurable_incr hb s
    have hc : ∀ a : Fin k → ℝ, Continuous (fun x : Fin k → ℝ => Real.exp (∑ i, a i * x i)) :=
      fun a => by fun_prop
    have hprod : ∀ a : Fin k → ℝ,
        Integrable (fun ω => R' ω * Real.exp (∑ i, a i * incr b s ω i)) P :=
      fun a => hR'2.integrable_mul (hexp k s h1 h2 h3 a)
    have hint : ∀ (f : Ω → ℝ≥0), Measurable f → (∀ ω, (f ω : ℝ) ≤ |R' ω|) →
        ∀ a : Fin k → ℝ, Integrable (fun x : Fin k → ℝ => Real.exp (∑ i, a i * x i))
          ((P.withDensity (fun ω => (f ω : ℝ≥0∞))).map (incr b s)) := by
      intro f hf hfle a
      rw [integrable_map_measure (hc a).aestronglyMeasurable hΔ.aemeasurable,
        integrable_withDensity_iff_integrable_smul hf]
      refine (hprod a).mono ?_ (Filter.Eventually.of_forall fun ω => ?_)
      · exact ((hf.coe_nnreal_real).mul ((hc a).measurable.comp hΔ)).aestronglyMeasurable
      · simp only [Function.comp, NNReal.smul_def, smul_eq_mul, norm_mul, Real.norm_eq_abs,
          NNReal.abs_eq, abs_of_pos (Real.exp_pos _)]
        exact mul_le_mul_of_nonneg_right (hfle ω) (Real.exp_pos _).le
    have hval : ∀ (f : Ω → ℝ≥0), Measurable f → ∀ a : Fin k → ℝ,
        ∫ x, Real.exp (∑ i, a i * x i) ∂((P.withDensity (fun ω => (f ω : ℝ≥0∞))).map (incr b s))
          = ∫ ω, (f ω : ℝ) * Real.exp (∑ i, a i * incr b s ω i) ∂P := by
      intro f hf a
      rw [integral_map hΔ.aemeasurable (hc a).aestronglyMeasurable,
        integral_withDensity_eq_integral_smul hf]
      rfl
    haveI : IsFiniteMeasure (μp.map (incr b s)) := Measure.isFiniteMeasure_map _ _
    haveI : IsFiniteMeasure (μn.map (incr b s)) := Measure.isFiniteMeasure_map _ _
    refine ext_of_exp_moments (hint fp hfp (fun ω => ?_)) (fun a => ?_)
    · simp only [fp, Real.coe_toNNReal']; exact max_le (le_abs_self _) (abs_nonneg _)
    · rw [hval fp hfp, hval fn hfn, ← sub_eq_zero, ← integral_sub]
      · rw [← horth' k s h1 h2 h3 a]
        congr 1; funext ω
        simp only [fp, fn, Real.coe_toNNReal']
        rcases le_total (R' ω) 0 with h | h
        · rw [max_eq_right h, max_eq_left (by linarith)]; ring
        · rw [max_eq_left h, max_eq_right (by linarith)]; ring
      · refine (hprod a).mono ((hfp.coe_nnreal_real.mul ((hc a).measurable.comp
          hΔ)).aestronglyMeasurable) (Filter.Eventually.of_forall fun ω => ?_)
        simp only [fp, Real.coe_toNNReal', norm_mul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _),
          abs_of_nonneg (le_max_right _ _ : (0:ℝ) ≤ max (R' ω) 0)]
        exact mul_le_mul_of_nonneg_right (max_le (le_abs_self _) (abs_nonneg _)) (Real.exp_pos _).le
      · refine (hprod a).mono ((hfn.coe_nnreal_real.mul ((hc a).measurable.comp
          hΔ)).aestronglyMeasurable) (Filter.Eventually.of_forall fun ω => ?_)
        simp only [fn, Real.coe_toNNReal', norm_mul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _),
          abs_of_nonneg (le_max_right _ _ : (0:ℝ) ≤ max (-R' ω) 0)]
        exact mul_le_mul_of_nonneg_right (max_le (neg_le_abs _) (abs_nonneg _)) (Real.exp_pos _).le
  -- equality on the preimages of measurable cylinders
  have hcyl : ∀ c ∈ MeasureTheory.measurableCylinders (fun _ : Set.Icc (0:ℝ) T => ℝ),
      μp (path b T ⁻¹' c) = μn (path b T ⁻¹' c) := by
    intro c hc
    obtain ⟨J, S, hS, rfl⟩ := (mem_measurableCylinders c).1 hc
    obtain ⟨k, s, h1, h2, h3, φ, hφ, hφeq⟩ := exists_partition b hb0 hT J
    have e : path b T ⁻¹' cylinder J S = incr b s ⁻¹' (φ ⁻¹' S) := by
      ext ω
      simp only [Set.mem_preimage, cylinder]
      rw [← hφeq ω]; rfl
    rw [e, ← Measure.map_apply (measurable_incr hb s) (hφ hS),
      ← Measure.map_apply (measurable_incr hb s) (hφ hS),
      hlaw k s h1 h2 (fun i => (h3 i).2)]
  -- equality on the whole σ-algebra of the process
  have htrim : μp.trim hm = μn.trim hm := by
    refine ext_of_generate_finite (m0 := pathSigma b T) (μ := μp.trim hm) (ν := μn.trim hm)
      (Set.preimage (path b T) '' MeasureTheory.measurableCylinders _) ?_
      (isPiSystem_measurableCylinders.comap _) ?_ ?_
    · show MeasurableSpace.comap (path b T) MeasurableSpace.pi = _
      rw [← generateFrom_measurableCylinders, MeasurableSpace.comap_generateFrom]
    · rintro _ ⟨c, hc, rfl⟩
      have hcm : MeasurableSet[pathSigma b T] (path b T ⁻¹' c) :=
        ⟨c, MeasurableSet.of_mem_measurableCylinders hc, rfl⟩
      rw [trim_measurableSet_eq hm hcm, trim_measurableSet_eq hm hcm]
      exact hcyl c hc
    · rw [trim_measurableSet_eq hm MeasurableSet.univ, trim_measurableSet_eq hm MeasurableSet.univ]
      have hu : (Set.univ : Set (Set.Icc (0:ℝ) T → ℝ)) ∈ MeasureTheory.measurableCylinders _ :=
        (mem_measurableCylinders _).2 ⟨∅, Set.univ, MeasurableSet.univ, (cylinder_univ _).symm⟩
      have := hcyl _ hu
      simpa using this
  -- every σ(b)-set integral of `R'` vanishes
  have hset : ∀ C, MeasurableSet[pathSigma b T] C → ∫ x in C, R' x ∂P = 0 := by
    intro C hC
    have hC' : MeasurableSet C := hm C hC
    have heq : μp C = μn C := by
      rw [← trim_measurableSet_eq hm hC, ← trim_measurableSet_eq hm hC, htrim]
    have hpos : ∫ x in C, max (R' x) 0 ∂P = (μp C).toReal := by
      rw [integral_eq_lintegral_of_nonneg_ae (f := fun x => max (R' x) 0)
        (Filter.Eventually.of_forall fun _ => le_max_right _ _)
        (hR'meas.max measurable_const).aestronglyMeasurable, withDensity_apply _ hC']
      simp_rw [ofReal_max_zero']; rfl
    have hneg : ∫ x in C, max (-R' x) 0 ∂P = (μn C).toReal := by
      rw [integral_eq_lintegral_of_nonneg_ae (f := fun x => max (-R' x) 0)
        (Filter.Eventually.of_forall fun _ => le_max_right _ _)
        (hR'meas.neg.max measurable_const).aestronglyMeasurable, withDensity_apply _ hC']
      simp_rw [ofReal_max_zero']; rfl
    have hsplit : (fun x => R' x) = fun x => max (R' x) 0 - max (-R' x) 0 := by
      funext x
      rcases le_total (R' x) 0 with h | h
      · rw [max_eq_right h, max_eq_left (by linarith)]; ring
      · rw [max_eq_left h, max_eq_right (by linarith)]; ring
    rw [hsplit, integral_sub hR'int.pos_part.integrableOn hR'int.neg_part.integrableOn, hpos, hneg,
      heq, sub_self]
  refine hRR'.trans ?_
  refine ae_eq_of_forall_setIntegral_eq_of_sigmaFinite' hm (fun _ _ _ => hR'int.integrableOn)
    (fun _ _ _ => integrableOn_zero) (fun C hC _ => ?_) hR'm.aestronglyMeasurable
    stronglyMeasurable_const.aestronglyMeasurable
  rw [hset C hC]; simp

/-- **Hilbert-space form.** In `L²(P)`, an element of the closed subspace of
`σ(b)`-measurable classes that is orthogonal to every exponential of increments is `0`. -/
theorem eq_zero_of_orthogonal_exp_Lp {P : Measure Ω} [IsProbabilityMeasure P] {T : ℝ}
    (hT : 0 ≤ T) (b : ℝ → Ω → ℝ) (hb : ∀ t, Measurable (b t)) (hb0 : ∀ ω, b 0 ω = 0)
    (hexp : ∀ (r : ℕ) (s : Fin (r + 1) → ℝ), Monotone s → s 0 = 0 → (∀ i, s i ≤ T) →
      ∀ a : Fin r → ℝ, MemLp (fun ω => Real.exp (∑ i, a i * incr b s ω i)) 2 P)
    (f : Lp ℝ 2 P) (hf : f ∈ lpMeas ℝ ℝ (pathSigma b T) 2 P)
    (horth : ∀ (r : ℕ) (s : Fin (r + 1) → ℝ) (h1 : Monotone s) (h2 : s 0 = 0)
      (h3 : ∀ i, s i ≤ T) (a : Fin r → ℝ),
      inner ℝ ((hexp r s h1 h2 h3 a).toLp _) f = 0) : f = 0 := by
  rw [Lp.eq_zero_iff_ae_eq_zero]
  refine ae_eq_zero_of_orthogonal_exp hT b hb hb0 (Lp.memLp f) hf hexp ?_
  intro r s h1 h2 h3 a
  have h := horth r s h1 h2 h3 a
  rw [MeasureTheory.L2.inner_def] at h
  rw [← h]
  refine integral_congr_ae ?_
  filter_upwards [(hexp r s h1 h2 h3 a).coeFn_toLp] with ω hω
  rw [hω]; simp [mul_comm]

end QE.Chaos.Dense

/-! # Part E. The discrete stochastic exponential and Hermite polynomials -/


namespace QE.Chaos.DExp

open Finset

/-! ## Elementary symmetric sums and power sums -/

/-- Elementary symmetric sum `e_m(x)`. -/
def es {N : ℕ} (m : ℕ) (x : Fin N → ℝ) : ℝ := ∑ S ∈ powersetCard m univ, ∏ i ∈ S, x i

/-- Power sum `p_k(x)`. -/
def ps {N : ℕ} (k : ℕ) (x : Fin N → ℝ) : ℝ := ∑ i, x i ^ k

theorem es_zero {N : ℕ} (x : Fin N → ℝ) : es 0 x = 1 := by simp [es]

theorem es_eq_zero_of_lt {N m : ℕ} (x : Fin N → ℝ) (h : N < m) : es m x = 0 := by
  unfold es
  rw [powersetCard_eq_empty.mpr (by simpa using h), sum_empty]

theorem prod_one_add_eq_sum_es {N : ℕ} (x : Fin N → ℝ) :
    ∏ i, (1 + x i) = ∑ m ∈ range (N + 1), es m x := by
  rw [prod_one_add, sum_powerset, card_univ, Fintype.card_fin]; rfl

theorem aeval_esymm {N : ℕ} (m : ℕ) (x : Fin N → ℝ) :
    MvPolynomial.aeval x (MvPolynomial.esymm (Fin N) ℝ m) = es m x := by
  simp [MvPolynomial.esymm, es, map_sum, map_prod]

theorem aeval_psum {N : ℕ} (k : ℕ) (x : Fin N → ℝ) :
    MvPolynomial.aeval x (MvPolynomial.psum (Fin N) ℝ k) = ps k x := by
  simp [MvPolynomial.psum, ps, map_sum]

/-- **Newton's identities.** -/
theorem newton {N : ℕ} (m : ℕ) (x : Fin N → ℝ) :
    (m : ℝ) * es m x = ∑ k ∈ Icc 1 m, (-1) ^ (k - 1) * es (m - k) x * ps k x := by
  have h := congrArg (MvPolynomial.aeval x) (MvPolynomial.mul_esymm_eq_sum (Fin N) ℝ m)
  simp only [map_mul, map_natCast, map_pow, map_neg, map_one, map_sum, aeval_esymm,
    aeval_psum] at h
  rw [h, mul_sum]
  symm
  apply sum_nbij' (fun k => (m - k, k)) (fun a => a.2)
  · intro k hk
    simp only [mem_Icc] at hk
    simp only [mem_filter, Finset.HasAntidiagonal.mem_antidiagonal]
    omega
  · intro a ha
    simp only [mem_filter, Finset.HasAntidiagonal.mem_antidiagonal] at ha
    simp only [mem_Icc]; omega
  · intro k hk; simp only [mem_Icc] at hk; simp
  · intro a ha
    simp only [mem_filter, Finset.HasAntidiagonal.mem_antidiagonal] at ha
    ext <;> simp; omega
  · intro k hk
    simp only [mem_Icc] at hk
    have e : m + 1 + (m - k) = (k - 1) + 2 * (m + 1 - k) := by omega
    rw [← mul_assoc, ← mul_assoc, ← pow_add, e, pow_add, pow_mul]
    norm_num

/-! ## The homogenised Hermite polynomials -/

/-- `heH m a s = s^{m/2} He_m(a/√s)`, defined by the three-term recursion. -/
def heH : ℕ → ℝ → ℝ → ℝ
  | 0, _, _ => 1
  | 1, a, _ => a
  | m + 2, a, s => a * heH (m + 1) a s - (m + 1) * s * heH m a s

@[simp] theorem heH_zero (a s : ℝ) : heH 0 a s = 1 := rfl
@[simp] theorem heH_one (a s : ℝ) : heH 1 a s = a := rfl
theorem heH_succ_succ (m : ℕ) (a s : ℝ) :
    heH (m + 2) a s = a * heH (m + 1) a s - (m + 1) * s * heH m a s := rfl

theorem derivative_hermite_succ (n : ℕ) :
    Polynomial.derivative (Polynomial.hermite (n + 1)) = ((n : Polynomial ℤ) + 1) * Polynomial.hermite n := by
  induction n with
  | zero => simp [Polynomial.hermite_one, Polynomial.hermite_zero]
  | succ n ih =>
    rw [Polynomial.hermite_succ (n + 1), Polynomial.derivative_sub, Polynomial.derivative_mul,
      Polynomial.derivative_X, ih, Polynomial.hermite_succ n]
    simp only [Polynomial.derivative_mul, Polynomial.derivative_add, Polynomial.derivative_natCast,
      Polynomial.derivative_one]
    push_cast; ring

theorem hermite_succ_succ (n : ℕ) :
    Polynomial.hermite (n + 2) =
      Polynomial.X * Polynomial.hermite (n + 1) - ((n : Polynomial ℤ) + 1) * Polynomial.hermite n := by
  rw [Polynomial.hermite_succ (n + 1), derivative_hermite_succ]

theorem heH_one_eq_hermite (m : ℕ) (a : ℝ) :
    heH m a 1 = Polynomial.aeval a (Polynomial.hermite m) := by
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    match m, ih with
    | 0, _ => simp [Polynomial.hermite_zero]
    | 1, _ => simp [Polynomial.hermite_one]
    | m + 2, ih =>
      rw [heH_succ_succ, hermite_succ_succ, ih (m + 1) (by omega), ih m (by omega)]
      simp

theorem heH_homog (m : ℕ) (c a s : ℝ) : heH m (c * a) (c ^ 2 * s) = c ^ m * heH m a s := by
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    match m, ih with
    | 0, _ => simp
    | 1, _ => simp
    | m + 2, ih =>
      rw [heH_succ_succ, heH_succ_succ, ih (m + 1) (by omega), ih m (by omega)]
      ring

theorem continuous_heH (m : ℕ) : Continuous (fun p : ℝ × ℝ => heH m p.1 p.2) := by
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    match m, ih with
    | 0, _ => exact continuous_const
    | 1, _ => exact continuous_fst
    | m + 2, ih =>
      simp only [heH_succ_succ]
      have h1 := ih (m + 1) (by omega)
      have h0 := ih m (by omega)
      fun_prop


/-! ## Shadows along the hyperfilter -/

section Shadow

open Filter Topology QE.NSA ArchimedeanClass

theorem isInfinitesimal_ofSeq_iff_tendsto (w : ℕ → ℝ) :
    IsInfinitesimal (Hyperreal.ofSeq w) ↔ Tendsto w (hyperfilter ℕ : Filter ℕ) (𝓝 0) := by
  rw [isInfinitesimal_ofSeq_iff, Metric.tendsto_nhds]
  simp only [Real.dist_eq, sub_zero]

/-- A hyperreal `[w]` is finite with standard part `r` iff `w → r` along the hyperfilter. -/
theorem ofSeq_st_iff_tendsto (w : ℕ → ℝ) (r : ℝ) :
    (IsFinite (Hyperreal.ofSeq w) ∧ stdPart (Hyperreal.ofSeq w) = r) ↔
      Tendsto w (hyperfilter ℕ : Filter ℕ) (𝓝 r) := by
  have e : Hyperreal.ofSeq w - (r : ℝ*) = Hyperreal.ofSeq (fun n => w n - r) := rfl
  have key : IsInfinitesimal (Hyperreal.ofSeq w - (r : ℝ*)) ↔
      Tendsto w (hyperfilter ℕ : Filter ℕ) (𝓝 r) := by
    rw [e, isInfinitesimal_ofSeq_iff_tendsto]; exact tendsto_sub_nhds_zero_iff
  rw [← key]
  constructor
  · rintro ⟨hf, hs⟩
    have := isInfinitesimal_sub_stdPart hf
    rwa [hs] at this
  · intro hi
    refine ⟨?_, stdPart_unique hi⟩
    have : Hyperreal.ofSeq w = (Hyperreal.ofSeq w - (r : ℝ*)) + (r : ℝ*) := by ring
    rw [this]; exact hi.isFinite.add (coe_isFinite r)

variable {N : ℕ → ℕ}

/-- The limits of the power sums. -/
def piLim (a s : ℝ) (k : ℕ) : ℝ := if k = 1 then a else if k = 2 then s else 0

theorem newton_value (m : ℕ) (a s : ℝ) :
    (1 / ((m : ℝ) + 1)) * ∑ k ∈ Icc 1 (m + 1),
        (-1) ^ (k - 1) * (heH (m + 1 - k) a s / (m + 1 - k).factorial) * piLim a s k =
      heH (m + 1) a s / (m + 1).factorial := by
  rcases m with _ | m
  · simp [piLim]
  · have hsub : ({1, 2} : Finset ℕ) ⊆ Icc 1 (m + 1 + 1) := by
      intro k hk; simp only [mem_insert, mem_singleton] at hk; simp only [mem_Icc]; omega
    rw [← sum_subset hsub (fun k hk hk' => by
      simp only [mem_insert, mem_singleton, not_or] at hk'
      simp [piLim, hk'.1, hk'.2])]
    rw [sum_pair (by norm_num)]
    simp only [piLim, ite_true, show (2:ℕ) ≠ 1 by norm_num, ite_false]
    have e1 : m + 1 + 1 - 1 = m + 1 := by omega
    have e2 : m + 1 + 1 - 2 = m := by omega
    rw [e1, e2, show m + 1 + 1 = m + 2 from rfl, heH_succ_succ]
    rw [Nat.factorial_succ (m + 1), Nat.factorial_succ m]
    push_cast
    field_simp
    ring

/-- **Shadow of the elementary symmetric sums** (filter form). -/
theorem tendsto_es (x : ∀ j, Fin (N j) → ℝ) {a s : ℝ}
    (h1 : Tendsto (fun j => ps 1 (x j)) (hyperfilter ℕ : Filter ℕ) (𝓝 a))
    (h2 : Tendsto (fun j => ps 2 (x j)) (hyperfilter ℕ : Filter ℕ) (𝓝 s))
    (h3 : ∀ k, 3 ≤ k → Tendsto (fun j => ps k (x j)) (hyperfilter ℕ : Filter ℕ) (𝓝 0))
    (m : ℕ) :
    Tendsto (fun j => es m (x j)) (hyperfilter ℕ : Filter ℕ) (𝓝 (heH m a s / m.factorial)) := by
  have hπ : ∀ k, 1 ≤ k → Tendsto (fun j => ps k (x j)) (hyperfilter ℕ : Filter ℕ)
      (𝓝 (piLim a s k)) := by
    intro k hk
    by_cases e1 : k = 1
    · subst e1; simpa [piLim] using h1
    by_cases e2 : k = 2
    · subst e2; simpa [piLim] using h2
    simpa [piLim, e1, e2] using h3 k (by omega)
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    rcases m with _ | m
    · simp [es_zero]
    · have hN : (fun j => es (m + 1) (x j)) = fun j => (1 / ((m : ℝ) + 1)) *
          ∑ k ∈ Icc 1 (m + 1), (-1) ^ (k - 1) * es (m + 1 - k) (x j) * ps k (x j) := by
        funext j
        rw [← newton]; push_cast
        field_simp
      rw [hN, ← newton_value]
      refine Tendsto.const_mul _ (tendsto_finsetSum _ fun k hk => ?_)
      simp only [mem_Icc] at hk
      exact ((ih (m + 1 - k) (by omega)).const_mul _).mul (hπ k hk.1)

/-- **Shadow of the elementary symmetric sums** (hyperreal form): if `p₁ ≈ a`, `p₂ ≈ s`
and `p_k ≈ 0` for `k ≥ 3`, then `st e_m = heH_m(a, s)/m!`. -/
theorem st_es (x : ∀ j, Fin (N j) → ℝ) {a s : ℝ}
    (h1 : IsFinite (Hyperreal.ofSeq fun j => ps 1 (x j)) ∧
      stdPart (Hyperreal.ofSeq fun j => ps 1 (x j)) = a)
    (h2 : IsFinite (Hyperreal.ofSeq fun j => ps 2 (x j)) ∧
      stdPart (Hyperreal.ofSeq fun j => ps 2 (x j)) = s)
    (h3 : ∀ k, 3 ≤ k → IsInfinitesimal (Hyperreal.ofSeq fun j => ps k (x j))) (m : ℕ) :
    IsFinite (Hyperreal.ofSeq fun j => es m (x j)) ∧
      stdPart (Hyperreal.ofSeq fun j => es m (x j)) = heH m a s / m.factorial := by
  rw [ofSeq_st_iff_tendsto] at h1 h2 ⊢
  exact tendsto_es x h1 h2 (fun k hk => (isInfinitesimal_ofSeq_iff_tendsto _).1 (h3 k hk)) m

theorem abs_ps_le {n : ℕ} (x : Fin n → ℝ) {M : ℝ} (hM : ∀ i, |x i| ≤ M) {k : ℕ} (hk : 2 ≤ k) :
    |ps k x| ≤ M ^ (k - 2) * ps 2 x := by
  unfold ps
  rw [mul_sum]
  refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun i _ => ?_)
  have h0 : 0 ≤ |x i| := abs_nonneg _
  have e : |x i ^ k| = |x i| ^ (k - 2) * x i ^ 2 := by
    rw [abs_pow, ← sq_abs (x i), ← pow_add]; congr 1; omega
  rw [e]
  exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ h0 (hM i) _) (sq_nonneg _)

/-- Higher power sums are negligible when the increments are uniformly small. -/
theorem tendsto_ps_zero (x : ∀ j, Fin (N j) → ℝ) (M : ℕ → ℝ) (hM : ∀ j i, |x j i| ≤ M j)
    (hM0 : Tendsto M (hyperfilter ℕ : Filter ℕ) (𝓝 0)) {s : ℝ}
    (h2 : Tendsto (fun j => ps 2 (x j)) (hyperfilter ℕ : Filter ℕ) (𝓝 s))
    (k : ℕ) (hk : 3 ≤ k) :
    Tendsto (fun j => ps k (x j)) (hyperfilter ℕ : Filter ℕ) (𝓝 0) := by
  have hg : Tendsto (fun j => M j ^ (k - 2) * ps 2 (x j)) (hyperfilter ℕ : Filter ℕ) (𝓝 0) := by
    have := (hM0.pow (k - 2)).mul h2
    rwa [zero_pow (by omega), zero_mul] at this
  refine QE.NSA.tendsto_of_abs_sub_le hg (Eventually.of_forall fun j => ?_)
  rw [sub_zero]; exact abs_ps_le (x j) (hM j) (by omega)

theorem isInfinitesimal_ps (x : ∀ j, Fin (N j) → ℝ) (M : ℕ → ℝ) (hM : ∀ j i, |x j i| ≤ M j)
    (hM0 : IsInfinitesimal (Hyperreal.ofSeq M))
    (h2 : IsFinite (Hyperreal.ofSeq fun j => ps 2 (x j))) (k : ℕ) (hk : 3 ≤ k) :
    IsInfinitesimal (Hyperreal.ofSeq fun j => ps k (x j)) := by
  rw [isInfinitesimal_ofSeq_iff_tendsto]
  have h2' := (ofSeq_st_iff_tendsto _ _).1 ⟨h2, rfl⟩
  exact tendsto_ps_zero x M hM ((isInfinitesimal_ofSeq_iff_tendsto _).1 hM0) h2' k hk

theorem abs_log_one_add_sub_le {r : ℝ} (hr : |r| ≤ 1 / 2) :
    |Real.log (1 + r) - (r - r ^ 2 / 2)| ≤ 2 * |r| ^ 3 := by
  have hlt : |(-r)| < 1 := by rw [abs_neg]; linarith
  have h := Real.abs_log_sub_add_sum_range_le hlt 2
  have key : |Real.log (1 + r) - (r - r ^ 2 / 2)| ≤ |r| ^ 3 / (1 - |r|) := by
    convert h using 2
    · simp [sum_range_succ]; ring_nf
    · simp
    · simp
  refine key.trans ?_
  have h0 : 0 ≤ |r| := abs_nonneg r
  rw [div_le_iff₀ (by linarith)]
  nlinarith [pow_nonneg h0 3]

/-- **Shadow of the discrete exponential**: `st ∏ (1 + x_i) = exp (a - s/2)`. -/
theorem tendsto_prod_one_add (x : ∀ j, Fin (N j) → ℝ) (M : ℕ → ℝ) (hM : ∀ j i, |x j i| ≤ M j)
    (hM0 : Tendsto M (hyperfilter ℕ : Filter ℕ) (𝓝 0)) {a s : ℝ}
    (h1 : Tendsto (fun j => ps 1 (x j)) (hyperfilter ℕ : Filter ℕ) (𝓝 a))
    (h2 : Tendsto (fun j => ps 2 (x j)) (hyperfilter ℕ : Filter ℕ) (𝓝 s)) :
    Tendsto (fun j => ∏ i, (1 + x j i)) (hyperfilter ℕ : Filter ℕ) (𝓝 (Real.exp (a - s / 2))) := by
  have hsmall : ∀ᶠ j in (hyperfilter ℕ : Filter ℕ), M j ≤ 1 / 2 := by
    have := (Metric.tendsto_nhds.1 hM0) (1 / 2) (by norm_num)
    filter_upwards [this] with j hj
    rw [Real.dist_eq, sub_zero] at hj
    exact (le_abs_self _).trans hj.le
  set L : ℕ → ℝ := fun j => ∑ i, Real.log (1 + x j i) with hL
  have hlin : Tendsto (fun j => ps 1 (x j) - ps 2 (x j) / 2) (hyperfilter ℕ : Filter ℕ)
      (𝓝 (a - s / 2)) := h1.sub (h2.div_const 2)
  have hg : Tendsto (fun j => 2 * M j * ps 2 (x j)) (hyperfilter ℕ : Filter ℕ) (𝓝 0) := by
    have := (hM0.const_mul 2).mul h2
    simpa using this
  have hLt : Tendsto L (hyperfilter ℕ : Filter ℕ) (𝓝 (a - s / 2)) := by
    have hd : Tendsto (fun j => L j - (ps 1 (x j) - ps 2 (x j) / 2))
        (hyperfilter ℕ : Filter ℕ) (𝓝 0) := by
      refine QE.NSA.tendsto_of_abs_sub_le hg ?_
      filter_upwards [hsmall] with j hj
      rw [sub_zero]
      have e : L j - (ps 1 (x j) - ps 2 (x j) / 2) =
          ∑ i, (Real.log (1 + x j i) - (x j i - x j i ^ 2 / 2)) := by
        simp only [hL, ps, sum_sub_distrib, sum_div]; ring_nf
      rw [e, ps, mul_sum]
      refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun i _ => ?_)
      have hxi := hM j i
      refine (abs_log_one_add_sub_le (hxi.trans hj)).trans ?_
      have h0 : 0 ≤ |x j i| := abs_nonneg _
      rw [show |x j i| ^ 3 = |x j i| * x j i ^ 2 by rw [pow_succ', sq_abs]]
      nlinarith [sq_nonneg (x j i)]
    have := hd.add hlin
    simpa using this
  have hexp := (Real.continuous_exp.tendsto _).comp hLt
  refine hexp.congr' ?_
  filter_upwards [hsmall] with j hj
  simp only [Function.comp, hL]
  rw [Real.exp_sum]
  apply prod_congr rfl; intro i _
  have : |x j i| ≤ 1 / 2 := (hM j i).trans hj
  have hpos : 0 < 1 + x j i := by
    have := neg_abs_le (x j i); linarith
  exact Real.exp_log hpos

theorem st_prod_one_add (x : ∀ j, Fin (N j) → ℝ) (M : ℕ → ℝ) (hM : ∀ j i, |x j i| ≤ M j)
    (hM0 : IsInfinitesimal (Hyperreal.ofSeq M)) {a s : ℝ}
    (h1 : IsFinite (Hyperreal.ofSeq fun j => ps 1 (x j)) ∧
      stdPart (Hyperreal.ofSeq fun j => ps 1 (x j)) = a)
    (h2 : IsFinite (Hyperreal.ofSeq fun j => ps 2 (x j)) ∧
      stdPart (Hyperreal.ofSeq fun j => ps 2 (x j)) = s) :
    IsFinite (Hyperreal.ofSeq fun j => ∏ i, (1 + x j i)) ∧
      stdPart (Hyperreal.ofSeq fun j => ∏ i, (1 + x j i)) = Real.exp (a - s / 2) := by
  rw [ofSeq_st_iff_tendsto] at h1 h2 ⊢
  exact tendsto_prod_one_add x M hM ((isInfinitesimal_ofSeq_iff_tendsto _).1 hM0) h1 h2

end Shadow

/-! ## Coin moments of the discrete exponential -/

section Coins

open QE.OpenSto.Walsh

variable {N : ℕ}

/-- The increments `x_i(ω) = h_i c ξ_i`. -/
def incr (h : Fin N → ℝ) (c : ℝ) (ω : Fin N → Bool) : Fin N → ℝ := fun i => h i * c * sgn (ω i)

theorem avg_bool_one_add_pow4 (u : ℝ) :
    avg (fun b : Bool => (1 + u * sgn b) ^ 4) = 1 + 6 * u ^ 2 + u ^ 4 := by
  simp [avg, Fintype.card_bool]; ring

theorem avg_bool_one_add_sq (u : ℝ) :
    avg (fun b : Bool => (1 + u * sgn b) ^ 2) = 1 + u ^ 2 := by
  simp [avg, Fintype.card_bool]; ring

theorem E_prod_one_add_pow4 (h : Fin N → ℝ) (c : ℝ) :
    E (fun ω => (∏ i, (1 + incr h c ω i)) ^ 4) =
      ∏ i, (1 + 6 * h i ^ 2 * c ^ 2 + h i ^ 4 * c ^ 4) := by
  rw [← avg_eq_E]
  have : (fun ω : Fin N → Bool => (∏ i, (1 + incr h c ω i)) ^ 4) =
      fun ω => ∏ i, (fun i (b : Bool) => (1 + (h i * c) * sgn b) ^ 4) i (ω i) := by
    funext ω; rw [← prod_pow]; rfl
  rw [this, avg_prod (fun i (b : Bool) => (1 + (h i * c) * sgn b) ^ 4)]
  apply prod_congr rfl; intro i _
  rw [avg_bool_one_add_pow4]; ring

theorem E_prod_one_add_sq (h : Fin N → ℝ) (c : ℝ) :
    E (fun ω => (∏ i, (1 + incr h c ω i)) ^ 2) = ∏ i, (1 + h i ^ 2 * c ^ 2) := by
  rw [← avg_eq_E]
  have : (fun ω : Fin N → Bool => (∏ i, (1 + incr h c ω i)) ^ 2) =
      fun ω => ∏ i, (fun i (b : Bool) => (1 + (h i * c) * sgn b) ^ 2) i (ω i) := by
    funext ω; rw [← prod_pow]; rfl
  rw [this, avg_prod (fun i (b : Bool) => (1 + (h i * c) * sgn b) ^ 2)]
  apply prod_congr rfl; intro i _
  rw [avg_bool_one_add_sq]; ring

theorem E_prod_one_add_pow4_le (h : Fin N → ℝ) (c : ℝ) :
    E (fun ω => (∏ i, (1 + incr h c ω i)) ^ 4) ≤
      Real.exp (∑ i, (6 * h i ^ 2 * c ^ 2 + h i ^ 4 * c ^ 4)) := by
  rw [E_prod_one_add_pow4, Real.exp_sum]
  refine Finset.prod_le_prod₀ (fun i _ => by positivity) (fun i _ => ?_)
  have := Real.add_one_le_exp (6 * h i ^ 2 * c ^ 2 + h i ^ 4 * c ^ 4)
  linarith

theorem es_incr_eq_J (m : ℕ) (h : Fin N → ℝ) (c : ℝ) (ω : Fin N → Bool) :
    es m (incr h c ω) = J m c (fun S => ∏ i ∈ S, h i) ω := by
  unfold es J incr
  apply sum_congr rfl; intro S _
  rw [← prod_mul_distrib]; apply prod_congr rfl; intro i _; ring

/-- **Isometry of the elementary symmetric sums.** -/
theorem E_es_mul_es (m k : ℕ) (h h' : Fin N → ℝ) (c : ℝ) :
    E (fun ω => es m (incr h c ω) * es k (incr h' c ω)) =
      if m = k then es m (fun i => h i * h' i * c ^ 2) else 0 := by
  simp_rw [es_incr_eq_J]
  rw [J_isometry]
  split_ifs with hmk
  · subst hmk
    unfold es
    rw [mul_sum]; apply sum_congr rfl; intro S hS
    rw [(mem_powersetCard.mp hS).2.symm, prod_mul_distrib, prod_mul_distrib, prod_const,
      ← pow_mul, mul_comm (2:ℕ)]
    ring
  · rfl

theorem E_prod_one_add_mul_es (m : ℕ) (h h' : Fin N → ℝ) (c : ℝ) :
    E (fun ω => (∏ i, (1 + incr h c ω i)) * es m (incr h' c ω)) =
      es m (fun i => h i * h' i * c ^ 2) := by
  simp_rw [prod_one_add_eq_sum_es, sum_mul]
  rw [E_sum]
  simp_rw [E_es_mul_es]
  rw [sum_ite_eq']
  split_ifs with hm
  · rfl
  · rw [es_eq_zero_of_lt]; simp only [mem_range, not_lt] at hm; omega

theorem E_es_sq (m : ℕ) (h : Fin N → ℝ) (c : ℝ) :
    E (fun ω => es m (incr h c ω) ^ 2) = es m (fun i => h i ^ 2 * c ^ 2) := by
  have := E_es_mul_es m m h h c
  simp only [ite_true] at this
  simp_rw [sq]; rw [this]
  congr 1; funext i; ring

/-- **The Walsh chaos of the discrete exponential.** -/
theorem walsh_part_prod_one_add (m : ℕ) (h : Fin N → ℝ) (c : ℝ) (ω : Fin N → Bool) :
    ∑ S ∈ powersetCard m univ, coeff (fun η => ∏ i, (1 + incr h c η i)) S * chi S ω =
      es m (incr h c ω) := by
  have hF : (fun η => ∏ i, (1 + incr h c η i)) =
      fun η => ∑ S, (∏ i ∈ S, (h i * c)) * chi S η := by
    funext η
    rw [prod_one_add, powerset_univ]
    apply sum_congr rfl; intro S _
    unfold incr chi; rw [← prod_mul_distrib]
  rw [hF]
  unfold es incr
  apply sum_congr rfl; intro S _
  rw [coeff_of_expansion]
  unfold chi; rw [← prod_mul_distrib]

/-- Double counting: `p₁ e_m ≥ (m+1) e_{m+1}` for nonnegative entries. -/
theorem succ_mul_es_le {n : ℕ} (y : Fin n → ℝ) (hy : ∀ i, 0 ≤ y i) (m : ℕ) :
    ((m : ℝ) + 1) * es (m + 1) y ≤ ps 1 y * es m y := by
  classical
  have hL : ps 1 y * es m y = ∑ p ∈ univ ×ˢ powersetCard m (univ : Finset (Fin n)),
      y p.1 * ∏ i ∈ p.2, y i := by
    rw [ps, es, sum_mul_sum, sum_product]; simp
  have hR : ((m : ℝ) + 1) * es (m + 1) y =
      ∑ q ∈ (powersetCard (m + 1) (univ : Finset (Fin n)) ×ˢ univ).filter (fun q => q.2 ∈ q.1),
        ∏ i ∈ q.1, y i := by
    rw [sum_filter, sum_product, es, mul_sum]
    apply sum_congr rfl; intro T hT
    rw [← sum_filter]
    dsimp only
    rw [sum_const, nsmul_eq_mul, filter_mem_eq_inter, univ_inter,
      (mem_powersetCard.mp hT).2]
    push_cast; ring
  have hmid : ∑ q ∈ (powersetCard (m + 1) (univ : Finset (Fin n)) ×ˢ univ).filter
      (fun q => q.2 ∈ q.1), ∏ i ∈ q.1, y i =
      ∑ p ∈ (univ ×ˢ powersetCard m (univ : Finset (Fin n))).filter (fun p => p.1 ∉ p.2),
        y p.1 * ∏ i ∈ p.2, y i := by
    symm
    apply sum_nbij' (fun p => (insert p.1 p.2, p.1)) (fun q => (q.2, q.1.erase q.2))
    · intro p hp
      simp only [mem_filter, mem_product, mem_univ, mem_powersetCard, subset_univ, true_and,
        and_true] at hp ⊢
      exact ⟨by rw [card_insert_of_notMem hp.2, hp.1], mem_insert_self _ _⟩
    · intro q hq
      simp only [mem_filter, mem_product, mem_univ, mem_powersetCard, subset_univ, true_and,
        and_true] at hq ⊢
      exact ⟨by rw [card_erase_of_mem hq.2, hq.1]; rfl, notMem_erase _ _⟩
    · intro p hp
      simp only [mem_filter] at hp
      simp [erase_insert hp.2]
    · intro q hq
      simp only [mem_filter] at hq
      simp [insert_erase hq.2]
    · intro p hp
      simp only [mem_filter] at hp
      rw [prod_insert hp.2]
  rw [hR, hmid, hL]
  exact sum_le_sum_of_subset_of_nonneg (filter_subset _ _)
    (fun p _ _ => mul_nonneg (hy _) (prod_nonneg fun i _ => hy i))

/-- **Maclaurin-type bound** `e_m(y) ≤ p₁(y)^m / m!` for `y ≥ 0`. -/
theorem es_le_ps_pow {n : ℕ} (y : Fin n → ℝ) (hy : ∀ i, 0 ≤ y i) (m : ℕ) :
    es m y ≤ ps 1 y ^ m / m.factorial := by
  have hp : 0 ≤ ps 1 y := sum_nonneg fun i _ => by simpa using hy i
  induction m with
  | zero => simp [es_zero]
  | succ m ih =>
    have h1 := succ_mul_es_le y hy m
    have hpos : (0 : ℝ) < m + 1 := by positivity
    rw [Nat.factorial_succ, Nat.cast_mul, pow_succ]
    have : es (m + 1) y ≤ ps 1 y * es m y / (m + 1) := by
      rw [le_div_iff₀ hpos]; linarith
    refine this.trans ?_
    rw [div_le_div_iff₀ hpos (by positivity)]
    have := mul_le_mul_of_nonneg_left ih hp
    rw [mul_div_assoc', le_div_iff₀ (by positivity)] at this
    push_cast
    nlinarith

end Coins

end QE.Chaos.DExp

/-! # Part F. Step functions, Wiener chaos, chaos decomposition -/
namespace QE.Chaos.Wiener

open MeasureTheory Finset

/-- Step functions on `[0,T]`: values `c i` on `[s i, s (i+1))`. -/
structure StepFn (T : ℝ) where
  r : ℕ
  s : Fin (r + 1) → ℝ
  c : Fin r → ℝ
  mono : Monotone s
  nonneg : 0 ≤ s 0
  le_T : s (Fin.last r) ≤ T

namespace StepFn

variable {T : ℝ}

/-- `‖h‖² = ∑ c_i² (s_{i+1} - s_i)`. -/
def nrm2 (h : StepFn T) : ℝ := ∑ i, h.c i ^ 2 * (h.s i.succ - h.s i.castSucc)

/-- The value of the step function at time `u`. -/
def val (h : StepFn T) (u : ℝ) : ℝ :=
  ∑ i, if h.s i.castSucc ≤ u ∧ u < h.s i.succ then h.c i else 0

/-- Scaling the values. -/
def smul (a : ℝ) (h : StepFn T) : StepFn T :=
  { h with c := fun i => a * h.c i }

theorem nrm2_smul (a : ℝ) (h : StepFn T) : (h.smul a).nrm2 = a ^ 2 * h.nrm2 := by
  unfold nrm2 smul; rw [mul_sum]; apply sum_congr rfl; intro i _; ring

theorem nrm2_nonneg (h : StepFn T) : 0 ≤ h.nrm2 := by
  unfold nrm2
  refine sum_nonneg fun i _ => mul_nonneg (sq_nonneg _) (sub_nonneg.2 (h.mono ?_))
  exact Fin.castSucc_le_succ i

/-- The Wiener integral `I₁(h) = ∑ c_i (b(s_{i+1}) - b(s_i))` of a step function along a
process `b`. -/
def I1 {Ω : Type*} (b : ℝ → Ω → ℝ) (h : StepFn T) (ω : Ω) : ℝ :=
  ∑ i, h.c i * (b (h.s i.succ) ω - b (h.s i.castSucc) ω)

theorem I1_smul {Ω : Type*} (b : ℝ → Ω → ℝ) (a : ℝ) (h : StepFn T) (ω : Ω) :
    (h.smul a).I1 b ω = a * h.I1 b ω := by
  unfold I1 smul; rw [mul_sum]; apply sum_congr rfl; intro i _; ring

/-- If `‖h‖ = 0` then `I₁(h) = 0` identically. -/
theorem I1_eq_zero_of_nrm2 {Ω : Type*} (b : ℝ → Ω → ℝ) (h : StepFn T) (h0 : h.nrm2 = 0)
    (ω : Ω) : h.I1 b ω = 0 := by
  unfold nrm2 at h0
  have hterm := (sum_eq_zero_iff_of_nonneg (fun i _ => mul_nonneg (sq_nonneg (h.c i))
    (sub_nonneg.2 (h.mono (Fin.castSucc_le_succ i))))).1 h0
  unfold I1
  refine sum_eq_zero fun i hi => ?_
  rcases mul_eq_zero.1 (hterm i hi) with hc | hs
  · rw [pow_eq_zero_iff two_ne_zero] at hc; rw [hc, zero_mul]
  · rw [sub_eq_zero.1 hs, sub_self, mul_zero]

end StepFn

/-- The stochastic exponential `𝓔(h) = exp (I₁(h) - ‖h‖²/2)`. -/
def Expo {Ω : Type*} {T : ℝ} (b : ℝ → Ω → ℝ) (h : StepFn T) (ω : Ω) : ℝ :=
  Real.exp (h.I1 b ω - h.nrm2 / 2)

/-- The probabilists' Hermite polynomial `He_m` evaluated at a real number. -/
def He (m : ℕ) (a : ℝ) : ℝ := Polynomial.aeval a (Polynomial.hermite m)

namespace StepFn

variable {T : ℝ}

theorem ind_Ico_eq {x a b : ℝ} (hab : a ≤ b) :
    (if a ≤ x ∧ x < b then (1 : ℝ) else 0) = (if x < b then 1 else 0) - (if x < a then 1 else 0) := by
  by_cases h1 : x < a
  · have : x < b := lt_of_lt_of_le h1 hab
    simp [h1, this, not_le.2 h1]
  · by_cases h2 : x < b <;> simp [h1, h2, not_lt.1 h1]

/-- A sum against a step function is a combination of partial sums over `{x_j < s_i}`. -/
theorem sum_val_mul {ι : Type*} (I : Finset ι) (h : StepFn T) (x : ι → ℝ) (a : ι → ℝ) :
    ∑ j ∈ I, h.val (x j) * a j =
      ∑ i, h.c i * ((∑ j ∈ I, if x j < h.s i.succ then a j else 0) -
        ∑ j ∈ I, if x j < h.s i.castSucc then a j else 0) := by
  unfold val
  simp_rw [sum_mul]
  rw [sum_comm]
  apply sum_congr rfl; intro i _
  rw [← sum_sub_distrib, mul_sum]
  apply sum_congr rfl; intro j _
  have := ind_Ico_eq (x := x j) (h.mono (Fin.castSucc_le_succ i))
  have e : (if h.s i.castSucc ≤ x j ∧ x j < h.s i.succ then h.c i else 0) =
      h.c i * (if h.s i.castSucc ≤ x j ∧ x j < h.s i.succ then (1 : ℝ) else 0) := by
    split_ifs <;> simp
  rw [e, this]
  split_ifs <;> ring

/-- The square of a step function is the step function of the squares (the intervals
are disjoint). -/
theorem val_sq (h : StepFn T) (u : ℝ) :
    h.val u ^ 2 = ∑ i : Fin h.r, if h.s i.castSucc ≤ u ∧ u < h.s i.succ then h.c i ^ 2 else 0 := by
  unfold val
  -- at most one interval contains `u`
  by_cases hex : ∃ i : Fin h.r, h.s i.castSucc ≤ u ∧ u < h.s i.succ
  · obtain ⟨i, hi⟩ := hex
    have huniq : ∀ i' : Fin h.r, h.s i'.castSucc ≤ u ∧ u < h.s i'.succ → i' = i := by
      intro i' hi'
      by_contra hne
      rcases lt_or_gt_of_ne hne with hlt | hlt
      · have : h.s i'.succ ≤ h.s i.castSucc := h.mono (Fin.succ_le_castSucc_iff.2 hlt)
        linarith [hi.1, hi'.2]
      · have : h.s i.succ ≤ h.s i'.castSucc := h.mono (Fin.succ_le_castSucc_iff.2 hlt)
        linarith [hi'.1, hi.2]
    rw [sum_eq_single i (fun i' _ hne => by rw [if_neg (fun h' => hne (huniq i' h'))]) (by simp),
      sum_eq_single i (fun i' _ hne => by rw [if_neg (fun h' => hne (huniq i' h'))]) (by simp),
      if_pos hi, if_pos hi]
  · push Not at hex
    rw [sum_eq_zero (fun i _ => if_neg (fun h' => absurd h'.2 (not_lt.2 (hex i h'.1)))),
      sum_eq_zero (fun i _ => if_neg (fun h' => absurd h'.2 (not_lt.2 (hex i h'.1))))]
    simp

theorem abs_val_le (h : StepFn T) (u : ℝ) : |h.val u| ≤ ∑ i, |h.c i| := by
  unfold val
  refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun i _ => ?_)
  split_ifs <;> simp

end StepFn

section L2

variable {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)

open Classical in
/-- A function as an element of `L²(P)` (zero if it is not square integrable). -/
def toL2 (f : Ω → ℝ) : Lp ℝ 2 P := if hf : MemLp f 2 P then hf.toLp f else 0

theorem toL2_of_memLp {f : Ω → ℝ} (hf : MemLp f 2 P) : toL2 P f = hf.toLp f := by
  simp [toL2, hf]

theorem coeFn_toL2 {f : Ω → ℝ} (hf : MemLp f 2 P) : (toL2 P f : Ω → ℝ) =ᵐ[P] f := by
  rw [toL2_of_memLp P hf]; exact hf.coeFn_toLp

variable {T : ℝ} (b : ℝ → Ω → ℝ)

/-- Generators of the `m`-th Wiener chaos: `He_m(I₁(h))` with `‖h‖ = 1`. -/
def chaosGen (m : ℕ) : Set (Lp ℝ 2 P) :=
  {F | ∃ h : StepFn T, h.nrm2 = 1 ∧ F = toL2 P (fun ω => He m (h.I1 b ω))}

/-- **The `m`-th Wiener chaos** of the process `b`: the closed linear span in `L²(P)` of
`He_m(I₁(h))`, `h` a step function on `[0,T]` with `‖h‖ = 1`. -/
def chaos (m : ℕ) : Submodule ℝ (Lp ℝ 2 P) :=
  (Submodule.span ℝ (chaosGen P (T := T) b m)).topologicalClosure

instance (m : ℕ) : (chaos P (T := T) b m).HasOrthogonalProjection := by
  unfold chaos; infer_instance

/-- The orthogonal projection `Π_m` onto the `m`-th chaos. -/
def Pi (m : ℕ) : Lp ℝ 2 P →L[ℝ] Lp ℝ 2 P := (chaos P (T := T) b m).starProjection

end L2


section Hilbert

variable {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] {T : ℝ}
  (b : ℝ → Ω → ℝ)

theorem inner_toL2 {f g : Ω → ℝ} (hf : MemLp f 2 P) (hg : MemLp g 2 P) :
    inner ℝ (toL2 P f) (toL2 P g) = ∫ ω, f ω * g ω ∂P := by
  rw [L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [coeFn_toL2 P hf, coeFn_toL2 P hg] with ω h1 h2
  rw [h1, h2, real_inner_eq_re_inner, RCLike.inner_apply]
  simp [mul_comm]

/-- Orthogonality to the generators of a closed span extends to the closed span. -/
theorem inner_eq_zero_of_mem_closure_span {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {G : Set E} {u : E} (hu : ∀ g ∈ G, inner ℝ u g = 0) :
    ∀ w ∈ (Submodule.span ℝ G).topologicalClosure, inner ℝ u w = 0 := by
  let K : Submodule ℝ E := LinearMap.ker (innerSL ℝ u : E →L[ℝ] ℝ).toLinearMap
  have hK : IsClosed (K : Set E) := (innerSL ℝ u).isClosed_ker
  have hspan : Submodule.span ℝ G ≤ K := by
    rw [Submodule.span_le]; intro g hg; simp [K, hu g hg]
  have := Submodule.topologicalClosure_minimal _ hspan hK
  intro w hw; simpa [K] using this hw

/-- **Gaussian facts** used to compute chaos projections: the classical identities
`E[He_m(I₁h) He_k(I₁h')] = δ_{mk} m! ⟨h,h'⟩^m` and `E[𝓔(h) He_m(I₁h')] = ⟨h,h'⟩^m`
(for `‖h‖ = ‖h'‖ = 1`), with `⟨h,h'⟩ = E[I₁(h) I₁(h')]`. -/
structure GaussFacts : Prop where
  memLp_He : ∀ (m : ℕ) (h : StepFn T), h.nrm2 = 1 → MemLp (fun ω => He m (h.I1 b ω)) 2 P
  memLp_expo : ∀ h : StepFn T, MemLp (Expo b h) 2 P
  inner_He : ∀ (m k : ℕ) (h h' : StepFn T), h.nrm2 = 1 → h'.nrm2 = 1 →
    ∫ ω, He m (h.I1 b ω) * He k (h'.I1 b ω) ∂P =
      if m = k then (m.factorial : ℝ) * (∫ ω, h.I1 b ω * h'.I1 b ω ∂P) ^ m else 0
  inner_expo_He : ∀ (m : ℕ) (h h' : StepFn T), h'.nrm2 = 1 →
    ∫ ω, Expo b h ω * He m (h'.I1 b ω) ∂P = (∫ ω, h.I1 b ω * h'.I1 b ω ∂P) ^ m
  exists_unit : ∃ h : StepFn T, h.nrm2 = 1
  sq_I1 : ∀ h : StepFn T, h.nrm2 = 1 → ∫ ω, h.I1 b ω ^ 2 ∂P = 1
  sq_expo : ∀ h : StepFn T, ∫ ω, Expo b h ω ^ 2 ∂P = Real.exp h.nrm2

/-- The chaos component of an exponential: `(√‖h‖²)^m/m! · He_m(I₁(h)/‖h‖)`
(and `δ_{m0}` when `‖h‖ = 0`). -/
def Qm (m : ℕ) (h : StepFn T) (ω : Ω) : ℝ :=
  if h.nrm2 = 0 then (if m = 0 then 1 else 0)
  else √h.nrm2 ^ m / m.factorial * He m (h.I1 b ω / √h.nrm2)

variable {P b}

theorem He_zero (a : ℝ) : He 0 a = 1 := by simp [He]

theorem gen_mem_chaos {m : ℕ} {h : StepFn T} (hh : h.nrm2 = 1) :
    toL2 P (fun ω => He m (h.I1 b ω)) ∈ chaos P (T := T) b m :=
  Submodule.le_topologicalClosure _ (Submodule.subset_span ⟨h, hh, rfl⟩)

/-- Different chaoses are orthogonal. -/
theorem chaos_orthogonal (hG : GaussFacts P (T := T) b) {m k : ℕ} (hmk : m ≠ k) :
    ∀ u ∈ chaos P (T := T) b m, ∀ w ∈ chaos P (T := T) b k, inner ℝ u w = 0 := by
  have hgen : ∀ g ∈ chaosGen P (T := T) b m, ∀ g' ∈ chaosGen P (T := T) b k,
      inner ℝ g g' = 0 := by
    rintro _ ⟨h, hh, rfl⟩ _ ⟨h', hh', rfl⟩
    rw [inner_toL2 P (hG.memLp_He m h hh) (hG.memLp_He k h' hh'), hG.inner_He m k h h' hh hh',
      if_neg hmk]
  have step1 : ∀ g ∈ chaosGen P (T := T) b m, ∀ w ∈ chaos P (T := T) b k, inner ℝ g w = 0 :=
    fun g hg => inner_eq_zero_of_mem_closure_span (hgen g hg)
  intro u hu w hw
  rw [real_inner_comm]
  refine inner_eq_zero_of_mem_closure_span (G := chaosGen P (T := T) b m) (u := w) ?_ u hu
  intro g hg; rw [real_inner_comm]; exact step1 g hg w hw

theorem memLp_Qm (hG : GaussFacts P (T := T) b) (m : ℕ) (h : StepFn T) :
    MemLp (Qm b m h) 2 P := by
  unfold Qm
  by_cases h0 : h.nrm2 = 0
  · simp only [h0, if_true]; exact memLp_const _
  · simp only [h0, if_false]
    have hs : 0 < √h.nrm2 := Real.sqrt_pos.2 (lt_of_le_of_ne h.nrm2_nonneg (Ne.symm h0))
    have e : (fun ω => √h.nrm2 ^ m / m.factorial * He m (h.I1 b ω / √h.nrm2)) =
        fun ω => √h.nrm2 ^ m / m.factorial * He m ((h.smul (1 / √h.nrm2)).I1 b ω) := by
      funext ω; rw [StepFn.I1_smul]; congr 2; ring
    rw [e]
    have hh1 : (h.smul (1 / √h.nrm2)).nrm2 = 1 := by
      rw [StepFn.nrm2_smul, div_pow, Real.sq_sqrt h.nrm2_nonneg]; field_simp
    exact (hG.memLp_He m _ hh1).const_mul _

theorem heH_zero_right (m : ℕ) (a : ℝ) : QE.Chaos.DExp.heH m a 0 = a ^ m := by
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    match m with
    | 0 => simp [QE.Chaos.DExp.heH]
    | 1 => simp [QE.Chaos.DExp.heH]
    | k + 2 => rw [QE.Chaos.DExp.heH_succ_succ, ih (k + 1) (by omega)]; ring

/-- `Q_m(h)` is the homogenised Hermite polynomial `heH_m(I₁(h), ‖h‖²)/m!`. -/
theorem Qm_eq_heH (m : ℕ) (h : StepFn T) (ω : Ω) :
    Qm b m h ω = QE.Chaos.DExp.heH m (h.I1 b ω) h.nrm2 / m.factorial := by
  unfold Qm
  by_cases h0 : h.nrm2 = 0
  · rw [if_pos h0, h0, StepFn.I1_eq_zero_of_nrm2 b h h0, heH_zero_right]
    by_cases hm : m = 0
    · subst hm; simp
    · simp [hm, zero_pow hm]
  · rw [if_neg h0]
    have hs : 0 < √h.nrm2 := Real.sqrt_pos.2 (lt_of_le_of_ne h.nrm2_nonneg (Ne.symm h0))
    have e := QE.Chaos.DExp.heH_homog m (√h.nrm2) (h.I1 b ω / √h.nrm2) 1
    rw [mul_div_cancel₀ _ hs.ne', mul_one, Real.sq_sqrt h.nrm2_nonneg,
      QE.Chaos.DExp.heH_one_eq_hermite] at e
    rw [e, He]; ring

/-- **The chaos components of an exponential**: `Π_m 𝓔(h) = Q_m(h)`. -/
theorem Pi_expo (hG : GaussFacts P (T := T) b) (m : ℕ) (h : StepFn T) :
    Pi P (T := T) b m (toL2 P (Expo b h)) = toL2 P (Qm b m h) := by
  obtain ⟨h₁, hh₁⟩ := hG.exists_unit
  unfold Pi
  refine Submodule.eq_starProjection_of_mem_of_inner_eq_zero ?_ ?_
  · -- membership
    by_cases h0 : h.nrm2 = 0
    · by_cases hm : m = 0
      · subst hm
        have : toL2 P (Qm b 0 h) = toL2 P (fun ω => He 0 (h₁.I1 b ω)) := by
          congr 1; funext ω; simp [Qm, h0, He_zero]
        rw [this]; exact gen_mem_chaos hh₁
      · have : toL2 P (Qm b m h) = 0 := by
          have e : Qm b m h = fun _ => (0 : ℝ) := by funext ω; simp [Qm, h0, hm]
          rw [e, toL2_of_memLp P (memLp_const 0)]
          exact MemLp.toLp_zero _
        rw [this]; exact Submodule.zero_mem _
    · have hs : 0 < √h.nrm2 := Real.sqrt_pos.2 (lt_of_le_of_ne h.nrm2_nonneg (Ne.symm h0))
      set h' := h.smul (1 / √h.nrm2)
      have hh' : h'.nrm2 = 1 := by
        rw [StepFn.nrm2_smul, div_pow, Real.sq_sqrt h.nrm2_nonneg]; field_simp
      have e : Qm b m h = fun ω => (√h.nrm2 ^ m / m.factorial) * He m (h'.I1 b ω) := by
        funext ω; simp only [Qm, h0, if_false, h', StepFn.I1_smul]; congr 2; ring
      have hmem := hG.memLp_He m h' hh'
      have e2 : (fun ω => (√h.nrm2 ^ m / m.factorial) * He m (h'.I1 b ω)) =
          (√h.nrm2 ^ m / m.factorial) • (fun ω => He m (h'.I1 b ω)) := by
        funext ω; simp
      have hc := Submodule.smul_mem (chaos P (T := T) b m) (√h.nrm2 ^ m / m.factorial)
        (gen_mem_chaos (P := P) (b := b) (m := m) hh')
      rw [toL2_of_memLp P hmem] at hc
      rw [e, e2, toL2_of_memLp P (hmem.const_smul _)]
      exact hc
  · -- orthogonality to the chaos
    refine inner_eq_zero_of_mem_closure_span ?_
    rintro _ ⟨h'', hh'', rfl⟩
    rw [inner_sub_left, inner_toL2 P (hG.memLp_expo h) (hG.memLp_He m h'' hh''),
      inner_toL2 P (memLp_Qm hG m h) (hG.memLp_He m h'' hh''), hG.inner_expo_He m h h'' hh'',
      sub_eq_zero]
    by_cases h0 : h.nrm2 = 0
    · have hI : ∀ ω, h.I1 b ω = 0 := StepFn.I1_eq_zero_of_nrm2 b h h0
      by_cases hm : m = 0
      · subst hm; simp [Qm, h0, He_zero]
      · simp [Qm, h0, hm, hI, zero_pow hm]
    · have hs : 0 < √h.nrm2 := Real.sqrt_pos.2 (lt_of_le_of_ne h.nrm2_nonneg (Ne.symm h0))
      set h' := h.smul (1 / √h.nrm2)
      have hh' : h'.nrm2 = 1 := by
        rw [StepFn.nrm2_smul, div_pow, Real.sq_sqrt h.nrm2_nonneg]; field_simp
      have e : ∀ ω, Qm b m h ω * He m (h''.I1 b ω) =
          (√h.nrm2 ^ m / m.factorial) * (He m (h'.I1 b ω) * He m (h''.I1 b ω)) := by
        intro ω; simp only [Qm, h0, if_false, h', StepFn.I1_smul]; ring_nf
      simp_rw [e]
      rw [integral_const_mul, hG.inner_He m m h' h'' hh' hh'', if_pos rfl]
      have e3 : ∀ ω, h'.I1 b ω * h''.I1 b ω = (1 / √h.nrm2) * (h.I1 b ω * h''.I1 b ω) := by
        intro ω; simp only [h', StepFn.I1_smul]; ring
      simp_rw [e3]
      rw [integral_const_mul, mul_pow]
      have hf : (m.factorial : ℝ) ≠ 0 := by positivity
      field_simp
      rw [mul_assoc, ← mul_pow, one_div, mul_inv_cancel₀ hs.ne', one_pow, mul_one]

end Hilbert

section Density

open QE.Chaos.Dense

variable {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] {T : ℝ}
  (b : ℝ → Ω → ℝ)

/-- The closed span of the exponentials `𝓔(h)`, `h` a step function on `[0,T]`. -/
def expoSpan : Submodule ℝ (Lp ℝ 2 P) :=
  (Submodule.span ℝ (Set.range (fun h : StepFn T => toL2 P (Expo b h)))).topologicalClosure

instance : (expoSpan P (T := T) b).HasOrthogonalProjection := by
  unfold expoSpan; infer_instance

theorem StepFn.s_mem (h : StepFn T) (i : Fin (h.r + 1)) : h.s i ∈ Set.Icc (0 : ℝ) T :=
  ⟨h.nonneg.trans (h.mono (Fin.zero_le i)), (h.mono (Fin.le_last i)).trans h.le_T⟩

theorem measurable_b_pathSigma {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) T) :
    Measurable[pathSigma b T] (b t) := by
  have : b t = fun ω => path b T ω ⟨t, ht⟩ := rfl
  rw [this]
  exact (measurable_pi_apply _).comp (comap_measurable (path b T))

theorem measurable_I1_pathSigma (h : StepFn T) : Measurable[pathSigma b T] (h.I1 b) := by
  unfold StepFn.I1
  refine Finset.measurable_sum _ fun i _ => ?_
  exact ((measurable_b_pathSigma b (h.s_mem _)).sub
    (measurable_b_pathSigma b (h.s_mem _))).const_mul _

theorem measurable_Expo_pathSigma (h : StepFn T) : Measurable[pathSigma b T] (Expo b h) := by
  unfold Expo
  exact Real.measurable_exp.comp ((measurable_I1_pathSigma b h).sub measurable_const)

variable {P b}

/-- **Density of exponentials**: every square-integrable functional of the path lies in the
closed span of the exponentials `𝓔(h)`. -/
theorem mem_expoSpan (hT : 0 ≤ T) (hb : ∀ t, Measurable (b t)) (hb0 : ∀ ω, b 0 ω = 0)
    (hexpo : ∀ h : StepFn T, MemLp (Expo b h) 2 P) (v : Lp ℝ 2 P)
    (hv : v ∈ lpMeas ℝ ℝ (pathSigma b T) 2 P) : v ∈ expoSpan P (T := T) b := by
  set V := expoSpan P (T := T) b
  have hgen : ∀ h : StepFn T, toL2 P (Expo b h) ∈ lpMeas ℝ ℝ (pathSigma b T) 2 P := by
    intro h
    rw [mem_lpMeas_iff_aestronglyMeasurable]
    exact ((measurable_Expo_pathSigma b h).stronglyMeasurable.aestronglyMeasurable).congr
      (coeFn_toL2 P (hexpo h)).symm
  have hVle : V ≤ lpMeas ℝ ℝ (pathSigma b T) 2 P := by
    apply Submodule.topologicalClosure_minimal
    · rw [Submodule.span_le]; rintro _ ⟨h, rfl⟩; exact hgen h
    · exact isClosed_aestronglyMeasurable (pathSigma_le hb T)
  -- the exponentials of increments are multiples of the `𝓔(h)`
  have hstep : ∀ (r : ℕ) (s : Fin (r + 1) → ℝ), Monotone s → s 0 = 0 → (∀ i, s i ≤ T) →
      ∀ a : Fin r → ℝ, ∃ h : StepFn T, (fun ω => Real.exp (∑ i, a i * incr b s ω i)) =
        fun ω => Real.exp (h.nrm2 / 2) * Expo b h ω := by
    intro r s h1 h2 h3 a
    refine ⟨⟨r, s, a, h1, h2.ge, h3 _⟩, ?_⟩
    funext ω
    simp only [Expo, StepFn.I1, incr]
    rw [← Real.exp_add]; congr 1; ring
  have hexp : ∀ (r : ℕ) (s : Fin (r + 1) → ℝ), Monotone s → s 0 = 0 → (∀ i, s i ≤ T) →
      ∀ a : Fin r → ℝ, MemLp (fun ω => Real.exp (∑ i, a i * incr b s ω i)) 2 P := by
    intro r s h1 h2 h3 a
    obtain ⟨h, hh⟩ := hstep r s h1 h2 h3 a
    rw [hh]; exact (hexpo h).const_mul _
  set R := v - V.starProjection v
  have hR : R ∈ lpMeas ℝ ℝ (pathSigma b T) 2 P :=
    Submodule.sub_mem _ hv (hVle (V.starProjection_apply_mem v))
  have hRo : R ∈ Vᗮ := V.sub_starProjection_mem_orthogonal v
  have hR0 : R = 0 := by
    refine eq_zero_of_orthogonal_exp_Lp hT b hb hb0 hexp R hR ?_
    intro r s h1 h2 h3 a
    obtain ⟨h, hh⟩ := hstep r s h1 h2 h3 a
    have hmem : (hexp r s h1 h2 h3 a).toLp _ ∈ V := by
      have e : (hexp r s h1 h2 h3 a).toLp _ = Real.exp (h.nrm2 / 2) • toL2 P (Expo b h) := by
        rw [toL2_of_memLp P (hexpo h), ← MemLp.toLp_const_smul]
        exact (MemLp.toLp_eq_toLp_iff _ _).2 (Filter.EventuallyEq.of_eq (by rw [hh]; rfl))
      rw [e]
      exact Submodule.smul_mem _ _ (Submodule.le_topologicalClosure _
        (Submodule.subset_span ⟨h, rfl⟩))
    exact Submodule.inner_right_of_mem_orthogonal hmem hRo
  have : v = V.starProjection v := sub_eq_zero.1 hR0
  rw [this]; exact V.starProjection_apply_mem v

end Density

section Approx

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {T : ℝ}
  {b : ℝ → Ω → ℝ}

/-- The abstract lifting step: if `x` is approximated by the chaos components of the
approximants of `v` from the span of exponentials, at least as well as `v` itself, then
`x = Π_m v`. -/
theorem eq_Pi_of_approx (m : ℕ) {v x : Lp ℝ 2 P} (hv : v ∈ expoSpan P (T := T) b)
    (happrox : ∀ p ∈ Submodule.span ℝ (Set.range (fun h : StepFn T => toL2 P (Expo b h))),
      ‖x - Pi P (T := T) b m p‖ ≤ ‖v - p‖) :
    x = Pi P (T := T) b m v := by
  have hcl : v ∈ closure (Submodule.span ℝ
      (Set.range (fun h : StepFn T => toL2 P (Expo b h))) : Set (Lp ℝ 2 P)) := by
    have := hv; unfold expoSpan at this
    rwa [← SetLike.mem_coe, Submodule.topologicalClosure_coe] at this
  rw [← sub_eq_zero, ← norm_le_zero_iff]
  refine le_of_forall_pos_le_add fun ε hε => ?_
  obtain ⟨p, hp, hvp⟩ := Metric.mem_closure_iff.1 hcl (ε / 2) (by positivity)
  rw [dist_eq_norm] at hvp
  have h1 := happrox p hp
  have h2 : ‖Pi P (T := T) b m p - Pi P (T := T) b m v‖ ≤ ‖p - v‖ := by
    rw [← map_sub]; exact Submodule.norm_starProjection_apply_le _ _
  have h3 := norm_sub_le_norm_sub_add_norm_sub x (Pi P (T := T) b m p) (Pi P (T := T) b m v)
  rw [norm_sub_rev p v] at h2
  linarith

end Approx

section Completeness

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {T : ℝ}
  {b : ℝ → Ω → ℝ}

/-- The partial chaos sum `∑_{m < M} Π_m v`. -/
def chaosSum (M : ℕ) (v : Lp ℝ 2 P) : Lp ℝ 2 P := ∑ m ∈ Finset.range M, Pi P (T := T) b m v

theorem Pi_mem (m : ℕ) (v : Lp ℝ 2 P) : Pi P (T := T) b m v ∈ chaos P (T := T) b m :=
  Submodule.starProjection_apply_mem _ v

theorem inner_sub_Pi (m : ℕ) (v : Lp ℝ 2 P) {w : Lp ℝ 2 P} (hw : w ∈ chaos P (T := T) b m) :
    inner ℝ (v - Pi P (T := T) b m v) w = 0 :=
  Submodule.starProjection_inner_eq_zero v w hw

theorem inner_sub_chaosSum (hG : GaussFacts P (T := T) b) {M m : ℕ} (hm : m < M)
    (v : Lp ℝ 2 P) {w : Lp ℝ 2 P} (hw : w ∈ chaos P (T := T) b m) :
    inner ℝ (v - chaosSum (T := T) (b := b) M v) w = 0 := by
  unfold chaosSum
  rw [← Finset.add_sum_erase _ _ (Finset.mem_range.2 hm), ← sub_sub, inner_sub_left,
    inner_sub_Pi m v hw, zero_sub, sum_inner, Finset.sum_eq_zero, neg_zero]
  intro m' hm'
  exact chaos_orthogonal hG (Finset.ne_of_mem_erase hm') _ (Pi_mem m' v) _ hw

/-- **Best approximation**: the partial chaos sum is the closest point of `⊕_{m<M} 𝓗_m`. -/
theorem norm_sub_chaosSum_le (hG : GaussFacts P (T := T) b) (M : ℕ) (v : Lp ℝ 2 P)
    (u : ℕ → Lp ℝ 2 P) (hu : ∀ m, u m ∈ chaos P (T := T) b m) :
    ‖v - chaosSum (T := T) (b := b) M v‖ ≤ ‖v - ∑ m ∈ Finset.range M, u m‖ := by
  set d := v - chaosSum (T := T) (b := b) M v
  set e := chaosSum (T := T) (b := b) M v - ∑ m ∈ Finset.range M, u m
  have hde : inner ℝ d e = 0 := by
    have : e = ∑ m ∈ Finset.range M, (Pi P (T := T) b m v - u m) := by
      simp only [e, chaosSum, Finset.sum_sub_distrib]
    rw [this, inner_sum]
    refine Finset.sum_eq_zero fun m hm => ?_
    exact inner_sub_chaosSum hG (Finset.mem_range.1 hm) v
      (Submodule.sub_mem _ (Pi_mem m v) (hu m))
  have hsum : v - ∑ m ∈ Finset.range M, u m = d + e := by simp only [d, e]; abel
  rw [hsum]
  have := norm_add_sq_eq_norm_sq_add_norm_sq_real hde
  nlinarith [norm_nonneg d, norm_nonneg (d + e), sq_nonneg ‖e‖]

theorem norm_sub_chaosSum_le_norm (hG : GaussFacts P (T := T) b) (M : ℕ) (v : Lp ℝ 2 P) :
    ‖v - chaosSum (T := T) (b := b) M v‖ ≤ ‖v‖ := by
  simpa using norm_sub_chaosSum_le hG M v (fun _ => 0) (fun m => Submodule.zero_mem _)

theorem chaosSum_sub (M : ℕ) (v w : Lp ℝ 2 P) :
    chaosSum (T := T) (b := b) M (v - w) = chaosSum (T := T) (b := b) M v - chaosSum (T := T) (b := b) M w := by
  simp [chaosSum, Finset.sum_sub_distrib]

theorem chaosSum_add (M : ℕ) (v w : Lp ℝ 2 P) :
    chaosSum (T := T) (b := b) M (v + w) = chaosSum (T := T) (b := b) M v + chaosSum (T := T) (b := b) M w := by
  simp [chaosSum, Finset.sum_add_distrib]

theorem chaosSum_smul (M : ℕ) (c : ℝ) (v : Lp ℝ 2 P) :
    chaosSum (T := T) (b := b) M (c • v) = c • chaosSum (T := T) (b := b) M v := by
  simp [chaosSum, Finset.smul_sum]

theorem norm_Qm_sq (hG : GaussFacts P (T := T) b) (m : ℕ) (h : StepFn T) :
    ‖toL2 P (Qm b m h)‖ ^ 2 = h.nrm2 ^ m / m.factorial := by
  rw [← real_inner_self_eq_norm_sq, inner_toL2 P (memLp_Qm hG m h) (memLp_Qm hG m h)]
  by_cases h0 : h.nrm2 = 0
  · by_cases hm : m = 0
    · subst hm; simp [Qm, h0]
    · simp [Qm, h0, hm, zero_pow hm]
  · have hs : 0 < √h.nrm2 := Real.sqrt_pos.2 (lt_of_le_of_ne h.nrm2_nonneg (Ne.symm h0))
    set h' := h.smul (1 / √h.nrm2)
    have hh' : h'.nrm2 = 1 := by
      rw [StepFn.nrm2_smul, div_pow, Real.sq_sqrt h.nrm2_nonneg]; field_simp
    have e : ∀ ω, Qm b m h ω * Qm b m h ω =
        (√h.nrm2 ^ m / m.factorial) ^ 2 * (He m (h'.I1 b ω) * He m (h'.I1 b ω)) := by
      intro ω; simp only [Qm, h0, if_false, h', StepFn.I1_smul]; ring_nf
    simp_rw [e]
    rw [integral_const_mul, hG.inner_He m m h' h' hh' hh', if_pos rfl]
    simp_rw [← sq]
    rw [hG.sq_I1 h' hh', one_pow, mul_one, div_pow, ← pow_mul, mul_comm m 2, pow_mul,
      Real.sq_sqrt h.nrm2_nonneg]
    have hf : (m.factorial : ℝ) ≠ 0 := by positivity
    field_simp

/-- The chaos expansion of an exponential converges: `‖𝓔(h) - ∑_{m<M} Π_m 𝓔(h)‖ → 0`. -/
theorem tendsto_chaosSum_expo (hG : GaussFacts P (T := T) b) (h : StepFn T) :
    Filter.Tendsto (fun M => ‖toL2 P (Expo b h) - chaosSum (T := T) (b := b) M (toL2 P (Expo b h))‖)
      Filter.atTop (nhds 0) := by
  set v := toL2 P (Expo b h)
  have hv : ‖v‖ ^ 2 = Real.exp h.nrm2 := by
    rw [← real_inner_self_eq_norm_sq, inner_toL2 P (hG.memLp_expo h) (hG.memLp_expo h)]
    simp_rw [← sq]; exact hG.sq_expo h
  have hS : ∀ M, ‖chaosSum (T := T) (b := b) M v‖ ^ 2 =
      ∑ m ∈ Finset.range M, h.nrm2 ^ m / m.factorial := by
    intro M
    induction M with
    | zero => simp [chaosSum]
    | succ M ih =>
      have e : chaosSum (T := T) (b := b) (M + 1) v =
          chaosSum (T := T) (b := b) M v + Pi P (T := T) b M v := by
        simp [chaosSum, Finset.sum_range_succ]
      have ho : inner ℝ (chaosSum (T := T) (b := b) M v) (Pi P (T := T) b M v) = 0 := by
        unfold chaosSum; rw [sum_inner]
        exact Finset.sum_eq_zero fun m hm => chaos_orthogonal hG
          (Nat.ne_of_lt (Finset.mem_range.1 hm)) _ (Pi_mem m v) _ (Pi_mem M v)
      have := norm_add_sq_eq_norm_sq_add_norm_sq_real ho
      rw [e, sq, this, ← sq, ← sq, ih, Finset.sum_range_succ, Pi_expo hG M h, norm_Qm_sq hG M h]
  have hsq : ∀ M, ‖v - chaosSum (T := T) (b := b) M v‖ ^ 2 =
      Real.exp h.nrm2 - ∑ m ∈ Finset.range M, h.nrm2 ^ m / m.factorial := by
    intro M
    have horth : inner ℝ (v - chaosSum (T := T) (b := b) M v) (chaosSum (T := T) (b := b) M v) = 0 := by
      unfold chaosSum
      rw [inner_sum]
      exact Finset.sum_eq_zero fun m hm =>
        inner_sub_chaosSum hG (Finset.mem_range.1 hm) v (Pi_mem m v)
    have := norm_add_sq_eq_norm_sq_add_norm_sq_real horth
    rw [sub_add_cancel, ← sq, ← sq, ← sq, hv, hS] at this
    linarith
  have hlim : Filter.Tendsto (fun M => Real.exp h.nrm2 -
      ∑ m ∈ Finset.range M, h.nrm2 ^ m / m.factorial) Filter.atTop (nhds 0) := by
    have hs := (Real.summable_pow_div_factorial h.nrm2).hasSum.tendsto_sum_nat
    have he : Real.exp h.nrm2 = ∑' m : ℕ, h.nrm2 ^ m / m.factorial := by
      rw [Real.exp_eq_exp_ℝ, NormedSpace.exp_eq_tsum_div]
    rw [he]
    simpa using (tendsto_const_nhds (x := ∑' m : ℕ, h.nrm2 ^ m / (m.factorial : ℝ))).sub hs
  have hsqrt := hlim.sqrt
  rw [Real.sqrt_zero] at hsqrt
  refine hsqrt.congr fun M => ?_
  rw [← hsq M, Real.sqrt_sq (norm_nonneg _)]

/-- **Wiener–Itô chaos decomposition** on the closed span of the exponentials (hence, with
`mem_expoSpan`, on all of `L²` of the path σ-algebra): `∑_{m<M} Π_m v → v`. -/
theorem tendsto_chaosSum (hG : GaussFacts P (T := T) b) {v : Lp ℝ 2 P}
    (hv : v ∈ expoSpan P (T := T) b) :
    Filter.Tendsto (fun M => chaosSum (T := T) (b := b) M v) Filter.atTop (nhds v) := by
  let C : Submodule ℝ (Lp ℝ 2 P) :=
    { carrier := {v | Filter.Tendsto (fun M => ‖v - chaosSum (T := T) (b := b) M v‖) Filter.atTop (nhds 0)}
      zero_mem' := by simp [chaosSum]
      add_mem' := by
        intro v w hv hw
        simp only [Set.mem_ofPred_eq] at *
        refine squeeze_zero (fun _ => norm_nonneg _) (fun M => ?_) (by simpa using hv.add hw)
        rw [chaosSum_add]
        calc ‖v + w - (chaosSum M v + chaosSum M w)‖ =
            ‖(v - chaosSum (T := T) (b := b) M v) + (w - chaosSum (T := T) (b := b) M w)‖ := by
              congr 1; abel
          _ ≤ _ := norm_add_le _ _
      smul_mem' := by
        intro c v hv
        simp only [Set.mem_ofPred_eq] at *
        refine (by simpa using hv.const_mul ‖c‖ : Filter.Tendsto _ _ (nhds (‖c‖ * 0))).congr' ?_
          |>.trans (by simp)
        refine Filter.Eventually.of_forall fun M => ?_
        simp only
        rw [chaosSum_smul, ← smul_sub, norm_smul, Real.norm_eq_abs] }
  have hgen : Submodule.span ℝ (Set.range (fun h : StepFn T => toL2 P (Expo b h))) ≤ C := by
    rw [Submodule.span_le]; rintro _ ⟨h, rfl⟩; exact tendsto_chaosSum_expo hG h
  have hcl : v ∈ closure (C : Set (Lp ℝ 2 P)) := by
    have := hv; unfold expoSpan at this
    rw [← SetLike.mem_coe, Submodule.topologicalClosure_coe] at this
    exact closure_mono hgen this
  have hvC : v ∈ C := by
    show Filter.Tendsto _ _ _
    rw [Metric.tendsto_atTop]
    intro ε hε
    obtain ⟨w, hw, hvw⟩ := Metric.mem_closure_iff.1 hcl (ε / 2) (by positivity)
    rw [dist_eq_norm] at hvw
    obtain ⟨M₀, hM₀⟩ := Metric.tendsto_atTop.1 hw (ε / 2) (by positivity)
    refine ⟨M₀, fun M hM => ?_⟩
    have h1 := hM₀ M hM
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (norm_nonneg _)] at h1 ⊢
    have h2 := norm_sub_chaosSum_le_norm hG M (v - w)
    rw [chaosSum_sub] at h2
    calc ‖v - chaosSum (T := T) (b := b) M v‖ =
        ‖(v - w - (chaosSum (T := T) (b := b) M v - chaosSum (T := T) (b := b) M w)) +
          (w - chaosSum (T := T) (b := b) M w)‖ := by congr 1; abel
      _ ≤ _ := norm_add_le _ _
      _ < ε / 2 + ε / 2 := by linarith
      _ = ε := by ring
  have := hvC
  simp only [C, Submodule.mem_mk, AddSubmonoid.mem_mk, AddSubsemigroup.mem_mk,
    Set.mem_ofPred_eq] at this
  exact tendsto_iff_norm_sub_tendsto_zero.2 (by
    refine this.congr fun M => ?_; rw [norm_sub_rev])

end Completeness

end QE.Chaos.Wiener

/-! # Part G. The Wiener chaos of the Loeb Brownian motion -/

namespace QE.Chaos.Lift

open Finset QE.Chaos.Wiener

section StepSums

/-- `#{j < N : j τ < s} = ⌈s/τ⌉` for `0 ≤ s ≤ N τ`. -/
theorem card_filter_mul_lt {N : ℕ} {τ s : ℝ} (hτ : 0 < τ) (hs0 : 0 ≤ s) (hsN : s ≤ N * τ) :
    (univ.filter (fun j : Fin N => (j : ℝ) * τ < s)).card = ⌈s / τ⌉₊ := by
  have hc : ⌈s / τ⌉₊ ≤ N := by
    apply Nat.ceil_le.2; rw [div_le_iff₀ hτ]; exact hsN
  have : univ.filter (fun j : Fin N => (j : ℝ) * τ < s) =
      (univ.filter (fun j : Fin N => (j : ℕ) < ⌈s / τ⌉₊)) := by
    ext j; simp only [mem_filter, mem_univ, true_and]
    rw [Nat.lt_ceil, lt_div_iff₀ hτ]
  rw [this]
  have e : (univ.filter (fun j : Fin N => (j : ℕ) < ⌈s / τ⌉₊)) =
      (range ⌈s / τ⌉₊).attachFin (fun j hj => lt_of_lt_of_le (mem_range.1 hj) hc) := by
    ext j; simp
  rw [e, card_attachFin, card_range]

theorem abs_mul_card_sub_le {N : ℕ} {τ s : ℝ} (hτ : 0 < τ) (hs0 : 0 ≤ s) (hsN : s ≤ N * τ) :
    |τ * (univ.filter (fun j : Fin N => (j : ℝ) * τ < s)).card - s| ≤ τ := by
  rw [card_filter_mul_lt hτ hs0 hsN]
  have h1 := Nat.le_ceil (s / τ)
  have h2 := Nat.ceil_lt_add_one (div_nonneg hs0 hτ.le)
  have e1 : τ * (s / τ) = s := by field_simp
  rw [abs_le]; constructor
  · nlinarith [mul_le_mul_of_nonneg_left h1 hτ.le]
  · nlinarith [mul_lt_mul_of_pos_left h2 hτ]

/-- Partial sums over `{j τ < s}` and over the walk index `{j < ⌊s/τ⌋}` differ by at most one
term. -/
theorem abs_sum_lt_sub_sum_floor_le {N : ℕ} {τ s A : ℝ} (hτ : 0 < τ) (hA : 0 ≤ A)
    (a : Fin N → ℝ) (ha : ∀ j, |a j| ≤ A) :
    |(∑ j : Fin N, if (j : ℝ) * τ < s then a j else 0) -
        ∑ j : Fin N, if (j : ℕ) < ⌊s / τ⌋₊ then a j else 0|
      ≤ A := by
  rw [← sum_sub_distrib]
  set D := univ.filter (fun j : Fin N => ⌊s / τ⌋₊ ≤ (j : ℕ) ∧ (j : ℝ) * τ < s)
  have hterm : ∀ j : Fin N, ((if (j : ℝ) * τ < s then a j else 0) -
      if (j : ℕ) < ⌊s / τ⌋₊ then a j else 0) = if j ∈ D then a j else 0 := by
    intro j
    have hlt : (j : ℕ) < ⌊s / τ⌋₊ → (j : ℝ) * τ < s := by
      intro h
      have h1 : ((j : ℕ) : ℝ) < ⌊s / τ⌋₊ := by exact_mod_cast h
      have h2 : ((⌊s / τ⌋₊ : ℕ) : ℝ) ≤ s / τ :=
        Nat.floor_le (by
          by_contra hneg
          push Not at hneg
          have : ⌊s / τ⌋₊ = 0 := Nat.floor_eq_zero.2 (by linarith)
          omega)
      rw [← lt_div_iff₀ hτ]; linarith
    simp only [D, mem_filter, mem_univ, true_and]
    by_cases h1 : (j : ℕ) < ⌊s / τ⌋₊
    · simp [h1, hlt h1, not_le.2 h1]
    · by_cases h2 : (j : ℝ) * τ < s
      · simp [h1, h2, not_lt.1 h1]
      · simp [h1, h2]
  simp_rw [hterm]
  rw [sum_ite_mem, univ_inter]
  have hcard : D.card ≤ 1 := by
    rw [card_le_one]
    intro i hi j hj
    simp only [D, mem_filter, mem_univ, true_and] at hi hj
    have key : ∀ k : Fin N, ⌊s / τ⌋₊ ≤ (k : ℕ) → (k : ℝ) * τ < s → (k : ℕ) = ⌊s / τ⌋₊ := by
      intro k hk1 hk2
      have : ((k : ℕ) : ℝ) < s / τ := by rw [lt_div_iff₀ hτ]; exact hk2
      have h3 : (k : ℕ) < ⌊s / τ⌋₊ + 1 := by
        have := Nat.lt_floor_add_one (s / τ)
        exact_mod_cast (show ((k : ℕ) : ℝ) < (⌊s / τ⌋₊ : ℝ) + 1 by linarith)
      omega
    exact Fin.ext ((key i hi.1 hi.2).trans (key j hj.1 hj.2).symm)
  calc |∑ j ∈ D, a j| ≤ ∑ j ∈ D, |a j| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ _j ∈ D, A := sum_le_sum fun j _ => ha j
    _ = D.card * A := by rw [sum_const, nsmul_eq_mul]
    _ ≤ 1 * A := mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) hA
    _ = A := one_mul A

/-- The granular energy of a step function on the time lattice converges to `‖h‖²`:
`|∑_j h(jτ)² τ - ‖h‖²| ≤ 2 τ ∑ c_i²`. -/
theorem abs_sum_val_sq_sub_nrm2_le {T : ℝ} (hT : 0 < T) {N : ℕ} (hN : 0 < N) (h : StepFn T) :
    |∑ j : Fin N, h.val (j * (T / N)) ^ 2 * (T / N) - h.nrm2| ≤
      2 * (T / N) * ∑ i, h.c i ^ 2 := by
  set τ := T / N with hτdef
  have hτ : 0 < τ := by positivity
  have hNτ : (N : ℝ) * τ = T := by rw [hτdef]; field_simp
  have hcnt : ∀ u ∈ Set.Icc (0 : ℝ) T,
      |τ * (univ.filter (fun j : Fin N => (j : ℝ) * τ < u)).card - u| ≤ τ :=
    fun u hu => abs_mul_card_sub_le hτ hu.1 (by rw [hNτ]; exact hu.2)
  have e1 : ∑ j : Fin N, h.val (j * τ) ^ 2 * τ = ∑ i, h.c i ^ 2 *
      (τ * (univ.filter (fun j : Fin N => (j : ℝ) * τ < h.s i.succ)).card -
        τ * (univ.filter (fun j : Fin N => (j : ℝ) * τ < h.s i.castSucc)).card) := by
    simp_rw [StepFn.val_sq, sum_mul]
    rw [sum_comm]
    apply sum_congr rfl; intro i _
    rw [card_eq_sum_ones, card_eq_sum_ones, sum_filter, sum_filter]
    push_cast
    rw [mul_sum, mul_sum, ← sum_sub_distrib, mul_sum]
    apply sum_congr rfl; intro j _
    have := StepFn.ind_Ico_eq (x := (j : ℝ) * τ) (h.mono (Fin.castSucc_le_succ i))
    have e : (if h.s i.castSucc ≤ (j : ℝ) * τ ∧ (j : ℝ) * τ < h.s i.succ then h.c i ^ 2 else 0) =
        h.c i ^ 2 * (if h.s i.castSucc ≤ (j : ℝ) * τ ∧ (j : ℝ) * τ < h.s i.succ
          then (1 : ℝ) else 0) := by split_ifs <;> simp
    rw [e, this]; split_ifs <;> ring
  rw [e1, StepFn.nrm2, ← sum_sub_distrib, mul_sum]
  refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun i _ => ?_)
  rw [← mul_sub, abs_mul, abs_of_nonneg (sq_nonneg _)]
  have h1 := hcnt _ (h.s_mem i.succ)
  have h2 := hcnt _ (h.s_mem i.castSucc)
  have : |τ * ((univ.filter (fun j : Fin N => (j : ℝ) * τ < h.s i.succ)).card : ℝ) -
      τ * (univ.filter (fun j : Fin N => (j : ℝ) * τ < h.s i.castSucc)).card -
        (h.s i.succ - h.s i.castSucc)| ≤ 2 * τ := by
    rw [abs_le] at h1 h2 ⊢; constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]
  nlinarith [sq_nonneg (h.c i)]

/-- The step function evaluated on the time lattice is bounded by `∑ |c_i|`. -/
theorem abs_val_le_sum {T : ℝ} (h : StepFn T) (u : ℝ) : |h.val u| ≤ ∑ i, |h.c i| :=
  StepFn.abs_val_le h u

end StepSums

section Internal

open QE.Chaos.Loeb QE.Chaos.DExp QE.NSA MeasureTheory Filter Topology
open QE.OpenSto.Walsh (sgn)

variable (T : ℝ) (n : ℕ → ℕ)

/-- The Loeb Brownian motion `b = st W` as a process indexed by real time. -/
def bproc : ℝ → Ult (ℕ → Bool) → ℝ := fun t ω => andersonB T n t ω

/-- The step function sampled on the time lattice `j τ`, `τ = T/n_k`. -/
def sv (h : StepFn T) (k : ℕ) : Fin (n k) → ℝ := fun j => h.val (j * (T / n k))

/-- The space step `√τ`. -/
def cc (k : ℕ) : ℝ := √(T / n k)

/-- The increments `h(t_j) ΔW_j` of the discrete Wiener integral. -/
def xin (h : StepFn T) (k : ℕ) (ω : Fin (n k) → Bool) : Fin (n k) → ℝ :=
  DExp.incr (sv T n h k) (cc T n k) ω

/-- The discrete Wiener integral `p₁ = ∑_j h(t_j) ΔW_j`. -/
def pI (h : StepFn T) : ∀ k, (Fin (n k) → Bool) → ℝ := fun k ω => ps 1 (xin T n h k ω)

/-- The discrete stochastic exponential `𝓔_n(h) = ∏_j (1 + h(t_j) ΔW_j)`. -/
def pE (h : StepFn T) : ∀ k, (Fin (n k) → Bool) → ℝ := fun k ω => ∏ i, (1 + xin T n h k ω i)

/-- Its `m`-th Walsh level, the elementary symmetric sum `e_m`. -/
def pS (m : ℕ) (h : StepFn T) : ∀ k, (Fin (n k) → Bool) → ℝ := fun k ω => es m (xin T n h k ω)

variable {T n}

theorem sgn_sq' (b : Bool) : (sgn b : ℝ) ^ 2 = 1 := by cases b <;> simp [sgn]

theorem ps2_xin (h : StepFn T) (k : ℕ) (ω : Fin (n k) → Bool) (hT : 0 ≤ T) :
    ps 2 (xin T n h k ω) = ∑ j : Fin (n k), h.val (j * (T / n k)) ^ 2 * (T / n k) := by
  unfold ps xin DExp.incr sv cc
  apply Finset.sum_congr rfl; intro j _
  rw [mul_pow, mul_pow, sgn_sq', Real.sq_sqrt (div_nonneg hT (Nat.cast_nonneg _))]; ring

theorem tendsto_cc (hn : IsUnlimited ((n : ℕ → ℕ) : Ult ℕ)) :
    Tendsto (fun k => cc T n k) (hyperfilter ℕ : Filter ℕ) (𝓝 0) := by
  have := (tendsto_dt (T := T) hn).sqrt
  simpa [cc] using this

theorem eventually_n_pos (hn : IsUnlimited ((n : ℕ → ℕ) : Ult ℕ)) :
    ∀ᶠ k in (hyperfilter ℕ : Filter ℕ), 0 < n k :=
  QE.Chaos.Loeb.eventually_pos_of_unlimited hn

theorem tendsto_ps2_xin (hT : 0 < T) (hn : IsUnlimited ((n : ℕ → ℕ) : Ult ℕ)) (h : StepFn T)
    (w : ∀ k, Fin (n k) → Bool) :
    Tendsto (fun k => ps 2 (xin T n h k (w k))) (hyperfilter ℕ : Filter ℕ) (𝓝 h.nrm2) := by
  have hb : Tendsto (fun k => 2 * (T / n k) * ∑ i, h.c i ^ 2) (hyperfilter ℕ : Filter ℕ)
      (𝓝 0) := by
    have := ((tendsto_dt (T := T) hn).const_mul 2).mul_const (∑ i, h.c i ^ 2)
    simpa using this
  refine tendsto_of_abs_sub_le hb ?_
  filter_upwards [eventually_n_pos hn] with k hk
  rw [ps2_xin h k (w k) hT.le]
  exact abs_sum_val_sq_sub_nrm2_le hT hk h

/-- The increments are uniformly small: `|h(t_j) ΔW_j| ≤ (∑|c_i|) √τ`. -/
theorem abs_xin_le (h : StepFn T) (k : ℕ) (ω : Fin (n k) → Bool) (i : Fin (n k)) :
    |xin T n h k ω i| ≤ (∑ i, |h.c i|) * cc T n k := by
  unfold xin DExp.incr sv
  rw [abs_mul, abs_mul]
  have : |(sgn (ω i) : ℝ)| = 1 := by cases ω i <;> simp [sgn]
  have hc : 0 ≤ cc T n k := Real.sqrt_nonneg _
  rw [this, mul_one, abs_of_nonneg hc]
  exact mul_le_mul_of_nonneg_right (StepFn.abs_val_le h _) hc

theorem tendsto_M (hn : IsUnlimited ((n : ℕ → ℕ) : Ult ℕ)) (h : StepFn T) :
    Tendsto (fun k => (∑ i, |h.c i|) * cc T n k) (hyperfilter ℕ : Filter ℕ) (𝓝 0) := by
  simpa using (tendsto_cc (T := T) hn).const_mul (∑ i, |h.c i|)

/-- **The discrete Wiener integral against the walk**: along any representative path, `p₁`
is within `2 ∑|c_i| √τ` of `∑ c_i (W(s_{i+1}) - W(s_i))`. -/
theorem abs_pI_sub_walk_le (hT : 0 < T) (h : StepFn T) {k : ℕ} (hk : 0 < n k) (u : ℕ → Bool) :
    |pI T n h k (fun i => u i) -
        ∑ i, h.c i * (walkSeq T n (h.s i.succ) k u - walkSeq T n (h.s i.castSucc) k u)| ≤
      2 * (∑ i, |h.c i|) * cc T n k := by
  set τ := T / n k with hτ
  have hτ0 : 0 < τ := by positivity
  set c := cc T n k
  have hc : 0 ≤ c := Real.sqrt_nonneg _
  -- p₁ as a combination of partial sums
  have e1 : pI T n h k (fun i => u i) = ∑ i, h.c i *
      ((∑ j : Fin (n k), if (j : ℝ) * τ < h.s i.succ then c * sgn (u j) else 0) -
        ∑ j : Fin (n k), if (j : ℝ) * τ < h.s i.castSucc then c * sgn (u j) else 0) := by
    have := StepFn.sum_val_mul (univ : Finset (Fin (n k))) h (fun j => (j : ℝ) * τ)
      (fun j => c * sgn (u j))
    rw [← this]
    unfold pI ps xin DExp.incr sv
    apply Finset.sum_congr rfl; intro j _; simp [c]; ring
  -- the walk as a partial sum
  have hwalk : ∀ t ∈ Set.Icc (0 : ℝ) T, walkSeq T n t k u =
      ∑ j : Fin (n k), if (j : ℕ) < ⌊t / τ⌋₊ then c * sgn (u j) else 0 := by
    intro t ht
    unfold walkSeq
    have hle : walkIdx T (n k) t ≤ n k := walkIdx_le hT hk ht.2
    rw [← QE.Chaos.Loeb.sum_fin_lt_eq_blockSum hle u, Finset.mul_sum, Finset.sum_filter]
    apply Finset.sum_congr rfl; intro j _
    have e : walkIdx T (n k) t = ⌊t / τ⌋₊ := rfl
    rw [e]
    by_cases hj : (j : ℕ) < ⌊t / τ⌋₊
    · rw [if_pos hj, if_pos hj]; rfl
    · rw [if_neg hj, if_neg hj]
  have hdiff : ∀ t ∈ Set.Icc (0 : ℝ) T,
      |(∑ j : Fin (n k), if (j : ℝ) * τ < t then c * sgn (u j) else 0) - walkSeq T n t k u| ≤ c := by
    intro t ht
    rw [hwalk t ht]
    refine abs_sum_lt_sub_sum_floor_le hτ0 hc _ fun j => ?_
    rw [abs_mul, abs_of_nonneg hc]
    have : |(sgn (u j) : ℝ)| = 1 := by cases u j <;> simp [sgn]
    rw [this, mul_one]
  rw [e1, ← Finset.sum_sub_distrib]
  calc |∑ i, (h.c i * ((∑ j : Fin (n k), if (j : ℝ) * τ < h.s i.succ then c * sgn (u j) else 0) -
          ∑ j : Fin (n k), if (j : ℝ) * τ < h.s i.castSucc then c * sgn (u j) else 0) -
        h.c i * (walkSeq T n (h.s i.succ) k u - walkSeq T n (h.s i.castSucc) k u))|
      ≤ ∑ i, |h.c i| * (2 * c) := by
        refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
        rw [← mul_sub, abs_mul]
        refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
        have h1 := hdiff _ (h.s_mem i.succ)
        have h2 := hdiff _ (h.s_mem i.castSucc)
        calc _ = |((∑ j : Fin (n k), if (j : ℝ) * τ < h.s i.succ then c * sgn (u j) else 0) -
              walkSeq T n (h.s i.succ) k u) - ((∑ j : Fin (n k), if (j : ℝ) * τ < h.s i.castSucc
                then c * sgn (u j) else 0) - walkSeq T n (h.s i.castSucc) k u)| := by
              congr 1; ring
          _ ≤ c + c := (abs_sub _ _).trans (add_le_add h1 h2)
          _ = 2 * c := by ring
    _ = 2 * (∑ i, |h.c i|) * c := by rw [← Finset.sum_mul]; ring

end Internal

section Shadows

open QE.Chaos.Loeb QE.Chaos.DExp QE.NSA MeasureTheory Filter Topology ArchimedeanClass
open QE.OpenSto.Walsh (sgn)

variable {T : ℝ} {n : ℕ → ℕ}

theorem ae_isFinite_walk_s (hT : 0 < T) (hn : IsUnlimited ((n : ℕ → ℕ) : Ult ℕ)) (h : StepFn T) :
    ∀ᵐ ω ∂(L n), ∀ i, IsFinite (andersonW T n (h.s i) ω) := by
  refine ae_all_iff.2 fun i => ?_
  exact ae_isFinite_andersonW hT hn (t := ⟨h.s i, (h.s_mem i).1⟩) (h.s_mem i).2

/-- Along a representative path where the walk at the jump times converges, `p₁ → I₁(h)`. -/
theorem tendsto_pI (hT : 0 < T) (hn : IsUnlimited ((n : ℕ → ℕ) : Ult ℕ)) (h : StepFn T)
    (u : ℕ → ℕ → Bool) (β : Fin (h.r + 1) → ℝ)
    (hβ : ∀ i, Tendsto (fun k => walkSeq T n (h.s i) k (u k)) (hyperfilter ℕ : Filter ℕ) (𝓝 (β i))) :
    Tendsto (fun k => pI T n h k (fun i => u k i)) (hyperfilter ℕ : Filter ℕ)
      (𝓝 (∑ i, h.c i * (β i.succ - β i.castSucc))) := by
  have hW : Tendsto (fun k => ∑ i, h.c i * (walkSeq T n (h.s i.succ) k (u k) -
      walkSeq T n (h.s i.castSucc) k (u k))) (hyperfilter ℕ : Filter ℕ)
      (𝓝 (∑ i, h.c i * (β i.succ - β i.castSucc))) :=
    tendsto_finsetSum _ fun i _ => ((hβ _).sub (hβ _)).const_mul _
  have hdiff : Tendsto (fun k => pI T n h k (fun i => u k i) - ∑ i, h.c i *
      (walkSeq T n (h.s i.succ) k (u k) - walkSeq T n (h.s i.castSucc) k (u k)))
      (hyperfilter ℕ : Filter ℕ) (𝓝 0) := by
    have hb : Tendsto (fun k => 2 * (∑ i, |h.c i|) * cc T n k) (hyperfilter ℕ : Filter ℕ)
        (𝓝 0) := by simpa using (tendsto_cc (T := T) hn).const_mul (2 * ∑ i, |h.c i|)
    refine tendsto_of_abs_sub_le hb ?_
    filter_upwards [eventually_n_pos hn] with k hk
    rw [sub_zero]; exact abs_pI_sub_walk_le hT h hk (u k)
  simpa using hdiff.add hW

/-- **The discrete Wiener integral lifts the Wiener integral**: `st p₁ = I₁(h)(b)` a.s. -/
theorem ae_st_pI (hT : 0 < T) (hn : IsUnlimited ((n : ℕ → ℕ) : Ult ℕ)) (h : StepFn T) :
    ∀ᵐ ω ∂(L n), IsFinite (iF n (pI T n h) ω) ∧
      stdPart (iF n (pI T n h) ω) = h.I1 (bproc T n) ω := by
  filter_upwards [ae_isFinite_walk_s hT hn h] with ω hω
  obtain ⟨u, rfl⟩ := exists_rep ω
  have hβ : ∀ i, Tendsto (fun k => walkSeq T n (h.s i) k (u k)) (hyperfilter ℕ : Filter ℕ)
      (𝓝 (andersonB T n (h.s i) (u : Ult (ℕ → Bool)))) := by
    intro i
    exact (ofSeq_st_iff_tendsto _ _).1 ⟨hω i, rfl⟩
  rw [iF_coe]
  exact (ofSeq_st_iff_tendsto _ _).2 (tendsto_pI hT hn h u _ hβ)

/-- `st e_m(h ΔW) = heH_m(I₁(h), ‖h‖²)/m!` almost surely. -/
theorem ae_st_pS (hT : 0 < T) (hn : IsUnlimited ((n : ℕ → ℕ) : Ult ℕ)) (h : StepFn T) (m : ℕ) :
    ∀ᵐ ω ∂(L n), IsFinite (iF n (pS T n m h) ω) ∧
      stdPart (iF n (pS T n m h) ω) = heH m (h.I1 (bproc T n) ω) h.nrm2 / m.factorial := by
  filter_upwards [ae_st_pI hT hn h] with ω hω
  obtain ⟨u, rfl⟩ := exists_rep ω
  rw [iF_coe] at hω ⊢
  have h1 := (ofSeq_st_iff_tendsto _ _).1 hω
  have h2 := tendsto_ps2_xin hT hn h (fun k i => u k i)
  have h3 := tendsto_ps_zero (fun k => xin T n h k (fun i => u k i)) _
    (fun k i => abs_xin_le h k _ i) (tendsto_M hn h) h2
  exact (ofSeq_st_iff_tendsto _ _).2 (tendsto_es _ h1 h2 h3 m)

/-- `st 𝓔_n(h) = 𝓔(h)(b)` almost surely. -/
theorem ae_st_pE (hT : 0 < T) (hn : IsUnlimited ((n : ℕ → ℕ) : Ult ℕ)) (h : StepFn T) :
    ∀ᵐ ω ∂(L n), IsFinite (iF n (pE T n h) ω) ∧
      stdPart (iF n (pE T n h) ω) = Expo (bproc T n) h ω := by
  filter_upwards [ae_st_pI hT hn h] with ω hω
  obtain ⟨u, rfl⟩ := exists_rep ω
  rw [iF_coe] at hω ⊢
  have h1 := (ofSeq_st_iff_tendsto _ _).1 hω
  have h2 := tendsto_ps2_xin hT hn h (fun k i => u k i)
  exact (ofSeq_st_iff_tendsto _ _).2 (tendsto_prod_one_add _ _
    (fun k i => abs_xin_le h k _ i) (tendsto_M hn h) h1 h2)

/-! ### Moment bounds and S-integrability -/

/-- A uniform bound for the granular energy. -/
def Bh (h : StepFn T) : ℝ := h.nrm2 + 2 * T * ∑ i, h.c i ^ 2

theorem sum_sv_sq_le (hT : 0 < T) (h : StepFn T) {k : ℕ} (hk : 0 < n k) :
    ∑ j : Fin (n k), sv T n h k j ^ 2 * cc T n k ^ 2 ≤ Bh h := by
  have hτ : T / n k ≤ T := div_le_self hT.le (by exact_mod_cast hk)
  have := abs_sum_val_sq_sub_nrm2_le hT hk h
  have e : ∑ j : Fin (n k), sv T n h k j ^ 2 * cc T n k ^ 2 =
      ∑ j : Fin (n k), h.val (j * (T / n k)) ^ 2 * (T / n k) := by
    apply Finset.sum_congr rfl; intro j _
    simp only [sv, cc]; rw [Real.sq_sqrt (div_nonneg hT.le (Nat.cast_nonneg _))]
  rw [e]
  have hc : 0 ≤ ∑ i, h.c i ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
  unfold Bh
  have := (abs_le.1 this).2
  nlinarith [mul_le_mul_of_nonneg_right hτ hc]

theorem cc_le (hT : 0 < T) {k : ℕ} (hk : 0 < n k) : cc T n k ≤ √T :=
  Real.sqrt_le_sqrt (div_le_self hT.le (by exact_mod_cast hk))

theorem isFinite_ofSeq_of_eventually_le {w : ℕ → ℝ} {C : ℝ} (h0 : ∀ k, 0 ≤ w k)
    (h : ∀ᶠ k in (hyperfilter ℕ : Filter ℕ), w k ≤ C) : IsFinite (Hyperreal.ofSeq w) :=
  (isFinite_ofSeq_iff w).2 ⟨C, h.mono fun k hk => by rwa [abs_of_nonneg (h0 k)]⟩

open QE.Chaos.Bon in
theorem isDeg_pS (h : StepFn T) (m k : ℕ) : IsDeg (n k) (fun ω => pS T n m h k ω) m := by
  unfold pS es xin DExp.incr
  refine isDeg_sum _ _ m fun S hS => ?_
  have hc := (Finset.mem_powersetCard.1 hS).2
  have := isDeg_prod S (fun i (ω : Fin (n k) → Bool) => sv T n h k i * cc T n k * sgn (ω i))
    (fun _ => 1) fun i _ => ((isDeg_coin i).const_mul (sv T n h k i * cc T n k)).congr
      fun ω => by ring
  simpa [hc] using this

theorem es_one_eq_ps_one {N : ℕ} (x : Fin N → ℝ) : es 1 x = ps 1 x := by
  simp [es, ps, Finset.powersetCard_one]

theorem pI_eq_pS (h : StepFn T) (k : ℕ) (ω : Fin (n k) → Bool) :
    pI T n h k ω = pS T n 1 h k ω := by
  simp [pI, pS, es_one_eq_ps_one]

theorem E_pS_sq_le (hT : 0 < T) (h : StepFn T) (m : ℕ) {k : ℕ} (hk : 0 < n k) :
    QE.OpenSto.Walsh.E (fun ω => pS T n m h k ω ^ 2) ≤ Bh h ^ m / m.factorial := by
  unfold pS xin
  rw [E_es_sq]
  refine (es_le_ps_pow _ (fun i => by positivity) m).trans ?_
  have hps : ps 1 (fun i => sv T n h k i ^ 2 * cc T n k ^ 2) ≤ Bh h := by
    simpa [ps] using sum_sv_sq_le hT h hk
  have h0 : 0 ≤ ps 1 (fun i => sv T n h k i ^ 2 * cc T n k ^ 2) :=
    Finset.sum_nonneg fun i _ => by simp only [pow_one]; positivity
  gcongr

theorem SInt_pS_sq (hT : 0 < T) (hn : IsUnlimited ((n : ℕ → ℕ) : Ult ℕ)) (h : StepFn T)
    (m : ℕ) : SInt n (fun k ω => pS T n m h k ω ^ 2) := by
  refine SInt_of_sq_finite ?_
  refine isFinite_ofSeq_of_eventually_le (C := 9 ^ m * (Bh h ^ m / m.factorial) ^ 2)
    (fun k => by rw [← avg_eq_E]; exact avg_nonneg fun ω => by positivity) ?_
  filter_upwards [eventually_n_pos hn] with k hk
  have hb := QE.Chaos.Bon.bonami _ (isDeg_pS (T := T) (n := n) h m k)
  have h2 := E_pS_sq_le hT h m hk
  have h20 : 0 ≤ QE.OpenSto.Walsh.E (fun ω => pS T n m h k ω ^ 2) := by
    rw [← avg_eq_E]; exact avg_nonneg fun ω => by positivity
  calc QE.OpenSto.Walsh.E (fun ω => (pS T n m h k ω ^ 2) ^ 2)
      = QE.OpenSto.Walsh.E (fun ω => pS T n m h k ω ^ 4) := by
        congr 1; funext ω; ring
    _ ≤ 9 ^ m * QE.OpenSto.Walsh.E (fun ω => pS T n m h k ω ^ 2) ^ 2 := hb
    _ ≤ 9 ^ m * (Bh h ^ m / m.factorial) ^ 2 := by gcongr

theorem SInt_pI_sq (hT : 0 < T) (hn : IsUnlimited ((n : ℕ → ℕ) : Ult ℕ)) (h : StepFn T) :
    SInt n (fun k ω => pI T n h k ω ^ 2) := by
  have := SInt_pS_sq hT hn h 1
  simpa [pI_eq_pS] using this

theorem SInt_pE_sq (hT : 0 < T) (hn : IsUnlimited ((n : ℕ → ℕ) : Ult ℕ)) (h : StepFn T) :
    SInt n (fun k ω => pE T n h k ω ^ 2) := by
  refine SInt_of_sq_finite ?_
  set A := ∑ i, |h.c i|
  refine isFinite_ofSeq_of_eventually_le
    (C := Real.exp (6 * Bh h + A ^ 2 * T * Bh h))
    (fun k => by rw [← avg_eq_E]; exact avg_nonneg fun ω => by positivity) ?_
  filter_upwards [eventually_n_pos hn] with k hk
  have h4 := E_prod_one_add_pow4_le (sv T n h k) (cc T n k)
  have hsum := sum_sv_sq_le hT h hk
  have hsmall : ∀ j, sv T n h k j ^ 2 * cc T n k ^ 2 ≤ A ^ 2 * T := by
    intro j
    have h1 := abs_xin_le (T := T) (n := n) h k (fun _ => true) j
    have hc0 : 0 ≤ cc T n k := Real.sqrt_nonneg _
    have e : |xin T n h k (fun _ => true) j| = |sv T n h k j| * cc T n k := by
      simp only [xin, DExp.incr, abs_mul, QE.OpenSto.Walsh.sgn, if_true, abs_one, mul_one,
        abs_of_nonneg hc0]
    rw [e] at h1
    have hcT := cc_le (n := n) hT hk
    have hA : 0 ≤ A := Finset.sum_nonneg fun i _ => abs_nonneg _
    have : |sv T n h k j| * cc T n k ≤ A * √T :=
      h1.trans (mul_le_mul_of_nonneg_left hcT hA)
    have h0 : 0 ≤ |sv T n h k j| * cc T n k := mul_nonneg (abs_nonneg _) hc0
    calc sv T n h k j ^ 2 * cc T n k ^ 2 = (|sv T n h k j| * cc T n k) ^ 2 := by
          rw [mul_pow, sq_abs]
      _ ≤ (A * √T) ^ 2 := by gcongr
      _ = A ^ 2 * T := by rw [mul_pow, Real.sq_sqrt hT.le]
  have hexp : ∑ i, (6 * sv T n h k i ^ 2 * cc T n k ^ 2 + sv T n h k i ^ 4 * cc T n k ^ 4) ≤
      6 * Bh h + A ^ 2 * T * Bh h := by
    rw [Finset.sum_add_distrib]
    have e1 : ∑ i, 6 * sv T n h k i ^ 2 * cc T n k ^ 2 =
        6 * ∑ i, sv T n h k i ^ 2 * cc T n k ^ 2 := by
      rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro i _; ring
    have e2 : ∑ i, sv T n h k i ^ 4 * cc T n k ^ 4 ≤ A ^ 2 * T * ∑ i, sv T n h k i ^ 2 * cc T n k ^ 2 := by
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum fun i _ => ?_
      have := hsmall i
      have h0 : 0 ≤ sv T n h k i ^ 2 * cc T n k ^ 2 := by positivity
      calc sv T n h k i ^ 4 * cc T n k ^ 4 = (sv T n h k i ^ 2 * cc T n k ^ 2) *
            (sv T n h k i ^ 2 * cc T n k ^ 2) := by ring
        _ ≤ A ^ 2 * T * (sv T n h k i ^ 2 * cc T n k ^ 2) := mul_le_mul_of_nonneg_right this h0
    have hAT : 0 ≤ A ^ 2 * T := by positivity
    rw [e1]
    nlinarith [mul_le_mul_of_nonneg_left hsum hAT]
  calc QE.OpenSto.Walsh.E (fun ω => (pE T n h k ω ^ 2) ^ 2)
      = QE.OpenSto.Walsh.E (fun ω => (∏ i, (1 + DExp.incr (sv T n h k) (cc T n k) ω i)) ^ 4) := by
        congr 1; funext ω; simp only [pE, xin]; ring
    _ ≤ _ := h4
    _ ≤ _ := Real.exp_le_exp.2 hexp

/-! ### Products of two step functions on the lattice -/

/-- `y_j = h(t_j) h'(t_j) τ`. -/
def yv (T : ℝ) (n : ℕ → ℕ) (h h' : StepFn T) (k : ℕ) : Fin (n k) → ℝ :=
  fun i => sv T n h k i * sv T n h' k i * cc T n k ^ 2

theorem abs_sv_cc_le (h : StepFn T) (k : ℕ) (j : Fin (n k)) :
    |sv T n h k j| * cc T n k ≤ (∑ i, |h.c i|) * cc T n k := by
  have hc0 : 0 ≤ cc T n k := Real.sqrt_nonneg _
  have h1 := abs_xin_le (T := T) (n := n) h k (fun _ => true) j
  have e : |xin T n h k (fun _ => true) j| = |sv T n h k j| * cc T n k := by
    simp only [xin, DExp.incr, abs_mul, QE.OpenSto.Walsh.sgn, if_true, abs_one, mul_one,
      abs_of_nonneg hc0]
  rwa [e] at h1

theorem abs_yv_le (h h' : StepFn T) (k : ℕ) (j : Fin (n k)) :
    |yv T n h h' k j| ≤ ((∑ i, |h.c i|) * cc T n k) * ((∑ i, |h'.c i|) * cc T n k) := by
  have e : |yv T n h h' k j| = (|sv T n h k j| * cc T n k) * (|sv T n h' k j| * cc T n k) := by
    have hc0 : |cc T n k| = cc T n k := abs_of_nonneg (Real.sqrt_nonneg _)
    simp only [yv, abs_mul, abs_pow, hc0]; ring
  rw [e]
  exact mul_le_mul (abs_sv_cc_le h k j) (abs_sv_cc_le h' k j)
    (mul_nonneg (abs_nonneg _) (Real.sqrt_nonneg _))
    (mul_nonneg (Finset.sum_nonneg fun i _ => abs_nonneg _) (Real.sqrt_nonneg _))

theorem sum_abs_yv_le (hT : 0 < T) (h h' : StepFn T) {k : ℕ} (hk : 0 < n k) :
    ∑ j, |yv T n h h' k j| ≤ (Bh h + Bh h') / 2 := by
  have h1 := sum_sv_sq_le hT h hk
  have h2 := sum_sv_sq_le hT h' hk
  have : ∑ j, |yv T n h h' k j| ≤ ∑ j : Fin (n k), (sv T n h k j ^ 2 * cc T n k ^ 2 +
      sv T n h' k j ^ 2 * cc T n k ^ 2) / 2 := by
    refine Finset.sum_le_sum fun j _ => ?_
    have e : |yv T n h h' k j| = |sv T n h k j * cc T n k| * |sv T n h' k j * cc T n k| := by
      simp only [yv, abs_mul, abs_pow]; ring
    rw [e]
    nlinarith [sq_abs (sv T n h k j * cc T n k), sq_abs (sv T n h' k j * cc T n k),
      sq_nonneg (|sv T n h k j * cc T n k| - |sv T n h' k j * cc T n k|)]
  rw [← Finset.sum_div, Finset.sum_add_distrib] at this
  linarith

/-- The shadow of `e_m(y)`: `(st ∑ y)^m / m!`. -/
theorem tendsto_es_yv (hT : 0 < T) (hn : IsUnlimited ((n : ℕ → ℕ) : Ult ℕ)) (h h' : StepFn T) :
    IsFinite (Hyperreal.ofSeq fun k => ps 1 (yv T n h h' k)) ∧
    ∀ m, Tendsto (fun k => es m (yv T n h h' k)) (hyperfilter ℕ : Filter ℕ)
      (𝓝 (stdPart (Hyperreal.ofSeq fun k => ps 1 (yv T n h h' k)) ^ m / m.factorial)) := by
  have hfin : IsFinite (Hyperreal.ofSeq fun k => ps 1 (yv T n h h' k)) := by
    refine (isFinite_ofSeq_iff _).2 ⟨(Bh h + Bh h') / 2, ?_⟩
    filter_upwards [eventually_n_pos hn] with k hk
    refine le_trans ?_ (sum_abs_yv_le hT h h' hk)
    simp only [ps, pow_one]; exact Finset.abs_sum_le_sum_abs _ _
  refine ⟨hfin, fun m => ?_⟩
  set a := stdPart (Hyperreal.ofSeq fun k => ps 1 (yv T n h h' k))
  have h1 := (ofSeq_st_iff_tendsto _ _).1 ⟨hfin, rfl⟩
  set M : ℕ → ℝ := fun k => ((∑ i, |h.c i|) * cc T n k) * ((∑ i, |h'.c i|) * cc T n k)
  have hM0 : Tendsto M (hyperfilter ℕ : Filter ℕ) (𝓝 0) := by
    simpa using (tendsto_M hn h).mul (tendsto_M hn h')
  have h2 : Tendsto (fun k => ps 2 (yv T n h h' k)) (hyperfilter ℕ : Filter ℕ) (𝓝 0) := by
    have hb : Tendsto (fun k => M k * ((Bh h + Bh h') / 2)) (hyperfilter ℕ : Filter ℕ) (𝓝 0) := by
      simpa using hM0.mul_const ((Bh h + Bh h') / 2)
    refine tendsto_of_abs_sub_le hb ?_
    filter_upwards [eventually_n_pos hn] with k hk
    rw [sub_zero]
    have hM : 0 ≤ M k := by
      simp only [M]; exact mul_nonneg (mul_nonneg (Finset.sum_nonneg fun i _ => abs_nonneg _)
        (Real.sqrt_nonneg _)) (mul_nonneg (Finset.sum_nonneg fun i _ => abs_nonneg _)
        (Real.sqrt_nonneg _))
    calc |ps 2 (yv T n h h' k)| ≤ ∑ j, |yv T n h h' k j ^ 2| := by
          simp only [ps]; exact Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ j, M k * |yv T n h h' k j| := by
          refine Finset.sum_le_sum fun j _ => ?_
          rw [abs_pow, sq]
          exact mul_le_mul_of_nonneg_right (abs_yv_le h h' k j) (abs_nonneg _)
      _ = M k * ∑ j, |yv T n h h' k j| := by rw [Finset.mul_sum]
      _ ≤ M k * ((Bh h + Bh h') / 2) :=
          mul_le_mul_of_nonneg_left (sum_abs_yv_le hT h h' hk) hM
  have h3 := tendsto_ps_zero (yv T n h h') M (fun k j => abs_yv_le h h' k j) hM0 h2
  have := tendsto_es (yv T n h h') h1 h2 h3 m
  rwa [Wiener.heH_zero_right] at this

theorem tendsto_ps2_yv (hT : 0 < T) (hn : IsUnlimited ((n : ℕ → ℕ) : Ult ℕ)) (h h' : StepFn T) :
    Tendsto (fun k => ps 2 (yv T n h h' k)) (hyperfilter ℕ : Filter ℕ) (𝓝 0) := by
  set M : ℕ → ℝ := fun k => ((∑ i, |h.c i|) * cc T n k) * ((∑ i, |h'.c i|) * cc T n k)
  have hM0 : Tendsto M (hyperfilter ℕ : Filter ℕ) (𝓝 0) := by
    simpa using (tendsto_M hn h).mul (tendsto_M hn h')
  have hb : Tendsto (fun k => M k * ((Bh h + Bh h') / 2)) (hyperfilter ℕ : Filter ℕ) (𝓝 0) := by
    simpa using hM0.mul_const ((Bh h + Bh h') / 2)
  refine tendsto_of_abs_sub_le hb ?_
  filter_upwards [eventually_n_pos hn] with k hk
  rw [sub_zero]
  have hM : 0 ≤ M k := by
    simp only [M]; exact mul_nonneg (mul_nonneg (Finset.sum_nonneg fun i _ => abs_nonneg _)
      (Real.sqrt_nonneg _)) (mul_nonneg (Finset.sum_nonneg fun i _ => abs_nonneg _)
      (Real.sqrt_nonneg _))
  calc |ps 2 (yv T n h h' k)| ≤ ∑ j, |yv T n h h' k j ^ 2| := by
        simp only [ps]; exact Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j, M k * |yv T n h h' k j| := by
        refine Finset.sum_le_sum fun j _ => ?_
        rw [abs_pow, sq]
        exact mul_le_mul_of_nonneg_right (abs_yv_le h h' k j) (abs_nonneg _)
    _ = M k * ∑ j, |yv T n h h' k j| := by rw [Finset.mul_sum]
    _ ≤ M k * ((Bh h + Bh h') / 2) :=
        mul_le_mul_of_nonneg_left (sum_abs_yv_le hT h h' hk) hM

theorem ps1_yv_self (hT : 0 ≤ T) (h : StepFn T) (k : ℕ) (ω : Fin (n k) → Bool) :
    ps 1 (yv T n h h k) = ps 2 (xin T n h k ω) := by
  unfold ps yv xin DExp.incr
  apply Finset.sum_congr rfl; intro j _
  rw [pow_one, mul_pow, mul_pow, sgn_sq']; ring

/-! ### The Gaussian facts on the Loeb space -/

theorem ae_He_eq (hT : 0 < T) (hn : IsUnlimited ((n : ℕ → ℕ) : Ult ℕ)) (m : ℕ) (h : StepFn T)
    (hh : h.nrm2 = 1) :
    (fun ω => Wiener.He m (h.I1 (bproc T n) ω)) =ᵐ[L n]
      fun ω => (m.factorial : ℝ) * stdPart (iF n (pS T n m h) ω) := by
  filter_upwards [ae_st_pS hT hn h m] with ω hω
  rw [hω.2, hh, heH_one_eq_hermite, Wiener.He]
  have : (m.factorial : ℝ) ≠ 0 := by positivity
  field_simp

theorem ae_Expo_eq (hT : 0 < T) (hn : IsUnlimited ((n : ℕ → ℕ) : Ult ℕ)) (h : StepFn T) :
    Expo (bproc T n) h =ᵐ[L n] fun ω => stdPart (iF n (pE T n h) ω) := by
  filter_upwards [ae_st_pE hT hn h] with ω hω
  exact hω.2.symm

theorem ae_I1_eq (hT : 0 < T) (hn : IsUnlimited ((n : ℕ → ℕ) : Ult ℕ)) (h : StepFn T) :
    h.I1 (bproc T n) =ᵐ[L n] fun ω => stdPart (iF n (pI T n h) ω) := by
  filter_upwards [ae_st_pI hT hn h] with ω hω
  exact hω.2.symm

theorem iE_pS_mul (m k : ℕ) (h h' : StepFn T) :
    iE n (fun j ω => pS T n m h j ω * pS T n k h' j ω) =
      Hyperreal.ofSeq (fun j => if m = k then es m (yv T n h h' j) else 0) := by
  unfold iE; congr 1; funext j
  exact E_es_mul_es m k _ _ _

theorem iE_pE_mul (m : ℕ) (h h' : StepFn T) :
    iE n (fun j ω => pE T n h j ω * pS T n m h' j ω) =
      Hyperreal.ofSeq (fun j => es m (yv T n h h' j)) := by
  unfold iE; congr 1; funext j
  exact E_prod_one_add_mul_es m _ _ _

theorem st_es_yv (hT : 0 < T) (hn : IsUnlimited ((n : ℕ → ℕ) : Ult ℕ)) (h h' : StepFn T) (m : ℕ) :
    stdPart (Hyperreal.ofSeq fun j => es m (yv T n h h' j)) =
      stdPart (Hyperreal.ofSeq fun j => ps 1 (yv T n h h' j)) ^ m / m.factorial :=
  ((ofSeq_st_iff_tendsto _ _).2 ((tendsto_es_yv hT hn h h').2 m)).2

theorem integral_I1_mul (hT : 0 < T) (hn : IsUnlimited ((n : ℕ → ℕ) : Ult ℕ)) (h h' : StepFn T) :
    ∫ ω, h.I1 (bproc T n) ω * h'.I1 (bproc T n) ω ∂(L n) =
      stdPart (Hyperreal.ofSeq fun j => ps 1 (yv T n h h' j)) := by
  have hae : (fun ω => h.I1 (bproc T n) ω * h'.I1 (bproc T n) ω) =ᵐ[L n]
      fun ω => stdPart (iF n (pI T n h) ω) * stdPart (iF n (pI T n h') ω) := by
    filter_upwards [ae_I1_eq hT hn h, ae_I1_eq hT hn h'] with ω h1 h2; rw [h1, h2]
  rw [integral_congr_ae hae, integral_st_mul (SInt_pI_sq hT hn h) (SInt_pI_sq hT hn h')]
  have e : iE n (fun j ω => pI T n h j ω * pI T n h' j ω) =
      iE n (fun j ω => pS T n 1 h j ω * pS T n 1 h' j ω) := by
    unfold iE; congr 1; funext j; congr 1; funext ω; simp only [pI_eq_pS]
  rw [e, iE_pS_mul]
  simp only [if_true]
  rw [st_es_yv hT hn]
  simp

theorem gaussFacts_loeb (hT : 0 < T) (hn : IsUnlimited ((n : ℕ → ℕ) : Ult ℕ)) :
    GaussFacts (L n) (T := T) (bproc T n) where
  memLp_He m h hh :=
    (((memLp_st (SInt_pS_sq hT hn h m)).const_mul (m.factorial : ℝ))).ae_eq (ae_He_eq hT hn m h hh).symm
  memLp_expo h := (memLp_st (SInt_pE_sq hT hn h)).ae_eq (ae_Expo_eq hT hn h).symm
  inner_He m k h h' hh hh' := by
    have hae : (fun ω => Wiener.He m (h.I1 (bproc T n) ω) * Wiener.He k (h'.I1 (bproc T n) ω))
        =ᵐ[L n] fun ω => (m.factorial : ℝ) * stdPart (iF n (pS T n m h) ω) *
          ((k.factorial : ℝ) * stdPart (iF n (pS T n k h') ω)) := by
      filter_upwards [ae_He_eq hT hn m h hh, ae_He_eq hT hn k h' hh'] with ω h1 h2; rw [h1, h2]
    rw [integral_congr_ae hae]
    have e : (fun ω => (m.factorial : ℝ) * stdPart (iF n (pS T n m h) ω) *
        ((k.factorial : ℝ) * stdPart (iF n (pS T n k h') ω))) =
        fun ω => ((m.factorial : ℝ) * k.factorial) *
          (stdPart (iF n (pS T n m h) ω) * stdPart (iF n (pS T n k h') ω)) := by
      funext ω; ring
    rw [e, integral_const_mul, integral_st_mul (SInt_pS_sq hT hn h m) (SInt_pS_sq hT hn h' k),
      iE_pS_mul, integral_I1_mul hT hn]
    by_cases hmk : m = k
    · subst hmk
      simp only [if_true]
      rw [st_es_yv hT hn]
      have : (m.factorial : ℝ) ≠ 0 := by positivity
      field_simp
    · simp only [hmk, if_false]
      rw [show (Hyperreal.ofSeq fun _ : ℕ => (0 : ℝ)) = 0 from rfl, stdPart_zero, mul_zero]
  inner_expo_He m h h' hh' := by
    have hae : (fun ω => Expo (bproc T n) h ω * Wiener.He m (h'.I1 (bproc T n) ω))
        =ᵐ[L n] fun ω => stdPart (iF n (pE T n h) ω) *
          ((m.factorial : ℝ) * stdPart (iF n (pS T n m h') ω)) := by
      filter_upwards [ae_Expo_eq hT hn h, ae_He_eq hT hn m h' hh'] with ω h1 h2; rw [h1, h2]
    rw [integral_congr_ae hae]
    have e : (fun ω => stdPart (iF n (pE T n h) ω) *
        ((m.factorial : ℝ) * stdPart (iF n (pS T n m h') ω))) =
        fun ω => (m.factorial : ℝ) *
          (stdPart (iF n (pE T n h) ω) * stdPart (iF n (pS T n m h') ω)) := by
      funext ω; ring
    rw [e, integral_const_mul, integral_st_mul (SInt_pE_sq hT hn h) (SInt_pS_sq hT hn h' m),
      iE_pE_mul, integral_I1_mul hT hn, st_es_yv hT hn]
    have : (m.factorial : ℝ) ≠ 0 := by positivity
    field_simp
  exists_unit := by
    refine ⟨⟨1, ![0, T], ![1 / √T], ?_, by simp, by simp⟩, ?_⟩
    · intro i j hij
      fin_cases i <;> fin_cases j <;> simp_all [hT.le]
    · simp [StepFn.nrm2, div_pow, Real.sq_sqrt hT.le, hT.ne']
  sq_I1 h hh := by
    have := integral_I1_mul hT hn h h
    simp_rw [← sq] at this
    rw [this]
    have h2 := tendsto_ps2_xin hT hn h (fun _ _ => true)
    have e : (fun k => ps 1 (yv T n h h k)) = fun k => ps 2 (xin T n h k (fun _ => true)) := by
      funext k; exact ps1_yv_self hT.le h k _
    rw [e, ((ofSeq_st_iff_tendsto _ _).2 h2).2, hh]
  sq_expo h := by
    have hae : (fun ω => Expo (bproc T n) h ω ^ 2) =ᵐ[L n]
        fun ω => stdPart (iF n (pE T n h) ω) ^ 2 := by
      filter_upwards [ae_Expo_eq hT hn h] with ω h1; rw [h1]
    rw [integral_congr_ae hae, integral_st_sq (SInt_pE_sq hT hn h)]
    have e : iE n (fun j ω => pE T n h j ω ^ 2) =
        Hyperreal.ofSeq (fun j => ∏ i, (1 + yv T n h h j i)) := by
      unfold iE; congr 1; funext j
      show QE.OpenSto.Walsh.E (fun ω => (∏ i, (1 + DExp.incr (sv T n h j) (cc T n j) ω i)) ^ 2) = _
      rw [E_prod_one_add_sq]
      apply Finset.prod_congr rfl; intro i _; simp only [yv]; ring
    rw [e]
    have h1 : Tendsto (fun k => ps 1 (yv T n h h k)) (hyperfilter ℕ : Filter ℕ) (𝓝 h.nrm2) := by
      have e : (fun k => ps 1 (yv T n h h k)) = fun k => ps 2 (xin T n h k (fun _ => true)) := by
        funext k; exact ps1_yv_self hT.le h k _
      rw [e]; exact tendsto_ps2_xin hT hn h _
    have hM0 : Tendsto (fun k => ((∑ i, |h.c i|) * cc T n k) * ((∑ i, |h.c i|) * cc T n k))
        (hyperfilter ℕ : Filter ℕ) (𝓝 0) := by
      simpa using (tendsto_M hn h).mul (tendsto_M hn h)
    have := tendsto_prod_one_add (yv T n h h) _ (fun k j => abs_yv_le h h k j) hM0 h1
      (tendsto_ps2_yv hT hn h h)
    rw [((ofSeq_st_iff_tendsto _ _).2 this).2]
    congr 1; ring

end Shadows

end QE.Chaos.Lift

/-! # Part H. The lifting theorem -/

namespace QE.Chaos.Lift

open Finset QE.Chaos.Wiener QE.Chaos.Loeb QE.Chaos.DExp QE.NSA MeasureTheory Filter Topology
  ArchimedeanClass
open QE.OpenSto.Walsh (E coeff chi sgn)

section WalshProj

variable {N : ℕ}

/-- The `m`-th Walsh level `Π_m F = ∑_{|S| = m} F̂(S) χ_S`. -/
def piW (m : ℕ) (F : (Fin N → Bool) → ℝ) (ω : Fin N → Bool) : ℝ :=
  ∑ S ∈ powersetCard m univ, coeff F S * chi S ω

theorem coeff_sub' (F G : (Fin N → Bool) → ℝ) (S : Finset (Fin N)) :
    coeff (fun ω => F ω - G ω) S = coeff F S - coeff G S := by
  unfold coeff QE.OpenSto.Walsh.E
  rw [← sub_div, ← Finset.sum_sub_distrib]; congr 1
  apply Finset.sum_congr rfl; intro ω _; ring

theorem coeff_sum' {ι : Type*} (s : Finset ι) (c : ι → ℝ) (F : ι → (Fin N → Bool) → ℝ)
    (S : Finset (Fin N)) :
    coeff (fun ω => ∑ i ∈ s, c i * F i ω) S = ∑ i ∈ s, c i * coeff (F i) S := by
  unfold coeff
  have : (fun ω => (∑ i ∈ s, c i * F i ω) * chi S ω) =
      fun ω => ∑ i ∈ s, c i * (F i ω * chi S ω) := by
    funext ω; rw [Finset.sum_mul]; apply Finset.sum_congr rfl; intro i _; ring
  rw [this, QE.OpenSto.Walsh.E_sum]
  apply Finset.sum_congr rfl; intro i _
  exact QE.OpenSto.Walsh.E_smul _ _

theorem piW_sub (m : ℕ) (F G : (Fin N → Bool) → ℝ) (ω : Fin N → Bool) :
    piW m (fun η => F η - G η) ω = piW m F ω - piW m G ω := by
  unfold piW; rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl; intro S _; rw [coeff_sub']; ring

theorem piW_sum {ι : Type*} (s : Finset ι) (c : ι → ℝ) (F : ι → (Fin N → Bool) → ℝ) (m : ℕ)
    (ω : Fin N → Bool) :
    piW m (fun η => ∑ i ∈ s, c i * F i η) ω = ∑ i ∈ s, c i * piW m (F i) ω := by
  unfold piW
  simp_rw [coeff_sum', Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro i _
  apply Finset.sum_congr rfl; intro S _; ring

theorem piW_eq_full (m : ℕ) (F : (Fin N → Bool) → ℝ) (ω : Fin N → Bool) :
    piW m F ω = ∑ S, (if S.card = m then coeff F S else 0) * chi S ω := by
  unfold piW
  rw [Finset.powersetCard_eq_filter, Finset.powerset_univ, Finset.sum_filter]
  apply Finset.sum_congr rfl; intro S _; split_ifs <;> simp

/-- **Parseval contraction**: `E (Π_m F)² ≤ E F²`. -/
theorem E_piW_sq_le (m : ℕ) (F : (Fin N → Bool) → ℝ) :
    E (fun ω => piW m F ω ^ 2) ≤ E (fun ω => F ω ^ 2) := by
  have h1 := QE.OpenSto.Walsh.parseval (piW m F) (piW m F)
  have h2 := QE.OpenSto.Walsh.parseval F F
  simp_rw [← sq] at h1 h2
  rw [h1, h2]
  have hc : ∀ S, coeff (piW m F) S = if S.card = m then coeff F S else 0 := by
    intro S
    have : piW m F = fun ω => ∑ S, (if S.card = m then coeff F S else 0) * chi S ω := by
      funext ω; exact piW_eq_full m F ω
    rw [this, QE.OpenSto.Walsh.coeff_of_expansion]
  refine Finset.sum_le_sum fun S _ => ?_
  rw [hc]; split_ifs <;> simp [sq_nonneg]

/-- The Walsh level of the discrete exponential is `e_m`. -/
theorem piW_pE {T : ℝ} {n : ℕ → ℕ} (m : ℕ) (h : StepFn T) (k : ℕ) (ω : Fin (n k) → Bool) :
    piW m (pE T n h k) ω = pS T n m h k ω :=
  walsh_part_prod_one_add m _ _ ω

end WalshProj

section SIntApprox

variable {n : ℕ → ℕ}

/-- **S-integrability by approximation**: if `F` is approximated in internal `L²`, within every
standard `ε`, by functions `G` with `G²` S-integrable, then `F²` is S-integrable. -/
theorem SInt_sq_of_approx {f : ∀ k, (Fin (n k) → Bool) → ℝ}
    (hf : IsFinite (iE n (fun k ω => f k ω ^ 2)))
    (happ : ∀ ε : ℝ, 0 < ε → ∃ g : ∀ k, (Fin (n k) → Bool) → ℝ,
      SInt n (fun k ω => g k ω ^ 2) ∧ iE n (fun k ω => (f k ω - g k ω) ^ 2) ≤ (ε : ℝ*)) :
    SInt n (fun k ω => f k ω ^ 2) := by
  have habs : ∀ k ω, |f k ω ^ 2| = f k ω ^ 2 := fun k ω => abs_of_nonneg (sq_nonneg _)
  refine ⟨by simpa [habs] using hf, fun K hK => ?_⟩
  simp only [habs]
  -- the auxiliary level `K' = √K`
  have hKpos : ∀ᶠ k in (hyperfilter ℕ : Filter ℕ), 1 < K k := hK 1
  set K' : ℕ → ℝ := fun k => √(K k)
  have hK' : ∀ r : ℝ, ∀ᶠ k in hyperfilter ℕ, r < K' k := by
    intro r
    filter_upwards [hK (max r 0 ^ 2 + 1)] with k hk
    have : max r 0 < √(K k) := by
      rw [Real.lt_sqrt (le_max_right _ _)]; linarith
    exact lt_of_le_of_lt (le_max_left _ _) this
  have hratio : IsInfinitesimal (Hyperreal.ofSeq fun k => K' k / K k) := by
    rw [QE.Chaos.DExp.isInfinitesimal_ofSeq_iff_tendsto]
    have hinv : Tendsto (fun k => 1 / K' k) (hyperfilter ℕ : Filter ℕ) (𝓝 0) := by
      rw [Metric.tendsto_nhds]; intro ε hε
      filter_upwards [hK' (1 / ε)] with k hk
      have hpos : 0 < K' k := lt_trans (by positivity) hk
      rw [Real.dist_eq, sub_zero, abs_of_pos (by positivity)]
      rw [div_lt_iff₀ hpos]; rw [div_lt_iff₀ hε] at hk; linarith
    refine hinv.congr' ?_
    filter_upwards [hKpos] with k hk
    simp only [K']
    have hs : 0 < √(K k) := Real.sqrt_pos.2 (by linarith)
    rw [div_eq_div_iff hs.ne' (by linarith), one_mul, Real.mul_self_sqrt (by linarith)]
  refine (QE.NSA.isInfinitesimal_of_abs_lt ?_)
  intro r hr
  obtain ⟨g, hg, hfg⟩ := happ (r / 4) (by positivity)
  set tail := iE n (fun k ω => if K k < f k ω ^ 2 then f k ω ^ 2 else 0)
  have hbound : tail ≤ 2 * iE n (fun k ω => (f k ω - g k ω) ^ 2) +
      2 * iE n (fun k ω => if K' k < |g k ω ^ 2| then |g k ω ^ 2| else 0) +
      2 * (Hyperreal.ofSeq (fun k => K' k / K k) * iE n (fun k ω => f k ω ^ 2)) := by
    rw [← iE_seq_mul]
    have e2 : ∀ x : ℝ*, 2 * x = ((2 : ℝ) : ℝ*) * x := fun x => by norm_num
    rw [e2, e2, e2, ← iE_const_mul, ← iE_const_mul, ← iE_const_mul, ← iE_add, ← iE_add]
    refine iE_mono_ev ?_
    filter_upwards [hKpos] with k hk ω
    have hK'0 : 0 ≤ K' k := Real.sqrt_nonneg _
    have hKK : K' k ≤ K k := by
      simp only [K']; rw [Real.sqrt_le_left (by linarith)]; nlinarith
    have hsq : f k ω ^ 2 ≤ 2 * (f k ω - g k ω) ^ 2 + 2 * g k ω ^ 2 := by
      nlinarith [sq_nonneg (f k ω - 2 * g k ω)]
    rw [abs_of_nonneg (sq_nonneg (g k ω))]
    by_cases hc : K k < f k ω ^ 2
    · rw [if_pos hc]
      have h3 : K' k ≤ K' k / K k * f k ω ^ 2 := by
        rw [div_mul_eq_mul_div, le_div_iff₀ (by linarith)]
        exact mul_le_mul_of_nonneg_left hc.le hK'0
      by_cases hg' : K' k < g k ω ^ 2
      · rw [if_pos hg']; nlinarith [mul_nonneg (div_nonneg hK'0 (by linarith : (0:ℝ) ≤ K k))
          (sq_nonneg (f k ω))]
      · rw [if_neg hg']; push Not at hg'; nlinarith
    · rw [if_neg hc]
      have : 0 ≤ (if K' k < g k ω ^ 2 then g k ω ^ 2 else 0) := by split_ifs <;> positivity
      nlinarith [sq_nonneg (f k ω - g k ω), mul_nonneg (div_nonneg hK'0 (by linarith : (0:ℝ) ≤ K k))
        (sq_nonneg (f k ω))]
  have htail0 : 0 ≤ tail := iE_nonneg fun k ω => by split_ifs <;> positivity
  have hI : IsInfinitesimal (2 * iE n (fun k ω => if K' k < |g k ω ^ 2| then |g k ω ^ 2| else 0) +
      2 * (Hyperreal.ofSeq (fun k => K' k / K k) * iE n (fun k ω => f k ω ^ 2))) := by
    have h2 : ∀ x : ℝ*, IsInfinitesimal x → IsInfinitesimal (2 * x) := fun x hx => by
      have := hx.nat_mul 2; simpa using this
    exact (h2 _ (hg.2 K' hK')).add (h2 _ (hratio.mul_finite hf))
  have hsmall := hI.abs_lt (r := r / 2) (by positivity)
  rw [abs_of_nonneg htail0]
  have : (2 : ℝ*) * iE n (fun k ω => (f k ω - g k ω) ^ 2) ≤ ((r / 2 : ℝ) : ℝ*) := by
    have : (2 : ℝ*) * ((r / 4 : ℝ) : ℝ*) = ((r / 2 : ℝ) : ℝ*) := by push_cast; ring
    rw [← this]; exact mul_le_mul_of_nonneg_left hfg (by norm_num)
  calc tail ≤ _ := hbound
    _ = 2 * iE n (fun k ω => (f k ω - g k ω) ^ 2) + (2 * iE n (fun k ω =>
          if K' k < |g k ω ^ 2| then |g k ω ^ 2| else 0) +
          2 * (Hyperreal.ofSeq (fun k => K' k / K k) * iE n (fun k ω => f k ω ^ 2))) := by ring
    _ < ((r / 2 : ℝ) : ℝ*) + ((r / 2 : ℝ) : ℝ*) := add_lt_add_of_le_of_lt this
        (lt_of_le_of_lt (le_abs_self _) hsmall)
    _ = (r : ℝ*) := by push_cast; ring

end SIntApprox

section Helpers

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

theorem toL2_sum {ι : Type*} (s : Finset ι) (a : ι → ℝ) (u : ι → Ω → ℝ)
    (hu : ∀ i ∈ s, MemLp (u i) 2 P) :
    toL2 P (fun ω => ∑ i ∈ s, a i * u i ω) = ∑ i ∈ s, a i • toL2 P (u i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    rw [toL2_of_memLp P (memLp_const 0)]; exact MemLp.toLp_zero _
  | insert j s hj ih =>
    have hs : ∀ i ∈ s, MemLp (u i) 2 P := fun i hi => hu i (Finset.mem_insert_of_mem hi)
    have hmem : MemLp (fun ω => ∑ i ∈ s, a i * u i ω) 2 P :=
      memLp_finset_sum s (f := fun i ω => a i * u i ω) fun i hi => (hs i hi).const_mul (a i)
    simp only [Finset.sum_insert hj]
    rw [← ih hs]
    have huj := hu j (Finset.mem_insert_self j s)
    have hj' := huj.const_mul (a j)
    have hadd : toL2 P (fun ω => a j * u j ω + ∑ i ∈ s, a i * u i ω) =
        toL2 P (fun ω => a j * u j ω) + toL2 P (fun ω => ∑ i ∈ s, a i * u i ω) := by
      rw [toL2_of_memLp P (f := fun ω => a j * u j ω + ∑ i ∈ s, a i * u i ω) (hj'.add hmem),
        toL2_of_memLp P hj', toL2_of_memLp P hmem]
      exact MemLp.toLp_add hj' hmem
    have hsm : toL2 P (fun ω => a j * u j ω) = a j • toL2 P (u j) := by
      rw [toL2_of_memLp P (f := fun ω => a j * u j ω) hj', toL2_of_memLp P huj]
      exact MemLp.toLp_const_smul (a j) huj
    rw [hadd, hsm]

theorem norm_toL2_sub_sq {u w : Ω → ℝ} (hu : MemLp u 2 P) (hw : MemLp w 2 P) :
    ‖toL2 P u - toL2 P w‖ ^ 2 = ∫ ω, (u ω - w ω) ^ 2 ∂P := by
  rw [← real_inner_self_eq_norm_sq]
  have e : toL2 P u - toL2 P w = toL2 P (fun ω => u ω - w ω) := by
    rw [toL2_of_memLp P hu, toL2_of_memLp P hw,
      toL2_of_memLp P (f := fun ω => u ω - w ω) (hu.sub hw)]
    exact (MemLp.toLp_sub hu hw).symm
  rw [e, inner_toL2 P (f := fun ω => u ω - w ω) (g := fun ω => u ω - w ω) (hu.sub hw)
    (hu.sub hw)]
  simp_rw [sq]

end Helpers

theorem le_of_stdPart_lt {x : ℝ*} {r : ℝ} (hx : IsFinite x) (h : stdPart x < r) : x ≤ (r : ℝ*) := by
  have := QE.Chaos.Loeb.coe_le_stdPart (r := r) hx
  by_contra hc
  push Not at hc
  exact absurd (this hc.le) (not_le.2 h)

theorem stdPart_le_stdPart {x y : ℝ*} (hx : IsFinite x) (hy : IsFinite y) (h : x ≤ y) :
    stdPart x ≤ stdPart y := by
  by_contra hc
  push Not at hc
  set r := (stdPart y + stdPart x) / 2
  have h1 : y ≤ (r : ℝ*) := le_of_stdPart_lt hy (by simp only [r]; linarith)
  have h2 : (r : ℝ*) < x := by
    by_contra h3
    push Not at h3
    have := QE.Chaos.Loeb.stdPart_le_coe hx h3
    simp only [r] at this; linarith
  exact absurd (h.trans h1) (not_le.2 h2)

variable {n : ℕ → ℕ}

theorem SInt_sq_sum {ι : Type*} (s : Finset ι) (f : ι → ∀ k, (Fin (n k) → Bool) → ℝ)
    (hf : ∀ i ∈ s, SInt n (fun k ω => f i k ω ^ 2)) :
    SInt n (fun k ω => (∑ i ∈ s, f i k ω) ^ 2) := by
  have e : (fun k ω => (∑ i ∈ s, f i k ω) ^ 2) =
      fun k ω => ∑ i ∈ s, ∑ j ∈ s, f i k ω * f j k ω := by
    funext k ω; rw [sq, Finset.sum_mul_sum]
  rw [e]
  have hsum : ∀ (t : Finset ι) (g : ι → ∀ k, (Fin (n k) → Bool) → ℝ),
      (∀ i ∈ t, SInt n (g i)) → SInt n (fun k ω => ∑ i ∈ t, g i k ω) := by
    intro t g hg
    classical
    induction t using Finset.induction_on with
    | empty =>
      have h0 : SInt n (fun _ _ => (0 : ℝ)) := SInt_of_sq_finite (by
        rw [show (fun (k : ℕ) (_ : Fin (n k) → Bool) => (0 : ℝ) ^ 2) = fun _ _ => 0 from by
          funext k ω; simp, iE_const]
        exact coe_isFinite 0)
      simpa using h0
    | insert a t ha ih =>
      simp only [Finset.sum_insert ha]
      exact (hg a (Finset.mem_insert_self a t)).add
        (ih fun i hi => hg i (Finset.mem_insert_of_mem hi))
  exact hsum s _ fun i hi => hsum s _ fun j hj => SInt_mul_of_sq (hf i hi) (hf j hj)

section Lifting

variable {T : ℝ} {n : ℕ → ℕ}

/-- The path `t ↦ b(t, ω)` of the Loeb Brownian motion on `[0, T]`. -/
def bpath (T : ℝ) (n : ℕ → ℕ) (ω : Ult (ℕ → Bool)) : Set.Icc (0 : ℝ) T → ℝ :=
  QE.Chaos.Dense.path (bproc T n) T ω

/-- The internal Walsh projection `Π_m F` of an internal functional `F = [f_k]`. -/
def piI (m : ℕ) (f : ∀ k, (Fin (n k) → Bool) → ℝ) : ∀ k, (Fin (n k) → Bool) → ℝ :=
  fun k => piW m (f k)

/-- The internal approximant `∑ c_h 𝓔_n(h)` of a finite combination of exponentials. -/
def Gc (c : StepFn T →₀ ℝ) : ∀ k, (Fin (n k) → Bool) → ℝ :=
  fun k ω => ∑ h ∈ c.support, c h * pE T n h k ω

theorem SInt_Gc_sq (hT : 0 < T) (hn : IsUnlimited ((n : ℕ → ℕ) : Ult ℕ)) (c : StepFn T →₀ ℝ) :
    SInt n (fun k ω => Gc (n := n) c k ω ^ 2) := by
  refine SInt_sq_sum _ _ fun h _ => ?_
  have := (SInt_pE_sq hT hn h).const_mul (c h ^ 2)
  refine this.mono fun k ω => ?_
  rw [abs_of_nonneg (sq_nonneg _)]; ring_nf; exact le_rfl

theorem piI_Gc (m : ℕ) (c : StepFn T →₀ ℝ) (k : ℕ) (ω : Fin (n k) → Bool) :
    piI m (Gc (n := n) c) k ω = ∑ h ∈ c.support, c h * pS T n m h k ω := by
  unfold piI Gc
  rw [piW_sum]
  simp_rw [piW_pE]

theorem SInt_piI_Gc_sq (hT : 0 < T) (hn : IsUnlimited ((n : ℕ → ℕ) : Ult ℕ)) (m : ℕ)
    (c : StepFn T →₀ ℝ) : SInt n (fun k ω => piI m (Gc (n := n) c) k ω ^ 2) := by
  simp_rw [piI_Gc]
  refine SInt_sq_sum _ _ fun h _ => ?_
  have := (SInt_pS_sq hT hn h m).const_mul (c h ^ 2)
  refine this.mono fun k ω => ?_
  rw [abs_of_nonneg (sq_nonneg _)]; ring_nf; exact le_rfl

theorem ae_st_Gc (hT : 0 < T) (hn : IsUnlimited ((n : ℕ → ℕ) : Ult ℕ)) (c : StepFn T →₀ ℝ) :
    ∀ᵐ ω ∂(L n), IsFinite (iF n (Gc c) ω) ∧
      stdPart (iF n (Gc c) ω) = ∑ h ∈ c.support, c h * Expo (bproc T n) h ω := by
  have hall : ∀ᵐ ω ∂(L n), ∀ h ∈ c.support, IsFinite (iF n (pE T n h) ω) ∧
      stdPart (iF n (pE T n h) ω) = Expo (bproc T n) h ω :=
    (Filter.eventually_all_finset _).2 fun h _ => ae_st_pE hT hn h
  filter_upwards [hall] with ω hω
  obtain ⟨u, rfl⟩ := exists_rep ω
  rw [iF_coe]
  refine (ofSeq_st_iff_tendsto _ _).2 ?_
  refine tendsto_finsetSum _ fun h hh => (Tendsto.const_mul _ ?_)
  have := hω h hh; rw [iF_coe] at this
  exact (ofSeq_st_iff_tendsto _ _).1 this

theorem ae_st_piI_Gc (hT : 0 < T) (hn : IsUnlimited ((n : ℕ → ℕ) : Ult ℕ)) (m : ℕ)
    (c : StepFn T →₀ ℝ) :
    ∀ᵐ ω ∂(L n), IsFinite (iF n (piI m (Gc c)) ω) ∧
      stdPart (iF n (piI m (Gc c)) ω) = ∑ h ∈ c.support, c h * Qm (bproc T n) m h ω := by
  have hall : ∀ᵐ ω ∂(L n), ∀ h ∈ c.support, IsFinite (iF n (pS T n m h) ω) ∧
      stdPart (iF n (pS T n m h) ω) = heH m (h.I1 (bproc T n) ω) h.nrm2 / m.factorial :=
    (Filter.eventually_all_finset _).2 fun h _ => ae_st_pS hT hn h m
  filter_upwards [hall] with ω hω
  obtain ⟨u, rfl⟩ := exists_rep ω
  have e : iF n (piI m (Gc c)) (u : Ult (ℕ → Bool)) =
      Hyperreal.ofSeq (fun k => ∑ h ∈ c.support, c h * pS T n m h k (fun i => u k i)) := by
    rw [iF_coe]; congr 1; funext k; exact piI_Gc m c k _
  rw [e]
  refine (ofSeq_st_iff_tendsto _ _).2 ?_
  refine tendsto_finsetSum _ fun h hh => (Tendsto.const_mul _ ?_)
  have := hω h hh; rw [iF_coe] at this
  rw [Qm_eq_heH]
  exact (ofSeq_st_iff_tendsto _ _).1 this

theorem span_eq_toL2 (hT : 0 < T) (hn : IsUnlimited ((n : ℕ → ℕ) : Ult ℕ)) (c : StepFn T →₀ ℝ) :
    (c.sum fun h a => a • toL2 (L n) (Expo (bproc T n) h)) =
      toL2 (L n) (fun ω => ∑ h ∈ c.support, c h * Expo (bproc T n) h ω) := by
  rw [toL2_sum _ _ _ fun h _ => (gaussFacts_loeb hT hn).memLp_expo h]; rfl

theorem Pi_span (hT : 0 < T) (hn : IsUnlimited ((n : ℕ → ℕ) : Ult ℕ)) (m : ℕ)
    (c : StepFn T →₀ ℝ) :
    Pi (L n) (T := T) (bproc T n) m (c.sum fun h a => a • toL2 (L n) (Expo (bproc T n) h)) =
      toL2 (L n) (fun ω => ∑ h ∈ c.support, c h * Qm (bproc T n) m h ω) := by
  have hG := gaussFacts_loeb hT hn
  rw [toL2_sum _ _ _ fun h _ => memLp_Qm hG m h]
  unfold Finsupp.sum
  rw [map_sum]
  apply Finset.sum_congr rfl; intro h _
  rw [map_smul, Pi_expo hG m h]

/-- **Lifting theorem** (`thm:stoch-chaos-lifting`): for an internal functional `F` of the
hyperfinite walk with `F²` S-integrable and `st F = Φ(b)` a.s., every Walsh level `Π_m F` has
S-integrable square and `st Π_m F = Π_m Φ(b)` a.s., where `Π_m` on the right is the orthogonal
projection onto the `m`-th Wiener chaos of the Loeb Brownian motion `b`. -/
theorem chaos_lifting (hT : 0 < T) (hn : IsUnlimited ((n : ℕ → ℕ) : Ult ℕ))
    (Φ : (Set.Icc (0 : ℝ) T → ℝ) → ℝ) (hΦ : Measurable Φ)
    (hΦ2 : MemLp (fun ω => Φ (bpath T n ω)) 2 (L n))
    (f : ∀ k, (Fin (n k) → Bool) → ℝ) (hF2 : SInt n (fun k ω => f k ω ^ 2))
    (hst : ∀ᵐ ω ∂(L n), stdPart (iF n f ω) = Φ (bpath T n ω)) (m : ℕ) :
    SInt n (fun k ω => piI m f k ω ^ 2) ∧
      (fun ω => stdPart (iF n (piI m f) ω)) =ᵐ[L n]
        (Pi (L n) (T := T) (bproc T n) m (toL2 (L n) (fun ω => Φ (bpath T n ω))) :
          Ult (ℕ → Bool) → ℝ) := by
  have hG := gaussFacts_loeb hT hn
  set v := toL2 (L n) (fun ω => Φ (bpath T n ω)) with hvdef
  -- `v` lies in the closed span of the exponentials
  have hvm : v ∈ lpMeas ℝ ℝ (QE.Chaos.Dense.pathSigma (bproc T n) T) 2 (L n) := by
    rw [mem_lpMeas_iff_aestronglyMeasurable]
    have : Measurable[QE.Chaos.Dense.pathSigma (bproc T n) T] (fun ω => Φ (bpath T n ω)) :=
      hΦ.comp (comap_measurable _)
    exact this.stronglyMeasurable.aestronglyMeasurable.congr (coeFn_toL2 _ hΦ2).symm
  have hv : v ∈ expoSpan (L n) (T := T) (bproc T n) :=
    mem_expoSpan hT.le (fun t => measurable_andersonB T n t) (fun ω => andersonB_zero T n ω)
      hG.memLp_expo v hvm
  have hFfin := hF2.ae_isFinite_of_sq
  -- the key estimates for an approximant `c`
  have hfG : ∀ c : StepFn T →₀ ℝ, SInt n (fun k ω => (f k ω - Gc c k ω) ^ 2) := by
    intro c
    refine ((hF2.add (SInt_Gc_sq hT hn c)).const_mul 2).mono fun k ω => ?_
    rw [abs_sq]
    nlinarith [sq_nonneg (f k ω + Gc c k ω)]
  have hK2 : ∀ c : StepFn T →₀ ℝ,
      stdPart (iE n (fun k ω => (f k ω - Gc c k ω) ^ 2)) =
        ‖v - (c.sum fun h a => a • toL2 (L n) (Expo (bproc T n) h))‖ ^ 2 := by
    intro c
    rw [span_eq_toL2 hT hn c, hvdef, norm_toL2_sub_sq hΦ2
      (memLp_finset_sum _ fun h _ => (hG.memLp_expo h).const_mul (c h))]
    rw [← integral_st_sq (hfG c)]
    refine integral_congr_ae ?_
    filter_upwards [hFfin, ae_st_Gc hT hn c, hst] with ω h1 h2 h3
    rw [iF_sub, stdPart_sub' h1 h2.1, h2.2, h3]
  have hK3 : ∀ c : StepFn T →₀ ℝ,
      iE n (fun k ω => (piI m f k ω - piI m (Gc c) k ω) ^ 2) ≤
        iE n (fun k ω => (f k ω - Gc c k ω) ^ 2) := by
    intro c
    unfold iE
    refine Hyperreal.ofSeq_le_ofSeq.2 (Eventually.of_forall fun k => ?_)
    dsimp only
    have e : (fun ω => (piI m f k ω - piI m (Gc c) k ω) ^ 2) =
        fun ω => piW m (fun η => f k η - Gc c k η) ω ^ 2 := by
      funext ω; simp only [piI]; rw [piW_sub]
    rw [e]; exact E_piW_sq_le m _
  have hfinE : ∀ c : StepFn T →₀ ℝ, IsFinite (iE n (fun k ω => (f k ω - Gc c k ω) ^ 2)) := by
    intro c
    have := (hfG c).1
    simpa only [abs_sq] using this
  -- approximation in the closure
  have hcl : ∀ ε : ℝ, 0 < ε → ∃ c : StepFn T →₀ ℝ,
      ‖v - (c.sum fun h a => a • toL2 (L n) (Expo (bproc T n) h))‖ < ε := by
    intro ε hε
    have hcl' : v ∈ closure (Submodule.span ℝ
        (Set.range (fun h : StepFn T => toL2 (L n) (Expo (bproc T n) h))) : Set (Lp ℝ 2 (L n))) := by
      have := hv; unfold expoSpan at this
      rwa [← SetLike.mem_coe, Submodule.topologicalClosure_coe] at this
    obtain ⟨p, hp, hvp⟩ := Metric.mem_closure_iff.1 hcl' ε hε
    obtain ⟨c, rfl⟩ := Finsupp.mem_span_range_iff_exists_finsupp.1 hp
    exact ⟨c, by rwa [dist_eq_norm] at hvp⟩
  -- S-integrability of `(Π_m F)²`
  have hS : SInt n (fun k ω => piI m f k ω ^ 2) := by
    refine SInt_sq_of_approx ?_ fun ε hε => ?_
    · refine QE.Chaos.Loeb.isFinite_of_nonneg_le' (iE_nonneg fun k ω => sq_nonneg _) ?_
        (by simpa only [abs_sq] using hF2.1)
      unfold iE
      exact Hyperreal.ofSeq_le_ofSeq.2 (Eventually.of_forall fun k => E_piW_sq_le m _)
    · obtain ⟨c, hc⟩ := hcl (√ε) (Real.sqrt_pos.2 hε)
      refine ⟨piI m (Gc c), SInt_piI_Gc_sq hT hn m c, (hK3 c).trans ?_⟩
      refine le_of_stdPart_lt (hfinE c) ?_
      rw [hK2 c]
      have h0 := norm_nonneg (v - (c.sum fun h a => a • toL2 (L n) (Expo (bproc T n) h)))
      calc _ < √ε ^ 2 := by gcongr
        _ = ε := Real.sq_sqrt hε.le
  refine ⟨hS, ?_⟩
  -- the abstract lifting step
  set x := toL2 (L n) (fun ω => stdPart (iF n (piI m f) ω))
  have hx2 : MemLp (fun ω => stdPart (iF n (piI m f) ω)) 2 (L n) := memLp_st hS
  have happrox : ∀ p ∈ Submodule.span ℝ
      (Set.range (fun h : StepFn T => toL2 (L n) (Expo (bproc T n) h))),
      ‖x - Pi (L n) (T := T) (bproc T n) m p‖ ≤ ‖v - p‖ := by
    intro p hp
    obtain ⟨c, rfl⟩ := Finsupp.mem_span_range_iff_exists_finsupp.1 hp
    rw [Pi_span hT hn m c]
    have hQ : MemLp (fun ω => ∑ h ∈ c.support, c h * Qm (bproc T n) m h ω) 2 (L n) :=
      memLp_finset_sum _ fun h _ => (memLp_Qm hG m h).const_mul (c h)
    have hsq : ‖x - toL2 (L n) (fun ω => ∑ h ∈ c.support, c h * Qm (bproc T n) m h ω)‖ ^ 2 ≤
        ‖v - (c.sum fun h a => a • toL2 (L n) (Expo (bproc T n) h))‖ ^ 2 := by
      rw [norm_toL2_sub_sq hx2 hQ, ← hK2 c]
      have hfinPi : IsFinite (iE n (fun k ω => (piI m f k ω - piI m (Gc c) k ω) ^ 2)) :=
        QE.Chaos.Loeb.isFinite_of_nonneg_le' (iE_nonneg fun k ω => sq_nonneg _) (hK3 c)
          (hfinE c)
      have hI := integral_sq_sub_le hS.ae_isFinite_of_sq
        (SInt_piI_Gc_sq hT hn m c).ae_isFinite_of_sq hfinPi
      calc ∫ ω, (stdPart (iF n (piI m f) ω) -
            ∑ h ∈ c.support, c h * Qm (bproc T n) m h ω) ^ 2 ∂(L n)
          = ∫ ω, (stdPart (iF n (piI m f) ω) - stdPart (iF n (piI m (Gc c)) ω)) ^ 2 ∂(L n) := by
            refine integral_congr_ae ?_
            filter_upwards [ae_st_piI_Gc hT hn m c] with ω hω
            rw [hω.2]
        _ ≤ stdPart (iE n (fun k ω => (piI m f k ω - piI m (Gc c) k ω) ^ 2)) := hI.2
        _ ≤ stdPart (iE n (fun k ω => (f k ω - Gc c k ω) ^ 2)) :=
            stdPart_le_stdPart hfinPi (hfinE c) (hK3 c)
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 hsq
  have hx : x = Pi (L n) (T := T) (bproc T n) m v := eq_Pi_of_approx m hv happrox
  have := coeFn_toL2 (L n) hx2
  rw [show toL2 (L n) (fun ω => stdPart (iF n (piI m f) ω)) =
    Pi (L n) (T := T) (bproc T n) m v from hx] at this
  exact this.symm

end Lifting

end QE.Chaos.Lift

/-! # Part I. Definitions for the shadow theorem -/

namespace QE.Chaos.Shadow

open Finset

section Counting

/-- The `m`-subsets containing a fixed set `A`. -/
theorem card_powersetCard_superset {α : Type*} [DecidableEq α] (s A : Finset α) (hA : A ⊆ s)
    {m : ℕ} (hm : A.card ≤ m) :
    ((powersetCard m s).filter (fun U => A ⊆ U)).card = (s.card - A.card).choose (m - A.card) := by
  have : (powersetCard m s).filter (fun U => A ⊆ U) =
        (powersetCard (m - A.card) (s \ A)).image (fun V => V ∪ A) := by
      ext U
      simp only [mem_filter, mem_powersetCard, mem_image]
      constructor
      · rintro ⟨⟨hU, hc⟩, hAU⟩
        refine ⟨U \ A, ⟨sdiff_subset_sdiff hU le_rfl, ?_⟩, sdiff_union_of_subset hAU⟩
        rw [card_sdiff_of_subset hAU, hc]
      · rintro ⟨V, ⟨hV, hc⟩, rfl⟩
        have hdisj : Disjoint V A := by
          rw [disjoint_left]; intro x hx hxA; exact (mem_sdiff.1 (hV hx)).2 hxA
        refine ⟨⟨union_subset (hV.trans sdiff_subset) hA, ?_⟩, subset_union_right⟩
        rw [card_union_of_disjoint hdisj, hc]; omega
  rw [this, card_image_of_injOn, card_powersetCard, card_sdiff_of_subset hA]
  intro V hV W hW h
  simp only [mem_coe, mem_powersetCard] at hV hW
  have hVd : Disjoint V A := by
    rw [disjoint_left]; intro x hx hxA; exact (mem_sdiff.1 (hV.1 hx)).2 hxA
  have hWd : Disjoint W A := by
    rw [disjoint_left]; intro x hx hxA; exact (mem_sdiff.1 (hW.1 hx)).2 hxA
  have := congrArg (· \ A) h
  simpa [union_sdiff_cancel_right hVd, union_sdiff_cancel_right hWd] using this

/-- `C(N, m) ≤ N^m / m!`. -/
theorem choose_le_pow_div' (N m : ℕ) : (N.choose m : ℝ) ≤ (N : ℝ) ^ m / m.factorial := by
  have := Nat.choose_le_pow_div (α := ℝ) m N
  exact_mod_cast this

end Counting

section Defs

open QE.Chaos.Calc
open QE.OpenSto.Walsh (E coeff chi sgn)

variable {p : ℕ}

/-- The coarse cell vectors `v_j = (1[j < k_l])_l`. -/
def vC (T : ℝ) (n : ℕ) (t : Fin p → ℝ) : Fin n → (Fin p → ℝ) := fun j => cellVec T n t j

/-- The cylinder functional `F_n = g(W(t_1), …, W(t_p))` on `n` coins, `τ = T/n`. -/
def Fn (T : ℝ) (n : ℕ) (t : Fin p → ℝ) (g : (Fin p → ℝ) → ℝ) : (Fin n → Bool) → ℝ :=
  fun ω => g (walkVec √(T / n) (vC T n t) ∅ ω)

/-- The same functional of the walk on `N` coins. -/
def FN (T : ℝ) (N : ℕ) (t : Fin p → ℝ) (g : (Fin p → ℝ) → ℝ) : (Fin N → Bool) → ℝ :=
  fun ω => g (fineWalk T N t ω)

/-- The normalised block sums `ζ_j = q^{-1/2} ∑_{r<q} ξ_{j,r}` of the fine coins. -/
def zeta (n q : ℕ) (ω : Fin (n * q) → Bool) (j : Fin n) : ℝ :=
  (∑ r : Fin q, (sgn (ω (finProdFinEquiv (j, r))) : ℝ)) / √q

/-- The `m`-th Walsh level of `F`, as a polynomial evaluated at variables `x`
(`x = ξ` gives `Π_m F`; `x = G`, normalised Gaussian increments, gives the Gaussian lift). -/
def liftI {n : ℕ} (m : ℕ) (F : (Fin n → Bool) → ℝ) (x : Fin n → ℝ) : ℝ :=
  ∑ S ∈ powersetCard m univ, coeff F S * ∏ j ∈ S, x j

/-- The kernel constant of the fine comparison. -/
def Ck' (p m : ℕ) (T : ℝ) (N : ℕ → ℝ) : ℝ := Cker p m T N + m / 6 * N (m + 2)

/-- The constant of the `L²` estimate (ii). -/
def Al2 (p m : ℕ) (T : ℝ) (N : ℕ → ℝ) : ℝ :=
  Ck' p m T N ^ 2 * T ^ m / m.factorial + 4 * ((m.choose 2 : ℝ) + m * p) * T ^ (m - 1) * N m ^ 2

end Defs

end QE.Chaos.Shadow

/-! # Part J. The internal L² core estimate -/

namespace QE.Chaos.Shadow

open Finset QE.Chaos.Calc QE.Chaos.Lift
open QE.OpenSto.Walsh (E coeff chi sgn)

section L2Core

variable {n q : ℕ}

/-- Positions of the fine coins of `U` in block `j`. -/
def j_A (U : Finset (Fin (n * q))) (j : Fin n) : Finset (Fin q) :=
  univ.filter (fun r => finProdFinEquiv (j, r) ∈ U)

theorem j_chi_unblock (U : Finset (Fin (n * q))) (ω : Fin n → Fin q → Bool) :
    (chi U (unblock n q ω) : ℝ) = ∏ j, (chi (j_A U j) (ω j) : ℝ) := by
  rw [QE.OpenSto.Walsh.chi_eq_prod_univ]
  rw [← Fintype.prod_equiv finProdFinEquiv (fun x => (if finProdFinEquiv x ∈ U then
    (sgn (unblock n q ω (finProdFinEquiv x)) : ℝ) else 1)) _ (fun _ => rfl)]
  rw [Fintype.prod_prod_type]
  apply Finset.prod_congr rfl; intro j _
  rw [QE.OpenSto.Walsh.chi_eq_prod_univ]
  apply Finset.prod_congr rfl; intro r _
  simp [j_A, unblock_apply]

theorem j_zeta_unblock (ω : Fin n → Fin q → Bool) (j : Fin n) :
    zeta n q (unblock n q ω) j = (∑ r, (sgn (ω j r) : ℝ)) / √q := by
  simp [zeta, unblock_apply]

theorem j_avg_chi {q : ℕ} (A : Finset (Fin q)) :
    avg (fun b : Fin q → Bool => (chi A b : ℝ)) = if A = ∅ then 1 else 0 := by
  rw [avg_eq_E]; exact QE.OpenSto.Walsh.E_chi A

theorem j_avg_sum_chi {q : ℕ} (A : Finset (Fin q)) :
    avg (fun b : Fin q → Bool => (∑ r, (sgn (b r) : ℝ)) / √q * chi A b) =
      (∑ r, if ({r} : Finset (Fin q)) = A then (1 : ℝ) else 0) / √q := by
  rw [avg_eq_E]
  have : (fun b : Fin q → Bool => (∑ r, (sgn (b r) : ℝ)) / √q * chi A b) =
      fun b => (1 / √q) * ∑ r, (chi {r} b : ℝ) * chi A b := by
    funext b
    have e1 : ∀ r, (chi {r} b : ℝ) = sgn (b r) := fun r => by simp [chi]
    simp_rw [e1]; rw [← Finset.sum_mul]; ring
  rw [this, QE.OpenSto.Walsh.E_smul, QE.OpenSto.Walsh.E_sum]
  simp_rw [QE.OpenSto.Walsh.E_chi_mul]
  ring

/-- The block factor of the coefficient of `∏_{j ∈ S} ζ_j` at `U`. -/
def j_beta (S : Finset (Fin n)) (U : Finset (Fin (n * q))) (j : Fin n) : ℝ :=
  if j ∈ S then (∑ r, if ({r} : Finset (Fin q)) = j_A U j then (1 : ℝ) else 0) / √q
  else if j_A U j = ∅ then 1 else 0

theorem j_coeff_prod_zeta (S : Finset (Fin n)) (U : Finset (Fin (n * q))) :
    coeff (fun ω => ∏ j ∈ S, zeta n q ω j) U = ∏ j, j_beta S U j := by
  unfold coeff
  rw [E_eq_avg_unblock]
  have : (fun ω : Fin n → Fin q → Bool =>
      (∏ j ∈ S, zeta n q (unblock n q ω) j) * (chi U (unblock n q ω) : ℝ)) =
      fun ω => ∏ j, (fun j (b : Fin q → Bool) => (if j ∈ S then (∑ r, (sgn (b r) : ℝ)) / √q
        else 1) * (chi (j_A U j) b : ℝ)) j (ω j) := by
    funext ω
    have h : ∏ j ∈ S, zeta n q (unblock n q ω) j =
        ∏ j, (if j ∈ S then zeta n q (unblock n q ω) j else 1) := by
      rw [Finset.prod_ite_mem, univ_inter]
    rw [j_chi_unblock, h, ← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl; intro j _
    simp only [j_zeta_unblock]
  rw [this]
  refine (avg_prod (ι := Fin n) (β := Fin q → Bool) (fun j (b : Fin q → Bool) =>
    (if j ∈ S then (∑ r, (sgn (b r) : ℝ)) / √q else 1) * (chi (j_A U j) b : ℝ))).trans ?_
  apply Finset.prod_congr rfl; intro j _
  unfold j_beta
  by_cases hj : j ∈ S
  · simp only [hj, if_true]; exact j_avg_sum_chi _
  · simp only [hj, if_false, one_mul]; exact j_avg_chi _

theorem j_fp_blk (i : Fin (n * q)) : finProdFinEquiv (blk i, bpos i) = i := by
  show finProdFinEquiv ((finProdFinEquiv.symm i).1, (finProdFinEquiv.symm i).2) = i
  rw [Prod.mk.eta]; exact Equiv.apply_symm_apply _ _

theorem j_sum_single {q : ℕ} (A : Finset (Fin q)) :
    (∑ r, if ({r} : Finset (Fin q)) = A then (1 : ℝ) else 0) = if A.card = 1 then 1 else 0 := by
  by_cases h : A.card = 1
  · obtain ⟨a, rfl⟩ := Finset.card_eq_one.1 h
    rw [if_pos h, Finset.sum_eq_single a (fun r _ hr => by
      rw [if_neg]; intro h'; exact hr (Finset.singleton_inj.1 h')) (by simp)]
    simp
  · rw [if_neg h]
    refine Finset.sum_eq_zero fun r _ => ?_
    rw [if_neg]; rintro rfl; exact h (Finset.card_singleton r)

theorem j_mem_A {U : Finset (Fin (n * q))} {j : Fin n} {r : Fin q} :
    r ∈ j_A U j ↔ finProdFinEquiv (j, r) ∈ U := by simp [j_A]

theorem j_mem_image_iff (U : Finset (Fin (n * q))) (j : Fin n) :
    j ∈ U.image blk ↔ (j_A U j).Nonempty := by
  constructor
  · rintro hj
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 hj
    exact ⟨bpos i, j_mem_A.2 (by rw [j_fp_blk]; exact hi)⟩
  · rintro ⟨r, hr⟩
    refine Finset.mem_image.2 ⟨_, j_mem_A.1 hr, ?_⟩
    simp [blk]

theorem j_card_A_le (U : Finset (Fin (n * q))) (hU : Set.InjOn blk (U : Set (Fin (n * q))))
    (j : Fin n) : (j_A U j).card ≤ 1 := by
  rw [Finset.card_le_one]
  intro r hr r' hr'
  have h := hU (j_mem_A.1 hr) (j_mem_A.1 hr') (by simp [blk])
  have := congrArg (fun i => (finProdFinEquiv.symm i).2) h
  simpa using this

theorem j_beta_zero_of_not_inj (U : Finset (Fin (n * q)))
    (hU : ¬ Set.InjOn blk (U : Set (Fin (n * q)))) (S : Finset (Fin n)) :
    ∏ j, j_beta S U j = 0 := by
  simp only [Set.InjOn, not_forall] at hU
  obtain ⟨i, hi, i', hi', hb, hne⟩ := hU
  have hA : 2 ≤ (j_A U (blk i)).card := by
    have h1 : bpos i ∈ j_A U (blk i) := j_mem_A.2 (by rw [j_fp_blk]; exact hi)
    have h2 : bpos i' ∈ j_A U (blk i) := j_mem_A.2 (by rw [hb, j_fp_blk]; exact hi')
    have h3 : bpos i ≠ bpos i' := by
      intro h; apply hne
      rw [← j_fp_blk i, ← j_fp_blk i', hb, h]
    exact Finset.one_lt_card.2 ⟨_, h1, _, h2, h3⟩
  refine Finset.prod_eq_zero (Finset.mem_univ (blk i)) ?_
  unfold j_beta
  rw [j_sum_single]
  have hne' : j_A U (blk i) ≠ ∅ := by
    intro h; rw [h] at hA; simp at hA
  split_ifs <;> first | rfl | omega | simp_all

theorem j_beta_inj (U : Finset (Fin (n * q))) (hU : Set.InjOn blk (U : Set (Fin (n * q))))
    (S : Finset (Fin n)) :
    ∏ j, j_beta S U j = if S = U.image blk then (1 / √q) ^ S.card else 0 := by
  have hb : ∀ j, j_beta S U j = if j ∈ S then (if j ∈ U.image blk then 1 / √q else 0)
      else (if j ∈ U.image blk then 0 else 1) := by
    intro j
    unfold j_beta
    rw [j_sum_single]
    have hle := j_card_A_le U hU j
    by_cases hne : (j_A U j).Nonempty
    · have hjB : j ∈ U.image blk := (j_mem_image_iff U j).2 hne
      have h1 : (j_A U j).card = 1 := le_antisymm hle (Finset.card_pos.2 hne)
      simp [hjB, h1, Finset.nonempty_iff_ne_empty.1 hne]
    · have hjB : j ∉ U.image blk := fun h => hne ((j_mem_image_iff U j).1 h)
      have h1 : (j_A U j).card ≠ 1 := by
        intro h; exact hne (Finset.card_pos.1 (by omega))
      simp [hjB, h1, Finset.not_nonempty_iff_eq_empty.1 hne]
  simp_rw [hb]
  split_ifs with hSB
  · subst hSB
    have : ∀ j, (if j ∈ U.image blk then (if j ∈ U.image blk then 1 / √q else 0)
        else (if j ∈ U.image blk then 0 else 1)) = if j ∈ U.image blk then 1 / √q else 1 := by
      intro j; split_ifs <;> rfl
    simp_rw [this]
    rw [Finset.prod_ite_mem, univ_inter, Finset.prod_const]
  · obtain ⟨j, hj⟩ : ∃ j, (j ∈ S ∧ j ∉ U.image blk) ∨ (j ∉ S ∧ j ∈ U.image blk) := by
      by_contra hc
      push Not at hc
      apply hSB; ext j
      constructor
      · intro h; exact (hc j).1 h
      · intro h; by_contra h'; exact (hc j).2 h' h
    refine Finset.prod_eq_zero (Finset.mem_univ j) ?_
    rcases hj with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> simp [h1, h2]

/-- **Fine Walsh coefficients of the Gaussian-lift approximant**. -/
theorem j_coeff_liftI (m : ℕ) (F : (Fin n → Bool) → ℝ) (U : Finset (Fin (n * q))) :
    coeff (fun ω => liftI m F (zeta n q ω)) U =
      if Set.InjOn blk (U : Set (Fin (n * q))) ∧ U.card = m then
        coeff F (U.image blk) / √q ^ m else 0 := by
  unfold liftI
  rw [coeff_sum' (powersetCard m univ) (fun S => coeff F S)
    (fun S ω => ∏ j ∈ S, zeta n q ω j) U]
  simp_rw [j_coeff_prod_zeta]
  by_cases hU : Set.InjOn blk (U : Set (Fin (n * q)))
  · simp_rw [j_beta_inj U hU]
    have hcard : (U.image blk).card = U.card := Finset.card_image_of_injOn hU
    simp only [mul_ite, mul_zero]
    rw [Finset.sum_ite_eq']
    by_cases hm : U.card = m
    · rw [if_pos (Finset.mem_powersetCard.2 ⟨Finset.subset_univ _, by rw [hcard, hm]⟩),
        if_pos ⟨hU, hm⟩, hcard, hm, one_div, inv_pow, div_eq_mul_inv]
    · rw [if_neg (fun h => hm (by rw [← hcard]; exact (Finset.mem_powersetCard.1 h).2)),
        if_neg (fun h => hm h.2)]
  · rw [if_neg (fun h => hU h.1)]
    refine Finset.sum_eq_zero fun S _ => ?_
    rw [j_beta_zero_of_not_inj U hU, mul_zero]

theorem j_coeff_piW (m : ℕ) {N' : ℕ} (F : (Fin N' → Bool) → ℝ) (U : Finset (Fin N')) :
    coeff (piW m F) U = if U.card = m then coeff F U else 0 := by
  have : piW m F = fun ω => ∑ S, (if S.card = m then coeff F S else 0) * chi S ω := by
    funext ω; exact piW_eq_full m F ω
  rw [this, QE.OpenSto.Walsh.coeff_of_expansion]

theorem j_abs_E_le {N' : ℕ} {f : (Fin N' → Bool) → ℝ} {C : ℝ} (h : ∀ ω, |f ω| ≤ C) :
    |E f| ≤ C := by
  rw [← avg_eq_E]; exact abs_avg_le_of_le h

variable {p : ℕ}

/-- Fine coin `i` is a boundary coin: its fine vector differs from the coarse vector of its
block. -/
def j_bd (T : ℝ) (t : Fin p → ℝ) (i : Fin (n * q)) : Prop :=
  cellVec T (n * q) t i ≠ cellVec T n t (blk i)

open Classical in
/-- **Per-set bound** on the difference of the fine Walsh coefficients. -/
theorem j_term_le {m : ℕ} (hn : 0 < n) (hq : 0 < q) {T : ℝ} (hT : 0 < T) (t : Fin p → ℝ)
    (ht0 : ∀ l, 0 ≤ t l) {g : (Fin p → ℝ) → ℝ} {N : ℕ → ℝ} (hg : DBnd g (m + 4) N)
    (U : Finset (Fin (n * q))) (hU : U.card = m) :
    (coeff (fun ω => liftI m (Fn T n t g) (zeta n q ω)) U -
        coeff (piW m (FN T (n * q) t g)) U) ^ 2 ≤
      (T / ((n * q : ℕ) : ℝ)) ^ m * (Ck' p m T N ^ 2 * (T / n) ^ 2 +
        4 * N m ^ 2 * (U.filter (j_bd T t)).card +
        N m ^ 2 * ((U ×ˢ U).filter (fun x => x.1 ≠ x.2 ∧ blk x.1 = blk x.2)).card) := by
  set c := √(T / n) with hc
  set c' := √(T / ((n * q : ℕ) : ℝ)) with hc'
  have hcpos : 0 < c := Real.sqrt_pos.2 (by positivity)
  have hc'pos : 0 < c' := Real.sqrt_pos.2 (by positivity)
  have hcc : c / √q = c' := by
    rw [hc, hc', ← Real.sqrt_div' _ (Nat.cast_nonneg q)]; congr 1; push_cast; field_simp
  have hc2 : c' ^ 2 = T / ((n * q : ℕ) : ℝ) := Real.sq_sqrt (by positivity)
  have hNm : 0 ≤ N m := hg.2.1 m (by omega)
  have hgm : DBnd g m N := hg.mono (by omega)
  set fv : Fin (n * q) → Fin p → ℝ := fun i => cellVec T (n * q) t i
  set cv : Fin n → Fin p → ℝ := fun j => cellVec T n t j
  -- the fine coefficient
  have hY : coeff (piW m (FN T (n * q) t g)) U =
      c' ^ m * E (fun ω => cds c' (U.toList.map fv) g (walkVec c' fv U ω)) := by
    rw [j_coeff_piW, if_pos hU]
    have := coeff_walk c' hc'pos.ne' fv g U.toList (Finset.nodup_toList U)
    rw [Finset.toList_toFinset, Finset.length_toList, hU] at this
    rw [← this]
    unfold FN; congr 1; funext ω; rw [fineWalk_eq_walkVec]
  have hE2 : |E (fun ω => cds c' (U.toList.map fv) g (walkVec c' fv U ω))| ≤ N m :=
    j_abs_E_le fun ω => abs_cds_le hgm (by simp [hU]) (by
      intro v hv; obtain ⟨i, -, rfl⟩ := List.mem_map.1 hv; exact norm_cellVec_le _ _ _ _) hc'pos _
  set E2 := E (fun ω => cds c' (U.toList.map fv) g (walkVec c' fv U ω))
  have hcnt1 : (0 : ℝ) ≤ (U.filter (j_bd T t)).card := Nat.cast_nonneg _
  have hcnt2 : (0 : ℝ) ≤ ((U ×ˢ U).filter (fun x => x.1 ≠ x.2 ∧ blk x.1 = blk x.2)).card :=
    Nat.cast_nonneg _
  have hpos : 0 ≤ (T / ((n * q : ℕ) : ℝ)) ^ m := by positivity
  have hc'm : (c' ^ m) ^ 2 = (T / ((n * q : ℕ) : ℝ)) ^ m := by rw [← pow_mul, mul_comm, pow_mul, hc2]
  by_cases hinj : Set.InjOn blk (U : Set (Fin (n * q)))
  · set l := U.toList.map blk
    have hl : l.Nodup := (Finset.nodup_toList U).map_on fun x hx y hy h =>
      hinj (Finset.mem_toList.1 hx) (Finset.mem_toList.1 hy) h
    have hlen : l.length = m := by simp [l, hU]
    have hlU : l.toFinset = U.image blk := by
      ext j; simp [l, List.mem_toFinset, List.mem_map, Finset.mem_image]
    have hX : coeff (fun ω => liftI m (Fn T n t g) (zeta n q ω)) U =
        c' ^ m * E (fun ω => cds c (l.map cv) g (walkVec c cv l.toFinset ω)) := by
      rw [j_coeff_liftI, if_pos ⟨hinj, hU⟩, ← hlU]
      have := coeff_walk c hcpos.ne' cv g l hl
      rw [hlen] at this
      have e : coeff (Fn T n t g) l.toFinset = coeff (fun ω => g (walkVec c cv ∅ ω)) l.toFinset :=
        rfl
      rw [e, this, ← hcc, div_pow]; ring
    have hE1 : |E (fun ω => cds c (l.map cv) g (walkVec c cv l.toFinset ω))| ≤ N m :=
      j_abs_E_le fun ω => abs_cds_le hgm (by simp [hlen]) (by
        intro v hv; obtain ⟨i, -, rfl⟩ := List.mem_map.1 hv; exact norm_cellVec_le _ _ _ _) hcpos _
    set E1 := E (fun ω => cds c (l.map cv) g (walkVec c cv l.toFinset ω))
    rw [hX, hY, ← mul_sub, mul_pow, hc'm]
    refine mul_le_mul_of_nonneg_left ?_ hpos
    by_cases hgood : ∀ i ∈ U, ¬ j_bd T t i
    · have hUv : U.toList.map fv = l.map cv := by
        simp only [l, List.map_map]
        refine List.map_congr_left fun i hi => ?_
        have := hgood i (Finset.mem_toList.1 hi)
        simp only [j_bd, not_not] at this
        simp [fv, cv, this]
      have hk := kernel_coin_bound_fine hn hq hT t ht0 hg l hl hlen U.toList rfl hUv
      rw [Finset.toList_toFinset] at hk
      have hk' : |E1 - E2| ≤ Ck' p m T N * (T / n) := hk
      have h0 : 0 ≤ Ck' p m T N * (T / n) := (abs_nonneg _).trans hk'
      have : (E1 - E2) ^ 2 ≤ Ck' p m T N ^ 2 * (T / n) ^ 2 := by
        rw [← mul_pow]; exact sq_le_sq' (abs_le.1 hk').1 (abs_le.1 hk').2
      nlinarith [sq_nonneg (N m)]
    · push Not at hgood
      obtain ⟨i, hi, hbi⟩ := hgood
      have h1 : (1 : ℝ) ≤ (U.filter (j_bd T t)).card := by
        have := Finset.card_pos.2
          (⟨i, Finset.mem_filter.2 ⟨hi, hbi⟩⟩ : (U.filter (j_bd T t)).Nonempty)
        exact_mod_cast this
      have hd : |E1 - E2| ≤ 2 * N m := (abs_sub _ _).trans (by linarith)
      have : (E1 - E2) ^ 2 ≤ 4 * N m ^ 2 := by
        have := sq_le_sq' (abs_le.1 hd).1 (abs_le.1 hd).2; nlinarith
      nlinarith [mul_le_mul_of_nonneg_left h1 (by positivity : (0:ℝ) ≤ 4 * N m ^ 2),
        sq_nonneg (Ck' p m T N * (T / n)), mul_nonneg (sq_nonneg (N m)) hcnt2]
  · rw [j_coeff_liftI, if_neg (fun h => hinj h.1), hY, zero_sub, neg_sq, mul_pow, hc'm]
    refine mul_le_mul_of_nonneg_left ?_ hpos
    simp only [Set.InjOn, not_forall] at hinj
    obtain ⟨i, hi, i', hi', hb, hne⟩ := hinj
    have h1 : (1 : ℝ) ≤ ((U ×ˢ U).filter (fun x => x.1 ≠ x.2 ∧ blk x.1 = blk x.2)).card := by
      have := Finset.card_pos.2 (⟨(i, i'), Finset.mem_filter.2
        ⟨Finset.mem_product.2 ⟨hi, hi'⟩, hne, hb⟩⟩ :
          ((U ×ˢ U).filter (fun x => x.1 ≠ x.2 ∧ blk x.1 = blk x.2)).Nonempty)
      exact_mod_cast this
    have : E2 ^ 2 ≤ N m ^ 2 := by
      have := sq_le_sq' (abs_le.1 hE2).1 (abs_le.1 hE2).2; nlinarith
    nlinarith [mul_le_mul_of_nonneg_left h1 (sq_nonneg (N m)),
      sq_nonneg (Ck' p m T N * (T / n)), mul_nonneg (sq_nonneg (N m)) hcnt1]

/-! ### Counting -/

theorem j_card_block_le (j : Fin n) :
    (univ.filter (fun i : Fin (n * q) => blk i = j)).card ≤ q := by
  calc (univ.filter (fun i : Fin (n * q) => blk i = j)).card ≤ (univ : Finset (Fin q)).card := by
        refine Finset.card_le_card_of_injOn bpos (fun _ _ => Finset.mem_univ _) ?_
        intro i hi i' hi' h
        simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_univ, true_and] at hi hi'
        rw [← j_fp_blk i, ← j_fp_blk i', hi, hi', h]
    _ = q := by simp

theorem j_card_block_nat_le (k : ℕ) :
    (univ.filter (fun i : Fin (n * q) => (blk i : ℕ) = k)).card ≤ q := by
  by_cases hk : k < n
  · have : univ.filter (fun i : Fin (n * q) => (blk i : ℕ) = k) =
        univ.filter (fun i : Fin (n * q) => blk i = ⟨k, hk⟩) := by
      ext i; simp [Fin.ext_iff]
    rw [this]; exact j_card_block_le _
  · have : univ.filter (fun i : Fin (n * q) => (blk i : ℕ) = k) = ∅ := by
      ext i; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty,
        iff_false]
      intro h; exact hk (h ▸ (blk i).2)
    rw [this]; simp

theorem j_bd_block (hn : 0 < n) (hq : 0 < q) {T : ℝ} (hT : 0 < T) {t : Fin p → ℝ}
    (ht0 : ∀ l, 0 ≤ t l) {i : Fin (n * q)} (hi : j_bd T t i) :
    ∃ l, (blk i : ℕ) = QE.NSA.walkIdx T n (t l) := by
  by_contra hc
  push Not at hc
  apply hi
  funext l
  obtain ⟨h1, h2⟩ := idx_bounds hT hn hq (ht0 l)
  have hv := val_blk i
  have hb := (bpos i).2
  unfold cellVec
  have hne := hc l
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have : (i : ℕ) < QE.NSA.walkIdx T (n * q) (t l) := by
      have : q * ((blk i : ℕ) + 1) ≤ q * QE.NSA.walkIdx T n (t l) := Nat.mul_le_mul_left _ hlt
      nlinarith
    rw [if_pos this, if_pos hlt]
  · have : ¬ (i : ℕ) < QE.NSA.walkIdx T (n * q) (t l) := by
      have : q * (QE.NSA.walkIdx T n (t l) + 1) ≤ q * (blk i : ℕ) := Nat.mul_le_mul_left _ hgt
      push Not; nlinarith
    rw [if_neg this, if_neg (by omega)]

open Classical in
theorem j_card_bd_le (hn : 0 < n) (hq : 0 < q) {T : ℝ} (hT : 0 < T) {t : Fin p → ℝ}
    (ht0 : ∀ l, 0 ≤ t l) : (univ.filter (j_bd (n := n) (q := q) T t)).card ≤ p * q := by
  have hsub : univ.filter (j_bd (n := n) (q := q) T t) ⊆ (univ : Finset (Fin p)).biUnion
      (fun l => univ.filter (fun i : Fin (n * q) => (blk i : ℕ) = QE.NSA.walkIdx T n (t l))) := by
    intro i hi
    obtain ⟨l, hl⟩ := j_bd_block hn hq hT ht0 (Finset.mem_filter.1 hi).2
    exact Finset.mem_biUnion.2 ⟨l, Finset.mem_univ _, Finset.mem_filter.2 ⟨Finset.mem_univ _, hl⟩⟩
  calc _ ≤ _ := Finset.card_le_card hsub
    _ ≤ ∑ l : Fin p, (univ.filter (fun i : Fin (n * q) =>
          (blk i : ℕ) = QE.NSA.walkIdx T n (t l))).card := Finset.card_biUnion_le
    _ ≤ ∑ _l : Fin p, q := Finset.sum_le_sum fun l _ => j_card_block_nat_le _
    _ = p * q := by simp

theorem j_card_pairs_le :
    (univ.filter (fun x : Fin (n * q) × Fin (n * q) => x.1 ≠ x.2 ∧ blk x.1 = blk x.2)).card ≤
      n * q * q := by
  have hsub : univ.filter (fun x : Fin (n * q) × Fin (n * q) => x.1 ≠ x.2 ∧ blk x.1 = blk x.2) ⊆
      (univ : Finset (Fin (n * q))).biUnion (fun i =>
        (univ.filter (fun i' : Fin (n * q) => blk i' = blk i)).map
          ⟨fun i' => (i, i'), fun a b h => by simpa using h⟩) := by
    intro x hx
    obtain ⟨-, hb⟩ := Finset.mem_filter.1 hx
    refine Finset.mem_biUnion.2 ⟨x.1, Finset.mem_univ _, Finset.mem_map.2 ⟨x.2, ?_, rfl⟩⟩
    exact Finset.mem_filter.2 ⟨Finset.mem_univ _, hb.2.symm⟩
  calc _ ≤ _ := Finset.card_le_card hsub
    _ ≤ ∑ i : Fin (n * q), ((univ.filter (fun i' : Fin (n * q) => blk i' = blk i)).map
          ⟨fun i' => (i, i'), fun a b h => by simpa using h⟩).card := Finset.card_biUnion_le
    _ ≤ ∑ _i : Fin (n * q), q := Finset.sum_le_sum fun i _ => by
          rw [Finset.card_map]; exact j_card_block_le _
    _ = n * q * q := by simp

open Classical in
theorem j_sum_cnt1 {m : ℕ} (hm : 1 ≤ m) (T : ℝ) (t : Fin p → ℝ) :
    ∑ U ∈ powersetCard m (univ : Finset (Fin (n * q))), (U.filter (j_bd T t)).card =
      (univ.filter (j_bd (n := n) (q := q) T t)).card * (n * q - 1).choose (m - 1) := by
  have h := Finset.sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow
    (s := powersetCard m (univ : Finset (Fin (n * q))))
    (t := univ.filter (j_bd (n := n) (q := q) T t)) (r := fun U i => i ∈ U)
  have e1 : ∀ U : Finset (Fin (n * q)), (univ.filter (j_bd (n := n) (q := q) T t)).bipartiteAbove (fun U i => i ∈ U) U =
      U.filter (j_bd T t) := by
    intro U; ext i; simp [Finset.bipartiteAbove, and_comm]
  have e2 : ∀ i, (powersetCard m (univ : Finset (Fin (n * q)))).bipartiteBelow
      (fun U i => i ∈ U) i = (powersetCard m univ).filter (fun U => {i} ⊆ U) := by
    intro i; ext U; simp [Finset.bipartiteBelow]
  simp_rw [e1, e2] at h
  rw [h]
  rw [Finset.sum_congr rfl (fun i _ => card_powersetCard_superset univ {i}
    (Finset.subset_univ _) (by simpa using hm))]
  simp [mul_comm]

open Classical in
theorem j_sum_cnt2 (m : ℕ) :
    ∑ U ∈ powersetCard m (univ : Finset (Fin (n * q))),
        ((U ×ˢ U).filter (fun x => x.1 ≠ x.2 ∧ blk x.1 = blk x.2)).card ≤
      (univ.filter (fun x : Fin (n * q) × Fin (n * q) => x.1 ≠ x.2 ∧ blk x.1 = blk x.2)).card *
        (if 2 ≤ m then (n * q - 2).choose (m - 2) else 0) := by
  have h := Finset.sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow
    (s := powersetCard m (univ : Finset (Fin (n * q))))
    (t := univ.filter (fun x : Fin (n * q) × Fin (n * q) => x.1 ≠ x.2 ∧ blk x.1 = blk x.2))
    (r := fun U x => x.1 ∈ U ∧ x.2 ∈ U)
  have e1 : ∀ U : Finset (Fin (n * q)), (univ.filter (fun x : Fin (n * q) × Fin (n * q) => x.1 ≠ x.2 ∧
      blk x.1 = blk x.2)).bipartiteAbove (fun U x => x.1 ∈ U ∧ x.2 ∈ U) U =
      (U ×ˢ U).filter (fun x => x.1 ≠ x.2 ∧ blk x.1 = blk x.2) := by
    intro U; ext x; simp [Finset.bipartiteAbove, Finset.mem_product]; tauto
  simp_rw [e1] at h
  rw [h]
  refine (Finset.sum_le_sum (g := fun _ => if 2 ≤ m then (n * q - 2).choose (m - 2) else 0)
    fun x hx => ?_).trans (by rw [Finset.sum_const, smul_eq_mul])
  obtain ⟨-, hne, -⟩ := Finset.mem_filter.1 hx
  have e2 : (powersetCard m (univ : Finset (Fin (n * q)))).bipartiteBelow
      (fun U x => x.1 ∈ U ∧ x.2 ∈ U) x = (powersetCard m univ).filter (fun U => {x.1, x.2} ⊆ U) := by
    ext U; simp [Finset.bipartiteBelow, Finset.insert_subset_iff]
  rw [e2]
  have hc : ({x.1, x.2} : Finset (Fin (n * q))).card = 2 := Finset.card_pair hne
  split_ifs with hm
  · rw [card_powersetCard_superset univ _ (Finset.subset_univ _) (by rw [hc]; exact hm), hc]
    simp
  · rw [Nat.le_zero, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro U hU hsub
    have := Finset.card_le_card hsub
    rw [hc, (Finset.mem_powersetCard.1 hU).2] at this
    omega

/-! ### Assembly -/

theorem j_E_sq_eq {m : ℕ} {T : ℝ} (t : Fin p → ℝ) (g : (Fin p → ℝ) → ℝ) :
    E (fun ω : Fin (n * q) → Bool =>
        (liftI m (Fn T n t g) (zeta n q ω) - piW m (FN T (n * q) t g) ω) ^ 2) =
      ∑ U ∈ powersetCard m (univ : Finset (Fin (n * q))),
        (coeff (fun ω => liftI m (Fn T n t g) (zeta n q ω)) U -
          coeff (piW m (FN T (n * q) t g)) U) ^ 2 := by
  set D := fun ω : Fin (n * q) → Bool =>
    liftI m (Fn T n t g) (zeta n q ω) - piW m (FN T (n * q) t g) ω
  have hp := QE.OpenSto.Walsh.parseval D D
  simp_rw [← sq] at hp
  rw [show (fun ω : Fin (n * q) → Bool =>
      (liftI m (Fn T n t g) (zeta n q ω) - piW m (FN T (n * q) t g) ω) ^ 2) =
      fun ω => D ω ^ 2 from rfl, hp]
  simp only [D]
  simp_rw [coeff_sub']
  rw [Finset.powersetCard_eq_filter, Finset.powerset_univ, Finset.sum_filter]
  apply Finset.sum_congr rfl; intro U _
  split_ifs with hU
  · rfl
  · rw [j_coeff_liftI, j_coeff_piW, if_neg (fun h => hU h.2), if_neg hU]; simp

open Classical in
/-- The `L²` core estimate with a given bound `p' q` on the number of boundary coins. -/
theorem l2_core_gen {m : ℕ} (hm : 1 ≤ m) (hn : 0 < n) (hq : 0 < q) {T : ℝ} (hT : 0 < T)
    (hτ : T / n ≤ 1) (t : Fin p → ℝ) (ht0 : ∀ l, 0 ≤ t l) {g : (Fin p → ℝ) → ℝ}
    {N : ℕ → ℝ} (hg : DBnd g (m + 4) N) (p' : ℕ)
    (hbd : (univ.filter (j_bd (n := n) (q := q) T t)).card ≤ p' * q) :
    E (fun ω : Fin (n * q) → Bool =>
        (liftI m (Fn T n t g) (zeta n q ω) - piW m (FN T (n * q) t g) ω) ^ 2) ≤
      (Ck' p m T N ^ 2 * T ^ m / m.factorial +
        4 * ((m.choose 2 : ℝ) + m * p') * T ^ (m - 1) * N m ^ 2) * (T / n) := by
  classical
  rw [j_E_sq_eq]
  set x : ℝ := ((n * q : ℕ) : ℝ) with hx
  have hxpos : 0 < x := by rw [hx]; exact_mod_cast Nat.mul_pos hn hq
  have hxnq : x = n * q := by rw [hx]; push_cast; ring
  set a := T / x with ha
  have hapos : 0 < a := div_pos hT hxpos
  set τ := T / n with hτdef
  have hτ0 : 0 < τ := by positivity
  have hNm : 0 ≤ N m := hg.2.1 m (by omega)
  -- sum of the per-set bounds
  have hsum : ∑ U ∈ powersetCard m (univ : Finset (Fin (n * q))),
      (coeff (fun ω => liftI m (Fn T n t g) (zeta n q ω)) U -
        coeff (piW m (FN T (n * q) t g)) U) ^ 2 ≤
      a ^ m * (((n * q).choose m : ℝ) * (Ck' p m T N ^ 2 * τ ^ 2) +
        4 * N m ^ 2 * ((p' * q : ℕ) * ((n * q - 1).choose (m - 1) : ℕ) : ℝ) +
        N m ^ 2 * ((n * q * q : ℕ) * ((if 2 ≤ m then (n * q - 2).choose (m - 2) else 0 : ℕ)) : ℝ)) := by
    refine (Finset.sum_le_sum fun U hU => j_term_le hn hq hT t ht0 hg U
      (Finset.mem_powersetCard.1 hU).2).trans ?_
    rw [← Finset.mul_sum]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
      Finset.sum_const, Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul]
    have h1 : (∑ U ∈ powersetCard m (univ : Finset (Fin (n * q))),
        ((U.filter (j_bd T t)).card : ℝ)) ≤ ((p' * q : ℕ) * ((n * q - 1).choose (m - 1) : ℕ) : ℝ) := by
      rw [← Nat.cast_sum, j_sum_cnt1 hm T t]
      exact_mod_cast Nat.mul_le_mul_right _ hbd
    have h2 : (∑ U ∈ powersetCard m (univ : Finset (Fin (n * q))),
        (((U ×ˢ U).filter (fun x => x.1 ≠ x.2 ∧ blk x.1 = blk x.2)).card : ℝ)) ≤
        ((n * q * q : ℕ) * ((if 2 ≤ m then (n * q - 2).choose (m - 2) else 0 : ℕ)) : ℝ) := by
      rw [← Nat.cast_sum]
      exact_mod_cast (j_sum_cnt2 m).trans (Nat.mul_le_mul_right _ j_card_pairs_le)
    rw [← Finset.mul_sum]
    have := mul_le_mul_of_nonneg_left h1 (by positivity : (0:ℝ) ≤ 4 * N m ^ 2)
    have := mul_le_mul_of_nonneg_left h2 (sq_nonneg (N m))
    nlinarith
  refine hsum.trans ?_
  -- the arithmetic
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
  have hamx : a ^ (k + 1) * x ^ (k + 1) = T ^ (k + 1) := by
    rw [ha, div_pow, div_mul_cancel₀ _ (pow_ne_zero _ hxpos.ne')]
  have hTn : T ^ (k + 1) / n = T ^ k * τ := by rw [hτdef, pow_succ]; ring
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have hqpos : (0 : ℝ) < q := by exact_mod_cast hq
  -- term 1
  have t1 : a ^ (k + 1) * (((n * q).choose (k + 1) : ℝ) * (Ck' p (k + 1) T N ^ 2 * τ ^ 2)) ≤
      Ck' p (k + 1) T N ^ 2 * T ^ (k + 1) / (k + 1).factorial * τ := by
    have hc := choose_le_pow_div' (n * q) (k + 1)
    have : a ^ (k + 1) * ((n * q).choose (k + 1) : ℝ) ≤ T ^ (k + 1) / (k + 1).factorial := by
      calc _ ≤ a ^ (k + 1) * (((n * q : ℕ) : ℝ) ^ (k + 1) / (k + 1).factorial) :=
            mul_le_mul_of_nonneg_left hc (by positivity)
        _ = T ^ (k + 1) / (k + 1).factorial := by rw [← hx, mul_div_assoc', hamx]
    have hτ2 : τ ^ 2 ≤ τ := by nlinarith
    calc a ^ (k + 1) * (((n * q).choose (k + 1) : ℝ) * (Ck' p (k + 1) T N ^ 2 * τ ^ 2))
        = (a ^ (k + 1) * ((n * q).choose (k + 1) : ℝ)) * Ck' p (k + 1) T N ^ 2 * τ ^ 2 := by ring
      _ ≤ (T ^ (k + 1) / (k + 1).factorial) * Ck' p (k + 1) T N ^ 2 * τ := by
          gcongr
      _ = _ := by ring
  -- term 2
  have t2 : a ^ (k + 1) * (4 * N (k + 1) ^ 2 * ((p' * q : ℕ) * ((n * q - 1).choose k : ℕ) : ℝ)) ≤
      4 * ((k + 1 : ℕ) * p' : ℝ) * T ^ k * N (k + 1) ^ 2 * τ := by
    have hc := choose_le_pow_div' (n * q - 1) k
    have hle : (((n * q - 1 : ℕ)) : ℝ) ^ k ≤ x ^ k := by
      gcongr; rw [hx]; exact_mod_cast Nat.sub_le _ _
    have hfac : (1 : ℝ) ≤ k.factorial := by exact_mod_cast Nat.one_le_iff_ne_zero.2 k.factorial_ne_zero
    have key : a ^ (k + 1) * (q * x ^ k) = T ^ k * τ := by
      rw [← hTn, ← hamx, pow_succ x k, hxnq]; field_simp
    have hcb : ((n * q - 1).choose k : ℝ) ≤ x ^ k :=
      hc.trans ((div_le_self (by positivity) hfac).trans hle)
    have hk1 : (p' : ℝ) ≤ ((k + 1 : ℕ) * p' : ℝ) := by
      have : (1 : ℝ) ≤ ((k + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_pos k
      nlinarith [Nat.cast_nonneg (α := ℝ) p']
    push_cast
    calc a ^ (k + 1) * (4 * N (k + 1) ^ 2 * (p' * q * ((n * q - 1).choose k : ℝ)))
        ≤ a ^ (k + 1) * (4 * N (k + 1) ^ 2 * (p' * q * x ^ k)) := by gcongr
      _ = 4 * p' * N (k + 1) ^ 2 * (a ^ (k + 1) * (q * x ^ k)) := by ring
      _ = 4 * p' * N (k + 1) ^ 2 * (T ^ k * τ) := by rw [key]
      _ ≤ 4 * ((k + 1 : ℝ) * p') * N (k + 1) ^ 2 * (T ^ k * τ) := by
          push_cast at hk1; gcongr
      _ = _ := by ring
  -- term 3
  have t3 : a ^ (k + 1) * (N (k + 1) ^ 2 * ((n * q * q : ℕ) *
      ((if 2 ≤ k + 1 then (n * q - 2).choose (k + 1 - 2) else 0 : ℕ)) : ℝ)) ≤
      4 * ((k + 1).choose 2 : ℝ) * T ^ k * N (k + 1) ^ 2 * τ := by
    split_ifs with h2
    · obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
      have hc := choose_le_pow_div' (n * q - 2) j
      have hle : (((n * q - 2 : ℕ)) : ℝ) ^ j ≤ x ^ j := by
        gcongr; rw [hx]; exact_mod_cast Nat.sub_le _ _
      have hfac : (1 : ℝ) ≤ j.factorial := by exact_mod_cast Nat.one_le_iff_ne_zero.2 j.factorial_ne_zero
      have hcb : ((n * q - 2).choose j : ℝ) ≤ x ^ j :=
        hc.trans ((div_le_self (by positivity) hfac).trans hle)
      have key : a ^ (j + 2) * ((n * q * q : ℕ) * x ^ j) = T ^ (j + 1) * τ := by
        have hamx' : a ^ (j + 2) * x ^ (j + 2) = T ^ (j + 2) := hamx
        have hTn' : T ^ (j + 2) / n = T ^ (j + 1) * τ := hTn
        rw [← hTn', ← hamx']
        push_cast
        rw [show x ^ (j + 2) = x ^ j * x * x by ring, hxnq]; field_simp
      have hch : (1 : ℝ) ≤ ((j + 2).choose 2 : ℝ) := by
        exact_mod_cast Nat.choose_pos (by omega)
      have e : j + 1 + 1 - 2 = j := by omega
      rw [e]
      calc a ^ (j + 1 + 1) * (N (j + 1 + 1) ^ 2 * ((n * q * q : ℕ) * ((n * q - 2).choose j : ℕ) : ℝ))
          ≤ a ^ (j + 2) * (N (j + 2) ^ 2 * ((n * q * q : ℕ) * x ^ j)) := by
            push_cast; gcongr
        _ = N (j + 2) ^ 2 * (T ^ (j + 1) * τ) := by rw [← key]; ring
        _ ≤ 4 * ((j + 2).choose 2 : ℝ) * N (j + 2) ^ 2 * (T ^ (j + 1) * τ) := by
            have : 0 ≤ N (j + 2) ^ 2 * (T ^ (j + 1) * τ) := by positivity
            nlinarith
        _ = _ := by ring
    · simp only [Nat.cast_zero, mul_zero]
      positivity
  rw [Nat.add_sub_cancel]
  rw [mul_add, mul_add]
  calc _ ≤ Ck' p (k + 1) T N ^ 2 * T ^ (k + 1) / (k + 1).factorial * τ +
        4 * ((k + 1 : ℕ) * p' : ℝ) * T ^ k * N (k + 1) ^ 2 * τ +
        4 * ((k + 1).choose 2 : ℝ) * T ^ k * N (k + 1) ^ 2 * τ := by
        have := t1; have := t2; have := t3; linarith
    _ = _ := by push_cast; ring


/-- **The `L²` core estimate of (ii)** (granular, exact for every `n`, `q`): the fine coins'
Gaussian-lift approximant `Π_m F_n(ζ)` and the fine Walsh level `Π_m F_{nq}` differ in `L²`
by at most `√(A_m τ)`. -/
theorem l2_core {m : ℕ} (hm : 1 ≤ m) (hn : 0 < n) (hq : 0 < q) {T : ℝ} (hT : 0 < T)
    (hτ : T / n ≤ 1) (t : Fin p → ℝ) (ht0 : ∀ l, 0 ≤ t l) {g : (Fin p → ℝ) → ℝ}
    {N : ℕ → ℝ} (hg : DBnd g (m + 4) N) :
    E (fun ω : Fin (n * q) → Bool =>
        (liftI m (Fn T n t g) (zeta n q ω) - piW m (FN T (n * q) t g) ω) ^ 2) ≤
      Al2 p m T N * (T / n) := by
  classical
  exact l2_core_gen hm hn hq hT hτ t ht0 hg p (j_card_bd_le hn hq hT ht0)

/-! ### Times on the lattice -/

theorem j_walkIdx_lattice (hn : 0 < n) (hq : 0 < q) {T : ℝ} (hT : 0 < T) {s : ℝ}
    (hs : (QE.NSA.walkIdx T n s : ℝ) * (T / n) = s) :
    QE.NSA.walkIdx T (n * q) s = q * QE.NSA.walkIdx T n s := by
  set k := QE.NSA.walkIdx T n s
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have hqpos : (0 : ℝ) < q := by exact_mod_cast hq
  have : s / (T / ((n * q : ℕ) : ℝ)) = ((q * k : ℕ) : ℝ) := by
    rw [← hs]; push_cast; field_simp
  unfold QE.NSA.walkIdx
  rw [this, Nat.floor_natCast]

theorem j_not_bd_lattice (hn : 0 < n) (hq : 0 < q) {T : ℝ} (hT : 0 < T) {t : Fin p → ℝ}
    (hlat : ∀ l, (QE.NSA.walkIdx T n (t l) : ℝ) * (T / n) = t l) (i : Fin (n * q)) :
    ¬ j_bd T t i := by
  intro hi; apply hi
  funext l
  unfold cellVec
  rw [j_walkIdx_lattice hn hq hT (hlat l)]
  have hv := val_blk i
  have hb := (bpos i).2
  by_cases h : (blk i : ℕ) < QE.NSA.walkIdx T n (t l)
  · have : q * ((blk i : ℕ) + 1) ≤ q * QE.NSA.walkIdx T n (t l) := Nat.mul_le_mul_left _ h
    rw [if_pos (by nlinarith), if_pos h]
  · have : q * QE.NSA.walkIdx T n (t l) ≤ q * (blk i : ℕ) := Nat.mul_le_mul_left _ (by omega)
    rw [if_neg (by nlinarith), if_neg h]

open Classical in
/-- (ii) on the time lattice: the boundary term `m p` drops out. -/
theorem l2_core_lattice {m : ℕ} (hm : 1 ≤ m) (hn : 0 < n) (hq : 0 < q) {T : ℝ} (hT : 0 < T)
    (hτ : T / n ≤ 1) (t : Fin p → ℝ) (ht0 : ∀ l, 0 ≤ t l)
    (hlat : ∀ l, (QE.NSA.walkIdx T n (t l) : ℝ) * (T / n) = t l) {g : (Fin p → ℝ) → ℝ}
    {N : ℕ → ℝ} (hg : DBnd g (m + 4) N) :
    E (fun ω : Fin (n * q) → Bool =>
        (liftI m (Fn T n t g) (zeta n q ω) - piW m (FN T (n * q) t g) ω) ^ 2) ≤
      (Ck' p m T N ^ 2 * T ^ m / m.factorial +
        4 * (m.choose 2 : ℝ) * T ^ (m - 1) * N m ^ 2) * (T / n) := by
  have hbd : (univ.filter (j_bd (n := n) (q := q) T t)).card ≤ 0 * q := by
    rw [zero_mul, Nat.le_zero, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    exact fun i _ => j_not_bd_lattice hn hq hT hlat i
  have := l2_core_gen hm hn hq hT hτ t ht0 hg 0 hbd
  simpa using this

open Classical in
/-- (ii) for `m = 1` on the time lattice: the error is of order `τ`, not `√τ`. -/
theorem l2_core_one_lattice (hn : 0 < n) (hq : 0 < q) {T : ℝ} (hT : 0 < T)
    (t : Fin p → ℝ) (ht0 : ∀ l, 0 ≤ t l)
    (hlat : ∀ l, (QE.NSA.walkIdx T n (t l) : ℝ) * (T / n) = t l) {g : (Fin p → ℝ) → ℝ}
    {N : ℕ → ℝ} (hg : DBnd g (1 + 4) N) :
    E (fun ω : Fin (n * q) → Bool =>
        (liftI 1 (Fn T n t g) (zeta n q ω) - piW 1 (FN T (n * q) t g) ω) ^ 2) ≤
      Ck' p 1 T N ^ 2 * T * (T / n) ^ 2 := by
  rw [j_E_sq_eq]
  have hxpos : (0 : ℝ) < ((n * q : ℕ) : ℝ) := by exact_mod_cast Nat.mul_pos hn hq
  calc _ ≤ ∑ U ∈ powersetCard 1 (univ : Finset (Fin (n * q))),
        (T / ((n * q : ℕ) : ℝ)) ^ 1 * (Ck' p 1 T N ^ 2 * (T / n) ^ 2 + 4 * N 1 ^ 2 * 0 +
          N 1 ^ 2 * 0) := by
        refine Finset.sum_le_sum fun U hU => ?_
        have hc := (Finset.mem_powersetCard.1 hU).2
        have h := j_term_le hn hq hT t ht0 hg U hc
        have e1 : (U.filter (j_bd T t)).card = 0 := by
          rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
          exact fun i _ => j_not_bd_lattice hn hq hT hlat i
        have e2 : ((U ×ˢ U).filter (fun x => x.1 ≠ x.2 ∧ blk x.1 = blk x.2)).card = 0 := by
          rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
          rintro ⟨a, b⟩ hx ⟨hne, -⟩
          obtain ⟨ha, hb⟩ := Finset.mem_product.1 hx
          exact hne (Finset.card_le_one.1 hc.le a ha b hb)
        rw [e1, e2] at h; simpa using h
    _ = Ck' p 1 T N ^ 2 * T * (T / n) ^ 2 := by
        rw [Finset.sum_const, Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin,
          Nat.choose_one_right, nsmul_eq_mul]
        field_simp
        ring

end L2Core

end QE.Chaos.Shadow

/-! # Part K. Laws: coins against Gaussians -/

namespace QE.Chaos.Shadow

open Finset MeasureTheory ProbabilityTheory Filter Topology QE.NSA QE.Chaos.Loeb QE.Chaos.Bon
open QE.OpenSto.Walsh (E coeff chi sgn)
open scoped NNReal
open ArchimedeanClass

section LawGauss

/-- The fine coin numbers `N_k = n₀ (k+1)`. -/
abbrev k_Nseq (n₀ : ℕ) : ℕ → ℕ := fun k => n₀ * (k + 1)

theorem k_unlimited {n₀ : ℕ} (hn₀ : 0 < n₀) : IsUnlimited ((k_Nseq n₀ : ℕ → ℕ) : Ult ℕ) := by
  intro m
  refine Germ.coe_lt.2 ?_
  have : ∀ᶠ k in (atTop : Filter ℕ), m < k_Nseq n₀ k := by
    filter_upwards [eventually_ge_atTop m] with k hk
    simp only [k_Nseq]; nlinarith
  exact this.filter_mono Nat.hyperfilter_le_atTop

/-- The normalised block sums of the `n₀ q` fine coins. -/
def k_zeta (n₀ q : ℕ) (η : Fin (n₀ * q) → Bool) (j : Fin n₀) : ℝ :=
  (∑ r : Fin q, (sgn (η (finProdFinEquiv (j, r))) : ℝ)) / √q

/-- The integer times `0, 1, …, n₀`. -/
def k_times (n₀ : ℕ) : Fin (n₀ + 1) → ℝ≥0 := fun i => (i : ℝ≥0)

theorem k_walkIdx (n₀ q : ℕ) (hn₀ : 0 < n₀) (hq : 0 < q) (i : ℕ) :
    walkIdx (n₀ : ℝ) (n₀ * q) (i : ℝ) = i * q := by
  unfold walkIdx
  have : (i : ℝ) / ((n₀ : ℝ) / ((n₀ * q : ℕ) : ℝ)) = ((i * q : ℕ) : ℝ) := by
    push_cast; field_simp
  rw [this, Nat.floor_natCast]

/-- A block of fine coins is the difference of two initial segments. -/
theorem k_sum_block (n₀ q : ℕ) (f : Fin (n₀ * q) → ℝ) (j : Fin n₀) :
    ∑ x ∈ univ.filter (fun x : Fin (n₀ * q) => (x : ℕ) < ((j : ℕ) + 1) * q), f x -
      ∑ x ∈ univ.filter (fun x : Fin (n₀ * q) => (x : ℕ) < (j : ℕ) * q), f x =
      ∑ r : Fin q, f (finProdFinEquiv (j, r)) := by
  rw [sum_filter, sum_filter, ← sum_sub_distrib, ← Equiv.sum_comp finProdFinEquiv,
    Fintype.sum_prod_type]
  rw [Finset.sum_eq_single j]
  · apply sum_congr rfl; intro r _
    have h1 : ((finProdFinEquiv (j, r) : Fin (n₀ * q)) : ℕ) = r + q * j := rfl
    have hr := r.isLt
    rw [h1, if_pos (by nlinarith), if_neg (by nlinarith), sub_zero]
  · intro j' _ hne
    refine sum_eq_zero fun r _ => ?_
    have h1 : ((finProdFinEquiv (j', r) : Fin (n₀ * q)) : ℕ) = r + q * j' := rfl
    have hr := r.isLt
    rw [h1]
    rcases lt_or_gt_of_ne (Fin.val_injective.ne hne) with hlt | hlt
    · rw [if_pos (by nlinarith), if_pos (by nlinarith), sub_self]
    · rw [if_neg (by nlinarith), if_neg (by nlinarith), sub_self]
  · simp

theorem k_walkVec_val (n₀ q : ℕ) (hn₀ : 0 < n₀) (hq : 0 < q) (η : Fin (n₀ * q) → Bool)
    (i : Fin (n₀ + 1)) :
    walkVec (n₀ : ℝ) (n₀ * q) (k_times n₀) η i =
      (1 / √q) * ∑ x ∈ univ.filter (fun x : Fin (n₀ * q) => (x : ℕ) < (i : ℕ) * q),
        (sgn (η x) : ℝ) := by
  unfold walkVec k_times
  rw [NNReal.coe_natCast, k_walkIdx n₀ q hn₀ hq]
  congr 1
  push_cast
  rw [show (n₀ : ℝ) / (n₀ * q) = 1 / q by field_simp, Real.sqrt_div' _ (Nat.cast_nonneg q),
    Real.sqrt_one]

/-- The block sums are the walk increments over unit times. -/
theorem k_zeta_eq_walk (n₀ q : ℕ) (hn₀ : 0 < n₀) (hq : 0 < q) (η : Fin (n₀ * q) → Bool)
    (j : Fin n₀) :
    k_zeta n₀ q η j = walkVec (n₀ : ℝ) (n₀ * q) (k_times n₀) η j.succ -
      walkVec (n₀ : ℝ) (n₀ * q) (k_times n₀) η j.castSucc := by
  rw [k_walkVec_val n₀ q hn₀ hq, k_walkVec_val n₀ q hn₀ hq, ← mul_sub, Fin.val_succ,
    Fin.val_castSucc, k_sum_block, k_zeta, one_div, inv_mul_eq_div]

/-- **Loeb transfer for functionals of the normalised block sums.** -/
theorem k_tendsto_E {n₀ : ℕ} (hn₀ : 0 < n₀) (H : (Fin n₀ → ℝ) → ℝ) (hH : Continuous H)
    (hS : SInt (k_Nseq n₀) (fun k η => H (k_zeta n₀ (k + 1) η))) :
    Integrable (fun ω => H (fun j : Fin n₀ => andersonB n₀ (k_Nseq n₀) ((j : ℝ) + 1) ω -
        andersonB n₀ (k_Nseq n₀) j ω)) (L (k_Nseq n₀)) ∧
    Tendsto (fun k => E (fun η : Fin (n₀ * (k + 1)) → Bool => H (k_zeta n₀ (k + 1) η)))
      (hyperfilter ℕ : Filter ℕ)
      (𝓝 (∫ ω, H (fun j : Fin n₀ => andersonB n₀ (k_Nseq n₀) ((j : ℝ) + 1) ω -
        andersonB n₀ (k_Nseq n₀) j ω) ∂(L (k_Nseq n₀)))) := by
  set N := k_Nseq n₀
  have hn := k_unlimited hn₀
  have hT : (0 : ℝ) < n₀ := by exact_mod_cast hn₀
  set h : (Fin (n₀ + 1) → ℝ) → ℝ := fun x => H (fun j => x j.succ - x j.castSucc)
  have hh : Continuous h := hH.comp (continuous_pi fun j =>
    (continuous_apply _).sub (continuous_apply _))
  have htT : ∀ l, (k_times n₀ l : ℝ) ≤ (n₀ : ℝ) := fun l => by
    simp only [k_times, NNReal.coe_natCast]; exact_mod_cast Nat.lt_succ_iff.1 l.isLt
  have hwalk := ae_st_walk hT hn (k_times n₀) htT h hh
  have heq : iF N (fun k η => H (k_zeta n₀ (k + 1) η)) =
      iF N (fun k ω => h (walkVec (n₀ : ℝ) (N k) (k_times n₀) ω)) := by
    congr 1; funext k η
    simp only [h]
    congr 1; funext j
    exact k_zeta_eq_walk n₀ (k + 1) hn₀ (Nat.succ_pos k) η j
  have hae : ∀ᵐ ω ∂(L N), stdPart (iF N (fun k η => H (k_zeta n₀ (k + 1) η)) ω) =
      H (fun j : Fin n₀ => andersonB n₀ N ((j : ℝ) + 1) ω - andersonB n₀ N j ω) := by
    filter_upwards [hwalk] with ω hω
    rw [heq, hω]
    simp only [h, k_times, Fin.val_succ, Fin.val_castSucc]
    congr 1; funext j; push_cast; rfl
  obtain ⟨hint, hEq⟩ := st_iE_eq_integral hS
  refine ⟨hint.congr hae, ?_⟩
  have hfin := isFinite_iE_of_abs hS.1
  exact (QE.Chaos.DExp.ofSeq_st_iff_tendsto _ _).1 ⟨hfin, hEq.trans (integral_congr_ae hae)⟩

theorem k_continuous_mlEval {n : ℕ} (a : Finset (Fin n) → ℝ) : Continuous (mlEval a) := by
  unfold mlEval
  exact continuous_finset_sum _ fun S _ => continuous_const.mul
    (continuous_finset_prod _ fun i _ => continuous_apply i)

theorem k_pow_le {x : ℝ} {i : ℕ} (hi : i ≤ 4) : |x| ^ i ≤ 1 + x ^ 4 := by
  rcases le_or_gt |x| 1 with h | h
  · have : |x| ^ i ≤ 1 := pow_le_one₀ (abs_nonneg _) h
    nlinarith [sq_nonneg (x ^ 2)]
  · have : |x| ^ i ≤ |x| ^ 4 := pow_le_pow_right₀ h.le hi
    rw [show |x| ^ 4 = x ^ 4 by rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, sq_abs, ← pow_mul]]
      at this
    linarith

/-- Polynomial growth from a bounded `(k+1)`-st derivative, `k ≤ 3`. -/
theorem k_growth (Ψ : ℝ → ℝ) (k : ℕ) (hk : k ≤ 3) (hΨ : ContDiff ℝ ((k : WithTop ℕ∞) + 1) Ψ)
    {B : ℝ} (hB : ∀ x, |iteratedDeriv (k + 1) Ψ x| ≤ B) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x, |Ψ x| ≤ C * (1 + x ^ 4) := by
  refine ⟨∑ i ∈ range (k + 1), |iteratedDeriv i Ψ 0| + |B|, by positivity, fun x => ?_⟩
  have ht := taylor_abs_le Ψ k hΨ hB 0 x
  rw [zero_add] at ht
  have h4 : 0 ≤ 1 + x ^ 4 := by positivity
  have hsum : |∑ i ∈ range (k + 1), iteratedDeriv i Ψ 0 * x ^ i / (i.factorial : ℝ)| ≤
      (∑ i ∈ range (k + 1), |iteratedDeriv i Ψ 0|) * (1 + x ^ 4) := by
    rw [sum_mul]
    refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun i hi => ?_)
    have hi4 : i ≤ 4 := by have := mem_range.1 hi; omega
    rw [abs_div, abs_mul, abs_pow, Nat.abs_cast]
    have hf : (1 : ℝ) ≤ i.factorial := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (Nat.factorial_ne_zero i)
    calc |iteratedDeriv i Ψ 0| * |x| ^ i / (i.factorial : ℝ) ≤ |iteratedDeriv i Ψ 0| * |x| ^ i :=
          div_le_self (by positivity) hf
      _ ≤ _ := mul_le_mul_of_nonneg_left (k_pow_le hi4) (abs_nonneg _)
  have hrem : B * |x| ^ (k + 1) / ((k + 1).factorial : ℝ) ≤ |B| * (1 + x ^ 4) := by
    have hf : (1 : ℝ) ≤ (k + 1).factorial := by
      exact_mod_cast Nat.one_le_iff_ne_zero.2 (Nat.factorial_ne_zero _)
    calc B * |x| ^ (k + 1) / ((k + 1).factorial : ℝ) ≤ |B| * |x| ^ (k + 1) / ((k + 1).factorial : ℝ) := by
          gcongr; exact le_abs_self B
      _ ≤ |B| * |x| ^ (k + 1) := div_le_self (by positivity) hf
      _ ≤ _ := mul_le_mul_of_nonneg_left (k_pow_le (by omega)) (abs_nonneg _)
  have := abs_sub_abs_le_abs_sub (Ψ x) (∑ i ∈ range (k + 1), iteratedDeriv i Ψ 0 * x ^ i / (i.factorial : ℝ))
  nlinarith [abs_nonneg (∑ i ∈ range (k + 1), iteratedDeriv i Ψ 0 * x ^ i / (i.factorial : ℝ))]

/-- S-integrability of `Ψ(Q(ζ))` for a polynomial `Q` of bounded degree and `Ψ` of growth
`C (1 + x⁴)`. -/
theorem k_SInt {n₀ d : ℕ} (a : Finset (Fin n₀) → ℝ) (ha : DegLe a d) (Ψ : ℝ → ℝ) {C : ℝ}
    (hC : ∀ x, |Ψ x| ≤ C * (1 + x ^ 4)) :
    SInt (k_Nseq n₀) (fun k η => Ψ (mlEval a (k_zeta n₀ (k + 1) η))) := by
  refine SInt_of_sq_finite ?_
  refine (isFinite_ofSeq_iff _).2 ⟨2 * C ^ 2 * (1 + 9 ^ (4 * d) * (∑ S, a S ^ 2) ^ 4),
    Eventually.of_forall fun k => ?_⟩
  dsimp only
  have h8 := E_fine_eight_le (Nat.succ_pos k) a ha
  have hpt : ∀ η : Fin (n₀ * (k + 1)) → Bool, Ψ (mlEval a (k_zeta n₀ (k + 1) η)) ^ 2 ≤
      2 * C ^ 2 * (1 + mlEval a (k_zeta n₀ (k + 1) η) ^ 8) := by
    intro η
    set y := mlEval a (k_zeta n₀ (k + 1) η)
    have h1 := hC y
    have h2 : Ψ y ^ 2 ≤ (C * (1 + y ^ 4)) ^ 2 := by
      rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) h1 2
    nlinarith [sq_nonneg (y ^ 4 - 1), sq_nonneg C]
  have hnn : 0 ≤ E (fun η : Fin (n₀ * (k + 1)) → Bool => Ψ (mlEval a (k_zeta n₀ (k + 1) η)) ^ 2) := by
    rw [← avg_eq_E]; exact avg_nonneg fun _ => sq_nonneg _
  rw [abs_of_nonneg hnn]
  calc E (fun η : Fin (n₀ * (k + 1)) → Bool => Ψ (mlEval a (k_zeta n₀ (k + 1) η)) ^ 2)
      ≤ E (fun η : Fin (n₀ * (k + 1)) → Bool => 2 * C ^ 2 * (1 + mlEval a (k_zeta n₀ (k + 1) η) ^ 8)) := by
        rw [← avg_eq_E, ← avg_eq_E]; exact avg_mono hpt
    _ = 2 * C ^ 2 * (1 + E (fun η : Fin (n₀ * (k + 1)) → Bool =>
          mlEval a (k_zeta n₀ (k + 1) η) ^ 8)) := by
        rw [← avg_eq_E, ← avg_eq_E, avg_const_mul, avg_add, avg_const]
    _ ≤ _ := by gcongr; exact h8

/-- **From the coin-world bounds to Gaussians.** If coins and normalised block sums are within
`bound` for every block size `q`, then coins and a standard Gaussian vector are within `bound`. -/
theorem k_law_of_bound {n₀ d : ℕ} (hn₀ : 0 < n₀) (a : Finset (Fin n₀) → ℝ) (ha : DegLe a d)
    (Ψ : ℝ → ℝ) (hΨc : Continuous Ψ) {C : ℝ} (hC : ∀ x, |Ψ x| ≤ C * (1 + x ^ 4)) (bound : ℝ)
    (hb : ∀ q : ℕ, 0 < q → |E (fun η : Fin n₀ → Bool => Ψ (mlEval a (fun j => sgn (η j)))) -
      E (fun η : Fin (n₀ * q) → Bool =>
        Ψ (mlEval a (fun j => (∑ r : Fin q, (sgn (η (finProdFinEquiv (j, r))) : ℝ)) / √q)))| ≤
        bound)
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {G : Ω → Fin n₀ → ℝ}
    (hG : HasLaw G (Measure.pi fun _ => gaussianReal 0 1) P) :
    Integrable (fun ω => Ψ (mlEval a (G ω))) P ∧
      |E (fun η : Fin n₀ → Bool => Ψ (mlEval a (fun j => sgn (η j)))) -
        ∫ ω, Ψ (mlEval a (G ω)) ∂P| ≤ bound := by
  set H : (Fin n₀ → ℝ) → ℝ := fun x => Ψ (mlEval a x)
  have hH : Continuous H := hΨc.comp (k_continuous_mlEval a)
  have hn := k_unlimited hn₀
  obtain ⟨hint, ht⟩ := k_tendsto_E hn₀ H hH (k_SInt a ha Ψ hC)
  have hI := integral_iid_gaussian_eq hn n₀ hn₀ hG H hH.stronglyMeasurable
  have hlawL := hasLaw_unit_increments hn n₀ hn₀
  refine ⟨?_, ?_⟩
  · have h1 : Integrable H (Measure.pi fun _ : Fin n₀ => gaussianReal 0 1) := by
      rw [← hlawL.map_eq]
      exact (integrable_map_measure hH.aestronglyMeasurable hlawL.aemeasurable).2 hint
    rw [← hG.map_eq] at h1
    exact (integrable_map_measure hH.aestronglyMeasurable hG.aemeasurable).1 h1
  · rw [hI]
    exact le_of_tendsto' ((tendsto_const_nhds).sub ht).abs fun k => hb (k + 1) (Nat.succ_pos k)

/-- **Invariance principle, coins vs Gaussians (fourth order).** -/
theorem law_coins_gauss4 {n d : ℕ} (hn : 0 < n) (a : Finset (Fin n) → ℝ) (ha : DegLe a d)
    (Ψ : ℝ → ℝ) (hΨ : ContDiff ℝ 4 Ψ) {B : ℝ} (hB : ∀ x, |iteratedDeriv 4 Ψ x| ≤ B)
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {G : Ω → Fin n → ℝ}
    (hG : HasLaw G (Measure.pi fun _ => gaussianReal 0 1) P) :
    Integrable (fun ω => Ψ (mlEval a (G ω))) P ∧
      |E (fun η : Fin n → Bool => Ψ (mlEval a (fun j => sgn (η j)))) -
        ∫ ω, Ψ (mlEval a (G ω)) ∂P| ≤ B / 6 * 9 ^ (d - 1) * ∑ j, infl a j ^ 2 := by
  have hΨ' : ContDiff ℝ (((3 : ℕ) : WithTop ℕ∞) + 1) Ψ := by
    convert hΨ using 2; norm_num
  obtain ⟨C, -, hC⟩ := k_growth Ψ 3 le_rfl hΨ' hB
  exact k_law_of_bound hn a ha Ψ hΨ.continuous hC _
    (fun q hq => invariance4_coins hq a ha Ψ hΨ hB) hG

/-- **Invariance principle, coins vs Gaussians (third order).** -/
theorem law_coins_gauss3 {n d : ℕ} (hn : 0 < n) (a : Finset (Fin n) → ℝ) (ha : DegLe a d)
    (Ψ : ℝ → ℝ) (hΨ : ContDiff ℝ 3 Ψ) {B : ℝ} (hB : ∀ x, |iteratedDeriv 3 Ψ x| ≤ B)
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {G : Ω → Fin n → ℝ}
    (hG : HasLaw G (Measure.pi fun _ => gaussianReal 0 1) P) :
    Integrable (fun ω => Ψ (mlEval a (G ω))) P ∧
      |E (fun η : Fin n → Bool => Ψ (mlEval a (fun j => sgn (η j)))) -
        ∫ ω, Ψ (mlEval a (G ω)) ∂P| ≤
        B / 6 * (1 + √3) * 3 ^ (d - 1) * ∑ j, infl a j * √(infl a j) := by
  have hΨ' : ContDiff ℝ (((2 : ℕ) : WithTop ℕ∞) + 1) Ψ := by
    convert hΨ using 2; norm_num
  obtain ⟨C, -, hC⟩ := k_growth Ψ 2 (by norm_num) hΨ' hB
  exact k_law_of_bound hn a ha Ψ hΨ.continuous hC _
    (fun q hq => invariance3_coins hq a ha Ψ hΨ hB) hG

/-! ### The cylinder functional -/

/-- `K_m = T^{m-1} N_m² / (m-1)!`. -/
def Km (T : ℝ) (m : ℕ) (N : ℕ → ℝ) : ℝ := T ^ (m - 1) * N m ^ 2 / (m - 1).factorial

theorem k_liftI_eq {n : ℕ} (m : ℕ) (F : (Fin n → Bool) → ℝ) (x : Fin n → ℝ) :
    liftI m F x = mlEval (fun S => if S.card = m then coeff F S else 0) x := by
  unfold liftI mlEval
  rw [powersetCard_eq_filter, powerset_univ, sum_filter]
  apply sum_congr rfl; intro S _
  by_cases h : S.card = m <;> simp [h]

/-- The Walsh coefficients of the cylinder functional: `|F̂_n(S)| ≤ τ^{m/2} N_m`. -/
theorem k_abs_coeff_le {p m n : ℕ} {T : ℝ} (hT : 0 < T) (hn : 0 < n) (t : Fin p → ℝ)
    {g : (Fin p → ℝ) → ℝ} {N : ℕ → ℝ} (hg : QE.Chaos.Calc.DBnd g m N) (S : Finset (Fin n))
    (hS : S.card = m) : coeff (Fn T n t g) S ^ 2 ≤ (T / n) ^ m * N m ^ 2 := by
  have hc : 0 < √(T / n) := Real.sqrt_pos.2 (by positivity)
  have hl := QE.Chaos.Calc.coeff_walk (√(T / n)) hc.ne' (vC T n t) g S.toList (nodup_toList S)
  rw [toList_toFinset] at hl
  have hlen : S.toList.length = m := by rw [length_toList, hS]
  rw [hlen] at hl
  have hE : |E (fun ω => QE.Chaos.Calc.cds √(T / n) (S.toList.map (vC T n t)) g
      (QE.Chaos.Calc.walkVec √(T / n) (vC T n t) S ω))| ≤ N m := by
    rw [← avg_eq_E]
    refine abs_avg_le_of_le fun ω => QE.Chaos.Calc.abs_cds_le hg (by simp [hlen]) ?_ hc _
    intro v hv
    obtain ⟨j, -, rfl⟩ := List.mem_map.1 hv
    exact QE.Chaos.Calc.norm_cellVec_le T n t j
  have e : coeff (Fn T n t g) S = √(T / n) ^ m * E (fun ω => QE.Chaos.Calc.cds √(T / n)
      (S.toList.map (vC T n t)) g (QE.Chaos.Calc.walkVec √(T / n) (vC T n t) S ω)) := hl
  rw [e, mul_pow, ← pow_mul, mul_comm m 2, pow_mul, Real.sq_sqrt (by positivity)]
  exact mul_le_mul_of_nonneg_left (by rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hE 2)
    (by positivity)

/-- **Influence bound**: `Inf_j(Π_m F_n) ≤ K_m τ`. -/
theorem infl_chaos_le {p m n : ℕ} (hm : 1 ≤ m) (hn : 0 < n) {T : ℝ} (hT : 0 < T)
    (t : Fin p → ℝ) {g : (Fin p → ℝ) → ℝ} {N : ℕ → ℝ} (hg : QE.Chaos.Calc.DBnd g m N)
    (j : Fin n) :
    infl (fun S => if S.card = m then coeff (Fn T n t g) S else 0) j ≤ Km T m N * (T / n) := by
  classical
  set τ := T / n with hτ
  have hτ0 : 0 < τ := by positivity
  have hset : (univ.filter (fun S : Finset (Fin n) => j ∈ S)).filter (fun S => S.card = m) =
      (powersetCard m univ).filter (fun U => {j} ⊆ U) := by
    ext S; simp [mem_powersetCard, and_comm]
  have e1 : infl (fun S => if S.card = m then coeff (Fn T n t g) S else 0) j =
      ∑ S ∈ (powersetCard m univ).filter (fun U => {j} ⊆ U), coeff (Fn T n t g) S ^ 2 := by
    unfold infl
    rw [← hset, sum_filter, sum_filter, sum_filter]
    apply sum_congr rfl; intro S _
    by_cases h1 : j ∈ S <;> by_cases h2 : S.card = m <;> simp [h1, h2]
  rw [e1]
  have hcard := card_powersetCard_superset (univ : Finset (Fin n)) {j} (subset_univ _)
    (m := m) (by simpa using hm)
  simp only [card_univ, Fintype.card_fin, card_singleton] at hcard
  have hN2 : 0 ≤ N m ^ 2 := sq_nonneg _
  calc ∑ S ∈ (powersetCard m univ).filter (fun U => {j} ⊆ U), coeff (Fn T n t g) S ^ 2
      ≤ ∑ S ∈ (powersetCard m univ).filter (fun U => {j} ⊆ U), τ ^ m * N m ^ 2 := by
        refine sum_le_sum fun S hS => ?_
        exact k_abs_coeff_le hT hn t hg S (mem_powersetCard.1 (mem_filter.1 hS).1).2
    _ = ((n - 1).choose (m - 1) : ℝ) * (τ ^ m * N m ^ 2) := by
        rw [sum_const, hcard, nsmul_eq_mul]
    _ ≤ ((n : ℝ) ^ (m - 1) / (m - 1).factorial) * (τ ^ m * N m ^ 2) := by
        gcongr
        refine (choose_le_pow_div' (n - 1) (m - 1)).trans ?_
        gcongr
        exact_mod_cast Nat.sub_le n 1
    _ = Km T m N * τ := by
        unfold Km
        have hnτ : (n : ℝ) * τ = T := by rw [hτ]; field_simp
        obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
        simp only [Nat.add_sub_cancel]
        rw [← hnτ, mul_pow, pow_succ]
        ring

theorem sum_infl_sq_le {p m n : ℕ} (hm : 1 ≤ m) (hn : 0 < n) {T : ℝ} (hT : 0 < T)
    (t : Fin p → ℝ) {g : (Fin p → ℝ) → ℝ} {N : ℕ → ℝ} (hg : QE.Chaos.Calc.DBnd g m N) :
    ∑ j, infl (fun S => if S.card = m then coeff (Fn T n t g) S else 0) j ^ 2 ≤
      T * Km T m N ^ 2 * (T / n) := by
  have hb : ∀ j : Fin n, infl (fun S => if S.card = m then coeff (Fn T n t g) S else 0) j ^ 2 ≤
      (Km T m N * (T / n)) ^ 2 := fun j =>
    pow_le_pow_left₀ (infl_nonneg _ _) (infl_chaos_le hm hn hT t hg j) 2
  refine (sum_le_sum fun j _ => hb j).trans ?_
  rw [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
  have : (n : ℝ) * (T / n) = T := by field_simp
  refine le_of_eq ?_
  rw [show (n : ℝ) * (Km T m N * (T / n)) ^ 2 = ((n : ℝ) * (T / n)) * Km T m N ^ 2 * (T / n) by
    ring, this]

theorem sum_infl_pow_three_halves_le {p m n : ℕ} (hm : 1 ≤ m) (hn : 0 < n) {T : ℝ} (hT : 0 < T)
    (t : Fin p → ℝ) {g : (Fin p → ℝ) → ℝ} {N : ℕ → ℝ} (hg : QE.Chaos.Calc.DBnd g m N) :
    ∑ j, infl (fun S => if S.card = m then coeff (Fn T n t g) S else 0) j *
        √(infl (fun S => if S.card = m then coeff (Fn T n t g) S else 0) j) ≤
      T * (Km T m N * √(Km T m N)) * √(T / n) := by
  have hK : 0 ≤ Km T m N := by unfold Km; positivity
  have hτ : 0 ≤ T / n := by positivity
  have hb : ∀ j : Fin n, infl (fun S => if S.card = m then coeff (Fn T n t g) S else 0) j *
      √(infl (fun S => if S.card = m then coeff (Fn T n t g) S else 0) j) ≤
      (Km T m N * (T / n)) * √(Km T m N * (T / n)) := fun j => by
    have h1 := infl_chaos_le hm hn hT t hg j
    have h0 := infl_nonneg (fun S => if S.card = m then coeff (Fn T n t g) S else 0) j
    exact mul_le_mul h1 (Real.sqrt_le_sqrt h1) (Real.sqrt_nonneg _) (by positivity)
  refine (sum_le_sum fun j _ => hb j).trans ?_
  rw [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul, Real.sqrt_mul hK]
  have : (n : ℝ) * (T / n) = T := by field_simp
  refine le_of_eq ?_
  rw [show (n : ℝ) * (Km T m N * (T / n) * (√(Km T m N) * √(T / n))) =
    ((n : ℝ) * (T / n)) * (Km T m N * √(Km T m N)) * √(T / n) by ring, this]

/-- **(iii), fourth order, for the `m`-th Walsh chaos of the cylinder functional** against its
Gaussian lift (any standard Gaussian vector `G`):
`|E Ψ(Π_m F_n) - E Ψ(Π_m F̃_n)| ≤ (B/6) 9^{m-1} T K_m² τ`. -/
theorem law_chaos_gauss4 {p m n : ℕ} (hm : 1 ≤ m) (hn : 0 < n) {T : ℝ} (hT : 0 < T)
    (t : Fin p → ℝ) {g : (Fin p → ℝ) → ℝ} {N : ℕ → ℝ} (hg : QE.Chaos.Calc.DBnd g m N)
    (Ψ : ℝ → ℝ) (hΨ : ContDiff ℝ 4 Ψ) {B : ℝ} (hB : ∀ x, |iteratedDeriv 4 Ψ x| ≤ B)
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {G : Ω → Fin n → ℝ}
    (hG : HasLaw G (Measure.pi fun _ => gaussianReal 0 1) P) :
    Integrable (fun ω => Ψ (liftI m (Fn T n t g) (G ω))) P ∧
      |E (fun η : Fin n → Bool => Ψ (liftI m (Fn T n t g) (fun j => sgn (η j)))) -
        ∫ ω, Ψ (liftI m (Fn T n t g) (G ω)) ∂P| ≤
        B / 6 * 9 ^ (m - 1) * T * Km T m N ^ 2 * (T / n) := by
  simp_rw [k_liftI_eq]
  obtain ⟨hi, hb⟩ := law_coins_gauss4 hn _ (degLe_chaos (Fn T n t g) m) Ψ hΨ hB hG
  refine ⟨hi, hb.trans ?_⟩
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB 0)
  have := sum_infl_sq_le hm hn hT t hg
  calc B / 6 * 9 ^ (m - 1) * ∑ j, infl (fun S => if S.card = m then coeff (Fn T n t g) S else 0) j ^ 2
      ≤ B / 6 * 9 ^ (m - 1) * (T * Km T m N ^ 2 * (T / n)) := by gcongr
    _ = _ := by ring

/-- **(iii), third order**: `|E Ψ(Π_m F_n) - E Ψ(Π_m F̃_n)| ≤ (B/6)(1+√3) 3^{m-1} T K_m^{3/2} √τ`. -/
theorem law_chaos_gauss3 {p m n : ℕ} (hm : 1 ≤ m) (hn : 0 < n) {T : ℝ} (hT : 0 < T)
    (t : Fin p → ℝ) {g : (Fin p → ℝ) → ℝ} {N : ℕ → ℝ} (hg : QE.Chaos.Calc.DBnd g m N)
    (Ψ : ℝ → ℝ) (hΨ : ContDiff ℝ 3 Ψ) {B : ℝ} (hB : ∀ x, |iteratedDeriv 3 Ψ x| ≤ B)
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {G : Ω → Fin n → ℝ}
    (hG : HasLaw G (Measure.pi fun _ => gaussianReal 0 1) P) :
    Integrable (fun ω => Ψ (liftI m (Fn T n t g) (G ω))) P ∧
      |E (fun η : Fin n → Bool => Ψ (liftI m (Fn T n t g) (fun j => sgn (η j)))) -
        ∫ ω, Ψ (liftI m (Fn T n t g) (G ω)) ∂P| ≤
        B / 6 * (1 + √3) * 3 ^ (m - 1) * T * (Km T m N * √(Km T m N)) * √(T / n) := by
  simp_rw [k_liftI_eq]
  obtain ⟨hi, hb⟩ := law_coins_gauss3 hn _ (degLe_chaos (Fn T n t g) m) Ψ hΨ hB hG
  refine ⟨hi, hb.trans ?_⟩
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB 0)
  have := sum_infl_pow_three_halves_le hm hn hT t hg
  calc B / 6 * (1 + √3) * 3 ^ (m - 1) * ∑ j, infl (fun S => if S.card = m then
        coeff (Fn T n t g) S else 0) j * √(infl (fun S => if S.card = m then
          coeff (Fn T n t g) S else 0) j)
      ≤ B / 6 * (1 + √3) * 3 ^ (m - 1) * (T * (Km T m N * √(Km T m N)) * √(T / n)) := by
        gcongr
    _ = _ := by ring

end LawGauss

end QE.Chaos.Shadow

/-! # Part L. Kernels and tails -/

namespace QE.Chaos.Shadow

open Finset QE.Chaos.Calc QE.Chaos.Loeb QE.NSA MeasureTheory ProbabilityTheory Filter Topology
  ArchimedeanClass
open QE.OpenSto.Walsh (E coeff chi sgn)
open scoped NNReal

section Unlimited

theorem isUnlimited_mul_succ {n : ℕ} (hn : 0 < n) :
    IsUnlimited (((fun k => n * (k + 1)) : ℕ → ℕ) : Ult ℕ) := by
  intro m
  refine Germ.coe_lt.2 ?_
  have : ∀ᶠ k in (Filter.cofinite : Filter ℕ), m < n * (k + 1) := by
    rw [Nat.cofinite_eq_atTop]
    filter_upwards [eventually_ge_atTop m] with k hk
    nlinarith
  exact hyperfilter_le_cofinite this

/-- Passing a uniform finite bound to the limit along the hyperfilter. -/
theorem abs_sub_le_of_tendsto {X C : ℝ} {Y : ℕ → ℝ} {y : ℝ}
    (hY : Tendsto Y (hyperfilter ℕ : Filter ℕ) (𝓝 y)) (h : ∀ k, |X - Y k| ≤ C) : |X - y| ≤ C :=
  le_of_tendsto ((continuous_abs.tendsto _).comp (tendsto_const_nhds.sub hY))
    (Eventually.of_forall h)

end Unlimited

section KernelShadow

variable {p : ℕ}

/-- `u(s) = (1[s < t_l])_l`, the direction in which the path moves when the increment at
time `s` is perturbed. -/
def uvec (t : Fin p → ℝ≥0) (s : ℝ) : Fin p → ℝ := fun l => if s < t l then 1 else 0

/-- The classical (Stroock) kernel `φ_m(s) = E[∂_{u(s_1)} ⋯ ∂_{u(s_m)} g(B(t_1), …, B(t_p))]`. -/
def phiK {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (B : ℝ≥0 → Ω → ℝ) (t : Fin p → ℝ≥0)
    (g : (Fin p → ℝ) → ℝ) {m : ℕ} (s : Fin m → ℝ) : ℝ :=
  ∫ ω, dirD (List.ofFn fun i => uvec t (s i)) g (fun l => B (t l) ω) ∂P

theorem walkVec_eq_fineWalk (T : ℝ) (N : ℕ) (t : Fin p → ℝ≥0) (ω : Fin N → Bool) :
    QE.Chaos.Loeb.walkVec T N t ω = fineWalk T N (fun l => (t l : ℝ)) ω := rfl

/-- **Item (i) of the shadow theorem: the kernels, pointwise.**  For `s` in a cell product with
distinct cell indices `j i` and with no `s_i ∈ [k_l τ, t_l)`, the step kernel
`f̃(s) = F̂_n(S)/τ^{m/2}` differs from the classical kernel `φ_m(s)` by at most `C_m τ`.
Here `B` is any (pre-)Brownian motion on any probability space. -/
theorem chaos_kernel_shadow {m n : ℕ} (hn : 0 < n) {T : ℝ} (hT : 0 < T) (t : Fin p → ℝ≥0)
    (htT : ∀ l, (t l : ℝ) ≤ T) {g : (Fin p → ℝ) → ℝ} {N : ℕ → ℝ}
    (hg : ContDiff ℝ (m + 4) g) (hgb : ∀ k ≤ m + 4, ∀ x, ‖iteratedFDeriv ℝ k g x‖ ≤ N k)
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {B : ℝ≥0 → Ω → ℝ}
    (hB : IsPreBrownianReal B P) (j : Fin m → Fin n) (hj : Function.Injective j) (s : Fin m → ℝ)
    (hs : ∀ i, (j i : ℝ) * (T / n) ≤ s i ∧ s i < ((j i : ℝ) + 1) * (T / n))
    (hbd : ∀ i l, ¬ ((walkIdx T n (t l) : ℝ) * (T / n) ≤ s i ∧ s i < t l)) :
    |coeff (Fn T n (fun l => (t l : ℝ)) g) (univ.image j) / √(T / n) ^ m - phiK P B t g s| ≤
      Cker p m T N * (T / n) := by
  set tR : Fin p → ℝ := fun l => (t l : ℝ)
  have hDB : DBnd g (m + 4) N := dBnd_of_iteratedFDeriv hg (by exact_mod_cast hgb)
  set l := List.ofFn j with hl
  have hnd : l.Nodup := List.nodup_ofFn.2 hj
  have hlen : l.length = m := by simp [l]
  have hfin : l.toFinset = univ.image j := by ext x; simp [l, List.mem_ofFn]
  set v := fun j : Fin n => cellVec T n tR j
  set c := √(T / n)
  have hc : c ≠ 0 := (Real.sqrt_pos.2 (by positivity)).ne'
  -- the coarse kernel is a coin expectation of central differences
  have hcoeff := coeff_walk c hc v g l hnd
  set X := E (fun ω : Fin n → Bool => cds c (l.map v) g (walkVec c v l.toFinset ω))
  have hX : coeff (Fn T n tR g) (univ.image j) / c ^ m = X := by
    rw [← hfin]
    have : Fn T n tR g = fun ω => g (walkVec c v ∅ ω) := rfl
    rw [this, hcoeff, hlen]; field_simp
  -- the fine walks on `n (k+1)` coins
  set Ns : ℕ → ℕ := fun k => n * (k + 1)
  have hNs : IsUnlimited ((Ns : ℕ → ℕ) : Ult ℕ) := isUnlimited_mul_succ hn
  set h := dirD (l.map v) g
  have hcont : Continuous h := continuous_dirD hDB.1 (ws := l.map v)
    (by rw [List.length_map, hlen]; omega)
  have hbdd : ∀ x, |h x| ≤ N m := by
    intro x
    have := abs_dirD_le_unit (hDB.mono (show m ≤ m + 4 by omega)) (ws := l.map v)
      (by rw [List.length_map, hlen])
      (fun w hw => by
        obtain ⟨a, -, rfl⟩ := List.mem_map.1 hw
        exact norm_cellVec_le T n tR a) x
    simpa [hlen] using this
  have hY : ∀ k, |X - E (fun ω : Fin (Ns k) → Bool => h (fineWalk T (Ns k) tR ω))| ≤
      Cker p m T N * (T / n) := fun k =>
    kernel_coin_bound hn (Nat.succ_pos k) hT tR (fun l => (t l).2) hDB l hnd hlen
  have hlim := st_E_walk hT hNs t htT h hcont hbdd
  have hfinY : IsFinite (Hyperreal.ofSeq fun k =>
      E (fun ω : Fin (Ns k) → Bool => h (QE.Chaos.Loeb.walkVec T (Ns k) t ω))) := by
    refine (isFinite_ofSeq_iff _).2 ⟨N m, Eventually.of_forall fun k => ?_⟩
    rw [← QE.Chaos.avg_eq_E]
    exact QE.Chaos.abs_avg_le_of_le fun ω => hbdd _
  have htend := (QE.Chaos.DExp.ofSeq_st_iff_tendsto _ _).1 ⟨hfinY, hlim⟩
  have hXY := abs_sub_le_of_tendsto htend (fun k => by
    rw [show (fun ω : Fin (Ns k) → Bool => h (QE.Chaos.Loeb.walkVec T (Ns k) t ω)) =
      fun ω => h (fineWalk T (Ns k) tR ω) from rfl]; exact hY k)
  -- the classical side
  have hlaw := integral_brownian_eq hT hNs hB t htT h hcont.stronglyMeasurable
  have hdir : (List.ofFn fun i => uvec t (s i)) = l.map v := by
    rw [hl, List.map_ofFn]
    congr 1; funext i
    funext l'
    simp only [Function.comp, uvec, v, cellVec, tR]
    have hk := walkIdx_bounds hT hn (t := (t l' : ℝ)) (t l').2
    have hτ : 0 < T / n := by positivity
    by_cases hlt : (j i : ℕ) < walkIdx T n (t l')
    · rw [if_pos hlt]
      have h1 : ((j i : ℕ) : ℝ) + 1 ≤ (walkIdx T n (t l') : ℝ) := by exact_mod_cast hlt
      have : s i < t l' := by
        calc s i < ((j i : ℝ) + 1) * (T / n) := (hs i).2
          _ ≤ (walkIdx T n (t l') : ℝ) * (T / n) := mul_le_mul_of_nonneg_right h1 hτ.le
          _ ≤ t l' := hk.2
      rw [if_pos this]
    · rw [if_neg hlt]
      push Not at hlt
      have h1 : (walkIdx T n (t l') : ℝ) ≤ ((j i : ℕ) : ℝ) := by exact_mod_cast hlt
      have : ¬ s i < t l' := fun hst => hbd i l' ⟨le_trans (mul_le_mul_of_nonneg_right h1 hτ.le)
        (hs i).1, hst⟩
      rw [if_neg this]
  have hphi : phiK P B t g s = ∫ ω, h (fun l => andersonB T Ns (t l) ω) ∂(L Ns) := by
    unfold phiK; rw [hdir]; exact hlaw
  rw [hX, hphi]
  exact hXY

end KernelShadow

section Tail

variable {p : ℕ}

/-- `E (Π_m F)² = ∑_{|S| = m} F̂(S)²`. -/
theorem E_piW_sq {N : ℕ} (m : ℕ) (F : (Fin N → Bool) → ℝ) :
    E (fun ω => QE.Chaos.Lift.piW m F ω ^ 2) = ∑ S ∈ powersetCard m univ, coeff F S ^ 2 := by
  have h1 := QE.OpenSto.Walsh.parseval (QE.Chaos.Lift.piW m F) (QE.Chaos.Lift.piW m F)
  simp_rw [← sq] at h1
  rw [h1]
  have hc : ∀ S, coeff (QE.Chaos.Lift.piW m F) S = if S.card = m then coeff F S else 0 := by
    intro S
    have : QE.Chaos.Lift.piW m F =
        fun ω => ∑ S, (if S.card = m then coeff F S else 0) * chi S ω := by
      funext ω; exact QE.Chaos.Lift.piW_eq_full m F ω
    rw [this, QE.OpenSto.Walsh.coeff_of_expansion]
  simp_rw [hc]
  rw [powersetCard_eq_filter, powerset_univ, sum_filter]
  apply sum_congr rfl; intro S _; split_ifs <;> simp

/-- **Item (iv), discrete side**: the Walsh tail of the cylinder functional is uniformly small,
`∑_{|S| ≥ M} F̂_n(S)² ≤ T N₁² / M`, for every `n`. -/
theorem chaos_tail_discrete {n M : ℕ} (hM : 0 < M) {T : ℝ} (hT : 0 < T) (t : Fin p → ℝ)
    {g : (Fin p → ℝ) → ℝ} {N : ℕ → ℝ} (hg : DBnd g 1 N) :
    ∑ S ∈ univ.filter (fun S : Finset (Fin n) => M ≤ S.card), coeff (Fn T n t g) S ^ 2 ≤
      T * N 1 ^ 2 / M := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rw [Finset.sum_eq_zero]
    · positivity
    · intro S hS
      have := (Finset.mem_filter.1 hS).2
      have hS0 : S = ∅ := Finset.eq_empty_of_isEmpty S
      rw [hS0] at this; simp at this; omega
  refine (QE.OpenSto.Walsh.chaos_tail _ M hM).trans ?_
  set c := √(T / n)
  have hc : 0 < c := Real.sqrt_pos.2 (by positivity)
  have hD : ∀ i : Fin n, ∀ ω, QE.OpenSto.Walsh.D i (Fn T n t g) ω ^ 2 ≤ c ^ 2 * N 1 ^ 2 := by
    intro i ω
    have e := D_walk c hc.ne' (vC T n t) g (S := ∅) (i := i) (by simp)
    have : QE.OpenSto.Walsh.D i (Fn T n t g) ω =
        c * cd c (vC T n t i) g (walkVec c (vC T n t) (insert i ∅) ω) := by
      rw [show Fn T n t g = fun ω => g (walkVec c (vC T n t) ∅ ω) from rfl, e]
    rw [this, mul_pow]
    have hb := abs_cds_le hg (vs := [vC T n t i]) rfl
      (by intro w hw; simp at hw; rw [hw]; exact norm_cellVec_le T n t i) hc
      (walkVec c (vC T n t) (insert i ∅) ω)
    have : |cd c (vC T n t i) g (walkVec c (vC T n t) (insert i ∅) ω)| ≤ N 1 := by
      simpa [cds] using hb
    have h2 : cd c (vC T n t i) g (walkVec c (vC T n t) (insert i ∅) ω) ^ 2 ≤ N 1 ^ 2 := by
      rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) this 2
    exact mul_le_mul_of_nonneg_left h2 (sq_nonneg c)
  have hsum : ∑ i, E (fun ω => QE.OpenSto.Walsh.D i (Fn T n t g) ω ^ 2) ≤ T * N 1 ^ 2 := by
    calc ∑ i, E (fun ω => QE.OpenSto.Walsh.D i (Fn T n t g) ω ^ 2)
        ≤ ∑ _i : Fin n, c ^ 2 * N 1 ^ 2 := by
          refine Finset.sum_le_sum fun i _ => ?_
          rw [← QE.Chaos.avg_eq_E]
          exact QE.Chaos.avg_le_of_le fun ω => hD i ω
      _ = n * (c ^ 2 * N 1 ^ 2) := by simp
      _ = T * N 1 ^ 2 := by
          rw [Real.sq_sqrt (by positivity)]; field_simp
  exact div_le_div_of_nonneg_right hsum (Nat.cast_nonneg _)

/-- The same tail in terms of the Walsh levels: `∑_{M ≤ m ≤ n} E (Π_m F_n)² ≤ T N₁²/M`. -/
theorem chaos_tail_discrete_levels {n M : ℕ} (hM : 0 < M) {T : ℝ} (hT : 0 < T) (t : Fin p → ℝ)
    {g : (Fin p → ℝ) → ℝ} {N : ℕ → ℝ} (hg : DBnd g 1 N) (M' : ℕ) :
    ∑ m ∈ Finset.Ico M M', E (fun ω => QE.Chaos.Lift.piW m (Fn T n t g) ω ^ 2) ≤
      T * N 1 ^ 2 / M := by
  refine le_trans ?_ (chaos_tail_discrete (n := n) hM hT t hg)
  simp_rw [E_piW_sq]
  rw [← Finset.sum_biUnion]
  · refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun _ _ _ => sq_nonneg _)
    intro S hS
    simp only [Finset.mem_biUnion, Finset.mem_Ico, mem_powersetCard] at hS
    obtain ⟨m, ⟨hm1, -⟩, -, hc⟩ := hS
    simp only [Finset.mem_filter, mem_univ, true_and]; omega
  · intro m₁ _ m₂ _ hne
    simp only [Function.onFun]
    rw [Finset.disjoint_left]
    intro S h1 h2
    exact hne ((mem_powersetCard.1 h1).2.symm.trans (mem_powersetCard.1 h2).2)

end Tail

end QE.Chaos.Shadow

/-! # Part M. The cylinder functional on the Loeb space -/

namespace QE.Chaos.Shadow

open Finset QE.Chaos.Calc QE.Chaos.Loeb QE.Chaos.Lift QE.Chaos.Wiener QE.NSA MeasureTheory
  ProbabilityTheory Filter Topology ArchimedeanClass
open QE.OpenSto.Walsh (E coeff chi sgn)
open scoped NNReal

section Cylinder

variable {p : ℕ}

/-- The cylinder functional on paths, `Φ(x) = g(x(t_1), …, x(t_p))`. -/
def PhiCyl {T : ℝ} (t : Fin p → ℝ≥0) (htT : ∀ l, (t l : ℝ) ≤ T) (g : (Fin p → ℝ) → ℝ)
    (x : Set.Icc (0 : ℝ) T → ℝ) : ℝ :=
  g (fun l => x ⟨t l, (t l).2, htT l⟩)

theorem measurable_PhiCyl {T : ℝ} (t : Fin p → ℝ≥0) (htT : ∀ l, (t l : ℝ) ≤ T)
    {g : (Fin p → ℝ) → ℝ} (hg : Continuous g) : Measurable (PhiCyl t htT g) :=
  hg.measurable.comp (measurable_pi_iff.2 fun l => measurable_pi_apply _)

theorem PhiCyl_bpath {T : ℝ} (t : Fin p → ℝ≥0) (htT : ∀ l, (t l : ℝ) ≤ T) (g : (Fin p → ℝ) → ℝ)
    (n : ℕ → ℕ) (ω : Ult (ℕ → Bool)) :
    PhiCyl t htT g (bpath T n ω) = g (fun l => andersonB T n (t l) ω) := rfl

theorem abs_le_N0 {g : (Fin p → ℝ) → ℝ} {r : ℕ} {N : ℕ → ℝ} (hg : DBnd g r N) (x : Fin p → ℝ) :
    |g x| ≤ N 0 := by
  have := abs_dirD_le_unit hg (ws := []) (by simp) (by simp) x
  simpa [dirD] using this

variable {n : ℕ → ℕ} {T : ℝ}

theorem SInt_FN_sq {g : (Fin p → ℝ) → ℝ} {r : ℕ} {N : ℕ → ℝ} (hg : DBnd g r N)
    (t : Fin p → ℝ) : SInt n (fun k ω => FN T (n k) t g ω ^ 2) := by
  refine SInt_of_sq_finite ((isFinite_ofSeq_iff _).2 ⟨N 0 ^ 4, Eventually.of_forall fun k => ?_⟩)
  rw [← QE.Chaos.avg_eq_E]
  refine QE.Chaos.abs_avg_le_of_le fun ω => ?_
  show |(FN T (n k) t g ω ^ 2) ^ 2| ≤ N 0 ^ 4
  have h := abs_le_N0 hg (fineWalk T (n k) t ω)
  have : |(FN T (n k) t g ω ^ 2) ^ 2| = |g (fineWalk T (n k) t ω)| ^ 4 := by
    simp only [FN, abs_pow]; ring
  rw [this]; exact pow_le_pow_left₀ (abs_nonneg _) h 4

theorem ae_st_FN (hT : 0 < T) (hn : IsUnlimited ((n : ℕ → ℕ) : Ult ℕ)) (t : Fin p → ℝ≥0)
    (htT : ∀ l, (t l : ℝ) ≤ T) {g : (Fin p → ℝ) → ℝ} (hg : Continuous g) :
    ∀ᵐ ω ∂(L n), stdPart (iF n (fun k => FN T (n k) (fun l => (t l : ℝ)) g) ω) =
      PhiCyl t htT g (bpath T n ω) :=
  ae_st_walk hT hn t htT g hg

theorem memLp_PhiCyl (t : Fin p → ℝ≥0) (htT : ∀ l, (t l : ℝ) ≤ T) {g : (Fin p → ℝ) → ℝ}
    {r : ℕ} {N : ℕ → ℝ} (hg : DBnd g r N) :
    MemLp (fun ω => PhiCyl t htT g (bpath T n ω)) 2 (L n) := by
  refine MemLp.of_bound ?_ (N 0) (Eventually.of_forall fun ω => ?_)
  · exact ((measurable_PhiCyl t htT (continuous_dirD (ws := []) hg.1 (by simp))).comp
      (QE.Chaos.Dense.measurable_path (fun t => measurable_andersonB T n t) T)).aestronglyMeasurable
  · rw [Real.norm_eq_abs]; exact abs_le_N0 hg _

/-- **The lifting theorem for the cylinder functional**: `st Π_m F_N = Π_m Φ(b)` a.s. -/
theorem lifting_cyl (hT : 0 < T) (hn : IsUnlimited ((n : ℕ → ℕ) : Ult ℕ)) (t : Fin p → ℝ≥0)
    (htT : ∀ l, (t l : ℝ) ≤ T) {g : (Fin p → ℝ) → ℝ} {r : ℕ} {N : ℕ → ℝ} (hg : DBnd g r N)
    (m : ℕ) :
    SInt n (fun k ω => piI m (fun k => FN T (n k) (fun l => (t l : ℝ)) g) k ω ^ 2) ∧
      (fun ω => stdPart (iF n (piI m (fun k => FN T (n k) (fun l => (t l : ℝ)) g)) ω)) =ᵐ[L n]
        (Pi (L n) (T := T) (bproc T n) m
          (toL2 (L n) (fun ω => PhiCyl t htT g (bpath T n ω))) : Ult (ℕ → Bool) → ℝ) := by
  have hgc : Continuous g := continuous_dirD (ws := []) hg.1 (by simp)
  exact chaos_lifting hT hn (PhiCyl t htT g) (measurable_PhiCyl t htT hgc)
    (memLp_PhiCyl t htT hg) _ (SInt_FN_sq hg _) (ae_st_FN hT hn t htT hgc) m

theorem norm_sq_Lp (F : Lp ℝ 2 (L n)) : ‖F‖ ^ 2 = ∫ ω, (F : Ult (ℕ → Bool) → ℝ) ω ^ 2 ∂(L n) := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  refine integral_congr_ae (Eventually.of_forall fun ω => ?_)
  simp [sq]

theorem stdPart_sum_le {ι : Type*} (s : Finset ι) (x : ι → ℝ*) (hx : ∀ i ∈ s, IsFinite (x i)) :
    ∑ i ∈ s, stdPart (x i) = stdPart (∑ i ∈ s, x i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, ih fun i hi => hx i (Finset.mem_insert_of_mem hi)]
    have hfa := hx a (Finset.mem_insert_self a s)
    have hfs : IsFinite (∑ i ∈ s, x i) := by
      clear ih
      induction s using Finset.induction_on with
      | empty => simpa using (coe_isFinite (0 : ℝ))
      | insert b s hb ih2 =>
        rw [Finset.sum_insert hb]
        exact (hx b (Finset.mem_insert_of_mem (Finset.mem_insert_self b s))).add
          (ih2 (fun h => ha (Finset.mem_insert_of_mem h)) fun i hi => hx i (by
            rcases Finset.mem_insert.1 hi with rfl | hi
            · exact Finset.mem_insert_self _ _
            · exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hi)))
    exact (stdPart_add hfa hfs).symm

/-- **Item (iv), classical side**: the Wiener chaos tail of `Φ = g(b(t_1), …, b(t_p))` obeys the
same bound, `∑_{M ≤ m < M'} ‖Π_m Φ‖² ≤ T N₁² / M`. -/
theorem chaos_tail_classical (hT : 0 < T) (hn : IsUnlimited ((n : ℕ → ℕ) : Ult ℕ))
    (t : Fin p → ℝ≥0) (htT : ∀ l, (t l : ℝ) ≤ T) {g : (Fin p → ℝ) → ℝ} {N : ℕ → ℝ}
    (hg : DBnd g 1 N) {M : ℕ} (hM : 0 < M) (M' : ℕ) :
    ∑ m ∈ Finset.Ico M M', ‖Pi (L n) (T := T) (bproc T n) m
      (toL2 (L n) (fun ω => PhiCyl t htT g (bpath T n ω)))‖ ^ 2 ≤ T * N 1 ^ 2 / M := by
  set f := fun k => FN T (n k) (fun l => (t l : ℝ)) g
  have hterm : ∀ m, ‖Pi (L n) (T := T) (bproc T n) m
      (toL2 (L n) (fun ω => PhiCyl t htT g (bpath T n ω)))‖ ^ 2 =
        stdPart (iE n (fun k ω => piI m f k ω ^ 2)) := by
    intro m
    obtain ⟨hS, hae⟩ := lifting_cyl hT hn t htT hg m
    rw [norm_sq_Lp, ← integral_st_sq hS]
    refine integral_congr_ae ?_
    filter_upwards [hae] with ω hω; rw [hω]
  simp_rw [hterm]
  have hfin : ∀ m ∈ Finset.Ico M M', IsFinite (iE n (fun k ω => piI m f k ω ^ 2)) := by
    intro m _
    have := (lifting_cyl hT hn t htT hg m).1.1
    simpa only [abs_sq] using this
  rw [stdPart_sum_le _ _ hfin, ← iE_sum]
  have hle : iE n (fun k ω => ∑ m ∈ Finset.Ico M M', piI m f k ω ^ 2) ≤
      ((T * N 1 ^ 2 / M : ℝ) : ℝ*) := by
    unfold iE
    refine Hyperreal.ofSeq_le_ofSeq.2 (Eventually.of_forall fun k => ?_)
    dsimp only
    rw [QE.OpenSto.Walsh.E_sum]
    have e : f k = Fn T (n k) (fun l => (t l : ℝ)) g := by
      funext ω; simp only [f, FN, Fn, fineWalk_eq_walkVec]; rfl
    simp only [piI, e]
    exact chaos_tail_discrete_levels hM hT _ hg M'
  refine QE.Chaos.Loeb.stdPart_le_coe ?_ hle
  exact QE.Chaos.Loeb.isFinite_of_nonneg_le'
    (iE_nonneg fun k ω => Finset.sum_nonneg fun m _ => sq_nonneg _) hle (coe_isFinite _)

end Cylinder

section GaussLift

variable {T : ℝ} {n : ℕ} {Ns : ℕ → ℕ}

/-- The lattice times `jτ`, `j = 0, …, n`. -/
def latT (T : ℝ) (n : ℕ) (hT : 0 ≤ T) (i : Fin (n + 1)) : ℝ≥0 :=
  ⟨(i : ℝ) * (T / n), mul_nonneg (Nat.cast_nonneg _) (div_nonneg hT (Nat.cast_nonneg _))⟩

theorem latT_le (hT : 0 ≤ T) (hn : 0 < n) (i : Fin (n + 1)) : (latT T n hT i : ℝ) ≤ T := by
  simp only [latT, NNReal.coe_mk]
  have hi : (i : ℝ) ≤ n := by exact_mod_cast Nat.lt_succ_iff.1 i.isLt
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  calc (i : ℝ) * (T / n) ≤ n * (T / n) := mul_le_mul_of_nonneg_right hi (by positivity)
    _ = T := by field_simp

theorem latT_mono (hT : 0 ≤ T) : Monotone (latT T n hT) := by
  intro a b hab
  show (a : ℝ) * (T / n) ≤ (b : ℝ) * (T / n)
  exact mul_le_mul_of_nonneg_right (by exact_mod_cast hab) (div_nonneg hT (Nat.cast_nonneg _))

/-- The normalised Brownian increments `G_j = (b(t_{j+1}) - b(t_j))/√τ` on the time lattice. -/
def Gl (T : ℝ) (n : ℕ) (Ns : ℕ → ℕ) (ω : Ult (ℕ → Bool)) (j : Fin n) : ℝ :=
  (andersonB T Ns (((j : ℕ) + 1 : ℝ) * (T / n)) ω - andersonB T Ns ((j : ℝ) * (T / n)) ω) /
    √(T / n)

/-- The `G_j` are independent standard Gaussians. -/
theorem hasLaw_Gl (hT : 0 < T) (hn : 0 < n) (hNs : IsUnlimited ((Ns : ℕ → ℕ) : Ult ℕ)) :
    HasLaw (fun ω => Gl T n Ns ω) (Measure.pi fun _ => gaussianReal 0 1) (L Ns) := by
  have h := andersonB_increments_hasLaw hT hNs (latT T n hT.le) (latT_mono hT.le)
    (latT_le hT.le hn)
  set τ := T / n
  have hτ : 0 < τ := by positivity
  have e1 : ∀ i : Fin n, ((latT T n hT.le i.succ : ℝ)) = ((i : ℕ) + 1 : ℝ) * (T / n) := by
    intro i
    show ((i.succ : ℕ) : ℝ) * (T / n) = _
    rw [Fin.val_succ, Nat.cast_succ]
  have e0 : ∀ i : Fin n, ((latT T n hT.le i.castSucc : ℝ)) = (i : ℝ) * (T / n) := by
    intro i; rfl
  have hvar : ∀ i : Fin n, latT T n hT.le i.succ - latT T n hT.le i.castSucc =
      τ.toNNReal := by
    intro i
    apply NNReal.eq
    rw [NNReal.coe_sub (latT_mono hT.le (Fin.castSucc_le_succ i)), e1, e0,
      Real.coe_toNNReal _ hτ.le]
    simp only [τ]; ring
  simp_rw [hvar] at h
  set Y : (Fin n → ℝ) → (Fin n → ℝ) := fun x i => x i / √τ
  have hY : HasLaw Y (Measure.pi fun _ => gaussianReal 0 1)
      (Measure.pi fun _ : Fin n => gaussianReal 0 τ.toNNReal) := by
    have hm : Measurable Y := measurable_pi_iff.2 fun i => (measurable_pi_apply i).div_const _
    refine ⟨hm.aemeasurable, ?_⟩
    show Measure.map (fun (x : Fin n → ℝ) i => (fun (_ : Fin n) (y : ℝ) => y / √τ) i (x i)) _ = _
    rw [Measure.pi_map_pi (f := fun (_ : Fin n) (y : ℝ) => y / √τ)
      (fun i => (measurable_id.div_const _).aemeasurable)]
    congr 1; funext i
    rw [gaussianReal_map_div_const]
    congr 1
    · simp
    · apply NNReal.eq
      rw [NNReal.coe_div, Real.coe_toNNReal _ hτ.le]
      show τ / (√τ ^ 2) = 1
      rw [Real.sq_sqrt hτ.le]; field_simp
  have := hY.comp h
  refine this.congr (Eventually.of_forall fun ω => ?_)
  funext j
  simp only [Function.comp, Y, Gl]
  rw [e1, e0]

end GaussLift

section ZetaWalk

variable {T : ℝ} {n : ℕ}

theorem walkIdx_latT (hT : 0 < T) (hn : 0 < n) (q : ℕ) (hq : 0 < q) (i : ℕ) :
    walkIdx T (n * q) ((i : ℝ) * (T / n)) = i * q := by
  unfold walkIdx
  have : (i : ℝ) * (T / n) / (T / ((n * q : ℕ) : ℝ)) = ((i * q : ℕ) : ℝ) := by
    push_cast; field_simp
  rw [this, Nat.floor_natCast]

theorem walkVec_latT (hT : 0 < T) (hn : 0 < n) (q : ℕ) (hq : 0 < q) (η : Fin (n * q) → Bool)
    (i : Fin (n + 1)) :
    QE.Chaos.Loeb.walkVec T (n * q) (latT T n hT.le) η i =
      √(T / ((n * q : ℕ) : ℝ)) * ∑ x ∈ univ.filter (fun x : Fin (n * q) => (x : ℕ) < (i : ℕ) * q),
        (sgn (η x) : ℝ) := by
  unfold QE.Chaos.Loeb.walkVec
  rw [show ((latT T n hT.le i : ℝ≥0) : ℝ) = (i : ℝ) * (T / n) from rfl,
    walkIdx_latT hT hn q hq i]

/-- The normalised block sums are the normalised walk increments on the time lattice. -/
theorem zeta_eq_walk (hT : 0 < T) (hn : 0 < n) (q : ℕ) (hq : 0 < q) (η : Fin (n * q) → Bool)
    (j : Fin n) :
    zeta n q η j = (QE.Chaos.Loeb.walkVec T (n * q) (latT T n hT.le) η j.succ -
      QE.Chaos.Loeb.walkVec T (n * q) (latT T n hT.le) η j.castSucc) / √(T / n) := by
  rw [walkVec_latT hT hn q hq, walkVec_latT hT hn q hq, ← mul_sub, Fin.val_succ,
    Fin.val_castSucc, QE.Chaos.Shadow.k_sum_block, zeta]
  have hq' : (0 : ℝ) < q := by exact_mod_cast hq
  have hτ : 0 < T / n := by positivity
  have e : √(T / ((n * q : ℕ) : ℝ)) = √(T / n) / √q := by
    rw [← Real.sqrt_div' _ hq'.le]; congr 1; push_cast; field_simp
  rw [e]
  have h1 : √(T / n) ≠ 0 := (Real.sqrt_pos.2 hτ).ne'
  have h2 : √(q : ℝ) ≠ 0 := (Real.sqrt_pos.2 hq').ne'
  field_simp

/-- Shadows of functionals of the normalised block sums: `st H(ζ) = H(G)` a.s. -/
theorem ae_st_zeta (hT : 0 < T) (hn : 0 < n) (H : (Fin n → ℝ) → ℝ) (hH : Continuous H) :
    ∀ᵐ ω ∂(L (fun k => n * (k + 1))),
      stdPart (iF (fun k => n * (k + 1)) (fun k η => H (zeta n (k + 1) η)) ω) =
        H (Gl T n (fun k => n * (k + 1)) ω) := by
  set Ns : ℕ → ℕ := fun k => n * (k + 1)
  have hNs : IsUnlimited ((Ns : ℕ → ℕ) : Ult ℕ) := isUnlimited_mul_succ hn
  set h : (Fin (n + 1) → ℝ) → ℝ := fun x => H (fun j => (x j.succ - x j.castSucc) / √(T / n))
  have hh : Continuous h := hH.comp (continuous_pi fun j =>
    ((continuous_apply j.succ).sub (continuous_apply j.castSucc)).div_const _)
  have hw := ae_st_walk hT hNs (latT T n hT.le) (latT_le hT.le hn) h hh
  filter_upwards [hw] with ω hω
  have e : (fun k (η : Fin (Ns k) → Bool) => H (zeta n (k + 1) η)) =
      fun k η => h (QE.Chaos.Loeb.walkVec T (Ns k) (latT T n hT.le) η) := by
    funext k η
    simp only [h]
    congr 1; funext j
    exact zeta_eq_walk hT hn (k + 1) (Nat.succ_pos k) η j
  rw [e, hω]
  simp only [h, Gl]
  congr 1; funext j
  rw [show ((latT T n hT.le j.succ : ℝ≥0) : ℝ) = ((j : ℕ) + 1 : ℝ) * (T / n) by
    show ((j.succ : ℕ) : ℝ) * (T / n) = _; rw [Fin.val_succ, Nat.cast_succ]]
  rfl

end ZetaWalk

end QE.Chaos.Shadow

/-! # Part N. The L² shadow and the comparison of laws -/

namespace QE.Chaos.Shadow

open Finset QE.Chaos.Calc QE.Chaos.Loeb QE.Chaos.Lift QE.Chaos.Wiener QE.Chaos.Bon QE.NSA
  MeasureTheory ProbabilityTheory Filter Topology ArchimedeanClass
open QE.OpenSto.Walsh (E coeff chi sgn)
open scoped NNReal

section L2Zero

variable {p : ℕ}

theorem liftI_zero {n : ℕ} (F : (Fin n → Bool) → ℝ) (x : Fin n → ℝ) :
    liftI 0 F x = E F := by
  simp [liftI, QE.OpenSto.Walsh.coeff_empty]

theorem piW_zero {N : ℕ} (F : (Fin N → Bool) → ℝ) (ω : Fin N → Bool) :
    piW 0 F ω = E F := by
  simp [piW, QE.OpenSto.Walsh.coeff_empty, QE.OpenSto.Walsh.chi]

theorem Cker_nonneg {m : ℕ} {T : ℝ} (hT : 0 < T) {N : ℕ → ℝ} (hN2 : 0 ≤ N (m + 2))
    (hN4 : 0 ≤ N (m + 4)) : 0 ≤ Cker p m T N := by
  unfold Cker; positivity

/-- The level `m = 0` of the `L²` estimate: `(E F_n - E F_N)² ≤ A_0 τ`. -/
theorem l2_core0 {n q : ℕ} (hn : 0 < n) (hq : 0 < q) {T : ℝ} (hT : 0 < T) (hτ : T / n ≤ 1)
    (t : Fin p → ℝ) (ht0 : ∀ l, 0 ≤ t l) {g : (Fin p → ℝ) → ℝ} {N : ℕ → ℝ}
    (hg : DBnd g 4 N) :
    E (fun ω : Fin (n * q) → Bool =>
        (liftI 0 (Fn T n t g) (zeta n q ω) - piW 0 (FN T (n * q) t g) ω) ^ 2) ≤
      Al2 p 0 T N * (T / n) := by
  simp_rw [liftI_zero, piW_zero]
  rw [← QE.Chaos.avg_eq_E, QE.Chaos.avg_const]
  have hk := kernel_coin_bound (m := 0) hn hq hT t ht0 (by simpa using hg) [] (by simp) rfl
  simp only [List.map_nil, cds, List.toFinset_nil, dirD] at hk
  have e1 : E (fun ω : Fin n → Bool => g (walkVec √(T / n) (fun j : Fin n => cellVec T n t j) ∅ ω))
      = E (Fn T n t g) := rfl
  have e2 : E (fun ω : Fin (n * q) → Bool => g (fineWalk T (n * q) t ω)) =
      E (FN T (n * q) t g) := rfl
  rw [e1, e2] at hk
  have hτ0 : 0 ≤ T / n := by positivity
  have hC : 0 ≤ Cker p 0 T N := Cker_nonneg hT (hg.2.1 2 (by norm_num)) (hg.2.1 4 le_rfl)
  have hA : Al2 p 0 T N = Cker p 0 T N ^ 2 := by simp [Al2, Ck']
  rw [hA]
  have h2 : (E (Fn T n t g) - E (FN T (n * q) t g)) ^ 2 ≤ (Cker p 0 T N * (T / n)) ^ 2 := by
    rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hk 2
  calc _ ≤ (Cker p 0 T N * (T / n)) ^ 2 := h2
    _ = Cker p 0 T N ^ 2 * (T / n) * (T / n) := by ring
    _ ≤ Cker p 0 T N ^ 2 * (T / n) * 1 :=
        mul_le_mul_of_nonneg_left hτ (by positivity)
    _ = _ := mul_one _

/-- The `L²` core estimate at every level `m`. -/
theorem l2_core_all {m n q : ℕ} (hn : 0 < n) (hq : 0 < q) {T : ℝ} (hT : 0 < T)
    (hτ : T / n ≤ 1) (t : Fin p → ℝ) (ht0 : ∀ l, 0 ≤ t l) {g : (Fin p → ℝ) → ℝ}
    {N : ℕ → ℝ} (hg : DBnd g (m + 4) N) :
    E (fun ω : Fin (n * q) → Bool =>
        (liftI m (Fn T n t g) (zeta n q ω) - piW m (FN T (n * q) t g) ω) ^ 2) ≤
      Al2 p m T N * (T / n) := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · exact l2_core0 hn hq hT hτ t ht0 (by simpa using hg)
  · exact l2_core hm hn hq hT hτ t ht0 hg

end L2Zero

section L2Shadow

variable {p : ℕ}

theorem continuous_liftI {n : ℕ} (m : ℕ) (F : (Fin n → Bool) → ℝ) : Continuous (liftI m F) := by
  have : liftI m F = mlEval (fun S => if S.card = m then coeff F S else 0) := by
    funext x; exact k_liftI_eq m F x
  rw [this]; exact k_continuous_mlEval _

theorem sum_chaos_coeff_sq_le {n : ℕ} (m : ℕ) (F : (Fin n → Bool) → ℝ) {C : ℝ}
    (hC : ∀ ω, |F ω| ≤ C) :
    ∑ S, (if S.card = m then coeff F S else 0) ^ 2 ≤ C ^ 2 := by
  have hp := QE.OpenSto.Walsh.parseval F F
  simp_rw [← sq] at hp
  calc ∑ S, (if S.card = m then coeff F S else 0) ^ 2 ≤ ∑ S, coeff F S ^ 2 :=
        Finset.sum_le_sum fun S _ => by split_ifs <;> simp [sq_nonneg]
    _ = E (fun ω => F ω ^ 2) := hp.symm
    _ ≤ C ^ 2 := by
        rw [← QE.Chaos.avg_eq_E]
        refine QE.Chaos.avg_le_of_le fun ω => ?_
        rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (hC ω) 2

/-- The internal Gaussian-lift approximant `X̃ = Π_m F_n(ζ)` has S-integrable square. -/
theorem SInt_liftI_zeta_sq {n : ℕ} (m : ℕ) (F : (Fin n → Bool) → ℝ) {C : ℝ}
    (hC : ∀ ω, |F ω| ≤ C) :
    SInt (fun k => n * (k + 1)) (fun k η => liftI m F (zeta n (k + 1) η) ^ 2) := by
  refine SInt_of_sq_finite ((isFinite_ofSeq_iff _).2 ⟨9 ^ m * (C ^ 2) ^ 2,
    Eventually.of_forall fun k => ?_⟩)
  set a : Finset (Fin n) → ℝ := fun S => if S.card = m then coeff F S else 0
  have h4 := E_fine_four_le (n := n) (Nat.succ_pos k) a (degLe_chaos F m)
  have hs := sum_chaos_coeff_sq_le m F hC
  rw [← QE.Chaos.avg_eq_E]
  refine (QE.Chaos.abs_avg_le _).trans ?_
  rw [QE.Chaos.avg_eq_E]
  have e : (fun η : Fin (n * (k + 1)) → Bool => |(liftI m F (zeta n (k + 1) η) ^ 2) ^ 2|) =
      fun η => mlEval a (zeta n (k + 1) η) ^ 4 := by
    funext η; rw [k_liftI_eq, abs_of_nonneg (by positivity)]; ring
  rw [show (fun η : Fin ((fun k => n * (k + 1)) k) → Bool =>
      |(liftI m F (zeta n (k + 1) η) ^ 2) ^ 2|) = _ from e]
  refine le_trans (le_of_eq_of_le rfl h4) ?_
  have h0 : 0 ≤ ∑ S, a S ^ 2 := Finset.sum_nonneg fun S _ => sq_nonneg _
  gcongr

/-- The Loeb transfer of a uniform internal `L²` bound between the Gaussian-lift approximant and
the fine Walsh level. -/
theorem chaos_L2_of_core {m n : ℕ} (hn : 0 < n) {T : ℝ} (hT : 0 < T)
    (t : Fin p → ℝ≥0) (htT : ∀ l, (t l : ℝ) ≤ T) {g : (Fin p → ℝ) → ℝ}
    {N : ℕ → ℝ} (hg : DBnd g (m + 4) N) {A : ℝ}
    (hcore : ∀ q : ℕ, 0 < q → E (fun ω : Fin (n * q) → Bool =>
        (liftI m (Fn T n (fun l => (t l : ℝ)) g) (zeta n q ω) -
          piW m (FN T (n * q) (fun l => (t l : ℝ)) g) ω) ^ 2) ≤ A) :
    ‖toL2 (L (fun k => n * (k + 1)))
        (fun ω => liftI m (Fn T n (fun l => (t l : ℝ)) g) (Gl T n (fun k => n * (k + 1)) ω)) -
      Pi (L (fun k => n * (k + 1))) (T := T) (bproc T (fun k => n * (k + 1))) m
        (toL2 (L (fun k => n * (k + 1)))
          (fun ω => PhiCyl t htT g (bpath T (fun k => n * (k + 1)) ω)))‖ ≤ √A := by
  set Ns : ℕ → ℕ := fun k => n * (k + 1)
  have hNs : IsUnlimited ((Ns : ℕ → ℕ) : Ult ℕ) := isUnlimited_mul_succ hn
  set tR : Fin p → ℝ := fun l => (t l : ℝ)
  set F := Fn T n tR g
  set f : ∀ k, (Fin (Ns k) → Bool) → ℝ := fun k => FN T (Ns k) tR g
  obtain ⟨hS, hae⟩ := lifting_cyl hT hNs t htT hg m
  have hFb : ∀ ω, |F ω| ≤ N 0 := fun ω => abs_le_N0 hg _
  set X : ∀ k, (Fin (Ns k) → Bool) → ℝ := fun k η => liftI m F (zeta n (k + 1) η)
  have hX2 : SInt Ns (fun k η => X k η ^ 2) := SInt_liftI_zeta_sq m F hFb
  have hXst := ae_st_zeta hT hn (liftI m F) (continuous_liftI m F)
  have hu : MemLp (fun ω => liftI m F (Gl T n Ns ω)) 2 (L Ns) :=
    (memLp_st hX2).ae_eq (by filter_upwards [hXst] with ω h; exact h)
  set v := Pi (L Ns) (T := T) (bproc T Ns) m
    (toL2 (L Ns) (fun ω => PhiCyl t htT g (bpath T Ns ω)))
  have hv2 : MemLp (v : Ult (ℕ → Bool) → ℝ) 2 (L Ns) := Lp.memLp v
  have hvv : toL2 (L Ns) (v : Ult (ℕ → Bool) → ℝ) = v := by
    rw [toL2_of_memLp _ hv2]; exact Lp.toLp_coeFn v hv2
  have hdiff : SInt Ns (fun k η => (X k η - piI m f k η) ^ 2) := by
    refine ((hX2.add hS).const_mul 2).mono fun k η => ?_
    rw [abs_sq]; nlinarith [sq_nonneg (X k η + piI m f k η)]
  have hsq : ‖toL2 (L Ns) (fun ω => liftI m F (Gl T n Ns ω)) - v‖ ^ 2 ≤ A := by
    rw [← hvv, norm_toL2_sub_sq hu hv2]
    have h1 : ∫ ω, (liftI m F (Gl T n Ns ω) - (v : Ult (ℕ → Bool) → ℝ) ω) ^ 2 ∂(L Ns) =
        stdPart (iE Ns (fun k η => (X k η - piI m f k η) ^ 2)) := by
      rw [← integral_st_sq hdiff]
      refine integral_congr_ae ?_
      filter_upwards [hXst, hae, hX2.ae_isFinite_of_sq, hS.ae_isFinite_of_sq] with ω h1 h2 h3 h4
      rw [iF_sub, stdPart_sub' h3 h4]
      simp only [X] at h1 ⊢
      rw [h1, ← h2]
    rw [h1]
    have hle : iE Ns (fun k η => (X k η - piI m f k η) ^ 2) ≤ ((A : ℝ) : ℝ*) := by
      unfold iE
      exact Hyperreal.ofSeq_le_ofSeq.2 (Eventually.of_forall fun k => hcore (k + 1) (Nat.succ_pos k))
    have hfin : IsFinite (iE Ns (fun k η => (X k η - piI m f k η) ^ 2)) := by
      simpa only [abs_sq] using hdiff.1
    exact QE.Chaos.Loeb.stdPart_le_coe hfin hle
  exact Real.le_sqrt_of_sq_le hsq

/-- **Item (ii) of the shadow theorem: the Gaussian lift in `L²`.**  On the Loeb space of the walk
with `n (k+1)` coins (`b` its Brownian shadow, `G_j = Δb_j/√τ` on the coarse lattice),
`‖Π_m F̃_n - Π_m Φ‖_{L²} ≤ √(A_m τ)`, `Φ = g(b(t_1), …, b(t_p))`. -/
theorem chaos_L2_shadow {m n : ℕ} (hn : 0 < n) {T : ℝ} (hT : 0 < T)
    (hτ : T / n ≤ 1) (t : Fin p → ℝ≥0) (htT : ∀ l, (t l : ℝ) ≤ T) {g : (Fin p → ℝ) → ℝ}
    {N : ℕ → ℝ} (hg : DBnd g (m + 4) N) :
    ‖toL2 (L (fun k => n * (k + 1)))
        (fun ω => liftI m (Fn T n (fun l => (t l : ℝ)) g) (Gl T n (fun k => n * (k + 1)) ω)) -
      Pi (L (fun k => n * (k + 1))) (T := T) (bproc T (fun k => n * (k + 1))) m
        (toL2 (L (fun k => n * (k + 1)))
          (fun ω => PhiCyl t htT g (bpath T (fun k => n * (k + 1)) ω)))‖ ≤
      √(Al2 p m T N * (T / n)) :=
  chaos_L2_of_core hn hT t htT hg fun q hq =>
    l2_core_all hn hq hT hτ _ (fun l => (t l).2) hg

/-- Item (ii) on the time lattice: if every `t_l` is a lattice time, the boundary term `m p`
drops out. -/
theorem chaos_L2_shadow_lattice {m n : ℕ} (hm : 1 ≤ m) (hn : 0 < n) {T : ℝ} (hT : 0 < T)
    (hτ : T / n ≤ 1) (t : Fin p → ℝ≥0) (htT : ∀ l, (t l : ℝ) ≤ T)
    (hlat : ∀ l, (walkIdx T n (t l) : ℝ) * (T / n) = t l) {g : (Fin p → ℝ) → ℝ}
    {N : ℕ → ℝ} (hg : DBnd g (m + 4) N) :
    ‖toL2 (L (fun k => n * (k + 1)))
        (fun ω => liftI m (Fn T n (fun l => (t l : ℝ)) g) (Gl T n (fun k => n * (k + 1)) ω)) -
      Pi (L (fun k => n * (k + 1))) (T := T) (bproc T (fun k => n * (k + 1))) m
        (toL2 (L (fun k => n * (k + 1)))
          (fun ω => PhiCyl t htT g (bpath T (fun k => n * (k + 1)) ω)))‖ ≤
      √((Ck' p m T N ^ 2 * T ^ m / m.factorial +
        4 * (m.choose 2 : ℝ) * T ^ (m - 1) * N m ^ 2) * (T / n)) :=
  chaos_L2_of_core hn hT t htT hg fun q hq =>
    l2_core_lattice hm hn hq hT hτ _ (fun l => (t l).2) hlat hg

/-- Item (ii), `m = 1` on the time lattice: the bound is `C_1 √T τ`. -/
theorem chaos_L2_shadow_one_lattice {n : ℕ} (hn : 0 < n) {T : ℝ} (hT : 0 < T)
    (t : Fin p → ℝ≥0) (htT : ∀ l, (t l : ℝ) ≤ T)
    (hlat : ∀ l, (walkIdx T n (t l) : ℝ) * (T / n) = t l) {g : (Fin p → ℝ) → ℝ}
    {N : ℕ → ℝ} (hg : DBnd g (1 + 4) N) :
    ‖toL2 (L (fun k => n * (k + 1)))
        (fun ω => liftI 1 (Fn T n (fun l => (t l : ℝ)) g) (Gl T n (fun k => n * (k + 1)) ω)) -
      Pi (L (fun k => n * (k + 1))) (T := T) (bproc T (fun k => n * (k + 1))) 1
        (toL2 (L (fun k => n * (k + 1)))
          (fun ω => PhiCyl t htT g (bpath T (fun k => n * (k + 1)) ω)))‖ ≤
      |Ck' p 1 T N| * √T * (T / n) := by
  have h := chaos_L2_of_core (m := 1) hn hT t htT hg fun q hq =>
    l2_core_one_lattice hn hq hT _ (fun l => (t l).2) hlat hg
  refine h.trans (le_of_eq ?_)
  have hτ : 0 ≤ T / n := by positivity
  rw [show Ck' p 1 T N ^ 2 * T * (T / n) ^ 2 = (|Ck' p 1 T N| * √T * (T / n)) ^ 2 by
    rw [mul_pow, mul_pow, sq_abs, Real.sq_sqrt hT.le]]
  exact Real.sqrt_sq (by positivity)

end L2Shadow

section LawShadow

variable {p : ℕ}

theorem integral_abs_le_sqrt {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {f : Ω → ℝ} (hf : MemLp f 2 P) :
    ∫ ω, |f ω| ∂P ≤ √(∫ ω, f ω ^ 2 ∂P) := by
  have hi1 : Integrable (fun ω => |f ω|) P := (hf.integrable one_le_two).abs
  have hi2 : Integrable (fun ω => f ω ^ 2) P := hf.integrable_sq
  set c := ∫ ω, |f ω| ∂P
  have h0 : 0 ≤ ∫ ω, (|f ω| - c) ^ 2 ∂P := integral_nonneg fun ω => sq_nonneg _
  have e : ∫ ω, (|f ω| - c) ^ 2 ∂P = ∫ ω, f ω ^ 2 ∂P - c ^ 2 := by
    have : (fun ω => (|f ω| - c) ^ 2) = fun ω => f ω ^ 2 - 2 * c * |f ω| + c ^ 2 := by
      funext ω; rw [sub_sq, sq_abs]; ring
    rw [this, integral_add (f := fun ω => f ω ^ 2 - 2 * c * |f ω|) (g := fun _ => c ^ 2)
      (hi2.sub (hi1.const_mul _)) (integrable_const _),
      integral_sub (f := fun ω => f ω ^ 2) (g := fun ω => 2 * c * |f ω|) hi2 (hi1.const_mul _),
      integral_const_mul, integral_const]
    simp; ring
  rw [e] at h0
  exact Real.le_sqrt_of_sq_le (by linarith)

/-- **Item (iii) of the shadow theorem, comparison with the Wiener chaos.**  For `Ψ ∈ C⁴` with
`|Ψ⁽⁴⁾| ≤ B` and Lipschitz with constant `Lc`,
`|E Ψ(Π_m F_n) - E Ψ(Π_m Φ)| ≤ (B/6) 9^{m-1} T K_m² τ + Lc √(A_m τ)`. -/
theorem chaos_law_shadow4 {m n : ℕ} (hm : 1 ≤ m) (hn : 0 < n) {T : ℝ} (hT : 0 < T)
    (hτ : T / n ≤ 1) (t : Fin p → ℝ≥0) (htT : ∀ l, (t l : ℝ) ≤ T) {g : (Fin p → ℝ) → ℝ}
    {N : ℕ → ℝ} (hg : DBnd g (m + 4) N) (Ψ : ℝ → ℝ) (hΨ : ContDiff ℝ 4 Ψ) {B : ℝ}
    (hB : ∀ x, |iteratedDeriv 4 Ψ x| ≤ B) {Lc : ℝ≥0} (hL : LipschitzWith Lc Ψ) :
    Integrable (fun ω => Ψ ((Pi (L (fun k => n * (k + 1))) (T := T)
        (bproc T (fun k => n * (k + 1))) m (toL2 (L (fun k => n * (k + 1)))
          (fun ω => PhiCyl t htT g (bpath T (fun k => n * (k + 1)) ω))) :
            Ult (ℕ → Bool) → ℝ) ω)) (L (fun k => n * (k + 1))) ∧
    |E (fun η : Fin n → Bool => Ψ (liftI m (Fn T n (fun l => (t l : ℝ)) g) (fun j => sgn (η j)))) -
      ∫ ω, Ψ ((Pi (L (fun k => n * (k + 1))) (T := T) (bproc T (fun k => n * (k + 1))) m
        (toL2 (L (fun k => n * (k + 1)))
          (fun ω => PhiCyl t htT g (bpath T (fun k => n * (k + 1)) ω))) :
            Ult (ℕ → Bool) → ℝ) ω) ∂(L (fun k => n * (k + 1)))| ≤
      B / 6 * 9 ^ (m - 1) * T * Km T m N ^ 2 * (T / n) + Lc * √(Al2 p m T N * (T / n)) := by
  set Ns : ℕ → ℕ := fun k => n * (k + 1)
  have hNs : IsUnlimited ((Ns : ℕ → ℕ) : Ult ℕ) := isUnlimited_mul_succ hn
  set tR : Fin p → ℝ := fun l => (t l : ℝ)
  set F := Fn T n tR g
  set v := Pi (L Ns) (T := T) (bproc T Ns) m
    (toL2 (L Ns) (fun ω => PhiCyl t htT g (bpath T Ns ω)))
  set w : Ult (ℕ → Bool) → ℝ := (v : Ult (ℕ → Bool) → ℝ)
  set u : Ult (ℕ → Bool) → ℝ := fun ω => liftI m F (Gl T n Ns ω)
  have hG := hasLaw_Gl hT hn hNs
  obtain ⟨hiu, hlaw⟩ := law_chaos_gauss4 hm hn hT tR (hg.mono (by omega)) Ψ hΨ hB hG
  have hw2 : MemLp w 2 (L Ns) := Lp.memLp v
  have hu2 : MemLp u 2 (L Ns) := by
    have hX2 := SInt_liftI_zeta_sq m F (fun ω => abs_le_N0 hg _)
    exact (memLp_st hX2).ae_eq (by
      filter_upwards [ae_st_zeta hT hn (liftI m F) (continuous_liftI m F)] with ω h; exact h)
  have hiw : Integrable (fun ω => Ψ (w ω)) (L Ns) := by
    refine Integrable.mono' (g := fun ω => |Ψ 0| + Lc * |w ω|)
      ((integrable_const _).add ((hw2.integrable one_le_two).abs.const_mul _))
      (hL.continuous.measurable.comp_aemeasurable hw2.aestronglyMeasurable.aemeasurable).aestronglyMeasurable
      (Eventually.of_forall fun ω => ?_)
    have := hL.dist_le_mul (w ω) 0
    rw [Real.dist_eq, Real.dist_eq, sub_zero] at this
    rw [Real.norm_eq_abs]
    calc |Ψ (w ω)| ≤ |Ψ 0| + |Ψ (w ω) - Ψ 0| := by
          have := abs_sub_abs_le_abs_sub (Ψ (w ω)) (Ψ 0); linarith
      _ ≤ |Ψ 0| + Lc * |w ω| := by linarith
  refine ⟨hiw, ?_⟩
  have hL2 := chaos_L2_shadow hn hT hτ t htT hg
  have hdiff : |∫ ω, Ψ (u ω) ∂(L Ns) - ∫ ω, Ψ (w ω) ∂(L Ns)| ≤ Lc * √(Al2 p m T N * (T / n)) := by
    rw [← integral_sub hiu hiw]
    refine (abs_integral_le_integral_abs).trans ?_
    have hpt : ∀ ω, |Ψ (u ω) - Ψ (w ω)| ≤ Lc * |u ω - w ω| := by
      intro ω
      have := hL.dist_le_mul (u ω) (w ω)
      rwa [Real.dist_eq, Real.dist_eq] at this
    have hint : Integrable (fun ω => |u ω - w ω|) (L Ns) :=
      ((hu2.sub hw2).integrable one_le_two).abs
    calc ∫ ω, |Ψ (u ω) - Ψ (w ω)| ∂(L Ns) ≤ ∫ ω, Lc * |u ω - w ω| ∂(L Ns) :=
          integral_mono ((hiu.sub hiw).abs) (hint.const_mul _) hpt
      _ = Lc * ∫ ω, |u ω - w ω| ∂(L Ns) := integral_const_mul _ _
      _ ≤ Lc * √(∫ ω, (u ω - w ω) ^ 2 ∂(L Ns)) :=
          mul_le_mul_of_nonneg_left (integral_abs_le_sqrt (hu2.sub hw2)) Lc.2
      _ ≤ Lc * √(Al2 p m T N * (T / n)) := by
          refine mul_le_mul_of_nonneg_left ?_ Lc.2
          have hvv : toL2 (L Ns) w = v := by
            rw [toL2_of_memLp _ hw2]; exact Lp.toLp_coeFn v hw2
          have := norm_toL2_sub_sq hu2 hw2
          rw [hvv] at this
          rw [← this, Real.sqrt_sq (norm_nonneg _)]
          exact hL2
  calc _ = |(E (fun η : Fin n → Bool => Ψ (liftI m F (fun j => sgn (η j)))) - ∫ ω, Ψ (u ω) ∂(L Ns)) +
        (∫ ω, Ψ (u ω) ∂(L Ns) - ∫ ω, Ψ (w ω) ∂(L Ns))| := by ring_nf
    _ ≤ _ := abs_add_le _ _
    _ ≤ _ := add_le_add hlaw hdiff

end LawShadow

end QE.Chaos.Shadow

/-! # Part O. The full Gaussian lift -/

namespace QE.Chaos.Shadow

open Finset QE.Chaos.Calc QE.Chaos.Loeb QE.Chaos.Lift QE.Chaos.Wiener QE.Chaos.Bon QE.NSA
  MeasureTheory ProbabilityTheory Filter Topology ArchimedeanClass
open QE.OpenSto.Walsh (E coeff chi sgn)
open scoped NNReal

section Total

variable {p : ℕ}

/-- The internal approximant of a sum of Walsh levels evaluated at the block sums. -/
theorem sum_liftI_eq_mlEval {n : ℕ} (I : Finset ℕ) (F : (Fin n → Bool) → ℝ) (x : Fin n → ℝ) :
    ∑ m ∈ I, liftI m F x = mlEval (fun S => if S.card ∈ I then coeff F S else 0) x := by
  simp_rw [k_liftI_eq]
  unfold mlEval
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro S _
  rw [← Finset.sum_mul]
  congr 1
  dsimp only
  by_cases h : S.card ∈ I
  · rw [if_pos h, Finset.sum_eq_single S.card (fun b _ hb => by rw [if_neg (Ne.symm hb)])
      (fun h' => absurd h h'), if_pos rfl]
  · rw [if_neg h]; exact Finset.sum_eq_zero fun b hb => by
      rw [if_neg]; rintro rfl; exact h hb

/-- `‖∑_{m ∈ I} Π_m F̃_n‖² = ∑_{|S| ∈ I} F̂_n(S)²`: the Gaussian monomials are orthonormal. -/
theorem norm_sq_sum_lift {n : ℕ} (hn : 0 < n) {T : ℝ} (hT : 0 < T) (I : Finset ℕ)
    (F : (Fin n → Bool) → ℝ) {C : ℝ} (hC : ∀ ω, |F ω| ≤ C) :
    MemLp (fun ω => ∑ m ∈ I, liftI m F (Gl T n (fun k => n * (k + 1)) ω)) 2
        (L (fun k => n * (k + 1))) ∧
      ∫ ω, (∑ m ∈ I, liftI m F (Gl T n (fun k => n * (k + 1)) ω)) ^ 2 ∂(L (fun k => n * (k + 1)))
        = ∑ S ∈ univ.filter (fun S : Finset (Fin n) => S.card ∈ I), coeff F S ^ 2 := by
  set Ns : ℕ → ℕ := fun k => n * (k + 1)
  set a : Finset (Fin n) → ℝ := fun S => if S.card ∈ I then coeff F S else 0
  set X : ∀ k, (Fin (Ns k) → Bool) → ℝ := fun k η => mlEval a (zeta n (k + 1) η)
  have hX : SInt Ns (fun k η => X k η ^ 2) := by
    have := SInt_sq_sum I (fun m k η => liftI m F (zeta n (k + 1) η))
      (fun m _ => SInt_liftI_zeta_sq m F hC)
    refine this.mono fun k η => ?_
    rw [abs_sq]; simp only [X, a]; rw [← sum_liftI_eq_mlEval]
  have hst := ae_st_zeta hT hn (mlEval a) (k_continuous_mlEval a)
  have hmem : MemLp (fun ω => ∑ m ∈ I, liftI m F (Gl T n Ns ω)) 2 (L Ns) := by
    refine (memLp_st hX).ae_eq ?_
    filter_upwards [hst] with ω h
    rw [sum_liftI_eq_mlEval]; exact h
  refine ⟨hmem, ?_⟩
  have e1 : ∫ ω, (∑ m ∈ I, liftI m F (Gl T n Ns ω)) ^ 2 ∂(L Ns) =
      stdPart (iE Ns (fun k η => X k η ^ 2)) := by
    rw [← integral_st_sq hX]
    refine integral_congr_ae ?_
    filter_upwards [hst] with ω h
    rw [sum_liftI_eq_mlEval, ← h]
  rw [e1]
  have e2 : iE Ns (fun k η => X k η ^ 2) =
      ((∑ S ∈ univ.filter (fun S : Finset (Fin n) => S.card ∈ I), coeff F S ^ 2 : ℝ) : ℝ*) := by
    unfold iE
    have : ∀ k, E (fun η : Fin (Ns k) → Bool => X k η ^ 2) =
        ∑ S ∈ univ.filter (fun S : Finset (Fin n) => S.card ∈ I), coeff F S ^ 2 := by
      intro k
      have := E_fine_sq (n := n) (Nat.succ_pos k) a
      refine (le_antisymm (le_of_eq_of_le rfl this.le) (le_of_le_of_eq this.ge rfl)).trans ?_
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl; intro S _; simp only [a]; split_ifs <;> simp
    simp_rw [this]; rfl
  rw [e2, Hyperreal.stdPart_coe]

end Total

section Total2

variable {p : ℕ}

theorem toL2_mem_expoSpan {n : ℕ → ℕ} {T : ℝ} (hT : 0 < T) (hn : IsUnlimited ((n : ℕ → ℕ) : Ult ℕ))
    (Φ : (Set.Icc (0 : ℝ) T → ℝ) → ℝ) (hΦ : Measurable Φ)
    (hΦ2 : MemLp (fun ω => Φ (bpath T n ω)) 2 (L n)) :
    toL2 (L n) (fun ω => Φ (bpath T n ω)) ∈ expoSpan (L n) (T := T) (bproc T n) := by
  have hG := gaussFacts_loeb hT hn
  have hvm : toL2 (L n) (fun ω => Φ (bpath T n ω)) ∈
      lpMeas ℝ ℝ (QE.Chaos.Dense.pathSigma (bproc T n) T) 2 (L n) := by
    rw [mem_lpMeas_iff_aestronglyMeasurable]
    have : Measurable[QE.Chaos.Dense.pathSigma (bproc T n) T] (fun ω => Φ (bpath T n ω)) :=
      hΦ.comp (comap_measurable _)
    exact this.stronglyMeasurable.aestronglyMeasurable.congr (coeFn_toL2 _ hΦ2).symm
  exact mem_expoSpan hT.le (fun t => measurable_andersonB T n t) (fun ω => andersonB_zero T n ω)
    hG.memLp_expo _ hvm

theorem norm_sq_sum_Pi {n : ℕ → ℕ} {T : ℝ} (hT : 0 < T) (hn : IsUnlimited ((n : ℕ → ℕ) : Ult ℕ))
    (I : Finset ℕ) (v : Lp ℝ 2 (L n)) :
    ‖∑ m ∈ I, Pi (L n) (T := T) (bproc T n) m v‖ ^ 2 =
      ∑ m ∈ I, ‖Pi (L n) (T := T) (bproc T n) m v‖ ^ 2 := by
  have hG := gaussFacts_loeb (T := T) hT hn
  classical
  induction I using Finset.induction_on with
  | empty => simp
  | insert a I ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, ← ih]
    have ho : inner ℝ (Pi (L n) (T := T) (bproc T n) a v)
        (∑ m ∈ I, Pi (L n) (T := T) (bproc T n) m v) = 0 := by
      rw [inner_sum]
      exact Finset.sum_eq_zero fun m hm => chaos_orthogonal hG
        (by rintro rfl; exact ha hm) _ (Pi_mem a v) _ (Pi_mem m v)
    have := norm_add_sq_eq_norm_sq_add_norm_sq_real ho
    rw [sq, this, ← sq, ← sq]

/-- **The classical chaos tail in norm**: `‖Φ - ∑_{m<M} Π_m Φ‖² ≤ T N₁²/M` (with the
Wiener–Itô decomposition `Φ = ∑_m Π_m Φ`). -/
theorem norm_sub_chaosSum_le_tail {n : ℕ → ℕ} {T : ℝ} (hT : 0 < T)
    (hn : IsUnlimited ((n : ℕ → ℕ) : Ult ℕ)) (t : Fin p → ℝ≥0) (htT : ∀ l, (t l : ℝ) ≤ T)
    {g : (Fin p → ℝ) → ℝ} {N : ℕ → ℝ} (hg : DBnd g 1 N) {M : ℕ} (hM : 0 < M) :
    ‖toL2 (L n) (fun ω => PhiCyl t htT g (bpath T n ω)) -
        chaosSum (T := T) (b := bproc T n) M (toL2 (L n) (fun ω => PhiCyl t htT g (bpath T n ω)))‖
      ≤ √(T * N 1 ^ 2 / M) := by
  set v := toL2 (L n) (fun ω => PhiCyl t htT g (bpath T n ω))
  have hG := gaussFacts_loeb (T := T) hT hn
  have hgc : Continuous g := continuous_dirD (ws := []) hg.1 (by simp)
  have hv := toL2_mem_expoSpan hT hn (PhiCyl t htT g) (measurable_PhiCyl t htT hgc)
    (memLp_PhiCyl t htT hg)
  have hlim := tendsto_chaosSum hG hv
  have hlim2 : Tendsto (fun M' => ‖chaosSum (T := T) (b := bproc T n) M' v -
      chaosSum (T := T) (b := bproc T n) M v‖) atTop
      (𝓝 ‖v - chaosSum (T := T) (b := bproc T n) M v‖) :=
    ((hlim.sub tendsto_const_nhds).norm)
  refine le_of_tendsto hlim2 ?_
  filter_upwards [eventually_ge_atTop M] with M' hM'
  have e : chaosSum (T := T) (b := bproc T n) M' v - chaosSum (T := T) (b := bproc T n) M v =
      ∑ m ∈ Finset.Ico M M', Pi (L n) (T := T) (bproc T n) m v := by
    unfold chaosSum; rw [Finset.sum_Ico_eq_sub _ hM']
  rw [e]
  refine Real.le_sqrt_of_sq_le ?_
  rw [norm_sq_sum_Pi hT hn]
  exact chaos_tail_classical hT hn t htT hg hM M'

theorem liftI_eq_zero_of_lt {n : ℕ} {m : ℕ} (hm : n < m) (F : (Fin n → Bool) → ℝ) (x : Fin n → ℝ) :
    liftI m F x = 0 := by
  unfold liftI
  rw [Finset.powersetCard_eq_empty.2 (by simpa using hm), Finset.sum_empty]

/-- The full Gaussian lift `F̃_n = ∑_S F̂_n(S) ∏_{j ∈ S} G_j = ∑_{m ≤ n} Π_m F̃_n`. -/
def Ftil {n : ℕ} (F : (Fin n → Bool) → ℝ) (G : Fin n → ℝ) : ℝ :=
  ∑ m ∈ Finset.range (n + 1), liftI m F G

/-- **Item (iv), the consequence, quantitatively**: for every `M ≥ 1`,
`‖F̃_n - Φ‖ ≤ ∑_{m<M} √(A_m τ) + 2 √(T N₁²/M)`. -/
theorem chaos_total_bound {n : ℕ} (hn : 0 < n) {T : ℝ} (hT : 0 < T) (hτ : T / n ≤ 1)
    (t : Fin p → ℝ≥0) (htT : ∀ l, (t l : ℝ) ≤ T) {g : (Fin p → ℝ) → ℝ} {N : ℕ → ℝ}
    (hg : ∀ r, DBnd g r N) {M : ℕ} (hM : 0 < M) :
    ‖toL2 (L (fun k => n * (k + 1)))
        (fun ω => Ftil (Fn T n (fun l => (t l : ℝ)) g) (Gl T n (fun k => n * (k + 1)) ω)) -
      toL2 (L (fun k => n * (k + 1)))
        (fun ω => PhiCyl t htT g (bpath T (fun k => n * (k + 1)) ω))‖ ≤
      ∑ m ∈ Finset.range M, √(Al2 p m T N * (T / n)) + 2 * √(T * N 1 ^ 2 / M) := by
  set Ns : ℕ → ℕ := fun k => n * (k + 1)
  have hNs : IsUnlimited ((Ns : ℕ → ℕ) : Ult ℕ) := isUnlimited_mul_succ hn
  set F := Fn T n (fun l => (t l : ℝ)) g
  have hFb : ∀ ω, |F ω| ≤ N 0 := fun ω => abs_le_N0 (hg 0) _
  set v := toL2 (L Ns) (fun ω => PhiCyl t htT g (bpath T Ns ω))
  set u : ℕ → Ult (ℕ → Bool) → ℝ := fun m ω => liftI m F (Gl T n Ns ω)
  have hu : ∀ m, MemLp (u m) 2 (L Ns) := fun m => by
    have := (norm_sq_sum_lift hn hT {m} F hFb).1
    simpa [u] using this
  obtain ⟨R, hR⟩ : ∃ R, R = M + n + 1 := ⟨_, rfl⟩
  have hFt : (fun ω => Ftil F (Gl T n Ns ω)) = fun ω => ∑ m ∈ Finset.range R, u m ω := by
    funext ω
    unfold Ftil
    have hsub : Finset.range (n + 1) ⊆ Finset.range R := by
      intro x hx; simp only [Finset.mem_range] at hx ⊢; omega
    refine Finset.sum_subset hsub fun m hm hm' => ?_
    simp only [Finset.mem_range] at hm hm'
    exact liftI_eq_zero_of_lt (by omega) F _
  have hsplit : toL2 (L Ns) (fun ω => ∑ m ∈ Finset.range R, u m ω) =
      ∑ m ∈ Finset.range M, toL2 (L Ns) (u m) +
        toL2 (L Ns) (fun ω => ∑ m ∈ Finset.Ico M R, u m ω) := by
    have h1 := toL2_sum (P := L Ns) (Finset.range R) (fun _ => (1 : ℝ)) u (fun m _ => hu m)
    have h2 := toL2_sum (P := L Ns) (Finset.Ico M R) (fun _ => (1 : ℝ)) u (fun m _ => hu m)
    simp only [one_mul, one_smul] at h1 h2
    rw [h1, h2, Finset.range_eq_Ico, ← Finset.sum_Ico_consecutive _ (Nat.zero_le M)
      (by omega : M ≤ R), ← Finset.range_eq_Ico]
  have hdecomp : toL2 (L Ns) (fun ω => Ftil F (Gl T n Ns ω)) - v =
      ∑ m ∈ Finset.range M, (toL2 (L Ns) (u m) - Pi (L Ns) (T := T) (bproc T Ns) m v) +
        toL2 (L Ns) (fun ω => ∑ m ∈ Finset.Ico M R, u m ω) -
          (v - chaosSum (T := T) (b := bproc T Ns) M v) := by
    rw [hFt, hsplit, Finset.sum_sub_distrib]
    simp only [chaosSum]; abel
  rw [hdecomp]
  have hA : ∀ m ∈ Finset.range M,
      ‖toL2 (L Ns) (u m) - Pi (L Ns) (T := T) (bproc T Ns) m v‖ ≤ √(Al2 p m T N * (T / n)) :=
    fun m _ => chaos_L2_shadow hn hT hτ t htT (hg (m + 4))
  have hB : ‖toL2 (L Ns) (fun ω => ∑ m ∈ Finset.Ico M R, u m ω)‖ ≤ √(T * N 1 ^ 2 / M) := by
    obtain ⟨hmem, hint⟩ := norm_sq_sum_lift hn hT (Finset.Ico M R) F hFb
    refine Real.le_sqrt_of_sq_le ?_
    rw [norm_sq_Lp, integral_congr_ae ((coeFn_toL2 _ hmem).mono fun ω h => by rw [h]), hint]
    refine le_trans ?_ (chaos_tail_discrete (n := n) hM hT (fun l => (t l : ℝ)) (hg 1))
    refine Finset.sum_le_sum_of_subset_of_nonneg (fun S hS => ?_) (fun _ _ _ => sq_nonneg _)
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_Ico] at hS ⊢
    exact hS.1
  have hC := norm_sub_chaosSum_le_tail hT hNs t htT (hg 1) hM
  calc ‖∑ m ∈ Finset.range M, (toL2 (L Ns) (u m) - Pi (L Ns) (T := T) (bproc T Ns) m v) +
        toL2 (L Ns) (fun ω => ∑ m ∈ Finset.Ico M R, u m ω) -
          (v - chaosSum (T := T) (b := bproc T Ns) M v)‖
      ≤ ‖∑ m ∈ Finset.range M, (toL2 (L Ns) (u m) - Pi (L Ns) (T := T) (bproc T Ns) m v)‖ +
          ‖toL2 (L Ns) (fun ω => ∑ m ∈ Finset.Ico M R, u m ω)‖ +
          ‖v - chaosSum (T := T) (b := bproc T Ns) M v‖ :=
        (norm_sub_le _ _).trans (by gcongr; exact norm_add_le _ _)
    _ ≤ ∑ m ∈ Finset.range M, √(Al2 p m T N * (T / n)) + √(T * N 1 ^ 2 / M) +
          √(T * N 1 ^ 2 / M) := by
        gcongr
        exact (norm_sum_le _ _).trans (Finset.sum_le_sum hA)
    _ = _ := by ring

/-- **Item (iv), the consequence**: for `g ∈ C_b^∞`, `‖F̃_n - Φ‖_{L²} → 0` as `n → ∞`. -/
theorem chaos_total_tendsto {T : ℝ} (hT : 0 < T) (t : Fin p → ℝ≥0) (htT : ∀ l, (t l : ℝ) ≤ T)
    {g : (Fin p → ℝ) → ℝ} {N : ℕ → ℝ} (hg : ∀ r, DBnd g r N) :
    Tendsto (fun n : ℕ => ‖toL2 (L (fun k => n * (k + 1)))
        (fun ω => Ftil (Fn T n (fun l => (t l : ℝ)) g) (Gl T n (fun k => n * (k + 1)) ω)) -
      toL2 (L (fun k => n * (k + 1)))
        (fun ω => PhiCyl t htT g (bpath T (fun k => n * (k + 1)) ω))‖) atTop (𝓝 0) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hN1 : 0 ≤ T * N 1 ^ 2 := by positivity
  -- choose `M` with `2 √(T N₁²/M) < ε/2`
  obtain ⟨M, hM0, hM⟩ : ∃ M : ℕ, 0 < M ∧ 2 * √(T * N 1 ^ 2 / M) < ε / 2 := by
    have : Tendsto (fun M : ℕ => 2 * √(T * N 1 ^ 2 / M)) atTop (𝓝 0) := by
      have h1 : Tendsto (fun M : ℕ => T * N 1 ^ 2 / (M : ℝ)) atTop (𝓝 0) :=
        tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
      simpa using (h1.sqrt).const_mul 2
    obtain ⟨M, hM⟩ := (Metric.tendsto_atTop.1 this) (ε / 2) (by positivity)
    refine ⟨M + 1, Nat.succ_pos M, ?_⟩
    have := hM (M + 1) (by omega)
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (by positivity)] at this
    exact this
  -- then `n` large
  have hfin : Tendsto (fun n : ℕ => ∑ m ∈ Finset.range M, √(Al2 p m T N * (T / n))) atTop
      (𝓝 0) := by
    have : ∀ m ∈ Finset.range M, Tendsto (fun n : ℕ => √(Al2 p m T N * (T / n))) atTop (𝓝 0) := by
      intro m _
      have h1 : Tendsto (fun n : ℕ => T / (n : ℝ)) atTop (𝓝 0) :=
        tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
      simpa using ((h1.const_mul (Al2 p m T N)).sqrt)
    simpa using tendsto_finsetSum _ this
  obtain ⟨n₀, hn₀⟩ := (Metric.tendsto_atTop.1 hfin) (ε / 2) (by positivity)
  have hτ : Tendsto (fun n : ℕ => T / (n : ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  obtain ⟨n₁, hn₁⟩ := (Metric.tendsto_atTop.1 hτ) 1 one_pos
  refine ⟨max (max n₀ n₁) 1, fun n hn => ?_⟩
  have hn0 : 0 < n := by omega
  have hτn : T / n ≤ 1 := by
    have := hn₁ n (by omega)
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (by positivity)] at this
    exact this.le
  have hb := chaos_total_bound hn0 hT hτn t htT hg hM0
  have h2 := hn₀ n (by omega)
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (Finset.sum_nonneg fun m _ => Real.sqrt_nonneg _)]
    at h2
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (norm_nonneg _)]
  linarith

/-- **Item (iv), the rate**: if `∑_m √A_m < ∞` then `‖F̃_n - Φ‖ ≤ √τ ∑_m √A_m`. -/
theorem chaos_total_rate {n : ℕ} (hn : 0 < n) {T : ℝ} (hT : 0 < T) (hτ : T / n ≤ 1)
    (t : Fin p → ℝ≥0) (htT : ∀ l, (t l : ℝ) ≤ T) {g : (Fin p → ℝ) → ℝ} {N : ℕ → ℝ}
    (hg : ∀ r, DBnd g r N) (hsum : Summable fun m => √(Al2 p m T N)) :
    ‖toL2 (L (fun k => n * (k + 1)))
        (fun ω => Ftil (Fn T n (fun l => (t l : ℝ)) g) (Gl T n (fun k => n * (k + 1)) ω)) -
      toL2 (L (fun k => n * (k + 1)))
        (fun ω => PhiCyl t htT g (bpath T (fun k => n * (k + 1)) ω))‖ ≤
      √(T / n) * ∑' m, √(Al2 p m T N) := by
  set D := ‖toL2 (L (fun k => n * (k + 1)))
        (fun ω => Ftil (Fn T n (fun l => (t l : ℝ)) g) (Gl T n (fun k => n * (k + 1)) ω)) -
      toL2 (L (fun k => n * (k + 1)))
        (fun ω => PhiCyl t htT g (bpath T (fun k => n * (k + 1)) ω))‖
  have hτ0 : 0 ≤ T / n := by positivity
  have hbound : ∀ M : ℕ, 0 < M → D ≤ √(T / n) * ∑' m, √(Al2 p m T N) + 2 * √(T * N 1 ^ 2 / M) := by
    intro M hM
    refine (chaos_total_bound hn hT hτ t htT hg hM).trans ?_
    gcongr
    have : ∑ m ∈ Finset.range M, √(Al2 p m T N * (T / n)) =
        √(T / n) * ∑ m ∈ Finset.range M, √(Al2 p m T N) := by
      rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro m _
      rw [Real.sqrt_mul' _ hτ0, mul_comm]
    rw [this]
    exact mul_le_mul_of_nonneg_left (hsum.sum_le_tsum _ fun m _ => Real.sqrt_nonneg _)
      (Real.sqrt_nonneg _)
  have hlim : Tendsto (fun M : ℕ => √(T / n) * ∑' m, √(Al2 p m T N) + 2 * √(T * N 1 ^ 2 / M))
      atTop (𝓝 (√(T / n) * ∑' m, √(Al2 p m T N))) := by
    have h1 : Tendsto (fun M : ℕ => T * N 1 ^ 2 / (M : ℝ)) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
    simpa using tendsto_const_nhds.add ((h1.sqrt).const_mul 2)
  exact ge_of_tendsto hlim (by
    filter_upwards [eventually_ge_atTop 1] with M hM
    exact hbound M (by omega))

end Total2

section LawComb

variable {p : ℕ}

/-- Weighted sums of Walsh levels as one multilinear polynomial. -/
theorem sum_smul_liftI_eq_mlEval {n : ℕ} (M : ℕ) (a : ℕ → ℝ) (F : (Fin n → Bool) → ℝ)
    (x : Fin n → ℝ) :
    ∑ m ∈ Finset.range (M + 1), a m * liftI m F x =
      mlEval (fun S => if S.card ≤ M then a S.card * coeff F S else 0) x := by
  simp_rw [k_liftI_eq]
  unfold mlEval
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro S _
  by_cases h : S.card ≤ M
  · rw [if_pos h, Finset.sum_eq_single S.card]
    · rw [if_pos rfl]; ring
    · intro b _ hb; rw [if_neg (Ne.symm hb)]; ring
    · intro h'; exact absurd (Finset.mem_range.2 (Nat.lt_succ_of_le h)) h'
  · rw [if_neg h, zero_mul]
    refine Finset.sum_eq_zero fun b hb => ?_
    rw [if_neg]; · ring
    rintro rfl; exact h (Nat.lt_succ_iff.1 (Finset.mem_range.1 hb))

theorem degLe_comb {n : ℕ} (M : ℕ) (a : ℕ → ℝ) (F : (Fin n → Bool) → ℝ) :
    DegLe (fun S : Finset (Fin n) => if S.card ≤ M then a S.card * coeff F S else 0) M := by
  intro S hS; exact if_neg (by omega)

/-- **Item (iii) for linear combinations of chaoses**: for `Q = ∑_{m ≤ M} a_m Π_m`,
`|E Ψ(Q F_n) - E Ψ(Q Φ)| ≤ (B/6) 9^{M-1} ∑_j Inf_j(Q)² + Lc ∑_m |a_m| √(A_m τ)`. -/
theorem chaos_law_comb4 {M n : ℕ} (hn : 0 < n) {T : ℝ} (hT : 0 < T) (hτ : T / n ≤ 1)
    (t : Fin p → ℝ≥0) (htT : ∀ l, (t l : ℝ) ≤ T) {g : (Fin p → ℝ) → ℝ} {N : ℕ → ℝ}
    (hg : DBnd g (M + 4) N) (a : ℕ → ℝ) (Ψ : ℝ → ℝ) (hΨ : ContDiff ℝ 4 Ψ) {B : ℝ}
    (hB : ∀ x, |iteratedDeriv 4 Ψ x| ≤ B) {Lc : ℝ≥0} (hL : LipschitzWith Lc Ψ) :
    |E (fun η : Fin n → Bool => Ψ (∑ m ∈ Finset.range (M + 1),
        a m * liftI m (Fn T n (fun l => (t l : ℝ)) g) (fun j => sgn (η j)))) -
      ∫ ω, Ψ (∑ m ∈ Finset.range (M + 1), a m * (Pi (L (fun k => n * (k + 1))) (T := T)
        (bproc T (fun k => n * (k + 1))) m (toL2 (L (fun k => n * (k + 1)))
          (fun ω => PhiCyl t htT g (bpath T (fun k => n * (k + 1)) ω))) :
            Ult (ℕ → Bool) → ℝ) ω) ∂(L (fun k => n * (k + 1)))| ≤
      B / 6 * 9 ^ (M - 1) * ∑ j, infl (fun S : Finset (Fin n) => if S.card ≤ M then
          a S.card * coeff (Fn T n (fun l => (t l : ℝ)) g) S else 0) j ^ 2 +
        Lc * ∑ m ∈ Finset.range (M + 1), |a m| * √(Al2 p m T N * (T / n)) := by
  set Ns : ℕ → ℕ := fun k => n * (k + 1)
  have hNs : IsUnlimited ((Ns : ℕ → ℕ) : Ult ℕ) := isUnlimited_mul_succ hn
  set F := Fn T n (fun l => (t l : ℝ)) g
  set b : Finset (Fin n) → ℝ := fun S => if S.card ≤ M then a S.card * coeff F S else 0
  set v := toL2 (L Ns) (fun ω => PhiCyl t htT g (bpath T Ns ω))
  set w : ℕ → Ult (ℕ → Bool) → ℝ := fun m => (Pi (L Ns) (T := T) (bproc T Ns) m v :
    Ult (ℕ → Bool) → ℝ)
  set u : ℕ → Ult (ℕ → Bool) → ℝ := fun m ω => liftI m F (Gl T n Ns ω)
  have hG := hasLaw_Gl hT hn hNs
  obtain ⟨hiu, hlaw⟩ := law_coins_gauss4 hn b (degLe_comb M a F) Ψ hΨ hB hG
  have hFb : ∀ ω, |F ω| ≤ N 0 := fun ω => abs_le_N0 hg _
  have hu2 : ∀ m, MemLp (u m) 2 (L Ns) := fun m => by
    have := (norm_sq_sum_lift hn hT {m} F hFb).1
    simpa [u] using this
  have hw2 : ∀ m, MemLp (w m) 2 (L Ns) := fun m => Lp.memLp _
  set U : Ult (ℕ → Bool) → ℝ := fun ω => ∑ m ∈ Finset.range (M + 1), a m * u m ω
  set W : Ult (ℕ → Bool) → ℝ := fun ω => ∑ m ∈ Finset.range (M + 1), a m * w m ω
  have hU : (fun ω => Ψ (mlEval b (Gl T n Ns ω))) = fun ω => Ψ (U ω) := by
    funext ω; simp only [U, u, b]; rw [sum_smul_liftI_eq_mlEval]
  have hcoin : (fun η : Fin n → Bool => Ψ (mlEval b (fun j => sgn (η j)))) =
      fun η => Ψ (∑ m ∈ Finset.range (M + 1), a m * liftI m F (fun j => sgn (η j))) := by
    funext η; simp only [b]; rw [sum_smul_liftI_eq_mlEval]
  rw [hU] at hiu hlaw
  rw [hcoin] at hlaw
  have hW2 : MemLp W 2 (L Ns) := memLp_finset_sum _ fun m _ => (hw2 m).const_mul (a m)
  have hU2 : MemLp U 2 (L Ns) := memLp_finset_sum _ fun m _ => (hu2 m).const_mul (a m)
  have hiW : Integrable (fun ω => Ψ (W ω)) (L Ns) := by
    refine Integrable.mono' (g := fun ω => |Ψ 0| + Lc * |W ω|)
      ((integrable_const _).add ((hW2.integrable one_le_two).abs.const_mul _))
      (hL.continuous.measurable.comp_aemeasurable
        hW2.aestronglyMeasurable.aemeasurable).aestronglyMeasurable
      (Eventually.of_forall fun ω => ?_)
    have := hL.dist_le_mul (W ω) 0
    rw [Real.dist_eq, Real.dist_eq, sub_zero] at this
    rw [Real.norm_eq_abs]
    have := abs_sub_abs_le_abs_sub (Ψ (W ω)) (Ψ 0)
    linarith
  have hdiff : |∫ ω, Ψ (U ω) ∂(L Ns) - ∫ ω, Ψ (W ω) ∂(L Ns)| ≤
      Lc * ∑ m ∈ Finset.range (M + 1), |a m| * √(Al2 p m T N * (T / n)) := by
    rw [← integral_sub hiu hiW]
    refine (abs_integral_le_integral_abs).trans ?_
    have hint : ∀ m, Integrable (fun ω => |u m ω - w m ω|) (L Ns) := fun m =>
      (((hu2 m).sub (hw2 m)).integrable one_le_two).abs
    have hpt : ∀ ω, |Ψ (U ω) - Ψ (W ω)| ≤
        Lc * ∑ m ∈ Finset.range (M + 1), |a m| * |u m ω - w m ω| := by
      intro ω
      have h1 := hL.dist_le_mul (U ω) (W ω)
      rw [Real.dist_eq, Real.dist_eq] at h1
      refine h1.trans (mul_le_mul_of_nonneg_left ?_ Lc.2)
      simp only [U, W]
      rw [← Finset.sum_sub_distrib]
      refine (Finset.abs_sum_le_sum_abs _ _).trans (le_of_eq ?_)
      apply Finset.sum_congr rfl; intro m _; rw [← mul_sub, abs_mul]
    have hsumint : Integrable (fun ω => ∑ m ∈ Finset.range (M + 1), |a m| * |u m ω - w m ω|)
        (L Ns) := integrable_finset_sum _ fun m _ => (hint m).const_mul _
    calc ∫ ω, |Ψ (U ω) - Ψ (W ω)| ∂(L Ns)
        ≤ ∫ ω, Lc * ∑ m ∈ Finset.range (M + 1), |a m| * |u m ω - w m ω| ∂(L Ns) :=
          integral_mono ((hiu.sub hiW).abs) (hsumint.const_mul _) hpt
      _ = Lc * ∑ m ∈ Finset.range (M + 1), |a m| * ∫ ω, |u m ω - w m ω| ∂(L Ns) := by
          rw [integral_const_mul, integral_finset_sum _ fun m _ => (hint m).const_mul _]
          congr 1; apply Finset.sum_congr rfl; intro m _; exact integral_const_mul _ _
      _ ≤ Lc * ∑ m ∈ Finset.range (M + 1), |a m| * √(Al2 p m T N * (T / n)) := by
          refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun m hm => ?_) Lc.2
          refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
          refine (integral_abs_le_sqrt (f := fun ω => u m ω - w m ω) ((hu2 m).sub (hw2 m))).trans ?_
          have hvv : toL2 (L Ns) (w m) = Pi (L Ns) (T := T) (bproc T Ns) m v := by
            rw [toL2_of_memLp _ (hw2 m)]; exact Lp.toLp_coeFn _ (hw2 m)
          have := norm_toL2_sub_sq (hu2 m) (hw2 m)
          rw [hvv] at this
          rw [← this, Real.sqrt_sq (norm_nonneg _)]
          have hm' : m ≤ M := Nat.lt_succ_iff.1 (Finset.mem_range.1 hm)
          exact chaos_L2_shadow hn hT hτ t htT (hg.mono (by omega))
  calc _ = |(E (fun η : Fin n → Bool => Ψ (∑ m ∈ Finset.range (M + 1),
          a m * liftI m F (fun j => sgn (η j)))) - ∫ ω, Ψ (U ω) ∂(L Ns)) +
        (∫ ω, Ψ (U ω) ∂(L Ns) - ∫ ω, Ψ (W ω) ∂(L Ns))| :=
          (congrArg abs (sub_add_sub_cancel _ _ _)).symm
    _ ≤ _ := abs_add_le _ _
    _ ≤ _ := add_le_add hlaw hdiff

end LawComb

end QE.Chaos.Shadow
