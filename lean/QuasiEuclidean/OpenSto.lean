-- SPDX-License-Identifier: MIT
-- Copyright 2026 Metere Industries, Inc. Author: Alfredo Metere.
-- Quasi-Euclidean Granular Geometry. Any derivative work must carry this notice:
--   This work is derivative of the Quasi-Euclidean Granular Geometry book
--   authored by Alfredo Metere. Copyright 2026 Metere Industries, Inc.
--   All rights reserved
-- See LICENSE.md and NOTICE.


import Mathlib
import QuasiEuclidean.Ch15b_Learning

/-!
# Open problems settled (op-sto)

Walsh–Itô chaos (`QE.OpenSto.Walsh`), granular information geometry
(`QE.OpenSto.InfoGeo`), Euclidean lattice fields (`QE.OpenSto.Field`), and the
learning-machine results (`QE.OpenSto.Learn`: granular implicit function theorem,
cancellation of quantisation errors, Occam bounds over functions and orbits).
-/

/-!
# The Walsh–Itô chaos of the Anderson walk

Exact, finitary statements on the coin space `Fin n → Bool` with the uniform
(counting) expectation.
-/

set_option linter.unusedSectionVars false
set_option linter.deprecated false

namespace QE.OpenSto.Walsh

open Finset

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-- Sign of a coin. -/
def sgn (b : Bool) : K := if b then 1 else -1

@[simp] theorem sgn_true : (sgn true : K) = 1 := rfl
@[simp] theorem sgn_false : (sgn false : K) = -1 := rfl

theorem sgn_mul_self (b : Bool) : (sgn b : K) * sgn b = 1 := by cases b <;> simp

/-- Uniform expectation on the coin space. -/
noncomputable def E {n : ℕ} (X : (Fin n → Bool) → K) : K := (∑ ω, X ω) / 2 ^ n

/-- Walsh character `χ_S(ω) = ∏_{i ∈ S} ξ_i`. -/
def chi {n : ℕ} (S : Finset (Fin n)) (ω : Fin n → Bool) : K := ∏ i ∈ S, sgn (ω i)

theorem chi_eq_prod_univ {n : ℕ} (S : Finset (Fin n)) (ω : Fin n → Bool) :
    (chi S ω : K) = ∏ i, (if i ∈ S then sgn (ω i) else 1) := by
  rw [prod_ite_mem, univ_inter]; rfl

/-- Sum of a character over all paths. -/
theorem sum_chi {n : ℕ} (S : Finset (Fin n)) :
    ∑ ω, (chi S ω : K) = if S = ∅ then 2 ^ n else 0 := by
  simp_rw [chi_eq_prod_univ]
  rw [← Fintype.prod_sum (fun i (b : Bool) => if i ∈ S then (sgn b : K) else 1)]
  have h : ∀ i : Fin n, ∑ b : Bool, (if i ∈ S then (sgn b : K) else 1)
      = if i ∈ S then 0 else 2 := by
    intro i; split_ifs <;> simp
  simp_rw [h]
  split_ifs with hS
  · subst hS; simp
  · obtain ⟨i, hi⟩ := Finset.nonempty_iff_ne_empty.mpr hS
    exact prod_eq_zero (mem_univ i) (by simp [hi])

/-- Characters multiply by symmetric difference. -/
theorem chi_mul {n : ℕ} (S T : Finset (Fin n)) (ω : Fin n → Bool) :
    (chi S ω : K) * chi T ω = chi (symmDiff S T) ω := by
  simp_rw [chi_eq_prod_univ, ← prod_mul_distrib]
  apply prod_congr rfl; intro i _
  have := sgn_mul_self (K := K) (ω i)
  by_cases hS : i ∈ S <;> by_cases hT : i ∈ T <;>
    simp [hS, hT, Finset.mem_symmDiff, this]

/-- **Orthonormality** of the Walsh characters. -/
theorem E_chi_mul {n : ℕ} (S T : Finset (Fin n)) :
    E (fun ω => (chi S ω : K) * chi T ω) = if S = T then 1 else 0 := by
  unfold E
  simp_rw [chi_mul, sum_chi]
  have : symmDiff S T = ∅ ↔ S = T := symmDiff_eq_bot
  by_cases h : S = T
  · rw [if_pos (this.mpr h), if_pos h]; field_simp
  · rw [if_neg (mt this.mp h), if_neg h]; simp

theorem E_chi {n : ℕ} (S : Finset (Fin n)) :
    E (fun ω => (chi S ω : K)) = if S = ∅ then 1 else 0 := by
  unfold E; rw [sum_chi]; split_ifs <;> simp

/-- Walsh coefficient `ĉ_S(F) = E[F χ_S]`. -/
noncomputable def coeff {n : ℕ} (F : (Fin n → Bool) → K) (S : Finset (Fin n)) : K :=
  E (fun ω => F ω * chi S ω)

theorem E_sum {n : ℕ} {ι : Type*} (s : Finset ι) (X : ι → (Fin n → Bool) → K) :
    E (fun ω => ∑ j ∈ s, X j ω) = ∑ j ∈ s, E (X j) := by
  unfold E; rw [sum_comm, sum_div]

theorem E_smul {n : ℕ} (a : K) (X : (Fin n → Bool) → K) :
    E (fun ω => a * X ω) = a * E X := by
  unfold E; rw [← mul_sum, mul_div_assoc]

/-- Reproducing kernel: `∑_S χ_S(η) χ_S(ω) = 2^n [η = ω]`. -/
theorem sum_chi_chi {n : ℕ} (η ω : Fin n → Bool) :
    ∑ S : Finset (Fin n), (chi S η : K) * chi S ω = if η = ω then 2 ^ n else 0 := by
  have h1 : ∀ S : Finset (Fin n), (chi S η : K) * chi S ω = ∏ i ∈ S, (sgn (η i) * sgn (ω i)) := by
    intro S; unfold chi; rw [prod_mul_distrib]
  simp_rw [h1]
  rw [← Finset.powerset_univ, ← prod_one_add]
  split_ifs with h
  · subst h; simp [sgn_mul_self]; norm_num
  · obtain ⟨i, hi⟩ : ∃ i, η i ≠ ω i := by
      by_contra hc; push Not at hc; exact h (funext hc)
    apply prod_eq_zero (mem_univ i)
    cases hη : η i <;> cases hω : ω i <;> simp_all

/-- **Exact finite Walsh expansion.** -/
theorem walsh_expansion {n : ℕ} (F : (Fin n → Bool) → K) (ω : Fin n → Bool) :
    F ω = ∑ S : Finset (Fin n), coeff F S * chi S ω := by
  unfold coeff E
  simp_rw [div_mul_eq_mul_div, sum_mul]
  rw [← sum_div, sum_comm]
  simp_rw [mul_assoc, ← mul_sum, sum_chi_chi]
  simp

/-- The coefficients of an expansion are its Walsh coefficients. -/
theorem coeff_of_expansion {n : ℕ} (a : Finset (Fin n) → K) (T : Finset (Fin n)) :
    coeff (fun ω => ∑ S, a S * chi S ω) T = a T := by
  unfold coeff
  simp_rw [sum_mul, mul_assoc]
  rw [E_sum]
  simp_rw [E_smul, E_chi_mul]
  simp

/-- **Uniqueness** of the Walsh expansion. -/
theorem walsh_unique {n : ℕ} (a b : Finset (Fin n) → K)
    (h : ∀ ω, ∑ S, a S * chi S ω = ∑ S, b S * chi S ω) : a = b := by
  funext T
  rw [← coeff_of_expansion a T, ← coeff_of_expansion b T]
  congr 1; funext ω; exact h ω

/-- **Parseval.** -/
theorem parseval {n : ℕ} (F G : (Fin n → Bool) → K) :
    E (fun ω => F ω * G ω) = ∑ S, coeff F S * coeff G S := by
  have : (fun ω => F ω * G ω) = fun ω => ∑ S, coeff F S * (chi S ω * G ω) := by
    funext ω; conv_lhs => rw [walsh_expansion F ω]
    rw [sum_mul]; simp_rw [mul_assoc]
  rw [this, E_sum]
  simp_rw [E_smul]
  apply sum_congr rfl; intro S _
  unfold coeff; congr 1; congr 1; funext ω; ring

/-! ## Discrete multiple Itô sums -/

/-- Discrete `m`-fold Itô sum with space step `s`:
`J_m(f)(ω) = ∑_{|S| = m} f(S) ∏_{i ∈ S} ΔW_i`, `ΔW_i = s ξ_i`. -/
def J {n : ℕ} (m : ℕ) (s : K) (f : Finset (Fin n) → K) (ω : Fin n → Bool) : K :=
  ∑ S ∈ powersetCard m univ, f S * ∏ i ∈ S, (s * sgn (ω i))

theorem prod_increments {n : ℕ} (s : K) (S : Finset (Fin n)) (ω : Fin n → Bool) :
    ∏ i ∈ S, (s * sgn (ω i)) = s ^ S.card * chi S ω := by
  rw [prod_mul_distrib, prod_const]; rfl

/-- **The degree-`m` Walsh part is a discrete `m`-fold Itô sum** with kernel
`ĉ_S / s^m`. -/
theorem walsh_part_eq_J {n : ℕ} (F : (Fin n → Bool) → K) (m : ℕ) (s : K) (hs : s ≠ 0)
    (ω : Fin n → Bool) :
    ∑ S ∈ powersetCard m univ, coeff F S * chi S ω = J m s (fun S => coeff F S / s ^ m) ω := by
  unfold J
  apply sum_congr rfl; intro S hS
  rw [prod_increments, (mem_powersetCard.mp hS).2]
  field_simp

/-- **Chaos decomposition**: `F = ∑_{m=0}^{n} J_m(ĉ/s^m)`. -/
theorem chaos_decomposition {n : ℕ} (F : (Fin n → Bool) → K) (s : K) (hs : s ≠ 0)
    (ω : Fin n → Bool) :
    F ω = ∑ m ∈ range (n + 1), J m s (fun S => coeff F S / s ^ m) ω := by
  rw [walsh_expansion F ω]
  simp_rw [← walsh_part_eq_J F _ s hs ω]
  rw [← sum_fiberwise_of_maps_to (s := univ) (t := range (n + 1)) (g := Finset.card)
    (fun S _ => by
      simpa [Nat.lt_succ_iff] using (card_le_univ S).trans (by simp))]
  apply sum_congr rfl; intro m _
  apply sum_congr _ (fun _ _ => rfl)
  rw [powersetCard_eq_filter, powerset_univ]

theorem max_iff {n : ℕ} (S : Finset (Fin n)) (hS : S.Nonempty) (k : Fin n) :
    (k ∈ S ∧ ∀ x ∈ S, x ≤ k) ↔ k = S.max' hS := by
  constructor
  · rintro ⟨hk, hx⟩
    exact le_antisymm (le_max' S k hk) (max'_le S hS k hx)
  · rintro rfl; exact ⟨max'_mem S hS, fun x hx => le_max' S x hx⟩

/-- **Iterated (adapted) structure**: decomposition of an `(m+1)`-fold sum by
its last time.  The inner sum depends only on the increments before `k`. -/
theorem sum_by_max {n : ℕ} (m : ℕ) (f : Finset (Fin n) → K) (d : Fin n → K) :
    ∑ S ∈ powersetCard (m + 1) univ, f S * ∏ i ∈ S, d i =
      ∑ k, (∑ T ∈ powersetCard m (univ.filter (· < k)), f (insert k T) * ∏ i ∈ T, d i) * d k := by
  classical
  set g : Finset (Fin n) → K := fun S => f S * ∏ i ∈ S, d i
  have step1 : ∑ S ∈ powersetCard (m + 1) univ, g S =
      ∑ S ∈ powersetCard (m + 1) univ, ∑ k, (if k ∈ S ∧ ∀ x ∈ S, x ≤ k then g S else 0) := by
    apply sum_congr rfl; intro S hS
    have hne : S.Nonempty := by
      rw [← card_pos, (mem_powersetCard.mp hS).2]; omega
    simp_rw [max_iff S hne]
    simp
  rw [step1, sum_comm]
  apply sum_congr rfl; intro k _
  rw [← sum_filter, sum_mul]
  apply sum_nbij' (fun S => S.erase k) (fun T => insert k T)
  · intro S hS
    simp only [mem_filter, mem_powersetCard] at hS
    obtain ⟨⟨-, hc⟩, hk, hx⟩ := hS
    simp only [mem_powersetCard]
    refine ⟨fun x hx' => ?_, ?_⟩
    · have := mem_erase.mp hx'
      simp only [mem_filter, mem_univ, true_and]
      exact lt_of_le_of_ne (hx x this.2) this.1
    · rw [card_erase_of_mem hk, hc]; rfl
  · intro T hT
    simp only [mem_powersetCard] at hT
    have hkT : k ∉ T := fun h => by
      have := hT.1 h; simp at this
    simp only [mem_filter, mem_powersetCard, mem_insert]
    refine ⟨⟨subset_univ _, by rw [card_insert_of_notMem hkT, hT.2]⟩, Or.inl trivial, ?_⟩
    rintro x (rfl | hx)
    · exact le_rfl
    · have := hT.1 hx; simp at this; exact this.le
  · intro S hS
    simp only [mem_filter] at hS
    exact insert_erase hS.2.1
  · intro T hT
    simp only [mem_powersetCard] at hT
    have hkT : k ∉ T := fun h => by
      have := hT.1 h; simp at this
    exact erase_insert hkT
  · intro S hS
    simp only [mem_filter] at hS
    simp only [g]
    rw [insert_erase hS.2.1, ← mul_prod_erase S d hS.2.1]; ring

/-- The Itô sum in iterated form: `J_{m+1}(f) = ∑_k H_k ΔW_k` with the adapted
integrand `H_k = ∑_{T ⊆ [0,k), |T| = m} f(T ∪ {k}) ∏_{i∈T} ΔW_i`. -/
theorem J_succ_iterated {n : ℕ} (m : ℕ) (s : K) (f : Finset (Fin n) → K) (ω : Fin n → Bool) :
    J (m + 1) s f ω = ∑ k, (∑ T ∈ powersetCard m (univ.filter (· < k)),
        f (insert k T) * ∏ i ∈ T, (s * sgn (ω i))) * (s * sgn (ω k)) :=
  sum_by_max m f (fun i => s * sgn (ω i))

/-- **Discrete Itô isometry** for multiple sums, and orthogonality of
different orders. -/
theorem J_isometry {n : ℕ} (m m' : ℕ) (s : K) (f g : Finset (Fin n) → K) :
    E (fun ω => J m s f ω * J m' s g ω) =
      if m = m' then s ^ (2 * m) * ∑ S ∈ powersetCard m univ, f S * g S else 0 := by
  unfold J
  simp_rw [prod_increments, sum_mul_sum]
  rw [E_sum]
  simp_rw [E_sum]
  have h : ∀ S ∈ powersetCard m (univ : Finset (Fin n)), ∀ T ∈ powersetCard m' univ,
      E (fun ω => f S * (s ^ S.card * chi S ω) * (g T * (s ^ T.card * chi T ω)))
        = if S = T then s ^ (2 * m) * (f S * g S) else 0 := by
    intro S hS T hT
    rw [(mem_powersetCard.mp hS).2, (mem_powersetCard.mp hT).2]
    have : (fun ω => f S * (s ^ m * chi S ω) * (g T * (s ^ m' * chi T ω)))
        = fun ω => (f S * g T * s ^ m * s ^ m') * (chi S ω * chi T ω) := by
      funext ω; ring
    rw [this, E_smul, E_chi_mul]
    split_ifs with hST
    · subst hST
      have : m = m' := by rw [← (mem_powersetCard.mp hS).2, ← (mem_powersetCard.mp hT).2]
      subst this; ring
    · simp
  rw [sum_congr rfl (fun S hS => sum_congr rfl (h S hS))]
  simp_rw [sum_ite_eq]
  split_ifs with hm
  · subst hm; rw [mul_sum]; apply sum_congr rfl; intro S hS; simp [hS]
  · apply sum_eq_zero; intro S hS
    rw [if_neg]; intro hS'
    exact hm ((mem_powersetCard.mp hS).2.symm.trans (mem_powersetCard.mp hS').2)

/-! ## The discrete Malliavin derivative and Stroock's formula -/

/-- Discrete Malliavin derivative at time `i`:
`D_i F = (F(ξ_i = +1) - F(ξ_i = -1)) / 2`. -/
noncomputable def D {n : ℕ} (i : Fin n) (F : (Fin n → Bool) → K) (ω : Fin n → Bool) : K :=
  (F (Function.update ω i true) - F (Function.update ω i false)) / 2

/-- `G` does not depend on the coin `i`. -/
def Indep {n : ℕ} (i : Fin n) (G : (Fin n → Bool) → K) : Prop :=
  ∀ ω b, G (Function.update ω i b) = G ω

/-- Flip of coin `i`. -/
def flip {n : ℕ} (i : Fin n) (ω : Fin n → Bool) : Fin n → Bool :=
  Function.update ω i (!ω i)

theorem flip_invol {n : ℕ} (i : Fin n) : Function.Involutive (flip i) := by
  intro ω; funext j
  by_cases h : j = i
  · subst h; simp [flip]
  · simp [flip, Function.update_of_ne h]

theorem sum_flip {n : ℕ} (i : Fin n) (H : (Fin n → Bool) → K) :
    ∑ ω, H (flip i ω) = ∑ ω, H ω :=
  Equiv.sum_comp (flip_invol i).toPerm H

/-- Pairing the two values of coin `i`. -/
theorem sum_pair {n : ℕ} (i : Fin n) (H : (Fin n → Bool) → K) :
    ∑ ω, H ω = (∑ ω, (H (Function.update ω i true) + H (Function.update ω i false))) / 2 := by
  have hpt : ∀ ω, H (Function.update ω i true) + H (Function.update ω i false)
      = H ω + H (flip i ω) := by
    intro ω
    cases hω : ω i
    · have h1 : Function.update ω i false = ω := by
        rw [← hω]; exact Function.update_eq_self i ω
      simp [flip, hω, h1, add_comm]
    · have h1 : Function.update ω i true = ω := by
        rw [← hω]; exact Function.update_eq_self i ω
      simp [flip, hω, h1]
  simp_rw [hpt, sum_add_distrib, sum_flip]
  ring

theorem chi_update_of_notMem {n : ℕ} (S : Finset (Fin n)) (i : Fin n) (hi : i ∉ S)
    (ω : Fin n → Bool) (b : Bool) : (chi S (Function.update ω i b) : K) = chi S ω := by
  unfold chi
  apply prod_congr rfl; intro j hj
  rw [Function.update_of_ne (fun h : j = i => hi (h ▸ hj))]

theorem indep_chi {n : ℕ} (S : Finset (Fin n)) (i : Fin n) (hi : i ∉ S) :
    Indep i (fun ω => (chi S ω : K)) :=
  fun ω b => chi_update_of_notMem S i hi ω b

theorem indep_D {n : ℕ} (i : Fin n) (F : (Fin n → Bool) → K) : Indep i (D i F) := by
  intro ω b; simp [D, Function.update_idem]

/-- **Stroock step**: `E[F ξ_i G] = E[(D_i F) G]` for `G` independent of coin `i`. -/
theorem E_sgn_mul {n : ℕ} (i : Fin n) (F G : (Fin n → Bool) → K) (hG : Indep i G) :
    E (fun ω => F ω * sgn (ω i) * G ω) = E (fun ω => D i F ω * G ω) := by
  unfold E; congr 1
  rw [sum_pair i, sum_div]
  apply sum_congr rfl; intro ω _
  rw [hG ω true, hG ω false]
  simp only [Function.update_self, sgn_true, sgn_false, D]
  ring

/-- **Discrete Stroock formula** (one step): for `i ∉ S`,
`ĉ_{S ∪ {i}}(F) = ĉ_S(D_i F)`. -/
theorem coeff_insert {n : ℕ} (F : (Fin n → Bool) → K) (S : Finset (Fin n)) (i : Fin n)
    (hi : i ∉ S) : coeff F (insert i S) = coeff (D i F) S := by
  unfold coeff
  rw [← E_sgn_mul i F (fun ω => chi S ω) (indep_chi S i hi)]
  congr 1; funext ω
  unfold chi; rw [prod_insert hi]; ring

/-- `E F` is the empty coefficient. -/
theorem coeff_empty {n : ℕ} (F : (Fin n → Bool) → K) : coeff F ∅ = E F := by
  unfold coeff; congr 1; funext ω; simp [chi]

/-- Iterated discrete derivative along a list of times. -/
noncomputable def DS {n : ℕ} : List (Fin n) → ((Fin n → Bool) → K) → (Fin n → Bool) → K
  | [], F => F
  | a :: l, F => DS l (D a F)

/-- **Discrete Stroock formula**: `ĉ_S(F) = E[D_S F]` (for `S` listed without
repetition). -/
theorem stroock {n : ℕ} (l : List (Fin n)) (hl : l.Nodup) (F : (Fin n → Bool) → K) :
    coeff F l.toFinset = E (DS l F) := by
  induction l generalizing F with
  | nil =>
    rw [List.toFinset_nil, coeff_empty]; rfl
  | cons a l ih =>
    have ha : a ∉ l.toFinset := by
      rw [List.mem_toFinset]; exact (List.nodup_cons.mp hl).1
    rw [List.toFinset_cons, coeff_insert F _ a ha, ih (List.nodup_cons.mp hl).2]
    rfl

/-- The coefficients of a function independent of coin `i` vanish on sets
containing `i`. -/
theorem coeff_indep_mem {n : ℕ} (G : (Fin n → Bool) → K) (i : Fin n) (hG : Indep i G)
    (U : Finset (Fin n)) (hi : i ∈ U) : coeff G U = 0 := by
  unfold coeff E
  rw [sum_pair i]
  have : ∀ ω, G (Function.update ω i true) * chi U (Function.update ω i true)
      + G (Function.update ω i false) * chi U (Function.update ω i false) = 0 := by
    intro ω
    rw [hG ω true, hG ω false]
    unfold chi
    rw [← mul_prod_erase U _ hi, ← mul_prod_erase U _ hi]
    have h2 : ∀ b, ∏ x ∈ U.erase i, (sgn ((Function.update ω i b) x) : K)
        = ∏ x ∈ U.erase i, sgn (ω x) := by
      intro b; apply prod_congr rfl; intro x hx
      rw [Function.update_of_ne (ne_of_mem_erase hx)]
    simp only [h2, Function.update_self, sgn_true, sgn_false]; ring
  simp [this]

/-- Walsh coefficients of the derivative. -/
theorem coeff_D {n : ℕ} (F : (Fin n → Bool) → K) (i : Fin n) (U : Finset (Fin n)) :
    coeff (D i F) U = if i ∈ U then 0 else coeff F (insert i U) := by
  split_ifs with h
  · exact coeff_indep_mem _ i (indep_D i F) U h
  · exact (coeff_insert F U i h).symm

/-- **Number-operator identity** (Efron–Stein energy):
`∑_S |S| ĉ_S² = ∑_i E[(D_i F)²]`. -/
theorem number_operator {n : ℕ} (F : (Fin n → Bool) → K) :
    ∑ S, (S.card : K) * coeff F S ^ 2 = ∑ i, E (fun ω => D i F ω ^ 2) := by
  have h1 : ∀ i, E (fun ω => D i F ω ^ 2) = ∑ S ∈ univ.filter (fun S => i ∈ S), coeff F S ^ 2 := by
    intro i
    have := parseval (D i F) (D i F)
    simp_rw [← sq] at this
    rw [this]
    simp_rw [coeff_D]
    rw [← sum_filter_add_sum_filter_not univ (fun U => i ∈ U)]
    rw [sum_eq_zero (s := univ.filter (fun U => i ∈ U)) (fun U hU => by
      rw [if_pos (mem_filter.mp hU).2]; ring), zero_add]
    apply sum_nbij' (fun U => insert i U) (fun S => S.erase i)
    · intro U hU; simp_all
    · intro S hS; simp_all
    · intro U hU
      simp at hU
      exact erase_insert hU
    · intro S hS
      simp at hS
      exact insert_erase hS
    · intro U hU
      simp only [mem_filter, mem_univ, true_and] at hU
      rw [if_neg hU]
  simp_rw [h1]
  rw [sum_comm' (t' := univ) (s' := fun S => S)
    (h := fun i S => by simp)]
  apply sum_congr rfl; intro S _
  rw [sum_const, nsmul_eq_mul]


/-- **Granular Poincaré inequality** `Var F ≤ ∑_i E[(D_i F)²]`. -/
theorem poincare {n : ℕ} (F : (Fin n → Bool) → K) :
    E (fun ω => F ω ^ 2) - E F ^ 2 ≤ ∑ i, E (fun ω => D i F ω ^ 2) := by
  rw [← number_operator]
  have hp := parseval F F
  simp_rw [← sq] at hp
  rw [hp, ← coeff_empty, ← add_sum_erase univ _ (mem_univ ∅),
    ← add_sum_erase univ (fun S => (S.card : K) * coeff F S ^ 2) (mem_univ ∅)]
  simp only [card_empty, Nat.cast_zero, zero_mul, zero_add, add_sub_cancel_left]
  apply sum_le_sum; intro S hS
  have hne : S ≠ ∅ := ne_of_mem_erase hS
  have : (1 : K) ≤ S.card := by
    exact_mod_cast Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hne)
  nlinarith [sq_nonneg (coeff F S)]

/-- **Tail bound** of the chaos: `∑_{|S| ≥ M} ĉ_S² ≤ (1/M) ∑_i E[(D_i F)²]`. -/
theorem chaos_tail {n : ℕ} (F : (Fin n → Bool) → K) (M : ℕ) (hM : 0 < M) :
    ∑ S ∈ univ.filter (fun S : Finset (Fin n) => M ≤ S.card), coeff F S ^ 2 ≤
      (∑ i, E (fun ω => D i F ω ^ 2)) / M := by
  rw [← number_operator, le_div_iff₀ (by exact_mod_cast hM), sum_mul]
  calc ∑ S ∈ univ.filter (fun S : Finset (Fin n) => M ≤ S.card), coeff F S ^ 2 * M
      ≤ ∑ S ∈ univ.filter (fun S : Finset (Fin n) => M ≤ S.card), (S.card : K) * coeff F S ^ 2 := by
        apply sum_le_sum; intro S hS
        have : (M : K) ≤ S.card := by exact_mod_cast (mem_filter.mp hS).2
        nlinarith [sq_nonneg (coeff F S)]
    _ ≤ ∑ S, (S.card : K) * coeff F S ^ 2 :=
        sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun S _ _ => by positivity)

/-! ## Sharpness example: `W_n² = n s² + J_2(2)` -/

theorem sq_sum_eq {ι : Type*} [DecidableEq ι] (t : Finset ι) (x : ι → K) :
    (∑ i ∈ t, x i) ^ 2 = ∑ i ∈ t, x i ^ 2 + 2 * ∑ S ∈ powersetCard 2 t, ∏ i ∈ S, x i := by
  induction t using Finset.induction_on with
  | empty => simp [Finset.powersetCard_eq_empty.mpr (show (∅ : Finset ι).card < 2 by simp)]
  | insert a t ha ih =>
    have hdisj : Disjoint (powersetCard 2 t) ((powersetCard 1 t).image (insert a)) := by
      rw [disjoint_left]; intro S hS hS'
      obtain ⟨T, -, rfl⟩ := mem_image.mp hS'
      exact ha ((mem_powersetCard.mp hS).1 (mem_insert_self a T))
    have hp : powersetCard 2 (insert a t) =
        powersetCard 2 t ∪ (powersetCard 1 t).image (insert a) := powersetCard_succ_insert ha 1
    rw [sum_insert ha, sum_insert ha, hp, sum_union hdisj, sum_image (by
      intro T hT T' hT' h
      have h1 : a ∉ T := fun h' => ha ((mem_powersetCard.mp (mem_coe.mp hT)).1 h')
      have h2 : a ∉ T' := fun h' => ha ((mem_powersetCard.mp (mem_coe.mp hT')).1 h')
      rw [← erase_insert h1, ← erase_insert h2]; exact congrArg (fun U => U.erase a) h)]
    have h3 : ∑ T ∈ powersetCard 1 t, ∏ i ∈ insert a T, x i = x a * ∑ i ∈ t, x i := by
      rw [mul_sum, powersetCard_one, sum_map]
      apply sum_congr rfl; intro i hi
      have : a ∉ ({i} : Finset ι) := by
        rw [mem_singleton]; rintro rfl; exact ha hi
      simp [prod_insert this]
    rw [h3, add_sq, ih]; ring

/-- The Anderson walk at time `n`. -/
def Wn {n : ℕ} (s : K) (ω : Fin n → Bool) : K := s * ∑ i, sgn (ω i)

theorem W_sq_chaos {n : ℕ} (s : K) (ω : Fin n → Bool) :
    Wn s ω ^ 2 = n * s ^ 2 + J 2 s (fun _ => 2) ω := by
  unfold Wn J
  rw [mul_pow, sq_sum_eq]
  have hs : ∀ i, (sgn (ω i) : K) ^ 2 = 1 := fun i => by rw [sq, sgn_mul_self]
  simp only [hs, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
  have : ∀ S ∈ powersetCard 2 (univ : Finset (Fin n)),
      (2 : K) * ∏ i ∈ S, (s * sgn (ω i)) = s ^ 2 * 2 * ∏ i ∈ S, sgn (ω i) := by
    intro S hS; rw [prod_increments, (mem_powersetCard.mp hS).2]; unfold chi; ring
  rw [sum_congr rfl this, ← mul_sum]; ring

/-- **The discrete stochastic exponential and its chaos.**  For every
kernel `h`, `∏ᵢ (1 + hᵢ ΔWᵢ) = Σₘ Jₘ(h^{⊗m})`: the Walsh chaos of the discrete
exponential is the family of elementary symmetric sums of the `hᵢ ΔWᵢ`. -/
theorem stoch_exp_walsh {n : ℕ} (h : Fin n → K) (s : K) (ω : Fin n → Bool) :
    ∏ i, (1 + h i * (s * sgn (ω i))) =
      ∑ m ∈ range (n + 1), J m s (fun S => ∏ i ∈ S, h i) ω := by
  rw [prod_one_add, sum_powerset, card_univ, Fintype.card_fin]
  apply sum_congr rfl; intro m _
  unfold J
  apply sum_congr rfl; intro S _
  rw [prod_mul_distrib]

end QE.OpenSto.Walsh

/-!
# Granular information geometry

A statistical model with a lattice parameter: `p : (Fin d → ℤ) → S → K`, the
parameter `θ` being the index of the lattice point `h θ`, `h = 2ε`.  The
forward granular difference in direction `a` is
`Δ_a p θ x = (p (θ + e_a) x - p θ x) / h`.  Everything below is an exact
finite identity (finite sums over the finite sample space `S`).
-/

set_option linter.unusedSectionVars false

namespace QE.OpenSto.InfoGeo

open Finset

section Metric

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
variable {S : Type*} [Fintype S] {d : ℕ}

/-- Forward granular difference of a parametric family in direction `a`. -/
def D (h : K) (p : (Fin d → ℤ) → S → K) (a : Fin d) (θ : Fin d → ℤ) (x : S) : K :=
  (p (θ + Pi.single a 1) x - p θ x) / h

/-- Second granular difference `Δ_a Δ_b p`. -/
def D2 (h : K) (p : (Fin d → ℤ) → S → K) (a b : Fin d) (θ : Fin d → ℤ) (x : S) : K :=
  D h (D h p b) a θ x

/-- The granular Fisher metric `g_ab(θ) = ∑_x Δ_a p Δ_b p / p`. -/
def metric (h : K) (p : (Fin d → ℤ) → S → K) (a b : Fin d) (θ : Fin d → ℤ) : K :=
  ∑ x, D h p a θ x * D h p b θ x / p θ x

theorem metric_symm (h : K) (p : (Fin d → ℤ) → S → K) (a b : Fin d) (θ : Fin d → ℤ) :
    metric h p a b θ = metric h p b a θ := by
  unfold metric; congr 1; ext x; ring

/-- Second differences commute (shifts on `ℤ^d` commute). -/
theorem D2_comm (h : K) (p : (Fin d → ℤ) → S → K) (a b : Fin d) (θ : Fin d → ℤ) (x : S) :
    D2 h p a b θ x = D2 h p b a θ x := by
  unfold D2 D
  rw [show θ + Pi.single a 1 + Pi.single b 1 = θ + Pi.single b 1 + Pi.single a 1 by abel]
  ring

/-- The quadratic form of the metric is a sum of squares over the sample space. -/
theorem metric_quadratic_form (h : K) (p : (Fin d → ℤ) → S → K) (θ : Fin d → ℤ)
    (v : Fin d → K) :
    ∑ a, ∑ b, v a * v b * metric h p a b θ = ∑ x, (∑ a, v a * D h p a θ x) ^ 2 / p θ x := by
  have e : ∀ x, (∑ a, v a * D h p a θ x) ^ 2 / p θ x =
      ∑ a, ∑ b, v a * v b * (D h p a θ x * D h p b θ x / p θ x) := by
    intro x
    rw [sq, sum_mul_sum, sum_div]
    apply sum_congr rfl; intro a _
    rw [sum_div]; apply sum_congr rfl; intro b _; ring
  simp_rw [e]
  conv_rhs => rw [sum_comm]
  apply sum_congr rfl; intro a _
  conv_rhs => rw [sum_comm]
  apply sum_congr rfl; intro b _
  unfold metric; rw [mul_sum]

/-- The granular Fisher metric is positive semidefinite. -/
theorem metric_psd (h : K) (p : (Fin d → ℤ) → S → K) (θ : Fin d → ℤ)
    (hp : ∀ x, 0 < p θ x) (v : Fin d → K) :
    0 ≤ ∑ a, ∑ b, v a * v b * metric h p a b θ := by
  rw [metric_quadratic_form]
  exact sum_nonneg fun x _ => div_nonneg (sq_nonneg _) (hp x).le

/-- Diagonal entries: `1 + h² g_aa = ∑ q²/p`, the chi-square divergence between
neighbouring grains, with `q = p(θ + e_a)`. -/
theorem metric_diag_chi2 (h : K) (hh : h ≠ 0) (p : (Fin d → ℤ) → S → K) (a : Fin d)
    (θ : Fin d → ℤ) (hp : ∀ x, p θ x ≠ 0) (hp1 : ∑ x, p θ x = 1)
    (hq1 : ∑ x, p (θ + Pi.single a 1) x = 1) :
    metric h p a a θ = (∑ x, p (θ + Pi.single a 1) x ^ 2 / p θ x - 1) / h ^ 2 := by
  unfold metric D
  have e : ∀ x, (p (θ + Pi.single a 1) x - p θ x) / h * ((p (θ + Pi.single a 1) x - p θ x) / h)
      / p θ x = (p (θ + Pi.single a 1) x ^ 2 / p θ x - 2 * p (θ + Pi.single a 1) x + p θ x) / h ^ 2 := by
    intro x; have := hp x; field_simp; ring
  simp_rw [e, ← sum_div, sum_add_distrib, sum_sub_distrib, ← mul_sum, hp1, hq1]
  ring

/-- Granular `α`-connection coefficients
`Γ^{(α)}_{ab,c} = ∑ Δ_aΔ_b p (Δ_c p + (h/2)Δ_aΔ_c p)/S_a p - ((1+α)/2) ∑ Δ_a p Δ_b p Δ_c p/(p S_a p)`,
with `S_a p = p(θ + e_a)`. -/
def conn (h α : K) (p : (Fin d → ℤ) → S → K) (a b c : Fin d) (θ : Fin d → ℤ) : K :=
  ∑ x, D2 h p a b θ x * (D h p c θ x + h / 2 * D2 h p a c θ x) / p (θ + Pi.single a 1) x
    - (1 + α) / 2 * ∑ x, D h p a θ x * D h p b θ x * D h p c θ x / (p θ x * p (θ + Pi.single a 1) x)

/-- **Exact duality of the granular `α`- and `(-α)`-connections**:
`Δ_a g_bc = Γ^{(α)}_{ab,c} + Γ^{(-α)}_{ac,b}`, with no remainder. -/
theorem duality (h α : K) (hh : h ≠ 0) (p : (Fin d → ℤ) → S → K) (a b c : Fin d)
    (θ : Fin d → ℤ) (hp : ∀ x, p θ x ≠ 0) (hpa : ∀ x, p (θ + Pi.single a 1) x ≠ 0) :
    (metric h p b c (θ + Pi.single a 1) - metric h p b c θ) / h
      = conn h α p a b c θ + conn h (-α) p a c b θ := by
  unfold metric conn
  rw [← sum_sub_distrib, sum_div, mul_sum, mul_sum, ← sum_sub_distrib, ← sum_sub_distrib,
    ← sum_add_distrib]
  apply sum_congr rfl; intro x _
  have h1 := hp x; have h2 := hpa x
  unfold D2 D
  field_simp
  ring

/-- Self-duality at `α = 0`: `Δ_a g_bc = Γ^{(0)}_{ab,c} + Γ^{(0)}_{ac,b}`. -/
theorem self_dual (h : K) (hh : h ≠ 0) (p : (Fin d → ℤ) → S → K) (a b c : Fin d)
    (θ : Fin d → ℤ) (hp : ∀ x, p θ x ≠ 0) (hpa : ∀ x, p (θ + Pi.single a 1) x ≠ 0) :
    (metric h p b c (θ + Pi.single a 1) - metric h p b c θ) / h
      = conn h 0 p a b c θ + conn h 0 p a c b θ := by
  have := duality h 0 hh p a b c θ hp hpa
  rwa [neg_zero] at this

/-- The `α`-family is affine in `α`, with slope the granular skewness (Amari–Chentsov) tensor:
`Γ^{(α)}_{ab,c} = Γ^{(0)}_{ab,c} - (α/2) T_abc`, `T_abc = ∑ Δ_ap Δ_bp Δ_cp/(p S_a p)`. -/
theorem conn_affine (h α : K) (p : (Fin d → ℤ) → S → K) (a b c : Fin d) (θ : Fin d → ℤ) :
    conn h α p a b c θ = conn h 0 p a b c θ
      - α / 2 * ∑ x, D h p a θ x * D h p b θ x * D h p c θ x / (p θ x * p (θ + Pi.single a 1) x) := by
  unfold conn; ring

end Metric

section KL

variable {S : Type*} [Fintype S]

/-- Granular Kullback–Leibler divergence (in nats) on a finite sample space:
`D(q ‖ p) = ∑ q ln (q/p)`. -/
noncomputable def kl (q p : S → ℝ) : ℝ := ∑ x, q x * Real.log (q x / p x)

/-- Third-order expansion of `ln(1+r)` with explicit remainder, `|r| ≤ 1/2`. -/
theorem log_one_add_bound (r : ℝ) (hr : |r| ≤ 1 / 2) :
    |Real.log (1 + r) - (r - r ^ 2 / 2 + r ^ 3 / 3)| ≤ 2 * r ^ 4 := by
  have hlt : |(-r)| < 1 := by rw [abs_neg]; linarith
  have h := Real.abs_log_sub_add_sum_range_le hlt 3
  simp only [sum_range_succ, sum_range_zero, abs_neg, sub_neg_eq_add] at h
  norm_num at h
  have e : Real.log (1 + r) - (r - r ^ 2 / 2 + r ^ 3 / 3)
      = -r + r ^ 2 / 2 + -r ^ 3 / 3 + Real.log (1 + r) := by ring
  rw [e, add_comm 1 r]
  have h4 : |r| ^ 4 = r ^ 4 := by rw [pow_abs, abs_of_nonneg (by positivity)]
  have hpos : (0:ℝ) < 1 - |r| := by linarith
  calc _ ≤ |r| ^ 4 / (1 - |r|) := by
        convert h using 2; ring_nf
    _ ≤ 2 * r ^ 4 := by
        rw [div_le_iff₀ hpos, h4]; nlinarith [abs_nonneg r, pow_two_nonneg (r ^ 2)]

/-- Pointwise expansion of `(1+r) ln(1+r) - r`. -/
theorem phi_bound (r : ℝ) (hr : |r| ≤ 1 / 2) :
    |(1 + r) * Real.log (1 + r) - r - (r ^ 2 / 2 - r ^ 3 / 6)| ≤ 10 / 3 * r ^ 4 := by
  set E := Real.log (1 + r) - (r - r ^ 2 / 2 + r ^ 3 / 3) with hE
  have hb := log_one_add_bound r hr
  rw [← hE] at hb
  have e : (1 + r) * Real.log (1 + r) - r - (r ^ 2 / 2 - r ^ 3 / 6) = r ^ 4 / 3 + (1 + r) * E := by
    rw [hE]; ring
  rw [e]
  have h1 : |1 + r| ≤ 3 / 2 := by rw [abs_le] at hr ⊢; constructor <;> linarith
  have h4 : 0 ≤ r ^ 4 := by positivity
  calc |r ^ 4 / 3 + (1 + r) * E| ≤ |r ^ 4 / 3| + |(1 + r) * E| := abs_add_le _ _
    _ = r ^ 4 / 3 + |1 + r| * |E| := by rw [abs_of_nonneg (by positivity), abs_mul]
    _ ≤ r ^ 4 / 3 + 3 / 2 * (2 * r ^ 4) := by
        gcongr
    _ = 10 / 3 * r ^ 4 := by ring

/-- Pointwise expansion of `r - ln(1+r)`. -/
theorem psi_bound (r : ℝ) (hr : |r| ≤ 1 / 2) :
    |r - Real.log (1 + r) - (r ^ 2 / 2 - r ^ 3 / 3)| ≤ 2 * r ^ 4 := by
  have hb := log_one_add_bound r hr
  rw [show r - Real.log (1 + r) - (r ^ 2 / 2 - r ^ 3 / 3)
    = -(Real.log (1 + r) - (r - r ^ 2 / 2 + r ^ 3 / 3)) by ring, abs_neg]
  exact hb

/-- Granular score of the pair `(p, q)` with step `h`: `s = (q/p - 1)/h`. -/
noncomputable def score (h : ℝ) (p q : S → ℝ) (x : S) : ℝ := (q x / p x - 1) / h

/-- `k`-th score moment `∑ p s^k` (`k = 2`: granular Fisher information; `k = 3`: the
granular skewness `T`; `k = 4`: `Q`). -/
noncomputable def moment (k : ℕ) (h : ℝ) (p q : S → ℝ) : ℝ := ∑ x, p x * score h p q x ^ k

theorem moment_eq (k : ℕ) (h : ℝ) (hh : h ≠ 0) (p q : S → ℝ) :
    h ^ k * moment k h p q = ∑ x, p x * (q x / p x - 1) ^ k := by
  unfold moment score; rw [mul_sum]; apply sum_congr rfl; intro x _
  rw [div_pow]; field_simp

/-- **Exact second-order expansion of the granular KL divergence, forward direction.**
If `|q/p - 1| ≤ 1/2` on `S`, then
`|D(q‖p) - (h²/2) I + (h³/6) T| ≤ (10/3) h⁴ Q`. -/
theorem kl_expansion_fwd (h : ℝ) (hh : h ≠ 0) (p q : S → ℝ) (hp : ∀ x, 0 < p x)
    (hp1 : ∑ x, p x = 1) (hq1 : ∑ x, q x = 1) (hr : ∀ x, |q x / p x - 1| ≤ 1 / 2) :
    |kl q p - (h ^ 2 / 2 * moment 2 h p q - h ^ 3 / 6 * moment 3 h p q)|
      ≤ 10 / 3 * (h ^ 4 * moment 4 h p q) := by
  have m2 := moment_eq 2 h hh p q
  have m3 := moment_eq 3 h hh p q
  have m4 := moment_eq 4 h hh p q
  have e1 : h ^ 2 / 2 * moment 2 h p q - h ^ 3 / 6 * moment 3 h p q
      = ∑ x, p x * ((q x / p x - 1) ^ 2 / 2 - (q x / p x - 1) ^ 3 / 6) := by
    rw [show h ^ 2 / 2 * moment 2 h p q - h ^ 3 / 6 * moment 3 h p q
      = (h ^ 2 * moment 2 h p q) / 2 - (h ^ 3 * moment 3 h p q) / 6 by ring, m2, m3,
      sum_div, sum_div, ← sum_sub_distrib]
    apply sum_congr rfl; intro x _; ring
  have e0 : kl q p = ∑ x, p x * ((1 + (q x / p x - 1)) * Real.log (1 + (q x / p x - 1))
      - (q x / p x - 1)) := by
    unfold kl
    have hs : ∑ x, p x * (q x / p x - 1) = 0 := by
      have : ∀ x, p x * (q x / p x - 1) = q x - p x := by
        intro x; have := (hp x).ne'; field_simp
      simp_rw [this, sum_sub_distrib, hp1, hq1, sub_self]
    rw [← sub_zero (∑ x, q x * _), ← hs, ← sum_sub_distrib]
    apply sum_congr rfl; intro x _
    have := (hp x).ne'
    rw [show 1 + (q x / p x - 1) = q x / p x by ring]
    field_simp
  rw [e0, e1, m4, ← sum_sub_distrib, mul_sum]
  refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun x _ => ?_)
  rw [← mul_sub, abs_mul, abs_of_pos (hp x)]
  have := phi_bound (q x / p x - 1) (hr x)
  nlinarith [hp x]

/-- **Exact second-order expansion of the granular KL divergence, reverse direction.**
`|D(p‖q) - (h²/2) I + (h³/3) T| ≤ 2 h⁴ Q`. -/
theorem kl_expansion_rev (h : ℝ) (hh : h ≠ 0) (p q : S → ℝ) (hp : ∀ x, 0 < p x)
    (hp1 : ∑ x, p x = 1) (hq1 : ∑ x, q x = 1) (hr : ∀ x, |q x / p x - 1| ≤ 1 / 2) :
    |kl p q - (h ^ 2 / 2 * moment 2 h p q - h ^ 3 / 3 * moment 3 h p q)|
      ≤ 2 * (h ^ 4 * moment 4 h p q) := by
  have m2 := moment_eq 2 h hh p q
  have m3 := moment_eq 3 h hh p q
  have m4 := moment_eq 4 h hh p q
  have e1 : h ^ 2 / 2 * moment 2 h p q - h ^ 3 / 3 * moment 3 h p q
      = ∑ x, p x * ((q x / p x - 1) ^ 2 / 2 - (q x / p x - 1) ^ 3 / 3) := by
    rw [show h ^ 2 / 2 * moment 2 h p q - h ^ 3 / 3 * moment 3 h p q
      = (h ^ 2 * moment 2 h p q) / 2 - (h ^ 3 * moment 3 h p q) / 3 by ring, m2, m3,
      sum_div, sum_div, ← sum_sub_distrib]
    apply sum_congr rfl; intro x _; ring
  have e0 : kl p q = ∑ x, p x * ((q x / p x - 1) - Real.log (1 + (q x / p x - 1))) := by
    unfold kl
    have hs : ∑ x, p x * (q x / p x - 1) = 0 := by
      have : ∀ x, p x * (q x / p x - 1) = q x - p x := by
        intro x; have := (hp x).ne'; field_simp
      simp_rw [this, sum_sub_distrib, hp1, hq1, sub_self]
    rw [← zero_add (∑ x, p x * Real.log _), ← hs, ← sum_add_distrib]
    apply sum_congr rfl; intro x _
    have hpx := (hp x).ne'
    have hqx : 0 < q x / p x := by
      have := hr x; rw [abs_le] at this; linarith [this.1]
    rw [show 1 + (q x / p x - 1) = q x / p x by ring, show p x / q x = (q x / p x)⁻¹ by
      rw [inv_div], Real.log_inv]
    ring
  rw [e0, e1, m4, ← sum_sub_distrib, mul_sum]
  refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun x _ => ?_)
  rw [← mul_sub, abs_mul, abs_of_pos (hp x)]
  have := psi_bound (q x / p x - 1) (hr x)
  nlinarith [hp x]

/-- Asymmetry of the granular KL divergence: `D(q‖p) - D(p‖q) = (h³/6) T + R`,
`|R| ≤ (16/3) h⁴ Q`. -/
theorem kl_asymmetry (h : ℝ) (hh : h ≠ 0) (p q : S → ℝ) (hp : ∀ x, 0 < p x)
    (hp1 : ∑ x, p x = 1) (hq1 : ∑ x, q x = 1) (hr : ∀ x, |q x / p x - 1| ≤ 1 / 2) :
    |kl q p - kl p q - h ^ 3 / 6 * moment 3 h p q| ≤ 16 / 3 * (h ^ 4 * moment 4 h p q) := by
  have h1 := kl_expansion_fwd h hh p q hp hp1 hq1 hr
  have h2 := kl_expansion_rev h hh p q hp hp1 hq1 hr
  have := abs_sub (kl q p - (h ^ 2 / 2 * moment 2 h p q - h ^ 3 / 6 * moment 3 h p q))
    (kl p q - (h ^ 2 / 2 * moment 2 h p q - h ^ 3 / 3 * moment 3 h p q))
  calc _ = |(kl q p - (h ^ 2 / 2 * moment 2 h p q - h ^ 3 / 6 * moment 3 h p q))
      - (kl p q - (h ^ 2 / 2 * moment 2 h p q - h ^ 3 / 3 * moment 3 h p q))| := by ring_nf
    _ ≤ _ := by linarith

/-! ## Quantisation of the data -/

section Quant

variable {S' : Type*} [Fintype S'] [DecidableEq S']

/-- Push-forward of a law under the quantiser `Q : S → S'` (coarse-graining of the data). -/
def push (Q : S → S') (p : S → ℝ) (y : S') : ℝ := ∑ x with Q x = y, p x

theorem push_pos (Q : S → S') (p : S → ℝ) (hp : ∀ x, 0 < p x) (x : S) : 0 < push Q p (Q x) :=
  lt_of_lt_of_le (hp x) (single_le_sum (f := p) (fun x' _ => (hp x').le)
    (mem_filter.2 ⟨mem_univ x, rfl⟩))

theorem push_eq_zero_fibre (Q : S → S') (p : S → ℝ) (hp : ∀ x, 0 < p x) (y : S')
    (h0 : push Q p y = 0) : ∀ x, Q x ≠ y := by
  intro x hx; have := push_pos Q p hp x; rw [hx, h0] at this; exact lt_irrefl _ this

/-- The score of the quantised model is the conditional mean of the score on the cell:
`∑_{Q x = y} p s = p^Q(y) s^Q(y)`. -/
theorem fibre_score (h : ℝ) (hh : h ≠ 0) (Q : S → S') (p q : S → ℝ) (hp : ∀ x, 0 < p x)
    (y : S') :
    ∑ x with Q x = y, p x * score h p q x = push Q p y * score h (push Q p) (push Q q) y := by
  have e : ∀ x, p x * score h p q x = (q x - p x) / h := by
    intro x; unfold score; have := (hp x).ne'; field_simp
  simp_rw [e]
  rw [← sum_div, sum_sub_distrib]
  unfold score
  by_cases h0 : push Q p y = 0
  · have hq : push Q q y = 0 := by
      unfold push; rw [filter_false_of_mem (fun x _ => push_eq_zero_fibre Q p hp y h0 x)]; simp
    rw [h0]; unfold push at hq h0; rw [hq, h0]; simp
  · unfold push at h0 ⊢; field_simp

/-- **Exact information loss by quantisation of the data (Pythagorean identity).**
`I_ε[p,q] = I_ε[p^Q,q^Q] + ∑_x p(x) (s(x) - s^Q(Q x))²`. -/
theorem fisher_quantisation (h : ℝ) (hh : h ≠ 0) (Q : S → S') (p q : S → ℝ)
    (hp : ∀ x, 0 < p x) :
    moment 2 h p q = moment 2 h (push Q p) (push Q q)
      + ∑ x, p x * (score h p q x - score h (push Q p) (push Q q) (Q x)) ^ 2 := by
  set t := score h (push Q p) (push Q q)
  have hA : ∑ x, p x * score h p q x * t (Q x) = ∑ y, push Q p y * t y ^ 2 := by
    rw [← sum_fiberwise univ Q (fun x => p x * score h p q x * t (Q x))]
    apply sum_congr rfl; intro y _
    rw [sum_congr rfl (g := fun x => p x * score h p q x * t y)
      (fun x hx => by rw [(mem_filter.1 hx).2]), ← sum_mul, fibre_score h hh Q p q hp y]
    ring
  have hB : ∑ x, p x * t (Q x) ^ 2 = ∑ y, push Q p y * t y ^ 2 := by
    rw [← sum_fiberwise univ Q (fun x => p x * t (Q x) ^ 2)]
    apply sum_congr rfl; intro y _
    rw [sum_congr rfl (g := fun x => p x * t y ^ 2)
      (fun x hx => by rw [(mem_filter.1 hx).2]), ← sum_mul]
    rfl
  have e : ∀ x, p x * (score h p q x - t (Q x)) ^ 2
      = p x * score h p q x ^ 2 - 2 * (p x * score h p q x * t (Q x)) + p x * t (Q x) ^ 2 := by
    intro x; ring
  simp_rw [e, sum_add_distrib, sum_sub_distrib, ← mul_sum, hA, hB]
  unfold moment; ring

/-- Quantisation never increases the granular Fisher information. -/
theorem fisher_quantisation_le (h : ℝ) (hh : h ≠ 0) (Q : S → S') (p q : S → ℝ)
    (hp : ∀ x, 0 < p x) : moment 2 h (push Q p) (push Q q) ≤ moment 2 h p q := by
  rw [fisher_quantisation h hh Q p q hp]
  have : 0 ≤ ∑ x, p x * (score h p q x - score h (push Q p) (push Q q) (Q x)) ^ 2 :=
    sum_nonneg fun x _ => mul_nonneg (hp x).le (sq_nonneg _)
  linarith

/-- No information is lost iff the score is constant on every quantisation cell. -/
theorem fisher_quantisation_eq_iff (h : ℝ) (hh : h ≠ 0) (Q : S → S') (p q : S → ℝ)
    (hp : ∀ x, 0 < p x) :
    moment 2 h (push Q p) (push Q q) = moment 2 h p q ↔
      ∀ x, score h p q x = score h (push Q p) (push Q q) (Q x) := by
  rw [fisher_quantisation h hh Q p q hp]
  constructor
  · intro heq x
    have h0 : ∑ x, p x * (score h p q x - score h (push Q p) (push Q q) (Q x)) ^ 2 = 0 := by
      linarith
    rw [sum_eq_zero_iff_of_nonneg (fun x _ => mul_nonneg (hp x).le (sq_nonneg _))] at h0
    have := h0 x (mem_univ x)
    rcases mul_eq_zero.1 this with h1 | h1
    · exact absurd h1 (hp x).ne'
    · exact sub_eq_zero.1 (pow_eq_zero_iff two_ne_zero |>.1 h1)
  · intro hc
    have : ∑ x, p x * (score h p q x - score h (push Q p) (push Q q) (Q x)) ^ 2 = 0 :=
      sum_eq_zero fun x _ => by rw [hc x, sub_self]; ring
    rw [this, add_zero]

/-- **Exact bound on the information lost.** If the score varies by at most `c` inside
every cell, the loss is at most `c²`. (Cells of diameter `δ` and a score that is
`Λ`-Lipschitz in the data give `c = Λ δ`: the loss is of second order in the mesh.) -/
theorem fisher_loss_le (h : ℝ) (hh : h ≠ 0) (Q : S → S') (p q : S → ℝ)
    (hp : ∀ x, 0 < p x) (hp1 : ∑ x, p x = 1) (c : ℝ)
    (hc : ∀ x x', Q x = Q x' → |score h p q x - score h p q x'| ≤ c) :
    moment 2 h p q - moment 2 h (push Q p) (push Q q) ≤ c ^ 2 := by
  rw [fisher_quantisation h hh Q p q hp, add_sub_cancel_left]
  have hpt : ∀ x, |score h p q x - score h (push Q p) (push Q q) (Q x)| ≤ c := by
    intro x
    set y := Q x
    have hP := push_pos Q p hp x
    have key : push Q p y * (score h p q x - score h (push Q p) (push Q q) y)
        = ∑ x' with Q x' = y, p x' * (score h p q x - score h p q x') := by
      rw [mul_sub, ← fibre_score h hh Q p q hp y]
      simp_rw [mul_sub]; rw [sum_sub_distrib, ← sum_mul]; rfl
    have hb : |push Q p y * (score h p q x - score h (push Q p) (push Q q) y)| ≤ push Q p y * c := by
      rw [key]
      refine (abs_sum_le_sum_abs _ _).trans ?_
      unfold push; rw [sum_mul]
      apply sum_le_sum; intro x' hx'
      rw [abs_mul, abs_of_pos (hp x')]
      exact mul_le_mul_of_nonneg_left (hc x x' (mem_filter.1 hx').2.symm) (hp x').le
    rw [abs_mul, abs_of_pos hP] at hb
    exact le_of_mul_le_mul_left hb hP
  calc ∑ x, p x * (score h p q x - score h (push Q p) (push Q q) (Q x)) ^ 2
      ≤ ∑ x, p x * c ^ 2 := by
        apply sum_le_sum; intro x _
        apply mul_le_mul_of_nonneg_left _ (hp x).le
        have := hpt x
        have hc0 : 0 ≤ c := (abs_nonneg _).trans this
        rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) this 2
    _ = c ^ 2 := by rw [← sum_mul, hp1, one_mul]

/-- Gibbs' inequality, unnormalised form on a finite set: `∑ q ln(q/p) ≥ ∑ q - ∑ p`. -/
theorem gibbs {ι : Type*} (A : Finset ι) (q p : ι → ℝ) (hq : ∀ x ∈ A, 0 < q x)
    (hp : ∀ x ∈ A, 0 < p x) : ∑ x ∈ A, q x - ∑ x ∈ A, p x ≤ ∑ x ∈ A, q x * Real.log (q x / p x) := by
  rw [← sum_sub_distrib]
  apply sum_le_sum; intro x hx
  have h1 := Real.one_sub_inv_le_log_of_pos (div_pos (hq x hx) (hp x hx))
  rw [inv_div] at h1
  have : q x * (1 - p x / q x) = q x - p x := by have := (hq x hx).ne'; field_simp
  nlinarith [hq x hx]

/-- **Chain rule for the granular KL divergence under quantisation**:
`D(q‖p) = D(q^Q‖p^Q) + ∑_y q^Q(y) D(q(·|y) ‖ p(·|y))`. -/
theorem kl_chain (Q : S → S') (p q : S → ℝ) (hp : ∀ x, 0 < p x) (hq : ∀ x, 0 < q x) :
    kl q p = kl (push Q q) (push Q p) + ∑ y, push Q q y *
      ∑ x with Q x = y, q x / push Q q y * Real.log ((q x / push Q q y) / (p x / push Q p y)) := by
  have e : ∀ y, push Q q y * ∑ x with Q x = y,
      q x / push Q q y * Real.log ((q x / push Q q y) / (p x / push Q p y))
      = ∑ x with Q x = y, q x * Real.log (q x / p x)
        - push Q q y * Real.log (push Q q y / push Q p y) := by
    intro y
    rw [mul_sum]
    have hsum : push Q q y * Real.log (push Q q y / push Q p y)
        = ∑ x with Q x = y, q x * Real.log (push Q q y / push Q p y) := by
      unfold push; rw [sum_mul]
    rw [hsum, ← sum_sub_distrib]
    apply sum_congr rfl; intro x hx
    have hy := (mem_filter.1 hx).2
    have hQ := push_pos Q q hq x; have hP := push_pos Q p hp x
    rw [hy] at hQ hP
    have hqx := hq x; have hpx := hp x
    rw [show (q x / push Q q y) / (p x / push Q p y) = (q x / p x) / (push Q q y / push Q p y) by
      field_simp, Real.log_div (by positivity) (by positivity)]
    field_simp
  simp_rw [e, sum_sub_distrib]
  unfold kl
  rw [sum_fiberwise univ Q (fun x => q x * Real.log (q x / p x))]
  ring

/-- **Data processing**: quantising the data cannot increase the granular KL divergence. -/
theorem kl_quantisation_le (Q : S → S') (p q : S → ℝ) (hp : ∀ x, 0 < p x) (hq : ∀ x, 0 < q x) :
    kl (push Q q) (push Q p) ≤ kl q p := by
  rw [kl_chain Q p q hp hq]
  have : 0 ≤ ∑ y, push Q q y *
      ∑ x with Q x = y, q x / push Q q y * Real.log ((q x / push Q q y) / (p x / push Q p y)) := by
    apply sum_nonneg; intro y _
    by_cases hne : (univ.filter fun x => Q x = y).Nonempty
    · obtain ⟨x0, hx0⟩ := hne
      have hy := (mem_filter.1 hx0).2
      have hQ := push_pos Q q hq x0; have hP := push_pos Q p hp x0
      rw [hy] at hQ hP
      apply mul_nonneg hQ.le
      have g := gibbs (univ.filter fun x => Q x = y) (fun x => q x / push Q q y)
        (fun x => p x / push Q p y) (fun x _ => div_pos (hq x) hQ) (fun x _ => div_pos (hp x) hP)
      have h1 : ∑ x with Q x = y, q x / push Q q y = 1 := by
        rw [← sum_div]; exact div_self hQ.ne'
      have h2 : ∑ x with Q x = y, p x / push Q p y = 1 := by
        rw [← sum_div]; exact div_self hP.ne'
      rw [h1, h2, sub_self] at g; exact g
    · rw [not_nonempty_iff_eq_empty.1 hne, sum_empty, mul_zero]
  linarith

end Quant

end KL

/-! ## Shadows: a differentiable one-parameter family on a finite sample space -/

section Shadow

variable {S : Type*} [Fintype S]
open Filter Topology

/-- The score moments of the granular family converge to the classical ones:
`∑ p s_h^k → ∑ p (∂p/p)^k` as `h → 0⁺`. For `k = 2`: the granular Fisher information has
the classical Fisher information as its shadow. -/
theorem moment_tendsto (k : ℕ) (p : ℝ → S → ℝ) (θ : ℝ) (p' : S → ℝ)
    (hd : ∀ x, HasDerivAt (fun t => p t x) (p' x) θ) (hp : ∀ x, 0 < p θ x) :
    Tendsto (fun h => moment k h (p θ) (p (θ + h))) (𝓝[>] 0)
      (𝓝 (∑ x, p θ x * (p' x / p θ x) ^ k)) := by
  have hev : ∀ᶠ h in 𝓝[>] (0:ℝ), moment k h (p θ) (p (θ + h))
      = ∑ x, p θ x * ((h⁻¹ • (p (θ + h) x - p θ x)) / p θ x) ^ k := by
    filter_upwards [self_mem_nhdsWithin] with h hh
    unfold moment score
    apply sum_congr rfl; intro x _
    have := (hp x).ne'; have : h ≠ 0 := ne_of_gt hh
    congr 2; rw [smul_eq_mul]; field_simp
  refine Tendsto.congr' (EventuallyEq.symm hev) ?_
  apply tendsto_finsetSum; intro x _
  exact (((hd x).tendsto_slope_zero_right.div_const _).pow k).const_mul _

/-- Shadow of the forward granular Fisher information. -/
theorem fisher_shadow (p : ℝ → S → ℝ) (θ : ℝ) (p' : S → ℝ)
    (hd : ∀ x, HasDerivAt (fun t => p t x) (p' x) θ) (hp : ∀ x, 0 < p θ x) :
    Tendsto (fun h => moment 2 h (p θ) (p (θ + h))) (𝓝[>] 0) (𝓝 (∑ x, p' x ^ 2 / p θ x)) := by
  have := moment_tendsto 2 p θ p' hd hp
  convert this using 2
  apply sum_congr rfl; intro x _; have := (hp x).ne'; field_simp

/-- **Shadow of the granular KL divergence**: `D(p_{θ+h} ‖ p_θ)/h² → I(θ)/2`, the
classical second-order behaviour of the relative entropy (Fisher information as its Hessian). -/
theorem kl_shadow (p : ℝ → S → ℝ) (θ : ℝ) (p' : S → ℝ)
    (hd : ∀ x, HasDerivAt (fun t => p t x) (p' x) θ) (hp : ∀ x, 0 < p θ x)
    (hn : ∀ t, ∑ x, p t x = 1) :
    Tendsto (fun h => kl (p (θ + h)) (p θ) / h ^ 2) (𝓝[>] 0)
      (𝓝 ((∑ x, p' x ^ 2 / p θ x) / 2)) := by
  set I := ∑ x, p' x ^ 2 / p θ x
  have hI := fisher_shadow p θ p' hd hp
  have hT := moment_tendsto 3 p θ p' hd hp
  have hQ := moment_tendsto 4 p θ p' hd hp
  -- eventually the ratio q/p is within 1/2 of 1
  have hr : ∀ᶠ h in 𝓝[>] (0:ℝ), ∀ x, |p (θ + h) x / p θ x - 1| ≤ 1 / 2 := by
    rw [eventually_all]; intro x
    have hc : Tendsto (fun h => p (θ + h) x / p θ x - 1) (𝓝[>] 0) (𝓝 0) := by
      have h1 : Tendsto (fun h => p (θ + h) x) (𝓝 0) (𝓝 (p θ x)) := by
        have h2 : Tendsto (fun h : ℝ => θ + h) (𝓝 0) (𝓝 θ) := by
          simpa using (tendsto_const_nhds (x := θ)).add (tendsto_id (x := 𝓝 (0:ℝ)))
        exact (hd x).continuousAt.tendsto.comp h2
      have := ((h1.mono_left (nhdsWithin_le_nhds (s := Set.Ioi 0))).div_const (p θ x)).sub_const 1
      rwa [div_self (hp x).ne', sub_self] at this
    have := hc (Metric.closedBall_mem_nhds 0 (by norm_num : (0:ℝ) < 1 / 2))
    filter_upwards [this] with h hh
    simpa [Real.dist_eq] using hh
  -- main term
  have hmain : Tendsto (fun h => moment 2 h (p θ) (p (θ + h)) / 2
      - h / 6 * moment 3 h (p θ) (p (θ + h))) (𝓝[>] 0) (𝓝 (I / 2)) := by
    have h0 : Tendsto (fun h : ℝ => h) (𝓝[>] 0) (𝓝 0) := nhdsWithin_le_nhds
    have := (hI.div_const 2).sub ((h0.div_const 6).mul hT)
    simpa using this
  have herr : Tendsto (fun h => kl (p (θ + h)) (p θ) / h ^ 2 -
      (moment 2 h (p θ) (p (θ + h)) / 2 - h / 6 * moment 3 h (p θ) (p (θ + h))))
      (𝓝[>] 0) (𝓝 0) := by
    have hb : Tendsto (fun h : ℝ => 10 / 3 * (h ^ 2 * moment 4 h (p θ) (p (θ + h))))
        (𝓝[>] 0) (𝓝 0) := by
      have h0 : Tendsto (fun h : ℝ => h ^ 2) (𝓝[>] 0) (𝓝 0) := by
        have : Tendsto (fun h : ℝ => h ^ 2) (𝓝 0) (𝓝 0) := by
          simpa using (continuous_pow 2).tendsto (0:ℝ)
        exact this.mono_left nhdsWithin_le_nhds
      simpa using (h0.mul hQ).const_mul (10 / 3)
    apply squeeze_zero_norm' _ hb
    filter_upwards [hr, self_mem_nhdsWithin] with h hrh hh
    have hh0 : (h:ℝ) ≠ 0 := ne_of_gt hh
    have key := kl_expansion_fwd h hh0 (p θ) (p (θ + h)) hp (hn θ) (hn (θ + h)) hrh
    rw [Real.norm_eq_abs]
    have hpos : 0 < h ^ 2 := by positivity
    have e : kl (p (θ + h)) (p θ) / h ^ 2 - (moment 2 h (p θ) (p (θ + h)) / 2
        - h / 6 * moment 3 h (p θ) (p (θ + h)))
        = (kl (p (θ + h)) (p θ) - (h ^ 2 / 2 * moment 2 h (p θ) (p (θ + h))
          - h ^ 3 / 6 * moment 3 h (p θ) (p (θ + h)))) / h ^ 2 := by
      field_simp
    rw [e, abs_div, abs_of_pos hpos, div_le_iff₀ hpos]
    calc _ ≤ 10 / 3 * (h ^ 4 * moment 4 h (p θ) (p (θ + h))) := key
      _ = _ := by ring
  have := herr.add hmain
  simpa using this

/-- Second-order behaviour of the forward difference quotient:
`((f(θ+h) - f θ)/h - f'(θ))/h → f''(θ)/2` as `h → 0⁺` (L'Hôpital). -/
theorem second_order_fwd (f f1 : ℝ → ℝ) (θ c : ℝ) (hf : ∀ t, HasDerivAt f (f1 t) t)
    (hf1 : HasDerivAt f1 c θ) :
    Tendsto (fun h => ((f (θ + h) - f θ) / h - f1 θ) / h) (𝓝[>] 0) (𝓝 (c / 2)) := by
  have hF : ∀ h, HasDerivAt (fun h => f (θ + h) - f θ - h * f1 θ) (f1 (θ + h) - f1 θ) h := by
    intro h
    have h1 : HasDerivAt (fun h => f (θ + h)) (f1 (θ + h)) h := by
      exact (hf (θ + h)).comp_const_add θ h
    have h2 : HasDerivAt (fun h : ℝ => h * f1 θ) (1 * f1 θ) h := (hasDerivAt_id h).mul_const _
    convert (h1.sub_const (f θ)).sub h2 using 1; ring
  have hG : ∀ h : ℝ, HasDerivAt (fun h : ℝ => h ^ 2) (2 * h) h := by
    intro h; simpa using hasDerivAt_pow 2 h
  have hlim : Tendsto (fun h => (f1 (θ + h) - f1 θ) / (2 * h)) (𝓝[>] 0) (𝓝 (c / 2)) := by
    have := (hf1.tendsto_slope_zero_right).div_const 2
    refine this.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with h hh
    simp only [smul_eq_mul]; have : h ≠ 0 := ne_of_gt hh; field_simp
  have hcont : ∀ t, ContinuousAt f t := fun t => (hf t).continuousAt
  have hFa : Tendsto (fun h => f (θ + h) - f θ - h * f1 θ) (𝓝[>] 0) (𝓝 0) := by
    have : Tendsto (fun h => f (θ + h) - f θ - h * f1 θ) (𝓝 0) (𝓝 (f (θ + 0) - f θ - 0 * f1 θ)) :=
      (((hcont (θ + 0)).tendsto.comp (tendsto_const_nhds.add tendsto_id)).sub_const _).sub
        (tendsto_id.mul_const _)
    simpa using this.mono_left nhdsWithin_le_nhds
  have hGa : Tendsto (fun h : ℝ => h ^ 2) (𝓝[>] 0) (𝓝 0) := by
    have : Tendsto (fun h : ℝ => h ^ 2) (𝓝 0) (𝓝 0) := by
      simpa using (continuous_pow 2).tendsto (0:ℝ)
    exact this.mono_left nhdsWithin_le_nhds
  have hL := HasDerivAt.lhopital_zero_nhdsGT (Eventually.of_forall hF) (Eventually.of_forall hG)
    (by filter_upwards [self_mem_nhdsWithin] with h hh; exact mul_ne_zero two_ne_zero (ne_of_gt hh))
    hFa hGa hlim
  refine hL.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with h hh
  have : h ≠ 0 := ne_of_gt hh
  field_simp

/-- Same from the left: `((f(θ-h) - f θ)/h + f'(θ))/h → f''(θ)/2`. -/
theorem second_order_bwd (f f1 : ℝ → ℝ) (θ c : ℝ) (hf : ∀ t, HasDerivAt f (f1 t) t)
    (hf1 : HasDerivAt f1 c θ) :
    Tendsto (fun h => ((f (θ - h) - f θ) / h + f1 θ) / h) (𝓝[>] 0) (𝓝 (c / 2)) := by
  have hg : ∀ t, HasDerivAt (fun t => f (-t)) (-f1 (-t)) t := by
    intro t
    have := (hf (-t)).comp t (hasDerivAt_neg t)
    simpa [Function.comp_def] using this
  have hg1 : HasDerivAt (fun t => -f1 (-t)) c (-θ) := by
    have h0 : HasDerivAt f1 c (-(-θ)) := by simpa using hf1
    have := (h0.comp (-θ) (hasDerivAt_neg (-θ))).neg
    convert this using 1
    · ext t; simp
    · ring
  have := second_order_fwd (fun t => f (-t)) (fun t => -f1 (-t)) (-θ) c hg hg1
  refine this.congr' (Eventually.of_forall fun h => ?_)
  simp only [neg_neg, neg_add_eq_sub, neg_sub]
  ring

/-- The two-sided score difference behind the retained terms. -/
private theorem fisher_retained_aux (p p1 : ℝ → S → ℝ) (θ : ℝ) (p2 : S → ℝ) (σ : ℝ)
    (u : ℝ → S → ℝ) (hu : ∀ x, Tendsto (fun h => u h x) (𝓝[>] 0) (𝓝 (p2 x / 2))) :
    Tendsto (fun h => ∑ x, (2 * σ * p1 θ x * u h x + h * u h x ^ 2) / p θ x) (𝓝[>] 0)
      (𝓝 (σ * ∑ x, p1 θ x * p2 x / p θ x)) := by
  rw [mul_sum]
  apply tendsto_finsetSum; intro x _
  have h0 : Tendsto (fun h : ℝ => h) (𝓝[>] 0) (𝓝 0) := nhdsWithin_le_nhds
  have := ((((hu x).const_mul (2 * σ * p1 θ x)).add (h0.mul ((hu x).pow 2))).div_const (p θ x))
  convert this using 2; simp; ring

/-- **The retained `O(ε)` term of the forward granular Fisher information is the mixture
connection**: `(I⁺_h - I)/h → Γ^{(m)} = ∑ ∂p ∂²p / p` (the `α = -1` connection
coefficient `E[∂²ℓ ∂ℓ] + T` of the classical theory). -/
theorem fisher_retained_fwd (p p1 : ℝ → S → ℝ) (θ : ℝ) (p2 : S → ℝ)
    (hd : ∀ x t, HasDerivAt (fun t => p t x) (p1 t x) t)
    (hd2 : ∀ x, HasDerivAt (fun t => p1 t x) (p2 x) θ) (hp : ∀ x, 0 < p θ x) :
    Tendsto (fun h => (moment 2 h (p θ) (p (θ + h)) - ∑ x, p1 θ x ^ 2 / p θ x) / h) (𝓝[>] 0)
      (𝓝 (∑ x, p1 θ x * p2 x / p θ x)) := by
  set u : ℝ → S → ℝ := fun h x => ((p (θ + h) x - p θ x) / h - p1 θ x) / h
  have hu : ∀ x, Tendsto (fun h => u h x) (𝓝[>] 0) (𝓝 (p2 x / 2)) := fun x =>
    second_order_fwd (fun t => p t x) (fun t => p1 t x) θ (p2 x) (hd x) (hd2 x)
  have := fisher_retained_aux p p1 θ p2 1 u hu
  rw [one_mul] at this
  refine this.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with h hh
  have hh0 : h ≠ 0 := ne_of_gt hh
  unfold moment score
  rw [← sum_sub_distrib, sum_div]
  apply sum_congr rfl; intro x _
  have := (hp x).ne'
  simp only [u]
  field_simp; ring

/-- Backward version: `(I⁻_h - I)/h → -Γ^{(m)}`, with `I⁻_h` built from `p_{θ-h}`. -/
theorem fisher_retained_bwd (p p1 : ℝ → S → ℝ) (θ : ℝ) (p2 : S → ℝ)
    (hd : ∀ x t, HasDerivAt (fun t => p t x) (p1 t x) t)
    (hd2 : ∀ x, HasDerivAt (fun t => p1 t x) (p2 x) θ) (hp : ∀ x, 0 < p θ x) :
    Tendsto (fun h => (moment 2 h (p θ) (p (θ - h)) - ∑ x, p1 θ x ^ 2 / p θ x) / h) (𝓝[>] 0)
      (𝓝 (-∑ x, p1 θ x * p2 x / p θ x)) := by
  set u : ℝ → S → ℝ := fun h x => ((p (θ - h) x - p θ x) / h + p1 θ x) / h
  have hu : ∀ x, Tendsto (fun h => u h x) (𝓝[>] 0) (𝓝 (p2 x / 2)) := fun x =>
    second_order_bwd (fun t => p t x) (fun t => p1 t x) θ (p2 x) (hd x) (hd2 x)
  have := fisher_retained_aux p p1 θ p2 (-1) u hu
  rw [neg_one_mul] at this
  refine this.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with h hh
  have hh0 : h ≠ 0 := ne_of_gt hh
  unfold moment score
  rw [← sum_sub_distrib, sum_div]
  apply sum_congr rfl; intro x _
  have := (hp x).ne'
  simp only [u]
  field_simp; ring

/-- **The symmetrised granular Fisher information has no `O(ε)` retained term**:
`((I⁺_h + I⁻_h)/2 - I)/h → 0`. -/
theorem fisher_central (p p1 : ℝ → S → ℝ) (θ : ℝ) (p2 : S → ℝ)
    (hd : ∀ x t, HasDerivAt (fun t => p t x) (p1 t x) t)
    (hd2 : ∀ x, HasDerivAt (fun t => p1 t x) (p2 x) θ) (hp : ∀ x, 0 < p θ x) :
    Tendsto (fun h => ((moment 2 h (p θ) (p (θ + h)) + moment 2 h (p θ) (p (θ - h))) / 2
      - ∑ x, p1 θ x ^ 2 / p θ x) / h) (𝓝[>] 0) (𝓝 0) := by
  have := ((fisher_retained_fwd p p1 θ p2 hd hd2 hp).add
    (fisher_retained_bwd p p1 θ p2 hd hd2 hp)).div_const 2
  rw [add_neg_cancel, zero_div] at this
  refine this.congr' (Eventually.of_forall fun h => ?_)
  simp only; ring

end Shadow

/-! ## Shadows of the multi-parameter metric and `α`-connections -/

section ConnShadow

variable {S : Type*} [Fintype S] {d : ℕ}
open Filter Topology

/-- First-order directional difference quotient. -/
theorem dir_slope (f : (Fin d → ℝ) → ℝ) (f' : (Fin d → ℝ) →L[ℝ] ℝ) (θ0 : Fin d → ℝ)
    (hf : HasFDerivAt f f' θ0) (v : Fin d → ℝ) :
    Tendsto (fun h : ℝ => (f (θ0 + h • v) - f θ0) / h) (𝓝[>] 0) (𝓝 (f' v)) := by
  have hl : HasDerivAt (fun t : ℝ => θ0 + t • v) v 0 := by
    simpa using ((hasDerivAt_id (0:ℝ)).smul_const v).const_add θ0
  have hg : HasDerivAt (fun t : ℝ => f (θ0 + t • v)) (f' v) 0 := by
    have := (show HasFDerivAt f f' (θ0 + (0:ℝ) • v) by simpa using hf).comp_hasDerivAt (0:ℝ) hl
    simpa [Function.comp_def] using this
  refine hg.tendsto_slope_zero_right.congr' (Eventually.of_forall fun h => ?_)
  simp only [zero_add, zero_smul, add_zero, smul_eq_mul]; ring

/-- **Second difference quotients converge to the second derivative.** If `f` is
differentiable on `ℝ^d` with derivative `f'`, and `f'` is differentiable at `θ0` with
derivative `f''`, then `(f(θ0+hv+hw) - f(θ0+hv) - f(θ0+hw) + f θ0)/h² → f'' v w`. -/
theorem second_diff_tendsto (f : (Fin d → ℝ) → ℝ) (f' : (Fin d → ℝ) → (Fin d → ℝ) →L[ℝ] ℝ)
    (f'' : (Fin d → ℝ) →L[ℝ] (Fin d → ℝ) →L[ℝ] ℝ) (θ0 : Fin d → ℝ)
    (hf : ∀ y, HasFDerivAt f (f' y) y) (hf' : HasFDerivAt f' f'' θ0) (v w : Fin d → ℝ) :
    Tendsto (fun h : ℝ => (f (θ0 + h • v + h • w) - f (θ0 + h • v) - f (θ0 + h • w) + f θ0) / h ^ 2)
      (𝓝[>] 0) (𝓝 (f'' v w)) := by
  have hf1 : ∀ x ∈ interior (Set.univ : Set (Fin d → ℝ)), HasFDerivAt f (f' x) x :=
    fun x _ => hf x
  have hx : HasFDerivWithinAt f' f'' (interior Set.univ) θ0 := hf'.hasFDerivWithinAt
  have A := Convex.taylor_approx_two_segment convex_univ hf1 (Set.mem_univ θ0) hx
    (v := v) (w := w) (by simp) (by simp)
  have B := Convex.taylor_approx_two_segment convex_univ hf1 (Set.mem_univ θ0) hx
    (v := 0) (w := w) (by simp) (by simp)
  have tA := A.tendsto_div_nhds_zero
  have tB := B.tendsto_div_nhds_zero
  have := (tA.sub tB).add (tendsto_const_nhds (x := f'' v w))
  rw [sub_zero, zero_add] at this
  refine this.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with h hh
  have hh0 : (h:ℝ) ≠ 0 := ne_of_gt hh
  simp only [smul_zero, add_zero, map_zero, zero_apply, smul_eq_mul]
  field_simp
  ring

/-- The cast of an integer parameter index to `ℝ^d`. -/
def toR (k : Fin d → ℤ) : Fin d → ℝ := fun i => (k i : ℝ)

theorem toR_add (k l : Fin d → ℤ) : toR (k + l) = toR k + toR l := by
  ext i; simp [toR]

theorem toR_zero : toR (0 : Fin d → ℤ) = 0 := by ext i; simp [toR]

theorem toR_single (a : Fin d) : toR (Pi.single a (1:ℤ)) = Pi.single a (1:ℝ) := by
  ext i; by_cases h : i = a
  · subst h; simp [toR]
  · simp [toR, h]

/-- The lattice family of step `h` read off a real family `P` around `θ0`:
grain `k ∈ ℤ^d` sits at the parameter `θ0 + h k`. -/
def lat (P : (Fin d → ℝ) → S → ℝ) (θ0 : Fin d → ℝ) (h : ℝ) (k : Fin d → ℤ) (x : S) : ℝ :=
  P (θ0 + h • toR k) x

/-- The classical `α`-connection of a family on a finite sample space:
`Γ^{(α)}_{ab,c} = ∑ ∂_a∂_b p ∂_c p / p - ((1+α)/2) ∑ ∂_a p ∂_b p ∂_c p / p²`. -/
noncomputable def classConn (α : ℝ) (P : (Fin d → ℝ) → S → ℝ)
    (P' : (Fin d → ℝ) → S → (Fin d → ℝ) →L[ℝ] ℝ) (P'' : S → (Fin d → ℝ) →L[ℝ] (Fin d → ℝ) →L[ℝ] ℝ)
    (θ0 : Fin d → ℝ) (a b c : Fin d) : ℝ :=
  ∑ x, P'' x (Pi.single a 1) (Pi.single b 1) * P' θ0 x (Pi.single c 1) / P θ0 x
    - (1 + α) / 2 * ∑ x, P' θ0 x (Pi.single a 1) * P' θ0 x (Pi.single b 1) * P' θ0 x (Pi.single c 1)
        / (P θ0 x) ^ 2

section
variable (P : (Fin d → ℝ) → S → ℝ) (P' : (Fin d → ℝ) → S → (Fin d → ℝ) →L[ℝ] ℝ)
  (P'' : S → (Fin d → ℝ) →L[ℝ] (Fin d → ℝ) →L[ℝ] ℝ) (θ0 : Fin d → ℝ)
  (hP : ∀ x y, HasFDerivAt (fun y => P y x) (P' y x) y)
  (hP' : ∀ x, HasFDerivAt (fun y => P' y x) (P'' x) θ0) (hpos : ∀ x, 0 < P θ0 x)
include hP

private theorem lat_D_tendsto (a : Fin d) (x : S) :
    Tendsto (fun h => D h (lat P θ0 h) a 0 x) (𝓝[>] 0) (𝓝 (P' θ0 x (Pi.single a 1))) := by
  have := dir_slope (fun y => P y x) (P' θ0 x) θ0 (hP x θ0) (Pi.single a 1)
  refine this.congr' (Eventually.of_forall fun h => ?_)
  simp [D, lat, toR_single, toR_zero]

private theorem lat_shift_tendsto (a : Fin d) (x : S) :
    Tendsto (fun h => lat P θ0 h (0 + Pi.single a 1) x) (𝓝[>] 0) (𝓝 (P θ0 x)) := by
  have hc : Tendsto (fun h : ℝ => θ0 + h • (Pi.single a (1:ℝ) : Fin d → ℝ)) (𝓝 0) (𝓝 θ0) := by
    have : Continuous (fun h : ℝ => θ0 + h • (Pi.single a (1:ℝ) : Fin d → ℝ)) := by fun_prop
    simpa using this.tendsto 0
  have := ((hP x θ0).continuousAt.tendsto.comp hc).mono_left (nhdsWithin_le_nhds (s := Set.Ioi 0))
  refine this.congr' (Eventually.of_forall fun h => ?_)
  simp [lat, toR_single]

include hP' in
private theorem lat_D2_tendsto (a b : Fin d) (x : S) :
    Tendsto (fun h => D2 h (lat P θ0 h) a b 0 x) (𝓝[>] 0)
      (𝓝 (P'' x (Pi.single a 1) (Pi.single b 1))) := by
  have := second_diff_tendsto (fun y => P y x) (fun y => P' y x) (P'' x) θ0 (hP x) (hP' x)
    (Pi.single a 1) (Pi.single b 1)
  refine this.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with h hh
  have hh0 : (h:ℝ) ≠ 0 := ne_of_gt hh
  simp only [D2, D, lat, toR_add, toR_single, toR_zero, zero_add, smul_add, smul_zero, add_zero]
  field_simp
  ring_nf

/-- **Shadow of the granular Fisher metric** (multi-parameter). -/
theorem metric_shadow (a b : Fin d) :
    Tendsto (fun h => metric h (lat P θ0 h) a b 0) (𝓝[>] 0)
      (𝓝 (∑ x, P' θ0 x (Pi.single a 1) * P' θ0 x (Pi.single b 1) / P θ0 x)) := by
  unfold metric
  apply tendsto_finsetSum; intro x _
  have h0 : ∀ h : ℝ, lat P θ0 h 0 x = P θ0 x := fun h => by simp [lat, toR_zero]
  simp_rw [h0]
  exact ((lat_D_tendsto P P' θ0 hP a x).mul (lat_D_tendsto P P' θ0 hP b x)).div_const _

include hP' hpos in
/-- **Shadow of the granular `α`-connections**: `Γ^{(α),ε}_{ab,c} → Γ^{(α)}_{ab,c}`, the
classical `α`-connection, for a family differentiable on `ℝ^d` whose derivative is
differentiable at `θ0`. -/
theorem conn_shadow (α : ℝ) (a b c : Fin d) :
    Tendsto (fun h => conn h α (lat P θ0 h) a b c 0) (𝓝[>] 0)
      (𝓝 (classConn α P P' P'' θ0 a b c)) := by
  unfold conn classConn
  have h0 : ∀ h : ℝ, ∀ x, lat P θ0 h 0 x = P θ0 x := fun h x => by simp [lat, toR_zero]
  simp_rw [h0]
  have hid : Tendsto (fun h : ℝ => h) (𝓝[>] 0) (𝓝 0) := nhdsWithin_le_nhds
  apply Tendsto.sub
  · apply tendsto_finsetSum; intro x _
    have t1 := lat_D2_tendsto P P' P'' θ0 hP hP' a b x
    have t2 := lat_D_tendsto P P' θ0 hP c x
    have t3 := lat_D2_tendsto P P' P'' θ0 hP hP' a c x
    have t4 := lat_shift_tendsto P P' θ0 hP a x
    have := (t1.mul (t2.add ((hid.div_const 2).mul t3))).div t4 (hpos x).ne'
    simp only [zero_div, zero_mul, add_zero] at this
    refine this.congr (fun h => ?_); simp
  · apply Tendsto.const_mul
    apply tendsto_finsetSum; intro x _
    have t1 := lat_D_tendsto P P' θ0 hP a x
    have t2 := lat_D_tendsto P P' θ0 hP b x
    have t3 := lat_D_tendsto P P' θ0 hP c x
    have t4 := lat_shift_tendsto P P' θ0 hP a x
    have := ((t1.mul t2).mul t3).div (tendsto_const_nhds.mul t4)
      (mul_ne_zero (hpos x).ne' (hpos x).ne')
    rw [← sq] at this
    refine this.congr (fun h => ?_); simp

include hP' hpos in
/-- **The torsion of the granular connections has shadow `0`.** -/
theorem torsion_shadow (α : ℝ) (a b c : Fin d) :
    Tendsto (fun h => conn h α (lat P θ0 h) a b c 0 - conn h α (lat P θ0 h) b a c 0) (𝓝[>] 0)
      (𝓝 0) := by
  have := (conn_shadow P P' P'' θ0 hP hP' hpos α a b c).sub
    (conn_shadow P P' P'' θ0 hP hP' hpos α b a c)
  convert this using 2
  have hs : ∀ x, P'' x (Pi.single a 1) (Pi.single b 1) = P'' x (Pi.single b 1) (Pi.single a 1) :=
    fun x => second_derivative_symmetric_of_eventually_of_real
      (Eventually.of_forall fun y => hP x y) (hP' x) _ _
  have hm : ∀ x, P' θ0 x (Pi.single b 1) * P' θ0 x (Pi.single a 1) * P' θ0 x (Pi.single c 1)
      = P' θ0 x (Pi.single a 1) * P' θ0 x (Pi.single b 1) * P' θ0 x (Pi.single c 1) :=
    fun x => by ring
  unfold classConn
  simp_rw [hs, hm]
  ring

end

end ConnShadow

end QE.OpenSto.InfoGeo

/-!
# Euclidean lattice fields at the granule (open problem `prob:epilogue-qft`)

Finite-volume lattice field theory as finite, Lebesgue-free objects:

* `partition_pos`, `gibbs_pos`, `gibbs_sum`: on a finite site set `Λ` with a
  finite (hyperfinite) value lattice `V`, every action defines a Gibbs measure
  in which every configuration has positive probability; `phi4Action` is the
  lattice `φ⁴` action; `precision_posDef` / `precision_invertible`: the free
  precision `−Δ + m²` is positive definite, so the free covariance exists.
* `reflection_positive`: reflection positivity for every chain of `2(n+1)`
  time slices with arbitrary slice action and nearest-neighbour time coupling
  `κ ≥ 0` (key lemma `exp_kernel_psd`, proved from the exponential series).
* `wick`, `gauss_two`, `gauss_lin_even`, `gauss_lin_odd`: the exact Wick
  theorem for the Gaussian functional `P ↦ (e^{½∑G∂∂}P)(0)` on polynomial
  observables, from the exact integration by parts `gaussN_X_mul`.
-/

open Finset
set_option linter.unusedSectionVars false
set_option linter.deprecated false
set_option linter.unusedSimpArgs false

namespace QE.OpenSto.Field

theorem exp_kernel_psd {X I : Type*} [Fintype X] [Fintype I] (c : X → ℝ) (β : X → I → ℝ)
    (κ : ℝ) (hκ : 0 ≤ κ) :
    0 ≤ ∑ u, ∑ v, c u * c v * Real.exp (κ * ∑ i, β u i * β v i) := by
  have hs : ∀ u v, HasSum (fun n : ℕ => c u * c v * ((κ * ∑ i, β u i * β v i) ^ n / n.factorial))
      (c u * c v * Real.exp (κ * ∑ i, β u i * β v i)) := by
    intro u v
    have := NormedSpace.expSeries_div_hasSum_exp (κ * ∑ i, β u i * β v i)
    rw [← Real.exp_eq_exp_ℝ] at this
    exact this.mul_left _
  have hS : HasSum (fun n : ℕ => ∑ u, ∑ v, c u * c v * ((κ * ∑ i, β u i * β v i) ^ n / n.factorial))
      (∑ u, ∑ v, c u * c v * Real.exp (κ * ∑ i, β u i * β v i)) :=
    hasSum_sum fun u _ => hasSum_sum fun v _ => hs u v
  refine hS.nonneg fun n => ?_
  set P := Fintype.piFinset (fun _ : Fin n => (univ : Finset I))
  have key : ∑ u, ∑ v, c u * c v * ((κ * ∑ i, β u i * β v i) ^ n / n.factorial)
      = κ ^ n / n.factorial * ∑ p ∈ P, (∑ u, c u * ∏ k, β u (p k)) ^ 2 := by
    calc _ = ∑ u, ∑ v, ∑ p ∈ P, κ ^ n / n.factorial *
          ((c u * ∏ k, β u (p k)) * (c v * ∏ k, β v (p k))) := by
          apply sum_congr rfl; intro u _; apply sum_congr rfl; intro v _
          rw [mul_pow, sum_pow' univ (fun i => β u i * β v i), mul_sum, sum_div, mul_sum]
          apply sum_congr rfl; intro p _
          rw [prod_mul_distrib]; ring
      _ = ∑ p ∈ P, ∑ u, ∑ v, κ ^ n / n.factorial *
          ((c u * ∏ k, β u (p k)) * (c v * ∏ k, β v (p k))) := by
          rw [Finset.sum_comm (s := P)]
          exact sum_congr rfl fun u _ => Finset.sum_comm
      _ = _ := by
          rw [mul_sum]; apply sum_congr rfl; intro p _
          rw [sq, sum_mul_sum, mul_sum]; apply sum_congr rfl; intro u _
          rw [mul_sum]
  rw [key]
  exact mul_nonneg (by positivity) (sum_nonneg fun p _ => sq_nonneg _)

section RP
variable {Y I : Type*} [Fintype I] [Inhabited Y]

def ext {T : ℕ} (u : Fin T → Y) (s : ℕ) : Y := if h : s < T then u ⟨s, h⟩ else default

def glue (n : ℕ) (u v : Fin (n + 1) → Y) (t : ℕ) : Y :=
  if t ≤ n then ext v (n - t) else ext u (t - (n + 1))

def sqd (b : Y → I → ℝ) (y y' : Y) : ℝ := ∑ i, (b y' i - b y i) ^ 2

theorem sqd_comm (b : Y → I → ℝ) (y y' : Y) : sqd b y y' = sqd b y' y := by
  unfold sqd; exact sum_congr rfl fun i _ => by ring

noncomputable def chainAction (K : Y → ℝ) (b : Y → I → ℝ) (κ : ℝ) (L : ℕ) (ψ : ℕ → Y) : ℝ :=
  ∑ t ∈ range L, K (ψ t) + κ / 2 * ∑ t ∈ range (L - 1), sqd b (ψ t) (ψ (t + 1))

noncomputable def halfAction (K : Y → ℝ) (b : Y → I → ℝ) (κ : ℝ) (n : ℕ) (w : Fin (n + 1) → Y) : ℝ :=
  ∑ s ∈ range (n + 1), K (ext w s) + κ / 2 * ∑ s ∈ range n, sqd b (ext w s) (ext w (s + 1))
    + κ / 2 * ∑ i, b (w 0) i ^ 2

theorem ext_zero {n : ℕ} (w : Fin (n + 1) → Y) : ext w 0 = w 0 := by
  simp [ext]

theorem chainAction_glue (K : Y → ℝ) (b : Y → I → ℝ) (κ : ℝ) (n : ℕ) (u v : Fin (n + 1) → Y) :
    chainAction K b κ (2 * (n + 1)) (glue n u v) =
      halfAction K b κ n u + halfAction K b κ n v - κ * ∑ i, b (u 0) i * b (v 0) i := by
  unfold chainAction halfAction
  have hK : ∑ t ∈ range (2 * (n + 1)), K (glue n u v t)
      = ∑ s ∈ range (n + 1), K (ext v s) + ∑ s ∈ range (n + 1), K (ext u s) := by
    rw [two_mul, sum_range_add]
    congr 1
    · rw [← sum_range_reflect (fun s => K (ext v s)) (n + 1)]
      apply sum_congr rfl; intro t ht
      rw [mem_range] at ht
      simp only [glue, if_pos (Nat.lt_succ_iff.mp ht)]
      congr 2
    · apply sum_congr rfl; intro s _
      simp only [glue, if_neg (by omega : ¬ n + 1 + s ≤ n)]
      congr 2; omega
  have hB : ∑ t ∈ range (2 * (n + 1) - 1), sqd b (glue n u v t) (glue n u v (t + 1))
      = ∑ s ∈ range n, sqd b (ext v s) (ext v (s + 1)) + sqd b (v 0) (u 0)
        + ∑ s ∈ range n, sqd b (ext u s) (ext u (s + 1)) := by
    rw [show 2 * (n + 1) - 1 = (n + 1) + n by omega, sum_range_add, sum_range_succ]
    congr 2
    · rw [← sum_range_reflect (fun s => sqd b (ext v s) (ext v (s + 1))) n]
      apply sum_congr rfl; intro t ht
      rw [mem_range] at ht
      simp only [glue, if_pos (by omega : t ≤ n), if_pos (by omega : t + 1 ≤ n)]
      rw [sqd_comm]; congr 2 <;> omega
    · simp only [glue, le_refl, if_true, if_neg (by omega : ¬ n + 1 ≤ n), Nat.sub_self, ext_zero]
    · funext s
      simp only [glue, if_neg (by omega : ¬ n + 1 + s ≤ n),
        if_neg (by omega : ¬ n + 1 + s + 1 ≤ n)]
      congr 3 <;> omega
  rw [hK, hB]
  have hc : sqd b (v 0) (u 0) = ∑ i, b (u 0) i ^ 2 + ∑ i, b (v 0) i ^ 2
      - 2 * ∑ i, b (u 0) i * b (v 0) i := by
    unfold sqd; rw [mul_sum, ← sum_add_distrib, ← sum_sub_distrib]
    exact sum_congr rfl fun i _ => by ring
  rw [hc]; ring

/-- **Reflection positivity** of every chain action with nearest-neighbour
time coupling `κ ≥ 0` and arbitrary slice action `K`. -/
theorem reflection_positive [Fintype Y] (K : Y → ℝ) (b : Y → I → ℝ) (κ : ℝ) (hκ : 0 ≤ κ)
    (n : ℕ) (F : (Fin (n + 1) → Y) → ℝ) :
    0 ≤ ∑ u : Fin (n + 1) → Y, ∑ v : Fin (n + 1) → Y,
      Real.exp (-chainAction K b κ (2 * (n + 1)) (glue n u v)) * F u * F v := by
  have h := exp_kernel_psd (fun u => Real.exp (-halfAction K b κ n u) * F u)
    (fun u => b (u 0)) κ hκ
  refine h.trans (le_of_eq ?_)
  apply sum_congr rfl; intro u _; apply sum_congr rfl; intro v _
  rw [chainAction_glue]
  rw [show -(halfAction K b κ n u + halfAction K b κ n v - κ * ∑ i, b (u 0) i * b (v 0) i)
      = -halfAction K b κ n u + -halfAction K b κ n v + κ * ∑ i, b (u 0) i * b (v 0) i by ring,
    Real.exp_add, Real.exp_add]
  ring

end RP

section Exist
variable {Λ V : Type*} [Fintype Λ] [DecidableEq Λ] [Fintype V] [Nonempty V]

/-- Partition function of an arbitrary action on the finite configuration space `Λ → V`. -/
noncomputable def partition (S : (Λ → V) → ℝ) : ℝ := ∑ φ, Real.exp (-S φ)

theorem partition_pos (S : (Λ → V) → ℝ) : 0 < partition S :=
  sum_pos (fun _ _ => Real.exp_pos _) univ_nonempty

/-- Gibbs weight `e^{-S(φ)}/Z`. -/
noncomputable def gibbs (S : (Λ → V) → ℝ) (φ : Λ → V) : ℝ := Real.exp (-S φ) / partition S

theorem gibbs_pos (S : (Λ → V) → ℝ) (φ : Λ → V) : 0 < gibbs S φ :=
  div_pos (Real.exp_pos _) (partition_pos S)

theorem gibbs_sum (S : (Λ → V) → ℝ) : ∑ φ, gibbs S φ = 1 := by
  unfold gibbs; rw [← sum_div]; exact div_self (partition_pos S).ne'

/-- Quadratic (free) form of a real lattice field: `∑_{bonds}(f x − f y)² + m² ∑ f²`. -/
def freeForm (bonds : Finset (Λ × Λ)) (m2 : ℝ) (f : Λ → ℝ) : ℝ :=
  ∑ e ∈ bonds, (f e.1 - f e.2) ^ 2 + m2 * ∑ x, f x ^ 2

/-- The lattice `φ⁴` action of a field with values `val : V → ℝ`. -/
noncomputable def phi4Action (val : V → ℝ) (bonds : Finset (Λ × Λ)) (m2 lam : ℝ) (φ : Λ → V) : ℝ :=
  freeForm bonds m2 (fun x => val (φ x)) / 2 + lam * ∑ x, val (φ x) ^ 4

theorem freeForm_ge (bonds : Finset (Λ × Λ)) (m2 : ℝ) (f : Λ → ℝ) :
    m2 * ∑ x, f x ^ 2 ≤ freeForm bonds m2 f := by
  unfold freeForm; linarith [sum_nonneg fun e (_ : e ∈ bonds) => sq_nonneg (f e.1 - f e.2)]

theorem freeForm_pos (bonds : Finset (Λ × Λ)) (m2 : ℝ) (hm : 0 < m2) (f : Λ → ℝ) (hf : f ≠ 0) :
    0 < freeForm bonds m2 f := by
  obtain ⟨x, hx⟩ : ∃ x, f x ≠ 0 := by
    by_contra h; push Not at h; exact hf (funext h)
  have : 0 < ∑ x, f x ^ 2 :=
    lt_of_lt_of_le (by positivity) (single_le_sum (fun y _ => sq_nonneg (f y)) (mem_univ x))
  exact lt_of_lt_of_le (mul_pos hm this) (freeForm_ge bonds m2 f)

/-- The precision matrix `A = −Δ + m²` of the free field (graph Laplacian of `bonds`). -/
def precision (bonds : Finset (Λ × Λ)) (m2 : ℝ) : Matrix Λ Λ ℝ := fun x y =>
  (if x = y then m2 else 0) +
    ∑ e ∈ bonds, ((if e.1 = x then 1 else 0) - (if e.2 = x then 1 else 0)) *
      ((if e.1 = y then 1 else 0) - (if e.2 = y then 1 else 0))

theorem precision_quad (bonds : Finset (Λ × Λ)) (m2 : ℝ) (f : Λ → ℝ) :
    ∑ x, ∑ y, f x * precision bonds m2 x y * f y = freeForm bonds m2 f := by
  set g : Λ × Λ → Λ → ℝ := fun e x => (if e.1 = x then 1 else 0) - (if e.2 = x then 1 else 0)
  have hg : ∀ e : Λ × Λ, ∑ x, f x * g e x = f e.1 - f e.2 := by
    intro e; simp [g, mul_sub, sum_sub_distrib]
  have h1 : ∑ x, ∑ y, f x * (if x = y then m2 else 0) * f y = m2 * ∑ x, f x ^ 2 := by
    rw [mul_sum]; apply sum_congr rfl; intro x _
    simp only [mul_ite, ite_mul, mul_zero, zero_mul, sum_ite_eq, mem_univ, if_true]; ring
  have h2 : ∑ x, ∑ y, f x * (∑ e ∈ bonds, g e x * g e y) * f y
      = ∑ e ∈ bonds, (f e.1 - f e.2) ^ 2 := by
    have : ∀ x y, f x * (∑ e ∈ bonds, g e x * g e y) * f y
        = ∑ e ∈ bonds, (f x * g e x) * (f y * g e y) := by
      intro x y; rw [mul_sum, sum_mul]; exact sum_congr rfl fun e _ => by ring
    simp_rw [this]
    rw [show (∑ x, ∑ y, ∑ e ∈ bonds, (f x * g e x) * (f y * g e y))
        = ∑ x, ∑ e ∈ bonds, ∑ y, (f x * g e x) * (f y * g e y) from
          sum_congr rfl fun x _ => Finset.sum_comm, Finset.sum_comm]
    apply sum_congr rfl; intro e _
    rw [← hg e, sq, sum_mul_sum]
  have : ∀ x y, precision bonds m2 x y = (if x = y then m2 else 0) + ∑ e ∈ bonds, g e x * g e y :=
    fun x y => rfl
  simp_rw [this, mul_add, add_mul, sum_add_distrib]
  rw [h1, h2]; unfold freeForm; ring

theorem precision_posDef (bonds : Finset (Λ × Λ)) (m2 : ℝ) (hm : 0 < m2) :
    (precision bonds m2).PosDef := by
  rw [Matrix.posDef_iff_dotProduct_mulVec]
  refine ⟨?_, ?_⟩
  · ext x y
    simp only [Matrix.conjTranspose_apply, star_trivial, precision]
    congr 1
    · by_cases h : x = y <;> simp [h, eq_comm]
    · exact sum_congr rfl fun e _ => by ring
  · intro f hf
    have := freeForm_pos bonds m2 hm f hf
    rw [← precision_quad] at this
    simpa [dotProduct, Matrix.mulVec, mul_sum, mul_comm, mul_left_comm, mul_assoc] using this

/-- The free-field covariance `G = (−Δ+m²)⁻¹` exists. -/
theorem precision_invertible (bonds : Finset (Λ × Λ)) (m2 : ℝ) (hm : 0 < m2) :
    IsUnit (precision bonds m2) :=
  (precision_posDef bonds m2 hm).isUnit

end Exist

section Wick
open MvPolynomial
variable {σ : Type*} [Fintype σ] [DecidableEq σ] (G : σ → σ → ℝ)

/-- `D_x = ∑_y G(x,y) ∂_y`. -/
noncomputable def Dop (x : σ) (P : MvPolynomial σ ℝ) : MvPolynomial σ ℝ :=
  ∑ y, G x y • pderiv y P

/-- The Gaussian Laplacian `L = ½ ∑_{x,y} G(x,y) ∂_x ∂_y`. -/
noncomputable def Lop : Module.End ℝ (MvPolynomial σ ℝ) :=
  (1 / 2 : ℝ) • ∑ x, ∑ y, G x y • ((pderiv x).toLinearMap ∘ₗ (pderiv y).toLinearMap)

theorem Lop_apply (P : MvPolynomial σ ℝ) :
    Lop G P = (1 / 2 : ℝ) • ∑ x, ∑ y, G x y • pderiv x (pderiv y P) := by
  simp [Lop, LinearMap.sum_apply]

theorem pderiv_Lop (z : σ) (P : MvPolynomial σ ℝ) : pderiv z (Lop G P) = Lop G (pderiv z P) := by
  rw [Lop_apply, Lop_apply, (pderiv z).map_smul, map_sum]
  congr 1; apply sum_congr rfl; intro x _
  rw [map_sum]; apply sum_congr rfl; intro y _
  rw [(pderiv z).map_smul, pderiv_comm z x, pderiv_comm z y]

theorem pderiv_Lpow (z : σ) (k : ℕ) (P : MvPolynomial σ ℝ) :
    pderiv z ((Lop G ^ k) P) = (Lop G ^ k) (pderiv z P) := by
  induction k with
  | zero => simp
  | succ k ih => rw [pow_succ', Module.End.mul_apply, Module.End.mul_apply, pderiv_Lop, ih]

theorem Lop_Dop (x : σ) (P : MvPolynomial σ ℝ) : Lop G (Dop G x P) = Dop G x (Lop G P) := by
  unfold Dop
  rw [map_sum]; apply sum_congr rfl; intro y _
  rw [map_smul, pderiv_Lop]

theorem pderiv_X_eq (y x : σ) : pderiv y (X x : MvPolynomial σ ℝ) = if y = x then 1 else 0 := by
  by_cases h : y = x
  · subst h; simp
  · rw [if_neg h, pderiv_X_of_ne (Ne.symm h)]

/-- The commutator `[L, X_x] = D_x` (for symmetric `G`). -/
theorem Lop_X_mul (hG : ∀ x y, G x y = G y x) (x : σ) (P : MvPolynomial σ ℝ) :
    Lop G (X x * P) = X x * Lop G P + Dop G x P := by
  have h2 : ∀ a b : σ, pderiv a (pderiv b (X x * P)) =
      (if b = x then pderiv a P else 0) + (if a = x then pderiv b P else 0)
        + X x * pderiv a (pderiv b P) := by
    have h1 : ∀ c : σ, ∀ Q : MvPolynomial σ ℝ,
        pderiv c (X x * Q) = (if c = x then Q else 0) + X x * pderiv c Q := by
      intro c Q; rw [pderiv_mul, pderiv_X_eq]; split_ifs <;> simp
    intro a b
    rw [h1 b, map_add, h1 a]
    by_cases hb : b = x
    · simp [hb]; abel
    · simp [hb]
  rw [Lop_apply, Lop_apply]
  simp_rw [h2, smul_add, sum_add_distrib, smul_add]
  have e1 : ∑ a : σ, ∑ b : σ, G a b • (if b = x then pderiv a P else 0) = Dop G x P := by
    unfold Dop; apply sum_congr rfl; intro a _
    simp [hG a x]
  have e2 : ∑ a : σ, ∑ b : σ, G a b • (if a = x then pderiv b P else 0) = Dop G x P := by
    unfold Dop; simp
  have e3 : ∑ a : σ, ∑ b : σ, G a b • (X x * pderiv a (pderiv b P))
      = X x * ∑ a : σ, ∑ b : σ, G a b • pderiv a (pderiv b P) := by
    rw [mul_sum]; apply sum_congr rfl; intro a _
    rw [mul_sum]; apply sum_congr rfl; intro b _
    rw [mul_smul_comm]
  rw [e1, e2, e3, mul_smul_comm]
  rw [show (1 / 2 : ℝ) • Dop G x P + (1 / 2 : ℝ) • Dop G x P = Dop G x P by
    rw [← add_smul]; norm_num]
  abel

theorem Lpow_X_mul (hG : ∀ x y, G x y = G y x) (x : σ) (k : ℕ) (P : MvPolynomial σ ℝ) :
    (Lop G ^ k) (X x * P) = X x * (Lop G ^ k) P + (k : ℝ) • Dop G x ((Lop G ^ (k - 1)) P) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ', Module.End.mul_apply, ih, map_add, map_smul, Lop_X_mul G hG, Lop_Dop,
      Module.End.mul_apply]
    rcases k with _ | k
    · simp
    · rw [show k + 1 - 1 = k by omega, show k + 1 + 1 - 1 = k + 1 by omega, pow_succ',
        Module.End.mul_apply]
      push_cast
      module


/-- Truncated Gaussian functional `E_N(P) = ∑_{k<N} [L^k P](0)/k!`. -/
noncomputable def gaussN (N : ℕ) (P : MvPolynomial σ ℝ) : ℝ :=
  ∑ k ∈ range N, constantCoeff ((Lop G ^ k) P) / k.factorial

theorem gaussN_add (N : ℕ) (P Q : MvPolynomial σ ℝ) :
    gaussN G N (P + Q) = gaussN G N P + gaussN G N Q := by
  unfold gaussN; rw [← sum_add_distrib]
  exact sum_congr rfl fun k _ => by rw [map_add, map_add, add_div]

theorem gaussN_smul (N : ℕ) (c : ℝ) (P : MvPolynomial σ ℝ) :
    gaussN G N (c • P) = c * gaussN G N P := by
  unfold gaussN; rw [mul_sum]
  refine sum_congr rfl fun k _ => ?_
  rw [map_smul, smul_eq_C_mul, map_mul, constantCoeff_C]; ring

theorem gaussN_sum {ι : Type*} (s : Finset ι) (N : ℕ) (P : ι → MvPolynomial σ ℝ) :
    gaussN G N (∑ i ∈ s, P i) = ∑ i ∈ s, gaussN G N (P i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [gaussN]
  | insert a s ha ih => rw [sum_insert ha, sum_insert ha, gaussN_add, ih]

theorem constantCoeff_X_mul (x : σ) (Q : MvPolynomial σ ℝ) : constantCoeff (X x * Q) = 0 := by
  rw [map_mul, constantCoeff_X, zero_mul]

/-- **Gaussian integration by parts**, exact at every cutoff:
`E_{N+1}(X_x P) = ∑_y G(x,y) E_N(∂_y P)`. -/
theorem gaussN_X_mul (hG : ∀ x y, G x y = G y x) (x : σ) (N : ℕ) (P : MvPolynomial σ ℝ) :
    gaussN G (N + 1) (X x * P) = ∑ y, G x y * gaussN G N (pderiv y P) := by
  unfold gaussN
  rw [sum_range_succ']
  simp only [Lpow_X_mul G hG, map_add, constantCoeff_X_mul, zero_add, Nat.cast_zero, zero_smul,
    zero_div, add_zero]
  simp_rw [mul_sum]
  rw [Finset.sum_comm]
  refine sum_congr rfl fun k _ => ?_
  rw [Nat.add_sub_cancel, smul_eq_C_mul, map_mul, constantCoeff_C]
  unfold Dop
  rw [map_sum, mul_sum, sum_div]
  refine sum_congr rfl fun y _ => ?_
  rw [smul_eq_C_mul, map_mul, constantCoeff_C, pderiv_Lpow, Nat.factorial_succ]
  push_cast
  field_simp

/-! ### Homogeneity and stabilisation -/

theorem Lop_isHomogeneous {P : MvPolynomial σ ℝ} {n : ℕ} (h : P.IsHomogeneous n) :
    (Lop G P).IsHomogeneous (n - 2) := by
  rw [Lop_apply, ← mem_homogeneousSubmodule]
  refine Submodule.smul_mem _ _ (Submodule.sum_mem _ fun a _ => Submodule.sum_mem _ fun b _ =>
    Submodule.smul_mem _ _ ?_)
  rw [mem_homogeneousSubmodule, show n - 2 = n - 1 - 1 by omega]
  exact (h.pderiv).pderiv

theorem Lop_eq_zero {P : MvPolynomial σ ℝ} {n : ℕ} (h : P.IsHomogeneous n) (hn : n < 2) :
    Lop G P = 0 := by
  rw [Lop_apply]
  have : ∀ a b : σ, pderiv a (pderiv b P) = 0 := by
    intro a b
    have h0 : (pderiv b P).IsHomogeneous 0 := by
      have := h.pderiv (i := b); rwa [show n - 1 = 0 by omega] at this
    rw [← totalDegree_zero_iff_isHomogeneous, totalDegree_eq_zero_iff_eq_C] at h0
    rw [h0, pderiv_C]
  simp [this]

theorem Lpow_eq_zero {k : ℕ} : ∀ {P : MvPolynomial σ ℝ} {n : ℕ}, P.IsHomogeneous n → n < 2 * k →
    (Lop G ^ k) P = 0 := by
  induction k with
  | zero => intro P n _ hn; omega
  | succ k ih =>
    intro P n h hn
    rw [pow_succ, Module.End.mul_apply]
    by_cases hn2 : n < 2
    · rw [Lop_eq_zero G h hn2, map_zero]
    · exact ih (Lop_isHomogeneous G h) (by omega)

theorem gaussN_stable {P : MvPolynomial σ ℝ} {n : ℕ} (h : P.IsHomogeneous n) {N : ℕ}
    (hN : n < 2 * N) (j : ℕ) : gaussN G (N + j) P = gaussN G N P := by
  unfold gaussN
  rw [sum_range_add]
  have : ∀ i ∈ range j, constantCoeff ((Lop G ^ (N + i)) P) / ((N + i).factorial : ℝ) = 0 := by
    intro i _; rw [Lpow_eq_zero G h (by omega), map_zero, zero_div]
  rw [sum_eq_zero this, add_zero]

/-- The Gaussian functional `E(P) = E_N(P)` for any cutoff beyond half the degree. -/
noncomputable def gauss (P : MvPolynomial σ ℝ) : ℝ := gaussN G (P.totalDegree + 1) P

theorem gauss_eq {P : MvPolynomial σ ℝ} {n : ℕ} (h : P.IsHomogeneous n) {N : ℕ}
    (hN : n < 2 * N) : gauss G P = gaussN G N P := by
  by_cases hP : P = 0
  · subst hP; simp [gauss, gaussN]
  · unfold gauss
    rw [h.totalDegree hP]
    rcases le_total (n + 1) N with hle | hle
    · obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hle
      rw [gaussN_stable G h (by omega) j]
    · obtain ⟨j, hj⟩ := Nat.exists_eq_add_of_le hle
      rw [hj, gaussN_stable G h hN j]

/-- Integration by parts for the Gaussian functional, homogeneous form. -/
theorem gauss_X_mul (hG : ∀ x y, G x y = G y x) (x : σ) {P : MvPolynomial σ ℝ} {n : ℕ}
    (h : P.IsHomogeneous n) :
    gauss G (X x * P) = ∑ y, G x y * gauss G (pderiv y P) := by
  have hX : (X x * P).IsHomogeneous (1 + n) := (isHomogeneous_X ℝ x).mul h
  rw [gauss_eq G hX (N := n + 2) (by omega), gaussN_X_mul G hG]
  refine sum_congr rfl fun y _ => ?_
  rw [gauss_eq G (h.pderiv (i := y)) (N := n + 1) (by omega)]

theorem gauss_one : gauss G (1 : MvPolynomial σ ℝ) = 1 := by
  rw [gauss_eq G (isHomogeneous_one σ ℝ) (N := 1) (by norm_num)]
  simp [gaussN]

/-! ### Wick's theorem for monomials -/

/-- The monomial `φ(x₁)⋯φ(x_m)` of a list of sites. -/
noncomputable def mono (l : List σ) : MvPolynomial σ ℝ := (l.map X).prod

theorem mono_cons (a : σ) (l : List σ) : mono (a :: l) = X a * mono l := by simp [mono]

theorem mono_isHomogeneous (l : List σ) : (mono l).IsHomogeneous l.length := by
  induction l with
  | nil => simpa [mono] using isHomogeneous_one σ ℝ
  | cons a l ih =>
    rw [mono_cons, List.length_cons, add_comm]; exact (isHomogeneous_X ℝ a).mul ih

theorem pderiv_mono (y : σ) (l : List σ) :
    pderiv y (mono l) = ∑ j : Fin l.length, if l[j] = y then mono (l.eraseIdx j) else 0 := by
  induction l with
  | nil => simp [mono]
  | cons a l ih =>
    rw [mono_cons, pderiv_mul, pderiv_X_eq, ih]
    simp only [List.length_cons, Fin.sum_univ_succ, Fin.coe_ofNat_eq_mod, Fin.val_succ,
      List.getElem_cons_zero, List.getElem_cons_succ, List.eraseIdx_cons_zero,
      List.eraseIdx_cons_succ, mono_cons, mul_sum]
    congr 1
    · by_cases h : y = a
      · subst h; simp
      · simp [h, Ne.symm h]
    · refine sum_congr rfl fun j _ => ?_
      rw [show (a :: l)[j.succ] = l[j] from rfl]
      split_ifs <;> simp

/-- **Wick's theorem** (recursive form, exact):
`E[φ(x) φ(x₁)⋯φ(x_m)] = ∑_j G(x,x_j) E[∏_{i≠j} φ(x_i)]`. -/
theorem wick (hG : ∀ x y, G x y = G y x) (x : σ) (l : List σ) :
    gauss G (X x * mono l) = ∑ j : Fin l.length, G x l[j] * gauss G (mono (l.eraseIdx j)) := by
  rw [gauss_X_mul G hG x (mono_isHomogeneous l)]
  have hy : ∀ y, gauss G (pderiv y (mono l)) =
      ∑ j : Fin l.length, if l[j] = y then gauss G (mono (l.eraseIdx j)) else 0 := by
    intro y
    rw [gauss_eq G ((mono_isHomogeneous l).pderiv (i := y)) (N := l.length + 1) (by omega),
      pderiv_mono, gaussN_sum]
    refine sum_congr rfl fun j _ => ?_
    split_ifs
    · rw [gauss_eq G (mono_isHomogeneous _) (N := l.length + 1)]
      rw [List.length_eraseIdx]; split_ifs <;> omega
    · simp [gaussN]
  simp_rw [hy, mul_sum]
  rw [Finset.sum_comm]
  refine sum_congr rfl fun j _ => ?_
  simp [mul_ite]

theorem gauss_two (hG : ∀ x y, G x y = G y x) (x y : σ) :
    gauss G (X x * X y) = G x y := by
  have := wick G hG x [y]
  simp only [mono, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one,
    List.length_cons, List.length_nil] at this
  rw [this]; simp [mono, gauss_one]

/-! ### Moments of a linear observable -/

/-- The smeared field `φ(J) = ∑_x J(x) φ(x)`. -/
noncomputable def lin (J : σ → ℝ) : MvPolynomial σ ℝ := ∑ x, C (J x) * X x

theorem lin_isHomogeneous (J : σ → ℝ) : (lin J).IsHomogeneous 1 :=
  IsHomogeneous.sum _ _ _ fun x _ => isHomogeneous_C_mul_X (J x) x

theorem pderiv_lin (J : σ → ℝ) (y : σ) : pderiv y (lin J) = C (J y) := by
  unfold lin; rw [map_sum]; simp_rw [pderiv_C_mul, pderiv_X_eq]; simp [mul_ite]

/-- `E[φ(J)^{n+2}] = (n+1) ⟨J,GJ⟩ E[φ(J)^n]`. -/
theorem gauss_lin_pow (hG : ∀ x y, G x y = G y x) (J : σ → ℝ) (n : ℕ) :
    gauss G (lin J ^ (n + 2)) = (n + 1) * (∑ x, ∑ y, J x * G x y * J y) * gauss G (lin J ^ n) := by
  have hpow : ∀ m, (lin J ^ m).IsHomogeneous m := fun m => by
    simpa using (lin_isHomogeneous J).pow m
  rw [gauss_eq G (hpow (n + 2)) (N := n + 1 + 1) (by omega)]
  have e : lin J ^ (n + 2) = ∑ x, J x • (X x * lin J ^ (n + 1)) := by
    rw [pow_succ' (lin J) (n + 1)]; unfold lin; rw [sum_mul]
    refine sum_congr rfl fun x _ => ?_
    rw [smul_eq_C_mul]; ring
  rw [e, gaussN_sum]
  simp_rw [gaussN_smul, gaussN_X_mul G hG]
  have hd : ∀ y, pderiv y (lin J ^ (n + 1)) = (((n : ℝ) + 1) * J y) • lin J ^ n := by
    intro y
    rw [pderiv_pow, pderiv_lin, smul_eq_C_mul, Nat.add_sub_cancel]
    simp only [map_mul, map_add, map_one, map_natCast, Nat.cast_add, Nat.cast_one]; ring
  simp_rw [hd, gaussN_smul, ← gauss_eq G (hpow n) (N := n + 1) (by omega)]
  simp only [mul_sum, sum_mul]
  refine sum_congr rfl fun x _ => sum_congr rfl fun y _ => by ring

theorem gauss_lin_one (J : σ → ℝ) : gauss G (lin J) = 0 := by
  rw [gauss_eq G (lin_isHomogeneous J) (N := 1) (by norm_num)]
  simp [gaussN, lin]

/-- Gaussian moments of a smeared field: `E[φ(J)^{2k}] = (2k−1)!! ⟨J,GJ⟩^k`,
odd moments vanish. -/
theorem gauss_lin_even (hG : ∀ x y, G x y = G y x) (J : σ → ℝ) (k : ℕ) :
    gauss G (lin J ^ (2 * k)) =
      (∏ j ∈ range k, (2 * (j : ℝ) + 1)) * (∑ x, ∑ y, J x * G x y * J y) ^ k := by
  induction k with
  | zero => simp [gauss_one]
  | succ k ih =>
    rw [show 2 * (k + 1) = 2 * k + 2 by ring, gauss_lin_pow G hG, ih, prod_range_succ]
    push_cast; ring

theorem gauss_lin_odd (hG : ∀ x y, G x y = G y x) (J : σ → ℝ) (k : ℕ) :
    gauss G (lin J ^ (2 * k + 1)) = 0 := by
  induction k with
  | zero => simpa using gauss_lin_one G J
  | succ k ih =>
    rw [show 2 * (k + 1) + 1 = (2 * k + 1) + 2 by ring, gauss_lin_pow G hG, ih, mul_zero]

end Wick

end QE.OpenSto.Field

set_option linter.unusedSectionVars false

namespace QE.OpenSto.Learn

open Finset QE.Learn

/-! ## Occam bounds over realised functions and over symmetry orbits -/

section Occam

variable {Z : Type*} [Fintype Z]

theorem probS_mono (n : ℕ) (q : Z → ℝ) (hq : ∀ z, 0 ≤ q z) (A B : (Fin n → Z) → Prop)
    (hAB : ∀ ω, A ω → B ω) : probS n q A ≤ probS n q B := by
  classical
  unfold probS
  apply sum_le_sum; intro ω _
  have := wt_nonneg q hq ω
  by_cases ha : A ω
  · simp [ha, hAB ω ha]
  · simp only [ha, ite_false]; split_ifs <;> linarith

/-- **Occam bound over realised loss profiles.**  The deviation event of a
hypothesis depends on it only through its loss profile `ℓ h : Z → ℝ`, so the
union bound runs over the distinct profiles: the cardinality of the class is
replaced by the number of distinct functions it realises on the data space. -/
theorem occam_profiles {ι : Type*} [DecidableEq (Z → ℝ)] (q : Z → ℝ) (hq : ∀ z, 0 ≤ q z)
    (hq1 : ∑ z, q z = 1) (H : Finset ι) (ℓ : ι → Z → ℝ) (hℓ : ∀ h z, 0 ≤ ℓ h z ∧ ℓ h z ≤ 1)
    (m : ℕ) (hm : 0 < m) (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1 / 2) :
    probS m q (fun ω => ∃ h ∈ H,
        t ≤ (∑ z, q z * ℓ h z) - (∑ i, ℓ h (ω i)) / m) ≤
      (H.image ℓ).card * Real.exp (-(m * t ^ 2)) := by
  classical
  -- the class of profiles, with the clamped loss (equal to the profile on the image)
  let ℓ' : (Z → ℝ) → Z → ℝ := fun f z => max 0 (min (f z) 1)
  have hℓ' : ∀ f z, 0 ≤ ℓ' f z ∧ ℓ' f z ≤ 1 := fun f z =>
    ⟨le_max_left _ _, max_le (by norm_num) (min_le_right _ _)⟩
  have hfix : ∀ h z, ℓ' (ℓ h) z = ℓ h z := fun h z => by
    simp only [ℓ']; rw [min_eq_left (hℓ h z).2, max_eq_right (hℓ h z).1]
  refine le_trans ?_ (occam q hq hq1 (H.image ℓ) ℓ' hℓ' m hm t ht0 ht1)
  apply probS_mono m q hq
  rintro ω ⟨h, hh, hb⟩
  refine ⟨ℓ h, mem_image_of_mem ℓ hh, ?_⟩
  simp only [hfix]; exact hb

open Classical in
/-- **Union bound over orbits.**  If a finite group `G` acts on the
hypotheses and the loss is `G`-invariant, the Occam bound holds with the
number of `G`-orbits met by `H` in place of `#H`; and that number is at least
`#H / |G|`, so the symmetry saves at most `log |G|` bits. -/
theorem occam_orbits {G ι : Type*} [Group G] [Fintype G] [MulAction G ι]
    (q : Z → ℝ) (hq : ∀ z, 0 ≤ q z) (hq1 : ∑ z, q z = 1) (H : Finset ι)
    (ℓ : ι → Z → ℝ) (hℓ : ∀ h z, 0 ≤ ℓ h z ∧ ℓ h z ≤ 1)
    (hinv : ∀ (g : G) (h : ι), ℓ (g • h) = ℓ h)
    (m : ℕ) (hm : 0 < m) (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1 / 2) :
    probS m q (fun ω => ∃ h ∈ H,
        t ≤ (∑ z, q z * ℓ h z) - (∑ i, ℓ h (ω i)) / m) ≤
      (H.image (fun h => (Quotient.mk (MulAction.orbitRel G ι) h))).card *
        Real.exp (-(m * t ^ 2)) ∧
    H.card ≤ Fintype.card G *
      (H.image (fun h => (Quotient.mk (MulAction.orbitRel G ι) h))).card := by
  classical
  set π : ι → MulAction.orbitRel.Quotient G ι := fun h => Quotient.mk _ h
  -- the profile factors through the orbit map
  have hfac : ∀ h h', π h = π h' → ℓ h = ℓ h' := by
    intro h h' e
    have : h ∈ MulAction.orbit G h' := Quotient.exact e
    obtain ⟨g, rfl⟩ := this
    exact hinv g h'
  have hcard : (H.image ℓ).card ≤ (H.image π).card := by
    -- choose a profile map on orbits
    have : H.image ℓ ⊆ (H.image π).image (fun o => ℓ (Quotient.out o)) := by
      intro f hf
      obtain ⟨h, hh, rfl⟩ := mem_image.mp hf
      refine mem_image.mpr ⟨π h, mem_image_of_mem π hh, ?_⟩
      exact hfac _ _ (by simp [π])
    exact (card_le_card this).trans card_image_le
  constructor
  · refine (occam_profiles q hq hq1 H ℓ hℓ m hm t ht0 ht1).trans ?_
    apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
    exact_mod_cast hcard
  · apply orbits_lower H π (Fintype.card G)
    intro o _
    obtain ⟨h0, rfl⟩ := Quotient.exists_rep o
    -- the fibre over the orbit of `h0` lies in the image of `g ↦ g • h0`
    have hsub : H.filter (fun x => π x = Quotient.mk _ h0) ⊆
        (univ : Finset G).image (fun g => g • h0) := by
      intro x hx
      have hx' : π x = Quotient.mk _ h0 := (mem_filter.mp hx).2
      have : x ∈ MulAction.orbit G h0 := Quotient.exact hx'
      obtain ⟨g, rfl⟩ := this
      exact mem_image_of_mem _ (mem_univ g)
    exact (card_le_card hsub).trans (card_image_le.trans (by simp))

/-- The saving of the orbit bound is at most `ln |G|` in the complexity term:
`ln #H - ln |G| ≤ ln #orbits`. -/
theorem log_orbits_ge (Hc g o : ℕ) (hg : 0 < g) (ho : 0 < o) (h : Hc ≤ g * o) (hH : 0 < Hc) :
    Real.log Hc - Real.log g ≤ Real.log o := by
  have hgR : (0 : ℝ) < g := by exact_mod_cast hg
  have hoR : (0 : ℝ) < o := by exact_mod_cast ho
  have hHR : (0 : ℝ) < Hc := by exact_mod_cast hH
  have : (Hc : ℝ) ≤ g * o := by exact_mod_cast h
  have := Real.log_le_log hHR this
  rw [Real.log_mul hgR.ne' hoR.ne'] at this
  linarith

/-- **No-go: counting realised functions cannot beat random labels.**  If the
realised profiles `F` contain, for every binary labelling `y` of `m` data
points `z i`, a profile equal to the labelling on those points, then
`#F ≥ 2^m`. -/
theorem shatter_card {m : ℕ} (F : Finset (Z → ℝ)) (z : Fin m → Z)
    (hF : ∀ y : Fin m → Bool, ∃ f ∈ F, ∀ i, f (z i) = if y i then 1 else 0) :
    2 ^ m ≤ F.card := by
  classical
  choose f hfF hf using hF
  have hinj : Function.Injective f := by
    intro y y' e
    funext i
    have h1 := hf y i
    have h2 := hf y' i
    rw [e] at h1
    rw [h1] at h2
    cases hy : y i <;> cases hy' : y' i <;> simp_all
  have : (univ.image f) ⊆ F := by
    intro g hg; obtain ⟨y, _, rfl⟩ := mem_image.mp hg; exact hfF y
  calc 2 ^ m = (univ : Finset (Fin m → Bool)).card := by simp
    _ = (univ.image f).card := (card_image_of_injective _ hinj).symm
    _ ≤ F.card := card_le_card this

/-- Consequently the Occam radius computed from the number of realised
functions is at least `√(ln 2) > 1/2`: the bound is vacuous for every class
that fits all labellings of the sample size. -/
theorem shatter_radius {m : ℕ} (hm : 0 < m) (Fc : ℕ) (hF : 2 ^ m ≤ Fc) (δ : ℝ) (hδ0 : 0 < δ)
    (hδ1 : δ ≤ 1) :
    1 / 2 < Real.sqrt ((Real.log Fc + Real.log (1 / δ)) / m) := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hFpos : (0 : ℝ) < Fc := by
    have : 0 < Fc := lt_of_lt_of_le (by positivity) hF
    exact_mod_cast this
  have h1 : (m : ℝ) * Real.log 2 ≤ Real.log Fc := by
    have : ((2 : ℝ) ^ m) ≤ Fc := by exact_mod_cast hF
    have := Real.log_le_log (by positivity) this
    rwa [Real.log_pow] at this
  have h2 : 0 ≤ Real.log (1 / δ) := Real.log_nonneg (by rw [le_div_iff₀ hδ0]; linarith)
  have hl2 : (1 : ℝ) / 4 < Real.log 2 := by
    have := Real.log_two_gt_d9; linarith
  have key : (1 : ℝ) / 4 < (Real.log Fc + Real.log (1 / δ)) / m := by
    rw [lt_div_iff₀ hmR]; nlinarith
  have : Real.sqrt (1 / 4) = 1 / 2 := by
    rw [show (1 : ℝ) / 4 = (1 / 2) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  rw [← this]
  exact Real.sqrt_lt_sqrt (by norm_num) key

end Occam

/-! ## Quantisation errors cancel: the coarse cell as a product of residue sets -/

section Cell

/-- The residue box of a coarse cell: the error vectors `e = θ' - θ̂` of the
fine points `θ'` of one coarse cell (`thm:learning-coset`); coordinate `i`
ranges over its residue set `R i` (per-channel scales allowed). -/
def cell {N : ℕ} (R : Fin N → Finset ℝ) : Finset (Fin N → ℝ) := Fintype.piFinset R

theorem card_cell {N : ℕ} (R : Fin N → Finset ℝ) : (cell R).card = ∏ i, (R i).card := by
  simp [cell]

/-- Uniform average over the coarse cell. -/
noncomputable def avg {N : ℕ} (R : Fin N → Finset ℝ) (φ : (Fin N → ℝ) → ℝ) : ℝ :=
  (∑ e ∈ cell R, φ e) / ∏ i, ((R i).card : ℝ)

/-- Independence of the coordinates of the cell: the average of a product of
coordinate functions is the product of the coordinate averages. -/
theorem avg_prod {N : ℕ} (R : Fin N → Finset ℝ) (f : Fin N → ℝ → ℝ) :
    avg R (fun e => ∏ k, f k (e k)) = ∏ k, (∑ x ∈ R k, f k x) / (R k).card := by
  rw [avg, cell, ← prod_univ_sum, prod_div_distrib]

/-- First and second moments of the cell coordinates: `E eᵢ = μᵢ`,
`E eᵢeⱼ = μᵢμⱼ` for `i ≠ j`, `E eᵢ² = m₂ᵢ`. -/
theorem avg_mul {N : ℕ} (R : Fin N → Finset ℝ) (hR : ∀ i, (R i).Nonempty) (i j : Fin N) :
    avg R (fun e => e i * e j) =
      if i = j then (∑ x ∈ R i, x ^ 2) / (R i).card
      else ((∑ x ∈ R i, x) / (R i).card) * ((∑ x ∈ R j, x) / (R j).card) := by
  classical
  have hc : ∀ k, ((R k).card : ℝ) ≠ 0 := fun k => by
    have := (hR k).card_pos; positivity
  set f : Fin N → ℝ → ℝ := fun k x => (if k = i then x else 1) * (if k = j then x else 1)
  have hpt : ∀ e : Fin N → ℝ, e i * e j = ∏ k, f k (e k) := by
    intro e
    simp only [f, prod_mul_distrib, Fintype.prod_ite_eq']
  have : avg R (fun e => e i * e j) = avg R (fun e => ∏ k, f k (e k)) := by
    simp only [avg]; congr 1; apply sum_congr rfl; intro e _; exact hpt e
  rw [this, avg_prod]
  by_cases hij : i = j
  · subst hij
    rw [if_pos rfl]
    rw [Fintype.prod_eq_single i]
    · simp [f, sq]
    · intro k hk; simp [f, hk, hc k]
  · rw [if_neg hij]
    have : ∀ k, (∑ x ∈ R k, f k x) / (R k).card =
        (if k = i then (∑ x ∈ R i, x) / (R i).card else 1) *
        (if k = j then (∑ x ∈ R j, x) / (R j).card else 1) := by
      intro k
      by_cases h1 : k = i
      · subst h1; simp [f, hij]
      · by_cases h2 : k = j
        · subst h2; simp [f, h1]
        · simp [f, h1, h2, hc k]
    simp only [this, prod_mul_distrib, Fintype.prod_ite_eq']

theorem avg_coord {N : ℕ} (R : Fin N → Finset ℝ) (hR : ∀ i, (R i).Nonempty) (i : Fin N) :
    avg R (fun e => e i) = (∑ x ∈ R i, x) / (R i).card := by
  classical
  have hc : ∀ k, ((R k).card : ℝ) ≠ 0 := fun k => by
    have := (hR k).card_pos; positivity
  have : avg R (fun e => e i) = avg R (fun e => ∏ k, (if k = i then e k else 1)) := by
    simp only [avg, Fintype.prod_ite_eq']
  rw [this, avg_prod (f := fun k x => if k = i then x else 1)]
  rw [Fintype.prod_eq_single i]
  · simp
  · intro k hk; simp [hk, hc k]

/-- **Exact cell average of a quadratic loss change.**  Averaged over the
fine points of a coarse cell, `gᵀe + ½ eᵀHe` has mean
`Σᵢ gᵢμᵢ + ½ Σᵢⱼ Hᵢⱼ (m₂ᵢ if i = j, μᵢμⱼ otherwise)`, where `μᵢ` and `m₂ᵢ` are the
first two moments of the residue set of coordinate `i`. -/
theorem cell_mean_quadratic {N : ℕ} (R : Fin N → Finset ℝ) (hR : ∀ i, (R i).Nonempty)
    (g : Fin N → ℝ) (H : Fin N → Fin N → ℝ) :
    avg R (fun e => ∑ i, g i * e i + (1 / 2) * ∑ i, ∑ j, H i j * (e i * e j)) =
      ∑ i, g i * ((∑ x ∈ R i, x) / (R i).card) +
        (1 / 2) * ∑ i, ∑ j, H i j *
          (if i = j then (∑ x ∈ R i, x ^ 2) / (R i).card
           else ((∑ x ∈ R i, x) / (R i).card) * ((∑ x ∈ R j, x) / (R j).card)) := by
  have hlin : ∀ (φ ψ : (Fin N → ℝ) → ℝ) (a b : ℝ),
      avg R (fun e => a * φ e + b * ψ e) = a * avg R φ + b * avg R ψ := by
    intro φ ψ a b; simp only [avg, sum_add_distrib, ← mul_sum]; ring
  have hsum : ∀ (φ : Fin N → (Fin N → ℝ) → ℝ), avg R (fun e => ∑ i, φ i e) = ∑ i, avg R (φ i) := by
    intro φ; simp only [avg]; rw [sum_comm, sum_div]
  have hsmul : ∀ (φ : (Fin N → ℝ) → ℝ) (a : ℝ), avg R (fun e => a * φ e) = a * avg R φ := by
    intro φ a; simp only [avg, ← mul_sum]; ring
  have e1 := hlin (fun e => ∑ i, g i * e i) (fun e => ∑ i, ∑ j, H i j * (e i * e j)) 1 (1 / 2)
  simp only [one_mul] at e1
  rw [e1, hsum, hsum]
  congr 1
  · apply sum_congr rfl; intro i _; rw [hsmul, avg_coord R hR]
  · congr 1; apply sum_congr rfl; intro i _
    rw [hsum]; apply sum_congr rfl; intro j _; rw [hsmul, avg_mul R hR]

/-- Moments of the residue set of a coarse cell: `r` consecutive fine points
`h(a₀ + j)`, `j < r`.  Their mean is `h(a₀ + (r-1)/2)` and their variance is
exactly `h²(r²-1)/12`, whatever the offset `a₀`. -/
theorem residue_moments (h a0 : ℝ) (r : ℕ) :
    (∑ j ∈ range r, h * (a0 + j)) = r * (h * (a0 + (r - 1) / 2)) ∧
    (∑ j ∈ range r, (h * (a0 + j)) ^ 2) =
      r * ((h * (a0 + (r - 1) / 2)) ^ 2 + h ^ 2 * ((r : ℝ) ^ 2 - 1) / 12) := by
  induction r with
  | zero => simp
  | succ n ih =>
    rw [sum_range_succ, sum_range_succ, ih.1, ih.2]
    push_cast
    constructor <;> ring

/-- **The cancellation of quantisation errors, by counting.**  If each residue
set `R i` is symmetric about its centre `μᵢ` and lies within `cᵢ` of it, the
number of points of the coarse cell at which the centred dot-product error
`Σᵢ xᵢ(eᵢ - μᵢ)` reaches `t ≥ 0` is at most `#cell · exp(-t²/(2 Σᵢ cᵢ²xᵢ²))`. -/
theorem cell_tail {N : ℕ} (R : Fin N → Finset ℝ) (μ c : Fin N → ℝ)
    (hsym : ∀ i, ∀ y ∈ R i, 2 * μ i - y ∈ R i) (hc : ∀ i, ∀ y ∈ R i, |y - μ i| ≤ c i)
    (x : Fin N → ℝ) (t : ℝ) (ht : 0 ≤ t) (hpos : 0 < ∑ i, c i ^ 2 * x i ^ 2) :
    (((cell R).filter fun e => t ≤ ∑ i, x i * (e i - μ i)).card : ℝ) ≤
      (∏ i, ((R i).card : ℝ)) * Real.exp (-(t ^ 2 / (2 * ∑ i, c i ^ 2 * x i ^ 2))) := by
  classical
  set V := ∑ i, c i ^ 2 * x i ^ 2 with hV
  set s := t / V
  have hs : 0 ≤ s := div_nonneg ht hpos.le
  have hone : ∀ i, ∀ l : ℝ, ∑ y ∈ R i, Real.exp (l * (y - μ i)) ≤
      (R i).card * Real.exp (l ^ 2 * c i ^ 2 / 2) := by
    intro i l
    have hrefl : ∑ y ∈ R i, Real.exp (l * (y - μ i)) = ∑ y ∈ R i, Real.exp (-(l * (y - μ i))) := by
      apply sum_nbij' (fun y => 2 * μ i - y) (fun y => 2 * μ i - y)
      · intro y hy; exact hsym i y hy
      · intro y hy; exact hsym i y hy
      · intro y _; ring
      · intro y _; ring
      · intro y _; congr 1; ring
    have h2 : ∑ y ∈ R i, Real.exp (l * (y - μ i)) = ∑ y ∈ R i, Real.cosh (l * (y - μ i)) := by
      have : 2 * ∑ y ∈ R i, Real.exp (l * (y - μ i)) =
          2 * ∑ y ∈ R i, Real.cosh (l * (y - μ i)) := by
        rw [two_mul]; nth_rewrite 2 [hrefl]
        rw [← sum_add_distrib, mul_sum]
        apply sum_congr rfl; intro y _; rw [Real.cosh_eq]; ring
      linarith
    rw [h2]
    calc ∑ y ∈ R i, Real.cosh (l * (y - μ i)) ≤ ∑ y ∈ R i, Real.exp (l ^ 2 * c i ^ 2 / 2) := by
          apply sum_le_sum; intro y hy
          refine (Real.cosh_le_exp_half_sq _).trans (Real.exp_le_exp.mpr ?_)
          have : (y - μ i) ^ 2 ≤ c i ^ 2 := by
            have := hc i y hy; rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) this 2
          rw [mul_pow]; nlinarith [sq_nonneg l]
      _ = (R i).card * Real.exp (l ^ 2 * c i ^ 2 / 2) := by rw [sum_const, nsmul_eq_mul]
  calc (((cell R).filter fun e => t ≤ ∑ i, x i * (e i - μ i)).card : ℝ)
      = ∑ e ∈ cell R, if t ≤ ∑ i, x i * (e i - μ i) then (1 : ℝ) else 0 := by
        rw [sum_ite, sum_const_zero, add_zero, sum_const, nsmul_eq_mul, mul_one]
    _ ≤ ∑ e ∈ cell R, Real.exp (s * (∑ i, x i * (e i - μ i)) - s * t) := by
        apply sum_le_sum; intro e _
        split_ifs with h
        · exact Real.one_le_exp (by nlinarith)
        · exact (Real.exp_pos _).le
    _ = Real.exp (-(s * t)) * ∏ i, ∑ y ∈ R i, Real.exp ((s * x i) * (y - μ i)) := by
        rw [cell, prod_univ_sum, mul_sum]
        apply sum_congr rfl; intro e _
        rw [← Real.exp_sum, ← Real.exp_add]; congr 1
        rw [mul_sum]; simp only [mul_assoc]; ring
    _ ≤ Real.exp (-(s * t)) * ∏ i, (((R i).card : ℝ) * Real.exp ((s * x i) ^ 2 * c i ^ 2 / 2)) := by
        apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
        exact Finset.prod_le_prod₀ (fun i _ => sum_nonneg fun y _ => (Real.exp_pos _).le)
          (fun i _ => hone i _)
    _ = (∏ i, ((R i).card : ℝ)) * Real.exp (-(s * t) + s ^ 2 * V / 2) := by
        rw [prod_mul_distrib, ← Real.exp_sum, Real.exp_add]
        have : ∑ i, (s * x i) ^ 2 * c i ^ 2 / 2 = s ^ 2 * V / 2 := by
          rw [hV, mul_sum, sum_div]; apply sum_congr rfl; intro i _; ring
        rw [this]; ring
    _ = (∏ i, ((R i).card : ℝ)) * Real.exp (-(t ^ 2 / (2 * V))) := by
        congr 2; simp only [s]; field_simp; ring

/-- Markov's inequality on a finite set, by counting: `δ · #{φ > δ} ≤ Σ φ` for `φ ≥ 0`. -/
theorem count_markov {α : Type*} (C : Finset α) (φ : α → ℝ) (hφ : ∀ a ∈ C, 0 ≤ φ a)
    (δ : ℝ) : δ * ((C.filter fun a => δ < φ a).card : ℝ) ≤ ∑ a ∈ C, φ a := by
  classical
  calc δ * ((C.filter fun a => δ < φ a).card : ℝ) = ∑ a ∈ C.filter (fun a => δ < φ a), δ := by
        rw [sum_const, nsmul_eq_mul]; ring
    _ ≤ ∑ a ∈ C.filter (fun a => δ < φ a), φ a := sum_le_sum fun a ha => (mem_filter.mp ha).2.le
    _ ≤ ∑ a ∈ C, φ a := sum_le_sum_of_subset_of_nonneg (filter_subset _ _)
        fun a ha _ => hφ a ha

/-- **Quantisability is bounded below by the cell-averaged loss.**  If
`ℒ ≥ ℒ*` on the cell and `δ > 0`, the fraction of solutions
`{ℒ ≤ ℒ* + δ}` in the cell is at least `1 - (avg ℒ - ℒ*)/δ`. -/
theorem quantisability_lower {N : ℕ} (R : Fin N → Finset ℝ) (hR : ∀ i, (R i).Nonempty)
    (L : (Fin N → ℝ) → ℝ) (Lstar δ : ℝ) (hδ : 0 < δ) (hL : ∀ e ∈ cell R, Lstar ≤ L e) :
    1 - (avg R L - Lstar) / δ ≤
      (((cell R).filter fun e => L e ≤ Lstar + δ).card : ℝ) / ∏ i, ((R i).card : ℝ) := by
  classical
  have hc : (0 : ℝ) < ∏ i, ((R i).card : ℝ) :=
    prod_pos fun i _ => by have := (hR i).card_pos; positivity
  have hm := count_markov (cell R) (fun e => L e - Lstar) (fun e he => by linarith [hL e he]) δ
  have hsplit := card_filter_add_card_filter_not (s := cell R) (fun e => L e ≤ Lstar + δ)
  have hbad : ((cell R).filter fun e => ¬ (L e ≤ Lstar + δ)) =
      ((cell R).filter fun e => δ < L e - Lstar) := by
    apply filter_congr; intro e _; constructor
    · intro h; push Not at h; linarith
    · intro h; push Not; linarith
  rw [hbad, card_cell] at hsplit
  have hsplitR : (((cell R).filter fun e => L e ≤ Lstar + δ).card : ℝ) +
      (((cell R).filter fun e => δ < L e - Lstar).card : ℝ) = ∏ i, ((R i).card : ℝ) := by
    exact_mod_cast hsplit
  have hsum : ∑ e ∈ cell R, (L e - Lstar) =
      ∑ e ∈ cell R, L e - (∏ i, ((R i).card : ℝ)) * Lstar := by
    rw [sum_sub_distrib, sum_const, card_cell, nsmul_eq_mul]; push_cast; ring
  rw [hsum] at hm
  rw [le_div_iff₀ hc, avg]
  have e2 : (1 - ((∑ e ∈ cell R, L e) / (∏ i, ((R i).card : ℝ)) - Lstar) / δ) *
      (∏ i, ((R i).card : ℝ)) =
      (∏ i, ((R i).card : ℝ)) - (∑ e ∈ cell R, L e - (∏ i, ((R i).card : ℝ)) * Lstar) / δ := by
    field_simp
  rw [e2]
  have : (((cell R).filter fun e => δ < L e - Lstar).card : ℝ) ≤
      (∑ e ∈ cell R, L e - (∏ i, ((R i).card : ℝ)) * Lstar) / δ := by
    rw [le_div_iff₀ hδ]; linarith
  linarith

end Cell

/-! ## A granular implicit function theorem -/

section IFT

/-- Lattice points of `hℤ` within distance `r` of `c`: an integer interval. -/
noncomputable def fib1 (c r h : ℝ) : Finset ℤ := Icc ⌈(c - r) / h⌉ ⌊(c + r) / h⌋

theorem mem_fib1 {c r h : ℝ} (hh : 0 < h) (k : ℤ) : k ∈ fib1 c r h ↔ |h * k - c| ≤ r := by
  rw [fib1, mem_Icc, Int.ceil_le, Int.le_floor, div_le_iff₀ hh, le_div_iff₀ hh, abs_le]
  constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> nlinarith

/-- **Lattice points in an interval.**  A closed interval of length `2r`
contains between `⌊2r/h⌋` and `⌊2r/h⌋ + 1` points of `hℤ`, wherever it sits. -/
theorem card_fib1 {c r h : ℝ} (hh : 0 < h) (hr : 0 ≤ r) :
    ⌊2 * r / h⌋₊ ≤ (fib1 c r h).card ∧ (fib1 c r h).card ≤ ⌊2 * r / h⌋₊ + 1 := by
  rw [fib1, Int.card_Icc]
  set x := (c - r) / h
  set y := (c + r) / h
  have hL : y - x = 2 * r / h := by simp only [x, y]; field_simp; ring
  have hL0 : 0 ≤ 2 * r / h := by positivity
  have f1 := Int.floor_le y
  have f2 := Int.lt_floor_add_one y
  have c1 := Int.le_ceil x
  have c2 := Int.ceil_lt_add_one x
  have g1 := Nat.floor_le hL0
  have g2 := Nat.lt_floor_add_one (2 * r / h)
  set F := ⌊2 * r / h⌋₊
  -- integer bounds
  have up : ⌊y⌋ - ⌈x⌉ ≤ (F : ℤ) := by
    have : ((⌊y⌋ - ⌈x⌉ : ℤ) : ℝ) < F + 1 := by push_cast; linarith
    have : (⌊y⌋ - ⌈x⌉ : ℤ) < F + 1 := by exact_mod_cast this
    omega
  have lo : (F : ℤ) - 1 ≤ ⌊y⌋ - ⌈x⌉ := by
    have : ((F : ℤ) : ℝ) - 2 < ((⌊y⌋ - ⌈x⌉ : ℤ) : ℝ) := by push_cast; linarith
    have : (F : ℤ) - 2 < ⌊y⌋ - ⌈x⌉ := by exact_mod_cast this
    omega
  constructor <;> omega

/-- Lattice points of `hℤⁿ` in the sup-norm ball of radius `r` about `c`. -/
noncomputable def fibN {n : ℕ} (c : Fin n → ℝ) (r h : ℝ) : Finset (Fin n → ℤ) :=
  Fintype.piFinset fun i => fib1 (c i) r h

/-- The lattice point with index `k`. -/
def latPt {n : ℕ} (h : ℝ) (k : Fin n → ℤ) : Fin n → ℝ := fun i => h * k i

theorem mem_fibN {n : ℕ} {c : Fin n → ℝ} {r h : ℝ} (hh : 0 < h) (hr : 0 ≤ r) (k : Fin n → ℤ) :
    k ∈ fibN c r h ↔ ‖latPt h k - c‖ ≤ r := by
  rw [fibN, Fintype.mem_piFinset, pi_norm_le_iff_of_nonneg hr]
  simp only [mem_fib1 hh, latPt, Pi.sub_apply, Real.norm_eq_abs]

/-- **Lattice points in a cube**: between `⌊2r/h⌋ⁿ` and `(⌊2r/h⌋+1)ⁿ`. -/
theorem card_fibN {n : ℕ} (c : Fin n → ℝ) {r h : ℝ} (hh : 0 < h) (hr : 0 ≤ r) :
    ⌊2 * r / h⌋₊ ^ n ≤ (fibN c r h).card ∧ (fibN c r h).card ≤ (⌊2 * r / h⌋₊ + 1) ^ n := by
  rw [fibN, Fintype.card_piFinset]
  constructor
  · calc ⌊2 * r / h⌋₊ ^ n = ∏ _i : Fin n, ⌊2 * r / h⌋₊ := by simp
      _ ≤ ∏ i, (fib1 (c i) r h).card :=
          Finset.prod_le_prod' fun i _ => (card_fib1 hh hr).1
  · calc ∏ i, (fib1 (c i) r h).card ≤ ∏ _i : Fin n, (⌊2 * r / h⌋₊ + 1) :=
          Finset.prod_le_prod' fun i _ => (card_fib1 hh hr).2
      _ = (⌊2 * r / h⌋₊ + 1) ^ n := by simp

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
  [NormedSpace ℝ F]

/-- **Quantitative inverse estimates on a fibre.**  If `‖A⁻¹‖ ≤ a` and the
derivative of `f` stays within `β` of `A` on a convex set `V`, with `aβ < 1`,
then on `V`, `((1-aβ)/a)‖v-w‖ ≤ ‖f v - f w‖ ≤ (‖A‖+β)‖v-w‖`. -/
theorem fibre_bilip (f : E → F) (f' : E → E →L[ℝ] F) (A : E ≃L[ℝ] F) (a β : ℝ)
    (ha : ‖(A.symm : F →L[ℝ] E)‖ ≤ a) (V : Set E) (hV : Convex ℝ V)
    (hf : ∀ v ∈ V, HasFDerivWithinAt f (f' v) V v) (hβ : ∀ v ∈ V, ‖f' v - (A : E →L[ℝ] F)‖ ≤ β)
    {v w : E} (hv : v ∈ V) (hw : w ∈ V) :
    (1 - a * β) * ‖v - w‖ ≤ a * ‖f v - f w‖ ∧ ‖f v - f w‖ ≤ (‖(A : E →L[ℝ] F)‖ + β) * ‖v - w‖ := by
  have hmv : ‖(f v - A v) - (f w - A w)‖ ≤ β * ‖v - w‖ := by
    have := hV.norm_image_sub_le_of_norm_hasFDerivWithin_le (f := fun x => f x - A x)
      (f' := fun x => f' x - (A : E →L[ℝ] F))
      (fun x hx => (hf x hx).sub (A : E →L[ℝ] F).hasFDerivWithinAt) hβ hw hv
    simpa using this
  have hAd : A v - A w = A (v - w) := by simp
  constructor
  · have h1 : ‖v - w‖ ≤ a * ‖A (v - w)‖ := by
      calc ‖v - w‖ = ‖(A.symm : F →L[ℝ] E) (A (v - w))‖ := by simp
        _ ≤ ‖(A.symm : F →L[ℝ] E)‖ * ‖A (v - w)‖ := ContinuousLinearMap.le_opNorm _ _
        _ ≤ a * ‖A (v - w)‖ := mul_le_mul_of_nonneg_right ha (norm_nonneg _)
    have h2 : ‖A (v - w)‖ ≤ ‖f v - f w‖ + β * ‖v - w‖ := by
      have : A (v - w) = (f v - f w) - ((f v - A v) - (f w - A w)) := by rw [← hAd]; abel
      rw [this]; exact (norm_sub_le _ _).trans (by linarith)
    have ha0 : 0 ≤ a := (norm_nonneg _).trans ha
    nlinarith
  · have : f v - f w = A (v - w) + ((f v - A v) - (f w - A w)) := by rw [← hAd]; abel
    rw [this]
    calc ‖A (v - w) + ((f v - A v) - (f w - A w))‖ ≤ ‖A (v - w)‖ + β * ‖v - w‖ :=
          (norm_add_le _ _).trans (by linarith)
      _ ≤ ‖(A : E →L[ℝ] F)‖ * ‖v - w‖ + β * ‖v - w‖ := by
          have := (A : E →L[ℝ] F).le_opNorm (v - w); simp only [ContinuousLinearEquiv.coe_coe] at this
          linarith
      _ = (‖(A : E →L[ℝ] F)‖ + β) * ‖v - w‖ := by ring

/-- **Existence of the zero of a fibre** (Newton–Kantorovich, simplified
form): under the hypotheses of `fibre_bilip` on the closed ball of radius `R`
about `v₀` and `a‖f v₀‖ ≤ (1 - aβ)R`, the fibre has a zero `v*` in that ball,
with `‖v* - v₀‖ ≤ a‖f v₀‖/(1-aβ)`. -/
theorem fibre_zero [CompleteSpace E] (f : E → F) (f' : E → E →L[ℝ] F) (A : E ≃L[ℝ] F)
    (a β R : ℝ) (ha : ‖(A.symm : F →L[ℝ] E)‖ ≤ a) (hβ0 : 0 ≤ β) (haβ : a * β < 1) (v0 : E)
    (hf : ∀ v ∈ Metric.closedBall v0 R, HasFDerivWithinAt f (f' v) (Metric.closedBall v0 R) v)
    (hβ : ∀ v ∈ Metric.closedBall v0 R, ‖f' v - (A : E →L[ℝ] F)‖ ≤ β)
    (hR : a * ‖f v0‖ ≤ (1 - a * β) * R) :
    ∃ vs ∈ Metric.closedBall v0 R, f vs = 0 ∧ (1 - a * β) * ‖vs - v0‖ ≤ a * ‖f v0‖ := by
  set V := Metric.closedBall v0 R
  have ha0 : 0 ≤ a := (norm_nonneg _).trans ha
  have hR0 : 0 ≤ R := by
    have : 0 < 1 - a * β := by linarith
    have : 0 ≤ (1 - a * β) * R := (mul_nonneg ha0 (norm_nonneg _)).trans hR
    nlinarith
  set G : E → E := fun v => v - A.symm (f v)
  have hGlip : ∀ v ∈ V, ∀ w ∈ V, ‖G v - G w‖ ≤ a * β * ‖v - w‖ := by
    intro v hv w hw
    have hmv : ‖(f v - A v) - (f w - A w)‖ ≤ β * ‖v - w‖ := by
      have := (convex_closedBall v0 R).norm_image_sub_le_of_norm_hasFDerivWithin_le
        (f := fun x => f x - A x) (f' := fun x => f' x - (A : E →L[ℝ] F))
        (fun x hx => (hf x hx).sub (A : E →L[ℝ] F).hasFDerivWithinAt) hβ hw hv
      simpa using this
    have : G v - G w = A.symm ((A v - f v) - (A w - f w)) := by
      simp only [G, map_sub, ContinuousLinearEquiv.symm_apply_apply]
    rw [this]
    calc ‖A.symm ((A v - f v) - (A w - f w))‖
        ≤ ‖(A.symm : F →L[ℝ] E)‖ * ‖(A v - f v) - (A w - f w)‖ :=
          (A.symm : F →L[ℝ] E).le_opNorm _
      _ ≤ a * (β * ‖v - w‖) := by
          apply mul_le_mul ha _ (norm_nonneg _) ha0
          have : (A v - f v) - (A w - f w) = -((f v - A v) - (f w - A w)) := by abel
          rw [this, norm_neg]; exact hmv
      _ = a * β * ‖v - w‖ := by ring
  have hmaps : Set.MapsTo G V V := by
    intro v hv
    rw [Metric.mem_closedBall, dist_eq_norm] at hv ⊢
    have h1 := hGlip v (by rwa [Metric.mem_closedBall, dist_eq_norm]) v0 (Metric.mem_closedBall_self hR0)
    have h2 : ‖G v0 - v0‖ ≤ a * ‖f v0‖ := by
      simp only [G, sub_sub_cancel_left, norm_neg]
      exact ((A.symm : F →L[ℝ] E).le_opNorm _).trans (mul_le_mul_of_nonneg_right ha (norm_nonneg _))
    calc ‖G v - v0‖ = ‖(G v - G v0) + (G v0 - v0)‖ := by abel_nf
      _ ≤ ‖G v - G v0‖ + ‖G v0 - v0‖ := norm_add_le _ _
      _ ≤ a * β * R + a * ‖f v0‖ := by
          have : a * β * ‖v - v0‖ ≤ a * β * R := mul_le_mul_of_nonneg_left hv (by positivity)
          linarith
      _ ≤ R := by linarith
  set K : NNReal := ⟨a * β, by positivity⟩
  have hK : K < 1 := by
    rw [← NNReal.coe_lt_coe]; exact haβ
  have hcontr : ContractingWith K (hmaps.restrict G V V) := by
    refine ⟨hK, LipschitzWith.of_dist_le_mul fun x y => ?_⟩
    simp only [Subtype.dist_eq, Set.MapsTo.val_restrict_apply, dist_eq_norm]
    exact hGlip x x.2 y y.2
  have hcomp : IsComplete V := Metric.isClosed_closedBall.isComplete
  obtain ⟨vs, hvs, hfix, -, -⟩ := hcontr.exists_fixedPoint' hcomp hmaps
    (Metric.mem_closedBall_self hR0) (edist_ne_top _ _)
  have hf0 : f vs = 0 := by
    have : A.symm (f vs) = 0 := by
      have : G vs = vs := hfix
      simp only [G] at this
      have := congrArg (fun z => vs - z) this
      simpa using this
    simpa using congrArg A this
  refine ⟨vs, hvs, hf0, ?_⟩
  have := (fibre_bilip f f' A a β ha V (convex_closedBall v0 R) hf hβ hvs
    (Metric.mem_closedBall_self hR0)).1
  rwa [hf0, zero_sub, norm_neg] at this

/-- For an isomorphism of a nonzero space, `1 ≤ ‖A⁻¹‖ ‖A‖`. -/
theorem one_le_norm_symm_mul {n : ℕ} (hn : 0 < n) (A : (Fin n → ℝ) ≃L[ℝ] (Fin n → ℝ)) :
    1 ≤ ‖(A.symm : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ))‖ * ‖(A : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ))‖ := by
  have e : (A.symm : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ)).comp (A : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ))
      = ContinuousLinearMap.id ℝ (Fin n → ℝ) := by ext; simp
  have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  have hid : ‖ContinuousLinearMap.id ℝ (Fin n → ℝ)‖ = 1 := ContinuousLinearMap.norm_id
  calc (1 : ℝ) = ‖(A.symm : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ)).comp
        (A : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ))‖ := by rw [e, hid]
    _ ≤ _ := ContinuousLinearMap.opNorm_comp_le _ _

open Classical in
/-- **Granular implicit function theorem (fibre form).**  Let a fibre map
`f = F(u, ·)` of `ℝⁿ` (sup norm, `n ≥ 1`) satisfy the derivative bounds of
`fibre_zero` on the closed ball `V` of radius `R` about `v₀`, and put
`r₋ = δ/(‖A‖+β)`, `r₊ = aδ/(1-aβ)`.  If `a‖f v₀‖/(1-aβ) + r₊ ≤ R` (the window
contains the fibre), there is a zero `v*` such that the lattice fibre
`{k : hk ∈ V, ‖f(hk)‖ ≤ δ}` (all of whose points lie in the `r₊`-cube about `v*`)
contains the lattice points of the `r₋`-cube about `v*`; hence it has between
`⌊2r₋/h⌋ⁿ` and `(⌊2r₊/h⌋+1)ⁿ` points. -/
theorem granular_ift_fibre {n : ℕ} (hn : 0 < n) (f : (Fin n → ℝ) → (Fin n → ℝ))
    (f' : (Fin n → ℝ) → (Fin n → ℝ) →L[ℝ] (Fin n → ℝ)) (A : (Fin n → ℝ) ≃L[ℝ] (Fin n → ℝ))
    (a β R δ h : ℝ) (ha : ‖(A.symm : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ))‖ ≤ a) (hβ0 : 0 ≤ β)
    (haβ : a * β < 1) (hδ : 0 ≤ δ) (hh : 0 < h) (v0 : Fin n → ℝ)
    (hf : ∀ v ∈ Metric.closedBall v0 R, HasFDerivWithinAt f (f' v) (Metric.closedBall v0 R) v)
    (hβ : ∀ v ∈ Metric.closedBall v0 R, ‖f' v - (A : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ))‖ ≤ β)
    (hR : a * ‖f v0‖ / (1 - a * β) + a * δ / (1 - a * β) ≤ R) :
    ∃ vs ∈ Metric.closedBall v0 R, f vs = 0 ∧
      (∀ k : Fin n → ℤ, latPt h k ∈ Metric.closedBall v0 R → ‖f (latPt h k)‖ ≤ δ →
        k ∈ fibN vs (a * δ / (1 - a * β)) h) ∧
      fibN vs (δ / (‖(A : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ))‖ + β)) h ⊆
        (fibN vs (a * δ / (1 - a * β)) h).filter
          (fun k => latPt h k ∈ Metric.closedBall v0 R ∧ ‖f (latPt h k)‖ ≤ δ) ∧
      ⌊2 * (δ / (‖(A : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ))‖ + β)) / h⌋₊ ^ n ≤
        ((fibN vs (a * δ / (1 - a * β)) h).filter
          (fun k => latPt h k ∈ Metric.closedBall v0 R ∧ ‖f (latPt h k)‖ ≤ δ)).card ∧
      ((fibN vs (a * δ / (1 - a * β)) h).filter
          (fun k => latPt h k ∈ Metric.closedBall v0 R ∧ ‖f (latPt h k)‖ ≤ δ)).card ≤
        (⌊2 * (a * δ / (1 - a * β)) / h⌋₊ + 1) ^ n := by
  classical
  set V := Metric.closedBall v0 R
  have hpos : 0 < 1 - a * β := by linarith
  have ha0 : 0 ≤ a := (norm_nonneg _).trans ha
  set nA := ‖(A : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ))‖
  have hR' : a * ‖f v0‖ ≤ (1 - a * β) * R := by
    have h1 : 0 ≤ a * δ / (1 - a * β) := by positivity
    have h2 : a * ‖f v0‖ / (1 - a * β) ≤ R := by linarith
    rw [div_le_iff₀ hpos] at h2; linarith
  obtain ⟨vs, hvs, hf0, hdist⟩ := fibre_zero f f' A a β R ha hβ0 haβ v0 hf hβ hR'
  refine ⟨vs, hvs, hf0, ?_⟩
  set rp := a * δ / (1 - a * β)
  set rm := δ / (nA + β)
  have hrp : 0 ≤ rp := by positivity
  have haA : 1 ≤ a * nA :=
    (one_le_norm_symm_mul hn A).trans (mul_le_mul_of_nonneg_right ha (norm_nonneg _))
  have hnA : 0 < nA + β := by
    have : 0 < nA := by
      by_contra hc; push Not at hc
      have : nA = 0 := le_antisymm hc (norm_nonneg _)
      rw [this, mul_zero] at haA; linarith
    linarith
  have hrm : 0 ≤ rm := by positivity
  have hrmp : rm ≤ rp := by
    rw [div_le_div_iff₀ hnA hpos]
    nlinarith [mul_nonneg ha0 hβ0, mul_nonneg hδ (mul_nonneg ha0 hβ0)]
  have outer : ∀ k : Fin n → ℤ, latPt h k ∈ V → ‖f (latPt h k)‖ ≤ δ → k ∈ fibN vs rp h := by
    intro k hk hfk
    have := (fibre_bilip f f' A a β ha V (convex_closedBall v0 R) hf hβ hk hvs).1
    rw [hf0, sub_zero] at this
    refine (mem_fibN hh hrp k).mpr ?_
    rw [le_div_iff₀ hpos]
    nlinarith
  have inner : fibN vs rm h ⊆ (fibN vs rp h).filter
      (fun k => latPt h k ∈ V ∧ ‖f (latPt h k)‖ ≤ δ) := by
    intro k hk
    have hk' := (mem_fibN hh hrm k).mp hk
    have hkV : latPt h k ∈ V := by
      rw [Metric.mem_closedBall, dist_eq_norm]
      have h1 : ‖vs - v0‖ ≤ a * ‖f v0‖ / (1 - a * β) := by
        rw [le_div_iff₀ hpos]; linarith
      calc ‖latPt h k - v0‖ = ‖(latPt h k - vs) + (vs - v0)‖ := by abel_nf
        _ ≤ ‖latPt h k - vs‖ + ‖vs - v0‖ := norm_add_le _ _
        _ ≤ R := by linarith
    have hfk : ‖f (latPt h k)‖ ≤ δ := by
      have := (fibre_bilip f f' A a β ha V (convex_closedBall v0 R) hf hβ hkV hvs).2
      rw [hf0, sub_zero] at this
      calc ‖f (latPt h k)‖ ≤ (nA + β) * ‖latPt h k - vs‖ := this
        _ ≤ (nA + β) * rm := mul_le_mul_of_nonneg_left hk' hnA.le
        _ = δ := by simp only [rm]; field_simp
    exact mem_filter.mpr ⟨outer k hkV hfk, hkV, hfk⟩
  refine ⟨outer, inner, ?_, ?_⟩
  · exact (card_fibN vs hh hrm).1.trans (card_le_card inner)
  · exact (card_le_card (filter_subset _ _)).trans (card_fibN vs hh hrp).2

/-- **No-go: a fixed number of points per fibre is impossible in general.**
For the slab `|v - u/2| ≤ δ` over the lattice `hℤ²` (the linear constraint
`F(u,v) = v - u/2`, rational coefficients), the fibre over `u = hk` has an
odd number of points when `k` is even and an even number when `k` is odd,
whatever `δ ≥ 0`: the fibre counts are never constant. -/
theorem slab_half_parity (h δ : ℝ) (hh : 0 < h) (hδ : 0 ≤ δ) (m : ℤ) :
    Odd (fib1 (h * (2 * m) / 2) δ h).card ∧ Even (fib1 (h * (2 * m + 1) / 2) δ h).card := by
  have hx : 0 ≤ δ / h := div_nonneg hδ hh.le
  constructor
  · -- interval [m - δ/h, m + δ/h]
    have e1 : (h * (2 * m) / 2 - δ) / h = (m : ℝ) - δ / h := by field_simp
    have e2 : (h * (2 * m) / 2 + δ) / h = (m : ℝ) + δ / h := by field_simp
    rw [fib1, e1, e2, Int.card_Icc]
    have c1 : ⌈(m : ℝ) - δ / h⌉ = m - ⌊δ / h⌋ := by
      rw [sub_eq_add_neg, Int.ceil_intCast_add, Int.ceil_neg]; ring
    have c2 : ⌊(m : ℝ) + δ / h⌋ = m + ⌊δ / h⌋ := by rw [Int.floor_intCast_add]
    rw [c1, c2]
    have : 0 ≤ ⌊δ / h⌋ := Int.floor_nonneg.mpr hx
    refine ⟨⌊δ / h⌋.toNat, ?_⟩
    omega
  · have e1 : (h * (2 * m + 1) / 2 - δ) / h = (m : ℝ) + (1 / 2 - δ / h) := by field_simp; ring
    have e2 : (h * (2 * m + 1) / 2 + δ) / h = (m : ℝ) + (δ / h + 1 / 2) := by field_simp; ring
    rw [fib1, e1, e2, Int.card_Icc]
    have c1 : ⌈(m : ℝ) + (1 / 2 - δ / h)⌉ = m + 1 - ⌊δ / h + 1 / 2⌋ := by
      rw [Int.ceil_intCast_add]
      have : (1 / 2 - δ / h : ℝ) = -(δ / h + 1 / 2) + 1 := by ring
      rw [this, Int.ceil_add_one, Int.ceil_neg]; ring
    have c2 : ⌊(m : ℝ) + (δ / h + 1 / 2)⌋ = m + ⌊δ / h + 1 / 2⌋ := by rw [Int.floor_intCast_add]
    rw [c1, c2]
    have : 0 ≤ ⌊δ / h + 1 / 2⌋ := Int.floor_nonneg.mpr (by linarith)
    refine ⟨⌊δ / h + 1 / 2⌋.toNat, ?_⟩
    omega

/-- **Integer constraints give exact thick graphs.**  If the centre of the
fibre is a lattice point (e.g. `F(u,v) = v - ⟨a,u⟩` with integer `a` and
`u ∈ hℤ^{N-1}`), the fibre has exactly `2⌊δ/h⌋+1` points, for every `u`. -/
theorem slab_integer_card (h δ : ℝ) (hh : 0 < h) (hδ : 0 ≤ δ) (m : ℤ) :
    (fib1 (h * m) δ h).card = 2 * ⌊δ / h⌋₊ + 1 := by
  have e1 : (h * m - δ) / h = (m : ℝ) - δ / h := by field_simp
  have e2 : (h * m + δ) / h = (m : ℝ) + δ / h := by field_simp
  rw [fib1, e1, e2, Int.card_Icc]
  have c1 : ⌈(m : ℝ) - δ / h⌉ = m - ⌊δ / h⌋ := by
    rw [sub_eq_add_neg, Int.ceil_intCast_add, Int.ceil_neg]; ring
  have c2 : ⌊(m : ℝ) + δ / h⌋ = m + ⌊δ / h⌋ := by rw [Int.floor_intCast_add]
  rw [c1, c2]
  have hx : 0 ≤ δ / h := div_nonneg hδ hh.le
  have : (⌊δ / h⌋₊ : ℤ) = ⌊δ / h⌋ := Int.natCast_floor_eq_floor hx
  omega

end IFT

end QE.OpenSto.Learn
