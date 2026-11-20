/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruiyi Zhang
-/

module

public import Mathlib

/-!
# Interpolation Moments

The module proves vanishing of the low-order interpolation moments of the exponential sum. It supports Proposition 3.1 of the paper.

## Main results
* `AbcTwoNinths.ExteriorE1.taylorMomentZero`
-/

@[expose] public section


namespace AbcTwoNinths.ExteriorE1

open scoped BigOperators

section

private theorem twiceCardLeSum (s : Finset ℕ) :
    s.card * (s.card - 1) ≤ 2 * ∑ x ∈ s, x := by
  classical
  induction hn : s.card using Nat.strong_induction_on generalizing s with
  | h n ih =>
    by_cases hs : s.Nonempty
    · let z := s.max' hs
      have hz : z ∈ s := Finset.max'_mem s hs
      have hcard := Finset.card_erase_of_mem hz
      have hlt : (s.erase z).card < n := by
        rw [← hn, hcard]
        exact Nat.sub_lt (Finset.card_pos.mpr hs) (by decide)
      have hb := ih _ hlt _ rfl
      have hz' : s.card ≤ z + 1 := by
        simpa using Finset.card_le_card (show s ⊆ Finset.range (z+1) from
          fun x hx => Finset.mem_range.mpr (Nat.lt_succ_of_le (Finset.le_max' s x hx)))
      have hsum := Finset.sum_erase_add s (fun x : ℕ => x) hz
      have hrel : n * (n - 1) = (n - 1) * (n - 1 - 1) + 2 * (n - 1) := by
        cases n with
        | zero => simp
        | succ n =>
          cases n with
          | zero => simp
          | succ n => simp only [Nat.succ_sub_one]; ring
      rw [hrel]
      rw [hcard, hn] at hb
      omega
    · have hnil := Finset.not_nonempty_iff_eq_empty.mp hs
      simp [hnil] at hn
      simp [← hn, hnil]

/--
The alternating moment vanishes when the selected row degrees plus the moment order are below the triangular threshold. This is used in the proof of Proposition 3.1 of the paper.
-/
theorem taylorMomentZero {ι : Type*} [Fintype ι] [DecidableEq ι]
    (s : Finset ι) (u w : ι → ℝ) (A : Matrix ι ι ℝ)
    (m : ℕ) (d : ι → ℕ)
    (hm : 2 * ((∑ i ∈ s, d i) + m) < s.card * (s.card - 1)) :
    (∑ σ : Equiv.Perm ι, Equiv.Perm.sign σ •
      (∏ j : ι, if σ j ∈ s then u j ^ d (σ j) else A (σ j) j) *
        (∑ i ∈ s, w i * u (σ.symm i)) ^ m) = 0 := by
  classical
  induction m generalizing d with
  | zero =>
    simp only [Nat.add_zero, pow_zero, mul_one] at hm ⊢
    let M : Matrix ι ι ℝ := fun i j => if i ∈ s then u j ^ d i else A i j
    change (∑ σ : Equiv.Perm ι, Equiv.Perm.sign σ • ∏ j, M (σ j) j) = 0
    rw [← Matrix.det_apply]
    by_contra h
    have hi : Set.InjOn d (s : Set ι) := by
      intro i hi j hj he
      by_contra hn
      exact h (Matrix.det_zero_of_row_eq hn (funext fun x => by
        change i ∈ s at hi
        change j ∈ s at hj
        simp [M, hi, hj, he]))
    have hs := twiceCardLeSum (s.image d)
    rw [Finset.card_image_of_injOn hi, Finset.sum_image hi] at hs
    omega
  | succ m ih =>
    simp only [pow_succ, ← mul_assoc, Finset.mul_sum, Finset.sum_comm (s := Finset.univ)]
    apply Finset.sum_eq_zero
    intro i hi
    let e (x : ι) := if x = i then d x + 1 else d x
    have he : ∑ x ∈ s, e x = (∑ x ∈ s, d x) + 1 := by
      have hx (x : ι) : e x = d x + if x = i then 1 else 0 := by
        by_cases h : x = i <;> simp [e, h]
      simp [hx, Finset.sum_add_distrib, hi]
    have hzero := ih e (by omega)
    rw [← mul_zero (w i), ← hzero, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro σ _
    have hprod :
        (∏ j : ι, if σ j ∈ s then u j ^ e (σ j) else A (σ j) j) =
        (∏ j : ι, if σ j ∈ s then u j ^ d (σ j) else A (σ j) j) * u (σ.symm i) := by
      conv_lhs => rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ (σ.symm i))]
      conv_rhs => rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ (σ.symm i))]
      have hrest : (∏ j ∈ Finset.univ.erase (σ.symm i),
          if σ j ∈ s then u j ^ e (σ j) else A (σ j) j) =
          ∏ j ∈ Finset.univ.erase (σ.symm i), if σ j ∈ s then u j ^ d (σ j) else A (σ j) j := by
        apply Finset.prod_congr rfl
        intro j hj
        have hji : σ j ≠ i := fun hh => (Finset.mem_erase.mp hj).1 (by
          rw [← hh, σ.symm_apply_apply])
        simp [e, hji]
      rw [hrest]
      simp [hi, e, pow_succ, mul_assoc]
    rw [hprod]
    simp only [Units.smul_def, zsmul_eq_mul]
    ring

/--
The factorial-normalized exponential sum records the derivative order and the rows chosen in the determinant expansion. This is used in the proof of Proposition 3.1 of the paper.
-/
noncomputable def taylorExponentialSum {ι : Type*} [Fintype ι] [DecidableEq ι]
    (s : Finset ι) (u l ε : ι → ℝ) (γ : ℝ) (d : ι → ℕ) (m : ℕ) (t : ℝ) : ℝ :=
  (∏ i : ι, ((d i).factorial : ℝ)⁻¹) *
  ∑ σ : Equiv.Perm ι, (Equiv.Perm.sign σ •
      ∏ j : ι, if σ j ∈ s then u j ^ d (σ j) else
        u j ^ d (σ j) * Real.exp (l (σ j) * γ * u j) *
          (Real.exp (l (σ j) * ε j) - 1)) *
    (∑ i ∈ s, (l i * γ) * u (σ.symm i)) ^ m *
    Real.exp ((∑ i ∈ s, (l i * γ) * u (σ.symm i)) * t)

/--
The interpolation exponential sum vanishes at zero for orders below the triangular threshold minus the selected degree sum.
-/
theorem taylorExponentialSumAtZero {ι : Type*} [Fintype ι] [DecidableEq ι]
    (s : Finset ι) (u l ε : ι → ℝ) (γ : ℝ) (d : ι → ℕ) (m : ℕ)
    (hm : m < s.card * (s.card - 1) / 2 - ∑ i ∈ s, d i) :
    _root_.AbcTwoNinths.ExteriorE1.taylorExponentialSum s u l ε γ d m 0 = 0 := by
  have hdegree : 2 * ((∑ i ∈ s, d i) + m) < s.card * (s.card - 1) := by omega
  have h := _root_.AbcTwoNinths.ExteriorE1.taylorMomentZero s u (fun i => l i * γ)
    (fun i j => u j ^ d i * Real.exp (l i * γ * u j) * (Real.exp (l i * ε j) - 1))
    m d hdegree
  simp [_root_.AbcTwoNinths.ExteriorE1.taylorExponentialSum, h]

end

end AbcTwoNinths.ExteriorE1
