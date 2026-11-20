/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruiyi Zhang
-/

module

public import Mathlib

/-!
# Newton Interpolation

The module proves Newton expansion and degree-vanishing identities for binomial polynomials.

## Main results
* `AbcTwoNinths.Basic.weightedNewtonExpansion`
-/

@[expose] public section

namespace AbcTwoNinths.Basic

section

open Polynomial Function
open scoped BigOperators

/-- The Newton coefficient of order (n) is the (n)-th forward difference at zero. -/
def newtonCoefficient (f : ℕ → ℤ) (n : ℕ) : ℤ :=
  (fwdDiff (1 : ℕ))^[n] f 0

/-- Expands an integer sequence at a natural argument in the binomial basis. -/
theorem newtonExpansion (f : ℕ → ℤ) (z : ℕ) :
    f z = ∑ n ∈ Finset.range (z+1), (z.choose n : ℤ) * _root_.AbcTwoNinths.Basic.newtonCoefficient f n := by
  simpa [_root_.AbcTwoNinths.Basic.newtonCoefficient, nsmul_eq_mul] using shift_eq_sum_fwdDiff_iter (1 : ℕ) f z 0

/--
Newton coefficients vanish above the degree of a rational polynomial representing the sequence.
-/
theorem newtonDegreeVanish (f : ℕ → ℤ) (P : ℚ[X]) (n : ℕ)
    (hP : P.natDegree < n) (hf : ∀ z : ℕ, (f z : ℚ) = P.eval (z : ℚ)) :
    _root_.AbcTwoNinths.Basic.newtonCoefficient f n = 0 := by
  have h := congrFun (Polynomial.fwdDiff_iter_eq_zero_of_degree_lt hP) 0
  rw [fwdDiff_iter_eq_sum_shift] at h
  apply (Int.cast_eq_zero (α := ℚ)).mp
  rw [_root_.AbcTwoNinths.Basic.newtonCoefficient, fwdDiff_iter_eq_sum_shift, Int.cast_sum]
  simpa [hf, zsmul_eq_mul] using h

private theorem pochDegree (k : ℕ) : (descPochhammer ℚ k).natDegree ≤ k := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [descPochhammer_succ_right]
    exact (natDegree_mul_le ..).trans (by
      have h := natDegree_sub_le (X : ℚ[X]) (C (k : ℚ))
      simp at h
      omega)

/-- The rational polynomial taking the value `(c*z).choose k` at each natural argument `z`. -/
noncomputable def choosePoly (c k : ℕ) : ℚ[X] :=
  C ((k.factorial : ℚ)⁻¹) * (descPochhammer ℚ k).comp (C (c : ℚ) * X)

/--
Evaluating the scaled binomial polynomial at a natural number gives the corresponding binomial coefficient.
-/
theorem choosePolyEval (c k z : ℕ) :
    (_root_.AbcTwoNinths.Basic.choosePoly c k).eval (z : ℚ) = ((c*z).choose k : ℚ) := by
  rw [Nat.cast_choose_eq_descPochhammer_div ℚ]
  simp [_root_.AbcTwoNinths.Basic.choosePoly, Nat.cast_mul, div_eq_mul_inv, mul_comm]

/-- The scaled binomial polynomial has degree at most its lower binomial index. -/
theorem choosePolyDegree (c k : ℕ) : (_root_.AbcTwoNinths.Basic.choosePoly c k).natDegree ≤ k := by
  unfold _root_.AbcTwoNinths.Basic.choosePoly
  have h : (C (c : ℚ) * X).natDegree ≤ 1 :=
    (natDegree_mul_le ..).trans (by simp)
  exact (natDegree_mul_le ..).trans (by
    simp only [natDegree_C, zero_add]
    exact (natDegree_comp_le ..).trans (by simpa using Nat.mul_le_mul (pochDegree k) h))

/--
The Newton coefficient of a product of two scaled binomial sequences vanishes above the sum of their degrees.
-/
theorem chooseProductVanish (c k t m n : ℕ) (hn : k + m < n) :
    _root_.AbcTwoNinths.Basic.newtonCoefficient (fun z => ((c*z).choose k : ℤ) * ((t*z).choose m : ℤ)) n = 0 := by
  apply _root_.AbcTwoNinths.Basic.newtonDegreeVanish _ (_root_.AbcTwoNinths.Basic.choosePoly c k * _root_.AbcTwoNinths.Basic.choosePoly t m)
  · exact ((natDegree_mul_le ..).trans
      (Nat.add_le_add (_root_.AbcTwoNinths.Basic.choosePolyDegree c k) (_root_.AbcTwoNinths.Basic.choosePolyDegree t m))).trans_lt hn
  · intro z
    simp [_root_.AbcTwoNinths.Basic.choosePolyEval]

/-- If `p ∣ g - 1`, the weighted coefficient of order `n` is divisible by `p ^ (n - k)`. -/
theorem newtonWeightedDvd {R : Type*} [CommRing R] (p g : R)
    (hp : p ∣ g - 1) (c k t n M : ℕ) :
    p ^ (n - k) ∣ ∑ m ∈ Finset.range M,
      (g - 1) ^ m *
      (_root_.AbcTwoNinths.Basic.newtonCoefficient (fun z => ((c*z).choose k : ℤ) * ((t*z).choose m : ℤ)) n : R) := by
  apply Finset.dvd_sum
  intro m _
  by_cases h : k + m < n
  · simp [_root_.AbcTwoNinths.Basic.chooseProductVanish c k t m n h]
  · exact (pow_dvd_pow p (show n - k ≤ m by omega)).trans
      ((pow_dvd_pow_of_dvd hp m).trans (dvd_mul_right _ _))

/--
Expands a binomial coefficient times a geometric weight in the binomial basis within the given truncation bounds.
-/
theorem weightedNewtonExpansion {R : Type*} [CommRing R]
    (g : R) (c k t z D M : ℕ) (hz : z < D) (ht : t*z < M) :
    ((c*z).choose k : R) * g ^ (t*z) =
      ∑ n ∈ Finset.range D, (∑ m ∈ Finset.range M,
        (g-1)^m * (_root_.AbcTwoNinths.Basic.newtonCoefficient
          (fun y => ((c*y).choose k : ℤ) * ((t*y).choose m : ℤ)) n : R)) *
        (z.choose n : R) := by
  have hb : g ^ (t*z) = ∑ m ∈ Finset.range M, (g-1)^m * ((t*z).choose m : R) := by
    have h := add_pow (g-1) (1 : R) (t*z)
    simp only [sub_add_cancel, one_pow, mul_one] at h
    rw [h]
    apply Finset.sum_subset (Finset.range_subset_range.mpr (by omega))
    intro m _ hm
    have hlt : t*z < m := by simp at hm; omega
    simp [Nat.choose_eq_zero_of_lt hlt]
  have hnew (m : ℕ) : (((c*z).choose k : R) * ((t*z).choose m : R)) =
      ∑ n ∈ Finset.range D,
        (z.choose n : R) * (_root_.AbcTwoNinths.Basic.newtonCoefficient
          (fun y => ((c*y).choose k : ℤ) * ((t*y).choose m : ℤ)) n : R) := by
    have h := congrArg (fun a : ℤ => (a : R)) (_root_.AbcTwoNinths.Basic.newtonExpansion
      (fun y => ((c*y).choose k : ℤ) * ((t*y).choose m : ℤ)) z)
    push_cast at h
    rw [h]
    apply Finset.sum_subset (Finset.range_subset_range.mpr (by omega))
    intro n _ hn
    have hlt : z < n := by simp at hn; omega
    simp [Nat.choose_eq_zero_of_lt hlt]
  rw [hb, Finset.mul_sum]
  simp_rw [show ∀ m : ℕ, ((c*z).choose k : R) *
      ((g-1)^m * ((t*z).choose m : R)) =
      (g-1)^m * (((c*z).choose k : R) * ((t*z).choose m : R)) from fun m => by ring,
    hnew, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro n _
  apply Finset.sum_congr rfl
  intro m _
  ring

end

end AbcTwoNinths.Basic
