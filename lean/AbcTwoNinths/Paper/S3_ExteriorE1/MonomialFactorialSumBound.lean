/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruiyi Zhang
-/

module

public import AbcTwoNinths.Basic.DeterminantLogBound

/-!
# Monomial Factorial Sum Bound

The module bounds the logarithmic sum of the monomial factorials in the interpolation minor. It supports Proposition 3.1 of the paper.

## Main results
* `AbcTwoNinths.ExteriorE1.sumLogMonofactUpper`
-/

@[expose] public section


namespace AbcTwoNinths.ExteriorE1

open scoped BigOperators

section

/--
The logarithm of the product of factorial-normalized powers satisfies the upper bound for repeated interpolation rows. This is used in the proof of Proposition 3.1 of the paper.
-/
theorem sumLogMonofactUpper (J L : ℕ) (hJ : 0 < J) {Mmax : ℝ} (hM : 0 < Mmax) :
    Real.log (∏ i : Fin (J + 1) × Fin L, Mmax ^ i.1.val / (i.1.val.factorial : ℝ)) ≤
      (((J + 1) * L : ℕ) : ℝ) * (J : ℝ) / 2 *
        Real.log (Real.exp 2 * Mmax / (J : ℝ)) := by
  have hJ' : 0 < (J : ℝ) := by exact_mod_cast hJ
  have he (i : Fin (J + 1)) :
      Real.log (Mmax ^ i.val / (i.val.factorial : ℝ)) =
        (i.val : ℝ) * Real.log Mmax - Real.log (i.val.factorial : ℝ) := by
    rw [Real.log_div (pow_ne_zero _ hM.ne') (by positivity), Real.log_pow]
  rw [Real.log_prod (fun _ _ => by positivity), Fintype.sum_prod_type]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, he,
    ← Finset.mul_sum, Finset.sum_sub_distrib, ← Finset.sum_mul]
  rw [Real.log_div (by positivity) hJ'.ne', Real.log_mul (Real.exp_ne_zero _) hM.ne',
    Real.log_exp]
  push_cast
  have h := _root_.AbcTwoNinths.Basic.factorialRowLower J hJ
  have hs := _root_.AbcTwoNinths.Basic.determinantLogBoundRowSum J
  have hh := mul_le_mul_of_nonneg_left h (show 0 ≤ (L : ℝ) by positivity)
  have hc : ((J : ℝ) + 1) * (L : ℝ) * (J : ℝ) / 2 =
      (L : ℝ) * ∑ i : Fin (J + 1), (i.val : ℝ) := by
    rw [show ((J : ℝ) + 1) * (L : ℝ) * (J : ℝ) / 2 =
        (L : ℝ) * (((J : ℝ) + 1) * (J : ℝ)) / 2 by ring, ← hs]
    ring
  rw [hc]
  nlinarith only [hh, congrArg (fun x : ℝ => (L : ℝ) * x) hs]

end

end AbcTwoNinths.ExteriorE1
