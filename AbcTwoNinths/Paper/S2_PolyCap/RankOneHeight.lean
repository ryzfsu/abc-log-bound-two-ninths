/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruiyi Zhang
-/

module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Tactic

/-!
# Rank One Height

In the rank-one case, bounding the power index by `p - 1` and the product of the two primes by the
radical gives a cubic bound for the logarithmic height. This supports Proposition 2.1 of the paper.

## Main results
* `AbcTwoNinths.PolyCap.rankOneHeight`
-/

@[expose] public section


namespace AbcTwoNinths.PolyCap

section

/--
The rank-one depth and support bounds imply that the height is strictly below four times the cube of the radical bound. This is used in the proof of Proposition 2.1 of the paper.
-/
theorem rankOneHeight {H r R : ℝ} {p q d : ℕ}
    (hr : 0 < r) (hrR : r ≤ R) (hp : 1 ≤ p) (hq : 1 < q)
    (hpqR : (p : ℝ) * q ≤ R) (hd : d ≤ p - 1)
    (hdepth : H / (4 * r) < (d : ℝ) * Real.log (q : ℝ)) :
    H < 4 * R ^ 3 := by
  have hp' : (0 : ℝ) < p := by exact_mod_cast (show 0 < p by omega)
  have hq' : (1 : ℝ) < q := by exact_mod_cast hq
  have hdp : (d : ℝ) ≤ p := by exact_mod_cast (show d ≤ p by omega)
  have hlog0 : 0 ≤ Real.log (q : ℝ) := Real.log_nonneg hq'.le
  have hlog : Real.log (q : ℝ) < q := by
    linarith [Real.log_le_sub_one_of_pos (show (0 : ℝ) < q by positivity)]
  have hquot : H / (4 * r) < R :=
    (((hdepth.trans_le (mul_le_mul_of_nonneg_right hdp hlog0)).trans
      (mul_lt_mul_of_pos_left hlog hp')).trans_le hpqR)
  have hmul := (div_lt_iff₀ (show 0 < 4 * r by positivity)).mp hquot
  have hR : 0 < R := hr.trans_le hrR
  calc
    H < R * (4 * r) := hmul
    _ ≤ R * (4 * R) := by gcongr
    _ ≤ 4 * R ^ 3 := by
      have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hp
      have hR1 : 1 ≤ R := (show (1 : ℝ) ≤ p * q by
        simpa using mul_le_mul hp1 hq'.le zero_le_one hp'.le).trans hpqR
      nlinarith [mul_nonneg (sub_nonneg.mpr hR1) (sq_nonneg R)]

end

end AbcTwoNinths.PolyCap
