/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruiyi Zhang
-/

module

public import AbcTwoNinths.Paper.S3_ExteriorE1.StrictCapacity

/-!
# Log Slab Budget

The module bounds the cost of an integer slab in logarithmic coordinates. It supports Proposition 3.1 of the paper.

## Main results
* `AbcTwoNinths.ExteriorE1.slabLogBudget`
-/

@[expose] public section


namespace AbcTwoNinths.ExteriorE1

section

/--
The logarithmic penalty bounds the slab width between the reciprocal height and the scale and bounds its negative logarithm from below. This is used in the proof of Proposition 3.1 of the paper.
-/
theorem slabLogBudget (H T m B : ℝ) (d : ℕ)
    (hH : 1 < H) (hT : 1 ≤ T) (hm : 0 < m) (hmH : m ≤ 2 * H)
    (hB : 1 ≤ B)
    (hpen : Real.log (3 * T) + (d : ℝ) * Real.log B ≤ Real.log m - Real.log H / 2) :
    let ε := (3 * T / m) * B ^ d
    0 < ε ∧ ε < T ∧ Real.log H / 2 ≤ -Real.log ε ∧ 1 / H < ε := by
  let ε := (3 * T / m) * B ^ d
  have hT' : 0 < T := by linarith
  have hB' : 0 < B := by linarith
  have he : 0 < ε := by dsimp [ε]; positivity
  have hl : Real.log H / 2 ≤ -Real.log ε := by
    dsimp [ε]
    rw [Real.log_mul (by positivity) (by positivity),
      Real.log_div (by positivity) hm.ne', Real.log_pow]
    linarith
  have he1 : ε < 1 := by
    rw [← Real.log_lt_log_iff he (by norm_num), Real.log_one]
    linarith [Real.log_pos hH]
  refine ⟨he, he1.trans_le hT, hl, ?_⟩
  have hH' : 0 < H := by linarith
  have hBpow : 1 ≤ B ^ d := one_le_pow₀ hB
  have hfirst : 1 / H < 3 * T / m := by
    apply (div_lt_div_iff₀ hH' hm).2
    nlinarith [mul_nonneg (sub_nonneg.mpr hT) hH'.le]
  exact hfirst.trans_le (le_mul_of_one_le_right (by positivity) hBpow)

end

end AbcTwoNinths.ExteriorE1
