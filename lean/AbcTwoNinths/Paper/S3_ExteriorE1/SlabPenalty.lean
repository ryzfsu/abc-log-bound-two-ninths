/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruiyi Zhang
-/

module

public import AbcTwoNinths.Paper.S3_ExteriorE1.LogSlabBudget

/-!
# Slab Penalty

The module controls the loss introduced when converting the slab count into a strict inequality. It supports Proposition 3.1 of the paper.

## Main results
* `AbcTwoNinths.ExteriorE1.slabPenalty`
-/

@[expose] public section


namespace AbcTwoNinths.ExteriorE1

section

/--
The two budget bounds place the slab penalty at least half the logarithmic height below the logarithm of the multiplicity. This is used in the proof of Proposition 3.1 of the paper.
-/
theorem slabPenalty (H T m B x κ : ℝ) (d : ℕ)
    (hH : 1 < H) (hT : 0 < T) (hTx : T ≤ x) (hκ : 0 < κ)
    (hlo : κ * H / (3 * x) ≤ m)
    (h₁ : Real.log (9 * x ^ 2 / κ) ≤ Real.log H / 8)
    (h₂ : (d : ℝ) * Real.log B ≤ Real.log H / 8) :
    Real.log (3 * T) + (d : ℝ) * Real.log B ≤ Real.log m - Real.log H / 2 := by
  have hx := hT.trans_le hTx
  have hpos : 0 < κ * H / (3 * x) := by
    have : 0 < H := by linarith
    positivity
  have hm := hpos.trans_le hlo
  have hlog := Real.log_le_log hpos hlo
  have hTlog := Real.log_le_log (show 0 < 3 * T by positivity)
    (show 3 * T ≤ 3 * x by linarith)
  have heq : Real.log (9 * x ^ 2 / κ) =
      2 * Real.log (3 * x) - Real.log κ := by
    rw [show (9 : ℝ) * x ^ 2 = (3 * x) ^ 2 by ring,
      Real.log_div (by positivity) hκ.ne', Real.log_pow]
    norm_num
  rw [heq] at h₁
  rw [Real.log_div (by positivity) (by positivity), Real.log_mul hκ.ne' (by positivity)] at hlog
  linarith [Real.log_pos hH]

end

end AbcTwoNinths.ExteriorE1
