/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruiyi Zhang
-/

module

public import AbcTwoNinths.Paper.S3_ExteriorE1.TripleRank

/-!
# Onset Penalty

The module bounds the threshold losses associated with the support rank and the logarithmic scale. It supports Proposition 3.1 of the paper.

## Main results
* `AbcTwoNinths.ExteriorE1.onsetScalePenalty`
-/

@[expose] public section


namespace AbcTwoNinths.ExteriorE1

section

/--
Bounds the logarithmic loss from the support rank by one eighth of the slab budget at the given threshold.
-/
theorem onsetRankPenalty (x h : ℝ) (d : ℕ)
    (hx : 0 < x) (hh : 0 < h) (hy : 4 ≤ Real.log x)
    (hon : 192 * Real.log (768 / h) / h ≤ Real.log x)
    (hd : (d : ℝ) ≤ 12 * x / Real.log x) :
    (d : ℝ) * Real.log (1 + 3 * Real.log x) ≤ h * x / 8 := by
  let y := Real.log x
  let M : ℝ := 768 / h
  have hyp : 0 < y := by dsimp [y]; linarith
  have hMp : 0 < M := by dsimp [M]; positivity
  have hlog : Real.log (1 + 3 * y) ≤ Real.log M + 4 * y / M := by
    have h₁ := Real.log_le_log (show 0 < 1 + 3 * y by positivity)
      (show 1 + 3 * y ≤ 4 * y by dsimp [y]; linarith)
    have h₂ := Real.log_le_sub_one_of_pos (show 0 < 4 * y / M by positivity)
    rw [Real.log_div (by positivity) hMp.ne'] at h₂
    linarith
  have h1 : Real.log M ≤ h * y / 192 := by
    have hl := (div_le_iff₀ hh).mp hon
    dsimp [M, y]
    linarith
  have h2 : 4 * y / M = h * y / 192 := by
    dsimp [M]
    field_simp [hh.ne']
    ring
  have h3 : Real.log (1 + 3 * y) ≤ h * y / 96 := by linarith
  calc
    _ ≤ (d : ℝ) * (h * y / 96) := mul_le_mul_of_nonneg_left h3 (Nat.cast_nonneg _)
    _ ≤ (12 * x / y) * (h * y / 96) := mul_le_mul_of_nonneg_right hd (by positivity)
    _ = _ := by field_simp [hyp.ne']; ring

/--
Bounds the logarithmic scale loss by one eighth of the slab budget at the given threshold. This is used in the proof of Proposition 3.1 of the paper.
-/
theorem onsetScalePenalty (x h κ : ℝ) (hx : 0 < x) (hh : 0 < h)
    (hk : 0 < κ)
    (hon : (16 / h) * (max 0 (Real.log (9 / κ)) + 2 * Real.log (32 / h)) ≤ x) :
    Real.log (9 * x ^ 2 / κ) ≤ h * x / 8 := by
  let A : ℝ := 32 / h
  have hA : 0 < A := by dsimp [A]; positivity
  have hl := Real.log_le_sub_one_of_pos (div_pos hx hA)
  rw [Real.log_div hx.ne' hA.ne'] at hl
  have hxa : x / A = h * x / 32 := by dsimp [A]; field_simp [hh.ne']
  rw [hxa] at hl
  have hu : max 0 (Real.log (9 / κ)) + 2 * Real.log A ≤ h * x / 16 := by
    have hon' : 16 * (max 0 (Real.log (9 / κ)) + 2 * Real.log A) / h ≤ x := by
      simpa [A, div_mul_eq_mul_div] using hon
    linarith [(div_le_iff₀ hh).mp hon']
  rw [show 9 * x ^ 2 / κ = (9 / κ) * x ^ 2 by ring,
    Real.log_mul (by positivity) (by positivity), Real.log_pow]
  norm_num
  linarith [le_max_right 0 (Real.log (9 / κ))]

end

end AbcTwoNinths.ExteriorE1
