/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruiyi Zhang
-/

module

public import Mathlib

/-!
# Centered Index Width

The sum of the distances of `L` consecutive indices from their midpoint is at most `L² / 4`.

## Main results
* `AbcTwoNinths.Basic.widthBound`
-/

@[expose] public section

namespace AbcTwoNinths.Basic

section

/-- The width. -/
private noncomputable def width (L : ℕ) : ℝ :=
  ∑ i : Fin L, |(i.val : ℝ) - ((L : ℝ) - 1) / 2|

private theorem widthTwo (L : ℕ) : width (L+2) = width L + (L+1 : ℝ) := by
  unfold width
  rw [Fin.sum_univ_succ, Fin.sum_univ_castSucc]
  simp only [Fin.val_zero, Fin.val_succ, Fin.val_castSucc, Fin.val_last,
    Nat.cast_add, Nat.cast_one, Nat.cast_ofNat]
  have hm (i : Fin L) :
      (i.val : ℝ) + 1 - ((L + 2 : ℝ) - 1) / 2 =
        (i.val : ℝ) - ((L : ℝ) - 1) / 2 := by ring
  simp_rw [hm]
  simp only [Nat.cast_zero]
  have hL : 0 ≤ (L : ℝ) := by positivity
  rw [abs_of_nonpos (by linarith : 0 - (((L : ℝ) + 2) - 1) / 2 ≤ 0),
    abs_of_nonneg (by linarith :
      0 ≤ (L : ℝ) + 1 - ((L + 2 : ℝ) - 1) / 2)]
  ring

/--
The sum of the distances of the indices of a finite interval from its midpoint is at most one quarter of its squared length.
-/
theorem widthBound (L : ℕ) :
    (∑ i : Fin L, |(i.val : ℝ) - ((L : ℝ) - 1) / 2|) ≤ (L : ℝ)^2/4 := by
  change width L ≤ _
  induction L using Nat.twoStepInduction with
  | zero => simp [width]
  | one => norm_num [width, Fin.sum_univ_succ]
  | more L ih _ =>
    rw [widthTwo]
    push_cast
    nlinarith

end

end AbcTwoNinths.Basic
