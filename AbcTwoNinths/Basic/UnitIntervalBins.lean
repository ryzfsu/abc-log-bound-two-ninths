/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruiyi Zhang
-/

module

public import Mathlib

/-!
# Unit Interval Bins

The module assigns a point to its unit interval bin and bounds the residual coordinate.

## Main results
* `AbcTwoNinths.Basic.slabBinResidual`
-/

@[expose] public section


namespace AbcTwoNinths.Basic

section

/--
Index the cell containing a point in the half-open unit interval subdivided into equally long cells.
-/
noncomputable def slabBin (N : ℕ) (z : ℝ) (hz₀ : 0 ≤ z) (hz : z < 1)
    (hN : 0 < N) : Fin N :=
  ⟨⌊(N : ℝ) * z⌋₊, (Nat.floor_lt (mul_nonneg (Nat.cast_nonneg N) hz₀)).2 (by
    have hNR : 0 < (N : ℝ) := by exact_mod_cast hN
    nlinarith [mul_pos hNR (sub_pos.mpr hz)])⟩

/--
The difference between a point and its cell's left endpoint is nonnegative and strictly smaller than the cell length.
-/
theorem slabBinResidual (N : ℕ) (z : ℝ) (hz₀ : 0 ≤ z) (hz : z < 1)
    (hN : 0 < N) :
    0 ≤ z - ((_root_.AbcTwoNinths.Basic.slabBin N z hz₀ hz hN).val : ℝ) / N ∧
      z - ((_root_.AbcTwoNinths.Basic.slabBin N z hz₀ hz hN).val : ℝ) / N < 1 / N := by
  have hNR : 0 < (N : ℝ) := by exact_mod_cast hN
  change 0 ≤ z - (⌊(N : ℝ) * z⌋₊ : ℝ) / N ∧
    z - (⌊(N : ℝ) * z⌋₊ : ℝ) / N < 1 / N
  constructor
  · apply sub_nonneg.mpr
    apply (div_le_iff₀ hNR).mpr
    simpa [mul_comm] using Nat.floor_le (mul_nonneg hNR.le hz₀)
  · rw [sub_lt_iff_lt_add, ← add_div, lt_div_iff₀ hNR]
    simpa [mul_comm, add_comm] using Nat.lt_floor_add_one ((N : ℝ) * z)

end

end AbcTwoNinths.Basic
