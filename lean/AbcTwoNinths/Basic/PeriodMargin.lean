/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruiyi Zhang
-/

module

public import Mathlib

/-!
# Period Margin

The module defines the period margin for the rounded grid and gives its strict ceiling variant.

## Main results
* `AbcTwoNinths.Basic.periodMargin`
-/

@[expose] public section


namespace AbcTwoNinths.Basic

section

/-- The real period margin and the grid ratio imply the strict integer count inequality. -/
theorem periodMargin {I k M Q d : ℕ} {B g H U t : ℝ}
    (hQ : 0 < Q) (ht : 0 ≤ t) (hg : 0 < g) (hU : 0 < U)
    (hI : (I : ℝ) ≤ B) (hroof : H ≤ (k : ℝ) * (g * U))
    (hgrid : t ≤ (M : ℝ) / (Q : ℝ))
    (hmargin : B * (g * U) < H * t ^ d) :
    I * Q ^ d < k * M ^ d := by
  have hQp : 0 < (Q : ℝ) := by exact_mod_cast hQ
  have hh : (I : ℝ) * (g * U) < (k : ℝ) * (g * U) * ((M : ℝ) / Q) ^ d := by
    calc
      _ ≤ B * (g * U) := mul_le_mul_of_nonneg_right hI (by positivity)
      _ < H * t ^ d := hmargin
      _ ≤ ((k : ℝ) * (g * U)) * t ^ d := mul_le_mul_of_nonneg_right hroof (by positivity)
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ ht hgrid _) (by positivity)
  have hh' : (I : ℝ) < (k : ℝ) * ((M : ℝ) / Q) ^ d := by
    apply lt_of_mul_lt_mul_right _ (show 0 ≤ g * U by positivity)
    calc
      _ < (k : ℝ) * (g * U) * ((M : ℝ) / Q) ^ d := hh
      _ = _ := by ring
  rw [div_pow, ← mul_div_assoc] at hh'
  exact_mod_cast (lt_div_iff₀ (pow_pos hQp d)).1 hh'

end

section

end

end AbcTwoNinths.Basic
