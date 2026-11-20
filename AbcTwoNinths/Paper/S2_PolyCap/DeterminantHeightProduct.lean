/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruiyi Zhang
-/

module

public import AbcTwoNinths.Paper.S2_PolyCap.SuccessiveMinimaCoordinates

/-!
# Determinant Height Product

The module bounds the product of plane-basis heights using their determinant. It supports Proposition 2.1 of the paper.

## Main results
* `AbcTwoNinths.PolyCap.determinantHeightProduct`
-/

@[expose] public section


namespace AbcTwoNinths.PolyCap

section

/--
An absolute determinant of one and the four weighted entry bounds imply `h₁ * h₂ < 12 * T * h₀`.
-/
theorem determinantHeightProduct {a b c d h₀ h₁ h₂ U T : ℝ}
    (hd : |a * d-b * c| = 1) (hh₀ : 0 < h₀) (hh₁ : 0 ≤ h₁) (hh₂ : 0 ≤ h₂)
    (ha : |a| * h₁ ≤ 3 * h₀) (hb : |b| * h₂ ≤ 2 * h₀)
    (hc : |c| * h₁ ≤ 3 * U) (he : |d| * h₂ ≤ 2 * U) (hU : U < T) :
    h₁ * h₂ < 12 * T * h₀ := by
  have htri := abs_sub (a * d) (b * c)
  rw [hd, abs_mul, abs_mul] at htri
  calc
    h₁ * h₂ ≤ (|a| * |d| + |b| * |c|) * (h₁ * h₂) := by
      simpa using mul_le_mul_of_nonneg_right htri (mul_nonneg hh₁ hh₂)
    _ = (|a| * h₁) * (|d| * h₂) + (|b| * h₂) * (|c| * h₁) := by ring
    _ ≤ (3 * h₀) * (2 * U) + (2 * h₀) * (3 * U) := by
      apply add_le_add
      · exact mul_le_mul ha he (mul_nonneg (abs_nonneg _) hh₂) (by positivity)
      · exact mul_le_mul hb hc (mul_nonneg (abs_nonneg _) hh₁) (by positivity)
    _ = 12 * U * h₀ := by ring
    _ < _ := by
      have h := mul_lt_mul_of_pos_right hU hh₀
      linarith

end

end AbcTwoNinths.PolyCap
