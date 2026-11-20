/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruiyi Zhang
-/

module

public import Mathlib

/-!
# Rect Bounds

The module bounds plane coordinates and the determinant product in the reduced rectangular basis.

## Main results
* `AbcTwoNinths.Basic.coordBounds`
* `AbcTwoNinths.Basic.determinantProduct`
-/

@[expose] public section


namespace AbcTwoNinths.Basic

section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Control both coordinates using minimality under integer translates. -/
theorem coordBounds (w₁ w₂ : E) (h₁ : ‖w₁‖ ≤ ‖w₂‖)
    (h₂ : ∀ n : ℤ, ‖w₂‖ ≤ ‖(n : ℝ) • w₁ + w₂‖) (a b : ℝ) :
    |a| * ‖w₁‖ ≤ 3 * ‖a • w₁ + b • w₂‖ ∧
    |b| * ‖w₂‖ ≤ 2 * ‖a • w₁ + b • w₂‖ := by
  let z := a • w₁ + b • w₂
  have hβ : |b| * ‖w₂‖ ≤ 2 * ‖z‖ := by
    by_cases hb : b = 0
    · simp [hb, norm_nonneg]
    let t := a / b
    let n : ℤ := ⌊t + 1 / 2⌋
    have hn₁ : (n : ℝ) ≤ t + 1 / 2 := Int.floor_le _
    have hn₂ : t + 1 / 2 < (n : ℝ) + 1 := Int.lt_floor_add_one _
    have hn : |(n : ℝ) - t| ≤ 1 / 2 := abs_le.mpr ⟨by linarith, by linarith⟩
    have heq : (n : ℝ) • w₁ + w₂ = (t • w₁ + w₂) + ((n : ℝ) - t) • w₁ := by
      module
    have htri := norm_add_le (t • w₁ + w₂) (((n : ℝ) - t) • w₁)
    rw [← heq, norm_smul, Real.norm_eq_abs] at htri
    have hh := mul_le_mul_of_nonneg_right hn (norm_nonneg w₁)
    have hl : ‖w₂‖ ≤ 2 * ‖t • w₁ + w₂‖ := by
      linarith [h₂ n]
    have hm := mul_le_mul_of_nonneg_left hl (abs_nonneg b)
    have hz : b • (t • w₁ + w₂) = z := by
      dsimp [t, z]
      rw [smul_add, smul_smul, mul_comm b, div_mul_cancel₀ a hb]
    rw [← hz, norm_smul, Real.norm_eq_abs]
    linarith
  have htri := norm_sub_le z (b • w₂)
  have heq : z - b • w₂ = a • w₁ := add_sub_cancel_right _ _
  rw [heq, norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs] at htri
  exact ⟨by linarith, hβ⟩

/-- Determinant comparison in the reduced coordinates. -/
theorem determinantProduct (w₁ w₂ : E) (h₁ : ‖w₁‖ ≤ ‖w₂‖)
    (h₂ : ∀ n : ℤ, ‖w₂‖ ≤ ‖(n : ℝ) • w₁ + w₂‖)
    (a b c d : ℝ) (hdet : |a*d - b*c| = 1) :
    ‖w₁‖ * ‖w₂‖ ≤ 12 * ‖a • w₁ + b • w₂‖ * ‖c • w₁ + d • w₂‖ := by
  obtain ⟨ha, hb⟩ := _root_.AbcTwoNinths.Basic.coordBounds w₁ w₂ h₁ h₂ a b
  obtain ⟨hc, hd⟩ := _root_.AbcTwoNinths.Basic.coordBounds w₁ w₂ h₁ h₂ c d
  have h := abs_add_le (a*d) (-(b*c))
  rw [← sub_eq_add_neg, hdet, abs_neg, abs_mul, abs_mul] at h
  have hmul := mul_le_mul_of_nonneg_right h
    (mul_nonneg (norm_nonneg w₁) (norm_nonneg w₂))
  have hAD := mul_le_mul ha hd (by positivity) (by positivity)
  have hBC := mul_le_mul hb hc (by positivity) (by positivity)
  nlinarith only [hmul, hAD, hBC]

end

end AbcTwoNinths.Basic
