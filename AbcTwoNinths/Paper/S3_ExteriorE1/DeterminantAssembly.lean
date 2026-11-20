/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruiyi Zhang
-/

module

public import AbcTwoNinths.Paper.S3_ExteriorE1.RealContactCases
public import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Determinant Assembly

The module turns a quantitative interpolation determinant bound into the variable-radius real-logarithm estimate. It supports Proposition 3.1 of the paper.

## Main results
* `AbcTwoNinths.ExteriorE1.laurentProviderOfQuantitativeDeterminant`
-/

@[expose] public section


namespace AbcTwoNinths.ExteriorE1

section



/--
The quantitative determinant bound. This is used in the proof of Proposition 3.1 of the paper.
-/
def QuantitativeDeterminantBound : Prop :=
  ∀ (q₁ q₂ : ℚ) (b₁ b₂ : ℕ) (radius η₁ η₂ : ℝ),
    1 < q₁ → 1 < q₂ → _root_.AbcTwoNinths.ExteriorE1.Independent q₁ q₂ → 0 < b₁ → 0 < b₂ →
    1 ≤ radius → _root_.AbcTwoNinths.ExteriorE1.RadiusInputs q₁ radius η₁ → _root_.AbcTwoNinths.ExteriorE1.RadiusInputs q₂ radius η₂ →
    let B := (b₁ : ℝ) / η₂ + (b₂ : ℝ) / η₁
    let D₀ := max 4 (Real.log B / radius)
    let form := (b₂ : ℝ) * Real.log (q₂ : ℝ) - (b₁ : ℝ) * Real.log (q₁ : ℝ);
    -(Real.log (abs form)) ≤ 1157 * η₁ * η₂ * D₀ ^ 2 / radius

/--
The quantitative determinant bound implies the variable-radius Laurent estimate for
arbitrary positive coefficients used in Proposition 3.1.
-/
theorem laurentProviderOfQuantitativeDeterminant
    (hdet : _root_.AbcTwoNinths.ExteriorE1.QuantitativeDeterminantBound) : _root_.AbcTwoNinths.ExteriorE1.LaurentProvider := by
  intro q₁ q₂ b₁ b₂ radius η₁ η₂ hq₁ hq₂ hi hb₁ hb₂ hr hη₁ hη₂
  dsimp [_root_.AbcTwoNinths.ExteriorE1.LaurentTarget]
  have hη₁' : 0 < η₁ := lt_of_lt_of_le (by positivity) (le_trans
    (le_max_right _ _) hη₁)
  have hη₂' : 0 < η₂ := lt_of_lt_of_le (by positivity) (le_trans
    (le_max_right _ _) hη₂)
  have hD : 0 ≤ max 4 (Real.log ((b₁ : ℝ) / η₂ + (b₂ : ℝ) / η₁) / radius) :=
    le_trans (by norm_num) (le_max_left _ _)
  have hr' : 0 < radius := lt_of_lt_of_le (by norm_num) hr
  have hscale :
      1157 * η₁ * η₂ * (max 4
        (Real.log ((b₁ : ℝ) / η₂ + (b₂ : ℝ) / η₁) / radius)) ^ 2 / radius ≤
      4000 * η₁ * η₂ * (max 4
        (Real.log ((b₁ : ℝ) / η₂ + (b₂ : ℝ) / η₁) / radius)) ^ 2 / radius := by
    gcongr
    norm_num
  exact (hdet q₁ q₂ b₁ b₂ radius η₁ η₂ hq₁ hq₂ hi hb₁ hb₂ hr hη₁ hη₂).trans hscale

end

end AbcTwoNinths.ExteriorE1
