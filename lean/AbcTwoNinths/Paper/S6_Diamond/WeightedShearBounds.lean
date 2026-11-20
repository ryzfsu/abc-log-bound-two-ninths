/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruiyi Zhang
-/

module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Tactic

/-!
# Weighted Shear Bounds

The module bounds the coefficients of a weighted shear and excludes an overly short shear in both coordinate cases. It supports Section 6 of the paper.

## Main results
* `AbcTwoNinths.Diamond.scaledMassExcludeZeroFour`
-/

@[expose] public section


namespace AbcTwoNinths.Diamond

section

/-- The bound on `c * A + d * B` and the mass inequalities give the normalized coefficient
bound `(c / (8 * B) + d / (8 * A)) * ell ≤ 15 * H / x`. -/
theorem scaledMassCoefficient {x ell H V A B c d : ℝ}
    (hx : 0 < x) (hroof : x / 2 ≤ ell) (hV : V ≤ 3 * H)
    (hA : ell ≤ 2 * A) (hB : ell ≤ 2 * B)
    (hc : 0 ≤ c) (hd : 0 ≤ d) (hcoeff : c * A + d * B ≤ 5 * V) :
    (c / (8 * B) + d / (8 * A)) * ell ≤ 15 * H / x := by
  have he : 0 < ell := by linarith
  have ha : 0 < A := by linarith
  have hb : 0 < B := by linarith
  have hAB : 0 < 8 * A * (8 * B) := by positivity
  have hb0 : 0 ≤ c / (8 * B) + d / (8 * A) := by positivity
  have hnum :
      (c / (8 * B) + d / (8 * A)) * (8 * A * (8 * B)) =
        8 * (c * A + d * B) := by
    field_simp [ha.ne', hb.ne']
  have hden : 16 * ell ^ 2 ≤ 8 * A * (8 * B) := by
    nlinarith [mul_le_mul hA hB he.le (by positivity : 0 ≤ 2 * A)]
  have hscaled : (c / (8 * B) + d / (8 * A)) * (16 * ell ^ 2) ≤ 40 * V := by
    calc
      _ ≤ (c / (8 * B) + d / (8 * A)) * (8 * A * (8 * B)) :=
        mul_le_mul_of_nonneg_left hden hb0
      _ = 8 * (c * A + d * B) := hnum
      _ ≤ 40 * V := by linarith
  have hscale : (c / (8 * B) + d / (8 * A)) * ell ≤ (5 / 2 : ℝ) * V / ell := by
    apply (le_div_iff₀ he).mpr
    nlinarith
  have hV0 : 0 ≤ V := by nlinarith [mul_nonneg hc ha.le, mul_nonneg hd hb.le]
  calc
    _ ≤ (5 / 2 : ℝ) * V / ell := hscale
    _ ≤ (5 / 2 : ℝ) * V / (x / 2) :=
      div_le_div_of_nonneg_left (by positivity) (half_pos hx) hroof
    _ = 5 * V / x := by ring
    _ ≤ 15 * H / x := div_le_div_of_nonneg_right (by linarith) hx.le

/-- The contact lower bound and the two-logarithm product upper bound rule out
`τ < 4 * x / Real.log x` at the stated onset. -/
theorem scaledMassExcludeNonzeroFour {x ell H V A B m τ : ℝ}
    (hx : 0 < x) (hH : 0 < H) (hroof : x / 2 ≤ ell)
    (hV : V ≤ 3 * H) (hτ : 0 ≤ τ) (honset : 1000000000 ≤ Real.log x)
    (hshort : τ < 4 * x / Real.log x)
    (hprod : A * B ≤ 12 * V * τ) (hcontact : H / 2 ≤ m * ell)
    (hB1 : m * ell ^ 2 ≤ 9408 * (8 * A) * (8 * B)) : False := by
  have he : 0 < ell := by linarith
  have hl : 0 < Real.log x := by linarith
  have hbound : H * x / 4 ≤ 21676032 * (H * τ) := calc
    _ ≤ (H / 2) * ell := by nlinarith [mul_le_mul_of_nonneg_left hroof (half_pos hH).le]
    _ ≤ m * ell ^ 2 := by nlinarith [mul_le_mul_of_nonneg_right hcontact he.le]
    _ ≤ 9408 * (8 * A) * (8 * B) := hB1
    _ ≤ 21676032 * (H * τ) := by nlinarith [mul_le_mul_of_nonneg_right hV hτ]
  have hupper := mul_lt_mul_of_pos_left ((lt_div_iff₀ hl).mp hshort) hH
  have hlower := mul_le_mul_of_nonneg_right hbound hl.le
  have hon := mul_le_mul_of_nonneg_left honset (mul_pos hH hx).le
  nlinarith

/-- If the selected mass equals one basis-vector mass, the product bound and the onset
inequality rule out `τ < 4 * x / Real.log x`. -/
theorem scaledMassExcludeZeroFour {x ell V A B τ : ℝ}
    (hx : 0 < x) (hV : 0 < V) (hroof : x / 2 ≤ ell)
    (hA : ell ≤ 2 * A) (hB : ell ≤ 2 * B)
    (honset : 1000000000 ≤ Real.log x) (hshort : τ < 4 * x / Real.log x)
    (hprod : A * B ≤ 12 * V * τ) (hsource : V = A ∨ V = B) : False := by
  have hl : 0 < Real.log x := by linarith
  have hbound : ell / 2 ≤ 12 * τ := by
    rcases hsource with rfl | rfl
    · have hb : B ≤ 12 * τ := le_of_mul_le_mul_left (by nlinarith) hV
      linarith
    · have ha : A ≤ 12 * τ := le_of_mul_le_mul_left (by nlinarith) hV
      linarith
  have hmul := mul_le_mul_of_nonneg_right (show x / 4 ≤ 12 * τ by linarith) hl.le
  have hs := (lt_div_iff₀ hl).mp hshort
  have ho := mul_le_mul_of_nonneg_left honset hx.le
  nlinarith

end

end AbcTwoNinths.Diamond
