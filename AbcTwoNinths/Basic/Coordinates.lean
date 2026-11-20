/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruiyi Zhang
-/

module

public import Mathlib

/-!
# Coordinates

The module gives hypotheses that force both coefficients of a primitive exponent pair to be nonzero.

## Main results
* `AbcTwoNinths.Basic.coordinatesNonzero`
-/

@[expose] public section


namespace AbcTwoNinths.Basic

section

/--
The height floor and product bound force both source coordinates in the unimodular basis to be nonzero.
-/
theorem coordinatesNonzero
    {c₁ c₂ d₁ d₂ : ℤ} {h₀ h₁ h₂ T ell : ℝ}
    (hd : |c₁ * d₂ - c₂ * d₁| = 1)
    (hh₀ : 0 < h₀) (hf₁ : ell < h₁) (hf₂ : ell < h₂)
    (hwidth : 12 * T ≤ ell) (hprod : h₁ * h₂ < 12 * T * h₀)
    (hline₁ : c₂ = 0 → |c₁| = 1 → h₀ = h₁)
    (hline₂ : c₁ = 0 → |c₂| = 1 → h₀ = h₂) :
    c₁ ≠ 0 ∧ c₂ ≠ 0 := by
  constructor
  · intro hc
    have hh : |c₂| * |d₁| = 1 := by simpa [hc, abs_mul] using hd
    have hu := Int.mul_eq_one_iff_eq_one_or_neg_one.mp hh
    have hc₂ : |c₂| = 1 := by
      have hnonneg : 0 ≤ |c₂| := abs_nonneg _
      omega
    rw [hline₂ hc hc₂] at hh₀ hprod
    nlinarith [mul_nonneg (show 0 ≤ h₁ - 12 * T by linarith) hh₀.le]
  · intro hc
    have hh : |c₁| * |d₂| = 1 := by simpa [hc, abs_mul] using hd
    have hu := Int.mul_eq_one_iff_eq_one_or_neg_one.mp hh
    have hc₁ : |c₁| = 1 := by
      have hnonneg : 0 ≤ |c₁| := abs_nonneg _
      omega
    rw [hline₁ hc hc₁] at hh₀ hprod
    nlinarith [mul_nonneg (show 0 ≤ h₂ - 12 * T by linarith) hh₀.le]

end

end AbcTwoNinths.Basic
