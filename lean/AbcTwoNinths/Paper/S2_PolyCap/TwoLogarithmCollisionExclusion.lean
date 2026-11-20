/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruiyi Zhang
-/

module

public import AbcTwoNinths.Basic.Coordinates
public import AbcTwoNinths.Paper.S2_PolyCap.OddPrimeTwoLogarithmEstimate

/-!
# Two Logarithm Collision Exclusion

The unit determinant and the height-product bound exclude zero exponent coordinates. The odd-prime
two-logarithm estimate then excludes the claimed valuation depth. This supports Proposition 2.1 of
the paper.

## Main results
* `AbcTwoNinths.PolyCap.oddPrimeB1OfCoordinates`
-/

@[expose] public section


namespace AbcTwoNinths.PolyCap

section

open Real

/--
The coordinate and height inequalities contradict the odd-prime valuation bound for a difference of powers. This is used in the proof of Proposition 2.1 of the paper.
-/
theorem oddPrimeB1OfCoordinates
    {p : ℕ} {a b : ℚ} {c₁ c₂ d₁ d₂ : ℤ} {h₀ h₁ h₂ T H w Y : ℝ}
    (hp : p.Prime) (ho : 2 < p)
    (ha : _root_.AbcTwoNinths.Basic.IsPositivePrincipalUnit p a) (hb : _root_.AbcTwoNinths.Basic.IsPositivePrincipalUnit p b) (hi : _root_.AbcTwoNinths.Basic.RatMulIndependent a b)
    (hd : |c₁ * d₂ - c₂ * d₁| = 1)
    (hh₀ : 0 < h₀) (hf₁ : log (p : ℝ) < h₁) (hf₂ : log (p : ℝ) < h₂)
    (hwidth : 12 * T ≤ log (p : ℝ)) (hprod : h₁ * h₂ < 12 * T * h₀)
    (hline₁ : c₂ = 0 → |c₁| = 1 → h₀ = h₁)
    (hline₂ : c₁ = 0 → |c₂| = 1 → h₀ = h₂)
    (hh₁ : max (_root_.AbcTwoNinths.Basic.rationalHeight a) (log (p : ℝ)) ≤ h₁)
    (hh₂ : max (_root_.AbcTwoNinths.Basic.rationalHeight b) (log (p : ℝ)) ≤ h₂)
    (hH : 0 < H) (hw : 0 < w) (hY : 0 ≤ Y)
    (hdepth : H / (2 * w) ≤
      (padicValRat p (a ^ c₁.natAbs - b ^ c₂.natAbs) : ℝ) * log (p : ℝ))
    (hcoeff : log (p : ℝ) * ((c₁.natAbs : ℝ) / h₂ + (c₂.natAbs : ℝ) / h₁) ≤ exp Y)
    (hproduct : h₁ * h₂ ≤ H / (20000 * w * (1 + Y)^2)) : False := by
  obtain ⟨hc₁, hc₂⟩ := _root_.AbcTwoNinths.Basic.coordinatesNonzero hd hh₀ hf₁ hf₂ hwidth hprod hline₁ hline₂
  exact _root_.AbcTwoNinths.PolyCap.oddPrimeB1Contradiction hp ho ha hb hi
    (Int.natAbs_pos.mpr hc₁) (Int.natAbs_pos.mpr hc₂)
    hh₁ hh₂ hH hw hY hdepth hcoeff hproduct

end

end AbcTwoNinths.PolyCap
