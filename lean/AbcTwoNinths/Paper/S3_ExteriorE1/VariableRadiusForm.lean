/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruiyi Zhang
-/

module

public import Mathlib

/-!
# Variable Radius Form

The module formulates the variable-radius two-logarithm estimate using rational heights and multiplicative independence. It supports Proposition 3.1 of the paper.

## Main results
* `AbcTwoNinths.ExteriorE1.variableRadiusRealStatement`
-/

@[expose] public section


namespace AbcTwoNinths.ExteriorE1

section

noncomputable section

/--
The logarithm of the maximum of the absolute numerator and positive denominator in lowest terms. This is used in the proof of Proposition 3.1 of the paper.
-/
def rationalLogHeight (q : ℚ) : ℝ :=
  Real.log ((max q.num.natAbs q.den : ℕ) : ℝ)

/--
Every integral multiplicative relation between the two rationals has both exponents zero. This is used in the proof of Proposition 3.1 of the paper.
-/
def ratMulIndependent (q₁ q₂ : ℚ) : Prop :=
  ∀ m n : ℤ, q₁ ^ m * q₂ ^ n = 1 → m = 0 ∧ n = 0

/--
The maximum of four and the logarithm of the cross-normalized coefficient sum divided by the radius. This is used in the proof of Proposition 3.1 of the paper.
-/
def radiusDepth (r e₁ e₂ : ℝ) (b₁ b₂ : ℕ) : ℝ :=
  max 4 (Real.log ((b₁ : ℝ) / e₂ + (b₂ : ℝ) / e₁) / r)

/--
The second coefficient times the logarithm of the second rational minus the corresponding first term. This is used in the proof of Proposition 3.1 of the paper.
-/
def twoLogForm (q₁ q₂ : ℚ) (b₁ b₂ : ℕ) : ℝ :=
  (b₂ : ℝ) * Real.log (q₂ : ℝ) - (b₁ : ℝ) * Real.log (q₁ : ℝ)

/--
The variable-radius upper bound for the negative logarithm of the absolute two-logarithm form at two multiplicatively independent rationals greater than one. This is used in the proof of Proposition 3.1 of the paper.
-/
def variableRadiusRealStatement : Prop :=
  ∀ (q₁ q₂ : ℚ) (b₁ b₂ : ℕ) (r e₁ e₂ : ℝ),
    1 < q₁ → 1 < q₂ → _root_.AbcTwoNinths.ExteriorE1.ratMulIndependent q₁ q₂ →
    0 < b₁ → 0 < b₂ → 1 ≤ r →
    _root_.AbcTwoNinths.ExteriorE1.rationalLogHeight q₁ ≤ e₁ → _root_.AbcTwoNinths.ExteriorE1.rationalLogHeight q₂ ≤ e₂ →
    Real.exp r * |Real.log (q₁ : ℝ)| ≤ e₁ →
    Real.exp r * |Real.log (q₂ : ℝ)| ≤ e₂ →
    r ≤ e₁ → r ≤ e₂ →
    -Real.log |_root_.AbcTwoNinths.ExteriorE1.twoLogForm q₁ q₂ b₁ b₂| ≤
      4000 * e₁ * e₂ * (_root_.AbcTwoNinths.ExteriorE1.radiusDepth r e₁ e₂ b₁ b₂)^2 / r

end

end

end AbcTwoNinths.ExteriorE1
