/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruiyi Zhang
-/

module

public import Mathlib.Algebra.Module.ZLattice.Basic
public import Mathlib.MeasureTheory.Group.GeometryOfNumbers
public import Mathlib.Tactic
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
public import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Variable-Radius Logarithm Hypotheses

The variable-radius two-logarithm problem is expressed using rational logarithmic height,
multiplicative independence, and the estimates required of each rational base. This supports
Proposition 3.1 of the paper.

## Main results
* `AbcTwoNinths.ExteriorE1.rationalHeight`
* `AbcTwoNinths.ExteriorE1.RadiusInputs`
* `AbcTwoNinths.ExteriorE1.LaurentTarget`
* `AbcTwoNinths.ExteriorE1.LaurentProvider`
-/

@[expose] public section


namespace AbcTwoNinths.ExteriorE1

open MeasureTheory

section

/--
The logarithmic height of a rational number is the logarithm of the maximum of its absolute numerator and denominator. This is used in the proof of Proposition 3.1 of the paper.
-/
noncomputable def rationalHeight (q : ℚ) : ℝ :=
  Real.log ((max q.num.natAbs q.den : ℕ) : ℝ)

/--
Two rationals are multiplicatively independent if every integer-power relation between them is trivial. This is used in the proof of Proposition 3.1 of the paper.
-/
def Independent (q₁ q₂ : ℚ) : Prop :=
  ∀ a b : ℤ, q₁ ^ a * q₂ ^ b = 1 → a = 0 ∧ b = 0

/--
The height majorant dominates the rational height, the exponentially weighted logarithm and the radius. This is used in the proof of Proposition 3.1 of the paper.
-/
def RadiusInputs (q : ℚ) (radius η : ℝ) : Prop :=
  max (_root_.AbcTwoNinths.ExteriorE1.rationalHeight q) (max (Real.exp radius * |Real.log (q : ℝ)|) radius) ≤ η

/--
The negative logarithm of the absolute two-logarithm form is bounded by the variable-radius expression with coefficient 4000. This is used in the proof of Proposition 3.1 of the paper.
-/
def LaurentTarget (q₁ q₂ : ℚ) (b₁ b₂ : ℕ) (radius η₁ η₂ : ℝ) : Prop :=
  let B := (b₁ : ℝ) / η₂ + (b₂ : ℝ) / η₁
  let D₀ := max 4 (Real.log B / radius)
  let form := (b₂ : ℝ) * Real.log (q₂ : ℝ) - (b₁ : ℝ) * Real.log (q₁ : ℝ);
  -(Real.log (abs form)) ≤ 4000 * η₁ * η₂ * D₀ ^ 2 / radius

/-- The Laurent bound with coefficient 4000 holds for independent rational bases above one
and positive coefficients under the stated radius hypotheses. -/
def LaurentProvider : Prop :=
  ∀ (q₁ q₂ : ℚ) (b₁ b₂ : ℕ) (radius η₁ η₂ : ℝ),
    1 < q₁ → 1 < q₂ → _root_.AbcTwoNinths.ExteriorE1.Independent q₁ q₂ → 0 < b₁ → 0 < b₂ →
    1 ≤ radius → _root_.AbcTwoNinths.ExteriorE1.RadiusInputs q₁ radius η₁ → _root_.AbcTwoNinths.ExteriorE1.RadiusInputs q₂ radius η₂ →
    _root_.AbcTwoNinths.ExteriorE1.LaurentTarget q₁ q₂ b₁ b₂ radius η₁ η₂

end

end AbcTwoNinths.ExteriorE1
