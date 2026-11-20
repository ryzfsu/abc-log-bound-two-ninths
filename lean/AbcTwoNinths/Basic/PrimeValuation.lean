/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruiyi Zhang
-/

module

public import Mathlib

/-!
# Rational Heights and Principal Units

The rational height is the logarithm of the larger of the absolute numerator and denominator.
The principal-unit condition uses the valuation of the difference from one, and multiplicative
independence rules out nontrivial integer exponent relations.

## Main results
* `AbcTwoNinths.Basic.padicRationalHeight`
* `AbcTwoNinths.Basic.PadicRationalPrincipalUnit`
* `AbcTwoNinths.Basic.PadicRationalMulIndependent`
* `AbcTwoNinths.Basic.IsPadicPositivePrincipalUnit`
-/

@[expose] public section

namespace AbcTwoNinths.Basic

section

noncomputable section

/--
The logarithmic height of a reduced rational is the log of the larger of its absolute numerator and denominator.
-/
def padicRationalHeight (y : ℚ) : ℝ := Real.log (max y.num.natAbs y.den : ℕ)

/--
A nonzero rational is a principal unit at the given prime if its valuation is zero and it equals one or its difference from one has positive valuation.
-/
def PadicRationalPrincipalUnit (p : ℕ) (a : ℚ) : Prop :=
  a ≠ 0 ∧ (padicValRat p a = 0) ∧ (a = 1 ∨ 0 < padicValRat p (a - 1))

/--
Two rationals are multiplicatively independent if only the zero integer exponent pair gives product one.
-/
def PadicRationalMulIndependent (a b : ℚ) : Prop :=
  ∀ m n : ℤ, a ^ m * b ^ n = 1 → m = 0 ∧ n = 0

/--
A positive rational principal unit is a positive rational satisfying the principal-unit condition.
-/
def IsPadicPositivePrincipalUnit (p : ℕ) (y : ℚ) : Prop := 0 < y ∧ _root_.AbcTwoNinths.Basic.PadicRationalPrincipalUnit p y

end
end

end AbcTwoNinths.Basic
