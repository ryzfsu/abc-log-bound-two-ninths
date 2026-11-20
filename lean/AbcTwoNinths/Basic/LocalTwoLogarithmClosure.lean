/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruiyi Zhang
-/

module

public import AbcTwoNinths.Basic.TripleAndHeight
public import AbcTwoNinths.Basic.TwoLogarithmConstants
public import AbcTwoNinths.Basic.RationalDepthReduction

/-!
# Local Two Logarithm Closure

The exponent-lifting property at an odd prime states that multiplying both exponents by a
positive integer adds that integer's valuation to the valuation of the power difference.

## Main results
* `AbcTwoNinths.Basic.ExponentLTE`
-/

@[expose] public section

namespace AbcTwoNinths.Basic

section




/--
Multiplying both positive exponents by a positive integer increases the valuation of the difference by the valuation of that integer for independent positive principal units at an odd prime.
-/
def ExponentLTE : Prop :=
  ∀ (p c d g : ℕ) (a b : ℚ),
    p.Prime → 2 < p → _root_.AbcTwoNinths.Basic.IsPadicPositivePrincipalUnit p a → _root_.AbcTwoNinths.Basic.IsPadicPositivePrincipalUnit p b → _root_.AbcTwoNinths.Basic.PadicRationalMulIndependent a b →
    0 < c → 0 < d → 0 < g →
    padicValRat p (a^(c*g) - b^(d*g)) =
      padicValRat p (a^c - b^d) + padicValNat p g

end

end AbcTwoNinths.Basic
