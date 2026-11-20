/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruiyi Zhang
-/

module

public import AbcTwoNinths.Basic.PrimeValuation

/-!
# Local Interpolation Determinant

The module defines congruence of rational numbers in terms of local valuation.

## Main results
* `AbcTwoNinths.Basic.RatCongruent`
-/

@[expose] public section

namespace AbcTwoNinths.Basic

section

/--
Two rationals are congruent to depth `e` at `p` if they are equal or their difference has valuation at least `e`.
-/
def RatCongruent (p e : ℕ) (a b : ℚ) : Prop :=
  a = b ∨ (e : ℤ) ≤ padicValRat p (a - b)

end

end AbcTwoNinths.Basic
