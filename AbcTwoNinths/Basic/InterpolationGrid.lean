/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruiyi Zhang
-/

module

public import AbcTwoNinths.Basic.LocalInterpolationDeterminant

/-!
# Interpolation Grid

The module defines the interpolation grid and the entries evaluated at its nodes.

## Main results
* `AbcTwoNinths.Basic.determinantEntry`
-/

@[expose] public section

namespace AbcTwoNinths.Basic

section

open Finset

/--
The rational interpolation entry at row (k,t) and column (r,s) is a binomial coefficient times the two rational powers.
-/
def determinantEntry (a b : ℚ) (c₁ c₂ : ℕ)
    (kt rs : ℕ × ℕ) : ℚ :=
  (Nat.choose (rs.1*c₂ + rs.2*c₁) kt.1 : ℚ) *
    a^(kt.2*rs.1) * b^(kt.2*rs.2)

end

end AbcTwoNinths.Basic
