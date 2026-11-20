/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruiyi Zhang
-/
module

public import Mathlib

/-!
# An upper bound for log c

Theorem 1.1 concerns positive coprime integers `a` and `b` with `a + b = c`.
The product of the distinct primes dividing `a * b * c` is `radNat (a * b * c)`.
For every positive real `ε`, the estimate uses exponent `2 / 9 + ε`.

## Main results
* `AbcTwoNinths.twoNinths`
-/

@[expose] public section

namespace AbcTwoNinths

/-- The radical of a natural number, the product of its distinct prime factors. -/
def radNat (n : Nat) : Nat :=
  ∏ p ∈ n.primeFactors, p

/-- The positive, coprime triples with `a + b = c` in Theorem 1.1. -/
def TwoNinthsTriple (a b c : Nat) : Prop :=
  0 < a ∧ 0 < b ∧ a + b = c ∧ Nat.Coprime a b

/-- The uniform bound for `log c` in Theorem 1.1, for every positive `ε`. -/
def twoNinthsStatement : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧
    ∀ a b c : Nat, TwoNinthsTriple a b c →
      Real.log c ≤ C * (radNat (a * b * c) : ℝ) ^ ((2 : ℝ) / 9 + ε)

/-- Theorem 1.1 of the paper. -/
theorem twoNinths : twoNinthsStatement := by
  sorry

end AbcTwoNinths
