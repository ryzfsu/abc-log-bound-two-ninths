/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruiyi Zhang
-/
module

public import Mathlib

/-!
# The statement of Theorem 1.1

For every positive real `ε`, the theorem bounds `log c` for positive coprime
summands `a + b = c` using the radical of `a * b * c` to the power `2 / 9 + ε`.

## Main definitions
* `AbcTwoNinths.radNat`
* `AbcTwoNinths.TwoNinthsTriple`
* `AbcTwoNinths.twoNinthsStatement`
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

end AbcTwoNinths
