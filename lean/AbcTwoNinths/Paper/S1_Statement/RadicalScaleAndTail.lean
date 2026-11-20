/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruiyi Zhang
-/

module

public import AbcTwoNinths.Statement
public import AbcTwoNinths.Paper.S1_Statement.Parameters

/-!
# Radical Scale and Common Tail

The radical scale is one third of the logarithm of the radical. The common tail condition rules out
high triples uniformly above an admissible threshold. This supports Theorem 1.1 of the paper.

## Main results
* `AbcTwoNinths.Statement.radicalScale`
* `AbcTwoNinths.Statement.CommonTailExclusion`
* `AbcTwoNinths.Statement.radicalGeOne`
-/

@[expose] public section

namespace AbcTwoNinths.Statement

section

/--
The radical scale of three integers is one third of the logarithm of the radical of their product. This is used in the proof of Theorem 1.1 of the paper.
-/
noncomputable def radicalScale (a b c : Nat) : ℝ :=
  Real.log (radNat (a * b * c) : ℝ) / 3

/--
For each admissible rational eta, all triples beyond a common radical-scale threshold have height below the exponential cutoff. This is used in the proof of Theorem 1.1 of the paper.
-/
def CommonTailExclusion : Prop :=
  ∀ eta : ℚ, 0 < eta → eta < 1/9 → ∃ onset : ℝ,
    ∀ a b c : Nat, TwoNinthsTriple a b c → onset ≤ _root_.AbcTwoNinths.Statement.radicalScale a b c →
      Real.exp ((1 - 3 * (eta : ℝ)) * _root_.AbcTwoNinths.Statement.radicalScale a b c) ≤ Real.log c → False

/--
The real value of the natural radical is at least one. This is used in the proof of Theorem 1.1 of the paper.
-/
theorem radicalGeOne (n : Nat) : (1 : ℝ) ≤ (radNat n : ℝ) := by
  have h : 0 < radNat n := by
    unfold radNat
    exact Finset.prod_pos fun p hp => (Nat.prime_of_mem_primeFactors hp).pos
  exact_mod_cast h

end

end AbcTwoNinths.Statement
