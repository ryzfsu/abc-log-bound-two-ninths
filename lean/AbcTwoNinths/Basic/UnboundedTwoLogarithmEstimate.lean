/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruiyi Zhang
-/

module

public import AbcTwoNinths.Basic.PrimitiveGrid
public import AbcTwoNinths.Basic.NormalizedTwoLogarithmEstimate
public import AbcTwoNinths.Basic.UnboundedDepthHeightComparison

/-!
# Unbounded Two Logarithm Estimate

The normalized odd-prime depth bound for positive powers of independent rational principal units
gives the unbounded two-logarithm estimate with constant 147.

## Main results
* `AbcTwoNinths.Basic.unboundedNormalized`
* `AbcTwoNinths.Basic.twoLogUnbounded147`
-/

@[expose] public section

namespace AbcTwoNinths.Basic

section

open Real

/--
Bounds the valuation of a difference of powers at an odd prime using normalized rational heights.
-/
theorem unboundedNormalized (p m n : ℕ) (a b : ℚ) (A B : ℝ)
    (hp : p.Prime) (hp' : 2 < p) (ha : _root_.AbcTwoNinths.Basic.IsPadicPositivePrincipalUnit p a) (hb : _root_.AbcTwoNinths.Basic.IsPadicPositivePrincipalUnit p b)
    (hi : _root_.AbcTwoNinths.Basic.PadicRationalMulIndependent a b) (hm : 0 < m) (hn : 0 < n)
    (hA : 1 ≤ A) (hB : 1 ≤ B)
    (hha : _root_.AbcTwoNinths.Basic.padicRationalHeight a ≤ A*log p) (hhb : _root_.AbcTwoNinths.Basic.padicRationalHeight b ≤ B*log p) :
    (padicValRat p (a^m-b^n) : ℝ) ≤ 147*(_root_.AbcTwoNinths.Basic.unboundedD p m n A B ^ 2*(A*B)) :=
  _root_.AbcTwoNinths.Basic.normalizedFromGrid _root_.AbcTwoNinths.Basic.unboundedPrimitiveGrid p m n a b A B
    hp hp' ha hb hi hm hn hA hB hha hhb

end

section

/-- The unbounded odd-prime two-logarithm estimate holds with constant 147. -/
theorem twoLogUnbounded147 : _root_.AbcTwoNinths.Basic.TwoLogUnbounded 147 :=
  _root_.AbcTwoNinths.Basic.twoLogUnboundedOfNormalized _root_.AbcTwoNinths.Basic.unboundedNormalized

end

end AbcTwoNinths.Basic
