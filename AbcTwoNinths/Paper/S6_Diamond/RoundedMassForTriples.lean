/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruiyi Zhang
-/

module

public import AbcTwoNinths.Paper.S6_Diamond.RoundedOldSupportMass
public import AbcTwoNinths.Basic.TripleAndHeight

/-!
# Projected volume for triples

Specializes the projected volume bound for the original prime support to one third of the
logarithm of the radical. It supports Section 6 of the paper.

## Main results
* `AbcTwoNinths.Diamond.nativeRoundedMass`
-/

@[expose] public section


namespace AbcTwoNinths.Diamond

open Real

section


/--
For a triple beyond the size threshold, the mass floor times the rounded old-support multiplicity is at most one. This is used in Section 6 of the paper.
-/
theorem nativeRoundedMass (t : _root_.AbcTwoNinths.Basic.Triple) (S : Finset ℕ) (roof : ℕ)
    (hS : ∀ q ∈ S, q.Prime) (hprod : ∏ q ∈ S, q ≤ t.radical)
    (hx : exp 15 ≤ t.thirdLogRadical) :
    _root_.AbcTwoNinths.Diamond.massFloor t.thirdLogRadical *
      ((⌊3 * log t.thirdLogRadical⌋₊ + 1 : ℕ) : ℝ)^Fintype.card (_root_.AbcTwoNinths.ExteriorE2.OldIndex S roof) ≤ 1 := by
  apply _root_.AbcTwoNinths.Diamond.roundedMassOldSupport S roof hS hprod hx
  change log (t.radical : ℝ) = 3 * (log (t.radical : ℝ) / 3)
  ring

end

end AbcTwoNinths.Diamond
