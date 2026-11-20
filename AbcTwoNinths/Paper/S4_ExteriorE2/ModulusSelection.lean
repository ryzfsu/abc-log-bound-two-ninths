/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruiyi Zhang
-/

module

public import AbcTwoNinths.Paper.S4_ExteriorE2.SmallPrimeValuationMass
public import AbcTwoNinths.Paper.S4_ExteriorE2.ModulusShareSelection

/-!
# Modulus Selection

The module selects a modulus accounting for excess small-prime valuation mass. It supports Proposition 4.1 of the paper.

## Main results
* `AbcTwoNinths.ExteriorE2.e2ViolationModulus`
-/

@[expose] public section


namespace AbcTwoNinths.ExteriorE2

section




/--
A violation of the small-prime mass estimate yields a divisor of the smooth part with controlled modulus and depth. This is used in the proof of Proposition 4.1 of the paper.
-/
theorem e2ViolationModulus (t : _root_.AbcTwoNinths.Basic.Triple) {σ κ B : ℝ}
    (hB : 0 < B) (hfour : Real.log (4 : ℝ) ≤ B)
    (hcutoff : t.logHeight * Real.exp (-σ * t.thirdLogRadical) ≤ Real.exp B)
    (hlarge : 8 * B ≤ κ * t.logHeight)
    (hrad : ∑ q ∈ (_root_.AbcTwoNinths.Statement.sideValue t (_root_.AbcTwoNinths.Statement.minRadicalSide t)).primeFactors,
      Real.log (q : ℝ) ≤ 2 * B)
    (hbad : ¬ _root_.AbcTwoNinths.Statement.SmallPrimeMassBound σ κ t) :
    let A := _root_.AbcTwoNinths.Statement.sideValue t (_root_.AbcTwoNinths.Statement.minRadicalSide t)
    let cutoff := t.logHeight * Real.exp (-σ * t.thirdLogRadical)
    ∃ M L : ℕ, 2 ≤ M ∧ 0 < L ∧ M ^ L ∣ _root_.AbcTwoNinths.ExteriorE2.smoothPart A cutoff ∧
      M ^ L ∣ A ∧ (¬ 2 ∣ M ∨ 4 ∣ M) ∧
      B / 2 ≤ Real.log (M : ℝ) ∧ Real.log (M : ℝ) ≤ B ∧
      κ * t.logHeight / 16 ≤ (L : ℝ) * Real.log (M : ℝ) := by
  have hc : 0 < t.c := by rw [← t.add]; exact Nat.add_pos_left t.apos _
  have ha (i : _root_.AbcTwoNinths.Statement.Side) : 0 < _root_.AbcTwoNinths.Statement.sideValue t i := by
    cases i
    exact t.apos
    exact t.bpos
    exact hc
  dsimp
  exact _root_.AbcTwoNinths.ExteriorE2.modulusShareSelection (ha _) hB hfour hcutoff hlarge hrad (lt_of_not_ge hbad).le

end

end AbcTwoNinths.ExteriorE2
