/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruiyi Zhang
-/

module

public import AbcTwoNinths.Paper.S4_ExteriorE2.CutoffResidueImageBound
public import AbcTwoNinths.Paper.S4_ExteriorE2.GridCost
public import AbcTwoNinths.Basic.PrimeValuation
public import AbcTwoNinths.Paper.S4_ExteriorE2.ResidueQuotientRing
public import AbcTwoNinths.Basic.TwoLogarithmHeightBound
public import AbcTwoNinths.Basic.VariableGridMinor
public import AbcTwoNinths.Paper.S4_ExteriorE2.CompositeContactGrid
public import AbcTwoNinths.Basic.RationalDepthReduction
public import AbcTwoNinths.Basic.VariableGridBounds
public import AbcTwoNinths.Basic.TripleAndHeight
public import AbcTwoNinths.Basic.NormalizedTwoLogarithmEstimate
public import AbcTwoNinths.Paper.S4_ExteriorE2.SquaredSource

/-!
# Source Order

The module chooses the source order allowed by the selected modulus. It supports Proposition 4.1 of the paper.

## Main results
* `AbcTwoNinths.ExteriorE2.sourceOrderOfModulus`
-/

@[expose] public section


namespace AbcTwoNinths.ExteriorE2

section



/--
A divisor greater than two on any side of an ordered triple forces the larger addend to be at least two and strictly orders the complementary pair. This is used in the proof of Proposition 4.1 of the paper.
-/
theorem sourceOrderOfModulus (t : _root_.AbcTwoNinths.Basic.Triple) (s : _root_.AbcTwoNinths.Statement.Side) {M : ℕ}
    (hord : t.a ≤ t.b) (hM : 2 < M) (hd : M ∣ _root_.AbcTwoNinths.Statement.sideValue t s) :
    2 ≤ t.b ∧ (_root_.AbcTwoNinths.ExteriorE2.sourcePair t s).2 < (_root_.AbcTwoNinths.ExteriorE2.sourcePair t s).1 := by
  have hc : 0 < t.c := by rw [← t.add]; exact Nat.add_pos_left t.apos _
  have hside : 0 < _root_.AbcTwoNinths.Statement.sideValue t s := by
    cases s
    · exact t.apos
    · exact t.bpos
    · exact hc
  have hle := Nat.le_of_dvd hside hd
  have hbig : 2 < _root_.AbcTwoNinths.Statement.sideValue t s := hM.trans_le hle
  have hsum := t.add
  have ha := t.apos
  have hb := t.bpos
  cases s <;> simp only [_root_.AbcTwoNinths.Statement.sideValue, _root_.AbcTwoNinths.ExteriorE2.sourcePair] at hbig ⊢
  · omega
  · omega
  · have hne : t.a ≠ t.b := by
      intro he
      have hh := t.coprime
      rw [he] at hh
      have hb1 : t.b = 1 := by simpa [Nat.Coprime] using hh
      omega
    omega

end

end AbcTwoNinths.ExteriorE2
