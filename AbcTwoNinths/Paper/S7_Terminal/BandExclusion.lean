/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruiyi Zhang
-/

module

public import AbcTwoNinths.Paper.S1_Statement.OrderedTriple

/-!
# Band Exclusion

The module defines the band-exclusion condition for large ordered triples. It supports Section 7 of the paper.

## Main results
* `AbcTwoNinths.Terminal.BandEngine`
-/

@[expose] public section

namespace AbcTwoNinths.Terminal

section

/--
At every admissible parameter choice, both exterior estimates exclude ordered high triples beyond a common onset. This is used in Section 7 of the paper.
-/
def BandEngine : Prop :=
  ∀ η : ℚ, _root_.AbcTwoNinths.Statement.admissibleEta η →
    ∀ σ κ : ℝ, _root_.AbcTwoNinths.Statement.admissibleCutoff η σ → _root_.AbcTwoNinths.Statement.admissibleMargin η κ →
      ∃ X : ℝ, ∀ t : _root_.AbcTwoNinths.Basic.Triple, t.a ≤ t.b →
        _root_.AbcTwoNinths.Statement.High η X t → _root_.AbcTwoNinths.Statement.RealContactBound κ t → _root_.AbcTwoNinths.Statement.SmallPrimeMassBound σ κ t → False

end

end AbcTwoNinths.Terminal
