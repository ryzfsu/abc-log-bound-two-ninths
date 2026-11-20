/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruiyi Zhang
-/

module

public import AbcTwoNinths.Paper.S3_ExteriorE1.PlaneContactEndpoint
public import AbcTwoNinths.Paper.S3_ExteriorE1.RealContactFromSlab

/-!
# Closed Real Contact Estimate

For each admissible exponent parameter and each positive margin κ, the bound `log(c/a) ≤ κ log c`
holds for all ordered high triples beyond a common threshold. This is Proposition 3.1 of the paper.

## Main results
* `AbcTwoNinths.ExteriorE1.realContactEventually`
-/

@[expose] public section


namespace AbcTwoNinths.ExteriorE1

section



/-- Proposition 3.1 of the paper. This is used in Section 3 of the paper. -/
theorem realContactEventually (η : ℚ) (hη : _root_.AbcTwoNinths.Statement.admissibleEta η) (κ : ℝ) (hκ : 0 < κ) :
    ∃ X : ℝ, 0 ≤ X ∧ ∀ t : _root_.AbcTwoNinths.Basic.Triple, t.a ≤ t.b → _root_.AbcTwoNinths.Statement.High η X t → _root_.AbcTwoNinths.Statement.RealContactBound κ t :=
  _root_.AbcTwoNinths.ExteriorE1.e1OfVariableRadius _root_.AbcTwoNinths.ExteriorE1.variableRadius η hη κ hκ

end

end AbcTwoNinths.ExteriorE1
