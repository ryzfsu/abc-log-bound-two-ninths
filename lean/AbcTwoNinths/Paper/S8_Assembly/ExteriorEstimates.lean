/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruiyi Zhang
-/

module

public import AbcTwoNinths.Paper.S8_Assembly.AssembleExponentBound
public import AbcTwoNinths.Paper.S7_Terminal.BandExclusion
public import AbcTwoNinths.Paper.S5_Selection.Selected
public import AbcTwoNinths.Paper.S3_ExteriorE1.ClosedRealContactEstimate
public import AbcTwoNinths.Paper.S4_ExteriorE2.SmallPrimeValuationMass
public import AbcTwoNinths.Paper.S2_PolyCap.PolynomialBound
public import AbcTwoNinths.Paper.S4_ExteriorE2.SmallPrimePowerTail

/-!
# Exterior Estimates

The module combines the real-contact and small-prime-power estimates at a common margin. It supports Section 8 of the paper.

## Main results
* `AbcTwoNinths.Assembly.fixedMarginExteriorOfE2`
-/

@[expose] public section


namespace AbcTwoNinths.Assembly

section



/-- An eventual bound on small-prime mass and the real-contact estimate give both exterior
bounds for ordered high triples with the same margin and a common threshold. -/
theorem fixedMarginExteriorOfE2
    (tails : ∀ η : ℚ, _root_.AbcTwoNinths.Statement.admissibleEta η →
      ∃ σ κ X : ℝ, _root_.AbcTwoNinths.Statement.admissibleCutoff η σ ∧ _root_.AbcTwoNinths.Statement.admissibleMargin η κ ∧
        0 ≤ X ∧
        (∀ t : _root_.AbcTwoNinths.Basic.Triple, t.a ≤ t.b → _root_.AbcTwoNinths.Statement.High η X t → _root_.AbcTwoNinths.Statement.SmallPrimeMassBound σ κ t)) :
    _root_.AbcTwoNinths.Statement.FixedMarginExterior := by
  apply _root_.AbcTwoNinths.ExteriorE2.fixedMarginExteriorOfSplitTails
  intro η hη
  obtain ⟨σ, κ, X₂, hσ, hκ, hX₂, h₂⟩ := tails η hη
  obtain ⟨X₁, hX₁, h₁⟩ := _root_.AbcTwoNinths.ExteriorE1.realContactEventually η hη κ hκ.1
  exact ⟨σ, κ, X₁, X₂, hσ, hκ, hX₁, hX₂, h₁, h₂⟩

end

end AbcTwoNinths.Assembly
