/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruiyi Zhang
-/

module

public import AbcTwoNinths.Paper.S1_Statement.LeastRadicalSide
public import AbcTwoNinths.Paper.S1_Statement.ExponentIntervalSeparation
public import AbcTwoNinths.Paper.S5_Selection.OwnerSelection
public import Mathlib.Tactic

/-!
# Prime selection from the exterior estimates

Selects the unique prime above the small-prime cutoff on the side of least radical and bounds its
logarithmic valuation mass. This is Proposition 5.1 of the paper.

## Main results
* `AbcTwoNinths.Selection.selectedPrimeOfExteriorBounds`
-/

@[expose] public section


namespace AbcTwoNinths.Selection

section



/-- Proposition 5.1 of the paper. This is used in Section 5 of the paper. -/
theorem selectedPrimeOfExteriorBounds {η : ℚ} {σ κ X : ℝ} (t : _root_.AbcTwoNinths.Basic.Triple)
    (hη : _root_.AbcTwoNinths.Statement.admissibleEta η) (hσ : _root_.AbcTwoNinths.Statement.admissibleCutoff η σ)
    (hκ : _root_.AbcTwoNinths.Statement.admissibleMargin η κ) (hX : 0 ≤ X) (hord : t.a ≤ t.b)
    (hH : _root_.AbcTwoNinths.Statement.High η X t) (h1 : _root_.AbcTwoNinths.Statement.RealContactBound κ t) (h2 : _root_.AbcTwoNinths.Statement.SmallPrimeMassBound σ κ t) :
    let u := _root_.AbcTwoNinths.Statement.sideValue t (_root_.AbcTwoNinths.Statement.minRadicalSide t)
    let T := t.logHeight * Real.exp (-σ * t.thirdLogRadical)
    ∃ p ∈ u.primeFactors, T < (p : ℝ) ∧
      (∀ q ∈ u.primeFactors, T < (q : ℝ) → q = p) ∧
      (1 - 2 * κ) * t.logHeight ≤ (padicValNat p u : ℝ) * Real.log p := by
  dsimp only
  have hHp : 0 < t.logHeight := (Real.exp_pos _).trans_le hH.2
  have hηp : 0 < (η : ℝ) := by exact_mod_cast hη.1
  have hκb := hκ.2
  have hmass : 0 < (1 - 2 * κ) * t.logHeight := mul_pos (by linarith) hHp
  exact _root_.AbcTwoNinths.Selection.ownerSelectionOfE1E2 hmass (_root_.AbcTwoNinths.Statement.minSideFull t hord h1) h2
    (mul_pos hHp (Real.exp_pos _))
    (_root_.AbcTwoNinths.Statement.cutoffSquareSeparation hη hσ hX hH) (_root_.AbcTwoNinths.Statement.minSidePair t)

end

end AbcTwoNinths.Selection
