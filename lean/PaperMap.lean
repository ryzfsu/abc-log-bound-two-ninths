/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruiyi Zhang
-/
module

public import AbcTwoNinths.Paper.S8_Assembly.MainTheorem
public import AbcTwoNinths.Paper.S2_PolyCap.PolynomialBound
public import AbcTwoNinths.Paper.S3_ExteriorE1.ClosedRealContactEstimate
public import AbcTwoNinths.Paper.S4_ExteriorE2.SmallPrimePowerTail
public import AbcTwoNinths.Paper.S5_Selection.Selected
public import AbcTwoNinths.Paper.S6_Diamond.SelectedPrimeData
public import AbcTwoNinths.Paper.S6_Diamond.FreshPrimePair
public import AbcTwoNinths.Paper.S7_Terminal.IntegralDeterminantBounds
public import AbcTwoNinths.Paper.S7_Terminal.SelectedDiamond
public import AbcTwoNinths.Paper.S7_Terminal.SelectedDiamondExclusion
public import AbcTwoNinths.Paper.S8_Assembly.CommonTail
public import AbcTwoNinths.Paper.S8_Assembly.AssembleExponentBound

/-!
# Numbered results of the paper

The declarations below give paper numbers to the corresponding formal statements.

## Main results
* `AbcTwoNinths.Paper.thm_1_1`
* `AbcTwoNinths.Paper.prop_2_1`
* `AbcTwoNinths.Paper.prop_3_1`
* `AbcTwoNinths.Paper.prop_4_1`
* `AbcTwoNinths.Paper.prop_5_1`
* `AbcTwoNinths.Paper.prop_6_1`
* `AbcTwoNinths.Paper.lemma_6_2`
* `AbcTwoNinths.Paper.prop_7_1`
* `AbcTwoNinths.Paper.lemma_7_2`
* `AbcTwoNinths.Paper.lemma_7_3`
* `AbcTwoNinths.Paper.prop_8_1`
* `AbcTwoNinths.Paper.lemma_8_2`
-/

public section

namespace AbcTwoNinths.Paper

/-- Theorem 1.1 of the paper. -/
alias thm_1_1 := AbcTwoNinths.Assembly.logBound

/-- Proposition 2.1 of the paper. -/
alias prop_2_1 := AbcTwoNinths.PolyCap.polynomialCap

/-- Proposition 3.1 of the paper. -/
alias prop_3_1 := AbcTwoNinths.ExteriorE1.realContactEventually

/-- Proposition 4.1 of the paper. -/
alias prop_4_1 := AbcTwoNinths.ExteriorE2.smallPrimeMassEventually

/-- Proposition 5.1 of the paper. -/
alias prop_5_1 := AbcTwoNinths.Selection.selectedPrimeOfExteriorBounds

/-- Proposition 6.1 of the paper. -/
alias prop_6_1 := AbcTwoNinths.Diamond.selectedDeterminantInputs

/-- Lemma 6.2 of the paper. -/
alias lemma_6_2 := AbcTwoNinths.Diamond.existsFreshPrimePair

/-- Proposition 7.1 of the paper. -/
alias prop_7_1 := AbcTwoNinths.Terminal.terminalBounds

/-- Lemma 7.2 of the paper. -/
alias lemma_7_2 := AbcTwoNinths.Terminal.selectedDiamondProvider

/-- Lemma 7.3 of the paper. -/
alias lemma_7_3 := AbcTwoNinths.Terminal.bandEngineOfSelectedDiamond

/-- Proposition 8.1 of the paper. -/
alias prop_8_1 := AbcTwoNinths.Assembly.commonTailOf

/-- Lemma 8.2 of the paper. -/
alias lemma_8_2 := AbcTwoNinths.Assembly.logBoundOfProviders

end AbcTwoNinths.Paper
