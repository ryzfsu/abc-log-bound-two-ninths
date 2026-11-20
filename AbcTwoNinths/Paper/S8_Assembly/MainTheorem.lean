/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruiyi Zhang
-/

module

public import AbcTwoNinths.Paper.S7_Terminal.SelectedDiamondExclusion
public import AbcTwoNinths.Paper.S8_Assembly.ExteriorEstimates
public import AbcTwoNinths.Paper.S7_Terminal.SelectedDiamond
public import AbcTwoNinths.Paper.S7_Terminal.DiamondPacket

/-!
# Main Theorem

The polynomial height cap, the exterior estimates, and the determinant contradiction give the
bound with exponent `2/9 + ε`. This is Theorem 1.1 of the paper.

## Main results
* `AbcTwoNinths.Assembly.logBound`
-/

@[expose] public section

namespace AbcTwoNinths.Assembly

open AbcTwoNinths.PolyCap (polynomialCap)
open AbcTwoNinths.ExteriorE2 (smallPrimeMassEventually)
open AbcTwoNinths.Terminal (bandEngineOfSelectedDiamond selectedDiamondProvider)

/-- Theorem 1.1 of the paper. This is used in Section 8 of the paper. -/
theorem logBound : twoNinthsStatement :=
  logBoundOfProviders polynomialCap
    (fixedMarginExteriorOfE2 smallPrimeMassEventually)
    (bandEngineOfSelectedDiamond selectedDiamondProvider)

end AbcTwoNinths.Assembly
