/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruiyi Zhang
-/

module

public import AbcTwoNinths.Paper.S3_ExteriorE1.VariableRadiusRealContact
public import AbcTwoNinths.Paper.S3_ExteriorE1.ValuationGcd
public import AbcTwoNinths.Paper.S3_ExteriorE1.CoprimeTwoLogarithmEstimate

/-!
# Coprime Real Contact

The module specializes the real determinant estimate and slab implication to coprime sources. It supports Proposition 3.1 of the paper.

## Main results
* `AbcTwoNinths.ExteriorE1.quantitativeDeterminantOfCoprime`
-/

@[expose] public section


namespace AbcTwoNinths.ExteriorE1

section



/--
The Laurent bound for coprime exponents gives the quantitative real determinant bound. This is used in the proof of Proposition 3.1 of the paper.
-/
theorem quantitativeDeterminantOfCoprime (coprime : _root_.AbcTwoNinths.ExteriorE1.CoprimeLaurent1157) :
    _root_.AbcTwoNinths.ExteriorE1.QuantitativeDeterminantBound :=
  _root_.AbcTwoNinths.ExteriorE1.realVarRadiusLaurent1157 coprime

end

end AbcTwoNinths.ExteriorE1
