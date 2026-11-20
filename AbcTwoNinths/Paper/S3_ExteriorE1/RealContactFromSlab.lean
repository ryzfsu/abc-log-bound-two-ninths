/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruiyi Zhang
-/

module

public import AbcTwoNinths.Paper.S3_ExteriorE1.CoprimeRealContact
public import AbcTwoNinths.Paper.S3_ExteriorE1.VariableRadiusLogarithmEstimate

/-!
# Variable-Radius Estimate from Determinants

The quantitative interpolation determinant bound yields the variable-radius estimate for a real
two-logarithm form. This supports Proposition 3.1 of the paper.

## Main results
* `AbcTwoNinths.ExteriorE1.quantitativeDeterminant`
* `AbcTwoNinths.ExteriorE1.variableRadius`
-/

@[expose] public section


namespace AbcTwoNinths.ExteriorE1

section



/-- The coprime two-logarithm estimate yields the quantitative determinant bound for
the selected minor. -/
theorem quantitativeDeterminant : _root_.AbcTwoNinths.ExteriorE1.QuantitativeDeterminantBound :=
  _root_.AbcTwoNinths.ExteriorE1.quantitativeDeterminantOfCoprime _root_.AbcTwoNinths.ExteriorE1.realVarRadiusLaurentCoprime

/-- The quantitative determinant bound gives Laurent's variable-radius estimate in
the formulation with a maximum in each height parameter. -/
theorem laurentProvider : _root_.AbcTwoNinths.ExteriorE1.LaurentProvider :=
  _root_.AbcTwoNinths.ExteriorE1.laurentProviderOf1157 _root_.AbcTwoNinths.ExteriorE1.quantitativeDeterminant

/-- Laurent's variable-radius estimate holds with separate height, logarithm, and radius
hypotheses for each rational base. -/
theorem variableRadius : _root_.AbcTwoNinths.ExteriorE1.variableRadiusRealStatement :=
  _root_.AbcTwoNinths.ExteriorE1.laurentProviderIffVariableRadius.mp _root_.AbcTwoNinths.ExteriorE1.laurentProvider

end

end AbcTwoNinths.ExteriorE1
