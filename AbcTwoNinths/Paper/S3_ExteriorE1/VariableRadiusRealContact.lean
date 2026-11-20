/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruiyi Zhang
-/

module

public import AbcTwoNinths.Paper.S3_ExteriorE1.DeterminantAssembly
public import AbcTwoNinths.Paper.S3_ExteriorE1.ParametersConsumer
public import AbcTwoNinths.Paper.S3_ExteriorE1.VariableRadiusForm

/-!
# Variable Radius Real Contact

The module relates the variable-radius forms of the real estimate and instantiates them with an explicit bound. It supports Proposition 3.1 of the paper.

## Main results
* `AbcTwoNinths.ExteriorE1.laurentProviderOf1157`
-/

@[expose] public section


namespace AbcTwoNinths.ExteriorE1

section



/--
Laurent's estimate with a maximum in each radius input is equivalent to the separate height, logarithm and radius inequalities.
-/
theorem laurentProviderIffVariableRadius :
    _root_.AbcTwoNinths.ExteriorE1.LaurentProvider ↔ _root_.AbcTwoNinths.ExteriorE1.variableRadiusRealStatement := by
  constructor
  · intro h q₁ q₂ b₁ b₂ r e₁ e₂ hq₁ hq₂ hi hb₁ hb₂ hr hh₁ hh₂ hl₁ hl₂ hr₁ hr₂
    exact h q₁ q₂ b₁ b₂ r e₁ e₂ hq₁ hq₂ hi hb₁ hb₂ hr
      (max_le hh₁ (max_le hl₁ hr₁)) (max_le hh₂ (max_le hl₂ hr₂))
  · intro h q₁ q₂ b₁ b₂ r e₁ e₂ hq₁ hq₂ hi hb₁ hb₂ hr he₁ he₂
    obtain ⟨hh₁, hl₁, hr₁⟩ := max_le_iff.mp he₁ |>.imp_right max_le_iff.mp
    obtain ⟨hh₂, hl₂, hr₂⟩ := max_le_iff.mp he₂ |>.imp_right max_le_iff.mp
    exact h q₁ q₂ b₁ b₂ r e₁ e₂ hq₁ hq₂ hi hb₁ hb₂ hr hh₁ hh₂ hl₁ hl₂ hr₁ hr₂

/--
The determinant estimate yields the Laurent inequality with the variable-radius
height hypotheses for two positive rational bases.
-/
theorem laurentProviderOf1157
    (estimate : _root_.AbcTwoNinths.ExteriorE1.QuantitativeDeterminantBound) : _root_.AbcTwoNinths.ExteriorE1.LaurentProvider :=
  _root_.AbcTwoNinths.ExteriorE1.laurentProviderOfQuantitativeDeterminant estimate

end

end AbcTwoNinths.ExteriorE1
