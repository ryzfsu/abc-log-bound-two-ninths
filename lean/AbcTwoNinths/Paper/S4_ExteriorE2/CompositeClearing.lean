/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruiyi Zhang
-/

module

public import AbcTwoNinths.Paper.S4_ExteriorE2.ResidueQuotientRing
public import AbcTwoNinths.Paper.S4_ExteriorE2.CompositeHeight

/-!
# Composite Clearing

The module bounds the logarithmic cost of clearing denominators from a composite-modulus minor. It supports Proposition 4.1 of the paper.

## Main results
* `AbcTwoNinths.ExteriorE2.compositeClearedLogBound`
-/

@[expose] public section


namespace AbcTwoNinths.ExteriorE2

section

/--
Divisibility of a localized numerator by a modulus power bounds the log height of any nonzero integer obtained by clearing it in the localization. This is used in the proof of Proposition 4.1 of the paper.
-/
theorem compositeClearedLogBound {B E : ℕ} (hB : 0 < B)
    (x u : _root_.AbcTwoNinths.ExteriorE2.SubringCoprime B) {Z : ℤ} (hZ : Z ≠ 0)
    (hclear : (Z : ℚ) = u.val * x.val)
    (hdepth : (B : ℤ) ^ E ∣ x.val.num) :
    (E : ℝ) * Real.log B ≤ Real.log (Z.natAbs : ℝ) := by
  have he : (Z : _root_.AbcTwoNinths.ExteriorE2.SubringCoprime B) = u * x := by
    apply Subtype.ext
    exact hclear
  have hd := _root_.AbcTwoNinths.ExteriorE2.compositeDvdOfNum x hdepth
  have hd' : (B : _root_.AbcTwoNinths.ExteriorE2.SubringCoprime B) ^ E ∣ (Z : _root_.AbcTwoNinths.ExteriorE2.SubringCoprime B) := by
    rw [he, mul_comm]
    exact dvd_mul_of_dvd_left hd _
  apply _root_.AbcTwoNinths.ExteriorE2.compositeLogOfDepth hB hZ
  simpa using _root_.AbcTwoNinths.ExteriorE2.compositeNumOfDvd (Z : _root_.AbcTwoNinths.ExteriorE2.SubringCoprime B) hd'

end

end AbcTwoNinths.ExteriorE2
