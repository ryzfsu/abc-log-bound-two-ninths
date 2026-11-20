/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruiyi Zhang
-/

module

public import AbcTwoNinths.Paper.S4_ExteriorE2.CompositeQuotient
public import AbcTwoNinths.Paper.S4_ExteriorE2.CompositeClearing

/-!
# Composite Cross Difference

The module obtains a contradiction from a nonzero cross difference that is too small relative to its divisor. It supports Proposition 4.1 of the paper.

## Main results
* `AbcTwoNinths.ExteriorE2.compositeCrossDifference`
-/

@[expose] public section


namespace AbcTwoNinths.ExteriorE2

section

/--
Equality modulo a power of the modulus implies that this power divides the integer cross-difference of the two fractions. This is used in the proof of Proposition 4.1 of the paper.
-/
theorem compositeCrossDifference {B E : ℕ} (a b : _root_.AbcTwoNinths.ExteriorE2.SubringCoprime B)
    (hab : Ideal.Quotient.mk (_root_.AbcTwoNinths.ExteriorE2.compositeIdeal B E) a =
      Ideal.Quotient.mk (_root_.AbcTwoNinths.ExteriorE2.compositeIdeal B E) b) :
    (B : ℤ) ^ E ∣ a.val.num * (b.val.den : ℤ) - b.val.num * (a.val.den : ℤ) := by
  let Z : ℤ := a.val.num * (b.val.den : ℤ) - b.val.num * (a.val.den : ℤ)
  let u : _root_.AbcTwoNinths.ExteriorE2.SubringCoprime B := (a.val.den : _root_.AbcTwoNinths.ExteriorE2.SubringCoprime B) * (b.val.den : _root_.AbcTwoNinths.ExteriorE2.SubringCoprime B)
  have he : (Z : _root_.AbcTwoNinths.ExteriorE2.SubringCoprime B) = u * (a - b) := by
    apply Subtype.ext
    change (Z : ℚ) = (a.val.den : ℚ) * (b.val.den : ℚ) * (a.val - b.val)
    have hA := a.val.num_div_den
    have hB := b.val.num_div_den
    have ha : (a.val.den : ℚ) ≠ 0 := by exact_mod_cast a.val.den_nz
    have hb : (b.val.den : ℚ) ≠ 0 := by exact_mod_cast b.val.den_nz
    have hA' := (div_eq_iff ha).mp hA
    have hB' := (div_eq_iff hb).mp hB
    push_cast [Z]
    linear_combination (b.val.den : ℚ) * hA' - (a.val.den : ℚ) * hB'
  have hd := _root_.AbcTwoNinths.ExteriorE2.compositeDvdOfNum (a - b) ((_root_.AbcTwoNinths.ExteriorE2.compositeQuotientEqIff a b).mp hab)
  have hd' : (B : _root_.AbcTwoNinths.ExteriorE2.SubringCoprime B) ^ E ∣ (Z : _root_.AbcTwoNinths.ExteriorE2.SubringCoprime B) := by
    rw [he, mul_comm]
    exact dvd_mul_of_dvd_left hd _
  have hZ : (B : ℤ) ^ E ∣ Z := by
    simpa using _root_.AbcTwoNinths.ExteriorE2.compositeNumOfDvd (Z : _root_.AbcTwoNinths.ExteriorE2.SubringCoprime B) hd'
  exact hZ

end

end AbcTwoNinths.ExteriorE2
