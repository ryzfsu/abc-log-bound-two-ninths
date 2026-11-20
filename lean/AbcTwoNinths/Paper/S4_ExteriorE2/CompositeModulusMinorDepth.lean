/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruiyi Zhang
-/

module

public import AbcTwoNinths.Paper.S4_ExteriorE2.CompositeContactGrid
public import AbcTwoNinths.Basic.RationalBinomialMinor

/-!
# Composite Modulus Minor Depth

The module derives divisibility of the selected rational interpolation minor from quotient contact hypotheses. It supports Proposition 4.1 of the paper.

## Main results
* `AbcTwoNinths.ExteriorE2.compositeActualDepth`
-/

@[expose] public section


namespace AbcTwoNinths.ExteriorE2

section
open scoped BigOperators


/--
Quotient contact and the row-degree budget force the modulus power to divide the numerator of the interpolation determinant. This is used in the proof of Proposition 4.1 of the paper.
-/
theorem compositeActualDepth {I : Type*} [Fintype I] [DecidableEq I]
    {B c d : ℕ} (hI : 0 < Fintype.card I) (hc : c.Coprime d)
    (a b : (_root_.AbcTwoNinths.ExteriorE2.SubringCoprime B)ˣ)
    (ha : Ideal.Quotient.mk (_root_.AbcTwoNinths.ExteriorE2.compositeIdeal B 1) a.val = 1)
    (hb : Ideal.Quotient.mk (_root_.AbcTwoNinths.ExteriorE2.compositeIdeal B 1) b.val = 1)
    (hab : Ideal.Quotient.mk (_root_.AbcTwoNinths.ExteriorE2.compositeIdeal B (Fintype.card I)) (a.val ^ c) =
      Ideal.Quotient.mk (_root_.AbcTwoNinths.ExteriorE2.compositeIdeal B (Fintype.card I)) (b.val ^ d))
    (E : ℕ) (k t r s : I → ℕ)
    (hE : E + (∑ i, k i) ≤ Fintype.card I * (Fintype.card I - 1) / 2) :
    (B : ℤ) ^ E ∣ (_root_.AbcTwoNinths.Basic.actualEntry a.val.val b.val.val k t r s c d).det.num := by
  let f := Ideal.Quotient.mk (_root_.AbcTwoNinths.ExteriorE2.compositeIdeal B (Fintype.card I))
  let A : Matrix I I (_root_.AbcTwoNinths.ExteriorE2.SubringCoprime B) := fun i j =>
    (Nat.choose (r j * d + s j * c) (k i) : _root_.AbcTwoNinths.ExteriorE2.SubringCoprime B) *
      a.val ^ (t i * r j) * b.val ^ (t i * s j)
  have eqA : (_root_.AbcTwoNinths.ExteriorE2.SubringCoprime B).subtype.mapMatrix A =
      _root_.AbcTwoNinths.Basic.actualEntry a.val.val b.val.val k t r s c d := by
    ext i j
    change (_root_.AbcTwoNinths.ExteriorE2.SubringCoprime B).subtype (A i j) = _
    simp [A, _root_.AbcTwoNinths.Basic.actualEntry]
  rw [← eqA]
  refine _root_.AbcTwoNinths.ExteriorE2.compositeContactGridDepth hI hc (Units.map f.toMonoidHom a)
    (Units.map f.toMonoidHom b) ?_ ?_ ?_ E 1 k t r s A ?_ hE
  · apply Units.ext
    exact ha
  · apply Units.ext
    exact hb
  · apply Units.ext
    simpa [f, map_pow] using hab
  · intro i j
    change f (A i j) = _
    simp [A, f, mul_pow, mul_comm, mul_left_comm, ← pow_mul]

end

end AbcTwoNinths.ExteriorE2
