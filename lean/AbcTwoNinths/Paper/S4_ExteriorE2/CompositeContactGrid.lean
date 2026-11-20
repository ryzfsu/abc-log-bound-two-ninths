/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruiyi Zhang
-/

module

public import AbcTwoNinths.Paper.S4_ExteriorE2.CompositeBezout
public import AbcTwoNinths.Paper.S4_ExteriorE2.CompositeQuotientNewton

/-!
# Composite Contact Grid

The module derives a grid determinant depth bound from the composite quotient contact. It supports Proposition 4.1 of the paper.

## Main results
* `AbcTwoNinths.ExteriorE2.compositeContactGridDepth`
-/

@[expose] public section


namespace AbcTwoNinths.ExteriorE2

section
open scoped BigOperators

/--
For coprime-exponent principal contact data, the modulus to the allowed Newton depth divides the numerator of the grid determinant. This is used in the proof of Proposition 4.1 of the paper.
-/
theorem compositeContactGridDepth {I : Type*} [Fintype I] [DecidableEq I]
    {B c d : ℕ} (hI : 0 < Fintype.card I) (hc : c.Coprime d)
    (a b : (_root_.AbcTwoNinths.ExteriorE2.SubringCoprime B ⧸ _root_.AbcTwoNinths.ExteriorE2.compositeIdeal B (Fintype.card I))ˣ)
    (ha : Units.map (_root_.AbcTwoNinths.ExteriorE2.compositeReduce B (Fintype.card I) hI).toMonoidHom a = 1)
    (hb : Units.map (_root_.AbcTwoNinths.ExteriorE2.compositeReduce B (Fintype.card I) hI).toMonoidHom b = 1)
    (hab : a ^ c = b ^ d)
    (E C : ℕ) (k t r s : I → ℕ) (A : Matrix I I (_root_.AbcTwoNinths.ExteriorE2.SubringCoprime B))
    (hA : ∀ i j, Ideal.Quotient.mk (_root_.AbcTwoNinths.ExteriorE2.compositeIdeal B (Fintype.card I)) (A i j) =
      (Nat.choose (C * (r j * d + s j * c)) (k i) :
        _root_.AbcTwoNinths.ExteriorE2.SubringCoprime B ⧸ _root_.AbcTwoNinths.ExteriorE2.compositeIdeal B (Fintype.card I)) *
        (↑(a ^ r j * b ^ s j)) ^ t i)
    (hE : E + (∑ i, k i) ≤ Fintype.card I * (Fintype.card I - 1) / 2) :
    (B : ℤ) ^ E ∣ ((_root_.AbcTwoNinths.ExteriorE2.SubringCoprime B).subtype.mapMatrix A).det.num := by
  obtain ⟨w, hw, hgrid⟩ := _root_.AbcTwoNinths.ExteriorE2.principalCommonBase
    (G := (_root_.AbcTwoNinths.ExteriorE2.SubringCoprime B ⧸ _root_.AbcTwoNinths.ExteriorE2.compositeIdeal B (Fintype.card I))ˣ)
    (H := (_root_.AbcTwoNinths.ExteriorE2.SubringCoprime B ⧸ _root_.AbcTwoNinths.ExteriorE2.compositeIdeal B 1)ˣ)
    (Units.map (_root_.AbcTwoNinths.ExteriorE2.compositeReduce B (Fintype.card I) hI).toMonoidHom)
    hc (a := a) (b := b) ha hb hab
  obtain ⟨g, hg⟩ := Ideal.Quotient.mk_surjective (I := _root_.AbcTwoNinths.ExteriorE2.compositeIdeal B (Fintype.card I))
    (w : _root_.AbcTwoNinths.ExteriorE2.SubringCoprime B ⧸ _root_.AbcTwoNinths.ExteriorE2.compositeIdeal B (Fintype.card I))
  have hg₁ : Ideal.Quotient.mk (_root_.AbcTwoNinths.ExteriorE2.compositeIdeal B 1) g = 1 := by
    rw [← _root_.AbcTwoNinths.ExteriorE2.compositeReduceMk B (Fintype.card I) hI g, hg]
    exact congrArg Units.val hw
  refine _root_.AbcTwoNinths.ExteriorE2.compositeQuotientNewtonDepth g hg₁ E C k t
    (fun j => r j * d + s j * c) A ?_ hE
  intro i j
  rw [hA, hgrid, map_mul, map_natCast, map_pow, hg, ← Units.val_pow_eq_pow_val,
    ← Units.val_pow_eq_pow_val, ← pow_mul]
  rw [Nat.mul_comm (r j * d + s j * c) (t i)]

end

end AbcTwoNinths.ExteriorE2
