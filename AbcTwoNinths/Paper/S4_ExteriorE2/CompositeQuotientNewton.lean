/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruiyi Zhang
-/

module

public import AbcTwoNinths.Paper.S4_ExteriorE2.CompositeQuotient
public import AbcTwoNinths.Paper.S4_ExteriorE2.CompositeRationalNewton

/-!
# Composite Quotient Newton

The module derives depth of an interpolation determinant through Newton expansion in the composite quotient. It supports Proposition 4.1 of the paper.

## Main results
* `AbcTwoNinths.ExteriorE2.compositeQuotientNewtonDepth`
-/

@[expose] public section


namespace AbcTwoNinths.ExteriorE2

section
open scoped BigOperators

/--
Newton-form entry congruences and the row-degree bound force a power of the modulus to divide the determinant numerator. This is used in the proof of Proposition 4.1 of the paper.
-/
theorem compositeQuotientNewtonDepth {I : Type*} [Fintype I] [DecidableEq I]
    {B : ℕ} (g : _root_.AbcTwoNinths.ExteriorE2.SubringCoprime B)
    (hg : Ideal.Quotient.mk (_root_.AbcTwoNinths.ExteriorE2.compositeIdeal B 1) g = 1)
    (E c : ℕ) (k t z : I → ℕ) (A : Matrix I I (_root_.AbcTwoNinths.ExteriorE2.SubringCoprime B))
    (hA : ∀ i j, Ideal.Quotient.mk (_root_.AbcTwoNinths.ExteriorE2.compositeIdeal B (Fintype.card I)) (A i j) =
      Ideal.Quotient.mk (_root_.AbcTwoNinths.ExteriorE2.compositeIdeal B (Fintype.card I))
        ((Nat.choose (c * z j) (k i) : _root_.AbcTwoNinths.ExteriorE2.SubringCoprime B) * g ^ (t i * z j)))
    (hE : E + (∑ i, k i) ≤ Fintype.card I * (Fintype.card I - 1) / 2) :
    (B : ℤ) ^ E ∣ ((_root_.AbcTwoNinths.ExteriorE2.SubringCoprime B).subtype.mapMatrix A).det.num := by
  have hg' := (_root_.AbcTwoNinths.ExteriorE2.compositeQuotientEqIff (E := 1) g 1).mp (by simpa using hg)
  have hg'' := _root_.AbcTwoNinths.ExteriorE2.compositeDvdOfNum (B := B) (E := 1) (g - 1) hg'
  exact _root_.AbcTwoNinths.ExteriorE2.compositeRationalNewtonDepth g (by simpa using hg'') E c k t z A
    (fun i j => (_root_.AbcTwoNinths.ExteriorE2.compositeQuotientEqIff _ _).mp (hA i j)) hE

end

end AbcTwoNinths.ExteriorE2
