/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruiyi Zhang
-/

module

public import AbcTwoNinths.Paper.S4_ExteriorE2.CompositeModulusMinorDepth
public import AbcTwoNinths.Paper.S4_ExteriorE2.CompositeSelectedMinor

/-!
# Composite Modulus Minor Bound

Combines the divisibility and height bounds for the selected interpolation minor at a composite
modulus. It supports Proposition 4.1 of the paper.

## Main results
* `AbcTwoNinths.ExteriorE2.compositeActualBound`
-/

@[expose] public section


namespace AbcTwoNinths.ExteriorE2

section
open scoped BigOperators


/--
A nonzero interpolation minor with composite contact gives an integer satisfying both the logarithmic depth bound and the archimedean size bound. This is used in the proof of Proposition 4.1 of the paper.
-/
theorem compositeActualBound {I : Type*} [Fintype I] [DecidableEq I]
    {B c d E R S la ua lb ub : ℕ} (hB : 0 < B) (hI : 0 < Fintype.card I)
    (hc : c.Coprime d) (a b : (_root_.AbcTwoNinths.ExteriorE2.SubringCoprime B)ˣ)
    (ha : Ideal.Quotient.mk (_root_.AbcTwoNinths.ExteriorE2.compositeIdeal B 1) a.val = 1)
    (hb : Ideal.Quotient.mk (_root_.AbcTwoNinths.ExteriorE2.compositeIdeal B 1) b.val = 1)
    (hab : Ideal.Quotient.mk (_root_.AbcTwoNinths.ExteriorE2.compositeIdeal B (Fintype.card I)) (a.val ^ c) =
      Ideal.Quotient.mk (_root_.AbcTwoNinths.ExteriorE2.compositeIdeal B (Fintype.card I)) (b.val ^ d))
    (k t r s : I → ℕ)
    (hE : E + (∑ i, k i) ≤ Fintype.card I * (Fintype.card I - 1) / 2)
    (hr : ∀ j, r j ≤ R) (hs : ∀ j, s j ≤ S)
    (he : ∀ σ : Equiv.Perm I, la ≤ ∑ j, t (σ j)*r j ∧ (∑ j, t (σ j)*r j) ≤ ua)
    (hf : ∀ σ : Equiv.Perm I, lb ≤ ∑ j, t (σ j)*s j ∧ (∑ j, t (σ j)*s j) ≤ ub)
    (hD0 : (_root_.AbcTwoNinths.Basic.actualEntry a.val.val b.val.val k t r s c d).det ≠ 0) :
    ∃ Z : ℤ, (E : ℝ) * Real.log B ≤ Real.log (Z.natAbs : ℝ) ∧
      (Z.natAbs : ℝ) ≤ (Fintype.card I).factorial *
        (∏ j, ((R*d+S*c : ℕ) : ℝ)^(k j) / ((k j).factorial : ℝ)) *
        Real.exp ((ua-la : ℕ) * Real.log (max (a.val.val.num.natAbs : ℝ) (a.val.val.den : ℝ)) +
          (ub-lb : ℕ) * Real.log (max (b.val.val.num.natAbs : ℝ) (b.val.val.den : ℝ))) := by
  let A : Matrix I I (_root_.AbcTwoNinths.ExteriorE2.SubringCoprime B) := fun i j =>
    (Nat.choose (r j * d + s j * c) (k i) : _root_.AbcTwoNinths.ExteriorE2.SubringCoprime B) *
      a.val ^ (t i * r j) * b.val ^ (t i * s j)
  have eqA : (_root_.AbcTwoNinths.ExteriorE2.SubringCoprime B).subtype.mapMatrix A =
      _root_.AbcTwoNinths.Basic.actualEntry a.val.val b.val.val k t r s c d := by
    ext i j
    change (_root_.AbcTwoNinths.ExteriorE2.SubringCoprime B).subtype (A i j) = _
    simp [A, _root_.AbcTwoNinths.Basic.actualEntry]
  have hD : A.det.val = (_root_.AbcTwoNinths.Basic.actualEntry a.val.val b.val.val k t r s c d).det := by
    change (_root_.AbcTwoNinths.ExteriorE2.SubringCoprime B).subtype A.det = _
    rw [RingHom.map_det, eqA]
  refine _root_.AbcTwoNinths.ExteriorE2.compositeSelectedMinorBound hB a b k t r s c d R S la ua lb ub hr hs
    he hf A.det hD (hD.symm ▸ hD0) ?_
  rw [hD]
  exact _root_.AbcTwoNinths.ExteriorE2.compositeActualDepth hI hc a b ha hb hab E k t r s hE

end

end AbcTwoNinths.ExteriorE2
