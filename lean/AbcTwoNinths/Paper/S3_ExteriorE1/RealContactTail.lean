/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruiyi Zhang
-/

module

public import AbcTwoNinths.Paper.S3_ExteriorE1.LowRankContact

/-!
# Real Contact Tail

If an ordered high triple fails the real-contact bound with margin κ, its prime support has at
least two elements and the gcd of the quotient exponents is positive and less than `1 / κ` . This
supports Proposition 3.1 of the paper.

## Main results
* `AbcTwoNinths.ExteriorE1.quotientVec`
* `AbcTwoNinths.ExteriorE1.orderedFailureInputs`
-/

@[expose] public section


namespace AbcTwoNinths.ExteriorE1

section




/--
The coordinate at a support prime is its exponent in c minus its exponent in b. This is used in the proof of Proposition 3.1 of the paper.
-/
def quotientVec (t : _root_.AbcTwoNinths.Basic.Triple) (i : _root_.AbcTwoNinths.Basic.supp t) : ℤ :=
  (t.c.factorization i.val : ℤ) - t.b.factorization i.val

/-- The valuation quotient coordinate is the negative of the signed support coefficient. -/
theorem quotientVecEqNegCoeff (t : _root_.AbcTwoNinths.Basic.Triple) (i : _root_.AbcTwoNinths.Basic.supp t) :
    _root_.AbcTwoNinths.ExteriorE1.quotientVec t i = -_root_.AbcTwoNinths.Basic.coeff t i.val := by
  simp only [_root_.AbcTwoNinths.ExteriorE1.quotientVec, _root_.AbcTwoNinths.Basic.coeff]
  ring

/--
The support gcd times an integral vector equals the valuation quotient vector coordinatewise.
-/
theorem quotientFromGcd (t : _root_.AbcTwoNinths.Basic.Triple) :
    ∃ w : _root_.AbcTwoNinths.Basic.supp t → ℤ, ∀ i, _root_.AbcTwoNinths.ExteriorE1.quotientVec t i = (_root_.AbcTwoNinths.ExteriorE1.quotientGcd t : ℤ) * w i := by
  classical
  have hd (i : _root_.AbcTwoNinths.Basic.supp t) : (_root_.AbcTwoNinths.ExteriorE1.quotientGcd t : ℤ) ∣ _root_.AbcTwoNinths.ExteriorE1.quotientVec t i := by
    rw [← Int.natAbs_dvd_natAbs, _root_.AbcTwoNinths.ExteriorE1.quotientVecEqNegCoeff, Int.natAbs_neg]
    exact Finset.gcd_dvd i.property
  choose w hw using hd
  exact ⟨w, hw⟩

/--
For a high ordered triple failing the real estimate, the support has at least two primes and its quotient gcd lies strictly between zero and the reciprocal margin. This is used in the proof of Proposition 3.1 of the paper.
-/
theorem orderedFailureInputs
    (η : ℚ) (hη : _root_.AbcTwoNinths.Statement.admissibleEta η) (κ : ℝ) (hκ : 0 < κ)
    (t : _root_.AbcTwoNinths.Basic.Triple) (hab : t.a ≤ t.b) (hh : _root_.AbcTwoNinths.Statement.High η 0 t) (hf : ¬ _root_.AbcTwoNinths.Statement.RealContactBound κ t) :
    2 ≤ (_root_.AbcTwoNinths.Basic.supp t).card ∧ 0 < _root_.AbcTwoNinths.ExteriorE1.quotientGcd t ∧ (_root_.AbcTwoNinths.ExteriorE1.quotientGcd t : ℝ) < 1 / κ := by
  refine ⟨?_, _root_.AbcTwoNinths.ExteriorE1.quotientGcdPos t, _root_.AbcTwoNinths.ExteriorE1.quotientGcdLtOfNotE1 t κ hκ hf⟩
  by_contra! h
  exact _root_.AbcTwoNinths.ExteriorE1.rankOneClosed η hη t hab (by omega) hh

end

end AbcTwoNinths.ExteriorE1
