/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruiyi Zhang
-/

module

public import AbcTwoNinths.Paper.S3_ExteriorE1.RealContactTail
public import AbcTwoNinths.Basic.PrimitiveResidueVector

/-!
# Primitive Quotient

The module proves that division by the common exponent factor leaves a primitive quotient. It supports Proposition 3.1 of the paper.

## Main results
* `AbcTwoNinths.ExteriorE1.quotientPrimitive`
-/

@[expose] public section


namespace AbcTwoNinths.ExteriorE1

section




/--
Dividing the quotient exponent vector by its coordinate gcd gives a primitive vector in the full exponent lattice. This is used in the proof of Proposition 3.1 of the paper.
-/
theorem quotientPrimitive (t : _root_.AbcTwoNinths.Basic.Triple) (w : _root_.AbcTwoNinths.Basic.supp t → ℤ)
    (hw : ∀ i, _root_.AbcTwoNinths.ExteriorE1.quotientVec t i = (_root_.AbcTwoNinths.ExteriorE1.quotientGcd t : ℤ) * w i) :
    _root_.AbcTwoNinths.Basic.PrimitiveIn ⊤ w := by
  classical
  intro n u _ hu
  have hd : _root_.AbcTwoNinths.ExteriorE1.quotientGcd t * n ∣ _root_.AbcTwoNinths.ExteriorE1.quotientGcd t := by
    unfold _root_.AbcTwoNinths.ExteriorE1.quotientGcd at ⊢
    apply Finset.dvd_gcd
    intro p hp
    let i : _root_.AbcTwoNinths.Basic.supp t := ⟨p, hp⟩
    have he : w i = (n : ℤ) * u i := by
      rw [← hu]
      simp [Pi.smul_apply]
    have hq := hw i
    rw [_root_.AbcTwoNinths.ExteriorE1.quotientVecEqNegCoeff, he, ← mul_assoc, ← Nat.cast_mul] at hq
    change -_root_.AbcTwoNinths.Basic.coeff t p = _ at hq
    have habs := congrArg Int.natAbs hq
    rw [Int.natAbs_neg, Int.natAbs_mul, Int.natAbs_natCast] at habs
    exact ⟨(u i).natAbs, habs⟩
  have hg := _root_.AbcTwoNinths.ExteriorE1.quotientGcdPos t
  have hn : n ≠ 0 := by
    intro hn
    simp [hn, hg.ne'] at hd
  have hle := Nat.le_of_dvd hg hd
  have hle' : _root_.AbcTwoNinths.ExteriorE1.quotientGcd t * n ≤ _root_.AbcTwoNinths.ExteriorE1.quotientGcd t * 1 := by simpa using hle
  have := Nat.le_of_mul_le_mul_left hle' hg
  omega

end

end AbcTwoNinths.ExteriorE1
