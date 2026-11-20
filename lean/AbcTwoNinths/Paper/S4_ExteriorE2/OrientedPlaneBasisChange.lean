/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruiyi Zhang
-/

module

public import Mathlib

/-!
# Oriented Plane Basis Change

The module constructs the inverse unimodular basis and checks that rounding preserves the determinant. It supports Proposition 4.1 of the paper.

## Main results
* `AbcTwoNinths.ExteriorE2.inverseUnimodularBasis`
* `AbcTwoNinths.ExteriorE2.roundedBasisDet`
-/

@[expose] public section


namespace AbcTwoNinths.ExteriorE2

section

/--
Recover the original pair in an additive commutative group from its two determinant-one integral combinations. This is used in the proof of Proposition 4.1 of the paper.
-/
theorem inverseUnimodularBasis {A : Type*} [AddCommGroup A]
    (v b : A) (p q r s : ℤ) (h : p * s - q * r = 1) :
    let u := p • v + q • b
    let w := r • v + s • b
    v = s • u + (-q) • w ∧ b = (-r) • u + p • w := by
  dsimp only
  have hp : s * p + -q * r = 1 := by linarith only [h]
  have hq : s * q + -q * s = 0 := by ring
  have hr : -r * p + p * r = 0 := by ring
  have hs : -r * q + p * s = 1 := by linarith only [h]
  constructor
  · rw [smul_add, smul_add, smul_smul, smul_smul, smul_smul, smul_smul]
    rw [add_add_add_comm, ← add_smul, ← add_smul, hp, hq, one_smul, zero_smul, add_zero]
  · rw [smul_add, smul_add, smul_smul, smul_smul, smul_smul, smul_smul]
    rw [add_add_add_comm, ← add_smul, ← add_smul, hr, hs, zero_smul, one_smul, zero_add]

/--
Subtracting an integral multiple of the first row from the second preserves determinant one. This is used in the proof of Proposition 4.1 of the paper.
-/
theorem roundedBasisDet (p q r s m : ℤ) (h : p * s - q * r = 1) :
    p * (s - m * q) - q * (r - m * p) = 1 := by
  linear_combination h

end

end AbcTwoNinths.ExteriorE2
