/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruiyi Zhang
-/

module

public import AbcTwoNinths.Paper.S2_PolyCap.CoprimeMonomialParts

/-!
# Part Powers

The module shows that natural scalar multiplication of an exponent vector takes powers of its monomial parts. It supports Proposition 4.1 of the paper.

## Main results
* `AbcTwoNinths.ExteriorE2.partsNsmul`
-/

@[expose] public section


namespace AbcTwoNinths.ExteriorE2

section



/--
Multiplying an exponent vector by a natural number `g` raises each of its positive and
negative part products to the `g` th power.
-/
theorem partsNsmul {I : Type*} [Fintype I] (q : I → ℕ) (a : I → ℤ) (g : ℕ) :
    _root_.AbcTwoNinths.PolyCap.posPartNat q (g • a) = _root_.AbcTwoNinths.PolyCap.posPartNat q a ^ g ∧
    _root_.AbcTwoNinths.PolyCap.negPartNat q (g • a) = _root_.AbcTwoNinths.PolyCap.negPartNat q a ^ g := by
  have pos (b : I → ℤ) : _root_.AbcTwoNinths.PolyCap.posPartNat q (g • b) = _root_.AbcTwoNinths.PolyCap.posPartNat q b ^ g := by
    unfold _root_.AbcTwoNinths.PolyCap.posPartNat
    rw [← Finset.prod_pow]
    apply Finset.prod_congr rfl
    intro j _
    change q j ^ ((g : ℤ) * b j).toNat = (q j ^ (b j).toNat) ^ g
    by_cases hj : 0 ≤ b j
    · rw [Int.toNat_mul (by positivity) hj, Int.toNat_natCast, Nat.mul_comm, pow_mul]
    · rw [Int.toNat_eq_zero.mpr (mul_nonpos_of_nonneg_of_nonpos (by positivity) (by omega)),
          Int.toNat_eq_zero.mpr (by omega)]
      simp
  refine ⟨pos a, ?_⟩
  simpa only [_root_.AbcTwoNinths.PolyCap.negPartNat, smul_neg] using pos (-a)

end

end AbcTwoNinths.ExteriorE2
