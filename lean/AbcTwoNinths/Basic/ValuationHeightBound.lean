/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruiyi Zhang
-/

module

public import Mathlib

/-!
# Valuation Height Bound

The module bounds valuation depth by the logarithmic height of the source.

## Main results
* `AbcTwoNinths.Basic.valHeight`
-/

@[expose] public section


namespace AbcTwoNinths.Basic

section

/--
For a rational number distinct from one with denominator prime to the given prime, the valuation power is bounded by the absolute numerator difference, which is at most twice the multiplicative height.
-/
theorem valHeight {p : ℕ} (hp : p.Prime) {u : ℚ}
    (hu : u ≠ 1) (hunit : ¬ p ∣ u.den) :
    p ^ (padicValRat p (u - 1)).toNat ≤ (u.num - (u.den : ℤ)).natAbs ∧
      (u.num - (u.den : ℤ)).natAbs ≤ 2 * max u.num.natAbs u.den := by
  let : Fact p.Prime := ⟨hp⟩
  have hdq : (u.den : ℚ) ≠ 0 := by exact_mod_cast u.den_nz
  have hdiff : u.num - (u.den : ℤ) ≠ 0 := by
    intro h
    apply hu
    rw [← Rat.num_div_den u]
    exact (div_eq_one_iff_eq hdq).2 (by exact_mod_cast sub_eq_zero.mp h)
  have hden : padicValNat p u.den = 0 := by
    by_contra hn
    have hd := padicValInt_dvd (p := p) (u.den : ℤ)
    have hd' : p ^ padicValNat p u.den ∣ u.den := by
      simpa [padicValInt.of_nat] using Int.natAbs_dvd_natAbs.mpr hd
    obtain ⟨k, hk⟩ : ∃ k, padicValNat p u.den = k + 1 :=
      ⟨padicValNat p u.den - 1, by omega⟩
    have hpPow : p ∣ p ^ padicValNat p u.den := by
      rw [hk, pow_succ, mul_comm]
      exact dvd_mul_right _ _
    exact hunit (hpPow.trans hd')
  have hsub : u - 1 = ((u.num - (u.den : ℤ) : ℤ) : ℚ) / u.den := by
    conv_lhs => rw [← Rat.num_div_den u]
    push_cast
    field_simp
  have hval : padicValRat p (u - 1) = padicValInt p (u.num - (u.den : ℤ)) := by
    rw [hsub, padicValRat.div (by exact_mod_cast hdiff) hdq,
      padicValRat.of_int, padicValRat.of_nat, hden, Nat.cast_zero, sub_zero]
  constructor
  · rw [hval, Int.toNat_natCast]
    have hd := padicValInt_dvd (p := p) (u.num - (u.den : ℤ))
    exact Nat.le_of_dvd (Int.natAbs_pos.mpr hdiff)
      (by simpa using Int.natAbs_dvd_natAbs.mpr hd)
  · have htri := Int.natAbs_add_le u.num (-(u.den : ℤ))
    rw [← sub_eq_add_neg] at htri
    simp only [Int.natAbs_neg, Int.natAbs_natCast] at htri
    omega

end

end AbcTwoNinths.Basic
