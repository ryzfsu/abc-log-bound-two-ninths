/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruiyi Zhang
-/

module

public import AbcTwoNinths.Basic.TripleAndHeight

/-!
# Principal Unit Length Floor

For a nontrivial positive rational principal unit at `p`, the larger reduced component is at
least `p + 1`, and the logarithm of the product of the reduced components exceeds `log p`.

## Main results
* `AbcTwoNinths.Basic.lengthFloor`
-/

@[expose] public section

namespace AbcTwoNinths.Basic

section



/--
For a nontrivial positive principal unit at a prime p, the larger reduced component is at least p + 1 and the logarithm of their product exceeds log p.
-/
theorem lengthFloor : _root_.AbcTwoNinths.Basic.PrincipalUnitLengthBound := by
  intro p y hp hy hne
  let : Fact p.Prime := ⟨hp⟩
  obtain ⟨hypos, _, _, hone⟩ := hy
  have hv := hone.resolve_left hne
  have hnum : 0 < y.num := Rat.num_pos.mpr hypos
  have hden : 0 < y.den := y.den_pos
  have hdenQ : (y.den : ℚ) ≠ 0 := by exact_mod_cast hden.ne'
  have hrepr : (y.num : ℚ) / (y.den : ℚ) = y := Rat.num_div_den y
  have hdiff : y.num - (y.den : ℤ) ≠ 0 := by
    intro he
    apply hne
    rw [← hrepr, sub_eq_zero.mp he]
    simp [hdenQ]
  have hrepr' : y - 1 = ((y.num - (y.den : ℤ) : ℤ) : ℚ) / (y.den : ℚ) := by
    push_cast
    rw [sub_div, div_self hdenQ, hrepr]
  rw [hrepr', padicValRat.div (by exact_mod_cast hdiff) hdenQ,
    padicValRat.of_int, padicValRat.of_nat] at hv
  have hdvd : p ∣ (y.num - (y.den : ℤ)).natAbs := by
    apply padicValNat.dvd_of_ne_zero
    change 0 < (padicValNat p (y.num - (y.den : ℤ)).natAbs : ℤ) -
      (padicValNat p y.den : ℤ) at hv
    omega
  have hle := Nat.le_of_dvd (Int.natAbs_pos.mpr hdiff) hdvd
  have hNumNat : (y.num.natAbs : ℤ) = y.num := Int.natAbs_of_nonneg hnum.le
  have hFloor : p + 1 ≤ max y.num.natAbs y.den := by
    rcases le_total y.num (y.den : ℤ) with h | h
    · have ha := Int.natAbs_of_nonneg (show 0 ≤ - (y.num - (y.den : ℤ)) by omega)
      rw [Int.natAbs_neg] at ha
      exact le_trans (by omega : p + 1 ≤ y.den) (le_max_right _ _)
    · have ha := Int.natAbs_of_nonneg (show 0 ≤ y.num - (y.den : ℤ) by omega)
      exact le_trans (by omega : p + 1 ≤ y.num.natAbs) (le_max_left _ _)
  refine ⟨hFloor, ?_⟩
  apply Real.log_lt_log (by exact_mod_cast hp.pos)
  change (p : ℝ) < ((y.num.natAbs * y.den : ℕ) : ℝ)
  have hsz : max y.num.natAbs y.den ≤ y.num.natAbs * y.den := by
    apply max_le
    · simpa using Nat.mul_le_mul_left y.num.natAbs (show 1 ≤ y.den by omega)
    · simpa using Nat.mul_le_mul_right y.den (show 1 ≤ y.num.natAbs by omega)
  exact_mod_cast (show p < y.num.natAbs * y.den by omega)

end

end AbcTwoNinths.Basic
