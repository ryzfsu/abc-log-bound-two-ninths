/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruiyi Zhang
-/

module

public import AbcTwoNinths.Paper.S5_Selection.SelectedPrime
public import AbcTwoNinths.Paper.S6_Diamond.SignedPrincipalUnitBracket

/-!
# Projected Principal Units

The module lower-bounds the height of projected principal units and handles a vanishing transverse coordinate. It supports Section 6 of the paper.

## Main results
* `AbcTwoNinths.Diamond.principalHeightFloor`
-/

@[expose] public section


namespace AbcTwoNinths.Diamond

section



/--
A rational principal unit different from one has logarithmic height at least the logarithm of half the prime. This is used in Section 6 of the paper.
-/
theorem principalHeightFloor {p : ℕ} [Fact p.Prime] {a : ℚ}
    (ha : _root_.AbcTwoNinths.Basic.Principal p a) (hne : a ≠ 1) :
    Real.log ((p : ℝ) / 2) ≤ _root_.AbcTwoNinths.Basic.rationalHeight a := by
  let k : ℤ := a.num - a.den
  have hd : (a.den : ℚ_[p]) ≠ 0 := by exact_mod_cast a.den_nz
  have heq : (k : ℚ_[p]) = ((a : ℚ_[p]) - 1) * a.den := by
    dsimp [k]
    rw [Int.cast_sub, Int.cast_natCast, Rat.cast_def]
    field_simp
  have hk : k ≠ 0 := by
    intro hz
    have he := heq
    rw [hz, Int.cast_zero] at he
    have hh := (mul_eq_zero.mp he.symm).resolve_right hd
    apply hne
    exact_mod_cast sub_eq_zero.mp hh
  have hv : (p : ℤ) ∣ k := by
    apply Padic.norm_intCast_lt_one_iff.mp
    rw [heq, norm_mul]
    exact (mul_le_of_le_one_right (norm_nonneg _)
      (by simpa using Padic.norm_int_le_one (p := p) (a.den : ℤ))).trans_lt ha
  have hp : p ≤ k.natAbs := Nat.le_of_dvd (Int.natAbs_pos.mpr hk)
    (by simpa using Int.natAbs_dvd_natAbs.mpr hv)
  have hbound : k.natAbs ≤ 2 * max a.num.natAbs a.den := by
    calc
      _ ≤ a.num.natAbs + a.den := by
        dsimp [k]
        simpa [sub_eq_add_neg] using Int.natAbs_add_le a.num (-(a.den : ℤ))
      _ ≤ _ := by omega
  unfold _root_.AbcTwoNinths.Basic.rationalHeight
  have hp0 : (0 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
  apply Real.log_le_log (by positivity)
  have h := hp.trans hbound
  exact (div_le_iff₀ (by norm_num : (0 : ℝ) < 2)).mpr (by exact_mod_cast h.trans_eq (Nat.mul_comm _ _))

end

end AbcTwoNinths.Diamond
