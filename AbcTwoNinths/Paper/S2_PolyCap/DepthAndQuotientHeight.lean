/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruiyi Zhang
-/

module

public import AbcTwoNinths.Paper.S2_PolyCap.OddPrimePowerLifting

/-!
# Depth And Quotient Height

The height of a quotient of positive integers is bounded by the logarithm of their maximum. A
positive rational p-adic unit distinct from one has logarithmic height strictly greater than the
valuation depth of its difference from one. This supports Proposition 2.1 of the paper.

## Main results
* `AbcTwoNinths.PolyCap.depthLtHeight`
* `AbcTwoNinths.PolyCap.ratioHeightLe`
-/

@[expose] public section


namespace AbcTwoNinths.PolyCap

section

/--
For a positive rational p-adic unit distinct from one, the valuation of its difference from one times log p is strictly below its logarithmic height.
-/
theorem depthLtHeight {p : ℕ} [Fact p.Prime] {w : ℚ}
    (hw : 0 < w) (hv : padicValRat p w = 0) (hne : w ≠ 1) :
    (padicValRat p (w - 1) : ℝ) * Real.log p < _root_.AbcTwoNinths.Basic.padicRationalHeight w := by
  let d : ℤ := w.num - w.den
  have hdq : (w.den : ℚ) ≠ 0 := by positivity
  have hrew : w - 1 = (d : ℚ) / w.den := by
    push_cast [d]
    calc
      w - 1 = (w.num : ℚ) / w.den - 1 := congrArg (fun v : ℚ => v - 1) w.num_div_den.symm
      _ = _ := by field_simp
  have hd : d ≠ 0 := by
    intro h
    have hz : w - 1 = 0 := by simp [hrew, h]
    exact hne (sub_eq_zero.mp hz)
  rw [hrew, padicValRat.div (by exact_mod_cast hd) hdq,
    _root_.AbcTwoNinths.Basic.denominatorValZero hv, sub_zero, padicValRat.of_int]
  have hnum : 0 < w.num := by
    have h := hw
    rw [← w.num_div_den] at h
    exact_mod_cast (div_pos_iff_of_pos_right (by positivity : (0 : ℚ) < w.den)).mp h
  have hden : (0 : ℤ) < w.den := by positivity
  have hdmax : d.natAbs < max w.num.natAbs w.den := by
    have hz : |d| < max w.num (w.den : ℤ) := by
      rw [abs_lt]
      dsimp [d]
      constructor <;> omega
    have he : (w.num.natAbs : ℤ) = w.num := by rw [Int.natCast_natAbs, abs_of_pos hnum]
    apply (Nat.cast_lt (α := ℤ)).mp
    simpa only [Nat.cast_max, Int.natCast_natAbs, abs_of_pos hnum] using hz
  change ((padicValNat p d.natAbs : ℕ) : ℝ) * Real.log p <
    Real.log (max w.num.natAbs w.den : ℕ)
  have hl := (Nat.le_of_dvd (Int.natAbs_pos.mpr hd)
    (pow_padicValNat_dvd (p := p) (n := d.natAbs))).trans_lt hdmax
  have hp : p.Prime := Fact.out
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hn := Real.log_lt_log (pow_pos hpR (padicValNat p d.natAbs))
    (by exact_mod_cast hl : (p : ℝ) ^ padicValNat p d.natAbs < (max w.num.natAbs w.den : ℕ))
  rwa [Real.log_pow] at hn

/--
The logarithmic height of a quotient of positive natural numbers is at most the sum of their logarithms. This is used in the proof of Proposition 2.1 of the paper.
-/
theorem ratioHeightLe {x y : ℕ} (hx : 0 < x) (hy : 0 < y) :
    _root_.AbcTwoNinths.Basic.padicRationalHeight ((x : ℚ) / y) ≤ Real.log x + Real.log y := by
  let w : ℚ := (x : ℚ) / y
  have he : Rat.divInt (x : ℤ) (y : ℤ) = w := by simp [w, Rat.divInt_eq_div]
  have hnd := Rat.num_dvd (x : ℤ) (by exact_mod_cast hy.ne' : (y : ℤ) ≠ 0)
  have hdd := Rat.den_dvd (x : ℤ) (y : ℤ)
  rw [he] at hnd hdd
  have hn : w.num.natAbs ≤ x := Nat.le_of_dvd hx (by simpa using Int.natAbs_dvd_natAbs.mpr hnd)
  have hd : w.den ≤ y := Nat.le_of_dvd hy (by exact_mod_cast hdd)
  have hmax : max w.num.natAbs w.den ≤ x * y := max_le
    (hn.trans (Nat.le_mul_of_pos_right x hy)) (hd.trans (Nat.le_mul_of_pos_left y hx))
  change Real.log (max w.num.natAbs w.den : ℕ) ≤ _
  rw [← Real.log_mul (by positivity : (x : ℝ) ≠ 0) (by positivity : (y : ℝ) ≠ 0)]
  exact Real.log_le_log (by positivity) (by exact_mod_cast hmax)

end

end AbcTwoNinths.PolyCap
