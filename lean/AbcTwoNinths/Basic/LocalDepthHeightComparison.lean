/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruiyi Zhang
-/

module

public import AbcTwoNinths.Basic.TwoLogarithmHeightBound

/-!
# Local Depth Height Comparison

The module turns divisibility of a cleared nonzero minor into a lower bound for its logarithmic height.

## Main results
* `AbcTwoNinths.Basic.depthFormula36`
-/

@[expose] public section

namespace AbcTwoNinths.Basic

section

open Real

/--
A lower bound for the prime valuation of a nonzero integer bounds its logarithmic absolute value from below.
-/
theorem integerLogOfDepth (p E : ℕ) (hp : p.Prime) (z : ℤ) (hz : z ≠ 0)
    (hE : (E : ℤ) ≤ padicValRat p (z : ℚ)) :
    (E : ℝ) * log p ≤ log (z.natAbs : ℝ) := by
  rw [padicValRat.of_int] at hE
  have hv : E ≤ padicValNat p z.natAbs := by exact_mod_cast hE
  have hn : 0 < z.natAbs := Int.natAbs_pos.mpr hz
  have hd : p^E ∣ z.natAbs :=
    (pow_dvd_pow p hv).trans pow_padicValNat_dvd
  have hle : p^E ≤ z.natAbs := Nat.le_of_dvd hn hd
  have hp₀ : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hh := log_le_log (pow_pos hp₀ E) (show (p : ℝ)^E ≤ z.natAbs by exact_mod_cast hle)
  simpa only [log_pow] using hh

/--
The triangular exponent deficit for a rectangle with J plus one rows and 36 columns is 630 times the square of J plus one.
-/
theorem depthFormula36 (J : ℕ) :
    ((J+1)*36)*((J+1)*36-1)/2 - 36*((J+1)*J/2) = 630*(J+1)^2 := by
  have hh : 2 * (((J+1)*36)*((J+1)*36-1)/2) =
      ((J+1)*36)*((J+1)*36-1) := by
    have h : (((J+1)*36)*((J+1)*36-1)) % 2 = 0 := by
      rw [Nat.mul_mod]
      have h₀ : ((J+1)*36) % 2 = 0 := by omega
      simp [h₀]
    omega
  have hj : ((J+1)*J) % 2 = 0 := by
    rw [Nat.mul_mod, Nat.add_mod J 1]
    have hJ : J % 2 = 0 ∨ J % 2 = 1 := by omega
    rcases hJ with h | h <;> simp [h]
  have hpoly : ((J+1)*36)*((J+1)*36-1) =
      1260*(J+1)^2+36*((J+1)*J) := by
    have hsub : (J+1)*36-1 = 36*J+35 := by omega
    rw [hsub]
    ring
  omega

end

end AbcTwoNinths.Basic
