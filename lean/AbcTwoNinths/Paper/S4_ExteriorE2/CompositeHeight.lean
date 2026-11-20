/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruiyi Zhang
-/

module

public import Mathlib

/-!
# Composite Height

The module bounds logarithmic height below by the divisibility depth at a composite modulus. It supports Proposition 4.1 of the paper.

## Main results
* `AbcTwoNinths.ExteriorE2.compositeLogOfDepth`
-/

@[expose] public section


namespace AbcTwoNinths.ExteriorE2

section

/--
If a positive base raised to an exponent divides a nonzero integer, the exponent times the logarithm of the base is at most the logarithm of its absolute value. This is used in the proof of Proposition 4.1 of the paper.
-/
theorem compositeLogOfDepth {B E : ℕ} (hB : 0 < B) {z : ℤ} (hz : z ≠ 0)
    (hdepth : (B : ℤ) ^ E ∣ z) :
    (E : ℝ) * Real.log B ≤ Real.log (z.natAbs : ℝ) := by
  have hd : B ^ E ∣ z.natAbs := by
    have h := Int.natAbs_dvd_natAbs.mpr hdepth
    simpa using h
  have hle := Nat.le_of_dvd (Int.natAbs_pos.mpr hz) hd
  have hp : (0 : ℝ) < B := by exact_mod_cast hB
  simpa only [Real.log_pow] using Real.log_le_log (pow_pos hp E)
    (show (B : ℝ) ^ E ≤ z.natAbs by exact_mod_cast hle)

end

end AbcTwoNinths.ExteriorE2
