/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruiyi Zhang
-/

module

public import AbcTwoNinths.Paper.S3_ExteriorE1.SlabCollision

/-!
# Euclidean Division in Slab Coordinates

For a positive pivot, the normalized Euclidean remainder lies in `[0, 1)` and its negative is the
difference between the integer and real quotients. This supports Proposition 3.1 of the paper.

## Main results
* `AbcTwoNinths.ExteriorE1.residualEdiv`
* `AbcTwoNinths.ExteriorE1.normalizedEmod`
-/

@[expose] public section


namespace AbcTwoNinths.ExteriorE1

section

/--
For a positive divisor, the integer quotient minus the real quotient equals the negative normalized remainder.
-/
theorem residualEdiv (m n : ℤ) (hm : 0 < m) :
    ((n / m : ℤ) : ℝ) - (n : ℝ) / m = -((n % m : ℤ) : ℝ) / m := by
  have hid : ((n / m : ℤ) : ℝ) * (m : ℝ) + ((n % m : ℤ) : ℝ) = (n : ℝ) := by
    exact_mod_cast Int.ediv_mul_add_emod n m
  field_simp [show (m : ℝ) ≠ 0 by exact_mod_cast hm.ne']
  linarith

/--
For a positive divisor, the normalized Euclidean remainder lies in the half-open unit interval. This is used in the proof of Proposition 3.1 of the paper.
-/
theorem normalizedEmod (m n : ℤ) (hm : 0 < m) :
    0 ≤ ((n % m : ℤ) : ℝ) / m ∧ ((n % m : ℤ) : ℝ) / m < 1 := by
  have hmR : 0 < (m : ℝ) := by exact_mod_cast hm
  exact ⟨div_nonneg (by exact_mod_cast Int.emod_nonneg n hm.ne') hmR.le,
    (div_lt_one hmR).mpr (by exact_mod_cast Int.emod_lt_of_pos n hm)⟩

end

end AbcTwoNinths.ExteriorE1
