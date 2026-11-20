/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruiyi Zhang
-/

module

public import AbcTwoNinths.Basic.TwoLogarithmConstants

/-!
# Rows Depth

The module compares the chosen interpolation row order with the available modulus depth. It supports Proposition 4.1 of the paper.

## Main results
* `AbcTwoNinths.ExteriorE2.rowsOrderLeDepth`
-/

@[expose] public section


namespace AbcTwoNinths.ExteriorE2

section

/--
The small-prime mass and area bounds put the interpolation row count within the remaining depth. This is used in the proof of Proposition 4.1 of the paper.
-/
theorem rowsOrderLeDepth {H x l L κ Q U Z G : ℝ}
    (hH : 0 ≤ H) (hκ : 0 < κ) (hQ : 44236800 / κ ≤ Q)
    (hx : x ≤ 4 * l) (hl : 0 < l) (hUZ0 : 0 ≤ U * Z)
    (hmass : κ * H / 16 ≤ L * l) (hUZ : U * Z ≤ 24 * H * x / Q)
    (hL : 146 + 2 * G ≤ L) :
    (_root_.AbcTwoNinths.Basic.rows (_root_.AbcTwoNinths.Basic.order ((Z / l) * (U / l))) : ℝ) ≤ L - G := by
  have hQκ : 44236800 ≤ Q * κ := (div_le_iff₀ hκ).mp hQ
  have hQ0 : 0 < Q := lt_of_lt_of_le (by positivity) hQ
  have hprod : U * Z * (Q * κ) ≤ 1536 * (L * l ^ 2) := by
    calc
      U * Z * (Q * κ) = U * Z * Q * κ := by ring
      _ ≤ 24 * H * x * κ :=
        mul_le_mul_of_nonneg_right ((le_div_iff₀ hQ0).mp hUZ) hκ.le
      _ ≤ (24 * H * (4 * l)) * κ := by gcongr
      _ = (κ * H / 16) * (1536 * l) := by ring
      _ ≤ (L * l) * (1536 * l) := mul_le_mul_of_nonneg_right hmass (by positivity)
      _ = 1536 * (L * l ^ 2) := by ring
  have harea : 28800 * (U * Z) ≤ L * l ^ 2 := by
    have h := (mul_le_mul_of_nonneg_left hQκ hUZ0).trans hprod
    linarith
  let A := (Z / l) * (U / l)
  have hAeq : A = U * Z / l ^ 2 := by dsimp [A]; ring
  have hA : 0 ≤ A := by rw [hAeq]; positivity
  have hscaled : 28800 * A ≤ L := by
    rw [hAeq, ← mul_div_assoc]
    exact (div_le_iff₀ (by positivity : 0 < l ^ 2)).mpr harea
  have hceil : (_root_.AbcTwoNinths.Basic.order A : ℝ) < 400 * A + 1 :=
    Nat.ceil_lt_add_one (by positivity)
  change (_root_.AbcTwoNinths.Basic.rows (_root_.AbcTwoNinths.Basic.order A) : ℝ) ≤ L - G
  simp only [_root_.AbcTwoNinths.Basic.rows, _root_.AbcTwoNinths.Basic.levels, Nat.cast_mul, Nat.cast_add,
    Nat.cast_one, Nat.cast_ofNat]
  linarith

end

end AbcTwoNinths.ExteriorE2
