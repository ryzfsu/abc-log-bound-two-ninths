/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruiyi Zhang
-/

module

public import AbcTwoNinths.Basic.ScalarClosure

/-!
# Scalar Bound on a Finite Window

Uniform bounds on the coefficients of `Z - m * log Z ≤ b` give an explicit upper bound for `Z`
when `Z ≥ 1`.

## Main results
* `AbcTwoNinths.Basic.polynomialBoundOnFiniteWindow`
-/

@[expose] public section


namespace AbcTwoNinths.Basic

section

open Real

/--
Bounded coefficients in the logarithmic inequality give an explicit uniform upper bound for Z.
-/
theorem polynomialBoundOnFiniteWindow {Z m b : ℝ}
    (hZ : 1 ≤ Z) (hm : m ≤ 4 * exp 50) (hb : b ≤ 109 + 349 * exp 50)
    (master : Z - m * log Z ≤ b) :
    Z ≤ 2 * (109 + 349 * exp 50) + 2 * (4 * exp 50) * log (2 * (4 * exp 50)) := by
  have hlog : 0 ≤ log Z := log_nonneg hZ
  exact _root_.AbcTwoNinths.Basic.masterBounded (zero_lt_one.trans_le hZ) (by positivity)
    (show Z - (4 * exp 50) * log Z ≤ 109 + 349 * exp 50 from
      (sub_le_sub_left (mul_le_mul_of_nonneg_right hm hlog) Z).trans (master.trans hb))

end

end AbcTwoNinths.Basic
