/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruiyi Zhang
-/

module

public import AbcTwoNinths.Basic.TripleAndHeight

/-!
# Scalar Closure

The module turns a scalar crossing inequality into upper and ceiling bounds on the counting parameter.

## Main results
* `AbcTwoNinths.Basic.masterLtCrossing`
* `AbcTwoNinths.Basic.masterBounded`
-/

@[expose] public section


namespace AbcTwoNinths.Basic

section

open Real

/-- A bound on $u-m\log u$ forces $u<x$ if $m\le x$ and the bound is strictly below $x-m\log x$. -/
theorem masterLtCrossing {u x m B : ℝ} (hx : 0 < x) (hm : 0 ≤ m)
    (hmx : m ≤ x) (hmaster : u - m * log u ≤ B)
    (hcross : B + m * log x < x) : u < x := by
  by_contra! hxu
  have hu : 0 < u := lt_of_lt_of_le hx hxu
  have ht : 0 ≤ u / x - 1 := sub_nonneg.mpr ((one_le_div hx).mpr hxu)
  have hlog := Real.log_le_sub_one_of_pos (div_pos hu hx)
  rw [Real.log_div hu.ne' hx.ne'] at hlog
  have ha := mul_le_mul_of_nonneg_left hlog hm
  have hb := mul_le_mul_of_nonneg_right hmx ht
  have hid : x * (u / x - 1) = u - x := by field_simp
  rw [hid] at hb
  linarith

/-- A bound $u-M\log u\le B$ for positive $u,M$ gives $u\le 2B+2M\log(2M)$. -/
theorem masterBounded {u M B : ℝ} (hu : 0 < u) (hM : 0 < M)
    (hmaster : u - M * log u ≤ B) :
    u ≤ 2 * B + 2 * M * log (2 * M) := by
  have hpos : 0 < 2 * M := by positivity
  have hlog := Real.log_le_sub_one_of_pos (div_pos hu hpos)
  rw [Real.log_div hu.ne' hpos.ne'] at hlog
  have ha := mul_le_mul_of_nonneg_left hlog hM.le
  have hid : M * (u / (2 * M) - 1) = u / 2 - M := by field_simp
  rw [hid] at ha
  linarith

end

end AbcTwoNinths.Basic
