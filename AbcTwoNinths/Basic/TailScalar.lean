/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruiyi Zhang
-/

module

public import Mathlib

/-!
# Tail Scalar

The module chooses an onset past which the scalar height gap yields the required positive contact bound.

## Main results
* `AbcTwoNinths.Basic.positiveContactTail`
-/

@[expose] public section


namespace AbcTwoNinths.Basic

section

open Real

/-- The contact gap. -/
noncomputable def contactGap (k : ℝ) : ℝ := 1 / 2 - 2*k

/-- The contact scale. -/
noncomputable def contactScale (k : ℝ) : ℝ := 2 / (contactGap k * log 2)

/-- The contact height onset. -/
noncomputable def contactHeightOnset (k : ℝ) : ℝ :=
  2 * (log 2 + |log (contactScale k)| + 1) / contactGap k

/--
Above the contact height threshold, every index at least two gives a root-depth upper bound strictly below the selected valuation mass bound.
-/
theorem positiveContactTail {k H j : ℝ}
    (hk : k < 1/4) (hj : 2 ≤ j) (hH : _root_.AbcTwoNinths.Basic.contactHeightOnset k ≤ H) :
    H/j + log 2 + log (H/log 2) < (1-2*k)*H := by
  have hd : 0 < contactGap k := by unfold contactGap; linarith
  have hl : 0 < log (2 : ℝ) := log_pos (by norm_num)
  have ha : 0 < contactScale k := by unfold contactScale; positivity
  have hbound : 2 * (log 2 + |log (contactScale k)| + 1) ≤ H * contactGap k := by
    exact (div_le_iff₀ hd).mp hH
  have hp : 0 < H := by
    apply lt_of_lt_of_le _ hH
    unfold _root_.AbcTwoNinths.Basic.contactHeightOnset
    positivity
  have hy : 0 < H / log 2 := div_pos hp hl
  have hlog := log_le_sub_one_of_pos (div_pos hy ha)
  rw [log_div hy.ne' ha.ne'] at hlog
  have heq : H / log 2 / contactScale k = H * contactGap k / 2 := by
    unfold contactScale
    field_simp [hl.ne', hd.ne']
  rw [heq] at hlog
  have hj' : H/j ≤ H/2 :=
    (div_le_div_iff_of_pos_left hp (by linarith) (by norm_num)).mpr hj
  have hid : (1-2*k)*H = H/2 + H * contactGap k := by unfold contactGap; ring
  rw [hid]
  linarith [le_abs_self (log (contactScale k))]

end

end AbcTwoNinths.Basic
