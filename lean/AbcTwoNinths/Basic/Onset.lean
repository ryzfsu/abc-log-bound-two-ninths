/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruiyi Zhang
-/

module

public import AbcTwoNinths.Basic.ScalarClosure

/-!
# Onset

The module chooses a threshold beyond which the numerical inequalities for the polynomial cap hold.

## Main results
* `AbcTwoNinths.Basic.eventualPolynomialCap`
-/

@[expose] public section


namespace AbcTwoNinths.Basic

section

open Real

/--
Beyond the radical-scale threshold, the support estimate and the logarithmic inequality imply Z < 60x.
-/
theorem eventualPolynomialCap {x Z s : ℝ}
    (hx : exp 50 / 3 ≤ x) (hs : 0 ≤ s)
    (hsupp : s ≤ 3 * (3*x) / log (3*x))
    (master : Z - (2*s)*log Z ≤ 9 + 2*log (3*x) + 3*x + s*(24+3*log (3*x))) :
    Z < 60*x := by
  let W := 3*x
  let L := log W
  have hW : exp 50 ≤ W := by dsimp [W]; linarith
  have hWpos : 0 < W := (exp_pos _).trans_le hW
  have hL : 50 ≤ L := (le_log_iff_exp_le hWpos).2 hW
  have hLpos : 0 < L := by linarith
  have hWbig : 25 * L ≤ W := by
    have he := pow_div_factorial_le_exp L hLpos.le 2
    norm_num [Nat.factorial] at he
    rw [show exp L = W from exp_log hWpos] at he
    nlinarith [mul_nonneg hLpos.le (sub_nonneg.mpr hL)]
  have hsup : s * L ≤ 3*W := (le_div_iff₀ hLpos).mp hsupp
  have hsW : 50*s ≤ 3*W := by
    simpa [mul_comm s 50] using (mul_le_mul_of_nonneg_left hL hs).trans hsup
  have hlog20 : log 20 ≤ 5 := by
    have he : (2 : ℝ) < exp 1 := by
      linarith [add_one_lt_exp (show (1:ℝ) ≠ 0 by norm_num)]
    have hpow : (2 : ℝ)^5 ≤ (exp 1)^5 := pow_le_pow_left₀ (by norm_num) he.le _
    rw [← exp_nat_mul] at hpow
    exact (log_le_iff_le_exp (by norm_num : (0:ℝ) < 20)).2 (by norm_num at hpow ⊢; linarith)
  have hlog : log (20*W) ≤ 5 + L := by
    rw [log_mul (by norm_num) hWpos.ne']
    linarith [show log W = L from rfl]
  have hcross : (9+2*L+W+s*(24+3*L)) + (2*s)*log (20*W) < 20*W := by
    have hp := mul_le_mul_of_nonneg_left hlog (show 0 ≤ 2*s by positivity)
    nlinarith
  have hm : 2*s ≤ 20*W := by linarith
  have h := _root_.AbcTwoNinths.Basic.masterLtCrossing (show 0 < 20*W by positivity)
    (show 0 ≤ 2*s by positivity) hm master hcross
  linarith

end

end AbcTwoNinths.Basic
