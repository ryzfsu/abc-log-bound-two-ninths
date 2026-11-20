/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruiyi Zhang
-/

module

public import AbcTwoNinths.Paper.S3_ExteriorE1.TwoLogarithmRadius

/-!
# Radius Windows

The module checks the small-radius and high-radius windows against the exponential inequalities used for real contact. It supports Proposition 3.1 of the paper.

## Main results
* `AbcTwoNinths.ExteriorE1.highRadiusWindows`
-/

@[expose] public section


namespace AbcTwoNinths.ExteriorE1

section

-- Reuse the cubic Taylor comparison from RankZeroWindows.
private theorem cubicLeExp {z : ℝ} (hz : 0 ≤ z) :
    z ^ 3 / 6 ≤ Real.exp z := by
  simpa [Nat.factorial] using (Real.pow_div_factorial_le_exp z hz 3)

/-- If `t < exp (-ell / 2)` and `ell ≥ u / 2`, the margin bound implies
`320000 * t * (6 * u) ^ 2 ≤ θ`. -/
theorem tinyRadiusWindow {θ u ell t : ℝ} (hu : 0 < u)
    (hell : u / 2 ≤ ell) (hsmall : 320000 * 13824 ≤ θ * u)
    (ht : t < Real.exp (-ell / 2)) : 320000 * t * (6 * u) ^ 2 ≤ θ := by
  have ht' : t ≤ Real.exp (-(u / 4)) :=
    ht.le.trans (Real.exp_le_exp.mpr (by linarith))
  have hcube : u ^ 3 / 384 ≤ Real.exp (u / 4) := by
    convert cubicLeExp (by positivity : 0 ≤ u / 4) using 1
    ring
  have hpaid : u ^ 3 * Real.exp (-(u / 4)) ≤ 384 := by
    rw [Real.exp_neg, ← div_eq_mul_inv]
    apply (div_le_iff₀ (Real.exp_pos _)).2
    linarith
  have hscaled : (320000 * t * (6 * u) ^ 2) * u ≤ θ * u := by
    calc
      _ ≤ (320000 * Real.exp (-(u / 4)) * (6 * u) ^ 2) * u := by gcongr
      _ = (320000 * 36) * (u ^ 3 * Real.exp (-(u / 4))) := by ring
      _ ≤ 320000 * 13824 := by linarith
      _ ≤ θ * u := hsmall
  have hdiv := (le_div_iff₀ hu).2 hscaled
  rwa [mul_div_cancel_right₀ _ hu.ne'] at hdiv

/-- A sufficiently large radical scale and the bound `t ≤ x / log x` imply the depth
and margin inequalities needed for the two radius cases. -/
theorem highRadiusWindows {δ θ x u t : ℝ}
    (hδ : 0 < δ) (hθ : 0 < θ) (hx : 0 < x)
    (hlogx : Real.exp (320000 * 2048 / (θ * (3 * δ))) ≤ x)
    (hu : 3 * δ * x ≤ u) (hdepth : 48 ≤ 3 * δ * x)
    (hsmall : 320000 * 13824 ≤ θ * (3 * δ * x))
    (ht : t ≤ x / Real.log x) :
    48 ≤ u ∧ 320000 * 13824 ≤ θ * u ∧ 320000 * 2048 * t ≤ θ * u := by
  have hK : 0 < (320000 * 2048 : ℝ) / (θ * (3 * δ)) := by positivity
  have hlog := (Real.le_log_iff_exp_le hx).2 hlogx
  have hlog0 : 0 < Real.log x := hK.trans_le hlog
  have hmain := (div_le_iff₀ (show 0 < θ * (3 * δ) by positivity)).1 hlog
  have hmono := mul_le_mul_of_nonneg_right hmain hx.le
  have hscaled : 320000 * 2048 * (x / Real.log x) ≤ θ * (3 * δ * x) := by
    rw [← mul_div_assoc]
    apply (div_le_iff₀ hlog0).2
    convert hmono using 1
    ring
  have hpay := mul_le_mul_of_nonneg_left hu hθ.le
  exact ⟨hdepth.trans hu, hsmall.trans hpay,
    (mul_le_mul_of_nonneg_left ht (by norm_num)).trans (hscaled.trans hpay)⟩

end

end AbcTwoNinths.ExteriorE1
