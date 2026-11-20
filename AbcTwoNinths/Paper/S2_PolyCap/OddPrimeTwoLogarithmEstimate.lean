/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruiyi Zhang
-/

module

public import AbcTwoNinths.Basic.UnboundedTwoLogarithmEstimate

/-!
# Odd Prime Two Logarithm Estimate

The module applies an unrestricted local two-logarithm estimate to exclude deep contact at the selected odd prime. It supports Proposition 2.1 of the paper.

## Main results
* `AbcTwoNinths.PolyCap.oddPrimeB1Contradiction`
-/

@[expose] public section

namespace AbcTwoNinths.PolyCap

section

open Real

/--
The odd-prime two-logarithm estimate rules out simultaneous depth, coefficient and height-product bounds. This is used in the proof of Proposition 2.1 of the paper.
-/
theorem oddPrimeB1Contradiction
    {p m n : ℕ} {a b : ℚ} {η₁ η₂ H w Y : ℝ}
    (hp : p.Prime) (ho : 2 < p)
    (ha : _root_.AbcTwoNinths.Basic.IsPositivePrincipalUnit p a) (hb : _root_.AbcTwoNinths.Basic.IsPositivePrincipalUnit p b) (hi : _root_.AbcTwoNinths.Basic.RatMulIndependent a b)
    (hm : 0 < m) (hn : 0 < n)
    (h₁ : max (_root_.AbcTwoNinths.Basic.rationalHeight a) (log (p : ℝ)) ≤ η₁)
    (h₂ : max (_root_.AbcTwoNinths.Basic.rationalHeight b) (log (p : ℝ)) ≤ η₂)
    (hH : 0 < H) (hw : 0 < w) (hY : 0 ≤ Y)
    (hdepth : H / (2 * w) ≤
      (padicValRat p (a^m - b^n) : ℝ) * log (p : ℝ))
    (hcoeff : log (p : ℝ) * ((m : ℝ) / η₂ + (n : ℝ) / η₁) ≤ exp Y)
    (hproduct : η₁ * η₂ ≤ H / (20000 * w * (1 + Y)^2)) :
    False := by
  let ell := log (p : ℝ)
  let V : ℝ := padicValRat p (a^m - b^n)
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  have he : (1 : ℝ) / 2 ≤ ell := by
    have hlog : log 2 ≤ ell := log_le_log (by norm_num) hp2
    linarith [log_two_gt_d9]
  have he0 : 0 < ell := by linarith
  have hη₁ : 0 < η₁ := he0.trans_le ((le_max_right _ _).trans h₁)
  have hη₂ : 0 < η₂ := he0.trans_le ((le_max_right _ _).trans h₂)
  let u := exp 2 * log (p : ℝ) * ((m : ℝ) / η₂ + (n : ℝ) / η₁)
  have hu : 0 < u := by
    unfold u
    change 0 < exp 2 * ell * ((m : ℝ) / η₂ + (n : ℝ) / η₁)
    positivity
  have huY : u ≤ exp (2 + Y) := by
    rw [exp_add]
    unfold u
    rw [mul_assoc]
    exact mul_le_mul_of_nonneg_left hcoeff (exp_pos _).le
  have hlog : log u ≤ 2 + Y := by
    simpa only [log_exp] using log_le_log hu huY
  let D := max 4 (log u / ell)
  have hD : D ≤ 4 * (1 + Y) := by
    apply max_le (by linarith)
    apply (div_le_iff₀ he0).2
    have hmul := mul_le_mul_of_nonneg_left he (show 0 ≤ 4 * (1 + Y) by linarith)
    linarith
  have hD0 : 0 ≤ D := le_trans (by norm_num : (0 : ℝ) ≤ 4) (le_max_left _ _)
  have hsq : D^2 ≤ (4 * (1 + Y))^2 := by
    have hsum : 0 ≤ 4 * (1 + Y) + D := by linarith
    nlinarith [mul_nonneg (sub_nonneg.mpr hD) hsum]
  have hB1 : V * ell^2 ≤ 147 * η₁ * η₂ * D^2 :=
    _root_.AbcTwoNinths.Basic.twoLogUnbounded147 p a b m n η₁ η₂ hp ho ha hb hi hm hn h₁ h₂
  have hden : 0 < 20000 * w * (1 + Y)^2 := by positivity
  have hUpper : V * ell^2 ≤ (147 * 16 / 20000 : ℝ) * (H / w) := by
    calc
      _ ≤ 147 * η₁ * η₂ * D^2 := hB1
      _ ≤ 147 * (H / (20000 * w * (1 + Y)^2)) * (4 * (1 + Y))^2 := by
        have hscaled := mul_le_mul_of_nonneg_left hproduct (by norm_num : (0 : ℝ) ≤ 147)
        exact mul_le_mul
          (by
            convert hscaled using 1
            ring)
          hsq (sq_nonneg _) (by positivity)
      _ = _ := by
        field_simp [hw.ne', show 1 + Y ≠ 0 by linarith]
        ring
  have hLower : H / (2 * w) * (1 / 2) ≤ V * ell^2 := by
    calc
      _ ≤ H / (2 * w) * ell := mul_le_mul_of_nonneg_left he (by positivity)
      _ ≤ (V * ell) * ell := mul_le_mul_of_nonneg_right hdepth he0.le
      _ = _ := by ring
  have hratio : 0 < H / w := div_pos hH hw
  have heq : H / (2 * w) * (1 / 2) = (1 / 4 : ℝ) * (H / w) := by ring
  rw [heq] at hLower
  linarith

end

end AbcTwoNinths.PolyCap
