/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruiyi Zhang
-/

module

public import Mathlib.Analysis.Complex.ExponentialBounds
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Tactic

/-!
# Two Logarithm Radius

The module constructs admissible interpolation parameters from the smallness bound on a two-logarithm form. It supports Proposition 3.1 of the paper.

## Main results
* `AbcTwoNinths.ExteriorE1.realVariableRadiusParametersOfTinyBound`
-/

@[expose] public section


namespace AbcTwoNinths.ExteriorE1

section

/--
The coefficient scale is the maximum of four and the logarithm of the coefficient sum divided by the radius. This is used in the proof of Proposition 3.1 of the paper.
-/
noncomputable def radiusJ (B radius : ℝ) : ℝ := max 4 (Real.log B / radius)

/--
The two window bounds yield a radius at least one that controls both logarithmic heights and the cost in the two-logarithm estimate. This is used in the proof of Proposition 3.1 of the paper.
-/
theorem realVariableRadiusParametersOfTinyBound
    {u θ ell t L₁ L₂ S₁ S₂ B : ℝ}
    (hθ : 0 < θ) (hu : 48 ≤ u)
    (hsmallWindow : t < Real.exp (-ell / 2) → 320000 * t * (6 * u) ^ 2 ≤ θ)
    (hlargeWindow : 320000 * 2048 * t ≤ θ * u)
    (hell : u / 2 ≤ ell) (ht : 0 < t)
    (hL₁ : (1 : ℝ) / 2 ≤ L₁) (hL₂ : (1 : ℝ) / 2 ≤ L₂)
    (hmass : L₁ * L₂ ≤ 5 * Real.exp u * t)
    (hS₁ : S₁ ≤ L₁) (hS₂ : S₂ ≤ L₂)
    (hslab₁ : S₁ ≤ 7 * L₁ * Real.exp (-ell) / t)
    (hslab₂ : S₂ ≤ 7 * L₂ * Real.exp (-ell) / t)
    (hsep₁ : Real.exp (-L₁) ≤ S₁) (hsep₂ : Real.exp (-L₂) ≤ S₂)
    (hB : Real.log B ≤ 2 * u) :
    ∃ radius : ℝ, 1 ≤ radius ∧
      max (max L₁ (Real.exp radius * S₁)) radius ≤ 4 * L₁ ∧
      max (max L₂ (Real.exp radius * S₂)) radius ≤ 4 * L₂ ∧
      4000 * (4 * L₁) * (4 * L₂) * _root_.AbcTwoNinths.ExteriorE1.radiusJ B radius ^ 2 / radius ≤ θ * Real.exp u := by
  have hH : 0 < Real.exp u := Real.exp_pos _
  have finish (radius : ℝ) (hradius : 0 < radius)
      (hw : 320000 * t * _root_.AbcTwoNinths.ExteriorE1.radiusJ B radius ^ 2 ≤ θ * radius) :
      4000 * (4 * L₁) * (4 * L₂) * _root_.AbcTwoNinths.ExteriorE1.radiusJ B radius ^ 2 / radius ≤ θ * Real.exp u := by
    apply (div_le_iff₀ hradius).2
    calc
      _ = 64000 * (L₁ * L₂) * _root_.AbcTwoNinths.ExteriorE1.radiusJ B radius ^ 2 := by ring
      _ ≤ 64000 * (5 * Real.exp u * t) * _root_.AbcTwoNinths.ExteriorE1.radiusJ B radius ^ 2 := by gcongr
      _ = Real.exp u * (320000 * t * _root_.AbcTwoNinths.ExteriorE1.radiusJ B radius ^ 2) := by ring
      _ ≤ Real.exp u * (θ * radius) := mul_le_mul_of_nonneg_left hw hH.le
      _ = _ := by ring
  by_cases hbranch : Real.exp (-ell / 2) ≤ t
  · let radius := ell + Real.log t - Real.log 7
    have hlogt : -ell / 2 ≤ Real.log t := by
      simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos _) hbranch
    have hlog7 : Real.log (7 : ℝ) ≤ 6 := by
      linarith [Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 7)]
    have hradiusu : u / 8 ≤ radius := by dsimp [radius]; linarith
    have hradius : 1 ≤ radius := by linarith
    have hradius0 : 0 < radius := by linarith
    have hpayIdentity : Real.exp radius * (7 * Real.exp (-ell) / t) = 1 := by
      dsimp [radius]
      rw [Real.exp_sub, Real.exp_add, Real.exp_log ht,
        Real.exp_log (by norm_num : (0 : ℝ) < 7), Real.exp_neg]
      field_simp [ne_of_gt (Real.exp_pos ell), ne_of_gt ht]
    have scale (L S : ℝ) (hL : (1 : ℝ) / 2 ≤ L)
        (hslab : S ≤ 7 * L * Real.exp (-ell) / t) (hsep : Real.exp (-L) ≤ S) :
        max (max L (Real.exp radius * S)) radius ≤ 4 * L := by
      have hL0 : 0 < L := by linarith
      have hpay : Real.exp radius * S ≤ L := calc
        _ ≤ Real.exp radius * (7 * L * Real.exp (-ell) / t) :=
          mul_le_mul_of_nonneg_left hslab (Real.exp_pos _).le
        _ = L * (Real.exp radius * (7 * Real.exp (-ell) / t)) := by ring
        _ = L := by rw [hpayIdentity, mul_one]
      have hex : Real.exp (radius - L) ≤ L := by
        rw [sub_eq_add_neg, Real.exp_add]
        exact (mul_le_mul_of_nonneg_left hsep (Real.exp_pos _).le).trans hpay
      have hl : radius - L ≤ Real.log L := by
        simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos _) hex
      have hl' := Real.log_le_sub_one_of_pos hL0
      exact max_le (max_le (by linarith) (by linarith)) (by linarith)
    have hj : _root_.AbcTwoNinths.ExteriorE1.radiusJ B radius ≤ 16 := by
      apply max_le (by norm_num)
      exact (div_le_iff₀ hradius0).2 (by linarith)
    have hj0 : 0 ≤ _root_.AbcTwoNinths.ExteriorE1.radiusJ B radius := (by norm_num : (0 : ℝ) ≤ 4).trans (le_max_left ..)
    refine ⟨radius, hradius, scale L₁ S₁ hL₁ hslab₁ hsep₁, scale L₂ S₂ hL₂ hslab₂ hsep₂,
      finish radius hradius0 ?_⟩
    have hs : _root_.AbcTwoNinths.ExteriorE1.radiusJ B radius ^ 2 ≤ 256 := by nlinarith
    calc
      _ ≤ 320000 * t * 256 := mul_le_mul_of_nonneg_left hs (by positivity)
      _ ≤ θ * (u / 8) := by linarith
      _ ≤ θ * radius := mul_le_mul_of_nonneg_left hradiusu hθ.le
  · have hj : _root_.AbcTwoNinths.ExteriorE1.radiusJ B 1 ≤ 6 * u := by
      unfold _root_.AbcTwoNinths.ExteriorE1.radiusJ
      rw [div_one]
      exact max_le (by linarith) (by linarith)
    have hj0 : 0 ≤ _root_.AbcTwoNinths.ExteriorE1.radiusJ B 1 := (by norm_num : (0 : ℝ) ≤ 4).trans (le_max_left ..)
    have hs : _root_.AbcTwoNinths.ExteriorE1.radiusJ B 1 ^ 2 ≤ (6 * u) ^ 2 := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hj) (show 0 ≤ 6 * u + _root_.AbcTwoNinths.ExteriorE1.radiusJ B 1 by linarith)]
    have scale (L S : ℝ) (hL : (1 : ℝ) / 2 ≤ L) (hS : S ≤ L) :
        max (max L (Real.exp 1 * S)) 1 ≤ 4 * L := by
      have hp := mul_le_mul_of_nonneg_left hS (Real.exp_pos 1).le
      have hq := mul_le_mul_of_nonneg_right Real.exp_one_lt_three.le
        (show 0 ≤ L by linarith)
      exact max_le (max_le (by linarith) (by linarith)) (by linarith)
    refine ⟨1, le_rfl, scale L₁ S₁ hL₁ hS₁, scale L₂ S₂ hL₂ hS₂,
      finish 1 zero_lt_one ?_⟩
    calc
      _ ≤ 320000 * t * (6 * u) ^ 2 := mul_le_mul_of_nonneg_left hs (by positivity)
      _ ≤ θ := hsmallWindow (lt_of_not_ge hbranch)
      _ = θ * 1 := by ring

end

end AbcTwoNinths.ExteriorE1
