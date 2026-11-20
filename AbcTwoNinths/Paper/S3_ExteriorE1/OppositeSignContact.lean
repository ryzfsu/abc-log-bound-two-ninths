/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruiyi Zhang
-/

module

public import AbcTwoNinths.Paper.S3_ExteriorE1.ParametersConsumer
public import AbcTwoNinths.Paper.S3_ExteriorE1.VariableRadiusForm

/-!
# Opposite Sign Contact

The module excludes the opposite-sign contact case under the stated separation hypotheses. It supports Proposition 3.1 of the paper.

## Main results
* `AbcTwoNinths.ExteriorE1.excludeOpposite`
-/

@[expose] public section


namespace AbcTwoNinths.ExteriorE1

section



/-- Laurent's variable-radius bound rules out a difference of two positive multiples
of logarithms with contact depth greater than `θ * exp u` under the specified height
and slab inequalities. -/
theorem excludeOpposite
    (provider : _root_.AbcTwoNinths.ExteriorE1.variableRadiusRealStatement)
    (q₁ q₂ : ℚ) (b₁ b₂ : ℕ) (L₁ L₂ u θ ell t contact : ℝ)
    (hq₁ : 1 < q₁) (hq₂ : 1 < q₂) (hind : _root_.AbcTwoNinths.ExteriorE1.ratMulIndependent q₁ q₂)
    (hb₁ : 0 < b₁) (hb₂ : 0 < b₂)
    (hform : |_root_.AbcTwoNinths.ExteriorE1.twoLogForm q₁ q₂ b₁ b₂| = contact)
    (hθ : 0 < θ) (hu : 48 ≤ u) (hsmall : 320000 * 13824 ≤ θ * u)
    (hlarge : 320000 * 2048 * t ≤ θ * u)
    (hell : u / 2 ≤ ell) (ht : 0 < t)
    (hL₁ : (1 : ℝ) / 2 ≤ L₁) (hL₂ : (1 : ℝ) / 2 ≤ L₂)
    (hmass : L₁ * L₂ ≤ 5 * Real.exp u * t)
    (hH₁ : _root_.AbcTwoNinths.ExteriorE1.rationalLogHeight q₁ = L₁) (hH₂ : _root_.AbcTwoNinths.ExteriorE1.rationalLogHeight q₂ = L₂)
    (hS₁ : Real.log (q₁ : ℝ) ≤ L₁) (hS₂ : Real.log (q₂ : ℝ) ≤ L₂)
    (hslab₁ : Real.log (q₁ : ℝ) ≤ 7 * L₁ * Real.exp (-ell) / t)
    (hslab₂ : Real.log (q₂ : ℝ) ≤ 7 * L₂ * Real.exp (-ell) / t)
    (hsep₁ : Real.exp (-L₁) ≤ Real.log (q₁ : ℝ))
    (hsep₂ : Real.exp (-L₂) ≤ Real.log (q₂ : ℝ))
    (hc₁ : (b₁ : ℝ) * L₁ ≤ 3 * Real.exp u)
    (hc₂ : (b₂ : ℝ) * L₂ ≤ 3 * Real.exp u)
    (hcontact : θ * Real.exp u < -Real.log contact) : False := by
  let B := (b₁ : ℝ) / (4 * L₂) + (b₂ : ℝ) / (4 * L₁)
  have hL1 : 0 < L₁ := by linarith
  have hL2 : 0 < L₂ := by linarith
  have hBpos : 0 < B := by dsimp [B]; positivity
  have h₁ : (b₁ : ℝ) ≤ 6 * Real.exp u := by
    have h := mul_le_mul_of_nonneg_left hL₁ (show (0 : ℝ) ≤ b₁ by positivity)
    linarith
  have h₂ : (b₂ : ℝ) ≤ 6 * Real.exp u := by
    have h := mul_le_mul_of_nonneg_left hL₂ (show (0 : ℝ) ≤ b₂ by positivity)
    linarith
  have hB : B ≤ 6 * Real.exp u := by
    have h₁' : (b₁ : ℝ) / (4 * L₂) ≤ 3 * Real.exp u := by
      apply (div_le_iff₀ (by positivity)).mpr
      have hm := mul_le_mul_of_nonneg_right hL₂ (Real.exp_pos u).le
      nlinarith only [h₁, hm]
    have h₂' : (b₂ : ℝ) / (4 * L₁) ≤ 3 * Real.exp u := by
      apply (div_le_iff₀ (by positivity)).mpr
      have hm := mul_le_mul_of_nonneg_right hL₁ (Real.exp_pos u).le
      nlinarith only [h₂, hm]
    dsimp [B]
    linarith
  have hlogB : Real.log B ≤ 2 * u := by
    have h := Real.log_le_log hBpos hB
    rw [Real.log_mul (by norm_num) (Real.exp_pos u).ne', Real.log_exp] at h
    linarith [Real.log_le_sub_one_of_pos (show (0 : ℝ) < 6 by norm_num)]
  refine _root_.AbcTwoNinths.ExteriorE1.excludeContactWithRadius hθ hu hsmall hlarge hell ht hL₁ hL₂
    hmass hS₁ hS₂ hslab₁ hslab₂ hsep₁ hsep₂ hlogB ?_ hcontact
  intro r hr h₁ h₂
  have h₁a := max_le_iff.mp h₁
  have h₂a := max_le_iff.mp h₂
  have h₁b := max_le_iff.mp h₁a.1
  have h₂b := max_le_iff.mp h₂a.1
  have hg₁ : 0 ≤ Real.log (q₁ : ℝ) := Real.log_nonneg (by exact_mod_cast hq₁.le)
  have hg₂ : 0 ≤ Real.log (q₂ : ℝ) := Real.log_nonneg (by exact_mod_cast hq₂.le)
  have hh := provider q₁ q₂ b₁ b₂ r (4 * L₁) (4 * L₂)
    hq₁ hq₂ hind hb₁ hb₂ hr (hH₁.trans_le h₁b.1) (hH₂.trans_le h₂b.1)
    (by simpa only [abs_of_nonneg hg₁] using h₁b.2)
    (by simpa only [abs_of_nonneg hg₂] using h₂b.2) h₁a.2 h₂a.2
  rwa [hform] at hh

end

end AbcTwoNinths.ExteriorE1
