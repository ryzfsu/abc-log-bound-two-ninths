/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruiyi Zhang
-/

module

public import AbcTwoNinths.Basic.TripleAndHeight
public import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Collision Threshold Inequalities

The basis height floors, coordinate bounds, and height-product bound supply the numerical
hypotheses of the odd-prime two-logarithm estimate. This supports Proposition 2.1 of the paper.

## Main results
* `AbcTwoNinths.PolyCap.numericPremisesForContradiction`
-/

@[expose] public section


namespace AbcTwoNinths.PolyCap

section

open Real

/--
The height floors and weighted coefficient bounds give the six numerical inequalities used to exclude a collision. This is used in the proof of Proposition 2.1 of the paper.
-/
theorem numericPremisesForContradiction {p r : ℕ} {c₁ c₂ : ℤ} {H h₀ h₁ h₂ : ℝ}
    (ho : 2 < p) (hr : 1 ≤ r) (hH : 2 < H)
    (hh₀_pos : 0 < h₀) (hh₀ : h₀ ≤ 4 * H)
    (hf₁ : log (p : ℝ) < h₁) (hf₂ : log (p : ℝ) < h₂)
    (hc₁ : |(c₁ : ℝ)| * h₁ ≤ 3 * h₀) (hc₂ : |(c₂ : ℝ)| * h₂ ≤ 2 * h₀)
    (hprod : h₁ * h₂ < 12 * (1 / (1920000 * (r : ℝ) * (1 + log (20 * H)) ^ 2)) * h₀) :
    let w : ℝ := 2 * (r : ℝ)
    let Y : ℝ := log (20 * H)
    let T : ℝ := 1 / (1920000 * (r : ℝ) * (1 + Y) ^ 2)
    0 < H ∧ 0 < w ∧ 0 ≤ Y ∧ 12 * T ≤ log (p : ℝ) ∧
    log (p : ℝ) * ((c₁.natAbs : ℝ) / h₂ + (c₂.natAbs : ℝ) / h₁) ≤ exp Y ∧
    h₁ * h₂ ≤ H / (20000 * w * (1 + Y) ^ 2) := by
  let Y := log (20 * H)
  let D : ℝ := 1920000 * (r : ℝ) * (1 + Y) ^ 2
  have hr' : (1 : ℝ) ≤ r := by exact_mod_cast hr
  have hrpos : (0 : ℝ) < r := by linarith
  have hY : 0 ≤ Y := log_nonneg (by linarith)
  have hYsq : 1 ≤ (1 + Y) ^ 2 := by nlinarith
  have hD : 1920000 ≤ D := by
    calc
      1920000 = 1920000 * (1 * 1) := by norm_num
      _ ≤ 1920000 * ((r : ℝ) * (1 + Y) ^ 2) := by gcongr
      _ = D := by unfold D; ring
  have hDpos : 0 < D := by linarith
  have hp3 : (3 : ℝ) ≤ p := by
    exact_mod_cast (show 3 ≤ p by omega)
  have hlp : 1 < log (p : ℝ) :=
    (lt_log_iff_exp_lt (by linarith)).2 (by linarith [exp_one_lt_d9])
  have h₁pos : 0 < h₁ := by linarith
  have h₂pos : 0 < h₂ := by linarith
  have hxy : log (p : ℝ) ≤ h₁ * h₂ := by
    calc
      log (p : ℝ) ≤ h₁ := hf₁.le
      _ = h₁ * 1 := by ring
      _ ≤ h₁ * h₂ := by gcongr; linarith
  change 0 < H ∧ 0 < 2 * (r : ℝ) ∧ 0 ≤ Y ∧ 12 * (1 / D) ≤ log (p : ℝ) ∧
    _ ∧ _
  refine ⟨by linarith only [hh₀_pos, hh₀], by positivity, hY, ?_, ?_, ?_⟩
  · rw [mul_one_div]
    exact ((div_le_iff₀ hDpos).2 (by linarith) : (12 : ℝ) / D ≤ 1).trans hlp.le
  · have castAbs (c : ℤ) : (c.natAbs : ℝ) = |(c : ℝ)| := by
      rw [← Int.cast_abs, ← Int.natCast_natAbs, Int.cast_natCast]
    rw [castAbs, castAbs]
    calc
      _ = log (p : ℝ) / (h₁ * h₂) * (|(c₁ : ℝ)| * h₁ + |(c₂ : ℝ)| * h₂) := by
        field_simp
      _ ≤ 1 * (5 * h₀) := by
        apply mul_le_mul
        · exact (div_le_one (mul_pos h₁pos h₂pos)).2 hxy
        · linarith
        · positivity
        · norm_num
      _ ≤ exp Y := by
        rw [show exp Y = 20 * H from exp_log (by linarith)]
        linarith
  · change h₁ * h₂ ≤ H / (20000 * (2 * (r : ℝ)) * (1 + Y) ^ 2)
    calc
      _ ≤ 12 * (1 / D) * h₀ := hprod.le
      _ ≤ 12 * (1 / D) * (4 * H) := by gcongr
      _ = _ := by
        unfold D
        field_simp
        ring

end

end AbcTwoNinths.PolyCap
