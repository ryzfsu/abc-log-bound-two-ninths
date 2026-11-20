/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruiyi Zhang
-/

module

public import AbcTwoNinths.Paper.S1_Statement.OrderedTriple
public import AbcTwoNinths.Paper.S3_ExteriorE1.PlaneHeightComparison

/-!
# Small Prime Logarithmic Bounds

The module bounds the logarithmic height budget for the source triple and its reduced plane. It supports Proposition 4.1 of the paper.

## Main results
* `AbcTwoNinths.ExteriorE2.nativeLogHLe`
* `AbcTwoNinths.ExteriorE2.nativeLogBudget`
-/

@[expose] public section


namespace AbcTwoNinths.ExteriorE2

section

open Real

/--
The cutoff hypothesis bounds the logarithm of the height by four times the logarithm of the modulus. This is used in the proof of Proposition 4.1 of the paper.
-/
theorem nativeLogHLe {t : _root_.AbcTwoNinths.Basic.Triple} {η : ℚ} {X σ : ℝ} {B : ℕ}
    (hη : _root_.AbcTwoNinths.Statement.admissibleEta η) (hX : 0 ≤ X) (hHigh : _root_.AbcTwoNinths.Statement.High η X t)
    (hσ : _root_.AbcTwoNinths.Statement.admissibleCutoff η σ) (hH : 0 < t.logHeight)
    (hB : (log t.logHeight - σ * t.thirdLogRadical) / 2 ≤ log (B : ℝ)) :
    log t.logHeight ≤ 4 * log (B : ℝ) := by
  have hη' : (η : ℝ) < 1 / 9 := by
    simpa only [Rat.cast_div, Rat.cast_one, Rat.cast_ofNat] using
      (Rat.cast_lt (K := ℝ)).2 hη.2
  have hx := hX.trans hHigh.1
  have hσ' := hσ.2
  unfold _root_.AbcTwoNinths.Statement.cutoffBudget at hσ'
  have hrate : 2 * σ ≤ _root_.AbcTwoNinths.Statement.highRate η := by
    unfold _root_.AbcTwoNinths.Statement.highRate at *
    linarith
  have hlog := (Real.le_log_iff_exp_le hH).2 hHigh.2
  have hmul := mul_le_mul_of_nonneg_right hrate hx
  linarith

/--
The coordinate estimates bound the normalized exponent logarithm plus one by fifteen times the logarithm of the modulus. This is used in the proof of Proposition 4.1 of the paper.
-/
theorem nativeLogBudget {t : _root_.AbcTwoNinths.Basic.Triple} {η : ℚ} {X σ : ℝ} {B c d : ℕ}
    (hη : _root_.AbcTwoNinths.Statement.admissibleEta η) (hX : 0 ≤ X) (hHigh : _root_.AbcTwoNinths.Statement.High η X t)
    (hσ : _root_.AbcTwoNinths.Statement.admissibleCutoff η σ) (hB : 3 ≤ B)
    (hmod : (log t.logHeight - σ * t.thirdLogRadical) / 2 ≤ log (B : ℝ))
    {a b sourceHeight uHeight vHeight : ℝ}
    (ha : 1 ≤ a) (hb : 1 ≤ b) (hcd : 0 < c + d)
    (hH : 0 < t.logHeight) (hsource : sourceHeight ≤ 2 * t.logHeight)
    (hu : log 2 ≤ uHeight) (hv : log 2 ≤ vHeight)
    (hc : (c : ℝ) * uHeight ≤ 3 * sourceHeight)
    (hd : (d : ℝ) * vHeight ≤ 2 * sourceHeight) :
    log ((d : ℝ) / b + (c : ℝ) / a) + 1 ≤ 15 * log (B : ℝ) := by
  have hlog := _root_.AbcTwoNinths.ExteriorE2.nativeLogHLe hη hX hHigh hσ hH hmod
  have htwo : (1 / 2 : ℝ) < log 2 := by
    nlinarith [Real.log_two_gt_d9]
  have hcr : (0 : ℝ) ≤ c := by positivity
  have hdr : (0 : ℝ) ≤ d := by positivity
  have hcl := mul_le_mul_of_nonneg_left (htwo.le.trans hu) hcr
  have hdl := mul_le_mul_of_nonneg_left (htwo.le.trans hv) hdr
  have hcb : (c : ℝ) / a ≤ c := by
    exact (div_le_iff₀ (by linarith)).2 (by nlinarith [mul_nonneg hcr (sub_nonneg.mpr ha)])
  have hdb : (d : ℝ) / b ≤ d := by
    exact (div_le_iff₀ (by linarith)).2 (by nlinarith [mul_nonneg hdr (sub_nonneg.mpr hb)])
  have hpos : 0 < (d : ℝ) / b + (c : ℝ) / a := by
    rcases Nat.eq_zero_or_pos c with h | h
    · have hd' : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
      exact add_pos_of_pos_of_nonneg (div_pos hd' (by linarith)) (by positivity)
    · have hc' : (0 : ℝ) < c := by exact_mod_cast h
      exact add_pos_of_nonneg_of_pos (by positivity) (div_pos hc' (by linarith))
  have hsum : (d : ℝ) / b + (c : ℝ) / a ≤ 32 * t.logHeight := by linarith
  have hlogsum := Real.log_le_log hpos hsum
  rw [Real.log_mul (by norm_num) hH.ne'] at hlogsum
  have hBr : (3 : ℝ) ≤ B := by exact_mod_cast hB
  have hB1 : 1 ≤ log (B : ℝ) :=
    ((Real.lt_log_iff_exp_lt (by linarith)).2
      (Real.exp_one_lt_three.trans_le hBr)).le
  have hlog32 : log (32 : ℝ) ≤ 5 * log (B : ℝ) := by
    rw [show (32 : ℝ) = 2 ^ (5 : ℕ) by norm_num, Real.log_pow]
    norm_num only [Nat.cast_ofNat]
    linarith [Real.log_le_log (by norm_num : (0 : ℝ) < 2) (show (2 : ℝ) ≤ B by linarith)]
  linarith



end

end AbcTwoNinths.ExteriorE2
