/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruiyi Zhang
-/

module

public import AbcTwoNinths.Paper.S4_ExteriorE2.NativeMultiplicity
public import AbcTwoNinths.Basic.PeriodMargin

/-!
# Interpolation Grid Margin

The module converts the logarithmic budget into a margin absorbing the loss from exponent multiplicity. It supports Proposition 4.1 of the paper.

## Main results
* `AbcTwoNinths.ExteriorE2.nativeGridMarginOfLogBudget`
-/

@[expose] public section


namespace AbcTwoNinths.ExteriorE2

section

/--
Beyond the explicit height threshold, the logarithm of the multiplicity costs at most half the prescribed depth share.
-/
theorem logMultiplicityLeHalfShare {g H θ : ℝ}
    (hg : 1 ≤ g) (hH : 0 < H) (hθ : 0 < θ)
    (hg_ub : g * Real.log 2 ≤ 2 * H)
    (hH_onset : 4 / θ * Real.log (8 / (θ * Real.log 2)) ≤ H) :
    Real.log g ≤ θ * H / 2 := by
  have h₂ : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hθH : 0 < θ * H / 4 := by positivity
  have hratio : 0 < 8 / (θ * Real.log 2) := by positivity
  have hg' : 0 < g := by linarith
  have hbound : g ≤ (θ * H / 4) * (8 / (θ * Real.log 2)) := by
    calc
      g ≤ 2 * H / Real.log 2 := (le_div_iff₀ h₂).2 hg_ub
      _ = _ := by field_simp; norm_num
  have hlog := Real.log_le_log hg' hbound
  rw [Real.log_mul hθH.ne' hratio.ne'] at hlog
  have hstart : Real.log (8 / (θ * Real.log 2)) ≤ θ * H / 4 := by
    have ht := (mul_le_mul_of_nonneg_left hH_onset hθ.le)
    rw [← mul_assoc] at ht
    have hcancel : θ * (4 / θ) = 4 := by field_simp
    rw [hcancel] at ht
    linarith
  linarith [Real.log_le_sub_one_of_pos hθH]

/--
The depth, height and logarithmic savings bounds make the grid count strictly less than the period. This is used in the proof of Proposition 4.1 of the paper.
-/
theorem nativeGridMarginOfLogBudget {I k Q d : ℕ} {B g H U θ depth rootHeight saving : ℝ}
    (hQ : 0 < Q) (hB : 0 < B) (hg : 1 ≤ g) (hH : 0 < H)
    (hU : 0 < U) (hθ : 0 < θ) (hI : (I : ℝ) ≤ B)
    (hroof : H ≤ (k : ℝ) * (g * U))
    (hshare : θ * H ≤ depth) (hlte : depth ≤ rootHeight + Real.log g)
    (hroot : g * rootHeight ≤ 2 * H) (hroot_lb : Real.log 2 ≤ rootHeight)
    (hH_onset : 4 / θ * Real.log (8 / (θ * Real.log 2)) ≤ H)
    (hsaving : Real.log B ≤ Real.log H - saving)
    (hbudget : Real.log (4 / θ) + Real.log U + (d : ℝ) * Real.log Q < saving) :
    I * Q ^ d < k := by
  have hg' : 0 < g := by linarith
  have hQ' : 0 < (Q : ℝ) := by exact_mod_cast hQ
  have hlog := _root_.AbcTwoNinths.ExteriorE2.logMultiplicityLeHalfShare hg hH hθ
    ((mul_le_mul_of_nonneg_left hroot_lb hg'.le).trans hroot) hH_onset
  have hmult := _root_.AbcTwoNinths.ExteriorE2.multiplicityOfRootBound hg' hH hshare hlte hroot hlog
  have hlogg := Real.log_le_log hg' ((le_div_iff₀ hθ).2 hmult)
  have hm := _root_.AbcTwoNinths.ExteriorE2.strictMarginOfExponentBudget hB hg' hU hH hQ' hsaving
    (d := d) (by linarith)
  simpa using (_root_.AbcTwoNinths.Basic.periodMargin (I := I) (k := k) (M := 1) hQ
    (by positivity : 0 ≤ 1 / (Q : ℝ)) hg' hU hI hroof (by simp) hm)

end

end AbcTwoNinths.ExteriorE2
