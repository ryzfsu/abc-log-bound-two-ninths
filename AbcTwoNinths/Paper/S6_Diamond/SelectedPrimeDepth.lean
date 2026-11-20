/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruiyi Zhang
-/

module

public import AbcTwoNinths.Paper.S1_Statement.PrincipalUnitValuationBracket
public import Mathlib
public import AbcTwoNinths.Paper.S5_Selection.OrderedRadicalData
public import AbcTwoNinths.Paper.S2_PolyCap.SideProjection
public import AbcTwoNinths.Paper.S6_Diamond.ProjectedKernelBasis
public import AbcTwoNinths.Paper.S6_Diamond.SelectedShellOnset
public import AbcTwoNinths.Paper.S6_Diamond.PrincipalUnitBracket

/-!
# Selected Prime Depth

Computes the valuation of the normalized principal-unit difference at the selected prime and
bounds its depth. It supports Section 6 of the paper.

## Main results
* `AbcTwoNinths.Diamond.smNormalizedBracket`
-/

@[expose] public section


namespace AbcTwoNinths.Diamond

section



/-- The scaled coefficient bound for a high triple forces the normalized
p-adic logarithmic bracket at its selected prime to equal four. -/
theorem smNormalizedBracket
    {eta : ℚ} {sigma kappa : ℝ} (t : _root_.AbcTwoNinths.Basic.Triple)
    (heta : _root_.AbcTwoNinths.Statement.admissibleEta eta) (hsigma : _root_.AbcTwoNinths.Statement.admissibleCutoff eta sigma)
    (hkappa : _root_.AbcTwoNinths.Statement.admissibleMargin eta kappa) {p : ℕ} (hp : p.Prime)
    (hcut : t.logHeight * Real.exp (-sigma * t.thirdLogRadical) < (p : ℝ))
    (hh : _root_.AbcTwoNinths.Statement.High eta 16 t)
    {B₁ B₂ : ℝ} (hB₁ : 0 < B₁) (hB₂ : 0 < B₂)
    {c d : ℤ} (hc : c ≠ 0)
    (hscale : ((c.natAbs : ℝ) / B₂ + (d.natAbs : ℝ) / B₁) *
      Real.log (p : ℝ) ≤ 32 * t.logHeight / t.thirdLogRadical) :
    max 4 (Real.log (Real.exp 2 * Real.log (p : ℝ) *
      (((c.natAbs : ℝ) / B₂ + (d.natAbs : ℝ) / B₁) / 2)) /
        Real.log (p : ℝ)) = 4 := by
  have hx := hh.1
  have hx0 : 0 ≤ t.thirdLogRadical := by linarith
  have he : (eta : ℝ) < 1 / 9 := by
    have h := (Rat.cast_lt (K := ℝ)).mpr heta.2
    norm_num at h ⊢
    exact h
  have hs := hsigma.2
  unfold _root_.AbcTwoNinths.Statement.cutoffBudget _root_.AbcTwoNinths.Statement.highRate at hs
  have hr : (1 / 2 : ℝ) ≤ _root_.AbcTwoNinths.Statement.highRate eta - sigma := by
    unfold _root_.AbcTwoNinths.Statement.highRate
    linarith
  have hext : Real.exp (t.thirdLogRadical / 2) < (p : ℝ) := calc
    _ ≤ Real.exp ((_root_.AbcTwoNinths.Statement.highRate eta - sigma) * t.thirdLogRadical) := Real.exp_le_exp.mpr
      (by nlinarith [mul_le_mul_of_nonneg_right hr hx0])
    _ = Real.exp (_root_.AbcTwoNinths.Statement.highRate eta * t.thirdLogRadical) * Real.exp (-sigma * t.thirdLogRadical) := by
      rw [← Real.exp_add]
      congr 1
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hh.2 (Real.exp_pos _).le
    _ < _ := hcut
  have hroof : t.thirdLogRadical / 2 ≤ Real.log (p : ℝ) := by
    simpa only [Real.log_exp] using (Real.log_lt_log (Real.exp_pos _) hext).le
  exact _root_.AbcTwoNinths.Statement.actualBracket t heta hsigma hkappa hp hcut hx hroof
    hB₁ hB₂ hc hscale

end

section



end

end AbcTwoNinths.Diamond
