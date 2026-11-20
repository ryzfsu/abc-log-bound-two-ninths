/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruiyi Zhang
-/

module

public import AbcTwoNinths.Paper.S1_Statement.OrderedTriple
public import Mathlib.Tactic

/-!
# Principal Unit Valuation Bracket

For a prime above the cutoff and under the coefficient height bounds, the principal-unit estimate's
logarithmic bracket equals four. This supports Theorem 1.1 of the paper.

## Main results
* `AbcTwoNinths.Statement.actualBracket`
-/

@[expose] public section


namespace AbcTwoNinths.Statement

section



/-- The principal-unit valuation bracket equals `4` under the prime cutoff, depth,
and normalized coefficient bounds for the triple. -/
theorem actualBracket {eta : ℚ} {sigma kappa : ℝ} (t : _root_.AbcTwoNinths.Basic.Triple)
    (heta : _root_.AbcTwoNinths.Statement.admissibleEta eta) (hsigma : _root_.AbcTwoNinths.Statement.admissibleCutoff eta sigma)
    (_hkappa : _root_.AbcTwoNinths.Statement.admissibleMargin eta kappa)
    {p : ℕ} (hp : p.Prime)
    (hcut : t.logHeight * Real.exp (-sigma * t.thirdLogRadical) < (p : ℝ))
    (hx : 16 ≤ t.thirdLogRadical) (hroof : t.thirdLogRadical / 2 ≤ Real.log (p : ℝ))
    {B₁ B₂ : ℝ} (hB₁ : 0 < B₁) (hB₂ : 0 < B₂)
    {c d : ℤ} (hc : c ≠ 0)
    (hscale : ((c.natAbs : ℝ) / B₂ + (d.natAbs : ℝ) / B₁) *
      Real.log (p : ℝ) ≤ 32 * t.logHeight / t.thirdLogRadical) :
    max 4 (Real.log (Real.exp 2 * Real.log (p : ℝ) *
      (((c.natAbs : ℝ) / B₂ + (d.natAbs : ℝ) / B₁) / 2)) /
        Real.log (p : ℝ)) = 4 := by
  let x := t.thirdLogRadical
  let ell := Real.log (p : ℝ)
  let b := (c.natAbs : ℝ) / B₂ + (d.natAbs : ℝ) / B₁
  change 16 ≤ x at hx
  change x / 2 ≤ ell at hroof
  change b * ell ≤ 32 * t.logHeight / x at hscale
  change max 4 (Real.log (Real.exp 2 * ell * (b / 2)) / ell) = 4
  have hxpos : 0 < x := by linarith
  have hell : 0 < ell := by linarith
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hb : 0 < b := by
    dsimp [b]
    apply add_pos_of_pos_of_nonneg
    · exact div_pos (by exact_mod_cast Int.natAbs_pos.mpr hc) hB₂
    · positivity
  have hterm : ell * (b / 2) ≤ t.logHeight := by
    have h := (le_div_iff₀ hxpos).mp hscale
    have hmul := mul_le_mul_of_nonneg_left hx (mul_nonneg hb.le hell.le)
    nlinarith
  have hlocal : t.logHeight ≤ Real.exp (ell + sigma * x) := by
    have h := mul_lt_mul_of_pos_right hcut (Real.exp_pos (sigma * x))
    change t.logHeight * Real.exp (-sigma * x) * Real.exp (sigma * x) <
      (p : ℝ) * Real.exp (sigma * x) at h
    rw [show -sigma * x = -(sigma * x) by ring, mul_assoc, ← Real.exp_add,
      neg_add_cancel, Real.exp_zero, mul_one] at h
    rw [Real.exp_add, show Real.exp ell = (p : ℝ) from Real.exp_log hpR]
    exact h.le
  have hetaR : 0 < (eta : ℝ) := by exact_mod_cast heta.1
  have hs : sigma ≤ 1 / 2 := by
    have h := hsigma.2
    unfold _root_.AbcTwoNinths.Statement.cutoffBudget _root_.AbcTwoNinths.Statement.highRate at h
    linarith
  have hlog : Real.log (Real.exp 2 * ell * (b / 2)) ≤ 2 + (ell + sigma * x) := by
    have h := mul_le_mul_of_nonneg_left (hterm.trans hlocal) (Real.exp_pos 2).le
    rw [← Real.exp_add] at h
    exact (Real.log_le_iff_le_exp (by positivity)).2 (by simpa only [mul_assoc] using h)
  have hsx := mul_le_mul_of_nonneg_right hs hxpos.le
  apply max_eq_left
  apply (div_le_iff₀ hell).2
  linarith

end

end AbcTwoNinths.Statement
