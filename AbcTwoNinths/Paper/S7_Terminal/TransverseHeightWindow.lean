/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruiyi Zhang
-/

module

public import AbcTwoNinths.Paper.S6_Diamond.SelectedShellPrimeSupply
public import AbcTwoNinths.Paper.S7_Terminal.SelectedAxialGrowth
public import AbcTwoNinths.Paper.S4_ExteriorE2.VolumeSecondMoment

/-!
# Transverse Height Window

The module furnishes the transverse inequalities needed to apply the shell contradiction. It supports Section 7 of the paper.

## Main results
* `AbcTwoNinths.Terminal.transverseConstants`
* `AbcTwoNinths.Terminal.shellWindow`
-/

@[expose] public section


namespace AbcTwoNinths.Terminal



section

/--
Admissibility gives a positive half-margin and a strict upper bound for three transverse exponents. This is used in Section 7 of the paper.
-/
theorem transverseConstants {η : ℚ} {κ : ℝ} (hη : _root_.AbcTwoNinths.Statement.admissibleEta η)
    (hκ : _root_.AbcTwoNinths.Statement.admissibleMargin η κ) :
    0 < _root_.AbcTwoNinths.ExteriorE2.margin (η : ℝ)/2 ∧
    3 * (3*(η : ℝ) + _root_.AbcTwoNinths.ExteriorE2.gap (η : ℝ)/2) < 1 - 2*κ := by
  have heta : (η : ℝ) < 1/9 := by
    simpa using (Rat.cast_lt (K := ℝ)).mpr hη.2
  refine ⟨half_pos (_root_.AbcTwoNinths.ExteriorE2.marginPos heta), ?_⟩
  unfold _root_.AbcTwoNinths.ExteriorE2.gap
  linarith [hκ.2]

/--
Bounds the cost plus the logarithm of the larger fresh prime, normalized by the selected prime logarithm. This is used in Section 7 of the paper.
-/
theorem shellWindow {p R q₁ q₂ : ℕ} {H η x cost : ℝ}
    (adm : _root_.AbcTwoNinths.ExteriorE2.Admissible p H η x)
    (hx : Real.exp (4 / _root_.AbcTwoNinths.ExteriorE2.margin η) ≤ x)
    (h₁ : _root_.AbcTwoNinths.ExteriorE2.Fresh (_root_.AbcTwoNinths.ExteriorE2.m p H (_root_.AbcTwoNinths.ExteriorE2.margin η) x) R q₁)
    (h₂ : _root_.AbcTwoNinths.ExteriorE2.Fresh (_root_.AbcTwoNinths.ExteriorE2.m p H (_root_.AbcTwoNinths.ExteriorE2.margin η) x) R q₂)
    (hc : 0 ≤ cost) (hr : cost < 2*x/Real.log x) :
    let t := cost + Real.log ((max q₁ q₂ : ℕ) : ℝ)
    _root_.AbcTwoNinths.ExteriorE2.margin η/2 < t/Real.log p ∧ t/Real.log p < 3*η + _root_.AbcTwoNinths.ExteriorE2.gap η/2 := by
  have he := _root_.AbcTwoNinths.ExteriorE2.marginPos adm.eta_lt
  have hlog : 4 / _root_.AbcTwoNinths.ExteriorE2.margin η ≤ Real.log x :=
    (Real.le_log_iff_exp_le adm.hx).2 hx
  have hl : 0 < Real.log x := lt_of_lt_of_le (by positivity : 0 < 4 / _root_.AbcTwoNinths.ExteriorE2.margin η) hlog
  have hα : 2 / Real.log x < _root_.AbcTwoNinths.ExteriorE2.margin η := by
    apply (div_lt_iff₀ hl).2
    have h := (div_le_iff₀ he).1 hlog
    linarith
  have hs := _root_.AbcTwoNinths.ExteriorE2.MPos (p : ℝ) H (_root_.AbcTwoNinths.ExteriorE2.margin η) x
  have hq : Real.sqrt (_root_.AbcTwoNinths.ExteriorE2.m p H (_root_.AbcTwoNinths.ExteriorE2.margin η) x) < ((max q₁ q₂ : ℕ) : ℝ) :=
    h₁.2.1.trans_le (by exact_mod_cast le_max_left q₁ q₂)
  have hqpos := (Real.sqrt_pos.2 hs).trans hq
  have hlower := Real.log_lt_log (Real.sqrt_pos.2 hs) hq
  rw [Real.log_sqrt hs.le] at hlower
  have hu : ((max q₁ q₂ : ℕ) : ℝ) ≤ _root_.AbcTwoNinths.ExteriorE2.m p H (_root_.AbcTwoNinths.ExteriorE2.margin η) x := by
    rw [Nat.cast_max]
    exact max_le h₁.2.2.1 h₂.2.2.1
  have hu' := Real.log_le_log hqpos hu
  have h := _root_.AbcTwoNinths.ExteriorE2.transverseRatio (α := 2 / Real.log x)
    (t := cost + Real.log ((max q₁ q₂ : ℕ) : ℝ)) adm (by positivity) hα
    (by linarith)
    (by rw [div_mul_eq_mul_div]; linarith)
  exact ⟨h.1, h.2.1.trans_lt h.2.2.1⟩

end

end AbcTwoNinths.Terminal
