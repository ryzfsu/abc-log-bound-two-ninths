/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruiyi Zhang
-/

module

public import AbcTwoNinths.Paper.S6_Diamond.SelectedShellPrimeSupply

/-!
# Common threshold for the shell and prime supply

Finds a common threshold for the shell inequalities and the supply of auxiliary primes. It
supports Section 6 of the paper.

## Main results
* `AbcTwoNinths.Diamond.selectedOnsetShellSupply`
-/

@[expose] public section


namespace AbcTwoNinths.Diamond

section

/-- Above the common threshold, a prime on the minimum-radical side that clears the cutoff
has logarithm at least half the radical scale and contributes at least half the logarithmic
height through its valuation, under the assumed valuation bound. -/
theorem selectedPrimeOnsetBounds {η : ℚ} {σ κ X : ℝ} {t : _root_.AbcTwoNinths.Basic.Triple} {p : ℕ}
    (hη : _root_.AbcTwoNinths.Statement.admissibleEta η) (hσ : _root_.AbcTwoNinths.Statement.admissibleCutoff η σ) (hκ : _root_.AbcTwoNinths.Statement.admissibleMargin η κ)
    (hh : _root_.AbcTwoNinths.Statement.High η (max X (Real.exp (10^9))) t)
    (hp : p ∈ (_root_.AbcTwoNinths.Statement.sideValue t (_root_.AbcTwoNinths.Statement.minRadicalSide t)).primeFactors)
    (hcut : t.logHeight * Real.exp (-σ * t.thirdLogRadical) < (p : ℝ))
    (hm : (1 - 2 * κ) * t.logHeight ≤
      (padicValNat p (_root_.AbcTwoNinths.Statement.sideValue t (_root_.AbcTwoNinths.Statement.minRadicalSide t)) : ℝ) * Real.log p) :
    _root_.AbcTwoNinths.Statement.High η 16 t ∧ (10^9 : ℝ) ≤ Real.log t.thirdLogRadical ∧ t.thirdLogRadical / 2 ≤ Real.log p ∧
      5 ≤ p ∧ t.logHeight / 2 ≤
        (padicValNat p (_root_.AbcTwoNinths.Statement.sideValue t (_root_.AbcTwoNinths.Statement.minRadicalSide t)) : ℝ) * Real.log p := by
  have htail : Real.exp (10^9) ≤ t.thirdLogRadical := (le_max_right X _).trans hh.1
  have ha := _root_.AbcTwoNinths.Diamond.selectedShellAdmissible hη hσ (Real.exp_pos (10^9))
    (show _root_.AbcTwoNinths.Statement.High η (Real.exp (10^9)) t from ⟨htail, hh.2⟩) hp hcut
  have hx₁₆ : 16 ≤ t.thirdLogRadical :=
    (show (16 : ℝ) ≤ Real.exp (10^9) by linarith [Real.add_one_le_exp (10^9 : ℝ)]).trans htail
  have hlogx : (10^9 : ℝ) ≤ Real.log t.thirdLogRadical := by
    simpa using Real.log_le_log (Real.exp_pos (10^9)) htail
  have hell : t.thirdLogRadical / 2 ≤ Real.log p := by
    have hc : (1 / 2 : ℝ) ≤ _root_.AbcTwoNinths.ExteriorE2.c₀ (η : ℝ) := by linarith [_root_.AbcTwoNinths.ExteriorE2.c₀Lower ha.eta_lt]
    linarith [mul_le_mul_of_nonneg_right hc ha.hx.le, ha.log_lo]
  have hp₅ : 5 ≤ p := by
    by_contra! hh₅
    have hc : (p : ℝ) ≤ 4 := by exact_mod_cast (show p ≤ 4 by omega)
    have he : (p : ℝ) ≤ Real.exp 4 :=
      hc.trans (by linarith [Real.add_one_le_exp (4 : ℝ)])
    have hp₄ : Real.log p ≤ 4 := by simpa using Real.log_le_log ha.hp he
    linarith
  have hk : (1 / 2 : ℝ) ≤ 1 - 2 * κ := by linarith [hκ.2, ha.eta_pos]
  exact ⟨⟨hx₁₆, hh.2⟩, hlogx, hell, hp₅,
    (show t.logHeight / 2 ≤ (1 - 2 * κ) * t.logHeight by
      linarith [mul_le_mul_of_nonneg_right hk ha.hH.le]).trans hm⟩

/--
Supplies a unique prime above the cutoff together with its numerical bounds and a lower count and witness for the fresh-prime shell. This is used in Section 6 of the paper.
-/
theorem selectedOnsetShellSupply {η : ℚ} {σ κ X : ℝ}
    (hη : _root_.AbcTwoNinths.Statement.admissibleEta η) (hσ : _root_.AbcTwoNinths.Statement.admissibleCutoff η σ) (hκ : _root_.AbcTwoNinths.Statement.admissibleMargin η κ)
    {t : _root_.AbcTwoNinths.Basic.Triple} (hord : t.a ≤ t.b)
    (hh : _root_.AbcTwoNinths.Statement.High η (max (max X (Real.exp (10^9))) (max 1
      (max 128 (16 * (1 + 6 / _root_.AbcTwoNinths.ExteriorE2.margin (η : ℝ))) / _root_.AbcTwoNinths.ExteriorE2.margin (η : ℝ)))) t)
    (h1 : _root_.AbcTwoNinths.Statement.RealContactBound κ t) (h2 : _root_.AbcTwoNinths.Statement.SmallPrimeMassBound σ κ t) :
    let u := _root_.AbcTwoNinths.Statement.sideValue t (_root_.AbcTwoNinths.Statement.minRadicalSide t)
    let T := t.logHeight * Real.exp (-σ * t.thirdLogRadical)
    ∃ p ∈ u.primeFactors, T < (p : ℝ) ∧
      (∀ q ∈ u.primeFactors, T < (q : ℝ) → q = p) ∧
      (1 - 2 * κ) * t.logHeight ≤ (padicValNat p u : ℝ) * Real.log p ∧
      _root_.AbcTwoNinths.ExteriorE2.Admissible (p : ℝ) t.logHeight (η : ℝ) t.thirdLogRadical ∧
      _root_.AbcTwoNinths.Statement.High η 16 t ∧ (10^9 : ℝ) ≤ Real.log t.thirdLogRadical ∧ t.thirdLogRadical / 2 ≤ Real.log p ∧
      5 ≤ p ∧ t.logHeight / 2 ≤ (padicValNat p u : ℝ) * Real.log p ∧
      let S := _root_.AbcTwoNinths.ExteriorE2.m (p : ℝ) t.logHeight (_root_.AbcTwoNinths.ExteriorE2.margin (η : ℝ)) t.thirdLogRadical
      S / (4 * Real.log S) ≤ ((_root_.AbcTwoNinths.ExteriorE2.fresh t.radical S).card : ℝ) ∧
      ∃ q ∈ _root_.AbcTwoNinths.ExteriorE2.fresh t.radical S, q.Prime ∧ Real.sqrt S < (q : ℝ) ∧
        (q : ℝ) ≤ S ∧ ¬ q ∣ 2 * t.radical := by
  obtain ⟨p, hp, hcut, huniq, hm, ha, hcount⟩ :=
    _root_.AbcTwoNinths.Diamond.selectedShellSupply hη hσ hκ hord hh h1 h2
  obtain ⟨h16, hlogx, hell, hp5, hhalf⟩ :=
    selectedPrimeOnsetBounds hη hσ hκ ⟨(le_max_left _ _).trans hh.1, hh.2⟩ hp hcut hm
  exact ⟨p, hp, hcut, huniq, hm, ha, h16, hlogx, hell, hp5, hhalf, hcount⟩

end

end AbcTwoNinths.Diamond
