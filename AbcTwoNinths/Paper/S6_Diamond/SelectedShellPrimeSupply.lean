/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruiyi Zhang
-/

module

public import AbcTwoNinths.Paper.S5_Selection.Selected
public import AbcTwoNinths.Paper.S6_Diamond.LargeFreshPrimeSupply

/-!
# Selected Shell Prime Supply

The module defines admissibility for the selected shell and supplies fresh primes there. It supports Section 6 of the paper.

## Main results
* `AbcTwoNinths.Diamond.selectedShellSupply`
-/

@[expose] public section


namespace AbcTwoNinths.Diamond

section



/--
A prime on the least-radical side above the admissible cutoff satisfies the shell inequalities for a high triple at positive onset.
-/
theorem selectedShellAdmissible {η : ℚ} {σ X : ℝ} {t : _root_.AbcTwoNinths.Basic.Triple} {p : ℕ}
    (hη : _root_.AbcTwoNinths.Statement.admissibleEta η) (hσ : _root_.AbcTwoNinths.Statement.admissibleCutoff η σ) (hX : 0 < X)
    (hh : _root_.AbcTwoNinths.Statement.High η X t) (hp : p ∈ (_root_.AbcTwoNinths.Statement.sideValue t (_root_.AbcTwoNinths.Statement.minRadicalSide t)).primeFactors)
    (hcut : t.logHeight * Real.exp (-σ * t.thirdLogRadical) < (p : ℝ)) :
    _root_.AbcTwoNinths.ExteriorE2.Admissible (p : ℝ) t.logHeight (η : ℝ) t.thirdLogRadical := by
  have hη₀ : 0 < (η : ℝ) := by exact_mod_cast hη.1
  have hη₁ : (η : ℝ) < 1 / 9 := by
    simpa using (Rat.cast_lt (K := ℝ)).mpr hη.2
  have hx := hX.trans_le hh.1
  have hH := (Real.exp_pos _).trans_le hh.2
  have hp₀ : 0 < (p : ℝ) := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).pos
  have hheight := Real.log_le_log (Real.exp_pos _) hh.2
  rw [Real.log_exp] at hheight
  have hlog := Real.log_lt_log (mul_pos hH (Real.exp_pos _)) hcut
  rw [Real.log_mul hH.ne' (Real.exp_pos _).ne', Real.log_exp] at hlog
  have hmargin : 0 < _root_.AbcTwoNinths.ExteriorE2.margin (η : ℝ) := _root_.AbcTwoNinths.ExteriorE2.marginPos hη₁
  have hσ' : σ ≤ _root_.AbcTwoNinths.ExteriorE2.margin (η : ℝ) := by
    convert hσ.2 using 1
    unfold _root_.AbcTwoNinths.Statement.cutoffBudget _root_.AbcTwoNinths.Statement.highRate _root_.AbcTwoNinths.ExteriorE2.margin _root_.AbcTwoNinths.ExteriorE2.gap
    ring
  have hlo : _root_.AbcTwoNinths.ExteriorE2.c₀ (η : ℝ) * t.thirdLogRadical ≤ Real.log p := by
    unfold _root_.AbcTwoNinths.ExteriorE2.c₀ _root_.AbcTwoNinths.Statement.highRate at *
    linarith [mul_le_mul_of_nonneg_right hσ' hx.le, mul_nonneg hmargin.le hx.le]
  have hd : p ∣ _root_.AbcTwoNinths.Statement.sideRadical t (_root_.AbcTwoNinths.Statement.minRadicalSide t) := by
    exact Finset.dvd_prod_of_mem (fun q : ℕ => q) hp
  have hr : 0 < _root_.AbcTwoNinths.Statement.sideRadical t (_root_.AbcTwoNinths.Statement.minRadicalSide t) :=
    Finset.prod_pos fun _ h => (Nat.prime_of_mem_primeFactors h).pos
  have hle : (p : ℝ) ≤ (_root_.AbcTwoNinths.Statement.sideRadical t (_root_.AbcTwoNinths.Statement.minRadicalSide t) : ℝ) := by
    exact_mod_cast Nat.le_of_dvd hr hd
  have hhi := Real.log_le_log hp₀ (hle.trans (_root_.AbcTwoNinths.Statement.minSideLeScale t))
  rw [Real.log_exp] at hhi
  exact ⟨hp₀, hH, hx, hη₀, hη₁, hheight, hlo, hhi⟩

/--
At the common onset the unique prime above the cutoff satisfies the valuation-mass bound and defines a shell with at least M/(4 log M) fresh primes and a fresh witness. This is used in Section 6 of the paper.
-/
theorem selectedShellSupply {η : ℚ} {σ κ X : ℝ}
    (hη : _root_.AbcTwoNinths.Statement.admissibleEta η) (hσ : _root_.AbcTwoNinths.Statement.admissibleCutoff η σ) (hκ : _root_.AbcTwoNinths.Statement.admissibleMargin η κ)
    {t : _root_.AbcTwoNinths.Basic.Triple} (hord : t.a ≤ t.b)
    (hh : _root_.AbcTwoNinths.Statement.High η (max X (max 1
      (max 128 (16 * (1 + 6 / _root_.AbcTwoNinths.ExteriorE2.margin (η : ℝ))) / _root_.AbcTwoNinths.ExteriorE2.margin (η : ℝ)))) t)
    (h1 : _root_.AbcTwoNinths.Statement.RealContactBound κ t) (h2 : _root_.AbcTwoNinths.Statement.SmallPrimeMassBound σ κ t) :
    let u := _root_.AbcTwoNinths.Statement.sideValue t (_root_.AbcTwoNinths.Statement.minRadicalSide t)
    let T := t.logHeight * Real.exp (-σ * t.thirdLogRadical)
    ∃ p ∈ u.primeFactors, T < (p : ℝ) ∧
      (∀ q ∈ u.primeFactors, T < (q : ℝ) → q = p) ∧
      (1 - 2 * κ) * t.logHeight ≤ (padicValNat p u : ℝ) * Real.log p ∧
      _root_.AbcTwoNinths.ExteriorE2.Admissible (p : ℝ) t.logHeight (η : ℝ) t.thirdLogRadical ∧
      let S := _root_.AbcTwoNinths.ExteriorE2.m (p : ℝ) t.logHeight (_root_.AbcTwoNinths.ExteriorE2.margin (η : ℝ)) t.thirdLogRadical
      S / (4 * Real.log S) ≤ ((_root_.AbcTwoNinths.ExteriorE2.fresh t.radical S).card : ℝ) ∧
      ∃ q ∈ _root_.AbcTwoNinths.ExteriorE2.fresh t.radical S, q.Prime ∧ Real.sqrt S < (q : ℝ) ∧
        (q : ℝ) ≤ S ∧ ¬ q ∣ 2 * t.radical := by
  dsimp only
  let K := max 128 (16 * (1 + 6 / _root_.AbcTwoNinths.ExteriorE2.margin (η : ℝ))) / _root_.AbcTwoNinths.ExteriorE2.margin (η : ℝ)
  have htail : max 1 K ≤ t.thirdLogRadical := (le_max_right X _).trans hh.1
  have hpos : 0 < max 1 K := zero_lt_one.trans_le (le_max_left _ _)
  have ht : _root_.AbcTwoNinths.Statement.High η (max 1 K) t := ⟨htail, hh.2⟩
  obtain ⟨p, hp, hcut, huniq, hmass⟩ :=
    _root_.AbcTwoNinths.Selection.selectedPrimeOfExteriorBounds t hη hσ hκ hpos.le hord ht h1 h2
  have ha := _root_.AbcTwoNinths.Diamond.selectedShellAdmissible hη hσ hpos ht hp hcut
  have hR : 0 < t.radical :=
    Finset.prod_pos fun _ h => (Nat.prime_of_mem_primeFactors h).pos
  have hlog : Real.log t.radical = 3 * t.thirdLogRadical := by
    unfold _root_.AbcTwoNinths.Basic.Triple.thirdLogRadical _root_.AbcTwoNinths.Basic.Triple.logRadical
    ring
  exact ⟨p, hp, hcut, huniq, hmass, ha,
    _root_.AbcTwoNinths.Diamond.freshPrimeSupply hR hlog ha ((le_max_right 1 K).trans htail)⟩

end

end AbcTwoNinths.Diamond
