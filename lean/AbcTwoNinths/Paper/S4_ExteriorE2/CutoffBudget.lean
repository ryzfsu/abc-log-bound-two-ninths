/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruiyi Zhang
-/

module

public import AbcTwoNinths.Paper.S4_ExteriorE2.TailOnset

/-!
# Cutoff Budget

The module converts excess small-prime valuation mass into a modulus satisfying the cutoff budget. It supports Proposition 4.1 of the paper.

## Main results
* `AbcTwoNinths.ExteriorE2.e2ViolationTightModulus`
-/

@[expose] public section


namespace AbcTwoNinths.ExteriorE2

section




/--
For a high triple beyond the stated threshold, the logarithmic cutoff bounds log 4 and half the radical scale x, and its exponential equals the cutoff.
-/
theorem e2TightCutoffBudget (t : _root_.AbcTwoNinths.Basic.Triple) {η : ℚ} {X σ : ℝ}
    (hη : _root_.AbcTwoNinths.Statement.admissibleEta η) (hσ : _root_.AbcTwoNinths.Statement.admissibleCutoff η σ)
    (hX : 2 * Real.log (4 : ℝ) ≤ X) (hHigh : _root_.AbcTwoNinths.Statement.High η X t) :
    let B := Real.log t.logHeight - σ * t.thirdLogRadical
    Real.log (4 : ℝ) ≤ B ∧ t.thirdLogRadical ≤ 2 * B ∧
    t.logHeight * Real.exp (-σ * t.thirdLogRadical) = Real.exp B := by
  dsimp
  have hη' : (η : ℝ) < 1 / 9 := by
    have hq := (Rat.cast_lt (K := ℝ)).2 hη.2
    simpa only [Rat.cast_div, Rat.cast_one, Rat.cast_ofNat] using hq
  have hcut := hσ.2
  unfold _root_.AbcTwoNinths.Statement.cutoffBudget at hcut
  have hrate : 1 / 2 ≤ _root_.AbcTwoNinths.Statement.highRate η - σ := by
    unfold _root_.AbcTwoNinths.Statement.highRate at *
    linarith
  have hx4 := hX.trans hHigh.1
  have hx : 0 ≤ t.thirdLogRadical := by linarith [Real.log_nonneg (show (1 : ℝ) ≤ 4 by norm_num)]
  have hp : 0 < t.logHeight := (Real.exp_pos _).trans_le hHigh.2
  have hlog := (Real.le_log_iff_exp_le hp).mpr hHigh.2
  have hb : t.thirdLogRadical ≤ 2 * (Real.log t.logHeight - σ * t.thirdLogRadical) := by
    nlinarith [mul_le_mul_of_nonneg_right hrate hx]
  refine ⟨by linarith, hb, ?_⟩
  rw [Real.exp_sub, Real.exp_log hp]
  simp [neg_mul, Real.exp_neg, div_eq_mul_inv]

/--
Excess small-prime mass yields a modulus below or at the cutoff whose power divides the smooth part and carries at least one sixteenth of the required mass. This is used in the proof of Proposition 4.1 of the paper.
-/
theorem e2ViolationTightModulus (t : _root_.AbcTwoNinths.Basic.Triple) {η : ℚ} {X σ κ : ℝ}
    (hη : _root_.AbcTwoNinths.Statement.admissibleEta η) (hσ : _root_.AbcTwoNinths.Statement.admissibleCutoff η σ) (hκ : 0 < κ)
    (hX : 2 * Real.log (4 : ℝ) ≤ X) (hHigh : _root_.AbcTwoNinths.Statement.High η X t)
    (hstart : (16 / κ) ^ 2 ≤ t.logHeight) (hbad : ¬ _root_.AbcTwoNinths.Statement.SmallPrimeMassBound σ κ t) :
    let A := _root_.AbcTwoNinths.Statement.sideValue t (_root_.AbcTwoNinths.Statement.minRadicalSide t)
    let cutoff := t.logHeight * Real.exp (-σ * t.thirdLogRadical)
    ∃ M L : ℕ, 2 ≤ M ∧ 0 < L ∧ M ^ L ∣ _root_.AbcTwoNinths.ExteriorE2.smoothPart A cutoff ∧
      M ^ L ∣ A ∧ (¬ 2 ∣ M ∨ 4 ∣ M) ∧ (M : ℝ) ≤ cutoff ∧
      (Real.log t.logHeight - σ * t.thirdLogRadical) / 2 ≤ Real.log (M : ℝ) ∧
      κ * t.logHeight / 16 ≤ (L : ℝ) * Real.log (M : ℝ) := by
  obtain ⟨hfour, hx, hcut⟩ := _root_.AbcTwoNinths.ExteriorE2.e2TightCutoffBudget t hη hσ hX hHigh
  have hB : 0 < Real.log t.logHeight - σ * t.thirdLogRadical :=
    (Real.log_pos (by norm_num : (1 : ℝ) < 4)).trans_le hfour
  have hH : 0 < t.logHeight := (Real.exp_pos _).trans_le hHigh.2
  have hsqrt := (Real.le_sqrt (by positivity : 0 ≤ 16 / κ) hH.le).mpr hstart
  have hspos := Real.sqrt_pos.2 hH
  have hsκ := (div_le_iff₀ hκ).mp hsqrt
  have hhκ := mul_le_mul_of_nonneg_right hsκ hspos.le
  rw [mul_right_comm, ← pow_two, Real.sq_sqrt hH.le] at hhκ
  have hlogSq : Real.log t.logHeight = 2 * Real.log (Real.sqrt t.logHeight) := by
    rw [← Real.sq_sqrt hH.le, Real.log_pow]
    norm_num
  have hlarge : 8 * (Real.log t.logHeight - σ * t.thirdLogRadical) ≤ κ * t.logHeight := by
    have hnonneg : 0 ≤ σ * t.thirdLogRadical :=
      mul_nonneg hσ.1.le ((mul_nonneg (by norm_num) (Real.log_nonneg (by norm_num))).trans
        (hX.trans hHigh.1))
    rw [hlogSq]
    linarith [Real.log_le_sub_one_of_pos hspos]
  have hrad : (∑ q ∈ (_root_.AbcTwoNinths.Statement.sideValue t (_root_.AbcTwoNinths.Statement.minRadicalSide t)).primeFactors,
      Real.log (q : ℝ)) ≤ t.thirdLogRadical := by
    have hp := _root_.AbcTwoNinths.Statement.minSideLeScale t
    have hpos : 0 < (_root_.AbcTwoNinths.Statement.sideRadical t (_root_.AbcTwoNinths.Statement.minRadicalSide t) : ℝ) := by
      exact_mod_cast (Finset.prod_pos fun _ h => (Nat.prime_of_mem_primeFactors h).pos :
        0 < _root_.AbcTwoNinths.Statement.sideRadical t (_root_.AbcTwoNinths.Statement.minRadicalSide t))
    have hl := (Real.log_le_iff_le_exp hpos).mpr hp
    unfold _root_.AbcTwoNinths.Statement.sideRadical _root_.AbcTwoNinths.Basic.radical at hl
    push_cast at hl
    rwa [Real.log_prod (fun q hq => by
      exact_mod_cast (Nat.prime_of_mem_primeFactors hq).ne_zero)] at hl
  obtain ⟨M, L, hM, hL, hsm, hd, hparity, hlo, hhi, hmass⟩ :=
    _root_.AbcTwoNinths.ExteriorE2.e2ViolationModulus t hB hfour hcut.le hlarge (hrad.trans hx) hbad
  dsimp
  refine ⟨M, L, hM, hL, hsm, hd, hparity, ?_, hlo, hmass⟩
  rw [hcut]
  exact (Real.log_le_iff_le_exp (by exact_mod_cast (show 0 < M by omega))).mp hhi

end

end AbcTwoNinths.ExteriorE2
