/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruiyi Zhang
-/

module

public import AbcTwoNinths.Paper.S1_Statement.OrderedTriple

/-!
# Exponent Interval Separation

For high triples, the square of the prime cutoff is at least the cube root of the radical. This
supports Theorem 1.1 of the paper.

## Main results
* `AbcTwoNinths.Statement.cutoffSquareSeparation`
-/

@[expose] public section


namespace AbcTwoNinths.Statement

section



/--
On the high tail at a nonnegative onset the square of the cutoff dominates the exponential of the radical scale. This is used in the proof of Theorem 1.1 of the paper.
-/
theorem cutoffSquareSeparation {η : ℚ} {σ X : ℝ} {t : _root_.AbcTwoNinths.Basic.Triple}
    (hη : _root_.AbcTwoNinths.Statement.admissibleEta η) (hσ : _root_.AbcTwoNinths.Statement.admissibleCutoff η σ)
    (hX : 0 ≤ X) (hH : _root_.AbcTwoNinths.Statement.High η X t) :
    Real.exp t.thirdLogRadical ≤ (t.logHeight * Real.exp (-σ * t.thirdLogRadical)) ^ 2 := by
  have he' : (η : ℝ) < (((1 : ℚ) / 9 : ℚ) : ℝ) := Rat.cast_lt.mpr hη.2
  have he : (η : ℝ) < 1 / 9 := by simpa using he'
  have hb := hσ.2
  unfold _root_.AbcTwoNinths.Statement.cutoffBudget at hb
  have hr : (1 : ℝ) / 2 ≤ _root_.AbcTwoNinths.Statement.highRate η - σ := by
    unfold _root_.AbcTwoNinths.Statement.highRate at hb ⊢
    linarith
  have hx : 0 ≤ t.thirdLogRadical := hX.trans hH.1
  have ht : Real.exp (t.thirdLogRadical / 2) ≤ t.logHeight * Real.exp (-σ * t.thirdLogRadical) := by
    calc
      Real.exp (t.thirdLogRadical / 2) ≤ Real.exp ((_root_.AbcTwoNinths.Statement.highRate η - σ) * t.thirdLogRadical) :=
        Real.exp_le_exp.mpr (by
          rw [div_eq_mul_inv, mul_comm t.thirdLogRadical]
          exact mul_le_mul_of_nonneg_right (by simpa using hr) hx)
      _ = Real.exp (_root_.AbcTwoNinths.Statement.highRate η * t.thirdLogRadical) * Real.exp (-σ * t.thirdLogRadical) := by
        rw [sub_mul, sub_eq_add_neg, neg_mul, Real.exp_add]
      _ ≤ _ := mul_le_mul_of_nonneg_right hH.2 (Real.exp_pos _).le
  calc
    Real.exp t.thirdLogRadical = Real.exp (t.thirdLogRadical / 2) ^ 2 := by
      rw [pow_two, ← Real.exp_add]
      congr 1
      ring
    _ ≤ _ := pow_le_pow_left₀ (Real.exp_pos _).le ht _

end

end AbcTwoNinths.Statement
