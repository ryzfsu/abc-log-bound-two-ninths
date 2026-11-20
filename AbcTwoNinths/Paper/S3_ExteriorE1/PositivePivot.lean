/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruiyi Zhang
-/

module

public import AbcTwoNinths.Paper.S3_ExteriorE1.ActualPivot

/-!
# Positive Pivot

The module proves that the source admits a positive pivot with the necessary coordinate height bounds. It supports Proposition 3.1 of the paper.

## Main results
* `AbcTwoNinths.ExteriorE1.actualPositivePivot`
-/

@[expose] public section


namespace AbcTwoNinths.ExteriorE1

section




/--
The absolute quotient exponent at each support prime, weighted by its logarithm, is at most the height of the triple.
-/
theorem quotientCoordinateHeight (t : _root_.AbcTwoNinths.Basic.Triple) (r : _root_.AbcTwoNinths.Basic.supp t) :
    Real.log (r.val : ℝ) * |(_root_.AbcTwoNinths.ExteriorE1.quotientVec t r : ℝ)| ≤ t.logHeight := by
  classical
  rw [_root_.AbcTwoNinths.ExteriorE1.quotientSignedHeight]
  have ha (i : _root_.AbcTwoNinths.Basic.supp t) : 0 ≤ Real.log (i.val : ℝ) :=
    Real.log_nonneg (by exact_mod_cast (_root_.AbcTwoNinths.Basic.suppPrime t i.property).one_le)
  unfold _root_.AbcTwoNinths.ExteriorE1.signedHeight
  rw [abs_eq_max_neg, mul_max_of_nonneg _ _ (ha r)]
  apply max_le
  · refine (mul_le_mul_of_nonneg_left (le_max_left _ (0 : ℝ)) (ha r)).trans
      (le_trans ?_ (le_max_left _ _))
    exact Finset.single_le_sum
      (f := fun i : _root_.AbcTwoNinths.Basic.supp t => Real.log (i.val : ℝ) * max (_root_.AbcTwoNinths.ExteriorE1.quotientVec t i : ℝ) 0)
      (fun i _ => mul_nonneg (ha i) (le_max_right _ _))
      (Finset.mem_univ r)
  · refine (mul_le_mul_of_nonneg_left (le_max_left _ (0 : ℝ)) (ha r)).trans
      (le_trans ?_ (le_max_right _ _))
    exact Finset.single_le_sum
      (f := fun i : _root_.AbcTwoNinths.Basic.supp t => Real.log (i.val : ℝ) * max (-(_root_.AbcTwoNinths.ExteriorE1.quotientVec t i : ℝ)) 0)
      (fun i _ => mul_nonneg (ha i) (le_max_right _ _))
      (Finset.mem_univ r)

/--
Failure of the real exterior bound gives a primitive quotient direction with a positive maximal coordinate between the stated height bounds. This is used in the proof of Proposition 3.1 of the paper.
-/
theorem actualPositivePivot (η : ℚ) (hη : _root_.AbcTwoNinths.Statement.admissibleEta η)
    (κ : ℝ) (hκ : 0 < κ) (t : _root_.AbcTwoNinths.Basic.Triple)
    (hab : t.a ≤ t.b) (hh : _root_.AbcTwoNinths.Statement.High η 0 t) (hf : ¬ _root_.AbcTwoNinths.Statement.RealContactBound κ t) :
    ∃ (v : _root_.AbcTwoNinths.Basic.supp t → ℤ) (s : ℤ) (r : _root_.AbcTwoNinths.Basic.supp t), (s = 1 ∨ s = -1) ∧
      (∀ i, _root_.AbcTwoNinths.ExteriorE1.quotientVec t i = (_root_.AbcTwoNinths.ExteriorE1.quotientGcd t : ℤ) * (s * v i)) ∧
      _root_.AbcTwoNinths.Basic.PrimitiveIn ⊤ v ∧ 0 < v r ∧ (∀ i, |v i| ≤ v r) ∧
      t.logHeight / ((_root_.AbcTwoNinths.ExteriorE1.quotientGcd t : ℝ) * (3 * t.thirdLogRadical)) ≤ (v r : ℝ) ∧
      (v r : ℝ) ≤ 2 * t.logHeight := by
  obtain ⟨w, r, hp, hw, hmax, hlo⟩ := _root_.AbcTwoNinths.ExteriorE1.actualPivotLower η hη κ hκ t hab hh hf
  have hg := _root_.AbcTwoNinths.ExteriorE1.quotientGcdPos t
  have hgR : (1 : ℝ) ≤ (_root_.AbcTwoNinths.ExteriorE1.quotientGcd t : ℝ) := by exact_mod_cast hg
  have hH : 0 < t.logHeight := (Real.exp_pos _).trans_le hh.2
  have hx : 0 < 3 * t.thirdLogRadical := by
    have := Finset.single_le_sum (f := fun i : _root_.AbcTwoNinths.Basic.supp t => Real.log (i.val : ℝ))
      (fun i _ => Real.log_nonneg (by exact_mod_cast
        (_root_.AbcTwoNinths.Basic.suppPrime t i.property).one_le)) (Finset.mem_univ r)
    have hpR : 1 < (r.val : ℝ) := by
      exact_mod_cast (_root_.AbcTwoNinths.Basic.suppPrime t r.property).one_lt
    exact (Real.log_pos hpR).trans_le (this.trans (_root_.AbcTwoNinths.ExteriorE1.quotientSupportWeight t))
  have hwr : w r ≠ 0 := by
    intro hz
    simp [hz] at hlo
    exact (not_le_of_gt (div_pos hH (mul_pos (by linarith) hx))) hlo
  obtain ⟨v, s, hs, hv, hvr, hpos, hmax'⟩ := _root_.AbcTwoNinths.ExteriorE1.normalizePivot w r hwr hmax
  have hvprim : _root_.AbcTwoNinths.Basic.PrimitiveIn ⊤ v := by
    intro n u _ hu
    apply hp n (s • u) (by simp)
    funext i
    have hi := congrFun hu i
    change (n : ℤ) * u i = v i at hi
    change (n : ℤ) * (s * u i) = w i
    rw [hv i, ← hi]
    ring
  have hvR : (v r : ℝ) = |(w r : ℝ)| := by exact_mod_cast hvr
  refine ⟨v, s, r, hs, fun i => by rw [hw, hv], hvprim, hpos, hmax',
    by rwa [hvR], ?_⟩
  have hlog : (1 : ℝ) / 2 ≤ Real.log (r.val : ℝ) := by
    have hp2 : (2 : ℝ) ≤ (r.val : ℝ) := by
      exact_mod_cast (_root_.AbcTwoNinths.Basic.suppPrime t r.property).two_le
    exact (by linarith [Real.log_two_gt_d9] : (1 : ℝ) / 2 ≤ Real.log 2).trans
      (Real.log_le_log (by norm_num) hp2)
  have he := _root_.AbcTwoNinths.ExteriorE1.quotientCoordinateHeight t r
  rw [hw, Int.cast_mul, abs_mul] at he
  push_cast at he
  rw [abs_of_nonneg (by linarith : (0 : ℝ) ≤ (_root_.AbcTwoNinths.ExteriorE1.quotientGcd t : ℝ)), ← hvR] at he
  have hpv : (0 : ℝ) ≤ (v r : ℝ) := by exact_mod_cast hpos.le
  have hfactor : (1 : ℝ) / 2 ≤ Real.log (r.val : ℝ) * (_root_.AbcTwoNinths.ExteriorE1.quotientGcd t : ℝ) := by
    nlinarith [mul_nonneg (show 0 ≤ Real.log (r.val : ℝ) by linarith)
      (sub_nonneg.mpr hgR)]
  nlinarith [mul_le_mul_of_nonneg_right hfactor hpv]

end

end AbcTwoNinths.ExteriorE1
