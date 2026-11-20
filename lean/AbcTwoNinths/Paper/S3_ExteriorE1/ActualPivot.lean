/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruiyi Zhang
-/

module

public import AbcTwoNinths.Paper.S3_ExteriorE1.PivotNormalization

/-!
# Actual Pivot

The module gives a positive lower bound on the selected pivot coordinate of the source. It supports Proposition 3.1 of the paper.

## Main results
* `AbcTwoNinths.ExteriorE1.actualPivotLower`
-/

@[expose] public section


namespace AbcTwoNinths.ExteriorE1

section




/--
For an ordered high triple violating the real estimate, a primitive quotient vector has a maximal coordinate of magnitude at least H divided by three times x times the quotient gcd. This is used in the proof of Proposition 3.1 of the paper.
-/
theorem actualPivotLower (η : ℚ) (hη : _root_.AbcTwoNinths.Statement.admissibleEta η)
    (κ : ℝ) (hκ : 0 < κ) (t : _root_.AbcTwoNinths.Basic.Triple)
    (hab : t.a ≤ t.b) (hh : _root_.AbcTwoNinths.Statement.High η 0 t) (hf : ¬ _root_.AbcTwoNinths.Statement.RealContactBound κ t) :
    ∃ (w : _root_.AbcTwoNinths.Basic.supp t → ℤ) (r : _root_.AbcTwoNinths.Basic.supp t),
      _root_.AbcTwoNinths.Basic.PrimitiveIn ⊤ w ∧
      (∀ i, _root_.AbcTwoNinths.ExteriorE1.quotientVec t i = (_root_.AbcTwoNinths.ExteriorE1.quotientGcd t : ℤ) * w i) ∧
      (∀ i, |w i| ≤ |w r|) ∧
      t.logHeight / ((_root_.AbcTwoNinths.ExteriorE1.quotientGcd t : ℝ) * (3 * t.thirdLogRadical)) ≤ |(w r : ℝ)| := by
  classical
  obtain ⟨hrank, hg, _⟩ := _root_.AbcTwoNinths.ExteriorE1.orderedFailureInputs η hη κ hκ t hab hh hf
  have : Nonempty (_root_.AbcTwoNinths.Basic.supp t) := by
    obtain ⟨i, hi⟩ := Finset.card_pos.mp (show 0 < (_root_.AbcTwoNinths.Basic.supp t).card by omega)
    exact ⟨⟨i, hi⟩⟩
  obtain ⟨w, hw⟩ := _root_.AbcTwoNinths.ExteriorE1.quotientFromGcd t
  let a : _root_.AbcTwoNinths.Basic.supp t → ℝ := fun i => Real.log (i.val : ℝ)
  have ha (i : _root_.AbcTwoNinths.Basic.supp t) : 0 < a i := by
    apply Real.log_pos
    exact_mod_cast (_root_.AbcTwoNinths.Basic.suppPrime t i.property).one_lt
  have hH : t.logHeight ≤ ∑ i, a i * |(_root_.AbcTwoNinths.ExteriorE1.quotientVec t i : ℝ)| := by
    rw [_root_.AbcTwoNinths.ExteriorE1.quotientSignedHeight t]
    exact _root_.AbcTwoNinths.ExteriorE1.signedHeightLeWeightedAbs a _ fun i => (ha i).le
  obtain ⟨r, hr, _, hlow⟩ := _root_.AbcTwoNinths.ExteriorE1.existsPivot a (_root_.AbcTwoNinths.ExteriorE1.quotientVec t) w (_root_.AbcTwoNinths.ExteriorE1.quotientGcd t : ℤ)
    (by exact_mod_cast hg.ne') ha hw t.logHeight hH
  have hgR : 0 < (_root_.AbcTwoNinths.ExteriorE1.quotientGcd t : ℝ) := by exact_mod_cast hg
  push_cast at hlow
  rw [abs_of_pos hgR] at hlow
  have hsum : 0 < ∑ i, a i := Finset.sum_pos (fun i _ => ha i) Finset.univ_nonempty
  have hx : 0 < 3 * t.thirdLogRadical := hsum.trans_le (_root_.AbcTwoNinths.ExteriorE1.quotientSupportWeight t)
  refine ⟨w, r, _root_.AbcTwoNinths.ExteriorE1.quotientPrimitive t w hw, hw, hr,
    (div_le_iff₀ (mul_pos hgR hx)).mpr ?_⟩
  exact ((div_le_iff₀ (mul_pos hgR hsum)).mp hlow).trans
    (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (_root_.AbcTwoNinths.ExteriorE1.quotientSupportWeight t) hgR.le)
      (abs_nonneg _))

end

end AbcTwoNinths.ExteriorE1
