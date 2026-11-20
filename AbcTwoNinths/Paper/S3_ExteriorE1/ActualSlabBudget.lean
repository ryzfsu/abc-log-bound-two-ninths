/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruiyi Zhang
-/

module

public import AbcTwoNinths.Paper.S3_ExteriorE1.OnsetPenalty

/-!
# Actual Slab Budget

The module bounds the logarithmic cost of the slab attached to an actual source triple. It supports Proposition 3.1 of the paper.

## Main results
* `AbcTwoNinths.ExteriorE1.actualSlabBudget`
-/

@[expose] public section


namespace AbcTwoNinths.ExteriorE1

section




/-- For a high triple and a pivot size within the given bounds, the explicit slab width
lies between `1 / t.logHeight` and `T`, and the total cell count is less than the pivot size. -/
theorem actualSlabBudget (η : ℚ) (hη : _root_.AbcTwoNinths.Statement.admissibleEta η) (κ : ℝ) (hκ : 0 < κ)
    (t : _root_.AbcTwoNinths.Basic.Triple) (r : _root_.AbcTwoNinths.Basic.supp t) [Nonempty {i : _root_.AbcTwoNinths.Basic.supp t // i ≠ r}]
    (m : ℝ) (hm : 0 < m) (hlo : κ * t.logHeight / (3 * t.thirdLogRadical) ≤ m) (hhi : m ≤ 2 * t.logHeight)
    (hx : Real.exp 4 ≤ t.thirdLogRadical) (hh : Real.exp (_root_.AbcTwoNinths.Statement.highRate η * t.thirdLogRadical) ≤ t.logHeight)
    (hon₁ : Real.exp (192 * Real.log (768 / _root_.AbcTwoNinths.Statement.highRate η) / _root_.AbcTwoNinths.Statement.highRate η) ≤ t.thirdLogRadical)
    (hon₂ : (16 / _root_.AbcTwoNinths.Statement.highRate η) *
      (max 0 (Real.log (9 / κ)) + 2 * Real.log (32 / _root_.AbcTwoNinths.Statement.highRate η)) ≤ t.thirdLogRadical) :
    let T := t.thirdLogRadical / Real.log t.thirdLogRadical
    let d := Fintype.card {i : _root_.AbcTwoNinths.Basic.supp t // i ≠ r}
    let ε := (3 * T / m) * (1 + 3 * Real.log t.thirdLogRadical) ^ d
    1 ≤ T ∧ T ≤ t.logHeight ∧ 0 < ε ∧ ε < T ∧ Real.log t.logHeight / 2 ≤ -Real.log ε ∧
    1 / t.logHeight < ε ∧ (⌈T / ε⌉₊ : ℝ) *
      (∏ i : {i : _root_.AbcTwoNinths.Basic.supp t // i ≠ r},
        (⌈(d : ℝ) * Real.log (i.val.val : ℝ) / T⌉₊ : ℝ)) < m := by
  classical
  let x := t.thirdLogRadical
  let h := _root_.AbcTwoNinths.Statement.highRate η
  let T := x / Real.log x
  let α := {i : _root_.AbcTwoNinths.Basic.supp t // i ≠ r}
  let d := Fintype.card α
  let a : α → ℝ := fun i => Real.log (i.val.val : ℝ)
  let B := 1 + 3 * Real.log x
  have ha (i : α) : 0 < a i := Real.log_pos (by
    exact_mod_cast (_root_.AbcTwoNinths.Basic.suppPrime t i.val.property).one_lt)
  have hh' : (2 : ℝ) / 3 < h := by
    have hη' : (η : ℝ) < 1 / 9 := by
      have hc : (η : ℝ) < (((1 : ℚ) / 9 : ℚ) : ℝ) := Rat.cast_lt.mpr hη.2
      simpa using hc
    dsimp [h, _root_.AbcTwoNinths.Statement.highRate]
    linarith
  have hp : 0 < h := by linarith
  have hxp : 0 < x := (Real.exp_pos _).trans_le hx
  have hy : 4 ≤ Real.log x := by simpa using Real.log_le_log (Real.exp_pos 4) hx
  have hyp : 0 < Real.log x := by linarith
  have hT : 1 ≤ T := (le_div_iff₀ hyp).2 (by
    linarith [Real.log_le_sub_one_of_pos hxp])
  have hTp : 0 < T := by linarith
  have hTx : T ≤ x := (div_le_iff₀ hyp).2 (by nlinarith)
  have hH : 1 < t.logHeight := (Real.one_lt_exp_iff.mpr (mul_pos hp hxp)).trans_le hh
  have hu : h * x ≤ Real.log t.logHeight := by
    simpa using Real.log_le_log (Real.exp_pos (h * x)) hh
  have hx5 : 5 ≤ x := by linarith [Real.log_le_sub_one_of_pos hxp]
  have hTH : T ≤ t.logHeight := by
    have hpow := Real.pow_div_factorial_le_exp ((2 / 3 : ℝ) * x) (by positivity) 2
    norm_num at hpow
    refine hTx.trans ((show x ≤ (2 / 3 * x)^2 / 2 by
      nlinarith [mul_nonneg hxp.le (sub_nonneg.mpr hx5)]).trans
      (hpow.trans ((Real.exp_le_exp.mpr ?_).trans hh)))
    exact mul_le_mul_of_nonneg_right hh'.le hxp.le
  have hd : (d : ℝ) ≤ 12 * x / Real.log x := by
    have hc := Fintype.card_le_of_injective (fun i : α => i.val) Subtype.val_injective
    exact (show (d : ℝ) ≤ ((_root_.AbcTwoNinths.Basic.supp t).card : ℝ) by simpa using (Nat.cast_le (α := ℝ)).mpr hc).trans
      (_root_.AbcTwoNinths.ExteriorE1.tripleRankBound t hx)
  have hsum : (∑ i, a i) ≤ 3 * x := by
    let f : _root_.AbcTwoNinths.Basic.supp t → ℝ := fun i => Real.log (i.val : ℝ)
    have hf (i : _root_.AbcTwoNinths.Basic.supp t) : 0 ≤ f i := Real.log_nonneg (by
      exact_mod_cast (_root_.AbcTwoNinths.Basic.suppPrime t i.property).one_le)
    have hsplit := Fintype.sum_subtype_add_sum_subtype (fun i : _root_.AbcTwoNinths.Basic.supp t => i ≠ r) f
    have hnon : 0 ≤ ∑ i : {i : _root_.AbcTwoNinths.Basic.supp t // ¬ i ≠ r}, f i.val :=
      Finset.sum_nonneg fun i _ => hf i.val
    exact (show (∑ i, a i) ≤ ∑ i, f i by
      change (∑ i : α, f i.val) ≤ _
      rw [← hsplit]
      exact le_add_of_nonneg_right hnon).trans (_root_.AbcTwoNinths.ExteriorE1.quotientSupportWeight t)
  have h₁ := _root_.AbcTwoNinths.ExteriorE1.onsetScalePenalty x h κ hxp hp hκ hon₂
  have h₂ := _root_.AbcTwoNinths.ExteriorE1.onsetRankPenalty x h d hxp hp hy
    (by simpa using Real.log_le_log (Real.exp_pos _) hon₁) hd
  have hpen := _root_.AbcTwoNinths.ExteriorE1.slabPenalty t.logHeight T m B x κ d hH hTp hTx hκ hlo
    (by linarith) (by linarith)
  have hB : 1 ≤ B := by dsimp [B]; linarith
  obtain ⟨he, heT, helog, helo⟩ := _root_.AbcTwoNinths.ExteriorE1.slabLogBudget t.logHeight T m B d hH hT hm hhi hB hpen
  have hrewrite : 1 + 3 * x / T = B := by
    dsimp [T, B]; field_simp [hxp.ne', hyp.ne']
  have hcap := _root_.AbcTwoNinths.ExteriorE1.strictCapacity a ha T (3 * x) m hTp (by positivity) hm hsum
  dsimp only at hcap
  rw [hrewrite] at hcap
  exact ⟨hT, hTH, he, heT, helog, helo, hcap heT⟩

end

end AbcTwoNinths.ExteriorE1
