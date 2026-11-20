/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruiyi Zhang
-/

module

public import AbcTwoNinths.Paper.S3_ExteriorE1.LogRank
public import AbcTwoNinths.Paper.S3_ExteriorE1.PivotNormalization

/-!
# Triple Rank

The module bounds the rank of the exponent data attached to a primitive triple. It supports Proposition 3.1 of the paper.

## Main results
* `AbcTwoNinths.ExteriorE1.tripleRankBound`
-/

@[expose] public section


namespace AbcTwoNinths.ExteriorE1

section




/-- When `X = t.thirdLogRadical` is at least `exp 4`, the triple's prime support contains
at most `12 * X / log X` primes. -/
theorem tripleRankBound (t : _root_.AbcTwoNinths.Basic.Triple) (hx : Real.exp 4 ≤ t.thirdLogRadical) :
    ((_root_.AbcTwoNinths.Basic.supp t).card : ℝ) ≤ 12 * t.thirdLogRadical / Real.log t.thirdLogRadical := by
  have hxp : 0 < t.thirdLogRadical := (Real.exp_pos _).trans_le hx
  have h3 : t.thirdLogRadical ≤ 3 * t.thirdLogRadical := by linarith
  have hs : (∑ p ∈ _root_.AbcTwoNinths.Basic.supp t, Real.log (p : ℝ)) ≤ 3 * t.thirdLogRadical := by
    have h := _root_.AbcTwoNinths.ExteriorE1.quotientSupportWeight t
    change (∑ i ∈ (_root_.AbcTwoNinths.Basic.supp t).attach, Real.log (i.val : ℝ)) ≤ _ at h
    rwa [Finset.sum_attach (_root_.AbcTwoNinths.Basic.supp t) (fun p => Real.log (p : ℝ))] at h
  have hlog : 4 ≤ Real.log t.thirdLogRadical := by
    simpa using Real.log_le_log (Real.exp_pos 4) hx
  have hh := _root_.AbcTwoNinths.ExteriorE1.rankLeFourWeightDivLog (_root_.AbcTwoNinths.Basic.supp t) (fun _ => _root_.AbcTwoNinths.Basic.suppPrime t)
    (3 * t.thirdLogRadical) (hx.trans h3) hs
  calc
    _ ≤ 4 * (3 * t.thirdLogRadical) / Real.log (3 * t.thirdLogRadical) := hh
    _ ≤ 4 * (3 * t.thirdLogRadical) / Real.log t.thirdLogRadical :=
      div_le_div_of_nonneg_left (by positivity) (by linarith) (Real.log_le_log hxp h3)
    _ = _ := by ring

end

end AbcTwoNinths.ExteriorE1
