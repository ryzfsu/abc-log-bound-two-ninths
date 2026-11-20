/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruiyi Zhang
-/

module

public import AbcTwoNinths.Paper.S4_ExteriorE2.ResidueImageCardinality

/-!
# Bounded Support Dimension

The module converts source support bounds into a dimension bound for the residue lattice. It supports Proposition 4.1 of the paper.

## Main results
* `AbcTwoNinths.ExteriorE2.nativeSupportDimension`
-/

@[expose] public section


namespace AbcTwoNinths.ExteriorE2

section

/--
For `x = t.thirdLogRadical > 1` , any subset of the prime divisors of `abc` has size at most
`sqrt x + 1 + 6 * x / log x` .
-/
theorem nativeSupportDimension (t : _root_.AbcTwoNinths.Basic.Triple) (S : Finset ℕ)
    (hS : S ⊆ (t.a * t.b * t.c).primeFactors) (hx : 1 < t.thirdLogRadical) :
    (S.card : ℝ) ≤ Real.sqrt t.thirdLogRadical + 1 + 6 * t.thirdLogRadical / Real.log t.thirdLogRadical := by
  let N := ⌈Real.sqrt t.thirdLogRadical⌉₊
  have hs : 1 < Real.sqrt t.thirdLogRadical := by
    exact (Real.lt_sqrt (by norm_num)).2 (by simpa using hx)
  have hNlo : Real.sqrt t.thirdLogRadical ≤ (N : ℝ) := Nat.le_ceil _
  have hNhi : (N : ℝ) ≤ Real.sqrt t.thirdLogRadical + 1 :=
    (Nat.ceil_lt_add_one (by positivity : 0 ≤ Real.sqrt t.thirdLogRadical)).le
  have hN : 1 < N := by exact_mod_cast (hs.trans_le hNlo)
  have hlog := Real.log_le_log (by linarith : 0 < Real.sqrt t.thirdLogRadical) hNlo
  rw [Real.log_sqrt (by linarith : 0 ≤ t.thirdLogRadical)] at hlog
  have hpos : 0 < Real.log t.thirdLogRadical := Real.log_pos hx
  have hdiv : 3 * t.thirdLogRadical / Real.log (N : ℝ) ≤ 6 * t.thirdLogRadical / Real.log t.thirdLogRadical := by
    calc
      _ ≤ 3 * t.thirdLogRadical / (Real.log t.thirdLogRadical / 2) :=
        div_le_div_of_nonneg_left (by linarith) (by positivity) hlog
      _ = _ := by ring
  exact (_root_.AbcTwoNinths.ExteriorE2.nativeSupportCardByLogMass t S hS N hN).trans (add_le_add hNhi hdiv)

end

end AbcTwoNinths.ExteriorE2
