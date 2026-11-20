/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruiyi Zhang
-/

module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Data.Nat.Factorization.Basic
public import Mathlib.Tactic

/-!
# Separation of a Positive Rational from One

For positive integers `B < C` , the logarithm of `C / B` is at least `1 / C` . This supports
Proposition 3.1 of the paper.

## Main results
* `AbcTwoNinths.ExteriorE1.rationalSeparation`
-/

@[expose] public section


namespace AbcTwoNinths.ExteriorE1

set_option autoImplicit false

section

open Real
open scoped BigOperators

/--
For positive integers B < C, the logarithm of C/B is at least exp(-log C). This is used in the proof of Proposition 3.1 of the paper.
-/
theorem rationalSeparation {B C : ℕ} (hB : 0 < B) (hBC : B < C) :
    exp (-log (C : ℝ)) ≤ log ((C : ℝ) / B) := by
  have hBr : (0 : ℝ) < B := by exact_mod_cast hB
  have hCr : (0 : ℝ) < C := by exact_mod_cast hB.trans hBC
  have hgap : (B : ℝ) + 1 ≤ C := by exact_mod_cast hBC
  have hlog := log_le_sub_one_of_pos (div_pos hBr hCr)
  rw [log_div hBr.ne' hCr.ne'] at hlog
  rw [log_div hCr.ne' hBr.ne', exp_neg, exp_log hCr]
  have hinv : (C : ℝ)⁻¹ ≤ 1 - (B : ℝ) / C := by
    have heq : 1 - (B : ℝ) / C = ((C : ℝ) - B) / C := by
      field_simp
    rw [inv_eq_one_div, heq]
    exact (div_le_div_iff_of_pos_right hCr).2 (by linarith)
  linarith

end

end AbcTwoNinths.ExteriorE1
