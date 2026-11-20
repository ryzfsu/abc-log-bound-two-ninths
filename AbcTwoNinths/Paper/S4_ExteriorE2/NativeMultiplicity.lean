/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruiyi Zhang
-/

module

public import Mathlib

/-!
# Exponent multiplicity and budget

The module bounds exponent multiplicity in terms of the root data and obtains a strict margin from the exponent budget. It supports Proposition 4.1 of the paper.

## Main results
* `AbcTwoNinths.ExteriorE2.strictMarginOfExponentBudget`
-/

@[expose] public section


namespace AbcTwoNinths.ExteriorE2

section

/--
When the depth lies between `θ * H` and `rootHeight + err` and the error is at most
`θ * H / 2` , the bound `g * rootHeight ≤ 2 * H` gives `g * θ ≤ 4` .
-/
theorem multiplicityOfRootBound {g H θ depth rootHeight err : ℝ}
    (hg : 0 < g) (hH : 0 < H)
    (hshare : θ * H ≤ depth) (hlte : depth ≤ rootHeight + err)
    (hroot : g * rootHeight ≤ 2 * H)
    (herr : err ≤ θ * H / 2) :
    g * θ ≤ 4 := by
  have h₁ : θ * H / 2 ≤ rootHeight := by linarith
  have h₂ := mul_le_mul_of_nonneg_left h₁ hg.le
  apply le_of_mul_le_mul_right _ hH
  nlinarith

/--
A strict exponent budget suffices for the corrected grid inequality. This is used in the proof of Proposition 4.1 of the paper.
-/
theorem strictMarginOfExponentBudget {B g U H Q : ℝ} {d : ℕ}
    (hB : 0 < B) (hg : 0 < g) (hU : 0 < U) (hH : 0 < H) (hQ : 0 < Q)
    {saving : ℝ} (hs : Real.log B ≤ Real.log H - saving)
    (hb : Real.log g + Real.log U + (d : ℝ) * Real.log Q < saving) :
    B * (g * U) < H * (1 / Q) ^ d := by
  rw [one_div_pow, mul_one_div]
  apply (lt_div_iff₀ (pow_pos hQ d)).2
  apply (Real.log_lt_log_iff (by positivity) hH).1
  rw [Real.log_mul (by positivity) (by positivity),
    Real.log_mul hB.ne' (by positivity), Real.log_mul hg.ne' hU.ne', Real.log_pow]
  linarith

end

end AbcTwoNinths.ExteriorE2
