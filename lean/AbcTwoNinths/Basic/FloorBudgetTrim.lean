/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruiyi Zhang
-/

module

public import AbcTwoNinths.Basic.GreedyTrim

/-!
# Floor Budget Trim

The module trims an integer budget while tracking the loss introduced by taking floors.

## Main results
* `AbcTwoNinths.Basic.floorBudgetTrim`
-/

@[expose] public section


namespace AbcTwoNinths.Basic

section

/--
A divisor meeting the logarithmic budget yields a modulus whose prescribed power divides the ambient integer and whose logarithm lies between half and all of the budget.
-/
theorem floorBudgetTrim {A n L : ℕ} {B : ℝ}
    (hn : 0 < n) (hnA : n ∣ A) (hL : 0 < L)
    (hfour : Real.log (4 : ℝ) ≤ B)
    (hcap : ∀ q ∈ n.primeFactors, Real.log (q : ℝ) ≤ B)
    (hbudget : B ≤ Real.log (n : ℝ) / L -
      ∑ q ∈ n.primeFactors, Real.log (q : ℝ)) :
    ∃ M : ℕ, 2 ≤ M ∧ M ^ L ∣ A ∧ (¬ 2 ∣ M ∨ 4 ∣ M) ∧
      B / 2 ≤ Real.log (M : ℝ) ∧ Real.log (M : ℝ) ≤ B := by
  obtain ⟨M, hM, hdvd, hparity, hlo, hhi⟩ :=
    _root_.AbcTwoNinths.Basic.trimFactorization hn.ne' hL hfour hcap hbudget
  exact ⟨M, hM, hdvd.trans hnA, hparity, hlo, hhi⟩

end

end AbcTwoNinths.Basic
