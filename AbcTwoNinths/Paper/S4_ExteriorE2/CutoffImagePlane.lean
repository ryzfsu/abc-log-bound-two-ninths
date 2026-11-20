/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruiyi Zhang
-/

module

public import AbcTwoNinths.Paper.S4_ExteriorE2.GridCost
public import AbcTwoNinths.Paper.S4_ExteriorE2.CutoffResidueImageBound
public import AbcTwoNinths.Paper.S4_ExteriorE2.ModulusExclusionReduction

/-!
# Uniform cutoff grid bound

Shows that for fixed grid width the logarithmic grid cost is eventually smaller than any
prescribed positive multiple of one third of the logarithm of the radical. It supports
Proposition 4.1 of the paper.

## Main results
* `AbcTwoNinths.ExteriorE2.eventualConstantGridCost`
-/

@[expose] public section


namespace AbcTwoNinths.ExteriorE2

open Filter

section




/--
For fixed `Q` and positive `σ` , the logarithmic grid cost
`log (4 / θ) + log U + S.card * log Q` is less than `σ * t.thirdLogRadical` for sufficiently
large `t.thirdLogRadical` , uniformly over the stated supports and scales.
-/
theorem eventualConstantGridCost (Q : ℕ) {θ σ : ℝ} (hσ : 0 < σ) :
    ∃ X : ℝ, ∀ t : _root_.AbcTwoNinths.Basic.Triple, X ≤ t.thirdLogRadical →
      ∀ S : Finset ℕ, S ⊆ (t.a * t.b * t.c).primeFactors →
        ∀ U : ℝ, 0 < U → U ≤ 3 * t.thirdLogRadical →
          Real.log (4 / θ) + Real.log U + (S.card : ℝ) * Real.log Q < σ * t.thirdLogRadical := by
  obtain ⟨X, hX⟩ := _root_.AbcTwoNinths.ExteriorE2.eventualE2GridCost (θ := θ) hσ
  obtain ⟨Y, hY⟩ := eventually_atTop.1
    (Real.tendsto_log_atTop.eventually (eventually_ge_atTop (Q : ℝ)))
  refine ⟨max X Y, fun t ht S hS U hU hUhi => ?_⟩
  have hy := hY t.thirdLogRadical ((le_max_right _ _).trans ht)
  have hbase := hX t ((le_max_left _ _).trans ht) S hS U hU hUhi
  rcases Nat.eq_zero_or_pos Q with rfl | hQ
  · have hn : 1 ≤ ((⌈3 * Real.log t.thirdLogRadical⌉₊ + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_pos _
    have hz := mul_nonneg (Nat.cast_nonneg S.card) (Real.log_nonneg hn)
    simp only [Nat.cast_zero, Real.log_zero, mul_zero, add_zero]
    linarith
  · have hq : (Q : ℝ) ≤ ((⌈3 * Real.log t.thirdLogRadical⌉₊ + 1 : ℕ) : ℝ) := by
      push_cast
      linarith [Nat.le_ceil (3 * Real.log t.thirdLogRadical), show (0 : ℝ) ≤ Q by positivity]
    have hl := Real.log_le_log (by exact_mod_cast hQ) hq
    linarith [mul_le_mul_of_nonneg_left hl (Nat.cast_nonneg S.card)]

end

end AbcTwoNinths.ExteriorE2
