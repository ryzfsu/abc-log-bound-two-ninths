/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruiyi Zhang
-/

module

public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Tactic

/-!
# Rational Exponent Parameters

For every positive real epsilon, a positive rational parameter below epsilon gives an exponent
`1/3 - eta` below `2/9 + epsilon` . This supports Theorem 1.1 of the paper.

## Main results
* `AbcTwoNinths.Statement.etaOf`
* `AbcTwoNinths.Statement.realEpsilonRationalParameters`
-/

@[expose] public section

namespace AbcTwoNinths.Statement

section

/--
The rational exponent parameter of Table 1 for a positive rational tolerance. This is used in the proof of Theorem 1.1 of the paper.
-/
def etaOf (epsilon : ℚ) : ℚ := 1 / 9 - min (epsilon / 2) (1 / 18)

/--
The chosen parameter lies strictly between zero and one ninth and gives the required exponent inequality.
-/
theorem etaOfSpec {epsilon : ℚ} (he : 0 < epsilon) :
    0 < _root_.AbcTwoNinths.Statement.etaOf epsilon ∧ _root_.AbcTwoNinths.Statement.etaOf epsilon < 1/9 ∧
    1/3 - _root_.AbcTwoNinths.Statement.etaOf epsilon < 2/9 + epsilon := by
  unfold _root_.AbcTwoNinths.Statement.etaOf
  have hp : 0 < min (epsilon / 2) (1 / 18 : ℚ) := lt_min (by linarith) (by norm_num)
  have h₁ := min_le_left (epsilon / 2) (1 / 18 : ℚ)
  have h₂ := min_le_right (epsilon / 2) (1 / 18 : ℚ)
  exact ⟨by linarith, by linarith, by linarith⟩

/--
Every positive real tolerance admits a smaller positive rational tolerance whose parameter gives the required exponent. This is used in the proof of Theorem 1.1 of the paper.
-/
theorem realEpsilonRationalParameters {epsilon : ℝ} (he : 0 < epsilon) :
    ∃ e : ℚ, 0 < e ∧ (e : ℝ) < epsilon ∧ 0 < _root_.AbcTwoNinths.Statement.etaOf e ∧ _root_.AbcTwoNinths.Statement.etaOf e < 1/9 ∧
      1/3 - (_root_.AbcTwoNinths.Statement.etaOf e : ℝ) < 2/9 + epsilon := by
  obtain ⟨e, h0, he'⟩ := exists_rat_btwn he
  have hep : 0 < e := by exact_mod_cast h0
  obtain ⟨ha, hb, hc⟩ := _root_.AbcTwoNinths.Statement.etaOfSpec hep
  have hcast := (Rat.cast_lt (K := ℝ)).2 hc
  push_cast at hcast
  exact ⟨e, hep, he', ha, hb, by linarith⟩

end

end AbcTwoNinths.Statement
