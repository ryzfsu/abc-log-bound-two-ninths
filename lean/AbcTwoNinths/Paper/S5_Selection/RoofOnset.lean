/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruiyi Zhang
-/

module

public import AbcTwoNinths.Paper.S1_Statement.OrderedTriple

/-!
# Threshold for the selected-prime bounds

The module selects a threshold above which the high-triple inequalities needed for the distinguished prime are available. It supports Proposition 5.1 of the paper.

## Main results
* `AbcTwoNinths.Selection.highThreshold`
-/

@[expose] public section


namespace AbcTwoNinths.Selection

section


/-- For any prescribed height floor, a positive radical threshold ensures that high triples
meet the floor and have positive one-third logarithmic radical. -/
theorem highThreshold {η : ℚ} (he : _root_.AbcTwoNinths.Statement.admissibleEta η) (K : ℝ) :
    ∃ X : ℝ, 0 < X ∧ ∀ t : _root_.AbcTwoNinths.Basic.Triple, _root_.AbcTwoNinths.Statement.High η X t → K ≤ t.logHeight ∧ 0 < t.thirdLogRadical := by
  have he' : (η : ℝ) < 1/9 := by
    have h := (Rat.cast_lt (K := ℝ)).mpr he.2
    norm_num at h ⊢
    exact h
  have hr : 0 < _root_.AbcTwoNinths.Statement.highRate η := by unfold _root_.AbcTwoNinths.Statement.highRate; linarith
  refine ⟨max 1 (K/_root_.AbcTwoNinths.Statement.highRate η), lt_of_lt_of_le zero_lt_one (le_max_left _ _), ?_⟩
  intro t ht
  have hx := (le_max_right 1 (K/_root_.AbcTwoNinths.Statement.highRate η)).trans ht.1
  have hk := (div_le_iff₀ hr).mp hx
  have h := Real.add_one_le_exp (_root_.AbcTwoNinths.Statement.highRate η*t.thirdLogRadical)
  exact ⟨le_trans (by linarith [mul_comm t.thirdLogRadical (_root_.AbcTwoNinths.Statement.highRate η)] : K ≤ Real.exp (_root_.AbcTwoNinths.Statement.highRate η*t.thirdLogRadical)) ht.2,
    lt_of_lt_of_le zero_lt_one ((le_max_left _ _).trans ht.1)⟩

end

end AbcTwoNinths.Selection
