/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruiyi Zhang
-/

module

public import AbcTwoNinths.Paper.S4_ExteriorE2.ModulusSelection
public import AbcTwoNinths.Paper.S1_Statement.LeastRadicalSide

/-!
# Height threshold

Raises the radical threshold so that a triple in the high range exceeds a prescribed logarithmic
height. It supports Proposition 4.1 of the paper.

## Main results
* `AbcTwoNinths.ExteriorE2.enlargeHighForHeight`
-/

@[expose] public section


namespace AbcTwoNinths.ExteriorE2

section




/--
Enlarging the threshold for high triples enforces any fixed lower bound on their height. This is used in the proof of Proposition 4.1 of the paper.
-/
theorem enlargeHighForHeight {η : ℚ} (hη : _root_.AbcTwoNinths.Statement.admissibleEta η) (X B : ℝ) :
    ∃ Y : ℝ, 0 ≤ Y ∧ X ≤ Y ∧ ∀ t : _root_.AbcTwoNinths.Basic.Triple, _root_.AbcTwoNinths.Statement.High η Y t → _root_.AbcTwoNinths.Statement.High η X t ∧ B ≤ t.logHeight := by
  have hη' : (η : ℝ) < 1 / 9 := by
    have hq := (Rat.cast_lt (K := ℝ)).2 hη.2
    simpa only [Rat.cast_div, Rat.cast_one, Rat.cast_ofNat] using hq
  have hrate : 0 < _root_.AbcTwoNinths.Statement.highRate η := by unfold _root_.AbcTwoNinths.Statement.highRate; linarith
  let Y := max (max 0 X) (Real.log (max 1 B) / _root_.AbcTwoNinths.Statement.highRate η)
  have hY0 : 0 ≤ Y := (le_max_left 0 X).trans (le_max_left _ _)
  have hYX : X ≤ Y := (le_max_right 0 X).trans (le_max_left _ _)
  refine ⟨Y, hY0, hYX, ?_⟩
  intro t h
  refine ⟨⟨hYX.trans h.1, h.2⟩, ?_⟩
  have hle : Real.log (max 1 B) / _root_.AbcTwoNinths.Statement.highRate η ≤ t.thirdLogRadical :=
    (le_max_right (max 0 X) _).trans h.1
  have hlog := (div_le_iff₀ hrate).mp hle
  have hexp := Real.exp_le_exp.mpr hlog
  rw [Real.exp_log (lt_of_lt_of_le zero_lt_one (le_max_left 1 B)), mul_comm] at hexp
  exact (le_max_right 1 B).trans (hexp.trans h.2)

end

end AbcTwoNinths.ExteriorE2
