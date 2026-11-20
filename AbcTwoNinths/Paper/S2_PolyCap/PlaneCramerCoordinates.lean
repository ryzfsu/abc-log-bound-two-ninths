/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruiyi Zhang
-/

module

public import AbcTwoNinths.Paper.S2_PolyCap.DeterminantHeightProduct

/-!
# Plane Cramer Coordinates

The module gives Cramer's rule for lattice coordinates in an integer basis with unit determinant. It supports Proposition 2.1 of the paper.

## Main results
* `AbcTwoNinths.PolyCap.cramerUnitDet`
-/

@[expose] public section


namespace AbcTwoNinths.PolyCap

section

/-- The cramer a. This is used in the proof of Proposition 2.1 of the paper. -/
def cramerA (w m x : ℤ × ℤ) : ℤ := _root_.AbcTwoNinths.PolyCap.det2 w m * _root_.AbcTwoNinths.PolyCap.det2 x m
/-- The cramer b. This is used in the proof of Proposition 2.1 of the paper. -/
def cramerB (w m x : ℤ × ℤ) : ℤ := _root_.AbcTwoNinths.PolyCap.det2 w m * _root_.AbcTwoNinths.PolyCap.det2 w x

/-- An integer determinant of absolute value one has square one. -/
theorem detSqOfUnit {w m : ℤ × ℤ} (hd : |_root_.AbcTwoNinths.PolyCap.det2 w m| = 1) :
    _root_.AbcTwoNinths.PolyCap.det2 w m * _root_.AbcTwoNinths.PolyCap.det2 w m = 1 := by
  have he : _root_.AbcTwoNinths.PolyCap.det2 w m = 1 ∨ _root_.AbcTwoNinths.PolyCap.det2 w m = -1 := by
    rcases abs_choice (_root_.AbcTwoNinths.PolyCap.det2 w m) with h | h <;> omega
  rcases he with h | h <;> norm_num [h]

/-- For a unimodular integer pair, the Cramer coefficients recover both coordinates of any integer vector. -/
theorem cramerCoordinates {w m : ℤ × ℤ} (hd : |_root_.AbcTwoNinths.PolyCap.det2 w m| = 1) (x : ℤ × ℤ) :
    _root_.AbcTwoNinths.PolyCap.cramerA w m x * w.1 + _root_.AbcTwoNinths.PolyCap.cramerB w m x * m.1 = x.1 ∧
    _root_.AbcTwoNinths.PolyCap.cramerA w m x * w.2 + _root_.AbcTwoNinths.PolyCap.cramerB w m x * m.2 = x.2 := by
  have h := _root_.AbcTwoNinths.PolyCap.detSqOfUnit hd
  simp only [_root_.AbcTwoNinths.PolyCap.cramerA, _root_.AbcTwoNinths.PolyCap.cramerB, _root_.AbcTwoNinths.PolyCap.det2] at *
  constructor
  · linear_combination x.1 * h
  · linear_combination x.2 * h

/-- In real coordinates, an integer vector is the linear combination of the unimodular pair given
by its integer Cramer coefficients. -/
theorem cramerReal {w m : ℤ × ℤ} (hd : |_root_.AbcTwoNinths.PolyCap.det2 w m| = 1) (x : ℤ × ℤ) :
    _root_.AbcTwoNinths.PolyCap.realPair x = (_root_.AbcTwoNinths.PolyCap.cramerA w m x : ℝ) • _root_.AbcTwoNinths.PolyCap.realPair w + (_root_.AbcTwoNinths.PolyCap.cramerB w m x : ℝ) • _root_.AbcTwoNinths.PolyCap.realPair m := by
  obtain ⟨h₁, h₂⟩ := _root_.AbcTwoNinths.PolyCap.cramerCoordinates hd x
  apply Prod.ext
  · change (x.1 : ℝ) = (_root_.AbcTwoNinths.PolyCap.cramerA w m x : ℝ) * w.1 + (_root_.AbcTwoNinths.PolyCap.cramerB w m x : ℝ) * m.1
    exact_mod_cast h₁.symm
  · change (x.2 : ℝ) = (_root_.AbcTwoNinths.PolyCap.cramerA w m x : ℝ) * w.2 + (_root_.AbcTwoNinths.PolyCap.cramerB w m x : ℝ) * m.2
    exact_mod_cast h₂.symm

/-- The Cramer-coordinate matrix of the two standard basis vectors has determinant of absolute value
one when the original integer basis is unimodular. -/
theorem cramerUnitDet {w m : ℤ × ℤ} (hd : |_root_.AbcTwoNinths.PolyCap.det2 w m| = 1) :
    |_root_.AbcTwoNinths.PolyCap.cramerA w m (1, 0) * _root_.AbcTwoNinths.PolyCap.cramerB w m (0, 1) -
      _root_.AbcTwoNinths.PolyCap.cramerB w m (1, 0) * _root_.AbcTwoNinths.PolyCap.cramerA w m (0, 1)| = 1 := by
  have h := _root_.AbcTwoNinths.PolyCap.detSqOfUnit hd
  have he : _root_.AbcTwoNinths.PolyCap.cramerA w m (1, 0) * _root_.AbcTwoNinths.PolyCap.cramerB w m (0, 1) -
      _root_.AbcTwoNinths.PolyCap.cramerB w m (1, 0) * _root_.AbcTwoNinths.PolyCap.cramerA w m (0, 1) = _root_.AbcTwoNinths.PolyCap.det2 w m := by
    simp only [_root_.AbcTwoNinths.PolyCap.cramerA, _root_.AbcTwoNinths.PolyCap.cramerB, _root_.AbcTwoNinths.PolyCap.det2] at *
    linear_combination (w.1 * m.2 - w.2 * m.1) * h
  rwa [he]

end

end AbcTwoNinths.PolyCap
