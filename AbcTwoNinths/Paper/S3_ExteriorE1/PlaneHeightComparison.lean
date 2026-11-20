/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruiyi Zhang
-/

module

public import Mathlib

/-!
# Plane Height Comparison

Weighted exponent height defines a continuous seminorm on a real coordinate space. With positive
weights, it controls every coordinate and is positive away from zero. This supports Proposition 3.1
of the paper.

## Main results
* `AbcTwoNinths.ExteriorE1.heightSeminorm`
* `AbcTwoNinths.ExteriorE1.coordLeHeight`
* `AbcTwoNinths.ExteriorE1.heightPosOfNeZero`
-/

@[expose] public section


namespace AbcTwoNinths.ExteriorE1

section

open scoped BigOperators

variable {ι : Type*} [Fintype ι]

/--
The positive weight is the sum of the weighted positive parts of the coordinates. This is used in the proof of Proposition 3.1 of the paper.
-/
def positiveWeight (a y : ι → ℝ) : ℝ := ∑ i, a i * max (y i) 0

/--
The weighted height is the larger of the positive weights of a vector and its negative. This is used in the proof of Proposition 3.1 of the paper.
-/
def height (a y : ι → ℝ) : ℝ := max (_root_.AbcTwoNinths.ExteriorE1.positiveWeight a y) (_root_.AbcTwoNinths.ExteriorE1.positiveWeight a (-y))

/-- Positive weight is subadditive for nonnegative coordinate weights. -/
theorem positiveWeightAddLe (a : ι → ℝ) (ha : ∀ i, 0 ≤ a i) (x y : ι → ℝ) :
    _root_.AbcTwoNinths.ExteriorE1.positiveWeight a (x + y) ≤ _root_.AbcTwoNinths.ExteriorE1.positiveWeight a x + _root_.AbcTwoNinths.ExteriorE1.positiveWeight a y := by
  unfold _root_.AbcTwoNinths.ExteriorE1.positiveWeight
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro i _
  rw [← mul_add]
  refine mul_le_mul_of_nonneg_left (max_le ?_ ?_) (ha i)
  · exact add_le_add (le_max_left _ _) (le_max_left _ _)
  · exact add_nonneg (le_max_right _ _) (le_max_right _ _)

/-- Nonnegative real scaling multiplies the positive weight by the same scalar. -/
theorem positiveWeightSmul (a : ι → ℝ) (c : ℝ) (hc : 0 ≤ c) (y : ι → ℝ) :
    _root_.AbcTwoNinths.ExteriorE1.positiveWeight a (c • y) = c * _root_.AbcTwoNinths.ExteriorE1.positiveWeight a y := by
  unfold _root_.AbcTwoNinths.ExteriorE1.positiveWeight
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  change a i * max (c * y i) 0 = _
  rw [show (0 : ℝ) = c * 0 from (mul_zero c).symm, ← mul_max_of_nonneg _ _ hc]
  ring

/--
Nonnegative weights define a seminorm on the finite real coordinate space. This is used in the proof of Proposition 3.1 of the paper.
-/
noncomputable def heightSeminorm (a : ι → ℝ) (ha : ∀ i, 0 ≤ a i) :
    Seminorm ℝ (ι → ℝ) :=
  Seminorm.of (_root_.AbcTwoNinths.ExteriorE1.height a) (by
    intro x y
    unfold _root_.AbcTwoNinths.ExteriorE1.height
    rw [neg_add]
    exact max_le ((_root_.AbcTwoNinths.ExteriorE1.positiveWeightAddLe a ha x y).trans
      (add_le_add (le_max_left _ _) (le_max_left _ _)))
      ((_root_.AbcTwoNinths.ExteriorE1.positiveWeightAddLe a ha (-x) (-y)).trans
        (add_le_add (le_max_right _ _) (le_max_right _ _))))
    (by
      intro c y
      have key (d : ℝ) (hd : 0 ≤ d) (z : ι → ℝ) :
          _root_.AbcTwoNinths.ExteriorE1.height a (d • z) = d * _root_.AbcTwoNinths.ExteriorE1.height a z := by
        unfold _root_.AbcTwoNinths.ExteriorE1.height
        rw [← smul_neg, _root_.AbcTwoNinths.ExteriorE1.positiveWeightSmul a d hd, _root_.AbcTwoNinths.ExteriorE1.positiveWeightSmul a d hd,
          mul_max_of_nonneg _ _ hd]
      rw [Real.norm_eq_abs]
      rcases le_total 0 c with hc | hc
      · rw [abs_of_nonneg hc, key c hc]
      · rw [abs_of_nonpos hc, show c • y = (-c) • (-y) by simp, key (-c) (neg_nonneg.mpr hc)]
        simp [_root_.AbcTwoNinths.ExteriorE1.height, max_comm])

/-- The weighted height seminorm is continuous. -/
theorem heightContinuous (a : ι → ℝ) (ha : ∀ i, 0 ≤ a i) :
    Continuous (_root_.AbcTwoNinths.ExteriorE1.heightSeminorm a ha) := by
  change Continuous (fun y : ι → ℝ => _root_.AbcTwoNinths.ExteriorE1.height a y)
  unfold _root_.AbcTwoNinths.ExteriorE1.height _root_.AbcTwoNinths.ExteriorE1.positiveWeight
  fun_prop

/-- The weighted absolute value of each coordinate is at most the weighted height. -/
theorem coordLeHeight (a : ι → ℝ) (ha : ∀ i, 0 ≤ a i) (y : ι → ℝ) (i : ι) :
    a i * |y i| ≤ _root_.AbcTwoNinths.ExteriorE1.height a y := by
  classical
  rw [abs_eq_max_neg, mul_max_of_nonneg _ _ (ha i)]
  have h (z : ι → ℝ) : a i * z i ≤ _root_.AbcTwoNinths.ExteriorE1.positiveWeight a z :=
    (mul_le_mul_of_nonneg_left (le_max_left _ 0) (ha i)).trans
      (Finset.single_le_sum (fun j _ => mul_nonneg (ha j) (le_max_right _ 0))
        (Finset.mem_univ i))
  exact max_le ((h y).trans (le_max_left _ _)) ((h (-y)).trans (le_max_right _ _))

/--
Strictly positive weights give positive height to each nonzero vector. This is used in the proof of Proposition 3.1 of the paper.
-/
theorem heightPosOfNeZero (a : ι → ℝ) (ha : ∀ i, 0 < a i)
    (y : ι → ℝ) (hy : y ≠ 0) :
    0 < _root_.AbcTwoNinths.ExteriorE1.heightSeminorm a (fun i => (ha i).le) y := by
  have hx : ∃ i, y i ≠ 0 := by
    by_contra! hz
    exact hy (funext hz)
  obtain ⟨i, hi⟩ := hx
  change 0 < _root_.AbcTwoNinths.ExteriorE1.height a y
  exact (mul_pos (ha i) (abs_pos.mpr hi)).trans_le (_root_.AbcTwoNinths.ExteriorE1.coordLeHeight a (fun j => (ha j).le) y i)

end

end AbcTwoNinths.ExteriorE1
