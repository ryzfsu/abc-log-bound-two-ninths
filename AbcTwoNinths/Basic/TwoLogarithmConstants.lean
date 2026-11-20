/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruiyi Zhang
-/

module

public import Mathlib

/-!
# Two Logarithm Constants

The module bounds interpolation orders, grid dimensions, and the cost of the grid edges.

## Main results
* `AbcTwoNinths.Basic.contradiction`
-/

@[expose] public section

namespace AbcTwoNinths.Basic

section

/-- The interpolation order is the natural ceiling of 400 times the height product. -/
noncomputable def order (A : ℝ) : ℕ := ⌈400 * A⌉₊
/-- The interpolation grid uses 36 levels. -/
def levels : ℕ := 36
/-- The row count at order J is the number of levels times J + 1. -/
def rows (J : ℕ) : ℕ := (J+1)*_root_.AbcTwoNinths.Basic.levels

/--
The rectangle edge is the natural floor of the square root of the weighted aspect ratio times the requested size.
-/
noncomputable def edge (q : ℕ) (a b : ℝ) : ℕ := ⌊Real.sqrt (q*a/b)⌋₊

/-- The integral edge is at most its unrounded square root. -/
theorem edgeLe (q : ℕ) (a b : ℝ) :
    (_root_.AbcTwoNinths.Basic.edge q a b : ℝ) ≤ Real.sqrt (q*a/b) :=
  Nat.floor_le (Real.sqrt_nonneg _)

/-- The rectangle with both endpoints included contains more points than the prescribed size. -/
theorem rectCard (q : ℕ) (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    q < (_root_.AbcTwoNinths.Basic.edge q a b+1)*(_root_.AbcTwoNinths.Basic.edge q b a+1) := by
  have h₁ : Real.sqrt (q*a/b) < (_root_.AbcTwoNinths.Basic.edge q a b : ℝ)+1 := Nat.lt_floor_add_one _
  have h₂ : Real.sqrt (q*b/a) < (_root_.AbcTwoNinths.Basic.edge q b a : ℝ)+1 := Nat.lt_floor_add_one _
  have hq : 0 ≤ (q : ℝ) := by positivity
  have he : Real.sqrt (q*a/b) * Real.sqrt (q*b/a) = q := by
    rw [← Real.sqrt_mul (by positivity)]
    have h : (q*a/b)*(q*b/a) = (q : ℝ)^2 := by field_simp
    rw [h, Real.sqrt_sq hq]
  exact_mod_cast he ▸ (mul_lt_mul'' h₁ h₂ (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))

/--
For height product A at least one, the order lies between 400A and 401A and the row count is at most 14472A.
-/
theorem orderBounds (A : ℝ) (hA : 1 ≤ A) :
    400*A ≤ (_root_.AbcTwoNinths.Basic.order A : ℝ) ∧ (_root_.AbcTwoNinths.Basic.order A : ℝ) ≤ 401*A ∧ (_root_.AbcTwoNinths.Basic.rows (_root_.AbcTwoNinths.Basic.order A) : ℝ) ≤ 14472*A := by
  have h₁ : 400*A ≤ (_root_.AbcTwoNinths.Basic.order A : ℝ) := Nat.le_ceil _
  have h₂ : (_root_.AbcTwoNinths.Basic.order A : ℝ) < 400*A+1 := Nat.ceil_lt_add_one (by linarith)
  refine ⟨h₁, by linarith, ?_⟩
  simp [_root_.AbcTwoNinths.Basic.rows, _root_.AbcTwoNinths.Basic.levels]
  linarith

/--
Multiplying an edge by its opposite weight gives at most the square root of the size times the product of the weights.
-/
theorem edgeCost (q : ℕ) (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    (_root_.AbcTwoNinths.Basic.edge q a b : ℝ)*b ≤ Real.sqrt (q*(a*b)) := by
  calc
    _ ≤ Real.sqrt (q*a/b)*b := mul_le_mul_of_nonneg_right (_root_.AbcTwoNinths.Basic.edgeLe q a b) hb.le
    _ = _ := by
      calc
        Real.sqrt (q*a/b)*b = Real.sqrt (q*a/b)*Real.sqrt (b^2) := by rw [Real.sqrt_sq hb.le]
        _ = _ := ?_
      rw [← Real.sqrt_mul (by positivity)]
      congr 1
      field_simp

/--
The sum of the two grid square roots is at most 127A when A is at least one and the order is at most 401A.
-/
theorem sqrtBudget (A J : ℝ) (hA : 1 ≤ A) (hJ : J ≤ 401*A) :
    Real.sqrt (36*A) + Real.sqrt (36*J*A) ≤ 127*A := by
  have h₁ : Real.sqrt (36*A) ≤ 6*A := by
    apply (Real.sqrt_le_iff).2
    exact ⟨by linarith, by nlinarith [mul_nonneg (show 0 ≤ A-1 by linarith) (show 0 ≤ A by linarith)]⟩
  have h₂ : Real.sqrt (36*J*A) ≤ 121*A := by
    apply (Real.sqrt_le_iff).2
    exact ⟨by linarith, by nlinarith [mul_nonneg (show 0 ≤ 401*A-J by linarith) (show 0 ≤ A by linarith), sq_nonneg A]⟩
  linarith

/-- The coordinate allowance is the sum of the two interpolation edges. -/
noncomputable def maxCoord (a b : ℝ) : ℕ :=
  _root_.AbcTwoNinths.Basic.edge _root_.AbcTwoNinths.Basic.levels a b + _root_.AbcTwoNinths.Basic.edge (_root_.AbcTwoNinths.Basic.order (a*b)*_root_.AbcTwoNinths.Basic.levels) a b

/-- The coordinate allowance times its opposite weight is at most 127 times the weight product. -/
theorem maxCoordCost (a b : ℝ) (ha : 1 ≤ a) (hb : 1 ≤ b) :
    (_root_.AbcTwoNinths.Basic.maxCoord a b : ℝ)*b ≤ 127*(a*b) := by
  have hA : 1 ≤ a*b := by nlinarith [mul_nonneg (show 0 ≤ a-1 by linarith) (show 0 ≤ b-1 by linarith)]
  obtain ⟨_, hj, _⟩ := _root_.AbcTwoNinths.Basic.orderBounds (a*b) hA
  have h1 := _root_.AbcTwoNinths.Basic.edgeCost _root_.AbcTwoNinths.Basic.levels a b (by linarith) (by linarith)
  have h2 := _root_.AbcTwoNinths.Basic.edgeCost (_root_.AbcTwoNinths.Basic.order (a*b)*_root_.AbcTwoNinths.Basic.levels) a b (by linarith) (by linarith)
  have hh := _root_.AbcTwoNinths.Basic.sqrtBudget (a*b) (_root_.AbcTwoNinths.Basic.order (a*b) : ℝ) hA hj
  simp only [_root_.AbcTwoNinths.Basic.levels, Nat.cast_ofNat, Nat.cast_mul] at h1 h2
  rw [mul_comm (_root_.AbcTwoNinths.Basic.order (a*b) : ℝ) 36] at h2
  simp only [_root_.AbcTwoNinths.Basic.maxCoord, _root_.AbcTwoNinths.Basic.levels, Nat.cast_add, add_mul]
  linarith

/--
The assumed strict determinant inequality contradicts the order, height and logarithmic bounds.
-/
theorem contradiction (A ell U M W : ℝ) (hA : 1 ≤ A) (hell : 1 < ell)
    (hU : 0 < U) (hM : 0 < M) (hlog : Real.log U + 1 ≤ 15*ell)
    (hm : M ≤ (127*A)*U) (hw : W ≤ 127*A)
    (hdet : ((_root_.AbcTwoNinths.Basic.order A : ℝ)+1)*35 <
       2*Real.log (_root_.AbcTwoNinths.Basic.rows (_root_.AbcTwoNinths.Basic.order A))/ell +
       (_root_.AbcTwoNinths.Basic.order A : ℝ)*(2+Real.log (M/(_root_.AbcTwoNinths.Basic.order A : ℝ)))/ell + 36*W) : False := by
  obtain ⟨hj₁,hj₂,hn⟩ := _root_.AbcTwoNinths.Basic.orderBounds A hA
  have hej : 0 < (_root_.AbcTwoNinths.Basic.order A : ℝ) := by linarith
  have hen : 0 < (_root_.AbcTwoNinths.Basic.rows (_root_.AbcTwoNinths.Basic.order A) : ℝ) := by simp [_root_.AbcTwoNinths.Basic.rows, _root_.AbcTwoNinths.Basic.levels]; positivity
  have hMratio : M/(_root_.AbcTwoNinths.Basic.order A : ℝ) < U := by
    apply (div_lt_iff₀ hej).2
    exact hm.trans_lt (by
      rw [mul_comm U]
      exact mul_lt_mul_of_pos_right (show 127*A < (_root_.AbcTwoNinths.Basic.order A : ℝ) by linarith) hU)
  have hLogM := Real.log_lt_log (div_pos hM hej) hMratio
  have hCross : (2+Real.log (M/(_root_.AbcTwoNinths.Basic.order A : ℝ)))/ell < 16 := by
    apply (div_lt_iff₀ (by linarith : 0 < ell)).2
    linarith
  have hCross' := mul_lt_mul_of_pos_left hCross hej
  have he : Real.log (14472 : ℝ) < 11 := by
    apply (Real.log_lt_iff_lt_exp (by norm_num)).2
    have h : (5/2 : ℝ) < Real.exp 1 := by linarith [Real.exp_one_gt_d9]
    calc
      (14472 : ℝ) < (5/2)^11 := by norm_num
      _ ≤ (Real.exp 1)^11 := pow_le_pow_left₀ (by norm_num) h.le 11
      _ = _ := by rw [← Real.exp_nat_mul]; norm_num
  have hA0 : 0 < A := by linarith
  have hLogN : Real.log (_root_.AbcTwoNinths.Basic.rows (_root_.AbcTwoNinths.Basic.order A)) < 11*A := by
    have h := Real.log_le_log hen hn
    rw [Real.log_mul (by norm_num : (14472 : ℝ) ≠ 0) hA0.ne'] at h
    linarith [Real.log_le_sub_one_of_pos hA0]
  have hFirst : 2*Real.log (_root_.AbcTwoNinths.Basic.rows (_root_.AbcTwoNinths.Basic.order A))/ell < 22*A := by
    apply (div_lt_iff₀ (by linarith : 0 < ell)).2
    nlinarith [mul_nonneg hA0.le (show 0 ≤ ell-1 by linarith)]
  have hCross'' : (_root_.AbcTwoNinths.Basic.order A : ℝ)*(2+Real.log (M/(_root_.AbcTwoNinths.Basic.order A : ℝ)))/ell <
      (_root_.AbcTwoNinths.Basic.order A : ℝ)*16 := by simpa [mul_div_assoc] using hCross'
  linarith

end

end AbcTwoNinths.Basic
