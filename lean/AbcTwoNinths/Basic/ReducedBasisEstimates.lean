/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruiyi Zhang
-/

module

public import Mathlib

/-!
# Reduced Basis Estimates

The module compares rounded minima and determinants with the distance to a primitive line.

## Main results
* `AbcTwoNinths.Basic.detAreaComparison`
-/

@[expose] public section


namespace AbcTwoNinths.Basic

section

/--
A lower bound for distance to the first basis line bounds the seminorm of every linear combination from below.
-/
theorem quotientLb {E : Type*} [AddCommGroup E] [Module ℝ E]
    (f : Seminorm ℝ E) (w z : E) (t : ℝ)
    (hmin : ∀ q : ℝ, t ≤ f (z - q • w)) (a b : ℝ) :
    |b| * t ≤ f (a • w + b • z) := by
  by_cases hb : b = 0
  · simp [hb]
  have hvec : a • w + b • z = b • (z - (-a / b) • w) := by
    rw [smul_sub, smul_smul]
    have he : b * (-a / b) = -a := by field_simp
    rw [he, neg_smul]
    abel
  rw [hvec, map_smul_eq_mul, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_left (hmin _) (abs_nonneg b)

/--
An integer-reduced vector at least as long as the first vector has seminorm at most twice that of its specified real translate.
-/
theorem roundedMinimumLe {E : Type*} [AddCommGroup E] [Module ℝ E]
    (f : Seminorm ℝ E) (w z : E) (q t : ℝ)
    (hclose : f (z - q • w) = t)
    (hshort : ∀ n : ℤ, f z ≤ f (z - (n : ℝ) • w))
    (hfirst : f w ≤ f z) :
    f z ≤ 2 * t := by
  let n : ℤ := ⌊q + 1 / 2⌋
  have hn₁ := Int.floor_le (q + 1 / 2)
  have hn₂ := Int.lt_floor_add_one (q + 1 / 2)
  have hn : |q - (n : ℝ)| ≤ 1 / 2 := abs_le.mpr ⟨by dsimp [n]; linarith, by dsimp [n]; linarith⟩
  have hvec : z - (n : ℝ) • w = (z - q • w) + (q - (n : ℝ)) • w := by
    rw [sub_smul]
    abel
  have hh := hshort n
  rw [hvec] at hh
  have ht := map_add_le_add f (z - q • w) ((q - (n : ℝ)) • w)
  rw [hclose, map_smul_eq_mul, Real.norm_eq_abs] at ht
  have hmul := mul_le_mul_of_nonneg_right hn (apply_nonneg f w)
  linarith

/--
A change of basis of determinant one or minus one bounds the first basis seminorm using two entries of its inverse.
-/
theorem detAreaComparison {E : Type*} [AddCommGroup E] [Module ℝ E]
    (f : Seminorm ℝ E) (w z x y : E) (a b c d H T L : ℝ)
    (hw : w = a • x + b • z) (hy : y = c • x + d • z)
    (hdet : a * d - b * c = 1 ∨ a * d - b * c = -1)
    (hwH : f w = H) (hyT : f y = T) (hxL : f x = L) :
    L ≤ |d| * H + |b| * T := by
  have he : d • w - b • y = (a * d - b * c) • x := by
    rw [hw, hy]
    module
  have hnorm : f (d • w - b • y) = L := by
    rw [he, map_smul_eq_mul, Real.norm_eq_abs, hxL]
    rcases hdet with h | h <;> rw [h] <;> norm_num
  have htri := map_add_le_add f (d • w) (-(b • y))
  rw [← sub_eq_add_neg, hnorm, map_neg_eq_map, map_smul_eq_mul, map_smul_eq_mul,
    Real.norm_eq_abs, Real.norm_eq_abs, hwH, hyT] at htri
  exact htri

end

end AbcTwoNinths.Basic
