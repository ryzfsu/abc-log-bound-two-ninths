/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruiyi Zhang
-/

module

public import AbcTwoNinths.Basic.ReducedBasisEstimates

/-!
# Plane Basis Height Bounds

The module bounds the basis lengths of a reduced exponent plane. It supports Proposition 3.1 of the paper.

## Main results
* `AbcTwoNinths.ExteriorE1.reducedBasisBounds`
-/

@[expose] public section


namespace AbcTwoNinths.ExteriorE1

section

/-- For a seminorm-reduced unimodular basis, the product of the basis heights is at most
four times the comparison product, and the weighted coordinates of `w` are bounded by
three and two times its seminorm, respectively. -/
theorem reducedBasisBounds {E : Type*} [AddCommGroup E] [Module ℝ E]
    (f : Seminorm ℝ E) (w y x z : E) (a b c d q t : ℝ)
    (hw : w = a • x + b • z) (hy : y = c • x + d • z)
    (hdet : a * d - b * c = 1 ∨ a * d - b * c = -1)
    (ht : 0 < t) (hclose : f (z - q • x) = t)
    (hmin : ∀ p : ℝ, t ≤ f (z - p • x))
    (hshort : ∀ n : ℤ, f z ≤ f (z - (n : ℝ) • x))
    (hfirst : f x ≤ f z) :
    f x * f z ≤ 4 * f w * f y ∧
      |a| * f x ≤ 3 * f w ∧ |b| * f z ≤ 2 * f w := by
  have h2 := _root_.AbcTwoNinths.Basic.roundedMinimumLe f x z q t hclose hshort hfirst
  let z' := z - q • x
  have hwa : w = (a + b * q) • x + b • z' := by
    rw [hw]
    dsimp [z']
    module
  have hya : y = (c + d * q) • x + d • z' := by
    rw [hy]
    dsimp [z']
    module
  have hdet' : (a + b * q) * d - b * (c + d * q) = 1 ∨
      (a + b * q) * d - b * (c + d * q) = -1 := by
    rwa [show (a + b * q) * d - b * (c + d * q) = a * d - b * c by ring]
  have harea := _root_.AbcTwoNinths.Basic.detAreaComparison f w z' x y (a + b * q) b (c + d * q) d
    (f w) (f y) (f x) hwa hya hdet' rfl rfl rfl
  have hb := _root_.AbcTwoNinths.Basic.quotientLb f x z t hmin a b
  have hd := _root_.AbcTwoNinths.Basic.quotientLb f x z t hmin c d
  rw [← hw] at hb
  rw [← hy] at hd
  have hb2 : |b| * f z ≤ 2 * f w := by
    have hh := mul_le_mul_of_nonneg_left h2 (abs_nonneg b)
    linarith
  have hprod : f x * f z ≤ 4 * f w * f y := calc
    _ ≤ f x * (2 * t) := mul_le_mul_of_nonneg_left h2 (apply_nonneg f x)
    _ ≤ (|d| * f w + |b| * f y) * (2 * t) :=
      mul_le_mul_of_nonneg_right harea (by positivity)
    _ ≤ _ := by
      nlinarith only [mul_le_mul_of_nonneg_right hb (apply_nonneg f y),
        mul_le_mul_of_nonneg_right hd (apply_nonneg f w)]
  have hcoef : a • x = w - b • z := by rw [hw]; abel
  have htri := map_add_le_add f w (-(b • z))
  rw [← sub_eq_add_neg, ← hcoef, map_neg_eq_map, map_smul_eq_mul,
    map_smul_eq_mul, Real.norm_eq_abs, Real.norm_eq_abs] at htri
  exact ⟨hprod, by linarith, hb2⟩

end

end AbcTwoNinths.ExteriorE1
