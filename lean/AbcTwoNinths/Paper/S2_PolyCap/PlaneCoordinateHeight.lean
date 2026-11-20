/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruiyi Zhang
-/

module

public import AbcTwoNinths.Paper.S2_PolyCap.CoprimeMonomialParts

/-!
# Plane Coordinate Height

The module defines plane height and relates its norm inequalities to the rational height of evaluated monomials. It supports Proposition 2.1 of the paper.

## Main results
* `AbcTwoNinths.PolyCap.planeHeightEqRatHeight`
-/

@[expose] public section


namespace AbcTwoNinths.PolyCap

section
open Real

/-- The plane map. This is used in the proof of Proposition 2.1 of the paper. -/
def planeMap {ι : Type*} (e v : ι → ℤ) (x : ℤ × ℤ) : ι → ℤ :=
  fun j => x.1 * e j + x.2 * v j

/-- The plane coord. This is used in the proof of Proposition 2.1 of the paper. -/
noncomputable def planeCoord {ι : Type*} (q : ι → ℕ) (e v : ι → ℤ)
    (j : ι) (z : ℝ × ℝ) : ℝ :=
  (z.1 * (e j : ℝ) + z.2 * (v j : ℝ)) * log (q j : ℝ)

/-- The coord height. This is used in the proof of Proposition 2.1 of the paper. -/
noncomputable def coordHeight {ι : Type*} [Fintype ι] (u : ι → ℝ) : ℝ :=
  max (∑ j, max (u j) 0) (∑ j, max (-(u j)) 0)

/-- The plane height. This is used in the proof of Proposition 2.1 of the paper. -/
noncomputable def planeHeight {ι : Type*} [Fintype ι] (q : ι → ℕ)
    (e v : ι → ℤ) (z : ℝ × ℝ) : ℝ :=
  _root_.AbcTwoNinths.PolyCap.coordHeight (fun j => _root_.AbcTwoNinths.PolyCap.planeCoord q e v j z)

/-- The coordinate height of a real vector is nonnegative. -/
theorem coordHeightNonneg {ι : Type*} [Fintype ι] (u : ι → ℝ) : 0 ≤ _root_.AbcTwoNinths.PolyCap.coordHeight u :=
  (Finset.sum_nonneg fun j _ => le_max_right (u j) 0).trans (le_max_left _ _)

/-- Negating the vector preserves coordinate height. -/
theorem coordHeightNeg {ι : Type*} [Fintype ι] (u : ι → ℝ) :
    _root_.AbcTwoNinths.PolyCap.coordHeight (-u) = _root_.AbcTwoNinths.PolyCap.coordHeight u := by
  simp only [_root_.AbcTwoNinths.PolyCap.coordHeight, Pi.neg_apply, neg_neg]
  exact max_comm _ _

/-- Scaling every coordinate by a real scalar multiplies coordinate height by its absolute value. -/
theorem coordHeightSmul {ι : Type*} [Fintype ι] (t : ℝ) (u : ι → ℝ) :
    _root_.AbcTwoNinths.PolyCap.coordHeight (fun j => t * u j) = |t| * _root_.AbcTwoNinths.PolyCap.coordHeight u := by
  have aux (s : ℝ) (hs : 0 ≤ s) (w : ι → ℝ) :
      _root_.AbcTwoNinths.PolyCap.coordHeight (fun j => s * w j) = s * _root_.AbcTwoNinths.PolyCap.coordHeight w := by
    have hm (a : ℝ) : max (s * a) 0 = s * max a 0 := by
      rw [mul_max_of_nonneg _ _ hs, mul_zero]
    simp only [_root_.AbcTwoNinths.PolyCap.coordHeight, ← mul_neg, hm, ← Finset.mul_sum,
      ← mul_max_of_nonneg _ _ hs]
  by_cases ht : 0 ≤ t
  · rw [abs_of_nonneg ht]; exact aux t ht u
  · rw [abs_of_neg (lt_of_not_ge ht)]
    have he : (fun j => t * u j) = (fun j => (-t) * (-u) j) := by
      funext j; simp
    rw [he, aux _ (by linarith) _, _root_.AbcTwoNinths.PolyCap.coordHeightNeg]

/-- The coordinate height of a sum is at most the sum of the coordinate heights. -/
theorem coordHeightAdd {ι : Type*} [Fintype ι] (u v : ι → ℝ) :
    _root_.AbcTwoNinths.PolyCap.coordHeight (u + v) ≤ _root_.AbcTwoNinths.PolyCap.coordHeight u + _root_.AbcTwoNinths.PolyCap.coordHeight v := by
  have aux (a b : ι → ℝ) : (∑ j, max (a j + b j) 0) ≤
      (∑ j, max (a j) 0) + (∑ j, max (b j) 0) := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_le_sum fun j _ => max_le
      (add_le_add (le_max_left _ _) (le_max_left _ _))
      (add_nonneg (le_max_right _ _) (le_max_right _ _))
  exact max_le ((aux u v).trans (add_le_add (le_max_left _ _) (le_max_left _ _)))
    ((by simpa only [Pi.add_apply, Pi.neg_apply, neg_add_rev, add_comm] using aux (-u) (-v) :
        (∑ j, max (-((u + v) j)) 0) ≤ (∑ j, max (-(u j)) 0) + (∑ j, max (-(v j)) 0)).trans
        (add_le_add (le_max_right _ _) (le_max_right _ _)))

/-- Coordinate height lies between one half and one times the sum of the absolute coordinates. -/
theorem coordHeightBounds {ι : Type*} [Fintype ι] (u : ι → ℝ) :
    (1 / 2 : ℝ) * ∑ j, |u j| ≤ _root_.AbcTwoNinths.PolyCap.coordHeight u ∧ _root_.AbcTwoNinths.PolyCap.coordHeight u ≤ ∑ j, |u j| := by
  have h (x : ℝ) : |x| = max x 0 + max (-x) 0 := by
    rcases le_total 0 x with hx | hx
    · rw [abs_of_nonneg hx, max_eq_left hx, max_eq_right (neg_nonpos.mpr hx), add_zero]
    · rw [abs_of_nonpos hx, max_eq_right hx, max_eq_left (neg_nonneg.mpr hx), zero_add]
  constructor
  · simp only [h, Finset.sum_add_distrib]
    have hl := le_max_left (∑ j, max (u j) 0) (∑ j, max (-(u j)) 0)
    have hr := le_max_right (∑ j, max (u j) 0) (∑ j, max (-(u j)) 0)
    change _ ≤ max _ _
    linarith
  · exact max_le (Finset.sum_le_sum fun j _ => max_le (le_abs_self _) (abs_nonneg _))
      (Finset.sum_le_sum fun j _ => max_le (neg_le_abs _) (abs_nonneg _))

/-- Real scalar multiplication changes plane height by the absolute value of the scalar. -/
theorem planeHeightSmul {ι : Type*} [Fintype ι] (q : ι → ℕ) (e v : ι → ℤ)
    (t : ℝ) (z : ℝ × ℝ) :
    _root_.AbcTwoNinths.PolyCap.planeHeight q e v (t • z) = |t| * _root_.AbcTwoNinths.PolyCap.planeHeight q e v z := by
  unfold _root_.AbcTwoNinths.PolyCap.planeHeight
  rw [← _root_.AbcTwoNinths.PolyCap.coordHeightSmul]
  congr 1
  funext j
  simp only [_root_.AbcTwoNinths.PolyCap.planeCoord, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
  ring

/-- The plane height of a sum is at most the sum of the two plane heights. -/
theorem planeHeightAdd {ι : Type*} [Fintype ι] (q : ι → ℕ) (e v : ι → ℤ)
    (x y : ℝ × ℝ) :
    _root_.AbcTwoNinths.PolyCap.planeHeight q e v (x + y) ≤ _root_.AbcTwoNinths.PolyCap.planeHeight q e v x + _root_.AbcTwoNinths.PolyCap.planeHeight q e v y := by
  unfold _root_.AbcTwoNinths.PolyCap.planeHeight
  convert _root_.AbcTwoNinths.PolyCap.coordHeightAdd (fun j => _root_.AbcTwoNinths.PolyCap.planeCoord q e v j x) (fun j => _root_.AbcTwoNinths.PolyCap.planeCoord q e v j y) using 2
  funext j
  simp only [_root_.AbcTwoNinths.PolyCap.planeCoord, Prod.fst_add, Prod.snd_add, Pi.add_apply]
  ring

/--
For integer plane coordinates and distinct prime bases, the plane height equals the logarithmic
height of the rational monomial with exponents given by the plane map.
-/
theorem planeHeightEqRatHeight {ι : Type*} [Fintype ι] (q : ι → ℕ)
    (hq : ∀ j, (q j).Prime) (hinj : Function.Injective q) (e v : ι → ℤ) (x : ℤ × ℤ) :
    _root_.AbcTwoNinths.Basic.rationalHeight (_root_.AbcTwoNinths.PolyCap.prodMonomial q (_root_.AbcTwoNinths.PolyCap.planeMap e v x)) =
      _root_.AbcTwoNinths.PolyCap.planeHeight q e v ((x.1 : ℝ), (x.2 : ℝ)) := by
  simpa only [_root_.AbcTwoNinths.PolyCap.planeHeight, _root_.AbcTwoNinths.PolyCap.coordHeight, _root_.AbcTwoNinths.PolyCap.planeCoord, _root_.AbcTwoNinths.PolyCap.planeMap, Int.cast_add, Int.cast_mul]
    using (_root_.AbcTwoNinths.PolyCap.ratHeightProdMonomial q hq hinj (_root_.AbcTwoNinths.PolyCap.planeMap e v x)).1

end

end AbcTwoNinths.PolyCap
