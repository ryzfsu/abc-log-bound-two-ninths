/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruiyi Zhang
-/

module

public import Mathlib

/-!
# Diamond Label Injectivity

The module proves that sites in the diamond's short ball have distinct interpolation labels. It supports Section 7 of the paper.

## Main results
* `AbcTwoNinths.Terminal.ballLabelsInjective`
-/

@[expose] public section


namespace AbcTwoNinths.Terminal

section

/--
The sheared diamond height of an integer site is the weighted sum of its absolute horizontal and vertical coordinates after the shear. This is used in Section 7 of the paper.
-/
def diamondHeight (c h t : ℝ) (s : ℤ × ℤ) : ℝ :=
  |(s.1 : ℝ) + c * (s.2 : ℝ)| * h + |(s.2 : ℝ)| * t

/--
The second coordinate is injective on any subset of the diamond when twice its radius is less than its horizontal weight. This is used in Section 7 of the paper.
-/
theorem ballLabelsInjective {c h t r : ℝ} {S : Set (ℤ × ℤ)}
    (hh : 0 < h) (ht : 0 ≤ t) (hr : 2 * r < h)
    (hball : ∀ s ∈ S, _root_.AbcTwoNinths.Terminal.diamondHeight c h t s ≤ r) :
    Function.Injective (fun s : S => s.val.2) := by
  intro a b hy
  apply Subtype.ext
  apply Prod.ext _ hy
  by_contra hne
  have hint : (1 : ℤ) ≤ |a.val.1 - b.val.1| := by
    rw [le_abs]
    omega
  have hreal : (1 : ℝ) ≤ |(a.val.1 : ℝ) - (b.val.1 : ℝ)| := by
    exact_mod_cast hint
  have hy' : (a.val.2 : ℝ) = (b.val.2 : ℝ) := by exact_mod_cast hy
  have htri := abs_sub ((a.val.1 : ℝ) + c * (a.val.2 : ℝ))
    ((b.val.1 : ℝ) + c * (b.val.2 : ℝ))
  have hcancel :
      (a.val.1 : ℝ) + c * (a.val.2 : ℝ) -
        ((b.val.1 : ℝ) + c * (b.val.2 : ℝ)) =
      (a.val.1 : ℝ) - (b.val.1 : ℝ) := by rw [hy']; ring
  rw [hcancel] at htri
  have ha := hball a.val a.property
  have hb := hball b.val b.property
  unfold _root_.AbcTwoNinths.Terminal.diamondHeight at ha hb
  have hl := mul_le_mul_of_nonneg_right hreal hh.le
  have hu := mul_le_mul_of_nonneg_right htri hh.le
  rw [add_mul] at hu
  linarith [mul_nonneg (abs_nonneg (a.val.2 : ℝ)) ht,
    mul_nonneg (abs_nonneg (b.val.2 : ℝ)) ht]

end

end AbcTwoNinths.Terminal
