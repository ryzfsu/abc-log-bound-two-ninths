/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruiyi Zhang
-/

module

public import AbcTwoNinths.Paper.S4_ExteriorE2.PlaneEstimate

/-!
# Reduced Height

The module bounds the coefficient sizes and height product of a reduced exponent basis. It supports Proposition 4.1 of the paper.

## Main results
* `AbcTwoNinths.ExteriorE2.reducedHeightProduct`
* `AbcTwoNinths.ExteriorE2.reducedHeightCoeffs`
-/

@[expose] public section


namespace AbcTwoNinths.ExteriorE2

section

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

/--
A determinant lower bound of one bounds the product of the rounded basis heights by four times the product of the input height bounds. This is used in the proof of Proposition 4.1 of the paper.
-/
theorem reducedHeightProduct (f : Seminorm ℝ E)
    (u w x y : E) (q d H ρ : ℝ)
    (hd : 0 ≤ d) (hmin : ∀ s : ℝ, d ≤ f (w - s • u))
    (hq : f (w - q • u) = d)
    (hs : f u ≤ f (w - (round q : ℝ) • u))
    (Hpos : 0 ≤ H) (hx : f x ≤ H) (hy : f y ≤ ρ)
    (a b c e : ℝ) (ex : x = a • u + b • w) (ey : y = c • u + e • w)
    (hdet : 1 ≤ |a * e - b * c|) :
    f u * f (w - (round q : ℝ) • u) ≤ 4 * H * ρ := by
  have h := _root_.AbcTwoNinths.ExteriorE2.determinantHeightBound f hd hmin a b c e
  rw [← ex, ← ey] at h
  have hd' : f u * d ≤ 2 * f x * f y := calc
    f u * d = 1 * |f u| * d := by rw [one_mul, abs_of_nonneg (apply_nonneg f u)]
    _ ≤ |a * e - b * c| * f u * d := by
      rw [abs_of_nonneg (apply_nonneg f u)]
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hdet (apply_nonneg f u)) hd
    _ ≤ _ := h
  have hp : f x * f y ≤ H * ρ := mul_le_mul hx hy (apply_nonneg f y) Hpos
  have hround := mul_le_mul_of_nonneg_left (_root_.AbcTwoNinths.ExteriorE2.roundedHeightBound f u w q d hq hs)
    (apply_nonneg f u)
  linarith only [hd', hp, hround]

/--
In the rounded plane basis the first and second coefficient heights are at most three and two times the vector height, respectively. This is used in the proof of Proposition 4.1 of the paper.
-/
theorem reducedHeightCoeffs (f : Seminorm ℝ E) (u w : E)
    (q d : ℝ) (hmin : ∀ s : ℝ, d ≤ f (w - s • u))
    (hq : f (w - q • u) = d)
    (hs : f u ≤ f (w - (round q : ℝ) • u)) (a b : ℝ) :
    let v := w - (round q : ℝ) • u
    let x := a • u + b • v
    |a| * f u ≤ 3 * f x ∧ |b| * f v ≤ 2 * f x := by
  dsimp only
  let m : ℝ := (round q : ℤ)
  let v := w - m • u
  let x := a • u + b • v
  have hv := _root_.AbcTwoNinths.ExteriorE2.roundedHeightBound f u w q d hq hs
  have hb := _root_.AbcTwoNinths.ExteriorE2.transverseCoeffBound f hmin (a - b * m) b
  have hx : (a - b * m) • u + b • w = x := by dsimp [x, v]; module
  rw [hx] at hb
  have hb' : |b| * f v ≤ 2 * f x := by
    change f v ≤ 2 * d at hv
    have hh := mul_le_mul_of_nonneg_left hv (abs_nonneg b)
    linarith
  have ha := map_add_le_add f x ((-b) • v)
  rw [show x + (-b) • v = a • u by dsimp [x]; module, map_smul_eq_mul,
    map_smul_eq_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_neg] at ha
  exact ⟨by linarith, hb'⟩

end

end AbcTwoNinths.ExteriorE2
