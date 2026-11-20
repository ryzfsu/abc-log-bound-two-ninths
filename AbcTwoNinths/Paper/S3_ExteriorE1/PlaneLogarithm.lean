/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruiyi Zhang
-/

module

public import Mathlib.Analysis.Normed.Module.Seminorm.Basic
public import Mathlib.LinearAlgebra.Span.Basic
public import Mathlib.Tactic

/-!
# Plane Logarithm

The module bounds the logarithmic form on a plane from the sizes of its basis vectors. It supports Proposition 3.1 of the paper.

## Main results
* `AbcTwoNinths.ExteriorE1.planeLogBound`
-/

@[expose] public section


namespace AbcTwoNinths.ExteriorE1

set_option autoImplicit false

section

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

/--
An attained quotient distance and two strip bounds control the linear functional on the span with factor seven. This is used in the proof of Proposition 3.1 of the paper.
-/
theorem planeLogBound (f : Seminorm ℝ E) (L : E →ₗ[ℝ] ℝ)
    {v u : E} {H T t ε p q : ℝ}
    (hv : f v = H) (hu : f u ≤ H + T) (ht : 0 < t)
    (htT : t ≤ T) (hTH : T ≤ H)
    (hmin : ∀ a : ℝ, t ≤ f (u - a • v)) (hclose : f (u - q • v) = t)
    (hp : |p| ≤ 1) (hsource : |L v| ≤ ε) (hstrip : |L (u - p • v)| ≤ ε)
    {w : E} (hw : w ∈ Submodule.span ℝ ({v, u} : Set E)) :
    |L w| ≤ 7 * f w * ε / t := by
  have hH : 0 < H := ht.trans_le (htT.trans hTH)
  have hε : 0 ≤ ε := (abs_nonneg _).trans hsource
  have hqH : |q| * H ≤ H + T + t := by
    have h := map_add_le_add f u (-(u - q • v))
    rw [map_neg_eq_map] at h
    have he : u + -(u - q • v) = q • v := by abel
    rw [he, map_smul_eq_mul, Real.norm_eq_abs, hv, hclose] at h
    linarith
  have hq : |q| ≤ 3 := by nlinarith
  have hpq : |p - q| ≤ 4 := by linarith [abs_sub p q]
  have hlogClose : |L (u - q • v)| ≤ 5 * ε := by
    have he : u - q • v = (u - p • v) + (p - q) • v := by
      rw [sub_smul]
      abel
    rw [he, map_add, map_smul, smul_eq_mul]
    calc
      _ ≤ |L (u - p • v)| + |(p - q) * L v| := abs_add_le _ _
      _ ≤ ε + 4 * ε := by
        rw [abs_mul]
        exact add_le_add hstrip
          (mul_le_mul hpq hsource (abs_nonneg _) (by norm_num))
      _ = _ := by ring
  obtain ⟨a, b, hab⟩ := Submodule.mem_span_pair.mp hw
  let r := a + b * q
  have hw' : w = r • v + b • (u - q • v) := by
    rw [← hab]
    dsimp [r]
    rw [add_smul, mul_smul, smul_sub, smul_smul]
    abel
  have hb : |b| * t ≤ f w := by
    by_cases hb : b = 0
    · simp [hb]
    · have he : w = b • (u - (q - r / b) • v) := by
        have hmul : b * (q - r / b) = b * q - r := by field_simp
        rw [hw', smul_sub, smul_smul, smul_sub, smul_smul, hmul, sub_smul, mul_smul]
        abel
      conv_rhs => rw [he, map_smul_eq_mul, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_left (hmin _) (abs_nonneg _)
  have hr : |r| * H ≤ 2 * f w := by
    have he : w + -(b • (u - q • v)) = r • v := by rw [hw']; abel
    have h := map_add_le_add f w (-(b • (u - q • v)))
    rw [he, map_neg_eq_map, map_smul_eq_mul, map_smul_eq_mul,
      Real.norm_eq_abs, Real.norm_eq_abs, hv, hclose] at h
    linarith
  have h1 : |r| * t ≤ 2 * f w :=
    (mul_le_mul_of_nonneg_left (htT.trans hTH) (abs_nonneg _)).trans hr
  have h2 : |L w| ≤ |r| * ε + |b| * (5 * ε) := by
    rw [hw', map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul]
    exact (abs_add_le _ _).trans (by
      rw [abs_mul, abs_mul]
      exact add_le_add (mul_le_mul_of_nonneg_left hsource (abs_nonneg _))
        (mul_le_mul_of_nonneg_left hlogClose (abs_nonneg _)))
  apply (le_div_iff₀ ht).2
  calc
    |L w| * t ≤ (|r| * ε + |b| * (5 * ε)) * t :=
      mul_le_mul_of_nonneg_right h2 ht.le
    _ = (|r| * t) * ε + (|b| * t) * (5 * ε) := by ring
    _ ≤ (2 * f w) * ε + f w * (5 * ε) :=
      add_le_add (mul_le_mul_of_nonneg_right h1 hε)
        (mul_le_mul_of_nonneg_right hb (mul_nonneg (by norm_num) hε))
    _ = 7 * f w * ε := by ring

end

end AbcTwoNinths.ExteriorE1
