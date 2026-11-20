/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruiyi Zhang
-/

module

public import Mathlib

/-!
# Exponential Height Distance

A continuous positive-definite seminorm attains a positive minimum distance from a vector outside a
line to that line. This supports Proposition 3.1 of the paper.

## Main results
* `AbcTwoNinths.ExteriorE1.existsAttainedQuotientDistOfContinuous`
-/

@[expose] public section


namespace AbcTwoNinths.ExteriorE1

section

/--
A continuous positive-definite seminorm attains a positive minimum distance from a vector outside the line to that line. This is used in the proof of Proposition 3.1 of the paper.
-/
theorem existsAttainedQuotientDistOfContinuous {E : Type*}
    [AddCommGroup E] [Module ℝ E] [TopologicalSpace E] [ContinuousSub E]
    [ContinuousSMul ℝ E] (f : Seminorm ℝ E) (hf : Continuous f)
    (v u : E) (hv : 0 < f v)
    (hind : ¬ ∃ s : ℝ, u = s • v)
    (hpos : ∀ z : E, z ≠ 0 → 0 < f z) :
    ∃ q t : ℝ, 0 < t ∧ f (u - q • v) = t ∧ ∀ a : ℝ, t ≤ f (u - a • v) := by
  let M : ℝ := 2 * f u / f v
  let φ (a : ℝ) := f (u - a • v)
  have hM : 0 ≤ M := div_nonneg (mul_nonneg (by norm_num) (apply_nonneg f u)) hv.le
  have hzero : (0 : ℝ) ∈ Set.Icc (-M) M := ⟨by linarith, hM⟩
  have hc : Continuous φ := hf.comp (continuous_const.sub (continuous_id.smul continuous_const))
  obtain ⟨q, hq, hmin⟩ := isCompact_Icc.exists_isMinOn ⟨0, hzero⟩ hc.continuousOn
  have hn : u - q • v ≠ 0 := fun h => hind ⟨q, sub_eq_zero.mp h⟩
  refine ⟨q, φ q, hpos _ hn, rfl, fun a => ?_⟩
  by_cases ha : a ∈ Set.Icc (-M) M
  · exact hmin ha
  have habs : M < |a| := by
    rw [← not_le, abs_le]
    exact ha
  have hbig : 2 * f u < |a| * f v := (div_lt_iff₀ hv).mp habs
  have htri := map_add_le_add f u (-(u - a • v))
  rw [map_neg_eq_map, show u + -(u - a • v) = a • v by abel,
    map_smul_eq_mul, Real.norm_eq_abs] at htri
  have hq₀ : φ q ≤ φ 0 := hmin hzero
  have hzero' : φ 0 = f u := by simp [φ]
  dsimp [φ] at *
  linarith

end

end AbcTwoNinths.ExteriorE1
