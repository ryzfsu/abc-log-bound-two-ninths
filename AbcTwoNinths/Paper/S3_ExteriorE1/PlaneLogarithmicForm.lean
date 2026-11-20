/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruiyi Zhang
-/

module

public import AbcTwoNinths.Paper.S3_ExteriorE1.ResidualPlaneContact
public import AbcTwoNinths.Paper.S3_ExteriorE1.PlaneLogarithm

/-!
# Plane Logarithmic Form

The module bounds the weighted logarithmic form on the reduced plane and packages the resulting slab. It supports Proposition 3.1 of the paper.

## Main results
* `AbcTwoNinths.ExteriorE1.reducedLogSlab`
-/

@[expose] public section


namespace AbcTwoNinths.ExteriorE1

section

/--
The linear form obtained by summing coordinates against the given real weights. This is used in the proof of Proposition 3.1 of the paper.
-/
def weightedLog {ι : Type*} [Fintype ι] (a : ι → ℝ) : (ι → ℝ) →ₗ[ℝ] ℝ :=
  ∑ i : ι, a i • LinearMap.proj i

/-- The weighted logarithmic form evaluates to the sum of the coordinate products. -/
theorem weightedLogApply {ι : Type*} [Fintype ι] (a y : ι → ℝ) :
    _root_.AbcTwoNinths.ExteriorE1.weightedLog a y = ∑ i, a i * y i := by
  simp [_root_.AbcTwoNinths.ExteriorE1.weightedLog, Finset.sum_apply]

/-- For nonnegative weights, the height is at most the sum of the absolute weighted coordinates. -/
theorem weightAbsLe {ι : Type*} [Fintype ι] (a y : ι → ℝ) (ha : ∀ i, 0 ≤ a i) :
    _root_.AbcTwoNinths.ExteriorE1.height a y ≤ ∑ i, |a i * y i| := by
  apply max_le <;> apply Finset.sum_le_sum <;> intro i _
  · rw [abs_mul, abs_of_nonneg (ha i)]
    exact mul_le_mul_of_nonneg_left (max_le (le_abs_self _) (abs_nonneg _)) (ha i)
  · rw [abs_mul, abs_of_nonneg (ha i)]
    exact mul_le_mul_of_nonneg_left (max_le (neg_le_abs _) (abs_nonneg _)) (ha i)

/--
A short residual in a prime-weighted plane gives independent integral generators for a sublattice containing the source, with height, coefficient and logarithm bounds. This is used in the proof of Proposition 3.1 of the paper.
-/
theorem reducedLogSlab {ι : Type*} [Fintype ι]
    (q : ι → ℕ) (w u : ι → ℤ) (r : ι) (hr : w r ≠ 0)
    (hq : ∀ i, (q i).Prime)
    (hprim : ∀ (z : ι → ℤ) (s : ℝ), (∀ i, (z i : ℝ) = s * (w i : ℝ)) →
      ∃ k : ℤ, z = k • w)
    (hind : ¬ ∃ s : ℝ, ∀ i, (u i : ℝ) = s * (w i : ℝ))
    (g : ℤ) (hg : g ≠ 0) (p T ε : ℝ)
    (hp : |p| ≤ 1)
    (hTH : T ≤ _root_.AbcTwoNinths.ExteriorE1.height (fun i => Real.log (q i : ℝ)) (fun i => ((g * w i : ℤ) : ℝ)))
    (hR : _root_.AbcTwoNinths.ExteriorE1.height (fun i => Real.log (q i : ℝ))
      (fun i => (u i : ℝ) - p * ((g * w i : ℤ) : ℝ)) ≤ T)
    (hLv : |_root_.AbcTwoNinths.ExteriorE1.weightedLog (fun i => Real.log (q i : ℝ))
      (fun i => ((g * w i : ℤ) : ℝ))| ≤ ε)
    (hLu : |_root_.AbcTwoNinths.ExteriorE1.weightedLog (fun i => Real.log (q i : ℝ))
      (fun i => (u i : ℝ) - p * ((g * w i : ℤ) : ℝ))| ≤ ε) :
    ∃ (x y : ι → ℤ) (a b : ℤ) (t : ℝ),
      0 < t ∧ t ≤ T ∧
      (∀ m n : ℤ, m • x + n • y = 0 → m = 0 ∧ n = 0) ∧
      g • w = a • x + b • y ∧
      let A := fun i => Real.log (q i : ℝ)
      let L₁ := _root_.AbcTwoNinths.ExteriorE1.height A (fun i => (x i : ℝ))
      let L₂ := _root_.AbcTwoNinths.ExteriorE1.height A (fun i => (y i : ℝ))
      let H := _root_.AbcTwoNinths.ExteriorE1.height A (fun i => ((g * w i : ℤ) : ℝ))
      L₁ * L₂ ≤ 4 * H * t ∧
      |(a : ℝ)| * L₁ ≤ 3 * H ∧ |(b : ℝ)| * L₂ ≤ 2 * H ∧
      |_root_.AbcTwoNinths.ExteriorE1.weightedLog A (fun i => (x i : ℝ))| ≤ 7 * L₁ * ε / t ∧
      |_root_.AbcTwoNinths.ExteriorE1.weightedLog A (fun i => (y i : ℝ))| ≤ 7 * L₂ * ε / t := by
  let A := fun i => Real.log (q i : ℝ)
  have hA (i : ι) : 0 < A i := Real.log_pos (by exact_mod_cast (hq i).one_lt)
  let F := _root_.AbcTwoNinths.ExteriorE1.heightSeminorm A (fun i => (hA i).le)
  let v : ι → ℝ := fun i => ((g * w i : ℤ) : ℝ)
  let U : ι → ℝ := fun i => u i
  have hF (z : ι → ℝ) : F z = _root_.AbcTwoNinths.ExteriorE1.height A z := rfl
  have hv : v ≠ 0 := by
    intro h
    have h' : ((g * w r : ℤ) : ℝ) = 0 := congrFun h r
    exact mul_ne_zero hg hr (by exact_mod_cast h')
  have hind' : ¬ ∃ s : ℝ, U = s • v := by
    rintro ⟨s, h⟩
    refine hind ⟨s * (g : ℝ), fun i => ?_⟩
    have hi : (u i : ℝ) = s * ((g * w i : ℤ) : ℝ) := congrFun h i
    rwa [Int.cast_mul, ← mul_assoc] at hi
  obtain ⟨s, t, ht, hdist, hmin⟩ := _root_.AbcTwoNinths.ExteriorE1.existsAttainedQuotientDistOfContinuous F
    (_root_.AbcTwoNinths.ExteriorE1.heightContinuous A _) v U (_root_.AbcTwoNinths.ExteriorE1.heightPosOfNeZero A hA v hv) hind'
    (_root_.AbcTwoNinths.ExteriorE1.heightPosOfNeZero A hA)
  have htT : t ≤ T := (hmin p).trans hR
  have hU : F U ≤ F v + T := by
    have htri := map_add_le_add F (p • v) (U - p • v)
    rw [show p • v + (U - p • v) = U by abel, map_smul_eq_mul, Real.norm_eq_abs] at htri
    have hh := mul_le_mul_of_nonneg_right hp (apply_nonneg F v)
    change F (U - p • v) ≤ T at hR
    linarith
  obtain ⟨x, y, a, b, hx, hy, hi, he, _, _, hprod, ha, hb⟩ :=
    _root_.AbcTwoNinths.ExteriorE1.reducedPlaneOfResidual q w u r hr hq hprim hind g hg (s * (g : ℝ))
  have hres : (fun i => (u i : ℝ) - (s * (g : ℝ)) * (w i : ℝ)) = U - s • v := by
    ext i
    change (u i : ℝ) - (s * (g : ℝ)) * (w i : ℝ) = (u i : ℝ) - s * ((g * w i : ℤ) : ℝ)
    rw [Int.cast_mul, mul_assoc]
  have hd' : _root_.AbcTwoNinths.ExteriorE1.height A (U - s • v) = t := hdist
  rw [hres, hd'] at hprod
  have span (z : ι → ℤ) (hz : _root_.AbcTwoNinths.Basic.inPlane w u z) :
      (fun i => (z i : ℝ)) ∈ Submodule.span ℝ ({v, U} : Set (ι → ℝ)) := by
    obtain ⟨c, d, hz⟩ := hz
    apply Submodule.mem_span_pair.mpr
    refine ⟨c / (g : ℝ), d, ?_⟩
    have hg' : (g : ℝ) ≠ 0 := by exact_mod_cast hg
    ext i
    change c / (g : ℝ) * ((g * w i : ℤ) : ℝ) + d * (u i : ℝ) = (z i : ℝ)
    rw [hz, Int.cast_mul, ← mul_assoc, div_mul_cancel₀ _ hg']
  exact ⟨x, y, a, b, t, ht, htT, hi, he, hprod, ha, hb,
    _root_.AbcTwoNinths.ExteriorE1.planeLogBound F (_root_.AbcTwoNinths.ExteriorE1.weightedLog A) rfl hU ht htT hTH hmin hdist hp hLv hLu (span x hx),
    _root_.AbcTwoNinths.ExteriorE1.planeLogBound F (_root_.AbcTwoNinths.ExteriorE1.weightedLog A) rfl hU ht htT hTH hmin hdist hp hLv hLu (span y hy)⟩

end

end AbcTwoNinths.ExteriorE1
