/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruiyi Zhang
-/

module

public import AbcTwoNinths.Paper.S3_ExteriorE1.SourceExponentPlane
public import AbcTwoNinths.Basic.SaturatedPlane

/-!
# Residual Plane Contact

The module constructs a reduced plane from the residual case of the real-contact analysis. It supports Proposition 3.1 of the paper.

## Main results
* `AbcTwoNinths.ExteriorE1.reducedPlaneOfResidual`
-/

@[expose] public section


namespace AbcTwoNinths.ExteriorE1

section

/--
Two independent integral plane vectors represent the multiple of the primitive direction with height product at most 4 H T and weighted coefficients at most 3 H and 2 H. This is used in the proof of Proposition 3.1 of the paper.
-/
theorem reducedPlaneOfResidual {ι : Type*} [Fintype ι]
    (q : ι → ℕ) (w u : ι → ℤ) (r : ι) (hr : w r ≠ 0)
    (hq : ∀ i, (q i).Prime)
    (hprim : ∀ (z : ι → ℤ) (s : ℝ), (∀ i, (z i : ℝ) = s * (w i : ℝ)) →
      ∃ k : ℤ, z = k • w)
    (hind : ¬ ∃ s : ℝ, ∀ i, (u i : ℝ) = s * (w i : ℝ))
    (g : ℤ) (hg : g ≠ 0) (s : ℝ) :
    let f := _root_.AbcTwoNinths.ExteriorE1.height (fun i => Real.log (q i : ℝ))
    let H := f (fun i => ((g * w i : ℤ) : ℝ))
    let T := f (fun i => (u i : ℝ) - s * (w i : ℝ))
    ∃ (u₁ u₂ : ι → ℤ) (a b : ℤ),
      _root_.AbcTwoNinths.Basic.inPlane w u u₁ ∧ _root_.AbcTwoNinths.Basic.inPlane w u u₂ ∧
      (∀ m n : ℤ, m • u₁ + n • u₂ = 0 → m = 0 ∧ n = 0) ∧
      g • w = a • u₁ + b • u₂ ∧
      let A := f (fun i => (u₁ i : ℝ))
      let B := f (fun i => (u₂ i : ℝ))
      0 < A ∧ 0 < B ∧ A * B ≤ 4 * H * T ∧
      |(a : ℝ)| * A ≤ 3 * H ∧ |(b : ℝ)| * B ≤ 2 * H := by
  obtain ⟨z, ⟨v₁, v₂, hv⟩, _, j, k, hk, hu⟩ :=
    _root_.AbcTwoNinths.Basic.saturatedPlaneBasisExists w u r hr hprim hind
  have hz : ¬ ∃ c : ℚ, ∀ i, (z i : ℚ) = c * (w i : ℚ) := by
    rintro ⟨c, hc⟩
    apply hind
    refine ⟨(j : ℝ) + (k : ℝ) * (c : ℝ), fun i => ?_⟩
    have hci : (z i : ℝ) = (c : ℝ) * (w i : ℝ) := by exact_mod_cast hc i
    have hui : u i = j * w i + k * z i := congrFun hu i
    rw [hui]
    push_cast
    rw [hci]
    ring
  let f := _root_.AbcTwoNinths.ExteriorE1.height (fun i => Real.log (q i : ℝ))
  let F := _root_.AbcTwoNinths.ExteriorE1.heightSeminorm (fun i => Real.log (q i : ℝ))
    (fun i => Real.log_nonneg (by exact_mod_cast (hq i).one_le))
  let p := ((j : ℝ) - s) / (k : ℝ)
  have hw : w ≠ 0 := fun h => hr (congrFun h r)
  obtain ⟨x, y, a, b, ⟨c, hc⟩, ⟨d, hd⟩, hi, he, hA, hB, hp, ha, hb⟩ :=
    _root_.AbcTwoNinths.ExteriorE1.reducedIntegralPlane q w z hq hw hz p
  have hplane (l : ℤ × ℤ) : _root_.AbcTwoNinths.Basic.inPlane w u (_root_.AbcTwoNinths.ExteriorE1.planeMap w z l) := by
    refine ⟨(l.1 : ℝ) + (l.2 : ℝ) * v₁, (l.2 : ℝ) * v₂, fun i => ?_⟩
    simp only [_root_.AbcTwoNinths.ExteriorE1.planeMap, Int.cast_add, Int.cast_mul, hv]
    ring
  have hom (c : ℝ) (v : ι → ℝ) : f (c • v) = |c| * f v := by
    change F (c • v) = |c| * F v
    rw [map_smul_eq_mul, Real.norm_eq_abs]
  have hgres : (fun i => ((g * w i : ℤ) : ℝ)) = (g : ℝ) • (fun i => (w i : ℝ)) := by
    ext i
    exact Int.cast_mul _ _
  have hkR : (k : ℝ) ≠ 0 := by exact_mod_cast hk
  have hrres : (fun i => (u i : ℝ) - s * (w i : ℝ)) = (k : ℝ) • _root_.AbcTwoNinths.ExteriorE1.linearPlane w z (p, 1) := by
    ext i
    have hei : u i = j * w i + k * z i := congrFun hu i
    change (u i : ℝ) - s * w i = (k : ℝ) * (p * w i + 1 * z i)
    rw [hei]
    push_cast
    dsimp [p]
    field_simp
    ring
  have hg₁ : (1 : ℝ) ≤ |(g : ℝ)| := by
    exact_mod_cast (show (1 : ℤ) ≤ |g| by have := abs_pos.mpr hg; omega)
  have hk₁ : (1 : ℝ) ≤ |(k : ℝ)| := by
    exact_mod_cast (show (1 : ℤ) ≤ |k| by have := abs_pos.mpr hk; omega)
  have hgr := congrArg f hgres
  have hkr := congrArg f hrres
  rw [hom] at hgr hkr
  refine ⟨x, y, g * a, g * b, hc ▸ hplane c, hd ▸ hplane d, hi, ?_, hA, hB, ?_, ?_, ?_⟩
  · nth_rw 1 [he]
    rw [smul_add, smul_smul, smul_smul]
  · change _ ≤ 4 * f (fun i => ((g * w i : ℤ) : ℝ)) * f (fun i => (u i : ℝ) - s * (w i : ℝ))
    rw [hgr, hkr]
    have h₁ : f (fun i => (w i : ℝ)) ≤ |(g : ℝ)| * f (fun i => (w i : ℝ)) := by
      change F (fun i => (w i : ℝ)) ≤ |(g : ℝ)| * F (fun i => (w i : ℝ))
      simpa only [one_mul] using mul_le_mul_of_nonneg_right hg₁ (apply_nonneg F _)
    have h₂ : f (_root_.AbcTwoNinths.ExteriorE1.linearPlane w z (p, 1)) ≤ |(k : ℝ)| * f (_root_.AbcTwoNinths.ExteriorE1.linearPlane w z (p, 1)) := by
      change F (_root_.AbcTwoNinths.ExteriorE1.linearPlane w z (p, 1)) ≤ |(k : ℝ)| * F (_root_.AbcTwoNinths.ExteriorE1.linearPlane w z (p, 1))
      simpa only [one_mul] using mul_le_mul_of_nonneg_right hk₁ (apply_nonneg F _)
    exact hp.trans (mul_le_mul (mul_le_mul_of_nonneg_left h₁ (by norm_num)) h₂
      (apply_nonneg F _) (mul_nonneg (by norm_num) (mul_nonneg (abs_nonneg _) (apply_nonneg F _))))
  · change |((g * a : ℤ) : ℝ)| * _ ≤ 3 * f (fun i => ((g * w i : ℤ) : ℝ))
    rw [hgr, Int.cast_mul, abs_mul]
    have hh := mul_le_mul_of_nonneg_left ha (abs_nonneg (g : ℝ))
    nlinarith only [hh]
  · change |((g * b : ℤ) : ℝ)| * _ ≤ 2 * f (fun i => ((g * w i : ℤ) : ℝ))
    rw [hgr, Int.cast_mul, abs_mul]
    have hh := mul_le_mul_of_nonneg_left hb (abs_nonneg (g : ℝ))
    nlinarith only [hh]

end

end AbcTwoNinths.ExteriorE1
