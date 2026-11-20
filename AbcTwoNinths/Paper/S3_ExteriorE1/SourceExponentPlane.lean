/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruiyi Zhang
-/

module

public import AbcTwoNinths.Paper.S3_ExteriorE1.IntegralPlaneCoordinates
public import AbcTwoNinths.Paper.S3_ExteriorE1.PlaneHeightComparison

/-!
# Source Exponent Plane

The module constructs the reduced integral plane and relates its height to the original exponent height. It supports Proposition 3.1 of the paper.

## Main results
* `AbcTwoNinths.ExteriorE1.reducedIntegralPlane`
-/

@[expose] public section


namespace AbcTwoNinths.ExteriorE1

section



variable {ι : Type*} [Fintype ι]

/--
The real linear map sends a pair of coefficients to the indicated combination of the two integral vectors. This is used in the proof of Proposition 3.1 of the paper.
-/
def linearPlane (w z : ι → ℤ) : (ℝ × ℝ) →ₗ[ℝ] (ι → ℝ) where
  toFun p i := p.1 * w i + p.2 * z i
  map_add' p q := by ext i; change (p.1 + q.1) * w i + (p.2 + q.2) * z i = _; simp; ring
  map_smul' c p := by ext i; change (c * p.1) * w i + (c * p.2) * z i = c * (_ + _); ring

/--
Pulling the logarithmic height seminorm back along the real plane map gives the coordinate plane height.
-/
theorem sourceExponentPlanePlaneHeight (q : ι → ℕ) (w z : ι → ℤ)
    (ha : ∀ i, 0 ≤ Real.log (q i : ℝ)) (p : ℝ × ℝ) :
    (_root_.AbcTwoNinths.ExteriorE1.heightSeminorm (fun i => Real.log (q i : ℝ)) ha).comp (_root_.AbcTwoNinths.ExteriorE1.linearPlane w z) p =
      _root_.AbcTwoNinths.ExteriorE1.planeHeight q w z p := by
  change _root_.AbcTwoNinths.ExteriorE1.height (fun i => Real.log (q i : ℝ)) (_root_.AbcTwoNinths.ExteriorE1.linearPlane w z p) = _
  unfold _root_.AbcTwoNinths.ExteriorE1.height _root_.AbcTwoNinths.ExteriorE1.positiveWeight _root_.AbcTwoNinths.ExteriorE1.planeHeight _root_.AbcTwoNinths.ExteriorE1.planeCoord
  congr 1 <;> apply Finset.sum_congr rfl <;> intro i _
  · rw [mul_max_of_nonneg _ _ (ha i), mul_zero]
    congr 1
    exact mul_comm _ _
  · rw [mul_max_of_nonneg _ _ (ha i), mul_zero]
    congr 1
    change Real.log (q i : ℝ) * -(p.1 * w i + p.2 * z i) = _
    ring

/-- The pullback of the logarithmic height seminorm to the real plane is continuous. -/
theorem planeHeightContinuous (q : ι → ℕ) (w z : ι → ℤ)
    (ha : ∀ i, 0 ≤ Real.log (q i : ℝ)) :
    Continuous ((_root_.AbcTwoNinths.ExteriorE1.heightSeminorm (fun i => Real.log (q i : ℝ)) ha).comp (_root_.AbcTwoNinths.ExteriorE1.linearPlane w z)) := by
  apply (_root_.AbcTwoNinths.ExteriorE1.heightContinuous _ ha).comp
  change Continuous (fun p : ℝ × ℝ => fun i => p.1 * (w i : ℝ) + p.2 * (z i : ℝ))
  fun_prop

set_option linter.unusedSectionVars false in
/--
A nonzero two-coordinate minor guarantees that every nonzero real coefficient pair has nonzero image.
-/
theorem planeNonzeroOfMinor (w z : ι → ℤ) {i j : ι}
    (hm : w i * z j - w j * z i ≠ 0) (p : ℝ × ℝ) (hp : p ≠ 0) :
    _root_.AbcTwoNinths.ExteriorE1.linearPlane w z p ≠ 0 := by
  intro hz
  have h₁ : p.1 * (w i : ℝ) + p.2 * (z i : ℝ) = 0 := congrFun hz i
  have h₂ : p.1 * (w j : ℝ) + p.2 * (z j : ℝ) = 0 := congrFun hz j
  have hd : (w i : ℝ) * z j - (w j : ℝ) * z i ≠ 0 := by exact_mod_cast hm
  apply hp
  apply Prod.ext
  · change p.1 = 0
    apply (mul_eq_zero.mp ?_).resolve_right hd
    linear_combination (z j : ℝ) * h₁ - (z i : ℝ) * h₂
  · change p.2 = 0
    apply (mul_eq_zero.mp ?_).resolve_right hd
    linear_combination (w i : ℝ) * h₂ - (w j : ℝ) * h₁

/--
Two independent integral plane vectors express the first generator with controlled coefficients and bounded product of heights. This is used in the proof of Proposition 3.1 of the paper.
-/
theorem reducedIntegralPlane (q : ι → ℕ) (w z : ι → ℤ)
    (hq : ∀ i, (q i).Prime) (hw : w ≠ 0)
    (hind : ¬ ∃ c : ℚ, ∀ i, (z i : ℚ) = c * (w i : ℚ)) (p : ℝ) :
    ∃ (u₁ u₂ : ι → ℤ) (a b : ℤ),
      (∃ c : ℤ × ℤ, u₁ = _root_.AbcTwoNinths.ExteriorE1.planeMap w z c) ∧
      (∃ c : ℤ × ℤ, u₂ = _root_.AbcTwoNinths.ExteriorE1.planeMap w z c) ∧
      (∀ m n : ℤ, m • u₁ + n • u₂ = 0 → m = 0 ∧ n = 0) ∧
      w = a • u₁ + b • u₂ ∧
      let f := _root_.AbcTwoNinths.ExteriorE1.height (fun i => Real.log (q i : ℝ))
      let A := f (fun i => (u₁ i : ℝ))
      let B := f (fun i => (u₂ i : ℝ))
      let H := f (fun i => (w i : ℝ))
      0 < A ∧ 0 < B ∧ A * B ≤ 4 * H * f (_root_.AbcTwoNinths.ExteriorE1.linearPlane w z (p, 1)) ∧
      |(a : ℝ)| * A ≤ 3 * H ∧ |(b : ℝ)| * B ≤ 2 * H := by
  have ha (i : ι) : 0 < Real.log (q i : ℝ) :=
    Real.log_pos (by exact_mod_cast (hq i).one_lt)
  let f := (_root_.AbcTwoNinths.ExteriorE1.heightSeminorm (fun i => Real.log (q i : ℝ)) (fun i => (ha i).le)).comp (_root_.AbcTwoNinths.ExteriorE1.linearPlane w z)
  obtain ⟨i, j, hm⟩ := _root_.AbcTwoNinths.ExteriorE1.existsMinor hw hind
  have hp (x : ℝ × ℝ) (hx : x ≠ 0) : 0 < f x :=
    _root_.AbcTwoNinths.ExteriorE1.heightPosOfNeZero _ ha _ (_root_.AbcTwoNinths.ExteriorE1.planeNonzeroOfMinor w z hm x hx)
  obtain ⟨x, y, a, b, hd, heq, hpos₁, hpos₂, hprod, ha', hb'⟩ :=
    _root_.AbcTwoNinths.ExteriorE1.coordinateReduction q w z hq hw hind f (_root_.AbcTwoNinths.ExteriorE1.planeHeightContinuous _ _ _ _)
      hp (_root_.AbcTwoNinths.ExteriorE1.sourceExponentPlanePlaneHeight _ _ _ _) p
  have hinj := _root_.AbcTwoNinths.ExteriorE1.planeMapInjective w z hm
  refine ⟨_root_.AbcTwoNinths.ExteriorE1.planeMap w z x, _root_.AbcTwoNinths.ExteriorE1.planeMap w z y, a, b, ⟨x, rfl⟩, ⟨y, rfl⟩, ?_, ?_, ?_⟩
  · intro m n h
    have hxy : m • x + n • y = 0 := hinj (calc
      _root_.AbcTwoNinths.ExteriorE1.planeMap w z (m • x + n • y) = m • _root_.AbcTwoNinths.ExteriorE1.planeMap w z x + n • _root_.AbcTwoNinths.ExteriorE1.planeMap w z y := by
        ext k
        change (m * x.1 + n * y.1) * w k + (m * x.2 + n * y.2) * z k =
          m * (x.1 * w k + x.2 * z k) + n * (y.1 * w k + y.2 * z k)
        ring
      _ = 0 := h
      _ = _root_.AbcTwoNinths.ExteriorE1.planeMap w z 0 := by ext k; simp [_root_.AbcTwoNinths.ExteriorE1.planeMap])
    have h₁ : m * x.1 + n * y.1 = 0 := congrArg Prod.fst hxy
    have h₂ : m * x.2 + n * y.2 = 0 := congrArg Prod.snd hxy
    have hd' : _root_.AbcTwoNinths.ExteriorE1.det2 x y ≠ 0 := by intro hh; simp [hh] at hd
    constructor <;> apply (mul_eq_zero.mp ?_).resolve_right hd' <;> unfold _root_.AbcTwoNinths.ExteriorE1.det2
    · linear_combination y.2 * h₁ - y.1 * h₂
    · linear_combination x.1 * h₂ - x.2 * h₁
  · ext k
    have h₁ : 1 = a * x.1 + b * y.1 := congrArg Prod.fst heq
    have h₂ : 0 = a * x.2 + b * y.2 := congrArg Prod.snd heq
    change w k = a * (x.1 * w k + x.2 * z k) + b * (y.1 * w k + y.2 * z k)
    linear_combination w k * h₁ + z k * h₂
  · have hcast (c : ℤ × ℤ) :
        _root_.AbcTwoNinths.ExteriorE1.linearPlane w z (_root_.AbcTwoNinths.ExteriorE1.realPair c) = fun i => (_root_.AbcTwoNinths.ExteriorE1.planeMap w z c i : ℝ) := by
      ext i
      simp [_root_.AbcTwoNinths.ExteriorE1.linearPlane, _root_.AbcTwoNinths.ExteriorE1.realPair, _root_.AbcTwoNinths.ExteriorE1.planeMap]
    have hfirst : _root_.AbcTwoNinths.ExteriorE1.linearPlane w z (1, 0) = fun i => (w i : ℝ) := by
      ext i
      simp [_root_.AbcTwoNinths.ExteriorE1.linearPlane]
    have he (p : ℝ × ℝ) : f p = _root_.AbcTwoNinths.ExteriorE1.height (fun i => Real.log (q i : ℝ)) (_root_.AbcTwoNinths.ExteriorE1.linearPlane w z p) := rfl
    simpa only [he, hcast, hfirst] using
      And.intro hpos₁ (And.intro hpos₂ (And.intro hprod (And.intro ha' hb')))

end

end AbcTwoNinths.ExteriorE1
