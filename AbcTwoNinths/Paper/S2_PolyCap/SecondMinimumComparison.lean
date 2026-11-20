/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruiyi Zhang
-/

module

public import AbcTwoNinths.Paper.S2_PolyCap.PrimitivePlaneBasis

/-!
# Second Minimum Comparison

The module rounds real Cramer coefficients to compare a candidate vector with the second minimum. It supports Proposition 2.1 of the paper.

## Main results
* `AbcTwoNinths.PolyCap.secondMinimumCompare`
-/

@[expose] public section


namespace AbcTwoNinths.PolyCap

section

/-- The floor of a real number plus one half lies within one half of the original number. -/
theorem nearestIntBound (s : ℝ) : |(⌊s + 1/2⌋ : ℤ) - s| ≤ 1/2 := by
  rw [abs_le]
  constructor
  · linarith [Int.lt_floor_add_one (s + 1/2)]
  · linarith [Int.floor_le (s + 1/2)]

/--
A determinant-one pair expands every integer pair over the reals with its two oriented determinants as coefficients.
-/
theorem realPairCramer {w z x : ℤ × ℤ} (h : _root_.AbcTwoNinths.PolyCap.det2 w z = 1) :
    _root_.AbcTwoNinths.PolyCap.realPair x = (_root_.AbcTwoNinths.PolyCap.det2 x z : ℝ) • _root_.AbcTwoNinths.PolyCap.realPair w + (_root_.AbcTwoNinths.PolyCap.det2 w x : ℝ) • _root_.AbcTwoNinths.PolyCap.realPair z := by
  have h1 : x.1 = _root_.AbcTwoNinths.PolyCap.det2 x z * w.1 + _root_.AbcTwoNinths.PolyCap.det2 w x * z.1 := by
    unfold _root_.AbcTwoNinths.PolyCap.det2 at *
    linear_combination -x.1 * h
  have h2 : x.2 = _root_.AbcTwoNinths.PolyCap.det2 x z * w.2 + _root_.AbcTwoNinths.PolyCap.det2 w x * z.2 := by
    unfold _root_.AbcTwoNinths.PolyCap.det2 at *
    linear_combination -x.2 * h
  apply Prod.ext
  · change (x.1 : ℝ) = (_root_.AbcTwoNinths.PolyCap.det2 x z : ℝ) * w.1 + (_root_.AbcTwoNinths.PolyCap.det2 w x : ℝ) * z.1
    exact_mod_cast h1
  · change (x.2 : ℝ) = (_root_.AbcTwoNinths.PolyCap.det2 x z : ℝ) * w.2 + (_root_.AbcTwoNinths.PolyCap.det2 w x : ℝ) * z.2
    exact_mod_cast h2

/--
A least-height unimodular companion has height at most that of any independent competitor whose height dominates the first vector's height. This is used in the proof of Proposition 2.1 of the paper.
-/
theorem secondMinimumCompare {ι : Type*} [Fintype ι]
    (q : ι → ℕ) (e v : ι → ℤ) {w z m x : ℤ × ℤ}
    (hz : _root_.AbcTwoNinths.PolyCap.det2 w z = 1)
    (hm : ∀ y : ℤ × ℤ, |_root_.AbcTwoNinths.PolyCap.det2 w y| = 1 →
      _root_.AbcTwoNinths.PolyCap.planeHeight q e v (_root_.AbcTwoNinths.PolyCap.realPair m) ≤ _root_.AbcTwoNinths.PolyCap.planeHeight q e v (_root_.AbcTwoNinths.PolyCap.realPair y))
    (hwx : _root_.AbcTwoNinths.PolyCap.planeHeight q e v (_root_.AbcTwoNinths.PolyCap.realPair w) ≤ _root_.AbcTwoNinths.PolyCap.planeHeight q e v (_root_.AbcTwoNinths.PolyCap.realPair x))
    (hd : _root_.AbcTwoNinths.PolyCap.det2 w x ≠ 0) :
    _root_.AbcTwoNinths.PolyCap.planeHeight q e v (_root_.AbcTwoNinths.PolyCap.realPair m) ≤ _root_.AbcTwoNinths.PolyCap.planeHeight q e v (_root_.AbcTwoNinths.PolyCap.realPair x) := by
  by_cases h : |_root_.AbcTwoNinths.PolyCap.det2 w x| = 1
  · exact hm x h
  let a : ℝ := _root_.AbcTwoNinths.PolyCap.det2 x z
  let d : ℝ := _root_.AbcTwoNinths.PolyCap.det2 w x
  have hd' : d ≠ 0 := by dsimp [d]; exact_mod_cast hd
  have h2 : 2 ≤ |d| := by
    have hh : (2 : ℤ) ≤ |_root_.AbcTwoNinths.PolyCap.det2 w x| := by
      have := abs_pos.mpr hd
      omega
    dsimp [d]
    exact_mod_cast hh
  let s : ℝ := a / d
  let k : ℤ := ⌊s + 1/2⌋
  let y := (z.1 + k * w.1, z.2 + k * w.2)
  have hy : _root_.AbcTwoNinths.PolyCap.det2 w y = 1 := by
    dsimp [_root_.AbcTwoNinths.PolyCap.det2, y] at *
    linear_combination hz
  have hyR : _root_.AbcTwoNinths.PolyCap.realPair y = ((k : ℝ) - s) • _root_.AbcTwoNinths.PolyCap.realPair w + (1 / d) • _root_.AbcTwoNinths.PolyCap.realPair x := by
    have hxR := _root_.AbcTwoNinths.PolyCap.realPairCramer (x := x) hz
    change _root_.AbcTwoNinths.PolyCap.realPair x = a • _root_.AbcTwoNinths.PolyCap.realPair w + d • _root_.AbcTwoNinths.PolyCap.realPair z at hxR
    have hrepr : _root_.AbcTwoNinths.PolyCap.realPair y = _root_.AbcTwoNinths.PolyCap.realPair z + (k : ℝ) • _root_.AbcTwoNinths.PolyCap.realPair w := by
      ext <;> simp [_root_.AbcTwoNinths.PolyCap.realPair, y]
    rw [hrepr, hxR, smul_add, smul_smul, smul_smul]
    have hdd : 1 / d * d = 1 := by field_simp
    rw [hdd, one_smul]
    apply Prod.ext <;>
      simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul] <;>
      dsimp [s] <;> ring
  have hround : |(k : ℝ) - s| ≤ 1/2 := _root_.AbcTwoNinths.PolyCap.nearestIntBound s
  have hdiv : |1 / d| ≤ (1/2 : ℝ) := by
    rw [abs_div, abs_one, div_le_iff₀ (abs_pos.mpr hd')]
    linarith
  calc
    _ ≤ _root_.AbcTwoNinths.PolyCap.planeHeight q e v (_root_.AbcTwoNinths.PolyCap.realPair y) := hm y (by simp [hy])
    _ ≤ |(k : ℝ) - s| * _root_.AbcTwoNinths.PolyCap.planeHeight q e v (_root_.AbcTwoNinths.PolyCap.realPair w) +
        |1 / d| * _root_.AbcTwoNinths.PolyCap.planeHeight q e v (_root_.AbcTwoNinths.PolyCap.realPair x) := by
      rw [hyR]
      exact (_root_.AbcTwoNinths.PolyCap.planeHeightAdd q e v _ _).trans_eq (by rw [_root_.AbcTwoNinths.PolyCap.planeHeightSmul, _root_.AbcTwoNinths.PolyCap.planeHeightSmul])
    _ ≤ _ := by
      have hw0 : 0 ≤ _root_.AbcTwoNinths.PolyCap.planeHeight q e v (_root_.AbcTwoNinths.PolyCap.realPair w) := _root_.AbcTwoNinths.PolyCap.coordHeightNonneg _
      have hx0 : 0 ≤ _root_.AbcTwoNinths.PolyCap.planeHeight q e v (_root_.AbcTwoNinths.PolyCap.realPair x) := _root_.AbcTwoNinths.PolyCap.coordHeightNonneg _
      linarith [mul_le_mul_of_nonneg_right hround hw0, mul_le_mul_of_nonneg_right hdiv hx0]

end

end AbcTwoNinths.PolyCap
