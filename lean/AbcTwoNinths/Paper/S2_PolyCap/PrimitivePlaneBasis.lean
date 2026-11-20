/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruiyi Zhang
-/

module

public import AbcTwoNinths.Paper.S2_PolyCap.HeightMinimumSelection

/-!
# Primitive Plane Basis

The module finds a companion for a shortest lattice vector with determinant one up to sign. It supports Proposition 2.1 of the paper.

## Main results
* `AbcTwoNinths.PolyCap.minHasCompanion`
-/

@[expose] public section


namespace AbcTwoNinths.PolyCap

section

/--
The determinant of two ordered integer pairs. This is used in the proof of Proposition 2.1 of the paper.
-/
def det2 (x y : ℤ × ℤ) : ℤ := x.1 * y.2 - x.2 * y.1

/--
A nonzero vector minimizing the plane height for an injective plane map has an integral companion of determinant one. This is used in the proof of Proposition 2.1 of the paper.
-/
theorem minHasCompanion {ι : Type*} [Fintype ι] (q : ι → ℕ)
    (hq : ∀ j, (q j).Prime) {e v : ι → ℤ} (hinj : Function.Injective (_root_.AbcTwoNinths.PolyCap.planeMap e v))
    {w : ℤ × ℤ} (hw : w ≠ 0)
    (hm : ∀ x : ℤ × ℤ, x ≠ 0 → _root_.AbcTwoNinths.PolyCap.planeHeight q e v (_root_.AbcTwoNinths.PolyCap.realPair w) ≤ _root_.AbcTwoNinths.PolyCap.planeHeight q e v (_root_.AbcTwoNinths.PolyCap.realPair x)) :
    ∃ z, _root_.AbcTwoNinths.PolyCap.det2 w z = 1 := by
  let g : ℕ := Int.gcd w.1 w.2
  obtain ⟨a, ha⟩ := Int.gcd_dvd_left w.1 w.2
  obtain ⟨b, hb⟩ := Int.gcd_dvd_right w.1 w.2
  change w.1 = (g : ℤ) * a at ha
  change w.2 = (g : ℤ) * b at hb
  have hab : (a, b) ≠ (0 : ℤ × ℤ) := by
    intro h
    apply hw
    have hf := congrArg Prod.fst h
    have hs := congrArg Prod.snd h
    change a = 0 at hf
    change b = 0 at hs
    exact Prod.ext (by simp [ha, hf]) (by simp [hb, hs])
  have hgpos : 0 < g := by
    by_contra! h
    have hz : g = 0 := by omega
    exact hw (Prod.ext (by simp [ha, hz]) (by simp [hb, hz]))
  have hr : _root_.AbcTwoNinths.PolyCap.realPair w = (g : ℝ) • _root_.AbcTwoNinths.PolyCap.realPair (a, b) := by
    apply Prod.ext
    · change (w.1 : ℝ) = (g : ℝ) * (a : ℝ)
      exact_mod_cast ha
    · change (w.2 : ℝ) = (g : ℝ) * (b : ℝ)
      exact_mod_cast hb
  have h := hm (a, b) hab
  rw [hr, _root_.AbcTwoNinths.PolyCap.planeHeightSmul, abs_of_nonneg (Nat.cast_nonneg g)] at h
  have hp := _root_.AbcTwoNinths.PolyCap.heightPosOfInjective q hq hinj hab
  have hg' : (g : ℝ) ≤ 1 := by
    by_contra! hgt
    nlinarith [mul_pos (sub_pos.mpr hgt) hp]
  have hg : g = 1 := by
    have hle : g ≤ 1 := by exact_mod_cast hg'
    omega
  refine ⟨(-Int.gcdB w.1 w.2, Int.gcdA w.1 w.2), ?_⟩
  have hbez := Int.gcd_eq_gcd_ab w.1 w.2
  change (g : ℤ) = _ at hbez
  rw [hg] at hbez
  simp only [_root_.AbcTwoNinths.PolyCap.det2]
  linear_combination -hbez

end

end AbcTwoNinths.PolyCap
