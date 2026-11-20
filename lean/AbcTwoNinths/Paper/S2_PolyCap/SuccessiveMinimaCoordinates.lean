/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruiyi Zhang
-/

module

public import AbcTwoNinths.Paper.S2_PolyCap.UnimodularMinima

/-!
# Successive Minima Coordinates

The module bounds coordinates of plane vectors in a basis at successive minima. It supports Proposition 2.1 of the paper.

## Main results
* `AbcTwoNinths.PolyCap.coordBoundsOfMinima`
-/

@[expose] public section


namespace AbcTwoNinths.PolyCap

section

/--
In a transverse minimum pair ordered by height, the weighted second and first coordinates are bounded by twice and three times the plane height, respectively. This is used in the proof of Proposition 2.1 of the paper.
-/
theorem coordBoundsOfMinima {ι : Type*} [Fintype ι]
    (q : ι → ℕ) (e v : ι → ℤ) {w m : ℤ × ℤ}
    (hd : _root_.AbcTwoNinths.PolyCap.det2 w m ≠ 0)
    (hmin : ∀ x : ℤ × ℤ, _root_.AbcTwoNinths.PolyCap.det2 w x ≠ 0 →
      _root_.AbcTwoNinths.PolyCap.planeHeight q e v (_root_.AbcTwoNinths.PolyCap.realPair m) ≤ _root_.AbcTwoNinths.PolyCap.planeHeight q e v (_root_.AbcTwoNinths.PolyCap.realPair x))
    (hwm : _root_.AbcTwoNinths.PolyCap.planeHeight q e v (_root_.AbcTwoNinths.PolyCap.realPair w) ≤ _root_.AbcTwoNinths.PolyCap.planeHeight q e v (_root_.AbcTwoNinths.PolyCap.realPair m))
    (a b : ℝ) :
    let H := _root_.AbcTwoNinths.PolyCap.planeHeight q e v
    let z := a • _root_.AbcTwoNinths.PolyCap.realPair w + b • _root_.AbcTwoNinths.PolyCap.realPair m
    |b| * H (_root_.AbcTwoNinths.PolyCap.realPair m) ≤ 2 * H z ∧ |a| * H (_root_.AbcTwoNinths.PolyCap.realPair w) ≤ 3 * H z := by
  let H := _root_.AbcTwoNinths.PolyCap.planeHeight q e v
  let z := a • _root_.AbcTwoNinths.PolyCap.realPair w + b • _root_.AbcTwoNinths.PolyCap.realPair m
  change |b| * H (_root_.AbcTwoNinths.PolyCap.realPair m) ≤ 2 * H z ∧ |a| * H (_root_.AbcTwoNinths.PolyCap.realPair w) ≤ 3 * H z
  have hn (r : ℝ × ℝ) : 0 ≤ H r := _root_.AbcTwoNinths.PolyCap.coordHeightNonneg _
  have hs (t : ℝ) (r : ℝ × ℝ) : H (t • r) = |t| * H r := _root_.AbcTwoNinths.PolyCap.planeHeightSmul q e v t r
  have ha (r s : ℝ × ℝ) : H (r+s) ≤ H r + H s := _root_.AbcTwoNinths.PolyCap.planeHeightAdd q e v r s
  have hb : |b| * H (_root_.AbcTwoNinths.PolyCap.realPair m) ≤ 2 * H z := by
    by_cases h : b = 0
    · simp [h, hn z]
    let s := a / b
    let k : ℤ := ⌊s + 1/2⌋
    let y := (m.1 + k * w.1, m.2 + k * w.2)
    have hy : _root_.AbcTwoNinths.PolyCap.det2 w y = _root_.AbcTwoNinths.PolyCap.det2 w m := by dsimp [_root_.AbcTwoNinths.PolyCap.det2,y]; ring
    have hrepr : _root_.AbcTwoNinths.PolyCap.realPair y = (1/b) • z + ((k : ℝ) - s) • _root_.AbcTwoNinths.PolyCap.realPair w := by
      dsimp [z, s]
      apply Prod.ext <;>
        simp only [_root_.AbcTwoNinths.PolyCap.realPair, y, Int.cast_add, Int.cast_mul, Prod.fst_add, Prod.snd_add,
          Prod.smul_fst, Prod.smul_snd, smul_eq_mul] <;>
        field_simp <;> ring
    have hround : |(k : ℝ) - s| ≤ 1/2 := _root_.AbcTwoNinths.PolyCap.nearestIntBound s
    have hc : H (_root_.AbcTwoNinths.PolyCap.realPair m) ≤ H ((1/b) • z) + H (((k : ℝ) - s) • _root_.AbcTwoNinths.PolyCap.realPair w) :=
      (hmin y (hy ▸ hd)).trans (by
      change H (_root_.AbcTwoNinths.PolyCap.realPair y) ≤ _
      rw [hrepr]
      exact ha _ _)
    rw [hs, hs, abs_div, abs_one, one_div, inv_mul_eq_div] at hc
    have hh : H (_root_.AbcTwoNinths.PolyCap.realPair m) / 2 ≤ H z / |b| := by
      linarith [mul_le_mul_of_nonneg_right hround (hn (_root_.AbcTwoNinths.PolyCap.realPair w))]
    have hh' := (le_div_iff₀ (abs_pos.mpr h)).mp hh
    linarith
  refine ⟨hb, ?_⟩
  have hrepr : a • _root_.AbcTwoNinths.PolyCap.realPair w = z + (-b) • _root_.AbcTwoNinths.PolyCap.realPair m := by
    dsimp [z]; rw [neg_smul, add_neg_cancel_right]
  have hh := ha z ((-b) • _root_.AbcTwoNinths.PolyCap.realPair m)
  rw [← hrepr, hs, hs, abs_neg] at hh
  linarith

end

end AbcTwoNinths.PolyCap
