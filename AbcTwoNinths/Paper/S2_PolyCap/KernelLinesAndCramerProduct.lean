/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruiyi Zhang
-/

module

public import AbcTwoNinths.Paper.S2_PolyCap.CollisionCoordinateWidth

/-!
# Kernel Lines And Cramer Product

The module combines the Cramer determinant product with the integer lines in an exponent kernel. It supports Proposition 2.1 of the paper.

## Main results
* `AbcTwoNinths.PolyCap.cramerProductAndLines`
-/

@[expose] public section


namespace AbcTwoNinths.PolyCap

section

/--
For a unimodular basis `w, m` with `m` minimizing height off the line through `w` and `H w ≤ H m`,
the bound `H (-lam, 1) < T` gives `H w * H m < 12 * T * H (1, 0)` when `H (1, 0) > 0`, together
with weighted Cramer coefficient bounds and height equalities when `(1, 0)` is a signed basis vector.
-/
theorem cramerProductAndLines {ι : Type*} [Fintype ι]
    (q : ι → ℕ) (e v : ι → ℤ) {w m : ℤ × ℤ} {lam T : ℝ}
    (hd : |_root_.AbcTwoNinths.PolyCap.det2 w m| = 1)
    (hm : ∀ x : ℤ × ℤ, _root_.AbcTwoNinths.PolyCap.det2 w x ≠ 0 →
      _root_.AbcTwoNinths.PolyCap.planeHeight q e v (_root_.AbcTwoNinths.PolyCap.realPair m) ≤ _root_.AbcTwoNinths.PolyCap.planeHeight q e v (_root_.AbcTwoNinths.PolyCap.realPair x))
    (hwm : _root_.AbcTwoNinths.PolyCap.planeHeight q e v (_root_.AbcTwoNinths.PolyCap.realPair w) ≤ _root_.AbcTwoNinths.PolyCap.planeHeight q e v (_root_.AbcTwoNinths.PolyCap.realPair m))
    (h0 : 0 < _root_.AbcTwoNinths.PolyCap.planeHeight q e v (1, 0))
    (hT : _root_.AbcTwoNinths.PolyCap.planeHeight q e v (-lam, 1) < T) :
    let a := _root_.AbcTwoNinths.PolyCap.cramerA w m (1, 0); let b := _root_.AbcTwoNinths.PolyCap.cramerB w m (1, 0)
    let H := _root_.AbcTwoNinths.PolyCap.planeHeight q e v
    |(a : ℝ)| * H (_root_.AbcTwoNinths.PolyCap.realPair w) ≤ 3 * H (1, 0) ∧
    |(b : ℝ)| * H (_root_.AbcTwoNinths.PolyCap.realPair m) ≤ 2 * H (1, 0) ∧
    H (_root_.AbcTwoNinths.PolyCap.realPair w) * H (_root_.AbcTwoNinths.PolyCap.realPair m) < 12 * T * H (1, 0) ∧
    (b = 0 → |a| = 1 → H (1, 0) = H (_root_.AbcTwoNinths.PolyCap.realPair w)) ∧
    (a = 0 → |b| = 1 → H (1, 0) = H (_root_.AbcTwoNinths.PolyCap.realPair m)) := by
  dsimp only
  let a := _root_.AbcTwoNinths.PolyCap.cramerA w m (1, 0)
  let b := _root_.AbcTwoNinths.PolyCap.cramerB w m (1, 0)
  let c := _root_.AbcTwoNinths.PolyCap.cramerA w m (0, 1)
  let d := _root_.AbcTwoNinths.PolyCap.cramerB w m (0, 1)
  have hne : _root_.AbcTwoNinths.PolyCap.det2 w m ≠ 0 := by intro h; simp [h] at hd
  have horig :
      ((1, 0) : ℝ × ℝ) = (a : ℝ) • _root_.AbcTwoNinths.PolyCap.realPair w + (b : ℝ) • _root_.AbcTwoNinths.PolyCap.realPair m := by
    simpa [_root_.AbcTwoNinths.PolyCap.realPair] using _root_.AbcTwoNinths.PolyCap.cramerReal hd (1, 0)
  have hcol := _root_.AbcTwoNinths.PolyCap.cramerCollisionRepr hd lam
  have hfirst := _root_.AbcTwoNinths.PolyCap.coordBoundsOfMinima q e v hne hm hwm (a : ℝ) (b : ℝ)
  dsimp only at hfirst
  rw [← horig] at hfirst
  have hsecond := _root_.AbcTwoNinths.PolyCap.coordBoundsOfMinima q e v hne hm hwm
    ((c : ℝ) - lam * (a : ℝ)) ((d : ℝ) - lam * (b : ℝ))
  dsimp only at hsecond
  change ((-lam, 1) : ℝ × ℝ) = _ at hcol
  rw [← hcol] at hsecond
  have hdet : |(a : ℝ) * ((d : ℝ) - lam * (b : ℝ)) -
      (b : ℝ) * ((c : ℝ) - lam * (a : ℝ))| = 1 := by
    have he : (a : ℝ) * ((d : ℝ) - lam * (b : ℝ)) -
        (b : ℝ) * ((c : ℝ) - lam * (a : ℝ)) = (a : ℝ) * d - (b : ℝ) * c := by ring
    rw [he]
    exact_mod_cast _root_.AbcTwoNinths.PolyCap.cramerUnitDet hd
  refine ⟨hfirst.2, hfirst.1,
    _root_.AbcTwoNinths.PolyCap.determinantHeightProduct hdet h0 (_root_.AbcTwoNinths.PolyCap.coordHeightNonneg _) (_root_.AbcTwoNinths.PolyCap.coordHeightNonneg _)
      hfirst.2 hfirst.1 hsecond.2 hsecond.1 hT, ?_, ?_⟩
  · intro hb ha
    change b = 0 at hb
    change |a| = 1 at ha
    have hr : ((1, 0) : ℝ × ℝ) = (a : ℝ) • _root_.AbcTwoNinths.PolyCap.realPair w := by simpa [hb] using horig
    have ha' : |(a : ℝ)| = 1 := by exact_mod_cast ha
    conv_lhs => rw [hr, _root_.AbcTwoNinths.PolyCap.planeHeightSmul, ha', one_mul]
  · intro ha hb
    change a = 0 at ha
    change |b| = 1 at hb
    have hr : ((1, 0) : ℝ × ℝ) = (b : ℝ) • _root_.AbcTwoNinths.PolyCap.realPair m := by simpa [ha] using horig
    have hb' : |(b : ℝ)| = 1 := by exact_mod_cast hb
    conv_lhs => rw [hr, _root_.AbcTwoNinths.PolyCap.planeHeightSmul, hb', one_mul]

end

end AbcTwoNinths.PolyCap
