/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruiyi Zhang
-/

module

public import AbcTwoNinths.Paper.S2_PolyCap.PlaneCramerCoordinates

/-!
# Collision Coordinate Width

The module bounds the height of a residue collision by its coordinate width and recovers the pair by Cramer's rule. It supports Proposition 2.1 of the paper.

## Main results
* `AbcTwoNinths.PolyCap.cramerCollisionRepr`
-/

@[expose] public section


namespace AbcTwoNinths.PolyCap

section

/-- Bounds the height of the collision direction by the weighted sum of its coordinate widths. -/
theorem heightLeCollisionWidth {ι : Type*} [Fintype ι] (q : ι → ℕ)
    (hq : ∀ j, (q j).Prime) (e v : ι → ℤ) (lam : ℝ) :
    _root_.AbcTwoNinths.PolyCap.planeHeight q e v (-lam, 1) ≤
      ∑ j, |(v j : ℝ) - lam * (e j : ℝ)| * Real.log (q j : ℝ) := by
  refine (_root_.AbcTwoNinths.PolyCap.coordHeightBounds (fun j => _root_.AbcTwoNinths.PolyCap.planeCoord q e v j (-lam, 1))).2.trans_eq ?_
  apply Finset.sum_congr rfl
  intro j _
  have hl : 0 ≤ Real.log (q j : ℝ) :=
    Real.log_nonneg (by exact_mod_cast (hq j).one_le)
  rw [_root_.AbcTwoNinths.PolyCap.planeCoord, abs_mul, abs_of_nonneg hl]
  congr 2
  ring

/--
Expresses the real direction of slope parameter lambda in an integral unimodular basis. This is used in the proof of Proposition 2.1 of the paper.
-/
theorem cramerCollisionRepr {w m : ℤ × ℤ} (hd : |_root_.AbcTwoNinths.PolyCap.det2 w m| = 1) (lam : ℝ) :
    ((-lam, 1) : ℝ × ℝ) =
      ((_root_.AbcTwoNinths.PolyCap.cramerA w m (0, 1) : ℝ) - lam * (_root_.AbcTwoNinths.PolyCap.cramerA w m (1, 0) : ℝ)) • _root_.AbcTwoNinths.PolyCap.realPair w +
      ((_root_.AbcTwoNinths.PolyCap.cramerB w m (0, 1) : ℝ) - lam * (_root_.AbcTwoNinths.PolyCap.cramerB w m (1, 0) : ℝ)) • _root_.AbcTwoNinths.PolyCap.realPair m := by
  have h1 := _root_.AbcTwoNinths.PolyCap.cramerReal hd (1, 0)
  have h2 := _root_.AbcTwoNinths.PolyCap.cramerReal hd (0, 1)
  have he : ((-lam, 1) : ℝ × ℝ) = _root_.AbcTwoNinths.PolyCap.realPair (0, 1) + (-lam) • _root_.AbcTwoNinths.PolyCap.realPair (1, 0) := by
    ext <;> simp [_root_.AbcTwoNinths.PolyCap.realPair]
  calc
    _ = _ := he
    _ = _ := by
      conv_lhs => rw [h2, h1]
      ext <;> simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd,
        smul_eq_mul] <;> ring

end

end AbcTwoNinths.PolyCap
