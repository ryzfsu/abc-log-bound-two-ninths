/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruiyi Zhang
-/

module

public import AbcTwoNinths.Paper.S6_Diamond.SignedPrincipalUnitBracket
public import AbcTwoNinths.Paper.S4_ExteriorE2.ResidueLattice
public import AbcTwoNinths.Basic.PlaneDiamond
public import AbcTwoNinths.Paper.S6_Diamond.WeightedProjectionShear
public import AbcTwoNinths.Paper.S6_Diamond.SelectedShellOnset
public import AbcTwoNinths.Paper.S6_Diamond.SelectedTwoLogarithmDepth

/-!
# Selected Weighted Projection

Uses the selected prime's valuation estimate to construct the hypotheses for the weighted shear
bound. It supports Section 6 of the paper.

## Main results
* `AbcTwoNinths.Diamond.selectedShearBoundOf`
-/

@[expose] public section


namespace AbcTwoNinths.Diamond

section





/--
Every real shear of an independent signed kernel lift on the selected support has weighted cost at least four times x divided by log x. This is used in Section 6 of the paper.
-/
def SelectedShearBound (t : _root_.AbcTwoNinths.Basic.Triple) {p : ℕ}
    (hp : p ∈ (_root_.AbcTwoNinths.Statement.sideValue t (_root_.AbcTwoNinths.Statement.minRadicalSide t)).primeFactors) : Prop :=
  ∀ [Fact p.Prime] [Fact (2 < p)],
    let side := _root_.AbcTwoNinths.PolyCap.selectedSideData t hp
    let q := _root_.AbcTwoNinths.ExteriorE2.base side.n side.d
    let r := _root_.AbcTwoNinths.ExteriorE2.residue q (_root_.AbcTwoNinths.ExteriorE2.prime side.n side.d) (_root_.AbcTwoNinths.Selection.avoidOfSide side)
    let s := (_root_.AbcTwoNinths.ExteriorE2.vec side.n side.d).toAdd
    ∀ (w : _root_.AbcTwoNinths.ExteriorE2.Kernel r) (j : _root_.AbcTwoNinths.ExteriorE2.Support side.n side.d), s j ≠ 0 →
      (¬ ∃ a : ℚ, ∀ i, (w.val.toAdd i : ℚ) = a * (s i : ℚ)) →
      ∀ α : ℝ, 4 * t.thirdLogRadical / Real.log t.thirdLogRadical ≤
        ∑ i, |(w.val.toAdd i : ℝ) - α * (s i : ℝ)| * Real.log (q i : ℝ)

/--
The cutoff, depth mass and size hypotheses on a selected prime imply the weighted lower bound for every real shear. This is used in Section 6 of the paper.
-/
theorem selectedShearBoundOf (t : _root_.AbcTwoNinths.Basic.Triple) {p : ℕ}
    (hp : p ∈ (_root_.AbcTwoNinths.Statement.sideValue t (_root_.AbcTwoNinths.Statement.minRadicalSide t)).primeFactors)
    {η : ℚ} {σ κ : ℝ}
    (he : _root_.AbcTwoNinths.Statement.admissibleEta η) (hs : _root_.AbcTwoNinths.Statement.admissibleCutoff η σ) (hk : _root_.AbcTwoNinths.Statement.admissibleMargin η κ)
    (ho : t.a ≤ t.b) (hcut : t.logHeight * Real.exp (-σ * t.thirdLogRadical) < (p : ℝ))
    (hh : _root_.AbcTwoNinths.Statement.High η 16 t) (hlog : (10^9 : ℝ) ≤ Real.log t.thirdLogRadical)
    (hell : t.thirdLogRadical / 2 ≤ Real.log p) (hp5 : 5 ≤ p)
    (hm : t.logHeight / 2 ≤ (padicValNat p (_root_.AbcTwoNinths.Statement.sideValue t (_root_.AbcTwoNinths.Statement.minRadicalSide t)) : ℝ) * Real.log p) :
    _root_.AbcTwoNinths.Diamond.SelectedShearBound t hp := by
  intro _ _ side q r s w j hj hind α
  obtain ⟨source, hsource, depth⟩ := _root_.AbcTwoNinths.Diamond.selectedB1Depth t hp hp5 he hs hk hcut hh
  have hx : 0 < t.thirdLogRadical := by linarith [hh.1]
  have hH : 0 < t.logHeight := (Real.exp_pos _).trans_le hh.2
  have hV := _root_.AbcTwoNinths.Diamond.selectedMassLe t hp ho
  have h := _root_.AbcTwoNinths.Diamond.nativeWeightedShear q (_root_.AbcTwoNinths.ExteriorE2.prime side.n side.d) (_root_.AbcTwoNinths.Selection.avoidOfSide side)
    Subtype.val_injective source w (j := j) (by simpa [hsource] using hj)
    (by simpa [hsource] using hind) (α := α) hx hH hell hm (by norm_num at hlog ⊢; exact hlog)
    (by simpa [hsource, _root_.AbcTwoNinths.Basic.mass] using hV) depth
  simpa only [hsource] using h



end

end AbcTwoNinths.Diamond
