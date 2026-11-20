/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruiyi Zhang
-/

module

public import AbcTwoNinths.Paper.S6_Diamond.SelectedWeightedProjection
public import AbcTwoNinths.Paper.S6_Diamond.SelectedShearEstimate

/-!
# Fresh Prime Projection Separation

The module obtains separation in the projection used to construct the fresh-prime plane. It supports Section 6 of the paper.

## Main results
* `AbcTwoNinths.Diamond.selectedProjectedSeparation`
-/

@[expose] public section


namespace AbcTwoNinths.Diamond

section



/--
A residue-kernel vector whose projected cost is below twice the scale divided by its logarithm has zero projection. This is used in Section 6 of the paper.
-/
theorem selectedProjectedSeparation (t : _root_.AbcTwoNinths.Basic.Triple) {p : ℕ}
    [Fact p.Prime] [Fact (2 < p)]
    (hp : p ∈ (_root_.AbcTwoNinths.Statement.sideValue t (_root_.AbcTwoNinths.Statement.minRadicalSide t)).primeFactors)
    (hx : 0 ≤ t.thirdLogRadical) (hlog : 0 ≤ Real.log t.thirdLogRadical) (shear : _root_.AbcTwoNinths.Diamond.SelectedShearBound t hp)
    {I : Type*} [Fintype I] :
    let side := _root_.AbcTwoNinths.PolyCap.selectedSideData t hp
    let q := _root_.AbcTwoNinths.ExteriorE2.base side.n side.d
    let s := (_root_.AbcTwoNinths.ExteriorE2.vec side.n side.d).toAdd
    ∀ e : Unit ⊕ I ≃ _root_.AbcTwoNinths.ExteriorE2.Support side.n side.d, s (e (.inl ())) ≠ 0 →
      let red := _root_.AbcTwoNinths.ExteriorE2.residueLatticeReduction (q ∘ e) (fun i => _root_.AbcTwoNinths.ExteriorE2.prime side.n side.d (e i))
        (fun i => _root_.AbcTwoNinths.Selection.avoidOfSide side (e i))
      let weight := fun j : I => Real.log (q (e (.inr j)) : ℝ)
      ∀ w ∈ red.ker, _root_.AbcTwoNinths.ExteriorE2.cost weight (_root_.AbcTwoNinths.ExteriorE2.project (s ∘ e) w) < 2 * t.thirdLogRadical / Real.log t.thirdLogRadical →
        _root_.AbcTwoNinths.ExteriorE2.project (s ∘ e) w = 0 := by
  intro side q s e hroof red weight
  have htarget : 2 * t.thirdLogRadical / Real.log t.thirdLogRadical ≤ 4 * t.thirdLogRadical / Real.log t.thirdLogRadical :=
    div_le_div_of_nonneg_right (by linarith) hlog
  exact _root_.AbcTwoNinths.Diamond.projectedSeparationOfReindexedShear e q (_root_.AbcTwoNinths.ExteriorE2.prime side.n side.d)
    (_root_.AbcTwoNinths.Selection.avoidOfSide side) s hroof (fun w hi a => htarget.trans (shear w _ hroof hi a))

end

end AbcTwoNinths.Diamond
