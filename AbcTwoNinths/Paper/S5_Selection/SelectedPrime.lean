/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruiyi Zhang
-/

module

public import AbcTwoNinths.Paper.S5_Selection.RoofOnset
public import AbcTwoNinths.Paper.S2_PolyCap.SideProjection
public import AbcTwoNinths.Paper.S5_Selection.NativeRoof

/-!
# Selected Prime

The module constructs a primitive signed-kernel vector with a lower bound for its largest exponent from contact at a given odd prime. It supports Proposition 5.1 of the paper.

## Main results
* `AbcTwoNinths.Selection.selectedPrimeRoofBounds`
-/

@[expose] public section


namespace AbcTwoNinths.Selection


section

/--
Beyond a common threshold, selected-prime mass and real contact give a primitive selected-side kernel vector with a lower bound on its largest absolute coordinate. This is used in the proof of Proposition 5.1 of the paper.
-/
theorem selectedPrimeRoofBounds {η : ℚ} {κ : ℝ} (hη : _root_.AbcTwoNinths.Statement.admissibleEta η) (hκ : _root_.AbcTwoNinths.Statement.admissibleMargin η κ) :
    ∃ X : ℝ, 0 < X ∧ ∀ (t : _root_.AbcTwoNinths.Basic.Triple) (p : ℕ) [Fact p.Prime] [Fact (2 < p)]
      (hp : p ∈ (_root_.AbcTwoNinths.Statement.sideValue t (_root_.AbcTwoNinths.Statement.minRadicalSide t)).primeFactors),
      t.a ≤ t.b → _root_.AbcTwoNinths.Statement.High η X t → _root_.AbcTwoNinths.Statement.RealContactBound κ t →
      (1 - 2*κ)*t.logHeight ≤ (padicValNat p (_root_.AbcTwoNinths.Statement.sideValue t (_root_.AbcTwoNinths.Statement.minRadicalSide t)) : ℝ)*Real.log p →
      let s := _root_.AbcTwoNinths.PolyCap.selectedSideData t hp
      let r := _root_.AbcTwoNinths.ExteriorE2.residue (_root_.AbcTwoNinths.ExteriorE2.base s.n s.d) (_root_.AbcTwoNinths.ExteriorE2.prime s.n s.d) (_root_.AbcTwoNinths.Selection.avoidOfSide s)
      ∃ w : _root_.AbcTwoNinths.ExteriorE2.Kernel r, w.val = _root_.AbcTwoNinths.ExteriorE2.vec s.n s.d ∧
        (∀ (g : ℕ) (v : _root_.AbcTwoNinths.ExteriorE2.Kernel r), 0 < g → w = v ^ g → g = 1) ∧
        (2-2*κ)*t.logHeight/(3*t.thirdLogRadical) ≤
          ((Finset.univ.sup (fun i : _root_.AbcTwoNinths.ExteriorE2.Support s.n s.d => (w.val.toAdd i).natAbs) : ℕ) : ℝ) := by
  obtain ⟨X, hX, h⟩ := _root_.AbcTwoNinths.Selection.highThreshold hη (_root_.AbcTwoNinths.Basic.contactHeightOnset κ)
  refine ⟨X, hX, ?_⟩
  intro t p _ _ hp ho hh he hm
  have heta : 0 < (η : ℝ) := by exact_mod_cast hη.1
  have hk := hκ.2
  exact _root_.AbcTwoNinths.Selection.nativeRoof t hp (by linarith) (h t hh).1 hm he (h t hh).2
    (_root_.AbcTwoNinths.PolyCap.selectedSideProjection t hp ho)

end

end AbcTwoNinths.Selection
