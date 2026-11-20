/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruiyi Zhang
-/

module

public import AbcTwoNinths.Paper.S2_PolyCap.SecondMinimumComparison

/-!
# Unimodular Minima

The module constructs a unimodular integer basis that realizes the two successive minima. It supports Proposition 2.1 of the paper.

## Main results
* `AbcTwoNinths.PolyCap.existsUnimodularMinima`
-/

@[expose] public section


namespace AbcTwoNinths.PolyCap

section

/--
The prime-weighted plane height admits a unimodular basis realizing both successive minima. This is used in the proof of Proposition 2.1 of the paper.
-/
theorem existsUnimodularMinima {ι : Type*} [Fintype ι]
    (q : ι → ℕ) (hq : ∀ j, (q j).Prime) {e v : ι → ℤ}
    (he : e ≠ 0) (hind : ¬ ∃ c : ℚ, ∀ j, (v j : ℚ) = c * (e j : ℚ)) :
    ∃ w m : ℤ × ℤ, w ≠ 0 ∧ |_root_.AbcTwoNinths.PolyCap.det2 w m| = 1 ∧
      (∀ x : ℤ × ℤ, x ≠ 0 → _root_.AbcTwoNinths.PolyCap.planeHeight q e v (_root_.AbcTwoNinths.PolyCap.realPair w) ≤ _root_.AbcTwoNinths.PolyCap.planeHeight q e v (_root_.AbcTwoNinths.PolyCap.realPair x)) ∧
      (∀ x : ℤ × ℤ, _root_.AbcTwoNinths.PolyCap.det2 w x ≠ 0 → _root_.AbcTwoNinths.PolyCap.planeHeight q e v (_root_.AbcTwoNinths.PolyCap.realPair m) ≤ _root_.AbcTwoNinths.PolyCap.planeHeight q e v (_root_.AbcTwoNinths.PolyCap.realPair x)) := by
  obtain ⟨i, j, hd⟩ := _root_.AbcTwoNinths.PolyCap.existsNonzeroMinorOfInd he hind
  obtain ⟨w, hw, hwmin⟩ := _root_.AbcTwoNinths.PolyCap.selectHeightMinimum q hq hd (fun x => x ≠ 0)
    (w := (1, 0)) (by decide)
  obtain ⟨z, hz⟩ := _root_.AbcTwoNinths.PolyCap.minHasCompanion q hq (_root_.AbcTwoNinths.PolyCap.planeMapInjectiveOfMinor hd) hw hwmin
  obtain ⟨m, hm, hmmin⟩ := _root_.AbcTwoNinths.PolyCap.selectHeightMinimum q hq hd (fun x => |_root_.AbcTwoNinths.PolyCap.det2 w x| = 1)
    (w := z) (by simp [hz])
  refine ⟨w, m, hw, hm, hwmin, fun x hx => ?_⟩
  apply _root_.AbcTwoNinths.PolyCap.secondMinimumCompare q e v hz hmmin _ hx
  apply hwmin
  intro h
  subst x
  exact hx (by simp [_root_.AbcTwoNinths.PolyCap.det2])

end

end AbcTwoNinths.PolyCap
