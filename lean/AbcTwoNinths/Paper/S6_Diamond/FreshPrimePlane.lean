/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruiyi Zhang
-/

module

public import AbcTwoNinths.Paper.S6_Diamond.LargeFreshPrimeSupply
public import AbcTwoNinths.Paper.S6_Diamond.SameSourceOverlapCounting
public import AbcTwoNinths.Paper.S6_Diamond.FreshTorusWitness
public import AbcTwoNinths.Paper.S6_Diamond.DistinctPrimeSurvival

/-!
# Fresh Prime Plane

Uses the volume of the projected weighted ball to construct an integral plane with two auxiliary
prime coordinates. It supports Section 6 of the paper.

## Main results
* `AbcTwoNinths.Diamond.freshPrimeMassEventually`
-/

@[expose] public section


namespace AbcTwoNinths.Diamond

section




-- The elaboration of fresh prime plane needs a larger budget.
set_option maxHeartbeats 1200000

open MeasureTheory

/--
Above a common threshold, a fresh prime pair outside the exceptional set generates a plane with unique integral coordinates and injective character. This is used in Section 6 of the paper.
-/
theorem freshPrimeMassEventually {η : ℝ} (hη : η < 1/9) :
    ∃ X : ℝ, ∀ {I : Type} [Fintype I] [DecidableEq I]
      {p R : ℕ} [Fact p.Prime] [Fact (2 < p)] (_hpR : p ∣ R)
      (old : Unit ⊕ I → ℕ) (prime : ∀ i, (old i).Prime) (avoid : ∀ i, p ≠ old i)
      (_hi : Function.Injective old) (_holdR : ∀ i, old i ∣ R) (v : _root_.AbcTwoNinths.Diamond.LatticeSelectedPlaneData old prime avoid)
      (weight : I → ℝ) {H x r B : ℝ} (bad : Finset (ℕ × ℕ)),
      X ≤ x → 0 < R → Real.log R = 3*x → _root_.AbcTwoNinths.ExteriorE2.Admissible p H η x →
      max 128 (16*(1+6/_root_.AbcTwoNinths.ExteriorE2.margin η)) / _root_.AbcTwoNinths.ExteriorE2.margin η ≤ x →
      v.val.toAdd (.inl ()) ≠ 0 →
      (∀ (w : _root_.AbcTwoNinths.Diamond.LatticeSelectedPlaneData old prime avoid) (a : ℝ),
        (∀ i, (w.val.toAdd i : ℝ) = a * v.val.toAdd i) → ∃ c : ℤ, w = v ^ c) →
      (∀ w ∈ (_root_.AbcTwoNinths.Diamond.oldPrimeReduction old prime avoid).toAdditive.ker,
        _root_.AbcTwoNinths.ExteriorE2.cost weight (_root_.AbcTwoNinths.ExteriorE2.project v.val.toAdd w) < r → _root_.AbcTwoNinths.ExteriorE2.project v.val.toAdd w = 0) →
      (∀ i, 0 < weight i) → 0 < r → 0 < B → (∑ i, weight i) ≤ B →
      H ≤ 3*x*|(v.val.toAdd (.inl ()) : ℝ)| →
      _root_.AbcTwoNinths.Diamond.massFloor x ≤ (volume : Measure (_root_.AbcTwoNinths.ExteriorE2.Coord I)).real (_root_.AbcTwoNinths.ExteriorE2.ball weight 0 (r/2)) →
      (bad.card : ℝ) ≤ _root_.AbcTwoNinths.Diamond.badBudget x (Real.log (_root_.AbcTwoNinths.ExteriorE2.m p H (_root_.AbcTwoNinths.ExteriorE2.margin η) x)) →
      ∃ q : ℕ × ℕ, let S := _root_.AbcTwoNinths.ExteriorE2.m p H (_root_.AbcTwoNinths.ExteriorE2.margin η) x
        q ∉ bad ∧ _root_.AbcTwoNinths.ExteriorE2.Fresh S R q.1 ∧ _root_.AbcTwoNinths.ExteriorE2.Fresh S R q.2 ∧ q.1 < q.2 ∧
        ∃ (pr : ∀ i, (_root_.AbcTwoNinths.Diamond.freshExtendedBase old q i).Prime)
          (av : ∀ i, p ≠ _root_.AbcTwoNinths.Diamond.freshExtendedBase old q i) (u : _root_.AbcTwoNinths.Diamond.LatticeSelectedPlaneData (_root_.AbcTwoNinths.Diamond.freshExtendedBase old q) pr av),
          let V := _root_.AbcTwoNinths.Diamond.extension (_root_.AbcTwoNinths.Diamond.freshExtendedBase old q) pr av v
          let γ := _root_.AbcTwoNinths.Diamond.planeCharacter (_root_.AbcTwoNinths.Diamond.freshExtendedBase old q) pr av V u
          u.val.toAdd (.inr false) = 1 ∧ u.val.toAdd (.inr true) = -1 ∧
          _root_.AbcTwoNinths.ExteriorE2.cost weight (_root_.AbcTwoNinths.ExteriorE2.project v.val.toAdd (fun i => u.val.toAdd (.inl i))) < r ∧
          (∀ y : _root_.AbcTwoNinths.Diamond.LatticeSelectedPlaneData (_root_.AbcTwoNinths.Diamond.freshExtendedBase old q) pr av, _root_.AbcTwoNinths.Diamond.inRealPlane V.val u.val y.val →
            ∃! c : ℤ × ℤ, y.val = _root_.AbcTwoNinths.Diamond.along V.val u.val c) ∧ Function.Injective γ ∧
          (γ (Multiplicative.ofAdd ((1,0) : ℤ × ℤ)) : ℚ) = _root_.AbcTwoNinths.Diamond.character old prime avoid v := by
  obtain ⟨X, select⟩ := _root_.AbcTwoNinths.Diamond.survivesAtCommonOnset hη
  refine ⟨X, ?_⟩
  intro I _ _ p R _ _ hpR old prime avoid hi holdR v weight H x r B bad
    hX hR hx adm cut hv line sep hw hr hB hW roof mass badBound
  classical
  have : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  have : Finite (_root_.AbcTwoNinths.ExteriorE2.Label p) := inferInstanceAs (Finite ((ZMod p)ˣ ⧸ _root_.AbcTwoNinths.ExteriorE2.signs p))
  have hvred : _root_.AbcTwoNinths.Diamond.oldPrimeReduction old prime avoid v.val = 1 := v.property
  have family := @_root_.AbcTwoNinths.Diamond.nativeSameSourceFamily I _ _ (_root_.AbcTwoNinths.ExteriorE2.Label p) _ _
    v.val.toAdd hv (_root_.AbcTwoNinths.Diamond.oldPrimeReduction old prime avoid) hvred
    (by exact _root_.AbcTwoNinths.Diamond.primitiveOfLine old prime avoid v hv line) (_root_.AbcTwoNinths.Diamond.residuePrimeLabel p) weight hw
    R hR (p : ℝ) H η x r B hx adm cut (by exact sep) hr hB hW
  obtain ⟨P, _, count, pair⟩ := family
  obtain ⟨q, hq, good⟩ := select hX hR hx adm roof mass P bad count badBound
  obtain ⟨hf, ht, hlt, _, w, hshort, hlabel⟩ := pair q hq
  obtain ⟨pr, av, inj⟩ := _root_.AbcTwoNinths.Diamond.freshExtendedBaseValid hpR old prime avoid hi holdR q hf ht hlt
  obtain ⟨u, _, huf, hut, hcost, hplane, hinj, _, hsource, _⟩ :=
    _root_.AbcTwoNinths.Diamond.freshTorusWitness hpR q hf ht (_root_.AbcTwoNinths.Diamond.freshExtendedBase old q) pr av inj rfl rfl
      v hv line _ _ rfl rfl weight w hshort hlabel
  exact ⟨q, good, hf, ht, hlt, pr, av, u, huf, hut, hcost, hplane, hinj, hsource⟩

end

end AbcTwoNinths.Diamond
