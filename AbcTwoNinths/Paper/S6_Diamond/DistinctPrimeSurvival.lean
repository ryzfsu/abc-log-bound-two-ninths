/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruiyi Zhang
-/

module

public import AbcTwoNinths.Paper.S6_Diamond.PrimitivePlaneLine
public import AbcTwoNinths.Paper.S6_Diamond.MassThreshold

/-!
# Distinct Prime Survival

The module proves that a distinct candidate prime survives the exclusions at the common onset. It supports Section 6 of the paper.

## Main results
* `AbcTwoNinths.Diamond.survivesAtCommonOnset`
-/

@[expose] public section


namespace AbcTwoNinths.Diamond

section



/-- Above a common radical threshold, the lower bound on candidate pairs exceeds the
exceptional-pair budget, so at least one candidate survives. -/
theorem survivesAtCommonOnset {η : ℝ} (hη : η < 1/9) :
    ∃ X : ℝ, ∀ {R p : ℕ} [Fact p.Prime] [Fact (2 < p)] {H x roof W : ℝ},
      X ≤ x → 0 < R → Real.log R = 3*x → _root_.AbcTwoNinths.ExteriorE2.Admissible p H η x →
      H ≤ 3*x*|roof| → _root_.AbcTwoNinths.Diamond.massFloor x ≤ W →
      ∀ P B : Finset (ℕ × ℕ),
      let S := _root_.AbcTwoNinths.ExteriorE2.m p H (_root_.AbcTwoNinths.ExteriorE2.margin η) x
      let n := ((_root_.AbcTwoNinths.ExteriorE2.fresh R S).card : ℝ)
      (n/2)*(n*W/((Nat.card (_root_.AbcTwoNinths.ExteriorE2.Label p) : ℝ)/|roof|)-1) ≤ P.card →
      (B.card : ℝ) ≤ _root_.AbcTwoNinths.Diamond.badBudget x (Real.log S) → ∃ q ∈ P, q ∉ B := by
  obtain ⟨X, hX⟩ := _root_.AbcTwoNinths.Diamond.strictBulk hη
  refine ⟨X, ?_⟩
  intro R p _ _ H x roof W hx hR hxR adm hm hW P B
  dsimp only
  intro hP hB
  have budget := hX hx hR hxR adm (Fact.out : p.Prime).one_lt hm hW
  dsimp only at budget
  rw [_root_.AbcTwoNinths.ExteriorE2.labelCardReal, div_div] at hP
  have hlt : (B.card : ℝ) < P.card := hB.trans_lt (budget.trans_le hP)
  have cardLt : B.card < P.card := by exact_mod_cast hlt
  by_contra! allBad
  exact cardLt.not_ge (Finset.card_le_card (show P ⊆ B from allBad))

end

end AbcTwoNinths.Diamond
